# doc-gen4 ボトルネック計測レポート

**対象**: doc-gen4 `v4.31.0` (rev `0bc516c`) / Lean `v4.31.0` / Mathlib `v4.31.0`
**測定対象プロジェクト**: `InformationTheory` (431 モジュール, Mathlib 全体に依存)
**測定日**: 2026-08-09
**目的**: 新規 Lean ドキュメントジェネレーター構想の Step 1「現状の時間を分解して測る」

---

## 0. 結論サマリ

計測の結果、現行 doc-gen4 のコストは **3 つの層**に分かれ、それぞれ別の原因で高価であることが確定した。

| 層 | 何が起きるか | 実測での支配率 | 原因 |
|---|---|---|---|
| **A. 環境ロード** | モジュールごとに 1 プロセスを起動し、その import closure 全体を `importModules` する | 単一モジュール抽出の **89.6〜97%** | プロセス境界ごとに closure 全体を再ロードする設計 |
| **B. 意味解析** | `DocInfo.ofConstant` を宣言ごとに実行 (型の pretty print + equation lemma 生成) | 環境が共有されている場合の主コスト。Lean core 抽出では **93.9%** | `getEqnsFor?` が実際に equational lemma を elaborate する |
| **C. HTML 生成** | `fromDb` が DB からモジュールを読み直して HTML 化 | HTML 生成 CPU の **78.4%** が DB 読み出し | 宣言ごとに個別 SQL を発行する N+1 構造 |

そして構想の中心仮説は**支持された**。同一の 432 モジュールを、

- **方式A** (現行 doc-gen4 = モジュールごとに 1 プロセス): 2.51 秒/モジュール → 432 モジュール換算 **約 1084 秒**
- **方式B** (1 プロセスでまとめて抽出): **47.4 秒**

**約 23 倍**の差。うち方式A の 89.6% が `importModules` であり、これは「自パッケージの宣言だけを見たいのに、依存ライブラリ全体を毎回ロードし直している」コストそのものである。

---

## 1. 測定環境

| 項目 | 値 |
|---|---|
| マシン | Apple M1, 8 コア, 16 GB RAM |
| OS | macOS (Darwin 25.6.0) |
| ディスク | APFS, 空き 17 GB (測定開始時) |
| Mathlib olean | 5.7 GB / 8,229 モジュール |
| InformationTheory olean | 600 MB / 431 モジュール |

計測はいずれも olean が既にビルド済み・ページキャッシュが暖まった状態で行った (cold cache では import がさらに遅い。実測で同一モジュールが 7.35s → 3.32s と 2 倍以上変動する)。

---

## 2. 対象パイプラインの構造

doc-gen4 は v4.31 で **SQLite ベース**に再設計されている。Lake の facet として次の順に走る。

```text
bibPrepass                     参考文献の前処理 (1 回)
   │
genCore  Init / Std / Lake / Lean    ← 4 プロセス。core 宣言を api-docs.db へ
   │
single <module>                ← モジュール 1 個につき 1 プロセス。 ★ここが N 回
   │                              (依存モジュールの docInfo に再帰的に依存)
   ▼
api-docs.db  (SQLite)
   │
fromDb  <root modules>         ← 1 プロセス。DB から全対象モジュールの HTML を生成
   │                              + 検索インデックス + navbar
   ▼
.lake/build/doc/**.html
```

`single` の実体は次の 2 段だけである (`Main.lean`)。

```lean
let doc ← load <| .analyzeConcreteModules relevantModules   -- 環境ロード + 意味解析
updateModuleDb builtinDocstringValues doc buildDir dbFile (some sourceUri)  -- DB 書き込み
```

`load` の中身 (`DocGen4/Load.lean`) は `importModules` して `Process.process` を呼ぶだけであり、
**`analyzeConcreteModules` は既に `Array Name` を受け取れる**。1 モジュールに固定しているのは
`Main.lean` の CLI 定義だけで、バッチ抽出はアーキテクチャ上すでに可能である (→ §4.3)。

### 2.1 見落としやすい構造的な性質

コードを読んで確認した、計測前には分からない性質:

1. **`process` は環境の全定数を走査する** (`Process/Analyze.lean:186`)

   ```lean
   for (name, cinfo) in env.constants do
     let some modidx := env.getModuleIdxFor? name | unreachable!
     if !relevantModules.contains moduleName then continue
   ```

   1 モジュールを抽出する場合でも、Mathlib 依存プロジェクトでは **49 万定数**を走査して
   数十件だけ処理する。走査自体は 0.18 秒と安いが、コストは closure サイズに比例して増える。

2. **`collectTactics` がモジュールごとに全タクティクを列挙する** (`Analyze.lean:133`)

   `getAllModuleDocs` は対象モジュールごとに `Elab.Tactic.Doc.allTacticDocs` を呼ぶ。
   単発では 10〜40 ms で見えないが、バッチ化すると O(モジュール数 × 全タクティク数) として
   顕在化する (→ §4.3 で 16.37 秒、バッチ総時間の 36%)。

3. **`fromDb` の後段はモジュール数に比例した固定コストを毎回払う**

   - `htmlOutputIndex` は `declarations/` 配下の **全 `.bmp` をディスクから読み直す** (`Output.lean:205`)
   - `collectBackrefs` は全 `backrefs-*.json` を読む
   - `updateNavbarFromDisk` は `doc/` 配下の **全 HTML を再帰スキャン**する
   - `headerData` も全 `.bmp` を読む

   つまり「1 モジュールだけ変更」しても、この 4 つは全モジュール規模で走る設計になっている。

---

## 3. 計測方法

doc-gen4 に計装を入れた。環境変数 `DOCGEN_TIMING=<path>` が設定されているときだけ、
各フェーズの実測時間を JSONL で追記する (無効時はゼロコスト)。

- 追加: `DocGen4/Timing.lean` (`emit` / `timed` / `timed'`)
- 計装点: `Main.lean` (single / genCore / fromDb / headerData の各段)、
  `DocGen4/Load.lean` (initSearchPath / importModules / process)、
  `DocGen4/Process/Analyze.lean` (getAllModuleDocs / 定数ループ / ソート、
  走査件数・該当件数・`ofConstant` 累積時間つき)、
  `DocGen4/Output.lean` (HTML タスクごとの DB ロード / レンダ / 書き込み、インデックス各段)
- 追加コマンド: `doc-gen4 batch` — `single` と同じ処理を**複数モジュール 1 プロセス**で行う (方式B の測定用)

並列プロセスが同一ファイルに追記するため、各レコードは PID を持つ。
集計は `docs/doc-gen-bench/analyze.ts`。

パッチ内容は `docs/doc-gen-bench/doc-gen4-instrumentation.patch` に保存してある。

---

## 4. 実測結果

### 4.1 最小ケース: Lean core のみ (end-to-end)

`InformationTheory.Meta.EntryPoint` は `import Lean` だけの 1 モジュール。
これを `lake build InformationTheory.Meta.EntryPoint:docs` でドキュメント化した。
= 構想文書でいう「A. Lean core だけの小規模プロジェクト」。

**wall 265 秒 / ピーク RSS 2.23 GB**

| フェーズ | プロセス | wall | 内訳 |
|---|---|---|---|
| `genCore Lean` | 1 | **239.7s** | import 3.0s / modDocs 9.6s / **定数ループ 225.1s** / DB 1.85s |
| `genCore Std` | 1 | 71.1s | import 0.88s / modDocs 2.13s / 定数ループ 65.5s / DB 2.38s |
| `genCore Init` | 1 | 30.1s | import 0.23s / modDocs 2.26s / 定数ループ 25.7s / DB 1.86s |
| `genCore Lake` | 1 | 7.9s | import 0.40s / modDocs 0.64s / 定数ループ 6.6s / DB 0.19s |
| `single` (対象の 1 モジュール) | 1 | 3.2s | **import 3.15s (97%)** / 解析 0.08s / DB 0.003s |
| `fromDb` | 1 | 18.1s | → §4.4 |

4 つの `genCore` は並列に走るので wall は最長の `Lean` に律速される。

**定数ループの内訳** (= `DocInfo.ofConstant` の累積):

| | 走査した定数 | 該当した定数 | ループ時間 | うち `ofConstant` |
|---|---|---|---|---|
| Lean | 203,906 | 88,115 | 225.1s | 224.4s (**99.7%**) |
| Std | 112,076 | 50,600 | 65.5s | 65.3s |
| Init | 65,197 | 65,197 | 25.7s | 25.6s |

1 宣言あたり **2.55 ms**。この中身は `Info.ofConstantVal` (型の pretty print) と
`computeEquations?` である。後者は `getEqnsFor?` を呼び、**equational lemma を実際に生成する**
(`Process/DefinitionInfo.lean:30`)。ビルド中に

```
WARNING: Failed to calculate equational lemmata for Lean.Meta.Tactic.TryThis.addRewriteSuggestion:
  (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

が出るのは、ここで本物の elaboration が走っている証拠である。

**出力サイズ** (Lean core 2,394 モジュール分):

| | サイズ |
|---|---|
| `api-docs.db` | 129 MB |
| `doc/` (HTML 2,402 ファイル) | 223 MB |
| `doc-data/` | 198 MB |
| 合計 | **550 MB** |

### 4.2 `single` のコスト構造 — import closure サイズへの依存

代表モジュールを直接 `doc-gen4 single` で処理した (逐次、キャッシュ暖機済み)。

| モジュール | closure | total | import | modDocs | 定数ループ | 走査/該当 | DB |
|---|---:|---:|---:|---:|---:|---|---:|
| `Mathlib.Init` | 1,161 | 0.71s | **0.66s** | 0.00s | 0.04s | 123,283 / 6 | 0.00s |
| `Mathlib.Order.Basic` | 1,285 | 1.01s | **0.79s** | 0.01s | 0.21s | 132,336 / 431 | 0.01s |
| `Mathlib.Analysis.SpecialFunctions.Log.Basic` | 3,503 | 7.64s | **7.35s** | 0.02s | 0.26s | 339,540 / 179 | 0.01s |
| `Mathlib.MeasureTheory.Integral.Bochner.Basic` | 4,066 | 3.81s | **3.32s** | 0.03s | 0.45s | 385,778 / 202 | 0.01s |
| `InformationTheory.Shannon.BirkhoffErgodic` | 4,777 | 4.02s | **3.75s** | 0.03s | 0.24s | 429,468 / 65 | 0.01s |
| `InformationTheory` (root) | 6,019 | 5.48s | **5.24s** | 0.04s | 0.18s | 490,037 / 0 | 0.00s |

**import が総時間の 90〜97% を占める。**実際の意味解析は 0.04〜0.45 秒に過ぎない。

`InformationTheory` root に至っては、49 万定数を走査して**該当 0 件** — つまり
5.48 秒かけて何も抽出していない。root モジュールは `import` しかないので当然だが、
現行設計ではこの空振りにも closure 全体のロードが課される。

ピーク RSS も closure に比例する: 720 MB (`Mathlib.Init`) → 3.26 GB (`InformationTheory` root)。
16 GB のマシンでは、8 並列で走らせると 8 × 2〜3 GB = 16〜24 GB となりスワップ域に入る。
**メモリが実効並列度の上限を決めている。**

### 4.3 方式A vs 方式B — 1 プロセスで複数モジュールを抽出する

構想文書の Step 3。`doc-gen4 batch` を追加して同一の 432 モジュール
(`InformationTheory` 全体 + root) を両方式で処理した。

| | プロセス数 | 実測 | 432 モジュール換算 |
|---|---:|---:|---:|
| **方式A**: モジュールごとに 1 プロセス | 112 (実測) | 281.06s | **約 1,084s** |
| **方式B**: 1 プロセスでまとめて | 1 | **47.4s** | **47.4s** |

**約 23 倍。** 方式A の内訳は 281.06 秒中 **251.92 秒 (89.6%) が `importModules`**。

方式B の内訳:

| フェーズ | 時間 | 比率 |
|---|---:|---:|
| `importModules` (1 回だけ) | 12.91s | 28% |
| `getAllModuleDocs` | **16.37s** | **36%** |
| 定数ループ (走査 490,171 / 該当 8,824) | 15.99s | 35% |
| `updateModuleDb` | 0.64s | 1.4% |
| 合計 | 45.93s | |

注目すべきは、バッチ化すると **`getAllModuleDocs` が最大項に浮上する**こと。
これは §2.1 で述べた `collectTactics` の O(モジュール数 × 全タクティク数) が原因で、
1 モジュールずつ処理している限り 10〜40 ms に埋もれて見えない。
新設計では「全タクティクを 1 回列挙してモジュール別に振り分ける」だけで消える。

つまりバッチ化の利得は 23 倍で頭打ちではなく、**この O(n×m) を潰せばさらに縮む**。

### 4.4 `fromDb` (HTML 生成) の内訳

Lean core 2,394 モジュール、wall 18.07 秒。

| フェーズ | 時間 | 比率 |
|---|---:|---:|
| `walCheckpoint` | 0.44s | 2.4% |
| `loadLinkingContext` | 0.32s | 1.8% |
| `getTransitiveImports` | 0.02s | 0.1% |
| **`htmlOutputResultsParallel`** | **16.77s** | **92.8%** |
| `loadAllTactics` | 0.001s | ~0% |
| `htmlOutputIndex` | 0.43s | 2.4% |
| `updateNavbarFromDisk` | 0.02s | 0.1% |

`htmlOutputResultsParallel` は 20 タスクに分割される。全タスクの累積 CPU 78.05 秒の内訳:

| | 累積 CPU | 比率 |
|---|---:|---:|
| DB 接続オープン | 0.22s | 0.3% |
| **モジュールを DB から読む** | **61.23s** | **78.4%** |
| HTML レンダリング | 7.16s | 9.2% |
| HTML 書き込み | 4.05s | 5.2% |
| 検索用 JSON 生成 | 3.32s | 4.3% |
| 検索用 JSON 書き込み | 1.71s | 2.2% |

**HTML 生成の実コストは DB 読み出しであって、レンダリングではない** (9.2%)。
原因は `DB/Read.lean` の `loadModule` が N+1 クエリ構造になっていること: モジュールの
メンバー一覧を 1 クエリで取った後、宣言ごとに `loadDocInfo` を呼び、その中でさらに
引数・属性・宣言範囲・equation を個別のプリペアドステートメントで引いている。
加えて `getContainedNames` は `name_info` × `declaration_ranges` の 4 way 自己結合である。

1 モジュールあたり 32.6 ms CPU。新設計で IR をモジュール単位のファイル (またはブロブ 1 行) に
まとめれば、この 78% はほぼ消える性質のコストである。

### 4.5 増分ビルド

| シナリオ | wall | doc-gen4 の起動 |
|---|---:|---|
| 1 回目 (cold) | 265s | genCore ×4 + single ×1 + fromDb |
| **2 回目 (無変更)** | **2.33s** | **なし** (Lake が全 job を replay) |
| **3 回目 (1 モジュール変更)** | **5.21s** | `single` ×1 のみ (0.86s)。`fromDb` は replay |

Lake のトレース機構は正しく効いており、**無変更なら doc-gen4 は 1 プロセスも起動しない**。
ここは現行実装の明確な強みで、新設計でも同等以上を保証する必要がある。

ただし 3 回目で `fromDb` が再実行されなかった点は注意が必要である。lakefile は
「空のマーカーファイルのトレース変化で再ビルドを誘発する」設計になっているが、
今回はモジュール内容を変更しても HTML 再生成が走らなかった。
**変更が HTML に伝播しない (stale page が残る) 可能性**があり、増分性の正しさは
速度とは別に検証すべき項目である (→ §6 の Q&A で再論)。

### 4.6 フルビルド (InformationTheory + Mathlib 全体)

*(測定中 — 完了後に追記)*

### 4.7 `DISABLE_EQUATIONS` の効果

doc-gen4 には equation lemma の生成を切るスイッチがある (`Analyze.lean:162`)。
方式B (432 モジュールのバッチ抽出) で有無を比較した。

> 注: この 2 本はフルビルドと並行して測ったため、絶対値は §4.3 の単独測定 (47.4s) より
> 2 倍以上遅い。**両者が同一条件下にあるので相対比較のみ有効。**

| | equations あり | `DISABLE_EQUATIONS=1` | 差 |
|---|---:|---:|---:|
| `ofConstant` 累積 | 22.72s | 21.11s | **−7.1%** |
| 定数ループ全体 | 27.51s | 29.80s | (ノイズ) |
| バッチ総時間 | 98.07s | 96.38s | −1.7% |

**InformationTheory では equation の寄与は小さい (意味解析部分で 7%)。**
理由は明快で、このプロジェクトの宣言はほぼ `theorem` であり、
equation lemma が生成されるのは `definition` だけだからである
(`DefinitionInfo.ofDefinitionVal` からしか `computeEquations?` は呼ばれない)。

逆に Lean core (`Init` / `Std`) は definition が支配的で、そこでは
「equational lemmata の計算がヒートビート上限に達した」警告が実際に出る (§4.1)。
**equation のコストは「対象パッケージが定義中心か定理中心か」で大きく変わる**ため、
新設計では常時オフではなく**オプトイン/オプトアウト可能な段階**として設計すべきである。

---

## 5. import closure の分布 (なぜ `single` 方式が破綻するか)

`.lean` ヘッダを解析して、パッケージ内の推移的 import closure サイズを求めた
(`docs/doc-gen-bench/closure-sizes.ts`。Lean 4.31 の `module` / `public import` 構文に対応)。

| パッケージ | モジュール数 | closure 合計 | 平均 | p50 | p90 | 最大 |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 8,169 | **7,375,495** | 903 | 751 | 1,999 | 3,280 |
| Mathlib + InformationTheory | 8,600 | **8,485,717** | 987 | 813 | 2,194 | 3,280 |

これは**パッケージ内**の closure であり、実際にはこれに Lean core (最大 2,259 モジュール) が乗る。
実測 `loadedModules` は 4,777〜6,021 だった。

`single` 方式では、この closure 合計がそのまま「延べモジュールロード回数」になる。
Mathlib + InformationTheory で **述べ 850 万モジュールロード**。
実測の import 単価 (約 0.9 ms/モジュール) を掛けると **約 7,600 秒 (2.1 時間) の CPU 時間**が
環境ロードだけに費やされる計算になる。

一方バッチ方式なら、この項は **1 回分の closure ロード (実測 12.9 秒)** に潰れる。
**これが構想の中心仮説「依存ライブラリの規模から切り離せる」の定量的な根拠である。**

---

## 6. 構想文書「9. 最初に答えるべき技術的質問」への回答

**Q1. Environment のロードは全体時間の何割か**
→ **モジュール単位抽出では 89.6〜97%。** 1 プロセスにまとめると 28% まで下がる (§4.2, §4.3)。
ただし Lean core の `genCore` だけは例外で、そこでは環境ロードは 1.3% にすぎず、意味解析が 94% を占める (§4.1)。
つまり「環境ロードが支配的」なのは *downstream パッケージ*の話であり、
*自パッケージの宣言が多い*ケースでは意味解析が支配的になる。**両方に手を入れる必要がある。**

**Q2. 1 プロセスで複数モジュールを処理するとどれだけ短縮できるか**
→ **同一 432 モジュールで 1,084 秒 → 47.4 秒、約 23 倍** (§4.3)。
仮説は支持された。さらに `collectTactics` の O(n×m) を直せば 47.4 秒のうち 16.4 秒が消える。

**Q3. `DocInfo` 相当の意味解析で最も高価な処理は何か**
→ **`DocInfo.ofConstant`、1 宣言あたり 2.55 ms。**内訳は型の pretty print と
`computeEquations?` (`getEqnsFor?` による equational lemma の生成)。
後者はヒートビート上限に達して警告を出すほど重い (§4.1)。

**Q4. equation 情報を省くとどれだけ速くなるか**
→ **対象パッケージの性質に強く依存する。**InformationTheory (定理中心) では
意味解析部分で 7%、全体で 2% しか効かなかった (§4.7)。equation lemma は `definition` にしか
生成されないため、定理が大半のライブラリでは削っても効果が薄い。
一方 Lean core のような定義中心のコードでは、equation 計算がヒートビート上限に達するほど重い。
**「全体で何割」という単一の数字は存在しない**ので、切り替え可能な段階として設計するのが正しい。

**Q5. 外部リンク解決に必要な依存側データは何か**
→ `fromDb` が使うのは `LinkingContext` の 3 つだけ (`DB.lean:475`):
`moduleNames` / `sourceUrls` (モジュール → ソース URL) / `name2ModIdx` (宣言名 → モジュール)。
Lean core 2,394 モジュールで `name2ModIdx` は **100,535 エントリ**、構築に 0.32 秒。
**依存パッケージについて必要なのは「宣言名 → モジュール名 → URL」の写像だけ**であり、
型・docstring・equation は一切要らない。これは構想 3.1 の「依存は外部参照にする」を
そのまま裏づける (Mathlib の完全な IR を持つ必要がない)。

**Q6. `.olean` hash だけで安全にキャッシュを無効化できるか**
→ 現行 Lake は olean トレースで正しく無変更を検出できている (2 回目 2.33 秒, §4.5)。
ただし olean hash だけでは不足で、少なくとも pretty printer の出力に影響する
**Lean バージョン**と**抽出器バージョン**が必要 (構想 3.4 の設計で正しい)。
さらに現行実装では逆方向の欠陥 — 変更が HTML に伝播しない疑い — が観測されており (§4.5)、
「無効化しすぎない」だけでなく「取りこぼさない」ことの検証が要る。

**Q7. Lean version と extractor version の変更をどう検出するか**
→ 現行 doc-gen4 はこれをキャッシュキーに入れていない (空マーカーファイル方式)。
新設計では IR のヘッダに埋めるべき項目として確定 (構想 3.4 の方針で妥当)。

**Q8. exported name, alias, generated declaration をどの段階で IR へ入れるか**
→ 現行は書き込み時に解決している。`updateModuleDb` が `saveRecursors` で
`.rec` / `.casesOn` / `.recOn` / `.brecOn` を `internal_names` に登録し、
構造体の射影関数も同様に登録する (`DB.lean:598`)。
`Eq.ndrec` / `HEq.ndrec` は名指しの特別扱い。
**この解決を抽出時に済ませておかないと、レンダリング側が環境を必要としてしまう**ため、
IR には解決済みで入れるのが正しい。

**Q9. source location を安定して取得できるか**
→ 取得できている。`findDeclarationRanges?` の結果を `declaration_ranges` テーブルに保存し、
ソース URI は Lake の facet (`srcUri`) が git remote + commit から組み立てて
`single` に引数で渡す。範囲を持たない宣言は `isBlackListed` で除外される
(`Process/DocInfo.lean:155`)。

**Q10. IR を JSON から SQLite やバイナリへ変える必要が出る規模はどこか**
→ 現行 doc-gen4 は既に SQLite であり、そこが**遅い側**になっている (§4.4 で HTML 生成 CPU の 78.4%)。
教訓は「規模が来たら SQLite」ではなく、**アクセスパターンに合わない粒度で SQLite を使うと逆効果**ということ。
doc-gen4 は宣言ごとに行を分割したため、レンダリング時に N+1 クエリで再構築する羽目になっている。
モジュール単位で読んでモジュール単位で書くなら、**モジュール 1 個 = 1 ブロブ**が正しい粒度で、
索引だけを別に持てばよい。

---

## 7. 再現手順

```bash
# 計装を有効にしてビルド (パッチ適用済みの doc-gen4 が前提)
lake build doc-gen4

# end-to-end (Lean core のみ)
DOCGEN_TIMING=$PWD/docs/doc-gen-bench/raw/smoke.jsonl \
  lake build InformationTheory.Meta.EntryPoint:docs

# 単一モジュールのコスト構造
DOCGEN_TIMING=... lake env .lake/packages/doc-gen4/.lake/build/bin/doc-gen4 \
  single --build .lake/build <Module> bench.db "file:///tmp/x"

# 方式B (バッチ)
DOCGEN_TIMING=... lake env .lake/packages/doc-gen4/.lake/build/bin/doc-gen4 \
  batch --build .lake/build bench.db "file:///tmp/x" $(cat docs/doc-gen-bench/raw/it-modules.txt)

# 方式A (逐次 1 プロセス/モジュール)
docs/doc-gen-bench/run-serial.sh

# フルビルド
docs/doc-gen-bench/run-full.sh

# 集計
deno run -A docs/doc-gen-bench/analyze.ts <file.jsonl> [--by-module]
deno run -A docs/doc-gen-bench/closure-sizes.ts .lake/packages/mathlib/Mathlib Mathlib
```
