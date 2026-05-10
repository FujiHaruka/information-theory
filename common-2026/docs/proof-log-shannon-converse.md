# Shannon converse (Phase 4-γ) Lean 形式化 — ボトルネック分析

将来「数学的に類似な定理同士の plumbing を自動化するツール」「証明書面の inequality 方向（DPI 系で `I(X;Y) ≤ I(f(X);Y)` か `I(f(X);Y) ≤ I(X;Y)` か）を事前に静的検証するツール」を作るためのベースライン記録。Shannon ムーンショット計画 (`docs/shannon-moonshot-plan.md`) の Phase 4-γ を、Phase 4-α (DPI) + Phase 4-β (bridge) + Phase 3 (Fano Measure 版) の組み合わせで 1 セッションで完走した記録。

**定量データ**: [docs/metrics/shannon-converse.metrics.md](metrics/shannon-converse.metrics.md)

## 0. 対象問題と成果物

教科書的な single-shot 通信路符号化定理の逆 (Cover & Thomas Theorem 8.9.1 の measure-theoretic 形)：

```
Msg : Ω → M (uniform on |M| ≥ 2)、Yo : Ω → Y、decoder : Y → M、
Pe = μ {Msg ≠ decoder ∘ Yo} のとき、
log |M| ≤ I(Msg; Yo).toReal + h(Pe) + Pe · log(|M| − 1)
```

成果物:

- `Common2026/Shannon/Converse.lean` — 124 行、0 errors / 0 sorry
  - 主定理: `shannon_converse_single_shot`
  - 補助補題 (private): `entropy_of_uniform_msg : entropy μ Msg = log |M|`
- `Common2026.lean` に `import Common2026.Shannon.Converse` を追記

`lake env lean Common2026/Shannon/Converse.lean` silent (上流 `Bridge.lean` 由来の `unusedSectionVars` 警告のみ)、`lake build Common2026.Shannon.Converse` 通過。

## 1. 問題のキャラクター

「**plumbing 層の組み合わせ**」型。新規補題は `entropy_of_uniform_msg` (20 行) のみで、本体 50 行は既存補題の代入とチェーン化に終始する。Phase 4-α (DPI) + Phase 4-β (bridge) + Phase 3 (Fano Measure 版) が積み上がっていればパッと出る、という設計予測がそのまま実現した。

過去のフェーズとの規模感比較 (proof-log と最終ファイルの行数から):

| Phase | 主要ファイル | 行数 | 新規補題の中核 | 性格 |
|---|---|---|---|---|
| Phase 3 (Fano Measure) | `Common2026/Fano/Measure.lean` | 数百行 | `fano_inequality_measure_theoretic` | 測度論経由の重実装 |
| Phase 4-α (DPI) | `Common2026/Shannon/DPI.lean` | 168 行 | `mutualInfo_le_of_postprocess` | klDiv の DPI 接続 |
| Phase 4-β (bridge) | `Common2026/Shannon/Bridge.lean` | 588 行 | `mutualInfo_eq_entropy_sub_condEntropy` | KL ↔ entropy − condEntropy 同値 |
| **Phase 4-γ (本回)** | `Common2026/Shannon/Converse.lean` | **124 行** | (組み合わせのみ) | **plumbing** |

## 2. 数学的方針

主定理の証明は次のチェーンで尽きる：

```
log |M|
  = entropy μ Msg                                         -- helper: uniform Msg ⇒ entropy = log|M|
  = (mutualInfo μ Msg (decoder ∘ Yo)).toReal
      + condEntropy μ Msg (decoder ∘ Yo)                  -- Phase 4-β bridge を整理
  ≤ (mutualInfo μ Msg Yo).toReal
      + condEntropy μ Msg (decoder ∘ Yo)                  -- Phase 4-α DPI、ENNReal → ℝ にリフト
  ≤ (mutualInfo μ Msg Yo).toReal
      + binEntropy(Pe) + Pe · log(|M| − 1)                -- Phase 3 Fano (decoder = id : M → M)
```

各 `≤ / =` を `have` で立てて最後に `linarith` で閉じる、という素直な calc 構造。

### 設計判断: encoder を引数から落とした

**計画書 (`docs/shannon-moonshot-plan.md` Phase 4-γ) は encoder 付き版**を想定していた:

```
shannon_converse_single_shot
  (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M) :
  log |M| ≤ I(encoder ∘ Msg; Yo).toReal + h(Pe) + Pe · log(|M| − 1)
```

しかしこれは**そのままでは Phase 4-α DPI から導けない**。Phase 4-α DPI (`mutualInfo_le_of_postprocess`) は `f : Y → Z` で前処理側を縮める方向、すなわち

```
mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo
```

を返す。これを「`encoder ∘ Msg` を増幅する側」に使うと逆方向 `I(encoder ∘ Msg; Yo) ≤ I(Msg; Yo)` が得られるだけで、計画の不等式 `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` は成立しない（一般には `Msg → encoder ∘ Msg → Yo` の Markov 仮定を別途必要とする、Cover & Thomas 8.6 のあのチェーン）。

→ **encoder を引数から削除し、`I(Msg; Yo)` 版だけを書いた**。docstring に「encoder 版は injective encoder の系として後付け可能」と明記。これは plan to code の差分として最大の判断。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ (loogle) | 所要試行 | 見つかった場所 / 結果 |
|---|---|---|---|
| `Measure.count {x} = 1` | `MeasureTheory.Measure.count, _ = 1` → `MeasureTheory.Measure.count {_}` | 2 回 | `Mathlib.MeasureTheory.Measure.Count: Measure.count_singleton` |
| `Real.negMulLog` の展開 | (検索なし、Phase 4-β Bridge.lean で既知) | 0 回 | `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` |
| `Real.log_inv : log a⁻¹ = -log a` | (検索なし、定常知識) | 0 回 | `Mathlib.Analysis.SpecialFunctions.Log.Basic` |
| `ENNReal.toReal_mono : b ≠ ∞ → a ≤ b → a.toReal ≤ b.toReal` | (検索なし、定常知識) | 0 回 | `Mathlib.Data.ENNReal.Real` |

### 「Mathlib に無かった」もの

このセッションでは **無し**。すべて既存補題と定常知識で組めた。本フェーズの目的が「plumbing で完結する」設計だったので、新規補題の探索コストは構造的にゼロ近傍。

## 4. 試行錯誤と後戻り

### 4.1 設計フェーズ: encoder 版が DPI 方向と整合しない

**症状**: 計画書の Phase 4-γ 節をそのままコードに落とそうとして、`mutualInfo_le_of_postprocess` の戻り値方向と計画の不等式方向が逆であることに気付いた。

**原因**: 計画書は教科書 (Cover & Thomas) の Markov chain 形 `Msg → X → Y → M_hat` を前提に `I(M; Y) ≤ I(X; Y)` を素朴にコピーしていた。だが Phase 4-α DPI は Markov 仮定なしの確率測度版で、得られるのは postprocess 方向 `I(Xs; f∘Yo) ≤ I(Xs; Yo)` のみ。encoder 側の不等式 `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` は得られない。

**抜け方**: encoder を引数から消し、定式化を `I(Msg; Yo)` 直接版に変える判断を docstring に明記して採用。injective encoder の系として後付け可能と書いた。

**教訓**: 
- 計画書のスケッチ式が Mathlib 既存補題の方向と整合するか、**実装直前に有向グラフで照合する**工程を別建てにすべき。今回は「計画 → Write」の直前で気付いたので 1 回の docstring 修正で済んだが、Write 後に気付いていたら全面書き直しになっていた
- ツール仕様への示唆: 「**inequality 方向の静的検証**」。ある計画 Lean 命題の RHS と LHS を、利用予定補題の戻り型と照合し、方向が整合するかを diagnostic にする。「Cover & Thomas 風の DPI を書いてあるが、Mathlib の `mutualInfo_le_of_postprocess` は逆方向」と即時警告できる

### 4.2 `lake` バイナリが PATH に無い

**症状**: 最初の `lake env lean Common2026/Shannon/Converse.lean` が `Exit code 127: zsh: command not found: lake` で失敗。

**原因**: zsh のサブシェルが `~/.zshrc` を読まない構成で、`elan` の PATH 追記が効いていなかった。

**抜け方**: `which lake || ls ~/.elan/bin/` でバイナリ位置を確認、以降 `/Users/haruka/.elan/bin/lake env lean ...` を絶対パスで叩いた。

**教訓**: 
- このプロジェクトの fresh セッションで `lake` 直叩きは信頼できない。**毎回 `which lake` する代わりに、絶対パス `~/.elan/bin/lake` を最初から使うか、またはセッション冒頭で 1 回 `source ~/.profile` する**べき
- ツール仕様への示唆: Claude Code のセッション初期化フックで `~/.elan/bin` を PATH に明示的に足す。CLAUDE.md レベルの注意書きより、ハーネス側でやれることなら確実

### 4.3 上流 `Bridge.lean` の `.olean` が空でビルドエラー

**症状**: PATH 修正後の最初の `lake env lean Common2026/Shannon/Converse.lean` が

```
error: object file '.../Bridge.olean' of module Common2026.Shannon.Bridge does not exist
```

で失敗。

**原因**: 前回セッション (Phase 4-β 完成セッション) で `Bridge.lean` を書いた直後にビルドが走らずコミットされ、ローカルの `.lake/build/` には `.olean` が無い状態だった。`lake env lean` は依存 `.olean` を探すだけで再ビルドしない。

**抜け方**: `lake build Common2026.Shannon.Bridge` を 1 回挟み、再度 `lake env lean Common2026/Shannon/Converse.lean` で silent。

**教訓**: 
- これは Phase 1 の proof-log でも記録した「LSP shows stale errors after upstream edits」の親戚。**git pull / セッション開始時に「直近編集された上流 `.lean` の `.olean` 存在を確認する」プリチェックがあれば事故を未然に防げる**
- ツール仕様への示唆: 「`.olean` 不在 / mtime 古い」を LSP / `lake env lean` 失敗の前に診断するヘルパ。CLAUDE.md に書いてあっても **fresh セッションでは忘れる** (今回の自分も初手で踏んだ)

### 4.4 `entropy_of_uniform_msg` で `[DecidableEq M]` が unused

**症状**: helper を埋めた後、`unusedSectionVars` linter が `[DecidableEq M]` は使われていないと警告。

**原因**: `entropy μ Msg` の和は `Fintype M` 由来の `Finset.univ` を取るだけで `DecidableEq` は不要。一方主定理 `shannon_converse_single_shot` は `decoder = id : M → M` を Fano に渡すときに比較が要るので `DecidableEq` を要求する。`variable` 宣言で全体に `[DecidableEq M]` を付けていたために helper だけ余ってしまう構図。

**抜け方**: `omit [DecidableEq M] in private lemma entropy_of_uniform_msg ...` で helper だけ instance を落とす。Phase 4-β Bridge.lean で同パターン (3 回) があり、参考にした。

**教訓**: 
- `variable [Inst]` を付ける単位はファイル全体ではなく **「使う補題の集合」** で考える。helper を別のセクションに切り出して別 variable 宣言する設計もありうる。今回は 1 補題なので `omit ... in` で十分
- ツール仕様への示唆: `[Inst]` の必要性を補題ごとに静的解析して、不要な instance を `omit ... in` 形に自動 lint で提案する

## 5. ボトルネックではなかったもの

- **新規補題探索**: 今回は構造的にゼロ。Phase 4-α / 4-β / Phase 3 の積み上げが効いている。loogle 1 件 × 2 クエリで `Measure.count_singleton` を確認しただけ
- **proof body の試行錯誤**: 主定理の本体 (50 行) は `set Pe`, `have h_entropy_log`, `have h_bridge`, `have h_dpi_ennreal`, `have h_dpi`, `have h_Pe_eq := rfl`, `have h_fano`, `linarith` の流れで書き下し 1 回で通過。中間で「タクティクが効かない」「型が合わない」リトライは無し
- **`errorProb μ Msg (decoder ∘ Yo) (id : M → M) = Pe` の同値**: `id ∘` と `(f ∘ g) ω = f (g ω)` がいずれも definitional reduction なので `rfl` 1 行。Phase 3 Fano の引数を再構成して `Pe` と一致させる作業を「面倒な等式変形が要りそう」と身構えていたが、Lean の reducible 性で完全に消えた
- **数学的アイデア**: 教科書的な Shannon converse の証明そのまま。新規発想は不要
- **コンテキスト長**: 1M context、proof body 50 行 + helper 20 行 + 既存ファイル参照、何ら圧迫感なし
- **ビルド時間**: `lake build Common2026.Shannon.Bridge` は 4 秒、`lake build Common2026.Shannon.Converse` は数秒。Phase 4-β を warm 状態で持ち越せていた

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **inequality 方向の静的検証** (§4.1) — 計画 Lean 命題の RHS−LHS と利用予定補題の戻り方向を照合し、不整合を Write 前に警告 | 計画 → 実装の差分判断 (今回 1 回、docstring 修正で済んだが計画段階で見つけられれば 0 回) |
| 高 | **`.olean` 鮮度診断** (§4.3) — セッション冒頭または `lake env lean` 失敗時に「直近編集された上流ファイルの `.olean` が古い／無い」を即時提示 | Phase 1 proof-log でも記録した recurring 問題。今回 1 ラウンドトリップ |
| 中 | **Lean 環境の PATH 自動 bootstrap** (§4.2) — Claude Code の起動時フックで `~/.elan/bin` を PATH に追加 | 1 回の `Exit code 127` ラウンドトリップ。低コストだが頻発 |
| 中 | **`variable [Inst]` の utilization lint** (§4.4) — 各補題で `Inst` が実際に使われたかを静的解析、不要なら `omit ... in` を提案 | 1 回の Edit 修正、毎フェーズで 1〜3 件発生 |
| 低 | **計画書の `I(...)` 不等式記号と Mathlib 補題の方向対応辞書** | §4.1 の根本解決。ただし `inequality 方向の静的検証` のサブ機能でカバーされる |

特に **§4.1 の inequality 方向検証** は Phase 4-γ 固有でなく、Cover & Thomas 風の情報量不等式群を Lean に移植する将来の作業すべてに効く。Phase 5 以降の仕事で恩恵が出る蓋然性が高い。

## 7. 補足

### 実際に打った loogle クエリ

```
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "MeasureTheory.Measure.count, _ = 1"
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "MeasureTheory.Measure.count {_}"
```

### 主定理の最終形 (シグネチャ)

```lean
theorem shannon_converse_single_shot
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ Msg Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

### 採らなかった代替案

- **encoder 付き版を Markov 仮定込みで書く**: 計画書当初の形。`Msg → encoder ∘ Msg → Yo` Markov 仮定を `mutualInfo μ Msg Yo = mutualInfo μ (encoder ∘ Msg) Yo` の補題で別途証明し、それを bridge する案。Markov 仮定の measure 版定式化と DPI からの取り出しに 100〜200 行追加が見込まれ、ムーンショット成立 (sorry ゼロで通る) を遅らせる。Phase 5 で「injective encoder の系として」追加する余地として残した
- **`mutualInfo` を ENNReal のまま扱う bound**: `hMI_finite` 仮定を回避できる。ただし `binEntropy` と `Pe · log(|M|-1)` が ℝ 値なので、結局 toReal を一度通す必要があり、有限性は何処かで要請せざるを得ない。主定理の仮定として 1 行で片付けるのが最も簡潔
