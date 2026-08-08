# N17 — 単位 B (3 レート `Thm7(W)` の領域層) の受け皿昇格 + gateway atom (中核 8)

**Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 (N17 起票ブロック) /
**配分決定の SoT** = 同 plan §7 判断ログ 12 (⚠ **cap 20 → 23 の延長・判断ログ 5 のテスト可能な線との関係・
引き受けたリスク・カウンタの実測はそちら。本書は複製しない**) /
**単位の SoT** = 子 plan [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md)
§3.2 (単位 B の (i)–(iv) + 撤退) / §4 (設計軸 (a) 決着済・(b) 未決) / §6 撤退ライン **R-2** / **R-4** /
**員数と型検査の SoT** = facts [`bc-facts.md`](bc-facts.md) `## N2 (T3c)` の **N2-c** / **N2-d** / **N2-l** /
**出発点** = 型検査 probe `docs/shannon/probes/t3c-n2/r1-thm7-region.lean` (**167 行 / 0 sorry**)

**leg 冒頭宣言 (N17)** (⚠ 親 plan §5.1 の N17 起票ブロックからの逐語コピー): 側 = 形式化債務 / 動かすもの =
子 plan の単位 B (3 レート `Thm7(W)` の領域層) の受け皿を層 3 に実在させ、gateway atom
(中核 8 = 合併レベルの閉性を `closure` 無しで出す) の実際の難度を初めて機械で測る

> ⚠⚠ **本書の §0 と §1 は着手前に凍結されており、実行 leg / 監査は 1 文字も書き換えてはならない**
> (親 plan §4.4-2 の義務。r19 / r20 で確立した作法 = **事後に見立てを直して当てにいく経路を構造的に塞ぐ**)。
> ⚠ **見立ての当たり外れ / 反証条件の発火状況は §4 に別途書く** — **§0 / §1 は動かさず、効きは着地側に書く**。
> **凍結の機械確認**: 起票 commit と現行の同区間 (`## 0.` 行から `## 2.` の直前まで) の md5 一致で見る。
> ⚠⚠ **空行を落として正規化してから md5 を取る** — **生の `grep -v` は末尾空行で偽陽性を出す**
> (r20 の監査が実測)。
>
> ⚠⚠ **本 leg は §0 のゴールの Lean 側には届かない**。親 §6-5 は既に「**形式化債務は残る形式化枠 2 leg に
> 収まらない**」と判定済であり (親 §7 判断ログ 3 / facts N2-a)、⟹ **N17 / N18 でそこへ届く見込みは無い**。
> ⚠⚠ **本 leg の成果を「§0 に近づいた」と書かない** (親 §0.1-2)。⚠ **同時に「だから走らせる意味が無い」とも
> 書かない** — 走らせる意味は **単位 B の受け皿を層 3 に実在させ、中核 8 の実際の難度を初めて機械で測ること**
> である (⚠ **中核 8–10 は 0/3 で、その行数は 1 行も測れていない**)。

---

## 0. 着手前の見立てと「締める / 緩める」の明記 (§4.4 の義務。⚠ 事後に書き換えない)

⚠ **本節は昇格先ファイルを 1 行も書く前に書いた**。以下は紙と `rg` / `loogle` / `dep_consumers.sh` の上の
見立てであり、**`lake env lean` に掛けた結果は §3 に別途書く** (一致しなかったものは一致しなかったと書く)。
⚠ **見立ては当たりにいくものではなく較正の材料である**。
⚠⚠ **本節に壁宣言は 1 つも無い** — 「中核 8 は Mathlib に無い」型の判断は **機械検証を経た実行 leg の仕事**で
あり (CLAUDE.md の wall 宣言規約: loogle 0 件は必要条件であって十分条件ではない / 結論形での二段検索 /
in-project を `rg` / 名指しした候補は compiler に否定させる)、**起票段階では書かない**。

### 見立て A (**締める**) — 受け皿の昇格は「167 行の移送」ではない

理由 = probe は `InformationTheory/` から 1 行も import されていない測定専用物であり、昇格は次を**新たに**負う:
**(a)** `InformationTheory.lean` への import 行の登録 / **(b)** `docs/rules/` の docstring + 命名規約
(probe の `namespace ProbeThm7` / `PROBE — not an in-project asset` ヘッダは使えない) / **(c)** style gate /
**(d)** 新規 `sorry` を入れるなら honesty gate / **(e)** ⚠⚠ **型検査が保証しない 3 件の転記照合** —
**17 スロットと 13 変数の対応** / **入れ子の向き** / **上限値が `Thm7` のものであること** (子 §3.2 (iii) /
facts N2-c。⚠ **転記義務は 1 ミリも縮まない**)。

**着手前の 1 行反証 (§4.4-1 の義務。⚠ 締める側は着手前に機械へ掛ける)** = ⭐ **逆に縮む部分が 1 つ見つかった** —
probe の局所 def `miR` / `cmiR` は **in-project に既に在る**: `mutualInfoReal`
(`InformationTheory/Shannon/BroadcastChannel/OuterBoundTransport.lean:149`) と `condMutualInfoReal`
(同 `:154`)、しかも **本 relay の N8 が置いたもの**である (CLAUDE.md「In-repo asset search」が名指しする形を
1 件回避した) ⟹ **新規 def は 2 本減りうる**。
⚠ **ただし署名が違う** — `condMutualInfoReal` は `[IsFiniteMeasure μ]` を **instance 引数**で取るが probe の
`cmiR` は **明示引数 `(hν : IsFiniteMeasure ν)`** で取る。合併の内側が `⋃ (ν : Measure _) (hν : IsFiniteMeasure ν)`
と束ねている以上、**消費できるかは束縛子の設計に依存する** (見立て B / C / D と連動) ⟹
⚠⚠ **既存 2 本の署名を先回りで変えて解決しない** (波及の実測は §1-(b) の反証条件 3)。
⟹ **A は「昇格は移送ではない」の形では生きるが、「行数が増える一方だ」の形では成り立たない**。

### 見立て B (**緩める**) — 型クラス列の不整合は**受け皿の昇格を止めない**

理由 = 子 §3.2 (iv) は「領域 def には `[TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]` が追加で
要る ⟹ **既存 BC 家系 11 本と型クラス列が揃わない**」と書くが、**その 3 個を要求しているのは
`CompactSpace (ProbabilityMeasure α)` を合成する段**である —
`Mathlib/MeasureTheory/Measure/Prokhorov.lean:65` の節変数
`{E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]` +
同 `:167` の `instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E)` (⚠ **2026-08-09 に逐語確認**)。
⟹ ⚠ **要求元は中核 8 の道具であって領域 def そのものではない**。現に probe は
`[Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]` (β₁ / β₂ も同型) の**4 型クラスだけ**で
**167 行 / 0 sorry を通している** (facts N2-c) ⟹ **昇格は既存 11 本の署名を 1 文字も変えずに新規ファイルへ載る**。
⚠ **この 4 型クラス列は既存 2 家系の列の和である** — `bcOuterRegionUV` (`OuterBoundUV/Region.lean:425`) は
`[MeasurableSpace] [StandardBorelSpace] [Nonempty]`、`martonRegionUnionBounded`
(`Marton/RegionCardinality.lean:270`) は `[Fintype] [MeasurableSpace]` (在庫 §3.3 の逐語 `#check` 出力)。

**殺す道具 (§4.4-2 の義務どおり着手前に決めた。⚠ 形式化 leg ゆえ §4.5 の道具 3 = 明示 witness の直接評価を
機械へ読み替える)** = **`lake env lean <昇格先ファイル>` 1 本**。probe の型クラス列のまま昇格して**無出力**なら
B は生存、`failed to synthesize instance` が 1 件でも出たら **B は死ぬ**。
⚠⚠ **`rg` で「既存署名に `TopologicalSpace` が 0 件」を再確認しても B を支えない** — それは N2 §3.2 の D3 が
既に書いていることであり、**B の主張は「def が 3 個を要求しない」の側**である ⟹ **判定はコンパイラが下す**。
⚠ **B は緩める側ゆえ §4.4 の非対称性が効く** — 外れると**その見立ての上に leg を組んでから死ぬ**。

### 見立て C (**締める**) — gateway atom (中核 8) は**現行の束縛子のままでは通らない**

理由 3 点 (⚠ **どれも 2026-08-09 に機械で現物を当てた。壁判定ではない**):

1. **最も近い in-project 先例は閉性を「定義で」得ている** — `bcOuterRegionUV_isClosed`
   (`OuterBoundUV/Region.lean:431`) の本体は **`isClosed_closure` の 1 語**で、`bcOuterRegionUV` の def が
   `closure (⋃ …)` を取っているから閉じているだけである。⚠ 同 def の docstring は逐語で
   *a union of closed half-plane intersections need not be closed* と**閉包を取る理由**を書いている。
   ⚠⚠ **in-project の領域 def 11 本はすべて `closure (⋃ …)`** (在庫
   [`bc-t3c-c2-inventory.md`](bc-t3c-c2-inventory.md) §3.3) ⟹ **合併レベルの閉性を `closure` 無しで出した
   先例は 0 本**である。
2. **`isClosed_iUnion` は別物である** — `Mathlib/Topology/AlexandrovDiscrete.lean:77` にあり、節変数
   `[AlexandrovDiscrete α]` の下にある (子 §3.2 (iv) の記述を逐語で再確認した)。
3. **射影ルートの前提が現行の束縛子には付かない** — `isClosedMap_fst_of_compactSpace` は添字空間の
   `CompactSpace` を要求するが、probe の内側の合併は **`(ν : Measure (Amb …)) (hν : IsFiniteMeasure ν)`** で
   束ねており `ProbabilityMeasure` ではない ⟹ **Prokhorov のコンパクト性は付かない**。⚠ **その束縛子が
   総質量を固定することは Lean で証明されていない** (facts **N2-l (5)** が名指した未閉項)。

**着手前の 1 行反証 (§4.4-1 の義務)** = ⚠⚠ **束縛子は def の側で変えられる**。CLAUDE.md
「Mathlib-shape-driven Definitions」は「**支配する Mathlib 補題の結論形に合わせて def を選び直す**」ことを
第一選択に定めており、内側の合併を `(ν : ProbabilityMeasure (Amb …))` へ取り替えるのは **証明ではなく def の
設計**である ⟹ **C は無条件には成り立たない**。
⟹ **C が生きるのは「probe の束縛子をそのまま昇格した場合」に限る** ⟹ ⭐ **実行 leg は束縛子の取り替えを
先に試す** (⚠ **取り替えると facts N2-c の「`(ν : Measure _)` の下線を 1 つ戻すと elaborate が終わらなくなる」
ハザードの近傍に入る** — ⚠ **係数を合併の外で解決する def を消さないこと**)。

### 見立て D (**緩める**) — 中核 8 の 3 段のうち**内側 `kv` 段は既製品で閉じる**

理由 = `thm7Region` の入れ子は `⋃_p ⋂_{kJ,T_J} ⋃_{kv,ν}` であり、**合併は 2 か所・交叉は 1 か所**である
⟹ ⚠ **中核 8 は 1 本の補題ではなく、添字空間ごとに別の道具を要する 3 段に割れる**。
そのうち **内側の `kv` は基数境界で有限に落ちる** — probe は
`⋃ (kv : AuxIdx → ℕ) (_ : ∀ i, kv i < thm7Cap α i)` と**束縛つき合併**の形で書いており、
`AuxIdx = Fin 3 × Fin 3` は有限、`thm7Cap α i = Fintype.card α + 6` (`i.2 = 2` のとき) / `+ 1` は有限値
⟹ **添字集合 `{kv | ∀ i, kv i < thm7Cap α i}` は有限**である。
⟹ **既製品が形ごと当たる公算がある**: `Set.Finite.isClosed_biUnion {s : Set α} {f : α → Set X} (hs : s.Finite)
(h : ∀ i ∈ s, IsClosed (f i)) : IsClosed (⋃ i ∈ s, f i)` (`Mathlib/Topology/Basic.lean:171`、節 `[TopologicalSpace X]`)
/ `isClosed_iUnion_of_finite [Finite ι] {s : ι → Set X} (h : ∀ i, IsClosed (s i)) : IsClosed (⋃ i, s i)`
(同 `:181`)。⚠ **2 本とも 2026-08-09 に逐語確認した** (⚠ **`isClosed_iUnion` (見立て C-2) とは別物である**)。
⟹ **「3 段すべてが未解決」ではない**。

**殺す道具 (§4.4-2 の義務どおり着手前に決めた)** = **`lake env lean` 1 本 + loogle の逐語照合**。
`{kv : AuxIdx → ℕ | ∀ i, kv i < thm7Cap α i}` の `Set.Finite` を出す 1 行を書いて通れば D は生存、
**通らない / `Set.pi` 系の橋が自前になる**なら D は死ぬ。
⚠⚠ **「有限だから閉じる」は各ファイバの閉性を前提にしている** — ⚠ **その前提 (`thm7RegionOfLaw ν hν` が
閉集合であること) は本 leg では未検証であり、D は「`kv` の合併段だけ」を緩める見立てである**
(⚠ **ファイバの閉性ごと緩めたと読まない**)。

### ⚠ 併記する 3 点 (どれか 1 つだけを書かない)

1. ⚠⚠ **本 leg は形式化債務であって `Thm7 ⊋ C` の材料を出す leg ではない** — **どちらに転んでも出ない。
   排除もされない**。⚠ **レート領域の包含についても 1 文字も言わない**。
2. ⚠⚠ **§6-5 は既に「収まらない」と判定済**ゆえ **N17 / N18 で §0 の Lean 側には届かない** ⟹
   ⚠⚠ **成果を「§0 に近づいた」と書かない** (親 §0.1-2)。
3. ⚠ **同時に「だから走らせる意味が無い」とも書かない** — 意味は **単位 B の受け皿を層 3 に実在させ、
   中核 8 の実際の難度を初めて機械で測ること**である。⚠ **測らなければ中核 8–10 は 0/3 のまま
   「行数が 1 行も測れていない」状態が続く**。

---

## 1. 反証条件 (§4.4-2 の義務。⚠ 着手前に書いてある。事後に書き換えない)

### (a) 継承分 — ⚠⚠ **無い。ただし継承しない理由を書く**

⚠ **本 leg は継承した反証条件を 1 本も持たない**。近傍の 3 組は**対象が違う**:

- [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2 の 3 本 / [`bc-t3c-n9-cone-gate.md`](bc-t3c-n9-cone-gate.md)
  §4.2 の 3 本 = いずれも **`(C2)` 側 ([probc] 上の判定) の分**である ⟹ **本 leg は評価しない**。
  ⚠ **「不発火」とも書かない** (評価していないものを不発火と書かない)。⚠⚠ **複製も書き換えもしない**。
- 子 plan §6 の **R-2 / R-3 / R-4** は**反証条件ではなく撤退ライン**である ⟹ 継承ではなく**そのまま効く**
  (⚠ とくに **R-4 = 「`R₀=0` スライスの Π01 性を『従う』で埋めた記述を見つけたら即座に差し戻す」は
  判定ではなく禁止条項の違反**である)。

### (b) 新規 3 本 (⚠ **発火を判定する道具を条件ごとに名指す**。⚠⚠ 「うまくいかなかったら」型は不可)

1. **受け皿が昇格先で 0 error に落ちない** ⟹ ⚠ **中核 8 に手を付けない**。
   **条件文** = probe の 167 行を `InformationTheory/` 配下の新規ファイルへ移し、import を実プロジェクト版へ
   張り替えたとき、`lake env lean` が **error を 1 件でも出す** (⚠ **`sorry` warning は error ではない**)、
   **または elaborate が終わらない**とき発火する (⚠ **後者の実例が facts N2-c にある** —
   `(ν : Measure _)` の下線を 1 つ戻すと 2000000 heartbeats でも落ちなかった)。
   **発火したときの処置** = ⚠⚠ **中核 8 へ進まない**。受け皿の 0 error 復帰が本 leg の全量になり、
   **その事実をそのまま §4 に書く**。⚠ **「probe で通っているのだから昇格も通る」と書かない** —
   **import 閉包も型クラス列も namespace も別物である**。
   **判定に使う道具** = **`lake env lean <昇格先ファイル>`** (無出力 = clean)。

2. **gateway atom (中核 8) が 3 段のいずれかで止まる** ⟹ ⚠ **その段だけを
   `sorry` + `@residual(plan:bc-computable-region-formalization)` で残して type-check done で着地する**
   (子 §3.2 撤退 / R-2 の規定そのもの)。
   **条件文** = 見立て C の 1 行反証 (**束縛子を `ProbabilityMeasure` へ取り替える**) を**先に試したうえで**なお
   `IsClosed (thm7Region W)` が **`closure` を付けずに**出ないとき発火する。
   ⚠⚠ **発火しても「壁」と書かない** — `@residual(wall:<name>)` を立てるには CLAUDE.md の wall 宣言規約
   (loogle 0 件は必要条件であって十分条件ではない / **結論形での二段検索** / **in-project を `rg`** /
   **名指しした候補は compiler に否定させる**) を**全部**通す必要があり、**本 leg でそこまで通せなければ
   `@residual(plan:bc-computable-region-formalization)` であって `@residual(wall:…)` ではない**。
   ⚠ **子 §1.1 のとおり現時点で ⓓ (壁) は 0 件であり、壁の主張はまだ 1 件も無い**。
   **判定に使う道具** = **`lake env lean`** + **loogle の結論形検索** (`|- IsClosed _` 形。⚠ **裸の識別子検索で
   終わらせない**) + **`rg` の in-project 検索** (⚠ **loogle は Mathlib しか見ない**)。

3. **昇格が既存宣言の署名変更を要求する** ⟹ ⚠⚠ **その場で止めて独立に起票へ回す** (子 §3.3 撤退 / **R-3 の
   精神**)。
   **条件文** = 昇格先ファイルが `mutualInfoReal` (`OuterBoundTransport.lean:149`) / `condMutualInfoReal`
   (同 `:154`) を消費しようとして、**`[IsFiniteMeasure μ]` の instance 引数を明示引数へ変える**等の署名工事が
   要ると判明したとき発火する。
   ⭐ **波及は起票時に実測済** (`scripts/dep_consumers.sh`、2026-08-09。⚠ **記憶や `rg` の近似ではない**):

   | 対象 | 直接消費者 | 推移閉包 |
   |---|---|---|
   | `mutualInfoReal` (`OuterBoundTransport.lean:149`) | **43 decl / 1 file** | **45 decl / 1 file** |
   | `condMutualInfoReal` (同 `:154`) | **38 decl / 1 file** | **40 decl / 1 file** |

   **発火したときの処置** = **既存 2 本は 1 文字も変えない**。**probe と同じ局所 def を昇格先ファイル内に置く**
   か、**束縛子の設計を変えて回避する**かのどちらかで、⚠ **どちらを選んだかを §4 に書く**。
   **判定に使う道具** = **`scripts/dep_consumers.sh`** + **`git diff --name-only`**
   (⚠ **既存 `.lean` が 1 本でも diff に出たら発火とみなす**。⚠ **`InformationTheory.lean` への import 1 行
   追加は除く** — それは新規ファイル登録の義務である)。

### 1.1 出力型 (⚠ 着手前に固定する。⚠⚠ 判定そのものはここに書かない)

本 leg の出力は **2 軸**である (⚠ **片方だけ書かない**):

- **受け皿** — `昇格した (0 error)` / `昇格が落ちた` (⚠ 後者なら反証条件 1 が発火し、中核 8 は評価しない)。
- **中核 8** — `通った (0 sorry)` / `sorry + @residual(plan:bc-computable-region-formalization) で退出` /
  `評価していない` (⚠ **3 値を区別する。「評価していない」を「通らなかった」と書かない**)。

⚠⚠ **「受け皿が昇格した」を「単位 B が閉じた」と書かない** — **本 leg が触るのは中核 8–10 のうち 8 の 1 本
だけ**であり、**9 (有界性) / 10 ((α) 合致) は N18 以降である**。
⚠ **新規 `sorry` + `@residual` を入れたら親 plan §4.3 / CLAUDE.md の 2 gate (honesty-auditor /
style-auditor) が要る** — ⚠ **自己監査にしない**。

### 1.2 ⚠ 禁止事項 (親 plan §1 / §3.1 / §4.3 / 子 plan §4 / §5 からの再掲。⚠⚠ 本 leg でも 1 つも緩めない)

- ⚠⚠ **「中核 8 は Mathlib に無いので壁」と機械検証を経ずに書かない** (反証条件 2 の処置欄)。
- ⚠⚠ **hypothesis に証明の核を担わせて `sorry` を消さない** — `*Hypothesis` predicate へのバンドル /
  `:True` slot / 退化定義の悪用 / name laundering。**唯一の退出路は `sorry` + `@residual(plan:…)`** である。
- ⚠⚠ **既存資産の署名を先回りで変えない** — 領域 def 11 本 / `mutualInfoReal` / `condMutualInfoReal`
  (反証条件 3)。
- ⚠⚠ **「スライスの実効コンパクト性は 3 レート版から従う」と書かない** (子 §4-b / **R-4**。
  ⚠ **半計算可能性は超平面との交わりで保たれるとは限らない**)。⚠ **これは判定ではなく禁止条項の違反である**。
- ⚠ **型検査が通ったことを「段が軽い」と読まない** — facts **N2-d** は、監査自身が実効コンパクト性を
  `∀ S, IsCompact S → IsEffectivelyCompactN S` と書いて**偽の命題をコンパイラに黙って通させた**ことを
  記録している ⟹ **型は実効性・一様性の脱落を守らない**。
- ⚠ **「あと少し」「残るのは行数と配線だけ」型の言い回しを使わない** (親 §4.1 軸 2 が名指しで禁じる tell)。
- ⚠ **`Thm7 ⊋ C` の材料が出たと書かない / `R ∈ Thm7` と書かない / `Thm7 ⊄ Thm8` を主張しない**。
- ⚠ **`import Mathlib` を書かない**。⚠ **新規ファイルを足したら `InformationTheory.lean` に import 行を
  追記する** (子 §5)。

---

## 2. 実施したこと

(N17 実行 leg が埋める)

## 3. 機械検証の結果

(N17 実行 leg が埋める)

## 4. 判定 — 見立ての較正と反証条件の発火状況 (⚠⚠ §0 / §1 は 1 文字も書き換えない)

(N17 実行 leg が埋める)

## 5. ⚠ 確かめて「いない」ことの名指し

(N17 実行 leg が埋める)

## 6. 波及 (⚠ facts / 親 plan / 子 plan の書き換えは着地 leg の仕事)

(N17 実行 leg が埋める)
