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

**昇格先** = `InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` (**新規 282 行**)、
namespace = `InformationTheory.Shannon.BroadcastChannel` (既存 BC 家系と同じ。`ProbeThm7` は捨てた)、
`InformationTheory.lean` に import 行 1 本を追記 (`Marton.RegionCardinality` の直後)。
⚠ 置き場所は起票の提案どおりで、変更していない。

**(a) in-repo 資産の消費 (⚠ 起票 §0-A ⭐ の実行)** — `miR` / `cmiR` は置かず、`mutualInfoReal`
(`OuterBoundTransport.lean:149`) / `condMutualInfoReal` (同 `:154`) を **ラッパ 0 本で直接消費**した。
⭐ **起票が心配した「消費できるかは束縛子の設計に依存する」は、束縛子を設計し直すことで消えた** —
probe の `cmiR ν (hν : IsFiniteMeasure ν) …` (明示引数) をやめ、`thm7Slots (ν : Measure _)
[IsFiniteMeasure ν]` の **instance 引数**に揃えた (CLAUDE.md「Mathlib-shape-driven Definitions」=
支配する既存補題の署名に def を合わせる)。⟹ **薄いラッパも局所 def も置いていない**。
⚠⚠ **既存 2 本の署名は 1 文字も変えていない** (§3 の `git diff` と `dep_consumers.sh` を参照)。

**(b) 内側の束縛子の取り替え (⚠ 起票 §0-C の 1 行反証を実際に機械へ掛けた)** —
`⋃ (ν : Measure (Amb …)) (hν : IsFiniteMeasure ν)` を **`⋃ (ν : ProbabilityMeasure (Thm7Ambient …))`**
へ取り替えた。⚠ **これは証明ではなく def の設計変更である**。⚠⚠ **2 つの def が同じ集合を定めることは
Lean で証明していない** (§5)。

**(c) 入れ子を 4 段の def のはしごへ分解** — `thm7RegionOfLaw` (1 法則) / `thm7RegionOfAuxReceiver`
(`⋃_{kv,ν}`) / `thm7RegionOfInput` (`⋂_{kJ,T_J}`) / `thm7Region` (`⋃_p`)。
理由 = **中核 8 の 3 段を段ごとに名前のある補題として測るため** (段ごとの結末を §4 に分けて書ける形にした)。

**(d) 命名と docstring を `docs/rules/` へ** — `AuxIdx`→`Thm7AuxIdx` / `Amb`→`Thm7Ambient` /
`slots`→`thm7Slots` / `Thm7Eligible`→`IsThm7Eligible`、`slice_comm` (連言 1 本) →
`zeroRateSlice` + `zeroRateSlice_iUnion` / `zeroRateSlice_iInter` の 2 本。
docstring は def と headline のみ・英語・process 語彙なし。

**(e) 転記照合を一次典拠へ当てた** — probe 冒頭が指す retrieval command
(`pdftotext -layout` + 論文 URL) をそのまま実行して照合した。
⚠⚠ **抽出テキストは repo に置いていない** (CLAUDE.md「Scratchpad」= public repo に一次文献の本文を
置かない)。照合の範囲と未了範囲は §5。

## 3. 機械検証の結果

⚠ **以下はすべて機械の出力である。散文の印象は入れていない**。

**(0) probe の現在の生存** — `lake env lean docs/shannon/probes/t3c-n2/r1-thm7-region.lean` = **無出力**
(clean)。⟹ 起票が `lake` を 1 度も走らせていなかった点は、走らせた結果 **probe は生きていた**。

**(1) 昇格 1 回目 — error 2 件 (逐語)**:

```
Thm7Region.lean:174:24: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
Thm7Region.lean:181:17: error(lean.unknownIdentifier): Unknown identifier `thm7Region`
```

⭐ **原因は facts N2-c が記録したハザードそのもの** — 174:24 は `thm7RegionOfLaw (ν : Measure _)` の
**下線 1 個**である。処置 = `(ν : Measure (Thm7Ambient kv kJ α β₁ β₂))` と完全に書く。
2 件目は 1 件目の巻き添え (def が立たないので参照が未知識別子になる)。
⟹ **昇格の初期コスト = 往復 1 回 / 修正 2 行**。

**(2) 昇格後** — `lake env lean InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` = **無出力**。
型クラス列は probe の 4 本 (`[Fintype] [MeasurableSpace] [StandardBorelSpace] [Nonempty]`) のままで、
**`failed to synthesize instance` は 0 件**。

**(3) 中核 8 の最終状態** — 同コマンドの出力は **warning 2 件のみ**:

```
Thm7Region.lean:249:6: warning: declaration uses `sorry`
Thm7Region.lean:277:8: warning: declaration uses `sorry`
```

**(4) Prokhorov 側の可用性 (scratchpad の独立 probe、逐語)** — ⚠ **散文で退けず compiler に当てた**:

```lean
example (E : Type) [Fintype E] [MeasurableSpace E] [TopologicalSpace E] [DiscreteTopology E]
    [BorelSpace E] : CompactSpace (ProbabilityMeasure E) := inferInstance     -- 通る (出力なし)

example (E : Type) [Fintype E] [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E] :
    CompactSpace (ProbabilityMeasure E) := inferInstance
-- error(lean.synthInstanceFailed): failed to synthesize instance of type class
--   TopologicalSpace (ProbabilityMeasure E)
```

⟹ **コンパクト性の道具は型クラス 3 本 (`TopologicalSpace` / `DiscreteTopology` / `BorelSpace`) を
要求し、現行の 4 本の列では位相そのものが存在しない**。⚠ **要求元は補題側であって def 側ではない**
(def は 4 本のまま 0 error で立っている = 上の (2))。

**(5) `#print axioms` (11 宣言に当てた)**:

| 宣言 | 結果 |
|---|---|
| `thm7Region` / `thm7RegionSlice` | **sorryAx-free** |
| `isClosed_setOf_inThm7` / `isClosed_thm7RegionOfLaw` / `finite_setOf_lt_thm7Cap` | **sorryAx-free** |
| `zeroRateSlice_iUnion` / `zeroRateSlice_iInter` | **sorryAx-free** |
| `isClosed_iUnion_thm7RegionOfLaw` (ν 段) | `sorryAx` |
| `isClosed_thm7RegionOfAuxReceiver` / `isClosed_thm7RegionOfInput` | `sorryAx` (上を経由) |
| `isClosed_thm7Region` (headline) | `sorryAx` |

⚠ **`sorryAx`-free は必要条件であって十分条件ではない** ⟹ **署名走査も併せた**: 上記 11 本の
仮定はすべて **データ引数か regularity の instance 引数** (`[IsFiniteMeasure ν]` / `[Fintype α]`) であり、
**核を担う hypothesis は 1 本も無い**。とくに headline `isClosed_thm7Region (W : BCChannel α β₁ β₂)` は
**仮定 0 本**である。

**(6) 既存署名の非改変** — `git diff --name-only HEAD` = **`InformationTheory.lean` の 1 本のみ**
(差分は import 行 1 行の追加)。`scripts/dep_consumers.sh` の実測は
`mutualInfoReal` = **43 decl / 1 file**、`condMutualInfoReal` = **38 decl / 1 file** で
**起票 §1-(b) の表と一致**する (⚠ 一致していることが「触っていない」の確認である)。

**(7) code-surface の機械層** — `deno run -A scripts/lean_doc_lint.ts <昇格先>` = **strict 10 規則 /
ratchet 4 規則すべて 0 件**。

## 4. 判定 — 見立ての較正と反証条件の発火状況 (⚠⚠ §0 / §1 は 1 文字も書き換えない)

### 4.1 反証条件の発火 (⚠ 3 本それぞれについて明記する)

- **反証条件 1 (受け皿が 0 error に落ちない)** = ⚠ **不発火**。ただし**無条件の不発火ではない** —
  1 回目は error 2 件で落ちており (§3-(1))、下線 1 個の修正を経て 0 error になった。
  ⟹ **「probe で通っているのだから昇格も通る」は成り立たなかった**。
- **反証条件 2 (中核 8 が 3 段のいずれかで止まる)** = ⚠⚠ **発火**。
  ⭐ **束縛子の取り替え (`ProbabilityMeasure` 化) を先に実行したうえでの発火である** (§2-(b))。
  処置は規定どおり **`sorry` + `@residual(plan:bc-computable-region-formalization)` を 2 本**、
  **署名は証明したい形のまま**で残した (§4.2 に段ごとの結末)。
  ⚠⚠ **壁とは書かない** — CLAUDE.md の wall 宣言規約を全部通していないので、分類は `plan:` である。
- **反証条件 3 (既存宣言の署名変更を要求する)** = ⚠ **不発火**。§3-(6) のとおり既存 `.lean` は
  1 本も diff に出ていない (`InformationTheory.lean` の import 1 行は起票の除外規定どおり)。
  ⭐ **回避の手段は「局所 def を置く」でも「署名工事」でもなく、第 3 の道 = 昇格先の束縛子を
  instance 引数へ設計し直して既存 2 本をそのまま消費する**であった (§2-(a))。

### 4.2 中核 8 の 3 段の結末 (⚠ 段ごとに分けて書く)

| 段 | 結末 | 根拠 |
|---|---|---|
| **ファイバ** (`thm7RegionOfLaw ν` が閉集合) | ⭐ **通った (sorryAx-free)** | `isClosed_setOf_inThm7` = 9 本の非狭義不等式を `isClosed_le` + `fun_prop` で、`isClosed_thm7RegionOfLaw` = 適格性で場合分け (不適格なら `∅`)。計 **14 行** |
| **内側 `kv` 段** (有限合併) | ⭐ **通った (`ν` 段を除いて)** | `finite_setOf_lt_thm7Cap` = `Set.Finite.pi` + `Set.finite_Iio` で **6 行**、`Set.Finite.isClosed_biUnion` が**形ごと当たり** **3 行** |
| **内側 `ν` 段** (法則の合併) | ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)`** | `isClosed_iUnion_thm7RegionOfLaw` (`Thm7Region.lean`) |
| **中間 `⋂_{kJ,T_J}` 段** | ⭐ **通った** | `isClosed_iInter` 3 段、**3 行** |
| **外側 `⋃_p` 段** (= headline) | ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)`** | `isClosed_thm7Region` (同ファイル) |

⟹ **段は 3 つではなく実際には 5 つに割れた**。
⚠⚠ **要約語「5 段中 3 段が通り」は使わない** (監査 訂正 7) — 正確な形は
**`sorryAx`-free は 3 本 (`isClosed_setOf_inThm7` / `isClosed_thm7RegionOfLaw` /
`finite_setOf_lt_thm7Cap`) であり、残る 2 本の段 (`isClosed_thm7RegionOfAuxReceiver` /
`isClosed_thm7RegionOfInput`) は `sorry` を経由する配線である**
(⚠ **§3-(5) の `#print axioms` の表は初めからこのとおり書いており、訂正の対象は要約語だけである**)。

⚠⚠ **残った 2 つは同じ材料を要するが同じ言明ではない** (監査 訂正 3。⚠ **起票時の
「同じ形の未閉項を共有している」は向きが不正確だった**) — **headline は添字 `p` について一様な
(グラフの) 形を要し、`ν` 段はその `p` 断面にすぎない** ⟹ **1 本の共有補題へ機械的に集約できる形では
ない** (⚠ **集約漏れではない**)。⭐ **機械の根拠 (逐語、監査 probe N1)**: 固定 `p` のはしごで headline を
出そうとすると `error(lean.synthInstanceFailed): failed to synthesize instance of type class
AlexandrovDiscrete (ℝ × ℝ × ℝ)` で落ちる。

⟹ **2 本が共有しているのは *材料* の側**であり、それは **(i) 25 スロットが弱位相で連続か** と
**(ii) 法則の集合が閉か** である
(⚠ **コンパクト性そのものではない** — §3-(4) でコンパクト性は型クラス 3 本を足せば出ると機械で確定した)。

### 4.3 見立て 4 本の較正 (⚠ 当てにいくものではない)

- **見立て A (締める)** = **生存**。(a)–(e) の 5 項目はすべて新たに負った。
  ⚠ **ただし ⭐ の「縮む側」は起票の予想より大きく当たった** — 起票は「消費できるかは束縛子の設計に
  依存する」と条件つきで書いたが、**設計を変えることでラッパ 0 本で消費できた**。
  ⚠⚠ **転記義務は縮まなかっただけでなく、照合の結果 1 件の不足を新たに検出した** (§5-(2))。
- **見立て B (緩める)** = **生存**。probe の 4 型クラス列のまま **0 error / `failed to synthesize
  instance` 0 件** (§3-(2))。⚠ B が予告した「要求元は中核 8 の道具であって領域 def そのものではない」も
  **機械で確認された** (§3-(4): 道具側は 3 本を要求し、def 側は 4 本で立っている)。
- **見立て C (締める)** = **結論は生存、理由の 1 つは死亡**。「現行の束縛子のままでは通らない」は
  **束縛子を取り替えてもなお通らない**形で生き残った。⚠⚠ **ただし C が挙げた理由 3
  (Prokhorov のコンパクト性が付かない) は機械で解消できることが確定した** — 型クラス 3 本を
  **補題側に**足せば `CompactSpace (ProbabilityMeasure E)` は合成される (§3-(4))。
  ⟹ **実際の未閉項は理由 3 ではなく §4.2 の (i)(ii) である**。⚠ **C の理由 1 / 2 は今回触れていない**
  (先例が `closure` を取っていることも `isClosed_iUnion` が別物であることも、本 leg では使っていない)。
- **見立て D (緩める)** = **完全に当たり**。`{kv | ∀ i, kv i < thm7Cap α i}` の `Set.Finite` は
  `Set.Finite.pi` + `Set.finite_Iio` で **6 行**、`Set.Finite.isClosed_biUnion` は**形ごと当たった**
  (自前の橋は 0 行)。⚠ **D 自身が但し書きした「ファイバの閉性は本 leg では未検証」も本 leg で閉じた**
  (`isClosed_thm7RegionOfLaw`、sorryAx-free) ⟹ **D の但し書きの側も外れた (良い方向に)**。

### 4.4 出力型 (起票 §1.1 が固定した 2 軸)

- **受け皿** = **昇格した (0 error)**。
- **中核 8** = **`sorry` + `@residual(plan:bc-computable-region-formalization)` で退出**
  (⚠⚠ **「5 段中 3 段が通った」とは書かない** = 監査 訂正 7。正確には **`sorryAx`-free が 3 本**で、
  **残る 2 本の段は `sorry` を経由する配線**であり、⚠ **その 2 本と headline の関係は §4.2 のとおり
  「断面と一様形」である**。⚠ **中核 8 そのものは通っていない**)。

⚠⚠ **これを「単位 B が閉じた」と書かない** — **中核 9 (有界性) / 10 ((α) 合致) は 1 行も触れていない**。

## 5. ⚠ 確かめて「いない」ことの名指し

**(1) 転記照合の未了範囲** — ⚠ **照合した範囲と、していない範囲を分ける**。

- ⭐ **照合した (一次典拠に当てた)**: **25 スロットの情報量と 13 変数の対応** (0–24 の全件) /
  **9 本の制約 (18a)–(18i) の右辺** / **6 本の適格性条件 (19a)–(19c) / (20a)–(20c)** /
  **上限値** (`|X|+6` と `|X|+1`。⚠ `bcAuxAlphabet k` の濃度が `k+1` なので `kv i < |X|+6` が
  `濃度 ≤ |X|+6` に対応することまで確認した) / **入れ子の向き** (「ある `p(x)` が存在し、
  **任意の** 補助チャネルに対し、**ある** 同時分布が」= `⋃_p ⋂_{T_J} ⋃_{aux}`)。
- ⚠ **照合していない**: 一次典拠の**証明**は 1 行も読んでいない ⟹ **定理 7 の主張そのものが
  正しいか**は本 leg の対象外である。**`thm7Region` が空でないか**も未検証 (⚠ 空集合も閉集合なので
  §4.2 の閉性は空虚に真でありうる。⚠⚠ **これは「型検査が実効性を守らない」型の穴である**)。

**(2) ⚠⚠ 照合で見つけた不足 (未修正のまま昇格させた)** — `IsThm7Law` の 4 節は
**一次典拠の因数分解より弱い**。一次典拠は 13 変数の同時分布が
「3 つの補助三つ組の条件つき分布 × 入力分布 × チャネル × 補助チャネル」の**積の形**であることを
要求するが、本 def の第 2–4 節は**周辺分布しか縛っていない** ⟹ **出力が補助変数から入力の下で
条件つき独立であることを要求していない** ⟹ **この述語は積の形より多くの法則を許す**。
⚠ **この不足は probe から継承したものであり、本 leg で作ったものではない**。
⚠ **本 leg では直さなかった** (直すには節の追加という設計変更と、その分の転記照合が新たに要る)。
⭐ **代わりに `IsThm7Law` の docstring に、4 節が何を言っていて何を言っていないかを明記した**
(コードが SoT)。⚠⚠ **この事実から他の領域との包含について何も導いていないし、導いてはならない**。

**(3) `R₀ = 0` スライスの実効コンパクト性 (Π01 性)** — ⚠⚠ **1 行も触れていない**。
本 leg が置いたのは `zeroRateSlice` の**集合レベルの可換性 2 本だけ**であり、
**半計算可能性については何も言っていない**。
⚠⚠ **「3 レート版から従う」とは書かない** (子 plan §4-b / R-4 = 判定ではなく禁止条項)。

**(4) 2 つの束縛子が同じ集合を定めるか** — ⭐⭐ **確率測度の下では機械で閉じた** (監査 訂正 4)。
`(ν : Measure _) (hν : IsFiniteMeasure ν)` 版と `(ν : ProbabilityMeasure _)` 版が **`thm7Region` の中で
同じ集合を定めることは、監査 probe が昇格先の def のまま両向き示した**
(`docs/shannon/probes/t3c-n17/audit-probes.lean` の **P3**。総質量の強制は同 **P2** = `IsThm7Law` の
第 4 節 `ν.map (fun q ↦ q.2.1) = p` と `p : ProbabilityMeasure α` から `IsProbabilityMeasure ν` が出る)。
⟹ ⭐ **facts **N2-l (5)** が名指した未閉項 (法則が総質量を固定することが証明されていない) は閉じた**。
⚠⚠ **未閉として残るのは中間 def が一般の `p : Measure α` を取る場合である** —
`thm7RegionOfAuxReceiver` / `thm7RegionOfInput` は `p` を確率測度に制限せず取るので、
**`p` が確率測度でないときは前者が空・後者が非空でありうる** ⟹ **その水準では 2 つは一致しない**。

**(5) 型クラス 3 本を証明の中で構成できるか** — §3-(4) は 3 本を**仮定として**与えたときの話である。
`Fintype α` + `StandardBorelSpace α` から `MeasurableSpace α = ⊤` を出して
`letI : TopologicalSpace α := ⊥` を構成できるか (= **補題の署名を 4 本のまま保てるか**) は**未検証**。

**(6) 中核 9 / 10** — **有界性も (α) 合致も 1 行も触れていない**。

**(7) 監査** — 本節を書いた時点で本 leg は**自己申告**であった。⭐ **その後 2 gate は実施済**
(honesty = [`bc-t3c-n17-audit.md`](bc-t3c-n17-audit.md) **訂正あり生存**・訂正 7 件・**主判定を動かすもの
0 件**・**tier 5 defect 0 件** / style = **PASS**) ⟹ **分類 (`plan:`) と署名の正直さは独立に検証された**。
⚠ **ただし監査は honesty gate であり、style 側について確認したのは `lean_doc_lint.ts` の機械層
(strict 10 / ratchet 4 がすべて 0 件) だけである** — **判断項目は別の gate が見た**。

**⚠⚠ 以下 (8)–(11) は監査 §5 が名指した「監査も確かめていないこと」であり、本 leg でも未確認である**
(⚠ **自己申告と監査のどちらもこれらを閉じていない**)。

**(8) ⚠⚠ `IsClosed (thm7Region W)` が真であること自体** — **誰も判定していない**。監査は
**命題の真偽を判定しておらず、反証も証明も試みていない** (⚠ **有限周囲空間 + 情報量の連続性 +
閉じた法則集合から真である見込みは高いが、見込みは判定ではない**)。
⟹ ⚠⚠ **偽であれば `@residual(plan:…)` の分類は `defect:false-statement` へ落ちる**。

**(9) 述語の弱化が領域を真に大きくするか** — **上位集合であることは確実**だが (§5-(2) + 監査 軸 2)、
**真の包含かは未検証**である。

**(10) 典拠の濃度補題** — 典拠の「上限つきと上限なしが一致する」という主張は **Lean 側で未形式化**であり、
**監査も検証していない** ⟹ ⚠⚠ **本 def は「上限つき領域」であって、上限なしの `Thm7(W)` と一致するかは
その補題に依存する**。

**(11) 下流の olean 再生成の影響** — `git diff --name-only` で既存 `.lean` に差分が無いことは確認したが
(§3-(6))、**下流の olean 再生成の影響は測っていない**。

## 6. 波及 — ⚠ **本 leg の結果でどの文書のどの行が書き換わったか**

⚠ **本節は「どこが書き換わったか」の索引である** — **後続 leg が何をするかは書かない** (本家系の規約)。
⚠ **監査 訂正 1 / 2 はコード側 (SoT) ゆえ監査自身が Edit 済**であり、本節の対象外である。

| 文書 | 書き換わった箇所 | 由来 |
|---|---|---|
| **本書** | **§4.2 末尾** (「同じ形の未閉項を共有している」→「同じ材料を要するが同じ言明ではない」+ `AlexandrovDiscrete (ℝ × ℝ × ℝ)` の逐語) / **§4.2 と §4.4 の要約語** (「5 段中 3 段が通り」→ `sorryAx`-free 3 本 + 配線 2 本) / **§5-(4)** (未証明 → 確率測度の下では機械で閉じた。残るのは一般 `p : Measure α` の場合) / **§5-(7)** (2 gate 未実施 → 実施済) / **§5-(8)–(11) を新設** | 監査 訂正 3 / 7 / 4 + 監査 §5 |
| [`bc-facts.md`](bc-facts.md) | **`## N17 (T3c)` 節を新設** / **`## N2 (T3c)` の N2-l 行の (5)** (未閉項 → 既閉、再検証コマンドつき) | 本 leg + 監査 訂正 5 |
| [`../audit/audit-tags.md`](../audit/audit-tags.md) | **`@residual` の `plan` 行の Slug 規約**に「末尾の `-plan` は落としてよい」を追記 (⚠ **in-tree の `plan:` slug を着地 leg が数え直し、`bc-computable-region-formalization` と `epi-debruijn-pertime-closure` の 2 slug / 4 か所・**2/2 とも `-plan` を落としている**ことを確認してから書いた**) | 監査 訂正 6 |
| 親 plan [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) | **§5.1 に N17 着地ブロック**を追記 / **§進捗の N17 行**を消化済へ / **予算 600 行**に収めるため §7 の決着済 entry をスタブ化 | 本 leg |
| 子 plan [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md) | **Status 行** (「未着手 — 1 行も書いていない」は偽になった) / **§進捗の B 行** / **§3.2 (iv)** (⚠ **「領域 def には 3 型クラスが追加で要る」は誤りだった** — 要求元は補題側) / **§3.2 (iii)** (転記照合が実際に行われた範囲) | 本 leg + §3-(2) / §3-(4) の機械実測 + 監査 軸 1-c |
| 親 moonshot [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) | **t3c の現況行 / facts 節一覧 / N17 の同期ブロック / Sub-plan テーブルの t3c 行** (⚠ **conflict では子が SoT**) | 親子 DAG の同期 |
