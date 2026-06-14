# footprint split plan — モノリシック証明を named helper へ分解する純リファクタ ✂️

**Status**: Phase 0 DONE / **Phase 1 (優先1 = >250 tier) 全 25 本処理 DONE** (2026-06-14) /
**DoD 緩和済** (現実的版) / **Parent**: なし (standalone) /
**関連**: 実測 SoT [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A.1 / §4.1 ・
命名 [`rules/naming.md`](rules/naming.md) ・docstring [`rules/docstrings.md`](rules/docstrings.md) ・
Lean style [`rules/lean-style.md`](rules/lean-style.md) ・honesty タグ [`audit/audit-tags.md`](audit/audit-tags.md)

## 進捗

- [x] Phase 0 — 測定 + pilot 較正 ✅ (`floorMatrix_dist_le`、commit `d2fb1fa`)
- [x] Phase 1 — 優先1 (>250 行 tier) を named helper へ分解 ✅ **全 25 本処理済** (clean 割れブロックは全抽出、>250 残留=不可分 core は現実的 DoD で許容)
- [ ] Phase 2 — 優先2 (>115 行 tier、159 本) を機会主義的に分解 📋 (dedup 候補は下記「Phase 2 への申し送り」参照、4 件全決着)
- [ ] Phase 3 — 最終再実測 + 裾縮小確認 📋
- [ ] Phase 4 — **option C (>250 spine 攻略)** 🔨 (2026-06-14 着手。**3 本クリア >250: 15→12、両機構検証済**。残 12 本。下記 Phase 4 節)

## Context

Mathlib 最大の暗黙規律は **1 宣言の footprint を小さく保ち、長くなったら名前付き補題に割る** こと
([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §1.2 / §3.A.1)。footprint =
宣言の `theorem`/`lemma`/`def` 行から次の top-level 宣言までの行数。Mathlib は IT+Probability で
**中央値 7 / 最大 115 / 150 超ゼロ**。本プロジェクトは粒度が大きく乖離している。

**分布スナップショット (再実測コマンドは [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md)、母集団は全宣言)** —
Phase 1 前 (commit `7771687`) → Phase 1 完了後 (`afdb482`):

| 指標 | Phase 1 前 | Phase 1 後 |
|---|---|---|
| 中央値 | 18 | 19 (抽出 helper が分布を上へ引く、知見通り) |
| p99 | 238 | 213 |
| 最大 | 907 | 677 (Mass の不可分 core) |
| **> 250 行** | **25** | **15** (−10、本セッション clean 割れ分) |
| > 150 行 | 97 | 91 |
| > 115 行 | 159 | 159 (= 優先2、抽出 helper 流入で件数は据置) |

> 250 残留 15 本は全て不可分 assembly core (10+ `set` ローカル結合 / `private` 参照 / sorry 持ち
spine)。option C (private de-private 化 + spine 再設計) なしには純抽出で消せない (DoD 緩和の根拠)。

このパスは **モノリシック証明の自己完結 `have` ブロックを top-level named helper 補題に切り出す**
だけの **純リファクタ**: 証明内容不変・対象 signature 不変・axiom 不変・sorry 数不変。proof done
(0 sorry / 0 residual) とは独立に進められる = 壁を一切触らない。

## 知見 — 純 `have` 抽出は >250 tier を clear しない (2026-06-14 実測)

**最大の 12 本をリファクタした後の裾の動き** (`python3` footprint 再実測):

| 指標 | リファクタ前 | 12 本後 |
|---|---|---|
| **> 250 行 件数** | 25 | **24** (−1 のみ) |
| 最大 footprint | 907 | **677** (−25%) |
| 中央値 | 18 | **19** (微増) |

**結論: 純 `have` 抽出は >250 の裾を消せない。** 根本原因 — 各証明に残る組立核 (300–680 行) は
抽出で不可分: (a) 10+ の `set` ローカルを束ねており切り出すと項が unify しない、(b) public helper に
漏らせない `private` 定義を参照する。閾値近傍 (~250–300、pilot 253 の類) の証明のみが ≤250 へ clean に
割れる。**中央値が微増したのは、抽出した helper が母集団の中央値より大きく分布を上へ引くため。**

抽出の **真の価値 = (i) 再利用可能な public helper の創出 (12 本で計 42 本) + (ii) 最大 footprint の
~20–30% 縮小** であって、**裾の消去ではない**。>250 の完全 clear には option C (`private` 定義の
public 化 + 組立 spine の再設計) が要り、本純リファクタパスの外 (DoD 緩和の根拠、下記)。

## Approach

**全体の形**: 「巨大証明を読む → 自己完結する `have` ブロックを抽出単位として特定 → top-level の
public・記述的命名・docstring なしの補題へ切り出し → 元証明はその補題を `exact`/`apply` で呼ぶ →
axiom 不変を `#print axioms` で確認」を、ファイル単位で 1 宣言ずつ適用する。

抽出は **Skeleton-driven** に行う: 先に helper の signature を `:= by sorry` で立てて型が通ることを
確認 → 中身を元証明の `have` ブロックから移植 → 元証明側を呼出に置換 → orphan `have` を削除。
中身を 1 つ移すごとに `lake env lean <file>` でグリーンを確認する (一括書換しない)。

### Hard rule — 抽出 helper 自身が新たな >250 モノリスになってはならない (anti-relabeling)

**抽出した helper の証明が大きい (>~150 行) 場合は、その helper をさらに小さい named helper へ
再分解する** (= 再帰)。1 つのモノリスを別名のモノリスへ **付け替えるだけ (relabel)** にしてはならない。
ゴールは **多数の小さい再利用可能宣言** であって、1 つの巨大 `have` を 1 つの巨大 `lemma` に
リネームすることではない。

戒めの実例: `isRescaledPathRegular_of_methodX` (#7) は body を 590→25 行に縮めたが、抽出先
`rescaledPath_indep_regular` が **498 行**になった = relabel に陥った。これは Phase 1 残作業
(下表) で **anti-relabeling ルールに従い再分解**する。抽出時は helper の footprint を都度測り、
>150 なら確定前にさらに割る。

### 抽出の単位 — どの `have` を切るか

- **数学 (measure 非依存) を優先抽出する** (pilot gotcha 3)。pure な `(n:ℕ)(q s ε:ℝ)` 補題で
  measure 引数を取らないものが最も clean かつ再利用性が高い。`μ` を引数に取る抽象化より、
  `μ` 依存を結論に持たない算術核を切るほうが良い。
- **自己完結 (call site のローカルへの依存が浅い) ブロック**を選ぶ。`set ... with hX` のローカルを
  多数参照するブロックは抽出コストが高い。
- **`private` 定数を参照するブロックは切らない** (pilot gotcha 5): public helper の statement に
  private symbol が漏れる。そういうブロックは inline のまま残す。

### Pilot で確定した 5 つの gotcha (ロールアウト必読)

pilot = `ConditionalMethodOfTypes/Core.lean` の `floorMatrix_dist_le` (commit `d2fb1fa`):
public・記述的命名・docstring なしの helper 3 本を抽出、body 241→97 行、
`#print axioms` は `[propext, Classical.choice, Quot.sound]` で抽出前後一致、`lake env lean` clean。

1. **`set ... with hX_def` のローカルは抽出補題の項と自動 unify しない**。call site で
   `rw [hX_def]` を入れて unfold してから `exact <helper>` する必要がある。
2. **auto-param で自動 discharge されていた副条件 (`finiteness`/`positivity`/`measurability`) が
   抽象化で壊れる**。helper の signature に対応する regularity instance/hypothesis を明示追加して
   直す (例: `[IsFiniteMeasure ν]`)。
3. **数学を抽象化せよ** (上の「抽出の単位」)。`μ` でなく純算術を切るのが最も clean。
4. **対象ファイルが `set_option linter.unusedVariables false` を持つ場合、抽出後に dead になった
   `have` が linter で検出されない**。`rg` で usage を grep してから orphan `have` を手で削除する
   (linter に頼らない)。
5. **`private` 定数を参照するブロックは切らない** (上記)。

### Mathlib 流 helper のルール (§4.1 / [`rules/naming.md`](rules/naming.md) / [`rules/docstrings.md`](rules/docstrings.md))

- **public で残す** (§1.4: 小補題 = 再利用 API。Mathlib の private は 1.3%、本プロジェクトは
  逆方向の 15.4%)。`private` 化しない。
- **記述的命名** ([`rules/naming.md`](rules/naming.md): 名前が結論の形を語る、`_of_` で仮説後置、
  `_le_`/`_eq_`/`_iff_`)。staging 語彙 (`Step`/`Bridge`/`Partial`/`Full`/`Discharge`) は使わない。
- **新規 `_aux` 補題を作らない** (名前で事実を語らせる)。機械連番 `aux1`/`aux2` は禁止。
- **docstring を付けない** (§1.4: 補助補題は裸。名前と module doc が意味を担う)。新規 helper に
  docstring を書かない (docstring-tidyup パスの方向と一致)。

### オーケストレーション

- **並列度 ≤ 2** の disjoint-file ownership。1 ファイル = 1 エージェントが所有する
  (純リファクタゆえ実装エージェントだが、衝突回避のため worktree isolation + boilerplate を付す
  — CLAUDE.md「Parallel orchestration」)。**マルチターゲットのファイルは 1 エージェントが
  全ターゲットを所有**する (下の Wave 表で注記)。
- **オーケストレータが検証 + commit** する。各ファイル完了後に `lake env lean` clean +
  `#print axioms` 不変 + signature byte-identical をオーケストレータが確認してから commit する
  (Hard invariants 全 4 点)。

## Hard invariants (違反 = DEFECT)

純リファクタの定義そのもの。1 つでも破れば抽出は不正。

1. **対象 signature が byte-identical**: 切り出し対象の `theorem`/`lemma`/`def` 行 (名前・引数・
   型・instance bracket) はリファクタ前後で 1 byte も変わらない。consumer から見た API 不変。
2. **`#print axioms <target>` 不変**: 抽出前の axiom 集合 (pilot は
   `[propext, Classical.choice, Quot.sound]`) と抽出後が完全一致。`sorryAx` が増えない/減らない。
3. **sorry 数不変 + honesty タグ verbatim 保存**: ファイル内 `sorry` 総数不変。`@residual(...)` /
   `@audit:*` タグはタグ文字列ごと verbatim 保存。**sorry を含む `have` を抽出する場合は、helper が
   その `@residual(...)` を verbatim relocate して担う** (タグが宙に浮かない)。最も安全なのは
   sorry ブロックを inline のまま残すこと (下の `ConvEntropyDensity` 注記)。
4. **compile clean**: 各ファイル `lake env lean <file>` が 0 error (sorry warning は元から
   ある分のみ許容)。最終 Phase で full `lake build` green。

## Phase 1 — 優先1 (>250 行 tier) を named helper へ分解 📋

**proof-log: no** (純リファクタ。判断の余地が小さく、proof-log 不要。axiom 確認結果は commit
message に残す)。

**Wave 編成はファイル単位の ownership で組む** (1 ファイル 1 エージェント、並列 ≤ 2)。
file:line (footprint) sorry-count は §4.1 入力データを verbatim 使用 (2026-06-14)。

### マルチターゲット・ファイル (1 エージェントが全ターゲットを所有)

| ファイル | ターゲット (footprint) | 状態 |
|---|---|---|
| `AWGN/AchievabilityDischarge.lean` | `awgn_random_coding_union_bound` (672→536) + `isAwgnTypicalityHypothesis` (597→432) — 計 2 本 | **DONE** |
| `EPI/Case1/SmoothingLimit.lean` | `entropy_power_inequality_of_density_explicit` (464→338) + `entropyPower_smoothed_epi_perT` (365→336) + `entropy_power_add_ge_of_finite_variance` (310→264) — 計 3 本 | **DONE** |

同一ファイル内の複数ターゲットは編集領域が重なるため **必ず同一エージェント**が直列処理する
(`.git/index.lock` 競合 + 行番号ドリフト回避)。SmoothingLimit の 3 本は全て 264–338 で **>250 残留**
(現実的 DoD で許容、下記)。

### 優先1 ターゲット一覧 (25 本 + pilot)

**前セッション DONE (12 本 + pilot 1 本)** — 検証済: signature byte-identical / `#print axioms` 不変 /
タグ保存 / compile clean。footprint は before→after。**DONE でも >250 残留分は現実的 DoD で許容**。

| file:line (footprint before→after) | 対象 | 備考 |
|---|---|---|
| `ConditionalMethodOfTypes/Core.lean` (253→122) | `floorMatrix_dist_le` | pilot `d2fb1fa` (>250 clear、helper 3 本) |
| `ConditionalMethodOfTypes/Mass.lean` (907→677) | `conditional_KL_concentration_ge` | 最大。**>250 残留** (組立核不可分) |
| `RateDistortion/.../FailureTendsto.lean` (798→653) | `codebookAvgFailureStrong_tendsto_zero` | **>250 残留** |
| `AWGN/AchievabilityDischarge.lean` (672→536) | `awgn_random_coding_union_bound` | マルチ。**>250 残留** |
| `AWGN/AchievabilityDischarge.lean` (597→432) | `isAwgnTypicalityHypothesis` | マルチ。**>250 残留** |
| `ChannelCoding/.../OuterN.lean` (608→466) | `exists_N_for_smooth_achievability_uniform` | **>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (464→338) | `entropy_power_inequality_of_density_explicit` | マルチ。**>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (365→336) | `entropyPower_smoothed_epi_perT` | マルチ。**>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (310→264) | `entropy_power_add_ge_of_finite_variance` | マルチ。**>250 残留** |
| `AWGN/Walls.lean` (485→323) | `continuousAepGaussian_holds` | **>250 残留** |
| `EPI/Case1/RatioLimit/PathRegular.lean` (590→25) | `isRescaledPathRegular_of_methodX` | body 縮小 + helper `rescaledPath_indep_regular` を 498→**122** へ 14 小 helper 再帰分解済 (`b2887fa`、anti-relabel 実証)。file max 122 で >250 clear |
| `SlepianWolf/FullRateRegion/PairBound.lean` (420→386) | `swErrorProb_total_expectation_le` | **>250 残留** |

**本セッション完了分 (13 本、commit `89f3331`..`afdb482`、全 Hard invariant 機械検証済)** —
8 本が ≤250 へ clear、5 本は不可分 core で >250 残留 (DoD 許容)。計 ~70 本の再利用 public helper 抽出。

| 対象 (footprint before→after) | 結果 | helper |
|---|---|---|
| `Boundary` `two_sum_projection_eq` 355→**50** | ✅ clear | 7 (anti-relabel: per-fibre core を 123 で止め再分解) |
| `GeneralDensity` `isBlachmanConvReady_convDensityAdd_gaussian` 346→**54** | ✅ clear | 11 (import cycle 回避でローカル抽出) |
| `GaussianWitness` `isBlachmanConvReady_gaussianPDFReal` 390→**78** | ✅ clear | 6 (int_prod dedup) |
| `SupplyTwoTime` `isBlachmanConvReady_convDensityAdd_gaussian_asym` 364→**92** | ✅ clear | 11 |
| `Assembly` `entropyPower_add_ge_case1_of_methodX` 253→**146** | ✅ clear | 2 (閾値近傍 over-shoot) |
| `Construction` `integrable_negPart_negMulLog_map_condTrunc_sum` 250→205 | ✅ clear | 3 |
| `SmoothInstantiation` `channel_coding_achievability_smooth_at_N_le` 256→218 | ✅ clear | 4 |
| `RandomCodebook` `random_codebook_E1_swap` 260→230 | ✅ clear | 4 (+E2/marginal dedup) |
| `KLFatouLSC` `negMulLog_convDensity_limsup_le` 374→353 | >250 残留 | 2 |
| `TwoSidedRatio` `integral_MRatioLowerZ_le_one` 382→350 | >250 残留 | 3 (+Liminf 重複2補題 dedup) |
| `ConvEntropyDensity` `negMulLog_convDensity_entropy_ge_density` 608→337 | >250 残留 | dead helper 4 本配線+~270行 dedup |
| `DensityForm` `entropy_power_inequality_of_density` 429→298 | >250 残留 | 3 |
| `Mono` `differentialEntropyExt_mono_add_of_integrable` 330→289 | >250 残留 | 6 |

注: #4 `ConvEntropyDensity` は plan の「sorry=1」想定が **誤り** だった (実際は `@audit:ok` の
sorryAx-free)。コード側の `@audit:ok`/`@residual`/sorry 数は全 13 本で機械検証して verbatim 保存
(Assembly は既存 sorry+@residual を含め 1→1 保存)。

## Phase 2 — 優先2 (>115 行 tier) を機会主義的に分解 📋

**proof-log: no**。

優先1 完了後に着手。>115 行 tier は **159 本**。本 Phase では個別列挙しない (優先1 と異なり、
着手時に再実測してファイル単位で拾う = §4.1 入力データのスナップショットに固定しない)。

- 優先1 と同じ抽出ルール・gotcha・Mathlib 流 helper ルール・Hard invariants を適用する。
- **機会主義的に進める**: 優先1 で触ったファイルに >115 の隣接宣言があれば同 Wave で拾う。
- **49–115 行 tier (392 本) は機会主義のみ**: 専用 Wave を組まない。優先1/2 で開いたファイルに
  あれば拾う程度。

### Phase 1 で見つかった具体的 dedup 候補 (Phase 2 の優先着手先)

純抽出で >250 を消せない代わり、**重複削除**は総行数を下げる高価値手 (ただし裾 >250 は縮まない —
重複補題は大定理より前にあり footprint は独立に測られる)。Phase 1 で agent が発見した候補
(全て cross-file = 第2ファイルを参照、`lake build` 連結確認が必須):

1. **`SmoothingLimit.lean` ⊃ DensityForm sibling — DONE (2/3、`f7dc459`)**。3 本のうち
   `integral_sub_integral_sq_smoothed_path_le` / `smoothed_path_absolutelyContinuous_and_negMulLog_integrable`
   は DensityForm の `_rescaled_path_` 版と body byte 一致 → 削除し FQ 呼出に差替済 (axioms 不変、~103 行減)。
   残る `isHeatFlowEndpointRegular_of_map_eq_rnDeriv` は **重複でない**: SmoothingLimit 版は `(vZ : ℝ≥0)`
   一般版、DensityForm `_of_canonical_rnDeriv` は `vZ=1` 特殊化で、L1219 に一般 vZ 呼出があるため inline 維持。
   なお **>250 残留 (339/336/264) は縮まない** (重複補題は大定理より前 = footprint 独立。handoff の「縮む」は誤り)。
2. ~~Ext.lean inline `hbound` → Mono helper~~ **DEAD (import cycle)**。`Mono.lean` は L1 で
   `EntropyPower.Ext` を import 済 (Mono→Ext) ゆえ Ext→Mono は直接 cycle。candidate 3 と同じ下位移設 re-arch が要る。
3. **GeneralDensity ↔ SupplyTwoTime の Blachman per-field helper** は `s=t` 特殊化でほぼ重複だが
   **import cycle** (SupplyTwoTime → GeneralDensity) で直接 dedup 不可。共有 helper を下位モジュールへ
   移設する re-arch が要る (Phase 2 の範囲外、option C 寄り)。
4. ~~`eq_sum_indicator_preimage_mul` (TwoSidedRatio) の inline 重複~~ **FALSE (重複なし、検証済)**。
   SMB 内で `.indicator (fun _ => (1` も `Finset.sum_eq_single`+indicator も TwoSidedRatio のみ、call site は
   内部 1 件で外部 0。dedup 余地なし。

> **Phase 1 dedup 候補 4 件すべて決着** (#1 DONE 2/3 / #2 import cycle DEAD / #3 re-arch 要 = option C 寄り /
> #4 重複なし FALSE)。残る Phase 2 = >115 tier の機会主義抽出のみ (plan 通り専用 Wave は組まない)。

### Phase 1 で確立した検証プロトコル (process 教訓、Phase 2 でも適用)

- **`lake env lean` の silence は「出力が空」で判定する。`rg 'error'` で grep しない。** 新しい Lean の
  `ring`/`ring_nf` 失敗診断は `Try this: [apply] ring_nf` 形式で **"error" 語を含まず**、keyword フィルタを
  すり抜ける (Phase 1 で GaussianWitness の検証を一度すり抜けた)。`out=$(lake env lean $F 2>&1); [ -z "$out" ]`。
- **`lake env lean` の phantom 失敗 (spurious な `ring` 失敗 / unknown identifier) は stale dependency olean
  が原因。`lake build <module>` が arbiter** — 依存を順に rebuild すれば解消し、target は sorryAx-free の
  まま (#print axioms で確認)。並行 `lake build` を多数走らせた後は特に出やすい。
- **namespace はファイル毎に違う** (`EPIDensityForm` / `EPIBlachmanGaussianWitness` / `EPIG2KLFatou` /
  `EPIStamSupplyTwoTime` / `EPIBlachmanGeneralDensity` / `EPIInfiniteVarianceTruncation` /
  `EPICase1RatioLimit` …)。`#print axioms` の FQ 名は `rg '^namespace'` で確認、`.Shannon.` 直下と仮定しない。
- **抽出で露出した unused binder は `_` プレフィックス**して compile を silent に保つ (Mathlib 慣習)。
- **閾値近傍 (~250–300) で ∀-quantified の pure-math ブロックを 2 つ以上持つ target は sub-150 へ
  over-shoot し得る** (Assembly 253→146、Boundary 355→50)。Phase 2 でこの形を優先的に狙うと裾も減る。

## Phase 3 — 最終再実測 + 裾縮小確認 📋

**proof-log: no**。

優先1 (+機会主義分) 完了後:

1. full `lake build` green。
2. `@residual` / `@audit:` タグ総数がパス全体で不変であることを再集計
   ([`audit-tags.md`](audit/audit-tags.md) grep レシピ)。
3. footprint 分布を再実測 ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md)「再実測コマンド」)。
   **裾の件数 (>250) + max は進捗指標として追跡する** が、現実的 DoD では **pass/fail ゲートではない**
   (知見の通り純抽出では裾は消えない)。本 Phase の達成基準 = 全優先1ターゲットで「clean に割れる
   ブロックを全て抽出済 + max footprint を抽出が許す限り縮小済」。>250 → 0 / 各 ≤150 は **aspirational**
   (option C 待ち)。

## Phase 4 — option C (>250 spine 攻略) 🔨

**2026-06-14 ユーザー決定で着手** (純抽出 DoD とは別軸の aspirational を実スコープ化)。残留 15 本の
不可分 assembly core を `private` de-private 化 + **組立 spine の分解**で >250 から落とす。

**proof-log: no** (純リファクタの延長。target sig + axioms 不変は維持)。

### 阻害メカニズム triage (15 本、`set` 数 / `private` 参照 / sorry=全0、2026-06-14 実測)

| カテゴリ | 本 (fp, set, priv) | option C 手法 |
|---|---|---|
| **set-heavy (≥15 set、最難)** | Mass(677,22,3) / union_bound(536,25,1) / FailureTendsto(653,15,0) / OuterN(468,22,0) / isAwgnTypicality(432,22,2) / Walls(323,16,3) | spine 分解 (set-locals 多数を引数化) + 一部 de-private。最後に回す |
| **mid set (6-11、priv=0、spine 再設計系)** | KLFatouLSC(353,11) / SmoothingLimit explicit(339,9)・smoothed(336,10)・add(264,7) / DensityForm(298,9) / **Mono(289,6)** | set-locals (密度・測度) を純 math helper へ抽出して spine 分解。de-private 不要 |
| **private-blocked (low set、de-private 系)** | TwoSidedRatio(350,2,14) / PairBound(390,2,1) / ConvEntropyDensity(337,9,1) | 参照 `private` を de-private → `have` ブロック抽出。最もクリーン |

### Approach (anti-relabel が本質)

純抽出が >250 を消せなかった原因は (a) `have` ブロックが多数の `set` ローカルを束ねる、(b) `private`
定義を参照し public helper に漏らせない。option C はこの 2 つを解く:

1. **`private` 参照の de-private 化**: 参照される `private` def/lemma から `private` を外し public API 化
   (記述的命名・docstring なし)。これで private-blocked ブロックが top-level 抽出可能になる。
2. **spine 分解 (relabel 厳禁)**: set-coupled な組立核を、束ねている `set` ローカル (密度 `fW`/`rfun`、
   測度 `ν`/`μV`/`μWz` 等 = **数学的対象**) を明示引数に取る純 measure-theory helper へ**複数本**抽出する。
   **1 本の巨大 helper への relabel は禁止** (R8): target が <250 でも新 helper が >250 なら **件数は減らない**。
   各 helper を <150 に分解して初めて >250 件数が減る。seam = Case 分岐 / 自己完結 `have` ブロック。

### 進捗 (option C) — 2026-06-14、7 本クリア、3 機構検証済

>250: **15 → 8** (max 677 = Mass 不変)。Mathlib-shape の純 helper 抽出で **3 機構が機械検証 PASS**:

- **spine 再設計系 (set-local → 明示引数 pure helper)**:
  - Mono `differentialEntropyExt_mono_add_of_integrable` 289→**188** (helper 6本、Case-B spine、pilot)
  - KLFatouLSC `negMulLog_convDensity_limsup_le` 353→**228** (helper 8本、n版/μ版ペアを1 helper に集約)
  - DensityForm `entropy_power_inequality_of_density` 298→**172** (5-tuple lift 組立を public helper 5本へ)
  - SmoothingLimit `entropyPower_smoothed_epi_perT` 336→**196** / `entropy_power_add_ge_of_finite_variance` 264→**192**
- **de-private 系**:
  - PairBound `swErrorProb_total_expectation_le` 390→**210** (`swError_EXY_strict` de-private + helper 7本)
- **★ helper 再利用系 (新機構、本セッション確立)**:
  - SmoothingLimit `entropy_power_inequality_of_density_explicit` 339→**225** = DensityForm の 5 lift helper
    を **FQ 名で呼ぶだけ** (inline 重複の 5-tuple lift 組立を除去、新 helper ゼロ)。`add` も 4-tuple 部は独自
    helper だが法輸送/noise法は同 helper を部分再利用。**含意: 残る lift3 系ターゲットは既存 5 helper 再利用で安い。**

全て target sig byte-identical / `#print axioms` 不変 / 0 新 sorry / 連結ビルド green を orchestrator 独立検証済。
helper は全 <150 (relabel 回避)。**3 機構確定 = 残り 8 本は技術リスクなし、実行コストのみ。**

### 残り 8 本 (次、易→難)

1. **private 系 (de-private、PB と同手法)**: ConvEntropyDensity(337,1priv `fibre_rnDeriv_integrable_iff`) /
   TwoSidedRatio(350,14priv = de-private 量多い)。
2. **set-heavy 最難 (15-25 set、spine 分解 + 一部 de-private、最後)**: Walls(323,16set,3priv) /
   isAwgnTypicality(432,22) / union_bound(536,25) / OuterN(468,22) / FailureTendsto(653,15) / Mass(677,22)。

### Hard invariants (Phase 1 の 4 点 + option C 追加分)

Phase 1 の 4 点 (target sig byte-identical / `#print axioms` 不変 / sorry 数不変・タグ verbatim / compile
clean) をそのまま適用。**加えて**: de-private 化した helper は public API として記述的命名 (staging 語彙
禁止)。spine 分解後に各 helper の footprint を測り **>150 なら更に分解** (anti-relabel)。連結ビルドで
importer green を確認 (de-private は可視性変更ゆえ consumer 再ビルドが要る)。

## 検証

**per-file (各ターゲット完了時、オーケストレータが確認)**:

- `lake env lean <file>` clean (0 error、新規 sorry warning なし)。
- `#print axioms <target>` がリファクタ前と一致 (invariant 2)。
- 対象 signature が byte-identical (invariant 1)。`git diff` で対象宣言行に変化がないこと。
- footprint が下がった (対象 body が短縮された)。

**final (Phase 3)**:

- full `lake build` green (invariant 4)。
- `@residual` (タグ) + `@audit:` 総数が pass 前後で保存 (invariant 3)。
- footprint 分布再実測で裾が縮小。

## DoD (現実的版、2026-06-14 ユーザー決定で緩和)

旧 DoD「>250 tier → 0 / 各 ≤150」は **純 `have` 抽出では達成不能**と実測判明 (上記知見、12 本後
25→24)。組立核 (10+ `set` ローカル結合 / `private` 定義参照) は抽出で不可分。ユーザー決定で
**現実的 DoD** に置換:

- **現実的 DoD (pass/fail ゲート)**: 全優先1ターゲットで **clean に割れるブロックを全て再利用可能な
  public helper へ抽出済** + **max footprint を抽出が許す限り縮小済** + 各ファイルで 4 つの Hard
  invariant を満たし、full build green、タグ総数保存。**不可分な組立核の >250 残留は許容**。
- **裾件数 (>250) + max は進捗指標**として追跡するが pass/fail ゲートではない。
- **aspirational (本パス外)**: 「>250 → 0」「各 ≤150」は option C (= `private` helper の de-private 化
  + 組立 spine の再アーキテクト) を要し本純リファクタパスのスコープ外。
- proof done (0 sorry / 0 residual) は **本パスの DoD ではない**: 純リファクタゆえ sorry 数は不変
  (#4 の 1 sorry を含め保存する)。完成度は別軸 (各 family の moonshot plan が tally)。

## Risks & mitigations

- **R1: auto-param 副条件の暗黙 discharge が抽象化で壊れる** (pilot gotcha 2)。
  → helper signature に regularity instance/hypothesis を明示追加。skeleton 段階で型が通ることを
  先に確認してから中身を移す。
- **R2: `set ... with` のローカルが helper 項と unify せず call site が `exact` で落ちる**
  (gotcha 1)。→ call site で `rw [hX_def]` を入れてから `exact`。
- **R3: `linter.unusedVariables false` のファイルで dead `have` が検出されず残る** (gotcha 4)。
  → 抽出後に `rg` で usage を grep し orphan `have` を手で削除。linter に依存しない。
- **R4: sorry 持ち #4 で `@residual` タグが宙に浮く / 二重化する**。→ デフォルトは sorry ブロックを
  inline 維持 (タグ移動なし)。やむを得ず抽出する場合のみ verbatim relocate (invariant 3)。
- **R5: マルチターゲット・ファイルで並列エージェントが衝突** (`AchievabilityDischarge` ×2 /
  `SmoothingLimit` ×3)。→ 1 ファイル = 1 エージェントが全ターゲットを直列処理 (Approach 参照)。
- **R6: helper が private 定数を引きずり出して public statement に private symbol が漏れる**
  (gotcha 5)。→ private 参照ブロックは抽出せず inline 維持。
- **R7: axiom が静かに変わる (`sorryAx` 混入等)**。→ invariant 2 を per-file で必ず機械確認。
  一致しなければその抽出を revert。
- **R8: relabel — 抽出 helper 自身が新たな >250 モノリスになる** (実例: `rescaledPath_indep_regular`
  498 行)。→ Approach の anti-relabeling Hard rule: helper footprint を都度測り >150 なら確定前に
  さらに小 helper へ再分解。1 モノリスを別名モノリスに付け替えない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

1. **抽出単位は「数学優先」**: pilot 較正で `μ` 抽象化より pure 算術核 (`(n:ℕ)(q s ε:ℝ)`) を切るのが
   最 clean と確定 (gotcha 3)。優先1 でも measure 非依存ブロックを第一候補にする。
2. **sorry 持ち #4 のデフォルトは inline 維持**: `negMulLog_convDensity_entropy_ge_density` の
   1 sorry は抽出せず inline に残し、周辺の sorry-free ブロックのみ切る。タグ移動を回避し invariant 3 を
   自明化する (抽出が必要になったら verbatim relocate へ切替)。
3. **2026-06-14: 純 have 抽出は >250 tier を clear できない**と実測判明 (12 本リファクタ後 25→24、
   max 907→677)。ユーザー決定で DoD を現実的版 (再利用 helper 抽出 + max 縮小、>250 残留許容) へ緩めて
   残り 13 本継続。裾の完全 clear は option C (`private` def の public 化 + spine 再設計) が要るが
   別スコープ。併せて anti-relabeling Hard rule を追加 (`rescaledPath_indep_regular` 498 行 relabel が
   戒め例) — 抽出 helper が >150 なら再分解、別名モノリスに付け替えない。
