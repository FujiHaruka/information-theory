# Shannon: MAC + BroadcastChannel legacy-tag → sorry-based migration plan

> **Parent**: [`mac-moonshot-plan.md`](mac-moonshot-plan.md) +
> [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) +
> [`mac-l1-discharge-moonshot-plan.md`](mac-l1-discharge-moonshot-plan.md)
> 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
> [`audit/audit-tags.md`](../audit/audit-tags.md) /
> [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md) (pilot) /
> [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md) +
> [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) (Round 1)。
>
> 本 plan は **proof completion ではなく legacy tag (suspect / 散文 `🟢ʰ`) → `sorry + @residual` の honesty 強化**
> (`audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする独立 workstream。proof done は
> 本 plan の出力にしない (= `mac-l1-discharge-moonshot-plan` / `mac-l2-discharge-*` /
> `mac-l3-discharge-*` / `bc-converse-fano-discharge-*` 等別 workstream)。

## Context

### なぜ MAC と BC を 1 plan にまとめるか (Plan 分割判断)

**結論: 1 plan (本 plan) に統合する**。MAC family と BC family を 1 sweep で扱う。
根拠は以下 4 点 — runbook 表 (Round 2、中規模、wall 集約候補) では「MAC/BC」と
**まとめて 1 行**で記載されており、本 plan はその指示を踏襲する:

1. **アーキテクチャの同型** — capacity region converse の Fano + chain + cleanup の
   divide-by-`n` arithmetic kernel が両 family で完全に同型構造を共有する
   (`mac_rate_le_of_fano` 〜 `bc_rate_le_of_fano (private)`)。converse outer-bound の
   分割は per-user (single direction × 2 + joint × 1 for MAC、common + private for BC)
   で構成が同じ — 一方の sweep 手順がそのままもう一方に適用できる。
2. **コード上の依存関係 (内部 cross-family)** — `BroadcastChannelSuperposition.lean` が
   `import Common2026.Shannon.MACL1Discharge` し、`BroadcastChannelSuperpositionBody.lean`
   が `import Common2026.Shannon.MACBodyDischarge` (verbatim 確認)。BC superposition の
   inner bound discharge が MAC L1 discharge を文字通り **import で再利用**しているため、
   ripple 順序を独立に管理すると同 olean を 2 回 refresh する非効率が発生 + drift risk。
3. **共有 wall (joint-typicality-multi)** — `audit-tags.md`「Wall name register」に既登録の
   `joint-typicality-multi` (Ch.15 MAC/BC/Relay) が両 family の inner bound discharge の
   wall。本 plan ではこれを **wall name として正式採用** (Wall name register 拡張 R4 では
   なく既存活用 — 後述)。共有 wall を伴う sweep は別 plan にすると register 上の wall
   消費追跡が分散する。
4. **件数規模が中規模 (49 件)** — pilot Hoeffding 19 件、Round 1 Cramér 13 件 + WynerZiv 22 件
   の合計 (35 件) と同等規模。1 plan の運用範囲内 (L-MIG-4 撤退ラインの予測規模 25-30 件
   超過は許容、Round 1 WynerZiv plan の手順を踏襲)。

代替案として「`mac-sorry-migration-plan.md` + `bc-sorry-migration-plan.md` 2 plan 分割」を
検討したが (4) を除く根拠が破綻するため不採用。具体的に: BC superposition body が MAC body
discharge を import で reuse している以上、BC sweep 中の `bc_capacity_region_inner_bound_with_superposition_body`
は MAC sweep の `mac_capacity_region_inner_bound_with_body` の sorry 化に伴って transitive
sorry に降格する。2 plan で sweep すると BC plan 単独で「MAC sweep 待ち」状態となり順序
依存が runbook 級の管理コストになる。1 plan で sweep すれば transitive sorry 化を 1 つの
Phase シーケンス内で吸収可能。

### なぜ MAC + BC が次の sweep family か

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25 集計)」表で
「MAC/BC」は **Round 2 (中規模、wall 集約候補 1-2 件あり)** に分類。Round 1 (Cramér /
Huffman / WynerZiv) 完了後の次 sweep として優先度が高い。verbatim 再計数 (本 plan
inventory step) で **計 49 件** が確定:

- MAC family: 28 件 (suspect 17 + 散文 `🟢ʰ` 11) — `MultipleAccessChannel.lean` 17,
  `MACFanoConverseBody.lean` 5, `MACBodyDischarge.lean` 2, `MACCornerPoint.lean` 2,
  `MACL1Discharge.lean` 1, `MACPerEventAEPDecay.lean` 1
- BC family: 21 件 (suspect 11 + 散文 `🟢ʰ` 10) — `BroadcastChannel.lean` 15,
  `BroadcastChannelExistenceBridgeBody.lean` 4, `BroadcastChannelSuperposition.lean` 1,
  `BroadcastChannelSuperpositionBody.lean` 1

`@audit:staged` / `@audit:defer` / `@audit:closed-by-successor` は本 family **0 件**
(verbatim 確認、`rg -c @audit:staged|@audit:defer|@audit:closed-by-successor` 全件 0 hit)。
既存 `sorry` も word-boundary 計数で **0 件** (Pilot Pattern D 適用; `MACPerEventAEPDecay.lean:44/56`
の 2 hit は docstring 内文字列リテラル `sorry`-free 等の説明文)。

### 親 moonshot との関係

`mac-moonshot-plan.md` / `broadcast-channel-moonshot-plan.md` / `mac-l1-discharge-moonshot-plan.md`
は L-MAC1〜L-MAC5、L-BC1〜L-BC5 すべて hypothesis pass-through で publish 済 (de-circularized
form 移行済、2026-05-21)。本 plan は **その pass-through 設計を変えない**:

- entropy-level Fano + chain inequality を hypothesis として取り body で `mac_rate_le_of_fano`
  ×3 / `bc_rate_le_of_fano` ×2 で **divide-by-`n` を実行**する converse outer bounds (大半が
  該当) は signature をできるだけ維持し、`@audit:suspect` タグを `@residual(plan:...)` 付き
  sorry に置換する **書換** が中心になる。
- BC の `bc_common_rate_bound` / `bc_private_rate_bound` 2 件は **tier 5 defect (circular +
  launder)** — 仮説型 ≡ 結論型 で body `:= h_*_lbh`、自著者が ⚠ HONESTY ALERT で「the body
  is `:= h_*RateBound_lbh`」と明示済 (`BroadcastChannel.lean:431/466`)。これらは **signature
  改変 + body sorry + `@residual(defect:circular)` 必須**。
- BC の `bc_random_codebook_markov_of_ensemble` 1 件は **honest-rebrand caveat + operational
  degeneracy** を著者が明記済 (`BroadcastChannelExistenceBridgeBody.lean:297`) で **tier 5
  defect (`defect:degenerate`)** 寄り。Phase 2 で sorry 化判定。
- **proof completion** (joint-typicality core / Bonferroni / random codebook averaging) は
  別 workstream に残る。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature honesty を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にはならない**。

### Tier 5 defect — Inline 検出済 (実装前に明示)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で発見した tier 5
defect (および tier 5 寄りの honesty-suspect declaration) を以下に列挙。**実装 agent は本 plan
に従って rewriter (signature 改変 + sorry 化) する際、新規に作らない + 既存を silent fix
しない**。それぞれ Phase 2.x 内で **defect 明示付き** で sorry 化する。

| file:line | decl 名 | defect kind | verbatim 根拠 |
|---|---|---|---|
| `BroadcastChannel.lean:443` | `bc_common_rate_bound` | `defect:circular` + `defect:launder` | signature `(h_commonRateBound_lbh : R₂ ≤ I_u) : R₂ ≤ I_u := h_commonRateBound_lbh` — 仮説型 ≡ 結論型、body identity。⚠️ HONESTY ALERT 著者明記 (line 431) で確認済 |
| `BroadcastChannel.lean:475` | `bc_private_rate_bound` | `defect:circular` + `defect:launder` | 同上、`(h_privateRateBound_lbh : R₁ ≤ I_xy) : R₁ ≤ I_xy := h_privateRateBound_lbh`。⚠️ HONESTY ALERT (line 466) |
| `BroadcastChannelExistenceBridgeBody.lean:314` | `bc_random_codebook_markov_of_ensemble` | `defect:degenerate` (predicate-degenerate downstream) | ⚠️ Honest-rebrand caveat (line 297) で著者明記 — 出力 predicate `IsBCRandomCodebookMarkov` が `errBound` を `_c` の error と link しない vacuous shape。本体は genuine averaging を計算するが `obtain ⟨_C₀, _hC₀⟩` で operational witness を discard、constructor だけ満たす |

`bc_common_rate_bound` / `bc_private_rate_bound` は **MAC 側 `mac_single_rate_bound₁/₂/sum`
(genuinely derived from entropy-level Fano + chain) と非対称**。MAC 側は身体が
`mac_rate_le_of_fano hn ... h_fano h_chain h_cleanup` で **genuine 派生**、BC 側は
load-bearing hypothesis bundling 形 (= tier 5 defect)。本 plan は BC 側を MAC 側と整合する
genuine 形にするか、それとも MAC 側と同一 entropy-level Fano hypothesis を取る形に signature
を再設計するかは Phase 2.3 で決定 — 暫定の Phase 2 では tier 5 defect 形を `defect:circular` 付
sorry に降ろし、honesty を回復してから設計判断を auditor に委ねる。

`bc_random_codebook_markov_of_ensemble` は本来 `IsBCBonferroniEnsembleDecay` → `IsBCRandomCodebookMarkov`
の genuine bridge であるべきだが、下流 predicate (`IsBCRandomCodebookMarkov`) の **operational
gap** が原因で body の操作的 witness が discarded。これは Phase 2.4 で
`@residual(defect:degenerate)` 付与、修正 (= `IsBCRandomCodebookMarkov` の再定義) は本 plan
scope 外 (`broadcast-channel-moonshot-plan` 配下の predicate redesign session に escalate)。

## Approach

**1 plan、file 単位 sweep を 3 Phase + audit + verify に分割**、共有 wall lemma は
`joint-typicality-multi` を register 既存名で活用 (新規追加なし)、cross-family ripple
(MAC↔BC 内部) を明示的に保護する。

### 戦略 (Phase 構造)

49 件の混在 (suspect 28 + 散文 `🟢ʰ` 21 + tier 5 defect 3) に対する sweep 順序を
**「壊れにくい → 構造的影響大」順** に設計:

```
Phase 0  inventory (本 plan 内 inline 表)
   │
Phase 1  V/C/H cleanup
   │      ├─ V (variational pass-through、純 wrapper)         ← 該当ゼロ件
   │      ├─ C (in-tree constructive primitive 経由)          ← 該当ゼロ件
   │      └─ H (散文 🟢ʰ 言及の docstring refine)               ← 21 件 (MultipleAccessChannel 9 + MACFanoConverseBody 1 + BroadcastChannel 9 + BroadcastChannelExistenceBridgeBody 1)
   │
Phase 1.5  audit-1 (Phase 1 全件)
   │
Phase 2.1  P retreat — MAC capacity region wrappers (genuine derivation 維持型)
   │      ├─ MultipleAccessChannel.lean 8 件 (mac_single_rate_bound₁/₂, mac_sum_rate_bound, mac_capacity_region_outer_bound, mac_capacity_region_outer_bound_three_bounds, mac_capacity_region_inner_bound, mac_capacity_region_inner_bound_bundled_strict, mac_capacity_region_consistent)
   │      ├─ MACCornerPoint.lean 2 件 (mac_capacity_region_subset_pentagon, mac_capacity_region_is_pentagon)
   │      ├─ MACBodyDischarge.lean 2 件 (mac_capacity_region_inner_bound_with_body, mac_capacity_region_with_body_two_side)
   │      ├─ MACFanoConverseBody.lean 4 件 (mac_single_rate_bound₁/₂_with_fano, mac_capacity_region_outer_bound_with_per_user_fano, mac_capacity_region_outer_bound_of_measure)
   │      ├─ MACL1Discharge.lean 1 件 (mac_capacity_region_inner_bound_with_joint_typ_aep)
   │      ├─ MACPerEventAEPDecay.lean 1 件 (mac_capacity_region_consistent_of_perEvent)
   │      └─ all bodies → `sorry` + `@residual(plan:mac-bc-sorry-migration-plan)` (signature 改変は最小限、entropy-level hyp は precondition として残す方針 — Phase 2.4 audit-2 で境界判定可能)
   │
Phase 2.2  P retreat — BC capacity region wrappers (genuine derivation 維持型)
   │      ├─ BroadcastChannel.lean 4 件 (excluding the 2 tier-5 defects) — bc_capacity_region_outer_bound_corner_limit, bc_capacity_region_inner_bound, bc_capacity_region_inner_bound_bundled_strict, bc_capacity_region_consistent
   │      ├─ BroadcastChannelSuperposition.lean 1 件 (bc_capacity_region_inner_bound_with_superposition_aep)
   │      ├─ BroadcastChannelSuperpositionBody.lean 1 件 (bc_capacity_region_inner_bound_with_superposition_body)
   │      ├─ BroadcastChannelExistenceBridgeBody.lean 2 件 (bc_inner_bound_with_ensemble_averaging, bc_inner_bound_with_ensemble_averaging_bundled — predicate-degenerate な bc_random_codebook_markov_of_ensemble を呼ぶ wrapper だが本 wrapper 自身は genuine modus ponens)
   │      └─ all bodies → `sorry` + `@residual(plan:mac-bc-sorry-migration-plan)`
   │
Phase 2.3  defect retreat — tier 5 (BC circular pair, BC degenerate)
   │      ├─ BroadcastChannel.lean:443 `bc_common_rate_bound` — signature から `h_commonRateBound_lbh` 削除、body sorry + `@residual(defect:circular)`
   │      ├─ BroadcastChannel.lean:475 `bc_private_rate_bound` — 同様、`h_privateRateBound_lbh` 削除
   │      └─ BroadcastChannelExistenceBridgeBody.lean:314 `bc_random_codebook_markov_of_ensemble` — body sorry + `@residual(defect:degenerate)` (signature は touch せず、下流 predicate の operational gap に attach)
   │
Phase 2.x  ripple — caller drift handling
   │      ├─ MAC↔BC 内部 cross-import (BroadcastChannelSuperposition → MACL1Discharge / BroadcastChannelSuperpositionBody → MACBodyDischarge) 経由の transitive sorry を docstring 散文化
   │      ├─ HONESTY ALERT 周辺 docstring の文言 (⚠️ The body is `:= h_*_lbh` 等) は signature が defect retreat 済になった旨を反映して書換
   │      └─ Pattern C: 即興 `(plan:..., transitive)` vocabulary 禁止
   │
Phase 2.4  audit-2 (Phase 2 全件 + tier 5 defect 3 件)
   │
Phase V   verify (全 10 file lake env lean 0 errors + 集計 + banner)
```

### 戦略の根拠

1. **Phase 1 (H 散文 refine) を最初** — `🟢ʰ` 言及 21 件はすべて declaration の docstring
   内の散文表現 (「honest-🟢ʰ entropy-level input」「genuine / honest-🟢ʰ」等)。本体コード
   や signature を touch せず、tier 4 vocabulary を tier 4 free な散文に書換るだけ。
   docstring 改変は type-check 影響なし。WynerZiv pilot で同様の操作を 3 件で実施済 (Phase
   1.5.1)、手順流用可能。

2. **Phase 2.1 (MAC) と Phase 2.2 (BC) を分離** — MAC↔BC の cross-import (BC superposition
   → MAC L1 / BC superposition body → MAC body discharge) があるため、上流 MAC 側を先に
   sweep して olean refresh、その後 BC 側 sweep が transitive sorry を含む状態で進める順序。
   逆順だと BC 側 sweep 後に MAC 側 signature 改変で BC 側 olean が再度 stale 化する
   (Pilot Pattern A 違反 risk)。

3. **Phase 2.3 (tier 5 defect) を Phase 2.1/2.2 完了後の独立 Phase に**: BC tier 5 defect
   2 件は MAC 側に対応 declaration が **既に genuinely derived** (`mac_single_rate_bound₁/₂/sum`
   が `mac_rate_le_of_fano` 経由で derive される正常形)。MAC 側を見ながら BC 側を fix する
   設計を選択可能だが、本 plan では **Phase 2.3 でまず defect signature を sorry に降ろして
   honesty を回復**してから、Phase 2.3.b (任意) で genuine 形に signature を再設計する判断を
   auditor に委ねる。silent fix 禁止 (Pattern F)。

4. **Phase 2.x ripple は MAC↔BC 内部 cross-family を最優先保護**: BC superposition は MAC
   L1 discharge を import 再利用、`mac_capacity_region_inner_bound` を Phase 2.1 で sorry 化
   すると BC superposition wrapper が transitive sorry。**WynerZiv pilot と同じく即興
   `(<class>:<slug>, transitive)` vocabulary 禁止**、docstring 散文で transitive 性を明示。

### 共有 wall lemma 集約の要否 (R4 — Wall name register 拡張)

**`joint-typicality-multi` を register **既存名** で活用、新規追加なし**。

検証手順 (`audit-tags.md`「Wall name register」逐次確認):
- `stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` /
  `nyquist-2w-dof` / `multivariate-mi` / `epi-n-dim` / `fourier` — 該当なし
- **`joint-typicality-multi` (意味: 多変数 joint typicality / Fano、関連: `Ch.15 MAC/BC/Relay`)**
  — **本 family の MAC inner bound (joint typicality 4 error events + Bonferroni) と BC inner
  bound (superposition coding + per-receiver joint typicality) の wall に一致**。MAC の
  `MACJointTypicalityAchievable` および BC の `BCSuperpositionAchievable` predicate は両方とも
  この壁の hypothesis-form pass-through。

ただし本 sweep で wall 名を `@residual(wall:joint-typicality-multi)` として **活用するかは
保留** — 理由:

- Round 1 pilot family (Hoeffding / Cramér / WynerZiv) は全て `plan:` slug で揃え wall name
  への切り替えを保留した。`audit-tags.md`「移行レシピ」も基本形は `plan:<slug>` であり、
  `wall:<name>` への切替は shared sorry 補題化 (`audit-tags.md`「共有 Mathlib 壁」) と
  セットで導入するのが register 設計上整合的。
- 本 sweep の 49 件は `mac-bc-sorry-migration-plan` slug 1 つで集計可能 + closure 担当 plan
  も `mac-moonshot-plan` / `broadcast-channel-moonshot-plan` / `mac-l1-discharge-moonshot-plan`
  に分散しており、`wall:joint-typicality-multi` 単一に集約するなら shared sorry 補題化が
  prerequisite。本 plan では shared sorry 補題化を **採用しない** (Hoeffding/Cramér/WynerZiv
  踏襲)。

**したがって本 plan の `@residual` slug は `plan:mac-bc-sorry-migration-plan` で揃える**
(新規 wall name 追加なし、新規 wall PR なし)。

Wall name register 拡張提案 (R4) — **必要なし**。既存の `joint-typicality-multi` で覆える。
ただし「`@residual(plan:mac-bc-sorry-migration-plan)` の真の壁は `joint-typicality-multi`
である」旨を Phase V で `mac-moonshot-plan.md` / `broadcast-channel-moonshot-plan.md` の
banner に注記し、将来 shared sorry 補題化のとき wall name 切替を可能にする。

### constructive recovery 候補 (Pilot Pattern B)

**0 件** (verbatim 確認、49 件全て load-bearing hypothesis consumer または derivation chain)。

- MAC family の `mac_single_rate_bound₁/₂/sum` / `mac_capacity_region_outer_bound` /
  `mac_capacity_region_outer_bound_three_bounds` 等は **既に entropy-level Fano + chain
  inequality を入力として derive** している (de-circularized form)。これは hypothesis-form
  pass-through だが、各 hypothesis (entropy-level scalar inequality) 自体が **Mathlib 壁の
  hypothesis-form pass-through** であり、constructive recovery で消せる種類ではない。
- BC family の 4 件 (excluding tier 5 defects) も同様の genuine pass-through。
- MACFanoConverseBody.lean の 4 件は **既に genuinely Fano-backed** (`macFanoEntropyData_of_measure`
  → `fano_inequality_measure_theoretic` 経由) で純構成的に近いが、joint-fano + chain-rule
  inputs を取る点で hypothesis-form。constructive recovery で hypothesis を消すルートはない。

Hoeffding pilot の `isHoeffdingMinimizerFullSupport_of_lagrange` のような「結論型が
`∀ a, 0 < · a` の regularity に reducible」declaration は本 family に **存在しない**。

### transitive sorry の handling 方針 (Pilot Pattern C)

Phase 2.1 / 2.2 / 2.3 で sweep される declaration は file 間の dependency chain を形成する
(MAC↔BC 内部 cross-import 含む):

```
MultipleAccessChannel.mac_capacity_region_outer_bound (Phase 2.1 sorry)
  ← MACBodyDischarge.mac_capacity_region_outer_bound_with_body (Phase 2.1, body is intentionally not @audit:suspect — 散文 transitive)
  ← MACFanoConverseBody.mac_capacity_region_outer_bound_with_per_user_fano (Phase 2.1 sorry)
  ← MACFanoConverseBody.mac_capacity_region_outer_bound_of_measure (Phase 2.1 sorry)
  ← MACPerEventAEPDecay.mac_capacity_region_consistent_of_perEvent (Phase 2.1 sorry)

MultipleAccessChannel.mac_capacity_region_inner_bound (Phase 2.1 sorry)
  ← MACBodyDischarge.mac_capacity_region_inner_bound_with_body (Phase 2.1 sorry)
  ← MACL1Discharge.mac_capacity_region_inner_bound_with_joint_typ_aep (Phase 2.1 sorry)
  ← BroadcastChannel.bc_capacity_region_inner_bound (Phase 2.2 sorry; cross-family via shape similarity but BC defines its own predicates)

BroadcastChannel.bc_capacity_region_inner_bound (Phase 2.2 sorry)
  ← BroadcastChannelSuperposition.bc_capacity_region_inner_bound_with_superposition_aep (Phase 2.2 sorry)
  ← BroadcastChannelSuperpositionBody.bc_capacity_region_inner_bound_with_superposition_body (Phase 2.2 sorry)
```

各 declaration の自身の `@audit:suspect` 削除に対応する `@residual(plan:mac-bc-sorry-migration-plan)`
は **1 つだけ**持つ。上流 sorry への依存は docstring 散文で明示:

```
Transitive `sorry` via `<upstream decl>` (Phase 2.{1,2,3} retreat). No
additional `@residual` tag attached — closure responsibility is shared with
the upstream declaration's `@residual(plan:mac-bc-sorry-migration-plan)`.
```

vocabulary divergence 回避のため、即興 `(plan:..., transitive)` suffix は禁止。

### cross-family entanglement 検証 (R3, R14)

verbatim 確認方法: `rg -nl <MAC/BC 主要 symbol>` で当該 file 外の use site を `Common2026.Shannon`
内で検索、各 file の `rg -n '^import Common2026' <target>` で import declaration を確認。

| entanglement | 種類 | 影響 |
|---|---|---|
| `BroadcastChannelSuperposition.lean` imports `MACL1Discharge` | MAC↔BC 内部 cross-import | Phase 2.x で MAC L1 sorry 化 → BC superposition は transitive sorry。同 sweep 内で吸収可、削除提案禁止 |
| `BroadcastChannelSuperpositionBody.lean` imports `MACBodyDischarge` | 同上 | 同上、BC superposition body は MAC body discharge を import 再利用 |
| `Common2026/Shannon/RelayCutset.lean` / `RelayInnerBound.lean` references `MACInnerBoundExistence` / `BCInnerBoundExistence` / `BCSuperpositionAchievable` / `MACJointTypicalityAchievable` 等 | **docstring 内 prose 言及のみ** (verbatim: `mirrors the MAC ...`、`is the relay analogue of MACCode ...` 等) | **実コード上の symbol 引用なし、`Common2026.Shannon.MultipleAccessChannel` / `Common2026.Shannon.BroadcastChannel` import なし** (verbatim 確認、Relay import は `ChannelCoding` / `CondMutualInfo` / `MIChainRule` のみ)。entanglement なし。docstring 内 prose を touch しない方針で本 sweep scope を MAC/BC 内部に閉じる |

**結論**: MAC↔BC 内部の cross-import 2 件は本 plan 内で完結処理 (削除提案禁止、ripple 散文化)、
MAC/BC → Relay の prose 言及は touch しない。**新規 cross-family entanglement 該当件数 = 0**
(prose 言及は entanglement カウントから除外、Round 1 WynerZiv の RelayCFBinningBody の
re-namespacing 利用とは性質が異なる — 後者は symbol 直接呼出 / re-export、本 family は prose
コメント言及のみ)。

### Phase 2.3 tier 5 defect の追加注意

`bc_common_rate_bound` / `bc_private_rate_bound` は MAC 側に **対応する genuine derivation
が既に存在する**:

- MAC: `mac_single_rate_bound₁/₂` (`MultipleAccessChannel.lean:449/474`) は entropy-level
  Fano + chain + cleanup を取り `mac_rate_le_of_fano` で純構成的 derive
- BC: `bc_common_rate_bound` / `bc_private_rate_bound` は `(h_lbh : R ≤ I) : R ≤ I := h_lbh`
  で **circular**

Phase 2.3 はまず defect signature を sorry に降ろして honesty 回復、その後 Phase 2.3.b
(オプション) で **MAC 側と同型の genuine signature 再設計** (entropy-level Fano + chain +
cleanup → `bc_rate_le_of_fano` 経由 derive、`BroadcastChannel.lean:511` の `private theorem
bc_rate_le_of_fano` を直接呼ぶ形) を提案する。再設計判断は honesty-auditor に委任 (Phase 2.4)。

## 在庫: 49 件 (suspect 28 + 散文 🟢ʰ 21) verbatim 分類

verbatim 確認方法: 各 `@audit:suspect|🟢ʰ` 周辺の docstring + theorem signature + body
1-3 行を実コードから Read。各 declaration の `file:line` は **タグ行** (= docstring 末尾の
`@audit:suspect(...)`)、declaration 名はその直後の `theorem` 行。

### MAC family — `MultipleAccessChannel.lean` (17 件: suspect 8 + 散文 🟢ʰ 9)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:42` | (docstring 散文、`mac_capacity_region_outer_bound` 説明) | "**genuine / honest-🟢ʰ, non-circular**" | H | docstring refine: `🟢ʰ` 削除、"non-circular" は残す | No | Phase 1 |
| `:47` | (docstring 散文) | "joint-message Fano and the per-letter chain rule remain honest-🟢ʰ" | H | "honest-🟢ʰ" → "real Mathlib gap (joint-typicality-multi wall)" | No | Phase 1 |
| `:50` | (docstring 散文、`mac_capacity_region_inner_bound` 説明) | "**honest-🟢ʰ, non-circular, error-carrying**" | H | docstring refine | No | Phase 1 |
| `:86` | (docstring 散文) | "conditional-MI chain rule remain honest-🟢ʰ (real Mathlib gaps)" | H | "honest-🟢ʰ" → "real Mathlib gaps (joint-typicality-multi wall)" | No | Phase 1 |
| `:443` | (docstring 散文、`mac_single_rate_bound₁` 説明) | "🟢ʰ Mathlib-wall residuals (real Mathlib gaps)" | H | "🟢ʰ Mathlib-wall residuals" → "Mathlib-wall residuals (joint-typicality-multi wall)" | No | Phase 1 |
| `:448` | `mac_single_rate_bound₁` | "genuine Fano + per-letter chain-rule derivation" — body は `mac_rate_le_of_fano hn ...` で純構成 derive | P (entropy-level hyp pass-through) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。body は genuine derive、entropy-level Fano + chain hyp が壁 (joint-typicality-multi)。signature 維持で body sorry に降格、または signature を維持して docstring 散文だけ修正の auditor 判定対象 |
| `:473` | `mac_single_rate_bound₂` | mirror of `_bound₁` | P | 同上 | No | Phase 2.1。同様の auditor 判定対象 |
| `:501` | `mac_sum_rate_bound` | "genuine Fano + per-letter chain-rule derivation" for joint message | P | 同上 | No | Phase 2.1 |
| `:534` | (docstring 散文、`mac_capacity_region_outer_bound` 説明) | "**genuine / honest-🟢ʰ converse**, no longer circular" | H | docstring refine | No | Phase 1 |
| `:558` | (docstring 散文) | "honest-🟢ʰ: the joint-message Fano discharge is not yet a project lemma" | H | "honest-🟢ʰ" 削除、本文の意味は保つ | No | Phase 1 |
| `:563` | (docstring 散文) | "honest-🟢ʰ: the `I(X^n;Y^n|·) ≤ n·I(X;Y|·)` chain rule" | H | 同上 | No | Phase 1 |
| `:576` | `mac_capacity_region_outer_bound` | entropy-level Fano + chain + cleanup ×3 pass-through、body は `mac_region_combine ... (mac_rate_le_of_fano ...)` ×3 で純構成 derive | P | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。MAC converse の headline、auditor 判定対象 (entropy-level hyp は precondition か load-bearing か) |
| `:648` | `mac_capacity_region_outer_bound_three_bounds` | 三 cut-bound hypothesis から `mac_region_combine` で region 構築 | P (three cut bound pass-through、load-bearing 度低) | `@residual(plan:mac-bc-sorry-migration-plan)` (auditor 委任) | No | Phase 2.1。`InMACCapacityRegion` の constructor だけ呼ぶ slim wrapper、変動 hyp 寄り |
| `:747` | (docstring 散文、`mac_capacity_region_inner_bound` 説明) | "achievability side)** — **honest-🟢ʰ, non-circular, error-carrying**" | H | docstring refine | No | Phase 1 |
| `:771` | `mac_capacity_region_inner_bound` | `MACJointTypicalityAchievable W ...` を hypothesis、body は `h_jt h_strict` modus ponens | P (load-bearing predicate consumer — joint-typicality-multi wall) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。MAC inner bound の headline、wall = joint-typicality-multi |
| `:788` | `mac_capacity_region_inner_bound_bundled_strict` | 同上 + `InMACCapacityRegion` の `≤` 入力を strict に変換する utility | P | 同上 | No | Phase 2.1 |
| `:821` | `mac_capacity_region_consistent` | 上記 outer + inner の two-side combine | P (両方を bundle) | 同上 | No | Phase 2.1 |

### MAC family — `MACFanoConverseBody.lean` (5 件: suspect 4 + 散文 🟢ʰ 1)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:265` | `mac_single_rate_bound₁_with_fano` | `d₁ : MACFanoEntropyData ...` + chain + cleanup → `mac_single_rate_bound₁_with_body` 経由 | P | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。entropy-level data + chain + cleanup の genuine bridge、auditor 判定対象 |
| `:280` | `mac_single_rate_bound₂_with_fano` | mirror | P | 同上 | No | Phase 2.1 |
| `:299` | `mac_capacity_region_outer_bound_with_per_user_fano` | `d₁/d₂ : MACFanoEntropyData` + joint Fano + chain + cleanup → 両 user 方向は genuine Fano-backed | P (per-user は genuine、joint-fano は wall pass-through) | 同上 | No | Phase 2.1。per-user 方向は genuine、joint 方向が `joint-typicality-multi` wall |
| `:332` | (docstring 散文、`mac_capacity_region_outer_bound_of_measure` 説明) | "all per-letter chain bounds remain the honest-🟢ʰ entropy-level inputs" | H | "honest-🟢ʰ" 削除、real Mathlib gap 言及残す | No | Phase 1 |
| `:338` | `mac_capacity_region_outer_bound_of_measure` | `μ : Measure Ω` + 各種 measure regularity + entropy uniform/decomp 識別 + joint Fano + chain + cleanup → per-user 方向は genuinely Fano-backed via `macFanoEntropyData_of_measure` | P (per-user 方向 genuine、joint-fano + chain は entropy-level hyp pass-through) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。最も genuine な wiring (measure → entropy → fano)、auditor 判定対象 (signature を維持して docstring だけ refine する選択肢あり) |

### MAC family — `MACBodyDischarge.lean` (2 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:609` | `mac_capacity_region_inner_bound_with_body` | `MACJointTypicalityAchievable` hypothesis を inner_bound にそのまま forward | P (純 forwarder) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。`mac_capacity_region_inner_bound` への transitive forwarder、auditor 判定対象 (純 forwarder = タグ削除のみ可能性) |
| `:650` | `mac_capacity_region_with_body_two_side` | outer + inner の two-side combine、body discharge layer 適用版 | P (outer + inner forwarder) | 同上 | No | Phase 2.1 |

### MAC family — `MACCornerPoint.lean` (2 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:374` | `mac_capacity_region_subset_pentagon` | `IsMACTimeSharingHyp` hypothesis をそのまま `h_region` に適用 | P (load-bearing predicate consumer — time-sharing wall) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1。`IsMACTimeSharingHyp` 自体は load-bearing claim (`InMACCapacityRegion → pentagon`)、wall = time-sharing (`mac-time-sharing-discharge-*` 別 plan) |
| `:388` | `mac_capacity_region_is_pentagon` | 上の wrapper + reverse direction (`mac_pentagon_subset_region`) を `eq_of_subset_of_subset` で合成 | P (`mac_capacity_region_subset_pentagon` 経由 transitive) | 同上 | No | Phase 2.1 |

### MAC family — `MACL1Discharge.lean` (1 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:533` | `mac_capacity_region_inner_bound_with_joint_typ_aep` | `MACJointTypicalityAchievable` hypothesis を inner_bound に forward (thin partial-discharge wrapper) | P (純 forwarder) | `@residual(plan:mac-l1-discharge-moonshot-plan)` | No | Phase 2.1。**slug は別 plan** (`mac-l1-discharge-moonshot-plan`) — Phase L-MAC1 partial discharge の closure 担当が異なる |

### MAC family — `MACPerEventAEPDecay.lean` (1 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:420` | `mac_capacity_region_consistent_of_perEvent` | per-event AEP decay + entropy-level Fano + chain + cleanup → outer + inner combine。本体は `mac_capacity_region_outer_bound` + `mac_random_codebook_markov_of_perEvent` を分割呼出 | P (outer side wall + inner side wall) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.1 |

### BC family — `BroadcastChannel.lean` (15 件: suspect 6 + 散文 🟢ʰ 9)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:41` | (docstring 散文、ファイル冒頭の outer-bound 説明) | "/ honest-🟢ʰ (R₁ conditional), non-circular**" | H | docstring refine | No | Phase 1 |
| `:46` | (docstring 散文) | "chain remain honest-🟢ʰ entropy-level inputs" | H | "honest-🟢ʰ" → 「real Mathlib gap (joint-typicality-multi wall)」言及 | No | Phase 1 |
| `:48` | (docstring 散文、inner-bound 説明) | "**honest-🟢ʰ, non-circular, error-carrying**" | H | docstring refine | No | Phase 1 |
| `:83` | (docstring 散文) | "rule remain honest-🟢ʰ (real Mathlib gaps)" | H | 同上 | No | Phase 1 |
| `:416` | (docstring 散文、`bc_common_rate_bound` 説明、🟢ʰ + ⚠️ HONESTY ALERT) | "🟢ʰ **load-bearing hypothesis — NOT a discharge.**" + "⚠️ The body is `:= h_commonRateBound_lbh`" | H + tier 5 defect (Phase 2.3) | Phase 1 で散文 refine (HONESTY ALERT は残す)、Phase 2.3 で signature 改変 | No | docstring 散文と signature の両方を touch。Phase 1 と Phase 2.3 で 2 stage |
| `:442` | `bc_common_rate_bound` | `(h_commonRateBound_lbh : R₂ ≤ I_u) : R₂ ≤ I_u := h_commonRateBound_lbh` — 仮説型 ≡ 結論型 | **tier 5 defect (`defect:circular` + `defect:launder`)** | Phase 2.3: signature から `h_commonRateBound_lbh` 削除、body sorry + `@residual(defect:circular)` | No | Phase 2.3。⚠️ HONESTY ALERT 著者明記、name laundering (`_lbh` suffix) |
| `:450` | (docstring 散文、`bc_private_rate_bound` 説明、🟢ʰ + ⚠️ HONESTY ALERT) | "🟢ʰ **load-bearing hypothesis — NOT a discharge.**" + "⚠️ The body is `:= h_privateRateBound_lbh`" | H + tier 5 defect | 同上 (Phase 1 散文 refine + Phase 2.3 signature 改変) | No | 同上 |
| `:474` | `bc_private_rate_bound` | mirror of `bc_common_rate_bound` | **tier 5 defect (`defect:circular` + `defect:launder`)** | 同上 | No | Phase 2.3 |
| `:535` | (docstring 散文、`bc_capacity_region_outer_bound` 説明) | "**genuine (R₂) / honest-🟢ʰ (R₁ conditional) converse**, no longer circular" | H | docstring refine | No | Phase 1 |
| `:560` | (docstring 散文) | "honest-🟢ʰ: the conditional Fano on `W₁ → Y₁^n | U^n` together with the degradation Markov chain is not yet a project lemma" | H | "honest-🟢ʰ" 削除、内容散文残す | No | Phase 1 |
| `:565` | (docstring 散文) | "inequalities (honest-🟢ʰ)" | H | 同上 | No | Phase 1 |
| `:595` | `bc_capacity_region_outer_bound_corner_limit` | `bc_capacity_region_outer_bound` の corner limit (`ε ≤ 0`) を `linarith` で扱う | P (transitive wrapper) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.2 |
| `:745` | `bc_capacity_region_inner_bound` | `BCSuperpositionAchievable W ...` hypothesis、body `h_ach h_strict` modus ponens | P (load-bearing predicate consumer — joint-typicality-multi wall) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.2。BC inner bound headline |
| `:769` | `bc_capacity_region_inner_bound_bundled_strict` | 同上 + `InBCCapacityRegion` の `≤` を strict に変換 | P | 同上 | No | Phase 2.2 |
| `:802` | `bc_capacity_region_consistent` | outer + inner の two-side combine | P (両方 bundle) | 同上 | No | Phase 2.2 |

注: `bc_capacity_region_outer_bound` (`BroadcastChannel.lean:574`) は本ファイル内で `@audit:suspect`
を持たない (verbatim 確認、`rg -B5 'bc_capacity_region_outer_bound\b' Common2026/Shannon/BroadcastChannel.lean`)。
**outer bound headline 本体は本 plan の sweep 対象外** — 既に genuine entropy-level Fano + chain
pass-through 形で publish 済、suspect 削除作業は corner_limit / inner_bound 等周辺 wrapper のみ。

### BC family — `BroadcastChannelExistenceBridgeBody.lean` (4 件: suspect 3 + 散文 🟢ʰ 1)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:290` | (docstring 散文、`bc_random_codebook_markov_of_ensemble` 説明、🟢ʰ + ⚠️ Honest-rebrand caveat) | "🟢ʰ **load-bearing posture — predicate-degenerate downstream.**" + "⚠️ **Honest-rebrand caveat (the produced predicate is operationally degenerate).**" | H + tier 5 defect (Phase 2.3) | Phase 1 散文 refine (HONESTY ALERT は残す)、Phase 2.3 で body sorry 化 | No | docstring 散文 + body 両方 touch |
| `:313` | `bc_random_codebook_markov_of_ensemble` | `IsBCBonferroniEnsembleDecay → IsBCRandomCodebookMarkov` の bridge、本体は genuine averaging を計算するが下流 predicate の operational gap で witness を `_C₀` で discard | **tier 5 defect (`defect:degenerate`)** | Phase 2.3: body sorry + `@residual(defect:degenerate)` (signature は touch せず、下流 `IsBCRandomCodebookMarkov` の predicate redesign 待ち) | No | Phase 2.3。本 plan は predicate redesign 範囲外 (`broadcast-channel-moonshot-plan` 配下 escalate) |
| `:371` | `bc_inner_bound_with_ensemble_averaging` | `IsBCBonferroniEnsembleDecay` + strict rate → `BCRandomCodebookAveraging` (`bc_inner_bound_with_averaging` 経由) | P (wrapper、predicate-degenerate な `bc_random_codebook_markov_of_ensemble` を呼ぶが本 wrapper 自身は genuine modus ponens) | `@residual(plan:mac-bc-sorry-migration-plan)` | No | Phase 2.2。wrapper 自身は honest だが上流が defect なので transitive 性を散文化 |
| `:390` | `bc_inner_bound_with_ensemble_averaging_bundled` | 上記の `InBCCapacityRegion` bundled 形 | P (同上) | 同上 | No | Phase 2.2 |

### BC family — `BroadcastChannelSuperposition.lean` (1 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:546` | `bc_capacity_region_inner_bound_with_superposition_aep` | `BCSuperpositionAchievable` hypothesis を `bc_capacity_region_inner_bound` に forward (thin partial-discharge wrapper) | P (純 forwarder) | `@residual(plan:mac-bc-sorry-migration-plan)` | **MAC↔BC 内部** (`import MACL1Discharge` 経由 transitive) | Phase 2.2。BC superposition の L-BC2 partial discharge entry。本 plan で完結、削除提案禁止 |

### BC family — `BroadcastChannelSuperpositionBody.lean` (1 件 suspect)

| file:line | decl 名 | 現タグ / 核 (verbatim 1 行) | パターン | 削除/置換予定タグ | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `:836` | `bc_capacity_region_inner_bound_with_superposition_body` | `bc_capacity_region_inner_bound_with_superposition_aep` への forwarder (body discharge layer 適用版) | P (純 forwarder) | `@residual(plan:mac-bc-sorry-migration-plan)` | **MAC↔BC 内部** (`import MACBodyDischarge` 経由 transitive) | Phase 2.2。BC superposition body discharge entry |

### 集計 (パターン別)

- V (variational pass-through、タグ削除のみ): **0 件**
- C (in-tree constructive、既に純構成的): **0 件**
- H (散文 🟢ʰ、docstring refine のみ): **21 件** (MAC 11 + BC 10、いずれも tier 4 vocabulary
  廃止 — Phase 1 で処理。うち 3 件は Phase 2.3 の tier 5 defect の docstring 部分と重複、Phase
  1 で散文 refine 後 Phase 2.3 で signature 改変するという 2 stage 設計)
- P (suspect: load-bearing hypothesis / predicate consumer の sorry 化、Phase 2.1 / 2.2):
  **25 件** (MAC 17 - 9 散文 = 8、+ MACFanoConverseBody 4 + MACBodyDischarge 2 + MACCornerPoint 2
  + MACL1Discharge 1 + MACPerEventAEPDecay 1 = 18、BC 11 - 9 散文 = 2 (outer corner_limit のみ、
  outer headline は suspect なし)、+ BroadcastChannel inner bound 3 + BC EBridge 2 + BC
  Superposition 1 + BC SuperpositionBody 1 = 7。合計 25 件)
- **tier 5 defect** (Phase 2.3): **3 件** (BC `bc_common_rate_bound` / `bc_private_rate_bound`
  の circular + launder × 2、BC `bc_random_codebook_markov_of_ensemble` の degenerate × 1)

**合計 = 21 (H) + 25 (P) + 3 (defect) = 49 件** (verbatim 集計一致)

### `⚠ HONESTY ALERT` / `FALSE` 検出 (R8, Pattern H)

verbatim 検証: `rg -n '⚠|HONESTY ALERT|FALSE' Common2026/Shannon/MultipleAccessChannel.lean
Common2026/Shannon/BroadcastChannel.lean Common2026/Shannon/MACFanoConverseBody.lean
Common2026/Shannon/BroadcastChannelExistenceBridgeBody.lean Common2026/Shannon/MACBodyDischarge.lean
Common2026/Shannon/MACCornerPoint.lean Common2026/Shannon/BroadcastChannelSuperposition.lean
Common2026/Shannon/BroadcastChannelSuperpositionBody.lean Common2026/Shannon/MACL1Discharge.lean
Common2026/Shannon/MACPerEventAEPDecay.lean`

| file:line | 種類 | 内容 | 本 plan での扱い |
|---|---|---|---|
| `BroadcastChannel.lean:431` | ⚠️ HONESTY ALERT | `bc_common_rate_bound` docstring "The body is `:= h_commonRateBound_lbh`. The multi-hundred-line ingredients ... are NOT discharged here" | **本 sweep の Phase 2.3 対象** — tier 5 defect (`defect:circular`)、scope 内 (Pattern H で言及される「scope 外として別 plan 化」する典型 false-predicate ではなく、circular bundling 系 defect。本 plan で sorry-based に migrate するのが正しい流儀) |
| `BroadcastChannel.lean:466` | ⚠️ HONESTY ALERT | `bc_private_rate_bound` 同上 | 同上、Phase 2.3 |
| `BroadcastChannelExistenceBridgeBody.lean:297` | ⚠️ Honest-rebrand caveat | `bc_random_codebook_markov_of_ensemble` "the produced predicate is operationally degenerate" — 下流 predicate `IsBCRandomCodebookMarkov` の operational gap が原因の vacuous shape。本 wrapper の body は genuine averaging を実行するが witness を discard | **Phase 2.3 対象 (`defect:degenerate`)、ただし predicate redesign は本 plan scope 外** — 下流 `IsBCRandomCodebookMarkov` の vacuous shape (operational gap) の修正は `broadcast-channel-moonshot-plan` 配下別 plan に escalate。本 plan は body のみ sorry 化、predicate signature は touch しない |
| `MACPerEventAEPDecay.lean:44` | ⚠ なし、`## Known Mathlib gap (passed through as a primitive, not sorry)` | docstring section header | Phase 1 / 2 の対象外、touch しない (ファイル運営上の prose) |
| `MACPerEventAEPDecay.lean:56` | ⚠ なし、`sorry-free.` | 上記 section 内の現状記述 | 同上 |

**HONESTY ALERT 検出 = 3 件、すべて Phase 2.3 tier 5 defect 対象内**。Pattern H 適用で
「scope 外として別 plan 化」する性質の false-predicate ではなく、**本 plan の Phase 2.3 で
silent fix せず sorry-based migration する典型例**。`MACPerEventAEPDecay.lean` の 2 hits は
section header 内の散文で、対象外。

### 未決事項に escalate される条件

- **predicate redesign** (`IsBCRandomCodebookMarkov` の operational gap): 本 plan scope 外、
  `broadcast-channel-moonshot-plan` 配下別 plan に escalate (未決事項 #4 参照)
- **`bc_common_rate_bound` / `bc_private_rate_bound` の genuine 形再設計**: Phase 2.3 で sorry
  化後、Phase 2.3.b で MAC 側と同型の entropy-level Fano + chain pass-through 形に signature
  再設計するか、auditor 判定対象 (未決事項 #2)

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 49 件全件を verbatim 確認 (`rg -n` でタグ行検出後 docstring + signature 1-3 行を実コード Read)
- [x] パターン分類 (H / P + 細分 tier 5 defect)
- [x] cross-family entanglement 確認 (MAC↔BC 内部 cross-import 2 件、MAC/BC → Relay の prose 言及は entanglement カウント外)
- [x] HONESTY ALERT 3 件検出 + 扱い決定 (Phase 2.3 内処理、別 plan escalate なし)
- [x] 既存 `sorry` word-boundary 計数 `0` 件 (Pilot Pattern D 適用、`MACPerEventAEPDecay.lean:44/56` の 2 hit は section header 散文)
- [x] Wall name register `joint-typicality-multi` 既登録確認 (新規追加なし、`plan:` slug で揃える)

**proof-log**: no (mechanical 在庫確認)。

### Phase 1 — H (散文 🟢ʰ) cleanup (低 risk、新規 sorry なし、docstring refine のみ) 📋

- [ ] **1.1** `MultipleAccessChannel.lean` の散文 `🟢ʰ` 言及 9 件 (line 42 / 47 / 50 / 86 / 443 / 534 / 558 / 563 / 747) を docstring refine:
  - "honest-🟢ʰ" → 散文「real Mathlib gap (joint-typicality-multi wall)」または単に「real Mathlib gap」
  - 「**genuine / honest-🟢ʰ, non-circular**」のような prose は意味を保ったまま tier 4 vocabulary を除去 (「**genuine, non-circular**」など)
  - 本体 type-check 影響なし
  - signature 改変なし
  - `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` で type-check done 確認 (docstring refine だけなので 0 errors 期待)
- [ ] **1.2** `MACFanoConverseBody.lean` の散文 `🟢ʰ` 1 件 (line 332) を docstring refine。同様の手順。
- [ ] **1.3** `BroadcastChannel.lean` の散文 `🟢ʰ` 9 件 (line 41 / 46 / 48 / 83 / 416 / 450 / 535 / 560 / 565) を docstring refine:
  - line 416 (`bc_common_rate_bound` docstring) と line 450 (`bc_private_rate_bound` docstring) は **Phase 2.3 で signature 改変も伴う tier 5 defect の docstring 部分** — Phase 1 では tier 4 vocabulary `🟢ʰ` のみ削除、`⚠️ HONESTY ALERT` の散文と「The body is `:= h_*RateBound_lbh`」は Phase 2.3 完了まで残す (Phase 2.3 で signature が改変されたら同時に docstring も書換)
- [ ] **1.4** `BroadcastChannelExistenceBridgeBody.lean` の散文 `🟢ʰ` 1 件 (line 290) を docstring refine。`⚠️ Honest-rebrand caveat` 散文は Phase 2.3 まで残す。
- [ ] **1.5** Phase 1 完了時:
  ```bash
  rg -n '🟢ʰ' Common2026/Shannon/MultipleAccessChannel.lean Common2026/Shannon/MACFanoConverseBody.lean Common2026/Shannon/BroadcastChannel.lean Common2026/Shannon/BroadcastChannelExistenceBridgeBody.lean | wc -l
  ```
  期待値 = **0**。各 file `lake env lean` 0 errors。

**Phase 1 DoD**: `🟢ʰ` 0 件、新規 `sorry` 0 件、各 file `lake env lean` 0 errors、`⚠️ HONESTY ALERT` は Phase 2.3 対象 3 件 (BroadcastChannel.lean:431/466, BroadcastChannelExistenceBridgeBody.lean:297) のみ残存。

**proof-log**: no (mechanical docstring refine、判断境界なし)。

### Phase 1.5 — audit-1 (Phase 1 全件) 📋

- [ ] **1.5.1** orchestrator は `honesty-auditor` を起動 (or `general-purpose` + SoT brief)。対象:
  - Phase 1 の散文 refine 21 件 (MAC 10 + BC 10 + 重複 1 = 21 件 — `BroadcastChannel.lean:416/450` の docstring と `BroadcastChannelExistenceBridgeBody.lean:290` の docstring は Phase 2.3 と連動する部分 refine のみ)。
  - 確認項目: tier 4 vocabulary `🟢ʰ` が完全に除去されているか、`⚠️ HONESTY ALERT` 散文が Phase 2.3 用に保たれているか、意味の歪曲がないか。
- [ ] **1.5.2** verdict 受領:
  - `ok` → Phase 2.1 着手
  - `questionable` → docstring 微調整 (vocabulary 揺れ等)、Phase 2 進行
  - `defect` → Phase 1 で生成した散文を再書換 (まれ、docstring refine だけなので tier 5 defect 化はほぼ起きない想定)

**proof-log**: no (audit verdict 1 件のみ、判断記録不要)。

### Phase 2.1 — P retreat (MAC family、25 件中 MAC 18 件) 📋

各 declaration の sweep 単位は以下:

- [ ] **2.1.1** `MultipleAccessChannel.lean` 8 件 (line 448 / 473 / 501 / 576 / 648 / 771 / 788 / 821):
  - signature **改変しない** (entropy-level Fano + chain + cleanup hypothesis は precondition として保持、auditor 判定で load-bearing 性が確定したら別 plan で再 sweep)
  - body を `sorry` に置換、docstring 末尾の `@audit:suspect(mac-moonshot-plan)` を `@residual(plan:mac-bc-sorry-migration-plan)` に書換
  - 散文 docstring の technical content (どの inequality を pass-through するかの説明) は保持
- [ ] **2.1.2** `MACFanoConverseBody.lean` 4 件 (line 265 / 280 / 299 / 338):
  - 同様。`MACFanoEntropyData` + chain + cleanup hypothesis は precondition 保持
  - 特に `mac_capacity_region_outer_bound_of_measure` (line 338) は measure-level の genuine wiring (`macFanoEntropyData_of_measure` 経由) で per-user 方向は本来 genuinely Fano-backed — auditor が「per-user 方向は constructive recovery 可能」と判定すれば L-MIG-1 で復元 (signature の measure-level hyp を残し body も genuine 保つ)
- [ ] **2.1.3** `MACBodyDischarge.lean` 2 件 (line 609 / 650):
  - signature 維持、body sorry + `@residual(plan:mac-bc-sorry-migration-plan)`
  - `mac_capacity_region_inner_bound_with_body` は `mac_capacity_region_inner_bound` への transitive forwarder で、Phase 2.1.1 で `mac_capacity_region_inner_bound` を sorry 化すると本 declaration も transitive sorry に降格。docstring 散文で transitive 性を明示
- [ ] **2.1.4** `MACCornerPoint.lean` 2 件 (line 374 / 388):
  - signature 維持。`IsMACTimeSharingHyp` predicate consumer、time-sharing wall (本 plan scope 外)
  - body sorry + `@residual(plan:mac-bc-sorry-migration-plan)` — または `@residual(plan:mac-time-sharing-discharge-*)` に分けるかは auditor 委任 (未決事項 #3)
- [ ] **2.1.5** `MACL1Discharge.lean` 1 件 (line 533):
  - **slug は別 plan** `@residual(plan:mac-l1-discharge-moonshot-plan)` (`mac-l1-discharge-moonshot-plan` は L-MAC1 partial discharge の closure 担当 plan、本 declaration の closure 責任が本 plan ではなくそちら)
  - signature 維持、body sorry
- [ ] **2.1.6** `MACPerEventAEPDecay.lean` 1 件 (line 420):
  - signature 維持、body sorry + `@residual(plan:mac-bc-sorry-migration-plan)`
- [ ] **2.1.7** olean refresh (Pilot Pattern A):
  ```bash
  lake build Common2026.Shannon.MultipleAccessChannel
  lake build Common2026.Shannon.MACBodyDischarge
  lake build Common2026.Shannon.MACFanoConverseBody
  lake build Common2026.Shannon.MACCornerPoint
  lake build Common2026.Shannon.MACL1Discharge
  lake build Common2026.Shannon.MACPerEventAEPDecay
  ```
  続いて Phase 2.1 で touch した 6 file + 依存 file (`BroadcastChannelSuperposition` / `BroadcastChannelSuperpositionBody` — Phase 2.2 で sweep するが事前に olean refresh 確認のため) を各 `lake env lean` で再 verify。

**Phase 2.1 DoD**:
- MAC family 6 file で `@audit:suspect(mac-moonshot-plan)` / `(mac-l1-discharge-moonshot-plan)` 0 件
- `@residual(plan:mac-bc-sorry-migration-plan)` 17 件 + `@residual(plan:mac-l1-discharge-moonshot-plan)` 1 件
- 新規 `sorry` 18 件 (各 `@residual` 1 sorry)
- 各 file `lake env lean` 0 errors
- BC superposition 系の type-check が事前 olean refresh で stale でないことを確認

**proof-log**: yes (`docs/proof-logs/proof-log-mac-bc-sorry-migration-phase-2.1.md`)。理由: 18 件の sorry 化判定 (signature を維持するか hyp を削除するか) で auditor 委任が複数発生 — slug 配分 (`mac-bc-sorry-migration-plan` vs `mac-l1-discharge-moonshot-plan` vs `mac-time-sharing-discharge-*`) の判定理由を残す。

### Phase 2.2 — P retreat (BC family、25 件中 BC 7 件 = excluding 2 tier-5 defects) 📋

- [ ] **2.2.1** `BroadcastChannel.lean` 4 件 (line 595 / 745 / 769 / 802) — outer corner_limit + inner bound 3 件 (excluding tier 5 defects):
  - signature 維持、body sorry + `@residual(plan:mac-bc-sorry-migration-plan)`
  - 注: `bc_capacity_region_outer_bound` (line 574) は suspect なし、本 plan で **touch しない** (既に genuine entropy-level Fano + chain pass-through 形で publish 済)
- [ ] **2.2.2** `BroadcastChannelExistenceBridgeBody.lean` 2 件 (line 371 / 390) — `bc_random_codebook_markov_of_ensemble` は Phase 2.3 に分離、本 step では wrapper 2 件のみ:
  - signature 維持、body sorry + `@residual(plan:mac-bc-sorry-migration-plan)`
  - 上流 `bc_random_codebook_markov_of_ensemble` が Phase 2.3 で `defect:degenerate` 付き sorry 化されるため、本 2 件は transitive sorry 状態に降格。docstring 散文で transitive 性を明示
- [ ] **2.2.3** `BroadcastChannelSuperposition.lean` 1 件 (line 546):
  - signature 維持、body sorry + `@residual(plan:mac-bc-sorry-migration-plan)`
  - **MAC↔BC 内部 cross-import** (`import MACL1Discharge`) 経由で transitive 性あり、Phase 2.1.5 で MAC L1 discharge を sorry 化済なので本 declaration の body も transitive sorry
- [ ] **2.2.4** `BroadcastChannelSuperpositionBody.lean` 1 件 (line 836):
  - 同上、`import MACBodyDischarge` 経由 cross-import
- [ ] **2.2.5** olean refresh:
  ```bash
  lake build Common2026.Shannon.BroadcastChannel
  lake build Common2026.Shannon.BroadcastChannelExistenceBridgeBody
  lake build Common2026.Shannon.BroadcastChannelSuperposition
  lake build Common2026.Shannon.BroadcastChannelSuperpositionBody
  ```
  各 file `lake env lean` 再 verify。

**Phase 2.2 DoD**:
- BC family 4 file で `@audit:suspect(broadcast-channel-moonshot-plan)` 0 件 (Phase 2.3 対象 3 件を除く)
- `@residual(plan:mac-bc-sorry-migration-plan)` 8 件 (MAC 17 + BC 7 = 24 件、Phase 2.1 + 2.2 累計)
- 新規 `sorry` 累計 25 件
- 各 file `lake env lean` 0 errors

**proof-log**: no (Phase 2.1 と同質、新たな判断境界なし)。

### Phase 2.3 — defect retreat (tier 5 defect 3 件、signature 改変必須) 📋

- [ ] **2.3.1** `BroadcastChannel.lean:443` `bc_common_rate_bound`:
  - **defect 種類**: `defect:circular` (仮説型 ≡ 結論型) + `defect:launder` (`_lbh` suffix で「load-bearing hypothesis」と命名し signature が claim 通り扱っていない)
  - signature 改変: `(h_commonRateBound_lbh : R₂ ≤ I_u)` を **削除**。`(_c : BroadcastCode ...)` と `(R₂ I_u : ℝ)` の precondition は残す。結論型 `R₂ ≤ I_u` は変えない。
  - body: `:= h_commonRateBound_lbh` → `:= by sorry`
  - docstring 末尾の `@audit:suspect(broadcast-channel-moonshot-plan)` を `@residual(defect:circular)` に書換、`⚠️ HONESTY ALERT` 散文は **削除** (signature が defect 形でなくなった旨を反映)、本文の technical content (Fano / DPI / chain rule の説明) は保持
- [ ] **2.3.2** `BroadcastChannel.lean:475` `bc_private_rate_bound`:
  - 同様、`(h_privateRateBound_lbh : R₁ ≤ I_xy)` を削除、body sorry + `@residual(defect:circular)`
- [ ] **2.3.3** `BroadcastChannelExistenceBridgeBody.lean:314` `bc_random_codebook_markov_of_ensemble`:
  - **defect 種類**: `defect:degenerate` (下流 predicate `IsBCRandomCodebookMarkov` の operational gap で本体の genuine averaging witness が `obtain ⟨_C₀, _hC₀⟩` で discard される、predicate-degenerate downstream)
  - signature: **touch せず** (`(R₁ R₂ : ℝ) (h_ens : IsBCBonferroniEnsembleDecay ...)` のまま、predicate redesign は本 plan scope 外)
  - body: 現状 14 行の genuine averaging 計算 → `:= by sorry`
  - docstring 末尾の `@audit:suspect(broadcast-channel-moonshot-plan)` を `@residual(defect:degenerate)` に書換、`⚠️ Honest-rebrand caveat` 散文は **保持** (下流 predicate の operational gap が残存することを記録、未決事項 #4 で escalate)
  - **追加 docstring 散文**:
    ```
    Phase 2.3 retreat — `IsBCRandomCodebookMarkov` の operational gap (errBound
    が `_c` の error と link されない vacuous shape) のため、本 body の genuine
    averaging content は predicate 構造上 propagate しない。predicate redesign
    は `broadcast-channel-moonshot-plan` 配下別 plan に escalate (未決事項 #4)、
    本 declaration は redesign 完了後に再評価。
    ```
- [ ] **2.3.4** olean refresh (`BroadcastChannel` / `BroadcastChannelExistenceBridgeBody` を `lake build`)、続いて両 file + 依存先 `BroadcastChannelSuperposition` / `BroadcastChannelSuperpositionBody` を `lake env lean` で再 verify。signature 改変は `bc_common_rate_bound` / `bc_private_rate_bound` のみで dependent caller の rg 検索結果に依存:
  ```bash
  rg -l 'bc_common_rate_bound\|bc_private_rate_bound' Common2026/Shannon/
  ```
  caller があれば Phase 2.x で対応。

**Phase 2.3 DoD**:
- 3 件で `@audit:suspect` 0 件、`@residual(defect:circular)` 2 件、`@residual(defect:degenerate)` 1 件
- 新規 `sorry` 累計 28 件 (Phase 2.1 18 + Phase 2.2 7 + Phase 2.3 3)
- 各 file `lake env lean` 0 errors
- signature 改変による caller drift の有無を Phase 2.x で散文化対応

**proof-log**: yes (`docs/proof-logs/proof-log-mac-bc-sorry-migration-phase-2.3.md`)。理由: tier 5 defect 化の判定 (signature 改変範囲 + docstring 文言) と Phase 2.3.b (再設計判断) の根拠を残す。

### Phase 2.3.b — オプション (BC tier 5 defect の genuine 形再設計、auditor 委任) 📋

Phase 2.3 で sorry 化された 2 件 (`bc_common_rate_bound` / `bc_private_rate_bound`) について、
**MAC 側と同型の entropy-level Fano + chain pass-through 形に signature を再設計** するかは
honesty-auditor (Phase 2.4) の判定に委ねる。再設計時の参考形:

```lean
/-- (genuine entropy-level Fano + chain + cleanup derivation 形、MAC 側と整合) -/
theorem bc_common_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₂ Pe₂ I_marg_u I_u ε : ℝ)
    (h_fano : (n : ℝ) * R₂ ≤ I_marg_u + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_chain : I_marg_u ≤ (n : ℝ) * I_u)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I_u + ε :=
  bc_rate_le_of_fano hn R₂ I_marg_u I_u Pe₂ (Real.log (M₂ : ℝ)) ε h_fano h_chain h_cleanup
```

再設計判断: auditor が「Phase 2.3 の sorry 化は honesty 回復として正しいが、MAC 側との
形式整合を取るには signature 再設計が望ましい」と判定したら、本 step を実施。`bc_rate_le_of_fano`
は `BroadcastChannel.lean:511` に既に `private theorem` として存在し再利用可能 — visibility を
`theorem` (or `protected theorem`) に変更する追加判断が伴う (visibility 変更は CLAUDE.md 規約
で問題なし、`private` は file-scoped のため当該 file 内で公開すれば足りる)。

本 step が auditor で **不要** と判定されたら sorry 化のままで close (本 plan の DoD は
type-check done のみ、proof done は別 workstream)。

### Phase 2.x — ripple (caller drift handling, 散文 transitive 明示) 📋

- [ ] **2.x.1** caller 列挙:
  ```bash
  rg -l '(mac_single_rate_bound|mac_sum_rate_bound|mac_region_combine|mac_capacity_region_outer_bound|mac_capacity_region_outer_bound_three_bounds|mac_capacity_region_inner_bound|mac_capacity_region_inner_bound_bundled_strict|mac_capacity_region_consistent|mac_capacity_region_inner_bound_with_body|mac_capacity_region_with_body_two_side|mac_capacity_region_outer_bound_with_per_user_fano|mac_capacity_region_outer_bound_of_measure|mac_capacity_region_inner_bound_with_joint_typ_aep|mac_capacity_region_consistent_of_perEvent|mac_capacity_region_subset_pentagon|mac_capacity_region_is_pentagon|bc_capacity_region_outer_bound_corner_limit|bc_capacity_region_inner_bound|bc_capacity_region_inner_bound_bundled_strict|bc_capacity_region_consistent|bc_capacity_region_inner_bound_with_superposition_aep|bc_capacity_region_inner_bound_with_superposition_body|bc_inner_bound_with_ensemble_averaging|bc_inner_bound_with_ensemble_averaging_bundled|bc_common_rate_bound|bc_private_rate_bound|bc_random_codebook_markov_of_ensemble)' Common2026/Shannon/
  ```
  予想 caller:
  - 同 family 内 (MAC↔BC 内部 cross-import 経由): `BroadcastChannelSuperposition.lean` / `BroadcastChannelSuperpositionBody.lean` (Phase 2.2 で既に sorry 化済)
  - 同 family 内 wrapper file: `MACBodyDischarge.lean` / `MACFanoConverseBody.lean` / `MACPerEventAEPDecay.lean` 等 (Phase 2.1 で既に sorry 化済)
  - 上記以外の同 file 内 wrapper: 例えば `mac_capacity_region_outer_bound_corner_limit` (`MultipleAccessChannel.lean:606`、suspect なし) は `mac_capacity_region_outer_bound` を呼ぶ → transitive sorry に降格
  - MAC log-rate form (`mac_capacity_region_outer_bound_log_rate`、line 665、suspect なし) も同様 transitive
  - BC outer log-rate form (`bc_capacity_region_outer_bound_log_rate`、`BroadcastChannel.lean:639`、suspect なし) も同様
- [ ] **2.x.2** 各 caller について **transitive sorry の docstring 散文** を追加 (Pilot Pattern C):
  ```
  Transitive `sorry` via `<upstream decl>` (Phase 2.{1,2,3} retreat). No
  additional `@residual` tag attached — closure responsibility is shared
  with the upstream declaration's `@residual(plan:mac-bc-sorry-migration-plan)`
  or `@residual(defect:circular|degenerate)`.
  ```
- [ ] **2.x.3** olean refresh + 全 file `lake env lean` 再 verify。Phase 2.x で sorry 件数は
  純増しない (transitive はタグ付与しないため)、ただし implicit な sorry warning は dependent
  file で増える (Lean が transitive `sorry` を warning として再表示)。
- [ ] **2.x.4** MAC↔BC 内部 cross-import 経由の transitive について、`MACL1Discharge.lean` ↔ `BroadcastChannelSuperposition.lean`、`MACBodyDischarge.lean` ↔ `BroadcastChannelSuperpositionBody.lean` の 2 経路を確認 (Phase 2.1.5 + Phase 2.2.5 の olean refresh で吸収済)。

**Phase 2.x DoD**:
- 全 caller の transitive sorry が散文化済、即興 vocabulary 0 件
- 各 file `lake env lean` 0 errors

**proof-log**: no (mechanical 散文追加)。

### Phase 2.4 — audit-2 (Phase 2.1 / 2.2 / 2.3 / 2.x 全件) 📋

- [ ] **2.4.1** orchestrator は `honesty-auditor` を起動。対象:
  - Phase 2.1: 18 件 (MAC family の P retreat、entropy-level hypothesis pass-through が load-bearing か precondition か境界判定)
  - Phase 2.2: 7 件 (BC family の P retreat)
  - Phase 2.3: 3 件 (tier 5 defect の signature 改変 + docstring 整合性)
  - Phase 2.x: caller drift の散文化 vocabulary 整合 + 即興 tag 不在確認
  - Phase 2.3.b: BC `bc_common_rate_bound` / `bc_private_rate_bound` の MAC 側との整合性 — genuine 形再設計が望ましいか判定
- [ ] **2.4.2** verdict 受領 + 修正対応 (Phase 1.5 同様):
  - `ok` → Phase V 着手
  - `questionable` → docstring refine or 散文追記、Phase V 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase V 進行前に解決
- [ ] **2.4.3** Phase 2.3.b 実施判断: auditor が「genuine 形再設計が望ましい」と判定したら Phase 2.3.b を後段で実施 (新規 commit)、本 plan に追記。判定が「sorry 化のままで close」なら本 plan は Phase 2.3 状態で closure。

**proof-log**: yes (auditor verdict + 境界判定結果 + 2.3.b 実施判断を proof-log に追記)。

### Phase V — verify + 計画の集約 📋

- [ ] **V.1** 全 10 file で `lake env lean` 確認:
  ```bash
  for f in Common2026/Shannon/MultipleAccessChannel.lean \
           Common2026/Shannon/BroadcastChannel.lean \
           Common2026/Shannon/MACFanoConverseBody.lean \
           Common2026/Shannon/BroadcastChannelExistenceBridgeBody.lean \
           Common2026/Shannon/MACBodyDischarge.lean \
           Common2026/Shannon/MACCornerPoint.lean \
           Common2026/Shannon/BroadcastChannelSuperposition.lean \
           Common2026/Shannon/BroadcastChannelSuperpositionBody.lean \
           Common2026/Shannon/MACL1Discharge.lean \
           Common2026/Shannon/MACPerEventAEPDecay.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```
  signature 改変があった file (Phase 2.3 で `BroadcastChannel.lean` / `BroadcastChannelExistenceBridgeBody.lean`) は事前に `lake build` で olean refresh (Pilot Pattern A)。
- [ ] **V.2** 集計コマンド実行:
  ```bash
  TARGETS="Common2026/Shannon/MultipleAccessChannel.lean Common2026/Shannon/BroadcastChannel.lean Common2026/Shannon/MACFanoConverseBody.lean Common2026/Shannon/BroadcastChannelExistenceBridgeBody.lean Common2026/Shannon/MACBodyDischarge.lean Common2026/Shannon/MACCornerPoint.lean Common2026/Shannon/BroadcastChannelSuperposition.lean Common2026/Shannon/BroadcastChannelSuperpositionBody.lean Common2026/Shannon/MACL1Discharge.lean Common2026/Shannon/MACPerEventAEPDecay.lean"
  rg -c '@audit:suspect' $TARGETS | awk -F: '{s+=$2} END {print "suspect:", s}'                           # = 0
  rg -c '🟢ʰ' $TARGETS | awk -F: '{s+=$2} END {print "🟢ʰ:", s}'                                          # = 0
  rg -c '@residual\(plan:mac-bc-sorry-migration-plan\)' $TARGETS | awk -F: '{s+=$2} END {print "residual(plan:mac-bc):", s}'  # ~24
  rg -c '@residual\(plan:mac-l1-discharge-moonshot-plan\)' $TARGETS | awk -F: '{s+=$2} END {print "residual(plan:mac-l1):", s}'  # = 1
  rg -c '@residual\(defect:circular\)' $TARGETS | awk -F: '{s+=$2} END {print "residual(defect:circular):", s}'   # = 2
  rg -c '@residual\(defect:degenerate\)' $TARGETS | awk -F: '{s+=$2} END {print "residual(defect:degenerate):", s}'  # = 1
  ```
  期待値合計: suspect = 0、🟢ʰ = 0、residual 合計 = 28 (24 + 1 + 2 + 1)、sorry word-boundary 件数 = 28 (各 residual 1 sorry)。
  注: `⚠️ HONESTY ALERT` 散文は Phase 2.3 で signature が改変済になった旨を反映して削除済、`⚠️ Honest-rebrand caveat` 散文のみ 1 件残る (`BroadcastChannelExistenceBridgeBody.lean`、未決事項 #4 の予約)。
- [ ] **V.3** 親 plan banner 更新:
  - `mac-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了 (`docs/shannon/mac-bc-sorry-migration-plan.md` 参照)、本 plan の pass-through 設計は変更なし。joint-typicality-multi wall + time-sharing wall (BC outer + MAC corner-point pentagon) が未 closure として残る」を追記。
  - `broadcast-channel-moonshot-plan.md` 冒頭 banner に同様の追記 + 「tier 5 defect 3 件 (`bc_common_rate_bound` / `bc_private_rate_bound` / `bc_random_codebook_markov_of_ensemble`) を sorry-based に migrate、`bc_common/private_rate_bound` の genuine 形再設計は Phase 2.3.b に依る」を明示。
  - `mac-l1-discharge-moonshot-plan.md` 冒頭 banner に「`mac_capacity_region_inner_bound_with_joint_typ_aep` の sorry 化 (本 plan で migration 完了、closure 担当は本 plan のまま)」を追記。
- [ ] **V.4** 知見を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレート / runbook に反映:
  - MAC↔BC 内部 cross-import (BC superposition → MAC L1 / BC superposition body → MAC body discharge) を含む family は 1 plan で統合 sweep が必須 — Plan 分割判断の事例として runbook に追記
  - `joint-typicality-multi` wall name register 既存活用の事例 (新規追加なし、`plan:` slug で揃える Hoeffding/Cramér/WynerZiv 踏襲) として記録
  - tier 5 defect 3 件 (BC) の inline detection が planner 段階で可能だった事実 → 後続 family の suspect inventory でも `⚠ HONESTY ALERT` 検出を必須化済 (Pattern H、本 plan で適用済)、運用継続
  - BC tier 5 defect の Phase 2.3.b 再設計判断パターン: MAC 側に同型 genuine derivation が存在する場合、family sweep 中に signature 再設計の選択肢を auditor 委任する手順を runbook に追加検討

## 撤退ライン

- **L-MIG-1 (variational / regularity hyp の load-bearing 判定が auditor で変動)**:
  Phase 2.1 / 2.2 の 25 件 P retreat declarations について auditor が「entropy-level Fano +
  chain + cleanup hypothesis は load-bearing でなく precondition」と判定したら、暫定の
  `@residual(plan:mac-bc-sorry-migration-plan)` を維持しつつ docstring 散文を refine — load-bearing
  性が「`joint-typicality-multi` wall への pass-through」ではなく「変動 hyp」になる場合は
  純タグ削除に降格 (該当件数 0 想定だが auditor 判定対象)。Phase 2.4 audit-2 で確定。

- **L-MIG-2 (Phase 2.3 で BC tier 5 defect の signature 改変が cross-family drift を起こす)**:
  `bc_common_rate_bound` / `bc_private_rate_bound` の signature 改変 (`h_*RateBound_lbh` 削除)
  が **本 file 外** で caller を持つかは Phase 2.x.1 の `rg` で再確認。caller があれば signature
  改変は影響範囲が広く、L-MIG-2 発動 — Phase 2.3 を **保留**、tier 5 defect 状態のまま docstring
  に `@audit:retract-candidate(circular)` を付与する暫定回避案を採用 (silent fix 禁止のため、必ず
  defect マーカーは残す)。再 sweep は別 session で MAC 側 entropy-level Fano + chain pass-through
  形と統合再設計する。

- **L-MIG-3 (Phase C/D closure / 別 workstream と方向衝突)**: 本 plan の sorry 化が
  `mac-l1-discharge-moonshot-plan` / `mac-l2-discharge-*` / `bc-converse-fano-discharge-*` 等の
  進行と衝突 (例: 後続 plan が `mac_capacity_region_inner_bound` の signature を closure 入口
  として再利用、または `bc_random_codebook_markov_of_ensemble` の vacuous predicate を別形で
  redesign 中) した場合、本 plan は該当 declaration を **scope 外**にして Phase 2.x で skip、
  当該 declaration の `@audit:suspect` を残す (incidental migration を後続 sweep に委ねる)。

- **L-MIG-4 (Approach 変更: pilot scope 縮減)**:
  Phase 2.1 / 2.2 / 2.3 / 2.x の 28 件 + 散文 21 件 = 49 件 sweep が 1-2 session で完走しない /
  honesty-auditor が DEFECT を多発させる場合、`MultipleAccessChannel.lean` 17 件 +
  `BroadcastChannel.lean` 15 件 = 32 件のみで pilot を close し、`MACFanoConverseBody.lean`
  以降 + `BroadcastChannelSuperposition.lean` 以降は後続 session に分離 (Hoeffding pilot の
  L-MIG-4 相当)。または file 単位で 1 file ずつ閉じて段階的に commit (`HoeffdingInteriorBody.lean
  4 件のみで pilot を close` の前例)。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **散文 `🟢ʰ` refine 強度** (auditor 判定対象 + planner 提案):
   - "honest-🟢ʰ" → "real Mathlib gap (joint-typicality-multi wall)" のような置換でいいか、
     wall name を docstring に明示することで `audit-tags.md`「Wall name register」と整合性を
     取るか。planner 推奨: **wall name を明示** (将来 shared sorry 補題化したときの参照点と
     して有用)。auditor 判定対象。

2. **BC tier 5 defect の Phase 2.3.b 再設計判断** (auditor 判定対象 + Phase 2.4 verdict 依存):
   - `bc_common_rate_bound` / `bc_private_rate_bound` を MAC 側と同型の genuine 形に再設計
     するか (`bc_rate_le_of_fano` を public 化 + entropy-level Fano + chain + cleanup hypothesis
     形に signature 改変)。`bc_rate_le_of_fano` は既に `private` で存在するため visibility 変更
     のみで再利用可能。**Phase 2.4 auditor verdict 待ち**。

3. **slug 配分** (auditor 判定対象):
   - 28 declarations のうち 26 件は `@residual(plan:mac-bc-sorry-migration-plan)`、1 件は
     `@residual(plan:mac-l1-discharge-moonshot-plan)`、3 件は `@residual(defect:circular|degenerate)`
     という配分。`MACCornerPoint.lean` 2 件 (`mac_capacity_region_subset_pentagon` /
     `mac_capacity_region_is_pentagon`) の closure 担当は `mac-time-sharing-discharge-*` (別 plan)
     とも解釈可能 — slug を `@residual(plan:mac-time-sharing-discharge-moonshot-plan)` (該当 plan
     存在確認後) に細分化するか、それとも本 plan slug で統一するか。planner 推奨: **本 plan
     slug で統一** (細分化は wall name register 拡張時に検討)。auditor 判定対象。

4. **`IsBCRandomCodebookMarkov` predicate redesign のリリース判断** (user 確認):
   - 本 plan は Phase 2.3.3 で `bc_random_codebook_markov_of_ensemble` の body を sorry 化する
     だけで、下流 predicate `IsBCRandomCodebookMarkov` の operational gap (= `errBound` が `_c`
     の error と link されない vacuous shape) は **scope 外** として `broadcast-channel-moonshot-plan`
     配下別 plan に escalate。escalate 先 plan の起草は本 plan 完了後の別 session。
     user の合意確認のため明示。

5. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。MAC / BC の analytical closure (joint typicality
   AEP / Bonferroni / random codebook averaging) は **未着手のまま**で本 plan は close する。
   `mac-moonshot-plan.md` / `broadcast-channel-moonshot-plan.md` の Phase pass-through 状態は
   変えない。

6. **caller drift 規模予測** (Phase 2.x で実測):
   想定 caller drift 規模: 5-10 declaration が transitive sorry 化、Phase 2.x で散文化対応に
   20-40 行追記。**1 session で完走可能 (中央予測)**、L-MIG-4 発動なし。主な caller:
   - 同 family 内 wrapper (Phase 2.1 / 2.2 で sorry 化済)
   - `mac_capacity_region_outer_bound_corner_limit` / `bc_capacity_region_outer_bound_corner_limit`
     (suspect なしの `linarith` wrapper)
   - log-rate form (`mac_capacity_region_outer_bound_log_rate` / `bc_capacity_region_outer_bound_log_rate`、
     suspect なしの specialization)

7. **MAC↔BC 内部 cross-import の future-proof** (informational):
   `BroadcastChannelSuperposition` → `MACL1Discharge`、`BroadcastChannelSuperpositionBody` →
   `MACBodyDischarge` は本 sweep で sorry 化を MAC 側 → BC 側の順に行ったため transitive sorry
   が綺麗に整理されるが、将来 MAC L1 / Body discharge を proof done に持っていく際に BC 側で
   transitive `sorry` warning が消える。banner 更新時に明示推奨。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner (本 session、docs-only) が
   `Common2026/Shannon/{MultipleAccessChannel, BroadcastChannel, MACFanoConverseBody,
   BroadcastChannelExistenceBridgeBody, MACBodyDischarge, MACCornerPoint,
   BroadcastChannelSuperposition, BroadcastChannelSuperpositionBody, MACL1Discharge,
   MACPerEventAEPDecay}.lean` 10 file の legacy tag 49 件 (suspect 28 + 散文 🟢ʰ 21) を
   verbatim 読込で per-declaration 分類。
   - **Plan 分割判断**: MAC ↔ BC の内部 cross-import (BC superposition → MAC L1 / BC
     superposition body → MAC body discharge) が判明し、1 plan 統合 sweep に確定。
     `mac-sorry-migration-plan.md` / `bc-sorry-migration-plan.md` の 2 plan 分割案は不採用
     (順序依存管理コスト + transitive sorry 化を別 plan で吸収する非効率を回避)。
   - **既存 sorry 計数**: word-boundary `rg -nw 'sorry'` で 2 hit、全て docstring 内文字列
     (`MACPerEventAEPDecay.lean:44` `## Known Mathlib gap` section header + `:56` `sorry-free.`
     prose)、実 sorry 0 件。Pilot Pattern D 適用済。
   - **tier 5 defect 3 件 (planner 段階で inline 発見)**:
     - `bc_common_rate_bound` (`BroadcastChannel.lean:443`) — 仮説型 ≡ 結論型 + name laundering
       `_lbh` suffix の二重 defect。著者が ⚠️ HONESTY ALERT で明記済 (line 431)
     - `bc_private_rate_bound` (`BroadcastChannel.lean:475`) — 同上 (line 466 HONESTY ALERT)
     - `bc_random_codebook_markov_of_ensemble` (`BroadcastChannelExistenceBridgeBody.lean:314`) —
       下流 predicate `IsBCRandomCodebookMarkov` の operational gap が原因の predicate-degenerate
       defect。著者が ⚠️ Honest-rebrand caveat (line 297) で明記済
     CLAUDE.md「検証の誠実性」inline detection rule に従い在庫表で明示、Phase 2.3 で
     `@residual(defect:circular|degenerate)` 付き sorry 化として handling。
   - **cross-family dependency**: MAC↔BC 内部 2 件 (`BroadcastChannelSuperposition` →
     `MACL1Discharge`、`BroadcastChannelSuperpositionBody` → `MACBodyDischarge`)。本 plan
     内で順序付け sweep (MAC 先行 → BC 後追い) で吸収可能、削除提案禁止。MAC/BC → Relay の
     docstring prose 言及 3 件 (`RelayCutset.lean:34/212/213/222`、`RelayInnerBound.lean:37/57/147/306/328/413`)
     は **実コード上の symbol 引用なし、import なし** のため cross-family entanglement カウント
     外 (Round 1 WynerZiv の RelayCFBinningBody re-namespacing 利用とは性質が異なる)。
   - **HONESTY ALERT 検出 3 件**: 全て tier 5 defect 対象内 (Phase 2.3)、本 plan scope 外として
     別 plan 化する性質ではない。runbook Pattern H 適用で「scope 外として別 plan 化」する
     性質ではなく、`mac-bc-sorry-migration-plan` で sorry-based migration するのが正しい流儀。
   - **wall name register 拡張**: 不要 (`joint-typicality-multi` を既登録名で活用、新規追加なし)。
     本 plan は `plan:` slug で揃え、shared sorry 補題化は採用しない (Round 1 踏襲)。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
