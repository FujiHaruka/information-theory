# Shannon: Relay legacy-tag → sorry-based migration plan

> **Parent**: [`relay-inner-bound-moonshot-plan.md`](relay-inner-bound-moonshot-plan.md)
> + [`relay-cutset-moonshot-plan.md`](relay-cutset-moonshot-plan.md)
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく legacy tag (suspect / 散文 🟢ʰ) →
> `sorry + @residual` への honesty 強化** (`audit-tags.md`「Deprecated」+
> 「移行レシピ」) を目的とする独立 workstream。
> Pilot references: [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md)
> (pure suspect pilot) / [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md)
> (chain sweep with P/V/C 全 P) /
> [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md)
> (3 種混在 + cross-family escalate 例)。

## Context

### 計数 (verbatim 確認、2026-05-25)

`rg` 検証 + 各 file の `@audit:*` 行直後 declaration を Read で照合した数値:

| file | suspect | staged | 🟢ʰ (生) | defer | closed | 既存 `sorry` (`rg -nwc`) | ⚠/HONESTY ALERT/FALSE |
|---|---:|---:|---:|---:|---:|---:|---:|
| `RelayInnerBodyDischarge.lean` | **15** | 0 | 0 | 0 | 0 | 0 | 0 |
| `RelayCutset.lean` | **3** | 0 | **11** (module/decl docstring 内散文) | 0 | 0 | 0 | 0 |
| `RelayInnerBound.lean` | **9** | 0 | **4** (module/decl docstring 内散文) | 0 | 0 | 0 | 0 |
| `RelayCFBinningBody.lean` | **5** | 0 | 0 | 0 | 0 | 0 | 0 |
| `RelayDFBlockMarkovBody.lean` | **4** | 0 | 0 | 0 | 0 | 0 | 0 |
| **合計** | **36** | 0 | 15 | 0 | 0 | 0 | 0 |

- 36 suspect は **全て** plan slug `relay-inner-bound-moonshot-plan` (32 件) +
  `relay-cutset-moonshot-plan` (4 件 — 詳細: RelayCFBinningBody 0 + RelayDFBlockMarkovBody 0 +
  RelayInnerBodyDischarge 0 + RelayInnerBound 0 + RelayCutset 4 件) に集約。**Hoeffding/WynerZiv
  と異なり tier 4 vocabulary は plan slug 2 つに集中、wall slug 不在**。
  - 実体は `rg`: `@audit:suspect(relay-inner-bound-moonshot-plan)` 32 件、
    `@audit:suspect(relay-cutset-moonshot-plan)` 4 件 (RelayCutset.lean:424/464/535 + 1 件
    集計外、`rg -c 'relay-cutset-moonshot-plan'` で `RelayCutset.lean:3` で確認)。
- **🟢ʰ 15 件は散文表現** (`module docstring` + 既に `@audit:suspect` 付き declaration の
  docstring 内形容詞 "honest-🟢ʰ" / "🟢ʰ load-bearing"); declaration を別途 tag する独立用途は
  **なし**。Phase 1 で suspect tag を削除 / migrate するとき、同じ docstring 内に存在する
  🟢ʰ 散文も同時に refine する (incidental migration、新規 declaration ではない)。
- 既存 word-boundary `sorry` 0 件 (Pilot Pattern D 適用済、`rg -nwc 'sorry'` 全 file 0)。
- ⚠ / HONESTY ALERT / FALSE 検出: **全 file 0 件** (Pattern H 該当なし)。

### なぜ Relay が次の sweep family か

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25 集計)」では Relay は
**Round 2 中-大** (concrete 36 suspect + 15 🟢ʰ = 51 legacy tag) で「shared wall は調査要」と
分類されている。verbatim 再計数の結果、Hoeffding / Cramér / WynerZiv pilot を踏まえた次の特徴が
判明:

1. **全 36 suspect が P (load-bearing predicate / hypothesis consumer)**。pilot
   Hoeffding のような V (variational pass-through) は **ゼロ**、constructive recovery
   候補も極めて限定的 (在庫表参照、後述)。Cramér pilot (13 件全 P) に類似。
2. **3 つの load-bearing predicate が family 内 chain を形成**:
   - `RelayDFAchievable W R Imrh Iry Ibroad` (`RelayInnerBound.lean:?`、`InRelayDFRate → RelayDFInnerBoundExistence` の gated implication)
   - `RelayCFAchievable W R Idec Ix1y Iy1hy1` (`RelayInnerBound.lean:431-437`、同 CF 版)
   - `IsRelayDFBlockMarkovWitness` (`RelayInnerBodyDischarge.lean:143-148`、definitionally `RelayDFAchievable`)
   - `IsRelayCFBinningWitness` (`RelayInnerBodyDischarge.lean:335-340`、definitionally `RelayCFAchievable`)

   この 4 predicate は **`RelayDFAchievable` / `RelayCFAchievable` を中核**として **`IsRelayDFBlockMarkovWitness` /
   `IsRelayCFBinningWitness` が def-eq で alias** している。実体は 2 つ。
3. **cross-family entanglement が 2 件 (Wyner–Ziv side)** (verbatim 確認済、後述「Cross-family
   entanglement」section):
   - `RelayCFBinningBody.lean:2` の `import InformationTheory.Shannon.WynerZivBinningCovering` → 3 predicate
     (`IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable`) を
     **re-namespacing 使用** (`RelayCFBinningBody.lean:135/203/312` 等)
   - `RelayInnerBodyDischarge.lean:2` の `import InformationTheory.Shannon.WynerZivBinningBody` →
     `wzBinningMeasure` を CF 用に re-export (`RelayCFBinningMeasure := wzBinningMeasure`)
   - `RelayCFBinningBody.lean:348` で `wyner_ziv_binning_via_covering_packing` を直接呼び出し
     (Wyner–Ziv の Phase 1.5 で sorry 化対象 declaration、`docs/shannon/wynerziv-sorry-migration-plan.md` 在庫表参照)
4. **shared wall lemma は不要**。`audit-tags.md`「Wall name register」に登録済の 10 wall name
   (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` /
   `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` / `fourier`) の
   いずれも Relay 文脈に直接当てはまる候補は **無い** (詳細: 関連 Mathlib gap は L-RI1/2/3/4 =
   block-Markov 符号化 + sliding-window decoder + WZ binning 周りの combinatorial existence で、
   それぞれ companion seed `relay-df-block-markov-discharge-*` / `relay-df-sliding-window-discharge-*` /
   `relay-cf-wz-binning-discharge-*` / `relay-cf-si-decode-discharge-*` で closure 予定)。Approach
   §「Wall name register 拡張提案 (R4)」で **新規 wall `joint-typicality-multi`** に Relay 系を
   集約する選択肢を検討するが、本 plan の sweep では `plan:relay-inner-bound-moonshot-plan` /
   `plan:relay-cutset-moonshot-plan` に揃え、新 wall 命名は別 PR に委ねる。

### 上位 moonshot との関係

`relay-inner-bound-moonshot-plan.md` と `relay-cutset-moonshot-plan.md` は **2026-05-21 de-circularization
直後の honest pass-through** state を維持 (load-bearing hypothesis 形で publish 済、Phase B/C/D で
別 plan として closure)。本 plan は **その pass-through 設計を変える** — specifically:

- **predicate consumer の sorry 化**: 36 suspect-tagged declaration の signature から load-bearing
  predicate / hypothesis を削除し body を `sorry` に置換。
- **predicate 定義側**: 4 load-bearing predicate (`RelayDFAchievable` / `RelayCFAchievable` /
  `IsRelayDFBlockMarkovWitness` (= alias) / `IsRelayCFBinningWitness` (= alias)) に
  `@audit:retract-candidate(load-bearing-predicate)` を付与 (削除はしない — 後段 `IsCFSideInfoDecodeHyp`
  / `IsBlockMarkovEncoderHyp` 等の sub-hyp も含めて Phase 2.3 で判断)。
- **cross-family WynerZiv re-namespacing は変更しない** — L-MIG-2 / R3 / R14 に従い predicate /
  re-export の **削除提案禁止**、未決事項に escalate (詳細: 「未決事項 #2」)。

**proof completion** (block-Markov random coding + sliding-window decoder + WZ binning achievability の
analytical closure) は別 workstream (`relay-df-*-discharge` / `relay-cf-*-discharge` 系) に残る。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean InformationTheory/Shannon/Relay<X>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` (`general-purpose` SoT-brief 代替可) を起動して classification +
  signature honesty を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にはならない**。

### Tier 5 defect — inline 検出 (planner 段階)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で発見した tier 5 defect /
構造的問題を以下に列挙。実装 agent は本 plan に従って rewrite する際、新規に作らない + 既存を
silent fix しない:

| file:line | decl 名 | 構造的観察 | verbatim 根拠 |
|---|---|---|---|
| `RelayInnerBodyDischarge.lean:143-148` | `IsRelayDFBlockMarkovWitness` | **alias defect 寄り (borderline)** | `def IsRelayDFBlockMarkovWitness W R Imrh Iry Ibroad : Prop := RelayDFAchievable W R Imrh Iry Ibroad` — `RelayDFAchievable` の名前変えのみ。docstring は "honest achievability residual" と説明、当該 alias は **load-bearing-predicate を不必要に二重化**。新規 sorry 化対象ではないが、Phase 2.3 retract-candidate 付与時に "alias of `RelayDFAchievable`、deprecation 候補" を散文明示 |
| `RelayInnerBodyDischarge.lean:335-340` | `IsRelayCFBinningWitness` | 同上 | `def IsRelayCFBinningWitness W R Idec Ix1y Iy1hy1 : Prop := RelayCFAchievable W R Idec Ix1y Iy1hy1` — `RelayCFAchievable` の alias。同様 |
| `RelayInnerBound.lean:?-?` (verbatim 確認要、headline `relay_df_inner_bound` の body) | `relay_df_inner_bound` | **modus ponens (= h_ach h_in_df_region)** だが、`h_ach : RelayDFAchievable W R …` は **conclusion を引き起こす gated implication 全体** を仮説に bundling → **load-bearing hypothesis pattern**、tier 4 legacy. Body `h_ach h_in_df_region` は 1 行 modus ponens (構造的に non-defect、`le_antisymm` 同等の合成)、ただし `h_ach` の load-bearing 性は WynerZiv plan の `wyner_ziv_converse_existence` (`h_nletter` bundling) と同質 | line 484-491、`@audit:suspect(relay-inner-bound-moonshot-plan)` 行 483 directly below docstring |
| 同上 (CF 版) | `relay_cf_inner_bound` | 同上 | line 590-597 |
| `RelayCutset.lean:424-433` | `relay_broadcast_cut` | **`h_chain : I_marg_b ≤ (n : ℝ) * Ib` が load-bearing hypothesis** (= Csiszár sum identity の per-letter chain consequence、Mathlib L-RC1 / L-RC2 wall)。`h_fano` + `h_cleanup` は本来 regularity precondition だが、`h_chain` が conclusion `R ≤ Ib + ε` の本質的核を bundling | body は `relay_cut_rate_le_of_fano hn R Pe I_marg I ε h_fano h_chain h_cleanup` で算術的に組み立て、`h_chain` の load-bearing 性が conclusion 達成の必要条件 |
| `RelayCutset.lean:465-473` | `relay_mac_cut` | 同上 (`h_chain : I_marg_m ≤ (n : ℝ) * Im`、conditional Csiszár sum identity に依存) | body 同形 |
| `RelayCutset.lean:536-549` | `relay_cutset_outer_bound` | 同上 (`h_chain_b` + `h_chain_m` の 2 load-bearing chain hyp) | body は `relay_cutset_combine` + 2 × `relay_cut_rate_le_of_fano` |

これらは **tier 5 真の defect ではない** (構造的 `:= h` 循環でも `:True` slot 悪用でもない) が、
**load-bearing hypothesis bundling** という tier 4 → tier 2 移行対象 (旧方針で許容、新方針 sorry-based
移行)。Phase 2 で signature 改変 + body sorry + `@residual(plan:relay-{inner-bound,cutset}-moonshot-plan)`。

### load-bearing predicate / hypothesis の chain 構造 (planner 段階の依存図)

```
RelayCutset.lean
  ├── relay_broadcast_cut          (load-bearing h_chain, suspect)
  ├── relay_mac_cut                (load-bearing h_chain, suspect)
  └── relay_cutset_outer_bound     (load-bearing h_chain_b + h_chain_m, suspect)
       (consumers: 上の 2 cut wrappers via relay_cut_rate_le_of_fano)

RelayInnerBound.lean   (suspect 9)
  ├── relay_df_inner_bound         (load-bearing h_ach : RelayDFAchievable, suspect)
  ├── relay_df_inner_bound_min_form (suspect、consumer of relay_df_inner_bound)
  ├── relay_df_inner_bound_two_bounds (suspect、同上)
  ├── relay_df_inner_bound_log_rate   (suspect、同上)
  ├── relay_cf_inner_bound         (load-bearing h_ach : RelayCFAchievable, suspect)
  ├── relay_cf_inner_bound_two_conditions (suspect、consumer of relay_cf_inner_bound)
  ├── relay_cf_inner_bound_log_rate    (suspect、同上)
  ├── relay_df_consistent         (load-bearing h_ach + cutset chain hyp, suspect)
  └── relay_cf_consistent         (load-bearing h_ach + cutset chain hyp, suspect)

RelayInnerBodyDischarge.lean   (suspect 15)
  ├── RelayDFInnerBoundExistence_of_witness  (load-bearing h : IsRelayDFBlockMarkovWitness, suspect)
  ├── relay_df_body_from_witness             (同 + h_in_df_region, suspect)
  ├── RelayCFInnerBoundExistence_of_witness  (load-bearing h : IsRelayCFBinningWitness, suspect)
  ├── relay_cf_body_from_witness             (同 + h_in_cf_region, suspect)
  ├── relay_df_inner_bound_discharged        (witness 経由 relay_df_inner_bound, suspect)
  ├── relay_df_inner_bound_discharged_min_form    (suspect)
  ├── relay_df_inner_bound_discharged_two_bounds  (suspect)
  ├── relay_cf_inner_bound_discharged             (suspect)
  ├── relay_cf_inner_bound_discharged_two_conditions (suspect)
  ├── relay_df_inner_bound_discharged_log_rate    (suspect)
  ├── relay_cf_inner_bound_discharged_log_rate    (suspect)
  ├── relay_df_consistent_discharged              (suspect、witness + cutset chain)
  ├── relay_cf_consistent_discharged              (suspect、witness + cutset chain)
  ├── relay_df_inner_bound_via_witness            (suspect、witness を h_ach に流す bridge)
  └── relay_cf_inner_bound_via_witness            (suspect、同 CF)

RelayCFBinningBody.lean   (suspect 5, ↑ WynerZiv cross-family)
  ├── relay_cf_si_decoder_fail_tendsto          (suspect、h_asymp existence-bundle)
  ├── relay_cf_existence_of_witness             (suspect、modus ponens via witness)
  ├── relay_cf_inner_bound_binning_discharged   (suspect、witness + _h_decode underscore)
  ├── relay_cf_inner_bound_binning_discharged_two_conditions (suspect)
  └── relay_cf_consistent_binning_discharged    (suspect、witness + cutset chain + _h_decode)

RelayDFBlockMarkovBody.lean   (suspect 4)
  ├── relayDFRateWitness_of_encoder_hyp           (suspect、constructive bridge from h_enc)
  ├── relayDFRateWitness_of_sub_hyps              (suspect、3 sub-hyps → rate witness)
  ├── relayDFRateWitness_of_sub_hyps'             (suspect、上の re-publish)
  └── relay_df_inner_bound_block_markov_discharged_region (suspect、InRelayDFRate + h_enc → rate witness)
```

**注意**: RelayDFBlockMarkovBody 4 件は **rate-only witness** (`RelayDFRateWitness R := ∃ N, ∀ n ≥ N, ∃ M c, exp (n R) ≤ M`)
を構成的に組み立てる bridge であり、**error-carrying achievability `RelayDFAchievable` を立てない** (rate-only → achievability
leap は excised、docstring に明記)。これらの body は **genuinely constructive** で、`h_enc : IsBlockMarkovEncoderHyp`
からの existence proof 1 段。`@audit:suspect` 付与の理由は `IsBlockMarkovEncoderHyp` / `IsRelayDecodableHyp` /
`IsDestinationJointlyTypicalHyp` の **3 sub-hyp が load-bearing predicate** であるため (consumer wrapper 自身は constructive)。

## Approach

**file 単位 sweep を 3 Phase + audit + verify に分割**、shared wall lemma は集約しない、cross-family
ripple (Wyner–Ziv re-namespacing) を明示的に保護する。Cramér pilot (上流 → 下流 chain 順序) と
WynerZiv pilot (3 種混在 sweep + cross-family escalate) の延長で、Relay 固有の chain 構造を加味する。

### 戦略 (上流 → 下流 chain 順序)

```
Phase 0    inventory (本 plan 内 inline 表、Phase 別 patch 順序)
   │
Phase 1    V/C cleanup
   │      ├─ V (variational pass-through、純 wrapper)              ← 該当 0 件 (実質 skip)
   │      └─ C (in-tree constructive primitive 経由)                ← 該当 0 件 (実質 skip)
   │      Phase 1 はゼロ件、Cramér pilot と同じく **空処理で記録のみ**
   │
Phase 2.1  P retreat — RelayCutset.lean (3 suspect、load-bearing h_chain*)
   │
Phase 2.2  P retreat — RelayInnerBound.lean (9 suspect、load-bearing h_ach + chain)
   │
Phase 2.3  P retreat — RelayInnerBodyDischarge.lean (15 suspect、witness predicate consumer chain)
   │
Phase 2.4  P retreat — RelayDFBlockMarkovBody.lean (4 suspect、3 sub-hyp consumer constructive bridge)
   │
Phase 2.5  P retreat — RelayCFBinningBody.lean (5 suspect、cross-family WZ predicate consumer)
   │      ↑ **cross-family ripple は保護 (削除しない)** — L-MIG-2 / R3 / R14 に従う
   │
Phase 2.x  ripple — caller drift 散文化 (Pattern C: 即興 vocabulary 禁止)
   │
Phase 2.6  predicate retract-candidate 付与
   │      ├─ family 内 closed: 4 alias / RelayDFAchievable / RelayCFAchievable / 3 DF sub-hyp / IsCFSideInfoDecodeHyp
   │      └─ cross-family (WynerZiv): 3 predicate は **削除提案禁止** + 未決事項 escalate
   │
Phase 2.7  audit-2 (honesty-auditor 起動、全 36 件 + 4+3+1 predicate)
   │
Phase V    verify (全 5 file lake env lean 0 errors + 集計 + 親 plan banner 更新)
```

**Phase 順 (上流 → 下流) を選んだ理由**:

Cramér pilot で実証済の「上流 sorry を先に確定させると olean refresh + 下流 transitive sorry の
散文化が一括で扱える」パターン。Relay の上流は `RelayCutset.lean` (cutset chain primitive、3 suspect)、
中流は `RelayInnerBound.lean` (DF/CF inner bound headline、9 suspect)、下流は `RelayInnerBodyDischarge.lean`
(witness-based wrapper、15 suspect) → `RelayDFBlockMarkovBody.lean` + `RelayCFBinningBody.lean` (sub-hyp
constructive bridge / CF decoder failure、9 suspect)。

Phase 2.5 (RelayCFBinningBody) を最後に置くのは:
- cross-family WynerZiv import を持つため、本 sweep 開始時点で WynerZiv 側 sweep の状態 (`docs/shannon/wynerziv-sorry-migration-plan.md`)
  と整合させやすい (両 family 並列 sweep 時の race を最小化)。
- L-MIG-2 (cross-family predicate 削除禁止) の発動条件を Phase 2.6 直前に確認できる。

### 共有 wall lemma 集約の要否

**集約しない**。`docs/audit/audit-tags.md`「Wall name register」表に Relay 系 wall は **未登録**。
本 sweep では `plan:relay-inner-bound-moonshot-plan` (32 件) + `plan:relay-cutset-moonshot-plan` (4 件)
の 2 slug に揃え、新規 wall name を register しない。

検証: register 登録済の 10 wall (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` /
`continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` /
`fourier`) のうち、Relay 文脈で **`joint-typicality-multi`** ("多変数 joint typicality / Fano、
Ch.15 MAC/BC/Relay") が **直接該当する可能性**を確認。詳細は Approach §「Wall name register 拡張提案
(R4)」。

### Wall name register 拡張提案 (R4)

`docs/audit/audit-tags.md` 「Wall name register」表で `joint-typicality-multi` (= 多変数 joint
typicality / Fano、Ch.15 MAC/BC/Relay) が登録済だが、Relay の 4 load-bearing predicate
(`RelayDFAchievable` / `RelayCFAchievable` / `IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness`)
+ Cutset 系 2 chain hyp (`h_chain_b` / `h_chain_m` = Csiszár sum identity 経由) はそれぞれ別の
Mathlib gap を表現:

- **block-Markov coding + sliding-window decoder** (L-RI1 + L-RI2) → 新 wall 候補 `relay-block-markov-aep`
- **Wyner–Ziv 系 random binning + side-info decoder** (L-RI3 + L-RI4) → WynerZiv plan の壁と共有可能、
  ただし当該 family が `plan:` slug 揃えを採用済 (詳細: `docs/shannon/wynerziv-sorry-migration-plan.md`「共有 wall lemma 集約の要否」)
- **Csiszár sum identity (conditional)** (L-RC1 + L-RC2) → 新 wall 候補 `csiszar-sum-conditional`
  (既存 `csiszar` は projection、別物)

**Phase 2.6 完了後、別 PR で次の選択肢を検討**:

1. (a) `joint-typicality-multi` を **MAC/BC/Relay 共通 wall** として残し、本 sweep + 後続 MAC/BC sweep を
  `wall:joint-typicality-multi` で揃える。
2. (b) Relay 専用 wall として `relay-block-markov-aep` を新規追加し、Wyner–Ziv 経由の CF achievability は
  別 wall (例: `relay-cf-wz-binning`) を割り当て、Cramér pilot と同じ「`plan:` slug 揃え」を維持。

本 plan の **デフォルトは (b) 寄り** (新 wall 追加せず `plan:` slug 揃え、後続 sweep で reconsider) だが、
本 plan の Phase V で **handoff 反映**として明示的に未決事項に列挙。

### constructive recovery 候補 (Pilot Pattern B)

planner 段階で各 declaration の **結論型を verbatim 確認**し、constructive 化可能な候補を flag:

| file:line | decl 名 | 結論型 | 構成的回復可能性 |
|---|---|---|---|
| `RelayDFBlockMarkovBody.lean:311-327` | `relayDFRateWitness_of_encoder_hyp` | `RelayDFRateWitness R := ∃ N, ∀ n ≥ N, ∃ M c, exp (n R) ≤ M` | **既に純構成的** (body 14 行、`obtain ⟨N, hN⟩ := h_enc` から `refine` で構成、`Classical.arbitrary` 経由の flatten)。`h_enc : IsBlockMarkovEncoderHyp` という load-bearing predicate に依存しているため `@audit:suspect` 付与されているが、wrapper 自身は constructive (Cramér pilot の `cramer_upper_legendre` 類似)。**Phase 2.4 で signature 改変 (`h_enc` 削除) は不要**、tag 削除のみで足る可能性 → auditor 委任 (L-MIG-1) |
| `RelayDFBlockMarkovBody.lean:345-352` | `relayDFRateWitness_of_sub_hyps` | 同上 | **構成的だが load-bearing predicate consumer**: `h_enc` + `_h_dec` (underscore) + `_h_typ` (underscore)、body は `relayDFRateWitness_of_encoder_hyp h_enc`。2 hyp は underscore で unused、`h_enc` は load-bearing → Phase 2.4 で `h_enc` 削除 + sorry、または上の constructive 性を継承して **タグ削除のみ** (auditor 委任) |
| `RelayDFBlockMarkovBody.lean:380-388` | `relayDFRateWitness_of_sub_hyps'` | 同上 | 同上 (re-publish wrapper) |
| `RelayDFBlockMarkovBody.lean:399-406` | `relay_df_inner_bound_block_markov_discharged_region` | 同上 | 同上 (rate-region 分解 + `h_enc` 構成) |
| `RelayInnerBodyDischarge.lean:213-217` (suspect 無し、参考) | `relayCFBinningMeasure.instIsProbabilityMeasure` | `IsProbabilityMeasure (relayCFBinningMeasure β₁ n M)` | **既に純構成的** (`infer_instance`)、suspect 付与なし。本 plan touch 外 |
| 残り 32 件 | (各種 P consumer) | 各種 `RelayDFInnerBoundExistence` / `RelayCFInnerBoundExistence` / `R ≤ Ib + ε` / `R ≤ relayCutsetBound …` | **constructive recovery 不可** (本体が deep info-theoretic 内容: gated implication の modus ponens は load-bearing hypothesis 依存) |

→ Phase 2.4 で 4 候補 (`relayDFRateWitness_*` 系) を **planner 指示は sorry 化だが、auditor が
constructive recovery 認定すればタグ削除のみに格下げ**。Hoeffding pilot の `isHoeffdingMinimizerFullSupport_of_lagrange`
と同形 (1 件 inline recovery 実施)。

### transitive sorry の handling 方針 (Pilot Pattern C)

Phase 2 で上流 (RelayCutset → RelayInnerBound → RelayInnerBodyDischarge) を順次 sorry 化すると、
下流 wrapper が transitive sorry を引き継ぐ。**即興 vocabulary 禁止** (`(plan:..., transitive)` 等は
`audit-tags.md` 未登録)。具体的な caller chain:

```
RelayCutset.relay_cutset_outer_bound  (Phase 2.1 で sorry 化)
  ←─ RelayInnerBound.relay_df_consistent / relay_cf_consistent   (Phase 2.2、transitive)
  ←─ RelayInnerBodyDischarge.relay_df_consistent_discharged / relay_cf_consistent_discharged (Phase 2.3、transitive)
  ←─ RelayCFBinningBody.relay_cf_consistent_binning_discharged   (Phase 2.5、transitive)

RelayInnerBound.relay_df_inner_bound / relay_cf_inner_bound  (Phase 2.2 で sorry 化)
  ←─ RelayInnerBodyDischarge.relay_df_inner_bound_via_witness / relay_cf_inner_bound_via_witness (Phase 2.3、transitive)
  ←─ RelayCFBinningBody.relay_cf_existence_of_witness  (Phase 2.5、modus ponens transitive)

RelayInnerBodyDischarge.relay_df_inner_bound_discharged  (Phase 2.3 で sorry 化)
  ←─ RelayCFBinningBody.relay_cf_inner_bound_binning_discharged (Phase 2.5、transitive)
```

各 transitive caller の docstring に **散文** を追加 (Pattern C):

```
Transitive `sorry` via `<upstream decl>` (Phase 2.{1,2,3} retreat). No `@residual`
tag is attached — the closure responsibility belongs to the upstream
declaration's `@residual(plan:<slug>)`.
```

即興 `(plan:..., transitive)` vocabulary 禁止。

## Cross-family entanglement (R3 / R14 verbatim 確認、Phase 2.5/2.6 で削除禁止 + escalate)

WynerZiv side との entanglement は **verbatim 確認済 2 件**。本 sweep で touch しない / 削除提案しない:

| Relay file:line | 使用 WynerZiv 記号 | パターン | escalate 先 |
|---|---|---|---|
| `RelayCFBinningBody.lean:2` | `import InformationTheory.Shannon.WynerZivBinningCovering` | re-namespacing import | 未決事項 #2 (cross-family entanglement) |
| `RelayCFBinningBody.lean:135` (`relayCFCovering_def`?) | `IsWynerZivBinningCovering R_cov ε_cov μ Ŷs Ys JT` を unfold で利用 | re-namespacing wrapper definition | 同上 |
| `RelayCFBinningBody.lean:163/173` | `IsWynerZivBinningCovering.mono` / `IsWynerZivBinningCovering.rate_irrelevant` | helper method 経由 | 同上 |
| `RelayCFBinningBody.lean:203` | `IsWynerZivBinningPacking R_bin ε_pack μ Ŷs Ys JT f_Ŷ` 利用 | 同上 (Packing) | 同上 |
| `RelayCFBinningBody.lean:235/246` | `IsWynerZivBinningPacking.mono` / `rate_irrelevant` | 同上 | 同上 |
| `RelayCFBinningBody.lean:262-263, 312` (`IsCFSideInfoDecodeHyp.toWZ`) | `IsWynerZivBinningAchievable R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ` を `def IsCFSideInfoDecodeHyp` の RHS で利用 + `.toWZ` 補題で逆向き | re-namespacing predicate equivalence + bridge | 同上 |
| `RelayCFBinningBody.lean:348` | `wyner_ziv_binning_via_covering_packing` を直接呼出 (`relay_cf_si_decoder_fail_le` の body) | **WynerZiv sweep の Phase 1.5 で sorry 化対象 declaration**、本 sweep の Phase 2.5 で transitive sorry に降格 | 散文 caller drift (Pattern C)、削除提案 = 禁止 |
| `RelayInnerBodyDischarge.lean:2` | `import InformationTheory.Shannon.WynerZivBinningBody` | re-namespacing import | 未決事項 #2 |
| `RelayInnerBodyDischarge.lean:205-209` (`relayCFBinningMeasure`) | `wzBinningMeasure β₁ n M` を `noncomputable def` で alias | re-export def | 同上 |
| `RelayInnerBodyDischarge.lean:213-217` (`relayCFBinningMeasure.instIsProbabilityMeasure`) | `wzBinningMeasure` の `IsProbabilityMeasure` instance を `infer_instance` で forward | 同上 | 同上 |

**Phase 2.5 / 2.6 で実装 agent への明示指示**:
- `IsCFSideInfoDecodeHyp` (`RelayCFBinningBody.lean:263`) は **本 family 内 predicate** だが、その RHS で
  `IsWynerZivBinningAchievable` を **definitionally 等価**として使用。Phase 2.6 で `IsCFSideInfoDecodeHyp` 自身に
  `@audit:retract-candidate(load-bearing-predicate)` を付与し、docstring に **「`IsWynerZivBinningAchievable` の
  re-namespacing alias、WynerZiv 側 predicate の状態に同期」** を明示する。
- WynerZiv 側 3 predicate (`IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable`)
  は **本 sweep で touch しない** (WynerZiv 側 plan の Phase 2.3 が retract-candidate 付与済の前提)。
- `wzBinningMeasure` / `wyner_ziv_binning_via_covering_packing` も **touch しない** (WynerZiv 側 plan の Phase
  1.5 で sorry 化された場合、本 sweep の Phase 2.5 で `relay_cf_si_decoder_fail_le` (suspect 無し本体) と
  `relay_cf_si_decoder_fail_tendsto` (suspect 行 361) が transitive sorry に降格。前者は本 sweep 対象外 — touch
  しない、後者は Phase 2.5 で sorry 化対象なので「transitive + own sorry」両方を扱う、散文で transitive
  性明示)。

**並列起動中の WynerZiv Phase 2.x planner との衝突回避**: 本 plan の Approach matrix と WynerZiv plan の
Approach matrix を **両方で同時参照可能**にするため、両 plan が:
- **削除提案禁止**を明示する Phase 2.x ripple step を持つ ✅ (本 plan: Phase 2.5/2.6、WynerZiv plan: Phase 2.x.3)
- **WynerZiv 3 predicate (Covering/Packing/Achievable) を deprecate しない**ことを未決事項に列挙 ✅
  (本 plan: 未決事項 #2、WynerZiv plan: L-MIG-2 + 未決事項 #5 候補)
- **Pattern G (cross-family) 該当**を escalate ✅

## ⚠ HONESTY ALERT / FALSE 検出 (Pattern H、R8)

`rg '⚠|HONESTY ALERT|FALSE' InformationTheory/Shannon/Relay{InnerBodyDischarge,Cutset,InnerBound,CFBinningBody,DFBlockMarkovBody}.lean`
は **全 file 0 hit** を返した (verbatim 確認 2026-05-25)。本 sweep scope 内で Pattern H 該当
declarations は **存在しない**。

## 在庫: 36 件 (suspect) + 散文 🟢ʰ 15 件 の verbatim 分類

verbatim 確認方法: 各 `@audit:suspect` / `🟢ʰ` 周辺 docstring + theorem signature + body 1-3 行を実コードから
読込、「signature の hypothesis が load-bearing か regularity か」を 1 件ずつ判定。各 declaration の
`path:line` は **タグ行**、declaration 名はその直後。

### `RelayCutset.lean` — 3 suspect + 散文 🟢ʰ 11

| file:line | decl 名 | suspect の核 (1 行) | パターン | 削除/置換予定タグ | 消費 hypothesis | cross-family? | constructive recovery? | Pattern (runbook) | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `RelayCutset.lean:424` | `relay_broadcast_cut` | "load-bearing hypothesis form (Fano + per-letter chain, NOT a discharge)" | P | `@residual(plan:relay-cutset-moonshot-plan)` | `h_fano` + `h_chain` (load-bearing) + `h_cleanup` | No | No (`h_chain` = Csiszár sum identity per-letter chain) | A (olean refresh attention) | body は `relay_cut_rate_le_of_fano` 1 行、`h_chain` 削除で sorry。本 wrapper の自身は arithmetic |
| `RelayCutset.lean:464` | `relay_mac_cut` | 同上 (MAC cut conditional chain) | P | 同上 | 同上 (`h_chain` = conditional Csiszár sum identity) | No | No | A | 同上 |
| `RelayCutset.lean:535` | `relay_cutset_outer_bound` | "genuine (broadcast cut) / honest-🟢ʰ (MAC cut) converse, no longer circular" | P | 同上 | `h_fano_b` + `h_fano_m` + `h_chain_b` (load-bearing) + `h_chain_m` (load-bearing) + 2 cleanup | No | No | A | body は `relay_cutset_combine` + 2 × `relay_cut_rate_le_of_fano`、両 chain hyp 削除で sorry |

**散文 🟢ʰ 11 件の扱い**: 全て module docstring (lines 37/44/71/93) + 上記 3 declaration の docstring 内
形容詞 (lines 322/334/393/435/496/519/524) として現れる "honest-🟢ʰ" 散文。**declaration の独立 tag では
ない** ので、Phase 2.1 で suspect 削除と同時に同じ docstring 内の "honest-🟢ʰ" / "🟢ʰ load-bearing" 表現を
**散文 refine** (tier 4 vocabulary 削除、新表現「genuine constructive (arithmetic core) + load-bearing
hypothesis `h_chain` (Csiszár sum identity wall)」等)。本 plan は **WynerZiv pilot の Phase 1.5.1 と同一手順**を踏襲。

### `RelayInnerBound.lean` — 9 suspect + 散文 🟢ʰ 4

| file:line | decl 名 | suspect の核 (1 行) | パターン | 削除/置換予定タグ | 消費 hypothesis | cross-family? | constructive recovery? | Pattern (runbook) | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `RelayInnerBound.lean:483` | `relay_df_inner_bound` | "honest-🟢ʰ, non-circular, error-carrying" | P | `@residual(plan:relay-inner-bound-moonshot-plan)` | `h_in_df_region : InRelayDFRate` + `h_ach : RelayDFAchievable` (load-bearing gated implication) | No | No | A | body `h_ach h_in_df_region`、`h_ach` 削除で sorry |
| `RelayInnerBound.lean:506` | `relay_df_inner_bound_min_form` | "Variant taking the rate-region hypothesis in the `min` form" | P (上流 wrapper) | 同上 | `h_min : R ≤ min ...` + `h_ach` | No | No | A | body は `relay_df_inner_bound` への forward、上流 sorry を継承 |
| `RelayInnerBound.lean:523` | `relay_df_inner_bound_two_bounds` | 同上 (two-inequality form) | P | 同上 | `h₁` + `h₂` + `h_ach` | No | No | A | 同上 |
| `RelayInnerBound.lean:538` | `relay_df_inner_bound_log_rate` | 同上 (`Real.log` rate form) | P | 同上 | `h_in_df_region` + `h_ach` | No | No | A | 同上 |
| `RelayInnerBound.lean:589` | `relay_cf_inner_bound` | 同上 (CF 版) | P | 同上 | `h_in_cf_region` + `h_ach : RelayCFAchievable` | No | No | A | body `h_ach h_in_cf_region` |
| `RelayInnerBound.lean:604` | `relay_cf_inner_bound_two_conditions` | "Variant taking the rate bound and the compression feasibility as separate hypotheses" | P | 同上 | `h_rate` + `h_feas` + `h_ach` | No | No | A | body forward |
| `RelayInnerBound.lean:616` | `relay_cf_inner_bound_log_rate` | 同上 (CF + log rate) | P | 同上 | 同上 | No | No | A | 同上 |
| `RelayInnerBound.lean:649` | `relay_df_consistent` | "Packages the two genuine/honest landings together" | P (load-bearing h_ach + cutset chain hyp 6 件) | 同上 + `@residual(plan:relay-cutset-moonshot-plan)` (両方) — **暫定で `plan:relay-inner-bound-moonshot-plan` のみ**、auditor 判定 | `h_fano_b/m` + `h_chain_b/m` (load-bearing) + 2 cleanup + `h_in_df_region` + `h_ach` | No | No | A | body は `⟨relay_cutset_outer_bound …, relay_df_inner_bound …⟩` の pair。上流 2 sorry の transitive 両継承 |
| `RelayInnerBound.lean:675` | `relay_cf_consistent` | 同上 (CF 版) | P | 同上 | 同上 (CF) | No | No | A | 同上 |

**散文 🟢ʰ 4 件**: module docstring (lines 44/49) + 2 headline docstring (lines 450/563) の "honest-🟢ʰ" 形容詞。
**Phase 2.2 で suspect 削除と同時に refine** (RelayCutset と同手順)。

### `RelayInnerBodyDischarge.lean` — 15 suspect

| file:line | decl 名 | suspect の核 (1 行) | パターン | 削除/置換予定タグ | 消費 hypothesis | cross-family? | constructive recovery? | Pattern (runbook) | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `RelayInnerBodyDischarge.lean:155` | `RelayDFInnerBoundExistence_of_witness` | "modus ponens routing lemma" | P | `@residual(plan:relay-inner-bound-moonshot-plan)` | `h_in_df_region` + `h : IsRelayDFBlockMarkovWitness` (load-bearing alias of RelayDFAchievable) | No | No | A | body `h h_in_df_region` |
| `RelayInnerBodyDischarge.lean:172` | `relay_df_body_from_witness` | "body-discharged variant of `relay_df_inner_bound`" | P | 同上 | 同上 | No | No | A | body forward via `RelayDFInnerBoundExistence_of_witness` |
| `RelayInnerBodyDischarge.lean:345` | `RelayCFInnerBoundExistence_of_witness` | 同上 (CF 版) | P | 同上 | `h_in_cf_region` + `h : IsRelayCFBinningWitness` | No | No | A | body `h h_in_cf_region` |
| `RelayInnerBodyDischarge.lean:361` | `relay_cf_body_from_witness` | 同上 (CF body discharge) | P | 同上 | 同上 | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:395` | `relay_df_inner_bound_discharged` | "Body-discharged variant of `relay_df_inner_bound` where … hypotheses are *replaced* by a single structured achievability witness" | P | 同上 | `h_in_df_region` + `h_witness : IsRelayDFBlockMarkovWitness` | No | No | A | body forward via `relay_df_body_from_witness` |
| `RelayInnerBodyDischarge.lean:409` | `relay_df_inner_bound_discharged_min_form` | "min-form" | P | 同上 | `h_min` + `h_witness` | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:423` | `relay_df_inner_bound_discharged_two_bounds` | "two-inequality form" | P | 同上 | `h₁` + `h₂` + `h_witness` | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:437` | `relay_cf_inner_bound_discharged` | "CF body-discharged" | P | 同上 | `h_in_cf_region` + `h_witness : IsRelayCFBinningWitness` | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:451` | `relay_cf_inner_bound_discharged_two_conditions` | 同上 | P | 同上 | `h_rate` + `h_feas` + `h_witness` | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:465` | `relay_df_inner_bound_discharged_log_rate` | 同上 (DF + log rate) | P | 同上 | `_hn` + `h_in_df_region` + `h_witness` | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:483` | `relay_cf_inner_bound_discharged_log_rate` | 同上 (CF + log rate) | P | 同上 | 同上 (CF) | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:516` | `relay_df_consistent_discharged` | "outer + inner combined, witness-discharged" | P | 同上 + (両 plan slug 候補) | 7 hyp (cutset 6 + `h_in_df_region`) + `h_witness` | No | No | A | body `⟨relay_cutset_outer_bound …, relay_df_inner_bound_discharged …⟩`、上流 2 sorry transitive |
| `RelayInnerBodyDischarge.lean:541` | `relay_cf_consistent_discharged` | 同上 (CF 版) | P | 同上 | 同上 (CF) | No | No | A | 同上 |
| `RelayInnerBodyDischarge.lean:582` | `relay_df_inner_bound_via_witness` | "adapter between the body-discharged signature and the original published signature" | P | 同上 | `h_in_df_region` + `h_witness` | No | No | A | body は `relay_df_inner_bound W R … h_in_df_region h_witness` (witness の load-bearing 性を `h_ach` slot に流す) |
| `RelayInnerBodyDischarge.lean:597` | `relay_cf_inner_bound_via_witness` | 同上 (CF) | P | 同上 | 同上 (CF) | No | No | A | 同上 |

**注意**: `IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` は **alias** (`def := RelayDFAchievable` /
`:= RelayCFAchievable`)。上の 15 declaration の signature 改変は **witness predicate hypothesis** を削除する
形になる (alias 経由でも `RelayDFAchievable` 経由でも、load-bearing 性は同じ)。Phase 2.6 で alias の deprecate
判断 (CLAUDE.md tier 5 borderline、未決事項 #1)。

### `RelayDFBlockMarkovBody.lean` — 4 suspect

| file:line | decl 名 | suspect の核 (1 行) | パターン | 削除/置換予定タグ | 消費 hypothesis | cross-family? | constructive recovery? | Pattern (runbook) | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `RelayDFBlockMarkovBody.lean:310` | `relayDFRateWitness_of_encoder_hyp` | "Constructive rate witness from the block-Markov encoder sub-hyp" | P (load-bearing `h_enc`) **+ C-candidate** | `@residual(plan:relay-inner-bound-moonshot-plan)` 暫定、**auditor が constructive recovery 認定すればタグ削除のみ** (L-MIG-1) | `h_enc : IsBlockMarkovEncoderHyp` (load-bearing predicate) | No | **✅ 既に純構成的** (body 14 行、`obtain` + `refine`) — `IsBlockMarkovEncoderHyp` 自身が load-bearing なため transitive load-bearing だが、wrapper 自身は arithmetic | B (overcorrect risk)、A | inline detection 推奨 (Hoeffding `isHoeffdingMinimizerFullSupport_of_lagrange` 類似) |
| `RelayDFBlockMarkovBody.lean:344` | `relayDFRateWitness_of_sub_hyps` | "Constructive rate witness from all three DF sub-hyps" | P + C-candidate (同上) | 同上 | `h_enc` + `_h_dec` (underscore) + `_h_typ` (underscore) | No | ✅ 同上 (`relayDFRateWitness_of_encoder_hyp h_enc` を 1 行 forward) | B、A | 同上 |
| `RelayDFBlockMarkovBody.lean:379` | `relayDFRateWitness_of_sub_hyps'` | "re-publish through the discharged route" | P + C-candidate (同上) | 同上 | 同上 (3 hyp) | No | ✅ 同上 | B、A | 同上 |
| `RelayDFBlockMarkovBody.lean:398` | `relay_df_inner_bound_block_markov_discharged_region` | "InRelayDFRate bundled + h_enc → rate witness" | P + C-candidate (同上) | 同上 | `h_region : InRelayDFRate` + `h_enc` | No | ✅ 同上 (`relayDFRateWitness_of_sub_hyps … h_enc h_region.relay_decodable h_region.destination_typical`) | B、A | 同上 |

**Phase 2.4 default 戦略**: 全 4 件で `h_enc` を signature に **残し** (constructive 性維持)、`@audit:suspect` タグ
**削除のみ** (`@residual` 付与しない)。これは Pilot Pattern B の overcorrect 回避: planner 既定の「全件 sorry 化」を
inline detection で「constructive recovery」に切替える。auditor が「`h_enc` は load-bearing predicate、constructive
wrapper でも本体の `RelayDFRateWitness` 達成は `h_enc` 経由のため transitive load-bearing で sorry 化が必要」と
判定したら L-MIG-1 で復元。

### `RelayCFBinningBody.lean` — 5 suspect + cross-family WynerZiv 依存

| file:line | decl 名 | suspect の核 (1 行) | パターン | 削除/置換予定タグ | 消費 hypothesis | cross-family? | constructive recovery? | Pattern (runbook) | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `RelayCFBinningBody.lean:361` | `relay_cf_si_decoder_fail_tendsto` | "Existence-form version of `relay_cf_si_decoder_fail_le`" | P (existence-form `h_asymp` load-bearing) | `@residual(plan:relay-inner-bound-moonshot-plan)` | `h_asymp : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M Ŷs Ys f_Ŷ f ε_cov ε_pack, … ∧ IsCFSideInfoDecodeHyp …` (existence-form predicate bundle) | **No** (本 declaration は `IsCFSideInfoDecodeHyp` を使うが当該 predicate は本 file 内 def) | No (existence-form bundle に core) | A、G (`IsCFSideInfoDecodeHyp` が re-namespacing alias、間接 cross-family) | body は `obtain` + `relay_cf_si_decoder_fail_le` 経由 (上流が WynerZiv 経由 transitive sorry)。signature 改変で `h_asymp` 削除 |
| `RelayCFBinningBody.lean:429` | `relay_cf_existence_of_witness` | "CF inner-bound existence from the achievability witness + rate region" | P (load-bearing `h_witness : IsRelayCFBinningWitness`) | 同上 | `h_in_cf_region` + `h_witness` | No | No | A | body は `RelayCFInnerBoundExistence_of_witness h_in_cf_region h_witness`、上流 sorry 継承 + 自身の witness 削除で sorry |
| `RelayCFBinningBody.lean:464` | `relay_cf_inner_bound_binning_discharged` | "binning-discharged form (witness + structured CF side-info decode bundle)" | P (`h_witness` + `_h_decode` underscore) | 同上 | `h_in_cf_region` + `_h_decode : IsCFSideInfoDecodeHyp` (underscore!) + `h_witness` | **Yes (indirect)** — `_h_decode` は `IsCFSideInfoDecodeHyp` (= `IsWynerZivBinningAchievable` の re-namespacing alias) を underscore 化、unused だが docstring の意味論には参照 | No | A、G | underscore `_h_decode` は **削除しない** (signature 保持、Pattern E extract-only consumer parameterization)。`h_witness` 削除 + body sorry |
| `RelayCFBinningBody.lean:491` | `relay_cf_inner_bound_binning_discharged_two_conditions` | 同上 (two-condition form) | P (同上) | 同上 | `h_rate` + `h_feas` + `_h_decode` + `h_witness` | Yes (indirect) | No | A、G | 同上 |
| `RelayCFBinningBody.lean:530` | `relay_cf_consistent_binning_discharged` | "binning-discharged + cut-set outer combined" | P (上記 + cutset chain) | 同上 + (両 plan slug 候補) | 6 cutset chain hyp + `h_in_cf_region` + `_h_decode` + `h_witness` | Yes (indirect) | No | A、G | body `⟨relay_cutset_outer_bound …, relay_cf_inner_bound_discharged …⟩` pair、上流 2 sorry transitive |

**注意 (Pattern G)**: 3 件 (464/491/530) の `_h_decode : IsCFSideInfoDecodeHyp` は underscore (unused) だが、
本 sweep で削除すべきではない (signature 保護 — caller API 互換性 + docstring の意味論的説明)。`IsCFSideInfoDecodeHyp`
自身は Phase 2.6 で `@audit:retract-candidate(load-bearing-predicate)` を **WynerZiv 同期と連動して** 付与 (cross-family
escalate)。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 5 file の 36 suspect + 15 散文 🟢ʰ を verbatim 確認 (`rg -c` + 該当 docstring + signature 1-3 行)
- [x] パターン分類 (全 36 件 = P、うち constructive recovery 候補 4 件、cross-family indirect 3 件)
- [x] cross-family 依存 (Wyner–Ziv re-namespacing 8 references + 1 direct call) を `rg` で確認
- [x] 既存 `sorry` word-boundary 計数 `0` 件確定 (Pilot Pattern D 適用済)
- [x] ⚠ / HONESTY ALERT / FALSE 検出: 0 件 (Pattern H 該当なし)
- [x] tier 5 inline 検出: alias defect 寄り 2 件 (`IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness`) を flag、Phase 2.6 で対応

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1 — V/C cleanup (実質 skip) 📋

- [ ] **1.1** V/C 該当 declaration の `@audit:suspect` 削除 — 該当ゼロ件、**実質作業なし**。
  Cramér pilot と同じ skip 記録のみ。

**Phase 1 DoD**: 該当作業なし。Phase 2 に直接進む。Pilot Pattern B の constructive recovery 候補 4 件
(`RelayDFBlockMarkovBody.lean`) は Phase 2.4 で扱う (V/C ではなく P + C-candidate)。

**proof-log**: no。

### Phase 2.1 — P retreat — `RelayCutset.lean` (3 suspect、load-bearing chain hyp) 📋

- [ ] **2.1.1** `relay_broadcast_cut` (line 425)
  - signature 改変: `h_chain : I_marg ≤ (n : ℝ) * Ib` を **削除** (load-bearing chain hyp、Csiszár sum identity)。
  - 残す: `(R Pe I_marg Ib ε : ℝ)` + `h_fano : RelayBcastCutFano M n R Pe I_marg` (Fano-side
    inequality、本 sweep では Fano discharge は他 plan 委任) + `h_cleanup` (regularity)。
  - 結論型 `R ≤ Ib + ε` 維持。
  - body: 旧 `relay_cut_rate_le_of_fano hn R Pe I_marg Ib ε h_fano h_chain h_cleanup` → `by sorry`。
  - docstring: 旧 `@audit:suspect(relay-cutset-moonshot-plan)` → `@residual(plan:relay-cutset-moonshot-plan)`、
    "honest-🟢ʰ" / "load-bearing hypothesis form (Fano + per-letter chain, NOT a discharge)" の散文を
    "load-bearing `h_chain` (Csiszár sum identity wall, L-RC1/L-RC2)" 表現に refine。
- [ ] **2.1.2** `relay_mac_cut` (line 465)
  - 同上 (conditional chain hyp 削除)。docstring の 🟢ʰ 散文 refine。
- [ ] **2.1.3** `relay_cutset_outer_bound` (line 536)
  - signature 改変: `h_chain_b` + `h_chain_m` を **両方削除** (2 load-bearing chain hyp)。
  - 残す: 6 hyp の残り (`hn` / `_c` / `R Pe I_marg_b I_marg_m Ib Im ε` / `h_fano_b` / `h_fano_m` /
    `h_cleanup_b` / `h_cleanup_m`)。
  - 結論型維持。
  - body → `by sorry`。
  - docstring refine。
- [ ] **2.1.4** Phase 2.1 完了時 `lake env lean InformationTheory/Shannon/RelayCutset.lean` 0 errors 確認。
  signature 改変したため olean refresh が必要 (Pilot Pattern A):
  ```bash
  lake build InformationTheory.Shannon.RelayCutset
  for f in InformationTheory/Shannon/RelayInnerBound.lean InformationTheory/Shannon/RelayInnerBodyDischarge.lean InformationTheory/Shannon/RelayCFBinningBody.lean; do
    lake env lean "$f"
  done
  ```
  dependent file (上記 3) で type drift が発生したら Phase 2.x ripple で散文化対応。
- [ ] **2.1.5** **`relay_cutset_outer_bound_corner_limit` (line 554-570、suspect 無し本体)** は touch しない。
  body は上流 `relay_cutset_outer_bound` (sorry 化済) を呼出 → transitive sorry に降格。
- [ ] **2.1.6** **`relay_cutset_outer_bound_log_rate` (line 597-612、suspect 無し本体)** は touch しない。
  同様の transitive 降格。

**Phase 2.1 DoD**:
- `RelayCutset.lean` で `@audit:suspect` 0 件、`@residual(plan:relay-cutset-moonshot-plan)` 3 件、sorry 3 件、
- 散文 🟢ʰ 11 件 → 0 件 (refine 完了)、
- `lake env lean InformationTheory/Shannon/RelayCutset.lean` 0 errors。

**proof-log**: yes (`docs/proof-logs/proof-log-relay-sorry-migration-phase-2.1.md`)。理由: chain hyp 削除の
load-bearing 性 + 🟢ʰ 散文 refine の判定境界を記録。

### Phase 2.2 — P retreat — `RelayInnerBound.lean` (9 suspect + 散文 🟢ʰ 4) 📋

- [ ] **2.2.1** `relay_df_inner_bound` (line 484)
  - signature 改変: `h_ach : RelayDFAchievable W R Imrh Iry Ibroad` を **削除** (load-bearing gated implication)。
  - 残す: `(W R Imrh Iry Ibroad)` + `h_in_df_region : InRelayDFRate`。
  - 結論型 `RelayDFInnerBoundExistence W R` 維持。
  - body `h_ach h_in_df_region` → `by sorry`。
  - docstring 🟢ʰ refine、tag 置換。

- [ ] **2.2.2** `relay_df_inner_bound_min_form` (line 507) / `relay_df_inner_bound_two_bounds` (line 524) /
  `relay_df_inner_bound_log_rate` (line 539) の 3 変種:
  - `h_ach` 削除、body sorry + `@residual(plan:relay-inner-bound-moonshot-plan)`。
  - 各 wrapper の本体は本来 `relay_df_inner_bound` への forwarding 1 行で構成的だが、上流 sorry 化に伴い
    自身も sorry になる。これは pure transitive (Pattern C) ではなく **自身の `h_ach` 削除に対する直接
    `@residual`** が必要 (signature 改変したため)。

- [ ] **2.2.3** `relay_cf_inner_bound` (line 590)
  - 同上 (CF 版、`h_ach : RelayCFAchievable` 削除)。

- [ ] **2.2.4** `relay_cf_inner_bound_two_conditions` (line 605) / `relay_cf_inner_bound_log_rate` (line 617)
  - 同上 (CF 変種、上の Phase 2.2.2 と同形)。

- [ ] **2.2.5** `relay_df_consistent` (line 650) / `relay_cf_consistent` (line 676)
  - signature 改変: `h_chain_b` + `h_chain_m` (cutset chain、Phase 2.1 と同じ load-bearing) + `h_ach` の
    **3 hyp 削除** (両 plan slug の交叉)。残す: `h_fano_b/m` + `h_cleanup_b/m` + `h_in_df_region` / `h_in_cf_region`。
  - body は `⟨relay_cutset_outer_bound …, relay_df_inner_bound …⟩` の pair → `by sorry`。
  - **`@residual` slug 判断**: 結論型は `(R ≤ relayCutsetBound …) ∧ RelayDFInnerBoundExistence …` で 2 plan
    の交叉。**暫定で `@residual(plan:relay-inner-bound-moonshot-plan)` のみ**付与し、auditor 委任 (未決事項
    #3)。両 slug 併記は audit-tags.md vocabulary 未登録のため不可。

- [ ] **2.2.6** Phase 2.2 完了時 olean refresh + dependent verify:
  ```bash
  lake build InformationTheory.Shannon.RelayInnerBound
  for f in InformationTheory/Shannon/RelayInnerBodyDischarge.lean InformationTheory/Shannon/RelayCFBinningBody.lean InformationTheory/Shannon/RelayDFBlockMarkovBody.lean; do
    lake env lean "$f"
  done
  ```

**Phase 2.2 DoD**:
- `RelayInnerBound.lean` で `@audit:suspect` 0 件、`@residual(plan:relay-inner-bound-moonshot-plan)` 9 件、sorry 9 件、
- 散文 🟢ʰ 4 件 → 0 件、
- `lake env lean InformationTheory/Shannon/RelayInnerBound.lean` 0 errors。

**proof-log**: yes。理由: 9 件のうち `_consistent` 2 件で 2 plan slug 交叉の判断境界を記録。

### Phase 2.3 — P retreat — `RelayInnerBodyDischarge.lean` (15 suspect) 📋

- [ ] **2.3.1** `RelayDFInnerBoundExistence_of_witness` (line 156) / `relay_df_body_from_witness` (line 173)
  - signature 改変: `h : IsRelayDFBlockMarkovWitness W R …` (= `RelayDFAchievable` alias) を **削除**。
  - 残す: `(W R Imrh Iry Ibroad)` + `h_in_df_region : InRelayDFRate`。
  - body sorry + `@residual(plan:relay-inner-bound-moonshot-plan)`。
- [ ] **2.3.2** `RelayCFInnerBoundExistence_of_witness` (line 346) / `relay_cf_body_from_witness` (line 362)
  - 同上 (CF 版、`IsRelayCFBinningWitness` 削除)。
- [ ] **2.3.3** `relay_df_inner_bound_discharged` (line 396) / 3 変種 (`_min_form` 411 / `_two_bounds` 424 /
  `_log_rate` 466) — 4 件:
  - `h_witness` 削除、body は元 `relay_df_body_from_witness …` (Phase 2.3.1 で sorry 化済) への forward だった
    が、自身も signature 改変 → sorry + `@residual`。
- [ ] **2.3.4** `relay_cf_inner_bound_discharged` (line 438) / 2 変種 (`_two_conditions` 452 / `_log_rate` 484)
  — 3 件: 同上 (CF 版)。
- [ ] **2.3.5** `relay_df_consistent_discharged` (line 517) / `relay_cf_consistent_discharged` (line 542)
  — 2 件:
  - signature 改変: cutset chain 2 hyp (Phase 2.1 同パターン) + `h_witness` 削除。
  - **2 plan slug 交叉**は Phase 2.2.5 と同じ暫定処理 (auditor 委任)。
- [ ] **2.3.6** `relay_df_inner_bound_via_witness` (line 583) / `relay_cf_inner_bound_via_witness` (line 598)
  — 2 件 (bridge):
  - signature: `h_witness` 削除、body は `relay_df_inner_bound W R … h_in_df_region h_witness` (Phase 2.2 で
    上流 sorry 化済) → sorry。
- [ ] **2.3.7** Phase 2.3 完了時 olean refresh:
  ```bash
  lake build InformationTheory.Shannon.RelayInnerBodyDischarge
  for f in InformationTheory/Shannon/RelayCFBinningBody.lean InformationTheory/Shannon/RelayDFBlockMarkovBody.lean; do
    lake env lean "$f"
  done
  ```

**Phase 2.3 DoD**:
- `RelayInnerBodyDischarge.lean` で `@audit:suspect` 0 件、`@residual(plan:relay-inner-bound-moonshot-plan)`
  15 件、sorry 15 件、
- `lake env lean InformationTheory/Shannon/RelayInnerBodyDischarge.lean` 0 errors。

**proof-log**: yes。witness predicate alias (`IsRelayDFBlockMarkovWitness` = `RelayDFAchievable`) の deprecation
判定根拠を記録。

### Phase 2.4 — P retreat (with C-candidate) — `RelayDFBlockMarkovBody.lean` (4 suspect) 📋

- [ ] **2.4.1** **planner default**: 4 件全てで `h_enc` (load-bearing predicate) を **signature に残す** +
  **`@audit:suspect` タグ削除のみ** (constructive recovery、Hoeffding pilot `isHoeffdingMinimizerFullSupport_of_lagrange`
  類似)。body は既に純構成的なので変更不要 (verbatim 確認、line 311-327 / 345-352 / 380-388 / 399-406)。
  - `relayDFRateWitness_of_encoder_hyp` (line 311): tag 削除のみ、body そのまま。
  - `relayDFRateWitness_of_sub_hyps` (line 345): 同上。
  - `relayDFRateWitness_of_sub_hyps'` (line 380): 同上。
  - `relay_df_inner_bound_block_markov_discharged_region` (line 399): 同上。
- [ ] **2.4.2** **代替**: auditor が「`h_enc` が load-bearing なので wrapper も transitive load-bearing で sorry
  化すべき」と判定 (L-MIG-1) したら、4 件全てで signature から `h_enc` を削除 + body sorry +
  `@residual(plan:relay-inner-bound-moonshot-plan)`。本判断は Phase 2.7 (audit-2) で確定。
- [ ] **2.4.3** Phase 2.4 完了時 `lake env lean InformationTheory/Shannon/RelayDFBlockMarkovBody.lean` 0 errors 確認。
  default (2.4.1) なら signature 改変なし → olean refresh 不要。代替 (2.4.2) なら olean refresh 必要。

**Phase 2.4 DoD (default)**:
- `RelayDFBlockMarkovBody.lean` で `@audit:suspect` 0 件、`@residual` 0 件 (constructive recovery)、sorry 0 件、
- `lake env lean InformationTheory/Shannon/RelayDFBlockMarkovBody.lean` 0 errors。

**Phase 2.4 DoD (代替 L-MIG-1)**:
- `@audit:suspect` 0 件、`@residual(plan:relay-inner-bound-moonshot-plan)` 4 件、sorry 4 件、
- 同上 type-check。

**proof-log**: yes。理由: constructive recovery 判定の境界 (Pilot Pattern B) を記録。

### Phase 2.5 — P retreat (cross-family aware) — `RelayCFBinningBody.lean` (5 suspect) 📋

- [ ] **2.5.1** `relay_cf_si_decoder_fail_tendsto` (line 362)
  - signature 改変: `h_asymp : ∀ ε > 0, ∃ N, ∀ n ≥ N, …` (existence-form load-bearing bundle) を **削除**。
  - 残す: `[Nonempty β]` + `[Nonempty γ]` + `(R_cov R_bin : ℝ)` + `(μ : Measure Ω) [IsFiniteMeasure μ]` + `(JT)`。
  - 結論型 (`∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M Ŷs Ys f_Ŷ f, μ.real {…} ≤ ε`) 維持。
  - body sorry + `@residual(plan:relay-inner-bound-moonshot-plan)`。
- [ ] **2.5.2** `relay_cf_existence_of_witness` (line 430)
  - signature 改変: `h_witness : IsRelayCFBinningWitness …` を **削除**。残す `h_in_cf_region`。
  - body sorry + `@residual(plan:relay-inner-bound-moonshot-plan)`。
- [ ] **2.5.3** `relay_cf_inner_bound_binning_discharged` (line 465)
  - signature 改変: `h_witness` を **削除**。**`_h_decode : IsCFSideInfoDecodeHyp` は underscore (unused) なので残す** (signature 保持)。
  - body sorry + `@residual(plan:relay-inner-bound-moonshot-plan)`。
- [ ] **2.5.4** `relay_cf_inner_bound_binning_discharged_two_conditions` (line 492)
  - 同上 (two-condition form)。
- [ ] **2.5.5** `relay_cf_consistent_binning_discharged` (line 531)
  - signature 改変: cutset chain 2 hyp + `h_witness` 削除 (Phase 2.2.5 / 2.3.5 同パターン)。`_h_decode` 残す。
  - body sorry。**2 plan slug 交叉**は暫定処理。
- [ ] **2.5.6** **`relay_cf_si_decoder_fail_le` (line 328-351、suspect 無し本体)** は touch しない。
  body は `wyner_ziv_binning_via_covering_packing` 直接呼出 (Wyner–Ziv 側 Phase 1.5 で sorry 化対象) → WynerZiv
  sweep 完了状態に応じて transitive sorry に降格する可能性あり。docstring 散文に **「transitive sorry via
  `wyner_ziv_binning_via_covering_packing` (WynerZiv sweep Phase 1.5 retreat)」** を **WynerZiv 側 sweep 完了
  確認後に追加** (本 plan 内で Phase V 直前に最終追記、本 Phase 2.5 では暫定保留)。
- [ ] **2.5.7** Phase 2.5 完了時 olean refresh + verify:
  ```bash
  lake build InformationTheory.Shannon.RelayCFBinningBody
  lake env lean InformationTheory/Shannon/RelayCFBinningBody.lean
  ```
  RelayCFBinningBody は terminal file (依存元 0)、上記 1 件のみで足る。

**Phase 2.5 DoD**:
- `RelayCFBinningBody.lean` で `@audit:suspect` 0 件、`@residual(plan:relay-inner-bound-moonshot-plan)` 5 件、sorry 5 件、
- cross-family WynerZiv re-namespacing は **無変更維持** (8+ references 全て temper せず)、
- `lake env lean` 0 errors。

**proof-log**: yes。理由: cross-family entanglement (8 references) を docstring 散文で保護する判断 + 1 件
(`relay_cf_si_decoder_fail_le`) の WynerZiv 同期判断を記録。

### Phase 2.x — ripple (caller drift handling, 散文 transitive 明示) 📋

- [ ] **2.x.1** caller 列挙: 既に上流→下流 chain 順で sweep 済のため、本 family **内** transitive caller は
  Phase 2.1/2.2/2.3/2.5 内で全て直接 sorry 化済 (Phase 2.4 default は constructive 維持で transitive
  不要)。本 family **外** caller の検索:
  ```bash
  rg -l '(relay_(broadcast|mac)_cut\b|relay_cutset_outer_bound|relay_(df|cf)_inner_bound(_(min_form|two_bounds|log_rate|two_conditions))?\b|relay_(df|cf)_consistent\b|IsRelayDFBlockMarkovWitness|IsRelayCFBinningWitness|RelayDFAchievable|RelayCFAchievable|RelayDFRateWitness|IsBlockMarkovEncoderHyp|IsRelayDecodableHyp|IsDestinationJointlyTypicalHyp|IsCFSideInfoDecodeHyp)' InformationTheory/Shannon/ | grep -v Relay
  ```
  expected hit: なし (Bash 確認済、家族外の use site は BroadcastChannel / MultipleAccessChannel /
  MACL1Discharge / LZ78ConverseAsymptotic で **docstring 内 reference のみ** = 実 Lean 呼出は 0)。
- [ ] **2.x.2** family 外 caller 0 件確認後、本 Phase は **scope 内処理ゼロ**で終了 (transitive 散文化対象なし)。
  family 内 transitive は Phase 2.1-2.5 完了時点で全件処理済。
- [ ] **2.x.3** **cross-family caller (WynerZiv 経由)**: `RelayCFBinningBody.lean:348`
  (`wyner_ziv_binning_via_covering_packing` 直接呼出) は **本 plan で touch しない**、WynerZiv sweep
  完了状態に応じて Phase V 直前に散文を追加 (Phase 2.5.6 参照)。

**Phase 2.x DoD**: family 外 caller 0 件、cross-family transitive は Phase V で確定。

**proof-log**: no (mechanical 散文追加なし、空 phase)。

### Phase 2.6 — predicate retract-candidate 付与 📋

family 内 closed の load-bearing predicate / hypothesis に `@audit:retract-candidate(load-bearing-predicate)` を付与:

| file:line | predicate | cross-family consumer? | retract-candidate 付与方針 |
|---|---|---|---|
| `RelayInnerBound.lean:?` (要 verbatim 行) | `RelayDFAchievable` (核 predicate) | No (family 内) | 付与 + docstring 散文 |
| `RelayInnerBound.lean:431-437` | `RelayCFAchievable` (核 predicate) | No | 同上 |
| `RelayInnerBodyDischarge.lean:143-148` | `IsRelayDFBlockMarkovWitness` (alias of RelayDFAchievable) | No | 付与 + **alias 性 docstring 明示** (Phase 0 inline detection: tier 5 alias defect 寄り、未決事項 #1) |
| `RelayInnerBodyDischarge.lean:335-340` | `IsRelayCFBinningWitness` (alias of RelayCFAchievable) | No | 同上 |
| `RelayDFBlockMarkovBody.lean:212-219` | `IsBlockMarkovEncoderHyp` | No (family 内) | **Phase 2.4 default なら付与しない** (constructive consumer のみ、load-bearing でない判定) / 代替なら付与 |
| `RelayDFBlockMarkovBody.lean:230-231` | `IsRelayDecodableHyp` (`def := R ≤ Imrh + Iry`、純算術) | No | **付与しない** (regularity-like、load-bearing でなく rate-region 等価) |
| `RelayDFBlockMarkovBody.lean:239-240` | `IsDestinationJointlyTypicalHyp` (`def := R ≤ Ibroad`、純算術) | No | **付与しない** (同上) |
| `RelayCFBinningBody.lean:263` | `IsCFSideInfoDecodeHyp` (= `IsWynerZivBinningAchievable` re-namespacing alias) | **Yes (indirect, WynerZiv の `IsWynerZivBinningAchievable` の alias)** | **付与する**、docstring 散文に「`IsWynerZivBinningAchievable` の re-namespacing alias、WynerZiv 側 sweep の retract-candidate 状態に同期」を明示 |

**cross-family (WynerZiv) predicate は touch しない**:
- `IsWynerZivBinningCovering` (WynerZivBinningCovering.lean:106)
- `IsWynerZivBinningPacking` (WynerZivBinningCovering.lean:180)
- `IsWynerZivBinningAchievable` (WynerZivBinningCovering.lean:416)
これらは **WynerZiv 側 sweep の Phase 2.3 で `@audit:retract-candidate(load-bearing-predicate)` 付与 +
cross-family 注記** が予定されている (`docs/shannon/wynerziv-sorry-migration-plan.md` Phase 2.3、cross-family
注記に「Relay CF (`RelayCFBinningBody.lean`) が consumer に存在」を含む)。本 sweep では touch せず、未決事項 #2 で escalate。

- [ ] **2.6.1** 各 family 内 predicate の docstring に `@audit:retract-candidate(load-bearing-predicate)` 付与
  (上表に従う)。
- [ ] **2.6.2** `IsCFSideInfoDecodeHyp` (line 263) に付与時、docstring 散文に WynerZiv 側 alias 性を明示。
- [ ] **2.6.3** `IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` の alias 性 (= `RelayDFAchievable` /
  `RelayCFAchievable` を unfold するだけ) を docstring に明示。「**Tier 5 alias defect 寄り — 後続 plan で
  deprecation 判定**」を併記 (未決事項 #1)。

**Phase 2.6 DoD**: `@audit:retract-candidate(load-bearing-predicate)` 5 件 (`RelayDFAchievable` /
`RelayCFAchievable` / `IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` / `IsCFSideInfoDecodeHyp`)
付与済 + alias / cross-family 散文注記済。

**proof-log**: no (mechanical 付与)。

### Phase 2.7 — audit-2 (independent honesty audit) 📋

- [ ] **2.7.1** Fresh `honesty-auditor` (または `general-purpose` + SoT brief) を起動。対象:
  - Phase 2.1 (RelayCutset 3 件、cutset chain hyp 削除 + 🟢ʰ 散文 refine)
  - Phase 2.2 (RelayInnerBound 9 件、`h_ach` 削除 + 2 plan slug 交叉判定)
  - Phase 2.3 (RelayInnerBodyDischarge 15 件、witness 削除 + alias 判定)
  - Phase 2.4 (RelayDFBlockMarkovBody 4 件、**default = constructive recovery / 代替 = L-MIG-1 sorry 化** の境界判定)
  - Phase 2.5 (RelayCFBinningBody 5 件、underscore `_h_decode` 保持 + cross-family aware sorry 化)
  - Phase 2.6 (5 predicate retract-candidate 付与 + alias 散文)
- [ ] **2.7.2** verdict 受領 + 修正対応:
  - `ok` → Phase V 着手。
  - `questionable` → docstring refine or 散文追記、Phase V 進行。
  - `defect` → 当該 declaration を撤回 / 修正、Phase V 進行前に解決。
- [ ] **2.7.3** **Phase 2.4 L-MIG-1 判定**: auditor が 4 件全てで constructive recovery 認定なら default 維持、
  load-bearing 認定なら 4 件全 sorry 化に切替 (本 plan 内追加 patch)。
- [ ] **2.7.4** **2 plan slug 交叉判定**: `relay_df_consistent` / `relay_cf_consistent` / `relay_df_consistent_discharged` /
  `relay_cf_consistent_discharged` / `relay_cf_consistent_binning_discharged` の 5 件で `@residual` slug を
  auditor verdict に従い:
  - 単一 slug 維持 (暫定 `plan:relay-inner-bound-moonshot-plan`)、または
  - 散文で「both `plan:relay-inner-bound-moonshot-plan` and `plan:relay-cutset-moonshot-plan` are closure
    candidates (compound conclusion)」 明示。

**proof-log**: yes (verdict + 対応記録)。

### Phase V — verify + 計画反映 📋

- [ ] **V.1** 全 5 file (+ family 内 transitive 影響受ける suspect-無し file) で `lake env lean` 確認:
  ```bash
  for f in InformationTheory/Shannon/RelayCutset.lean \
           InformationTheory/Shannon/RelayInnerBound.lean \
           InformationTheory/Shannon/RelayInnerBodyDischarge.lean \
           InformationTheory/Shannon/RelayDFBlockMarkovBody.lean \
           InformationTheory/Shannon/RelayCFBinningBody.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```
  signature 改変があった file (RelayCutset / RelayInnerBound / RelayInnerBodyDischarge / RelayCFBinningBody)
  は事前に `lake build InformationTheory.Shannon.Relay<X>` で olean refresh (Pilot Pattern A)。
  Phase 2.4 default なら RelayDFBlockMarkovBody は signature 改変なし → olean refresh 不要。

- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:suspect' InformationTheory/Shannon/Relay*.lean | awk -F: '{s+=$2} END {print "suspect:", s}'   # = 0
  rg -c '🟢ʰ' InformationTheory/Shannon/Relay*.lean | awk -F: '{s+=$2} END {print "🟢ʰ:", s}'                 # = 0
  rg -c '@residual\(plan:relay-inner-bound-moonshot-plan\)' InformationTheory/Shannon/Relay*.lean | awk -F: '{s+=$2} END {print "residual(IB):", s}'
  rg -c '@residual\(plan:relay-cutset-moonshot-plan\)' InformationTheory/Shannon/Relay*.lean | awk -F: '{s+=$2} END {print "residual(CS):", s}'
  rg -c '@audit:retract-candidate\(load-bearing-predicate\)' InformationTheory/Shannon/Relay*.lean | awk -F: '{s+=$2} END {print "retract:", s}'
  # word-boundary は backtick-quoted docstring 内 sorry も拾うので参考値、warning 数を信頼:
  rg -nw 'sorry' InformationTheory/Shannon/Relay*.lean | wc -l
  ```
  期待値: suspect 0、🟢ʰ 0、residual(IB) ~28-32、residual(CS) ~3-5 (2 plan slug 交叉 5 件の slug 配分次第)、
  retract 5、sorry warning ~32-36 (Phase 2.4 default なら 32、L-MIG-1 代替なら 36)。

- [ ] **V.3** 親 plan banner 更新:
  - `relay-inner-bound-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了 (本 plan 参照)、L-RI1〜RI4
    pass-through 設計は変更なし (predicate retract-candidate のみ付与)」を追記。
  - `relay-cutset-moonshot-plan.md` 冒頭 banner に同様 (L-RC1/RC2 chain hyp の sorry-based 移行完了)。

- [ ] **V.4** **WynerZiv sweep の最新状態を確認** (`docs/shannon/wynerziv-sorry-migration-plan.md` の Phase V
  完了タイムスタンプ + `rg @audit:retract-candidate InformationTheory/Shannon/WynerZivBinningCovering.lean` の付与
  状況)。WynerZiv 側 Phase 1.5 が完了済 (`wyner_ziv_binning_via_covering_packing` sorry 化済) なら、
  `RelayCFBinningBody.lean:348` 経由の transitive sorry が顕在化しているため、`relay_cf_si_decoder_fail_le`
  (line 328、suspect 無し本体) の docstring に **「transitive sorry via `wyner_ziv_binning_via_covering_packing`
  (WynerZiv sweep Phase 1.5 retreat)」** 散文を追加。WynerZiv sweep 未完了なら散文追加を遅延 (handoff で
  明示)。

- [ ] **V.5** Pilot 知見を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレに反映:
  - Relay family は **全 36 件 P + cross-family entanglement 8+1 references** (WynerZiv 側との結合) → Pattern G
    最初の本格適用例として記録 (WynerZiv pilot で初出、Relay で 8+ references 規模に拡大)。
  - constructive recovery 候補 4 件 (`relayDFRateWitness_*`) の inline detection / L-MIG-1 判断境界を記録 →
    Hoeffding pilot の 1 件 (`isHoeffdingMinimizerFullSupport_of_lagrange`) に続く 2 例目。
  - **2 plan slug 交叉 5 件** の `@residual` slug 判定は未解決 (audit-tags.md vocabulary 拡張候補) → 後続 PR
    で「compound `@residual(plan:slug1, plan:slug2)` EBNF 拡張」検討提案。
  - **alias defect 寄り** (`IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` = `RelayDFAchievable` /
    `RelayCFAchievable` の純 alias) は **tier 5 borderline** → 後続 deprecation plan で扱う候補。

## 撤退ライン

- **L-MIG-1 (Phase 2.4 で constructive recovery 認定 → 4 件タグ削除のみ)**: planner default は constructive
  recovery (タグ削除のみ)。auditor が「`h_enc` が load-bearing predicate のため wrapper も transitive
  load-bearing で sorry 化が必要」と判定したら 4 件全 sorry 化に切替 (Phase 2.7 で確定)。逆に「wrapper 自身は
  constructive (arithmetic core)、`h_enc` を `IsBlockMarkovEncoderHyp` の existence consequence として通
  すだけ」と判定したら default 維持。
- **L-MIG-2 (cross-family predicate 削除提案禁止、未決事項 escalate)**: WynerZiv 側 3 predicate
  (`IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable`) は
  `RelayCFBinningBody.lean` で 6+ references で消費。**本 sweep で touch しない**、未決事項 #2 で escalate。
  さらに **WynerZiv 側 sweep の Phase 2.3** で当該 predicate に `@audit:retract-candidate` 付与 + cross-family
  注記が予定済なので、本 plan は完了タイミングを **WynerZiv plan と同期 / 後追い**で進める。WynerZiv 完了
  前に本 sweep を完走させる場合は、WynerZiv 側 predicate 状態の docstring 散文を本 sweep が一切変更しない
  ことを確約。
- **L-MIG-3 (proof done と方向衝突)**: 本 plan の sorry 化が `relay-df-block-markov-discharge-*` /
  `relay-df-sliding-window-discharge-*` / `relay-cf-wz-binning-discharge-*` / `relay-cf-si-decode-discharge-*`
  の進行と衝突 (例: discharge 側が `RelayDFAchievable` の特定 construction を closure 入口として現役利用、
  または `IsRelayCFBinningWitness` alias の `def := …` を直接 unfold) した場合、本 plan は Phase 2.3 / 2.6
  を pause、discharge 側 plan の signature を変更しない範囲で predicate を residual 化する別レシピを検討
  (alias の def 改変 vs `@audit:retract-candidate` 付与のみ、両者共存可能か再判定)。
- **L-MIG-4 (Approach 変更: pilot scope 縮減)**: Phase 2 全体 (36 件 sorry 化 + 5 predicate 処理) が 1-2
  session で完走しない / honesty-auditor が DEFECT を多発させる場合、上流 → 下流 chain の **上 3 file** のみで
  pilot を close し、`RelayCFBinningBody.lean` 5 件 + `RelayDFBlockMarkovBody.lean` 4 件は後続 session に
  分離 (cross-family + constructive borderline の 2 重 risk があるため最後に切り離せる構造)。
- **L-MIG-5 (Wall name register 拡張提案 R4 の判断保留)**: Phase V で「新 wall (`relay-block-markov-aep` /
  `csiszar-sum-conditional`) を追加するか、既存 `joint-typicality-multi` に集約するか、`plan:` slug 揃え
  維持か」を 3 択で auditor + user 確認。本 plan の sweep は **plan: slug 揃え維持**で進行、wall register
  拡張は別 PR (未決事項 #4)。

## 未決事項

planner が判断つかない事項を列挙。auditor 委任 / user 確認に区分:

1. **`IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` の alias defect 判定** (auditor 判定対象 + user
   確認):
   両 alias は `def := RelayDFAchievable` / `def := RelayCFAchievable` の pure rename (verbatim 確認、`RelayInnerBodyDischarge.lean:143-148/335-340`)。CLAUDE.md「検証の誠実性」の **tier 5 alias defect** 候補
   寄りだが、`RelayDFAchievable` / `RelayCFAchievable` は family 内 honest open IT residual (`audit-tags.md`
   tier 4 → tier 2 移行対象) として残り、alias は historical naming consistency (Cover-Thomas Theorem
   15.10.2/15.10.3 の "witness" 用語 ↔ Mathlib-style "achievable" 用語の橋渡し) のため残置候補。本 plan の
   Phase 2.6 デフォルトは **retract-candidate 付与 + alias 散文明示**で残置。**user 確認待ち**:
   - (a) 残置 (現状維持)、(b) `RelayDFAchievable` / `RelayCFAchievable` に統合 (alias 削除)、
     (c) 逆方向統合 (`RelayDFAchievable := IsRelayDFBlockMarkovWitness`、textbook 用語優先) の 3 択。
   - 別 deprecation plan として後続 session で扱う候補。

2. **cross-family entanglement (WynerZiv 側) の sweep 統合判断** (planner escalate / 並列 plan 整合):
   - `RelayCFBinningBody.lean` の `IsCFSideInfoDecodeHyp` (`= IsWynerZivBinningAchievable` re-namespacing alias、
     `RelayCFBinningBody.lean:263`) は本 plan で `@audit:retract-candidate(load-bearing-predicate)` 付与予定。
   - WynerZiv 側 3 predicate (`IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` /
     `IsWynerZivBinningAchievable`) は `docs/shannon/wynerziv-sorry-migration-plan.md` Phase 2.3 で同じ
     付与が予定済。両 sweep の **完了タイミング同期**が必要 (相互 docstring 散文「Relay CF が consumer」/
     「WynerZiv 側 retract-candidate 付与済」が cross-reference)。
   - **R3 / R14 に従い削除提案禁止**、両 sweep 並列起動時の orchestrator level 整合は本 plan 範囲外。
   - **escalate 候補**: 後続 PR で「Relay-WZ 統合 sweep plan」を立てて 4 predicate (1 Relay alias + 3 WynerZiv)
     をまとめて deprecation 判断する選択肢。

3. **`relay_*_consistent` 系 5 件の 2 plan slug 交叉判定** (auditor 判定対象 + audit-tags.md vocabulary 候補):
   `relay_df_consistent` / `relay_cf_consistent` (Phase 2.2.5) + `relay_df_consistent_discharged` /
   `relay_cf_consistent_discharged` (Phase 2.3.5) + `relay_cf_consistent_binning_discharged` (Phase 2.5.5) の
   5 件は結論型が **`(R ≤ relayCutsetBound …) ∧ Relay{DF,CF}InnerBoundExistence …`** で 2 plan の交叉。
   本 plan のデフォルトは `@residual(plan:relay-inner-bound-moonshot-plan)` のみ付与 + docstring 散文で
   cutset chain 依存も明示。**auditor 判定対象**: 単一 slug + 散文 vs compound slug の EBNF 拡張要否。
   後者なら `audit-tags.md`「Wall name register」 / 「`@residual(<class>:<slug>)` EBNF」拡張 PR を別途検討。

4. **Wall name register 拡張 (R4) の判断保留** (user 確認):
   本 sweep では `plan:` slug 揃え (新 wall 追加なし) でクローズ。Phase V handoff に次の選択肢を残す:
   - (a) `joint-typicality-multi` を MAC/BC/Relay 共通 wall に拡張、後続 sweep で `wall:joint-typicality-multi`
     に置換。
   - (b) Relay 専用 wall `relay-block-markov-aep` を新規追加 (Cover-Thomas 15.10.2 block-Markov AEP / sliding-
     window decoder)、CF 側は WynerZiv 経由 (別 wall または `plan:`)。
   - (c) `plan:` slug 揃え維持 (現状)。
   - 判断は **後続 MAC/BC family sweep の inventory 完了後** に user + auditor 委任。

5. **`relay_cf_si_decoder_fail_le` (`RelayCFBinningBody.lean:328`、suspect 無し本体) の docstring 散文追記
   タイミング**: WynerZiv sweep Phase 1.5 完了 (= `wyner_ziv_binning_via_covering_packing` の sorry 化済) を
   確認後、本 plan の Phase V.4 で docstring に「transitive sorry via WynerZiv Phase 1.5」散文を追加。WynerZiv
   sweep 未完了なら **本 sweep の handoff に明示** + 追加を後続 session に委ねる。

6. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。L-RI1〜RI4 (block-Markov coding + sliding-window decoder + WZ
   binning achievability) + L-RC1/RC2 (Csiszár sum identity per-letter chain) の **analytical closure は未着手
   のまま** 本 plan は close。`relay-{inner-bound,cutset}-moonshot-plan.md` の honest pass-through 設計 (load-
   bearing hypothesis 形 publish) を sorry-based 形式に移行するだけ。companion seed
   (`relay-df-*-discharge` / `relay-cf-*-discharge`) の defer 状態は変えない。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner (本 session、docs-only) が `InformationTheory/Shannon/Relay{Cutset,InnerBound,
   InnerBodyDischarge,DFBlockMarkovBody,CFBinningBody}.lean` 5 file の legacy tag 51 件 (suspect 36 + 散文 🟢ʰ
   15) を verbatim 読込で per-declaration 分類。
   - **既存 sorry 計数**: word-boundary `rg -nwc 'sorry'` で **5 file 全て 0 hit** (Pilot Pattern D 適用済)。
   - **⚠ / HONESTY ALERT / FALSE 検出**: 全 file 0 hit (Pattern H 該当なし)。
   - **cross-family dependency 発見**: `RelayCFBinningBody.lean:2` (`import WynerZivBinningCovering`) + 8
     references (`IsWynerZivBinningCovering`/`Packing`/`Achievable` を 3 alias で再利用) + `RelayInnerBodyDischarge.lean:2`
     (`import WynerZivBinningBody`) + 1 `wzBinningMeasure` alias + 1 `.instIsProbabilityMeasure` forward + 1 直接呼出
     (`relay_cf_si_decoder_fail_le` body の `wyner_ziv_binning_via_covering_packing`)。**R3 / R14 verbatim 確認済**、
     Phase 2.5 / 2.6 で削除提案禁止 + 未決事項 #2 escalate。
   - **alias defect 寄り検出**: `IsRelayDFBlockMarkovWitness` / `IsRelayCFBinningWitness` (`RelayInnerBodyDischarge.lean:143-148/335-340`)
     は `def := RelayDFAchievable` / `:= RelayCFAchievable` の pure rename → tier 5 borderline、未決事項 #1
     escalate。
   - **constructive recovery 候補 4 件発見**: `RelayDFBlockMarkovBody.lean` の `relayDFRateWitness_*` 系 4
     件は body 純構成的 (verbatim 確認、`obtain` + `refine` + `Classical.arbitrary`)。Phase 2.4 default を
     「タグ削除のみ」(Hoeffding pilot 類似)、auditor 判定で L-MIG-1 切替可能と設計。
   - **戦略確定**: 上流 → 下流 chain 順序 (Cutset → InnerBound → InnerBodyDischarge → DFBlockMarkovBody → CFBinningBody)、
     cross-family 保護 (削除禁止)、shared wall 集約なし (`plan:` slug 揃え)、proof done は範囲外。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
