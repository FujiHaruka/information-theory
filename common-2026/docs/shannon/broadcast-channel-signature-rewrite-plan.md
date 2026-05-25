# Shannon: BC `bc_common_rate_bound` / `bc_private_rate_bound` signature rewrite plan

> **Parent**:
> - [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) — T3-C BC moonshot
> - [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) §Phase 2.3.b — 本 plan の **直接の起源** (auditor 委任の「genuine 形再設計」step)
> - 関連: [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)
>
> **本 plan の独立 workstream 化の理由**:
> `mac-bc-sorry-migration-plan` Phase 2.3 で 2 declaration は既に
> `(_, _, R, I) : R ≤ I := by sorry` + `@residual(defect:false-statement)` +
> `@audit:closed-by-successor(broadcast-channel-moonshot-plan)` の sorry-based
> 形態に migrated 済 (commit `1bd2564` 系列、`@audit:closed-by-successor`
> slug が **本 plan の名前を予約**)。残課題は MAC analogue
> `mac_single_rate_bound₁/₂` 同型の genuine entropy-level signature への
> rewrite であり、本 plan で正式 closure する。
> Round 2 残課題 follow-up リスト (handoff-sorry-migration.md §D)
> 「`bc_common_rate_bound` / `bc_private_rate_bound` signature rewrite」と一対一対応。

## Status (起草時、2026-05-26)

> **特異性**: 本 plan は通常の sorry-based migration plan と異なり、**proof done
> (0 sorry / 0 residual) に到達できる** 例外的 case。理由: BC 自身の同 file 内に
> 既に genuine derivation kernel `bc_rate_le_of_fano`
> (`BroadcastChannel.lean:528`, `private theorem`) が存在し、entropy-level Fano +
> chain + cleanup の 3 hypothesis から `R ≤ I + ε` を自前で証明する arithmetic
> kernel を提供している。signature を MAC analogue (`mac_single_rate_bound₁/₂`,
> `MultipleAccessChannel.lean:450/474`) と同型に rewrite すると body は
> `bc_rate_le_of_fano ...` 呼出 1 行で完結 (sorry 不要)。
>
> MAC 側は `mac_single_rate_bound₁/₂` が現在 `sorry` 残置 (`@residual(plan:mac-bc-sorry-migration-plan)`、
> wall:joint-typicality-multi pass-through 設計、`mac_rate_le_of_fano` が存在しない
> ため自前 arithmetic は別 plan 待ち)。BC 側は genuine kernel 既存ゆえ MAC 先行で
> proof done 到達可能 (Phase 2.3.b で予測されていた asymmetry の正式確認)。

## 進捗

- [ ] Phase 0 — 規模見積もり + verbatim 確認 + downstream consumer 確認 📋
- [ ] Phase 1 — `bc_common_rate_bound` signature rewrite (genuine 形 via `bc_rate_le_of_fano`) 📋
- [ ] Phase 2 — `bc_private_rate_bound` signature rewrite (同上、mirror) 📋
- [ ] Phase V — verify + olean refresh + 親 plan banner 更新 + handoff Round 2 残課題 closure 📋

## ゴール / Approach

### ゴール (短形)

`Common2026/Shannon/BroadcastChannel.lean` の 2 declaration を MAC analogue
`mac_single_rate_bound₁/₂` 同型の genuine entropy-level signature に rewrite し、
body は `bc_rate_le_of_fano` 呼出に置換。**0 sorry / 0 @residual / proof done**
に到達 (`@audit:closed-by-successor(broadcast-channel-moonshot-plan)` も
`@audit:ok` に昇格、auditor pass 後)。

### Approach (全体戦略)

3 つの構造観察から成る pivot:

1. **consumer 0 件 (verbatim 確認済)** — `rg -n 'bc_common_rate_bound|bc_private_rate_bound' Common2026/`
   は **`BroadcastChannel.lean` 自身の docstring 散文 (line 37, 109) + declaration
   header (line 453, 492) のみ**。`bc_capacity_region_outer_bound`
   (`BroadcastChannel.lean:591`) は両 declaration ではなく **直接
   `bc_rate_le_of_fano` を呼ぶ** (line 603, 605)。つまり 2 declaration は現在
   **dead code に近い leaf thin wrapper**。signature 改変の cross-file ripple
   は **0 file / 0 declaration**、本 file 内 docstring の散文 2 hits の整合更新
   のみ (consumer chain scope warning は **発火しない**)。

2. **genuine kernel 既存** — `bc_rate_le_of_fano` (`BroadcastChannel.lean:528`,
   `private theorem`) が entropy-level Fano + chain + cleanup → `R ≤ I + ε` の
   arithmetic を完結。`bc_capacity_region_outer_bound` body
   (`BroadcastChannel.lean:602-606`) で既に 2 回呼出され、`field_simp` / `linarith`
   ベースの genuine proof として 0 sorry で publish 済。同 file 内 `private` ゆえ
   visibility 変更不要 (CLAUDE.md「private は file-scoped」)、callers (両 declaration の
   新 body) は同 file 内なので reuse 可能。

3. **MAC analogue verbatim 一致** — `mac_single_rate_bound₁` (`MultipleAccessChannel.lean:450-458`):
   ```
   {M₁ M₂ n : ℕ} (hn : 0 < n) (_c : MACCode M₁ M₂ n α₁ α₂ β)
   (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
   (h_fano   : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
   (h_chain  : I_marg₁ ≤ (n : ℝ) * I₁)
   (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
   : R₁ ≤ I₁ + ε
   ```
   `mac_single_rate_bound₂` は indices swap した mirror。BC 側は
   `mac_bc-sorry-migration-plan.md:641-650` で planner が下書きした genuine 形を
   採用し、各々 `M₂`/`M₁` (BC は common = `R₂`, private = `R₁`) と `I_u`/`I_xy`
   に名前付け替えるのみ。

これら 3 つから、本 plan は signature 改変 + body 置換のみで proof done に到達。
撤退ラインは consumer 想定外発見時の Phase 2.3 状態維持 (現状維持) 1 本のみ。

### MAC peer との関係 (handoff Round 2 残課題リスト整合)

handoff §D で並んで列挙されている **2 件の MAC peer**:
- `mac_capacity_region_outer_bound_three_bounds` — Pattern B constructive recovery candidate
- BC `bc_capacity_region_outer_bound_corner_limit` — 同上

これら 2 件は **本 plan の scope 外**。Pattern B (constructive recovery) は
仮定が unnecessary か否かを auditor judgement で判定する別系統の手順で、
本 plan の 2 declaration (`bc_common/private_rate_bound`) とは **手法的に独立**:

- 本 plan = **signature rewrite** (entropy-level hypothesis 3 件を新規追加 +
  body を `bc_rate_le_of_fano` 呼出に置換)
- Pattern B candidate = **hypothesis 列挙の削減** (現 hypothesis が真に
  load-bearing か constructive に検証して削除候補化)

両者は同じ "rewrite" 範疇でも別アプローチゆえ、本 plan は前者のみ扱う。
Pattern B candidate 2 件は handoff Round 2 残課題リストにそのまま残し、別
session の別 plan で扱う (本 plan で touch しない、scope creep 防止)。

## Phase 0 — 規模見積もり + verbatim 確認 + downstream consumer 確認 📋

### 0.1 verbatim signature 確認 (現状、sorry-based migrated 済)

`Common2026/Shannon/BroadcastChannel.lean:453-458` 現状:

```lean
@residual(defect:false-statement)
@audit:closed-by-successor(broadcast-channel-moonshot-plan) -/
theorem bc_common_rate_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₂ I_u : ℝ) :
    R₂ ≤ I_u := by
  sorry
```

`Common2026/Shannon/BroadcastChannel.lean:492-497` 現状 (mirror):

```lean
@residual(defect:false-statement)
@audit:closed-by-successor(broadcast-channel-moonshot-plan) -/
theorem bc_private_rate_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ I_xy : ℝ) :
    R₁ ≤ I_xy := by
  sorry
```

両者は **load-bearing hypothesis 削除済 + body sorry + `@residual(defect:false-statement)`**
の状態。docstring に独立 audit (2026-05-25) による reclassification 注記済
(`circular` → `false-statement`、universally false counterexample `R := 1, I := 0`
を著者明記)。

### 0.2 bundle predicate の特定 (rewrite 前のもの、現在は既に削除済)

`mac-bc-sorry-migration-plan.md:109-110` より、Phase 2.3 migration 前は:
- `bc_common_rate_bound`: hypothesis `h_commonRateBound_lbh : R₂ ≤ I_u` →
  結論 `R₂ ≤ I_u` と **仮説型 ≡ 結論型** (tier 5 defect: `circular` + name laundering `_lbh` suffix)
- `bc_private_rate_bound`: hypothesis `h_privateRateBound_lbh : R₁ ≤ I_xy` →
  結論 `R₁ ≤ I_xy` 同上

これらは Phase 2.3 で削除済。本 plan は **削除済 hypothesis を補う形で
entropy-level 3 hypothesis を追加**して genuine 形に持っていく。

### 0.3 downstream consumer 確認 (verbatim, Phase 0 直前 rg)

```bash
rg -n 'bc_common_rate_bound|bc_private_rate_bound' Common2026/ docs/
```

結果 (verbatim):
- `Common2026/Shannon/BroadcastChannel.lean:37` (docstring 散文、`bc_*_rate_bound` を thin wrapper として紹介)
- `Common2026/Shannon/BroadcastChannel.lean:109` (docstring 散文、同上)
- `Common2026/Shannon/BroadcastChannel.lean:453` (`bc_common_rate_bound` 自身)
- `Common2026/Shannon/BroadcastChannel.lean:492` (`bc_private_rate_bound` 自身)
- 他 `.lean` 0 件
- `docs/audit/wave1-plan-sync-channel-coding.md` / `docs/shannon/mac-bc-sorry-migration-plan.md` /
  `docs/shannon/broadcast-channel-moonshot-plan.md` — plan/docs 内言及のみ

**consumer chain scope**: **0 file 横断 / 0 declaration drift**。
本 plan は 1 file scope 内で完結 (BroadcastChannel.lean のみ touch)。

### 0.4 規模見積もり

- 触る file: **1 file (`Common2026/Shannon/BroadcastChannel.lean`)**
- 触る declaration: **2 件 (`bc_common_rate_bound` / `bc_private_rate_bound`)**
- 追加行数予測: signature 拡張 2 件 × 約 4 行 = +8 行 / body 置換 2 件 × 約 3 行
  (`bc_rate_le_of_fano ...` 1 行 + 必要なら term-mode 整形) / docstring 整合更新
  (audit reclassification 注記の削除 + genuine 形成功の注記) = 計 +25 行程度
- 削除行数予測: 旧 `by sorry` body / `@residual(defect:false-statement)` タグ /
  「universally false」散文 = -20 行程度
- **net diff 規模**: +5 〜 +10 行 (essentially in-place rewrite)
- sorry 数: 現 **2 sorry → 改変後 0 sorry** (genuine derivation で完結)
- shared sorry 補題化必要性: **不要** (本 file 内 `bc_rate_le_of_fano` を直接呼ぶ)

### 0.5 撤退ライン

- **L-SIGRW-1 (想定外 consumer 出現)**: Phase 0.3 で consumer 0 件を確認済だが、
  Phase 1 直前にもう一度 `rg -n 'bc_common_rate_bound|bc_private_rate_bound'
  Common2026/` を回し、もし新規 caller (本 session 開始から作成された別 file 等)
  が出現していたら **signature 改変を保留** し、現状の Phase 2.3 sorry-based
  状態を維持。consumer 側を別 session で追ってから再起動。本 plan は close
  せず paused 状態 (Phase V の banner 更新も未実施) に置く。

- **L-SIGRW-2 (`bc_rate_le_of_fano` visibility 問題が表面化)**: `private theorem`
  は file-scoped (CLAUDE.md「Project Layout」) ゆえ同 file 内呼出は問題ない想定。
  もし Lean が `bc_rate_le_of_fano` を unknown identifier として弾いた場合 (例:
  名前空間境界の解釈差)、`protected theorem` への visibility 変更を 1 commit
  追加 (visibility 変更は CLAUDE.md 規約で問題なし)。Phase 1 着手時に LSP
  diagnostic で即判明、追加修正は数行で済む想定。

- **L-SIGRW-3 (MAC analogue が signature drift する)**: 本 plan 進行中に MAC 側
  (`MultipleAccessChannel.lean`) で `mac_single_rate_bound₁/₂` の signature 改変が
  並行 commit されると、本 plan の「同型に rewrite」前提が崩れる。MAC 側は本
  plan scope 外、念のため Phase 1 着手前に `git log --oneline --
  Common2026/Shannon/MultipleAccessChannel.lean | head -10` で直近変更を確認、
  signature drift が起きていないことを verbatim 再確認。drift があれば本 plan の
  signature を改めて MAC 直近版に合わせ直す (1 turn 追加)。

**proof-log**: yes (`docs/proof-logs/proof-log-broadcast-channel-signature-rewrite.md`)。
理由: (a) Phase 2.3 → Phase 2.3.b 移行の判定根拠記録、(b) MAC 側 asymmetry
(BC は proof done 到達 / MAC は sorry 残置) の構造観察を後続 plan の参考に残す。

## Phase 1 — `bc_common_rate_bound` signature rewrite (single sweep) 📋

### 1.1 新 signature (verbatim、MAC `mac_single_rate_bound₁` 同型 + BC 命名)

```lean
/-- **Common-message rate bound (genuine entropy-level Fano + chain
derivation)**.

For any BC block code `c` and rate `R₂`, given the entropy-level
Fano-side bound on `(W₂, Y₂^n)`, the per-letter chain inequality
`I_marg_u ≤ n · I_u`, and the `n⁻¹` clean-up estimate, the converse
derives the corner-point bound

```
R₂ ≤ I_u + ε        (where I_u = I(U; Y₂) and ε ≥ 0 is the clean-up slack)
```

via `bc_rate_le_of_fano`. Mirror of the MAC analogue `mac_single_rate_bound₁`
(`MultipleAccessChannel.lean:450`); the BC version is **proof done** because
the divide-by-`n` arithmetic kernel `bc_rate_le_of_fano`
(`BroadcastChannel.lean:528`) is in scope (the MAC analogue cannot do the
same yet because `mac_rate_le_of_fano` is not present).

The entropy-level inputs (`h_fano`, `h_chain`) are genuine real Mathlib gaps
(joint-typicality-multi wall) discharged structurally by upstream plans
`bc-converse-fano-discharge-*` / `bc-converse-chain-rule-discharge-*`; the
present theorem accepts them as raw scalar inequalities so this file
remains structurally minimal. -/
theorem bc_common_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₂ Pe₂ I_marg_u I_u ε : ℝ)
    (h_fano : (n : ℝ) * R₂ ≤ I_marg_u + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_chain : I_marg_u ≤ (n : ℝ) * I_u)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I_u + ε :=
  bc_rate_le_of_fano hn R₂ I_marg_u I_u Pe₂ (Real.log (M₂ : ℝ)) ε
    h_fano h_chain h_cleanup
```

### 1.2 旧 signature との差分

| 項目 | 旧 (Phase 2.3 後) | 新 (Phase 2.3.b = 本 plan) |
|---|---|---|
| 引数 | `(_hn : 0 < n) (_c) (R₂ I_u : ℝ)` (3 args) | `(hn) (_c) (R₂ Pe₂ I_marg_u I_u ε : ℝ) (h_fano) (h_chain) (h_cleanup)` (8 args) |
| 結論型 | `R₂ ≤ I_u` (universally false) | `R₂ ≤ I_u + ε` (genuine, derived) |
| body | `by sorry` | `bc_rate_le_of_fano hn R₂ I_marg_u I_u Pe₂ (Real.log (M₂ : ℝ)) ε h_fano h_chain h_cleanup` (term mode) |
| tags | `@residual(defect:false-statement)` + `@audit:closed-by-successor(...)` | (tags 削除、proof done 状態) |
| `_hn` → `hn` | `_hn` (unused) | `hn` (`bc_rate_le_of_fano` 第 1 引数として load-bearing) |

### 1.3 sub-step

- [ ] **1.1** Phase 0 撤退ライン L-SIGRW-1 再確認 (`rg -n 'bc_common_rate_bound|bc_private_rate_bound' Common2026/` で consumer 0 件継続確認)
- [ ] **1.2** L-SIGRW-3 再確認 (`git log --oneline -- Common2026/Shannon/MultipleAccessChannel.lean | head -5`)
- [ ] **1.3** `Common2026/Shannon/BroadcastChannel.lean:417-458` 周辺 docstring + signature + body の 1 件 `Edit`:
  - docstring: 旧「Audit reclassification (independent honesty audit, 2026-05-25): ... universally false (counterexample: R₂ := 1, I_u := 0)」段落を削除、新「genuine entropy-level Fano + chain derivation」段落に置換 (上記 1.1 の docstring を貼付)
  - `@residual(defect:false-statement)` 削除
  - `@audit:closed-by-successor(broadcast-channel-moonshot-plan)` 削除 (本 plan 自身が closure するので tag 不要、proof done 達成)
  - signature: `(_hn : 0 < n) (_c) (R₂ I_u : ℝ)` → `(hn : 0 < n) (_c) (R₂ Pe₂ I_marg_u I_u ε : ℝ) (h_fano ...) (h_chain ...) (h_cleanup ...)`
  - body: `by sorry` → term-mode `bc_rate_le_of_fano hn R₂ I_marg_u I_u Pe₂ (Real.log (M₂ : ℝ)) ε h_fano h_chain h_cleanup`
- [ ] **1.4** `lake env lean Common2026/Shannon/BroadcastChannel.lean` を実行、0 errors / 0 sorry warning 確認
- [ ] **1.5** もし `bc_rate_le_of_fano` が `private` で resolve しなければ L-SIGRW-2 発動: `BroadcastChannel.lean:528` の `private theorem bc_rate_le_of_fano` を `protected theorem bc_rate_le_of_fano` に変更 (1 行 Edit) + 再 verify

**Phase 1 DoD**:
- `bc_common_rate_bound` 0 sorry / 0 `@residual` / 0 `@audit:*` (proof done 直前)
- `lake env lean` 0 errors

**proof-log**: no (mechanical signature rewrite + term-mode body 1 行、観察事項なし)

## Phase 2 — `bc_private_rate_bound` signature rewrite (single sweep) 📋

### 2.1 新 signature (verbatim、MAC `mac_single_rate_bound₂` 同型 + BC 命名 (private = R₁))

```lean
/-- **Private-message rate bound (genuine conditional Fano + conditional-MI
chain derivation)**.

For any BC block code `c` and rate `R₁`, given the entropy-level
conditional Fano-side bound on `(W₁, Y₁^n) | W₂`, the per-letter
conditional-MI chain inequality `I_marg_xy ≤ n · I_xy`, and the `n⁻¹`
clean-up estimate, the converse derives the corner-point bound

```
R₁ ≤ I_xy + ε       (where I_xy = I(X; Y₁ | U) and ε ≥ 0 is the clean-up slack)
```

via `bc_rate_le_of_fano`. Mirror of `mac_single_rate_bound₂`
(`MultipleAccessChannel.lean:474`); BC version is **proof done** because
`bc_rate_le_of_fano` is in scope (see `bc_common_rate_bound` for the
analogous asymmetry note).

The entropy-level inputs (`h_fano`, `h_chain`) are real Mathlib gaps
(joint-typicality-multi wall) — the conditional Fano on `W₁ → Y₁^n | U^n`
together with the degradation Markov chain is not yet a project lemma —
discharged structurally by upstream plans
`bc-converse-fano-discharge-*` / `bc-converse-chain-rule-discharge-*`. -/
theorem bc_private_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ Pe₁ I_marg_xy I_xy ε : ℝ)
    (h_fano : (n : ℝ) * R₁ ≤ I_marg_xy + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_chain : I_marg_xy ≤ (n : ℝ) * I_xy)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I_xy + ε :=
  bc_rate_le_of_fano hn R₁ I_marg_xy I_xy Pe₁ (Real.log (M₁ : ℝ)) ε
    h_fano h_chain h_cleanup
```

### 2.2 sub-step (Phase 1 の mirror)

- [ ] **2.1** Phase 1 完了後の `lake env lean` 0 errors を前提に Phase 2 開始 (Phase 1 で `bc_rate_le_of_fano` visibility 問題が解決していれば Phase 2 の同じ問題は再発しない)
- [ ] **2.2** `Common2026/Shannon/BroadcastChannel.lean:460-497` 周辺 docstring + signature + body の 1 件 `Edit` (Phase 1.3 の mirror、indices: `R₂ → R₁`, `I_u → I_xy`, `I_marg_u → I_marg_xy`, `Pe₂ → Pe₁`, `M₂ → M₁`)
- [ ] **2.3** `lake env lean Common2026/Shannon/BroadcastChannel.lean` 再 verify

**Phase 2 DoD**:
- `bc_private_rate_bound` 0 sorry / 0 `@residual` / 0 `@audit:*` (proof done 直前)
- `lake env lean` 0 errors

**proof-log**: no (Phase 1 と完全 mirror)

## Phase V — verify + olean refresh + 親 plan banner 更新 + handoff closure 📋

### V.1 全 file `lake env lean` 確認

- [ ] **V.1** signature 改変があったので `lake build Common2026.Shannon.BroadcastChannel` で olean refresh、続いて dependent (`BroadcastChannelSuperposition.lean` / `BroadcastChannelSuperpositionBody.lean` / `BroadcastChannelRandomCodebook*` 系) を `lake env lean` で再 verify
- [ ] **V.2** consumer 0 件 (Phase 0.3 verbatim 確認) ゆえ追加 caller の transitive sorry drift は発生しない想定。dependent ファイルでも `import Common2026.Shannon.BroadcastChannel` 経由の symbol 解決のみ、本質的な再 verify は BroadcastChannel.lean 自身

### V.2 集計コマンド (target file)

```bash
TARGET="Common2026/Shannon/BroadcastChannel.lean"
rg -nw 'sorry' $TARGET                                   # 期待: 0 hit (元 2 件 → 0 件)
rg -n '@residual\(' $TARGET                              # 期待: `bc_capacity_region_outer_bound_corner_limit` の 1 件 (`@residual(plan:mac-bc-sorry-migration-plan)`、本 plan scope 外) のみ
rg -n '@audit:closed-by-successor\(broadcast-channel' $TARGET  # 期待: 0 hit (本 plan で resolve)
rg -n 'defect:false-statement' $TARGET                   # 期待: 0 hit
```

### V.3 親 plan banner 更新

- [ ] **V.3.1** `docs/shannon/broadcast-channel-moonshot-plan.md` 冒頭 Status banner に追記:
  > **2026-05-26 update**: `bc_common_rate_bound` / `bc_private_rate_bound` の
  > signature rewrite (Phase 2.3.b、`docs/shannon/broadcast-channel-signature-rewrite-plan.md`)
  > 完了 — entropy-level Fano + chain + cleanup の 3 hypothesis 受け取りの genuine 形に
  > rewrite し、`bc_rate_le_of_fano` 経由 proof done に到達。MAC analogue
  > `mac_single_rate_bound₁/₂` は `mac_rate_le_of_fano` 不在のため引き続き sorry 残置
  > (`@residual(plan:mac-bc-sorry-migration-plan)`)、BC 側のみ先行 proof done。

- [ ] **V.3.2** `docs/shannon/mac-bc-sorry-migration-plan.md` の Phase 2.3.b section
  に「実施完了」note + 本 plan path リンク追記 (line 633 周辺)

### V.4 handoff Round 2 残課題 closure 反映

- [ ] **V.4** `.claude/handoff-sorry-migration.md` §D「Round 2 残課題 follow-up」
  の bullet「`bc_common_rate_bound` / `bc_private_rate_bound` signature rewrite」
  に completed marker + 本 plan path 追記

### V.5 honesty audit (orchestrator 必須)

本 plan は **`sorry` 削除を伴う signature 改変** = CLAUDE.md「Independent honesty
audit」起動条件「既存 declaration の signature を変更 (引数削除 / 型変更) して
honesty 関連の意味が変わる」直撃。**proof done 達成宣言の前に必ず honesty-auditor
起動**:

- [ ] **V.5.1** orchestrator は `honesty-auditor` を起動 (`subagent_type:
  "honesty-auditor"`)。対象:
  - `bc_common_rate_bound` (新 line) — signature の genuine 性、`bc_rate_le_of_fano`
    呼出の引数順序整合、`h_fano` / `h_chain` / `h_cleanup` が load-bearing か
    regularity precondition か (= load-bearing precondition、本 plan は entropy-level
    hypothesis を pass-through するゆえ honest)
  - `bc_private_rate_bound` 同上 (mirror)
- [ ] **V.5.2** verdict:
  - `ok` → 本 plan close、`@audit:ok` 付与 (tier 1)
  - `questionable` → docstring refine
  - `defect` → 即修正 (sorry-based 状態に戻す等)
- [ ] **V.5.3** auditor 通過後、本 plan 全 Phase ☑ + status banner に
  「proof done achieved 2026-05-26」を記録

**Phase V DoD**:
- BroadcastChannel.lean `sorry` 件数が 2 件減 (旧総数 N → N-2)
- 親 plan banner 更新済
- handoff §D bullet completed
- honesty-auditor pass (verdict `ok`)

**proof-log**: yes — Phase V 末尾に「BC 側のみ先行 proof done 到達」+「MAC 側の
`mac_rate_le_of_fano` 不在 asymmetry」+「将来 MAC 側で同型 kernel 整備時の
ripple plan 提案」の 3 観察を 1 段落で記録

## 撤退ライン (Phase 横断、再掲)

- **L-SIGRW-1**: 想定外 consumer 出現 → Phase 0 で確認、Phase 1 直前にも再確認、出現したら本 plan 保留 + consumer 側別 session
- **L-SIGRW-2**: `bc_rate_le_of_fano` visibility 問題 → `private` → `protected` 変更 (1 行 fix)
- **L-SIGRW-3**: MAC analogue が signature drift → Phase 1 直前 git log 確認、drift があれば 1 turn 追加で MAC 直近版に合わせる

**撤退ライン 0 本発動** が前提シナリオ。L-SIGRW-3 のみ低確率発火、本 plan 実行
session で MAC 側を同時 touch しない限り発火しない。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **`bc_rate_le_of_fano` visibility relaxation の事前必要性** (auditor 判定対象 + Phase 1.5 で実測):
   - `private theorem` (file-scoped) は同 file 内で自由に呼出可能なはず (CLAUDE.md
     「Project Layout」)。Phase 1.5 で resolve できなかった場合のみ `protected
     theorem` に変更。事前変更を本 plan に組み込む必要は **無し** (planner 判断)。

2. **docstring 内の MAC analogue 言及 verbose 度** (auditor 判定対象):
   - 上記 1.1 / 2.1 docstring は MAC asymmetry 説明 ("BC version is proof done
     because ... MAC analogue cannot do the same yet because `mac_rate_le_of_fano`
     is not present") を 2 declaration 双方に含めている。冗長感あるが、後続 sweep で
     MAC 側 kernel 整備時に search で当てるための trail として有用。auditor 判定対象。

3. **`Pe₂` / `Pe₁` の signature 順序** (mechanical、verbatim 確認済):
   - MAC analogue は `(R Pe I_marg I ε : ℝ)` 順 (`MultipleAccessChannel.lean:453,
     477`)、本 plan も同順を採用。Phase 1.3 / 2.2 で実装時に LSP diagnostic で
     再確認。

4. **proof done 到達後の `@audit:ok` 付与タイミング** (auditor 委任):
   - Phase V.5.3 で honesty-auditor `ok` verdict 直後に付与するか、後続 session
     で別途確認後付与するか。本 plan は前者を採用 (V.5.3 で同 commit 付与)、
     auditor の judgement に従う。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **plan 起草時 (2026-05-26、本 plan 作成 turn)**:
   - 当初 brief「2 declaration の signature rewrite を別 plan として正式起草」を
     受領した時点で、2 declaration の現状を verbatim 確認 (`Common2026/Shannon/BroadcastChannel.lean:453, 492`) →
     **既に sorry-based migrated 済** (`@residual(defect:false-statement)` +
     `@audit:closed-by-successor(broadcast-channel-moonshot-plan)`) を発見。
   - brief の「signature rewrite」は **Phase 2.3 (sorry-based migration) 自体ではなく、
     後続の Phase 2.3.b (genuine 形再設計)** を意図していると判定 (handoff §D
     bullet の slug 名と「closed-by-successor(broadcast-channel-moonshot-plan)」が
     一対一対応、本 plan が当該 successor)。
   - また brief 内「中央予測 sorry 数」見積もりは本 plan では **0 sorry / proof done**
     と判定 (通常の sorry-based migration plan と異なる、`bc_rate_le_of_fano` 既存ゆえ)。
     short plan で OK の brief 但し書きと整合。
   - MAC peer 2 件 (`mac_capacity_region_outer_bound_three_bounds` + BC
     `bc_capacity_region_outer_bound_corner_limit`) は Pattern B constructive
     recovery 系で本 plan の signature rewrite とは手法的に独立、scope 外と明記
     (brief 要求事項 §「MAC との rate-region peer 関係」整合)。
