# Shannon: MAC `mac_single_rate_bound₁/₂` + `mac_sum_rate_bound` proof done plan

> **Parent**:
> - [`mac-moonshot-plan.md`](mac-moonshot-plan.md) — T3-B MAC moonshot (`mac_single_rate_bound₁/₂` / `mac_sum_rate_bound` 0 sorry を proof done 集計に含む)
> - [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) §Phase 2.1 — 3 declaration が現状 `@residual(plan:mac-bc-sorry-migration-plan)` で sorry 残置している起源
> - [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) — BC peer (本 plan の構造模倣元、Wave 6 で proof done 到達済 = `@audit:ok`)
> - 関連: [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)
>
> **本 plan の起源**: Wave 6-7 で BC `bc_common_rate_bound` + `bc_private_rate_bound`
> が `bc_rate_le_of_fano` (`BroadcastChannel.lean:431`, private arithmetic kernel)
> 経由で proof done 到達 (Tier 1 `@audit:ok`)。MAC peer の 3 declaration
> (`mac_single_rate_bound₁` `:450` / `mac_single_rate_bound₂` `:474` /
> `mac_sum_rate_bound` `:501`) は同型 kernel 経由で proof done 到達可能か否かを
> 当初未確認であったため、本 plan で正式 closure する。
> handoff `.claude/handoff-sorry-migration.md` §D「Round 2 残課題 follow-up」の
> 「MAC peer 3 declaration」bullet と一対一対応。

## Status (起草時、2026-05-26)

> **特異性 — BC plan と同じく proof done (0 sorry / 0 residual) 到達可能 case**。
>
> **重要発見 (起草 turn、planner verbatim 確認済)**: `mac_rate_le_of_fano` は
> **既に MAC file 内に publish 済** (`MultipleAccessChannel.lean:396-420`,
> `private theorem`)。BC plan 序文の「`mac_rate_le_of_fano` is not present」
> 注記、および `MultipleAccessChannel.lean:106-114` docstring「genuine
> derivations from entropy-level Fano + per-letter chain + clean-up inputs」
> の状況説明は **stale** — 実コードは既に kernel + 3 declaration の組合せが
> 揃っており、3 declaration の body 部 (`by sorry`) のみが kernel 呼出に
> 置換されていない状態。Task brief の前提「`mac_rate_le_of_fano` kernel
> 不在」も同じく stale (本 plan で Phase 0 verbatim 確認により判明)。
>
> 結果として、本 plan は **新規 kernel 追加 Phase 不要 + 3 declaration の
> body 置換のみ**で proof done 到達。BC plan より更に scope が小さい
> (BC: signature 改変 + body 置換 / 本 plan: body 置換のみ、signature は既に
> genuine 形)。

## 進捗

- [ ] Phase 0 — 規模見積もり + kernel verbatim 確認 + 3 declaration verbatim 確認 + downstream consumer 確認 📋
- [ ] Phase 1 — `mac_single_rate_bound₁` body 置換 (`by sorry` → term-mode `mac_rate_le_of_fano ...`) 📋
- [ ] Phase 2 — `mac_single_rate_bound₂` body 置換 (Phase 1 mirror、indices swap) 📋
- [ ] Phase 3 — `mac_sum_rate_bound` body 置換 (sum-rate adaptation、kernel 直接適用可) 📋
- [ ] Phase V — verify + olean refresh + 親 plan banner 更新 + honesty-auditor 必須起動 + handoff Round 2 残課題 closure 📋

## ゴール / Approach

### ゴール (短形)

`Common2026/Shannon/MultipleAccessChannel.lean` の 3 declaration (single user 1 / single user 2 / sum) の body `by sorry` を term-mode `mac_rate_le_of_fano hn R ... h_fano h_chain h_cleanup` の 1 行呼出に置換。**3 sorry → 0 sorry / 0 @residual / proof done** に到達 (`@residual(plan:mac-bc-sorry-migration-plan)` も削除、auditor pass 後 `@audit:ok` 付与)。

### Approach (全体戦略)

**4 つの構造観察**から成る pivot — BC peer plan より更に scope 小:

1. **kernel 既存 (Phase 0 で verbatim 確認済)** — `mac_rate_le_of_fano`
   (`MultipleAccessChannel.lean:396-420`, `private theorem`) が既に MAC file
   内に publish 済。entropy-level Fano + chain + cleanup → `R ≤ I + ε` の
   divide-by-`n` arithmetic を `field_simp` + `linarith` で完結
   (BC kernel `bc_rate_le_of_fano` と verbatim identical、変数名のみ汎用)。

2. **3 declaration の signature 既に genuine 形** — `mac_single_rate_bound₁`
   (`:450-458`) / `_bound₂` (`:474-482`) / `mac_sum_rate_bound` (`:501-510`)
   は既に Phase 2.1 (mac-bc-sorry-migration-plan) で:
   - load-bearing hypothesis (旧 `h_bound : R ≤ I` 循環) を **完全削除**
   - entropy-level 3 hypothesis (`h_fano` / `h_chain` / `h_cleanup`) に
     **既に置換済**
   - 結論型 `R ≤ I + ε` (genuine、削除済 hypothesis から導出可)
   - `@residual(plan:mac-bc-sorry-migration-plan)` 付き、body は `by sorry`
   - docstring に「genuine Fano + per-letter chain-rule derivation」明記済
     (`MultipleAccessChannel.lean:422-449, 460-473, 484-500`)

   つまり「genuine 形に rewrite する」work は **Phase 2.1 で既に完了済** —
   残るは body の `by sorry` を kernel 呼出に置換する **1 turn × 3 件** のみ。

3. **consumer 影響範囲 verbatim 確認 (Phase 0 段階で `rg` 確認済 → §0.3)** —
   `mac_single_rate_bound₁/₂` の caller は **同 file 内 + `MACL2Discharge.lean`
   の `_with_body` wrapper 2 件のみ** (`MACL2Discharge.lean:345-354,
   363-372`)。両 wrapper は **post-rewrite signature と同一の引数順序** で
   既に呼出している (`mac_single_rate_bound₁ hn c R₁ Pe₁ I_marg₁ I₁ ε
   h_fano.fano h_chain.chain h_cleanup`)。signature 不変ゆえ caller 側は
   **無修正で再 verify が通る想定 (0 ripple)**。`mac_sum_rate_bound` の caller
   は 0 件 (docstring 散文 + `MACBodyDischarge.lean` 内 docstring 散文のみ)。

4. **sum-rate も kernel 直接適用可** (BC peer には sum-rate 無し、本 plan 固有の
   verbatim 確認事項) — `mac_sum_rate_bound` の signature (`:501-510`):
   ```
   (h_fano : (n : ℝ) * (R₁ + R₂)
       ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
   (h_chain : I_joint ≤ (n : ℝ) * Iboth)
   (h_cleanup : (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε)
   : R₁ + R₂ ≤ Iboth + ε
   ```
   kernel の汎用 signature `(R I_marg I Pe L ε : ℝ)` に `R := R₁ + R₂`,
   `I_marg := I_joint`, `I := Iboth`, `Pe := Pe_joint`, `L := Real.log
   ((M₁ : ℝ) * (M₂ : ℝ))` を bind すれば **そのまま型一致**。sum-rate 特有の
   adaptation (kernel 拡張 / 二段適用 / `add_le_add` で結合) は **一切不要**。
   `mac_rate_le_of_fano hn (R₁ + R₂) I_joint Iboth Pe_joint
   (Real.log ((M₁ : ℝ) * (M₂ : ℝ))) ε h_fano h_chain h_cleanup` の 1 行で完結。

これら 4 つから、本 plan は 3 declaration の body を mechanical に `by sorry`
→ term-mode kernel 呼出に置換するだけ。撤退ラインは consumer 想定外発見時 /
kernel visibility 問題発生時のみ。

### BC peer (`broadcast-channel-signature-rewrite-plan.md`) との対称性 / 差分

| 項目 | BC plan (済) | 本 plan (MAC) |
|---|---|---|
| 対象 declaration | 2 件 (`bc_common_rate_bound` / `bc_private_rate_bound`) | 3 件 (`_bound₁` / `_bound₂` / `mac_sum_rate_bound`) |
| 着手前の状態 | signature が `(R I : ℝ) : R ≤ I := by sorry` (Phase 2.3 false-statement) | signature **既に genuine 形** (3 raw scalar hypothesis 受取、結論 `R ≤ I + ε`) |
| Phase 構成 | signature rewrite (2 Phase) + verify (1 Phase) | body 置換のみ (3 Phase) + verify (1 Phase) |
| kernel 必要性 | `bc_rate_le_of_fano` (既存、BC file 内) | `mac_rate_le_of_fano` (**既存、MAC file 内、verbatim 確認済**) |
| sum-rate 扱い | BC に sum-rate 無し (本 plan 固有) | kernel 直接適用可 (`R := R₁ + R₂`, `L := Real.log (M₁ * M₂)` で型一致) |
| net diff 規模 | +25 行 (signature 拡張 + body) | **+9 〜 +12 行** (`by sorry` 1 行 → term-mode kernel 呼出 2-3 行 × 3) |
| 撤退ライン | L-SIGRW-1/2/3 | L-MAC-PD-1/2/3 (consumer / kernel visibility / kernel verbatim drift) |

### 撤退ライン scope warning

本 plan は **撤退ライン発火想定 0 本** が前提シナリオ。consumer chain は 1 file
内 + `MACL2Discharge.lean` の 2 件 wrapper のみで scope expansion 警告
(3+ file 横断) は発火しない。signature 不変ゆえ wrapper 側の term-mode body
も無修正で型 check 通る想定。

## Phase 0 — 規模見積もり + kernel verbatim 確認 + 3 declaration verbatim 確認 + downstream consumer 確認 📋

### 0.1 kernel verbatim 確認 (起草 turn で実施済、本 plan 起源)

`Common2026/Shannon/MultipleAccessChannel.lean:396-420` 現状 (verbatim):

```lean
private theorem mac_rate_le_of_fano
    {n : ℕ} (hn : 0 < n) (R I_marg I Pe L ε : ℝ)
    (h_fano : (n : ℝ) * R ≤ I_marg + 1 + Pe * L)
    (h_chain : I_marg ≤ (n : ℝ) * I)
    (h_cleanup : (1 + Pe * L) / (n : ℝ) ≤ ε) :
    R ≤ I + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_fano' : R ≤ (I_marg + 1 + Pe * L) / (n : ℝ) := by
    have hdiv : (n : ℝ) * R / (n : ℝ) ≤ (I_marg + 1 + Pe * L) / (n : ℝ) :=
      div_le_div_of_nonneg_right h_fano (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rwa [hcancel] at hdiv
  have h_split : (I_marg + 1 + Pe * L) / (n : ℝ)
      = I_marg / (n : ℝ) + (1 + Pe * L) / (n : ℝ) := by
    rw [show I_marg + 1 + Pe * L = I_marg + (1 + Pe * L) by ring, add_div]
  have h_Imarg_div : I_marg / (n : ℝ) ≤ I := by
    have hdiv : I_marg / (n : ℝ) ≤ (n : ℝ) * I / (n : ℝ) :=
      div_le_div_of_nonneg_right h_chain (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * I / (n : ℝ) = I := by field_simp
    rwa [hcancel] at hdiv
  have : R ≤ I_marg / (n : ℝ) + (1 + Pe * L) / (n : ℝ) := h_split ▸ h_fano'
  linarith
```

BC `bc_rate_le_of_fano` (`BroadcastChannel.lean:431-452`) と **verbatim identical**
(BC では `25 行`、MAC では `25 行`、コメントの 1-2 行を除き完全同一)。
両 kernel が file-scoped `private theorem` ゆえ visibility は本 plan の Phase 1-3
で問題化しない想定 (CLAUDE.md「Project Layout: `private` は file-scoped」)。

### 0.2 3 declaration verbatim 確認 (現状、Phase 2.1 後の状態)

**`mac_single_rate_bound₁`** (`MultipleAccessChannel.lean:422-458`):

```lean
/-- **Single-user rate bound for sender 1 (genuine Fano + per-letter
chain-rule derivation)**. ...

The per-user Fano body and conditional-MI chain rule are themselves
Mathlib-wall residuals (joint-typicality-multi wall — real Mathlib gaps),
discharged structurally through `MACSingleFanoBound` / `MACPerLetterChain₁`
of `MACL2Discharge.lean`; the present theorem accepts them as raw scalar
inequalities so this file remains structurally minimal.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_single_rate_bound₁
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_chain : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε := by
  sorry
```

**`mac_single_rate_bound₂`** (`MultipleAccessChannel.lean:460-482`): mirror、
indices swap (`R₂` / `Pe₂` / `I_marg₂` / `I₂` / `M₂`)。

**`mac_sum_rate_bound`** (`MultipleAccessChannel.lean:484-510`):

```lean
/-- **Sum-rate bound (genuine Fano + per-letter chain-rule derivation)**.

For any MAC block code `c` and rate pair `(R₁, R₂)`, the converse asserts

```
R₁ + R₂ ≤ I(X₁, X₂; Y) + ε   (with Iboth := I(X₁, X₂; Y))
```

after Fano applied to the *joint* message `(W₁, W₂)`: ...

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_sum_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe_joint I_joint Iboth ε : ℝ)
    (h_fano : (n : ℝ) * (R₁ + R₂)
        ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup : (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    R₁ + R₂ ≤ Iboth + ε := by
  sorry
```

3 declaration とも signature は genuine entropy-level 形、`load-bearing hypothesis`
(旧 `h_bound : R ≤ I` 循環) は既に削除済、`@residual(plan:mac-bc-sorry-migration-plan)`
タグ + body `by sorry` のみが残置状態。

### 0.3 downstream consumer 確認 (verbatim, Phase 0 直前 rg)

```bash
rg -n 'mac_single_rate_bound₁|mac_single_rate_bound₂|mac_sum_rate_bound' Common2026/
```

結果 (verbatim、上から):

- `Common2026/Shannon/MultipleAccessChannel.lean:37` (docstring 散文、自身)
- `Common2026/Shannon/MultipleAccessChannel.lean:105` (docstring 散文、自身)
- `Common2026/Shannon/MultipleAccessChannel.lean:450, 474, 501` (3 declaration 自身)
- `Common2026/Shannon/MultipleAccessChannel.lean:638` (`mac_capacity_region_outer_bound_three_bounds` docstring 散文「`_with_body` 経由で genuine」紹介、コード参照無し)
- `Common2026/Shannon/MACBodyDischarge.lean:45, 68, 575` (docstring 散文 3 件、`mac_sum_rate_bound` を「parent file exit」と紹介、コード参照無し)
- `Common2026/Shannon/MACL2Discharge.lean:10, 11, 47, 322, 331, 341, 345-354, 357, 359, 363-372` —
  - `:10, 11, 47, 322, 331, 341, 357, 359` は docstring 散文
  - **`:345-354` `mac_single_rate_bound₁_with_body`** が `:353` で `mac_single_rate_bound₁ hn c R₁ Pe₁ I_marg₁ I₁ ε h_fano.fano h_chain.chain h_cleanup` を呼出 — **実コード caller 1 件**
  - **`:363-372` `mac_single_rate_bound₂_with_body`** が `:371` で `mac_single_rate_bound₂` を同パターンで呼出 — **実コード caller 1 件**
- `Common2026/Shannon/MACFanoConverseBody.lean:62, 63, 261, 266, 277, 280` — `_with_fano` wrappers 系の docstring + 自身 (両 `_with_fano` は `_with_body` 経由で MAC 3 declaration を呼ぶ間接 caller、しかし MAC 3 declaration 自身を直接 import せず `_with_body` を経由するため、引数順序整合は `_with_body` の 1 段でのみ verify すれば良い)

**consumer chain scope** (実コード caller のみ):
- `mac_single_rate_bound₁` ← `MACL2Discharge.mac_single_rate_bound₁_with_body` (1 caller、引数順序 post-rewrite と同一)
- `mac_single_rate_bound₂` ← `MACL2Discharge.mac_single_rate_bound₂_with_body` (1 caller、同上)
- `mac_sum_rate_bound` ← **実コード caller 0 件** (docstring 言及のみ)

**signature 不変ゆえ caller 側 0 修正** (本 plan は body のみ置換、signature
keep)。`MACL2Discharge.lean` の 2 件 wrapper は引数順序が既に post-rewrite と
同一、再 verify は olean refresh のみで完了する想定。

### 0.4 規模見積もり

- 触る file: **1 file (`Common2026/Shannon/MultipleAccessChannel.lean`)**
- 触る declaration: **3 件 (`mac_single_rate_bound₁/₂` / `mac_sum_rate_bound`)**
- 追加行数予測: 各 declaration の body 1 行 (`by sorry`) → 2-3 行 (`term-mode kernel 呼出 with arg list`) × 3 件 = +3 〜 +6 行
- 削除行数予測: `@residual(plan:mac-bc-sorry-migration-plan)` タグ × 3 = -3 行 (1 line each)
- docstring 更新 (kernel 呼出経由 proof done 注記、MAC asymmetry 注記の更新): +3 〜 +6 行
- **net diff 規模**: +3 〜 +9 行 (essentially in-place body 置換、本当に小さい)
- **sorry 数**: 現 **3 sorry → 改変後 0 sorry** (genuine derivation で完結)
- shared sorry 補題化必要性: **不要** (本 file 内 `mac_rate_le_of_fano` 直接呼出)
- 中央予測 sorry 数: **0** (proof done 到達)

### 0.5 撤退ライン

- **L-MAC-PD-1 (想定外 consumer 出現)**: Phase 0.3 で実コード caller 0 〜 1 件
  (signature 不変ゆえ ripple 想定 0) を確認済だが、Phase 1 直前にもう一度
  `rg -n 'mac_single_rate_bound₁|mac_single_rate_bound₂|mac_sum_rate_bound'
  Common2026/` を回し、新規 caller が出現していないか再確認。signature 不変
  ゆえ実際に発火する確率は極めて低いが、念のため。発火時は本 plan を保留し、
  caller 側を別 session で追ってから再起動。

- **L-MAC-PD-2 (`mac_rate_le_of_fano` visibility 問題)**: `private theorem` は
  file-scoped (CLAUDE.md「Project Layout」) ゆえ同 file 内呼出は問題ない想定。
  もし Lean が `mac_rate_le_of_fano` を unknown identifier として弾いた場合
  (例: namespace 境界の解釈差)、`protected theorem` への visibility 変更を 1
  commit 追加 (BC plan L-SIGRW-2 と同様の救済)。Phase 1 着手時に LSP
  diagnostic で即判明、追加修正は数行で済む想定。BC plan で同じ問題は発火
  しなかった (BC kernel も `private`) ので、MAC 側でも発火しない想定。

- **L-MAC-PD-3 (kernel verbatim drift)**: 本 plan 進行中に MAC 側
  (`MultipleAccessChannel.lean:396-420`) で `mac_rate_le_of_fano` の signature
  が並行 commit で改変されると、本 plan の「kernel 直接呼出」前提が崩れる。
  Phase 1 着手前に `git log --oneline -- Common2026/Shannon/MultipleAccessChannel.lean
  | head -5` で直近変更を確認、drift があれば本 plan の term-mode 呼出引数を
  改めて kernel 直近版に合わせ直す (1 turn 追加)。

**proof-log**: yes (`docs/proof-logs/proof-log-mac-rate-bound-proof-done.md`)。
理由: (a) `mac_rate_le_of_fano` kernel 既存発見 (Task brief が「kernel 不在」と
予測していた点と乖離) の planner 記録、(b) BC peer との対称性 / 差分の構造観察
を後続 plan の参考に残す、(c) `mac_capacity_region_outer_bound` (`:575`、本 plan
scope 外、別 `@residual(plan:mac-bc-sorry-migration-plan)` 系) が同 kernel × 3 +
`mac_region_combine` で proof done 到達可能か否かを (Phase V 末尾で) 観察記録。

## Phase 1 — `mac_single_rate_bound₁` body 置換 (single sweep) 📋

### 1.1 新 body (verbatim、`mac_rate_le_of_fano` term-mode 呼出)

```lean
/-- (docstring は既存維持、本文末尾の "@residual" タグ削除 + "proof done via kernel" 注記追加) -/
theorem mac_single_rate_bound₁
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_chain : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε :=
  mac_rate_le_of_fano hn R₁ I_marg₁ I₁ Pe₁ (Real.log (M₁ : ℝ)) ε
    h_fano h_chain h_cleanup
```

### 1.2 旧 body との差分

| 項目 | 旧 (Phase 2.1 後) | 新 (本 plan) |
|---|---|---|
| body | `by sorry` | `mac_rate_le_of_fano hn R₁ I_marg₁ I₁ Pe₁ (Real.log (M₁ : ℝ)) ε h_fano h_chain h_cleanup` (term mode) |
| tags | `@residual(plan:mac-bc-sorry-migration-plan)` | (tag 削除、proof done 状態) |
| signature | (不変) | (不変) |
| docstring | "joint-typicality-multi wall ... discharged structurally" | "proof done via `mac_rate_le_of_fano` kernel; entropy-level inputs are precondition not core" 1 段更新 |

### 1.3 sub-step

- [ ] **1.1** Phase 0 撤退ライン L-MAC-PD-1 再確認 (`rg -n 'mac_single_rate_bound₁|mac_single_rate_bound₂|mac_sum_rate_bound' Common2026/` で新規 caller 出現無し確認)
- [ ] **1.2** L-MAC-PD-3 再確認 (`git log --oneline -- Common2026/Shannon/MultipleAccessChannel.lean | head -5`)
- [ ] **1.3** `Common2026/Shannon/MultipleAccessChannel.lean:422-458` 周辺 docstring + body の 1 件 `Edit`:
  - docstring の `@residual(plan:mac-bc-sorry-migration-plan)` を削除
  - docstring に「**Proof done via `mac_rate_le_of_fano` kernel** (`MultipleAccessChannel.lean:396`、same file private)」段落追加 (BC peer の `bc_common_rate_bound` `:478-494` の `@audit:ok` docstring を参考)
  - body: `by sorry` → 上記 1.1 の term-mode 呼出
- [ ] **1.4** `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` を実行、0 errors / 0 sorry warning 確認
- [ ] **1.5** L-MAC-PD-2 発動 (`mac_rate_le_of_fano` が `private` で resolve しなければ): `MultipleAccessChannel.lean:396` の `private theorem mac_rate_le_of_fano` を `protected theorem mac_rate_le_of_fano` に変更 + 再 verify。BC peer plan の L-SIGRW-2 と同型の処理。

**Phase 1 DoD**:
- `mac_single_rate_bound₁` 0 sorry / 0 `@residual` (proof done 直前、auditor 通過待ち)
- `lake env lean` 0 errors

**proof-log**: no (mechanical body 置換、観察事項なし)

## Phase 2 — `mac_single_rate_bound₂` body 置換 (single sweep、Phase 1 mirror) 📋

### 2.1 新 body (verbatim、indices swap)

```lean
theorem mac_single_rate_bound₂
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₂ Pe₂ I_marg₂ I₂ ε : ℝ)
    (h_fano : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_chain : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I₂ + ε :=
  mac_rate_le_of_fano hn R₂ I_marg₂ I₂ Pe₂ (Real.log (M₂ : ℝ)) ε
    h_fano h_chain h_cleanup
```

### 2.2 sub-step (Phase 1 mirror)

- [ ] **2.1** Phase 1 完了後の `lake env lean` 0 errors を前提に Phase 2 開始 (Phase 1 で kernel visibility 問題が解決していれば Phase 2 の同問題は再発しない)
- [ ] **2.2** `Common2026/Shannon/MultipleAccessChannel.lean:460-482` 周辺 docstring + body の 1 件 `Edit` (Phase 1.3 mirror、indices: `R₁ → R₂`, `I_marg₁ → I_marg₂`, `I₁ → I₂`, `Pe₁ → Pe₂`, `M₁ → M₂`)
- [ ] **2.3** `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` 再 verify

**Phase 2 DoD**:
- `mac_single_rate_bound₂` 0 sorry / 0 `@residual` (proof done 直前)
- `lake env lean` 0 errors

**proof-log**: no (Phase 1 完全 mirror)

## Phase 3 — `mac_sum_rate_bound` body 置換 (sum-rate adaptation = kernel 直接適用) 📋

### 3.1 新 body (verbatim、kernel 直接適用 — sum-rate 固有 adaptation 不要)

```lean
theorem mac_sum_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe_joint I_joint Iboth ε : ℝ)
    (h_fano : (n : ℝ) * (R₁ + R₂)
        ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup : (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    R₁ + R₂ ≤ Iboth + ε :=
  mac_rate_le_of_fano hn (R₁ + R₂) I_joint Iboth Pe_joint
    (Real.log ((M₁ : ℝ) * (M₂ : ℝ))) ε
    h_fano h_chain h_cleanup
```

### 3.2 kernel binding 解説 (verbatim 確認済、Phase 3 固有)

kernel `mac_rate_le_of_fano` の汎用 signature `(R I_marg I Pe L ε : ℝ)`:

| kernel 位置 | sum-rate での bind | 型 verbatim |
|---|---|---|
| `R` | `R₁ + R₂` | `ℝ` ✓ |
| `I_marg` | `I_joint` | `ℝ` ✓ |
| `I` | `Iboth` | `ℝ` ✓ |
| `Pe` | `Pe_joint` | `ℝ` ✓ |
| `L` | `Real.log ((M₁ : ℝ) * (M₂ : ℝ))` | `ℝ` ✓ |
| `ε` | `ε` | `ℝ` ✓ |

kernel の hypothesis 型:
- `h_fano : (n : ℝ) * R ≤ I_marg + 1 + Pe * L` → bind 後 `(n : ℝ) * (R₁ + R₂) ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))` ✓ (sum-rate `h_fano` と verbatim 一致)
- `h_chain : I_marg ≤ (n : ℝ) * I` → bind 後 `I_joint ≤ (n : ℝ) * Iboth` ✓
- `h_cleanup : (1 + Pe * L) / (n : ℝ) ≤ ε` → bind 後 `(1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε` ✓
- 結論 `R ≤ I + ε` → bind 後 `R₁ + R₂ ≤ Iboth + ε` ✓ (sum-rate 結論と verbatim 一致)

**型一致を verbatim で確認済 — sum-rate adaptation の難易度は "単純 (mechanical
binding)"**。BC peer plan に sum-rate が無いため本 plan 固有の確認だが、kernel の
汎用 scalar signature が `R := R₁ + R₂` をそのまま受け入れる構造ゆえ、二段適用
や `add_le_add` 結合などの adaptation は **一切不要**。

### 3.3 sub-step (Phase 1-2 と同型)

- [ ] **3.1** Phase 2 完了後の `lake env lean` 0 errors を前提に Phase 3 開始
- [ ] **3.2** `Common2026/Shannon/MultipleAccessChannel.lean:484-510` 周辺 docstring + body の 1 件 `Edit`:
  - docstring の `@residual(plan:mac-bc-sorry-migration-plan)` を削除
  - docstring に「**Proof done via `mac_rate_le_of_fano` kernel** (kernel の汎用 scalar signature が `R := R₁ + R₂` をそのまま受ける、二段適用不要)」段落追加
  - body: `by sorry` → 上記 3.1 の term-mode 呼出
- [ ] **3.3** `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` 再 verify

**Phase 3 DoD**:
- `mac_sum_rate_bound` 0 sorry / 0 `@residual` (proof done 直前)
- `lake env lean` 0 errors

**proof-log**: no (sum-rate kernel binding は §3.2 で planner verbatim 確認済、
実装中の判断ログ追記事項なし)

## Phase V — verify + olean refresh + 親 plan banner 更新 + honesty-auditor + handoff closure 📋

### V.1 全 file `lake env lean` 確認 + olean refresh

- [ ] **V.1.1** body 置換ゆえ public symbol 変更無し、ただし `MultipleAccessChannel.lean` の `.olean` は body 変更で再生成必要。`lake build Common2026.Shannon.MultipleAccessChannel` で olean refresh
- [ ] **V.1.2** dependent 再 verify (signature 不変ゆえ 0 ripple 想定):
  - `lake env lean Common2026/Shannon/MACL2Discharge.lean` — `_with_body` × 2 件が `mac_single_rate_bound₁/₂` を呼出、引数順序不変ゆえ通る想定
  - `lake env lean Common2026/Shannon/MACFanoConverseBody.lean` — `_with_fano` × 2 件 (間接 caller via `_with_body`) も通る想定
  - `lake env lean Common2026/Shannon/MACBodyDischarge.lean` — docstring 散文言及のみ、コード参照無し
  - `lake env lean Common2026/Shannon/BroadcastChannel.lean` — BC peer の docstring が MAC を MAC analogue として言及 (`bc_common_rate_bound` `:479` 等)、本 plan の MAC peer proof done 到達後に docstring 更新の opportunity あり (V.3.1 で扱う)

### V.2 集計コマンド (target file)

```bash
TARGET="Common2026/Shannon/MultipleAccessChannel.lean"
rg -nw 'sorry' $TARGET                                          # 期待: 元 4 件 (3 rate bound + `mac_capacity_region_outer_bound` 1 件 + `mac_capacity_region_outer_bound_three_bounds` 1 件) → 2 件減 (3 rate bound proof done) で 2 件 (`_outer_bound` 系 2 件は本 plan scope 外)
rg -n '@residual\(' $TARGET                                     # 期待: `_outer_bound` 系 2 件 (`mac_capacity_region_outer_bound` `:574`, `_three_bounds` `:644`) のみ、3 rate bound は 0 件
rg -n 'plan:mac-bc-sorry-migration-plan' $TARGET                # 期待: 2 件 (`_outer_bound` 系)、3 rate bound 由来は消失
```

### V.3 親 plan banner 更新

- [ ] **V.3.1** `docs/shannon/mac-moonshot-plan.md` 末尾の「proof done 集計」ブロック更新:
  > **2026-05-26 update**: `mac_single_rate_bound₁` / `mac_single_rate_bound₂` /
  > `mac_sum_rate_bound` (`MultipleAccessChannel.lean:450 / 474 / 501`) の body
  > 置換 (`docs/shannon/mac-rate-bound-proof-done-plan.md`) 完了 — 既存 file 内
  > `mac_rate_le_of_fano` (`MultipleAccessChannel.lean:396`, `private theorem`)
  > 経由 proof done に到達。`MACL2Discharge.lean` `_with_body` × 2 件は signature
  > 不変ゆえ 0 ripple。BC peer (`bc_common_rate_bound` / `bc_private_rate_bound`)
  > と合わせて T3-B / T3-C の rate-bound 系 5 declaration が全て proof done。

- [ ] **V.3.2** `docs/shannon/mac-bc-sorry-migration-plan.md` の Phase 2.1 section
  に「実施完了 (body 置換ルート、kernel 既存ゆえ proof done 到達)」note + 本
  plan path リンク追記

- [ ] **V.3.3** `Common2026/Shannon/BroadcastChannel.lean` BC docstring 更新の
  opportunity — `bc_common_rate_bound` `:479-483` / `bc_private_rate_bound`
  `:533-535` の docstring 「the BC version is **proof done** because the
  divide-by-`n` arithmetic kernel `bc_rate_le_of_fano` is in scope (the MAC
  analogue cannot do the same yet because `mac_rate_le_of_fano` is not
  present)」が **stale** (本 plan で kernel 既存判明)。BC docstring を「MAC
  analogue も同型 kernel `mac_rate_le_of_fano` 経由で proof done 到達 (本 plan
  実施後)」に更新。これは本 plan の incidental migration として扱う (BC 側 file
  への touch、scope expansion 1 file 内に収まる)。

### V.4 handoff Round 2 残課題 closure 反映

- [ ] **V.4** `.claude/handoff-sorry-migration.md` §D「Round 2 残課題 follow-up」
  の bullet「MAC peer 3 declaration (`mac_single_rate_bound₁/₂` / `mac_sum_rate_bound`)
  proof done 化」に completed marker + 本 plan path 追記

### V.5 honesty audit (orchestrator 必須)

本 plan は **`sorry` 削除を伴う body 置換 + `@residual` タグ削除** = CLAUDE.md
「Independent honesty audit」起動条件「実装 agent が新規に `sorry` + `@residual`
を含む commit を作った場合 (or 既存 declaration の honesty 関連 tag が変わる)」
直撃 (tag 削除 = 旧 residual classification の closure 主張、自己申告だけでは
honest かの独立検証なし)。**proof done 達成宣言の前に必ず honesty-auditor 起動**。

- [ ] **V.5.1** orchestrator は `honesty-auditor` を起動 (`subagent_type:
  "honesty-auditor"`)。対象:
  - `mac_single_rate_bound₁` (新 line) — body が `mac_rate_le_of_fano` 呼出のみ
    で完結している (load-bearing hypothesis bundling していない)、引数順序が
    kernel signature と整合、3 hypothesis (`h_fano` / `h_chain` / `h_cleanup`)
    が load-bearing precondition か regularity か (= load-bearing precondition、
    本 plan は entropy-level hypothesis を pass-through するゆえ honest)
  - `mac_single_rate_bound₂` 同上 (mirror)
  - `mac_sum_rate_bound` 同上 (sum-rate kernel binding が verbatim 一致しているか、
    `R := R₁ + R₂` の bind が type 上正しいか、二段適用や `add_le_add` の隠れた
    load-bearing なしか)
- [ ] **V.5.2** verdict:
  - `ok` → 本 plan close、3 declaration に `@audit:ok` 付与 (tier 1、BC peer
    `bc_common_rate_bound` / `bc_private_rate_bound` の docstring 末尾形式と
    同型)
  - `questionable` → docstring refine
  - `defect` → 即修正 (sorry-based 状態に戻す等)
- [ ] **V.5.3** auditor 通過後、本 plan 全 Phase ☑ + status banner に
  「proof done achieved 2026-05-26 (MAC peer follow-up to BC Wave 6-7)」を記録

**Phase V DoD**:
- `MultipleAccessChannel.lean` `sorry` 件数が 3 件減 (旧総数 N → N-3、目視で本 plan 範囲の `:458, :482, :510` の 3 件が 0 に)
- 親 plan banner (mac-moonshot-plan) 更新済
- BC docstring incidental update (`bc_common_rate_bound` / `bc_private_rate_bound`)
- handoff §D bullet completed
- honesty-auditor pass (verdict `ok`)

**proof-log**: yes — Phase V 末尾に「BC peer plan と同型 kernel 経由 proof done
到達」+「`mac_rate_le_of_fano` kernel が既存だった発見 (Task brief stale 予測の
記録)」+「`mac_capacity_region_outer_bound` (`:575`、本 plan scope 外、`@residual`
継続) が同 kernel × 3 + `mac_region_combine` で proof done 到達可能か否かの観察
(後続 plan の参考)」を 1 段落で記録

## 撤退ライン (Phase 横断、再掲)

- **L-MAC-PD-1**: 想定外 consumer 出現 → Phase 0 で確認、Phase 1 直前にも再確認、出現したら本 plan 保留 + consumer 側別 session
- **L-MAC-PD-2**: `mac_rate_le_of_fano` visibility 問題 → `private` → `protected` 変更 (1 行 fix)
- **L-MAC-PD-3**: kernel signature drift → Phase 1 直前 git log 確認、drift があれば 1 turn 追加で kernel 直近版に term-mode 呼出を合わせ直す

**撤退ライン 0 本発動** が前提シナリオ。BC peer plan で同型撤退ラインが 0 発火
だった (Wave 6-7 verbatim 確認済) ため、本 plan でも 0 発火想定。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **`mac_rate_le_of_fano` visibility relaxation の事前必要性** (auditor 判定対象 + Phase 1.5 で実測):
   - `private theorem` (file-scoped) は同 file 内で自由に呼出可能なはず。BC peer
     plan の Phase 1.5 で `bc_rate_le_of_fano` が `private` のままで `bc_common_rate_bound`
     / `bc_private_rate_bound` の term-mode body から呼出可能だった verbatim 実績
     あり (Wave 6-7 commit `8e0e7e7` 系列で proof done 達成)。MAC でも同様、事前
     `protected` 化は不要。Phase 1.5 で LSP diagnostic 出たら発動の condition。

2. **docstring 内の MAC asymmetry 言及の旧文 update 範囲** (auditor 判定対象):
   - BC peer の `bc_common_rate_bound` `:479-483` の docstring は MAC asymmetry
     を「MAC analogue cannot do the same yet because `mac_rate_le_of_fano` is
     not present」と書いており、本 plan 完了後は **stale**。V.3.3 で incidental
     update を本 plan に組み込むか、別 follow-up plan に切り出すかは auditor 判定
     対象。planner 推奨: V.3.3 で本 plan に組み込む (BC file への touch 1 declaration
     × 2 件 × docstring 1 段落 = ~10 行で scope expansion 軽微)。

3. **`mac_capacity_region_outer_bound` (`:575`) と `mac_capacity_region_outer_bound_three_bounds`
   (`:645`) の proof done 化** (本 plan scope 外、Phase V proof-log で観察記録):
   - 両 declaration は `@residual(plan:mac-bc-sorry-migration-plan)` 継続。
     `_outer_bound` の body は「entropy-level inputs × 9 件 → `mac_rate_le_of_fano`
     × 3 + `mac_region_combine`」で proof done 到達可能性が高い (本 plan の 3
     declaration の延長線、kernel reuse)。`_three_bounds` の body は
     `mac_region_combine h₁ h₂ hs` の 1 行で proof done 到達可能 (kernel 呼出すら
     不要、`mac_region_combine` (`:517-520`) は既に publish 済の通常 lemma)。
     **両者とも本 plan の延長で proof done 到達可能、別 plan 推奨**。本 plan の
     Phase V proof-log で観察記録、後続 plan slug は仮称
     `mac-outer-bound-proof-done-plan` (まだ起草未着手)。

4. **proof done 到達後の `@audit:ok` 付与タイミング** (auditor 委任):
   - BC peer plan と同様、Phase V.5.3 で honesty-auditor `ok` verdict 直後に
     付与する想定 (本 plan は前者を採用)。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **plan 起草時 (2026-05-26、本 plan 作成 turn)**:
   - 当初 brief「MAC 側は同型の `mac_rate_le_of_fano` が **不在**」を受領した
     時点で、planner の前例確認 (BC peer plan + `MultipleAccessChannel.lean`
     verbatim 読込) によって **`mac_rate_le_of_fano` は既に `MultipleAccessChannel.lean:396-420`
     に publish 済**と判明。Task brief の予測が stale (BC peer 起草時の状況を
     根拠にしていた可能性)。
   - これに伴い、本 plan の Phase 構成を当初想定の「Phase 1 kernel 追加 + Phase
     2-4 declaration rewrite」から **「Phase 1-3 body 置換のみ + Phase V verify」**
     に縮減。新規 kernel 追加 Phase 不要。
   - 3 declaration の signature は **既に Phase 2.1 (mac-bc-sorry-migration-plan)
     で genuine entropy-level 形に rewrite 済** であることも verbatim 確認
     (`:450, 474, 501`)。本 plan は signature 改変ではなく純粋な body 置換、BC
     peer plan より更に scope 縮小。
   - sum-rate (`mac_sum_rate_bound`) の kernel 直接適用可否は Task brief が
     「kernel 再利用可否で予想規模変動」「sum-rate 形が per-letter chain shape
     異なる」と warning していたが、kernel の汎用 scalar signature `(R I_marg
     I Pe L ε : ℝ)` に `R := R₁ + R₂` をそのまま bind 可能なため adaptation
     不要 (§3.2 で verbatim 確認)。撤退ライン L-MAC-3 (sum-rate adaptation
     困難) は **発火しない**。
   - consumer chain は MAC file 内 + `MACL2Discharge.lean` 2 件 wrapper のみ、
     signature 不変ゆえ 0 ripple (§0.3 verbatim 確認)。撤退ライン L-MAC-2
     (consumer chain で sum_rate と single_rate が intricate に絡む) も
     **発火しない**。
   - 中央予測 sorry 数: **0** (proof done 到達)。BC peer plan と同型の確信度。
   - MAC outer-bound 系 2 declaration (`:575` `mac_capacity_region_outer_bound` /
     `:645` `mac_capacity_region_outer_bound_three_bounds`) は **本 plan scope
     外** だが、両者とも本 plan の kernel + 既存 `mac_region_combine` で proof
     done 到達可能性が高い (§未決事項 3)。後続 plan として記録。
