# MI chain rule ムーンショット計画 🌙 (B-7)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — 両 headline 完成済、0 sorry。
> 一般 chain rule `mutualInfo_chain_rule_fin` (`Common2026/Shannon/MIChainRule.lean:117`、
> 標準 `[StandardBorelSpace Y] [Nonempty Y]` + measurability 仮定のみ)、i.i.d. corollary
> `mutualInfo_iid_eq_nsmul` (MIChainRule.lean:392、`I(X^n;Y^n) = n • I(X_0;Y_0)`、
> i.i.d. 分布等式 (`μ.map = Measure.pi …` + copy 仮定) の honest 形)。pass-through なし。
>
> [moonshot-seeds.md](../moonshot-seeds.md) §B-7 の本体計画。前段 B-6 (MaxEntropy) / B-5 (Pinsker 弱形) / B-2+B-9 (Brascamp–Lieb + Hypercube) 完了後、B-3 (Channel coding achievability) の前段補題として独立着手 (2026-05-11)。

## 進捗

- [x] Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅ → [mi-chain-rule-inventory.md](mi-chain-rule-inventory.md)
- [x] Phase A — `mutualInfo` の MeasurableEquiv 不変性 (joint reshape 用 plumbing) ✅
- [x] Phase B — n 変数 chain rule `mutualInfo_chain_rule_fin` の induction ✅
- [x] Phase C — i.i.d. corollary `mutualInfo_iid_eq_nsmul`: 独立 `(X_i, Y_i)` 同分布で `I(X^n; Y^n) = n · I(X_0; Y_0)` ✅
- [x] Phase D — `Common2026.lean` 配線 + 検証 ✅

## ゴール / Approach

**ゴール**: B-3 (Channel coding achievability) が要する 2 つの定理を独立補題として publish:

1. **一般 chain rule**: `Xs : Fin n → Ω → α`, `Y` 任意 measurable に対し
   `I((X_0, …, X_{n-1}); Y) = ∑ i, I(X_i; Y | (X_0, …, X_{i-1}))`。
2. **i.i.d. corollary** (B-3 で実際に使う形): 各 `(X_i, Y_i) : Ω → α × β` が i.i.d. (`μ.map (X_i, Y_i) = ν` 共通かつ joint が product 測度) のとき
   `I(X^n; Y^n) = n · I(X_0; Y_0)`。

**Approach**:

- **Phase A**: `mutualInfo` の **左引数 MeasurableEquiv 不変性** `mutualInfo_map_left_measurableEquiv` を確立する。既存 `klDiv_map_measurableEquiv` (`MutualInfo.lean:52`) を `e × id` で持ち上げる薄い lemma 1 本。これで `α × (Fin n → α)` ↔ `Fin (n+1) → α` の reshape を chain rule 上で素直に処理できる。
- **Phase B** (一般 chain rule): Han Phase B の `jointEntropy_chain_rule` と **完全対称な induction**:
  - `n = 0`: LHS = `mutualInfo μ (constant) Yo = 0` (`mutualInfo_eq_zero_iff_indep` で trivially 独立)、RHS 空和。
  - `n+1`: `Xs : Fin (n+1) → Ω → α` を prefix `f : Ω → Fin n → α` と last `g : Ω → α` に分解 → Phase A reshape で LHS を `mutualInfo μ (fun ω => (f ω, g ω)) Yo` に変換 → 既存 `mutualInfo_chain_rule` (2 変数版、CondMutualInfo.lean:219) を 1 段適用 → IH を prefix に → `Fin.sum_univ_castSucc` で和に整形。
  - **重要観察**: 既存 `mutualInfo_chain_rule` は `Zc` 側の measurability + `StandardBorelSpace X, Y` を要求 (X = Xs, Y = Yo)。n 変数化で `Zc = prefix : Fin i.val → α` となるが `Fin i.val → α` は `Fintype` + `MeasurableSpace.pi` で `MeasurableSingletonClass` 自動発火 (Han Phase 0 で確認済)。`StandardBorelSpace` 要件は α 側 (`Xs i`) と Y 側にのみ課す。
- **Phase C** (i.i.d. corollary): chain rule 経由ではなく **`klDiv_compProd_eq_add` + `klDiv_prod_const_left` 直接** で帰納 (より短い):
  - i.i.d. 仮定: `μ.map (fun ω j => (Xs j ω, Ys j ω)) = Measure.pi (fun _ => μ.map (Xs 0, Ys 0))`、両 marginal も同様の product。
  - `klDiv (Π ν) (Π (μ.prod μ)) = n · klDiv ν (μ.prod μ)` を `klDiv_compProd_eq_add` から induction で得る。
  - 既存 `klDiv_prod_const_left` (`MutualInfo.lean:80`) で kernel const から KL の prod 加法性を引き出す。
  - **代替**: B-3 着手時に「Pi-valued joint の標準形」が必要と判明したら、chain rule 経由の証明に切り替え。本シードでは i.i.d. corollary のみ提供し、対称な再演習で `iid_chain_collapse` (prefix への独立性が condMutualInfo の prefix を落とす) を別補題化する道も残す。

**Pi reshape の方針**: Han Phase B/D で確立した `entropy_measurableEquiv_comp` + `MeasurableEquiv.piFinSuccAbove` パターンを `mutualInfo` 側で再演奏。`Pi.lean` の `subsetSplitMEquivAux` は本シードでは不要 (subset でなく prefix のみ扱う)。新規 reshape lemma は 0 を目標、既存 `MeasurableEquiv.piFinSuccAbove` + `klDiv_map_measurableEquiv` の組み合わせのみで通す。

**スコープ警戒**: 既存 `mutualInfo_chain_rule` の 2 変数形が `[StandardBorelSpace X] [Nonempty X]` を Xs 側に要求 → n 変数化で 各 step の `Xs i` (= α) 側に SBS を課す必要あり。`α` 有限 alphabet (Fintype + MeasurableSingletonClass + DecidableEq) で SBS は **自動 derive 可能か?** → Phase 0 で確認。NG なら明示的に `[StandardBorelSpace α]` を仮定に追加。

## Phase 0 - Mathlib + 既存 Common2026 インベントリ ✅

成果: [mi-chain-rule-inventory.md](mi-chain-rule-inventory.md)

主な確認事項:

- [x] Mathlib に `mutualInfo`/`condMutualInfo` の chain rule なし (Common2026 自作必須)。
- [x] 既存 `mutualInfo_chain_rule` (`CondMutualInfo.lean:219`) の完全シグネチャ verbatim 記録。
- [x] `klDiv_compProd_eq_add` (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`) で 2 重 compProd の plumbing は確立。
- [x] `Fintype α` + `MeasurableSingletonClass α` で `StandardBorelSpace α` の自動 derive 可否確認。
- [x] `Common2026.Shannon.Han.jointEntropy_chain_rule` のシグネチャ (n 変数 induction の参考形)。

## Phase A - mutualInfo の MeasurableEquiv 不変性 (左引数 reshape) ✅

スコープ:

```lean
/-- Mutual information is invariant under a MeasurableEquiv reshape of the
left random variable. -/
lemma mutualInfo_map_left_measurableEquiv
    {X' : Type*} [MeasurableSpace X']
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    (e : X ≃ᵐ X') :
    mutualInfo μ (fun ω => e (Xs ω)) Yo = mutualInfo μ Xs Yo
```

- [x] 戦略: `e × id : X × Y ≃ᵐ X' × Y` を構成。joint pushforward を `Measure.map_map` で書き換え、marginal pushforward を `Measure.map_map` で書き換え、`klDiv_map_measurableEquiv` で結ぶ。
- [x] 補題形は対称形 `mutualInfo_map_right_measurableEquiv` も同時提供 (B-3 で `Y` 側 reshape も使う見込み)。

## Phase B - n 変数 chain rule (一般形) ✅

スコープ:

```lean
/-- n-variable chain rule for mutual information:
`I(X_0, …, X_{n-1}; Y) = ∑ i, I(X_i; Y | (X_0, …, X_{i-1}))`. -/
theorem mutualInfo_chain_rule_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Yo : Ω → Y) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω i => Xs i ω) Yo
      = ∑ i : Fin n,
          condMutualInfo μ (Xs i) Yo
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
```

- [x] base case `n = 0`: `μ.map (fun ω _ => Xs · ω)` は singleton `Fin 0 → α` 上の dirac、`mutualInfo = 0` (joint = 周辺積の trivial 形)。Han Phase B の `n=0` と対称。
- [x] step case `n+1`: 上述 Approach 通り。`MeasurableEquiv.piFinSuccAbove` + Phase A reshape + 既存 2 変数 `mutualInfo_chain_rule` + IH + `Fin.sum_univ_castSucc`。

## Phase C - i.i.d. corollary (B-3 用) ✅

スコープ:

```lean
/-- i.i.d. corollary: if `(X_i, Y_i)` are i.i.d. (joint distribution = product of
copies of a fixed `ν`), then `I(X^n; Y^n) = n · I(X_0; Y_0)`. -/
theorem mutualInfo_iid_eq_nsmul
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    -- i.i.d. 仮定 (joint over n indices = product of i-th marginal):
    (h_joint_prod : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                      = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
    (h_marginal_X_prod : μ.map (fun ω i => Xs i ω) = Measure.pi (fun i => μ.map (Xs i)))
    (h_marginal_Y_prod : μ.map (fun ω i => Ys i ω) = Measure.pi (fun i => μ.map (Ys i)))
    -- 同分布: 全 i で marginal が i=0 と一致
    (h_iid_X : ∀ i, μ.map (Xs i) = μ.map (Xs 0))
    (h_iid_Y : ∀ i, μ.map (Ys i) = μ.map (Ys 0))
    (h_iid_joint : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                          = μ.map (fun ω => (Xs 0 ω, Ys 0 ω))) :
    mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω)
      = n • mutualInfo μ (Xs 0) (Ys 0)
```

- [x] 戦略: chain rule 経由ではなく、**product 測度の KL の加法性 (induction on `Fin n` via `pi_succ`) + i.i.d. で各項が等しい** で直接導出。`MeasurableEquiv.piFinSuccAbove` で `Fin (n+1) → γ ≃ᵐ γ × (Fin n → γ)` を使い、`klDiv_prod_const_left` (`MutualInfo.lean:80`) と `klDiv_compProd_eq_add` を組み合わせる。
- [x] **代替アプローチ** (chain rule 経由): chain rule で n 個の condMI に分解 → i.i.d. 仮定下で各 condMI を unconditional MI に reduce → ∑ = n · I。但し condMI = MI の reduction が独立性条件下で別補題を要求するため、**直接 product 経路を採用**。
- [x] **シグネチャ簡略化の検討**: `h_joint_prod` だけから両 marginal の product 性は自動導出可能 (`Measure.map_pi_comp_pi` 系)。実装着手時に試行、可能なら仮定を 1 本に圧縮。

## Phase D - 配線 + 検証 ✅

- [x] `Common2026/Shannon/MIChainRule.lean` 新規 file 作成。
- [x] `Common2026.lean` に `import Common2026.Shannon.MIChainRule` 追記。
- [x] `lake env lean Common2026/Shannon/MIChainRule.lean` silent 通過確認。
- [x] `Common2026/Shannon/CondMutualInfo.lean` は無改変 (新規 file で完結)。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-11 着手前**: i.i.d. corollary を chain rule 経由 vs product KL 直接の 2 経路で検討。後者の方が短い (chain rule 経由は condMI = MI の reduction 補題を別途要求し、独立性条件の plumbing が二度手間) と判断、Phase C は **直接経路 (product KL 加法性 + i.i.d. = 同項の和) を採用**。chain rule (Phase B) は B-3 がブロック型 jointly typical decoder で `I(X^n; Y^n | M)` のような条件付きを必要とする可能性を残すため独立に publish。

2. **2026-05-11 Phase 0 後**: i.i.d. corollary のシグネチャを変更。当初 `h_joint_prod` / `h_marginal_X_prod` / `h_marginal_Y_prod` の 3 つを別仮定としていたが、**i.i.d. を `IndepFun (Xs i) (joint Xs Ys j) μ` 系で記述する Mathlib 標準形が無く plumbing 過剰**になると判明。**「直接 `Measure.pi` を仮定として受ける」形 (上記 spec) で進める** — B-3 で使う側 (典型: tensor product channel) は分布の product 性を自前で証明する形が標準なので、本シードでは「product 性は前提として受け取る」設計で十分。

3. **2026-05-11 実装後 (Phase C 簡略化)**: i.i.d. corollary を「same-source の n コピー」形に再設計。当初 `(Xs i, Ys i)` の同分布を 3 つの仮定 `h_iid_X/Y/joint` で個別に受けていたが、**実際には全 i で同一の `X : Ω → α`, `Y : Ω → β` をコピーするだけで十分** (B-3 でも tensor product channel の i.i.d. 構成はこの形が標準)。最終 spec は `Xs i := fun ω => X (e i ω)`-相当の同分布コピーで `μ.map (fun ω => (Xs i ω, Ys i ω)) = μ.map (X, Y)` のみを要求、150 行台で完了。
