# EPI 方針 Y 半連続性壁 — 独立再評価 (KL-LSC 経由の回避可能性)

> 起点: `docs/shannon/epi-uncond-truncation-lsc-inventory.md` (S5 verdict: 壁 2 本 genuine、L-Uncond-3-scope 推奨)。
> 親: `docs/shannon/epi-unconditional-moonshot-plan.md` §スコープ判断 (方針 Y 確定、撤退 L-Uncond-3-scope)。
> 核心仮説 (検証対象): 「KL は弱収束下 LSC (Posner 1975) → entropy power LSC を導けないか」。
> 本ファイルは read-only 再評価。コード編集なし。

## §0 一行 verdict

**壁は genuine。klFun-Fatou + Mathlib KL-LSC では回避不能。** 理由は 2 段:
(1) **Mathlib に KL の弱収束下 LSC は存在しない** (loogle Found 0、KullbackLeibler/ 配下に LSC/liminf/Donsker-Varadhan ゼロ)。核心仮説の Mathlib 足場が無い。
(2) **in-tree の klFun-Fatou (W1) は弱収束ではなく density a.e. 収束を入力に取り、bridge 経由で entropy の USC (`limsup h ≤ h`) しか出さない**。方針 Y の LHS が要るのは entropy power の **LSC** (`h(X+Y) ≤ liminf h_t`) で、klFun-Fatou が出す向きと **逆**。しかも両向きとも有限分散 (`hpX_mom`) + 有限エントロピー (`hpX_ent`) を構造的に要求し、方針 Y が剥がしたい regularity がそのまま残る。
**→ L-Uncond-3-scope (方針 X 縮退) 発動を支持。** 核心仮説 (KL-LSC) は方向を逆に取り違えており、仮に Mathlib に KL-LSC があっても方針 Y の LHS には効かない。

## §1 EPIG2KLFatouLSC 補題インベントリ (verbatim、向き付き)

`InformationTheory/Shannon/EPIG2KLFatouLSC.lean`。namespace `InformationTheory.EPIG2KLFatou`。

| 補題 | file:line | 結論形 (verbatim 抜粋) | 向き | 主要前提 |
|---|---|---|---|---|
| `rnDeriv_withDensity_quotient_ae` (W2) | :60 | `(withDensity (ofReal∘f)).rnDeriv (withDensity (ofReal∘g)) =ᵐ ofReal (f/g)` | 等式 | `hf_nn`/`hg_pos`/`hf_int`/`hg_int` (regularity) |
| **`klDiv_le_liminf_of_ae_tendsto` (W1)** | :112 | `klDiv μ γ ≤ liminf (fun n => klDiv (μ_n n) γ) atTop` | **KL-LSC (liminf≥)** | `[IsFiniteMeasure γ/μ/μ_n]`、`μ≪γ`、`μ_n≪γ`、**入力 `h_ae` = density の γ-a.e. 収束 `(μ_n).rnDeriv γ → μ.rnDeriv γ`** |
| `convDensity_tendsto_ae_subseq` (W4) | :169 | `∃ ns, StrictMono ∧ ∀ᵐ x, f_{ns} → pX` (a.e. 部分列) | a.e. 収束 | `hpX_int`/**`hpX_mom`** (L¹ 収束に 2 次 moment) |
| `log_gaussianPDFReal_zero` | :206 | `log(g x) = -log√(2πv) - x²/(2v)` | 等式 | `v ≠ 0` |
| `cross_term_closed_form` | :225 | cross = affine in t、係数に `M2(pX)` | 等式 | **`hpX_mom`** |
| `pX_cross_term_expand` | :263 | `∫pX·log g = c₀∫pX - (1/2σ²)M2` | 等式 | **`hpX_mom`** |
| `cross_term_tendsto` (W3) | :281 | `∫ f_n·log g → ∫ pX·log g` | 収束 | **`hpX_mom`** |
| **`negMulLog_convDensity_limsup_le` (α、entry_point)** | :360 | `limsup (∫ negMulLog f_n) atTop ≤ ∫ negMulLog pX` | **entropy USC (limsup≤)** | `hpX_int`/`hpX_mass`/**`hpX_mom`**/**`hpX_ent`**/`σ²≠0` |

### 1-A klFun-Fatou は「両向き」を出すか → **NO、片向き (USC) のみ**

W1 が出すのは **KL の LSC** `klDiv μ γ ≤ liminf klDiv(μ_n)`。bridge
`klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (`EPIG2BridgeDensityHelpers.lean:97`、`(klDiv P Q).toReal = -differentialEntropy P - ∫ cross`) で
`h = -klDiv.toReal - cross`。符号反転により **KL-LSC (liminf≥) → entropy USC (limsup≤)**。
α 補題の結論 `limsup h_n ≤ h(pX)` がまさにこれ。klFun-Fatou は KL の **片側 (下から)** しか出さない:
Fatou は `∫ liminf ≤ liminf ∫` (非負被積分 `klFun ≥ 0`) の **一方向のみ**有効で、上界 (limsup) は別機構 (β下界 `negMulLog_convDensity_entropy_ge_density` の per-n `h(pX) ≤ h_n`) が供給している。

### 1-B 「逆向き Fatou」は出るか → 原理的に NO

α (`limsup h_n ≤ h(pX)`) の "逆" は entropy **LSC** `h(pX) ≤ liminf h_n`、すなわち KL の **USC** `limsup klDiv(μ_n) ≤ klDiv μ`。
これを klFun-Fatou で出すには `limsup ∫ klFun ≤ ∫ limsup klFun` が要るが、これは **上から可積分支配 (dominated)** が必要で、Fatou の非負版 (`lintegral_liminf_le`) の符号反転では出ない。
in-tree で entropy の LSC 方向 (`h(pX) ≤ h_n`) を供給しているのは Fatou ではなく **β下界** `negMulLog_convDensity_entropy_ge_density` (:124、cond-diff-entropy 経由) で、これは **per-n の点ごと不等式** (極限の半連続性ではない)。
かつ β下界も **`hpX_mom` + `hpX_ent` を要求**。

## §2 Mathlib KL/entropy LSC 在庫 (loogle、Found 件数 verbatim)

| クエリ | Found | 一致 |
|---|---|---|
| `InformationTheory.klDiv` (存在確認) | **29 declarations** | (Basic に集約、LSC 系ゼロ) |
| `InformationTheory.klDiv, LowerSemicontinuous` | **Found 0** | — |
| `LowerSemicontinuous (fun _ => InformationTheory.klDiv _ _)` | **Found 0 / 0 match** | — |
| `InformationTheory.klDiv _ _ ≤ Filter.liminf _ _` | **Found 0 / 0 match** | — |
| `InformationTheory.klDiv, Filter.Tendsto` | **Found 0** | — |
| `InformationTheory.klDiv, Filter.liminf` | **Found 0** | — |
| `MeasureTheory.ProbabilityMeasure, LowerSemicontinuous` | **Found 0** | — |
| `LowerSemicontinuous (fun μ : Measure _ => _)` | Found 7 / **0 match** | (Measure×LSC は 7 件あるが pattern 不一致 = 汎関数 LSC 不在) |
| `LowerSemicontinuous, Real.negMulLog` | **Found 0** | — |
| `ProbabilityTheory.gaussianReal, Filter.Tendsto` | **Found 0** | — |
| `MeasureTheory.Measure.conv, Filter.Tendsto` | **Found 0** | — |
| `nhds, ProbabilityMeasure, Filter.Tendsto` | Found 37 / **0 match** (dirac 弱収束 pattern) | — |

ファイル走査: `Mathlib/InformationTheory/KullbackLeibler/` = `Basic.lean`/`ChainRule.lean`/`KLFun.lean` の 3 本のみ。
`rg 'LowerSemicontinuous|liminf'` = **none**。`rg 'Donsker|Varadhan|variational entropy'` (InformationTheory 全体) = **none**。
**→ Mathlib に KL の弱収束下 LSC / 変分表示 (Donsker-Varadhan) は authoritative に不在。** 核心仮説の Mathlib 足場ゼロ。

## §3 方針 Y が要る半連続性の向き (LHS/RHS 別精査)

方針 Y step 2-3 (親 plan §Phase Y、inventory §1-B):
- **LHS**: `entropyPower (X+Y) ≤ liminf_{t→0⁺} entropyPower((X+Y)+√t Z)` = entropy power の **LSC (liminf≥)**。
- **RHS**: `entropyPower(X+√t Z) → entropyPower(X)` = **収束** (両側半連続)。

向きの確定: `N = exp(2h)` は `h` の単調増加変換ゆえ向きは保存。LHS が要るのは `h(X+Y) ≤ liminf h_t` = **entropy LSC**。
**klFun-Fatou (W1+bridge) が出すのは entropy USC (`limsup h ≤ h`、α 補題) で、LHS の要求と逆。**
RHS の収束は α (USC) + β (per-n 下界) の squeeze で出る (in-tree `negMulLog_convDensity_limsup_le` 周辺で実際に `h_n → h(pX)` を組んでいる) が、**RHS 収束も `hpX_mom`+`hpX_ent` 込み**。
→ 方針 Y の LHS = entropy LSC は、in-tree 資産が出す向き (USC) と逆で、かつ Mathlib 足場 (KL-LSC) も不在。

## §4 klFun-Fatou を逆向きに使えるか (Fatou の符号解析)

- Fatou 非負版 `lintegral_liminf_le` (`Add.lean:231`): `∫ liminf F ≤ liminf ∫ F`。`klFun ≥ 0` を `ofReal` で持ち上げて W1 が使用。**KL の liminf 下界 (LSC) を出す**。
- 逆 (limsup 上界) を出すには可積分支配の `limsup ∫ ≤ ∫ limsup` が要り、Fatou 非負版の単純符号反転では **出ない** (支配関数が無い、`negMulLog` の負側が L¹ 支配されない一般入力で破綻)。
- `negMulLog` は `x∈(0,1)` で正、`x>1` で負と符号変化 ⇒ `klFun` (≥0、凸) と違い entropy 被積分は片側 Fatou に乗らない。in-tree が entropy の両端 (USC は Fatou、LSC は別ルート β) を **異なる機構**で出しているのはこのため。
- **結論: 同一 Fatou machinery の符号反転で双対 (entropy LSC) は出ない。** entropy LSC は cond-diff-entropy の per-n 下界 (β) でのみ供給され、これは極限の半連続性ではなく点ごと不等式かつ regularity 込み。方針 Y の `liminf` を含む LHS-LSC を出す道具は in-tree にも Mathlib にも無い。

## §5 VERDICT

### 壁は genuine か → **YES (genuine、回避不能)**

1. **Mathlib KL-LSC 不在 (§2、Found 0 × 全クエリ + dir 走査 none)**: 核心仮説「KL は弱収束 LSC (Posner)」は数学的に真でも **Mathlib に formalize されていない**。新規自作必須 = `wall:entropy-lsc-weak` genuine 確定。
2. **向きの取り違え (§1-A/§3/§4)**: 仮に KL-LSC があっても、KL-LSC は entropy **USC** に翻訳され、方針 Y の LHS が要るのは entropy **LSC**。**核心仮説は方針 Y の要求と逆向き。** klFun-Fatou の双対 (逆向き) は Fatou 符号で原理的に出ない。
3. **regularity の不可避性 (§1 全 hpX_mom/hpX_ent)**: in-tree の α (USC)・β (LSC 点ごと)・W3・W4 すべてが `hpX_mom` (有限分散) + `hpX_ent` (有限エントロピー) を要求。これは方針 Y が剥がしたい regularity そのもの。inventory §4 の「平滑が裾を消さない」と整合 — 平滑列 density `f_n` の `hpX_mom` は生 pX の `hpX_mom` から来ており、heavy-tail では供給されない。
4. **弱収束 vs a.e. 収束の gap (§1 W1 入力)**: W1 は density の a.e. 収束を入力に取る。弱収束 (法則収束) から density a.e. 収束は**出ない** (より強い)。方針 Y が weak conv で攻めるなら W1 は直接使えず、`wall:gaussian-approx-identity-weak` (Found 0) も追加で genuine。

### 回避可能なら必要補題 → **回避不能。** 欠けている向きの明示:

**原理的に欠けているのは entropy power の LSC `h(pX) ≤ liminf h_t` (= KL の USC `limsup klDiv(μ_n) ≤ klDiv μ`)。**
- これは Fatou の非負版 (in-tree W1 が使う唯一の Fatou) の符号と逆で、可積分支配版 Fatou が要る。
- in-tree が entropy LSC 方向で持つのは β の **per-n 点ごと下界** (`h(pX) ≤ h_n`) のみで、これは「極限の半連続性」ではない。per-n 下界から liminf-LSC は trivially 出る (`h(pX) ≤ h_n ⟹ h(pX) ≤ liminf h_n`) が、**β自身が `hpX_mom`+`hpX_ent` 込み** ゆえ regularity は剥がれない。
- すなわち entropy LSC は技術的には β経由で in-tree に「ある」が、**有限分散+有限エントロピー前提付き** = 方針 X の射程。無前提版 entropy LSC (heavy-tail 込み) は Mathlib にも in-tree にも無く、proof route は moonshot 規模 (inventory §5 #1、200-400 行 + Mathlib 壁)。

### 推奨

**L-Uncond-3-scope (方針 X 縮退) 発動を支持。** case 1 を有限分散+有限微分エントロピーの honest regularity precondition 付きで締める。
- 退化トラップ除去 (特異 → entropyPower 0、case 2/3) は方針 X でも追加前提なしで保たれる (親 plan 発見 1+2)。
- 失うのは「有限分散でない a.c. 入力」の救済のみ。
- honest 撤退口: `sorry` + `@residual(wall:entropy-lsc-weak)` を S5 弱収束 LSC 補題に残し、最終定理は方針 X signature で genuine 着地。`hX_var`/`hX_ent` は **regularity precondition** (CLAUDE.md 判定軸: 前提条件、load-bearing でない)。

### 核心仮説への直接回答

「KL は弱収束 LSC だから entropy power LSC を導けないか」: (a) Mathlib に KL-LSC が無い (Found 0)。(b) **より本質的に、KL-LSC は entropy USC に翻訳され、方針 Y の LHS が要る entropy LSC とは逆向き。** entropy LSC に対応するのは KL の **USC** で、これは古典的に成立しない (KL は弱収束で下半連続だが上半連続ではない — Posner の結果は LSC のみ)。**核心仮説は方向を取り違えており、数学的に方針 Y の LHS を救えない。**
