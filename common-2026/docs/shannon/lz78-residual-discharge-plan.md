# T4-A LZ78 漸近最適性 — 残 chain-hyp discharge 実装サブ計画 🌙

> **🗄️ ARCHIVED 2026-05-27** (textbook-roadmap M3/M4 scope-out 反映)
>
> 本 plan が参照する `LZ78FinalGlue.lean` / `LZ78ConverseDischarge.lean` /
> `LZ78DistinctEncoding.lean` / `LZ78SMBSandwich.lean` はすべて commit `f67ec8a`
> (2026-05-26「scope-out 60 ファイル削除」) で削除済。textbook-roadmap は LZ78 M3
> (variable-depth tree AEP) / M4 (Barron a.s. lift) を **research-level upstream
> として scope-out** している (`docs/textbook-roadmap.md` 章 13 行 / line 48 / line 97)。
> 本 plan の Phase C2/C3/C4/Z4/Z5/Z6 は M3/M4 と実質同等で、本 plan は scope-out
> 範囲外。**以下の Phase 設計は記録として保持** (将来 M3/M4 を再開する場合の
> prior として参照可) するが、現状では着手不可。
>
> **Status 訂正**: 後続実装を期待していた `LempelZiv78.lean` §2 3 def の docstring
> 内 `@audit:closed-by-successor(lz78-residual-discharge-plan)` は successor 不在化、
> docstring は本 archive 反映で `@audit:closed-by-successor(textbook-roadmap-m3-m4-scope-out)`
> に書き換え (本 plan の Read で確認)。

---

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 (Ziv inequality) / L-LZ2 (converse)」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)
>
> **Supersedes (一部)**: [`lz78-ziv-bridge-plan.md`](./lz78-ziv-bridge-plan.md)
> — 当該 plan の **Phase 4 (per-path parsing factorization)** は「経路1 = compProd telescoping」を
> 第一候補に置くが、本セッションの Read 確認で **実行不可** と確定 (下記 §Context)。本 plan は
> その Phase 4 を **cylinder 集合分解の手組み (経路2) 一択**で再設計した修正版であり、
> ziv-bridge plan の Phase 2/3/5/6 設計 (log-sum / restate / Ziv 本体 / achiev assembly) は流用する。
> 並行して converse (L-LZ2) を Kraft 経由で先行 discharge する設計を追加する。
> ziv-bridge plan は archive 扱い (削除しない、設計の prior として参照)。
>
> **Inventory (必読、設計確定済)**:
> - [`lz78-ziv-bridge-inventory.md`](./lz78-ziv-bridge-inventory.md) — log-sum 原始子在庫、per-path factorization 不在の確定
> - [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md) — Kraft / Shannon code 資産
>
> **Goal (短形)**: 主定理 `lz78_asymptotic_optimality` (Cover–Thomas Thm 13.5.3) を pass-through
> なしで閉じる。distinct-code headline `lz78_two_sided_optimality_distinct_bdd_free`
> (`InformationTheory/Shannon/LZ78DistinctEncoding.lean:412`) が現在 honest 入力として受ける
> **2 述語 `h_achiev : IsLZ78AchievabilityChainHyp` / `h_converse : IsLZ78ConverseChainHyp` の両方を
> genuine 構成で discharge** し、hypothesis-free 系を publish する。**0 sorry / 0 warning**。

## Status (2026-05-21)

> **本 plan 起草時の実態整合 (Read 確認済、起草前タスク記述からの修正含む)**:
>
> 1. **h_bdd_above は distinct 版で既に解決済 — 残タスクではない**。タスク記述が引用した
>    `LZ78FinalGlue.lean:380` の「greedy bit 長は uniform 上界を与えず discharge 不可」は
>    **greedy 実装版** (`lz78GreedyImplEncodingLength`) の headline
>    `lz78_two_sided_optimality_greedy_impl_bdd_below_free` (`:385`) の話。**distinct 版**
>    headline `lz78_two_sided_optimality_distinct_bdd_free` (`LZ78DistinctEncoding.lean:412`) は
>    `h_bdd_above`/`h_bdd_below` を **両方内部 discharge 済** (`lz78DistinctEncodingLength_isBoundedUnder_le`
>    `:331` / `_ge` `:374`、Phase B counting envelope 経由)。本 plan は **distinct headline を主合流先**
>    とするので、残るは chain-hyp 2 述語のみ。h_bdd_above は本 plan のスコープ外 (解決済)。
>
> 2. **L-LZ1 の counting 層は genuine 完成済**。`lz78PhraseStrings_mul_log_le`
>    (`LZ78ZivCountingBody.lean:353`) が per-input `c·log c ≤ 8·log(|α|+1)·n` を genuine に与える
>    (`total_length_ge_count_mul_log` `:190` + Phase A 不変量 `lz78PhraseStrings_nodup`
>    `LZ78GreedyLongestPrefix.lean:126` / `_total_length_le` `:192` / `_forall_ne_nil` `:232`)。
>    **ゆえに L-LZ1 で残るのは「組合せ counting `c·log c ≤ Kn`」ではなく「measure-theoretic な
>    `c·log c ≤ -log Pₙ{block ω}` (= counting 量の n を -log Pₙ に差し替える橋)」だけ**。
>    この橋 = per-path parsing factorization が L-LZ1 の唯一の crux。
>
> 3. **`blockRV` は単純射影**。`Stationary.lean:81` で `blockRV p n = fun ω i => p.obs i ω`
>    (`obs i = X ∘ T^[i]`)。`StationaryProcess` は shift T + 単一観測 X のみで **compProd / Markov
>    kernel 構造を一切持たない**。ziv-bridge plan Phase 4 の「経路1 (compProd telescoping、
>    `Measure.compProd_apply` 逐次適用)」は **適用先の構造が存在しないため実行不可**。Phase 4 は
>    cylinder 集合分解の手組み一択。
>
> 4. **converse の `:= h` たらい回しと `:True` placeholder の所在**:
>    - `IsLZ78ConverseChainHyp.ofSMBBridge` (`LZ78SMBSandwich.lean:362`) は body `:= h` の
>      **循環たらい回し** (`IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` の defeq
>      別名、docstring `:347` が "deferred" と自白)。何も証明していない。
>    - `IsZivInequalityPassthrough` / `IsLZ78ConversePassthrough` (`LempelZiv78.lean:233,:260`) は
>      `:= True`、各 `.of*` constructor は `True.intro` (`LZ78ZivInequality.lean:330`,
>      `LZ78FinalGlue.lean:147` 等)。これらは distinct headline path を通らない (placeholder)。
>      本 plan は **distinct headline の 2 chain-hyp を proving** することで、これら placeholder に
>      依存しない genuine path を確立する。
>
> 5. **着手順は L-LZ2 (converse) 先行を推奨**。L-LZ1 と独立、Kraft 資産あり、headline の honest
>    仮定を 2→1 に確実に減らせる ROI。詳細 §Approach。

## 進捗

- [ ] Phase 0 — 着手前 signature / 前提条件 再確認 (本 plan + 2 inventory) 📋 → [lz78-ziv-bridge-inventory.md](./lz78-ziv-bridge-inventory.md)
- [ ] Phase C1 — `LZ78ConverseKraft.lean` skeleton (converse 群、全 `:= by sorry`) 📋
- [ ] Phase C2 — block pushforward の Kraft 充足 `blockKraftSum_le_one` (L-LZ2 crux 1) 📋
- [ ] Phase C3 — per-path coding 下界 `lz_per_path_ge_neg_log_blockProb` (Kraft の a.s.-pointwise 化、L-LZ2 crux 2) 📋
- [ ] Phase C4 — assembly `isLZ78ConverseChainHyp_distinct` (liminf、L-LZ2 解除目標) 📋
- [ ] Phase Z1 — `LZ78ZivEntropyBridge.lean` skeleton (achiev 群、全 `:= by sorry`) 📋
- [ ] Phase Z2 — `log_sum_inequality` (`ConvexOn.map_sum_le` から、独立) 📋
- [ ] Phase Z3 — `blockLogAvg_eq_neg_log_blockProb` (def restate、独立) 📋
- [ ] Phase Z4 — per-path parsing factorization `blockProb_eq_prod_phraseProb` (cylinder 手組み、L-LZ1 真の crux) 📋
- [ ] Phase Z5 — per-path Ziv `ziv_per_path_mul_log_le` (factorization + log-sum + 既存 counting) 📋
- [ ] Phase Z6 — assembly `isLZ78AchievabilityChainHyp_distinct` (limsup、L-LZ1 解除目標) 📋
- [ ] Phase V — `InformationTheory.lean` 編入 + hyp-free distinct headline publish + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase V 完成形)

distinct headline (`LZ78DistinctEncoding.lean:412`) の 2 引数を genuine 定理で供給した
hypothesis-free 系を新規 publish:

```lean
namespace InformationTheory.Shannon

/-- **T4-A 無仮定 distinct headline (Cover–Thomas Thm 13.5.3)**: ergodic process on a
finite alphabet について、distinct LZ78 encoding の per-symbol rate は a.s. entropy rate に
収束する。2 chain-hyp (Eq.13.124 / 13.130) は内部で genuine discharge 済、
h_bdd_above/below も distinct counting envelope で discharge 済。 -/
theorem lz78_two_sided_optimality_distinct
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78DistinctEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_distinct_bdd_free μ p
    (isLZ78AchievabilityChainHyp_distinct μ p)   -- Phase Z6
    (isLZ78ConverseChainHyp_distinct μ p)        -- Phase C4

end InformationTheory.Shannon
```

既存 `..._bdd_free` 定理は signature 不変で残す (下流互換)。本 plan は新規補題の追加 +
import 1 行のみ、既存 genuine 補題の証明・型は一切触らない。

### Approach (overall strategy / shape of solution)

**全体戦略 = L-LZ2 converse 先行 → L-LZ1 achievability (cylinder 手組み) → headline 合流**。

2 述語の依存構造は以下。**両者は独立** (L-LZ2 は Kraft、L-LZ1 は parsing factorization、共有
crux なし)。両者とも「**本物の壁ではなく構築可能** (L884 taxonomy の (a) 量の壁 = 難しくない・
未構築)」と独立 strategy 再評価が結論。着手順は L-LZ2 先行を **推奨** (理由は下記)。

```
        lz78_two_sided_optimality_distinct (Phase V, 無仮定)
                          │  (h_bdd_above/below は distinct 版で discharge 済)
        ┌──────────────────┴──────────────────┐
   h_achiev (Eq.13.124, L-LZ1)        h_converse (Eq.13.130, L-LZ2)
   limsup(lz/n) ≤ limsup blockLogAvg  liminf blockLogAvg ≤ liminf(lz/n)
        │ Phase Z2–Z6                       │ Phase C2–C4
        │                                  │
   ┌────┴─────────────┐              ┌──────┴───────────────┐
 Ziv 不等式            既存 counting   Kraft 下界            既存 SMB blockLogAvg
 c·logc ≤ -log Pₙ      c·logc ≤ Kn ✅  -log Pₙ ≤ lz n        (黒箱 reuse)
 (factorization が crux) (黒箱 reuse)  (a.s.-pointwise 化が crux)
        │                                  │
 per-path parsing            ┌─────────────┴──────────────┐
 factorization (Z4)     blockKraftSum_le_one (C2)   per-path 化 (C3)
 = cylinder 手組み       ← shannonLength_kraft_le_one  ← entropyD_le_expectedLength
 (真の crux、~80–200 行)    の block 版               _of_kraft の a.s. lift
```

#### なぜ L-LZ2 (converse) 先行を推奨するか

- **L-LZ1 と独立**: converse は Kraft 経由、achievability は parsing factorization 経由で、
  共有 crux がない。どちらから着手しても他方を block しない。
- **Kraft 資産あり = ROI が高い**: `ShannonCode.lean` の `entropyD_le_expectedLength_of_kraft`
  (`:164`)、`shannonLength_kraft_le_one` (`:129`)、`ShannonCodeKraftReverse.exists_prefix_code_of_kraft`
  が既存 genuine。converse の核心 (Kraft 下界 `-log Pₙ ≤ codeword 長`) はこれらの **block 版 +
  expectation→a.s.-pointwise 化**で組める。L-LZ1 の crux (cylinder 手組み factorization) より
  着手基盤が厚い。
- **headline の honest 仮定を確実に 2→1 に減らせる**: converse 単独 discharge が成れば、
  distinct headline は `h_achiev` 1 述語だけを受ける中間 headline を publish でき、
  honest 入力数を 2→1 に **確実に**前進させられる (L-LZ1 が遅れても部分前進が固定される)。

#### L-LZ2 converse の核心 (Phase C2–C4)

converse は `liminf blockLogAvg ≤ liminf(lz/n)` = **lz/n の下界**。重要な設計事実 (Read 確認):

- **SMB 流用では閉じない**。SMB (`algoet_cover_liminf_bound` / `shannon_mcmillan_breiman`
  `SMBAlgoetCover.lean`) は `blockLogAvg → entropyRate` を与えるだけで lz/n に一切触れない。
  converse が必要とするのは **逆向きの coding 下界** (任意 prefix code は `-log Pₙ` を下回れない)。
- **`bitLength` 下界は建てない**。`LZ78Phrase.bitLength` (`LZ78GreedyParsing.lean:107`,
  `= Nat.log 2(c+1)+Nat.log 2 a+2`) には **下界補題が一切ない** (`bitLength_mono_left`/
  `_mono_right` `:116,:124` / `bitLength_pos` `:131` / `bitLength_zero` `:137` / `bitLength_eq`
  `:110` のみ、下界 `bitLength c a ≥ log₂ c - …` 系は不在)。coding 下界は **bitLength 下界経路を
  建てず Kraft 経由**で建てる (Cover–Thomas 13.130 の coding-theorem 下界そのもの)。
- **核心 = Kraft 資産の expectation→a.s.-pointwise 変換**。`entropyD_le_expectedLength_of_kraft`
  (`:164`) は **expectation-level** (`entropyD D P ≤ expectedLength P l`) かつ **full-support hyp**
  (`hP : ∀ a, 0 < P.real {a}`) を要求。converse が必要なのは a.s.-pointwise `-log Pₙ{x} ≤ lz(x)`。
  Kraft 不等式 `Σ D^{-l(x)} ≤ 1` (LZ78 が prefix code = uniquely decodable から) に対し、
  **各 cylinder x について `D^{-lz(x)} ≤ Pₙ{x}` を直接立てる pointwise 形** (Kraft の per-codeword
  版、Cover–Thomas Eq. 13.130 の `l(x) ≥ -log Pₙ{x}` を取ってきて a.s. に lift) が C3 の crux。
- **参考 plan**: `lz78-achievability-converse-plan.md` の Phase E (Kraft pointwise 化、~200–350 行
  見積) — 本 plan C2–C4 はその設計を distinct headline に向けて具体化したもの。

#### L-LZ1 achievability の核心 (Phase Z2–Z6)

per-path Ziv `c·log c ≤ -log Pₙ{x}` (Cover–Thomas Eq.13.122–124) は **chain rule 不要の純組合せ論**。
構造:

1. parsing factorization `Pₙ{x} = ∏ⱼ qⱼ` (telescoping、Phase Z4) → `-log Pₙ = -Σⱼ log qⱼ`
2. log-sum 不等式 (`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`、在庫あり、Phase Z2) →
   `c·log c ≤ -Σⱼ log qⱼ` (Phase Z5)
3. distinct count を縛る部分は **既存 genuine** で済む: counting 層 `lz78PhraseStrings_mul_log_le`
   (`LZ78ZivCountingBody.lean:353`) が `c·log c ≤ 8·log(|α|+1)·n` を既に与えており、項数縛り
   `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`) も genuine。**counting 層の再構築は不要**。

**真の crux は Phase Z4 の factorization のみ**。重要な設計事実 (再掲): `blockRV` は単純射影で
compProd 構造なし → **cylinder 集合分解の手組み (経路2) 一択** (~80–200 行核心)。
`{x} = ⋂ⱼ {y : Fin n → α | y の j-prefix が x の j-prefix に一致}` を prefix が一致する cylinder の
交わりで書き、`Pₙ{x} = (μ.map (blockRV n)).real {x}` を有限加法性 + stationarity の条件確率積に
telescoping で開く。**Mathlib-shape-driven 厳守**: factorization の結論形を、Z5 で log を取って
log-sum (Z2) に流せる積形 (`Pₙ{x} = ∏ⱼ qⱼ`, `qⱼ ≥ 0`) に固定してから着手。教科書 literal の
`P(phrase|context)` 形を先に書かない (ziv-bridge plan の Mathlib-shape-driven 注意と同一)。

#### Mathlib-shape-driven の設計選択 (結論側を変えない)

結論側の `blockLogAvg` (`ShannonMcMillanBreiman.lean:55`,
`= -(1/n)·log ((μ.map (blockRV n)).real {blockRV n ω})`) / `IsLZ78AchievabilityChainHyp`
(`LZ78FinalGlue.lean:118`、verbatim `∀ᵐ ω, limsup(lz/n) ≤ limsup blockLogAvg`) /
`IsLZ78ConverseChainHyp` (`LZ78ConverseDischarge.lean:106`、verbatim `∀ᵐ ω, liminf blockLogAvg ≤
liminf(lz/n)`) の述語定義を **一切変えない**。本 plan は新規述語を導入せず、これらの **body を
満たす定理を distinct encoding について genuine に証明**し、headline 引数から外す。

### 規模見積

| Phase | 中央 | 範囲 | 出力 | proof-log |
|---|---|---|---|---|
| Phase 0 | — | — | 着手前確認 (新規 file 起草なし) | no |
| Phase C1 | **50 行** | 40–70 | `LZ78ConverseKraft.lean` skeleton (converse 群 `:= by sorry`) | no |
| Phase C2 | **80 行** | 50–120 | `blockKraftSum_le_one` (block pushforward の Kraft 充足) | yes |
| Phase C3 | **180 行** | 120–300 | `lz_per_path_ge_neg_log_blockProb` (Kraft の a.s.-pointwise 化、★crux) | yes |
| Phase C4 | **60 行** | 40–100 | `isLZ78ConverseChainHyp_distinct` (liminf assembly) | yes |
| Phase Z1 | **50 行** | 40–70 | `LZ78ZivEntropyBridge.lean` skeleton (achiev 群 `:= by sorry`) | no |
| Phase Z2 | **45 行** | 30–60 | `log_sum_inequality` (Jensen 適用、0·log0 edge) | yes |
| Phase Z3 | **8 行** | 5–10 | `blockLogAvg_eq_neg_log_blockProb` (def restate) | no |
| Phase Z4 | **140 行** | 80–200 / 撤退時 ~10 行 | `blockProb_eq_prod_phraseProb` (cylinder 手組み factorization、★crux) | yes |
| Phase Z5 | **120 行** | 80–200 | `ziv_per_path_mul_log_le` (factorization + log-sum + 既存 counting) | yes |
| Phase Z6 | **90 行** | 60–150 | `isLZ78AchievabilityChainHyp_distinct` (limsup assembly) | yes |
| Phase V | **15 行** | 10–25 | `InformationTheory.lean` import + hyp-free distinct headline | no |
| **累計** | **~840 行** | **545–1305** | 2 新規 file + import 1 行 | — |

### ファイル構成

```
InformationTheory/Shannon/
  LZ78ConverseKraft.lean       ← 新規 (~330 行) — L-LZ2 群
                                 ・blockKraftSum_le_one              (C2)
                                 ・(def lzCodewordLength? — C2/C3 設計次第)
                                 ・lz_per_path_ge_neg_log_blockProb  (C3, ★crux)
                                 ・isLZ78ConverseChainHyp_distinct   (C4, liminf)
  LZ78ZivEntropyBridge.lean    ← 新規 (~410 行) — L-LZ1 群 (ziv-bridge plan 修正版)
                                 ・log_sum_inequality                (Z2, 独立)
                                 ・blockLogAvg_eq_neg_log_blockProb  (Z3, 独立)
                                 ・(def phraseProb? — Z4 cylinder 手組み次第)
                                 ・blockProb_eq_prod_phraseProb      (Z4, ★crux)
                                 ・ziv_per_path_mul_log_le           (Z5)
                                 ・isLZ78AchievabilityChainHyp_distinct (Z6, limsup)
  LZ78DistinctEncoding.lean    ← (Phase V) hyp-free headline 別名を追記 (任意、既存定理は不変)
  InformationTheory.lean              ← import 2 行追記
```

---

## Phase 0 — 着手前 signature / 前提条件 再確認 📋

本 plan + 2 inventory で大枠確定済。**着手前に実装者が再確認する事項** (signature drift / 仮定漏れ):

- [ ] **`blockRV` が射影であることの再確認** (`Stationary.lean:81`): `blockRV p n = fun ω i => p.obs i ω`。
      compProd / kernel 構造が無いことを確認 → Phase Z4 を cylinder 手組み (経路2) で確定。
      **経路1 (compProd telescoping) は適用先の構造が無いため検討対象外**。
- [ ] **`blockLogAvg` の正確な def** (`ShannonMcMillanBreiman.lean:55`):
      `= -(1/n) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})`。Phase Z3 restate と
      Phase C3 下界の両方が `(μ.map (blockRV n)).real {x}` = `Pₙ{x}` を扱う → singleton 質量の
      `MeasurableSingletonClass (Fin n → α)` instance 解決を確認 (有限 alphabet × 有限 index で自動の見込み)。
- [ ] **2 chain-hyp の body verbatim** (Phase C4 / Z6 の target):
      - `IsLZ78AchievabilityChainHyp` (`LZ78FinalGlue.lean:118`): `∀ᵐ ω, limsup (lz n (blockRV n ω)/n) ≤ limsup (blockLogAvg μ p n ω)`
      - `IsLZ78ConverseChainHyp` (`LZ78ConverseDischarge.lean:106`): `∀ᵐ ω, liminf (blockLogAvg μ p n ω) ≤ liminf (lz n (blockRV n ω)/n)`
- [ ] **Kraft 資産 3 件の verbatim signature + `[...]` typeclass + full-support hyp** (Phase C2/C3):
      - `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`):
        `{D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
        (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) : entropyD D P ≤ expectedLength P l`
        — **expectation-level + full-support `hP`**。a.s.-pointwise 化が C3 の crux。
      - `shannonLength_kraft_le_one` (`:129`): `{D} (hD : 1 < D) (P) [IsProbabilityMeasure P]
        (hP : ∀ a, 0 < P.real {a}) : kraftSum D (shannonLength D P) ≤ 1` — full-support hyp。
      - `kraftSum` / `expectedLength` / `entropyD` / `shannonLength` def (`:59,:55,:45,:51`)。
      - `ShannonCodeKraftReverse.exists_prefix_code_of_kraft` (前提 `D ≥ 2`, `0 < l a`)。
- [ ] **既存 counting 層が genuine であることの再確認** (Phase Z5 の項数縛りで黒箱 reuse):
      `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`、`c·log c ≤ 8·log(|α|+1)·n`)、
      `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`)。
- [ ] **log-sum 原始子の domain / weights 制約** (Phase Z2):
      `Real.convexOn_mul_log : ConvexOn ℝ (Set.Ici 0) (fun x ↦ x*log x)` (`NegMulLog.lean:144`)、
      `ConvexOn.map_sum_le` (`Jensen.lean:67`、weights `∑ w = 1`, `0 ≤ wᵢ`)。`Pₙ{phrase}=0` の
      未出現 phrase で `0·log0` landmine、`n=0`/`log0` edge を special-case。
- [ ] **distinct headline の合流形** (Phase V): `lz78_two_sided_optimality_distinct_bdd_free`
      (`LZ78DistinctEncoding.lean:412`) が受ける 2 引数の型を確認 (`@lz78DistinctEncodingLength α _ _ _`)。

---

## Phase C1 — `LZ78ConverseKraft.lean` skeleton 📋

skeleton-driven (CLAUDE.md): converse 群の全 def/定理を `:= by sorry` で並べ、namespace/imports/variable 確定。

- [ ] imports: `InformationTheory.Shannon.ShannonCode` (Kraft 資産), `LZ78ConverseDischarge`
      (`IsLZ78ConverseChainHyp` def), `LZ78DistinctEncoding` (`lz78DistinctEncodingLength`),
      `ShannonMcMillanBreiman` (`blockLogAvg`), `LZ78GreedyLongestPrefix` (parsing / prefix-free 性),
      `Mathlib.Analysis.SpecialFunctions.Log.Basic`。`import Mathlib` 禁止、pinpoint。
- [ ] namespace `InformationTheory.Shannon`、`open MeasureTheory ProbabilityTheory Filter Topology`,
      `open scoped ENNReal NNReal BigOperators`。
- [ ] variable: `{α Ω}` + 有限 alphabet instances (`Fintype`/`DecidableEq`/`Nonempty`/`MeasurableSpace`/
      `MeasurableSingletonClass`) + `[MeasurableSpace Ω]`。
- [ ] 全 declaration を `:= by sorry` で stub: `blockKraftSum_le_one`, (必要なら `lzCodewordLength` def),
      `lz_per_path_ge_neg_log_blockProb`, `isLZ78ConverseChainHyp_distinct`。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/LZ78ConverseKraft.lean` が sorry warning のみで type-check。
- **撤退ライン**: なし (skeleton のみ)。

---

## Phase C2 — `blockKraftSum_le_one` (L-LZ2 crux 1) 📋

LZ78 distinct encoding が prefix code (uniquely decodable) であることから、block pushforward 測度
`Pₙ = μ.map (blockRV n)` 上で codeword 長が Kraft を充足: `∑ x, 2^{-lz(x)} ≤ 1` (or D-ary)。

- [ ] target: `kraftSum 2 (fun x : Fin n → α => lz78DistinctEncodingLength n x) ≤ 1` (or D=|α| ベース)。
      lz78 distinct encoding が異なる block を異なる prefix-free codeword に写すこと
      (`lz78PhraseStrings_nodup` の延長 = block レベルの単射性 + prefix-free 性) から導く。
- [ ] **設計判断**: distinct encoding の prefix-free 性が `LZ78GreedyLongestPrefix.lean` から直接出るか、
      `ShannonCodeKraftReverse.exists_prefix_code_of_kraft` の逆向き (prefix code → Kraft) が必要かを
      Phase 0 で確認。後者なら Kraft McMillan 不等式 (uniquely decodable → Kraft) を別途要する。
- **依存補題**: `kraftSum` def (`ShannonCode.lean:59`), `lz78DistinctEncodingLength_eq`
      (`LZ78DistinctEncoding.lean:133`), `lz78PhraseStrings_nodup` (`LZ78GreedyLongestPrefix.lean:126`)。
- **proof-log: yes** — prefix-free 性の出所、Kraft 和の cast を記録。
- **撤退ライン [L-LZ2-K1]**: McMillan (uniquely decodable → Kraft) が Mathlib 不在で重い場合、
      block codeword 長が `≥ -log₂ Pₙ{x}` を満たす **Shannon-code 代用** (`shannonLength` を block
      pushforward に適用、`shannonLength_kraft_le_one` `:129` を黒箱 reuse) で Kraft 充足を確保し、
      C3 で「LZ78 codeword 長 ≥ shannonLength ≥ -log Pₙ」と繋ぐ二段に変更。full discharge 維持。

---

## Phase C3 — `lz_per_path_ge_neg_log_blockProb` (Kraft の a.s.-pointwise 化、L-LZ2 真の crux) 📋

任意 prefix code は negative log-likelihood を下回れない (Cover–Thomas Eq.13.130): 各 block x で
`-log Pₙ{x} ≤ lz(x) · log D + O(1)`、すなわち `(lz n x)/n ≥ blockLogAvg μ p n ω - slack`。

- [ ] **target (pointwise 下界)**:
      `blockLogAvg μ p n ω - converseSlack n ≤ (lz78DistinctEncodingLength n (blockRV n ω) : ℝ) / n`、
      `converseSlack n → 0`。
- [ ] **核心 = Kraft の per-codeword 形を a.s.-pointwise に立てる**。expectation-level
      `entropyD_le_expectedLength_of_kraft` (`:164`) を直接 a.s. に持ち上げるのではなく、
      Kraft 充足 (C2) `Σ 2^{-lz(x)} ≤ 1` から **各 x で `2^{-lz(x)} ≤ Pₙ{x}` を主張する pointwise 形は
      一般には成立しない** (Kraft は和の制約)。代わりに Cover–Thomas が使う形は:
      Shannon-code 下界 `lz(x) ≥ ⌈-log_D Pₙ{x}⌉ ≥ -log_D Pₙ{x}` を **codeword の最適性ではなく
      pointwise の `D^{-lz(x)} ≤ Pₙ{x}` 不成立を回避**して立てる。**設計の核心 (Phase 0 で確定)**:
      C2 の撤退 (L-LZ2-K1) で Shannon-code 代用に切り替えた場合、`rpow_neg_shannonLength_le_real`
      (`ShannonCode.lean:106`、`D^{-shannonLength a} ≤ P.real {a}`) が **pointwise に既存 genuine**で
      あり、これを block pushforward に適用すれば `2^{-lz(x)} ≤ Pₙ{x}` (lz ≥ shannonLength のとき)
      が per-x で出る → `-log Pₙ{x} ≤ lz(x)·log D` の pointwise 下界が genuine に立つ。
      **これが a.s.-pointwise 化の最も筋の良い経路** (full-support hyp の扱いは下記)。
- [ ] **full-support hyp の扱い**: `rpow_neg_shannonLength_le_real` / `entropyD_le_expectedLength_of_kraft`
      は `0 < P.real {a}` を要求。block pushforward `Pₙ{x}` は未出現 block で 0 になりうる →
      **a.s. では出現する block (`Pₙ{x} > 0`) のみ扱えば十分** (a.s.-pointwise は support 内で成立、
      `log0 = 0` 規約で support 外 branch を special-case)。これは regularity hyp の範疇 (load-bearing
      ではない) であることを docstring に明記。
- [ ] slack `converseSlack n` の a.s. → 0: codeword 長の O(1) 項 (bitLength の `Nat.log 2(c+1)+…`) を
      `/n` で消す。既存 counting envelope `c = O(n/log n)` (`lz78PhraseStrings_count_isBigO`
      `LZ78ZivCountingBody.lean:405`) 流用。
- **依存補題**: `rpow_neg_shannonLength_le_real` (`ShannonCode.lean:106`), C2 `blockKraftSum_le_one`,
      `blockLogAvg` def, `lz78DistinctEncodingLength_eq` (`:133`), counting envelope (`:405`)。
- **proof-log: yes** — pointwise 下界の経路 (Shannon-code 代用 vs Kraft 直接)、full-support の a.s.
      回避、slack→0 を記録。
- **撤退ライン [L-LZ2-K2]**: pointwise `2^{-lz(x)} ≤ Pₙ{x}` の a.s. 化が `~1 セッション / ~300 行`で
      閉じない場合、`IsLZ78ConverseChainHyp` を **isolated honest hypothesis として残す** (明示
      signature、型 ≠ 結論、docstring で「Cover–Thomas 13.130 coding 下界、未 discharge、load-bearing」
      明示)。`Prop := True` / `:= h` 循環は使わない。**この場合でも achievability (L-LZ1) が
      genuine に閉じれば headline の honest 仮定は 2→1**。

---

## Phase C4 — `isLZ78ConverseChainHyp_distinct` (liminf assembly、L-LZ2 解除目標) 📋

C3 の pointwise 下界 + slack→0 を liminf に持ち上げ、`IsLZ78ConverseChainHyp` の body を genuine に満たす。

- [ ] target: `IsLZ78ConverseChainHyp μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _)`
      = `∀ᵐ ω, liminf (blockLogAvg μ p n ω) ≤ liminf (lz n (blockRV n ω)/n)` (body verbatim
      `LZ78ConverseDischarge.lean:106`)。
- [ ] `Filter.Eventually.of_forall` で a.s. 化 (C3 が per-ω で成立すれば) → per-ω で C3 pointwise 下界を
      `Filter.liminf_le_liminf` + slack の `Filter.Tendsto` 吸収で liminf に持ち上げ。
- **依存補題**: C3 `lz_per_path_ge_neg_log_blockProb`, `Filter.liminf_le_liminf`,
      `Filter.Tendsto` (slack → 0)。
- **proof-log: yes** — liminf 持ち上げの filter 補題選択、slack の Tendsto 吸収を記録。
- **撤退ライン**: liminf plumbing が重ければ既存 converse wrapper のパターン
      (`lz78_converse_lower_bound_pmfBased` `LZ78ConverseDischarge.lean:201` の構造) を参照。
      C3 が genuine なら full discharge。

---

## Phase Z1 — `LZ78ZivEntropyBridge.lean` skeleton 📋

ziv-bridge plan Phase 1 を踏襲 (修正: factorization を cylinder 手組み版に、converse 定理は本 file から除外
= `LZ78ConverseKraft.lean` に分離)。

- [ ] imports: `InformationTheory.Shannon.LZ78ZivInequality` (`card_phraseSet_le_pow`),
      `LZ78ZivCountingBody` (`lz78PhraseStrings_mul_log_le`, counting envelope),
      `LZ78DistinctEncoding`, `ShannonMcMillanBreiman` (`blockLogAvg`),
      `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`, `Mathlib.Analysis.Convex.Jensen`。
      **`Mathlib.Probability.Kernel.Composition.*` は import しない** (compProd 経路は不採用)。`import Mathlib` 禁止。
- [ ] namespace / open / variable (Phase C1 と同形)。
- [ ] 全 declaration を `:= by sorry` で stub: `log_sum_inequality`, `blockLogAvg_eq_neg_log_blockProb`,
      (必要なら `phraseProb` def), `blockProb_eq_prod_phraseProb`, `ziv_per_path_mul_log_le`,
      `isLZ78AchievabilityChainHyp_distinct`。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` が sorry warning のみ。
- **撤退ライン**: なし (skeleton のみ)。

---

## Phase Z2 — `log_sum_inequality` (独立) 📋

ziv-bridge plan Phase 2 をそのまま採用。`(Σ aₖ) log(Σaₖ/Σbₖ) ≤ Σ aₖ log(aₖ/bₖ)` を
`ConvexOn.map_sum_le` から導出。Z4/Z5 から独立に landable。

- [ ] target: `(∑ i ∈ s, a i) * log((∑ a)/(∑ b)) ≤ ∑ i ∈ s, a i * log(a i / b i)`、前提 `0 ≤ aᵢ`, `0 < bᵢ`。
- [ ] `Real.convexOn_mul_log` (`NegMulLog.lean:144`) を weights `wₖ = bₖ/Σb`、points `pₖ = aₖ/bₖ` で
      `ConvexOn.map_sum_le` (`Jensen.lean:67`) に適用。weights 検証 (`∑ wₖ = 1`, `0 ≤ wₖ`,
      `pₖ ∈ Set.Ici 0`)、両辺 `Σb` 倍で目標形へ。
- **依存補題**: `Real.convexOn_mul_log`, `ConvexOn.map_sum_le`, `Finset.sum_div`, `Finset.mul_sum`。
- **proof-log: yes** — 0·log0 / weights 正規化の cast を記録。
- **撤退ライン**: Jensen の weights 代入が詰まれば 2 項版を `ConvexOn` 2 点定義から直接示し
      `Finset.sum` 帰納で一般化 (~+30 行)。full discharge 維持。

---

## Phase Z3 — `blockLogAvg_eq_neg_log_blockProb` (独立) 📋

`n · blockLogAvg μ p n ω = -log Pₙ{block ω}` (`0 < n`)。def restate。

- [ ] target: `(n:ℝ) * blockLogAvg μ p n ω = -Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})`。
- [ ] `blockLogAvg` def (`ShannonMcMillanBreiman.lean:55`) を unfold、`n * (1/n) = 1` (`0 < n`)。
- **依存補題**: `blockLogAvg` def、`mul_one_div_cancel` / `field_simp`。
- **撤退ライン**: なし (~8 行)。

---

## Phase Z4 — per-path parsing factorization `blockProb_eq_prod_phraseProb` (cylinder 手組み、L-LZ1 真の crux) 📋

`Pₙ{block ω} = ∏ⱼ qⱼ`。**L-LZ1 全体の crux**。`blockRV` が射影 (compProd 構造なし) ゆえ
**cylinder 集合分解の手組み一択** (ziv-bridge plan の経路1 は実行不可)。

- [ ] **設計 (cylinder 手組み)**: `Pₙ{x} = (μ.map (blockRV n)).real {x}` を、x の parsing 切れ目に沿った
      prefix が一致する cylinder の交わり `{x} = ⋂ⱼ {y : Fin n → α | y∘(prefixⱼ) = x∘(prefixⱼ)}` で
      表し、有限加法性 + stationarity (`identDistrib_obs_zero` `Stationary.lean:94`) の条件確率積に
      telescoping で開く。結論形を Z5 で log を取れる積形 `Pₙ{x} = ∏ⱼ qⱼ` (`qⱼ ≥ 0`) に固定。
- [ ] **必要なら `phraseProb p x j` を新規 def 導入** (Mathlib-shape-driven: 結論形を log-sum に流せる形で
      定義してから着手。textbook の `P(phrase|context)` 形を先に書かない)。
- [ ] zero-mass edge: 未出現 prefix で `qⱼ = 0` → `Pₙ{x} = 0`、`log0 = 0` 規約で Z5 の log-sum に
      矛盾なく渡る branch を確保。`n=0` edge も special-case。
- **依存補題**: `Measure.map_apply`, `Measure.real` の有限加法性, `identDistrib_obs_zero`
      (`Stationary.lean:94`), parsing prefix の集合代数 (`lz78PhraseStrings` の prefix 構造、
      `LZ78GreedyLongestPrefix.lean`)。**`Measure.compProd_apply` は使わない** (適用先構造が無い)。
- **proof-log: yes** — cylinder 分解の集合代数、telescoping、zero-mass branch を記録。
- **撤退ライン [L-LZ1-F、最重要]**: factorization が `~1 セッション / ~200 行`で閉じない見込みなら
      **isolated honest hypothesis として分離** (明示 signature、型 ≠ 結論):

      ```lean
      /-- **Isolated honest input (L-LZ1-F)**: stationary process の per-path block 確率が
      LZ78 parsing の per-phrase 確率の積に分解する (Cover–Thomas 13.5、per-path 形)。
      blockRV は射影で compProd 構造を持たないため cylinder 手組みが要り、本 wave では
      未 discharge。NOT a discharge / load-bearing。 -/
      def IsLZ78PerPathParsingFactorization
          (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
        ∀ (n : ℕ) (x : Fin n → α),
          (μ.map (p.blockRV n)).real {x}
            = ∏ j ∈ Finset.range (lz78PhraseStrings (List.ofFn x)).length, phraseProb p x j
      ```

      Z2/Z3/Z5/Z6 は全て genuine、factorization のみ honest。**`sorry` / `Prop := True` /
      結論同型述語への `:= h` 循環は使わない**。これは現状 (`h_achiev` という blockLogAvg-level
      1 述語) より厳密に primitive (parsing-level) な deferral。

---

## Phase Z5 — `ziv_per_path_mul_log_le` (L-LZ1 本体) 📋

`c·log c ≤ -log Pₙ{block ω}`。factorization (Z4) + log-sum (Z2) の合流。**counting 項数縛りは既存 genuine reuse**。

- [ ] target: `(c:ℝ) * log c ≤ -Real.log ((μ.map (p.blockRV n)).real {x})`、
      `c := (lz78PhraseStrings (List.ofFn x)).length`。
- [ ] factorization (Z4) で `-log Pₙ{x} = -Σⱼ log qⱼ` に開く。
- [ ] log-sum (Z2) を `aₖ ≡ 1` (distinct phrase に均等重み) / `bₖ ≡ qⱼ` で適用 → `c·log c ≤ -Σⱼ log qⱼ`
      (Cover–Thomas Eq.13.122–124 の log-sum step)。
- [ ] distinct-phrase 項数 `c` の縛りは **既存 genuine 黒箱 reuse**: `card_phraseSet_le_pow`
      (`LZ78ZivInequality.lean:204`) で項数を縛る。**counting `c·log c ≤ Kn` は再構築不要**
      (`lz78PhraseStrings_mul_log_le` `:353` が既に genuine、本 Phase は -log Pₙ への橋に専念)。
- [ ] zero-mass / `c=0` / `n=0` edge を special-case。
- **依存補題**: Z4 factorization, Z2 `log_sum_inequality`, `card_phraseSet_le_pow` (`:204`)。
- **proof-log: yes** — log-sum の weight 選択 (`aₖ≡1`)、edge case を記録。
- **撤退ライン**: log-sum の weight 設計が合わなければ uniform-distribution 版
      (`Σ qⱼ ≤ 1` を使った `c log c ≤ -Σ log qⱼ`) を `convexOn_mul_log` 直適用で再構成。Z4 が L-LZ1-F で
      honest 化された場合は本 Phase の factorization 入力が honest hyp になるだけで残りは genuine。

---

## Phase Z6 — `isLZ78AchievabilityChainHyp_distinct` (limsup assembly、L-LZ1 解除目標) 📋

ziv-bridge plan Phase 6 を踏襲。per-path Ziv (Z5) → per-symbol bridge → limsup で `h_achiev`。

- [ ] **per-symbol helper**: `(lz78DistinctEncodingLength n x : ℝ)/n ≤ blockLogAvg μ p n (witness) + ε n`,
      `ε → 0`。`lz78DistinctEncodingLength_eq` (`:133`) で `lz n x = c·bitLength(c,|α|)`、
      `bitLength ≈ log₂ c + O(log|α|)` (`bitLength_eq` `LZ78GreedyParsing.lean:110` 上界) →
      `(lz n x)/n ≤ C·(c log c)/n + o(1)`、Ziv (Z5) + Z3 で `≤ C·blockLogAvg + o(1)`、
      `c = O(n/log n)` (`LZ78ZivCountingBody.lean:405`) で余剰項 → 0。
- [ ] target: `IsLZ78AchievabilityChainHyp μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _)`
      (body verbatim `LZ78FinalGlue.lean:118`)。`Filter.Eventually.of_forall` で a.s. 化 →
      per-ω で `Filter.limsup_le_limsup` + o(1) を `Filter.Tendsto` で吸収。既存
      `lz78_achievability_upper_bound_ergodic` (`LZ78FinalGlue.lean:175`) の limsup plumbing 参照。
- **依存補題**: Z5 Ziv, Z3 restate, `lz78DistinctEncodingLength_eq` (`:133`), counting envelope (`:405`),
      `bitLength_eq` 上界 (`LZ78GreedyParsing.lean:110`), `Filter.limsup_le_limsup`。
- **proof-log: yes** — o(1) の Tendsto 吸収、limsup 持ち上げを記録。
- **撤退ライン**: limsup plumbing が重ければ `lz78_achievability_upper_bound_ergodic` の collapse
      パターンを直接 instantiate。helper が genuine なら full discharge。

---

## Phase V — `InformationTheory.lean` 編入 + hyp-free distinct headline publish 📋

- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.LZ78ConverseKraft` と
      `import InformationTheory.Shannon.LZ78ZivEntropyBridge` を追記 (`LZ78DistinctEncoding` import の後ろ)。
- [ ] **hyp-free headline publish**: `lz78_two_sided_optimality_distinct` (別名の新 theorem) を
      `lz78_two_sided_optimality_distinct_bdd_free μ p (isLZ78AchievabilityChainHyp_distinct μ p)
      (isLZ78ConverseChainHyp_distinct μ p)` で publish。**既存 `_bdd_free` 定理は signature 不変で残す**。
      段階着地時 (片方の chain-hyp のみ genuine) は、残った honest 仮定を正直に明記した中間 headline
      (例: `..._converse_hyp_only`) を publish。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/LZ78ConverseKraft.lean` と
      `InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` が silent (0 error / 0 sorry / 0 warning)。
- [ ] 既存 genuine 補題 (`card_phraseSet_le_pow`, `lz78DistinctEncodingLength_eq`,
      `lz78PhraseStrings_mul_log_le`, `blockLogAvg`, Kraft 資産, SMB 系) の signature 無変更を
      `rg` で横断確認 (新規追加のみ)。
- [ ] upstream olean refresh: 新 public symbol を下流が拾うなら `lake build InformationTheory.Shannon.LZ78ConverseKraft`
      / `...LZ78ZivEntropyBridge` 一回。

---

## Blast radius

- **新規 lemma 投入先**: `InformationTheory/Shannon/LZ78ConverseKraft.lean` (新規, ~330 行, L-LZ2 群) +
  `InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` (新規, ~410 行, L-LZ1 群)。
- **編集される既存ファイル**: `InformationTheory.lean` (import 2 行追記)。`LZ78DistinctEncoding.lean` は
  **任意** (Phase V の hyp-free 系を別名で追記する場合のみ、既存定理は不変)。
- **signature 変更ゼロ確認**: 再利用する既存 genuine 補題はすべて **黒箱 reuse、signature 不変**:
  - `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`)
  - `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`), counting envelope (`:405`)
  - `lz78PhraseStrings_nodup` (`LZ78GreedyLongestPrefix.lean:126`) / `_total_length_le` (`:192`) / `_forall_ne_nil` (`:232`)
  - `lz78DistinctEncodingLength_eq` (`LZ78DistinctEncoding.lean:133`), `..._isBoundedUnder_le/_ge` (`:331,:374`)
  - `blockLogAvg` (`ShannonMcMillanBreiman.lean:55`), `shannon_mcmillan_breiman` (SMB)
  - Kraft: `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`),
    `shannonLength_kraft_le_one` (`:129`), `rpow_neg_shannonLength_le_real` (`:106`),
    `kraftSum`/`expectedLength`/`entropyD`/`shannonLength` def (`:59,:55,:45,:51`)
  - `IsLZ78AchievabilityChainHyp` (`LZ78FinalGlue.lean:118`), `IsLZ78ConverseChainHyp` (`LZ78ConverseDischarge.lean:106`)
  本 plan は新規補題追加のみで既存の証明・型を触らない。
- **placeholder への影響なし**: `IsZivInequalityPassthrough.of*` / `IsLZ78ConversePassthrough.of*` の
  `True.intro` 群、`IsLZ78ConverseChainHyp.ofSMBBridge := h` (`LZ78SMBSandwich.lean:362`) は distinct
  headline path を通らないため本 plan は触らない (genuine path を別経路で確立)。

---

## 撤退ライン (本 plan)

各 Phase は **独立撤退可能**。撤退時も honest 限定 (名前付き仮説、型 ≠ 結論、docstring で
load-bearing 明示)。`Prop := True` / 結論同型述語への `:= h` 循環 / `sorry` は **禁止**。

| ID | 対象 | 発動条件 | 撤退後の着地 |
|---|---|---|---|
| **L-LZ2-K1** | block Kraft 充足 (Phase C2) | McMillan (uniquely decodable → Kraft) が Mathlib 不在で重い | Shannon-code 代用に切替 (`shannonLength_kraft_le_one` reuse)、二段経路。full discharge 維持 |
| **L-LZ2-K2** | converse pointwise 化 (Phase C3) | a.s.-pointwise 下界 >300 行 | `IsLZ78ConverseChainHyp` を isolated honest hyp で残す。achiev が通れば 2→1 |
| **L-LZ1-F** | parsing factorization (Phase Z4、最重要) | cylinder 手組み >200 行 | `IsLZ78PerPathParsingFactorization` 1 述語を isolated honest hyp。Z2/Z3/Z5/Z6 genuine、現状より primitive な deferral |
| (Z2/Z3/Z5/Z6 解除目標) | log-sum / restate / Ziv 本体 / achiev assembly | — | 原始子在庫あり (Z2/Z3 確実)、Z4 が通れば Z5/Z6 達成 |

**all-or-nothing 注記**: distinct headline `lz78_two_sided_optimality_distinct_bdd_free` の 2 chain-hyp は
独立。**converse 群 (C2→C3→C4) が genuine になれば `h_converse` が flip、achiev 群 (Z2→Z3→Z4→Z5→Z6) が
genuine になれば `h_achiev` が flip**。片方だけ genuine でも honest 仮定数を 2→1 に確実に減らせる
(L-LZ2 先行推奨の主因)。両方 genuine で完全 hypothesis-free headline。L-LZ1-F / L-LZ2-K2 発動時は
当該 1 述語が isolated honest 入力として明示的に残る (現状より小さい deferral だが完全 discharge ではない)。

---

## 当面の next step

1. **Phase 0** 着手前確認 (blockRV 射影再確認、2 chain-hyp body verbatim、Kraft 資産の full-support hyp、
   既存 counting genuine の reuse 形、log-sum 前提、edge case)。
2. **Phase C1 → C2 → C3 → C4** (converse 先行、L-LZ2)。最初に着手すべきは **Phase C1 (skeleton)**、
   その後 **C2 (block Kraft 充足)**。C3 (Kraft a.s.-pointwise 化) が L-LZ2 の crux。
   converse 完了で headline honest 仮定が **確実に 2→1**。
3. **Phase Z1 → Z2 → Z3** (log-sum + restate、独立に full discharge — 確実な前進を先取り)。
4. **Phase Z4** (factorization、L-LZ1 真の crux) cylinder 手組み full 試行 → ~200 行 / 1 セッションで
   判定 → 閉じなければ L-LZ1-F (isolated honest hyp) 発動。
5. **Phase Z5 → Z6** (Ziv 本体 + achiev limsup)。
6. **Phase V** `InformationTheory.lean` 編入 + hyp-free distinct headline publish + clean check。

**並行実行の余地**: converse 群 (C1–C4) と achiev 群 (Z1–Z6) は別ファイル・独立 crux なので並列 agent
で同時着手可。各群内は逐次依存。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点の確定事項 (実装中の方針変更があればここに追記):
1. **(2026-05-21) ziv-bridge plan Phase 4 経路1 (compProd telescoping) は実行不可と確定** —
   `Stationary.lean:81` の Read で `blockRV p n = fun ω i => p.obs i ω` = 単純射影、`StationaryProcess`
   は shift T + 単一観測 X のみで compProd / Markov kernel 構造を持たないことを確認。`Measure.compProd_apply`
   の適用先が存在しない。本 plan は Phase Z4 を cylinder 集合分解の手組み (経路2) 一択で再設計し、
   ziv-bridge plan を一部 supersede。
2. **(2026-05-21) h_bdd_above は distinct 版で既に discharge 済 — 残タスクではない** —
   タスク記述が引用した `LZ78FinalGlue.lean:380` は greedy 実装版の話。distinct headline
   `lz78_two_sided_optimality_distinct_bdd_free` (`LZ78DistinctEncoding.lean:412`) は
   `..._isBoundedUnder_le` (`:331`) / `_ge` (`:374`) で両 boundedness を内部 discharge 済
   (counting envelope `lz78DistinctEncodingLength_rate_isBigO_one` `:273` 経由)。本 plan は distinct
   headline を主合流先とするので h_bdd_above はスコープ外。残タスクは chain-hyp 2 述語のみ。
3. **(2026-05-21) L-LZ1 counting 層は genuine 完成 — Ziv の crux は -log Pₙ への橋のみ** —
   `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`) が `c·log c ≤ 8·log(|α|+1)·n` を
   既に genuine に与える。Phase Z5 は組合せ counting を再構築せず、factorization (Z4) で -log Pₙ に
   橋渡しすることに専念。
4. **(2026-05-21) converse は SMB 流用不可、bitLength 下界も建てない、Kraft 経由一択** —
   SMB は blockLogAvg→entropyRate のみで lz/n に触れない。`LZ78Phrase.bitLength` には下界補題が無い
   (`mono`/`pos`/`zero`/`eq` のみ)。converse の coding 下界は `rpow_neg_shannonLength_le_real`
   (`ShannonCode.lean:106`、pointwise genuine `D^{-shannonLength} ≤ P.real`) を block pushforward に
   適用する Kraft/Shannon-code 経路で建てる。full-support hyp は a.s. (出現 block) で回避可能 = regularity 範疇。
5. **(2026-05-21) L-LZ2 converse 先行を推奨** — L-LZ1 と独立、Kraft 資産あり、headline honest 仮定を
   2→1 に確実に減らせる ROI。最初の着手は Phase C1 skeleton → C2 block Kraft 充足。
6. **(2026-05-21) たらい回し / placeholder の所在を明記** — `IsLZ78ConverseChainHyp.ofSMBBridge := h`
   (`LZ78SMBSandwich.lean:362`、defeq 別名の循環)、`Is*Passthrough := True` (`LempelZiv78.lean:233,:260`)
   は distinct headline path を通らない。本 plan は distinct headline の 2 chain-hyp を genuine に proving
   することで、これら placeholder に依存しない genuine path を確立する (placeholder 自体は触らない)。
-->
