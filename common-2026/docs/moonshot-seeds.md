# Moonshot シードカード集

> **Status (2026-05-12)**: 5 シード本体 + A 節 deferred 全件 + C 節 横断改善 全件完了 + **B-6 最大エントロピー完了 + B-5 Pinsker 弱形 完了 + B-2 / B-9 Shearer cover bundle 完了 + B-7 MI chain rule 完了 + B-3 Channel coding Phase A + B-(a,b) 部分完了 + B-1 Sanov A 形完了**。Loomis–Whitney → Slepian–Wolf → AEP (Phase A〜F unified) → Stein (achievability + converse 半分 + liminf/limsup sandwich) → Polymatroid (structure 化込) → MaxEntropy → Pinsker (弱形 `TV ≤ √KL`) → Brascamp–Lieb (組合せ形) + Hypercube product projection bound → MI chain rule (n 変数 + i.i.d. corollary) → Channel coding (DMC / Code / errorProb 定義 + jointly typical set 定義 + AEP joint 形 size/prob bound) → Sanov A 形 (type class probability upper bound `Q^n(T(P)) ≤ exp(-n·D(P‖Q))`) を **すべて 0 sorry** で通過。完了済みカードは本ファイルから撤去し、各 plan ファイル (`docs/<family>/*-plan.md`) に履歴を残置。残る伸び代は B 節既存シード (Sanov **LDP B 形** / Channel coding **(B)-(c)以降** / Strong Stein) と **B 節追加シード (Shannon code、2026-05-11 起草)**。シャープ Pinsker `TV ≤ √(KL/2)` (定数 1/√2) は **B-5' (将来) Mathlib 上流 PR** に切り出し済。Hypercube edge-boundary 形 (Han-Bregman 流) は **B-2' deferred** に切り出し (Mathlib に `SimpleGraph.edgeBoundary` の Boolean cube 形が無く本 bundle スコープ外)。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

---

## 次のシード候補

### B. 新シード入口 (5 シード完了で開いた)

- **Sanov の定理** ✅ (A 形完了 2026-05-12) → [docs/shannon/sanov-moonshot-plan.md](shannon/sanov-moonshot-plan.md) — `typeClass_Qn_le` / `typeClass_Qn_le_klDiv`: 有限アルファベット上で `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)` (Cover-Thomas 11.1.4)。`klDivSumForm` 形と `(klDiv P Q).toReal` 形両方を publish。`Common2026/Shannon/Sanov.lean` (319 行)。Stein converse `steinTypicalSet_Q_prob_le` の特化 (片側 inequality → 両側 equality) で多項係数 / `|T(P)| ≤ exp(n·H(P))` を回避。**LDP B 形 (完全な `lim (1/n) log Q^n({empirical ∈ E}) = -inf D(P‖Q)`)** は **B-1' deferred** に切り出し: type 列挙 `𝒫_n` の多項係数評価 (`Nat.multinomial`) + `(n+1)^{|α|} = exp(o(n))` plumbing + `inf` の `Tendsto` が追加 ~600-1000 行必要。
- **B-2. Hypercube edge isoperimetry / Han-Bregman bound** ✅ (singleton-cover 形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `hypercube_product_projection_bound`: 任意 `A ⊆ α^n` (`A.Nonempty`) で `|A| ≤ ∏ i, |π_{{i}}(A)|`。Brascamp–Lieb の `S i := {i}` / `k := 1` 特殊形として Phase C corollary。edge-boundary 形 (Han-Bregman 流) は **B-2' deferred** に切り出し: Mathlib に Boolean cube graph 既存なく、`SimpleGraph.edgeBoundary` 形は独立 inventory が必要なため本 bundle スコープ外。
- **Channel coding theorem (achievability)** 🚧 (Phase A + Phase B-(a, b) 部分完了 2026-05-12) → [docs/shannon/channel-coding-achievability-plan.md](shannon/channel-coding-achievability-plan.md) — DMC = `Kernel α β` (alias) + `Code` structure + `errorProb` / `averageErrorProb` / `mutualInfoOfChannel` を Phase A で publish (`Common2026/Shannon/ChannelCoding.lean` 514 行)。Phase B-(a, b): `jointlyTypicalSet` 定義 + `jointlyTypicalSet_prob_tendsto_one` (joint AEP, union bound on 3 complements 経由) + `jointlyTypicalSet_card_le` (`Finset.card_image_of_injective` + 既存 `typicalSet_card_le`) 完了。**Phase B-(c) (independent pair `P((X̃, Y) ∈ A) ≤ exp(-n(I-3ε))`) 以降 deferred**: 新規 AEP point-wise probability upper bound `typicalSet_prob_le` + i.i.d. product measure factorization (現 AEP は `Pairwise IndepFun` のみで `iIndepFun` 経由の block measure 分解は未整備) を含む ~1000-1600 行追加が必要。Slepian-Wolf strong typicality / 他の joint AEP 形派生に **本 514 行は単独で再利用可能**。
- **Strong Stein** (`Tendsto → K` strict 形): 現行 Stein は `K ≤ liminf ≤ limsup ≤ K/(1-ε)` の sandwich 止まり。`1/(1-ε)` 補正を消すには strong converse (concrete bound に `1+o(1)` factor) が必要。新規 inventory: strong converse 経路 (information spectrum / Han-Verdú approach) の Mathlib delta 調査。見積 unknown (inventory 後判定)。**(2026-05-11 再評価、B-5 弱形完了後)**: B-5 弱形の `tvNorm_le_sqrt_klDiv` (Common2026.Shannon.Pinsker) で `TV` と `KL` の plumbing は揃った。strong converse の concrete bound は **B-5' (sharp Pinsker) 待ち**ではなく、弱形でも `(1+o(1))` factor は導出可能 (定数のみ √2 緩い)。information spectrum 経路を試す前に Pinsker+TV continuity 経路を試す価値あり。

### B 追加 (2026-05-11 起草、既存 5 シード + B-1〜B-4 を踏まえた後続)

- **B-5. Pinsker 不等式** ✅ (弱形) → [docs/shannon/pinsker-moonshot-plan.md](shannon/pinsker-moonshot-plan.md) — Bretagnolle-Huber 経路で `tvNorm P Q ≤ √(klDiv P Q).toReal` (定数 1、シャープ Pinsker の定数 1/√2 の √2 倍ゆるい)。有限 alphabet 上で `tvNorm` を新規定義 + `klFun_ge_sub_sqrt_sq` 点別補題 + Cauchy-Schwarz on `|p-q|=|√p-√q|·(√p+√q)`。310 行。シャープ版 `TV ≤ √(KL/2)` は **B-5' (Mathlib 上流 PR 候補)** に切り出し、`klFun(t) ≥ 3(t-1)^2/(2(t+2))` の calculus 形式化が鍵。
- **B-6. 最大エントロピー** ✅ → [docs/shannon/max-entropy-moonshot-plan.md](shannon/max-entropy-moonshot-plan.md) (有限アルファベット上の Gibbs 不等式): `entropy μ X ≤ Real.log (Fintype.card α)`、等号 iff `μ.map X` 一様。Mathlib `klDiv_eq_zero_iff` + identity `klDiv P (uniform) = log|α| - H(P)` だけで終わる軽量シード。LoomisWhitney の `entropy_le_log_image_card` (uniformOn-specific) の **一般 measure 版** で、Shannon converse・LoomisWhitney 両方で暗黙に効いている identity を独立補題として publish。Cover-Thomas 2.6.4。見積 2〜3 日 / 50〜100 行 / 低リスク。**最軽量シード**、Pinsker / Sanov の前段補題としても再利用可。
- **B-7. 相互情報量 chain rule** ✅ → [docs/shannon/mi-chain-rule-moonshot-plan.md](shannon/mi-chain-rule-moonshot-plan.md) — `mutualInfo_chain_rule_fin`: `I(X_0, …, X_{n-1}; Y) = ∑ I(X_i; Y | X_{<i})` の n 変数 chain rule + `mutualInfo_iid_eq_nsmul`: 独立同分布 (Xs, Ys) で `I(X^n; Y^n) = n · I(X_0; Y_0)` (B-3 用 corollary)。Phase A (`mutualInfo` の MeasurableEquiv reshape 不変性、`mutualInfo_map_left/right_measurableEquiv`) + Phase B (Han Phase B と対称な induction、既存 2 変数 `mutualInfo_chain_rule` + `MeasurableEquiv.piFinSuccAbove` + prodComm reshape + `Fin.sum_univ_castSucc`) + Phase C (chain rule 経由ではなく `klDiv_compProd_eq_add` + `measurePreserving_arrowProdEquivProdArrow` で直接 product joint 加法性 + 新規補題 `klDiv_pi_eq_sum`) で 418 行。`Common2026/Shannon/MIChainRule.lean` 新規。B-3 (Channel coding achievability) の前段補題として publish 済。
- **B-8. Shannon コード** (per-symbol prefix code 達成可能性): 語長 `l_i = ⌈-log_D P(i)⌉` の prefix code が `H_D(P) ≤ E[L] < H_D(P) + 1` を達成。Mathlib `kraft_mcmillan_inequality` (uniquely decodable → Σ D^{-l_i} ≤ 1、`Mathlib.InformationTheory.Coding.KraftMcMillan`) を入口に、**逆向き** (Kraft 充足 → prefix code 存在) + **Shannon code 構成 + 期待長下界/上界** の 3 段。block source coding theorem (既存 `source_coding_theorem`、AEP Phase F) の **per-symbol 相補形**。Cover-Thomas 5.4 / 5.5 / 5.8.1。見積 1〜1.5 週 / 250〜450 行 / 中リスク (prefix code 構成の Mathlib 側 API 探索 + 期待長計算 plumbing が plumbing-heavy、新規数学はほぼ無し)。
- **B-9. Brascamp–Lieb 不等式** ✅ (組合せ形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `brascamp_lieb_finset`: 任意の cover `(S_i)_{i ∈ ι} ⊆ 𝒫(Fin n)` が各 `j` を `k` 回覆うとき `|A|^k ≤ ∏ i, |π_{S_i}(A)|`。Shearer engine (`HanDShearer.shearer_inequality`) + `entropy_le_log_image_card` + `entropy_uniformOn_eq_log_card` の 3 つを **任意 cover** で並べるだけ。B-2 と engine 共有で bundle 実装、`Common2026/Shannon/BrascampLieb.lean` (198 行)。LW は `S i := univ.erase i` 特殊形だが既存 `LoomisWhitney.lean` 維持 (refactor 見送り)。

### 横断観察 (B 追加シード間)

- **Pinsker → Strong Stein のショートカット** ✅ (B-5 弱形完了で再評価済 2026-05-11): 弱形 Pinsker でも qualitative `(1+o(1))` bound は導出可能と判断。シャープ版 (B-5') 待ちは不要。B-4 の inventory は本観察と独立に進める。
- **B-2 + B-9 の bundle 化** ✅ (2026-05-11 完了): どちらも Shearer を「異なる cover ファミリ」で呼ぶだけ。実装結果: **`structure ShearerCover` 抽象化は不要だった** — `shearer_inequality` が既に任意 `ι`/`S`/`k` に対して汎用なため、新規定義 `projectionSubset S A` + reshape lemma 1 つ (`jointEntropySubset_le_log_projectionSubset_card`) だけで BL が書ける。LW は既存形を維持 (refactor 見送り、新規 `BrascampLieb.lean` と並立)。Hypercube は singleton cover corollary `hypercube_product_projection_bound` 形のみ提供、edge-boundary 形は **B-2' deferred** に切り出し。
- **B-7 → B-3 短縮化** ✅ (2026-05-12 B-7 完了で実証): 最大の seed B-3 (Channel coding achievability、4〜6 週) を一括着手するより、B-7 (MI chain rule) を独立 plan として先に完了 → B-3 を「jointly typical decoder + 既存 MI chain rule + i.i.d. corollary」の短縮形に再見積もる方が手戻りリスクが低い。実装: chain rule 経路 (Phase B) ≠ i.i.d. corollary 経路 (Phase C、`klDiv_pi_eq_sum` 直接) と判明、Phase C は chain rule に依存せず独立 publish した方が短い (B-3 では i.i.d. corollary 単独で十分)。

- **B-3 i.i.d. product factorization の欠落** 📋 (2026-05-12 B-3 Phase B-(a,b) 完了時): AEP は `Pairwise IndepFun` ベースで構築されているが、Phase B-(c) `jointlyTypicalSet_indep_prob_le` を立てるには point-wise probability `(μ.map (jointRV Xs n)) {x} = ∏ P(x_i)` が必要 → `iIndepFun` ベースの new lemma `typicalSet_prob_le` を AEP に追加する必要あり。AEP の Phase D で `entropy_jointRV_eq_n_smul` の証明に `iIndepFun` を使った block entropy chain rule は既に存在 (`AEP.lean:527`)、その plumbing を point-wise probability に延長することは技術的には可能。本シード Phase B-(c) 再開時に AEP 拡張も含めて plan に組み込む。

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 5 シード plan + deferred (2026-05-10 / 2026-05-11、全て完了):
  - [Loomis–Whitney moonshot](shannon/loomis-whitney-moonshot-plan.md) ✅
  - [Slepian–Wolf moonshot](shannon/slepian-wolf-moonshot-plan.md) ✅
  - [AEP moonshot](shannon/aep-moonshot-plan.md) ✅ (Phase A〜C)
  - [AEP source coding (Phase D)](shannon/aep-source-coding-plan.md) ✅
  - [AEP achievability (Phase E)](shannon/aep-achievability-plan.md) ✅
  - [Stein moonshot](shannon/stein-moonshot-plan.md) ✅ (Phase A〜B achievability)
  - [Stein converse (Phase A〜C)](shannon/stein-converse-plan.md) ✅
  - [Polymatroid moonshot](han/polymatroid-moonshot-plan.md) ✅ (Phase A〜C)
  - [Polymatroid structure (Phase D)](han/polymatroid-structure-plan.md) ✅
  - [HanD Pi refactor](han/hand-pi-refactor-plan.md) ✅
  - [Max Entropy moonshot (B-6)](shannon/max-entropy-moonshot-plan.md) ✅
  - [Pinsker moonshot (B-5)](shannon/pinsker-moonshot-plan.md) ✅ (弱形 `TV ≤ √KL`)
  - [Shearer cover bundle (B-2 + B-9)](shannon/shearer-cover-bundle-plan.md) ✅
  - [MI chain rule (B-7)](shannon/mi-chain-rule-moonshot-plan.md) ✅
  - [Channel coding achievability (B-3)](shannon/channel-coding-achievability-plan.md) 🚧 (Phase A + B-(a, b))
  - [Sanov moonshot (B-1)](shannon/sanov-moonshot-plan.md) ✅ (A 形 `Q^n(T(P)) ≤ exp(-n·D)`)
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)
