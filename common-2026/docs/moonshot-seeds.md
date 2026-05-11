# Moonshot シードカード集

> **Status (2026-05-11)**: 5 シード本体 + A 節 deferred 全件 + C 節 横断改善 全件完了 + **B-6 最大エントロピー完了 + B-5 Pinsker 弱形 完了**。Loomis–Whitney → Slepian–Wolf → AEP (Phase A〜F unified) → Stein (achievability + converse 半分 + liminf/limsup sandwich) → Polymatroid (structure 化込) → MaxEntropy → Pinsker (弱形 `TV ≤ √KL`) を **すべて 0 sorry** で通過。完了済みカードは本ファイルから撤去し、各 plan ファイル (`docs/<family>/*-plan.md`) に履歴を残置。残る伸び代は B 節既存シード (Sanov / Hypercube isoperimetry / Channel coding achievability / Strong Stein) と **B 節追加シード (MI chain rule / Shannon code / Brascamp-Lieb、2026-05-11 起草)**。シャープ Pinsker `TV ≤ √(KL/2)` (定数 1/√2) は **B-5' (将来) Mathlib 上流 PR** に切り出し済。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

---

## 次のシード候補

### B. 新シード入口 (5 シード完了で開いた)

- **Sanov の定理** (Stein の自然な拡張): `klDiv` の operational meaning を別形 (large deviation principle の rate function) で Lean 化。Stein で立った plumbing (log-likelihood ratio plumbing + Pi 化 chain rule) がそのまま再利用可。
- **Hypercube edge isoperimetry / Han-Bregman bound**: Loomis–Whitney 完了で Shearer の組合せ応用 1 本立った状態。同じ engine (Shearer) を別 cover で適用するシリーズの第 2 弾。見積 1 週間 / 200〜300 行 / 低リスク。
- **Channel coding theorem (achievability)**: Shannon converse は完了済。achievability 半分 (Cover-Thomas Ch 7 strong typicality + jointly typical decoder) は AEP plumbing 上に構築可能。見積 4〜6 週間 / 800〜1500 行 / 高リスク。
- **Strong Stein** (`Tendsto → K` strict 形): 現行 Stein は `K ≤ liminf ≤ limsup ≤ K/(1-ε)` の sandwich 止まり。`1/(1-ε)` 補正を消すには strong converse (concrete bound に `1+o(1)` factor) が必要。新規 inventory: strong converse 経路 (information spectrum / Han-Verdú approach) の Mathlib delta 調査。見積 unknown (inventory 後判定)。**(2026-05-11 再評価、B-5 弱形完了後)**: B-5 弱形の `tvNorm_le_sqrt_klDiv` (Common2026.Shannon.Pinsker) で `TV` と `KL` の plumbing は揃った。strong converse の concrete bound は **B-5' (sharp Pinsker) 待ち**ではなく、弱形でも `(1+o(1))` factor は導出可能 (定数のみ √2 緩い)。information spectrum 経路を試す前に Pinsker+TV continuity 経路を試す価値あり。

### B 追加 (2026-05-11 起草、既存 5 シード + B-1〜B-4 を踏まえた後続)

- **B-5. Pinsker 不等式** ✅ (弱形) → [docs/shannon/pinsker-moonshot-plan.md](shannon/pinsker-moonshot-plan.md) — Bretagnolle-Huber 経路で `tvNorm P Q ≤ √(klDiv P Q).toReal` (定数 1、シャープ Pinsker の定数 1/√2 の √2 倍ゆるい)。有限 alphabet 上で `tvNorm` を新規定義 + `klFun_ge_sub_sqrt_sq` 点別補題 + Cauchy-Schwarz on `|p-q|=|√p-√q|·(√p+√q)`。310 行。シャープ版 `TV ≤ √(KL/2)` は **B-5' (Mathlib 上流 PR 候補)** に切り出し、`klFun(t) ≥ 3(t-1)^2/(2(t+2))` の calculus 形式化が鍵。
- **B-6. 最大エントロピー** ✅ → [docs/shannon/max-entropy-moonshot-plan.md](shannon/max-entropy-moonshot-plan.md) (有限アルファベット上の Gibbs 不等式): `entropy μ X ≤ Real.log (Fintype.card α)`、等号 iff `μ.map X` 一様。Mathlib `klDiv_eq_zero_iff` + identity `klDiv P (uniform) = log|α| - H(P)` だけで終わる軽量シード。LoomisWhitney の `entropy_le_log_image_card` (uniformOn-specific) の **一般 measure 版** で、Shannon converse・LoomisWhitney 両方で暗黙に効いている identity を独立補題として publish。Cover-Thomas 2.6.4。見積 2〜3 日 / 50〜100 行 / 低リスク。**最軽量シード**、Pinsker / Sanov の前段補題としても再利用可。
- **B-7. 相互情報量 chain rule**: `I(X_1, …, X_n; Y) = ∑ I(X_i; Y | X_{<i})`。`CondMutualInfo.lean` (413 行、既存) + `Han.lean` の `jointEntropy_chain_rule` と完全に対称な induction。Channel coding theorem **achievability** (B-3) の前段補題で、jointly typical decoder の解析が `I(X^n; Y^n) = n · I(X; Y)` の reduction を要する。Cover-Thomas 2.5.2 / 7.7.1。見積 1 週 / 150〜300 行 / 中リスク (CondMutualInfo の n 変数化が `Pi.lean` reshape を要する、Han Phase B と同形)。**B-3 を一括着手するより、本シードを独立 1 週 plan として先に完了 → B-3' (短縮版) として再見積もり推奨**。
- **B-8. Shannon コード** (per-symbol prefix code 達成可能性): 語長 `l_i = ⌈-log_D P(i)⌉` の prefix code が `H_D(P) ≤ E[L] < H_D(P) + 1` を達成。Mathlib `kraft_mcmillan_inequality` (uniquely decodable → Σ D^{-l_i} ≤ 1、`Mathlib.InformationTheory.Coding.KraftMcMillan`) を入口に、**逆向き** (Kraft 充足 → prefix code 存在) + **Shannon code 構成 + 期待長下界/上界** の 3 段。block source coding theorem (既存 `source_coding_theorem`、AEP Phase F) の **per-symbol 相補形**。Cover-Thomas 5.4 / 5.5 / 5.8.1。見積 1〜1.5 週 / 250〜450 行 / 中リスク (prefix code 構成の Mathlib 側 API 探索 + 期待長計算 plumbing が plumbing-heavy、新規数学はほぼ無し)。
- **B-9. Brascamp–Lieb 不等式** (組合せ形): 任意の cover `(S_i)_{i ∈ I} ⊆ 𝒫(Fin n)` が各 `j` を `k` 回覆うとき `|A|^k ≤ ∏ |π_{S_i}(A)|`。Shearer engine (`HanDShearer.lean`) を **別 cover (= 任意 S_i、Loomis-Whitney は S_i = univ.erase i の特殊形)** で 1 回呼び直すだけ。既存 B-2 (Hypercube edge isoperimetry) と engine 共有で **bundle 化可能** (cover 抽象化を 1 度行えば LW + Hypercube + BL の 3 件が共通 tooling + 個別 cover 構成 に分解)。見積 0.5〜1 週 / 100〜200 行 / 低リスク。Loomis-Whitney 完了で立った Shearer 応用シリーズの第 3 弾。

### 横断観察 (B 追加シード間)

- **Pinsker → Strong Stein のショートカット** ✅ (B-5 弱形完了で再評価済 2026-05-11): 弱形 Pinsker でも qualitative `(1+o(1))` bound は導出可能と判断。シャープ版 (B-5') 待ちは不要。B-4 の inventory は本観察と独立に進める。
- **B-2 + B-9 の bundle 化**: どちらも Shearer を「異なる cover ファミリ」で呼ぶだけ。cover を `structure ShearerCover` で抽象化すれば LW + Hypercube + BL が共通 tooling に乗る。Polymatroid structure 化と同型の wrapper plan。
- **B-7 → B-3 短縮化**: 最大の seed B-3 (Channel coding achievability、4〜6 週) を一括着手するより、B-7 (MI chain rule) を独立 1 週 plan として先に立て、B-3 を「jointly typical decoder + 既存 MI chain rule」の短縮形に再見積もる方が手戻りリスクが低い。

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
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)
