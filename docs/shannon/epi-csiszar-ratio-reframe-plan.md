# EPI: Csiszár 1-source gap の log-ratio 再定義 サブ計画

**Status**: CLOSED ✅ — false-as-framed な difference-gap monotonicity を genuine な log-ratio gap (`csiszarLogRatioGap`) に再定義し、ratio monotonicity atom (R-1〜R-5) を genuine 化。general unconditional EPI は後継ルート群で達成済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A-close G1

## 要点 (再利用可能な proof route / 判断軸)
- **difference 形は FALSE / ratio 形は genuine (本 plan の中核)**: `N_sum·J_sum ≤ N_X·J_X+N_Y·J_Y` は plain harmonic Stam から従わない (`N_i` 無制約で反例構成可)。一方 log-ratio `r(t) = log N_sum − log(N_X+N_Y)` の微分は `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)`、重み `α=N_X/(N_X+N_Y)` で `α²≤α` を使い純 algebra で ≤0 (isoperimetric 不要、Mathlib 壁なし)。EPI 復元は difference 版と equivalent。
- **redefine でなく new def を選ぶ**: 旧 difference def を残し新 `csiszarLogRatioGap` を併設すると、過去の `@audit:ok` を黙って無効化せず段階移行できる (in-place rewrite は audit pass の無効化が grep で見えない)。
- **ratio では rescale の `(1-s)`/`c²` 因子が log 内で相殺し scale 不変になる**: `log(c²A)−log(c²B)=log A−log B`。difference 版の `(1-s)` bookkeeping が消えるのは ratio 設計の追加利点。
- **load-bearing と regularity precondition の線引き**: core 不等式 `1/J_sum ≥ 1/J_X+1/J_Y` は producer 側 (`stam_step2_density_wall`) が genuine に持つ。consumer は ∀-量化 producer Prop を apply 入力 (IndepFun / convolution 同定 / IsBlachmanConvReady = regularity) で受けるのは OK、core 不等式そのものを hyp 化する (案 C) のは禁止。
- **auditor sufficiency check の欠落で偽 lemma が PASS した教訓**: difference defect は「非循環 + 非 bundling」だけの監査を通過した。非循環/非 bundling は必要条件であって十分条件でない — 仮説から結論が semantic に follow するか (反例構成を試みる) の sufficiency check が要る。
