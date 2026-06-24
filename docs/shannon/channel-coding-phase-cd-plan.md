# Channel coding achievability — Phase C + D (B-3'') ムーンショット計画 🌙

**Status**: CLOSED ✅ — B-3 親 plan の Phase C (random codebook + averaging) + Phase D (主定理 `channel_coding_achievability`: `R < I ⟹ ∃ code, P_err → 0`) を新規ファイル `ChannelCodingAchievability.lean` に並立 publish。Phase B の 3 つの joint AEP bound を黒箱で呼ぶ。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
親 plan (B-3): [`channel-coding-achievability-plan.md`](./channel-coding-achievability-plan.md)

## 要点 (≤5 行)
- averaging は probabilistic-method 形 (`codebookMeasure := Measure.pi (Measure.pi p)`) で restate — 当初の uniform-on-codebook 形は `p` 非 uniform で不整合だった (重要な後戻り)。
- decoder = 「unique m が joint typical」or fallback (`Classical.dec` + `Classical.choose`)、確率測度を絡めない。
- i.i.d. ambient は `IIDProductInput.lean` に分離 publish (`Ω := ℕ → α × β` 上の `Measure.infinitePi`、`Function.eval i` の rfl-true で MeasurableEquiv plumbing 不要)。
- 主定理 signature の full-support 仮説は `hp_pos` / `hW_pos` の正直な positivity のみ (後段 D-1 で smoothing 除去)。pass-through Prop 仮説なし。
