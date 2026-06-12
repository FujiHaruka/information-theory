# T3-E Joint Source–Channel Coding (Separation Theorem) ムーンショット計画 🌙

**Status**: CLOSED ✅ — `SeparationTheorem.lean` で IID-source 限定の separation theorem を publish (achievability + converse)。stationary ergodic 一般化は scope-out (撤退ライン L-S0)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-E. Joint Source–Channel Coding (Separation Theorem)」

## 要点
- 構造: source side / channel side は既存 black-box (AEP source coding + DMC channel coding)、composition primitive (`composeCode` / `composedErrorProb` / union bound / rate scaling) が novel 自作部。
- achievability は rate splitting `H<R_src<R_ch<C` + 既存 black-box 合成 (honest hyp `entropy < capacity`)。converse は source-side を `source_coding_converse` で実 discharge、channel-side rate bound は hypothesis pass-through 形。
- stationary ergodic 一般化は SMB closing 未閉で +1000 行を要し非現実的、別 seed `separation-theorem-stationary-ergodic-*` に deferred (撤退ライン L-S0)。
- 凍結スラッグ: 撤退ライン L-S0 (stationary ergodic scope-out)、L-S1〜L-S3 / L-P1〜L-P3 (Tier 縮退 / 自作 plumbing 肥大ライン) は本 plan 内定義。
