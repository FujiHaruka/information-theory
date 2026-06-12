# AEP Phase E — 源符号化定理 achievability ムーンショット計画 🌙

**Status**: CLOSED ✅ — `source_coding_achievability` 完成済。仮定は i.i.d. 標準形 (`iIndepFun`/`IdentDistrib`/`hpos`) のみ (pass-through なし)。両側等号 `source_coding_theorem` も完成。
**SoT**: `docs/textbook-roadmap.md` Ch.3。詳細履歴は git。

## 要点 (任意, ≤5 行)
- typical-set enumeration constructive scheme: `M_n := ⌈exp(nR)⌉`、encoder/decoder を `Finset.equivFin` + `Fin.castLE` で typical-block bijection 構成 (非 typical は default index で error 容認)。
- error rate は round-trip lemma の対偶 (error event ⊆ ∁ typicalSet) + `typicalSet_prob_tendsto_one` の補集合で 0 へ。
- rate Tendsto は `Nat.le_ceil` + `Nat.ceil_lt_add_one` の上下挟み込み squeeze (`R > 0` は entropy ≥ 0 + hR から内部 derive)。
