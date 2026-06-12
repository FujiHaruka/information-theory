# AWGN converse: C-1c Jensen affine substitution mini-plan

**Status**: CLOSED ✅ — `sum_log_one_add_le_n_log_one_add_avg` を 0 sorry / 0 residual 化 (`Real.log(1+x/N)` concavity の Jensen 適用)。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C」C-1c 項

## 要点 (将来作業で再利用しうる路)
- 採用路: `concaveOn_log_one_add_div` helper (`ConcaveOn ℝ (Ici 0) (fun x => Real.log (1 + x/N))`) を別補題化し、本体は `ConcaveOn.le_map_sum` を uniform weight `wᵢ := 1/n` で呼ぶだけ。
- friction 回避の鍵: composition friction (`comp_affineMap` の `smul`/`mul` normalization + preimage membership) を helper 1 箇所に集約 → 本体は mechanical。`smul_eq_mul` rewrite を忘れると `field_simp`/`ring` が `smul` を残して詰まる。
- power-mean (GM-AM) 経由は `log(1+x/N)` の `+1` シフトで base が変わり Mathlib 不適。
