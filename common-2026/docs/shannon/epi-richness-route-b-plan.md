# EPI richness 壁 (G4/W2) — route B (lift-and-transport) genuine closure サブ計画 ✅ CLOSED + 撤去

**Status**: CLOSED ✅ — done then superseded (route B 2-noise lift 機材は genuine closure 後、two-time case-1 が要する 3-noise lift へ superseded され撤去済、現役後継は `NoiseExtension.lean` の lift3 系)。

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)
>   §Phase A-close G4/W2 行 + 撤退ライン L-Concl-A-richness / L-Concl-A-γ。
> **slug**: `epi-richness-route-b-plan` (frozen — 他 doc が closure 経緯を参照するため slug は残す)。

## クローズ要約 (2026-06-09)

route B (lift-and-transport) は所期の目的を達成して **完全クローズ + 撤去**された。本 plan が
追跡した 2-noise lift 機材は最終コードに残っていない。経緯:

1. **B1 (2026-06-04, commit `8431a20`)**: lift 空間 `Ω×ℝ×ℝ` 上で 4-tuple joint independence を
   Mathlib product-measure API のみから構成し、`entropyPower` の law-only 性で base に EPI を
   transport する 2-noise 機材 4 lemma を genuine (0 sorry, `@audit:ok`) に着地。
   偽 in-place W2 `stamScalingNoise_exists` (atomic measure で `false-statement`) を honest マーク。
2. **B2 (2026-06-09, commit `192410c`/`80756fa`/`d1c992d`)**: G2 heat-flow-continuity 壁 (CLOSED)
   確認後、偽 in-place W2 + dead scaling/headline 7 decl を `ToBridge.lean` から削除 (consumer ripple 0)。
3. **2-noise route 撤去 (2026-06-09, commit `4cd6b12`)**: two-time case-1 assembler が **3-noise** lift
   (`Ω×ℝ×ℝ×ℝ`、別途 unit noise `Z` を要する) を必要としたため、B1 の 2-noise 機材は
   `EPINoiseExtension.entropy_power_inequality_via_lift3` 系へ superseded された。2-noise 機材
   (`liftMeasure` / `entropyPower_map_comp_fst_eq` / `stamScalingNoise_exists_on_lift` /
   `indepFun_add_add_on_lift` / `entropy_power_inequality_via_lift`) + richness 述語
   `IsStamScalingNoiseHyp` / `isStamScalingNoiseHyp_symm` (`ToBridge.lean`) は external consumer 0 を
   `dep_consumers.sh` で確認のうえ削除 (計 7 decl、ripple 0)。

## 現役の後継 (SoT は code)

- **3-noise lift transport**: `EPINoiseExtension.liftMeasure3` /
  `entropyPower_map_comp_fst_eq3` / `entropy_power_inequality_via_lift3` (`NoiseExtension.lean`、
  sorryAx-free genuine)。密度版 EPI 結論 `EPIDensityForm.entropy_power_inequality_of_density` +
  `EPICase1SmoothingLimit.entropy_power_inequality_of_density_explicit` /
  `entropy_power_add_ge_of_finite_variance` が消費。
- richness sub-wall は route B (lift) で踏まずに閉じられることが上記で実証済。in-place-noise-extension
  壁は route B では踏まない。

旧 plan 本文 (Phase 0-7 設計 / B1 vs B2 比較表 / 撤退ライン L-RouteB-* / 判断ログ) は git 履歴に残る
(本クローズ直前リビジョン)。新規参照は現役後継 (上記) と親 plan を見ること。
