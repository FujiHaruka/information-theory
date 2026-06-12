# 無条件 EPI — entropyPowerExt def-fix + 拡張単調性 campaign

**Status**: CLOSED ✅ (SUPERSEDED + DEAD) — 攻略対象 route α-ii (EReal chain rule self-build) は route β' (`epi-uncond-truncation-lsc-plan`、truncation+monotone-limit) が完全 supersede し、方針 Y gateway が route β' 経由で proof-done。route α-ii の dead island 2 file は物理削除済。def-fix campaign (P1-P5、`entropyPowerExt` の正部・負部 EReal 差) は genuine 着地済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (傘 moonshot)

## 要点

- **def-fix (CLOSED)**: `entropyPowerExt` の a.c. 枝を「正部 A・負部 B の EReal 差」に訂正 (旧 def は無限エントロピー入力で garbage 値を返し case-1 が false-as-stated だった)。A=⊤→h=+∞→∞ / B=⊤→h=−∞→0 を genuine 表現。
- 中心補題 = 拡張単調性 `entropyPowerExt_mono_add` (W a.c. ∧ W⊥V ⟹ `N(W+V) ≥ N(W)`)。crux = EReal chain rule ② で、これを route β' (truncation) が無条件版 bypass で closure 済。
- gateway atom の +∞ 伝播 `h(W)=⊤ ⟹ h(W+V)=⊤` は route β' の ⊤ 枝で genuine 着地。
- 後継 route β' (`epi-uncond-truncation-lsc-plan`) が方針 Y gateway を完全 proof-done 化。本 plan §7 以降の route α 攻略計画は dead。
