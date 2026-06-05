# Proof log — EPI case-1 difference G3 closure plan, Phase C (headline 結線)

対象 deliverable: `entropyPower_add_ge_case1_of_regular`
(`InformationTheory/Shannon/EPICase1RatioLimit.lean` §5、新規追加)。

## 結果

- **genuine assembly 達成 (0 sorry / sorryAx-free)**。`#print axioms
  entropyPower_add_ge_case1_of_regular` = `[propext, Classical.choice, Quot.sound]`。
- body は 3 行: ratio antitone (`csiszarLogRatioGap_antitoneOn_Ici_zero`) + §4
  saturation (`csiszarLogRatioGap_tendsto_zero_atTop`) を §1 order-limit bridge
  (`epi_of_csiszarLogRatioGap_tendsto`) に渡すだけ。計画 (判断ログ 7-9) の想定通り、
  2 本の genuine 柱の純合成で case-1 EPI が閉じた。
- `lake env lean` 0 errors。

## §1 の実 signature (報告事項)

`epi_of_csiszarLogRatioGap_tendsto` は計画の想定通り **`AntitoneOn` + `Tendsto` を
引数に取り EPI を返す**形 (`EPICase1RatioLimit.lean:102-108`)。手動 chain
(`epi_of_csiszarLogRatioGap_zero_nonneg` への分解) は不要だった。なお §1 は
`[IsProbabilityMeasure P]` を **要求しない** (ratio antitone と §4 のみ要求)。assembly
側で instance を持つので透過。

## noise v 規約整合の verdict

- **両柱とも v 一般 (v=1 固定でない)、型レベルで互換**。合成可能。
- ratio antitone 側: noise Gaussian law は `IsHeatFlowEndpointRegular` の field
  `v_Z : ℝ≥0` + `hZ_law : P.map Z = gaussianReal 0 v_Z` に格納 (instance ごとに自由)。
  explicit binder で v を露出しない。
- §4 側: `v_X v_Y : ℝ≥0` を explicit binder + `hZX_law : P.map Z_X = gaussianReal 0 v_X`。
- 同一 `P.map Z_X` が両方の Gaussian law に等しいので `v_Z = v_X` は暗黙に従う
  (gaussianReal 単射)。ただし assembly body では両柱を独立に呼ぶだけなので、v 一致の
  明示証明は不要だった (各柱は自分の hyp のみ消費)。

## precondition union の規模

honest hypothesis を両柱の union で thread。重複統合後の binder 構成:
- 共通: `hX/hY/hZX/hZY` (measurability)、`hXZX/hYZY` (pairwise indep)、`hXYZXY`
  (joint indep)。これらは両柱が要求するので 1 binder に統合。
- ratio antitone 専用: `h_reg_sum/X'/Y'` (3× `IsDeBruijnRegularityHyp`)、
  `h_endpt_sum/X/Y` (3× `IsHeatFlowEndpointRegular`)、`h_pos_stam` (per-t 10-conjunct
  bundle: Fisher 正値×3 + Stam + RegularDensity×2 + ∫=1×2 + conv-id + Blachman)。
- §4 専用: `hZXZY_indep`、`v_X/v_Y` + `hv_X/hv_Y` + `hZX_law/hZY_law`、
  `hZX_ac/hZY_ac/hZXZY_ac`、`h_scale_X/Y/sum` (per-t scaling regularity)、
  `varX/varY/varS` + `h_var*_nn` + `h_reg_X/Y/S` (3× `IsRescaledPathRegular`)。
- 計 ~30 binder。全て regularity (a.c. / 有限分散 / 有限エントロピー / measurability /
  IndepFun / Gaussian law / Fisher 正値 / Blachman)。**load-bearing でない** — EPI/Stam
  core は両柱内で genuine 供給、結論を hyp に encode していない。

## 観察 / 詰まった点

- 詰まりなし。最初の skeleton の引数渡しが一発で type-check 通過。
- `csiszarLogRatioGap_antitoneOn_Ici_zero` は `EPIStamToBridge` namespace 内だが、
  ファイル冒頭の `open ... EPIStamToBridge` (line 77) で修飾なし呼出可。`#print axioms`
  でフル namespace を要したのは olean stale (build リフレッシュで解消)。
- ratio antitone の引数順 (`hX hZX hXZX hY hZY hYZY hXYZXY` の interleave) が §4 の
  引数順 (`hX hY hZX hZY ...` の grouped) と異なる点だけ注意。表面的な順序差で、合成
  自体には影響なし。

## honest 命名

`_of_regular` (bare `_unconditional` 禁止)。precondition が real regularity であること
が名前から分かる形。case-1 が真の precondition ゼロ `_unconditional` にならない点は
方針 X の honest 限界 (方針 Y は genuine walled)。

## 次アクション (orchestrator)

- 新補題は `@audit:ok candidate (pending independent audit)` で self-tag。promotion は
  independent honesty-auditor の責務。ただし本補題は **新規 `@residual`/`sorry` を導入
  しない** (既存 `@audit:ok` 柱の純合成) ので、CLAUDE.md「Independent honesty audit」の
  起動条件には厳密には該当しない (新規 sorry 導入なし)。signature honesty (load-bearing
  でないこと) の確認のみ任意で実施可。
- 計画 Phase C (headline 結線) の `EPICase1RatioLimit` 側は完了。残るは
  `stamToEPIBridge_holds` / dispatch skeleton case-1 枝への配線 (Phase 5-b 相当、別 file)。
