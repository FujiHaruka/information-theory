# Shannon EPI: case-1 de Bruijn regularity **producer** サブ計画

> **Parent**: [`epi-case1-ratio-limit-plan.md`](epi-case1-ratio-limit-plan.md) +
> [`epi-case1-phaseC-methodx-wrapper-plan.md`](epi-case1-phaseC-methodx-wrapper-plan.md)
> §「方針X wrapper → de Bruijn regularity 群 への還元」
> **Status**: 📋 draft (案B 改訂、起草のみ、実装は別 session で `lean-implementer` dispatch)
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-file 節に列挙
> **proof-log**: yes (実装 session で `docs/shannon/proof-log-epi-case1-debruijn-producer.md`)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-producer-plan)`

## 進捗

- [x] M0 案D 調査 (de Bruijn Gaussian discharge の var=1 本質依存性) — 本 plan 内で完了
- [x] M1 blast radius 実測 (`IsRegularDeBruijnHypV2` / `IsDeBruijnRegularityHyp` consumer 全件)
- [~] ~~A vs B 確定 — 案A (v_Z 一般化) を採用~~ → **案A REVERT (L-A-esc 発火)、案B 採用** 🔄
- [x] B-0 path-identification 代数確認 (advisor 第一手) — 本 plan 内で完了
- [x] B-0' wrapper latent defect 解消方針確定 (3 択評価 → 推奨確定) — 本 plan 内で完了
- [ ] PB-1 wrapper restate: case-1 wrapper を unit-noise (v_X=v_Y=1) 固定形に restate 📋
- [ ] PB-2 path-identification reduction 補題 `gaussianConvolution_rescale_eq` 構築 📋
- [ ] PB-3 `IsDeBruijnRegularityHyp` producer (X / Y、unit-noise 直接) 構築 📋
- [ ] PB-4 sum-instance producer (W=(Z_X+Z_Y)/√2 unit + time-reparam) 構築 📋
- [ ] PB-5 `h_pos_stam` producer (Stam/Blachman genuine 既存配線) 構築 📋
- [ ] PB-6 最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise` 結線 📋
- [ ] PB-7 incidental: `IsIBPHypothesis` retract 📋
- [ ] PB-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋

## 文脈 (確定背景)

case-1 EPI wrapper `entropyPower_add_ge_case1_of_methodX`
(`EPICase1RatioLimit.lean:1470`、sorryAx-free) は結論
`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
を「方針X (a.c. / 2次モーメント / 雑音 Gaussian law `gaussianReal 0 v_X` / 4-tuple 独立)
**+ de Bruijn regularity 群**」へ還元済。

de Bruijn family は 0 sorry / 0 residual 化済 (commit `70314b8`)。
壁 `wall:debruijn-integration` / `wall:fisher-finiteness` / `wall:entropy-finiteness` /
`wall:cond-diff-entropy` / `wall:approx-identity-L1` はいずれも CLOSED
(`docs/audit/audit-tags.md` Wall register 参照)。

残るのは wrapper が thread する **de Bruijn regularity 群** を方針X の前提から供給する
**producer 構築**。wrapper signature (`EPICase1RatioLimit.lean:1488-1518`) が要求する群:

- `h_reg_sum` / `h_reg_X'` / `h_reg_Y'` : `IsDeBruijnRegularityHyp` 3 本
  (`EPIStamDischarge.lean:251`)
- `h_endpt_sum` / `h_endpt_X` / `h_endpt_Y` : `IsHeatFlowEndpointRegular` 3 本
  (`EPIG2HeatFlowContinuity.lean:488`)
- `h_pos_stam` : per-`t>0` の Fisher>0 (3 本) ∧ Stam ∧ IsRegularDensityV2 (2 本) ∧
  density 正規化 (2 本) ∧ sum conv-pin ∧ Blachman-conv-ready の合成 bundle
  (`EPICase1RatioLimit.lean:1496-1518`)

### 唯一の構造的障害 — de Bruijn group が unit-variance noise を要求

`IsRegularDeBruijnHypV2.Z_law : P.map Z = gaussianReal 0 1`
(**unit variance ハードコード**、`FisherInfoV2DeBruijn.lean:210`)。
`IsDeBruijnRegularityHyp.reg_at : ∀ t>0, IsRegularDeBruijnHypV2 X Z P t`
(`EPIStamDischarge.lean:262`) が `reg_at .Z_law` 経由で unit variance を継承するため、
`P.map Z_X = gaussianReal 0 v_X` (v_X≠1) からは `IsDeBruijnRegularityHyp X Z_X P` を
**型レベルで構成不能**。sum 側は `Z_X+Z_Y ∼ gaussianReal 0 (v_X+v_Y)`
(`EPICase1RatioLimit.lean:1556` 確定) なのでさらに v=2 で不整合。

---

## M0 — 案D 調査結果 (de Bruijn Gaussian discharge の var=1 本質依存性) — 案A 前提、保持

**問い**: de Bruijn の analytic core が var=1 を本質的に使うか。

**実 Read 調査結果** (verbatim):

| 補題 / 定義 | file:line | var=1 依存性 |
|---|---|---|
| `gaussianConvolution_law_conv` | `FisherInfoV2DeBruijnPerTime.lean:80` | **一般 `v_Z`** 既存。`(P.map X) ∗ gaussianReal 0 ⟨s·v_Z,_⟩`。`@audit:ok` |
| `pPath_eq_convDensityAdd` (Phase 1b) | `FisherInfoV2DeBruijnPerTime.lean:215` | **一般 `v_Z`** 既存。docstring「sum instance の noise `𝒩(0,2)` のため一般化必要、`v_Z=1` 形は `s·1=s` で回収」と明記 |
| `debruijnIdentityV2_holds_assembled` core chain (`_chain`) | `FisherInfoV2DeBruijnAssembly.lean:3397` (`_chain`), :3543 (top) | **v_Z 非依存** (density-level、`convDensityAdd` 経由)。`h_reg.Z_law` を chain に渡していない |
| `_entropy_eq` atom | `FisherInfoV2DeBruijnAssembly.lean:3437` | `hZ_law : gaussianReal 0 1` 受領。内部で Phase 1b を `v_Z:=1` で instantiate、`s*1=s` rewrite で var=1 を simp で潰すだけ |
| `_fisher_match` atom | `FisherInfoV2DeBruijnAssembly.lean:3485` | `_hZ_law : gaussianReal 0 1` 受領 (`_` prefix = 未使用)。var=1 は load-bearing でない |
| `deBruijn_identity_v2_gaussian` (Stage-2 publish) | `FisherInfoV2DeBruijn.lean:441` | `hZ_law : gaussianReal 0 1` 受領 + `gaussianConvolution_law_of_gaussian` (var=1 専用) を呼ぶ。Gaussian X 限定 publish point、producer chain 非経由 |

**M0 の結論 (var=1 本質依存ゼロ)**: de Bruijn の **density-level analytic core は v_Z-agnostic**。
v_Z=1 が現れるのは `_entropy_eq`/`_fisher_match` の Phase 1b instantiate (`s*1=s` simp) のみ。
**この事実は案B でも活きる** — 案B の sum-instance time-reparam が「density を unit-noise 形の
de Bruijn core に乗せる」根拠になる (B-0 参照)。

### M0 の落とし穴 (advisor verdict で判明、案A REVERT の根拠)

M0 は「de Bruijn **density-level** core が v_Z-agnostic」を正しく確認したが、**de Bruijn
identity の微分値 `(1/2)·J`** が v_Z=1 にどう依存するかを見落としていた:

- `deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:51`) /
  `debruijnIdentityV2_holds_assembled` (`Assembly:3543`) の結論は
  `HasDerivAt (s↦h(P.map(X+√s·Z))) ((1/2)·J(density_t)) t`。assembly atom は heat kernel
  variance を **時間 `s` に直結** (`_entropy_eq` が Phase 1b を `v_Z:=1` で叩き `s·1=s`)。
- 一般 v_Z では density = `convDensityAdd pX g_{s·v_Z}`、chain rule で genuine 微分値は
  `(v_Z/2)·J(at s·v_Z)`。**案A (`Z_law` だけ開いて微分値 `(1/2)·J` 据置) は false statement**
  (tier 5、degenerate)。
- ratio core への波及 (advisor Q1、verbatim): `csiszarLogRatioGap_hasDerivAt:724-749` が
  `deBruijn_identity_v2` を 3 成分で呼び、`:766-803` の entropyPower lift で `2·(1/2)=1` の
  cancellation により `(1/2)` が一律キャンセルし、ratio-gap 微分値は
  `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` (`(1/2)` 不在)。案A-corrected で
  `(1/2)·J → (v_Z/2)·J` にすると lift cancellation が `exp(2h)·v_Z·J` となり ratio 各項に
  **v_Z factor が非一律** (X→v_X, Y→v_Y, sum→v_X+v_Y) に乗る。harmonic Stam
  `csiszarLogRatioGap_deriv_le_zero:895` (arith core `csiszar_ratio_deriv_le_zero_arith`、α²≤α
  weights) は同時スケール不変だが **項毎 factor には不変でない** → **偽化**。

→ **案A / 案A-corrected はいずれも不採用** (値据置 = false statement、値一般化 = ratio core 偽化)。
正しい一般化は「**値ではなく path を unit 形に reparam して吸収する**」(案B)。

---

## M1 — blast radius 実測 (`rg -c`) — 案A 想定、案B では参照のみ

`IsRegularDeBruijnHypV2` / `IsDeBruijnRegularityHyp` consumer の file 別件数は
旧版 M1 表 (git 履歴参照) に記録。**案B は structure を一切 touch しない** ので M1 の
blast radius は案B では無効 (案B の影響範囲は case-1 局所 + 1 reduction 補題、PB 各 Phase 参照)。

`isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1346`) が
`IsDeBruijnRegularityHyp` の最大 consumer (34 件) だが、その `h_reg` precondition は
**明示的に `P.map Z_X = gaussianReal 0 1` (unit-variance noise) を要求**
(`EPIStamToBridge.lean:1352-1353`)。これは EPI 一般 line の設計全体が
**de Bruijn group level で unit-variance noise を前提**していることの verbatim 証拠
(B-0' の wrapper restate 推奨根拠)。

---

## B-0 — path-identification 代数確認 (advisor 第一手、本 plan で verbatim 確認済)

**問い**: `Z' := Z/√v` (v>0、`Z' ∼ N(0,1)`) としたとき、
`gaussianConvolution X Z' (t·v) =ᵐ gaussianConvolution X Z t` か。

**代数 (verbatim 確認)**:

- `gaussianConvolution X Z s := fun ω => X ω + Real.sqrt s * Z ω`
  (`FisherInfoV2DeBruijn.lean:127`、plain def、pointwise)。
- `Z' ω = Z ω / √v` と置くと:
  `gaussianConvolution X Z' (t·v) ω = X ω + √(t·v) · (Z ω / √v)`。
- `√(t·v) = √t · √v` (`Real.sqrt_mul (ht : 0 ≤ t) v`、`Mathlib/Data/Real/Sqrt.lean:352`、
  verbatim 確認済)。
- ⇒ `X ω + √t·√v·(Z ω/√v) = X ω + √t·(√v/√v)·Z ω = X ω + √t·Z ω = gaussianConvolution X Z t ω`
  (v>0 ⇒ `√v ≠ 0`、`Real.sqrt_pos.mpr`)。

**結論**: これは **点ごとの厳密恒等式** (a.e. でなく everywhere、t≥0 v>0 で)。
`P.map (gaussianConvolution X Z' (t·v)) = P.map (gaussianConvolution X Z t)`
が `congrArg (P.map ·)` + `funext` で従う。**Mathlib-direct、壁ゼロ**。

これにより:
- 元 path `X + √t·Z_X` (variance v_X noise) を、**unit-noise `Z_X' = Z_X/√v_X` 上の
  time-reparam path `X + √(t·v_X)·Z_X'`** と同一視できる。
- unit-noise `Z_X'` 上では `IsRegularDeBruijnHypV2 X Z_X' P (t·v_X)` の
  `Z_law : gaussianReal 0 1` が **無改変で成立** (M0 で確認した density-level core も
  Phase 1b `v_Z:=1` instantiate でそのまま使える)。

### B-0 の重要な系 — chain factor が ratio core に到達しない理由

advisor Q2/Q3 が懸念した「time-reparam `t→t·v` が HasDerivAt に chain factor `v` を持ち込む」
問題は、**producer 側で path-identification を density に閉じ込めれば回避できる**:

- producer が構成する `IsDeBruijnRegularityHyp X Z_X P` の `reg_at t ht` の **微分値は
  consumer (`deBruijn_identity_v2 X Z_X`) が決める**。consumer は `gaussianConvolution X Z_X s`
  (元 Z_X、時間 s) に対する `HasDerivAt ((1/2)·J(density_t)) t` を要求する (`Genuine.lean:57`)。
- 案B の wrapper restate (B-0' 推奨 (a)) で **noise を v_X=v_Y=1 に固定**すれば、
  `Z_X` 自体が unit-variance、reparam すら不要で X/Y 成分は素直に `reg_at` を埋められる。
- **time-reparam が要るのは sum-instance のみ** (`Z_X+Z_Y ∼ N(0,2)`)。sum producer は
  `W := (Z_X+Z_Y)/√2` (unit) を導入し、`X+Y+√t·(Z_X+Z_Y) = X+Y+√(2t)·W` で
  unit-noise core に乗せる。この reparam factor は **producer 内の `density_t` 定義に閉じる**
  (consumer `deBruijn_identity_v2 (X+Y) (Z_X+Z_Y)` は元 `Z_X+Z_Y` の時間 s に対する HasDerivAt を
  要求し、producer の `reg_at` が返す `density_t` がその s での conv density に一致していれば
  microscopic な微分値は consumer 側の `(1/2)·J(density_t)` のまま — sum の density は
  `convDensityAdd pX_sum g_{s·2}` で、PB-4 で v_Z=2 形 (Phase 1b 一般 v_Z) に pin する)。

**PB-4 設計上の確定事項 (B-0 帰結)**: sum producer は **`Z_law` を
`gaussianReal 0 1` で埋められない** (`Z_X+Z_Y ∼ N(0,2)`)。よって sum-instance を
**unit `W` を介して構成し path-identification 補題で元 `Z_X+Z_Y` 形に橋渡し**する。
ただし `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` の `reg_at` は構造上 `Z_X+Z_Y` を
引数に取る (型は polymorphic) ので、`reg_at t ht : IsRegularDeBruijnHypV2 (X+Y) (Z_X+Z_Y) P t` の
`Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 1` が **N(0,2) と矛盾し型不充足**。
→ **sum-instance も structure の unit-hardcode に阻まれる** (X/Y と同じ壁、ただし v=2)。
これが B-0' で **structure を touch しない案 (a) wrapper restate** を推奨する決定的理由
(下記)。

---

## B-0' — wrapper latent defect 解消方針 (3 択評価 → 推奨確定)

### latent defect の所在 (verbatim)

case-1 wrapper `entropyPower_add_ge_case1_of_methodX` (`EPICase1RatioLimit.lean:1470`) は
noise variance `v_X v_Y : ℝ≥0` を **任意** (`hv_X : v_X ≠ 0` のみ、`:1481`) で取りながら、
de Bruijn group `h_reg_X' : IsDeBruijnRegularityHyp X Z_X P` (`:1490`) を要求する。
後者の `reg_at` は `Z_law : gaussianReal 0 1` (unit) を強制 (`EPIStamDischarge.lean:262` →
`FisherInfoV2DeBruijn.lean:210`)。case-1 noise が `gaussianReal 0 v_X` (`:1482`) で v_X≠1 のとき、
この group は **型レベルで供給不能** → wrapper は v_X≠1 で **vacuously true** (現状 producer が
無いので consumer は誰も呼べず defect が顕在化していないだけ)。

ratio antitone `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`) /
`entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`) も同じ
`IsDeBruijnRegularityHyp` 群を取るので同じ latent v=1 制約を持つ。

現 wrapper は `@audit:ok` honest_residual だが、これは「de Bruijn group を thread する」設計が
honest なだけで、**v_X≠1 で producer が存在しえない (vacuous)** 点が honesty の死角。
producer を書く本 plan で **実体化が必要**。

### 3 択評価

| 案 | 内容 | 評価 |
|---|---|---|
| **(a) wrapper を v_X=v_Y=1 固定に restate** | case-1 wrapper の noise を unit-variance に固定 (`hZX_law : gaussianReal 0 1`)。sum は `Z_X+Z_Y ∼ N(0,2)` を **producer 内の time-reparam (W=(Z_X+Z_Y)/√2 unit)** で吸収 | **推奨**。structure 無改変。EPI 一般 line の設計 (`isStamToEPIScalingHyp_of_stam_debruijn` が unit-noise 要求、`EPIStamToBridge.lean:1352`) と完全整合。noise は補助変数で結論に現れない (下記) ので unit 固定は実害ゼロ |
| (b) wrapper を `Z_X'` (標準化) thread に書換 + path-identification | wrapper signature 自体を `Z_X' = Z_X/√v_X` thread に書換、producer は標準正規上で構築し path-identification で元 path に接続 | 書換範囲が wrapper + ratio antitone + `entropyPower_add_ge_case1_of_regular` の 3 decl 以上。`csiszarLogRatioGap` body (`EPIL3Integration.lean:1380`) の path `X+√t·Z_X` も `Z_X'` 化が要り、§3 saturation (`entropyPower_rescaled_path_tendsto` 整合) も再検証。範囲大 |
| (c) 現 wrapper 維持、producer 側で reparam 吸収 | wrapper signature 不変のまま、producer が v_X≠1 の `IsDeBruijnRegularityHyp X Z_X P` を path-identification で構成 | **不可能**。`reg_at` の `Z_law : gaussianReal 0 1` は `Z_X` (v_X≠1) に対し型不充足。path-identification は path (関数) を同一視するが、`Z_law` は **noise `Z_X` の law を直接主張**するので reparam では救えない (B-0 末尾の系) |

### 推奨 = (a) wrapper restate (unit-noise 固定)

**根拠 1 — noise は補助変数で結論に現れない**: wrapper の結論
`N(P.map(X+Y)) ≥ N(P.map X)+N(P.map Y)` は Z_X/Z_Y を含まない
(`EPICase1RatioLimit.lean:1519`)。Z は Stam/de Bruijn machinery の補助。よって
**X/Y 補助 noise を標準正規 (v=1) に固定しても結論の一般性を失わない**。case-1 EPI の
最終消費者は方針X からこの wrapper を呼ぶが、noise は producer が方針X 入力 (a.c. / 独立性)
から内部で導入する自由変数なので、unit に固定するのは自然。

**根拠 2 — EPI 一般 line が既に unit-noise を de Bruijn group level で要求**:
`isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1346`) の `h_reg`
precondition は `P.map Z_X = gaussianReal 0 1` を明示要求 (`:1352-1353`)。EPI 設計全体が
de Bruijn group の noise を unit と仮定している。case-1 wrapper が v_X 任意を取るのは
**この設計から逸脱した latent defect**で、unit 固定は逸脱の是正。

**根拠 3 — structure を touch しない**: 案 (a) は `IsRegularDeBruijnHypV2` /
`IsDeBruijnRegularityHyp` structure を一切改変しない (0 sorry 化したばかりの de Bruijn
family を再 touch するリスク回避)。sum-instance の N(0,2) noise だけが reparam を要するが、
これは **producer 内の sum 補題 1 本に局所化** (PB-4)。

**honesty 上の効果**: restate により wrapper は v_X=v_Y=1 (具体値) で型整合し、
producer が **実際に呼べる** (vacuous でない) ものになる。`_unitnoise` 命名で「unit-noise
case-1」を明示 (name laundering でない、実態に即した命名)。

**restate の影響範囲**: wrapper `entropyPower_add_ge_case1_of_methodX` の noise law を
`gaussianReal 0 v_X` → `gaussianReal 0 1` に固定し、`v_X v_Y` 引数を除去。
依存する `entropyPower_add_ge_case1_of_regular` (`:1343`) は `v_X v_Y` を
`IsRescaledPathRegular` / `entropyPower_rescaled_path_tendsto` (`:293`) にも渡しているが、
そちらは **一般 v_B を取る (`:296`) のでそのまま v=1 を渡せば動く** (saturation は
unit-noise でも `entropyPower_gaussian_additivity` で N(Z_X)+N(Z_Y) = N(Z_X+Z_Y) が成立、
sum noise は N(0,2) のまま `entropyPower_rescaled_path_tendsto` が `v_B := 2` を受ける)。
→ §3/§4 side (saturation / scaling) は v 任意で既に動くので restate の影響は
**de Bruijn group を要求する pillar 1 側のみ**。

---

## ゴール / Approach

### ゴール

`entropyPower_add_ge_case1_of_methodX`(restate 後 `_unitnoise` 形) が thread する
de Bruijn regularity 群 (`IsDeBruijnRegularityHyp` ×3 / `IsHeatFlowEndpointRegular` ×3 /
`h_pos_stam`) を方針X の前提 (a.c. / 2次モーメント / **unit-variance** 雑音 Gaussian law /
4-tuple 独立) から **producer 補題として供給**し、最終 wrapper
`entropyPower_add_ge_case1_of_methodX_unitnoise` の前提を「方針X (unit-noise) のみ」に縮約する。

de Bruijn regularity 群が precondition から消え、方針X のみ残ることを確認する
(`IsDeBruijnRegularityHyp` を含む前提が 0 件になる)。

### Approach (全体戦略) — 案B (noise 標準化 + time-reparam)

**核心 = noise を unit-variance に固定 (wrapper restate) → unit-noise producer chain →
sum-instance のみ time-reparam で N(0,2) を吸収 → wrapper 結線** の 4 段。
案A (`Z_law` 値一般化) は false statement (M0 落とし穴) なので破棄、structure は無改変。

**第 1 段 (PB-1) — wrapper restate (unit-noise)**:
case-1 wrapper の noise law を `gaussianReal 0 1` に固定し v_X/v_Y 引数を除去
(B-0' 推奨 (a))。EPI 一般 line の de Bruijn group 設計 (unit-noise) と整合。noise は
結論に現れない補助変数なので一般性を失わない。

**第 2 段 (PB-2) — path-identification reduction 補題**:
`gaussianConvolution X Z' (t·v) =ᵐ gaussianConvolution X Z t` (Z'=Z/√v、B-0 で代数確認、
点ごと厳密恒等式) を 1 本書く。sum-instance の N(0,2)→unit-W 橋渡しに使う。

**第 3 段 (PB-3 / PB-4) — producer chain**:
- **X / Y producer (PB-3)**: noise が既に unit (restate 後 `Z_X ∼ N(0,1)`) なので
  `IsDeBruijnRegularityHyp X Z_X P` を **直接** 構成 (reparam 不要)。`reg_at t ht` の各 field を
  方針X 入力 (a.c. → rnDeriv density witness、2次モーメント、Gaussian kernel conv-pin) で埋める。
- **sum producer (PB-4)**: `Z_X+Z_Y ∼ N(0,2)` は unit-hardcode `Z_law` と型不充足。
  `W := (Z_X+Z_Y)/√2` (unit) を導入し path-identification (PB-2) で
  `X+Y+√t·(Z_X+Z_Y) = X+Y+√(2t)·W` を同一視、unit de Bruijn core (`(1/2)·J`) に乗せる。
  reparam factor は producer 内の `density_t` (conv density `convDensityAdd pX_sum g_{s·2}`、
  Phase 1b 一般 v_Z=2 形) に閉じ、ratio core に到達しない (B-0 系)。

**第 4 段 (PB-5 / PB-6) — `h_pos_stam` producer + wrapper 結線**:
`h_pos_stam` の Stam / Blachman conjunct は genuine 既存 (`isStamInequalityHyp_via_step3` /
`isBlachmanConvReady_convDensityAdd_gaussian`) を配線。最終 wrapper
`entropyPower_add_ge_case1_of_methodX_unitnoise` で de Bruijn 群を producer から注入し、
前提を方針X (unit-noise) のみに縮約。

**撤退口**: producer の `pX` series (density witness) 等で a.c. precondition から Real density
witness が組めない部分が判明したら、その field のみ `sorry` +
`@residual(plan:epi-case1-debruijn-producer-plan)` で park (signature は producer 形を保つ)。
`*Hypothesis` predicate に核を bundling する撤退は禁止。

### 案A vs 案B — 確定 (案A REVERT、案B 採用)

| 観点 | 案A (`Z_law` v_Z 一般化) | 案B (noise 標準化 + time-reparam) ✓ |
|---|---|---|
| 数学的妥当性 | **不可** (値据置=false statement、値一般化=ratio core 偽化、M0 落とし穴 / advisor Q1) | OK (path-identification は厳密恒等式、unit de Bruijn core `(1/2)·J` を維持、B-0) |
| structure 改変 | `IsRegularDeBruijnHypV2.Z_law` field 改変 (0 sorry family 再 touch) | **structure 無改変** |
| EPI 一般 line 整合 | 一般 line は unit-noise 前提 (`isStamToEPIScalingHyp_of_stam_debruijn:1352`) なので逆行 | 整合 (unit-noise を維持) |
| 影響範囲 | M1 表 12 file に v_Z carrier 伝播 | case-1 局所 (wrapper restate + producer + reduction 補題 1 本) |
| 退化リスク | `v_Z=0` 退化 (`hv_Z_pos` で排除要) | time-reparam `t→t·v` の v>0 / `Y:=0` 退化に注意 (撤退ライン L-DBD 監視) |

**採用根拠**: 案A は M0 が「density core は v_Z-agnostic」を確認したものの
**de Bruijn 微分値 `(1/2)·J` の v_Z 依存を見落とし**、advisor verdict (Q1) で
ratio core 偽化が判明 → L-A-esc 発火。案B は path を unit 形に reparam することで
微分値 `(1/2)·J` を unit のまま維持し、chain factor を producer 内 density に局所化する
(B-0 系)。structure 無改変 + EPI 設計整合 + case-1 局所で、honesty / 影響範囲とも案A に優る。

---

## Phase 詳細

### PB-1 — wrapper restate (unit-noise 固定) (~30-50 行)

**スコープ**: case-1 wrapper の noise を unit-variance に固定し v_X/v_Y を除去。

対象 declaration (noise を unit に固定、v_X/v_Y 引数除去):
- `entropyPower_add_ge_case1_of_methodX` (`EPICase1RatioLimit.lean:1470`): `hZX_law` を
  `gaussianReal 0 1` に固定、`v_X v_Y hv_X hv_Y` 引数除去。
- 依存 `entropyPower_add_ge_case1_of_regular` (`:1343`) の呼出: §3/§4 side は v_B 任意を
  取る (`entropyPower_rescaled_path_tendsto:296`) ので `v_X:=1`/`v_Y:=1`/`v_sum:=2` を渡す
  (sum noise は N(0,2) のまま、saturation は `entropyPower_gaussian_additivity` で成立)。

**判断ログ記録対象**: wrapper restate により latent v=1 vacuous defect を実体化
(B-0' 推奨 (a))。**この restate は signature 改変で honesty 意味が変わる** ので PB-V で
独立 honesty audit 必須 (CLAUDE.md「Independent honesty audit」起動条件)。

- [ ] `entropyPower_add_ge_case1_of_methodX` の noise law を `gaussianReal 0 1` に固定
- [ ] v_X/v_Y/hv_X/hv_Y 引数除去 (sum-instance は body 内で N(0,2) を導出: `1+1=2`)
- [ ] 依存 consumer (`entropyPower_add_ge_case1_of_regular`) 呼出を v=1/v=1/v=2 で更新
- [ ] §3/§4 side (saturation/scaling) が v=1/v=2 で silent compile を確認

**Done 条件**: restate 後 wrapper が type-check done。noise が unit に固定され
producer が呼べる形になった (vacuous でない)。

### PB-2 — path-identification reduction 補題 (~20-40 行)

**スコープ**: B-0 で代数確認した path-identification を 1 本書く。
`FisherInfoV2DeBruijnPerTime.lean` か case-1 file に置く。

スケッチ:

```lean
/-- **path-identification (B-0)**: 標準化 noise `Z' = Z/√v` (v>0) 上の time-reparam path
`X + √(t·v)·Z'` は元 path `X + √t·Z` と点ごと一致。sum-instance の N(0,2)→unit-W 橋渡しに使う。
@residual(plan:epi-case1-debruijn-producer-plan) -- 閉じられれば外す -/
theorem gaussianConvolution_rescale_eq {α : Type*}
    (X Z : α → ℝ) (v : ℝ) (hv : 0 < v) (t : ℝ) (ht : 0 ≤ t) :
    InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X (fun ω => Z ω / Real.sqrt v) (t * v)
      = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z t := by
  funext ω
  unfold InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
  rw [Real.sqrt_mul ht.le v]  -- √(t·v) = √t·√v   ※ ht: 0≤t、hv で √v≠0
  -- √t·√v·(Z/√v) = √t·Z   (√v ≠ 0 from hv)
  field_simp [Real.sqrt_ne_zero'.mpr hv]  -- or Real.sqrt_pos.mpr hv
  ring
```

**注意 (degenerate 回避、CLAUDE.md L-DBD)**: `v > 0` を厳格に要求 (`√v ≠ 0` のため)。
`v = 0` 退化 (`√0 = 0` で除算不能) を `field_simp` が突かないよう `hv : 0 < v` を必須に。
case-1 では `v_X ≠ 0` / `v_X+v_Y ≠ 0` から `0 < v` を導く (sum は `2 > 0` で trivial)。

**Done 条件**: 補題が type-check done (理想は 0 sorry、`Real.sqrt_mul` + `field_simp` +
`ring` で閉じる見込み)。`P.map` 版 (`congrArg (P.map ·)`) の系も併記。

### PB-3 — `IsDeBruijnRegularityHyp` producer X / Y (unit-noise 直接) (~60-120 行)

**スコープ**: restate 後 noise が unit (`Z_X ∼ N(0,1)`) なので `IsDeBruijnRegularityHyp X Z_X P` を
**reparam なしで直接** 構成。case-1 file に置く。

producer 補題スケッチ (X 版、Y も同型):

```lean
/-- case-1 方針X (unit-noise) の前提から `IsDeBruijnRegularityHyp X Z_X P` を供給する producer。
noise が unit (`gaussianReal 0 1`) なので `reg_at` の `Z_law` を直接埋める (reparam 不要)。
@residual(plan:epi-case1-debruijn-producer-plan) -/
theorem isDeBruijnRegularityHyp_of_methodX_unitnoise
    (X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω => (X ω)^2) P) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P := by
  refine { density_path := fun t => convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩),
           reg_at := fun t ht => { Z_law := hZX_law, density_t := …, … },
           density_t_eq := …, integrable_deriv := … }
  …
```

各 field の供給元 (verbatim):
- `reg_at .Z_law`: `hZX_law` 直接 (unit、structure 無改変で型整合)
- `reg_at .density_t` / `.density_t_eq` / `density_path`: conv-pin
  `convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` (Phase 1b `v_Z:=1` 形、`s·1=s`)
- `reg_at .pX` series (`pX`/`pX_nn`/`pX_meas`/`pX_law`/`pX_mom`): **case-1 input density witness、
  供給元確定が PB-3 核心**:
  - `pX := fun x => ((P.map X).rnDeriv volume x).toReal` (a.c. ⇒ rnDeriv 存在)
  - `pX_nn`: `ENNReal.toReal_nonneg`
  - `pX_meas`: `Measure.measurable_rnDeriv` + `.toReal`
  - `pX_law`: `hX_ac` ⇒ `(P.map X) = volume.withDensity (rnDeriv …)`
    (`Measure.withDensity_rnDeriv_eq` の整合確認、toReal vs ENNReal density)
  - `pX_mom`: `h_mom_X` (`Integrable (X²) P`) → `Integrable (y²·pX y) volume`
    (push-forward `integral_map` / `lintegral_rnDeriv` 経由、**非自明、PB-3 で要詳細**)
- `integrable_deriv`: bounded-T interval integrability。`wall:fisher-finiteness` CLOSED 資産
  `gaussianConv_fisher_le_inv_var` (`FisherConvBound.lean:385`) で `J ≤ 1/(t·1)` 連続有界。

**`pX` series の honesty 判定**: load-bearing でない **regularity precondition**
(CLAUDE.md「判定の一言」前者)。「X が Lebesgue 密度を持つ」は input regularity で de Bruijn
analytic 核を bundle しない。case-1 では `hX_ac` から rnDeriv 経由で構成可能なので genuine に
閉じるのが目標。閉じられない field のみ park (撤退口 L-Prod-park)。

**Done 条件**: X / Y producer が type-check done。前提に `*Hypothesis` predicate が
含まれないこと (load-bearing bundling していないこと) を `rg` で確認。

### PB-4 — sum-instance producer (W=(Z_X+Z_Y)/√2 unit + time-reparam) (~60-120 行)

**スコープ**: `Z_X+Z_Y ∼ N(0,2)` は unit-hardcode `Z_law` と型不充足。
unit `W := (Z_X+Z_Y)/√2` を介し path-identification (PB-2) で構成。case-1 file に置く。

設計 (B-0 系に基づく):

```lean
/-- sum-instance producer。`Z_X+Z_Y ∼ N(0,2)` は unit-hardcode Z_law と不整合なので、
unit `W := (Z_X+Z_Y)/√2` を介し path-identification で `X+Y+√t·(Z_X+Z_Y)` を
`X+Y+√(2t)·W` と同一視して unit de Bruijn core に乗せる。
@residual(plan:epi-case1-debruijn-producer-plan) -/
theorem isDeBruijnRegularityHyp_sum_of_methodX_unitnoise
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (… measurability / IndepFun Z_X Z_Y / unit-noise laws / sum a.c. / sum 2次モーメント …) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
      (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P := by
  …
```

**重要な型整合課題 (B-0 末尾の系)**: `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` の
`reg_at t ht : IsRegularDeBruijnHypV2 (X+Y) (Z_X+Z_Y) P t` の `Z_law` は
`P.map (Z_X+Z_Y) = gaussianReal 0 1` を主張するが、実際は N(0,2) で **型不充足**。
path-identification は path (関数) を同一視するが、`Z_law` は noise `Z_X+Z_Y` の law を
**直接主張**するので reparam では救えない。

→ **2 つの sub-approach を PB-4 で評価** (skeleton で型確認してから確定):

- **(PB-4-α) `density_t` 形を v_Z=2 で pin**: `IsRegularDeBruijnHypV2` の `Z_law` が
  `gaussianReal 0 1` 固定なのが障害。だが `density_t_eq` (`EPIStamDischarge.lean:273`) は
  `density_t = density_path t` を pin するだけで、`density_path` は producer が自由に選べる。
  sum の真の density は `convDensityAdd pX_sum (gaussianPDFReal 0 ⟨2t,_⟩)` (Phase 1b v_Z=2)。
  問題は **`Z_law : gaussianReal 0 1` が型として N(0,2) と矛盾**する点 — これは
  `density_path` 選択では救えない。よって (PB-4-α) 単独では型不充足が残る。
- **(PB-4-β) structure を touch せず park**: 型不充足が structure の unit-hardcode に起因し、
  案B でも sum-instance のみ structure 改変なしには閉じられないと判明したら、**sum producer の
  `reg_at` を `sorry` + `@residual(plan:epi-case1-debruijn-producer-plan)` で park** (signature は
  producer 形を保つ)。X/Y producer (PB-3、unit-noise 直接) は genuine に閉じる見込みなので、
  proof done に届かないのは sum-instance のみ → type-check done で commit、proof done は
  次 wave。**この場合 structure 改変 (sum 専用 v_Z=2 受容形) を別 plan に切り出す closure 計画を
  判断ログに記録**。

**advisor 設計の正しい解釈**: advisor は「path-identification で chain factor を producer 内に
局所化」と述べたが、これは **X/Y (unit-noise) では完全に成立** (PB-3、そもそも reparam 不要)。
**sum-instance は `Z_law` が noise law を直接主張する構造的制約**で、path-identification だけでは
N(0,2)→unit に橋渡しできない (path は同一視できるが Z_law field が救えない)。PB-4 で
skeleton 型確認を最優先し、(α) で閉じなければ (β) で park し structure 改変を別 plan 化する。

**Done 条件**: sum producer が type-check done。(α) で genuine に閉じれば proof done 候補、
(β) park なら `@residual` 付き sorry + closure 計画を判断ログに記録。

### PB-5 — `h_pos_stam` producer (~40-80 行)

**スコープ**: wrapper の `h_pos_stam` bundle (`EPICase1RatioLimit.lean:1496-1518`) を
per-`t>0` で供給。各 conjunct と供給元:

| conjunct | 供給元 (file:line) |
|---|---|
| `0 < fisherInfoOfDensityReal (reg_*.density_t)` (×3) | conv-pin density の Fisher 正値性 (Gaussian-conv density a.e.>0 ⇒ Fisher>0、`FisherInfoV2` 系) |
| `IsStamInequalityHyp (X+√t·Z_X) (Y+√t·Z_Y) P` | `isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean:119`、sorryAx-free genuine) |
| `IsRegularDensityV2 (reg_*.density_t)` (×2) | conv-pin density regularity (`FisherInfoV2` 系) |
| `∫ density_t = 1` (×2) | conv density 正規化 (`hpX_mass` + Gaussian kernel 正規化、Phase 1b 資産) |
| sum conv-pin `density_t(sum) = convDensityAdd (density_t X) (density_t Y)` | Blachman conv identity |
| `IsBlachmanConvReady (density_t X) (density_t Y)` | `isBlachmanConvReady_convDensityAdd_gaussian` (genuine 既存) |

**注意**: bundle は `(h_reg_X'.reg_at t ht).density_t` を参照するので、PB-3/PB-4 producer が
返す instance の conv-pin density と **同一**でなければならない。PB-3 で
`density_path t := convDensityAdd pX g_t` (X/Y、v_Z=1)、PB-4 で sum を固定するので、PB-5 は
この具体形に対し Fisher>0 / IsRegularDensityV2 / 正規化を示す。PB-4 が (β) park の場合、
sum 系 conjunct (Fisher>0 sum / sum conv-pin) は sum producer の sorry に依存し transitive
sorry になる (compound `@residual` 検討)。

**Done 条件**: `h_pos_stam` producer が type-check done。Stam / Blachman conjunct が genuine
既存補題への delegation で閉じる (新 sorry なし) ことを確認。

### PB-6 — 最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise` (~20-40 行)

**スコープ**: PB-3/PB-4/PB-5 producer 群を restate 後 wrapper に注入する最終 wrapper を書く。

```lean
/-- **case-1 EPI、方針X (unit-noise) のみから (de Bruijn 群を producer で供給)**。
de Bruijn regularity 群は PB-3/PB-4/PB-5 producer が方針X (unit-noise) の前提から
discharge するので前提から消え、方針X (a.c. / 2次モーメント / unit Gaussian noise law /
4-tuple 独立) のみ残る。
@residual(plan:epi-case1-debruijn-producer-plan) -- producer の未閉 field (PB-4 sum) があれば -/
theorem entropyPower_add_ge_case1_of_methodX_unitnoise
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX hY hZX hZY : Measurable …)
    (hX_ac hY_ac hXY_ac : … ≪ volume)
    (h_mom_X h_mom_Y : Integrable (·²) P)
    (hZX_law : P.map Z_X = gaussianReal 0 1) (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_reg_X' := isDeBruijnRegularityHyp_of_methodX_unitnoise X Z_X P …
  have h_reg_Y' := isDeBruijnRegularityHyp_of_methodX_unitnoise Y Z_Y P …
  have h_reg_sum := isDeBruijnRegularityHyp_sum_of_methodX_unitnoise X Y Z_X Z_Y P …
  have h_endpt_X := …   -- IsHeatFlowEndpointRegular (既に一般 variance、v_Z:=1)
  have h_endpt_Y := …   -- v_Z:=1
  have h_endpt_sum := … -- v_Z:=2 (N(0,2) sum noise、structure は一般 v_Z)
  have h_pos_stam := …  -- PB-5 producer
  exact entropyPower_add_ge_case1_of_methodX X Y Z_X Z_Y P …
    h_reg_sum h_reg_X' h_reg_Y' h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
```

**`IsHeatFlowEndpointRegular` は障害なし**: 既に一般 variance (`EPIG2HeatFlowContinuity.lean:493`、
`v_Z:=v_X` 等を受容、`@audit:ok`)。case-1 では X→v_Z=1 / Y→v_Z=1 / sum→v_Z=2 を渡すだけ
(`EPIStamToBridge.lean:1435-1452` の既存 producer pattern を踏襲)。**de Bruijn group の
unit-hardcode は `IsRegularDeBruijnHypV2` 側のみ**で `IsHeatFlowEndpointRegular` には無い。

**命名 honesty**: `_unitnoise` は「noise を unit-variance に固定した case-1」を表す実態命名
(name laundering でない)。

**Done 条件**: 最終 wrapper の前提に `IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` /
`h_pos_stam` bundle が **含まれない**。`lake env lean` silent。PB-4 park があれば transitive
sorry (type-check done)、全閉なら proof done。

### PB-7 — incidental: `IsIBPHypothesis` retract (~5-10 行)

**スコープ**: `FisherInfoV2DeBruijnBody.lean:209` の `IsIBPHypothesis`
(`@audit:retract-candidate(name-laundering-alias)`、死 alias、consumer は `_h_ibp`
underscore-prefixed unused)。

**タイミング**: 案B は de Bruijn family を touch しないので、PB-7 は **独立 incidental** として
最後に行う (PB-1〜PB-6 完了後)。case-1 file の touch とは無関係だが本 plan scope 内で処理。

- [ ] `rg -n 'IsIBPHypothesis' InformationTheory/` で全 consumer 列挙
- [ ] 全 consumer が `_h_ibp` underscore unused であることを再確認
- [ ] declaration 削除 + consumer の unused 引数除去 (signature から落とす)

**Done 条件**: `rg "IsIBPHypothesis" InformationTheory/` が 0 hit (or bookkeeping コメントのみ)。
touched file 全て `lake env lean` silent。

### PB-V — verify + 独立 honesty audit (~5 行)

- [ ] touched file 全件 `lake env lean` silent
- [ ] `entropyPower_add_ge_case1_of_methodX_unitnoise` を `#print axioms` で確認:
  PB-4 sum park があれば `sorryAx` 残存 (type-check done)、全閉なら
  `[propext, Classical.choice, Quot.sound]` (proof done)
- [ ] **独立 honesty audit** (`honesty-auditor` subagent) を起動 (CLAUDE.md「Independent
  honesty audit」起動条件: 新規 `sorry` 導入 + PB-1 の wrapper signature 改変で honesty
  意味が変わる)
- [ ] audit verdict 確認:
  - wrapper restate (PB-1) が **vacuous defect を実体化**したか (v=1 固定で producer が
    実際に呼べる形になったか、`_unitnoise` 命名が name laundering でないか)
  - producer の `pX` series が **load-bearing bundling でない** regularity precondition か
  - PB-2 path-identification が **degenerate (v=0)** を突いていないか
  - PB-4 sum park (β の場合) の classification (`plan:epi-case1-debruijn-producer-plan` の
    正しさ + structure 改変 closure 計画の整合)

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。

---

## 撤退ライン

- **L-A-esc** (発火済): 案A (`Z_law` 値一般化) は値据置 = false statement、値一般化 = ratio
  core 偽化 (M0 落とし穴 / advisor Q1)。**案B にエスカレート済** (本改訂 plan)。案A への
  逆戻りは禁止 (数学的に通らない)。
- **L-Prod-park** (PB-3 段階): case-1 input density witness (`pX` series、特に `pX_mom` の
  2次モーメント push-forward / `pX_law` の rnDeriv 整合) が `hX_ac`/`h_mom_X` から genuine に
  組めない → 該当 field のみ `sorry` + `@residual(plan:epi-case1-debruijn-producer-plan)` で
  park (signature は producer 形を保つ)。`pX` series は regularity precondition なので最終
  wrapper の追加 precondition として外出しする選択肢もある (命名を実態に合わせる)。
- **L-Sum-struct** (PB-4 段階): sum-instance `Z_law` が N(0,2) を主張できず (unit-hardcode)、
  path-identification でも橋渡し不能と判明 (B-0 系) → sum producer の `reg_at` を `sorry` +
  `@residual(plan:epi-case1-debruijn-producer-plan)` で park。`IsRegularDeBruijnHypV2.Z_law` を
  **sum 専用に v_Z=2 受容形へ開く structure 改変**を別 plan に切り出す closure 計画を判断ログに
  記録 (案A の値一般化とは異なり、`Z_law` の noise-law field だけを general-variance 化し
  微分値 `(1/2)·J` は触らない — chain factor は producer 内 `density_t` に閉じるので ratio core
  偽化は起きない、B-0 系)。**この structure 改変は案A とは別物**: 案A は `density_t_eq` の
  conv-pin variance まで一般化して微分値が `(v_Z/2)·J` になるのが偽化原因、本 closure は
  `Z_law` field のみ開き conv-pin は reparam で unit 形に保つ。
- **L-Stam-deleg** (PB-5 段階): `h_pos_stam` の Fisher>0 / IsRegularDensityV2 / 正規化
  conjunct を既存資産に delegate できず新 sorry が必要 → 該当 conjunct を `sorry` +
  `@residual` で park。Stam / Blachman conjunct (genuine 既存) は park 不可 (delegate 必須)。

## Done 条件 (本 plan 全体)

- **proof done を目指す** (PB-4 sum が (β) park の場合は X/Y 系 proof done + sum
  type-check done): `entropyPower_add_ge_case1_of_methodX_unitnoise` の前提から de Bruijn
  regularity 群 (`IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` / `h_pos_stam`) が
  消え、方針X (unit-noise、+ density witness を残す場合は明示 regularity precondition) のみ残る
- producer X/Y (PB-3、unit-noise 直接) + sum (PB-4) + `IsHeatFlowEndpointRegular` 3 本
  (既存一般 variance に v=1/v=1/v=2 を渡すだけ) + `h_pos_stam` producer (PB-5) が genuine に
  閉じる (park field があれば `@residual(plan:epi-case1-debruijn-producer-plan)` で明示)
- PB-1 wrapper restate で latent v=1 vacuous defect が実体化 (unit 固定で producer が呼べる)
- PB-2 path-identification が degenerate (v=0) を突かない (`hv : 0 < v` 必須)
- touched file 全件 `lake env lean` silent
- `IsIBPHypothesis` retract 済 (PB-7、`rg` 0 hit)
- 独立 honesty audit (`honesty-auditor`) verdict 全 OK
- **honesty 不変条件**: producer の前提に load-bearing `*Hypothesis` predicate を bundling
  しない。time-reparam `t→t·v` の `v=0` / `Y:=0` 退化を突く degenerate-definition exploitation
  を作らない (CLAUDE.md L-DBD 前例: 退化 measure で gap が constant 化し trivially AntitoneOn に
  なる exploitation を避ける、time-reparam では v>0 厳格化 + noise が結論に現れない構造で回避)

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1470` — wrapper
  `entropyPower_add_ge_case1_of_methodX` (PB-1 restate 対象、producer の consumer)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1488-1518` — wrapper の de Bruijn
  regularity 群 前提 (producer で discharge する対象)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1481-1483` — wrapper の v_X/v_Y 任意
  noise law (latent v=1 vacuous defect の所在、PB-1 で unit 固定)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1343` — `entropyPower_add_ge_case1_of_regular`
  (PB-1 で v=1/v=1/v=2 渡しに更新、§3/§4 side は v 任意で動く)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:293` — `entropyPower_rescaled_path_tendsto`
  (§3 saturation、一般 v_B を取る `:296`、unit-noise 固定後も v=2 sum で動く)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:127` — `gaussianConvolution`
  def (`X + √t·Z`、PB-2 path-identification の代数基底)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:205-288` — `IsRegularDeBruijnHypV2`
  structure (`Z_law : gaussianReal 0 1` が :210、**案B は無改変**、sum-instance 型不充足の根源)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnGenuine.lean:51` — `deBruijn_identity_v2`
  (consumer、`(1/2)·J(density_t)` 微分値、unit-noise core)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:80` —
  `gaussianConvolution_law_conv` (一般 v_Z、sum の v_Z=2 conv に使用)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:215` — Phase 1b
  `pPath_eq_convDensityAdd` (一般 v_Z、PB-3/PB-4 conv-pin の整合先)
- `InformationTheory/Shannon/EPIStamDischarge.lean:251-288` — `IsDeBruijnRegularityHyp`
  structure (producer で構成する対象、`reg_at` 経由 unit `Z_law` 継承)
- `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:488` — `IsHeatFlowEndpointRegular`
  structure (既に一般 `v_Z`、`@audit:ok`、PB-6 で v=1/v=1/v=2 を渡すだけ、障害なし)
- `InformationTheory/Shannon/EPIStamToBridge.lean:699` — `csiszarLogRatioGap_hasDerivAt`
  (`deBruijn_identity_v2 X Z_X` を呼び `(1/2)·J` を得る、ratio core への入口、unit-noise 前提)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1085` — `csiszarLogRatioGap_antitoneOn_Ici_zero`
  (ratio antitone、同 de Bruijn group 前提、latent v=1 制約共有)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1346,1352-1353` —
  `isStamToEPIScalingHyp_of_stam_debruijn` (`h_reg` が `gaussianReal 0 1` unit-noise を明示要求、
  EPI 一般 line が de Bruijn group level で unit-noise 前提の verbatim 証拠 = PB-1 推奨根拠)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular`
  producer 既存 pattern (X→v_Z=1 / Y→v_Z=1 / sum→v_Z=2、general-variance 構築 prior art)
- `InformationTheory/Shannon/EPIL3Integration.lean:1380` — `csiszarLogRatioGap` def
  (path `X+√t·Z_X` を名指す、PB-1 restate 後も Z_X thread で不変)
- `InformationTheory/Shannon/EPIStamStep3Body.lean:119` — `isStamInequalityHyp_via_step3`
  (`h_pos_stam` の Stam conjunct、genuine sorryAx-free)
- `InformationTheory/Shannon/FisherConvBound.lean:385` — `gaussianConv_fisher_le_inv_var`
  (`integrable_deriv` の Fisher 有界性、`wall:fisher-finiteness` CLOSED 資産)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:209` — `IsIBPHypothesis`
  (PB-7 retract 対象、死 alias)
- `.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:352` — `Real.sqrt_mul`
  (PB-2 path-identification の `√(t·v)=√t·√v`)
- `docs/shannon/epi-case1-debruijn-producer-fork-sizing.md` — advisor verdict (案A revert /
  案B chain factor 解析 / Q1-Q3、本改訂の根拠)
- `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` — EPI 一般 line 側 density witness park の
  owner plan (case-1 と同 owner の input density precondition)
- `docs/audit/audit-tags.md` — `@residual` 語彙 / Wall register (de Bruijn 系壁 CLOSED 状態)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草時 — 案A 確定 (旧)**: M0 案D 調査で「de Bruijn density-level core は
   v_Z-agnostic」を確認、案A (`Z_law` を `gaussianReal 0 v_Z` 一般化) を採用。blast radius
   6-8 decl 想定。

2. **2026-06-05 — 案A REVERT (L-A-esc 発火) → 案B 採用 🔄**: fork-sizing advisor verdict
   (`epi-case1-debruijn-producer-fork-sizing.md`) で案A の致命的欠陥が判明。M0 は density-level
   core の v_Z-agnostic を正しく確認したが、**de Bruijn 微分値 `(1/2)·J` の v_Z 依存を見落とし**:
   一般 v_Z では chain rule で genuine 微分値が `(v_Z/2)·J(at s·v_Z)` になる。案A (値据置) は
   false statement (tier 5 degenerate)、案A-corrected (値一般化) は ratio core
   `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`、harmonic-Stam arith) が
   項毎 v_Z factor (v_X/v_Y/v_X+v_Y 非一律) で **偽化** (advisor Q1)。
   → 正しい一般化は「**値ではなく path を unit 形に reparam して吸収**」(案B)。本 plan を
   案B (noise 標準化 `Z':=Z/√v` + time-reparam) に全面改訂。旧 P-0〜P-2 (Z_law 一般化) を
   PB-1〜PB-6 (wrapper restate + path-identification + unit-noise producer) に置換。

3. **2026-06-05 — B-0 path-identification 代数確認 (advisor 第一手)**: `gaussianConvolution X Z' (t·v)
   = gaussianConvolution X Z t` (Z'=Z/√v、v>0、t≥0) は **点ごと厳密恒等式** であることを verbatim
   確認 (`gaussianConvolution` def `:127` + `Real.sqrt_mul` `Mathlib/Data/Real/Sqrt.lean:352` の
   `√(t·v)=√t·√v` + `√v≠0`)。a.e. ですらなく everywhere 成立。chain factor は producer 内の
   `density_t` に局所化され ratio core に到達しない (B-0 系)。ただし **X/Y は restate 後 unit-noise
   なので reparam すら不要**、time-reparam が要るのは sum-instance (N(0,2)) のみ。

4. **2026-06-05 — B-0' wrapper latent defect 解消方針 = (a) wrapper restate**: wrapper が
   v_X/v_Y 任意 noise を取りながら de Bruijn group (unit `Z_law` hardcode) を要求するのは
   **v_X≠1 で vacuously true (latent defect)**。3 択評価で (a) unit-noise 固定 restate を推奨:
   noise は結論に現れない補助変数 (`EPICase1RatioLimit.lean:1519`) で unit 固定は一般性を失わない、
   EPI 一般 line が既に de Bruijn group level で unit-noise を要求 (`isStamToEPIScalingHyp_of_stam_debruijn`
   の `h_reg` precondition `gaussianReal 0 1`、`EPIStamToBridge.lean:1352`)、structure 無改変。
   (c) 現 wrapper 維持 + producer reparam は **不可能** (path-identification は path を同一視するが
   `Z_law` は noise law を直接主張するので v_X≠1 を救えない、B-0 末尾の系)。

5. **2026-06-05 — sum-instance の構造的制約を明示 (PB-4 / L-Sum-struct)**: sum-instance
   `Z_X+Z_Y ∼ N(0,2)` は `IsRegularDeBruijnHypV2.Z_law : gaussianReal 0 1` (unit-hardcode) と
   型不充足。path-identification は path を unit-W 形に同一視できるが、`Z_law` field が noise
   `Z_X+Z_Y` の law を直接主張するため reparam で救えない。PB-4 で skeleton 型確認を最優先し、
   閉じなければ (L-Sum-struct) sum producer の `reg_at` を park し、`Z_law` field のみ
   general-variance 化する structure 改変 (案A とは別物: conv-pin variance は触らず微分値 `(1/2)·J`
   を保つので ratio core 偽化は起きない) を別 plan に切り出す。
