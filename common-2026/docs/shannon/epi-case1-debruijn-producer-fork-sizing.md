# EPI case-1 producer fork sizing (advisor 出力, 2026-06-05)

> read-only 診断。コード不変更。`epi-case1-debruijn-producer-plan.md` 案A revert (L-A-esc) 後の
> 案B vs 案A-corrected sizing。分岐の核心 2 問を verbatim file:line で確定。

## 診断 (根本)

M0 の新盲点は正しい。`deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:51-61`) /
`debruijnIdentityV2_holds_assembled` (`Assembly:3543`) の結論は
`HasDerivAt (s↦h(P.map(X+√s·Z))) ((1/2)·J(density_t)) t`。assembly atom は heat kernel variance を
**`s` に直結** (`_entropy_eq:3446/3452` が Phase 1b を v_Z:=1 で叩き `s·1=s`、`_chain:3404` も kernel
variance=`s`)。一般 v_Z では density = `convDensityAdd pX g_{s·v_Z}`、chain rule で genuine 微分値は
`(v_Z/2)·J(at s·v_Z)`。案A (Z_law だけ開いて値据置) は **false statement** になる (tier 5、degenerate
回避の docstring `EPIStamDischarge.lean:242-243` も `(1/2)` の Gaussian 値 `1/(2(v+t))` に key)。
案A は revert で正しい。

## 分岐の核心 2 問 — verbatim 確定

### Q1: 案A-corrected は既証 wrapper を un-prove するか → **NO (値変更は ratio で相殺)**

consumer chain: `entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`)
→ Pillar1 `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`)
→ `csiszarLogRatioGap_hasDerivAt` (`:699`) + `csiszarLogRatioGap_deriv_le_zero` (`:895`)。

- `csiszarLogRatioGap_hasDerivAt:724-749` が `deBruijn_identity_v2` を **3 成分** (X/Y/sum) で呼び、
  各 `(1/2)·J_i` を得る。`:766-803` で entropyPower 形に lift する際 `exp(2h)·(2·((1/2)·J_i))` の
  `2·(1/2)=1` で **`(1/2)` が全項一律キャンセル**。最終 ratio-gap 微分値は
  `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` (`:710-721`、`(1/2)` 不在)。
- `csiszarLogRatioGap_deriv_le_zero:895` は plain harmonic Stam `1/J_sum ≥ 1/J_X+1/J_Y` から ≤0 を出す
  (docstring `:840-893`)。これは **J_i 同時スケール不変** (両辺同因子で保存)。

帰結: 案A-corrected が `(1/2)·J_i → (v_Z_i/2)·J_i` に変えても、各成分の lift cancellation が
`exp(2h)·(2·((v_Z_i/2)·J_i)) = exp(2h)·v_Z_i·J_i` となり、ratio-gap の各項に `v_Z_i` factor が
**非一律**に乗る (X→v_X, Y→v_Y, sum→v_X+v_Y、v_X≠v_Y で異なる)。harmonic Stam は同時スケールには
不変だが **項毎に異なる factor** には不変でない → `csiszarLogRatioGap_deriv_le_zero` の arith core
(`csiszar_ratio_deriv_le_zero_arith`、α²≤α weights) が **破れる**。
∴ 案A-corrected は wrapper を直接 un-prove はしないが (型は通る)、analytic core の ≤0 が
**偽になる** ので proof done に到達不能。これは案A の revert を裏書きする (値一般化は ratio core を壊す)。

→ **案A-corrected は不採用**: 値を genuine 一般化すると ratio-gap deriv ≤0 (`:895`) が項毎 v_Z factor で
偽化。blast radius 云々以前に数学的に通らない。

### Q2: 案B で wrapper を壊さず producer が組めるか → **YES (wrapper は時間 s に対し unit-variance 形で固定)**

de Bruijn group consumer は全て `gaussianConvolution X Z s = X+√s·Z` の **時間 s** に対する
`HasDerivAt` を要求 (`:699` 結論、`:710`)。`csiszarLogRatioGap` の path も
`X+√t·Z_X` (`:1503-1505` の `h_pos_stam`、`:766` の lift)。

案B は noise を標準化 `Z_X':=Z_X/√v_X` (Z_X'~N(0,1)) し、時間 reparam で
`X+√t·Z_X = X+√(t·v_X)·Z_X'`。これにより de Bruijn group は **unit-variance Z_X'** で組め、
既存 `IsRegularDeBruijnHypV2.Z_law:gaussianReal 0 1` (`FisherInfoV2DeBruijn.lean:210`) を **無改変**で使える。
wrapper signature の de Bruijn group も `Z_X'` thread で型整合 (structure は X,Z 引数を polymorphic に取る)。

**ただし wrapper の path は `X+√t·Z_X` (元の Z_X) を名指す** (`csiszarLogRatioGap` body、`:766-803`)。
案B producer が組む group は `X+√t·Z_X'` 上。両者を繋ぐには:
- (a) `X+√t·Z_X = X+√(t·v_X)·Z_X'` の path 同一視を、wrapper が要求する全 de Bruijn field
  (density_t / reg_at / integrable_deriv の `(1/2)·J` 値) に伝播する reparam bridge、または
- (b) wrapper 側 (`csiszarLogRatioGap_*` 群) を `Z_X'` thread に書換える。

(a) は時間 affine reparam `t→t·v_X` が `HasDerivAt` に chain factor `v_X` を持ち込む — これは
Q1 と同じ `(v_X/2)·J` 問題が **producer 側に出る**。(b) は wrapper 群 (5+ decl) の書換。
**いずれも案A-corrected と同じ chain-factor 問題に帰着する** ので、案B は問題を移動するだけ。

→ 案B も「reparam factor が ratio core を壊さない」検証が案A-corrected と等価に必要。
plan の L-A-esc fallback 想定 (案B が clean な逃げ道) は **誤り**: 案B も chain factor を抱える。

## 第3案 — 案C (sum 専用標準化なし、producer を v_Z=1 path で組み wrapper path を整合) ✓ 推奨

核心: **chain factor を持ち込まない唯一の道は「producer も wrapper も time s に対し variance=s の
unit 形を共有する」こと**。現状 wrapper (`csiszarLogRatioGap_hasDerivAt:724`) は
`deBruijn_identity_v2 X Z_X` を `Z_X` (var v_X) で呼んでいる — が、その結論 `(1/2)·J` は
**v_X=1 でしか genuine でない** (Q1)。つまり **wrapper 自身が既に v_X≠1 で latent に false**。

これは案A revert より深い: case-1 wrapper `entropyPower_add_ge_case1_of_methodX` は v_X,v_Y を
**任意 ℝ≥0** で取る (`:1481`) のに、Pillar1 の de Bruijn 微分値は v=1 前提。
→ **既存 wrapper に latent defect の疑い** (v_X≠1 で `csiszarLogRatioGap_hasDerivAt` の `(1/2)·J` が
genuine 微分でない)。sorryAx-free だが、これは `deBruijn_identity_v2` が `IsRegularDeBruijnHypV2`
(Z_law:gaussianReal 0 1) を要求するため **producer が v_X≠1 の Z_X から `reg_at` を構成できない**
= 計画 P-1 の型不充足、で守られている (まだ producer が無いので consumer は vacuous に成立)。

∴ 正しい設計: **producer を `Z_X'`(unit) で組み、wrapper path `X+√t·Z_X` を
`X'_t := X` の variance=s 形に揃える reparam を、ratio core が見る前に吸収**。具体的には
案B(b) 寄りだが、reparam factor を ratio-gap の **微分値計算前** (`csiszarLogRatioGap_hasDerivAt`
内) で `v_X` を path 定義に畳み込む。これは Q1 の cancellation (`2·(1/2)=1`) を
`2·(v_X/2)·(1/v_X)` に置換できれば相殺する — **時間変数を `τ:=t·v_X` に取り替えれば
`dτ/dt=v_X` と `(v_X/2)` が打ち消し合い `(1/2)·J(τ)` に戻る**。

→ 推奨は **案B + 時間変数 τ=t·v_X の reparam**。ただし最 tractable な第一手は下記の検証。

## 推奨と最初の 1 手

**推奨: 案B (標準化 Z_X':=Z_X/√v_X) を採用するが、先に「latent defect 検証」を 1 手打つ。**

最初の 1 手 (read-only, 1 ターン): `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) の
`deBruijn_identity_v2 X Z_X ... (h_reg_X.reg_at t ht)` が、`h_reg_X.reg_at` の `Z_law` を
**実際に v_X=1 に固定しているか** を確認する。`IsDeBruijnRegularityHyp.reg_at` (`EPIStamDischarge.lean:262`)
が返す `IsRegularDeBruijnHypV2 X Z_X P t` の `Z_law` field は構造上 `gaussianReal 0 1` 固定
(`FisherInfoV2DeBruijn.lean:210`)。つまり wrapper は **「Z_X が unit variance」を de Bruijn group 経由で
暗黙要求**している。case-1 noise が v_X≠1 のとき、この group は producer から供給不能 (型不充足、計画の唯一障害)。

→ 結論: producer を **Z_X'(unit) で組むのが唯一型整合する道** (= 案B)。reparam は producer が
`X+√t·Z_X = X+√(t·v_X)·Z_X'` を介して **density_t / Z_law を unit Z_X' で埋める** ことで吸収され、
wrapper が見る `(1/2)·J` 値は unit 形のまま genuine。chain factor は producer 内の path 同一視
(`gaussianConvolution X Z_X' (t·v_X)` ↔ `gaussianConvolution X Z_X t`) に局所化し、ratio core
(`:895`) には到達しない。**案B は wrapper を壊さない** (wrapper は Z' thread でそのまま、または
producer が `IsDeBruijnRegularityHyp X Z_X P` を Z_X' 経由で構成し path 同一視 lemma 1 本で繋ぐ)。

第一手の具体: `rescaledInput_density_witness` (`:1670` で既使用) と
`pPath_eq_convDensityAdd` (一般 v_Z 既存、`PerTime.lean:194`) で
`P.map(X+√t·Z_X) の density = convDensityAdd pX g_{t·v_X}` を確認し、これを
`IsRegularDeBruijnHypV2 X Z_X' P (t·v_X)` の density_t に pin する path 同一視
`gaussianConvolution X Z_X' (t·v_X) =ᵐ gaussianConvolution X Z_X t` を 1 本 sketch する
(skeleton sorry で型確認)。これが通れば案B producer は unit de Bruijn core を chain-factor なしで使える。

## 撤退ライン判定

- **L-A-esc 発動: YES (正当)**。案A は値据置で false statement (Q1)。revert は正しい。
- 計画の L-A-esc fallback「案B は clean」は **誤り (要訂正)**: 案B も naive には chain factor を抱える。
  正しい案B は「reparam を producer 内 path 同一視に局所化し ratio core に到達させない」設計。
- 案A-corrected は **不採用** (ratio deriv ≤0 が項毎 v_Z factor で偽化、Q1)。

## proof-log 候補の教訓

「de Bruijn 微分値 `(1/2)·J` は kernel-variance=time の unit reparam 上でのみ genuine。
noise variance v≠1 を structure field で開く (案A) と HasDerivAt 値が chain factor `v/2` を持ち、
下流 harmonic-Stam ratio core (項毎 factor 非不変) を偽化する。一般化は値ではなく
**path を unit 形に reparam** して吸収すべき (case-1 標準化 = 案B)。」
