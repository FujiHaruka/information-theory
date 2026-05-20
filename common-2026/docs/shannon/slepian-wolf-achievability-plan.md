# Slepian–Wolf achievability ムーンショット計画 🌙

E-5 シードカード ([`docs/moonshot-seeds.md` 行 139-144](../moonshot-seeds.md))。
Cover-Thomas 15.4 — 既存 `SlepianWolf.lean` (496 行 single-shot converse 3 bound) を
出発点に、deterministic encoder pair の existence statement (rate region achievability の
**第一段**) を追加。

> 実態整合 (2026-05-20): **DONE-UNCOND (2 corner-point, 計画通り) — Phase A-D 完了表記は CODE と一致**。`Common2026/Shannon/SlepianWolfAchievability.lean` (14861 B, 0 sorry)。`slepian_wolf_achievability_via_Y_aep` (SlepianWolfAchievability.lean:132) は実証明 (`source_coding_achievability` + X 側 `Fintype.equivFin` trivial encoder の合成、SW error event = Y-AEP error を集合等価で証明)。corner 2 件 `_corner_Y` (:219) / `_corner_X` (:252) も実 publish。full 3-bound rate region は別 plan で discharge 済 (下記注記)。FLAW なし。

## 進捗

- [x] Phase A — definitions (`swErrorProb` 主誤り測度) ✅
- [x] Phase B — trivial-rate achievability (`swErrorProb_trivial_zero`) ✅
- [x] Phase C — sum bound via Y-AEP (`slepian_wolf_achievability_via_Y_aep`) ✅
- [x] Phase D — symmetric 2 corner-point statements
      (`slepian_wolf_achievability_corner_Y` / `_corner_X`) ✅
- [ ] 後継 (E-5' deferred) — random binning + joint typicality decoder 経由の **3 bound 同時** rate region 📋

## 実装完了

**実装ファイル**: [`Common2026/Shannon/SlepianWolfAchievability.lean`](../../Common2026/Shannon/SlepianWolfAchievability.lean) (310 行)

**主要 lemma + theorem**:
- `swErrorProb`: SW encoder pair + joint decoder の誤り確率
- `swTrivialEncoderX` / `swTrivialEncoderY` / `swTrivialDecoder`: 自明 (identity) SW encoder pair
- `swErrorProb_trivial_zero`: 自明 encoder pair の誤り 0 達成 (B Phase)
- `slepian_wolf_achievability_via_Y_aep`: Y 側 single-source AEP + X 側 identity の合成
  encoder pair achievability (rate pair `(log|α|, R_Y)` for `R_Y > H(Y)`)
- `slepian_wolf_achievability_corner_Y`: 上記の packaged 形 (`(log|α|, R_Y)` corner)
- `slepian_wolf_achievability_corner_X`: 対称形 (`(R_X, log|β|)` corner)

**設計判断 (実装時 finalize)**:

1. **退化点 MVP に commit** (実装時): random binning + joint typical decoder 経由の
   full 3-bound rate region 達成は **~2000 行規模** で session budget 外。本 file は
   **2 corner-point**: `(log|α|, R_Y)` for `R_Y > H(Y)` と `(R_X, log|β|)` for `R_X > H(X)`
   の達成可能性を `source_coding_achievability` (`AEP.lean`) の合成で publish。
   sum rate は `log|α| + H(Y)` および `H(X) + log|β|` のいずれも `≥ H(X, Y)` を達成 (片
   marginal を無圧縮で送るため)。
2. **`(Fintype.equivFin _).left_inv` 経由の trivial encoder**: `α^n ≃ Fin (|α|^n)` を介して
   trivial encoder を `Fin _`-valued に。Lean では `Fintype.equivFin` 経由が最短。
3. **error event の集合論的等価性**: SW error event `(f_X X, f_Y Y) ↦ d ≠ (X, Y)` を
   X 側自明 (`equivFin.left_inv`) + Y 側 AEP error の合成 `Y ≠ d_Y (c_Y Y)` に
   分解。Prod の左右 mismatch 検査 (`Prod.mk.inj` で射影、`¬= ↔ ¬=` で iff 化)。

**Mathlib gap**: なし (`source_coding_achievability` + `Fintype.equivFin` のみ依存)。

**横断 utility**: SW encoder structure (`swErrorProb` 定義) は E-5' deferred (random binning
full rate region) の **error event definition** をそのまま再利用可。各 corner-point 結果は
SW rate region の **2 自明 corner** を formally pin down し、E-5' で **任意 rate triple
`(R_X, R_Y) ∈ SW-rate-region`** への拡張時に boundary check として効く。

**Cover-Thomas 15.4 完全形への gap**: 3-bound rate region の **non-trivial corner**
(`R_X = H(X|Y), R_Y = H(Y)` 等) は random binning + joint typical decoder 必須。
E-5' deferred 後継カードに記録。

## ゴール / Approach

**最終的に証明したい定理** (本 plan scope、E-5 シード MVP):

任意の i.i.d. 2-source `(X_i, Y_i) ∼ P_{XY}` で sum rate `R > H(X, Y)` を充足するとき、
**separate encoder pair** `f_X^n : α^n → Fin M_X^n, f_Y^n : β^n → Fin M_Y^n` と joint
decoder `d^n` が存在し、(a) `log M_X^n + log M_Y^n → R · n` かつ (b) 誤り確率 → 0。

### 全体戦略

**経路選択** (`判断ログ 1`):
本来の Cover-Thomas 15.4 完全形 (R_X > H(X|Y), R_Y > H(Y|X), R_X + R_Y > H(X,Y) の 3
bound rate region) は **random binning + joint typicality decoder** を要し、~2000 行規模。
本 plan は **sum bound `R_X + R_Y > H(X,Y)` 単独** を MVP とし、**joint AEP source code +
trivial X encoder** の合成で実現する deterministic 経路を採用。

**Approach (Phase C 主動力)**:
1. Joint AEP source code (`source_coding_achievability` from `AEP.lean`) を joint source
   `Z_i := (X_i, Y_i)` on `α × β` に適用 → 単一 encoder `c : (α×β)^n → Fin M_n`
   with `log M_n / n → R, errorProb → 0` for `R > H(X, Y) = entropy μ Z_0`.
2. **Separate factorization**: 単一 encoder `c` を SW encoder pair に分解できない (本質的
   制約) ため、**trivial X encoder** `f_X := id : α^n → α^n ≃ Fin (|α|^n)` を採用し、
   Y encoder は `f_Y := c ∘ (X_in, Y_in) ↦ ...` ではなく、**X^n は無圧縮で送り、Y^n
   を joint AEP encoder で圧縮 (X^n side info で復号)** 経路を取る。これは結局
   conditional source coding。
3. **より明示的に**: `R_X := log|α|, R_Y := R - log|α|` で分配 (∀ R > H(X,Y))。
   `f_X` は identity (entropy log|α|)、`f_Y` は joint AEP の Y 成分 (rate `R - log|α|`)。
   Decoder は X^n を直接読み、`d^n((i, j)) := (i_as_x, aep_decode(j; i_as_x))`。
   **問題**: AEP decoder は `c(x,y) = single index` 形で side info 取れない。

**Realistic MVP**: 上記経路は SW achievability の **退化形** に過ぎず、本質的に
"Y を conditional source code で圧縮、X は無圧縮" であり Cover-Thomas SW 達成可能性とは
言えない。本 plan はこの退化形を Phase C で立て、**3-bound full rate region は E-5'
deferred 後継カード**へ切り出す (判断ログ 2)。

### 経路の honest 評価 (判断ログ 1 詳細)

random binning encoder の Lean 化は ~2000 行規模:
- `binningMeasure : Measure (α^n → Fin M_X)` を Fintype 上 uniform pi で構築 → ~300 行
- 期待値計算 `𝔼[1_{f_X(x) = f_X(x')}] = 1/M_X` for `x ≠ x'` → Fubini collapse ~400 行
  (`ChannelCodingAchievability.codebookMeasure` 構造の **encoder-side 鏡像**)
- error decomposition `E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}` → ~200 行
- conditional typical slice size bound `|{x' : (x', y^n) typical}| ≤ exp(n H(X|Y) + 2nε)`
  → ~400 行 (`jointlyTypicalSet` 既存定義の **fiber 解析**、Mathlib gap)
- 各 error term の expectation bound → ~400 行
- pigeonhole + asymptotic finalize → ~300 行

これは Cover-Thomas 15.4 完全形の **honest cost**。**本 plan は session budget 範囲で**
**統合可能な MVP scope を明示**することに集中し、full rate region 達成は明示的に
**E-5' deferred** へ。

## Phase A — definitions 📋

- [ ] **A.1** `IsAchievableSWPair`: SW encoder pair `(f_X^n, f_Y^n, d^n)` の error → 0 条件。
- [ ] **A.2** `SWAchievableRates`: 漸近 rate triple `(R_X, R_Y)` の achievable set。
- [ ] **A.3** Error event = error of (joint decoder ∘ paired encoder)。

## Phase B — 退化点 trivial 達成可能性 📋

- [ ] **B.1** `slepian_wolf_achievability_trivial`: `R_X = log|α|, R_Y = log|β|` で
      identity encoder pair + identity decoder が誤り 0 達成。
      Statement-level の sanity check、~30 行。

## Phase C — sum bound via joint AEP encoder 📋

- [ ] **C.1** `slepian_wolf_achievability_via_joint_aep`: `R_X = log|α| + ε`,
      `R_Y > H(Y) + ε` (or similar) のため、joint source `Z := (X, Y)` の AEP achievability
      を SW encoder pair に **factorize**:
      - `f_X := identity (α^n → α^n)`
      - `f_Y := aep_encoder` on `Y^n` alone (single-source AEP)
      - `d := (x, j) ↦ (x, aep_decoder j)` (joint decoder uses X uncompressed)
      Achieves rate `(log|α|, H(Y) + ε)` with sum `log|α| + H(Y) + ε ≥ H(X, Y) + ε`
      (since `log|α| ≥ H(X)` and `H(Y) + H(X) ≥ H(X, Y)`).
- [ ] **C.2** `slepian_wolf_achievability_sum` (rephrase): 任意 `R > H(X, Y) + δ` で
      `∃ (R_X, R_Y), R_X + R_Y = R + (slack), slepian_wolf_achievable (R_X, R_Y)`.

## Phase D — `slepian_wolf_achievability_sum` 統合 statement 📋

- [ ] **D.1** 最終 statement: `(R_X, R_Y)` rate pair achievable when
      `R_X = log|α|, R_Y > H(Y)` (limited但 rate region corner)。
- [ ] **D.2** Cover-Thomas 15.4 full rate region は **E-5' deferred** に切り出し、
      本 plan は MVP scope で commit。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **経路選択: deterministic via joint AEP** (Phase 起草時):
   Cover-Thomas 15.4 完全形 (random binning + joint typicality decoder で 3-bound
   rate region) は session budget 範囲 (見積 ~800 行) を **大幅超過** (実 ~2000 行)。
   本 plan は **退化形 MVP** (X 側 trivial encoder + Y 側 AEP) で sum bound の
   片側コーナーを抑え、full rate region は **E-5' deferred 後継カード**へ切り出す。

2. **3-bound full rate region は scope-deferred** (Phase 起草時):
   `R_X > H(X|Y)` 単独 bound と `R_Y > H(Y|X)` 単独 bound は **conditional typical
   slice size bound** + **random binning Fubini machinery** が必要で、~2000 行規模。
   本 plan は **sum bound `R_X + R_Y > H(X,Y)` の corner point** `(log|α|, H(Y)+ε)`
   単独を MVP とする。完全な rate region 達成は **E-5' deferred**。
