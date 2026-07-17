# Shannon-Hartley operational capacity closure ムーンショット計画 🌙

**Status**: 🔧 **def-fix 済 → 壁 gated（2026-07-17、leg 14、commit `4fd8a47c`、監査 all OK）**。
3 宣言（`contAwgn_eq_shannonHartley` / `contAwgnMaxMessages_bddAbove` / `contAwgn_ge_shannonHartley`）は
**false-as-framed だった**（leg 12）が、子 plan の **Leg P で修理済**。`@residual(defect:false-statement)` は
3 本とも離脱し、`@audit:defect` は消滅。**mainline は「偽」ではなく「壁 gated」に戻った** — ただし
2026-07-15 の壁 gated 判定とは**別物**（あちらは偽の def に対する誤判定だった）。

**根本原因（leg 13 の Leg 0 gateway で*入れ替わった*）**: `ContAwgnCode.encoder_power` の窓限定ではなく
**観測写像** `sampledSignal` + `errorProbAt` だった（`cause:signature-drops-constraint` の帰属先も訂正）。
**修理 = Proposal O**（点標本 → `[0,T]` 台の正規直交テスト関数 = Karhunen-Loève 展開。`encoder_power` の
全直線化はその一部）。証拠・機序・数値・教訓 → [`shannon-hartley-facts.md`](shannon-hartley-facts.md)
**§OBSERVATION-MAP**。**def の現物がコード側 SoT — ここに field を再キャッシュしない**。

**`wall:nyquist-2w-dof` は live consumer 2 に復活**（`eq` + `ge`）。**これは Leg P が偽装でなく修理だった
機械的証拠** — def-fix 後も主定理は `≈2WT` DOF カウントを要する（壁が消えていたら Leg 0 差し戻しだった）。
**Legs A/B/C/C' の作用素資産（`TimeBandLimiting.lean`）は本 refutation の影響を受けない**（有効資産、破棄しない）。

**🎉🎉 leg 17 = 壁が名指していた命題そのものが CLOSED。leg 18 = R4-gate A1 gateway PASS + R4-ACH-B（実基底）も CLOSED。次 = R4-ACH-A2（設計判断: 実固有基底 or 作用素下界で再定式化）。**
`wall:nyquist-2w-dof` の named proposition = **固有値集中は実定理として着地**（sorryAx-free、監査 all OK）:
`prolateCount_le : (prolateCount T W c : ℝ) ≤ 2WT + (2 + log(1+2WT))/c`（`0 < c`）/
`le_prolateCount : 2WT − (2 + log(1+2WT))/(1−c) ≤ prolateCount T W c`（`0 < c < 1`）
（`65897bdb`、監査 `43e473e3`）。**`c` は自由・`D` は明示** = converse（`c→0`）と achievability（`c→1`）の
両方が引ける強度。R3（`ec0553a6`）で 3 docstring を実名へ張り替え = **指示対象なき名前は消滅**。
**R1（固有基底 + 多重度 bridge）は DEAD** — 要らなかった（`prolateCount := finrank ℂ V` ゆえ多重度 bridge は
**構成上存在しない**。`Spectrum.lean:443` は atom / R2 両半分から 0 回消費 = positive control 付き probe で 2 度確認）。
**⚠️ 残 sorry 2 本（`eq`:477 / `ge`:725）は落ちていない** — 残渣は count の**下流 = R4 operational bridge**。
⟹ **`wall:nyquist-2w-dof` のタグ class は misclassified の疑いが leg 18 で強化**（named proposition は閉じ、
A1 = plumbing 実測、有限 V-固有基底は in-tree、C3 は in-tree）。**残る唯一の未 gateway-test = C1（converse interlacing）**。
C1 PASS で 2 consumer を `plan:` へ再分類 license（code 編集 = subagent + 独立 honesty-auditor）。**次 leg で判断**（下記）。
**Leg 0（gateway）✅（leg 13）→ Leg P（def-fix）✅（leg 14、`4fd8a47c`）→ Leg D'（BddAbove）✅ PROOF-DONE
（leg 14、`fb18b681`）→ Leg E-atom ✅ / E-trace ✅（leg 15）→ Leg E-sharp ✅（leg 16）**。
**⚠️ `ge` は Leg D' では閉じなかった**（旧計画の「`le_csSup` で transitive に closure」は def-fix 前の線 = 失効）—
achievability は ≈2WT 次元の構成を要し **`eq` ともども Leg E 系列待ち**。子 plan の「DAG 訂正」節が SoT。

**壁論拠は 3 度誤っていた（結論だけが生き残ってきた）**。台帳 **§SPECTRAL-ASSETS** が SoT:
1. 「無限次元スペクトル理論が Mathlib に無い」→ **誤り**（`Spectrum.lean:443` に存在。leg 15 が grep で反証）
2. 「trace 等式にスペクトル定理が要る」→ **誤り**（Parseval は任意の完全基底で効く。leg 15）
3. 「残渣 = Landau-Widom（鋭い漸近等式）」→ **枠付けが強すぎた**（leg 16）。consumer が要するのは
   **緩い片側上界のみ**で、`0 ≤ λ ≤ 1` + `tr A = 2WT` 厳密値 + 片側上界 `D` から Chebyshev 分割が
   `2WT − D/(1−c) ≤ #{λ>c} ≤ 2WT + D/c` の**両半分**を出す（監査が独立再導出 + consumer docstring と照合）。
   = `cause:weaker-relative` の**逆向き**適用（leg 15 E-atom の鏡像）。

**⚠️ 「解析核が落ちた」≠「family がほぼ完了」**。残債は壁の**下流**に移り、leg 16 で実測した:
**残 ~10–15 leg**（~3 ではない。**新しい壁はゼロ・判別子 PASS** — 全て plumbing / 既存 sorry-free 資産の上の self-build）。
~~**R1** 固有基底 + カウント bridge~~ = **DEAD（leg 17、構成上不要）** / **R2** ✅ **CLOSED（leg 17）** /
**R3** ✅ **CLOSED（leg 17）** /
**R4 = 独立した 2 本の bridge**（~1500–2500 行。converse 側 C0–C4 / achievability 側 A1–A4。
**achievability は interlacing を全く要さない**）= **残債の実質全部**。
**R1+R2+R3 は予告どおり consumer の sorry を 1 本も落とさなかった**（leg 16 の実測が的中）。
🔑 **C3 の核は secretly in-tree**（`parallel_per_input_mi_le_sum`、sorryAx-free）。
⚠️ **`ParallelGaussian` の 0-sorry 面は *capacity* 側（MI の `sSup`）だが consumer は *operational* 側
（メッセージ数の `sSup`）** — operational な parallel-Gaussian converse は存在しない = 残量の主駆動要因。
**slug は retire しない** — consumer 2 本（`eq`:477 / `ge`:725）が未 unblock。
詳細な obligation 表 + 次 3 leg の順序 + decisive atom → 子 plan「R4 の実体」節が SoT。
stretch（Phase 4/5-full）は不変。honesty bar 不変（CLAUDE.md「検証の誠実性」）。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §Ch.9 Shannon-Hartley（Ch.9.6）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)
> （sampling theorem = CLOSED、Phase 3/4 の信号↔サンプル橋）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（per-sample coding theorem =
> `awgn_achievability` / `awgn_converse`、Phase 3/4 の per-sample 資産）
> **Facts ledger**: `docs/shannon/shannon-facts.md`（あれば。machine 裏付けは code の `#print axioms` を SoT とし prose にキャッシュしない）

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅（commit 8bf07545）
- [~] Phase 1 — operational infra 🔄 **[FALSIFIED → Phase 1-fix で再設計済]**（commit 7e354045）
- [x] M-fix — 在庫 pass（faithful band-limit design question 解決）✅（commit 5aeb2f92）
- [x] **Phase 1-fix — faithful band-limit + continuous-codeword redesign ✅（commit 7c3afc86、独立 honesty audit PASS）**
- [~] Phase 5-min — wire + Option A README infra 🔄 **[旧着地 FALSIFIED、Phase 1-fix で mainline 復帰済]**（commit b8770fce / ff32ec82）
- [x] **l2Fourier bridge（fwd+inv）+ bandlimited_sup_bound ✅ proof-done・audit PASS（commit 9d8608a8/40c2e449/30b59a15）**
- [~] Phase 3 — achievability closure（`contAwgn_ge_shannonHartley`）🚧 **leg 1（synthSignal band-limit/energy）= ✅ audit PASS（89ede2a3/646605c7）**。leg 2（BddAbove）+ leg 3（assembly）は false-as-framed だった（leg 12）が **子 Leg P で def-fix 済（leg 14、`4fd8a47c`）** → 現在は**壁 gated**。**leg 2 = 子 Leg D' が Bessel 単独で壁非依存に閉じる**（`bandlimited_sup_bound` 経由は Proposal O では不要）。**⚠️ leg 3（`ge`）は Leg D' では閉じず Leg E 待ち** — achievability は ≈2WT 次元の構成 = 固有値カウントを下から読むことを要する（旧「`le_csSup` で transitive」は失効。子 plan の DAG 訂正が SoT）
- [~] Phase 2 — prolate-DOF スペクトル理論（`timeBandLimitingOp` + 固有値集中）🔄 **[Leg A✅ → Leg B コンパクト性 ✅ PROOF-DONE（d16a74e1）→ Leg C 固有値列挙 ✅ PROOF-DONE（de758f19、監査 PASS 77a5fdf2）→ Leg C' 非空虚性 ✅ CLOSED（a040a456、監査 PASS 569c48f0）→ 境界補題/退化統合 ✅（a7595371）** → **Leg 0（gateway）✅ CLOSED（leg 13、Proposal A/C を反証・Proposal O を PASS）→ Leg P（def-fix = Proposal O）✅ CLOSED（leg 14、`4fd8a47c`、監査 all OK、判別子 PASS = 壁が消えなかった）** → **Leg D' ✅ PROOF-DONE（leg 14、`fb18b681`、監査 `@audit:ok`）→ Leg E-atom ✅（leg 15、crude trace bound が壁非依存 closure、`69152fd9`/`7c43417a`）→ **Leg E-trace ✅（leg 15、厳密 trace 等式 `∑' i ⟪A bᵢ,bᵢ⟫ = 2WT` を Parseval で closure、`9f1129e1`/監査 `21981fc8`）** → **Leg E-sharp ✅（leg 16、第 2 モーメント `tr A − tr A² ≤ 2 + log(1+2WT)` を closure = **壁の解析核が消滅**、`552ac8de`+`00cb1c8b`/監査 all OK）** → **Leg 17 = count leg 全体が CLOSED**（R-atom `e8267457` = スペクトルギャップ on `Vᗮ` / **R2 `65897bdb` = 集中の両半分 `prolateCount_le` + `le_prolateCount`、`c` 自由・`D` 明示、監査 `43e473e3` all OK** / R3 `ec0553a6` = 指示対象なき名前を retire。**R1 は DEAD = 構成上不要**）→ **leg 18 = R4-gate A1 ✅ gateway PASS（`1540d943`/`c60abb37`、`timeBandLimitingOp_star_comm` + `le_inner_timeBandLimitingOp_of_mem`、壁でない・plumbing 確定、監査 all OK）+ R4-ACH-B ✅ CLOSED（`53723ec2`、実基底 sorryAx-free、監査 `@audit:ok`）**。次 = **R4-ACH-A2（設計判断先行: 実固有基底 or 作用素下界で再定式化）**。`ge` と `eq` の両方が R4 待ち。**⚠️ R4（operational bridge）= 残債の実質全部**（leg 16 実測 = 2 本の bridge・~1500–2500 行・**新しい壁はゼロ**）。~~次 = WSEB~~ ❌ **WSEB は命題が FALSE（leg 12）ゆえ leg ごと終了**。残債 = `∀ n, λ n ≠ 0`（infinite rank、壁ではない、未着手）]** → [shannon-hartley-phase2-spectral-plan.md](shannon-hartley-phase2-spectral-plan.md)
- [ ] Phase 4 — converse（`contAwgn_le_shannonHartley`、Phase 2 消費）📋 **[stretch]**
- [ ] Phase 5-full — `le_antisymm` 組立 📋 **[stretch / closure]**

## ゴール / Approach

### Goal（最終達成状態）

**mainline（達成済、commit 7c3afc86）**: Phase 1-fix で def を faithful・非退化・非循環に建て直し、
`contAwgn_eq_shannonHartley`（`@[entry_point]`）は **true-as-framed** な honest 単一 wall-sorry
（body = `sorry -- @residual(wall:nyquist-2w-dof)`）に復帰済（独立 audit PASS）。
`IsTwoWDegreesOfFreedom` load-bearing predicate 除去（`ShannonHartley.lean` から消滅済）も有効。

**stretch（残）**: その wall-sorry を genuine 証明で除去し `contAwgn_eq_shannonHartley` を 0-sorry
（`@audit:ok`）に復帰。真の壁核は converse 側の単一 `wall:nyquist-2w-dof`（prolate-DOF）に閉じ込め済
（**ただし壁が genuine なのは statement が true になった後**）。

honesty bar 不変（CLAUDE.md「検証の誠実性」）: genuine に建て、真に詰まる sub-wall のみ
honest `sorry + @residual(wall:<slug>)` で分解。**load-bearing hyp / 循環 def / `:True` slot は禁止**。

### def-fix の背景（overturn = 2 独立ルート、Phase 1-fix で解消済・history）

旧 Phase 1 def は 2 root で命題を空にしていた: (1) degenerate `IsBandlimited`（L¹-`𝓕` junk-0）、
(2) pointwise-vs-a.e. gap（encoder に continuity/L²-membership field 不在）。帰結は
`contAwgnMaxMessages = Nat.sSup(unbounded) = 0`。両 root は Phase 1-fix（着地節）で dissolve 済 =
コード側 `@audit:defect` 除去済（現状 false-as-framed ではない、以下は解決した設計上の理由の記録）。

### Approach（解の全体形 = 戦略）

Shannon-Hartley の operational 版 = **サンドイッチ**:
`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`（achievability, Phase 3）
`∧ contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`（converse, Phase 4）
→ `le_antisymm` で等号（Phase 5-full）。

戦略の要は **2W という次元定数を def に埋めず、証明の 2 方向から emerge させる**（`2W`・`⌊2WT⌋` を
def に含めない C3 の意図は Phase 1-fix でも継承。**旧 Phase 1 def はこの形は満たしたが degenerate/under-specified
で命題を空にしていた** → Phase 1-fix で faithful 化）:

- **achievability（≥）の信号構成は synthesis 補間 + per-sample coding で閉じる（壁非依存）。operational な `BddAbove`（leg 2）は 2026-07-15 に「`wall:nyquist-2w-dof` を要する」と判定されたが、2026-07-17（leg 12）に**その判定ごと撤回** — 命題が false-as-framed だった（`ContAwgnCode.encoder_power` の窓のみ拘束）。子 plan の Leg P（def-fix = 全直線エネルギー予算）後は、`bandlimited_sup_bound`（点値 sup）+ `awgn_converse` + `log(1+x)≤x` で **BddAbove が壁非依存に閉じる**見込み（子 Leg D'、~150–250 行）。ただし **exact 定数には依然 `≈2WT` DOF カウント（Leg E）が要る** = 壁は在るべき場所に残る。settled-facts → [`shannon-hartley-facts.md`](shannon-hartley-facts.md)**: 真間隔
  `Δ = T/n`（`n = ⌊2WT⌋`）でサンプリング → `awgn_achievability`（既所有、genuine）で
  `≈ exp(T·W·log(1+SNR))` メッセージの codebook → **synthesis bridge**（任意有限サンプルベクトルを補間する
  帯域制限信号を構成、`whittaker_shannon_bandlimited` の analysis 逆向き）で連続信号化。prolate（Phase 2）を
  要さない。**edge-effect は dissolve**（`encoder_power` は in-window `∫_{[0,T]}f²` だけ課金、sinc isometry で
  全直線 `∫_ℝ f² ≤ T·P` ⇒ `∫_{[0,T]} ≤ ∫_ℝ ≤ T·P`、窓外への sinc tail 漏れは電力制約を**緩める** = tolerate でない）。
- **converse（≤）は prolate-DOF 上界が本質**: 受信信号を上位 `≈2WT` 個の prolate 固有関数に射影
  → `awgn_converse`（既所有、genuine）+ 次元カウント。**ここだけが `wall:nyquist-2w-dof` を要する**
  （time-and-band limiting operator `P_W Q_T P_W` の固有値集中 = Landau-Pollak-Slepian、Mathlib 不在）。

したがって **真の壁は converse 側の単一核 `nyquist-2w-dof`（Phase 2 → Phase 4）に閉じ込められる**。
Phase 1 の周辺インフラと Phase 3 achievability は壁でない（in-project 定義・証明可能）。

### route（DAG 選択 + 次アクション）

Phase 1-fix 完了（commit 7c3afc86）で mainline は honest wall-sorry に着地。残る攻略順は
**bridge `l2Fourier_eq_fourierIntegral`（`bandlimited_sup_bound` を genuine 化、mainline-adjacent 次アクション）
→ Phase 3（achievability closure、既 skeleton の 5 sorry を fill、Phase 1-fix で un-blocked）
→ Phase 2（prolate 壁核・最深）→ Phase 4（converse）→ Phase 5-full（サンドイッチ組立）**。

**次アクション = bridge lemma fill**。`l2Fourier_eq_fourierIntegral`（L²-FT ↔ pointwise L¹ `Real.fourierIntegral`
の L¹∩L² 上一致）を埋めれば `bandlimited_sup_bound` が genuine 化する（~150–250 行、壁でない）。その後
Phase 3 achievability の GO 論法（edge-effect dissolve = exact sinc isometry、`contAwgnMaxMessages_bddAbove`）は
faithful def の下で有効 = 5 sorry が genuine 化可能。詳細 → Phase 1-fix「着地」/ Phase 3 節。

---

## 設計制約 — 循環罠 #2 回避（非循環設計の受入基準・SoT）

proof-pivot-advisor 名指しの循環罠: **連続時間 code を「長さ `⌊2WT⌋` のサンプルベクトルに制限」して
定義してはならない**。それは converse の DOF 限界（Landau-Pollak-Slepian）を def に埋め込む循環
（= 連続容量をサンプル済有限次元容量として定義に等価化）で、還元定理が `rfl` 化し証明が空になる。

**非循環設計の受入基準**（Phase 1 で全て充足済。Phase 3/4 の「循環チェック」欄で再照合）:

1. **C1 — codeword 空間**: codeword は `[0,T]` 上の**任意の帯域制限 `[-W,W]` 信号**（essentially
   time-limited to `[0,T]`）を許す。固定長サンプルベクトルへの制限は禁止。
   → 実装: `ContAwgnCode.encoder : Fin M → (ℝ → ℝ)`（関数、サンプルベクトルでない ✓）。
2. **C2 — capacity primitive**: `contAwgnOperationalCapacity` を operational 量として定義。**次元定数
   `2W`・`⌊2WT⌋` を一切含まない**。→ 実装: `contAwgnMaxMessages = sSup {M | ∃ code, averageError ≤ ε}`
   に `2W`・`Fin ⌊2WT⌋` 不在 ✓。
3. **C3 — 2W の出所**: 定数 `2W`・`⌊2WT⌋` は Phase 1 のどの def にも現れない。achievability（Phase 3、
   サンプリング rate 選択）と converse（Phase 4、prolate 次元カウント）の**両側から emerge** させる。
4. **C4 — 雑音 / サンプル数**: 雑音は per-sample iid Gaussian、サンプル数 `n` は**自由 ℕ パラメータ**。
   `n = ⌊2WT⌋` に定義段で固定しない。→ 実装: `ContAwgnCode.sampleCount : ℕ`（自由 field ✓）、
   雑音は `errorProbAt` 内 inline `Measure.pi (fun i => gaussianReal (sampledSignalᵢ) (N₀/2))`。

**違反の兆候（tell）**: `contAwgn_eq_shannonHartley` の証明が `rfl` / `unfold` のみで済む、`M(T)` の def に
`Fin (⌊2WT⌋)` が出る、reduction 定理が per-sample capacity をそのまま返す。これらが出たら循環。

---

## Phase 0 — Mathlib + InformationTheory API 在庫 ✅

commit 8bf07545。`docs/shannon/shannon-hartley-operational-inventory.md` に各 Phase feasibility を確定。
mainline GO 判定 + prolate = genuine 壁核の裏取り済。

## Phase 1 / Phase 5-min — retired（Phase 1-fix に統合）

- **Phase 1 — operational infra**（commit 7e354045）: `ShannonHartleyOperational.lean` の def 一式実装。
  当初 def が degenerate/under-specified で 2026-07-15 に FALSIFIED → **Phase 1-fix で再設計済**（着地節）。
  C2 primitive 形（`sSup` に `2W`/`⌊2WT⌋` 不在）+ 非循環設計意図 C1–C4 + 雑音 route β（per-sample iid
  Gaussian を `errorProbAt` に inline、proposed wall `cont-awgn-noise-measure` 不発）は Phase 1-fix でも継承・有効。
- **Phase 5-min — wire**（commit b8770fce / ff32ec82）: `IsTwoWDegreesOfFreedom` 等 load-bearing predicate の
  `ShannonHartley.lean` からの除去 + Option A README honesty infra（`gen_readme_table.ts` が `@residual(wall:*)`
  documented wall-sorry を許容）は有効な再利用インフラ。旧着地は false-as-framed で 2026-07-14 audit OVERTURNED
  だったが Phase 1-fix で mainline 復帰済。

---

## Phase 1-fix — faithful band-limit + continuous-codeword redesign ✅ **[DONE、commit 7c3afc86、audit PASS]**

**目的**: Phase 1 def を再設計し `contAwgn_eq_shannonHartley` を true-as-framed（finite・band-limited・
非退化）に復帰 → honest な単一 wall-sorry `@residual(wall:nyquist-2w-dof)` を回復。M-fix 在庫（commit 5aeb2f92）で
open design question（L² 関数上の spectral `IsBandlimited` 述語化 + Paley-Wiener 連続代表の Mathlib 有無）を先行解決。

### 着地（2026-07-15、commit 7c3afc86、独立 honesty audit PASS）

- **(a)** `IsBandlimited` を **L²-Fourier スペクトル台**で再定義（signature は `(ℝ→ℝ)` 維持 = option X、内部で
  complexify）→ degenerate L¹-`𝓕` junk-0 root 解消。
- **(b)** `ContAwgnCode` に regularity field `encoder_memLp` + `encoder_continuous` を追加 → pointwise-vs-a.e. gap 解消
  （codeword が canonical 連続 L² 代表を読む）。
- **(c)** Paley-Wiener sup bound は **field でなく派生 theorem** `bandlimited_sup_bound` として着地、body =
  `sorry -- @residual(plan:shannon-hartley-operational-moonshot-plan)`。
- **(d)** 唯一の genuine self-build gap = shared bridge lemma **`l2Fourier_eq_fourierIntegral`**（L²-FT ↔ pointwise
  L¹ `Real.fourierIntegral` の L¹∩L² 上一致、~150–250 行の tempered-distribution plumbing、**壁でない**）。
- **(e)** audit PASS: 2 false-as-framed root 双方 dissolve、新 field は regularity/非 load-bearing、wall は genuine。
- **auditor clarification（future closer 向け注意）**: `bandlimited_sup_bound` が与えるのは **full-line** の
  `|f(t)| ≤ √(2W)·‖f‖₂` 束（`‖f‖₂` は全直線 L² ノルム）。full-line → window energy `∫_{[0,T]}f² ≤ T·P` の tie は
  sup bound 単独ではなく `nyquist-2w-dof` の band-limit/essential-time-limitation 構造が供給する
  （sup bound だけで window-energy sample boundedness が出ると誤読しないこと）。

**循環チェック（充足）**: C1–C4 再照合済（`encoder : Fin M → (ℝ → ℝ)` は関数のまま、capacity primitive に
`2W`/`⌊2WT⌋` 不在）。continuity/L²-membership field は codeword regularity であり DOF 限界の埋め込みではない。
**README ripple**: Option A 脚注の `nyquist-2w-dof` は fix 完了で genuine documented wall に復帰（一時 false 状態は解消）。

---

## Phase 2 — prolate-DOF スペクトル理論 📋 **[stretch / 壁核・最深]**

> **サブ計画**: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md)
> **子 plan の負債は 1 つに減った（2026-07-17 leg 14）**: ~~(1) def-fix（観測写像を Karhunen-Loève 展開へ
> = Proposal O）~~ ✅ **返済済（Leg P、`4fd8a47c`）**。残るは
> (2) **壁核 self-build**（`wall:nyquist-2w-dof` = prolate/LPS の `≈2WT` DOF カウント、Leg E）。
> **build order = ~~Leg 0（gateway）✅~~ → ~~Leg P（def-fix）✅~~ → Leg D'（BddAbove を **Bessel 単独**で
> 壁非依存 closure）→ Leg E（壁 — `ge`・`eq` 両方がここ待ち）**。
> ~~中心問題 verdict「BddAbove ⟸ スカラー WSEB」~~ は **WSEB が FALSE ゆえ moot**（Leg W 終了）。
> settled-facts → [`shannon-hartley-facts.md`](shannon-hartley-facts.md)。在庫 = [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)。以下は pointer。

**目的**: time-and-band limiting operator `P_W Q_T P_W`（`Q_T` = `[0,T]` 時間制限、`P_W` = `[-W,W]`
帯域制限射影）のコンパクト自己共役性 + prolate-spheroidal 固有値集中（>1/2 の固有値が `≈2WT + O(log WT)`
個 = Landau-Pollak-Slepian）。**真の sub-wall = `wall:nyquist-2w-dof`**。proof-log: yes。概算 800–1500 行。

**主要 theorem（signature スケッチ）**:

```lean
/-- time-and-band limiting operator P_W ∘ Q_T ∘ P_W（自己共役・コンパクト）。 -/
noncomputable def timeBandLimitingOp (T W : ℝ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := ⟨? P_W ∘ Q_T ∘ P_W⟩

theorem timeBandLimitingOp_isSelfAdjoint (T W : ℝ) :
    (timeBandLimitingOp T W).IsSelfAdjoint := ⟨genuine 目標⟩

theorem timeBandLimitingOp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingOp T W) := ⟨genuine 目標。Hilbert-Schmidt 経由が有力⟩

/-- prolate 固有値列（降順、スペクトル定理から）。 -/
noncomputable def prolateEigenvalues (T W : ℝ) : ℕ → ℝ := ⟨? spectrum⟩

/-- **壁核**: >1/2 の固有値カウント = ⌊2WT⌋ + O(log WT)（Landau-Pollak-Slepian）。 -/
theorem prolate_eigenvalue_count (T W : ℝ) (hT : 0 < T) (hW : 0 < W) :
    ⟨#{n | 1/2 < prolateEigenvalues T W n} と 2WT の集中不等式⟩ := by
  sorry   -- @residual(wall:nyquist-2w-dof)
```

**依存（DAG edge）**: Phase 0 → Phase 2。Phase 2 → Phase 4（converse、上位次元カウント）。
achievability（Phase 3）は Phase 2 に依存しない公算。
**循環チェック**: 本 Phase は def でなく作用素の解析。C3（`2WT` は固有値カウントの**結論**として現れ、
def の入力ではない ✓）。
**受入基準**:
- **proof-done 条件（stretch）**: 作用素定義 + 自己共役 + コンパクト性が genuine、固有値集中が genuine。
- **honest-sorry 分解条件（現実的着地）**: 作用素 + 自己共役 + コンパクト性は **genuine を目標**（Mathlib
  compact operator + spectral theorem の上に建設）。**固有値集中の asymptotic `prolate_eigenvalue_count`
  は最有力の genuine 壁** → body `sorry + @residual(wall:nyquist-2w-dof)`。load-bearing hyp /
  `*Hypothesis` predicate 化は禁止（`nyquist-2w-dof` に集約）。
**feasibility unknown（inventory 反映）**: (a) Mathlib のスペクトル定理が本作用素に適用できる形か
（`IsSelfAdjoint` + compact → 固有値分解）、(b) 固有値の存在・降順列挙が既存 API で取れるか、
(c) 集中不等式（Landau-Pollak-Slepian）の Mathlib 不在は確定（loogle `Found 0`: prolate/Slepian）
→ **self-build ~800-1500 行のスペクトル解析**、詰まれば honest sorry で分解し次 leg。
**retreat line**: `prolate_eigenvalue_count` を `sorry + @residual(wall:nyquist-2w-dof)`。
作用素の自己共役・コンパクト性が Mathlib 不足で詰まる個別補題も同 wall に集約（compound 化しない）。

---

## Phase 3 — achievability closure 📋 **[Phase 1-fix に gated、fix 後 un-blocked]**

**目的**: `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`。真間隔 `Δ = T/n`
（`n = ⌊2WT⌋`）サンプリング → per-sample `awgn_achievability`（既所有 genuine）→ **synthesis bridge**
（有限サンプルベクトルを補間する帯域制限信号を構成）で連続信号化。proof-log: yes。**概算 500–850 行**
（+BddAbove leg 分が旧見積 300–600 からの delta）。

**既 skeleton**: `InformationTheory/Shannon/ShannonHartleyAchievability.lean`（11 decl、5 sorry:
`synthSignal_bandlimited` / `synthSignal_sq_integrable` / `synthSignal_energy` /
`contAwgnMaxMessages_bddAbove` / `contAwgn_ge_shannonHartley`）。**これらの 5 sorry は Phase 1-fix
（faithful def）完了後に初めて genuine 化する**: `synthSignal_bandlimited` は L²-FT = boxcar で本物の
帯域制限性を要し（現行 degenerate def では junk-true）、`contAwgnMaxMessages_bddAbove` は `IsBandlimited` が
実制約を課さないと成立しない。→ **Phase 3 は Phase 1-fix に gated**。

**★ code-tag 修正 to-do（実装 owner・次 leg）**: 上記 5 sorry は `@residual(plan:shannon-hartley-op-phase3)`
を付けているが、この slug は解決先ファイルが無い（`docs/shannon/shannon-hartley-op-phase3.md` は不在）。
解決可能な stem は本 plan の filename stem **`shannon-hartley-operational-moonshot-plan`**。
実装 owner が `@residual(plan:shannon-hartley-operational-moonshot-plan)` に書き換える（コードタグが SoT）。

**GO/NO-GO は PARTIAL（2026-07-17 leg 12 で再々判定。2026-07-15 の「leg 2 は WALL-GATED」は撤回）**:
信号「構成」（leg 1）は GO・壁非依存で proof-done 済。**leg 2 の `BddAbove` は壁ではなく false-as-framed**。
- **有効な部分（GO、不変）**: achievability の連続 encoder を `synthSignal` で構成する限り、
  `∫_ℝ f² = Δ·∑aᵢ²`（exact sinc isometry、leg 1 の `synthSignal_energy` で proof-done）ゆえ全直線 energy が
  discrete energy と**一致**する。⟹ **子 Leg P（def-fix = 全直線エネルギー予算）の下でも `encoder_power` は
  そのまま充足**（むしろ窓への降格が不要になる分だけ易しくなる。子 plan「傍証」節）。
- **偽だった部分（旧 NO-GO の再解釈）**: `BddAbove` は**任意の** `ContAwgnCode` を扱う converse 的主張だが、
  現行 def は窓エネルギーしか拘束しないため**超振動符号語で反証される** = 壁でなく偽。
  2026-07-15 は「窓内エネルギーから標本エネルギーを一様に抑えるには時間帯域集中が要る」と読んだ
  （= *難度*）が、正しい読みは「**抑えられない**」（= *非有界性*）だった。
  → 子 Leg P（def-fix）後、`bandlimited_sup_bound`（全直線 sup 境界がここで初めて有効化）+ `awgn_converse` +
  `log(1+x)≤x` で **BddAbove は壁非依存**に閉じる見込み（子 Leg D'）。`nyquist-2w-dof` は achievability と
  **共有されない**（converse 専用に戻る。ただし理由は 2026-07-14 の旧説明とは別）。

**新 file**: `InformationTheory/Shannon/ShannonHartleyAchievability.lean`（imports:
`ShannonHartleyOperational` + `WhittakerShannon`/`NormalizedSinc` + `AWGN.Achievability` + `AWGN.Converse`）。
`ShannonHartleyOperational.lean` を clean に保つ。作成時 `InformationTheory.lean` に import 登録（実装 owner 担当）。
**import cycle なし**（Converse/Achievability/WhittakerShannon は Operational を import しない、verified）。

**主要 theorem（signature スケッチ、Phase 1 実 def 使用）**:

```lean
theorem contAwgn_ge_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := ⟨サンドイッチの ≥ 方向、genuine⟩
```

**構成 leg（3 束）**:

- **leg 1 — bridge sub-module（synthesis + Parseval energy）**。**synthesis ≠ analysis に注意**:
  `whittaker_shannon_bandlimited` は analysis 方向（既帯域制限 f のサンプル）。achievability は synthesis 方向
  = 任意有限サンプルベクトルを補間する帯域制限 f の構成 + その帯域制限性証明（別途要）。再利用資産:
  `NormalizedSinc.sincN_int_eq_kronecker`（NormalizedSinc.lean:95、補間 exactness）+
  `integral_exp_boxcar_eq_sincN`（WhittakerShannon.lean:63、sinc↔boxcar）+ **line**-Plancherel
  `MeasureTheory.Lp.inner_fourier_eq` / `Lp.norm_fourier_eq`（LpSpace.lean:93/89）。**circle 版
  `Lp ℂ 2 haarAddCircle` の sampling engine は使わない**（line-Plancherel が正解）。
- **grid spacing の訂正**: サンプル間隔は真間隔 `Δ = T/n`（`sampledSignal` は spacing `T/n` で標本化、
  ShannonHartleyOperational.lean:110）で、`1/(2W)` **ではない**（`n = ⌊2WT⌋` floor で `Δ ≠ 1/(2W)`）。
  連続 encoder を真間隔 `Δ` で reconstruct し `[−n/(2T), n/(2T)] ⊆ [−W,W]`（`n/(2T) ≤ W`）に帯域制限。
  isometry は EXACT: `∫_ℝ f² = Δ·∑ aᵢ² = ∑(sampledSignalᵢ)² = ∑ cᵢ² ≤ n·P' = ⌊2WT⌋·(P/(2W)) ≤ T·P`。
- **leg 2 — BddAbove leg 🧨 false-as-framed（2026-07-17 leg 12。2026-07-15 の WALL-GATED 判定を撤回）**:
  `contAwgnMaxMessages = sSup {M : ℕ | …}`（`ShannonHartleyOperational.lean:424`）を `le_csSup` で下界するには
  集合の **`BddAbove`** が必須。ℕ 上で unbounded `sSup` は junk `0` を返す（repo は `Cramer/Cramer.lean` /
  `ParallelGaussian/PerCoord.lean` でこの ℕ-sSup-returns-0 罠に既遭遇）— **現行 def ではこの junk 経路が実際に
  発火する**（`¬BddAbove` ⟹ `M=0` ⟹ `log 0 = 0` ⟹ 容量 `=0` vs 閉形式 `>0`）。
  2026-07-15 は「`ContAwgnCode` は窓内エネルギーしか課さず `bandlimited_sup_bound` は無制約な全直線 `‖f‖₂` でしか
  点値を抑えられない」と正しく観察した上で**「ゆえに時間帯域集中（壁）が要る」と結論した**。正しい結論は
  **「ゆえに非有界 = 命題が偽」**だった（`shannon-hartley-facts.md` §NUMERIC-TRUE-ARTIFACT: 「制御できない」は
  *難度* に読めるが実際には *非有界性* を意味していた）。
  **⟹ 撤退の向きが反転**: 壁 self-build ではなく **def-fix**（子 Leg P）。修正後は同じ `bandlimited_sup_bound` が
  `‖f‖₂² ≤ T·P` と結合して `E_s ≤ 2WT·(T·P)` を n 一様に与え、**壁非依存**で閉じる（子 Leg D'）。
  **「全直線エネルギー field 追加は壁の偽装」という旧禁止は REVOKED**（子 plan「禁止の撤回」節が SoT。
  判別子 = 偽装なら壁が消える / この修正では `eq` に Leg E が残るので消えない）。
  **仮説化は依然禁止**（`≥`/BddAbove の core を hyp 化 = load-bearing tier-5）。
  → Phase 3 file が `AWGN.Converse` も import する理由（converse-flavored な BddAbove）は不変。
- **leg 3 — assembly（`awgn_achievability` 配線）**: 各 `ε ∈ Ioo 0 1` と大 `T` に `sampleCount = ⌊2WT⌋`
  を code の自由 field に代入（C3/C4 ✓）→ `awgn_achievability` で discrete `AwgnCode M n P'`
  （`M ≥ ⌈exp(n·(1/2)log(1+SNR'))⌉ = ⌈exp(T·W·log(1+SNR'))⌉`）→ leg 1 synthesis で連続 encoder 化 →
  `le_csSup`（leg 2 の BddAbove 消費）+ `limsup`/`⨅ε` 操作で `⨅ε contAwgnRate ≥ W·log(1+P/(N₀·W))`。
  **`sampledSignal` √(T/n) 正規化の役割**: 持ち上げた連続 encoder の `sampledSignal` が discrete codeword `cᵢ`
  と一致し、`√(T/n)` isometry で per-sample エネルギー ↔ 連続電力の Parseval 整合 → per-sample SNR = `P/(N₀·W)`
  で `awgn_achievability` の誤り評価がそのまま `averageError ≤ ε` に移る（この正規化がないと oversampling で SNR
  が膨らみ崩れる = 非退化の要）。誤り測度 match は verbatim 確認済（下記）。

**build order（skeleton-first, then bottom-up）**: (0) skeleton = 全 bridge 補題 + BddAbove 補題 +
`contAwgn_ge_shannonHartley` assembly を typed `sorry` で置き type-check done（committable、Parseval 定数 `Δ`
+ 帯域制限区間 `n/(2T)` を pin）→ (1) bridge sub-module（leg 1）を **interpolation-exactness (ii, `sincN_int_eq_kronecker`
再利用, ~30–80) → band-limited synthesis (i, `𝓕` linearity + sinc↔boxcar, ~100–200) → W-scaling/dilation (iv, ~50–150)
→ Parseval energy (iii, line-Plancherel × sinc, ~150–300、最重)** の順で fill → (2) BddAbove leg（leg 2, ~150–350）
→ (3) assembly（leg 3、`le_csSup` + 誤り測度等式 + `limsup`/`⨅ε`）。**bridge-sub-module-first が
top-down-with-sorries より de-risk**（2 つの feasibility unknown は leg 1–2 にあり assembly でない）。

**誤り測度 match（verbatim 確認済）**: `Code.errorProbAt W m = Measure.pi (fun i ↦ W (encoder m i)) (errorEvent m)`
（ChannelCoding/Basic.lean:192）、`awgnChannel N x = gaussianReal x N`（AWGN/Basic.lean:69）⇒ `N = (N₀/2).toNNReal`
+ `sampledSignal = cᵢ` で `ContAwgnCode.errorProbAt`（ShannonHartleyOperational.lean:121）に一致。
`IsAwgnChannelMeasurable` は無条件 dischargeable（`isAwgnChannelMeasurable`, AWGN/ChannelMeasurability.lean）。

**依存（DAG edge）**: Phase 1 + WhittakerShannon/NormalizedSinc（CLOSED）+ AWGN.awgn_achievability（genuine、leg 3）
→ Phase 3 leg 1/3。**leg 2（BddAbove）は Phase 2 の prolate 壁核と同一 `wall:nyquist-2w-dof` に依存する**
（2026-07-15 判定、旧「Phase 2 には依存しない（確定）」は撤回）。`awgn_converse` は BddAbove 単独では標本エネルギーの
一様境界を供給できず、そこが壁。
**循環チェック**: サンプリング rate `2W` / `sampleCount = ⌊2WT⌋` は achievability 側の**構成選択**であり
def の入力でない（C3 ✓）。`contAwgnMaxMessages` を `⌊2WT⌋` サンプルに制限せず、その値以上のメッセージ数を
**達成できる**と示すだけ（C1/C2 ✓、非循環は保持）。leg 2 の BddAbove が現行 def で取れないのは crude 上界の
不足ではなく**命題が偽**だから（2026-07-17。「時間帯域集中を要する」という 2026-07-15 の読みは撤回）。
**受入基準**:
- **proof-done 条件（= 目標）**: `≥` を fully genuine 証明（synthesis bridge + Parseval 電力橋 + BddAbove
  + `awgn_achievability` + 雑音サンプル iid Gaussian）。**leg 1（synthesis/energy）= 壁非依存で proof-done 済**。
  ~~**leg 2 + leg 3 = 現行 def では false-as-framed**~~ → 子 Leg P で **def-fix 済（leg 14）**。以降は壁 gated。
**retreat line（2026-07-17 leg 14 で再訂正 — 2 宣言を分離せよ）**: 旧文は「Phase 3 achievability は
`wall:nyquist-2w-dof` を共有しない」（leg 12）だったが、**def-fix 後は宣言ごとに割れる**:
- **leg 2（`bddAbove`）= 壁を共有しない** ✅ **証明済**（子 Leg D'、`fb18b681`、`@audit:ok`）— Bessel 単独。
  推移的定数閉包 55234 個に `prolate`/`bandlimited_sup_bound`/`Nyquist` 等が **0 hit**、`hW` すら未使用。
- **leg 3（`ge`）= 壁を共有する** ❌ 旧文の反例 — achievability は利得 ≈1 の次元を ≈2WT 本構成することを要し、
  これは固有値カウントを**下から**読むこと = `wall:nyquist-2w-dof` そのもの。**コード側タグが SoT**
  （`@residual(wall:nyquist-2w-dof)`、実装・監査が独立に同結論）。**旧「`le_csSup` 経由で transitive に
  closure」は def-fix 前の線ゆえ失効** — `ge` は Leg D' でなく **Leg E 待ち**。

**注記（判定が 3 度振れた軸ゆえ明示）**: 2026-07-15「achievability は壁を共有する」→ leg 12「撤回、偽の命題を
壁と読んだだけ」→ leg 14「def-fix 後は**共有する**（ただし `bddAbove` は共有しない）」。leg 12 の撤回は
**当時の（偽の）def に対しては正しかった** — 偽の命題に壁も何もないため。今の verdict はそれと矛盾しない:
**def が変わったので命題も変わった**。**full closure の前提** = ~~Leg 0~~✅ → ~~Leg P~~✅ → Leg D'（`bddAbove`）
→ **Leg E（`ge` + `eq`）**。
**~~Proposal A（全直線エネルギー単独）~~ / ~~Proposal C（Landau-Pollak、旧 FAIL 時の退避先）~~ は leg 13 で
両方とも反証・破棄**（Proposal C も同じ観測写像欠陥を継承する）→ 子 plan / §OBSERVATION-MAP。
旧選択肢 (b)「容量 def を achievable-rate 形へ再設計」は **park**（def-fix が成れば不要、別軸）。
**依然禁止**: load-bearing hyp 化 / `BddAbove` の `≥` 定理への仮説化（tier-5）。
**⚠️ 撤回**: 旧「全直線エネルギーの仮説化（壁の偽装）」の禁止は **REVOKED** — 全直線エネルギー **field** の追加は
def-fix の内容そのもので、偽装ではない（判別子 → 子 plan「禁止の撤回」節）。**hyp 化の禁止とは別物**（field ≠ hyp）。

---

## Phase 4 — converse 📋 **[stretch]**

**目的**: `contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P`。
受信信号を上位 `≈2WT` prolate 固有関数（Phase 2）に射影 → `awgn_converse`（既所有 genuine）+ 次元カウント。
proof-log: yes。概算 400–700 行。

**主要 theorem（signature スケッチ）**:

```lean
theorem contAwgn_le_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P := ⟨サンドイッチの ≤ 方向⟩
```

**構成 leg（Phase 1 実 def の使われ方）**:
- Phase 2 `prolate_eigenvalue_count` で「有効次元 ≤ `⌊2WT⌋ + O(log WT)`」を得る（**壁核を消費**）。
- ⚠️ **未検証の仮説（established fact ではない。owner = 子 plan の Leg 0 攻撃 1）**: 「任意の `ContAwgnCode T W P M` は
  `sampleCount` を自由に大きく取れる（oversampling）が、`sampledSignal` の `√(T/n)` tight-frame 正規化により
  sampling Gram 作用素が `≈ I` となり、有効ランクは `sampleCount` に依らず `≈2WT` に留まる ⟹ `contAwgnMaxMessages`
  の上界は `sampleCount` に依らず prolate DOF カウントで bound される」。
  - **`√(T/n)` 正規化の実在のみ verbatim 確認済**（`sampledSignal f T n i = √(T/n)·f(i·(T/n))`、
    `ShannonHartleyOperational.lean:396-397`）。**「Gram ≈ I」「有効ランク ≈2WT」は未検証** — これは
    `prolate_eigenvalue_count`（Phase 2 Leg E）**の内容そのもの**であって、その前に**仮定してはならない**。
  - **二度浮上した = load-bearing かつ未検証のシグナル**: 同じ主張が (a) 本 Phase 4 の散文、(b) 2026-07-17 に
    orchestrator が子 plan のブリーフで「オーバーサンプリングは漏れない理由」として独立に提示、の**2 つの異なる
    source から浮上**し、後者は planner が捕捉して子 plan の判断ログ #4 に隔離した。**独立に再浮上すること自体が、
    これが未検証のまま設計を駆動している証拠**（leg 9 の三者一致と同型 — 全員が同じ問いを間違える）。
  - **converse で使うなら Leg E の**結論として**使う**（仮定としてではない）。**BddAbove の正当化には使わない** —
    子 Leg D' は sup 境界（`bandlimited_sup_bound`）+ Riemann 正規化だけで n 一様上界を出し、部分空間次元を
    経由しない。ここで部分空間次元側を採ると**壁を誤輸入**する（= 2026-07-15 の under-estimation と同じ経路）。
- 上位固有関数への射影で受信信号を `≈2WT` 次元に還元 → per-letter `awgn_converse`
  （`Real.log M ≤ n·(1/2)log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`）を適用。
- `limsup(T→∞)` + Fano 項消滅（`Pe → 0`）で `⨅ε contAwgnRate ≤ W·log(1+P/(N₀·W))`。
**依存（DAG edge）**: Phase 1 + Phase 2（`prolate_eigenvalue_count`）+ AWGN.awgn_converse（genuine）→ Phase 4。
**循環チェック（最重要）**: C3 — `⌊2WT⌋` は Phase 2 固有値カウントの**結論**として converse に入り、
capacity def からは来ない ✓。受信信号を射影で次元還元するのは**証明ステップ**であり code def の制限でない
（C1 維持 ✓）。ここで「code をサンプルベクトルに制限」した瞬間に循環化する — 射影は受信側の解析、
codeword 空間は Phase 1 の任意帯域制限信号（`encoder : Fin M → (ℝ → ℝ)`）のまま。
**受入基準**:
- **proof-done 条件**: Phase 2 genuine 前提で `≤` を genuine 証明。
- **honest-sorry 分解条件**: Phase 2 の `prolate_eigenvalue_count` が sorry 状態なら Phase 4 は
  それを transitive 継承し `contAwgn_le_shannonHartley` も `@residual(wall:nyquist-2w-dof)`
  （Phase 4 独自の新 sorry は作らず Phase 2 継承）。
**feasibility unknown**: 射影後の受信分布が `awgn_converse` の要求形（`AwgnCode M n P` + per-letter Gaussian）
に載るか。prolate 固有関数系での Parseval / 電力保存。
**retreat line**: Phase 2 継承の `@residual(wall:nyquist-2w-dof)`。射影 → `awgn_converse` 配線が
Mathlib 不足で詰まる個別補題は同 wall に集約。

---

## Phase 5-full — le_antisymm 組立 📋 **[stretch / closure]**

**目的**: Phase 3 `≥` + Phase 4 `≤` の `le_antisymm` で `contAwgn_eq_shannonHartley` の wall-sorry を除去。
proof-log: no（wiring + 代数再利用、小規模）。概算 30–80 行。

```lean
theorem contAwgn_eq_shannonHartley ... :=
  le_antisymm (contAwgn_le_shannonHartley ...) (contAwgn_ge_shannonHartley ...)
```

- `twoW_perSample_eq_shannonHartley`（代数 leg、既存）+ `bandlimitedAwgnCapacity` / `perSampleAwgnCapacity`
  def を再利用。
- **中間状態**: Phase 3 が genuine・Phase 4 が sorry なら、`contAwgn_eq_shannonHartley` は `≤` 経由で
  `@residual(wall:nyquist-2w-dof)` を継承（`≥` は genuine）。
**依存（DAG edge）**: Phase 3 + Phase 4 → Phase 5-full。
**循環チェック**: 組立後の `contAwgn_eq_shannonHartley` が genuine 等号（`rfl` でない、Phase 3/4 の実証明を経由）
であることを確認。
**受入基準**: `contAwgn_eq_shannonHartley` 0 sorry / 0 residual、`@audit:ok`（= closure）。

---

## Sub-wall map

| Phase | 生む見込みの residual | 位置づけ |
|---|---|---|
| Phase 1（雑音測度） | proposed wall `cont-awgn-noise-measure`（**不発**） | route β（per-sample iid Gaussian を `errorProbAt` に inline）採用で `IsGaussianProcess` 依存が消え、当初 proposed だった雑音測度壁は不要になった（register 追加せず、code 側 slug も生成されない） |
| Phase 2（prolate 固有値集中） | `wall:nyquist-2w-dof`（**最有力・確定的**） | 真の壁核。作用素定義 + 自己共役 + コンパクト性は genuine 目標、**固有値集中 asymptotic のみ**が genuine 壁（loogle `Found 0`: prolate/Slepian、self-build ~800-1500 行）。詰まれば `prolate_eigenvalue_count` を honest sorry で分解 |
| Phase 3（achievability） | **leg 1 = なし（synthesis/energy 壁非依存・proof-done 済）／leg 2 (BddAbove) + leg 3 (assembly) = `defect:false-statement`（2026-07-17 leg 12、2026-07-15 の `wall:nyquist-2w-dof` 判定を撤回）** | 命題が偽（`encoder_power` の窓のみ拘束）ゆえ `sorry` は充填不能 = audit-tags.md「`defect` の (b) 用法」。**壁 gated ではない**。子 plan の Leg P（def-fix）後、BddAbove は `bandlimited_sup_bound` + `awgn_converse` + `log(1+x)≤x` で **壁非依存**に閉じる見込み（子 Leg D'）。leg 3 は `le_csSup` 経由で transitive に closure。**crude 上界は rate を閉じない**（`log M ≤ 2WT²P/N₀` ⟹ rate 発散）ため exact 定数は依然 Leg E = 壁が残る |
| Phase 1-fix（def 再設計） | **`plan:…moonshot-plan`（`bandlimited_sup_bound`）** ✅ | def を faithful 化し `@audit:defect` 除去済（commit 7c3afc86）。残 self-build = bridge `l2Fourier_eq_fourierIntegral`（壁でない、~150–250 行） |
| Phase 4（converse） | `wall:nyquist-2w-dof`（**Phase 2 transitive 継承**） | Phase 2 の `prolate_eigenvalue_count` を継承。Phase 4 独自の新 sorry は作らない |
| Phase 5-min（🔄 旧着地 FALSIFIED → 復帰済） | `@residual(wall:nyquist-2w-dof)`（honest） | 旧 mainline は degenerate def 下で false-as-framed（2026-07-14 audit OVERTURNED）だったが、Phase 1-fix で `contAwgn_eq_shannonHartley` は honest wall-sorry に復帰済 |

**register 整合**: `nyquist-2w-dof` は `docs/audit/audit-tags.md` Wall name register に既存。Phase 1-fix 完了で
`contAwgn_eq_shannonHartley` は true-as-framed になり、この sorry は genuine documented wall として有効
（`@audit:defect` 除去済）。register note の consumer 反映は実装 owner の担当（本 plan は
prose に壁事実をキャッシュしない）。各 node の前提: **genuine に詰まったら honest
`sorry + @residual(wall:nyquist-2w-dof)` で分解し次 leg**。load-bearing hyp / `*Hypothesis` predicate 化 /
循環 def / `:True` slot は全 Phase で禁止（CLAUDE.md）。

---

## 依存 DAG / ripple

```
[DONE] Phase 0 ─► M-fix 在庫 ─► Phase 1-fix ✅ ─► bridge l2Fourier ✅ ─► Phase 3 leg 1 ✅ (synthSignal)
                                                                              │
   [NEXT] 子 Leg 0 (gateway 🚦 実装を block) ─► 子 Leg P (def-fix) ─► 子 Leg D' (BddAbove 壁非依存) ─► Phase 3 leg 3 ─┐
                                                                                                                    ├─► Phase 5-full
                          Phase 4 (converse) ◄─ 子 Leg E (LPS count = 壁) ◄─ Legs A/B/C/C' ✅ (作用素資産) ─────────┘
```

- **mainline（現在地）**: `0 → M-fix → 1-fix ✅ → bridge ✅ → Phase 3 leg 1 ✅` まで着地。**そこから先は
  false-as-framed でブロック**（Status 節）。`Phase 1-fix で mainline 復帰` という旧記述は撤回。
- **next**: **子 plan の Leg 0（gateway）** — 修正後 def の真偽を敵対的に検査（実装ゼロ、Leg P/D' を block）。
  PASS → `Leg P → Leg D' → Phase 3 leg 3` / FAIL → 子 plan の Proposal C（Landau-Pollak）へ pivot。
  壁核 `Leg E → Phase 4` は Legs A/B/C/C'（有効資産、refutation の影響を受けない）の上に建つ → `5-full`。
- **ripple**: `IsTwoWDegreesOfFreedom` 削除は完了済で有効（consumer 影響 ShannonHartley.lean 内に閉じる）。
  新 file `ShannonHartleyAchievability.lean` は既存 + `InformationTheory.lean` に import 登録済
  （import cycle なし = Converse/Achievability/WhittakerShannon は Operational を import しない）。
  Phase 1-fix の def 書換 ripple: `IsBandlimited` / `ContAwgnCode` の consumer は Operational + Achievability の
  2 file（実装 owner は `dep_consumers` で blast radius を確認して書換）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ残す（≤ 10 entry）。

1. **✅ mainline OVERTURN は Phase 1-fix で RESOLVED（2026-07-15、commit 7c3afc86、audit PASS）**: 2026-07-14
   tier-2 audit を覆した 2 root（① degenerate L¹-`𝓕` `IsBandlimited`、② pointwise-vs-a.e. encoder gap）は
   def 再設計（L²-FT spectral-support + `encoder_memLp`/`encoder_continuous` field）で dissolve 済。
   `contAwgn_eq_shannonHartley` は honest 単一 wall-sorry `@residual(wall:nyquist-2w-dof)` に復帰、`@audit:defect` 除去済。
   残: bridge `l2Fourier_eq_fourierIntegral`（壁でない）→ Phase 3。
2. **mainline は false-as-framed、def-fix は子 plan が負う（2026-07-17 leg 12、active）**: 3 宣言が偽
   （root = `encoder_power` の窓のみ拘束、`cause:signature-drops-constraint`）。**2026-07-15 の「leg 2/3 は
   WALL-GATED」判定は撤回** — 壁 gated ではなく命題が偽だった（proof-pivot-advisor verdict 2 + 独立監査が
   CONFIRMED したが、**両者とも「どれくらい難しいか」を問い、誰も「そもそも真か」を問わなかった**）。
   `wall:nyquist-2w-dof` は live consumer 0 = DORMANT、**retire しない**（修正後 converse が要する）。
   詳細 → [`shannon-hartley-facts.md`](shannon-hartley-facts.md)（再キャッシュしない）。
3. **真の壁核は converse 側の `nyquist-2w-dof` 単一（不変）**: Phase 2 Leg E（固有値集中）→ Phase 4 に閉じ込める。
   **def-fix 後も壁はここに残る**ことが、def-fix が「壁の偽装」でない判別子（子 plan「禁止の撤回」節が SoT）。
   Phase 3 achievability は修正後 def の下で壁非依存に閉じる見込み。
4. **`√(T/n)` tight-frame ⟹ 有効ランク `≈2WT` は未検証仮説（active、owner = 子 Leg 0 攻撃 1）**: 正規化の**実在**は
   verbatim 確認済（`Operational.lean:396-397`）だが、「Gram ≈ I / 有効ランクが `sampleCount` に依らない」は
   **`prolate_eigenvalue_count`（Leg E）の内容そのもの**で、仮定してはならない（Phase 4 節に警告を明記）。
   **同一主張が 2 つの独立 source から浮上**（Phase 4 散文 + orchestrator ブリーフ）し、後者は planner が捕捉して
   子 plan 判断ログ #4 に隔離 = **未検証のまま設計を駆動している証拠**。**BddAbove の正当化には使わない**
   （部分空間次元側を採ると壁を誤輸入 = 2026-07-15 の under-estimation と同じ経路）。
5. **循環罠 #2 は設計制約節が SoT**: 各 Phase の「循環チェック」欄で C1–C4 を照合。Phase 1-fix の
   continuity/L²-membership field は codeword regularity（DOF 限界の埋め込みではない）。Phase 4 の受信信号射影は
   「証明ステップであって code def の制限でない」を厳守（codeword 空間は `encoder : Fin M → (ℝ → ℝ)` のまま）。
