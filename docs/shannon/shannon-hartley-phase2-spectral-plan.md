# Shannon-Hartley Phase 2 — 時間帯域制限作用素のスペクトル理論 + `ContAwgnCode` def-fix サブ計画 🌙

> **Parent**: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2（prolate-DOF 壁核）
> **Inventory**: [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)
> **Settled facts (SoT)**: [`shannon-hartley-facts.md`](shannon-hartley-facts.md)（§WSEB / §REVOKED / §NUMERIC-TRUE-ARTIFACT）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sinc/sampling = CLOSED）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（`awgn_converse` = Leg D' の trace 境界を供給）

## 進捗

- [x] M0 在庫調査 ✅（`shannon-hartley-phase2-spectral-inventory.md`）
- [x] Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` ✅ genuine（4d848a53）
- [x] Leg B — コンパクト性 `timeBandLimitingOp_isCompact` ✅ PROOF-DONE（d16a74e1、4 leaf 全 genuine、監査 PASS）
- [x] Leg C — 固有値降順列挙 `prolateEigenvalues` framework ✅ PROOF-DONE（de758f19、監査 PASS 77a5fdf2）
- [x] Leg C' — 非空虚性 `prolateEigenvalues_zero_pos` ✅ CLOSED（a040a456、監査 PASS 569c48f0）
- [x] 境界補題 + 退化物語の統合 ✅ CLOSED（a7595371、tightness が compiler-backed）
- [x] ~~Leg W — WSEB probe~~ ❌ **命題が FALSE と確定（leg 12、`d2938749`/`67e1ff3f`）**。下記「Leg W — 終了」
- [x] **Leg 0 — 修正後 def の gateway 検査** ✅ **CLOSED（leg 13）**。verdict: **Proposal A = FAIL（反証）/
      Proposal C = FAIL（同欠陥を継承）/ Proposal O = PASS** → 台帳 §OBSERVATION-MAP。下記「Leg 0 — 終了」
- [ ] **Leg P — 観測写像の def-fix（Proposal O = 正規直交テスト関数）** 📋 **[NEXT]**
- [ ] Leg D' — `contAwgnMaxMessages_bddAbove` を修正後 def の下で **Bessel 単独**で closure 📋 **[Leg P に gated]**
- [ ] Leg E — tight concentration `prolate_eigenvalue_count`（LPS）📋 **[converse exact 定数、genuine wall 公算大]**
- [ ] 残債 — `∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）
- [ ] 残債 — 散文 de-tag 3 件（下記「残債」節）

---

## ゴール / Approach

### Goal

**本 plan は 2 つの負債を負う**:

1. **def-fix（新規・最優先）**: `contAwgnMaxMessages_bddAbove` / `contAwgn_eq_shannonHartley` /
   `contAwgn_ge_shannonHartley` の 3 宣言は **false-as-framed** で、コード側は
   `@audit:defect(false-statement)` + `@residual(defect:false-statement)` +
   `@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` = **本 plan 名指し**。
   **この def-fix を負うのは本 plan**。
   **⚠️ 根本原因は Leg 0 で入れ替わった（leg 13）**: `encoder_power`（入力クラス）**ではなく**
   `sampledSignal` + `ContAwgnCode.errorProbAt`（**観測写像**）。`encoder_power` の窓限定は
   `BddAbove` を落とす**第 2 の**欠陥ではあるが、`eq` の falsity はそれを直しても残る。
   軸ごと違った。証拠と機序 → 台帳 **§OBSERVATION-MAP**（`cause:signature-drops-constraint` の
   帰属先も `encoder_power` → 観測写像に訂正）。
2. **壁核 self-build（従来）**: `wall:nyquist-2w-dof`（prolate/LPS の `≈2WT` DOF カウント）。
   **live consumer は 0（DORMANT）だが retire しない** — 修正後 def の下で converse が依然要する。

**Legs A/B/C/C' の資産（`TimeBandLimiting.lean`、107 decl / 0 sorry / 監査済）は本 refutation の影響を受けない**
= 有効資産。破棄しない。

### Approach（解の全体形 — gateway が先、実装は後）

```
Leg 0  修正後 def の真偽を敵対的に検査（実装ゼロ）  🚦 ✅ CLOSED（leg 13）
   │      ├ Proposal A（encoder_power → 全直線）      = FAIL  ← sub-Nyquist 漏れ、破棄
   │      ├ Proposal C（Landau-Pollak、指定退避先）   = FAIL  ← 同欠陥を継承、park 解除せず破棄
   │      └ Proposal O（点標本 → 正規直交テスト関数） = PASS  → ↓
   ▼
Leg P  def-fix: 観測写像を Karhunen-Loève 展開へ（Proposal O）  ripple は Leg 0 の見積を再測定のこと
   │      （C1 ✓ 符号語は関数 / C3 ✓ どの def にも 2W なし / C4 ✓ k は自由）
   ▼
Leg D' BddAbove を **Bessel 単独**で closure（Σᵢ⟨f,φᵢ⟩² ≤ ‖f‖² ≤ TP、k 一様、壁非依存）
   │      → contAwgn_ge_shannonHartley（leg 3、le_csSup）も transitive に closure
   ▼
Leg E  tight ≈2WT DOF カウント（LPS）← **壁はここに残る**（Legs A/B/C/C' の上に建つ）
   ▼
       contAwgn_eq_shannonHartley（Phase 4/5-full 組立）
```

**Proposal O — 観測写像を Karhunen-Loève 展開へ（Leg 0 PASS 済、Leg P のターゲット）**:

```lean
-- 現行（false を生む）: 点標本 + `Δ` 非依存の固定雑音。`√(T/n)` は Δ=1/(2W) でのみ等長
sampleCount : ℕ ; decoder : (Fin sampleCount → ℝ) → Fin M
sampledSignal f T n i = √(T/n) * f (i * (T/n))
-- Proposal O: [0,T] 台の正規直交テスト関数（k は自由のまま = C4）
testFn : Fin k → (ℝ → ℝ)
testFn_support    : ∀ i, Function.support (testFn i) ⊆ Set.Icc 0 T
testFn_orthonormal : ∀ i j, (∫ t, testFn i t * testFn j t) = if i = j then 1 else 0
-- 観測 yᵢ = ∫ (encoder m)·testFn i + zᵢ,  zᵢ ~ N(0, N₀/2) iid
-- + encoder_power も全直線へ（Proposal A の変更自体は独立に正しい／それ**だけ**では不十分だった）
```

**なぜこれが定義であって代用でないか（Leg 0 の核心）**: 正規直交族に対し白色雑音係数 `⟨ξ, φᵢ⟩` は
**厳密に** iid `N(0, N₀/2)` ⟹ `Measure.pi` が厳密（現行 `sampledSignal` は Nyquist 間隔でのみ等長 =
Nyquist を仮定して Nyquist を証明する代用だった）。教科書の整合フィルタ離散化そのもの。

**blast radius**: ⚠️ 下表は **Proposal A（field 1 本の型変更）で実測した旧値**であり **Proposal O には
適用できない**（観測写像の差し替えは `errorProbAt` / `averageError` / `contAwgnMaxMessages` の**署名**にも
及びうる）。**Leg P の最初の仕事は `scripts/dep_consumers.sh` での再実測**。旧値は参考のみ:
`ContAwgnCode` = direct 5 decl / 2 file、transitive 9 decl / 2 file
（`ShannonHartleyOperational.lean`: `.mk.inj` / `.errorProbAt` / `.averageError` / `contAwgnMaxMessages`
→ `contAwgnRate` / `contAwgnOperationalCapacity` / `contAwgn_eq_shannonHartley`。
`ShannonHartleyAchievability.lean`: `contAwgnMaxMessages_bddAbove` → `contAwgn_ge_shannonHartley`）。

**Leg D' が壁非依存で閉じる機構（Proposal O では Bessel 単独 = 旧 sup-境界ルートより単純）**:
`testFn` が正規直交ゆえ Bessel の不等式が直接効く。

```
∑ᵢ ⟨f, φᵢ⟩²  ≤  ‖f‖₂²  ≤  T·P                        — Bessel、k について一様、2W を経由しない
awgn_converse + log(1+x) ≤ x  ⟹  log M ≤ TP/N₀       — 有限 ⟹ BddAbove
```

**この上界は crude だが、Proposal A の crude 上界 `2WT²P/N₀` より真に強い**（rate `≤ P/N₀` = 広帯域極限で
**T→∞ でも有界**）。それでも `contAwgn_eq_shannonHartley` は閉じない — `ln(1+x) ≤ x` ゆえ
`P/N₀ ≥ W·ln(1+P/(W·N₀))` = SH で、**等号でない**。exact 定数には依然 `≈2WT` DOF カウント（Leg E）が要る。
**この非対称性が下記「禁止の撤回」の判別子そのもの**（偽装なら壁が消える → 消えない）。
**循環警報は鳴らない**（handoff の機械検査可能な予測: crude 経路が rate まで SH に閉じたら循環。閉じない ✓）。

**⚠️ 破棄された案（復活させないこと、根拠 → 台帳 §OBSERVATION-MAP）**:
- ~~**Proposal A 単独**（`encoder_power` → 全直線のみ）~~ = **FAIL**。sub-Nyquist で SH を超過。
  ただし `encoder_power` → 全直線という**変更自体は Proposal O の一部として維持**（A は誤りでなく不十分）。
- ~~**Proposal C（Landau-Pollak = 時間制限 + 帯域集中）**~~ = **FAIL**。旧 plan の指定退避先だったが
  **同じ観測写像欠陥を継承**（反例の補間子はエネルギーの 99.76% が窓内 ⟹ 時間制限で死なない）。park 解除せず破棄。
- ~~**per-sample 雑音分散を `(N₀/2)·2W·Δ` にスケール**~~ = **FAIL**。sub-Nyquist は塞ぐが oversampling で
  非有界に漏れる（`ν → 0` かつ信号部分空間は `≈2WT` 次元固定 ⟹ 部分空間内の総雑音 `2WT·ν → 0`）。
- ~~**`sampleCount ≥ ⌈2WT⌉` を field で要求**~~ = **数学的には動くが tier-5 で禁止**。DOF カウントを def に
  密輸 = C4 の存在理由そのもの。**honesty で reject（math で reject ではない）**。
---

## 禁止の撤回 — 「`ContAwgnCode` に全直線エネルギー field 追加は禁止」は **REVOKED**

**撤回対象**（本ファイル旧版の 4 箇所、いずれも同一趣旨）: 旧 `:164-165`（中心問題 verdict の「撤退」節）/
旧 `:205-206`（Leg W retreat line）/ 旧 `:244-245`（Leg D retreat line）/ 旧 `:293`（誠実性制約）。
文言 = 「`ContAwgnCode` へ全直線エネルギー field 追加は禁止（load-bearing tier-5、壁の偽装）」。

**なぜ書かれたか（当時は正しかった）**: WSEB=**TRUE** の枝で書かれた。WSEB が真なら
「窓エネルギー ⟹ 標本エネルギー」の tie は**実在する定理**（prolate/LPS）であり、それを証明する代わりに
field として仮定するのは **実在する壁の偽装** = tier-5。この推論は WSEB=TRUE の下で健全だった。

**なぜ今は誤りか**: **WSEB は FALSE**（`shannon-hartley-facts.md` §WSEB。6 行の解析証明、独立
`proof-pivot-advisor` が反証を試みて失敗）。**FALSE 枝が発火した**。そして旧 `:205-206` は
**同じ retreat line の中で自己矛盾していた**:

> 「WSEB が false → **`ContAwgnCode` / 容量 def の def-fix に escalate**（…全直線エネルギー field 追加は禁止 = 壁偽装 tier-5）」

= 「def-fix せよ」と「def-fix の唯一の内容を禁ずる」を 1 文で並べていた。禁止は TRUE 枝のために書かれ、
FALSE 枝に対して更新されないまま残った。**撤回は禁止の破棄ではなく、発火した枝への正しい解決**。

### 判別子 — 偽装と修正を分ける（主張でなく検査）

**偽装なら壁は消える。この修正では消えない。**

| | 壁偽装（tier-5） | Proposal O（正しい def-fix） |
|---|---|---|
| WSEB=TRUE 下で field 追加 | 実在する prolate 定理を仮定に降格 ⟹ **壁が消える** | — |
| `k ≥ ⌈2WT⌉` を field で要求 | DOF カウントを def に密輸 ⟹ **壁が消える**（Leg 0 で名指し reject） | — |
| Proposal O 適用後 | — | `BddAbove` は **Bessel 単独・壁非依存**で閉じるが、`contAwgn_eq_shannonHartley` は **依然 `≈2WT` DOF カウント（Leg E）を要する** ⟹ **壁は在るべき場所に残る** |

⟹ **`wall:nyquist-2w-dof` は Proposal O の後も retire されない**（DORMANT のまま Leg E で consumer が復活）。
壁が消えないことが、この field 追加が偽装でない**機械的に確認可能な**証拠。
**受入検査**: Leg P/D' 着地後に `contAwgn_eq_shannonHartley` が壁を要さず閉じたら、それは修正でなく偽装
（= 循環の tell）。その時は Leg 0 に差し戻す。

### 傍証 — 窓のみ拘束は「設計」でなく「事故」だった

`synthSignal_window_energy_le`（`ShannonHartleyAchievability.lean:451`、`@audit:ok`）の存在理由は
**全直線エネルギーを窓エネルギーへ降格すること**だけ:

```lean
theorem synthSignal_energy (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n) :
    (∫ t, (synthSignal T n a t) ^ 2) = (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2   -- 全直線、等号
theorem synthSignal_window_energy_le … :                                        -- ↑ を ≤ に落とすだけ
    (∫ t in Set.Icc (0 : ℝ) T, (synthSignal T n a t) ^ 2) ≤ (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2
  := by rw [← synthSignal_energy T n a hT hn]; exact setIntegral_le_integral …
```

**achievability 側は既に全直線で有界な信号を作っており、その強さを捨てている**。しかも
`scripts/dep_consumers.sh synthSignal_window_energy_le` = **direct consumers 0 decl / 0 file** =
**既に誰も使っていない**（窓のみ制約に合わせるためだけに先回りで建てられ、未使用のまま）。
⟹ **def-fix は achievability を難しくせず、むしろ易しくする**: 修正後 `encoder_power : ∀ m, (∫ t, (encoder m t)^2) ≤ T*P`
は `synthSignal_energy` の**等号がそのまま与える形**（`(T/n)∑aᵢ² = ∑cᵢ² ≤ T·P`）。
**予測（Leg P で確認）**: `synthSignal_window_energy_le` は def-fix 後に**恒久的に不要** = 削除候補。

---

## Leg 0 — 修正後 def の gateway 検査 🚦 ✅ **CLOSED（leg 13）— verdict: Proposal A/C = FAIL、Proposal O = PASS**

**目的だった**: 実装が 1 行も着地する前に、修正後 def の下で `contAwgn_eq_shannonHartley` が TRUE かを
敵対的に検査する。**gateway は仕事をした** — Proposal A は実装ゼロで反証された。

**証拠・機序・数値・教訓は台帳が SoT** → `shannon-hartley-facts.md` **§OBSERVATION-MAP**。
再検証: `python3 docs/shannon/leg0-gateway-probe.py`。ここに再キャッシュしない。

### verdict（3 行）

- **Proposal A（`encoder_power` → 全直線エネルギー）= FAIL**。`sampleCount` が自由（C4）ゆえ code は
  **Nyquist より粗く**標本でき、`sampledSignal` の `√(T/n)` は `Δ = 1/(2W)` でのみ等長 ⟹
  `s := P/(W·N₀) < 2` の全てで SH を超過（s→0 で比は非有界）。**厳密証明は整数事実に落ちる**（`5 > 4`）。
  独立 `proof-pivot-advisor` が周波数領域から再導出して確認 + 私の代替案（雑音分散スケール）を逆向きに反証。
- **Proposal C（Landau-Pollak）= FAIL**。plan が指定した退避先だったが**同じ欠陥を継承**する
  （反例の補間子はエネルギーの 99.76% が窓内 ⟹ 時間制限で死なない）。**park 解除せず破棄**。
- **Proposal O（点標本 → `[0,T]` 台の正規直交テスト関数）= PASS**。4 攻撃 + 収束テスト + 敵対的 φ 探索
  200 試行を生存。**Leg P の新ターゲット**。

### なぜ 4 攻撃が漏れを捕まえられなかったか（次の gateway 設計への入力）

**名指しの 4 攻撃はすべて*入力クラス*軸だった**（`encoder_power` を何に替えるか）。実際の欠陥は
**観測写像**軸（`sampledSignal` + `errorProbAt`）にあった。攻撃 1 は oversampling（`n → ∞`）だけを名指し、
**実際の漏れは真逆の向き**（under-sampling）— しかも oversampling は実際には漏れないことが確認された。
攻撃 1 が疑えと命じた「`√(T/n)` tight-frame ⟹ 実効ランク ≈2WT」という未検証仮説は、**疑うべき方向が
逆だった**（仮説は over 側では正しく、under 側で崩れる）。

**転用可能な tell（次の def にも適用せよ）**: **モデルがちょうど 1 つのパラメータ値でのみ較正されており、
その値が定理の証明すべき当の量であるとき、そのモデルは定義でなく代用である。** `sampledSignal` は
Nyquist 間隔でのみ等長 = Nyquist を仮定して Nyquist を証明する構図だった。

**gateway の無限後退を止める打ち切り**: 「新 def は代用か定義か」を問う 1 段のみ。Proposal O は
`Measure.pi`（独立雑音）を**厳密**にする（正規直交 ⟹ 白色雑音係数が厳密に iid）ので、この軸で止まる。
---

## Leg P — 観測写像の def-fix（Proposal O = 正規直交テスト関数）📋 **[NEXT]**

**目的**: Proposal O を適用し 3 宣言を false-as-framed から救出する。proof-log: yes。
**⚠️ 概算行数は意図的に置かない** — 旧 Leg P の「~80–150 行」は Proposal A（field 1 本の型変更）の
見積であり、Proposal O は**観測写像の差し替え**で ripple の桁が違う。**Leg P の最初の仕事は
`scripts/dep_consumers.sh` による ripple の実測**（見積を先に書くと leg 9 型の「合意された数字」になる）。

**変更（`ShannonHartleyOperational.lean`）**: `sampleCount` / `decoder` / `decoder_meas` と
`sampledSignal` / `ContAwgnCode.errorProbAt` を、Karhunen-Loève 展開へ差し替える:

- `ContAwgnCode` に `testFn : Fin k → (ℝ → ℝ)` + `testFn_support : ∀ i, Function.support (testFn i) ⊆ Set.Icc 0 T`
  + `testFn_orthonormal : ∀ i j, (∫ t, testFn i t * testFn j t) = if i = j then 1 else 0`（+ `MemLp` 等の regularity）。
  `k`（= 旧 `sampleCount`）は**自由 `ℕ` のまま**（C4 ✓）。
- 観測 `yᵢ = ∫ (encoder m)·testFn i + zᵢ`、`zᵢ ~ N(0, N₀/2)` iid。`errorProbAt` は `Measure.pi` の**まま**
  — 正規直交ゆえ白色雑音係数が**厳密に** iid（現行 def と違い代用でない）。
- `encoder_power` も**全直線へ直す**（Proposal A の変更自体は独立に正しい — Leg 0 は「A **だけ**では
  不十分」を示したのであって「A が誤り」を示したのではない。§OBSERVATION-MAP の 3 行目：A は
  `BddAbove` を TRUE にする）。窓限定のままだと `∫ f·φᵢ` が窓外エネルギーに拘束されず漏れが残る。

**同時に行う（def-fix の一部）**:
- `ContAwgnCode` docstring の defect 記述 + `@audit:defect(degenerate)` + `@audit:closed-by-successor(...)` を更新。
  **⚠️ 現 docstring は `encoder_power` を "the root cause" と名指すが Leg 0 でそれは誤りと判明** —
  修正後に残すと「修理済フィールドを欠陥と呼ぶ」誤誘導になる。**同一 commit で書き換える**。
- 3 宣言の `sorry -- @residual(defect:false-statement)` を実状に応じた tag へ:
  `contAwgnMaxMessages_bddAbove` → Leg D' で genuine（tag 消滅）/ `contAwgn_ge_shannonHartley` → 同上 /
  `contAwgn_eq_shannonHartley` → `@residual(wall:nyquist-2w-dof)` へ**復帰**（= 壁 consumer が 1 本戻る）。

**再利用資産**: `synthSignal_energy`（`ShannonHartleyAchievability.lean:398`、全直線**等号**、`@audit:ok`）が
修正後 `encoder_power` を**そのまま**満たす。`synthSignal_window_energy_le`（consumer 0）は削除候補。

**循環チェック（Leg 0 で機械接地済）**: C1 ✓（`encoder` は関数のまま）/ **C3 ✓ どの def にも `2W`/`⌊2WT⌋` が
現れない**（`testFn` は正規直交としか言わない）/ C4 ✓（`k` 自由）。**`2WT` カウントは prolate 固有値分布
からのみ出現** ⟹ 壁は Leg E に残る = **偽装でない**（判別子: 偽装なら壁が消える）。
**⚠️ 反対に `k ≥ ⌈2WT⌉` を field で課すのは tier-5 禁止**（DOF カウントを def に密輸 = C4 の存在理由そのもの。
数学的には動くが honesty で不可 — Leg 0 の独立チェッカーも同判定）。

**retreat line**: `testFn_orthonormal` を課した状態で achievability 側の code 構成が 3 turn 停滞 →
`sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)` で type-check done を保つ。
**禁止**: 3 宣言のどれかを `*Hypothesis` predicate に束ねて救出すること（tier-5）。

---

## Leg D' — `contAwgnMaxMessages_bddAbove` 壁非依存 closure 📋 **[Leg P に gated]**

**目的**: 修正後 def の下で `BddAbove` を **`wall:nyquist-2w-dof` を経由せず** genuine 化する。proof-log: yes。
概算 **~150–250 行の壁非依存 plumbing**（旧 Leg D の見積を継承 — 中身は WSEB でなく sup 境界に置換）。

**target signature（不変 = signature ripple 無し）**:

```lean
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε }
```

**構成**:
- **Bessel の不等式**（Proposal O の `testFn_orthonormal` から直接）: `∑ᵢ ⟨f, φᵢ⟩² ≤ ‖f‖₂² ≤ T·P`、
  **k について一様、`2W` を経由しない**。⚠️ 旧計画の点値 sup 境界ルート（`bandlimited_sup_bound` +
  `‖f‖_∞² ≤ 2W·T·P` ⟹ `E_s ≤ 2WT²P`）は **Proposal O では不要**（Bessel の方が単純かつ真に強い）。
  `bandlimited_sup_bound` は Leg D' からは落ちる — Leg E での再利用候補として残す。
- **`ContAwgnCode → AwgnCode` 配線**: per-observation power `P' = (∑ᵢ⟨f,φᵢ⟩²)/k` で `AwgnCode M k P'` を構成
  （`power_constraint` は構成から成立）。
- **`errorProbAt` 等式**: `ContAwgnCode.errorProbAt`（`Measure.pi` の per-observation AWGN）=
  `AwgnCode` 側の離散 `errorProbAt`。**⚠️ Proposal O で観測が `⟨f, φᵢ⟩` に変わるので、親 Phase 3 の
  verbatim 確認（`sampledSignal = cᵢ`）は無効 — Leg P 後に取り直すこと**。
- **`awgn_converse` + `log(1+x) ≤ x`**: `log M ≤ (∑ᵢ⟨f,φᵢ⟩²)/N₀ + Fano ≤ TP/N₀ + Fano`（k 一様）。
- **Fano 再配置**（`ε<1` 使用）+ edge case（`n=0` / `M<2`）+ **ℕ-sSup 罠**（unbounded `sSup` は junk `0`）。

**再利用資産**: `awgn_converse`（`AWGN/Converse.lean:607`、genuine）+ Mathlib の Bessel 不等式
（`inner_mul_le_norm_mul_norm` 族 / `Orthonormal.sum_inner_products_le` — **Leg D' 着手時に loogle で
verbatim 確認すること**、ここに署名をキャッシュしない）。
**Legs A/B/C/C'（作用素論）は参照しない** — reduction はスカラー。
**feasibility**: **self-buildable・壁非依存**（Leg 0 PASS 済 = 条件付きでなくなった）。
**consumer wiring**: `contAwgn_ge_shannonHartley`（`ShannonHartleyAchievability.lean:488`）が `le_csSup` で消費
⟹ Leg D' genuine 化で **leg 3 も transitive に closure**。

**retreat line（新 route 用）**: 修正後 def の下で Leg D' の plumbing が **3 turn 超で停滞**したら
`sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)`。**この撤退は honest** — 修正後 def の下で
statement は**真**であり（Leg 0 PASS 済）、残るのは配線だけだから。
**禁止（不変）**: `BddAbove` の core を `≥` 定理へ hyp 化 / `*Hypothesis` predicate に束ねる（tier-5）。
**`wall:nyquist-2w-dof` へは退避しない** — この route は壁を経由しないので、詰まりは壁でなく plumbing。

---

## Leg E — tight concentration `prolate_eigenvalue_count`（LPS）📋 **[壁が残る場所]**

**目的**: `#{n | 1/2 < prolateEigenvalues T W n}` の `⌊2WT⌋ + O(log WT)` 集中（Landau-Pollak-Slepian）。
`contAwgn_eq_shannonHartley` の exact 定数に必須。proof-log: yes（撤退 rationale）。**Phase-4 専用**。
Legs A/B/C/C' の上に建つ（それらは本 refutation の影響を受けない有効資産）。

**位置づけ**: **`wall:nyquist-2w-dof` の live consumer が復活するのはここ**（現在 0 = DORMANT）。
`@residual(wall:nyquist-2w-dof)` は本 leg の sanctioned 撤退口。
**genuine wall 公算大**（研究フロンティア）だが、**family 丸ごとの壁宣言の前に gateway atom を 1 本 dispatch する**
（CLAUDE.md gateway-atom-first）。loogle の過去 `Found 0` は**必要条件であって十分条件でない** — 壁宣言時は
two-stage conclusion-shape 検索 + template lemma 行数見積 + **in-project 先行 grep**（`cause:loogle-blind`、
本 family で 2 度発火）を揃える。

**循環チェック（最重要）**: `2WT` は本カウントの**結論**としてのみ現れ、`prolateEigenvalues` /
`timeBandLimitingOp` の def の入力ではない（C3 ✓）。**statement は `True` placeholder でなく実不等式で書く**。
**retreat line**: `sorry + @residual(wall:nyquist-2w-dof)`（compound 化しない）。

---

## Leg W — 終了（WSEB）❌ **命題が FALSE**

**Leg W は「probe 保留 / make-or-break / UNKNOWN」ではない。FALSE 枝が発火し、leg は閉じた。**
`sup{f(0)²/∫₀ᵀf² : f ∈ PW_W} = +∞` ⟹ WSEB 不等式は成り立たない。
⟹ **`wseb` を statement として建てない**（偽の命題に自前構築すべき理論はない）。
Leg D（旧・WSEB 経由の BddAbove）は as-framed で dead → **Leg D' が置換**（sup 境界経由、def-fix 後）。

詳細（6 行の解析証明 / 倍精度アーティファクト / forward-evaluated witness 276.29 / 単調性違反）→
`shannon-hartley-facts.md` §WSEB・§REVOKED・§NUMERIC-TRUE-ARTIFACT。**ここに再キャッシュしない**。

---

## 完了 leg（圧縮 — 履歴は git）

| Leg | 成果 | commit |
|---|---|---|
| A | 作用素 `A := P_W ∘L Q_T ∘L P_W` + 自己共役 + 正 + `‖A‖≤1`、新 file `TimeBandLimiting.lean` | 4d848a53 |
| B | `timeBandLimitingOp_isCompact`（4 leaf 全 genuine、reusable な L²-kernel⟹compact を含む） | d16a74e1 |
| C | `prolateEigenvalues` 降順列挙 framework（counting-function の一般逆、`0 < c` guard 必須） | de758f19 / 監査 77a5fdf2 |
| C' | 非空虚性 `prolateEigenvalues_zero_pos`（framework が spectral content を運ぶことを確定） | a040a456 / 監査 569c48f0 |
| 境界 | `timeLimitSubspace_eq_bot_of_nonpos` 他、退化 4 クラスの tightness が compiler-backed | a7595371 |

**これらは WSEB refutation の影響を受けない**（作用素論の資産であり、`ContAwgnCode` の def に依存しない）。
Leg E の土台として保持する。

---

## 残債

- [ ] **`∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）**。`λ 0` の atom より厳密に
      大きい obligation（`A` が無限 rank であることを要す）。退化側は解決済（a7595371 の
      `prolateEigenvalues_eq_zero_of_*` が全 `n` で成立）ゆえ **`0<T`, `0<W` regime だけ**見ればよい。
  - ⚠️ **罠（採るな）**: 「`_hasEigenvalue` の `≠ 0` 仮説は除去可能」— 監査により**実際に除去可能**と確定
    （`ker A ⊇ ker P_W ≠ ⊥` ゆえ `0` は常に固有値）。**だが除去してはいけない**: `λ n = 0` かつ `0` が固有値なら
    結論は自明成立 = 無条件形は pin する内容が厳密に**少ない**。仮説は「必要だから」でなく **content のため**に残す。
- [ ] **散文 de-tag 3 件**（いずれも prose、tag 構文ではない。コードの意味は変えない）:
  1. **`ShannonHartley.lean:29-31`** — module docstring が「reduces the whole gap to the single genuine Mathlib wall
     `@residual(wall:nyquist-2w-dof)`」と**偽**を述べ、かつ**phantom `@residual(wall:nyquist-2w-dof)` トークン**を含む。
     `rg 'nyquist-2w-dof' InformationTheory/` = 3 hit のうち**唯一の `@residual(...)` 形**ゆえ、
     **0-consumer の壁の SoT grep 数を水増ししている**。散文へ de-tag する（他 2 hit =
     `Operational.lean:459` / `TimeBandLimiting.lean:1459` は既に散文）。
  2. **`ShannonHartleyAchievability.lean:459`** — section header が `§E — boundedness of the message set (wall-gated)`
     のまま。**wall-gated ではない**（false-statement → def-fix 後は壁非依存）。
  3. **`Operational.lean:360–363` の `sampledSignal` docstring** — brief の指示は「`d2938749` で修正済ゆえ再修正でなく
     **確認**」。**確認結果 = 修正済だが行番号がずれている**: 当該 docstring は現在 **`:388-395`**（def は `:396`）で、
     `:360-363` は今や `ContAwgnCode` docstring の defect 説明。`:393-395` は
     「The two energies agree only in the limit, not at fixed `n`: for `n = 1` the discrete energy is `T · f(0)²` …
     it is false」= **正しく修正済**。**追加作業なし**（Leg P で def-fix 後に「it is false」の時制のみ要更新）。
- [ ] **`audit-tags.md` の kind 語彙に exact な受け皿が無い**（本 plan の write scope 外 = 報告のみ）:
      「inhabited かつ内部整合だが、意図した対象を under-constrain する def」に対し `ContAwgnCode` は
      `@audit:defect(degenerate)` を**最寄りの近似**として担いでいる（auditor の判断 + stretch は記録済）。
      新 kind **`under-constrained`**（cause `signature-drops-constraint`）が exact な受け皿。promote 判断は
      audit-tags.md の owner に属す。

---

## 誠実性制約（explicit）

- **3 宣言の `sorry` は充填不能**（命題が偽）。`@residual(defect:false-statement)` +
  `@audit:defect(false-statement)` + `@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` の
  3 点セットを **def-fix 完了まで維持する**。これは audit-tags.md **「`defect` の (b) 用法」= 正規**であり、
  **signature が defect 形のまま残るのが正しい状態**（監査は撤回してはならない — 撤回先が存在しない）。
- **`ContAwgnCode` への全直線エネルギー field 追加は REVOKED = 許可**（上記「禁止の撤回」)。
  **ただし判別子を満たすこと**: 修正後も `contAwgn_eq_shannonHartley` が `wall:nyquist-2w-dof`（Leg E）を
  要すること。壁が消えたら偽装 ⟹ Leg 0 へ差し戻し。
- **load-bearing hyp bundling 禁止（不変）**: WSEB / concentration / compact / BddAbove を
  `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate に束ねて仮説で渡さない。
  **`≥` 定理へ `BddAbove` を hyp 化しない**。
- **Leg D' の詰まりは `wall:nyquist-2w-dof` へ退避しない** — この route は壁を経由しない（詰まり = plumbing）。
  退避先は `@residual(plan:shannon-hartley-phase2-spectral-plan)`。
- **Leg E の詰まりのみ `wall:nyquist-2w-dof`**（同一 family 集約、compound 化しない）。**新 slug は**
  loogle-0 + two-stage conclusion-shape 検索 + template lemma 行数見積 + **in-project 先行 grep** が揃った時のみ。
- **def body に sorry 不可**: `prolateEigenvalues` は real def。`ContAwgnCode` の field も同様
  （def-fix は field の**型**を直す = sorry を置く場所ではない）。
- **散文に「壁である/ない」をキャッシュしない**。コードの `@residual` が SoT、高コストな事実は
  `shannon-hartley-facts.md` にリンク（re-derive > cache）。
- 実装 owner が新 sorry + `@residual` を commit したら **独立 honesty audit を同セッションで起動**（CLAUDE.md）。

---

## 循環チェック（C3 受入基準・全 Leg 集約）

**C3**: 定数 `2W`/`⌊2WT⌋` は **`prolate_eigenvalue_count`（Leg E）の結論としてのみ** 現れ、どの def の入力にも現れない。

- `timeBandLimitingOp T W` の `W` = 物理帯域幅（入力）≠ DOF カウント `2W`。✓
- `prolateEigenvalues` = spectrum から定義、`2WT` 非入力。✓
- **Leg P（def-fix）**: 全直線エネルギー `∫ t, f² ≤ T·P` は物理電力予算 = model 制約。`2W`/`⌊2WT⌋` 非出現、
  codeword はサンプルベクトルでなく関数のまま（C1 ✓）、`sampleCount` 自由（C4 ✓）。✓
- **Leg D'**: `BddAbove` は `E_s ≤ 2WT·(T·P)` で bound。**`2W` は `bandlimited_sup_bound` の結論由来**
  （`|f t| ≤ √(2W)·‖f‖₂` = Paley-Wiener の帰結）で def の入力ではない。EXACT `⌊2WT⌋` 不要。✓
- Leg E で初めて `2WT` が**カウントの結論**として出る。✓

**tell（循環兆候）**: `contAwgn_eq_shannonHartley` が `rfl`/`unfold` のみで済む、`prolateEigenvalues` def に
`2WT` 出現、reduction が per-sample capacity をそのまま返す、**`contAwgn_eq_shannonHartley` が壁なしで閉じる**
（← def-fix 特有の新 tell、上記「判別子」）。

---

## ripple / import

- **signature 変更あり（Leg P）**: `ContAwgnCode.encoder_power` の**型**が変わる。blast radius は実測
  **direct 5 decl / 2 file、transitive 9 decl / 2 file**（上記 Approach の表）。consumer の署名は不変
  （capacity 3 本 + `errorProbAt`/`averageError` は field を読まない）ゆえ実質 touch は
  **`ContAwgnCode` を構成する achievability 側**のみ。
- **Leg D' は signature 変更なし**（既存 sorry を fill）。
- **import cycle なし**: `TimeBandLimiting.lean`（Legs A/B/C/C'/E）は Mathlib spectral/Fourier +
  `NormalizedSinc`/`WhittakerShannon` を import。Leg P/D' は `ShannonHartleyOperational.lean` /
  `ShannonHartleyAchievability.lean` 内（`AWGN.Converse` の `awgn_converse` を消費、作用素 file に依存しない）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ（≤ 10 entry）。

1. **WSEB=FALSE で本 plan の負債が「壁 self-build」から「def-fix + 壁 self-build」の 2 本に増えた（leg 12、
   `d2938749`/`67e1ff3f`）**: 3 宣言（`contAwgnMaxMessages_bddAbove` / `contAwgn_eq_shannonHartley` /
   `contAwgn_ge_shannonHartley`）は false-as-framed で、コード側が
   `@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` = **本 plan を def-fix の負い手に名指し**。
   根本原因 `ContAwgnCode.encoder_power` の窓のみ拘束（`cause:signature-drops-constraint`）。
   `wall:nyquist-2w-dof` は live consumer 0 = DORMANT だが **retire しない**（修正後 def の converse が要する）。
   settled facts → `shannon-hartley-facts.md`（再キャッシュしない）。
2. **「全直線エネルギー field 追加は禁止」を REVOKED（active、上記「禁止の撤回」節が SoT）**: 禁止は WSEB=**TRUE** の枝で
   書かれ（真なら実在する prolate 定理の偽装 = tier-5）、**FALSE 枝が発火した**のに更新されず、旧 `:205-206` で
   「def-fix に escalate」と**同一文中で自己矛盾**していた。**判別子 = 偽装なら壁が消える / この修正では消えない**
   （BddAbove は壁非依存で閉じるが `eq` は Leg E を要する）。**傍証**: `synthSignal_window_energy_le`
   （`:451`、`@audit:ok`、**consumer 0 = 既に未使用**）は全直線エネルギーを窓へ降格するためだけに存在し、
   `synthSignal_energy`（`:398`）の**全直線等号**が修正後 field をそのまま満たす ⟹ **def-fix は achievability を
   易しくする**。窓のみ拘束は設計でなく事故だった。
3. **Leg 0（gateway）を Proposal A の block に置く（active、make-or-break）**: **修正後 def で
   `contAwgn_eq_shannonHartley` が TRUE になることを誰も検査していない**。leg 9 の失敗の本体は
   「三者が『どれくらい難しいか』を問い、誰も『そもそも真か』を問わなかった」こと
   （§NUMERIC-TRUE-ARTIFACT）。⟹ 実装が 1 行も着地する前に 4 攻撃（オーバーサンプリング / 非時間制限 /
   退化境界 2 種以上 / textbook strength diff）を通す。**UNKNOWN のまま Leg P へ進むことは禁止**。
4. **orchestrator の「オーバーサンプリングは漏れない」理由付けは 2 通りあり、片方は壁を誤輸入する（active、
   Leg 0 で決着させる）**: 「雑音が固定 `≈2WT` 次元部分空間に射影される」は **DOF カウント = 壁そのもの**を
   前提するので、これを BddAbove の正当化に使うと BddAbove が壁 gated に戻る（= 2026-07-15 の
   under-estimation 是正が生じた経路と同型）。**Leg D' の実 route はこれを要さない** —
   `bandlimited_sup_bound`（点値 sup、`@audit:ok`）+ `√(T/n)` Riemann 正規化（`:396-397` verbatim 確認済）だけで
   `E_s ≤ 2WT·(T·P)` が n 一様に出る。⟹ 正当化は **sup 境界側**を採り、部分空間次元側は採らない。
5. **crude BddAbove は rate を閉じない（active、設計上の期待値の固定）**: Leg D' の上界は
   `log M ≤ 2WT²P/N₀` で、rate `limsup_T (log M)/T ≤ 2WTP/N₀` は **T→∞ で発散**する。
   これは欠陥ではなく**期待どおり**: BddAbove（各 T で有限）は閉じるが exact 定数
   `W log(1+P/(N₀W))` には `≈2WT` DOF カウント（Leg E）が要る。**この非対称性が判断ログ #2 の判別子の実体**。
   Leg D' が rate まで閉じてしまったら循環を疑う。
6. **Proposal C（Landau-Pollak）は park、削除しない（active）**: 時間制限 + 帯域集中は LPS により忠実だが
   ripple が桁違い（`IsBandlimited` の使われ方を書き換える）。**Leg 0 が Proposal A を反証したときの撤退先**。
   Leg 0 の strength diff（攻撃 4）で「Proposal A が Wyner に着地するか」を確認し、着地しないなら本 park を起こす。
