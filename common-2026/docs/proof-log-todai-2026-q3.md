# 東大 2026 第3問 Lean 形式化 — 作業ログ

2026-05-06、Claude Opus 4.7 (1M context) による単発セッション。
将来の Mathlib 検索ツール開発のベースラインとして、
**実際に何を試して何が動いたか / 動かなかったか** を可能な限り粒度高く残す。

## 0. 対象問題と成果物

東大 2026 数学 第3問:

座標空間内の原点を中心とする半径 5 の球面 S 上に、相異なる 3 点 P, Q, R が
- P, Q は xy 平面上
- 三角形 PQR の重心が G(2, 0, 1)

の条件で動く。

- **(1)** 線分 PQ の中点 M の軌跡 → 円 (x − 3)² + y² = 4 から (5, 0) を除いたもの
- **(2)** 線分 PQ が通過する範囲 → 大円板 ∩ 双曲線 (x−3)²/4 − y²/5 ≤ 1 の左側 から (5, 0) を除いたもの

成果物 (最終形):

| ファイル | 行数 |
|---|---|
| `Common2026/T_Q3_1.lean` | 287 |
| `Common2026/T_Q3_2.lean` | 436 |
| `docs/proof-log-todai-2026-q3.md` | このファイル |

`lake build Common2026` (2688 jobs) クリーン通過、`sorry` ゼロ。

## 1. 定量サマリ

(目視カウント、誤差 ±2)

| 操作 | 回数 | 備考 |
|---|---|---|
| Bash 呼び出し | 約 20 | うち `lake env lean Common2026/T_Q3_*.lean` が約 12 回 |
| Edit | 約 20 | 部分的修正、特に T_Q3_2 の逆方向で多数 |
| Read | 約 10 | 既存 T_Q1/T_Q2、T_Q3_1/2 の自分の途中ファイル |
| Write | 3 | T_Q3_1.lean、T_Q3_2.lean、proof-log |
| TaskCreate | 8 | サブタスク分解 |
| TaskUpdate | 約 10 | ステータス遷移 |
| `lake env lean` 失敗 (エラー) | 約 7 回 | 修正 → 再走の繰り返し |
| `lake build` 成功 | 4 | 中間と最終 |
| WebSearch / WebFetch / mathlib 検索 | **0 回** | 補題名は記憶頼み、これが反省点 |

ツールコール総計 ≈ 70。

セッションの総時間は把握していないが、思考時間 + 編集時間で 1 時間〜2 時間相当の集中作業。

## 2. 数学解法 (要点)

P = (p₁, p₂, 0), Q = (q₁, q₂, 0), R = (r₁, r₂, r₃)
- 球面: p₁² + p₂² = 25, q₁² + q₂² = 25, r₁² + r₂² + r₃² = 25
- 重心 (2, 0, 1): p₁+q₁+r₁ = 6, p₂+q₂+r₂ = 0, r₃ = 3
- ⇒ r₁² + r₂² = 16

**(1)** M = (x, y) = ((p₁+q₁)/2, (p₂+q₂)/2) ⇒ r₁ = 6−2x, r₂ = −2y
⇒ (6−2x)² + 4y² = 16 ⇔ (x−3)² + y² = 4。
M = (5, 0) では P = Q となり除外。

**(2)** A = (x, y) が線分 PQ 上 ⇔ A·M = |M|² (線上) かつ |OA|² ≤ 25 (端点内)。
M を陽に動かして条件を整理: 線形条件 (6−x) m − y n = 5 と小円の交点存在
⇔ Cauchy–Schwarz より (3x−13)² ≤ 4 ((6−x)² + y²)
⇔ 5(x−3)² − 4y² ≤ 20 (双曲線内側)。

「右枝が円板と交わるのは (5, 0) のみ」「(5, 0) でなければ線形方程式上に
(5, 0) が乗らないので除外条件に注意せず取れる」が形式化での鍵。

## 3. 時系列ワークログ (試行錯誤を含む)

### Phase 1 — 問題理解と既存コード調査

1. PDF (`docs/todai_2026.pdf`) のページ 3 を `Read pages:"3"` で取得。
   問題文を画像化されているため Claude が読解。
2. `ls Common2026/` で既存ファイル一覧。`T_Q1_1`, `T_Q1_2`, `T_Q2_1`, `T_Q2_2` の存在を確認。
3. `T_Q1_1.lean`, `T_Q2_1.lean`, `T_Q2_2.lean` を Read してプロジェクト規約と style を吸収:
   - 名前空間 `Common2026.X_QY_Z`
   - 先頭にコメントブロックで問題文と方針
   - `Mathlib` ではなく必要な戦術ごとに import
   - 主結果 `theorem` を最終ゴールとし、補助は `private lemma`
4. `proof-log-todai-2026-q2.md` の冒頭を読んで「ボトルネック分析を残す」というスタイルを把握。
5. **数学を紙で解いた** (Claude の thinking 内で代数操作)。Thales 円・Cauchy–Schwarz の発想は
   思考フェーズで自力導出。本セッション中に文献検索や WebSearch は使わなかった。

### Phase 2 — T_Q3_1 (中点軌跡)

#### 2.1 設計

- `structure Config` で P : ℝ × ℝ, Q : ℝ × ℝ, R : ℝ × ℝ × ℝ と球面・重心条件をパッケージ。
- `def Locus M := (M.1 - 3)^2 + M.2^2 = 4 ∧ M ≠ (5, 0)` で軌跡を定義。
- `def IsMidpoint M cfg` で「M は cfg.P, cfg.Q の中点」。
- 主定理 `theorem locus_iff M : (∃ cfg, IsMidpoint M cfg) ↔ Locus M`。

#### 2.2 一発書き

T_Q3_1.lean は **最初の Write でほぼ全体を書き上げ** (220 行程度)、一発走行で
- `push_neg` の deprecation 警告のみ

という結果。完全成功ではないが、エラーゼロ・警告 1。
比較的シンプルな代数 (sphere・centroid・sqrt 構成) なので、
事前の数学整理が効いた。

#### 2.3 修正履歴 (T_Q3_1)

| ステップ | 操作 | 内容 |
|---|---|---|
| 1 | Edit | `push_neg` を `not_lt.mp` に置換 |
| 2 | Bash | `lake env lean Common2026/T_Q3_1.lean` → `Unknown identifier 'le_of_not_lt'` |
| 3 | Edit | `le_of_not_lt` → `not_lt.mp` (こちらが正解) |
| 4 | Bash | クリーンに通る (出力空) |

`le_of_not_lt` は **存在しなかった補題**。Mathlib では `not_lt.mp` が正解。
これは将来のツールが「`a < b` の否定から `b ≤ a` を得る」検索に対し
正しいシンボル名を返すべきポイント。

#### 2.4 後の Q3_2 のためのリファクタ

Q3_2 で `mkLocusConfig` を呼びたくなったので、Q3_1 の中で
inline で書いていた構成を **named def に切り出した**:

- `mkσ m`, `mkρ m` (Real.sqrt)
- `mkP m n`, `mkQ m n`, `mkR m n`
- `mkσ_sq`, `mkρ_sq`, `mkσ_pos`, `mkρ_pos`
- `mkP_add_mkQ_fst/snd`, `mkP_sphere`, `mkQ_sphere`, `mkR_sphere`, `mkP_ne_mkQ`
- `mkLocusConfig (m n hCircle hNotFive) : Config`
- `mkLocusConfig_P`, `mkLocusConfig_Q` (`@[simp]` lemma)

この時点で `private` と書いていた `m_ge_one_of_locus`, `m_lt_five_of_locus` を
public にした。

リファクタ後の T_Q3_1 ビルドはノートラブル。

### Phase 3 — T_Q3_2 順方向 (segment ⇒ SweptRange)

#### 3.1 想定

`A ∈ SweptRange` の 3 つの連言:
1. x² + y² ≤ 25 (disk)
2. 5(x−3)² − 4y² ≤ 20 (hyperbola)
3. A ≠ (5, 0)

順方向は cfg + t ∈ [0, 1] が与えられたときに 3 条件を導く。

#### 3.2 disk_of_segment

`A.1 = (1−t) P.1 + t Q.1` 等から
`A.1² + A.2² = (1−t)² · 25 + 2t(1−t)(P·Q) + t² · 25`、
`P·Q ≤ 25` (Cauchy–Schwarz 系) で `≤ 25`。

`nlinarith [cfg.hP, cfg.hQ, dot_le_of_sphere cfg, mul_nonneg ht0 (...), sq_nonneg t, sq_nonneg (1-t)]`
で一発。**nlinarith が二次の積を扱えること**を信用した。動いた。

#### 3.3 midpoint_on_circle

最初は「Q3_1 の `circle_eq_of_config` を呼ぼう」と考えたが、
**それは private** だった (Q3_2 から呼べない) ので **再導出**。
ほんの数行 (重心 → R → R²+ → 4) なので問題なし。

#### 3.4 dot_eq_of_segment

A·M = M·M を示す。直接 `nlinarith [cfg.hP, cfg.hQ]` で一発。
A ・ M = ((1-t)P + tQ) · (P+Q)/2 = (25 + P·Q)/2 = M·M を背景に持つが、
nlinarith が「中点を取って線形結合する」発想を機械的に再現してくれた。

#### 3.5 hyperbola_of_segment

ここが順方向の数学的山場。
`(M.1 - 3)² + M.2² = 4` と `A · M = M · M` から、`(6-x)·a - y·b = 3x - 13`
(a := M.1 - 3, b := M.2) を導き、Cauchy–Schwarz で `(3x-13)² ≤ 4·((6-x)² + y²)`。

Cauchy–Schwarz は `nlinarith [sq_nonneg ((6-A.1)*b + A.2*a)]` というヒントで誘導。
**`(ax - by)² + (ay + bx)² = (a²+b²)(x²+y²)` から `(ax-by)² ≤ (a²+b²)(x²+y²)`**
という古典恒等式を知っているとヒントが書きやすい。

#### 3.6 ne_five_zero_of_segment

A = (5, 0) を仮定して矛盾を導く。
A が線分 PQ 上で |A| = 5 だと A は端点のみ、結局 P = Q = (5, 0) で `cfg.hPQ` に矛盾。

このパスでは:
- `hyperbola_of_segment` を使うと等号成立条件 ⇒ M = (5, 0) になり、
  そこから P = Q を導く (15 行程度)。
- 別解として中点 M も (5, 0) であることを `dot_eq_of_segment` から導いてもよい。
- 結果的に後者を採用 (M = (5, 0) のときに P = Q を出す部分は短い)。

#### 3.7 ハマり: midpointOf の noncomputable と `unfold`

`midpointOf cfg : ℝ × ℝ := ((P.1+Q.1)/2, (P.2+Q.2)/2)` は実数除算なので
`noncomputable def` が必要。これに最初気付かず:

```
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Real.instDivInvMonoid'
```

を Edit 1 回で修正。

次に `unfold midpointOf at hM1_eq` が **「let に対しては効かない」**罠。
やむなく `midpointOf_fst`, `midpointOf_snd` を `rfl` で証明し `rw` で展開する補助補題を追加。

```
lemma midpointOf_fst (cfg : Config) :
    (midpointOf cfg).1 = (cfg.P.1 + cfg.Q.1) / 2 := rfl
```

順方向はここまでで概ね完成 (Edit 4回くらい)、Bash 走行 2 回でクリーン。

### Phase 4 — T_Q3_2 逆方向 (構成パート、最大の難所)

ここから **長い試行錯誤**。Edit 約 12 回、Bash 約 8 回。

#### 4.1 設計 v1: M を陽に与え、Q3_1 の `exists_config_of_locus` を再利用

最初 `exists_config_of_locus M h : ∃ cfg, IsMidpoint M cfg` を呼ぶつもりだった。
だが「∃」で隠されるので、A on segment の証明で cfg.P, cfg.Q を使えない。

→ Q3_1 をリファクタして **`mkLocusConfig` を named def として公開** することにした。
   `mkP`, `mkQ`, `mkR` も公開。

#### 4.2 設計 v2: M を陽に構成し、`mkLocusConfig` で cfg を作り、t を陽に与える

具体構成:

```
D := (6 − x)² + y²
E := 4 D − (3x − 13)²
sqrtE := √E
m := 3 + ((6−x)(3x−13) + y · sqrtE) / D
n := (−y(3x−13) + (6−x) · sqrtE) / D
```

代数恒等式:
- a² + b² = D · ((3x−13)² + sqrtE²) = 4 D²  (a, b は分子)
- (6−x) a − y b = D (3x − 13)

#### 4.3 ハマり 1: `set` + `field_simp` の相互作用

```
set D := (6 - x)^2 + y^2 with hD_def
set a := ...
...
have h_a2_b2 : a^2 + b^2 = 4 * D^2 := by ring
...
-- (m - 3)² + n² = 4 の証明
rw [h_simp, h_a2_b2]
-- goal: 4 * D^2 / D^2 = 4
field_simp
```

ここで `field_simp` が `set` で導入した `D` を **let-展開** してしまい、
目標が

```
-468 + x * 264 - x * y * sqrtE * 2 - x * y^2 * 3 - x^2 * 49 + x^3 * 3 + ... =
-468 + x * 264 + x * y^2 * 3 - x^2 * 49 + x^3 * 3 - y^2 * 13
```

という巨大な多項式に展開された。

**解決策**: `clear_value a b D` で let を不透明な仮定に変換。
これで `field_simp` は a, b, D を atomic 変数として扱い、`/D` と乗除のみクリアする。

```
have h_a2_b2 : a^2 + b^2 = 4 * D^2 := by ...
have h_lin_combo : ... := by ...
clear_value a b D
refine ⟨3 + a/D, b/D, ?_, ?_, ?_⟩
```

この `clear_value` の発想に至るのに 3 回の Bash → エラー → 思考のループが必要だった。
**将来のツールでは「set した変数が field_simp で展開されるとき clear_value を提案」が望ましい。**

#### 4.4 ハマり 2: 線形結合の符号ミス

`(6 − x) · a + y · b = D · (3x − 13)` と書いたが、b = −y(3x−13) + (6−x)·sqrtE のため
`y · b` は `−y²(3x−13) + y(6−x)·sqrtE`。

(6−x) · a + y · b の sqrtE 成分: `(6−x)·y + y·(6−x) = 2(6−x)y` で打ち消えない。
正しくは `(6 − x) · a − y · b` で sqrtE が消える。

これは `ring` がエラーを出して気付いた。Edit 1 回で修正。

**Mathlib 検索ツールの観点**: 「線形結合で sqrt を消す」は構文的には ring の範囲だが、
**符号を機械的に検算してくれる仕組みがほしい**。今回は手で展開して確認したが、
小さな計算ミスを ring に投げるのは品質保証として遅い。

#### 4.5 ハマり 3: `div_add_div_same` が見つからない

```
rw [div_pow, div_pow, div_add_div_same, ...]
-- error: Unknown identifier `div_add_div_same`
```

Mathlib には `div_add_div_same` という名前は無い (またはリネーム済み)。
正しくは `add_div : (a + b) / c = a / c + b / c`。逆方向 rewrite には `← add_div`。

```
rw [div_pow, div_pow, ← add_div]
```

これで `a^2/D^2 + b^2/D^2 = (a^2 + b^2)/D^2` が得られる。

**Mathlib 検索ツールの観点**: 「a/c + b/c を (a+b)/c に書く補題」を
直接検索できるとよい。今回は `div_add_div_same` という英語直訳でハズレた。

#### 4.6 ハマり 4: `(m, n) ≠ (5, 0)` の証明での polynomial expansion

`m = 5, n = 0` を仮定し、`a / D = 2`, `b / D = 0` から `a = 2D, b = 0` を得たい。
`field_simp at h1` を使うと中身を展開して polynomial 化されてしまう。

**解決策**: `(div_eq_iff hD_ne).mp h1` を直接使う:

```
have h1 : a / D = 2 := by linarith
have := (div_eq_iff hD_ne).mp h1
-- this : a = 2 * D
linarith
```

この `div_eq_iff` 補題に到達するまで `field_simp at` で 2 回失敗。
**将来のツール**: 「a / b = c ⟹ a = c * b」を直接検索できると速い。

#### 4.7 ハマり 5: u² ≤ 1 の派生

`u := mkρ m * (n - y) / (mkσ m * m)` に対し u² ≤ 1 を示すのに、
鍵不等式 `(6m − 5)(y − n)² ≤ (30 − 6m) m²` を経由する。

第一試行: 直接 `nlinarith [hLine, hMsq, hDisk, sq_nonneg (m * (x-m) + n * (y-n))]`
等のヒントで一発を狙ったが、**nlinarith は積の連鎖を勝手にやらない**ためダメ。

最終策: `key_sq_ineq` という補助補題に切り出し、内部で

1. `m(x − m) = −n(y − n)` (線形条件と m² + n² = 6m − 5 から)
2. `m²(x−m)² = n²(y−n)²` (両辺二乗)
3. `m²((x−m)² + (y−n)²) = (6m−5)(y−n)²` (移項と置換)
4. `|A − M|² ≤ 30 − 6m` (disk から)
5. 結合

を **明示的にステップを書く**。`linarith` と `nlinarith` を交互に使う。

#### 4.8 ハマり 6: `div_le_iff₀` のパターン照合失敗

```
rw [div_pow, mul_pow, hρ_sq, h_yn_sq, mul_pow, hσ_sq]
-- goal: (6m - 5) * (y - n)^2 / ((30 - 6m) * m^2) ≤ 1
rw [div_le_iff₀ hσm_sq_pos]
-- error: Did not find an occurrence of the pattern
--   ?m / (mkσ m * m)^2 ≤ ?
```

`hσm_sq_pos : 0 < (mkσ m * m)^2` だが、上の rewrite で
`(mkσ m * m)^2` が `(30 - 6m) * m^2` に置換済みなので **マッチしない**。

**解決策**: `div_le_one` を使い、置換の順序を変える:

```
rw [div_le_one (by positivity : (0:ℝ) < (mkσ m * m)^2)]
rw [mul_pow, hρ_sq, hσ_sq]
```

このとき rewrite 後の formula と hypothesis の形が一致するように 1 ステップ前で
分母条件を消費する。**Mathlib のリライト戦術は順序敏感** で、ここで 5 分溶けた。

#### 4.9 ハマり 7: `field_simp; ring` の "No goals to be solved"

最後の `(x, y).1 = (1-t) P.1 + t Q.1` の証明で:

```
have h_u_form : u * (mkσ m * n / mkρ m) = n * (n - y) / m := by
  show ...
  field_simp; ring
```

`field_simp` 単独で目標が閉じてしまい `ring` が "No goals to be solved" になった。
Edit 1 回で `; ring` を削除。**field_simp は強力で、ring を呼ばずに完結することがある**。

#### 4.10 ハマり 8: LSP のキャッシュ

T_Q3_1 を Edit するたびに、T_Q3_2 の方で「`mkρ` is unknown identifier」が
LSP 通知として残り続けた。実態は `lake build Common2026.T_Q3_1` で olean を
書き直さないと T_Q3_2 が古い olean を読むため。

**`lake build` を明示的に走らせる**ことで解決。本来は `lake env lean Common2026/T_Q3_2.lean`
が transitively rebuild すべきだが、Mathlib 規模だと挙動が遅延する印象。

### Phase 5 — 最終 build と log

1. `Common2026.lean` に `import Common2026.T_Q3_1` と `T_Q3_2` を追加
2. `lake build Common2026` で 2688 jobs 通過
3. proof-log v1 を執筆 (152 行)
4. ユーザーから「定量情報や試行錯誤も含めて拡充して」との指示
5. このログ v2 に上書き拡充

## 4. Mathlib 補題の利用記録

成功したもの (本セッションで実際に使った):

| 補題 / 戦術 | 用途 |
|---|---|
| `Real.sqrt_pos`, `Real.mul_self_sqrt` | sqrt の正値・二乗 |
| `pow_eq_zero_iff` | x^2 = 0 から x = 0 |
| `mul_eq_zero` | a · b = 0 から場合分け |
| `mul_pos`, `mul_le_mul_of_nonneg_left` | 不等式合成 |
| `div_eq_iff`, `div_self`, `mul_div_assoc`, `add_div`, `sub_div` | 除算の操作 |
| `div_le_one`, `div_le_iff₀`, `div_pow`, `mul_pow` | 不等式と除算 |
| `not_lt.mp` | 「`<` でない ⇒ `≥`」 |
| `congrArg Prod.fst/snd`, `Prod.ext` | ペア操作 |
| `sq_nonneg` | x² ≥ 0 |
| `linear_combination` | 多項式恒等式 + 仮定 |
| `field_simp` | 除算クリア |
| `linarith`, `nlinarith` | 不等式 (前者は線形、後者は限定的二次) |
| `ring` | 環演算 |
| `positivity` | 「明らかに正」の判定 |

失敗 / 試行錯誤したもの:

| 試したシンボル / 状況 | 結果 | 真の解 |
|---|---|---|
| `le_of_not_lt` | 存在しない | `not_lt.mp` |
| `div_add_div_same` | 存在しない名前 | `← add_div` |
| `field_simp at h1` (h1 : a/D = 2) | 内部展開して polynomial 化 | `(div_eq_iff hD_ne).mp h1` |
| `unfold midpointOf at hM1_eq` | let に対しては効かない | 補助 `midpointOf_fst/snd` |
| `nlinarith` で u² ≤ 1 を直接 | 連鎖が複雑で通らない | 鍵不等式を補助補題に切り出す |
| `rw [div_le_iff₀ hσm_sq_pos]` (順序ミス) | パターン不一致 | rewrite の順序を入れ替え `div_le_one` を先に |
| `field_simp; ring` (field_simp が自走完結) | "No goals to be solved" | `; ring` を削除 |

WebSearch / WebFetch / Mathlib 検索ツールの利用は **ゼロ**。
全て記憶頼み + Bash 経由のコンパイラ反応で軌道修正。

## 5. ファイル構造 (最終)

```
T_Q3_1.lean (287 行)
├── structure Config           -- P, Q, R と球面・重心条件
├── def Locus, IsMidpoint
├── 順方向: circle_eq_of_config + midpoint_ne_five_zero
├── m_ge_one_of_locus, m_lt_five_of_locus
├── mkσ, mkρ, mkP, mkQ, mkR
├── mkσ_sq, mkρ_sq, mkσ_pos, mkρ_pos
├── mkP_add_mkQ_fst/snd
├── mkP_sphere, mkQ_sphere, mkR_sphere, mkP_ne_mkQ
├── mkLocusConfig (+ @[simp] mkLocusConfig_P/Q)
├── exists_config_of_locus
└── theorem locus_iff

T_Q3_2.lean (436 行)
├── def OnSegment, SweptRange
├── 順方向 (Phase 3):
│   ├── dot_le_of_sphere, disk_of_segment
│   ├── midpointOf (+ midpointOf_fst/snd, midpoint_isMidpoint)
│   ├── midpoint_on_circle, dot_eq_of_segment
│   ├── hyperbola_of_segment
│   ├── ne_five_zero_of_segment
│   └── private lemma forward
├── 逆方向 (Phase 4):
│   ├── x_ne_five, D_pos
│   ├── exists_midpoint (sqrt + clear_value + linear_combination)
│   ├── key_sq_ineq
│   ├── onSegment_mkLocusConfig
│   └── private lemma backward
└── theorem swept_range_iff
```

## 6. 将来の Mathlib 検索ツールに対する観察

このセッションで露呈した、**ツールが解消しうる摩擦**:

### A. 補題名の guessing が高コスト

- `le_of_not_lt`, `div_add_div_same` のような **直訳的英語名でハズレ** が複数。
- 探索方法: コンパイラエラー → 思考 → 別名で再試行、というループ。
  記憶ベースなので Mathlib のリネームに追随できない。
- **ツールが提供すべき**: 「型シグネチャから補題を引く」自然言語インターフェース。
  `(¬ a < b) → b ≤ a` を投げると `not_lt.mp` が返る、など。

### B. 「形が似ている補題」の発見

- `div_add_div`, `div_add_div_same`, `add_div` の違いは **作用方向と引数の順番** だけ。
- 一覧で類似補題を提示して選ばせるとよい。

### C. タクティクの弱点パターン

- `nlinarith` は積の連鎖が深いと通らないので **手作業で中間補題を切り出す** 必要がある。
- `field_simp` は `set` の let を展開してしまう (`clear_value` でブロック)。
- `rw` は順序敏感で、一度置換したパターンは戻せない。
- これらは **「タクティク失敗のレシピ集」として索引化できると価値が高い**。

### D. 数学的補題の発見

- 今回の問題で核となる「Thales 円と小円の交差条件 ⇔ 双曲線」のような **発想** は、
  本セッションでは Claude が思考フェーズで自前で導出した。
- Mathlib にはより一般的な道具 (`InnerProductGeometry` 等) があるはずだが、
  検索コストが高くて使わなかった。
- **ツールで「この問題形なら Mathlib 内のあの構造体と相性が良い」と提案できれば** 形式化全体が短くなる可能性。

### E. ビルド時の cache 同期

- `lake build Common2026.T_Q3_1` を明示しないと T_Q3_2 が古い olean を読む。
- LSP の "Unknown identifier" エラーがキャッシュ起因なのか実在エラーなのか
  目視で見分けるのが面倒。
- **ツールで「これはキャッシュ起因」と判定**してくれると無駄な思考が減る。

## 7. 反省点と次回への提案

1. **探索の前に Mathlib 検索を試す**: 今回 0 回だった WebSearch / 自前 grep を
   1 ステップ最初に挟むだけで、`div_add_div_same` 系の試行錯誤は減らせる。
2. **`set` の使用を減らし `clear_value` をデフォルト**にする: `field_simp` との
   相性が悪すぎる。あるいは set の代わりに `let` を pattern で受ける構文を使う。
3. **二乗・除算が混じる不等式は補助補題に切り出す**: 今回 `key_sq_ineq` を
   切り出したことで証明全体が読める長さになった。
4. **大きな代数恒等式は ring に頼らず手で確認**: 線形結合の符号ミスは
   ring エラーで検出されるが、デバッグサイクルが長い。
5. **`lake build` を Edit のたびに走らせる**: LSP キャッシュは信用しない。

## 8. 残し物

- 「図示せよ」だが図描画はせず代数特徴付けのみ
- (5, 0) は `≠` で表現、集合差は使っていない
- `nlinarith` ヒント `sq_nonneg ((6 - A.1) * b + A.2 * a)` は手で導出した
  Cauchy–Schwarz 形。一般化された Mathlib 補題に置き換える余地あり
  (`inner_mul_le_norm_mul_norm` 等)
