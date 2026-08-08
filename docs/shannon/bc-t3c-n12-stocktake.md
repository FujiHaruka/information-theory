# N12 — 判定枠 6 leg (N6 … N11) の棚卸し

> **Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 の N12 起票ブロック (逐語の SoT)。
> 台帳 = [`bc-facts.md`](bc-facts.md) `## N6 (T3c)` … `## N11 (T3c)` / attack 台帳 = [`bc-open-problem-attacks.md`](bc-open-problem-attacks.md)。

**leg 冒頭宣言 (N12)**: 側 = 記録 / 動かすもの = 判定枠 6 leg (N6 … N11) が §0 のゴールに対して
何を確定させ何を確定させていないかを、SoT への裏取りと Lean 側の機械再導出つきで 2 欄に分けて確定させ、
A2 / N16 の投入先を型つきで選べる状態にする

⚠⚠ **本 leg は判定 leg ではない** — 新しい GO / NO-GO は 1 本も出していない (起票の反証条件 (3))。
⚠⚠ **「達成」の欄は作らない** (自己採点になる)。⚠ **本書は「確定 / 未確定」の 2 欄のみを持つ**。

---

## 0. 総括

**確定した側 (5 行以内)**

1. **`C` の境界は面単位で棚卸しされ、[probc] という 1 インスタンスの上で `Thm7 ⊆ C` の側が 6 方向 + 2 つの錐 + `R0=0` スライスについて閉じた** — 最後に残った幅 `ε` は N10 が**厳密に 0** にし、その射程は半空間 `e ≤ h(p)` の全体である。
2. **層 3 (Lean) に載ったのは `@[entry_point]` 定理 5 本ちょうど** (N8 の 3 本 + N11 の 2 本) で、**5 本とも `#print axioms` が sorryAx-free / 署名に load-bearing hypothesis 0 本 / `InformationTheory/Shannon/BroadcastChannel/` 配下の `sorry` と `@residual` は 0 件**である。
3. ⚠⚠ **その 5 本はレート領域の包含について 1 文字も言っていない** — 載ったのは制約の**右辺どうしの不等式** (N8) と `ℝ` 上の **1 変数不等式** (N11) であり、**N10 §2.1–§2.4 の恒等式群は 1 本も載っていない**。
4. **検証器 11 本は HEAD で全数再現する** (合計 **263/263**、EXIT=0)。⚠ **所要時間は台帳の記録より一律に長い** (下記 §1 注)。
5. **6 leg とも敵対的独立監査を通り、判定は 6 本とも生存した** (訂正 計 33 件、⚠ **主判定を動かした訂正は N6 の 1 件のみ**で、それは GO / NO-GO ではなく「未着手の面の数え方」である)。

**未確定の側 (5 行以内)**

1. ⚠⚠ **`Thm7 ⊋ C` の材料は依然 1 つも無く、排除もされていない**。6 leg のどれも、原理的にこの材料を産む設計になっていなかった (N9 起票の片側性 (i)–(iii))。
2. ⚠⚠ **決着は [probc] の族 (半空間 `e ≤ h(p)`) の上に留まり、一般 BC へは持ち上がらない** — 連鎖は BEC 固有の恒等式と二値の `δ` に全面的に依存する。
3. **`e > h(p)` 側に的があるか** (N10 §4.1 の gate 出力) は **N11 でも取っていない** — 反証条件 3 本つきで後続へ引き継がれたままである (⚠ **その 3 本の SoT は [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2。本書は参照のみで複製も書き換えもしない**)。
4. **(γ) = `(R2)` / `(R3)` は層 3 に無い** ⟹ **`h_Thm7(0,1,t)` の上界そのものは Lean に無い**。⟹ **「`ε = 0` が機械検証された」とは言えない**。
5. **N11 の「唯一の解析的入力」という枠付けには限定がある** — N10 §2.4 が併用する `σ_x := d*_t − ψ_t(x) ≥ 0` は `d*_t` が最大値として**達成される**ことに依り厳密には代数ではない (⚠ **N10 からの継承であり、監査も再導出していない**)。

⚠⚠ **「尽きた」ではない** — 残るのは **一般 BC / 他インスタンス / (γ) / `e > h(p)` 側**である (§4)。

---

## 1. 確定した項目

⚠ **裏が取れなかったものは本節に置かず §2 へ落とした** (起票の反証条件 (1))。
⚠ **本節の「裏取り」は台帳の主張と機械出力の対応の確認であって、散文の導出の再導出ではない** (→ §6-2)。

| # | 項目 | 由来 leg | SoT | 裏取りの方法 (実際に打ったコマンド) | 裏取りの結果 |
|---|---|---|---|---|---|
| 1 | 検証器 11 本は HEAD で全数再現する | N6 … N11 (+ A1 2 本) | facts `## N6 (T3c)` … `## N11 (T3c)` の各節ヘッダと plan §5.1 の各着地ブロックが記録する pass 本数 | `python3 docs/shannon/verifiers/{capacity_probc,n6_audit_probc,shoulder_certificate_probc,n7_audit_probc,kappa2_probc,kappa2_audit_probc,n9_cone_probc,n9_audit_probc,n10_epsilon_zero_probc,n10_audit_probc,n11_audit_morecapable}.py` | **11 本とも EXIT=0**。`18/18` / `20/20` / `18/18` / `20/20` / `11/11` / `12/12` / `19/19` / `46/46` / `22/22` / `34/34` / `43/43` = **合計 263/263**、**台帳の記録本数と全件一致** ⟹ 反証条件 (1) はこの軸では不発火。⚠ **`kappa2_probc` / `kappa2_audit_probc` の 2 本は A1 (N4) 由来で判定枠ではない** (ブリーフの 11 本の内数) |
| 2 | 判定枠 6 leg が層 3 へ載せたのは `@[entry_point]` 定理 **5 本ちょうど** (N8 = 3 / N11 = 2) | N8 / N11 | facts N8-a / N11-a、plan §5.1 の N8・N11 着地ブロック | `git show 51d1ccb1 -- InformationTheory/ \| rg -c '^\+@\[entry_point\]'` / 同 `4da3a9ad` / 窓内の全 commit (`git log --oneline 20b456b9..HEAD -- InformationTheory/`) について同じカウント | N8 = **3**、N11 = **2**。窓内で `InformationTheory/` に触れた commit は 5 本 (`51d1ccb1` / `72aaef9a` / `d9fa6558` / `4da3a9ad` / `db25d3dd`) で、**`@[entry_point]` を足したのは前 2 本だけ** (残り 3 本は `+0`) ⟹ **5 本ちょうど**。⚠ **同ディレクトリ全体の `@[entry_point]` は 24 ファイル 84 本**であり、**残る 79 本は前 relay 以前の分**である (⟹ ディレクトリ一括カウントは本項の反証にならない) |
| 3 | その 5 本は現行 HEAD にも生きている (改名・削除なし) | N8 / N11 | 同上 | `rg -n "theorem <name>" InformationTheory/ --glob '*.lean'` を 5 本の宣言名それぞれに | 5 本とも実在。`OuterBoundTransport.lean:975` / `:1011` / `:1033`、`MoreCapableBinary.lean:381` / `:396` |
| 4 | 5 本とも `#print axioms` が sorryAx-free | N8 / N11 | facts N8-a / N11-a、plan §5.1 | `lake build InformationTheory.Shannon.BroadcastChannel.{OuterBoundTransport,MoreCapableBinary}` (**stale olean 回避**) → 一時ファイルに `import` + `#print axioms` を書いて `lake env lean` | **5 本とも `[propext, Classical.choice, Quot.sound]`**、EXIT=0。逐語は §3.2 |
| 5 | 5 本の署名に load-bearing hypothesis は 0 本 | N8 / N11 | facts N8-d / N11-d | 同一ファイルの `#check @<name>` + `OuterBoundTransport.lean:945–1044` を Read して証明本体を確認 | 仮説は **measurability / `0 ≤ t` / `0 < p` / `p < 1/2` / `0 ≤ x` / `x ≤ 1` / `e * log 2 ≤ binEntropy p` / `IsMarkovChain μ (w,u) x z`** のみ。**すべて regularity precondition か定義域の制限**であり、結論の核を担うものは無い (§3.3 に 1 行ずつ) |
| 6 | `InformationTheory/Shannon/BroadcastChannel/` 配下の `sorry` / `@residual` は 0 件 | N8 / N11 | CLAUDE.md の Definition of Done | `rg -n 'sorry' … \| wc -l` / `rg -n '@residual' … \| wc -l` | **0 / 0** |
| 7 | ⚠⚠ 載った 5 本は**レート領域の包含について 1 文字も言っていない** | N8 / N11 | facts N8-b / N11-g (逐語の SoT = [`bc-t3c-n11-more-capable-lean.md`](bc-t3c-n11-more-capable-lean.md) §4) | `#check` の結論形の逐語確認 + `rg -n 'Thm7\|capacityRegion\|rateRegion\|RateRegion' MoreCapableBinary.lean` + `rg -n '^import' MoreCapableBinary.lean` | N8 の 3 本の結論は `plainDirectionalCombination … ≤ plainDirectionalBound …` = **`ℝ` 上の不等式** (制約の右辺どうし)。N11 の 2 本は **`Real.binEntropy` だけからなる `ℝ` 上の 1 変数不等式**で、**領域記号はヒット 0 件**、しかも `MoreCapableBinary.lean` は **BC の領域ファイルを 1 本も import していない** (import は Mathlib 4 本 + `InformationTheory.Meta.EntryPoint` のみ) ⟹ 領域について何も言えない構成である |
| 8 | `C ⊆ Thm7` は未証明の前提ではなく [auxrec] Theorem 7 そのものである | N6 (監査) | facts N6-p | `python3 docs/shannon/verifiers/n6_audit_probc.py` (`G2`) | `[PASS] G2 … auxrec.txt:1034-1036 -- 'Given a broadcast channel … and any achievable rate triple (R0,R1,R2), one can find some input distribution p(x) such that for any auxiliary channel T_J\|X,Y,Z, the following constraints are satisfied'` ⟹ NO-GO 枝は空でない |
| 9 | 支持方向 6 本のうち **5 枚は `(19)/(20a)/(20b)` を 1 本も消費せず無料で閉じる**。⚠ **F-SUM 値の 1 枚は無料ではなく `η = 1e-13` の条件つき**である | N6 (+ 監査) | facts N6-d | `python3 docs/shannon/verifiers/capacity_probc.py` (T7 / T9 / T15) + `n6_audit_probc.py` (`D1`–`D4`) | `[ok ] T7 … max \|branch - closed form\| = 3.775e-15 over 200 witnesses` / `[ok ] T9 (18b)/(18e) closed forms: max residual = 1.110e-15` / `[ok ] T15 … W=X gives M = 1.0620088128` (= `2C`) / `[PASS] D1 (I1) chain: (18a) <= I(W;Y) <= I(X;Y) <= 2C`。⚠ **T15 は screen** |
| 10 | 箱の射影恒等式は生存する。⚠⚠ **そこから「`R0>0` はスライスに従属する」は導かれない** (有理数の明示反例 2 本) | N6 (監査で一部覆った) | facts N6-g / N6-n | `python3 docs/shannon/verifiers/n6_audit_probc.py` (`C2` / `C3`) | `[PASS] C2 COUNTEREXAMPLE: equal R0=0 slices, different mixed-direction support` / `[PASS] C3 COUNTEREXAMPLE: 'Thm7 subset D' is conditional, not unconditional`。⚠ **最適化器を一切使っていない**ので未収束の artefact ではありえない |
| 11 | 錐 `λ0 ≥ λ1+λ2` は「従属」ではなく**無料で閉じている** | N6 (監査の副産物) | facts N6-o | 同上 (`C4` / `C5`) | `[PASS] C4 instance level: the sub-cone lam0 >= lam1+lam2 is FREE, not 'subordinate'`。⚠ **`0 < λ0 < λ1+λ2` の錐は当時未着手で、N9 が別途閉じた** (#13) |
| 12 | `R0 = 0` スライスは **NO-GO** — `Thm7\|_{R0=0} ⊆ C\|_{R0=0} + [0,ε]²` (⚠ 当時 `ε = 2.0786e-07`) | N7 | facts N7-a、[`bc-t3c-n7-shoulder-certificate.md`](bc-t3c-n7-shoulder-certificate.md) §0 / §2.1–§2.3 | `python3 docs/shannon/verifiers/shoulder_certificate_probc.py` + `n7_audit_probc.py` | `18/18` + `20/20 passed in 121.4s`。`[ok ] N1 instance constants vs the ledger: max \|ours - bc-facts ## N1 (T3c)\| = 7.733e-11` / `[ok ] N2 H(Y\|X) = H(Z\|X) = h(e)+h(p)` 残差なし。⚠⚠ **`ε` は N10 が厳密 0 に置き換えた** (#14) ⟹ N7 の値は上界として妥当だが緩い |
| 13 | 錐 `0 < λ0 < λ1+λ2` (=「`D = C` か」) は**恒等式により閉じた** | N9 | facts N9-a、[`bc-t3c-n9-cone-gate.md`](bc-t3c-n9-cone-gate.md) §3.1 | `python3 docs/shannon/verifiers/n9_cone_probc.py` + `n9_audit_probc.py` | `19/19` + `46/46`。`[ok ] C10 D_b is contained in the union of the beta-split boxes: max violation … = 1.110e-15` / `[ok ] C11 every beta-split box is contained in D_b … => D_b = union_beta Box(beta)` / `[ok ] C12 the cone support function is a reparametrised slice value: max … = 1.332e-15 over 200 cone directions`。⚠ **`C19` は screen であり leg も証拠に使っていない** |
| 14 | **`ε` は厳密に 0** — [probc] 上で `Ω(t) = d*_t` が全 `t ∈ [0,1]` で成立 | N10 | facts N10-a、[`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §3.1 | `python3 docs/shannon/verifiers/n10_epsilon_zero_probc.py` + `n10_audit_probc.py` | `22/22 tests passed in 196.1 s` + `34/34 tests passed in 50.6 s`。`[PASS] D3 identity T_t = … max residual 4.441e-15` (120000 fibres × 7 t) / `[PASS] D5 main bound T_t >= C(1-t) h(a) + t S_A >= 0: min … = 4.030e-11 >= 0` / `[PASS] D7 the bound is tight`。⚠⚠ **再導出されたのは支持関数の一致まで**で、**領域の等式は N9 §4.1 の連鎖の引用**である |
| 15 | 決着の射程は**半空間 `{(p,e) : 0<p<1/2, e ≤ h(p)}` の全体**であり、効いている条件は `δ ≥ 0` の 1 本だけである | N10 (監査 訂正 4 = 上方修正) | facts N10-e | `n10_epsilon_zero_probc.py` (`G2`) + `n10_audit_probc.py` (`B33`) | `[PASS] G2 negative control: e = h(p) is load-bearing (both directions): e=h(p)-0.05: min delta = +0.00000 … e=h(p)+0.02: min delta = -0.02000, min_t [d*_t - Omega] = -0.01993` / `[PASS] B33 more capable … survives e < h(p), fails e > h(p)` ⟹ **`e ≤ h(p)` 側で生き、`e > h(p)` 側で標的そのものが偽になる**。⚠⚠ **偽になることは分離ではない** (超えるのは上界と下界であって領域ではない) |
| 16 | N11 が載せた 2 本は **N10 の連鎖が消費する各点版**であり、互いに導出可能である | N11 (+ 監査) | facts N11-a / N11-b / N11-c、[`bc-t3c-n11-more-capable-lean.md`](bc-t3c-n11-more-capable-lean.md) §1.1–§1.5 | `python3 docs/shannon/verifiers/n11_audit_morecapable.py` | `43/43`。`PASS H2 hypothesis he forces e <= h2(p) < 1 (so 1-e > 0 is automatic)`。⚠ **2 本が互いに導出可能であることを機械証明したのは監査側の Lean probe** (`probes/t3c-n11/more-capable-binary-audit.lean`) **であり、その導出は層 3 には無い** |
| 17 | `ε` の伝播係数 (親 plan が「未計算」と名指しした量) は、集合の水準で**レート座標あたり係数 1・`R0` 座標 0**、支持関数の水準で **`λ1+λ2`** である | N9 | facts N9-f、[`bc-t3c-n9-cone-gate.md`](bc-t3c-n9-cone-gate.md) §2.5 | `n9_cone_probc.py` / `n9_audit_probc.py` (上記) | 両者とも pass。⚠⚠ **支持関数側の係数は錐の内側の言明であって大域ではない** (錐の外を支えているのは `R0 ≤ 2C` の条項) |

⚠ **裏取りで見つかった食い違い 1 件 (隠さずここに書く)** — **pass 本数は 11 本とも台帳と一致したが、所要時間は一律に台帳の記録より長い**:
`capacity_probc.py` は台帳「約 13 秒」に対し実測 **20.2 秒**、`n6_audit_probc.py` は「約 7 秒」に対し **12.2 秒**、
`shoulder_certificate_probc.py` は「約 29 秒」に対し **41.0 秒**。⚠ **判定に使う量ではない**ため §1 の行を落とすには当たらないが、
⚠ **原因 (マシン差か実装変更か) は本 leg では調べていない** (→ §6-10)。

---

## 2. 未確定の項目

| # | 項目 | なぜ未確定か | どの leg がどこまで触れたか | 何があれば確定するか |
|---|---|---|---|---|
| 1 | **`Thm7 ⊋ C` は成り立つか** | 6 leg のどれも、この材料を産む設計になっていなかった (N9 起票の片側性 (i)–(iii) は「本 leg では原理的に出ない」と事前に書いている) | N1 が和レート面で NO-GO / N6 が面を棚卸し / N7 が肩を閉じ / N9 が錐を閉じ / N10 が `ε` を 0 に — **いずれも「一致」の側**である。⚠ **排除もされていない** | `(18b),(18c),(18d)` を同時に天井より上げたまま**全 `T_J` で適格性を保つ** witness の明示構成 (§1 の入口 1 点)。⚠ **1 度も試されていない** |
| 2 | **一般 BC への持ち上げ** | 連鎖は BEC 固有の恒等式と二値の `δ` に全面的に依存する。さらに N6-j が「**NO-GO は比較であり比較の相手が要る / 一般 BC では `C` が未知**」と却下の load-bearing な前提を特定している | N6-j が (γ) を ill-posed と判定 / N10-e が「決着は [probc] の族に留まる」と明記 / N11 は `ℝ` 上の 1 変数不等式のみ | 障害そのものを**対象として名指し**し、回避条件を書くこと (→ §4-1)。⚠ **現状は散文の限定であって対象化されていない** |
| 3 | **`e > h(p)` 側に的があるか** | N10 §4.1 の gate 出力を **N11 が取らなかった** (判断ログ 8 により `δ ≥ 0` の層 3 化を優先) | N10 が gate 出力として 1 本渡し、反証条件 3 本を N10 §4.2 に**事前に**書いた。N11 は**手を出していない** | その反証条件 3 本に照らした [探索 + gate] 1 段。⚠⚠ **反証条件 3 本の SoT は [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2 であり、本書は参照のみ — 複製も書き換えもしない** |
| 4 | **(γ) `(R2)` / `(R3)` を層 3 へ載せる** | N8 が載せたのは N7 §2.1 の `(R1)` 1 本だけである | N7 が 3 本の還元を散文で立て、N8 が `(R1)` だけを層 3 へ。N8-b が「`h_Thm7(0,1,t)` の上界そのものは Lean に無い」と明記 | `(R2)` (`U' := (U,W)` の事後分解) と `(R3)` (2 つの緩和) の層 3 化。⚠ **領域 def / 計算可能性層に手を出したら判断ログ 5 のテスト可能な線により子 plan へ回す** |
| 5 | **「`ε = 0` が機械検証された」と言えるか** | **N10 §2.1–§2.4 の恒等式群は Lean に 1 本も載っていない** — 載ったのは N10 §2.5 の解析的入力 `δ ≥ 0` の各点版だけである | N10 が散文 + 検証器で閉じ、N11 が入力 1 本を層 3 へ | §2.1–§2.4 の恒等式群の層 3 化。⚠ **本項は N11-g の逐語であり、本 leg が新たに出した判定ではない** |
| 6 | **N11 の「唯一の解析的入力」という枠付け** | N10 §2.4 が併用する `σ_x := d*_t − ψ_t(x) ≥ 0` は `d*_t` が**最大値として達成される**ことに依り、厳密には代数ではない | N11 監査 訂正 6 が指摘。⚠⚠ **N10 からの継承であって N11 が作った誤りではない** / ⚠ **監査もこの点は再導出していない** | `σ_x ≥ 0` の独立な再導出 (達成性の議論を含む)。⚠ **本 leg も再導出していない** (→ §6-6) |
| 7 | **N7 の証明書の独立再現** | N7 監査は禁止事項として被監査検証器を 1 行も実行しておらず、`18/18` も「321 点中 321 点が閉じた」も**独立には未確認**である (独立に閉じたのは計 11 点) | N7-r (1) が名指し。⚠ **本 leg の実行 (#12) は原典の実行であって独立実装ではない** | 独立エンジンによる 321 点の再走 | 
| 8 | **N7 の報告セル数** | N7 は `t = 1` / `tol = 1e-9` で `2626` セルと書くが、監査の独立再実装は `75,523` である | N7-r (2)。⚠ **監査は「誤り」とは呼ばず判定を保留** (分岐規則 / incumbent / 「セル」の数え方の違いで説明がつく) | 数え方の定義を固定したうえでの再走 |
| 9 | **`C` の肩が `β` 族で尽きるか (一般の基数で)** | N6-f の族が `C` の境界そのものかは当時 screen のみで、N7 の挟み込みは**方向 `(0,1,t)` に限る** | N6-f (screen) → N7-i / N7 §5 収穫 2 で**この方向に限り** `ε` 以内に確定 | 他方向 / 一般基数での証明書。⚠ **N6-q (5) より掃いた基数は `≤ 4` まで** |
| 10 | **T18 の残り 5 方向** | 恒等式へ格上げされたのは `(1,1,1)` と `(2,1,1)` の 2 本だけである | N6-o が 2 本を格上げ、残り 5 本 (`(1.1,1,1)` / `(1.2,1,1)` / `(1.5,1,1)` / `(1,1,0.5)` / `(1.3,1,0.7)`) は screen 止まり | 各方向の恒等式または反例 |
| 11 | **`Thm7 = ⋃_p ⋂_J ⋃_w (箱)` の外側の `⋃_p`** | N6 の射影の議論は外側の `⋃_p` を落とした表示の上にあり (射影の議論自体は壊れない)、**`∃p ∀T_J ∃aux` は T3 家系の争点そのもの**である | N6-g の精度の訂正が名指し。⚠ **6 leg のどれもこの量化子には触れていない** | 量化子の段の形式化 (= N2 が員数を測り §6-5 で子 plan へ切り出した対象) |
| 12 | **否定側 (§3 の T3-β) の員数** | ⚠⚠ **誰も測っていない** (N2-l) | 判定枠 6 leg はすべて T3-α 側である | T3-β 側の gateway atom 1 本 |

---

## 3. 層 3 (Lean) の現況 — 機械再導出の結果をそのまま

### 3.1 commit 帰属で数えた `@[entry_point]` (⚠ ディレクトリ一括カウントではない)

```
git show 51d1ccb1 -- InformationTheory/ | rg -c '^\+@\[entry_point\]'   → 3   (N8)
git show 4da3a9ad -- InformationTheory/ | rg -c '^\+@\[entry_point\]'   → 2   (N11)
git log --oneline 20b456b9..HEAD -- InformationTheory/                  → 5 commits
  51d1ccb1 (+3) / 72aaef9a (+0) / d9fa6558 (+0) / 4da3a9ad (+2) / db25d3dd (+0)
```

- **N8 `51d1ccb1`**: `OuterBoundTransport.lean` に **+107 行 / 1 ファイル**。宣言 6 本 = `noncomputable def` 3 (`plainDirectionalCombination` / `plainDirectionalBound` / `plainDirectionalBoundCondFree`) + `@[entry_point]` 定理 3 (`plainDirectionalCombination_le_plainDirectionalBound` / `plainDirectionalBound_eq_condFree` / `plainDirectionalCombination_le_plainDirectionalBoundCondFree`)。
- **N11 `4da3a9ad`**: `MoreCapableBinary.lean` 新規 **+406 行 / 1 ファイル**。`@[entry_point]` 定理 2 (`log_two_mul_binEntropy_binConv_sub_binEntropy_le` / `binEntropy_binConv_sub_binEntropy_le`)。
- **5 本とも HEAD に実在** (`OuterBoundTransport.lean:975` / `:1011` / `:1033`、`MoreCapableBinary.lean:381` / `:396`) — 監査 leg での改名・削除は無い。
- ⚠ **参考値 (反証の対象にしてはならない)**: `InformationTheory/Shannon/BroadcastChannel/` 全体の `@[entry_point]` は **24 ファイル 84 本**、うち `OuterBoundTransport.lean` が 21 本 / `MoreCapableBinary.lean` が 2 本。**79 本は前 relay 以前の分**である。

### 3.2 `#print axioms` の逐語 (⚠ `lake build` 後に実行 = stale olean を回避)

```
lake build InformationTheory.Shannon.BroadcastChannel.OuterBoundTransport
lake build InformationTheory.Shannon.BroadcastChannel.MoreCapableBinary     → exit 0
lake env lean <probe>                                                       → EXIT=0
```

```
'InformationTheory.Shannon.BroadcastChannel.plainDirectionalCombination_le_plainDirectionalBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.plainDirectionalBound_eq_condFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.plainDirectionalCombination_le_plainDirectionalBoundCondFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.log_two_mul_binEntropy_binConv_sub_binEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.binEntropy_binConv_sub_binEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

⟹ **5 本とも sorryAx-free**。⚠⚠ **これは必要条件であって十分条件ではない** ⟹ §3.3 の署名走査を併せる。

### 3.3 署名走査 — 各定理の仮説は precondition か load-bearing か (1 行ずつ)

| 定理 | 仮説 | 判定 |
|---|---|---|
| `plainDirectionalCombination_le_plainDirectionalBound` | `Measurable y` / `Measurable w` / `Measurable u` / `0 ≤ t` | **すべて precondition**。measurability は regularity、`0 ≤ t` は方向の定義域 (`t < 0` では重み `t` の符号が反転する)。証明本体は連鎖律 + `min_le_right` + `linarith` の 3 行で、核を仮説から受け取っていない |
| `plainDirectionalBound_eq_condFree` | `Measurable x/z/w/u` / `IsMarkovChain μ (w,u) x z` | **すべて precondition**。マルコフ性は **witness の構造条件**であって結論の言い換えではない (結論は 2 つの `def` の等式であり、仮説にはその等式もその特殊形も現れない)。⚠ **N8-d は監査が `hmarkov` 落としの明示反例で必要性を確認したと記録する** |
| `plainDirectionalCombination_le_plainDirectionalBoundCondFree` | 上 2 本の和集合 | **すべて precondition**。証明本体は上 2 本の合成 (`rw` + `exact`) |
| `log_two_mul_binEntropy_binConv_sub_binEntropy_le` | `0 < p` / `p < 1/2` / `0 ≤ x` / `x ≤ 1` | **すべて定義域の制限**。⚠ **N11-c より `p` の 2 本は落とせる**が、情報理論的な中身が増えないため起票の逐語形で据え置かれている (⟹ **`p < 1/2` が必要であるかのように読まない**) |
| `binEntropy_binConv_sub_binEntropy_le` | 上 4 本 + `e * Real.log 2 ≤ Real.binEntropy p` | **すべて定義域の制限**。追加の 1 本は半空間 `e ≤ h(p)` そのもの (= §1-15 の射程) であって、結論の核ではない |

⟹ **load-bearing hypothesis は 0 本**。

### 3.4 `sorry` / `@residual` の数え上げ

```
rg -n 'sorry'     InformationTheory/Shannon/BroadcastChannel/ --glob '*.lean' | wc -l  →  0
rg -n '@residual' InformationTheory/Shannon/BroadcastChannel/ --glob '*.lean' | wc -l  →  0
```

### 3.5 ⚠⚠ 落としてはならない限定 (機械で裏づけた)

- **レート領域の包含については Lean は 1 文字も言っていない**。N8 の 3 本は結論が `ℝ` 上の不等式 (制約の右辺どうし) であり、N11 の 2 本は `Real.binEntropy` だけからなる `ℝ` 上の 1 変数不等式である。**`MoreCapableBinary.lean` は BC の領域ファイルを 1 本も import していない** (`Mathlib.Analysis.Convex.Deriv` / `Mathlib.Analysis.Convex.Jensen` / `Mathlib.Analysis.Real.Sqrt` / `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` / `InformationTheory.Meta.EntryPoint` の 5 本のみ) ⟹ **構成上、領域について何も言えない**。
- **N10 §2.1–§2.4 の恒等式群は Lean に 1 本も載っていない** ⟹ **「`ε = 0` が機械検証された」とは言えない**。
- **`h_Thm7(0,1,t)` の上界そのものは Lean に無い** (`(R2)` / `(R3)` = (γ) が未着手)。

---

## 4. 残件の候補表 (型つき)

⚠ **本節は候補の型付けであって判定 (GO / NO-GO) ではない** (起票の反証条件 (3))。
⚠ **`型なし` のものは「A2 の投入先候補」として推さない** (起票の反証条件 (2))。
型の語彙 = §5.3 のアーク型 (`定義` / `言い換え` / `障害の構造`) または判定枠の 3 段 (`[探索+gate]` / `[構築+probe]` / `[層3へ載せる]`)。
死因の語彙 = [`bc-open-problem-attacks.md`](bc-open-problem-attacks.md) の冒頭「死因の語彙」ブロックの 5 語 (`numeric-counterexample` / `known-result` / `probe-failed` / `too-hard` / `mathlib-wall`) + アーク 4 語 (`non-reproducing` / `inert` / `redundant` / `restatement`)。

| # | 候補 | 型 | 接続先 (facts の節) | 死因 |
|---|---|---|---|---|
| 1 | **一般 BC への持ち上げ** | ⚠⚠ **`型なし`** | 3 本は書ける (`## N6 (T3c)` N6-j / `## N10 (T3c)` N10-e / `## L2 (T3)`) が、**型が付かない** | — (型が無いので死因も定義されない) |
| 2 | **他インスタンス** ([probc] 以外の具体インスタンスで同じ 3 段を回す) | **`[探索+gate]`** | `## N6 (T3c)` (面ごとの棚卸しの方法) / `## M14 (T3b)` (文献自身の対での明示 witness) / `## M5 (T3b)` ([probc] 積クラスの領域レベルは未決) / `## L10` (Nair–Wang–Geng の軸 C) | `probe-failed` (`C` の閉形が書けるインスタンスが無い) / `known-result` (選んだインスタンスが [probc] の鏡像で新情報ゼロ) |
| 3 | **(γ) `(R2)` / `(R3)` を層 3 へ載せる** | **`[層3へ載せる]`** | `## N7 (T3c)` N7-b (還元 3 本の逐語) / `## N8 (T3c)` N8-b (載っていない 2 本の名指し) / `## N2 (T3c)` (形式化債務の員数と強度 diff) | `mathlib-wall` (`sorry` + `@residual(plan:bc-open-problem-t3c-plan)` で honest に退出) / `too-hard`。⚠ **領域 def / 計算可能性層に手を出したら判断ログ 5 のテスト可能な線で停止して子 plan へ回す** |
| 4 | **`e > h(p)` 側** (N10 §4.1 の gate 出力) | **`[探索+gate]`** ⚠⚠ **アーク型ではない** | `## N10 (T3c)` N10-e (半空間の射程) / `## N7 (T3c)` N7-p (`t` を含まない 3 変数の不等式) / `## N6 (T3c)` N6-c (more capable の向きと Theorem 3 の適用条件) / `## N11 (T3c)` N11-b | `numeric-counterexample` / `probe-failed`。⚠⚠ **反証条件 3 本の SoT は [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2 であり、本書は参照のみ — 複製も書き換えもしない** |

### 4.1 候補 1 が `型なし` になった理由 (⚠ 起票の反証条件 (2) の発火)

**アーク型 3 つのどれにも当たらない**:

- **`定義` ではない** — 新しい対象の def が提案されていない。
- **`言い換え` ではない** — 新語彙も、元の問いとの同値も提案されていない。
- **`障害の構造` ではない** — §5.3 はこの型に「**障害が対象として名指しされ**、回避条件が書かれている」ことを要求するが、
  現状あるのは**散文の限定**だけである (N10-e「連鎖は BEC 固有の恒等式と二値の `δ` に全面的に依存する」/ N6-j「NO-GO は比較であり比較の相手が要る」)。
  **回避条件はどこにも書かれていない**。⚠ **これは §5.3 が「埋めるべき空席の典型」と呼んだ形そのものである** (M12 の witness 取り替え機構が「量化子の順序」としか呼ばれていないのと同型)。

**判定枠の 3 段のどれにも当たらない**:

- **`[探索+gate]` ではない** — gate には GO / NO-GO の 2 枝が要るが、N6-j が「**一般 BC では `C` が未知**」ゆえ比較の相手が無いことを特定している ⟹ **gate 可能な面が構成できない**。⚠ **これが候補 2 (他インスタンス) との差である** — 具体インスタンスなら閉形の相手が立つ。
- **`[構築+probe]` ではない** — probe に掛ける構築物が無い。
- **`[層3へ載せる]` ではない** — 層 1 で通った命題が無い。

⟹ **候補 1 は A2 の投入先候補として推さない**。⚠⚠ **これは「一般 BC が死んだ」ではない** — **型が付いていないだけ**であり、
上の `障害の構造` の 2 要件 (対象としての名指し + 回避条件) を満たせば型が付く。⚠ **その名指しをすること自体が 1 leg の仕事である**。

### 4.2 候補 4 の型についての限定 (⚠ 起票の見立て「緩める」への回答)

起票の**緩める**方向の見立ては「**`e > h(p)` 側は A2 の投入先候補として生きている**」であった。
**型照合の結果は「判定枠型であってアーク型ではない」** — すなわち:

- **候補表には載る** (反証条件 (2) は「アーク型にも判定枠の 3 段にも型が付かないもの」を外すと定めており、本候補は判定枠型を持つ)。
- ⚠⚠ **しかし A2 は探索アークであり、アーク宣言は型を `定義 | 言い換え | 障害の構造` の 3 語から選ぶことを要求する** (§5.3 のアーク宣言の雛形) ⟹ **本候補を A2 の型として宣言することはできない**。
- ⟹ **投入先として型が合うのは N16 (未配分) か、次の判定枠の組である**。⚠ **どちらに配るかは本 leg では決めない** (配分は起票の仕事)。

⚠ **この結論は起票の見立てが予告したとおりである** (「この候補は判定枠型であってアーク型ではない公算があり」)。

---

## 5. 較正 — 判定枠 6 leg の実測

⚠⚠ **本節は報告であって判定ではない** (§5.3 の閾値較正 (c) と同じ作法)。

### (a) 監査の訂正件数と、うち主判定を動かしたものの件数

| leg | 監査 | 破りに振った系統 | 成立 / 落ちた | 訂正件数 | うち**主判定を動かした**もの | うち**上方修正** (leg が自分を過小に書いていた側) |
|---|---|---|---|---|---|---|
| N6 | [`bc-t3c-n6-audit.md`](bc-t3c-n6-audit.md) | 25 系統 | — (内訳は標的別) | **6** | **1** (⚠ ただし GO / NO-GO ではない — N6 は判定 leg ではなく、覆ったのは「未着手の面は `R0=0` の肩 1 枚」という**数え方**である。`gate` の選択自体は生存) | 3 |
| N7 | [`bc-t3c-n7-audit.md`](bc-t3c-n7-audit.md) | 35 系統 | — | **4** | **0** (4 件とも `ε` を動かさない。うち 1 件 = N7-h の**因果帰属**は覆ったが値は不変) | 0 |
| N8 | [`bc-t3c-n8-audit.md`](bc-t3c-n8-audit.md) | 反証 5 本 | 2 成立 / 3 落ちた | **4** | **0** (4 件とも docstring の読ませ方 ⟹ **Lean の命題・署名・証明は 1 文字も変わっていない**) | 0 |
| N9 | [`bc-t3c-n9-audit.md`](bc-t3c-n9-audit.md) | 43 系統 | 7 成立 / 36 落ちた | **7** | **0** | 3 |
| N10 | [`bc-t3c-n10-audit.md`](bc-t3c-n10-audit.md) | 39 系統 | 10 成立 / 29 落ちた | **8** | **0** (主判定 `ε = 0` を動かすものは 0 件) | 5 |
| N11 | [`bc-t3c-n11-audit.md`](bc-t3c-n11-audit.md) | 49 系統 | 6 成立 / 43 潰せず | **7** | **0** | 3 |
| **計** | — | **191 系統 + 反証 5 本** | — | **33** | **1** | **14** |

**読み (⚠ 判定ではない)**: **訂正 33 件のうち主判定を動かしたのは 1 件 (3.0%)** であり、**上方修正が 14 件 (42%)** ある。
⟹ ⚠⚠ **「監査が主判定をほとんど動かさない」を「監査が効いていない」と読んではならない** — 上方修正 14 件のうち少なくとも
N9-c / N10-c / N10-e / N11-c は**射程を広げるか証拠の型を強くしており**、N10-e に至っては**決着の射程を曲線から半空間へ広げた** (判断ログ 7)。
⚠ **同時に、主判定が 1 件しか動いていない以上、監査は「判定の向きを変える装置」としてはまだ 1 度しか発火していない**。

### (b) 反証条件の発火状況

| leg | 事前に書かれた反証条件 | 発火状況 |
|---|---|---|
| N6 | ⚠ **plan の起票ブロックには無い** (`git show 7ff07b0f` で確認 — N6 の冒頭宣言は**着地時に**追記されている)。代わりに §4.4-1 の**着手前反証 1 本**を実施 | 着手前反証は **成功** (ただし (γ) は生き返らない、N6-j)。⚠ **N6 は次段 (N7) の反証条件 3 本を成果物 §3.3 に事前に書いた** |
| N7 | **3 本** (N6 §3.3 が事前に書いたもの) | **3 本とも不発火**。(1) は**機構は実在したが発火せず** (しかも原因の帰属が監査で覆り、真の原因はエンジン側の定数) / (2) は恒等式で消えた / (3) は**逆向きの収穫**になった |
| N8 | ⚠⚠ **無い** — 起票 (`git show c90baafb`) は**冒頭宣言 1 行のみ**で、反証条件も §4.4 の見立ても書かれていない | **発火状況の欄が存在しない** |
| N9 | **3 本** (plan の起票ブロックに事前記載) | **3 本とも不発火**。(3) は**経路が起票の想定と違った**まま通った (射影の線形性 + N6-g であって、想定した標準論法ではない) |
| N10 | **3 本** ([`bc-t3c-n9-cone-gate.md`](bc-t3c-n9-cone-gate.md) §4.2 が事前に書いたもの) | (1) 不発火 / (2) 不発火 / (3) は⚠ **本 leg では判定できない** (N9 側への反証条件であり、N10 は N9 §2.3 / §1.3 を再検証していない) |
| N11 | **3 本** (plan の起票ブロックに事前記載) | **3 本とも不発火** |
| **N12 (本 leg)** | **3 本** (plan の起票ブロックに事前記載) | **(1) 不発火** (§1 の 17 行はすべて機械で裏が取れた。⚠ **時間の食い違い 1 件は §1 注に記録し、pass 本数は全件一致**) / **(2) 発火** (候補 1 = 一般 BC が `型なし` ⟹ **A2 の投入先候補として推さない**、§4.1) / **(3) 不発火** (新しい GO / NO-GO は 1 本も出していない) |

⚠⚠ **本表が見せている運用上の穴 (報告であって判定ではない)**: **§4.4-2 の「反証条件を先に書く」義務が plan の起票ブロックに現れるのは N9 以降である**。
N6 / N7 は成果物側で代替され、**N8 は 3 本も見立ても書かれていない**。
⚠ **N8 に反証条件が無かったことが実害を生んだかは本 leg では判定しない** (⚠ ただし **N8 は 6 leg 中ただ 1 つ、冒頭宣言そのものが過大だった leg** である — 「上界の連鎖」を載せたと書いたが載ったのは `(R1)` 1 本だけで、この過大は監査ではなく着地時の自己申告で訂正された)。

### (c) 見立ての当たり外れ (⚠ 締める方向 / 緩める方向を分ける)

| leg | 締める方向 | 緩める方向 | 予想 |
|---|---|---|---|
| N6 | 4 本中 **1 本が覆った** (⚠ 監査の訂正後。N6 自身は 2/4 と書いたが、うち 1 本は**締める方向として正しかった**と N6-n が確定) | 3 本とも**生存** (うち 1 本は screen 止まりで判定していない ⟹ 較正の母集団に入れない) | — |
| N7 | 5 本中 **5 本とも覆った** | 3 本とも**生存** | — |
| N8 | — (見立ての記載なし) | — | — |
| N9 | 5 本中 **4 本が覆り、1 本が一部覆った** (見立て 5 = 機構は実在するが `C` の肩を達成する族の上では発火しない) | 1 本 (`D = C` は成り立つ) は **殺せなかった** (⚠ **殺せなかったことは「証明された」と同義ではない** — 立ったのは恒等式であって手構成の失敗ではない) | — |
| N10 | 3 本とも **覆らなかった** (見立て 1 = 当たり、⚠ **ただし併記した「3 変数不等式は必要条件どまり」の側は誤りで訂正 1 が覆した** / 見立て 2・3 = 当たり) | 2 本のうち **1 本生存 / 1 本破棄** (見立て 4 = 成立 / ⚠ **見立て 5「`β` を `t` に依らずに選ぶ構成が全域で可能」= 破棄**) | 1 本 = **外れた** (最も起きやすいと予想した反証条件 2 が発火しなかった。⚠ **外した理由も同定されている**) |
| N11 | 1 本 (Mathlib / in-repo に当該不等式は無い) = **覆らなかった** (loogle 2 本 Found 0 + `gerber` 0 件 + in-repo 0 件で着手前に反証済 ⟹ genuine gap) | 1 本 (N10 §2.5 の構造論法が Mathlib API で通る) = **生存** (gateway-atom-first で 2 階微分の符号補題を先に通した) | — |

**§4.4 の非対称性は判定枠でも再現したか (⚠ 報告。⚠ 母集団を先に固定する)**

- **締める方向 = 計 18 本** (N6 4 / N7 5 / N9 5 / N10 3 / N11 1)。**完全に覆った 10 本 (56%) / 一部覆った 1 本 / 覆らなかった 7 本**。
  ⚠⚠ **前 relay の「9 件中 9 件が覆る (100%)」は判定枠では再現していない**。内訳は **leg ごとに割れており** (N7 = 5/5、N9 = 4/5 + 一部 1、N6 = 1/4、N10 = 0/3、N11 = 0/1) ⟹
  ⚠ **母集団によって割れるという N6-l / N7 §4 の所見が、6 leg 規模でそのまま拡大再生産された**。
- **緩める方向 = 計 10 本**、うち**判定できたのは 9 本** (⚠ N6 の 1 本は screen 止まりで判定していないので母集団に入れない)。**生存 8 本 / 破棄 1 本** (N10 見立て 5)。
  ⚠⚠ **これを「緩める提案は当たりやすい」と読んではならない** — §4.4 が明示的に禁じている読みであり、
  かつ**本母集団は「殺す道具を着手前に決めた見立てだけ」で構成されている** (§4.4-2 の義務が効いた母集団) ⟹ **前 relay の「当たり 3 / 外れ 5」とは母集団が違う**。
- **予想 = 1 本** (N10 見立て 6) で **外れ**。
- ⟹ **報告としての結論は 2 行**: **(i) §4.4 が「非対称なのは締める方向が全件覆るという一方だけ」と書いた、その一方が判定枠では崩れた** (56%)。
  **(ii) 緩める側の外れは 1 本しか出ていない** (N10 見立て 5) ⟹ ⚠ **「緩める側の外れの方が高くつく」という §4.4 の非対称性の後半は、本母集団では検証できるだけの外れが出ていない**
  (⚠ **その 1 本は §2.7 で破棄され leg の判定には使われていないので、「見立ての上に leg を組んでから死ぬ」形にはなっていない**)。

---

## 6. ⚠ この棚卸しが確かめていないこと (⚠⚠ ここを薄くしない)

1. **検証器 11 本は「被検証器そのもの」を実行しただけである** — 独立実装での再導出はしていない。各 leg の監査が持つ独立検証器も、**その leg の監査が書いたもの**であって本 leg の独立実装ではない。
2. **散文の導出を 1 本も再導出していない** — 本 leg の裏取りは「台帳の主張」と「検証器の pass/fail」の対応の確認までである。恒等式の各段 (N9 §2.1–§2.5 / N10 §2.1–§2.6) は読んでいない。
3. **一次文献 ([probc] / [auxrec]) の逐語を再取得していない** — `$LIT` は §4.9 の資産消滅で失われており、§1-8 の `G2` が印字する逐語は**検証器に埋め込まれた文字列**である。原典との照合は本 leg ではしていない。
4. **Lean 側で証明本体を読んだのは N8 の 3 本だけである** — `MoreCapableBinary.lean` の 406 行 / 29 宣言は**読んでいない**。N11 の 2 本については `#print axioms` + 署名 + import 一覧までである (⚠ CLAUDE.md §4.2 の「署名でなく証明本体を読む」は N11 について未実施)。
5. **各監査の訂正件数を数え直していない** — §5 (a) の 33 件は**各監査 / 台帳の自己申告を合計したもの**である。「主判定を動かしたか」の分類も各監査の自己申告であり、本 leg が独立に判定したものではない。
6. **`σ_x := d*_t − ψ_t(x) ≥ 0` (N10 §2.4) を再導出していない** — §2-6 が名指しする限定は N11 監査の指摘をそのまま引き継いだものであり、**本 leg も監査も達成性の議論を再導出していない**。
7. **§4 の型付けは我々の判定であり、機械には掛かっていない** — とくに候補 1 が `型なし` であるという結論は §5.3 の要件との照合であって、反例や恒等式による判定ではない。
8. **`e > h(p)` 側の反証条件 3 本 (N10 §4.2) の中身を評価していない** — 参照しただけで、成立可能性も難度も測っていない。
9. **候補表の「接続先 3 本」は節名の実在確認までである** — その節の**内容**が候補に実際に使えるかは見ていない (§1-1 の `rg` はタグの実在を確かめただけで、意味的な適合は未検査)。
10. **検証器の所要時間が台帳の記録より一律に長い件の原因を調べていない** — マシン差か実装変更かを切り分けていない (§1 注)。
11. **BC ディレクトリの `@[entry_point]` 84 本のうち、判定枠 6 leg 由来でない 79 本が何を述べているかを見ていない** — 「レート領域の包含を述べたものは 1 本も無い」という §1-7 の確定は**判定枠が載せた 5 本についてのみ**であり、79 本については何も言っていない。
12. **N8 に反証条件と見立てが無かったことの影響を評価していない** — §5 (b) は事実として記録したが、実害の有無は判定していない (⚠ **判定は次の leg へ回す** = 起票の反証条件 (3))。
13. **A1 (N3–N5) を棚卸しの対象にしていない** — 本 leg の対象は判定枠 6 leg (N6 … N11) であり、A1 の終端判定と閾値較正 (§5.3) は N5 が既に行っている。`kappa2` 系検証器 2 本を実行したのは 11 本の内数としてであって、A1 の棚卸しではない。
14. **層 3 の 5 本が「N10 / N7 の散文の連鎖に実際に接続しているか」を本 leg では確かめていない** — N8-b / N11-b が接続を記録し、N11 監査の `F1` / `F2` が独立に確認したと台帳が書くが、**本 leg はその確認を再走していない**。

---

## 7. `GOAL-CHANGE` の起票

**無し**。§0 のゴールと完了条件は 1 文字も動いていない。本 leg は側 = `記録` であり、
(C2) の命題を 1 本も動かしていないため §6-4 の `(C2)` 起票行も増えない (判断ログ 9)。
