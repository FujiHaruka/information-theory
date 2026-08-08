# N15 — 「`C` の閉形が [probc] の外に書けるインスタンス族が在るか」の探索と N16 への gate (判定枠 第 3 組の第 1 段)

**Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 (N15 起票ブロック) /
**配分決定の SoT** = 同 plan §7 判断ログ 10-(3) (⚠ **候補 2 と候補 4 を 1 本の gate に束ねた根拠はそちら。本書は複製しない**) /
**入力の候補表** = [`bc-t3c-n12-stocktake.md`](bc-t3c-n12-stocktake.md) §4 (候補 2 = 他インスタンス / 候補 4 = `e > h(p)` 側)。

**leg 冒頭宣言 (N15)** (⚠ 親 plan §5.1 の N15 起票ブロックからの逐語コピー): 側 = (C2) / 動かすもの =
「`C` の閉形 (= 比較の相手) が [probc] の外に書けるインスタンス族が在るか」を §4.5 の 3 道具で gate し、
GO なら N16 の第 2 段 [構築 + probe] へ渡す族を 1 つに絞り、NO-GO なら候補 2 と候補 4 が同時に死ぬことを
確定させて候補 1 の `restatement` 公算の裏づけを得る

> ⏳ **起票のみ (実行前)**。⚠⚠ **本書の §0 と §1 は着手前に書かれたものであり、事後に 1 文字も書き換えない**
> (親 plan §4.4-2 の義務。⚠ **見立ての当たり外れ / 反証条件の発火状況は §4.1 / §4.2 が担う**)。
> ⚠ **§2 以降は実行時に埋める**。

---

## 0. 着手前の見立てと「締める / 緩める」の明記 (§4.4 の義務。⚠ 事後に書き換えない)

⚠ **本節は機械を 1 つも走らせる前・一次文献を 1 行も引く前に書いた**。以下は紙の上の見立てであり、
機械に掛けた結果は §3 に別途書く (一致しなかったものは一致しなかったと書く)。

### 見立て A (**緩める**) — `C` の閉形は [probc] の外にも書ける

[probc] 論文 **Theorem 2 の逆向き semi-deterministic 積クラス**が、Theorem 3 (逆向き more capable) とは
**別の仮説**で 3 レートの閉形を供給する ⟹ **`e > h(p)` の離調で壊れるのは Theorem 3 側だけ**であり、
比較の相手は別ルートで立つ。

**殺す道具 = §4.5 の道具 3 (閉形の族 / 反例の手構成)** (⚠ **§4.4-2 の義務どおり着手前に決めた**) —
Theorem 2 の閉形を実際に 3 レート `(R0,R1,R2)` で書き下し、`Thm7` と同じ平面に置けるかを見る。
**書き下せない / 平面が揃わないなら見立て A は死ぬ**。

### 見立て B (**締める**) — 族が立っても `Thm7` 側が評価できず gate は GO を出せない

理由 = 積クラスでは `∀T_{J|X}` の潰れ (facts [`bc-facts.md`](bc-facts.md) `## M5 (T3b)` の S8) が未決だから。

**着手前の 1 行反証 (§4.4-1 の義務)** = facts `## N1 (T3c)` は **`Thm7` 側の上界を「単一の `T_J` だけで、
適格性 (19)/(20a)/(20b) を 1 本も消費せずに」立てた実例**である ⟹ **`Thm7` の上界だけを取るなら S8 を通らない**
⟹ **見立て B は無条件には成り立たない**。

⚠ **ただし下界側 (`Thm7` に点が入ることを言う側) は S8 を通る** ⟹ **B は「GO の型が上界比較に限られる」という
弱い形でなら生き残る**。

### 見立て C (**締める**) — Theorem 2 のクラスは [probc] の鏡像であり `known-result` で死ぬ

**着手前の 1 行反証 (§4.4-1 の義務)** = **Theorem 2 の仮説は `X₁→Y₁` と `X₂→Z₂` が決定的であること**
(逐語の SoT = facts `## M5 (T3b)` 行 1) であるのに対し、**[probc] のインスタンスは BEC と BSC で
どちらも決定的ではない** ⟹ **2 つのクラスは交わらない** ⟹ **鏡像ではない公算が高い**。

⚠ **この反証は逐語照合で機械に掛ける義務がある** — facts `## M5 (T3b)` 行 1 の再検証コマンドをそのまま使う
(⚠ **一次文献の取得は [`lit-fetch.sh`](lit-fetch.sh)。抽出テキストは repo が public なのでコミットしない**)。

### ⚠ 併記する 2 点 (どちらか一方だけを書かない)

1. ⚠⚠ **本 leg は gate であって `Thm7 ⊋ C` の材料を出す leg ではない** — **GO でも出ない**。
2. ⚠⚠ **`e < h(p)` の帯を「比較の相手が無い」という理由で捨てない** — **その帯が的として空なのは
   標的が真だと証明されたからであって、理由が違う** (SoT = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md)
   §4.1 の訂正 3 / 訂正 4)。

---

## 1. 反証条件 (§4.4-2 の義務。⚠ 着手前に書いてある。事後に書き換えない)

### (a) 候補 4 (`e > h(p)` 側) の分 = 継承 (⚠⚠ 複製も書き換えもしない)

**SoT = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2 の 3 本** (付記 2 本を含む)。
**本書は参照のみを書き、条件文を写さない** — 理由は親 plan §7 判断ログ 10-(3) が「複製も書き換えもしない」と
定めているためである。

### (b) 候補 2 (別インスタンス族) の分 = 本 leg で新たに書く 3 本

1. **選んだ族で `C` の閉形が 3 レートで書けない** — Theorem 2 / Claim 4 はいずれも**補助変数上の和集合**として
   与えられており (逐語の SoT = facts `## M5 (T3b)` 行 1)、同節の**最終行 (行 6)** は
   「**境界点 1 つでも最適化が要る**」と明記している ⟹ 「閉形」と呼べる形 (`Thm7` 側と同じ平面で
   支持関数か明示不等式として書ける形) にならないなら、**候補 2 は `probe-failed` で死ぬ**。
   ⚠ **これが 3 本の中で最も起きやすいと予測する**。
2. **選んだ族が [probc] の鏡像で新情報ゼロ** — 族の上での `Thm7` と `C` の比較が [probc] と同じ恒等式へ潰れる
   (= N9 / N10 の連鎖がそのまま再現する) なら **`known-result` で死ぬ**。
3. **族は立つが `Thm7` 側の比較が S8 に食われて外せない** — 上界だけでは gate の問いに答えられず、
   `∀T_{J|X}` の潰れ (facts `## M5 (T3b)` 最終行 (行 6) の S8、⚠ **未決**) を経由しないと比較が閉じないと
   判明したら、**本 leg では GO を出さず NO-GO 側に落とす**。
   ⚠ **S8 を本 leg で攻めない — 枠が無い**。

⚠ **3 本に共通の禁止 (親 plan §4.5)**: **数値掃引の非違反は証拠価値がほぼ 0 である** ⟹
⚠ **許容差を締める / 格子を細かくするのは証拠にならない**。

### 1.1 GO / NO-GO の出力型 (⚠ 着手前に固定する)

- **GO** = 「`C` の閉形が書けて `Thm7` と同じ平面に置ける族」が**具体に 1 つ**立つ ⟹
  **N16 の第 2 段 `[構築 + probe]` へその族 1 本だけを渡す**。
- **NO-GO** = **候補 2 と候補 4 が同時に死ぬ** ⟹ 親 plan §7 判断ログ 10-(3) のとおり
  **候補 1 (一般 BC への持ち上げ) の `restatement` 公算の裏づけ**になり、**N16 は棚卸しへ落ちる**
  (受け皿 = 候補 3 = (γ) の層 3 化)。
- ⚠ **否定的判定 (NO-GO / 反例 / 壁) を出した場合は親 plan §4.6 の敵対的独立監査が必須**である。

---

## 2. 対象の固定 (⚠ 原典からの逐語。記憶で書かない)

**一次文献の取得** = [`lit-fetch.sh`](lit-fetch.sh)。行番号はすべて `pdftotext -layout` 出力に対する実測値である
(⚠ **抽出テキストは repo が public ゆえコミットしない**)。本節が使う stem は
`probc` / `auxrec` / `GK-outer` / **`glnsum`** の 4 本で、⭐ **`glnsum` は本 leg で lit-fetch.sh へ追加した**
(Gohari–Liu–Nair, *The Capacity Region for Classes of Sum-Broadcast Channels*, arXiv:2606.12839。
⚠ **台帳は従来 id だけを持ち取得手順を持っていなかった**)。

**逐語の機械再検査** = [`verifiers/n15_instance_gate.py`](verifiers/n15_instance_gate.py) の **G0**
(**34 本**の引用を stem + 行番号で照合。`LIT=<dir>` を渡したときのみ走る)。

### 2.1 検査軸を成す 2 本の包含 (⚠ どちらも無条件であることを確認した)

| # | 主張 | 出典 (逐語) | 条件 |
|---|---|---|---|
| I1 | `C ⊆ Thm7` | `auxrec.txt:1034-1036` — "Theorem 7. **Given a broadcast channel** characterized by T (y, z\|x) **and any achievable rate triple** (R0 , R1 , R2 ), one can find some input distribution p(x) such that **for any auxiliary channel** TJ\|X,Y,Z , the following constraints are satisfied" | **無条件** (チャネルにもレートにも仮説が無い) |
| I2 | `Thm7 ⊆ UV` | `auxrec.txt:1172-1178` Remark 12 — "From (18a), (18b), (18e), (18i), we can extract the following constraints: … This implies that the outer bound in Theorem 7 is at least as good as the U V outer bound **for all broadcast channels** T (y, z\|x)." | **無条件** |

⚠ **I2 が指す `UV` の版**: `auxrec.txt:1014` 逐語 "for some triple of random variables (U, V, W ) such that
(U, V, W ) −− X −− (Y, Z)" = **一般 witness 版**であり、独立性 `p(u)p(v)p(w|u,v)` を課す版ではない
(版の差の SoT = facts [`bc-facts.md`](bc-facts.md) `## M1 (T3b)` 行 4b の (α))。
⭐ **下の [glnsum] 側の `O_UVW` も一般 witness 版である** — `glnsum.txt:60-61` 逐語
"for some pmf p(u, v, w, x). Further, it suffices to consider (U, V, W ) satisfying |W| ≤ |X | + 5, …"
⟹ **本節は 2 つの版を混ぜていない**。

⭐ **さらに制約集合そのものを逐語で突き合わせた** (⚠ **facts `## M1 (T3b)` 行 4 が版の取り違えで 1 度事故った
箇所なので、名前の一致では済ませない**): [glnsum] Theorem 2 の `(2a)`–`(2e)` (`glnsum.txt:55-59`) と
[auxrec] Theorem 6 の 4 本 (`auxrec.txt:1005,1011-1013`) は、**前者が和レート制約を 2 本に分けて書き、
後者が同じ 2 本を `min(·,·)` にまとめている**という表記の差しかない。**witness の条件も同一**
(`auxrec.txt:1014` "for some triple of random variables (U, V, W ) such that (U, V, W ) −− X −− (Y, Z)"
/ `glnsum.txt:61` "for some pmf p(u, v, w, x)")。
⟹ **`O_UVW`([glnsum]) と `UV`([auxrec] Theorem 6) は同一の領域である** ⟹ I2 の挟み込みは
[glnsum] の `O_UVW ⊋ C` にそのまま接続する。

### 2.2 [probc] の 3 つの対象と、そのクラス仮説

| 対象 | 逐語の所在 | 仮説 |
|---|---|---|
| **Claim 4** (積チャネルの外界) | `probc.txt:488-502` | "Given a product channel q(y1 , y2 , z1 , z2 \|x1 , x2 ) = q1 (y1 , z1 \|x1 )q2 (y2 , z2 \|x2 ), **the union over all p1 (w1 , u1 , v1 , x1 )p2 (w2 , u2 , v2 , x2 )** of triples (R0 , R1 , R2 ) satisfying … forms an outer bound to the capacity region of the product broadcast channel." |
| **Theorem 2** (逆向き semi-deterministic の容量) | `probc.txt:541-548` | "The capacity region for a product of **reversely semi-deterministic** (say, channels X1 → Y1 , X2 → Z2 are **deterministic**) broadcast channel is given by the union of rate triples satisfying … **over all p1 (w1 , v1 , x1 )p2 (w2 , u2 , x2 )**." (クラスの定義は `probc.txt:128-131` = "either both q1 (y1 \|x1 ), q2 (z2 \|x2 ) ∈ {0, 1} or both q1 (z1 \|x1 ), q2 (y2 \|x2 ) ∈ {0, 1}") |
| **Theorem 3** (逆向き more-capable の容量) | `probc.txt:558-574` | "The capacity region for a product of **reversely more-capable** (say, receiver Z1 is more capable than Y1 , and receiver Y2 is more capable than Z2 ) broadcast channel is given by …" (クラスの定義は `probc.txt:132-135` = 2 本の `∀p(x_i)` つき情報量不等式) |

⭐ **3 つを結ぶ逐語 (本 leg の判定の骨)**:

- `probc.txt:551` — Theorem 2 の逆定理 = "**The converse is also immediate from the outer bound in Claim 4.**"、
  `probc.txt:557` — "**Thus the outer bound is contained in the inner bound (and hence they coincide).**"
- `probc.txt:592` — Theorem 3 の逆定理 = "**The converse is also reasonably immediate from the outer bound in Claim 4.**"、
  `probc.txt:610-612` — "the region stated in Theorem 3 is at least as large as the outer bound in Claim 4. Hence the region in Theorem 3 is an outer bound, thus completing the converse."
- ⚠ **さらに 3 つ目のクラスが同じ Claim 4 から出る** — `probc.txt:617-624` Remark 4 "The achievable region in (8) also matches the outer bound in Claim 4 for a variety of other classes. For instance, say **Z1 is more capable than Y1 and Y2 is a deterministic function of X2**."

⟹ **[probc] が容量を決めた 3 クラスはいずれも「Claim 4 = C」という同一の逆定理で閉じている**
(⚠ **クラス仮説は互いに違うが、逆定理は 1 本しかない**)。

### 2.3 [probc] 自身が「UV は容量既知クラスで一致する」と書いた箇所の**射程**

⚠⚠ **本項は台帳の訂正を含む** (→ §6-1)。

`probc.txt:34-41` 逐語 (連続する 1 段落):

> "Marton's inner bound [3] and the UV outer bound [4](also sometimes referred to as the Nair–El Gamal
> outer bound) are the tightest known bounds on the capacity region of the broadcast channel. **These bounds
> have been shown to coincide for all classes of broadcast channels with known capacity regions.** Recently
> it has been shown [5], [6], [7] that there are channels for which these inner and outer bounds do not
> coincide. Therefore, clearly at least one of them is strictly sub-optimal.
> **In this paper we show that the UV outer bound is strictly suboptimal by establishing the capacity region
> for a new class of broadcast channels and showing that this capacity region coincides with Marton's inner
> bound but not with the UV outer bound.**"

⟹ ⚠⚠ **`:36` の一文は「本論文の寄与以前の知識状態」の記述であり、同じ段落の `:39-41` が
それを覆している** — [probc] の寄与そのものが「**容量が既知でありながら UV と一致しないクラス**」の構成である。
⟹ **`:36` を時制なしの定理として引くことはできない**。

**同じ切り分けを 2026 年の一次文献が明示的に書いている** — `glnsum.txt:64-76` 逐語:

> "Remark 2. The UVW outer bound, like Marton's inner bound, matches the capacity region for certain classes
> of broadcast channels, [1], [4], [8], [12], [13], [21], [23]–[25]. **In all these cases, O_UVW (T ) = C(T ) = M(T ).**
> … In [14], a class of product broadcast channels was identified for which Marton's inner bound (Theorem 1)
> equals the capacity region. Notably, **the UVW outer bound yields a strictly larger region, with
> O_UVW (T ) ⊋ C(T ) = M(T ).** … In Section III, we provide a **sum**-broadcast channel with semi-deterministic
> components for which **O_UVW (T ) ⊋ M(T )**. … Moreover, this sum-broadcast channel **does not admit a product
> decomposition, so the outer bound in [14] does not apply.**"

### 2.4 [probc] の外の族 — [glnsum] の和 (⊕) チャネル

| 対象 | 逐語の所在 | 内容 |
|---|---|---|
| **Definition 3** (和チャネル) | `glnsum.txt:376-397` | `T = Ta ⊕ Tb` — 入出力アルファベットを**直和**で貼り合わせ、成分外の遷移確率を 0 にする。⚠ **積ではない** |
| **Corollary 1** (⭐ `M` の支持関数の閉形) | `glnsum.txt:481-493` | 任意の `λ0 ≥ λ1 ≥ λ2 ≥ 0` に対し `max_{M(T)} λ0R0+λ1R1+λ2R2 = min_{α∈[0,1]} λ0 log2( 2^{SR_a/λ0} + 2^{SR_b/λ0} )` (`SR_x` = 成分 `T_x` の重みつき和レート) |
| **Theorem 4** (⭐ 主定理) | `glnsum.txt:682-698` | 成分が primary クラス条件 (a)/(b)/(c) を満たすとき `max_{O_aux} = max_{C} = max_{M}`、全 `λ` で満たすなら "**M(T ) = C(T ) = O_aux (T )**"。⚠ **`O_aux` = 同論文 Theorem 3 = `glnsum.txt:302` 逐語 "Theorem 3 (Theorem 8, [16])" = [auxrec] Theorem 8** |
| **Lemma 3** | `glnsum.txt:224` | "If TY Z\|X is either a less-noisy or **semi-deterministic** broadcast channel, then TY Z\|X ∈ P^{λ0,λ1,λ2} **for all** λ0 ≥ λ1 ≥ λ2 ≥ 0." |
| **§III のインスタンス** | `glnsum.txt:511-521` / `:557-597` / `:598-680` | Fig. 3 の**逆向き semi-deterministic 和チャネル** (成分は [probc] Claim 3 の Fig. 2 と同じ形。`:512` 逐語 "This channel resembles the example in [14, Claim 3]")。**Marton 和レート = 7/3** (Corollary 1 で評価)、**UVW 和レート ≥ 5/2** (`(R0,R1,R2) = (0, 5/4, 5/4)` が UVW 外界に入る明示 witness) |

### 2.5 `Thm7` と `Thm8` の**和レート**の順序 ([GK-outer] 2026)

- `GK-outer.txt:194` — "**Theorem 3 (Theorem 7, [12])**" ⟹ GK-outer の Theorem 3 = [auxrec] Theorem 7。
- `GK-outer.txt:255` — "**Theorem 4 (Theorem 8, [12])**" ⟹ GK-outer の Theorem 4 = [auxrec] Theorem 8。
- `GK-outer.txt:339-340` — "To address this, **we provide a weaker version of the outer bound in Theorem 3 (for the sum-rate)** which can be numerically evaluated." ⟹ Theorem 6 は `Thm7` の弱化 (和レートのみ)。
- `GK-outer.txt:381-383` — "**Proposition 2.** For every TG,K\|X,Y,Z , the sum-rate of the outer bound region in Theorem 4 is **greater than or equal to** the sum-rate of the outer bound region in Theorem 6 for the choice of J = (G, K). In other words, the sum-rate constraints established by Theorem 6 (Theorem 3) **imply the sum-rate constraints set forth in Theorem 4**."

⟹ **和レート (方向 `(1,1,1)`) に限り `SR_Thm7 ≤ SR_Thm6 ≤ SR_Thm8`**。
⚠⚠ **これは領域レベルの順序ではない** — `Thm7` と `Thm8` の包含はどちら向きも未証明であり
(`auxrec.txt:1558-1561` 逐語 "we give two outer bounds for broadcast channels. The examples for which these
two bounds strictly improve over the UV outer bound are different. **Unification of these two outer bounds into
a single bound is left as future work.**")、⚠ **本書はそれを主張しない**。

---

## 3. 導出 (⚠ 道具は §4.5 の 3 つだけ)

**機械の SoT** = [`verifiers/n15_instance_gate.py`](verifiers/n15_instance_gate.py) (**41/41**、EXIT=0。
逐語照合 `G0` を落とす `LIT` 無しの実行でも **7/7**)。⚠⚠ **G1–G6 は `fractions.Fraction` の厳密有理演算のみで、
最適化器も許容差も 1 つも使っていない**。浮動小数は G7 の 2 点評価だけである。

### 3.1 段 1 — 検査軸そのもの (**道具 1 = 恒等式への帰着**)

§2.1 の I1 / I2 はどちらも無条件ゆえ、**任意のチャネルで `C ⊆ Thm7 ⊆ UV`** が成り立つ。
⟹ **`UV = C` が成り立つ族では `Thm7 = C` が強制される** (`G6`)。
⟹ ⭐ **比較が情報を持ちうるのは `UV ⊋ C` が成り立つ族に限られる**。

⚠ **この段に数値は 1 つも入っていない** — 2 本の包含と集合の挟み込みだけである。

### 3.2 段 2 — `UV ⊋ C` かつ `C` が既知の族の列挙 (**道具 3 = 閉形の族の直接評価**)

⚠ **列挙の母集団を先に固定する** = 「**容量領域が公表されている BC のクラス**」。

| 族 | `C` は書けるか | `UV ⊋ C` か | 本 gate に対する状態 |
|---|---|---|---|
| **(A) 2011 年以前の容量既知クラス**全体 (degraded / less noisy / more capable / deterministic / semi-deterministic / degraded message sets / 逆向き degraded の積・和) | ○ | **× (`O_UVW = C = M`)** — `glnsum.txt:64-67` 逐語 | ⭐ **段 1 により `Thm7 = C` が強制** ⟹ 新情報ゼロ |
| **(B) [probc] の積 3 クラス** (Theorem 2 / Theorem 3 / Remark 4) | ○ | ○ (`glnsum.txt:69`) | ⚠ **[probc] の内側**。かつ §3.3 の連鎖で**和レート面は文献だけで閉じる** |
| **(C) [glnsum] の和クラス** (成分が degraded / less-noisy / more-capable / deterministic / semi-deterministic) | ○ (**Corollary 1 = 支持関数の閉形**) | ○ (`glnsum.txt:73`、明示 witness `(0,5/4,5/4)`) | ⭐ **[probc] の外** (`glnsum.txt:75-76` 逐語「積分解を持たないので [14] の外界は適用できない」) |
| **(D) erasure Blackwell** ([auxrec] §4.2) | **×** — `auxrec.txt:1250` 逐語 "**Determining the true corner point for the erasure Blackwell channel remains an open problem.**" | ○ (corner が達成不能) | **比較の相手が無い** ⟹ `probe-failed` |

⚠ **母集団の外は数えていない** — 「公表されていない容量既知クラス」は原理的に列挙できない (→ §6-4)。

### 3.3 段 3 — (B) の和レート面は文献だけで閉じる (**道具 1 = 恒等式への帰着**)

§2.2 の 3 本の逐語から `C ⊆ Thm8 ⊆ Corollary 4 = Claim 4 = C` が [probc] の積クラス上で立つ
(**(1)** `auxrec.txt:1507-1508` = Corollary 4 は Theorem 8 の特殊化 / **(2)** `auxrec.txt:1532-1535` Remark 17(1)
= 積チャネル上で Corollary 4 は [GGNY14] の外界へ帰着 / **(3)** `probc.txt:551-557` / `:592`,`:610-612`
= Claim 4 は内界と一致)。⟹ **`Thm8 = C`**。

これに §2.5 の Proposition 2 と `C ⊆ Thm7` を重ねると、方向 `(1,1,1)` で

  `SR_C ≤ SR_Thm7 ≤ SR_Thm6 ≤ SR_Thm8 = SR_C`

⟹ ⭐ **`SR_Thm7 = SR_C`**。⚠⚠ **和レート面に限る** — `R0` / `R0+R1` / `R0+R2` の面については何も出ない。

⚠ **同じ連鎖は (C) にも当たる** — [glnsum] Theorem 4 が `O_aux = C` を与え `O_aux` = [auxrec] Theorem 8
ゆえ、Fig. 3 のインスタンスでも `SR_Thm7 = SR_C = 7/3` が文献だけで従う。
⟹ ⚠⚠ **(C) を使うなら方向 `(1,1,1)` を避ける必要がある**。

### 3.4 段 4 — (C) には `(1,1,1)` を避けた**生きた方向の錐**が在る (**道具 1 + 道具 3**)

**入力は 3 つだけ**である: (i) `SR_C = 7/3` (`glnsum.txt:557-597`、Corollary 1 の閉形。⭐ **`G3` が
`α = 1/2` で 2 つの指数が一致して対数が消えることを厳密有理で確かめた** — 探索ではなく恒等式) /
(ii) `(0, 5/4, 5/4) ∈ UV` (`glnsum.txt:599-680` の明示 witness) / (iii) `C ⊆ {R ≥ 0}`。

方向 `λ = (1, 1, 1−d)` に対し

  `h_UV(λ) ≥ λ·(0,5/4,5/4) = (5/4)(2−d)` / `h_C(λ) ≤ max_C (R0+R1+R2) = 7/3`

⟹ **`h_UV(λ) > h_C(λ)` は `d < 2/15` と同値** (`G5`、厳密有理。`d = 2/15` で境界の差はちょうど 0)。
⟹ ⭐ **`d ∈ (0, 2/15)` の各方向で `C ⊊ UV` が厳密に立ち、しかもそれは和レート方向ではない**
⟹ **§2.5 の Proposition 2 は当たらない** ⟹ `h_C(λ) ≤ h_Thm7(λ) ≤ h_UV(λ)` は**両側とも文献に釘付けされていない**。

⚠ **ここで `Thm7` の値は 1 つも計算していない** — 立てたのは「潰れていない」ことだけである。
⚠⚠ **`Thm7 ⊋ C` の材料はここからは出ない** (gate ゆえ原理的に出ない)。

### 3.5 段 5 — 候補 4 (`e > h(p)` 側) の離調 (**道具 3 = 明示 witness の直接評価**)

[probc] のインスタンスは `X1 → Y1 = BEC(e)`, `X1 → Z1 = BSC(p)` (と鏡映)。`e > h(p)` へ離調すると:

- **Definition 3 の第 1 項** (`I(X1;Y1) ≥ I(X1;Z1)`, ∀`p(x1)`) は**一様入力で落ちる** (`p=0.1, e=0.6`:
  `0.4000 < 0.5310`)。⚠ **これは台帳 `## N10 (T3c)` の `B33` と同じ境界である**。
- **Definition 3 の第 2 項** (向きを逆にした版) は**歪んだ入力で落ちる** — `X1 = Bern(q)`, `q = 1e-3` で
  `I(X1;Y1) = 0.004563 > I(X1;Z1) = 0.002531` (BEC 側は `q log(1/q)` を保つが BSC 側は `q` の 1 次でしか
  伸びない)。⟹ **どちらの向きの more capable も成り立たない**。
- **Definition 2** は成分の決定性を要求するが `0 < e < 1` / `0 < p < 1/2` ではどちらも決定的でない。
- **Remark 4 の混合クラス**も決定的成分を要求するので同じ理由で当たらない。

⟹ (`G7`) **離調したインスタンスは [probc] の 3 クラスのいずれにも属さない** ⟹ **`C` の閉形を供給する
定理が 1 本も無い**。⚠ **これは「その帯に的が無い」ではなく「比較の相手が無い」である**。
⚠⚠ **`e < h(p)` の帯を同じ理由で捨ててはならない** — その帯が的として空なのは
**標的が真だと証明されたから**であって理由が違う (SoT = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md)
§4.1 の訂正 3 / 訂正 4)。

### 3.6 ⚠ 数値を screen として使った箇所 (明示)

- **§3.5 の 2 点評価** — 浮動小数を使うのはここだけである。⚠ **掃引ではなく 2 つの明示入力分布の直接評価**
  であり、差は倍精度の雑音より 13 桁以上大きい。⚠ **それでも「何も見つからなかった」型の証拠は 1 つも
  使っていない** (使ったのは**成立する不等式の提示**だけである)。
- **G1–G6 に screen は無い** — 厳密有理演算のみ。

---

## 4. 判定

### 4.1 判定

> ## ⭐ 判定 = **GO**

**理由 (1 行)**: **[glnsum] の和 (⊕) broadcast channel クラスは [probc] の外にあり** (積分解を持たない、
`glnsum.txt:75-76`)、**`C` の支持関数が全方向で閉形で書け** (Corollary 1)、**`UV ⊋ C` が
和レート方向を含む錐で厳密に立つ** ⟹ **`d ∈ (0, 2/15)` の方向 `(1,1,1−d)` では
`C ⊆ Thm7 ⊆ UV` の挟み込みが潰れず、かつ [GK-outer] Proposition 2 の釘付けも当たらない**。

⚠⚠ **併記する 4 点 (どれか 1 つでも落とすと本判定は過大になる)**:

1. **`Thm7 ⊋ C` の材料は本 leg でも 1 つも出ていない** — gate ゆえ原理的に出ない。**排除もされていない**。
2. **方向 `(1,1,1)` は使えない** — そこでは `SR_Thm7 = SR_C` が文献だけで従う (§3.3)。
   ⚠ **これは本 leg が新たに導いた否定的な事実であり、GO の射程を狭める側である**。
3. **GO の型は上界比較に寄っている** — `Thm7` の**上界**は単一の `T_J` で取れる (facts `## N1 (T3c)` の実例) が、
   **`Thm7` に点が入ることを言う側は `∀T_{J|X}` の潰れ (facts `## M5 (T3b)` 最終行の S8、⚠ 未決) を通る**。
4. **`Thm7 ⊆ Thm8` が (未証明のまま) 真であれば本族は即座に死ぬ** — [glnsum] Theorem 4 が `Thm8 = C` を
   全方向で与えているので、領域レベルの順序が付いた瞬間に `Thm7 = C` が従う。
   ⚠ **現在それはどちら向きも証明されていない** (`auxrec.txt:1558-1561`) が、⚠⚠ **本族の生死を握る唯一の
   外部依存はここである**。

### 4.2 反証条件の結果 (⚠ 事前に書いたもの。事後に書き換えない)

#### (a) 候補 4 の分 = 継承 (⚠ 条件文は写さない — SoT = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §4.2)

- **1 本目 = ⭐ 発火した**。§3.5 が `e > h(p)` の離調インスタンスは [probc] の 3 クラスのいずれにも
  属さないことを明示 witness 2 本で確かめた ⟹ **`C` の閉形を供給する定理が無く、比較の相手が立たない**。
  ⚠ **同 §4.2 の「最も起きやすい」という予告どおりの発火である**。
  ⚠ **付記 (同 §4.2 が事後に足した分) と整合**: 壊れるのは `e > h(p)` 側だけであり、`e < h(p)` 側では
  more capable は強まる。
- **2 本目 / 3 本目 = 本 leg では評価していない** — どちらも「超過をどう説明するか」の条件であり、
  1 本目が発火して比較の相手が消えた時点で**評価に入れる対象が無い**。⚠ **不発火と書かない**。

#### (b) 候補 2 の分 = 本 leg で新たに書いた 3 本

| # | 条件 | 結果 | 根拠 |
|---|---|---|---|
| **1** | 選んだ族で `C` の閉形が 3 レートで書けない (⚠ **最も起きやすいと予測**) | **不発火** | [glnsum] **Corollary 1** (`glnsum.txt:481-493`) は `M(T)` の**支持関数**を `λ0 ≥ λ1 ≥ λ2 ≥ 0` の全方向で明示の閉形で与える ⟹ 起票が要求した「`Thm7` 側と同じ平面で**支持関数**として書ける形」そのものである。⭐ **[probc] Theorem 2 / Theorem 3 が「境界点 1 つでも最適化が要る」(facts `## M5 (T3b)` 行 6) のに対し、和チャネルでは成分の重みつき和レートと 1 変数 `α` の最小化に潰れる** ⟹ **起票の予測は外れた** |
| **2** | 選んだ族が [probc] の鏡像で新情報ゼロ (`known-result`) | ⚠⚠ **部分発火** | **和レート方向 `(1,1,1)` では発火する** — §3.3 の連鎖で `SR_Thm7 = SR_C` が文献だけで従う。⚠ **同じ連鎖は [probc] の積 3 クラス全部に当たるので、候補 2 を「[probc] Theorem 2 の積クラス」で取る筋は和レート面では死ぬ**。**しかし §3.4 の錐 (`d ∈ (0, 2/15)`) では発火しない** — そこでは挟み込みも Proposition 2 も当たらない。⚠ **N9 / N10 の連鎖が再現するか**という条件文の字義については **再現しない** (連鎖は BEC 固有の恒等式と二値の `δ` に依存し、Fig. 3 の成分は `\|X\|=4` / `\|Y\|=6` / `\|Z\|=2` で二値ではない) |
| **3** | 族は立つが `Thm7` 側の比較が S8 に食われて外せない | **不発火 (⚠ 射程つき)** | facts `## N1 (T3c)` (A) が「`Thm7` の上界は単一の `T_J` だけで、適格性 (19)/(20a)/(20b) を 1 本も消費せずに立つ」実例を持つ ⟹ **上界側の比較は S8 を通らない** ⟹ 「上界だけでは gate の問いに答えられない」という条件文の前段が成り立たない。⚠⚠ **ただし `Thm7` に点が入ることを言う側は S8 を通る** — この限定は §4.1-3 に併記した。⚠ **S8 は本 leg で 1 mm も攻めていない** |

### 4.3 ⭐ 見立ての較正 (⚠ §0 は 1 文字も書き換えていない。効きは本節に書く)

⚠ **親 plan §4.4 の実測 (締める方向 = 9 件中 9 件が機械で覆った / 緩める方向 = 当たり 3・外れ 5) に
本 leg の 3 本を足せる形で書く**。⚠ **母集団と分類基準を先に固定する** — 本 leg は
「**着手前に §0 へ書かれた見立て 3 本**」だけを数え、`当たり` / `外れ` / `判定不能` の 3 値で分類する。

| 見立て | 向き | 判定 | どこが外れたか (1 行) |
|---|---|---|---|
| **A** (`C` の閉形は [probc] の外にも書ける) | **緩める** | ⚠ **結論は当たり / 経路は外れ** | **結論**は立った (族は在る) が、**予測した経路 ([probc] Theorem 2 の積クラス) は死ぬ** — Theorem 2 は [probc] の**内側**であり、しかもその和レート面は §3.3 の連鎖で文献だけで閉じる。⚠ **副次の主張「`e > h(p)` の離調で壊れるのは Theorem 3 側だけ」も外れ** — 離調したインスタンスは Theorem 2 のクラスにも入らない (成分が決定的でない、§3.5) ので Theorem 2 は最初から比較の相手を供給しない。**生きた族は和 (⊕) チャネル側にあった** |
| **B** (族が立っても `Thm7` 側が評価できず GO を出せない) | **締める** | ⚠ **強い形は外れ / 弱い形は当たり** | 強い形 (GO を出せない) は**覆った** — 上界側は単一 `T_J` で取れるので S8 を通らない。⚠ **§0 が自分で書いた弱い形「GO の型が上界比較に限られる」は生き残った** (§4.1-3)。⟹ **着手前 1 行反証は有効に働いた** |
| **C** (Theorem 2 のクラスは [probc] の鏡像で `known-result` で死ぬ) | **締める** | ⭐ **当たり (覆らなかった)** | ⚠⚠ **ただし着手前に書いた 1 行反証は「逐語としては正しいが的を外していた」** — 「Theorem 2 と Theorem 3 のクラス仮説は交わらない」は `probc.txt:128-135` の逐語どおり**正しい**が、`known-result` の死は**クラス仮説の一致からではなく共有された逆定理 (Claim 4 = C) から来る** ⟹ **仮説が違っても死因は同じである**。⟹ **反証の対象が違っていた** |

**⭐ 本 leg が §4.4 の実測に足すもの (⚠ 報告であって判定入力ではない)**:

- **締める方向 2 本** — **1 本覆った (B)** / **1 本覆らなかった (C)**。
  ⟹ ⚠⚠ **「締める方向は全件覆る」は本 leg でも再現しない** (N12 §5 (c) が判定枠で観測したのと同じ形)。
- **緩める方向 1 本** — **結論は生存したが根拠が入れ替わった (A)**。
  ⟹ ⭐ **新しい型の外れ方である**: 台帳の既存語彙 (`当たり` / `外れ`) は**結論の真偽**しか見ておらず、
  「**結論は当たったが、その見立てが指した対象は死んだ**」を表現できない。
  ⚠ **これを `当たり` に丸めると、見立て A が名指しした Theorem 2 の積クラスが生きているかのように読める**。
- ⭐ **本 leg 固有の観測 (C から)**: **着手前 1 行反証は「逐語として正しい」だけでは義務を果たさない** —
  反証が**見立ての死因と同じ軸**を突いているかを確かめる段が要る。⚠ **これは処方の提案であって
  §4.4 の改定ではない** (改定は plan の仕事)。

---

## 5. gate の出力 — N16 へ渡すもの

⚠ **N16 が何をするかは書かない (配分は orchestrator の仕事)。本節は「渡すもの」だけを書く。**

### 5.1 ⭐ 渡す族 = **1 本だけ**

> **[glnsum] の和 (⊕) broadcast channel クラス — 成分が semi-deterministic のもの。
> 具体インスタンス = `glnsum.txt:511-521` Fig. 3 の逆向き semi-deterministic 和チャネル。**

**この族が持ち込むもの (すべて逐語または厳密有理で裏が取れている)**:

| # | 資産 | 所在 |
|---|---|---|
| 1 | `C` の**支持関数の閉形** (全方向 `λ0 ≥ λ1 ≥ λ2 ≥ 0`) | `glnsum.txt:481-493` Corollary 1 |
| 2 | `C = M = Thm8` (**領域レベル**、全方向) | `glnsum.txt:682-698` Theorem 4 + `:224` Lemma 3 |
| 3 | 具体インスタンスの `SR_C = 7/3` (**厳密有理**、`α = 1/2` で対数が消える) | `glnsum.txt:557-597`、検証器 `G3` |
| 4 | `UV` 側の明示 witness `(0, 5/4, 5/4)` ⟹ `SR_UV ≥ 5/2` | `glnsum.txt:598-680`、検証器 `G4` |
| 5 | ⭐ **生きた方向の錐** = `λ = (1,1,1−d)`, `d ∈ (0, 2/15)` (⚠ **`d` の上限は厳密有理**) | 検証器 `G5` |
| 6 | ⚠ **使ってはならない方向** = `(1,1,1)` (そこでは `SR_Thm7 = SR_C` が文献だけで従う) | §3.3、検証器 `G0` の Proposition 2 逐語 |
| 7 | ⚠ **族の生死を握る外部依存 1 本** = `Thm7 ⊆ Thm8` の領域レベルの順序 (⚠ 現在どちら向きも未証明) | `auxrec.txt:1558-1561`、facts `## M1 (T3b)` 行 2 |
| 8 | 和チャネル固有の構造 = 成分指標 `Q` が **`X` の関数であると同時に `Y` の関数でも `Z` の関数でもある** (`glnsum.txt:636` 逐語 "since Q indicates the channel component and is therefore a function of either Y or Z") | `glnsum.txt:634-637` |

⚠ **渡さないもの (明示)**: **[probc] Theorem 2 の積クラスは渡さない** (§4.2 (b)-2 の部分発火。
和レート面は文献だけで閉じ、`C` の境界点 1 つに最適化が要る) / **erasure Blackwell は渡さない**
(`C` が未知ゆえ比較の相手が無い) / **`e > h(p)` の離調族は渡さない** (§4.2 (a) 1 本目が発火した)。

### 5.2 候補 2 / 候補 4 の状態 (⚠ NO-GO ではないので「同時に死んだ」とは書かない)

- **候補 4 (`e > h(p)` 側) = 死んだ**。死因 = `probe-failed` (比較の相手が無い)。
  ⚠ **これは「その帯に分離が無い」ではない** — **測れない**のである。
- **候補 2 (他インスタンス) = 生きている。ただし起票時の中身とは別物になった** —
  死んだのは「[probc] Theorem 2 の積クラスで同じ 3 段を回す」筋 (`known-result`、和レート面) であり、
  生きたのは**積ですらない和チャネル側**である。
- ⟹ ⚠⚠ **候補 1 (一般 BC への持ち上げ) の `restatement` 公算の裏づけは本 leg では得られない** —
  それは NO-GO のときの出力であった。⚠ **同時に、候補 1 が動いたわけでもない** (facts `## N6 (T3c)` の
  N6-j は 1 文字も動いていない)。
- **候補 3 ((γ) の層 3 化) は消していない** — 受け皿として残る (親 plan §7 判断ログ 10-(6))。

### 5.3 ⚠ 未反映

- 親 plan §5.1 の **N15 着地ブロック**は未反映である。
- facts [`bc-facts.md`](bc-facts.md) の **`## N15 (T3c)` 節**は未作成である。
- ⭐ **facts `## M1 (T3b)` 行 4 の訂正** (→ §6-1) は未反映である。
- **親 plan §5 の「次に来るもの」の候補行**は未反映である。
- ⚠ **本書冒頭の `⏳ 起票のみ (実行前)` の注記は残したままである** — 起票ブロックを事後に触らない義務
  (親 plan §4.4-2) と衝突しうるので、**書き換えの可否は orchestrator の判断へ回す**。
  ⚠ **§0 / §1 は 1 文字も動かしていない** (`4a8061f7` の 1–97 行と byte 一致。消したのは §2 の直前に
  置かれていた `⏳ 以下 §2–§6 は未記入である` のプレースホルダ 1 行だけである)。
- ⚠ **本 leg は否定的判定 (候補 4 の死 + facts 1 行の訂正) を含むので、親 plan §4.6 の敵対的独立監査が要る**
  (⚠ **本 leg は自分では監査できない**)。

---

## 6. ⚠ 確かめて「いない」ことの名指し

⚠⚠ **本節を薄くしない**。

1. ⭐⭐ **facts `## M1 (T3b)` 行 4 は本 leg の逐語照合と矛盾する — 訂正が要る (⚠ 本 leg は台帳を書き換えていない)**。
   同行は `probc.txt:34-36` を引いて **「容量が既知のクラスすべてで `Thm7` と `C` は私信平面 `R0 = 0` の上で
   一致する」**と結論している。⚠ **`:36` の一文は本論文の寄与**以前**の知識状態の記述であり、
   同じ段落の `:39-41` と Claim 3 (`probc.txt:339-344`) がそれを覆している** (§2.3)。
   ⟹ **同行の連鎖 `M ⊆ C ⊆ UV_2rate_general = M` は [probc] の積クラスでは成り立たない**
   (そこでは `SR_UV ≥ 44/15 > 8/3 = SR_M = SR_C`、しかも Claim 3 は `R0 = 0` の私信和レートの主張である)。
   ⚠⚠ **訂正の向きは「生きている空間が広がる」側である** — 同節 P4 の (i-1) が塞いだとする穴が
   実際には塞がっていない。⚠ **本 leg はこの訂正を facts へ書いていない** (台帳の書き換えは本 leg のスコープ外)。
   ⚠ **同時に、この訂正が過去の leg の判定を動かすかは判定していない** (N7 / N10 は [probc] の上で
   直接測っており行 4 を経由していない、というのは**読みであって機械の裏が無い**)。
2. **`Thm7` の値を 1 つも計算していない** — 本 leg が立てたのは「挟み込みが潰れていない」ことだけである。
   `h_Thm7(λ)` の上界も下界も、どの方向についても評価していない。
3. **[glnsum] Fig. 3 のチャネル行列を再構成していない** — 図はビットマップであり `pdftotext` では辺構造が
   取れない。本 leg は論文が印字した**値** (`SR_C = 7/3` / `(0,5/4,5/4) ∈ UV` / 成分の重みつき和レートの
   区分線形式) を使っており、**チャネルからそれらを独立に再導出していない**。
   ⚠ **同じ限定が [probc] Fig. 2 にも当たる**。
4. **列挙 (§3.2) の網羅性は「公表された容量既知クラス」に限る** — 未公表・未同定のクラスは数えていない。
   ⚠ **`glnsum.txt:64-65` の引用リスト ([1],[4],[8],[12],[13],[21],[23]–[25]) の中身を 1 本も開いていない**
   ⟹ **(A) の「`O_UVW = C = M`」は同論文の要約を信頼している**。
5. **[glnsum] Theorem 4 の証明を読んでいない** — 使ったのは主張の逐語と Lemma 3 の逐語だけである。
   **primary クラス `P` / `P̂` / `P̂_A` / `P̂_B` の定義 (`glnsum.txt:213-270`) も読んでいない**
   ⟹ **Fig. 3 の成分が条件 (a) を全 `λ` で満たすことは Lemma 3 の逐語に依存しており、独立には確かめていない**。
6. **[GK-outer] Proposition 2 の証明を読んだのは 4 行だけである** (`:384-399`)。とくに
   **`Thm7 ⊆ Theorem 6` の量化子の帳尻 (`∃p ∀T_J` の外側の `∃p` がどう運ばれるか) を再導出していない** —
   §3.3 の連鎖はこの部分を「Theorem 6 は Theorem 3 の弱化である」という著者の言明に依存させている。
7. **`Thm7 ⊆ Thm8` の領域レベルの順序を調べていない** — 探したのは 2 本の言明 (`auxrec.txt:1558-1561` /
   facts `## M1 (T3b)` 行 2) だけで、**2026 年以降の文献を掃いていない**。⚠ **§5.1-7 のとおりこれは
   本族の生死を握る唯一の外部依存である**。
8. **現行 [probc] インスタンス (BEC/BSC の逆向き more-capable 積) の上で `UV ⊋ C` かを確かめていない**。
   `glnsum.txt:69` の `O_UVW ⊋ C = M` は [probc] が同定した「あるクラス」についての要約であり、
   その厳密性の witness は **Claim 3 = 逆向き semi-deterministic の側**である。
   ⚠⚠ **もし現行インスタンスで `UV = C` なら、段 1 により N7 / N9 / N10 の `Thm7 = C` は挟み込みで
   強制されていたことになる** — ⚠ **本 leg はこれを肯定も否定もしていない。判定を待つ問いとして名指しする**。
9. **候補 4 の反証条件 2 本目 / 3 本目を評価していない** (§4.2 (a))。
10. **S8 (`∀T_{J|X}` の潰れ) を 1 mm も攻めていない** — 起票が「枠が無い」と明記したとおりである。
11. **和チャネルの構造 (§5.1-8 の `Q`) が `Thm7` の `∀T_J` を有限個へ落とすかを調べていない** —
    `Q` が `Y` の関数でも `Z` の関数でもあることは逐語で確認したが、**それが `T_J` の選択に効くかは未検討**である。
12. **`d < 2/15` の錐は下界であって最大ではない** — `h_C(λ)` に `λ_max · SR_C` という粗い上界を当てた結果である。
    **Corollary 1 で `h_C(1,1,1−d)` を実際に評価すればもっと広い錐が取れる可能性がある**が、
    そのためには成分の `SR^{λ,α}` を `λ ≠ (1,1,1)` で求める必要があり、**本 leg は求めていない**
    (`probc` Appendix A/B と `glnsum.txt:567-578` が与えるのは `λ = (1,1,1)` の場合だけである)。
13. **方向 `(1,1,1−d)` 以外の方向を試していない** — `(1+d,1,1)` / `(1,1−d,1−d)` なども同型に扱えるが評価していない。
14. **検証器 `G6` は集合論の含意を入れ子区間の模型で走らせたものである** — `C` / `Thm7` / `UV` の実物を
    使ってはいない。⚠ **段 1 の効力は §2.1 の 2 本の逐語に依存しており、`G6` はそれを使い違えていないかの
    自己点検にすぎない**。
15. **`glnsum` を [`lit-fetch.sh`](lit-fetch.sh) へ追加したが、他の leg が引く行番号との整合は確かめていない**
    (⚠ **台帳の既存 claim で `glnsum` の行番号を引くものは無い**、というのは `rg` の結果であって
    全文精読の結果ではない)。
16. **本 leg は Lean を 1 行も書いていない** — 層 1 + 層 2 のみである。
