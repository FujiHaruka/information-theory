# Shannon-Hartley converse 最終段 Lean 形式化 — ボトルネック分析

将来「事前ブリーフの verbatim 署名を自動抽出するツール」「Filter.Tendsto 合成の二重極限を配線する tactic 支援」を作るためのベースライン記録。

**定量データ**: [docs/metrics/shannon-hartley-converse-final.metrics.md](../metrics/shannon-hartley-converse-final.metrics.md)

このログは実装を担った `lean-implementer` subagent（`agent-aafa1fc32579dfa1d`）の完了報告を一次情報として、オーケストレーター側で再構成したもの。定性観察（詰まった箇所・空振り・後戻り）は実装者報告の逐語に基づく。

## 0. 対象問題と成果物

連続時間帯域 AWGN 容量 = Shannon-Hartley 閉形式のメイン定理 `contAwgn_eq_shannonHartley` を閉じる converse 最終段。前段までに achievability 半分（`≥`）と converse の C1/C2/C3（count domination・Gauss 回転・ellipsoid）が proof-done。本段は残る C4（water-filling + 二重極限）→ C0（converse 半分の実不等式）→ assembly（`le_antisymm`）。

成果物:

- `InformationTheory/Shannon/ShannonHartleyConverseFinal.lean` — 新規、7 decl、0 errors / 0 warnings / 0 sorry。D1 `contAwgn_log_le_waterfill` / D2 `contAwgnRate_le` / D3 `contAwgn_le_shannonHartley` / D4 `contAwgn_eq_shannonHartley` + helper 3（`waterfill_numerator_nonneg` / `contAwgn_logMaxMessages_le_waterfill` / `waterfill_full_div_tendsto`）。
- `InformationTheory/Shannon/ShannonHartleyMain.lean` — 旧 `contAwgn_eq_shannonHartley`（残 sorry 保持）を削除し ConverseFinal へ移動。
- `#print axioms contAwgn_eq_shannonHartley` = `[propext, Classical.choice, Quot.sound]`（sorryAx-free）、独立 honesty-auditor all-OK。

## 1. 問題のキャラクター

この段は **「事前に位置特定済みの資産を配線する + 実解析の二重極限を書き下す」型**で、Mathlib 検索型でも新規数学型でもない。数学的方針・消費資産の署名・分解（D1–D4）はすべて上流の設計 doc（`shannon-hartley-converse-c2-inventory.md` §Q3）とオーケストレーターのブリーフで確定しており、実装者は route 探索をしていない。

支配項は **Filter.Tendsto の合成による二重極限（T→∞ の後 c₀→0）の配線**。補題探索でも型検査でもなく、「収束の骨組みを Mathlib の `Tendsto.*` で組む」工程が時間を食った。

## 2. 数学的方針

### D1 fixed-T water-filling

ellipsoid `contAwgn_converse_ellipsoid` が既に Fano 項込みの `log M ≤ ∑ ½log(1+νᵢQᵢ/(N₀/2)) + binEntropy Pe + Pe·log(M-1)` を出す。この sum 部に `waterfill_head_tail_bound` を `P' := νᵢQᵢ`（`hP'ν i` は `le_refl`）で適用し、count `#{νᵢ>c₀} ≤ prolateCount` で head 項を抑える。Fano 変形は achievability 側 `contAwgn_log_le_of_pos_k` の該当ブロックを同型で再演。

### D2 二重極限（この段の核）

`contAwgnRate = limsup_T log(maxMsg)/T`。per-T で D1 を適用して `log(maxMsg)/T ≤ g_{c₀}(T)/T` を作り、`g_{c₀}(T)/T` が `waterfill_head_div_tendsto`（head/T → bandlimitedAwgnCapacity）+ 定数項の極限で `L_{c₀}` に収束することから `limsup ≤ L_{c₀}`、最後に c₀→0 を `ge_of_tendsto` で取る。「気づけば一直線、配線が長い」典型。

### D3 / D4

D3 は `⨅ ε:Ioo 0 1, contAwgnRate` に対し `le_of_forall_pos_le_add` + `ciInf_le_of_le`（BddBelow は `contAwgnRate_nonneg`）で ε→0。D4 は `le_antisymm` で両半を束ねるのみ。

## 3. Mathlib 補題探索の実録

**この段では補題探索がボトルネックにならなかった**（実装者報告の逐語: "No grep/loogle came up empty in a load-bearing way; all consumed assets existed exactly as the inventory's LEG 27 §Q3 / 'How the νᵢ enter' described"）。

理由: 消費資産（ellipsoid / `waterfill_head_tail_bound` / `waterfill_head_div_tendsto` / count facade / `contAwgnRate_nonneg` / `contAwgnMaxMessages_bddAbove` / Fano ブロック）の **verbatim 署名 + file:line** がオーケストレーターのブリーフに全て埋め込まれていた。実装者は署名を再検索する必要がなく、「無いものを無いと判断する」時間がゼロだった。これは本段最大の時間節約要因であり、探索コストを実装前に前倒しで潰した結果。

「Mathlib に存在しなかった」もの: **なし**。設計 SoT との食い違いも報告ゼロ。

## 4. 試行錯誤と後戻り

### 4.1 `conv_rhs` の rewrite 順序曖昧で dangling goal

**状況**: `g_{c₀}(T)/T` の等式変形で `conv_rhs => rw [div_right_comm, add_div, add_div]` を打った。

**原因**: RHS に `A/T` 形の部分項が複数あり、`add_div`/`div_right_comm` がどの `_/T` に当たるか曖昧で、rewrite が余計な goal を残した。

**抜け方**: 不透明な prolate/log 項を `set B := <count 項>` で抽象化してから `field_simp`（+ `T=0` 分岐を分割）。抽象化により `field_simp` が `T*P/(count·N₀/2)`（制御不能な分母）へ降りていくのを防いだ。

**教訓**: 複数の `_/T` を含む式で `conv` + 方向性 rewrite は脆い。「不透明項を `set` で名前に畳んでから field_simp」の方が頑健。将来の tactic 支援は「rewrite 対象が複数マッチする箇所を事前警告」+「不透明部分項の自動抽象化」があると当たりが安定する。

### 4.2 `field_simp` が閉じた後の trailing `ring` で "No goals"

**状況**: `field_simp` の後に慣例で `ring` / `ring_nf` を置いていた。

**原因**: `field_simp` が 2 つの goal を完全に閉じてしまい、後続 `ring` が "No goals" エラー（真の失敗ではない）。

**抜け方**: trailing の `ring`/`ring_nf` を削除。

**教訓**: `field_simp` の閉じ切り判定は事前に読めない。metrics のツール失敗 2 回はこの類（無害な over-tactic）。「直前 tactic が goal を全消ししたら後続を no-op 化」する寛容モードがあれば編集往復が減る。

### 4.3 `ge_of_tendsto` のメタ変数が刺さる

**状況**: c₀→0 の極限で `ge_of_tendsto` を適用。

**原因**: フィルタ `x` と関数 `f` がメタ変数のままだと `NeBot` インスタンス解決が詰まる。

**抜け方**: `(x := 𝓝[>] 0)` と `(f := …)` を両方明示 pin。

**教訓**: `ge_of_tendsto` / `le_of_tendsto` 系はフィルタ引数を明示しないと `NeBot` が stuck しがち。二重極限の外側（c₀→0）で頻出。極限系補題の「必須明示引数」を提示する補完があると初手で当たる。

### 4.4 stale-olean phantom（`unknown identifier`）

**状況**: `contAwgn_converse_ellipsoid` が "unknown identifier" になった（2 回）。

**原因**: 上流モジュールの olean が stale。

**抜け方**: `lake build` で上流モジュールを refresh（CLAUDE.md の既定手順どおり）。

**教訓**: 新規ファイルが直前 leg で追加された decl を参照するとき定番。`#print axioms` phantom と同根。既知の footgun で、手順書どおりに解消。

## 5. ボトルネックではなかったもの

- **Mathlib 補題探索** — 事前ブリーフに verbatim 署名が入っていたため実質ゼロ（§3）。ツール投資の観点で最大の示唆: 探索は「実装中」ではなく「ブリーフ作成時」に潰せる。
- **数学的アイデア** — 分解も方針も上流設計で確定済み。実装者は route 判断をしていない。
- **型検査の細部** — `nlinarith` / `gcongr` / `field_simp` / `linarith` でおおむね片付いた（4.1–4.3 の配線を除く）。
- **コンテキスト長** — 単一ターンで 7 decl を skeleton-driven で完遂（cache_read は大きいが圧迫報告なし）。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | ブリーフ用 **verbatim 署名 + TC bracket + file:line の自動抽出**（`sig_view` の延長） | 本段では既に人手で前倒し済み = 探索コスト実質ゼロを再現する仕組み。これが無い段では探索が支配項になりうる |
| 高 | **極限系補題（`ge_of_tendsto`/`Tendsto.*` 合成）の必須明示引数ヒント** | 4.3 のメタ変数 stuck の往復。二重極限の配線で再発頻度が高い |
| 中 | **不透明部分項の自動 `set` 抽象化 + rewrite マルチマッチ警告** | 4.1 の `conv`/`field_simp` 往復 |
| 中 | 直前 tactic が goal 全消し時に後続を no-op 化する寛容モード | 4.2 の "No goals" 往復（metrics 失敗 2 回） |
| 低 | 新規ファイルの上流 decl 参照時に olean refresh を自動挿入 | 4.4（既に手順書で解決済み） |

## 7. 補足

- **設計を縛らなかったのが奏功**: ブリーフは D2 の二重極限を「詰まったら honest sorry で残せ」と明示しつつ route は縛らず、実装者が per-T bound / g の tendsto / c₀→0 を自分で helper（`contAwgn_logMaxMessages_le_waterfill` / `waterfill_full_div_tendsto`）に割った。予測 lemma 名で縛らず自力分割を許した結果、全 sorry-free で着地。
- **採らなかった代替**: D2 を limsup 直接評価でなく per-T bound → 収束の 2 段に割った。limsup を直接いじると `IsBoundedUnder`/`cobddUnder` の副次 goal が絡むため、helper で g/T の tendsto を切り出す方が配線が短い。
- 定量サマリ（ツールコール数・編集回数・所要時間）は [metrics.md](../metrics/shannon-hartley-converse-final.metrics.md) 参照。
