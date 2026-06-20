# relay スキル設計 — セッション連鎖による自律完遂

長いタスクを、context 上限に阻まれず**無人で完遂**するためのスキル設計。1 セッションの context が重くなる前に handoff → 新 tmux セッション起動 → carryon で引き継ぎ、これを完遂まで自動で繰り返す。ユーザーは最初にゴールを与えるだけ。

## 解く問題 / なぜ既存手段で足りないか

- **context 上限**: 単一セッションでは長大タスクを最後まで持てない。判断精度も context 肥大で落ちる（malformed tool call cascade は総 context 量と単調相関 — CLAUDE.md interrupt trigger / memory `pitfall-agent-invoke-malformed`）。
- **auto-compaction では不十分**: ハーネスの自動要約は同一セッション・同一プロセス内の lossy 圧縮。fresh プロセスにならないので特殊トークン忠実度の劣化はリセットされない。curated な handoff の方が状態の質も高い。
- **`/loop` / cron では不十分**: 同一セッションで context が累積する。relay の眼目は「leg ごとに fresh プロセス」。
- 既存 3 スキル（handoff / carryon / tmux-new）は揃っているが、「context が埋まったら自分で次セッションを起こす」最後の自動化が無い。carryon の停止条件 3 は今『ユーザーに promote して止まる』。relay はそこを自動化する。

## Approach（解の形）

relay は **新規ロジックを足すのではなく、既存 3 スキルを駆動する薄いオーケストレーション層**。1 つの relay leg = carryon で状態復元 → オーケストレーターとして自走 → refresh トリガで handoff + 次 leg 起動 → 自セッションは idle 化（後続に kill される）。これを「完遂 / 要ユーザー判断 / 無進捗 / leg 上限」のいずれかに当たるまで連鎖。

設計の要は 3 点:

1. **逐次実行（並列でない）**: 常にアクティブな leg は 1 つ。同一作業ディレクトリを共有するので、後続を起こしたら現 leg は即 idle 化して git 競合（`.git/index.lock` / 二重 commit）を避ける。worktree 不要。
2. **handoff.md に relay 制御ブロックを載せる**: ゴール / leg 番号 / 進捗台帳 / 停止条件 / 前任セッション名。これが連鎖の状態キャリア。
3. **暴走防止が第一級の関心事**: leg 上限 + 無進捗検知 + 各 leg に最低 1 つの具体成果（commit）を要求。

## relay ループ（状態機械）

```
 ┌──────────────────────── leg N ────────────────────────┐
 │ 1. carryon で状態復元 (relay ブロック読込)              │
 │ 2. 前任 (predecessor) を kill ※後続が起動確認後に行う   │
 │ 3. オーケストレーターとして自走 (dispatch/検証/commit)  │
 │ 4. refresh トリガ? ──no──▶ 完遂 or 自走継続            │
 │            │yes                                        │
 │  a. 成果を commit/push  b. 進捗台帳に追記              │
 │  c. handoff 上書き (leg N+1, predecessor=自分)         │
 │  d. tmux-new で <goal>-r(N+1) 起動 → /relay 送信       │
 │  e. 後続の走り出しを確認 → 自 leg は idle 化           │
 └───────────────────────────┬───────────────────────────┘
                             ▼  (後続が step 2 で自分を kill)
                          leg N+1 ...

 完遂/停止条件 → handoff を DONE/PAUSED/ABORTED + サマリに更新
              → PushNotification で通知 → 新 leg を起こさず終了
```

### leg の手順

1. **(起動時) carryon で状態復元** — handoff.md を読み、relay ブロックでゴール / leg 番号 / 進捗台帳を把握。
2. **前任 kill** — carryon が走り出し作業開始できると確認できたら、handoff の `predecessor` を `tmux kill-session` で掃除（idle 堆積防止 / 常時アクティブ 1・idle 高々 1）。
3. **自走** — carryon のデフォルト挙動を継承（subagent dispatch / 検証 / commit / push、オーケストレーター規律準拠）。
4. **refresh トリガ到達時**:
   - a. 未コミット成果を commit/push（tree をクリーンに = carryon の git-status 整合を保つ）。
   - b. 進捗台帳に「leg N で何をしたか + commit hash」を追記。
   - c. handoff スキルで relay ブロック込みの handoff.md を**上書き**（leg N+1、predecessor=自分、台帳更新）。
   - d. tmux-new の起動機構で fresh セッション `<goal>-r<N+1>` を起こし **`/relay`** を送る（`/carryon` でなく `/relay` = 連鎖を再武装）。
   - e. 後続の走り出しを capture-pane で確認したら**自 leg は idle 化**（以降ツール呼び出しをしない）。後続が step 2 で自分を kill する。
5. **完遂 / 停止条件到達時** — 連鎖を止め、handoff を `Relay: DONE/PAUSED/ABORTED + サマリ` に更新、PushNotification で通知。新セッションは起こさない。

## refresh トリガ（いつ次 leg へ渡すか）

3 シグナルの OR:

- (a) **context 圧迫の自己判断** — 会話が長大化し判断精度低下が懸念される（carryon 停止条件 3 と同じソフト信号）。
- (b) **malformed tool call interrupt** — 2 度目の malformed（CLAUDE.md interrupt trigger）。高 context の確信シグナルなので、relay モード下では『handoff + セッション終了してユーザーに promote』を『handoff + 次 leg 自動起動』に格上げ。
- (c) **leg あたりステップ予算（任意の backstop）** — ソフト信号が鈍い時の保険。

トリガ前に leg 内で完遂できれば relay を DONE で閉じる。

## 終了 & 暴走防止（最重要）

自己増殖ループなので hard guardrail を第一級に置く:

- **leg 上限** — 既定 8 leg（起動時に変更可）。到達で停止 → 通知 → ユーザー待ち。
- **無進捗検知** — 各 leg は進捗台帳に具体成果（新 commit / 完了タスク / 閉じた sorry 等）を記す。2 leg 連続で測定可能な進捗ゼロなら abort → 通知。
- **各 leg に最低 1 成果** — commit を残せないなら、なぜかを台帳に明示。
- **停止条件（carryon 由来 + 追加）**:
  1. **完遂** — ゴール / プラン目標を満たし残タスク無し → DONE。
  2. **要ユーザー判断** — 方針分岐 / 不可逆操作の承認 / 撤退ライン該当 → PAUSED（新 leg を起こさず通知）。fresh セッションに渡しても同じ所で詰まるので渡さない。
  3. **無進捗 / leg 上限** → ABORTED / PAUSED。

## セッション命名 & 前任掃除

- **名前**: `<goal>-r<N>`（短い英語ハイフン名 + leg 番号）。例 `footprint-r2`, `footprint-r3`。tmux 名 = claude 名（tmux-new 準拠）。
- **後続が前任を kill**（successor kills predecessor）— 親が子起動直後に親を殺すと、子起動失敗時に連鎖が死ぬ。なので「子が carryon で走り出し作業開始を確認してから親を kill」。常時アクティブ 1 + idle 高々 1。
- 親（現 leg）は子起動後**即 idle**（git 競合回避）。観察したいユーザーはリモートアプリで最新 `-r<N>` を選ぶだけ（切替不要、tmux-new 準拠）。

## handoff.md の relay 制御ブロック

handoff スキルの通常状態に加え、relay 専用セクション:

```
## Relay control
- Mode: ON | DONE | PAUSED | ABORTED
- Goal: <完遂すべきゴール（1 セッションでは収まらない単位）>
- Leg: N / cap K
- Predecessor: <session-name>     # 後続が起動確認後に kill
- Stop-on: completion | user-decision | no-progress×2 | leg-cap
- Progress ledger:
  - r1: <成果 / commit hash>
  - r2: <成果 / commit hash>
```

進捗台帳は (1) 無進捗検知の根拠、(2) ユーザーが連鎖を後追い監査する材料。

## 起動される側のブートストラップ

- spawn 時に送るのは **`/relay`**（`/carryon` でなく）。relay の step 1 が「carryon で状態復元」なので carryon 機能を内包しつつ連鎖を再武装する。
- relay は起動時に分岐:
  - handoff.md に `Relay: ON` の活きたブロックがあり、自セッションが fresh（作業履歴なし）→ **継続 leg** として carryon へ。
  - ユーザーが `/relay <タスク>` と明示引数で呼んだ → **初回 leg** として現セッションで直接着手（carryon 不要、relay ブロックを新規作成）。

## 既存スキルとの合成 / 必要な最小改修

- **handoff** — relay 制御ブロックを書けるよう軽微拡張（relay が内容を渡す形でも可）。
- **tmux-new** — 送信トリガを引数化（既定 `/carryon`、relay は `/relay`）。または relay が tmux-new の起動手順を踏襲して `/relay` を送ると記述。
- **carryon** — 変更不要（relay が内部で呼ぶ）。
- **CLAUDE.md の malformed interrupt** — relay モード時は『次 leg 自動起動』に振る舞いを差し替える旨を追記（相互参照）。

## 決定事項

1. **スキル名 = `relay`**（セッション間の baton pass）。
2. **自律レベル = 完遂まで完全自走** — 停止条件（完遂 / 要ユーザー判断 / 無進捗×2 / leg 上限）に当たるまで人を介さず連鎖。チェックポイント承認待ちは設けない。代わりに guardrail を厚くする（下記）。
3. **refresh トリガ = ハイブリッド** — context 圧迫の自己判断 + malformed interrupt（2 度目）+ 任意の step 予算 backstop の OR。
4. **leg 上限の既定 = 8**（`/relay <task> cap=N` 等で変更可）。

完全自走を選んだぶん暴走防止が生命線。leg 上限 8 + 無進捗検知（2 leg 連続で成果ゼロ → abort）+ 各 leg 最低 1 commit + 終端で必ず PushNotification、をハード制約として実装する。
