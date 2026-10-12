# 教科書サイト Netlify → Cloudflare Pages 移行手順

## 現状

- `docs/textbook/site/deploy.sh` が `dist/` を孤立ブランチ `site` に force-push し、Netlify がそのブランチを
  「ビルドコマンド無し・公開ディレクトリ = ルート」で配信している。デプロイ専用の資格情報は無い。
- 公開 URL は `https://info-theory.fuji.land`。`fuji.land` の DNS は Route 53 にあり、`info-theory` は
  `info-theory.netlify.app.` への CNAME。
- `dist/` は 122 ファイル・約 30MB、最大ファイル約 700KB。`_redirects` / `_headers` は使っていないので、
  Netlify 固有設定の翻訳は要らない。
- Hypothesis のレビュー注釈はページの URL に紐づいている（`feedback.ts` の集計は `.html` の有無を吸収する）。

## Approach

**Cloudflare Pages の Git 連携で `site` ブランチをそのまま配信し、Route 53 の CNAME を張り替える。**
`deploy.sh` のロジックは変えない。変わるのは「`site` ブランチを見ているホスティング」と CNAME の向き先だけ。

- Pages を選ぶ理由：サブドメインなら DNS を Route 53 に置いたまま CNAME で独自ドメインを付けられる。
  Workers の独自ドメインは `fuji.land` のゾーンごと Cloudflare へ移す必要があり、他のレコードにも波及する。
- Direct Upload（`deno run -A npm:wrangler pages deploy dist`）は `site` ブランチの 25MB force-push を
  無くせるが、API トークンを手元に置くことになり、資格情報なしという現行設計を崩すので採らない。
- 既知の差分：Pages は `/ch01-01.html` を `/ch01-01` へリダイレクトし、これは設定で切れない。
  サイト内リンクはリダイレクト 1 回で通る。影響するのは既存の Hypothesis 注釈の表示だけで、
  切替後に実際に確かめてから対処を決める（手順 5）。

凡例：**[手動]** = Cloudflare ダッシュボード / Route 53 で人が操作、**[自動]** = リポジトリの編集。

## 手順

### 0. 事前準備 [手動]

1. Route 53 で `info-theory.fuji.land` の CNAME の TTL を 60 秒に下げる（切替の 1 日前まで。元の TTL を控える）。
2. Cloudflare アカウントを用意する（無料プランで足りる：25MiB/ファイル、20,000 ファイル/サイト）。

### 1. Pages プロジェクトを作る [手動]

1. Workers & Pages → Create → Pages → Connect to Git → GitHub で `FujiHaruka/information-theory` を許可して選ぶ。
2. 設定：
   - Project name：`info-theory`（取られていれば別名。以下 `<project>.pages.dev` と書く）
   - Production branch：`site`
   - Framework preset：None、Build command：空、Build output directory：`/`
3. 作成後、Settings → Builds → Branch control の **Preview branch control を None** にする。
   既定の「全ブランチ」のままだと、`main` に push するたびに Lean リポジトリ全体を clone するプレビュービルドが走る。
4. 初回デプロイが終わったら `https://<project>.pages.dev/` を開き、目次・数式・図・フォント（`/fonts/` 配下）・
   ページ間リンク・ダークモード切替が Netlify 版と同じに見えることを確かめる。

### 2. 独自ドメインを Pages に登録する [手動]

1. Pages プロジェクト → Custom domains → Set up a domain → `info-theory.fuji.land`。
2. 「外部 DNS で CNAME を設定せよ」と出る（ステータスは保留）。**この登録を CNAME 変更より先に行う。**
   逆順だと 522 エラーになる。

### 3. CNAME を張り替える [手動]

1. Route 53 で `info-theory.fuji.land` の CNAME を `info-theory.netlify.app.` → `<project>.pages.dev.` に変更。
2. Pages の Custom domains で Active になり、証明書が発行されるまで待つ（通常数分〜数十分）。

### 4. 動作確認 [手動 / 自動]

```bash
dig +short info-theory.fuji.land                       # <project>.pages.dev を指す
curl -sI https://info-theory.fuji.land/ | head -5        # 200、server: cloudflare
curl -sI https://info-theory.fuji.land/ch01-01.html      # 308 → /ch01-01
curl -sI https://info-theory.fuji.land/fonts/            # フォント配下が配信される（個別ファイルで確認）
```

ブラウザで、節内アンカー付きのリンク（`…#thm-1.1.5`）がリダイレクト後もその位置へ飛ぶことを確かめる。

### 5. Hypothesis 注釈の確認 [手動 → 必要なら自動]

1. 既存の注釈があるページを `?review=1` 付きで開き、注釈が本文上に表示されるか見る。
2. 表示されれば何もしない。`./feedback.ts` で注釈が集まることも確かめる。
3. 表示されない場合の対処候補（この時点でどちらにするか決める）：
   - `build.mjs` が各ページに `.html` 付き URL の `<link rel="canonical">` を出す（注釈の URL 同一視に使われる）。
   - サイト内リンクを拡張子なしで出力する（リダイレクトも消える。`check-links.ts` の対応が要る）。

### 6. Netlify を外す [手動]

手順 4・5 が通ってから行う。**ここまではいつでも CNAME を `info-theory.netlify.app.` に戻せば元に戻る**
（ただし戻したあと再度 Pages に向けると、独自ドメインが再有効化されるまでしばらくエラーになる）。

1. Netlify の Domain management から `info-theory.fuji.land` を外す。
2. 数日問題がなければ Netlify のサイトを削除する。
3. Route 53 の TTL を元に戻す。

### 7. リポジトリの記述を更新する [自動]

`deploy.sh` のロジックと `SITE_URL` は変えない。Netlify と書いている箇所だけを直す。

- `docs/textbook/site/deploy.sh` の冒頭コメント（Netlify → Cloudflare Pages、Preview branch control = None の理由）
- `docs/textbook/site/README.md` の見出しと「公開の仕組み」節（設定は Cloudflare ダッシュボードが持つ、の旨）
- `CLAUDE.md` の「Textbook site deploy」節の Netlify への言及
- 手順 5 で対処が要った場合はその変更

移行が完了したらこのファイルを削除する（履歴は git が持つ）。
