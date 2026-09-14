# 教科書サイトのホスト先を surge → Netlify に移す

**状態**: 計画（未着手）
**対象**: `docs/textbook/site/`（`build.mjs` / `deploy.sh` / `README.md`）と `CLAUDE.md` の「Textbook site deploy」節

## 現状

- ビルドは `deno run -A build.mjs` で `docs/textbook/site/dist/` に静的ファイル 124 個（HTML 101・woff2 21・CSS 1、計 25MB）を吐く。
- 公開は `deploy.sh` が surge CLI を expect で叩く。認証は `surge-credentials.txt`（**平文の email / password を public リポジトリにコミットしている**）。
- 公開先は `common2026-ch2.surge.sh`。この文字列を持っているのは `surge-credentials.txt` だけで、原稿・ビルドスクリプトはドメインを一切参照していない。
- `dist/` は git 管理外だが `.gitignore` にも入っていない（`dist/CNAME` は surge CLI が書き込む残骸）。
- リポジトリは public。GitHub Pages は `docs.yml` が API ドキュメントで既に使っているので、教科書サイトには使えない。

## Approach

**Netlify の Git 連携を使い、「ビルド済みファイルだけを載せた専用ブランチ」を Netlify の本番ブランチにする。** Netlify 側はビルドコマンド無し・公開ディレクトリ = ルートで、ブランチに push された中身をそのまま配信する。

- **ブランチは `site`（孤立ブランチ、常に 1 コミットに force-push）**。main の履歴とは合流させない。毎回 25MB を積み上げると public リポジトリの clone が重くなるので、履歴は残さず毎回作り直す。
- **`deploy.sh` の役目は変えない**（build → 公開）。中身を surge CLI から「一時ディレクトリで `git init` → dist をコミット → `git push --force origin site`」に差し替えるだけにする。`CLAUDE.md` の「原稿を直したら `deploy.sh` を走らせる」という運用も、README の位置づけもそのまま維持される。
- **認証情報が要らなくなる**。push は既存の SSH 鍵で通るので、`surge-credentials.txt` は削除できる。この移行のいちばん大きい利得はここ。
- **一時 clone 方式を採るのは、作業ツリーを汚さないため**。`git worktree add --orphan` はこのマシンの git 2.39 には無い（2.42 以降）。使い捨てリポジトリから force-push すれば、main のインデックスにも `.git/index.lock` にも触れない。

## そちら（Claude）で進めること

1. `.gitignore` に `/docs/textbook/site/dist/` を追加（`dist` を誤って main にコミットしないため）。
2. `deploy.sh` を書き換え。build（現状のまま）→ 一時ディレクトリに `dist/` をコピー → `git init` → 1 コミット → `git push --force origin HEAD:site`。末尾に公開 URL を出す。
3. 空でない `site` ブランチを初回 push しておく（**Netlify の UI はブランチが存在しないと選択肢に出ない**ので、人間の設定より先に済ませる必要がある）。
4. `surge-credentials.txt` を削除、`deploy.sh` から expect / surge の経路を削除。
5. `docs/textbook/site/README.md` の更新（タイトル・デプロイ節・「どこに何があるか」表の「公開先ドメインと認証情報」行）。
6. `CLAUDE.md`「Textbook site deploy」節の更新（surge の transient error に関する 1 行を削除、公開の仕組みを Netlify に）。
7. （人間の設定が済んだあと）実際に `deploy.sh` を走らせて、Netlify 上で全 101 ページと数式フォントが出ることを確認。

## 人間の手でやること（Netlify の UI）

**3 が終わってから着手する。** ブランチが無いと 3 番目の手順で詰まる。

1. Netlify にサインアップ / ログインする（GitHub アカウントでのログインが楽）。
2. Add new site → Import an existing project → GitHub → Netlify の GitHub App に `FujiHaruka/information-theory` へのアクセスを許可する。
3. ビルド設定を次のようにする。
   - Branch to deploy: `site`
   - Build command: **空**
   - Publish directory: `.`（ルート。空欄でも同じ）
   - Base directory: 空
4. サイト名（`https://<名前>.netlify.app` の `<名前>`）を決める。Site configuration → Site details → Change site name。決めたら教えてほしい（README に書く）。
5. 独自ドメインを当てたいなら Domain management で設定する（任意。当てないなら `.netlify.app` のままでよい）。
6. **surge のパスワードを変更するか、surge アカウントを捨てる。** 平文パスワードを public リポジトリにコミットしてあり、ファイルを消しても git の履歴には残る。移行後に surge を使わなくなっても、この 1 手だけは残る。
7. （任意）surge 側のサイトを畳む。`deno run -A npm:surge teardown common2026-ch2.surge.sh` はこちらでも実行できるので、畳んでよければ言ってほしい。

## 決めてもらう必要があるもの

- **サイト名**（上の 4）。これだけは Netlify の UI でしか決まらない。README への反映は名前が決まってからで、移行そのものはブロックしない。

## 補足（この計画では採らなかった選択肢）

- **Netlify にビルドさせる**（main を本番ブランチにして、Netlify 上で `deno run -A build.mjs` を走らせる）。ビルド環境に Deno を入れる手間と、ビルド時にフォントを外部から取りに行く不確実さが増える。「ビルド済みを push したらそのまま公開」という要望とも違う。
- **サイト用に別リポジトリを立てる**。本体リポジトリの clone サイズは増えないが、リポジトリが 2 つになる。25MB（圧縮後はその数分の 1）を 1 コミットぶんだけ持つ形なら本体に同居させても許容範囲と判断した。
- **GitHub Actions で main への push から自動デプロイ**。今の運用（原稿を直したら `deploy.sh`）を変えないことを優先した。あとから足せる。
