# ARS #431 — 「拿掉 strength-2 author-agree 單獨 accept」連鎖影響 + 可行性評估

**日期：** 2026-06-13
**目的：** 第四輪 codex re-verify 判定「三個結構 veto 是 whack-a-mole，真正缺陷是 strength-2 `author_state==agree` 單獨能 accept 非 exact 標題」。拍板前先把連鎖影響與可行性查實（回第一手程式碼，非推測）。
**結論先講：** 「更強 bibliographic 鑑別」在四 client 現況**不對稱可得**，s2 甚至連 candidate metadata 都丟掉。所以乾淨的根治方案是 **A 案（exact-title-or-bust）**，不是 codex 建議的「venue+volume+issue+page 唯一化」（後者三家拿不到，會變成只有 crossref 能做的跛腳 gate）。recall 損失比想像小（見 §3）。

---

## 1. 真正的缺陷（第四輪確認，我復現成立）

strength-2 的這兩條：
```
accept if author_state == agree                       # strength 2
accept if year_state == agree AND author_state == agree   # strength 2
```
讓「**非 exact 標題 + 同作者 + 同年/不衝突 + ratio≥0.70**」單獨過關。但這個特徵正是**一個作者自己的關聯著作群**的共同特徵：
- correction ↔ original（P1-a，反向）
- reply/comment ↔ original（P1-c）
- Part I ↔ Part II（P1-d）
- **Study 1 ↔ Study 2 / First ↔ Second Report / Theory ↔ Experiments companion（第四輪新增，全 evade 我的三 veto）**

復現 ratio（本機 SequenceMatcher）：Study 1/2 = **0.975**、First/Second Report = 0.901、Theory/Experiments = 0.878、Authors' reply = 0.897。全 ≥0.70，全同作者同年，全 strength-2 accept → 誤 `matched`。

用「同作者」當身分證據，對這整類**反向失效**：同作者是這些 distinct works 的共同點，不是區分點。再加 enumerated veto（study/report/experiment/...）永遠補不完——這就是 whack-a-mole 的定義，已四輪實證。

## 2. 為何「補洞」路線必須放棄

我連續四輪都在加 veto / 加 denylist 條目，codex 每輪找到清單外的下一個：
- R1→v2：notice veto（單邊）
- R2→v3：year-only 收緊
- R3→v4：notice 對稱 + reply wrapper + designator veto + generic denylist
- **R4：Study/Report/companion evade designator；guest editorial evade denylist；我的 non- fold 反噬把 `Non-invasive` vs `Invasive` 真矛盾洗成 match**

最後一個尤其是教訓：**我為了消假 veto（P2-e）動 negation 邏輯，反而引入新 false-positive**（[[feedback_simplify_reviewer_careful_removing_safety]] 活案例）。補洞路線不只補不完，還會自傷。

## 3. 根治方案的可行性 — candidate-side 到底拿得到什麼鑑別證據？

codex 建議「require DOI/ID, venue+volume+issue+page/article-number」。**但這在四 client 不對稱可得**（第一手讀 code）：

| client | title_search return | candidate metadata resolver 拿得到 | volume/issue/page |
|---|---|---|---|
| crossref | `scored[0][0]` = 完整 Crossref work item | title/year/author（現抽）；**DOI/volume/issue/page/container 在 item 內、可加抽** | ✓ 可得（需加 `_extract`） |
| openalex | `scored[0][0]` = work dict | title/year/author/**DOI**/primary_location(venue)；select=`id,title,authorships,publication_year,doi,primary_location` | ✗ 沒 select（要改 query） |
| arxiv | (待確認，XML entry) | title/year/author；arXiv **沒有** volume/issue/page 概念（preprint） | ✗ 本質不存在 |
| **s2** | **`{"matched", "paperId"}`** — **candidate dict 丟掉** | **連 year/author 都拿不到**（loop 內有 `cand`，但 return 不帶出） | ✗ 且要大改 return 型別 |

**關鍵事實：**
1. **s2 現在連 candidate 的 year/author 都沒回給 resolver**（只回 matched+paperId）。spec §0.4 的 strength tiers 要在 s2 生效，本來就得先改 s2 的 return 把 candidate metadata 帶出來——這筆改動 spec 已隱含要做。但要它再帶 venue/volume 是更大改動。
2. **volume/issue/page 只有 crossref 拿得到**（且要加抽）。openalex 要改 query select、arxiv 本質沒有、s2 要大改。所以「venue+volume+issue+page 唯一化」會變成**只有 crossref 能執行的 gate**，另三家照樣只能靠 title+author+year → 跛腳，等於沒根治。

**∴ codex 的 minimal fix（volume/issue/page 唯一化）在這個 4-client 拓樸下不可行為通用方案。** 真正通用、四家都能執行的根治只有一個共同點：**exact normalized title**（strength 3，四家都算得出 ratio==1.0 / normalized 相等）。

## 4. 兩個可行的根治方向（都通用於四 client）

### A 案：exact-title-or-bust（純收緊，最乾淨）
非 exact 標題的 title-fallback **一律不靠 author/year 單獨 accept**——要 matched 必須 exact normalized title（strength 3），否則 `unresolvable`。
```
reject if ratio < 0.70
reject if year_state==conflict OR author_state==conflict
accept if exact_normalized_title AND NOT generic_title_collision_risk   # 見下
reject otherwise   # 非 exact 一律 unresolvable（含同作者同年）
```
- **消掉**：P1-a/c/d + 第四輪 Study/Report/companion **整類**（它們全是非 exact）→ 不需要 §0.3 item-4 三個結構 veto，**直接刪掉那層**（簡化，非加層）。
- **generic-title（P1-b）**：exact 但低資訊。改用「generic head 命中 → 即使 exact 也要 DOI/ID 命中才算，否則 unresolvable」。這對 generic 是對的（generic 連 exact 都不足以證身分）。
- **代價（recall）**：合法的「短名引用同作者真論文」非 exact 者 → unresolvable。**但這代價比想像小**，見 §5。
- notice/reply/designator veto **全部不需要**（非 exact 自動不過）→ 連同我寫的 §0.11.1 整段可刪。**Fix C（non- fold）也不需要**（negation veto 整個在非 exact 才有意義，但非 exact 反正 unresolvable）→ 反噬問題消失。

### B 案：保留 author-agree 但加「結構差異 = 降級」總則（仍有 whack-a-mole 殘餘）
保留 strength-2，但定義一個**通用** structural-delta 偵測（不是 enumerate 字詞）：若兩個非 exact 標題的 principal delta 是「**任何**位置的數字/序數/timepoint token 差異」或「一側是另一側的 wrapper」，則 author-agree 不足、要 exact 或 DOI。
- 比 A 案保留更多 recall（同作者非序號類關聯著作仍可能 match）。
- **但**「principal delta 是序數/timepoint」這個偵測本身仍是啟發式，codex 第五輪很可能再找到不靠序數的 companion（如 `: Theory` vs `: Experiments` 根本沒數字）→ whack-a-mole 沒真正結束。§3 的 Theory/Experiments 案例（0.878）就是 B 案也擋不乾淨的證據。

## 5. A 案的 recall 代價 — 實際多大？

關鍵問題：合法的「**非 exact** 標題 + 同作者真論文」在真實 citation 語料多常見？分三種：

1. **短名引用（BERT 類）**：cited=`BERT` vs indexed=`BERT: Pre-training of Deep Bidirectional Transformers`。這是 spec 行671 的正向驗收案例。**但**——這類**幾乎都有 arXiv ID 或 DOI**（BERT = arXiv:1810.04805）。title-fallback 只在 **ID 查找先 miss** 才觸發。一篇有名到被短名引用的論文，ID 查找 miss 的機率低。所以「短名引用 + 無 ID + 靠 title-fallback」的交集，比「短名引用」本身小一個量級。
2. **標題輕微變體（標點/副標題差異）**：這些 normalized 後**常常就 exact 了**（normalization 已收標點/大小寫）→ 走 strength-3，不受影響。
3. **真正非 exact 且無 ID 且同作者**：剩下的才是 A 案的損失。這類與「同作者關聯相異著作」**在 title 層無法區分**（正是 §2 的根本困境）——所以把它們一起判 unresolvable，是 title-only fallback 層**本質做不到的區分**，unresolvable（safe direction）是誠實答案，不是過度保守。

**∴ A 案的真實 recall 損失 ≈「短名引用 ∩ 無 ID ∩ 非 exact」**，是個小交集；且損失全在 safe direction（unresolvable，非 false）。換來消滅整類 dangerous false-positive（同作者關聯著作誤併）。這個取捨對一個**引用真實性驗證工具**是對的：它的核心承諾是「不把相異著作判為同一」，寧可 unresolvable 不可 false matched。

## 6. 我的建議

**A 案。** 理由：
1. 唯一**通用於四 client**的根治（exact-title 四家都算得出；volume/issue/page 只 crossref 有）。
2. **簡化而非加層**：刪掉 §0.11.1 三個結構 veto + Fix C，strength tier 變兩條（exact-title / generic-needs-ID）。code 改動更小、更好驗。
3. 消滅**整類** same-author related-work false-positive（含所有 codex 未枚舉到的），不再 whack-a-mole。
4. recall 損失是小交集且 safe direction（§5）。
5. 符合工具核心承諾與 LLM-defect-class posture（mitigate by narrowing the claim，[[feedback_llm_defect_class_problems_may_have_no_current_fix]]）。

**代價要誠實寫進 spec**：BERT 類短名引用若無 ID 且非 exact → unresolvable（recall 降，acknowledged，safe direction）。spec 行671 的正向驗收案例要改述：BERT 短名**靠 ID 命中** matched（本來就該如此），不靠 title-fallback 的 author-agree。

**下一步**：A 案改完 spec（§0.12 v5，刪 §0.11.1 + 改 §0.4 strength tier）→ 第五輪 codex re-verify（這次攻面小很多：只剩 exact-title strength-3 + generic-needs-ID 兩條）→ 0 P1 進 code。

## 7. 若你選 B 案 / 撤退威脅本身
- **B 案**：我會定義通用 structural-delta 降級則，但**預告**第五輪 codex 很可能再破無序號 companion（§3 Theory/Experiments 已是證據），可能要再一輪。保留 recall 的代價是收斂更慢、殘餘風險高。
- **撤退威脅（記 known-limit）**：把「同作者同年關聯著作」整類記為 title-only fallback 層不可靠區分的 known-limit。但這**不可接受地留 dangerous direction 開著**（distinct→matched），與工具核心承諾衝突——除非同時拿掉 author-agree 把 dangerous 部分擋掉（那其實就回到 A 案）。所以純記 known-limit 不擋 dangerous 的版本我不建議。
