# ARS 資深研究者視角盲點盤點

| | |
|---|---|
| 日期 | 2026-06-10 |
| 基準 | main `6252b1b`（v3.12.0 + Item 7 spec） |
| 性質 | 產品級審查：這套工具拿來產真論文，缺什麼、擋什麼、騙了自己什麼 |
| 研究者畫像 | 高教品保領域、systematic review／政策研究、中英雙語投稿、單人為主偶有共作 |
| 外部輸入 | AACSB Global Research Impact Task Force, *A Framework for Research Impact* (May 2026) |
| 審查軌跡 | 初稿 → 主 context 自查（3 修正）→ codex 0.137 high + gemini-3.1-pro dual-track（11+7 findings）→ 本版 |
| 狀態 | 待使用者裁定；裁定前不開 issues |

分類標記：**【盲點】**初衷內該有而沒有／**【增補】**初衷外但高價值，附說服理由／**【non-goal】**誠實列出為什麼不做。撞已拍板 negative scope 的提案，明寫要求推翻哪條決策。

---

## 0. 一句話結論

ARS 是一台「文獻→寫作→審查→修訂」中段防錯密度極高的單篇論文品管機；它最大的結構性問題不在中段（中段是強項），而在三處：**(1) 跨篇 research program 層級的 state 為零**，每篇論文都從失憶開始（是盲點還是 scope 外，送裁定）；**(2) 品質機制全部回答「這篇有沒有錯」，沒有任何機制讓「這篇無懈可擊但平庸」變得可見**；**(3) 工具的旗艦防線（deterministic citation verification）在使用者自己的研究類型（政策研究、灰色文獻為主）上覆蓋率系統性最低**。

Dual-track 補了第四條：本盤點初稿自己也犯了「AI 對自寫物 anchoring」的錯——兩個提案（F-4、F-5 之半）提的是 repo 已存在的東西，一個提案（F-2 novelty mirror）原始形狀踩了 hidden-ranking 紅線。修訂記錄保留在各節，因為這些誤判本身就是「為什麼這個 repo 需要 cross-model 審」的現場證據。

---

## 1. 研究生命週期走查

生命週期：**grant/計畫申請** → RQ 孵化 → 文獻 → 方法設計 → 實驗/資料 → 分析 → 寫作 → 內部審查/修改 → 投稿 → rebuttal → camera-ready → 發表後 → 下一篇。（grant 段是 gemini 審查補上的，初稿漏列，見 F-13。）

| 階段 | 覆蓋 | 深度 | 判定 |
|---|---|---|---|
| grant/計畫申請 | funding_statement_guide（formatter reference）為止 | 近零 | **未拍板留白**：F-13 |
| RQ 孵化 | deep-research `socratic`（5-layer）+ FINER guidance-tool 對話 + #257 wording advisory | 完整對話工作流；Layer 1/5 已含 impact 探問（dual-track 修正，見 F-4 撤回紀錄） | 蓋到 |
| 文獻搜尋/篩選 | `lit-review` / `systematic-review`（PRISMA）+ literature_corpus + 四索引 citation gate | 全 suite 最厚 | 蓋到；灰色文獻低覆蓋（F-3） |
| 方法設計 | research_architect（Methodology Blueprint）；preregistration 僅 reference | Blueprint 為止 | 蓋到 |
| 實驗/資料蒐集 | 無。#260 只做 scholar 宣告的 provenance intake | 僅 intake/audit | **non-goal（正確）**：Kong §3.3 rejected；companion experiment-agent 接手 |
| 分析 | synthesis（文獻層）+ meta_analysis（SR）+ figure fidelity gate #261 | 文獻層完整；primary data 分析無 | non-goal（experiment-agent 領地），邊界清楚 |
| 寫作 | academic-paper 10 modes、12 agents、style calibration、anti-leakage | 完整 | 蓋到 |
| 內部審查/修改 | reviewer 6 modes + in-pair evaluator + R&R traceability + revision/revision-coach | 全 suite 最厚 | 蓋到；「建設 vs 防禦」失衡（F-2） |
| 投稿 | formatter：cover letter、CRediT 14 角色模板、DAS 四模板、COI/funding/ethics、雙盲版去作者資訊、Pre-Output Final Checklist（皆 prompt 層）；disclosure mode；journal_submission_guide（含 TSSCI 節） | **prompt 層 checklist 完整**（初稿低估，codex 修正）；deterministic 驗證零 | F-5 改寫後仍立案：gap 是 deterministic 化不是從無到有 |
| rebuttal/response | `revision`（point-by-point R&R）+ `revision-coach`（Response Letter Skeleton）吃外部審稿意見 | 完整工作流 | 蓋到 |
| camera-ready | format-convert（LaTeX/DOCX/PDF）為止 | 排版機械層 | 蓋到 |
| 發表後 | monitoring_agent（optional：retraction/correction alert、contradictory findings、author tracking）+ literature_monitoring_strategies（citation alert 指南） | advisory 指南層，非主流程（初稿寫「全空白」過度，codex 修正） | 殘餘 gap 窄而明確：F-7 |
| 下一篇（research program） | 無任何機制 | 零 | **F-1**：事實成立，分類送裁 |

走查結論：中段密度世界級。前端薄是 deliberate（實驗外包、idea generation 是 Kong L2 紅線）。**grant 段與「發表後+下一篇」段是未經裁定的留白**——沒有任何 design lesson 記錄過為什麼不做，跟五條 Rejected mechanisms 的待遇不對等。這是本盤點送裁定的核心。

---

## 2. 發現總表（dual-track 修訂後）

| # | 發現 | 分類 | 狀態 |
|---|---|---|---|
| F-1 | 跨篇 research program state 為零 | 增補（scope 裁定）；初稿標盲點，codex 論證 POSITIONING 寫的是 research-to-publication 不含 program 管理，降級 | 送裁 §3 |
| F-2 | 品質機制無「平庸可見性」 | 盲點 | 立案 §4；形狀 2 經 codex 抓出紅線問題後重設計 |
| F-3 | 灰色文獻在四索引 citation gate 下系統性低覆蓋（初稿「全部查無」過度，已軟化） | 盲點 | 立案 §6.2 |
| F-4 | ~~RQ 孵化缺 impact-pathway 探問~~ | **撤回** | §5.1 保留撤回紀錄：提案內容已存在於 socratic Layer 1/5 |
| F-5 | submission package 檢查的 deterministic 化（初稿「無此功能」錯；prompt 層 checklist 已完整） | 增補 | 改寫後立案 §5.2 |
| F-6 | venue selection 無支援 | 增補（撞線） | §5.3；dual-track 後條件收窄為 scholar-supplied candidate universe |
| F-7 | 發表後段殘餘 gap：自我論文的 citation-context audit、errata workflow、OA self-archiving 合規 | 增補（要動 POSITIONING scope） | 改寫後立案 §5.4 |
| F-8 | env flag 無單一總表（7 個 user flag，SETUP.md env 表列 5）；安全功能全 opt-in 預設關 | 盲點 | 立案 §7.1（數字經自查修正，codex 同向確認） |
| F-9 | Dogfooding 半斷流：worked example 停在 v2.7；v3.8 之後版本全為外部論文驅動（初稿「v3.4 之後全論文驅動、真實使用零痕跡」錯——v3.6.7 即 chapter-run 驅動且有 spec 記錄） | 盲點（窗口收窄後仍成立） | 立案 §7.2 |
| F-10 | 中文線止於排版：TSSCI 檢索/引用/字體有，中文審查慣例與投稿 workflow 無 | 增補 | 立案 §6.1 |
| F-11 | Multi-author：team_collaboration_protocol.md 已有 human-convention 層（初稿「零支援」錯）；passport 層 multi-author state 為零 | non-goal 維持 | §8 |
| F-12 | plain-language summary / 衍生物 | non-goal 維持（撞 Paper2X），理由 §8 | — |
| F-13 | grant/funding lifecycle 整段不在走查與產品內（gemini 補抓） | 增補（scope 裁定） | §5.5 |
| F-14 | bonus hygiene：Originality 權重 repo 內部不一致（quality_rubrics.md 20% vs review_criteria_framework.md 15%，codex 抓） | 盲點（小） | 順手修，可直接開 issue |

---

## 3. F-1 跨篇知識累積：research program 層級失憶【增補，scope 裁定】

### 事實（未被任何審查挑戰）

所有跨 session 機制都是**單篇內**的：Material Passport 是 per-run state；`resume_from_passport` 續同一 run；`compliance_history[]`、`reset_boundary[]`、`experiment_provenance[]` 都掛在單篇 passport 上。唯二跨篇的東西：verification cache（引用查核的效能快取）、`literature_corpus[]`（使用者外部維護重餵，No corpus mutation Iron Rule 明文不回寫）。

真實研究者的工作單位是研究線不是論文：同批文獻寫三篇、上一篇的 limitations 是下一篇的 RQ 種子、上一篇被 reviewer 打過的弱點下一篇先補、paper A 主張過 X 則 paper B 不能無意識主張 ¬X。ARS 自己的機制已經在單篇內生產這些資產（Stage 6 AI Self-Reflection、Acknowledged Limitations、R&R Traceability Matrix），但 run 結束即死。

### 分類修訂（codex P1）

初稿標【盲點】，論證是「copilot 服務 scholar，scholar 的存在形式是研究線」。codex 反駁：POSITIONING 的自我定義是 "full research-to-publication pipeline"——publication 是終點，research program 管理是擴張解釋。我接受：**這是 scope 決定不是落在既有 scope 內的漏洞**，改標【增補】，裁定權在使用者。AACSB spiral model（outcome 回饋下一輪 inquiry）是擴的理由，不是已承諾的依據。

### 紅線檢查（dual-track 後收緊）

「上一篇 limitation → 下一篇 RQ」做成 ARS 主動提案 = 撞 Kong L2。codex 進一步指出：L2 的 verb test 允許的是「對 scholar-supplied RQ 的 wording advisory」，**pre-RQ 階段 surface 上篇 limitations 並不在 L2 的明文允許清單內**，屬於 L2 沒有預想過的新 seam。合規形狀因此要滿足三個條件（codex 修訂）：

1. **Scholar-initiated**：scholar 明示「載入我的研究線」才啟動，不是新 run 自動跳出。
2. **All-artifacts-visible**：呈現該研究線的全部 prior limitations / 未解意見，不做「最相關的三條」這種隱性篩選（同 hidden-ranking 原則）。
3. **不 derive**：呈現原文 + Socratic 問句為止，不從 limitation 推導、改寫或排序候選 RQ。

跨篇 claim 一致性檢查（自我前作的 claim registry 對照）是 audit 不是 generation，#262 機制形狀可複用，紅線風險低。

### 與 data layer boundary 的關係（送裁）

2026-04-22 的禁令擋的是「整合外部 corpus」；research-line ledger 承接的是 **ARS 自產 artifacts**（passport、reflection、R&R matrix——格式 ARS 定義、內容 ARS 產出）。我判斷不在禁令射程內，但邊界是使用者拍的板。

### 裁定問題

要不要開「research line passport」設計線？最小切片：①scholar-initiated 的 prior-limitations advisory surface（上述三條件）；②自我 claim registry 的 cross-paper audit。若裁定不做，建議把「research program 層」明文寫進 POSITIONING non-goal——現在它是留白，跟五條 Rejected mechanisms 的記錄紀律不對等。

---

## 4. F-2 防禦性品質 vs 建設性品質：「無懈可擊但平庸」會全綠通過【盲點】

### 事實

防錯側：DA 3 mandatory checkpoints、Stage 2.5/4.5 integrity（zero issues 才放行）、7-mode failure checklist（no escape hatch）、generator-evaluator contract、sprint contract、citation gate、claim audit、49 條 lint。防的全是 hallucination / drift / corruption / sycophancy。

提質側：理論貢獻與論證銳度只出現在**評分側**（EIC/peer review 的 Originality 加權——主 rubric 20%，舊 reference 殘留 15%，見 F-14）與**防守側**（DA So-what test、CER stress test）。寫作期/修訂期的 coaching 全面降維到流程與排序（「選三件事改」「排優先序」）。Socratic 的深度集中在 RQ 期（5-layer 含 assumption probing 與 significance），**不延伸進寫作期**：沒有任何 mode 在 drafting/revision 階段陪 scholar 磨「這篇對哪條理論線的推進點、跟哪個學派對話、delta 在哪」。

結構性後果：一篇文獻完備、引用全驗證、統計無誤、論證結構完整、回應了所有模擬審稿意見的論文，可以全閘綠燈通過——而它可能是 AACSB p.13 受訪者批評的 "micro extensions of what we already know"。reviewer panel 忠實模擬現行 journal review 體制，等於把該體制推向保守增量的力場也內建了。25 modes 的 spectrum 分布（14 Fidelity / 7 Balanced / 4 Originality）顯示系統重心本來就在 fidelity。

### 與 S0 洞見的鏡像關係

HEEACT 評鑑工具加 S0 的原因是「AI 把報告寫到無懈可擊 = 品質訊號失效」。ARS 站在生產端，正是那台把論文寫到無懈可擊的機器。評鑑端已知 compliance ≠ perfection；生產端還沒有對應自覺。解法不是讓 ARS 學會判斷論文價值（LLM 判 novelty 不可靠，v3.0 自承 DA "attacks arguments, never premises"），是讓**平庸這個屬性變得可見**，判斷留給 scholar。

### 修補形狀（dual-track 後修訂）

1. **Contribution sharpening 對話層**【維持】：把 socratic Layer 5（SIGNIFICANCE & CONTRIBUTION，已存在於 RQ 期）的問句結構**延伸進 plan mode 與 revision coaching**（"十年後引用本文的人會說它證明了什麼？" "拿掉本文，這條文獻線少了哪塊？"）。改動小：plan_mode_protocol 與 Phase 2.5 coaching 各加一節，問句直接從 socratic_mentor_agent Layer 5 移植。過 L2（問不給）。
2. **Novelty delta 鏡子**【初稿形狀踩線，重設計】：初稿提「本文 claim ↔ 三篇最近鄰文獻」對照表。**codex 抓出紅線問題：「選哪三篇」本身就是 hidden selection pressure，Co-Scientist L1 管的是候選集隱性建構與 anchoring，不是最後有沒有寫「你決定」**。重設計後的合規形狀：對照集由 scholar 指定（"跟這五篇比"），或 enumerate 全部 bibliography 中標記為 same-RQ 的 entries（全集可見、不選樣）。成本變高，價值降低；**優先級降到形狀 1 之後**，甚至可以不做。
3. **Practitioner/policy-reader persona**【維持，誠實標注】：field_analyst 動態配 reviewer 機制現成，加一個非學術讀者 persona。LLM 模擬 practitioner 仍是 LLM，價值是視角多樣性不是真 stakeholder。

教訓記錄：「advisory ≠ 自動紅線安全」。本盤點初稿把 advisory 當免死金牌用了一次，被兩個模型從不同條目（F-2、F-6）獨立抓到同一原則。這條應該寫進未來所有 ARS 提案的 review 慣例：**檢查紅線時，先檢查候選集是怎麼建構的，再檢查最後誰決定**。

### 裁定問題

推薦先做形狀 1（最便宜、問句現成、最貼 Socratic DNA）。形狀 2 重設計後還值不值得做，送裁。

---

## 5. 生命週期斷點的修補提案

### 5.1 F-4 撤回紀錄：impact-pathway 探問已存在

初稿提案「socratic 加 impact-pathway 探問維度」。**Dual-track 兩模型一致打掉前提**：`socratic_mentor_agent.md` Layer 1 已有 "If your research succeeds, how would the world be different?" / "Important to whom?"，Layer 5（SIGNIFICANCE & CONTRIBUTION）已有 "If your research succeeds, who would make different decisions as a result?" / "Who benefits once it's filled?"；`research_question_agent.md` 明寫 FINER 是 "guidance tool (not a scoring tool): Designs 2-3 guiding questions for each FINER dimension"。我提案要加的問題逐字級地已經存在。

誤判根因：subagent 地圖只讀了 SKILL.md 層（拿到 5-layer 的名字沒拿到 agent prompt 的問句），主 context 自查的 grep 關鍵詞（stakeholder / impact pathway / who will use）漏掉了實際表述（how would the world be different / who would make different decisions）。關鍵詞錨定偏誤 + 對自寫提案的 anchoring，雙重失效；同 model 的獨立 context（codex prompt 內含維度提示）反而抓到。

殘餘 gap 只剩一條小的：Layer 5 的探問停在「誰會不同」，沒有「發表載體通路」的具體化（學術期刊 vs 評鑑準則 vs 政策白皮書——對政策研究者這是 RQ 期就該想的 dissemination 路徑）。價值低，不獨立立案，併入 F-2 形狀 1 的問句清單即可。

### 5.2 F-5 submission package 的 deterministic 化【增補，改寫後立案】

初稿宣稱「submission package 完整性檢查無」。**codex 修正：formatter_agent prompt 層已有完整 checklist**——雙盲版去作者資訊（:673）、CRediT 14 角色模板、DAS 四模板、COI/funding/ethics statement、Pre-Output Final Checklist（內容完整性+格式合規+必要元素+投稿包四節，any FAIL → fix and re-check）。

改寫後的真 gap：**這些全是 prompt 層 checklist（LLM 自我核對），零 deterministic 驗證**。對照 ARS 自己的演進邏輯——citation 從 prompt 層防線走到 #182 deterministic gate 花了 8 輪——submission package 正站在同一條演進線的起點。最值得 deterministic 化的三項：①雙盲去識別化殘留掃描（PDF metadata 作者欄、acknowledgments、自引措辭 "in our previous work"、補充檔檔名）——纯 script 可驗、失敗成本高（desk reject）、對單人研究者（沒有第二雙眼睛）價值最大；②字數/結構限制 vs venue 宣告的機械比對；③reference list ↔ 正文引用的雙向 set 比對。另 codex 指出 `repro_lock` 明文不被 integrity gate 讀（artifact_reproducibility_pattern.md:120-128）——transparency 鏈最後一哩斷在這裡，可併入同一個 verifier。

### 5.3 F-6 venue selection【增補，撞線，條件收窄】

現況：無 mode、無 agent；top_journals_by_field.md 是 EIC calibration 內部 reference。

**紅線分析（dual-track 後收窄）**：gemini 維持我的撞線判定並補刀（「AI 內部 retrieval 哪些 venue 顯示，本身就是 Top-K filter」）；codex 給出唯一可行形狀的精確條件：**candidate universe 必須 scholar-supplied 或 exhaustively disclosed**。亦即 ARS 不產生候選清單，只對 scholar 自己列出的 venues 填多軸事實表（scope 宣告、turnaround、OA 政策、字數限制、AI disclosure 政策——最後這項 ARS 的 venue_disclosure_policies 已有種子）。「幫我找適合的期刊」這個原始需求本身做不了（候選建構=隱性排名），能做的是「我在這四本之間猶豫」的事實比較器。價值縮水後還值不值得，送裁；優先級低於 F-1/F-2/F-5。

### 5.4 F-7 發表後段【增補，要求擴 POSITIONING scope，措辭修正】

初稿寫「citation tracking、errata、OA self-archiving 全空白」。**codex 修正：monitoring_agent 不是空白**——retraction/correction alert（含對自己研究的 impact assessment）、contradictory findings 偵測、author tracking、citation alert 設定指南都在，定位是 optional 的 post-research advisory。

準確的殘餘 gap 三項（皆是「對自己論文」的視角，monitoring_agent 是「對引用的別人論文」的視角）：①**自我 citation-context audit**：誰引用了我、把我的 claim 引成什麼樣——技術上是 L3 claim-faithfulness 的鏡像（同一套 anchor/judge 機制反向用），gemini 也獨立指出「總結 verifiable post-publication metrics 供機構 review 用」是不違反 Paper2X 的正當行政用途；②**自我 errata workflow**：發表後發現錯誤的更正流程支援；③**OA self-archiving 合規**：Sherpa Romeo 查詢、postprint 版本管理。

**此提案要求修改 POSITIONING 的 scope 敘述**（"research-to-publication"——publication 是終點站）。若裁定不擴，建議至少把「發表後是 deliberate non-goal」寫進 POSITIONING，理由同 F-1：留白與五條 Rejected mechanisms 的記錄紀律不對等。

### 5.5 F-13 grant/funding lifecycle【增補，scope 裁定；gemini 補抓】

本盤點初稿的生命週期走查從 RQ 孵化起跳，**整段漏掉 grant/計畫申請**——gemini 點出這是資深研究者實際行政負擔的大宗，且是 research program 的真正起點（先有計畫核定才有研究線）。repo 現況：funding_statement_guide 只處理「論文裡的 funding 聲明」，計畫書寫作（研究目的、文獻、方法、預期成果、預算敘述）零支援。

對使用者畫像（國科會申請）這是真實年度事件。但本盤點對它的立場有保留，跟 §9 的警告同源：**計畫書的「預期影響/預期成果」段是 impact-washing 的最高危文類**（承諾未發生的事），ARS 若進這個文類，最自然的滑坡就是「把預期影響寫到無懈可擊」。可辯護的切法：grant 的文獻段與方法段跟 ARS 現有能力（lit-review、research_architect）高度重疊，重用即可；預期成果段只做 advisory 探問不做生成。是否值得為此開 grant-mode（vs 使用者自己拿現有 modes 拼裝），送裁。我的傾向：**不開專屬 mode**，在 docs 補一頁「用現有 modes 寫計畫書的組裝指南」即可，把生成式支援明文排除。

---

## 6. 使用者畫像對位

### 6.1 F-10 中文線：比 SKILL.md 表面深，但止於排版【增補】

比預期好的部分（agent prompt 層實查）：literature_strategist 有 TSSCI/Airiti/台灣碩博士論文網檢索策略；apa7_chinese_citation_guide 有 TSSCI 期刊引用專節；formatter 有 xeCJK + TSSCI 期刊格式路由；pipeline Stage 5 指定 Source Han Serif TC。中文研究的「找文獻→寫→排版」鏈是通的。

缺的部分：①中文審查慣例——reviewer 5 persona 與 rubric 全以國際英文期刊為框架，台灣學報審查文化無對應；②TSSCI 投稿 workflow 無；③術語強制英文（"Academic terminology is kept in English"）對純中文社科論文是反向摩擦——台灣教育學界多數場合要求中文術語為主、英文夾注，現行規則方向相反。

裁定問題：投入量取決於你未來兩年的 TSSCI 投稿篇數，這是只有你知道的事實。若投，①③是寫作期就會痛的；②可以人肉。

### 6.2 F-3 灰色文獻：citation gate 對政策研究系統性低覆蓋【盲點】

四索引（S2 / OpenAlex / Crossref / arXiv）對政策研究的核心證據型態——政府報告、評鑑手冊、白皮書、法規、無 DOI 的國際組織文件——覆蓋率系統性偏低（初稿「全部查無」過度：部分 OECD/UNESCO 出版品有 DOI 可解析；codex 修正，gemini 對本條整體判 "factual and accurately assessed"）。C-V6 的精度優先設計（title-only unmatched → `unresolvable`，不 block）讓這些引用不被誤殺，這是對的；但後果是政策研究的 bibliography 大量落在 `unresolvable`，deterministic gate 的有效覆蓋率對這類研究大幅下降。**旗艦防線在維護者本人的研究類型上效力最低。**#250（gold set 缺 real-but-unindexed tuples）是同一個洞的工程面，本條是產品面：#250 說「量不到」，本條說「防不到」。

增補方向（成本遞增）：①`obtained_via: manual` 的灰色文獻 entry 加 structured provenance（URL + accessed_date + archive snapshot），manual 路線從「豁免」升級成「另一種可驗」；②URL 活性 + Wayback snapshot 存在性的 deterministic 檢查（script 層、無 LLM）；③接政府出版品 API（每轄區不同，維護地獄）。我的判斷：①②值得，③不值得。

---

## 7. 維護者品質 vs 使用者門檻

### 7.1 F-8 Opt-in 文化的暗面【盲點】

說公道話：49 條 lint、191 個 script、INV-* 全跑在 CI/maintainer 層，end user 零阻力。「lint 多 = 門檻高」不成立。

真正的門檻（數字經主 context 自查修正，codex 同向確認；gemini 在此條接受了未驗證的初稿數字，是 gemini 本輪唯一的 fact-check 失手，分歧記錄於 §11）：

1. **Flag 文件碎片化**：user-facing runtime flag 共 7 個，SETUP.md env 表列 5 個；`ARS_CLAIM_AUDIT`（claim audit 總開關）散在 README 行文三處、不在任何總表；`ARS_CACHE_DIR` 只在 design spec。問題本質不是數量是**沒有單一 flag 總表**。
2. **安全功能全部 opt-in 預設關**：strict citation policy、claim audit（default OFF）、cross-model verification。新研究者照 QUICKSTART 三步裝完，拿到 advisory 後綴（detection unconditional，標記會出現，這點誠實），但**沒有任何 block**。v2.7 那次 31% 引用錯誤率換來的 deterministic gate，預設不擋任何東西。Backward-compat 紀律（byte-equivalent 升級）與安全預設在此對撞，目前一律犧牲後者。
3. **配置疲勞**：paper full Phase 0 九項訪談；SETUP.md 408 行、5 種安裝法；新手路徑與 power-user 全貌之間無中間階梯。

增補形狀：①`ARS_PROFILE=strict|standard|minimal` 一鍵 profile（已確認 repo 無此名）；②單一 flag 總表進 SETUP.md（純文件工）；③裁定問題：新 user 預設要不要 citation_existence=strict？打破 byte-equivalent 慣例的取捨，只有你能裁。

### 7.2 F-9 Dogfooding 半斷流【盲點，時間線經 codex 修正】

初稿宣稱「v3.4 之後演進全為外部論文驅動、真實使用零痕跡」。**codex 打掉**：v3.6.7（04-30）的 spec 明寫源自 "v3.6.5/v3.6.6 production academic chapter run" 的 17 個 drift patterns——這正是 chapter 真實使用的 repo 痕跡（也吻合維護者 memory 中的 Springer chapter 時段）；v3.9.4.1 等版本是 codex post-ship 修正非論文驅動。

修正後仍成立的事實：①唯一完整 end-to-end worked example（showcase/）停在 v2.7 時代（2026-03-09），其後 **9 個 minor 版的新機制（triangulation、terminal policy、claim audit、Kong track、experiment provenance）沒有任何一個出現在完整真實 run 的 artifacts 裡**；②v3.8 之後（05-16 起）的 motivation 全是外部論文（Zhao/Co-Scientist/Kong/Kim）；③eval gold sets 幾乎全合成（citation_extraction 51 tuples 是 fabricated DOI，#250 自知；surface_form_parity 7 項中 3 項 maintainer 自寫）。

論文驅動買到結構化 threat model（可審計、可 lint 化），但量測的是「合成威脅下的防線」不是「真實使用中的價值」。風險走向：工具變成失敗模式文獻的博物館，而不是自己寫論文時痛處的解藥。

增補形狀（成本近零，改慣例不改程式）：①下一篇真論文走一次 full pipeline，產出第二個 showcase；考慮立「每 minor 至少一次 real-run smoke」的 release 慣例；②CHANGELOG 加 `Real-use findings` 慣例節，讓 lived experience 在 repo 留痕（v3.6.7 的 chapter-run 來源寫在 spec 內文深處，初稿盤點都沒挖到——這正說明回流痕跡需要一個固定位置）。

---

## 8. 誠實的 non-goal 清單

| 項目 | 為什麼不做 | 狀態 |
|---|---|---|
| 實驗執行/autonomous coding | Kong §3.3 rejected；scholar 跑、ARS 驗 provenance | 已拍板，維持 |
| Idea generation（RQ 提案/排序/改寫） | Kong L2，cognitive ownership 論證堅實。本盤點所有 RQ 期提案都設計成問不給；F-1 經 codex 收緊為三條件 | 已拍板，維持 |
| Paper2X auto-generation（含 plain-language summary 自動轉製） | POSITIONING rejected。**評估後不提案鬆動**：scholar-led 變體理論上可分，但它是 impact-washing 高危文類（S0 鏡像），dissemination design 已劃給 repo 外。不為它鬆動乾淨的紅線 | 維持 |
| Authenticated crawl / paywall bypass | 2026-04-22 拍板，集體風險論證 | 維持 |
| Data layer（外部 corpus 整合） | Passport 是唯一 input port。F-1 的 ledger 是 ARS 自產 artifacts 承接，我判斷不在射程內，邊界送裁 | 維持（F-1 邊界送裁） |
| Primary data 統計分析 | experiment-agent 領地 | 維持 |
| Multi-author 協作 | 修正：team_collaboration_protocol.md 已有 human-convention 層（roles/handoffs/approval 規則）+ intake 收 co-author data；零的是 passport 層 multi-author state（permissions、merge、co-author 確認）。**維持 non-goal**（單人工具的複雜度紅利就在單人），protocol 文件已足 | 維持，無需動作 |
| Grant 預期成果段的生成式支援 | F-13 評估後明文排除（impact-washing 最高危文類）；文獻/方法段重用現有 modes | 新增，建議記錄 |
| 發表後段、research program 層 | 若 F-7/F-1 裁定不做 → 寫進 POSITIONING non-goal，消除留白 | 待裁 |

---

## 9. 對 AACSB 報告的立場（含對使用者的挑戰）

**同意且已轉化為提案的**：impact-by-design——但 dual-track 證明 ARS 的 RQ 期已經做了（F-4 撤回是好消息：理念已內建），殘餘只在寫作期延伸（F-2 形狀 1）；spiral model 的跨輪迴路（F-1 的擴 scope 理由）；external engagement 視角（F-2 形狀 3）。

**挑戰報告本身的**：①它是學校層級 advocacy 文件，分析單位是 institution（p.10 明說 impact 不該落在個別 faculty 肩上），直接搬到單人 copilot 是 category error，本盤點只取「個人研究線」中間層；②它引了 Campbell's Law（p.19 n.15）卻對自家 Assessment Tool 毫無防 gaming 設計——一張自填 narrative worksheet，正是「把 impact 敘事寫到無懈可擊」的邀請函。

**挑戰使用者的（真反駁，不是迂迴同意）**：你同意 "research that reaches"，但你的機構角色和 S0 洞見都在告訴你 reach 的敘事面有多容易造假。這份報告若被工具化，最自然的產品化路徑就是「impact statement writer」——而那正是你在評鑑端要抓的東西。本盤點刻意把 reach 的接入點全部放在源頭（RQ 期，已存在）與事實層（citation-context audit、scholar-supplied 對照集），一個都不放在敘事層；F-13 的 grant 預期成果段同理排除。gemini 對這個 refusal 的評語是 "exceptionally well-argued" 但提醒「彙整 verifiable 既成 metrics 供機構表單」是正當用途——我接受這個區分：**回顧既成事實可以，前瞻承諾不行**。如果你不同意這個切法，分歧值得開 issue 吵。

---

## 10. 只有使用者能裁的判斷（按優先序）

1. **F-1 research-line ledger**：①算不算 data layer 禁令射程（我判斷不算）；②要不要開設計線（最小切片：scholar-initiated limitations surface + 自我 claim audit）；③不做的話要不要寫進 POSITIONING non-goal。
2. **F-7 發表後段要不要進 scope**：動 POSITIONING 的 identity 級決定。不做也請寫下 non-goal，消除留白。
3. **F-8 新 user 預設要不要 strict**：打破 byte-equivalent 慣例的取捨。
4. **F-2 做哪個形狀**：推薦先做形狀 1（socratic Layer 5 問句移植進 plan/revision coaching，最便宜）；形狀 2 重設計後價值縮水，可不做；形狀 3 便宜但價值虛。
5. **F-13 grant 段**：開組裝指南頁（我的傾向）還是完全不碰。
6. **F-10 中文線投入量**：取決於你的 TSSCI 投稿計畫。
7. **F-5/F-9/F-14**：低爭議（deterministic 化方向、real-run 慣例、rubric 權重 hygiene），可直接轉 scoped issues。

---

## 11. Dual-track 紀錄（codex 0.137 high-reasoning + gemini-3.1-pro-preview，2026-06-10）

**兩模型獨立收斂的（最高可信）**：①F-4 前提錯誤（兩邊都引 socratic_mentor_agent Layer 1/5 原文）；②「advisory ≠ 自動紅線安全，候選集建構本身是 ranking」（codex 打 F-2 形狀 2、gemini 打 F-6，不同條目同一原則）。

**codex 獨有的真 catch**：F-9 時間線（v3.6.7 chapter-run 證據）、F-5 低估（formatter checklist 原文）、F-7 過度宣稱（monitoring_agent 原文）、F-1 分類與 L2 三條件、F-14 rubric 不一致、F-3 措辭軟化。本輪 codex 表現顯著優於 gemini（11 條中 9 條成立）。

**gemini 獨有的真 catch**：F-13 grant lifecycle 整段遺漏（codex 沒抓到）；「回顧既成 metrics vs 前瞻承諾」的正當用途區分。

**分歧點（cross-model 的真學習）**：F-8 數字——codex 判 factual error（與主 context 自查一致），gemini 判 factual（接受了未驗證的 14/9 數字）。同一條宣稱、兩個 verdict，誰做了 first-party grep 誰就對。又一次印證 [[feedback_ai_only_chains_fail_at_fluent_wrongness]]：cross-model 不是保險，first-party deterministic 驗證才是。

**初稿五個被打掉/修正的宣稱全數源自同一根因**：subagent 地圖讀到 SKILL.md/README 層、沒讀 agent prompt 層（formatter/socratic_mentor/monitoring 的細節全在 agent .md 內文），主 context 又對自寫提案 anchoring。教訓：**對 prompt-架構 repo 做產品盤點，「功能存不存在」必須查到 agent prompt 層才算數**。

---

## 12. 裁定結果（2026-06-10，使用者拍板）

| Finding | 裁定 | 落點 |
|---|---|---|
| F-1 跨篇記憶 | **B：不做機制，出文件**。使用者問「靠 Claude Code memory 行不行」→ 答：個人層可（重餵 passport + assistant memory 提醒），產品層不可（public skill 不能依賴使用者環境；ARS anti-leakage 哲學本來就不信 LLM 記憶；passport 是唯一 state of record） | **#397**（POSITIONING non-goal + cross-paper workflow guide） |
| F-2 平庸可見性 | 做形狀 1（Layer 5 問句移植進 plan/revision coaching）；形狀 2/3 不做 | **#393**（p1） |
| F-3 灰色文獻 | 本輪未單獨立案（①manual provenance 強化可併入未來 citation-gate 線） | 報告留檔 |
| F-5 投稿包 | 做，design-first | **#394** |
| F-7 發表後 | **不做**：「使用者自己會查，戰線不宜拉過長」→ 寫成 recorded non-goal | **#397** |
| F-8 引用防線預設 | **預設不動，加配置訪談提問讓使用者選** | **#392** |
| F-9 real-run 慣例 | 做 | **#395** |
| F-10 TSSCI / F-13 計畫書 | **不做**：「給國際通用的 skill，用現有功能就好」 | 結案，報告留檔 |
| F-14 rubric 權重 | 修 | **#396** |

---

## 附錄：方法與證據

- 錨點文本全讀：POSITIONING.md（Rejected mechanisms 五條）、Kong L1/L2 design lessons（state-authority + verb test）、Co-Scientist L1（hidden ranking）、README、docs/PERFORMANCE.md、MODE_REGISTRY.md、data layer boundary memory（2026-04-22）。
- AACSB *A Framework for Research Impact*（May 2026）46 頁全讀：spiral model（App. B）、Assessment Tool（pp.20-23）、impact indicators（App. D）、Campbell's Law 自引（p.19 n.15）。
- 兩路 subagent 事實提取（SKILL.md 六軸地圖 + repo 八點掃描）→ 主 context 自查修正 3 處 → codex + gemini dual-track → 本版修訂 9 處。
- 本報告不動工程線：#330/#272/#250/#219/#89/#387 各有歸屬。
