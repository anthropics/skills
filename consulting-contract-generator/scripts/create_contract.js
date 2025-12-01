const fs = require('fs');
const { Document, Packer, Paragraph, TextRun, AlignmentType, HeadingLevel, LevelFormat } = require('docx');

const doc = new Document({
  styles: {
    default: { document: { run: { font: "MS Mincho", size: 22 } } },
    paragraphStyles: [
      { 
        id: "Title", 
        name: "Title", 
        basedOn: "Normal",
        run: { size: 32, bold: true, color: "000000", font: "MS Mincho" },
        paragraph: { spacing: { before: 240, after: 240 }, alignment: AlignmentType.CENTER } 
      },
      { 
        id: "Heading1", 
        name: "Heading 1", 
        basedOn: "Normal", 
        next: "Normal", 
        quickFormat: true,
        run: { size: 24, bold: true, color: "000000", font: "MS Mincho" },
        paragraph: { spacing: { before: 240, after: 120 }, outlineLevel: 0 } 
      }
    ]
  },
  numbering: {
    config: [
      { 
        reference: "article-list",
        levels: [
          { 
            level: 0, 
            format: LevelFormat.DECIMAL, 
            text: "第%1条", 
            alignment: AlignmentType.LEFT,
            style: { paragraph: { indent: { left: 0, hanging: 0 } } } 
          }
        ] 
      }
    ]
  },
  sections: [{
    properties: {
      page: { margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 } }
    },
    children: [
      new Paragraph({ 
        heading: HeadingLevel.TITLE, 
        children: [new TextRun("生成AIアドバイザリー業務委託契約書")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("合同会社大吉(以下「委託者」という)と、株式会社けんけん(以下「受託者」という)は、生成AI活用に関するアドバイザリー及びコンサルティング業務の委託に関し、以下のとおり業務委託契約(以下「本契約」という)を締結する。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (目的)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約は、委託者が受託者に対して、生成AI活用に関するアドバイザリー及びコンサルティング業務を委託し、受託者がこれを受託することを目的とする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (業務内容)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受託者は、委託者に対し、以下の業務を提供するものとする。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 生成AI活用戦略の策定支援")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 生成AIツールの選定・導入支援")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 従業員向け生成AI研修・教育の実施")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) プロンプトエンジニアリング指導")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(5) AI活用の効果測定及びレポーティング")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(6) その他、委託者が必要とする生成AI関連のアドバイザリー業務")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (契約期間)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 本契約の有効期間は、両当事者が記名捺印した日から1年間とする。ただし、期間満了の3ヶ月前までにいずれの当事者からも書面による解約の申し出がない場合は、同一条件でさらに1年間自動更新され、以後も同様とする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. いずれの当事者も、3ヶ月前までに相手方に書面で通知することにより、本契約を解約することができる。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (報酬及び支払条件)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 委託者は、受託者に対し、本契約に基づく業務の対価として、月額金200,000円(消費税別)を支払うものとする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 受託者は、毎月末日に当月分の請求書を委託者に送付し、委託者は翌月末日までに受託者が指定する銀行口座に振り込む方法により支払うものとする。なお、振込手数料は委託者の負担とする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (成果物)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 受託者は、業務遂行の過程において、提案書、レポート、研修資料その他の成果物(以下「成果物」という)を作成し、委託者に納品するものとする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 成果物の納品方法及び納期は、両当事者が別途協議の上、決定するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (知的財産権)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 本契約の履行により生じた成果物に関する著作権その他の知的財産権(著作権法第27条及び第28条に定める権利を含む)は、委託者及び受託者の共有とする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 前項の共有にかかる知的財産権の行使については、両当事者が別途協議の上、決定するものとする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("3. 受託者が本契約締結前から保有していた知的財産権及び本契約の履行とは無関係に受託者が開発した知的財産権については、受託者に帰属するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (再委託)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受託者は、委託者の事前の書面による承諾を得た場合に限り、本契約に基づく業務の全部又は一部を第三者に再委託することができる。この場合、受託者は再委託先の行為について、自らの行為と同様の責任を負うものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (機密保持)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("両当事者は、本契約の履行に関して知り得た相手方の機密情報について、別途締結する機密保持契約に従い、厳重に管理するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (委託者の義務)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("委託者は、受託者が業務を円滑に遂行できるよう、必要な情報の提供、担当者の選任その他の協力を行うものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (受託者の義務)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受託者は、善良なる管理者の注意をもって、誠実に本契約に基づく業務を遂行するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (契約解除)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 両当事者は、相手方が以下のいずれかに該当する場合、何らの催告なしに直ちに本契約の全部又は一部を解除することができる。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 本契約に定める義務に違反し、相当期間を定めた催告を受けたにもかかわらず、当該期間内にこれを是正しない場合")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 支払の停止又は破産手続開始、民事再生手続開始、会社更生手続開始、特別清算開始の申立があった場合")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 差押、仮差押、仮処分、競売の申立又は租税滞納処分を受けた場合")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) その他、本契約を継続し難い重大な事由が生じた場合")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 前項に基づく解除により相手方に損害が生じた場合であっても、解除した当事者は一切の責任を負わないものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (損害賠償)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 両当事者は、本契約に違反し、相手方に損害を与えた場合、当該損害を賠償する責任を負うものとする。ただし、賠償額の上限は金300万円とする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 前項の規定にかかわらず、故意又は重大な過失による場合は、上限額の適用を受けないものとする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("3. 第1項の損害賠償責任は、直接かつ現実に生じた通常の損害に限られ、逸失利益、特別損害及び間接損害は含まれないものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (権利義務の譲渡禁止)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("両当事者は、相手方の事前の書面による承諾を得ることなく、本契約上の地位及び本契約に基づく権利義務の全部又は一部を第三者に譲渡し、又は担保に供してはならない。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (反社会的勢力の排除)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 両当事者は、現在、暴力団、暴力団員、暴力団員でなくなった時から5年を経過しない者、暴力団準構成員、暴力団関係企業、総会屋等、社会運動等標ぼうゴロ又は特殊知能暴力集団等、その他これらに準ずる者(以下総称して「反社会的勢力」という)に該当しないこと、及び次の各号のいずれにも該当しないことを表明し、かつ将来にわたっても該当しないことを確約する。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 反社会的勢力が経営を支配していると認められる関係を有すること")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 反社会的勢力が経営に実質的に関与していると認められる関係を有すること")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 自己、自社若しくは第三者の不正の利益を図る目的又は第三者に損害を加える目的をもってするなど、不当に反社会的勢力を利用していると認められる関係を有すること")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) 反社会的勢力に対して資金等を提供し、又は便宜を供与するなどの関与をしていると認められる関係を有すること")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(5) 役員又は経営に実質的に関与している者が反社会的勢力と社会的に非難されるべき関係を有すること")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 両当事者は、相手方が前項の規定に違反した場合、何らの催告を要せずして、直ちに本契約を解除することができる。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("3. 第1項の規定により本契約を解除した当事者は、これにより相手方に損害が生じた場合であっても、一切の責任を負わないものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (契約の変更)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約の変更は、両当事者が書面により合意した場合に限り、その効力を生じるものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (分離可能性)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約のいずれかの条項又はその一部が無効又は執行不能と判断された場合であっても、本契約の残りの部分は引き続き完全な効力を有するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (協議事項)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約に定めのない事項及び本契約の解釈について疑義が生じた場合は、両当事者が誠実に協議の上、解決するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (管轄裁判所)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約に関する一切の紛争については、高松地方裁判所を第一審の専属的合意管轄裁判所とする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        pageBreakBefore: true,
        alignment: AlignmentType.LEFT,
        children: [new TextRun("本契約の成立を証するため、本書2通を作成し、両当事者記名捺印の上、各1通を保有する。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        alignment: AlignmentType.CENTER,
        children: [new TextRun("令和    年    月    日")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun({ text: "【委託者】", bold: true })] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("住所:")] 
      }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("商号:  合同会社大吉")] 
      }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("代表者:")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.RIGHT,
        children: [new TextRun("印")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun({ text: "【受託者】", bold: true })] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("住所:")] 
      }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("商号:  株式会社けんけん")] 
      }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("代表者:")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.RIGHT,
        children: [new TextRun("印")] 
      })
    ]
  }]
});

Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync("/mnt/user-data/outputs/生成AIアドバイザリー業務委託契約書.docx", buffer);
  console.log("生成AIアドバイザリー業務委託契約書を作成しました");
});
