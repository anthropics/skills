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
        children: [new TextRun("機密保持契約書")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("株式会社MIRAICHI(以下「開示者」という)と、株式会社けんけん(以下「受領者」という)は、開示者が受領者に対して開示する機密情報の取扱いに関し、以下のとおり機密保持契約(以下「本契約」という)を締結する。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (目的)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約は、開示者が受領者に対して、システム開発及び生成AIを含めたコンサルティング業務の遂行を目的として開示する機密情報について、その取扱いに関する事項を定めることを目的とする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (機密情報の定義)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("本契約において「機密情報」とは、開示者が受領者に対して開示する一切の情報(書面、電磁的記録、口頭その他の方法を問わない)をいう。特に以下の情報を含むが、これらに限定されない。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 顧客情報(氏名、住所、連絡先、取引履歴、購買情報等を含む)")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 技術情報、ノウハウ、システム構成、仕様書、設計書")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 営業情報、事業計画、マーケティング情報")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) その他、開示者が機密である旨を明示して開示した情報")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (機密保持義務)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受領者は、機密情報を善良なる管理者の注意をもって管理し、以下の各号を遵守するものとする。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 機密情報を第1条に定める目的以外に使用しないこと")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 機密情報を第三者に開示、漏洩しないこと")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 機密情報を複製する場合は、事前に開示者の書面による承諾を得ること")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) 受領者の役員及び従業員のうち、業務上機密情報を知る必要がある者に限り機密情報を開示し、これらの者に対し本契約と同等の機密保持義務を課すこと")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (適用除外)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("前条の規定にかかわらず、以下の各号のいずれかに該当する情報については、機密情報に該当しないものとする。")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(1) 開示の時点で既に公知であった情報")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(2) 開示後、受領者の責によらずして公知となった情報")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(3) 開示の時点で既に受領者が保有していた情報")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(4) 正当な権限を有する第三者から秘密保持義務を負うことなく適法に取得した情報")] 
      }),
      new Paragraph({ 
        indent: { left: 720 },
        children: [new TextRun("(5) 機密情報によらず独自に開発した情報")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (外部サービスの利用)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受領者は、業務遂行のため、適切なセキュリティ対策が講じられた外部サービス(Google Workspace、Microsoft 365等の企業向けサービスを含む)を利用することができる。ただし、個人情報を含む機密情報を生成AIサービスに入力する場合は、当該情報を匿名化又は一般化する等、合理的な配慮を行うものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (機密情報の返還・破棄)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("受領者は、開示者から要請があった場合、又は本契約が終了した場合には、開示者の指示に従い、遅滞なく機密情報(複製物を含む)を返還又は破棄し、その旨を開示者に書面で報告するものとする。")] 
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
        children: [new TextRun({ text: "  (契約期間)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 本契約は、両当事者の権限ある代表者または代理人が記名捺印した日をもって発効する。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 本契約の有効期間は、前項の発効日から3年間とする。ただし、期間満了の3ヶ月前までにいずれの当事者からも書面による解約の申し出がない場合は、同一条件でさらに1年間自動更新され、以後も同様とする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("3. 本契約が終了した場合においても、第3条に定める機密保持義務は、契約終了日から5年間存続する。ただし、個人情報に該当する機密情報については、契約終了後も適切な管理を継続するものとする。")] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      
      new Paragraph({ 
        numbering: { reference: "article-list", level: 0 },
        children: [new TextRun({ text: "  (損害賠償)", bold: true })] 
      }),
      new Paragraph({ 
        children: [new TextRun("1. 受領者が本契約に違反し、開示者に損害を与えた場合、受領者は開示者に対し、当該損害を賠償する責任を負うものとする。ただし、賠償額の上限は金500万円とする。")] 
      }),
      new Paragraph({ 
        children: [new TextRun("2. 前項の規定にかかわらず、受領者の故意又は重大な過失による場合は、上限額の適用を受けないものとする。")] 
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
        children: [new TextRun({ text: "【開示者】", bold: true })] 
      }),
      new Paragraph({ children: [new TextRun("")] }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("住所:")] 
      }),
      new Paragraph({ 
        alignment: AlignmentType.LEFT,
        children: [new TextRun("商号:  株式会社MIRAICHI")] 
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
        children: [new TextRun({ text: "【受領者】", bold: true })] 
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
  fs.writeFileSync("/mnt/user-data/outputs/機密保持契約書.docx", buffer);
  console.log("機密保持契約書を作成しました");
});
