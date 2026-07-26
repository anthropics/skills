const fs = require('fs');
const {
  Document, Packer, Paragraph, TextRun, HeadingLevel, AlignmentType,
  Table, TableRow, TableCell, WidthType, ShadingType, BorderStyle,
  PageBreak, Footer, PageNumber, LevelFormat
} = require('docx');

const HEAD='000078', GREEN='4EA506', CRIT='C0322F', WARN='B07600';
const INK='13151E', INK2='474D61', INK3='79809A', RULE='DDE2EC', BAND='EEF1F7';
const F='Calibri';

const P=(t,o={})=>new Paragraph({spacing:{after:o.after??120,before:o.before??0,line:276},
  indent:o.indent,children:[new TextRun({text:t,font:F,size:o.size??21,bold:o.bold,
  italics:o.italics,color:o.color??INK2})]});
const rich=(parts,o={})=>new Paragraph({spacing:{after:o.after??120,before:o.before??0,line:276},
  indent:o.indent,children:parts.map(([t,b,c])=>new TextRun({text:t,font:F,size:o.size??21,
  bold:!!b,color:c||o.color||INK2}))});
const H1=t=>new Paragraph({heading:HeadingLevel.HEADING_1,spacing:{before:340,after:150},
  children:[new TextRun({text:t,font:F,size:28,bold:true,color:HEAD})]});
const H2=t=>new Paragraph({heading:HeadingLevel.HEADING_2,spacing:{before:240,after:110},
  children:[new TextRun({text:t,font:F,size:23,bold:true,color:HEAD})]});
const H3=t=>new Paragraph({heading:HeadingLevel.HEADING_3,spacing:{before:190,after:90},
  children:[new TextRun({text:t,font:F,size:21,bold:true,color:INK})]});
const BAR=t=>new Paragraph({spacing:{before:420,after:200},
  border:{bottom:{style:BorderStyle.SINGLE,size:12,color:HEAD}},
  children:[new TextRun({text:t,font:F,size:31,bold:true,color:HEAD})]});
const CAP=t=>new Paragraph({spacing:{before:40,after:190},
  children:[new TextRun({text:t,font:F,size:16,color:INK3,italics:true})]});
const bl=(parts,lvl=0)=>new Paragraph({numbering:{reference:'b',level:lvl},
  spacing:{after:70,line:276},children:parts.map(([t,b,c])=>new TextRun({text:t,font:F,
  size:21,bold:!!b,color:c||INK2}))});
const callout=(title,body,col)=>new Paragraph({spacing:{before:150,after:190},
  border:{left:{style:BorderStyle.SINGLE,size:18,color:col,space:12}},indent:{left:200},
  children:[new TextRun({text:title+'  ',font:F,size:21,bold:true,color:INK}),
            new TextRun({text:body,font:F,size:21,color:INK2})]});

function table(head,rows,w,opt={}){
  const tot=w.reduce((a,b)=>a+b,0);
  const cell=(txt,ww,o={})=>new TableCell({width:{size:ww,type:WidthType.DXA},
    shading:o.shade?{type:ShadingType.CLEAR,fill:o.shade,color:'auto'}:undefined,
    margins:{top:55,bottom:55,left:85,right:85},
    borders:{top:{style:BorderStyle.SINGLE,size:2,color:RULE},
             bottom:{style:BorderStyle.SINGLE,size:2,color:RULE},
             left:{style:BorderStyle.NONE},right:{style:BorderStyle.NONE}},
    children:[new Paragraph({spacing:{after:0,line:240},alignment:o.align,
      children:[new TextRun({text:String(txt),font:F,size:o.size??18,bold:o.bold,
        color:o.color??INK2})]})]});
  return new Table({columnWidths:w,width:{size:tot,type:WidthType.DXA},rows:[
    new TableRow({tableHeader:true,children:head.map((h,i)=>cell(h,w[i],{bold:true,
      shade:BAND,size:16,align:i===0?AlignmentType.LEFT:AlignmentType.RIGHT}))}),
    ...rows.map(r=>new TableRow({children:r.map((c,i)=>{
      const o=c&&typeof c==='object';
      return cell(o?c.t:c,w[i],{align:i===0?AlignmentType.LEFT:AlignmentType.RIGHT,
        bold:o?c.b:false,color:o?c.c:undefined,
        shade:opt.foot&&r===rows[rows.length-1]?BAND:undefined});})}))]});
}
const g=t=>({t,c:GREEN,b:true}), r_=t=>({t,c:CRIT,b:true}),
      w_=t=>({t,c:WARN,b:true}), b_=t=>({t,b:true});

const doc=new Document({
  creator:'Jabatan Perkhidmatan Veterinar',
  title:'Lampiran G — Pemacu Output VetEC: Lawatan Ladang dan Identiti Zon',
  numbering:{config:[{reference:'b',levels:[
    {level:0,format:LevelFormat.BULLET,text:'•',alignment:AlignmentType.LEFT,
     style:{paragraph:{indent:{left:340,hanging:200}}}},
    {level:1,format:LevelFormat.BULLET,text:'–',alignment:AlignmentType.LEFT,
     style:{paragraph:{indent:{left:640,hanging:200}}}}]}]},
  styles:{default:{document:{run:{font:F,size:21,color:INK2}}}},
  sections:[{
    properties:{page:{size:{width:11906,height:16838},
      margin:{top:1134,bottom:1134,left:1134,right:1134}}}},
  ].map(s=>({...s,
    footers:{default:new Footer({children:[new Paragraph({alignment:AlignmentType.CENTER,
      children:[new TextRun({children:['Lampiran G — Pemacu Output VetEC  ·  ',
        PageNumber.CURRENT],font:F,size:16,color:INK3})]})]})},
    children:[

new Paragraph({spacing:{after:60},
  border:{bottom:{style:BorderStyle.SINGLE,size:12,color:GREEN}},
  children:[new TextRun({text:'JABATAN PERKHIDMATAN VETERINAR  ·  BAHAGIAN PEMBANGUNAN INDUSTRI TERNAKAN',
    font:F,size:15,bold:true,color:INK2})]}),
new Paragraph({spacing:{before:400,after:90},
  children:[new TextRun({text:'LAMPIRAN G',font:F,size:18,bold:true,color:INK3})]}),
new Paragraph({spacing:{after:150},
  children:[new TextRun({text:'Pemacu Output VetEC: Lawatan Ladang dan Identiti Zon',
    font:F,size:38,bold:true,color:HEAD})]}),
P('Lampiran F menyelesaikan soalan aras — zon yang mana, komoditi yang mana. Ia meninggalkan ' +
  'dua soalan terbuka. Pertama, adakah lawatan ladang benar-benar menyebabkan output naik, ' +
  'setelah bilangan pegawai dan zon diambil kira? Kedua, apakah sebenarnya "identiti zon" ' +
  'yang mengambil separuh varians output itu? Lampiran ini menjawab kedua-duanya.',
  {size:23,after:280}),

table(['Perkara','Butiran'],[
  ['Data VetEC','7 zon × 5 tahun (2021–2025), n = 35 — sama seperti Lampiran E dan F'],
  ['Data ciri zon','Keluasan negeri (km²), 64 titik operasi VetEC, Perangkaan Ternakan Malaysia'],
  ['Kaedah sebab-akibat','Tangga kawalan, beza pertama, ujian tanda, inferens rawak pilih atur'],
  ['Kaedah keteguhan','Gugur-satu-zon, gugur-satu-tahun, gugur-satu-sel (35 ujian)'],
  ['Kaedah pemisah','Aliran bukan kempen, kawalan pembohong, ujian plasebo ayam'],
  ['Nota sumber ternakan','Jadual 3.1 (lembu) dan 4.1 (ayam) dikenal pasti penuh. Satu jadual ' +
    'tambahan bertajuk terpotong dalam imej sumber; jumlahnya 297,186 ekor sepadan kambing — ' +
    'dilabel "kambing?" dan diuji berasingan, belum disahkan']],
  [2500,6800]),

new Paragraph({children:[new PageBreak()]}),

H1('Ringkasan: dua soalan, dua jawapan bersyarat'),
P('Kedua-dua soalan mempunyai jawapan positif pada pandangan pertama dan jawapan yang ' +
  'jauh lebih terhad selepas diperiksa. Jadual ini meringkaskan kedudukannya.',{after:180}),

table(['Soalan','Jawapan ringkas','Syarat penting'],[
  ['Adakah lawatan menaikkan output?',w_('Ya, tetapi terhad'),
   'Hanya kerja kempen; 78% pekali daripada 2021'],
  ['Adakah bilangan pegawai penting?',r_('Tidak'),
   'b = +39 unit/pegawai, p = 0.977 — nol pada setiap peringkat'],
  ['Adakah keluasan kawasan penting?',r_('Tidak'),
   'r = +0.148, p = 0.751 — zon terbesar bukan zon tertinggi'],
  ['Adakah populasi ternakan penting?',r_('Tidak'),
   'Antara zon p = 0.932; dalam zon p = 0.735'],
  ['Adakah titik operasi penting?',w_('Mungkin'),
   'r = +0.713, p = 0.072 — tidak dapat dibezakan daripada pantai']],
  [3000,1900,4400]),
CAP('Jadual G1. Ringkasan kedudukan setiap faktor yang diuji dalam Lampiran ini.'),

callout('Dapatan utama.',
  'Faktor yang paling kuat dalam data ini bukan pegawai, bukan keluasan, dan bukan ' +
  'populasi ternakan. Ia ialah pembahagian pantai barat lawan pantai timur — 47,829 ' +
  'unit berbanding 24,267 unit, nisbah 1.97 kali, p = 0.022 — yang sepadan tepat dengan ' +
  'struktur dua peringkat yang dikesan Tukey dalam Lampiran F.', HEAD),

BAR('BAHAGIAN I  ·  ADAKAH LAWATAN LADANG MENAIKKAN OUTPUT?'),

H1('G.1  Tangga kawalan: pekali menguat, bukan runtuh'),
P('Dalam Lampiran F, kesan komoditi runtuh sebaik sahaja zon dikawal. Lawatan ladang ' +
  'berkelakuan sebaliknya — pekalinya naik pada setiap langkah kawalan.'),

table(['Model','b','SE','p','R²'],[
  ['1. Lawatan sahaja','+10.29','2.44','0.0002','0.349'],
  ['2. + bilangan pegawai','+9.78','2.60','0.0007','0.357'],
  ['3. + kesan tetap zon (model E.2)',b_('+13.18'),'5.27',g('0.0191'),'0.605'],
  ['4. + kesan tetap tahun','+16.04','7.43',g('0.0419'),'0.615'],
  ['5. + saiz populasi penternak','+18.60','7.11',g('0.0162'),'0.674'],
  ['6. + program PPV','+21.93','7.63',g('0.0093'),'0.694']],
  [3700,1500,1400,1400,1300]),
CAP('Jadual G2. Pekali ke atas lawatan ladang apabila kawalan ditambah satu demi satu.'),

rich([['Tafsiran. ',1,INK],
  ['Kekeliruan antara zon ',0],['menyembunyikan',1],
  [' kesan ini, bukan menciptanya. Zon berlawatan tinggi ' +
   '(Barat Daya, Timur Laut) bukan zon output tinggi, jadi tidak mengawal zon ' +
   'menarik pekali ke bawah. Dalam model yang sama, pekali pegawai ialah ',0],
  ['+39 unit setiap pegawai (SE 1,297, p = 0.977)',1],
  [' — nol tulen. Bahagian "bukan bilangan pegawai" dalam soalan ini dijawab tegas.',0]]),

H1('G.2  Empat ujian ketat, semuanya lulus'),
P('Dengan hanya tujuh kluster, ralat piawai teguh tidak boleh dipercayai. Ujian berikut ' +
  'tidak bergantung pada andaian itu.'),

table(['Ujian','Apa yang diuji','Keputusan','p'],[
  ['Anggaran dalam-zon','Purata zon dibuang sepenuhnya','b = +16.04',g('0.0214')],
  ['Beza pertama','Adakah Δlawatan menggerakkan Δoutput','b = +15.38',g('0.0409')],
  ['Ujian tanda','Arah 28 perubahan tahunan','21/28 sepadan (75%)',g('0.0125')],
  ['Inferens rawak','20,000 pilih atur dalam zon','b = +16.04',g('0.0227')]],
  [2100,3400,2100,1400]),
CAP('Jadual G3. Ujian yang tidak bergantung pada ralat piawai teguh berkluster.'),

P('Ujian pilih atur ialah yang paling meyakinkan: lawatan dikocok dalam setiap zon ' +
  '20,000 kali, dan agihan nol yang terhasil mempunyai purata −0.15 dengan sisihan ' +
  'piawai 7.23. Nilai yang diperhati, +16.04, jatuh di luar 97.7% agihan itu.'),

H1('G.3  Tetapi pekali itu datang dari dua tempat sahaja'),

H2('Hampir kesemuanya ialah kerja kempen'),
P('Output teknikal ialah jumlah sepuluh aliran aktiviti. Memecahkannya kepada kerja ' +
  'kempen (pensampelan, vaksinasi, ujian lapangan) dan tujuh aliran lain mendedahkan ' +
  'dari mana pekali itu berasal.'),

table(['Sasaran','b','SE','p','% output'],[
  ['Output penuh (10 aliran)','+16.04','7.43',g('0.0419'),'100.0%'],
  ['Aliran kempen (sampel + vaksin + ujian)',b_('+15.46'),'7.03',g('0.0387'),'82.3%'],
  ['Tujuh aliran bukan kempen',r_('+0.59'),'0.77',r_('0.4560'),'17.7%']],
  [3900,1300,1300,1400,1400]),
CAP('Jadual G4. Kesan lawatan dipecahkan mengikut jenis kerja, kesan tetap zon + tahun.'),

rich([['Berbanding saiznya sendiri, aliran kempen bertindak balas ',0],
  ['5.6 kali lebih kuat',1],
  [' daripada aliran lain. Khidmat nasihat, kesihatan gerompok, rawatan, pembiakbakaan, ' +
   'lawat siasat, regulatori dan mesyuarat kesemuanya rata. Lawatan tidak menghasilkan ' +
   'lebih banyak kerja nasihat atau rawatan.',0]]),

H2('Dan 78% daripadanya datang daripada satu tahun'),
P('Menguraikan kovarians baki mengikut tahun menunjukkan berapa banyak setiap tahun ' +
  'menyumbang kepada pengangka pekali.'),

table(['Tahun','Sumbangan kepada pekali','Pekali jika tahun ini digugurkan','p'],[
  ['2021',r_('78.4%'),r_('+1.29'),r_('0.868')],
  ['2022','−5.5%','+20.10',g('0.025')],
  ['2023','4.0%','+19.77',g('0.023')],
  ['2024','6.2%','+17.34','0.063'],
  ['2025','16.9%','+20.75','0.056']],
  [1600,2900,2900,1600]),
CAP('Jadual G5. Leverage tahun ke atas pekali lawatan. Tanpa 2021 kesan itu lenyap.'),

P('Empat sel 2021 sahaja — Selatan, Tenggara, Utara dan Barat Daya — menyumbang 77% ' +
  'pekali. Ujian gugur-satu-sel mengesahkannya: daripada 35 ujian, pekali kekal ' +
  'signifikan dalam 23 sahaja, dan kesemua kegagalan melibatkan sel 2021.'),

H1('G.4  Tiada keutamaan masa'),
P('Sebab mesti mendahului kesan. Ujian lag menyemak sama ada urutan itu wujud.'),

table(['Ujian arah','b','p','Tafsiran'],[
  ['output(t) ~ lawatan(t−1)','+6.69',r_('0.4404'),'Lawatan tidak mendahului output'],
  ['lawatan(t) ~ output(t−1)','−0.0067',r_('0.3102'),'Output juga tidak mendahului lawatan'],
  ['output(t) ~ lawatan(t), kawal output(t−1)','+2.65',r_('0.7439'),
   'Kesan serentak hilang sepenuhnya']],
  [3600,1300,1300,3100]),
CAP('Jadual G6. Ujian keutamaan masa, n = 28 selepas lag.'),

H1('G.5  Magnitud tidak cukup besar'),
P('Walaupun pekali itu diterima sepenuhnya, saiz turun-naik lawatan terlalu kecil untuk ' +
  'menerangkan turun-naik output.'),

table(['Ukuran','Lawatan','Output','Nisbah'],[
  ['Pekali variasi dalam zon, purata 7 zon','15.8%','33.3%','2.1×'],
  ['Zon Tenggara','5.7%','35.2%','6.1×'],
  ['Zon Utara','8.3%','24.8%','3.0×']],
  [4200,1700,1700,1700]),
CAP('Jadual G7. Turun-naik dalam zon: output bergerak lebih daripada dua kali lawatan.'),

table(['Sumber varians output','% jumlah'],[
  ['Zon','50.8%'],['Tahun','2.1%'],['Bilangan pegawai','0.4%'],
  ['Lawatan ladang (sumbangan unik)',b_('8.2%')],
  ['Tidak diterangkan','38.5%']],
  [6400,2900]),
CAP('Jadual G8. Pecahan varians output. Lawatan menerangkan 17.5% baki turun-naik dalam zon.'),

H1('G.6  Tafsiran: produk bersama, bukan sebab-akibat'),
P('Bacaan yang paling sesuai dengan bukti ialah lawatan dan kerja kempen ialah dua ' +
  'produk bagi satu keputusan yang sama. Apabila zon melancarkan kempen pengawasan ' +
  'penyakit atau vaksinasi, ia melawat lebih banyak ladang dan merekod lebih banyak ' +
  'pensampelan, vaksinasi dan ujian lapangan — satu pasukan, satu perjalanan, beberapa ' +
  'kaunter. Keputusan kempen itulah pemboleh ubah sebenar.'),
callout('Ujian pemisah yang menentukan.',
  'Jika lawatan menyebabkan output, tujuh aliran bukan kempen sepatutnya turut naik ' +
  'dengan lawatan. Ia tidak (b = +0.59, p = 0.456). Itu kegagalan yang bersih.', CRIT),
P('Tiga kawalan pembohong pula lulus: lawatan tidak "meramal" bilangan pegawai ' +
  '(p = 0.230), bilangan penternak (p = 0.347), mahupun program PPV (p = 0.116). ' +
  'Jadi tiada kekeliruan yang jelas — hubungan itu nyata, cuma bukan hubungan sebab.'),

new Paragraph({children:[new PageBreak()]}),

BAR('BAHAGIAN II  ·  APA SEBENARNYA "IDENTITI ZON" ITU?'),

H1('G.7  Profil setiap zon'),
P('Tiga calon diuji sebagai kandungan kepada 50.8% varians yang diambil identiti zon: ' +
  'keluasan kawasan yang diliputi, bilangan titik operasi VetEC, dan populasi ternakan ' +
  'sebenar daripada Perangkaan Ternakan Malaysia.'),

table(['Zon VetEC','Negeri','km²','Titik','Lembu','Kambing?','Ayam (juta)'],[
  ['UTARA','Perlis, Kedah, P. Pinang','11,369','8','66,316','77,383','39.6'],
  ['TENGAH','Perak, Selangor','29,139','14','107,440','46,865','69.6'],
  ['BARAT DAYA','N. Sembilan, Melaka','8,350','10','76,663','29,214','68.6'],
  ['SELATAN','Johor','19,210','13','104,602','32,796','67.1'],
  ['TENGGARA','Pahang','36,137','9','138,565','41,170','16.1'],
  ['TIMUR','Terengganu','13,035',r_('5'),'102,502','39,891','4.5'],
  ['TIMUR LAUT','Kelantan','15,099',r_('5'),'68,548','29,867','4.7'],
  [b_('JUMLAH'),'',b_('132,339'),b_('64'),b_('664,636'),b_('297,186'),b_('270.1')]],
  [1500,2400,1150,750,1200,1200,1100],{foot:true}),
CAP('Jadual G9. Ciri identiti setiap zon, nilai 2025. Ternakan daripada Perangkaan Ternakan Malaysia.'),

H1('G.8  Mengapa ujian gantian yang mudah tidak sah'),
P('Godaan pertama ialah menggantikan dami zon dengan ciri-ciri ini dan melihat sama ada ' +
  'kesan zon lenyap. Ujian itu dijalankan, memberi keputusan yang kelihatan meyakinkan, ' +
  'dan kemudian digugurkan kerana ia tautologi.'),

table(['Ciri zon','R² apabila diregres atas dami zon'],[
  ['Keluasan kawasan',r_('1.0000  (malar dalam zon)')],
  ['Titik operasi',r_('1.0000  (malar dalam zon)')],
  ['Populasi ayam','0.9837'],
  ['Populasi kambing?','0.9720'],
  ['Populasi lembu','0.9700']],
  [4200,5100]),
CAP('Jadual G10. Setiap ciri zon hampir sepenuhnya ditentukan oleh identiti zon itu sendiri.'),

rich([['Keluasan dan titik operasi ialah dami zon yang dinamakan semula. Lima pemboleh ' +
   'ubah peringkat zon menjangkau hampir keseluruhan ruang enam-dimensi dami zon, jadi ' +
   'ia ',0],['mesti',1],[' menyerap kesan zon tanpa mengira sama ada ia benar-benar ' +
   'berkaitan. Ciri-ciri itu juga saling berkorelasi kuat: keluasan dengan lembu ' +
   'r = +0.88, titik operasi dengan ayam r = +0.89.',0]]),

H1('G.9  Keputusan peringkat zon yang sah'),
P('Dengan tujuh zon, hanya satu peramal boleh dianggar dengan yakin pada satu masa.'),

table(['Peramal tunggal','r','R² terlaras','p'],[
  ['Populasi ayam (plasebo)',w_('+0.797'),'0.563',w_('0.0318')],
  ['Titik operasi VetEC',b_('+0.713'),'0.410','0.0722'],
  ['Populasi kambing?','+0.536','0.145','0.2147'],
  ['Penternak pangkalan data VetEC','+0.467','0.061','0.2912'],
  ['Bilangan pegawai','+0.445','0.038','0.3170'],
  ['Populasi ruminan','+0.254','−0.123','0.5833'],
  ['Keluasan kawasan',r_('+0.148'),'−0.174',r_('0.7509')],
  ['Populasi lembu',r_('−0.040'),'−0.198',r_('0.9318')]],
  [4000,1600,1900,1800]),
CAP('Jadual G11. Korelasi peringkat zon dengan purata output lima tahun, n = 7.'),

callout('Amaran, bukan dapatan.',
  'Satu-satunya peramal yang mencapai p < 0.05 ialah populasi ayam — dan ayam bukan ' +
  'pelanggan VetEC. Apabila pemboleh ubah yang sepatutnya tidak berkaitan mengatasi ' +
  'setiap pemboleh ubah ruminan, itu tanda korelasi peringkat zon sedang menangkap ' +
  'sesuatu yang lebih umum.', WARN),

H1('G.10  Struktur sebenar: pantai barat lawan pantai timur'),

table(['Kumpulan','Zon','Purata output','Nisbah'],[
  ['Pantai barat','Utara, Tengah, Barat Daya, Selatan',b_('47,829'),'—'],
  ['Pantai timur','Tenggara, Timur, Timur Laut',b_('24,267'),b_('1.97×')],
  [b_('Ujian-t'),'','t = 3.27',g('p = 0.022')]],
  [1800,3900,2000,1900],{foot:true}),
CAP('Jadual G12. Perbezaan pantai, purata output teknikal 2021–2025.'),

P('Ayam berkorelasi +0.94 dengan "pantai barat"; titik operasi +0.74. Kedua-dua pemboleh ' +
  'ubah yang kelihatan penting dalam Jadual G11 hanyalah penanda kepada pembahagian ini. ' +
  'Dan pembahagian ini sepadan tepat dengan struktur dua peringkat yang dikesan Tukey ' +
  'dalam Lampiran F — Timur dan Timur Laut, dua zon yang berbeza secara signifikan ' +
  'daripada semua yang lain, ialah dua zon pantai timur yang paling kecil.'),

H1('G.11  Beban setiap titik operasi'),
P('Ukuran yang paling boleh ditindak ialah berapa banyak setiap titik operasi terpaksa ' +
  'tanggung.'),

table(['Zon VetEC','Titik','km² / titik','Lembu / titik','Penternak / titik','Output / titik'],[
  ['TENGGARA','9',r_('4,015'),r_('15,851'),'86','4,294'],
  ['TIMUR LAUT','5',r_('3,020'),r_('14,546'),'82','3,945'],
  ['TIMUR','5',r_('2,607'),r_('19,234'),'75',r_('2,885')],
  ['TENGAH','14','2,081','7,309','39','3,627'],
  ['SELATAN','13','1,478','8,175','43','3,055'],
  ['UTARA','8','1,421','8,495','70','6,801'],
  ['BARAT DAYA','10','835','7,417','43','4,642']],
  [1700,900,1500,1600,1900,1700]),
CAP('Jadual G13. Beban kerja setiap titik operasi. Tiga baris teratas ialah zon pantai timur.'),

rich([['Tiga zon pantai timur memikul ',0],['14,546 hingga 19,234 lembu setiap titik',1],
  ['; empat zon pantai barat memikul 7,309 hingga 8,495 — hampir ',0],['dua kali ganda',1],
  ['. Zon Timur mempunyai lembu terbanyak setiap titik dan titik paling sedikit, dan ' +
   'ialah zon yang Lampiran F kenal pasti sebagai terbawah secara signifikan. Julat ' +
   'km² setiap titik ialah 4.8 kali ganda; lembu setiap titik 2.6 kali ganda.',0]]),

H1('G.12  Populasi ternakan tidak meramal output — pada mana-mana peringkat'),

table(['Ujian','b atau r','p','Variasi baki'],[
  ['Lembu, antara zon (n = 7)','r = −0.040',r_('0.9318'),'—'],
  ['Lembu, dalam zon (KT zon + tahun)','b = −0.2319',r_('0.7348'),'2.6%'],
  ['Kambing?, dalam zon','b = +0.3511',r_('0.7896'),'2.1%'],
  ['Ruminan, dalam zon','b = −0.0807',r_('0.8782'),'3.8%'],
  ['Ayam, dalam zon (plasebo)','b = −0.0013','0.2320','0.9%']],
  [3600,2100,1700,1900]),
CAP('Jadual G14. Populasi ternakan terhadap output. Anggaran dalam zon melalui Frisch–Waugh–Lovell.'),

callout('Implikasi operasi.',
  'Beban kerja VetEC tidak diagihkan mengikut di mana ternakan sebenarnya berada. ' +
  'Zon Tenggara mempunyai lembu terbanyak (138,565) tetapi output pertengahan. Zon Timur ' +
  'mempunyai lembu ketiga terbanyak (102,502) dan output terendah sekali.', CRIT),

H1('G.13  Pangkalan data VetEC ialah hirisan kecil dan tidak sekata'),

table(['Zon VetEC','Penternak VetEC','Lembu negeri','Lembu setiap penternak'],[
  ['UTARA','684','66,316','97'],
  ['TENGGARA','1,362','138,565','102'],
  ['TENGAH','791','107,440','136'],
  ['SELATAN','595','104,602','176'],
  ['BARAT DAYA','301','76,663','255'],
  ['TIMUR','383','102,502','268'],
  ['TIMUR LAUT','123','68,548',r_('557')],
  [b_('JUMLAH'),b_('4,239'),b_('664,636'),b_('157')]],
  [2100,2300,2300,2600],{foot:true}),
CAP('Jadual G15. Liputan pangkalan data VetEC berbanding populasi lembu sebenar, 2025.'),

P('Nisbah lembu setiap penternak berdaftar berbeza 5.7 kali ganda antara zon. Pangkalan ' +
  'data VetEC bukan sampel seragam bagi sektor ternakan, yang mengehadkan kegunaan ' +
  '"penternak data asas" sebagai penyebut penanda aras.'),

H1('G.14  Penanda aras dinormalkan'),
P('Penyebut yang berbeza memberi kedudukan yang berbeza — kecuali bagi satu zon.'),

table(['Zon VetEC','Output mentah','/ pegawai','/ titik','/ 1000 km²','/ 1000 lembu','/ penternak'],[
  ['UTARA','54,408','3,127',b_('6,801'),'4,786',b_('801'),'97'],
  ['TENGAH','50,772','3,526','3,627','1,742','496','94'],
  ['BARAT DAYA','46,417',b_('3,868'),'4,642',b_('5,559'),'626',b_('108')],
  ['SELATAN','39,719','2,648','3,055','2,068','374','70'],
  ['TENGGARA','38,650','3,514','4,294',r_('1,070'),r_('271'),'50'],
  ['TIMUR',r_('14,427'),r_('1,244'),r_('2,885'),'1,107',r_('150'),r_('38')],
  ['TIMUR LAUT','19,724','1,370','3,945','1,306','271','48']],
  [1600,1500,1200,1150,1350,1350,1300]),
CAP('Jadual G16. Output dinormalkan mengikut enam penyebut, purata 2021–2025.'),

P('Zon Timur berada di kedudukan terendah mengikut lima daripada enam penyebut, dan ' +
  'kedua terendah mengikut yang keenam. Zon Tenggara jatuh dari pertengahan kepada ' +
  'kedudukan terendah apabila populasi lembu digunakan sebagai penyebut, kerana ia ' +
  'mempunyai lembu terbanyak.'),

new Paragraph({children:[new PageBreak()]}),

BAR('BAHAGIAN III  ·  PENAAKULAN DAN IMPLIKASI'),

H1('G.15  Bagaimana dua bahagian ini bertemu'),
P('Kedua-dua bahagian menunjuk kepada penjelasan yang sama, daripada dua arah berbeza.'),

bl([['Bahagian I mendapati kesan lawatan adalah nyata tetapi tertumpu pada kerja kempen ' +
  'dan pada satu tahun. Ia bukan tuas umum.',0]]),
bl([['Bahagian II mendapati identiti zon bukan keluasan dan bukan populasi ternakan, ' +
  'tetapi pembahagian pantai yang muncul dalam kepadatan titik operasi.',0]]),
bl([['Digabungkan: zon pantai timur mempunyai titik paling sedikit, beban ternakan ' +
  'setiap titik paling tinggi, lawatan paling sedikit, dan kerja kempen paling sedikit. ' +
  'Ini bukan empat masalah berasingan — ia satu kekangan kapasiti yang muncul dalam ' +
  'empat ukuran.',0]]),

P('Rantaian sebab yang paling disokong data ialah: kepadatan titik operasi menentukan ' +
  'berapa banyak kempen lapangan yang boleh dilancarkan; kempen menghasilkan lawatan ' +
  'ladang dan kerja pensampelan, vaksinasi serta ujian lapangan secara serentak; dan ' +
  'kerja itu ialah 82% output teknikal. Lawatan bukan penyebab dalam rantaian ini — ' +
  'ia kenderaan yang boleh dilihat.',{before:120}),

H2('Apa yang akan menyangkal setiap tafsiran'),
table(['Tafsiran','Ujian yang akan menyangkalnya'],[
  ['Lawatan ialah produk bersama, bukan sebab',
   'Zon menambah lawatan tanpa kempen dan output bukan kempen naik seiring'],
  ['Titik operasi ialah kekangan sebenar',
   'Titik baharu di Timur atau Timur Laut tidak menaikkan output zon itu'],
  ['Keluasan bukan kekangan',
   'Zon berkeluasan besar menunjukkan kos perjalanan yang mengehadkan output'],
  ['Populasi ternakan tidak relevan',
   'Zon dengan kenaikan ternakan yang ketara menunjukkan kenaikan output seiring']],
  [3400,6000]),
CAP('Jadual G17. Setiap tafsiran dinyatakan dalam bentuk yang boleh disangkal.'),

H1('G.16  Implikasi kepada tindakan Lampiran E dan F'),

H3('Tindakan 1 — Sasarkan lawatan ladang, bukan bilangan pegawai'),
rich([['Perlu dinyatakan semula. ',1,INK],
  ['Bahagian "bukan bilangan pegawai" disokong kuat pada setiap peringkat — pekali ' +
   'pegawai ialah +39 unit, p = 0.977, dan nol dalam setiap zon secara berasingan. ' +
   'Bahagian "sasarkan lawatan" pula perlu diubah: menambah lawatan tanpa kerja kempen ' +
   'yang menyertainya tidak dijangka menaikkan output. Yang boleh dipacu ialah keamatan ' +
   'kempen; lawatan ialah kenderaannya. Sasaran lawatan yang berdiri sendiri berisiko ' +
   'menghasilkan lebih banyak lawatan bernilai rendah.',0]]),

H3('Tindakan 2 — Penanda aras antara zon'),
rich([['Guna penyebut, bukan nilai mentah. ',1,INK],
  ['Output mentah mengelirukan kerana zon berbeza pada tiga dimensi serentak. Penyebut ' +
   'yang paling bermakna ialah output setiap titik operasi dan output setiap 1,000 lembu, ' +
   'kerana kedua-duanya menangkap beban sebenar. Penternak data asas ialah penyebut yang ' +
   'paling lemah kerana liputannya berbeza 5.7 kali ganda antara zon.',0]]),

H3('Tindakan 3 — Peruntukan titik operasi'),
rich([['Calon paling kuat, tetapi belum terbukti. ',1,INK],
  ['Titik operasi ialah satu-satunya faktor yang dikawal VetEC antara ketiga-tiga yang ' +
   'diuji, ia sejajar dengan struktur dua peringkat Tukey, dan metrik bebannya menunjukkan ' +
   'pantai timur memikul kira-kira dua kali ganda. Namun dengan tujuh zon ia tidak dapat ' +
   'dibezakan secara statistik daripada "berada di pantai timur" (p = 0.072). Ini hipotesis ' +
   'yang wajar diuji, bukan kesimpulan yang wajar dilaksanakan tanpa ujian.',0]]),

H1('G.17  Batasan'),
bl([['Tajuk salah satu jadual ternakan terpotong dalam imej sumber. Jumlahnya 297,186 ' +
  'ekor sepadan dengan kambing, dan ia dilabel "kambing?" sepanjang Lampiran ini. ' +
  'Ia patut disahkan sebelum petikan dibuat. Dapatan utama tidak bergantung padanya.',0]]),
bl([['Dengan tujuh zon, ciri peringkat zon tidak boleh dipisahkan secara statistik. ' +
  'Keluasan dan titik operasi malar dalam zon; ternakan 97–98% antara zon. Semua ' +
  'kenyataan tentang "faktor mana yang penting" adalah bersifat mencadang.',0]]),
bl([['Pekali lawatan bersandar pada tahun 2021. Data tambahan bagi 2026 dan seterusnya ' +
  'akan menentukan sama ada ia hubungan kekal atau ciri satu tahun.',0]]),
bl([['Keluasan negeri digunakan sebagai proksi kepada kawasan yang benar-benar diliputi. ' +
  'Kawasan operasi sebenar VetEC mungkin jauh lebih kecil dan berbeza-beza; jika data ' +
  'kawasan liputan sebenar ada, ujian ini patut diulang dengannya.',0]]),
bl([['Perangkaan Ternakan bagi 2025 ialah anggaran (ditanda "e" dalam sumber), bukan ' +
  'cerapan muktamad.',0]]),

new Paragraph({spacing:{before:340},
  border:{top:{style:BorderStyle.SINGLE,size:6,color:RULE}},
  children:[new TextRun({text:'Sumber: Laporan Log Teknikal 2021–2026; Perangkaan Ternakan ' +
    'Malaysia (Jadual 3.1 lembu, Jadual 4.1 ayam, dan satu jadual bertajuk terpotong); ' +
    'peta zon VetEC bagi titik operasi; keluasan negeri rasmi. Lampiran E dan F ialah ' +
    'rujukan asas — model E.2 dihasilkan semula tepat (b = +18.60) sebelum sebarang ' +
    'ujian dalam Lampiran ini dijalankan.',
    font:F,size:16,color:INK3,italics:true})]}),

  ]}))
});

Packer.toBuffer(doc).then(b=>{
  fs.writeFileSync('Lampiran-G-Pemacu-Output-VetEC.docx',b);
  console.log('ditulis:',b.length,'bait');
});
