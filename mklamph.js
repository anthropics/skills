const fs = require('fs');
const {
  Document, Packer, Paragraph, TextRun, HeadingLevel, AlignmentType,
  Table, TableRow, TableCell, WidthType, ShadingType, BorderStyle,
  PageBreak, Footer, PageNumber, LevelFormat, ExternalHyperlink
} = require('docx');

const HEAD='000078', GREEN='4EA506', CRIT='C0322F', WARN='B07600', LINK='0B5FA5';
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
const src=(label,url)=>new Paragraph({numbering:{reference:'b',level:0},
  spacing:{after:60,line:264},children:[
  new TextRun({text:label+' — ',font:F,size:17,color:INK2}),
  new ExternalHyperlink({link:url,children:[new TextRun({text:url,font:F,size:16,
    color:LINK,underline:{}})]})]});

function table(head,rows,w,opt={}){
  const tot=w.reduce((a,b)=>a+b,0);
  const cell=(txt,ww,o={})=>new TableCell({width:{size:ww,type:WidthType.DXA},
    shading:o.shade?{type:ShadingType.CLEAR,fill:o.shade,color:'auto'}:undefined,
    margins:{top:55,bottom:55,left:80,right:80},
    borders:{top:{style:BorderStyle.SINGLE,size:2,color:RULE},
             bottom:{style:BorderStyle.SINGLE,size:2,color:RULE},
             left:{style:BorderStyle.NONE},right:{style:BorderStyle.NONE}},
    children:[new Paragraph({spacing:{after:0,line:240},alignment:o.align,
      children:[new TextRun({text:String(txt),font:F,size:o.size??18,bold:o.bold,
        color:o.color??INK2})]})]});
  return new Table({columnWidths:w,width:{size:tot,type:WidthType.DXA},rows:[
    new TableRow({tableHeader:true,children:head.map((h,i)=>cell(h,w[i],{bold:true,
      shade:BAND,size:15,align:i===0?AlignmentType.LEFT:AlignmentType.RIGHT}))}),
    ...rows.map(r=>new TableRow({children:r.map((c,i)=>{
      const o=c&&typeof c==='object';
      return cell(o?c.t:c,w[i],{align:i===0?AlignmentType.LEFT:AlignmentType.RIGHT,
        bold:o?c.b:false,color:o?c.c:undefined,size:opt.size,
        shade:opt.foot&&r===rows[rows.length-1]?BAND:undefined});})}))]});
}
const g=t=>({t,c:GREEN,b:true}), r_=t=>({t,c:CRIT,b:true}),
      w_=t=>({t,c:WARN,b:true}), b_=t=>({t,b:true});

const doc=new Document({
  creator:'Jabatan Perkhidmatan Veterinar',
  title:'Lampiran H — Identiti Zon yang Tidak Diukur',
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
      children:[new TextRun({children:['Lampiran H — Identiti Zon yang Tidak Diukur  ·  ',
        PageNumber.CURRENT],font:F,size:16,color:INK3})]})]})},
    children:[

new Paragraph({spacing:{after:60},
  border:{bottom:{style:BorderStyle.SINGLE,size:12,color:GREEN}},
  children:[new TextRun({text:'JABATAN PERKHIDMATAN VETERINAR  ·  BAHAGIAN PEMBANGUNAN INDUSTRI TERNAKAN',
    font:F,size:15,bold:true,color:INK2})]}),
new Paragraph({spacing:{before:400,after:90},
  children:[new TextRun({text:'LAMPIRAN H',font:F,size:18,bold:true,color:INK3})]}),
new Paragraph({spacing:{after:150},
  children:[new TextRun({text:'Identiti Zon yang Tidak Diukur: Mandat Regulatori dan Artifak Pengukuran',
    font:F,size:36,bold:true,color:HEAD})]}),
P('Lampiran G menunjukkan identiti zon bukan keluasan kawasan dan bukan populasi ternakan, ' +
  'dan bahawa titik operasi tidak dapat dibezakan daripada pembahagian pantai. Ia meninggalkan ' +
  'soalan yang paling penting tanpa jawapan: jika bukan itu, apa? Lampiran ini menjawabnya, ' +
  'dan jawapannya mengubah cara keseluruhan siri ini patut dibaca.',
  {size:23,after:280}),

table(['Perkara','Butiran'],[
  ['Soalan','Apakah kandungan sebenar kesan zon yang tidak diukur?'],
  ['Data VetEC','7 zon × 5 tahun (2021–2025) dan lembaran separa 2026 (Jan–Apr)'],
  ['Pendekatan baharu','Memecahkan output kepada 10 aliran aktiviti dan bukan menganggapnya satu kuantiti'],
  ['Kaedah','Analisis campuran aktiviti, pecahan jurang, ujian musim, semakan unit pengukuran'],
  ['Sumber luar','Kesusasteraan penyakit veterinar Malaysia, status bebas penyakit WOAH, skim akreditasi ladang'],
  ['Status bukti luar','Kesusasteraan menengah dan dokumen awam. Belum disahkan dengan rekod program DVS dalaman']],
  [2400,6900]),

new Paragraph({children:[new PageBreak()]}),

H1('Ringkasan: identiti zon ialah mandat, bukan kapasiti'),
P('Tiga dapatan, disusun mengikut kekuatan bukti.',{after:180}),

H3('1. Jurang pantai lenyap sepenuhnya apabila kerja bermandat dikeluarkan'),
P('Zon pantai barat menghasilkan 1.61 kali output setiap pegawai berbanding zon pantai timur. ' +
  'Seluruh perbezaan itu terletak dalam dua aliran: ujian lapangan dan pensampelan. Keluarkan ' +
  'kedua-duanya, dan zon pantai timur sebenarnya berada sedikit di HADAPAN.'),

table(['Ukuran','Barat','Timur','Nisbah','t','p'],[
  ['Output penuh setiap pegawai','3,292','2,042','1.61×','1.81','0.1299'],
  ['Ujian lapangan + pensampelan',b_('1,935'),b_('446'),r_('4.34×'),'5.33',r_('0.0031')],
  ['Lapan aliran yang lain',b_('1,357'),b_('1,596'),g('0.85×'),'−0.55',g('0.6042')]],
  [3400,1400,1400,1300,900,1000]),
CAP('Jadual H1. Jurang pantai dipecahkan. Baris ketiga tidak signifikan dan bertanda songsang.'),

H3('2. Penurunan output kebangsaan ialah satu aliran, bukan kemerosotan prestasi'),
P('Output kebangsaan turun 9.3% antara 2021 dan 2025. Ujian lapangan turun 54,645 unit ' +
  'sementara sembilan aliran yang lain NAIK 27,438 unit. Tanpa ujian lapangan, output ' +
  'kebangsaan naik 15.3%.'),

H3('3. Kedudukan zon ialah artifak pilihan pengagregatan'),
P('"Output teknikal" menjumlahkan kiraan dalam unit yang tidak setara. Tiga aliran dikira ' +
  'setiap penternak atau setiap kes; yang lain jelas dikira setiap haiwan atau setiap sampel. ' +
  'Jika setiap aliran diberi berat sama, kedudukan zon berubah sehingga korelasi kedudukan ' +
  'dengan kedudukan asal hanya rho = +0.464 (p = 0.294) — pada dasarnya tiada kaitan.'),

callout('Kesimpulan pusat.',
  'Zon pantai timur tidak berprestasi rendah. Ia menjalankan kerja yang berbeza kerana ia ' +
  'tidak memikul obligasi ujian regulatori yang sama, dan sistem pengukuran memberi berat ' +
  'yang sangat besar kepada obligasi itu. Semua penanda aras yang membandingkan output ' +
  'mentah antara zon mengukur perbezaan mandat, bukan perbezaan prestasi.', HEAD),

BAR('BAHAGIAN I  ·  MENCIRIKAN BENDA YANG PERLU DITERANGKAN'),

H1('H.1  Saiz dan kestabilan kesan zon'),
P('Sebelum bertanya apa yang menyebabkan kesan zon, kita perlu tahu bentuknya. Kesan tetap ' +
  'zon dianggar dalam log dengan kesan tetap tahun dikawal, kemudian dipusatkan.'),

table(['Zon VetEC','Kesan (log)','Berbanding purata zon','SD merentas tahun'],[
  ['UTARA','+0.491','+63.4%','0.306'],
  ['TENGAH','+0.417','+51.7%','0.356'],
  ['BARAT DAYA','+0.323','+38.1%','0.270'],
  ['TENGGARA','+0.116','+12.3%','0.449'],
  ['SELATAN','−0.000','−0.0%',r_('0.629')],
  ['TIMUR LAUT','−0.499','−39.3%',g('0.094')],
  ['TIMUR','−0.847','−57.1%','0.317']],
  [2300,1900,2500,2600]),
CAP('Jadual H2. Kesan tetap zon dan kestabilannya. Julat 3.81 kali ganda.'),

rich([['Sisihan piawai antara zon ialah 0.500 log; sisihan piawai dalam zon merentas tahun ' +
  '0.346. Nisbah 1.45 bermakna kesan zon ialah ',0],['ciri yang cukup tetap',1],
  [', bukan bunyi latar — tetapi ia bukan malar. Zon Timur Laut sangat stabil (SD 0.094), ' +
   'sementara Zon Selatan sangat tidak stabil (SD 0.629).',0]]),

H1('H.2  Adakah ia skala atau campuran?'),
P('Ujian diagnostik yang menentukan. Jika zon melakukan kerja yang sama dalam jumlah berbeza, ' +
  'itu masalah kapasiti. Jika zon melakukan kerja yang berbeza, itu masalah mandat.'),

table(['Zon','Nasihat','Gerompok','Rawatan','Pembiak','Siasat','Regulat','Sampel',
       'Vaksin','Ujian lapangan','Mesyuarat'],[
  ['UTARA','8.7','1.8','3.0','1.1','2.7','2.4','16.0','24.9',b_('38.7'),'0.7'],
  ['TENGAH','4.7','0.9','1.0','0.2','0.9','0.5','18.7','30.3',b_('42.1'),'0.7'],
  ['BARAT DAYA','5.9','1.2','2.6','1.5','1.5','0.5','21.0','28.3',b_('37.1'),'0.3'],
  ['SELATAN','6.8','1.1','2.9','0.2','1.4','0.5','16.8','24.9',b_('45.0'),'0.4'],
  ['TENGGARA','5.9','1.7','1.9','0.1','0.6','1.1','14.6',r_('60.9'),r_('12.5'),'0.7'],
  ['TIMUR',r_('13.5'),'1.9','5.4','0.3',r_('12.4'),'2.0','12.9','45.5',r_('5.4'),'0.7'],
  ['TIMUR LAUT',r_('12.7'),r_('5.7'),r_('19.0'),'1.1','6.0','1.4','8.4','39.5',r_('2.9'),r_('3.3')],
  [b_('KEBANGSAAN'),b_('7.3'),b_('1.7'),b_('3.7'),b_('0.7'),b_('2.4'),b_('1.1'),
   b_('16.6'),b_('34.0'),b_('31.7'),b_('0.8')]],
  [1450,830,830,780,780,720,780,760,780,900,830],{foot:true,size:16}),
CAP('Jadual H3. Campuran aktiviti setiap zon, peratus output zon itu sendiri, 2021–2025.'),

rich([['Jawapannya jelas: ',0],['zon melakukan kerja yang berbeza',1],
  ['. Ujian lapangan ialah 37–45% output di keempat-empat zon pantai barat tetapi hanya ' +
   '2.9–12.5% di pantai timur. Sebaliknya Zon Timur Laut menjalankan 19.0% kerja rawatan ' +
   'berbanding 3.7% kebangsaan, dan Zon Timur 12.4% lawat siasat berbanding 2.4% kebangsaan. ' +
   'Zon Tenggara memberi 60.9% usahanya kepada vaksinasi.',0]]),

table(['Zon VetEC','Jarak campuran daripada corak kebangsaan'],[
  ['TIMUR LAUT',r_('0.350')],['TENGGARA',r_('0.332')],['TIMUR',r_('0.313')],
  ['SELATAN','0.163'],['TENGAH','0.120'],['UTARA','0.117'],['BARAT DAYA','0.093']],
  [3400,5900]),
CAP('Jadual H4. Jarak Euclid campuran aktiviti setiap zon daripada campuran kebangsaan.'),

BAR('BAHAGIAN II  ·  MENJEJAKI PUNCANYA'),

H1('H.3  Sembilan puluh peratus jurang pantai ialah satu aliran'),

table(['Aliran aktiviti','Barat/pegawai','Timur/pegawai','Nisbah','% jurang'],[
  [b_('Ujian lapangan'),b_('1,319'),b_('167'),r_('7.9×'),r_('90%')],
  ['Pensampelan','589','248','2.4×','27%'],
  ['Khidmat nasihat','214','182','1.2×','3%'],
  ['Pembiakbakaan','25','8','3.0×','1%'],
  ['Regulatori','34','27','1.3×','1%'],
  ['Mesyuarat','18','28',g('0.6×'),'−1%'],
  ['Kesihatan gerompok','41','55',g('0.7×'),'−1%'],
  ['Lawat siasat','54','86',g('0.6×'),'−3%'],
  ['Kes rawatan','76','142',g('0.5×'),'−5%'],
  ['Vaksinasi','884','1,025',g('0.9×'),'−11%'],
  [b_('JUMLAH'),b_('3,254'),b_('1,968'),b_('1.7×'),b_('100%')]],
  [2600,1800,1800,1400,1700],{foot:true}),
CAP('Jadual H5. Pecahan jurang pantai mengikut aliran, setiap pegawai, 2021–2025.'),

P('Lima aliran bertanda songsang — zon pantai timur menjalankan LEBIH banyak vaksinasi, ' +
  'rawatan, lawat siasat, kesihatan gerompok dan mesyuarat setiap pegawai. Vaksinasi sahaja ' +
  'menolak jurang ke bawah sebanyak 11%.'),

H1('H.4  Jurang itu lenyap sepenuhnya'),
P('Jadual H1 di halaman pertama ialah dapatan utama Lampiran ini. Diulang di sini dengan ' +
  'tafsirannya.'),
callout('Apabila ujian lapangan dan pensampelan dikeluarkan,',
  'zon pantai barat menghasilkan 1,357 unit setiap pegawai dan zon pantai timur 1,596 — ' +
  'nisbah 0.85 kali, tidak signifikan (p = 0.604). Kedudukan bertukar arah. Tiada jurang ' +
  'prestasi untuk diterangkan.', GREEN),

table(['Zon VetEC','Output/pegawai','Kedudukan','Tanpa ujian lapangan','Kedudukan','Anjakan'],[
  ['BARAT DAYA','3,868','1','1,623','2','−1'],
  ['TENGAH','3,526','2','1,380','4','−2'],
  ['TENGGARA','3,514','3',b_('2,559'),g('1'),g('+2')],
  ['UTARA','3,127','4','1,417','3','+1'],
  ['SELATAN','2,648','5','1,009',r_('7'),r_('−2')],
  ['TIMUR LAUT','1,370','6','1,215','5','+1'],
  ['TIMUR','1,244','7','1,016','6','+1']],
  [2100,1800,1400,2100,1200,1000]),
CAP('Jadual H6. Kedudukan zon dengan dan tanpa ujian lapangan. Julat mengecil 3.11× kepada 2.54×.'),

H1('H.5  Apakah "ujian lapangan" itu sebenarnya?'),
P('Log Teknikal tidak menyatakan definisi. Sumber luar memberi jawapan yang konsisten, dan ' +
  'ia menerangkan mengapa aliran ini tertumpu di sebelah barat.'),

bl([['Zon bebas penyakit kuku dan mulut dengan vaksinasi. ',1,INK],
  ['Malaysia mempunyai zon bebas FMD dengan vaksinasi yang meliputi Pulau Langkawi ' +
   '(Kedah, dalam Zon VetEC Utara) dan tiga daerah di Johor (Zon Selatan). Kod Kesihatan ' +
   'Haiwan Terestrial WOAH mensyaratkan serosurveilans berterusan dalam spesies mudah ' +
   'terjangkit untuk mengekalkan status itu.',0]]),
bl([['Ujian tuberkulosis bovin di ladang tenusu. ',1,INK],
  ['Kesusasteraan melaporkan TB bovin dikesan secara berterusan di ladang tenusu terutamanya ' +
   'di Selangor (Zon Tengah), dengan polisi uji-dan-sembelih menggunakan ujian kulit servikal ' +
   'perbandingan dan Bovigam. Hampir 30% ladang tenusu lembu di Selangor dilaporkan ditutup ' +
   'akibat reaktor TB berterusan.',0]]),
bl([['Pemantauan brucellosis. ',1,INK],
  ['Antibodi Brucella dikesan dalam 21.8% kawanan yang disampel di Semenanjung Malaysia ' +
   'antara 2000 dan 2008. Kawanan yang terjejas disyorkan menjalani pensampelan darah ' +
   'setiap empat bulan.',0]]),
bl([['Akreditasi ladang. ',1,INK],
  ['Skim Amalan Ladang Ternakan (SALT), yang dijenamakan semula di bawah myGAP pada 2013, ' +
   'menetapkan protokol biosekuriti dan program kesihatan kawanan. Ladang yang diakreditasi ' +
   'untuk eksport memerlukan sijil yang sah.',0]]),

rich([['Ketiga-tiga yang pertama ialah ',0],['obligasi berulang yang dikenakan pada kawanan ' +
  'tertentu',1],[' — bukan aktiviti mengembang yang boleh dipilih oleh zon. Kawanan tenusu ' +
  'peri-urban dan zon bebas penyakit menghasilkan aliran kerja ujian yang berterusan; ' +
  'kawanan pedaging pekebun kecil tidak.',0]],{before:120}),

H1('H.6  Ini menerangkan dapatan terkuat Lampiran F'),
P('Lampiran F mendapati bahagian lembu tenusu ialah penanda peringkat zon yang paling kuat ' +
  'bagi keamatan perkhidmatan (r = +0.913), tetapi tidak dapat menerangkan mengapa, dan ' +
  'mendapati ia lenyap dalam zon. Sekarang mekanismenya jelas.'),

table(['Zon VetEC','Bhg lembu tenusu','Ujian lapangan','% output','2021','2025'],[
  ['BARAT DAYA','35.7%','17,207','37.1%','29,468','15,590'],
  ['TENGAH','34.8%','21,400','42.1%','23,995','17,241'],
  ['UTARA','20.8%','21,038','38.7%','7,813',b_('19,482')],
  ['SELATAN','19.0%','17,893','45.0%',r_('49,711'),r_('1,881')],
  ['TENGGARA','3.6%','4,847','12.5%','1,677','5,105'],
  ['TIMUR LAUT','2.1%','568','2.9%','1,026','520'],
  ['TIMUR','0.3%','781','5.4%','918',r_('144')]],
  [2000,1900,1700,1300,1300,1400]),
CAP('Jadual H7. Bahagian lembu tenusu dan volum ujian lapangan mengikut zon.'),

rich([['Bahagian lembu tenusu berkorelasi ',0],['r = +0.891 (p = 0.0070)',1],
  [' dengan ujian lapangan dan ',0],['r = +0.918 (p = 0.0036)',1],
  [' dengan pensampelan. Lembu tenusu bukan pemacu output — ia penanda bagi kawanan yang ' +
   'tertakluk kepada rejim ujian wajib. Itulah sebabnya kesannya kuat antara zon dan sifar ' +
   'dalam zon: campuran komoditi zon berubah perlahan, tetapi obligasi ujiannya tidak ' +
   'berubah sama sekali dari tahun ke tahun.',0]]),

H1('H.7  Keruntuhan Zon Selatan ialah keruntuhan ujian lapangan'),
P('Lampiran D mengenal pasti Zon Selatan sebagai penurunan terbesar dalam panel: 85,197 ' +
  'kepada 21,397, iaitu −74.9%. Pecahan aliran menunjukkan puncanya.'),

table(['Aliran','2021','2025','Perubahan','% jurang'],[
  [b_('Ujian lapangan'),b_('49,711'),b_('1,881'),r_('−47,830'),r_('75%')],
  ['Vaksinasi','15,899','8,139','−7,760','12%'],
  ['Pensampelan','10,598','5,975','−4,623','7%'],
  ['Khidmat nasihat','5,198','1,480','−3,718','6%'],
  ['Kesihatan gerompok','833','338','−495','1%'],
  ['Empat aliran kecil lain','1,401','918','−483','1%'],
  ['Kes rawatan','1,557','2,573',g('+1,016'),'−2%'],
  [b_('JUMLAH'),b_('85,197'),b_('21,397'),b_('−63,800'),b_('100%')]],
  [2800,1600,1600,1800,1500],{foot:true}),
CAP('Jadual H8. Pecahan penurunan Zon Selatan 2021–2025.'),

P('Ujian lapangan Zon Selatan jatuh 96%. Ini bukan corak kemerosotan operasi — ia corak ' +
  'program yang tamat atau diubah. Zon Selatan merangkumi tiga daerah Johor yang membawa ' +
  'status bebas FMD dengan vaksinasi; sebarang perubahan kepada protokol serosurveilans ' +
  'di sana akan kelihatan tepat seperti ini. Kes rawatan naik dalam tempoh yang sama, ' +
  'menunjukkan kapasiti lapangan tidak hilang.'),

H1('H.8  Penurunan kebangsaan juga satu aliran'),

table(['Tahun','Ujian lapangan','Sembilan aliran lain','Jumlah'],[
  ['2021','114,608','179,204','293,812'],
  ['2022','102,910','171,790','274,700'],
  ['2023','91,004','159,979','250,983'],
  ['2024','50,180','184,304','234,484'],
  ['2025','59,963',b_('206,642'),'266,605'],
  [b_('Perubahan'),r_('−54,645'),g('+27,438'),b_('−27,207')]],
  [1900,2400,2600,2400],{foot:true}),
CAP('Jadual H9. Output kebangsaan dipecahkan kepada ujian lapangan dan yang lain.'),

callout('Pembacaan semula yang perlu.',
  'Angka "output turun 9.3%" adalah betul secara aritmetik tetapi mengelirukan sebagai ' +
  'penunjuk prestasi. Sembilan daripada sepuluh aliran aktiviti NAIK 15.3% antara 2021 ' +
  'dan 2025. Yang turun ialah satu aliran ujian regulatori, daripada 17.2 kepada 9.0 ujian ' +
  'setiap 100 lembu kebangsaan.', WARN),

new Paragraph({children:[new PageBreak()]}),

BAR('BAHAGIAN III  ·  ARTIFAK PENGUKURAN'),

H1('H.9  "Output teknikal" menjumlahkan unit yang tidak setara'),
P('Tajuk lajur dalam Log Teknikal sendiri mendedahkan masalah ini. Tiga aliran menyatakan ' +
  'unitnya; tujuh tidak.'),

table(['Aliran aktiviti','Jumlah 5 tahun','Setiap penternak/tahun','Unit dinyatakan'],[
  ['Vaksinasi','449,468',r_('24.5'),'tidak dinyatakan'],
  ['Ujian lapangan','418,665',r_('22.9'),'tidak dinyatakan'],
  ['Pensampelan','219,107',r_('12.0'),'tidak dinyatakan'],
  ['Khidmat nasihat','96,671','5.3',g('bil. penternak')],
  ['Kes rawatan','48,642','2.7',g('bil. KES')],
  ['Lawat siasat','31,804','1.7','tidak dinyatakan'],
  ['Kesihatan gerompok','22,172','1.2',g('bil. penternak')],
  ['Audit / verifikasi','14,847','0.8','tidak dinyatakan'],
  ['Mesyuarat','10,372','0.6','tidak dinyatakan'],
  ['Pembiakbakaan','8,836','0.5',g('bil. penternak')]],
  [2500,1900,2300,2600]),
CAP('Jadual H10. 18,315 penternak-tahun dalam pangkalan data. Aliran teratas mencapai 22–25 ' +
    'unit setiap penternak setahun — tidak konsisten dengan kiraan setiap orang.'),

P('Vaksinasi, ujian lapangan dan pensampelan masing-masing mencapai lebih 12 unit setiap ' +
  'penternak berdaftar setiap tahun. Tiada perkhidmatan pengembangan melawat penternak yang ' +
  'sama 23 kali setahun. Angka-angka itu hampir pasti kiraan setiap haiwan atau setiap sampel. ' +
  'Menjumlahkannya dengan kiraan setiap penternak bermakna satu ujian darah diberi berat yang ' +
  'sama dengan satu sesi khidmat nasihat sepenuh hari.'),

table(['Zon VetEC','Ujian lapangan 2025','Lembu negeri','Ujian setiap 100 lembu'],[
  ['UTARA','19,482','66,316',b_('29.4')],
  ['BARAT DAYA','15,590','76,663','20.3'],
  ['TENGAH','17,241','107,440','16.0'],
  ['TENGGARA','5,105','138,565','3.7'],
  ['SELATAN','1,881','104,602','1.8'],
  ['TIMUR LAUT','520','68,548','0.8'],
  ['TIMUR','144','102,502',r_('0.1')],
  [b_('KEBANGSAAN'),b_('59,963'),b_('664,636'),b_('9.0')]],
  [2200,2400,2200,2500],{foot:true}),
CAP('Jadual H11. Intensiti ujian lapangan berbanding saiz kawanan negeri. Julat lebih 200 kali ganda.'),

H1('H.10  Kedudukan zon bergantung pada pilihan pemberat'),
P('Ujian terakhir dan paling merendahkan. Jika setiap aliran aktiviti diberi berat yang sama ' +
  '— setiap satu ditukar kepada skor-z merentas zon, kemudian dipuratakan — kedudukan zon ' +
  'berubah hampir sepenuhnya.'),

table(['Zon VetEC','Output/pegawai','Kedudukan','Skor-z purata','Kedudukan'],[
  ['BARAT DAYA','3,868','1','+0.392','2'],
  ['TENGAH','3,526','2','−0.217',r_('5')],
  ['TENGGARA','3,514','3','+0.112','4'],
  ['UTARA','3,127','4','+0.606',g('1')],
  ['SELATAN','2,648','5','−0.476','6'],
  ['TIMUR LAUT','1,370','6','+0.136',g('3')],
  ['TIMUR','1,244','7','−0.553','7']],
  [2400,2100,1600,1900,1300]),
CAP('Jadual H12. Kedudukan zon di bawah dua pilihan pengagregatan. Spearman rho = +0.464, p = 0.294.'),

P('Zon Timur Laut bergerak dari kedudukan 6 kepada 3; Zon Tengah dari 2 kepada 5; Zon Utara ' +
  'dari 4 kepada 1. Kedua-dua kedudukan itu tidak berkorelasi secara statistik. Tiada satu ' +
  'pun daripadanya lebih "betul" — tetapi hakikat bahawa kedudukan bergantung sepenuhnya pada ' +
  'pilihan pemberat bermakna kedudukan mentah tidak boleh menyokong keputusan peruntukan.'),

BAR('BAHAGIAN IV  ·  FAKTOR YANG DITOLAK'),

H1('H.11  Musim tengkujuh: hipotesis munasabah yang gagal'),
P('Monsun timur laut melanda pantai timur dari November hingga Mac. Banjir November 2024 ' +
  'dilaporkan sebagai yang terburuk sejak 2014, menjejaskan Kelantan, Terengganu dan Pahang ' +
  'serta memutuskan akses ke kawasan terpencil. Jika akses lapangan ialah kekangan, suku ' +
  'pertama sepatutnya lemah tidak seimbang di zon pantai timur. Lembaran separa 2026 ' +
  '(Januari–April) membenarkan ujian itu.'),

table(['Zon VetEC','Pantai','2026 Jan–Apr','Purata 4 bulan','Nisbah'],[
  ['TENGGARA','Timur','17,934','12,883',g('1.39×')],
  ['TIMUR LAUT','Timur','8,935','6,575',g('1.36×')],
  ['BARAT DAYA','Barat','18,857','15,472','1.22×'],
  ['TENGAH','Barat','17,059','16,924','1.01×'],
  ['SELATAN','Barat','10,941','13,240','0.83×'],
  ['UTARA','Barat','12,144','18,136','0.67×'],
  ['TIMUR','Timur','2,006','4,809',r_('0.42×')]],
  [2100,1500,2000,2100,1600]),
CAP('Jadual H13. Ujian musim. Purata pantai barat 0.93×, pantai timur 1.06×; t = −0.42, p = 0.6951.'),

rich([['Hipotesis itu ',0],['ditolak',1],['. Dua daripada tiga zon pantai timur mencatat suku ' +
  'pertama yang LEBIH KUAT daripada purata tahunan mereka. Zon Timur lemah (0.42×), tetapi ' +
  'begitu juga Zon Utara di pantai barat (0.67×). Tiada defisit khusus pantai timur.',0]]),

H1('H.12  Ringkasan setiap faktor yang diuji merentas Lampiran G dan H'),

table(['Faktor yang dicalonkan','Status','Bukti'],[
  ['Obligasi ujian regulatori',g('Disokong kuat'),
   'Jurang pantai lenyap tanpanya (p = 0.604); campuran aktiviti berbeza secara sistematik'],
  ['Struktur kawanan (tenusu/komersial)',g('Disokong'),
   'r = +0.891 dengan ujian lapangan; mekanisme disokong kesusasteraan'],
  ['Artifak unit pengukuran',g('Disokong kuat'),
   'Aliran teratas 22–25 unit setiap penternak setahun; kedudukan tidak stabil rho = +0.464'],
  ['Kepadatan titik operasi',w_('Tidak diputuskan'),
   'r = +0.713, p = 0.072; tidak dapat dibezakan daripada pantai'],
  ['Akses makmal',w_('Belum diuji'),
   'Tiada data lokasi makmal diperoleh; hipotesis munasabah yang kekal terbuka'],
  ['Keluasan kawasan',r_('Ditolak'),'r = +0.148, p = 0.751'],
  ['Populasi ternakan',r_('Ditolak'),'Antara zon p = 0.932; dalam zon p = 0.735'],
  ['Bilangan pegawai',r_('Ditolak'),'b = +39 unit/pegawai, p = 0.977'],
  ['Musim tengkujuh / banjir',r_('Ditolak'),'Tiada defisit Q1 pantai timur; p = 0.695']],
  [2900,1700,4700]),
CAP('Jadual H14. Kedudukan setiap faktor selepas pengujian.'),

new Paragraph({children:[new PageBreak()]}),

BAR('BAHAGIAN V  ·  PENAAKULAN DAN IMPLIKASI'),

H1('H.13  Penaakulan'),
P('Rantaian yang paling disokong bukti berjalan seperti ini.'),

bl([['Struktur sektor berbeza secara geografi. ',1,INK],
  ['Ternakan tenusu di Malaysia tertumpu berhampiran pusat bandar dan kawasan peri-urban ' +
   'di pantai barat. Pekebun kecil di Kelantan dan Terengganu beroperasi dengan buruh ' +
   'keluarga yang tidak dibayar. Ini bukan pilihan VetEC — ia keadaan sedia ada.',0]]),
bl([['Struktur itu menentukan obligasi regulatori. ',1,INK],
  ['Kawanan tenusu dan zon bebas penyakit menarik ujian berulang wajib: ujian kulit TB, ' +
   'serosurveilans FMD, pensampelan brucellosis setiap empat bulan. Kawanan pedaging ' +
   'pekebun kecil tanpa status akreditasi tidak.',0]]),
bl([['Obligasi itu menghasilkan volum kiraan yang besar. ',1,INK],
  ['Ujian dikira setiap haiwan atau setiap sampel, jadi satu pusingan ujian kawanan boleh ' +
   'menghasilkan ribuan unit. Kerja nasihat dikira setiap penternak.',0]]),
bl([['Sistem pengukuran menjumlahkan kedua-duanya. ',1,INK],
  ['"Output teknikal" oleh itu didominasi oleh kerja ujian, yang bermakna ia mengukur ' +
   'obligasi regulatori zon dan bukan usaha pengembangannya.',0]]),

P('Ini menerangkan setiap dapatan yang aneh dalam siri ini secara serentak: mengapa bilangan ' +
  'pegawai tidak penting (obligasi ujian tidak berskala dengan kakitangan), mengapa lembu ' +
  'tenusu ialah penanda yang kuat antara zon tetapi sifar dalam zon (ia menanda status, dan ' +
  'status tidak berubah setiap tahun), mengapa lawatan ladang kelihatan berkesan hanya untuk ' +
  'kerja kempen (lawatan ialah kenderaan bagi pusingan ujian), dan mengapa Zon Timur berada ' +
  'di kedudukan terakhir mengikut setiap penyebut mentah (ia mempunyai obligasi ujian yang ' +
  'paling sedikit di negara ini, 0.1 ujian setiap 100 lembu).',{before:120}),

H2('Apa yang akan menyangkal tafsiran ini'),
table(['Tafsiran','Ujian yang akan menyangkalnya'],[
  ['Jurang ialah mandat, bukan prestasi',
   'Zon pantai timur menunjukkan output lebih rendah setiap pegawai dalam aliran yang tiada ' +
   'kaitan dengan ujian, setelah campuran kes disamakan'],
  ['Ujian lapangan ialah kerja bermandat',
   'Rekod DVS menunjukkan volum ujian lapangan ditetapkan oleh pilihan zon, bukan protokol penyakit'],
  ['Unit pengukuran tidak setara',
   'Definisi pengumpulan data menunjukkan kesepuluh aliran memang dikira setiap penternak'],
  ['Keruntuhan Selatan ialah perubahan program',
   'Tiada perubahan protokol serosurveilans Johor antara 2021 dan 2025 dalam rekod DVS']],
  [3300,6100]),
CAP('Jadual H15. Setiap tafsiran dinyatakan dalam bentuk yang boleh disangkal.'),

H1('H.14  Apa yang perlu disemak dalam rekod DVS'),
P('Lampiran ini bergantung pada kesusasteraan awam untuk mengenal pasti mekanisme. Empat ' +
  'semakan dalaman akan menukar hipotesis kepada kesimpulan.'),
bl([['Definisi pengumpulan data bagi kesepuluh aliran — khususnya sama ada ujian lapangan, ' +
  'pensampelan dan vaksinasi dikira setiap haiwan, setiap sampel, atau setiap penternak.',0]]),
bl([['Senarai kawasan berstatus: zon bebas FMD dengan vaksinasi, ladang tenusu di bawah ' +
  'uji-dan-sembelih TB, dan ladang myGAP/SALT yang diakreditasi, mengikut daerah.',0]]),
bl([['Sejarah protokol serosurveilans bagi tiga daerah Johor antara 2021 dan 2025, untuk ' +
  'mengesahkan atau menolak tafsiran keruntuhan Zon Selatan.',0]]),
bl([['Lokasi dan kapasiti makmal veterinar kawasan berbanding zon VetEC — satu-satunya ' +
  'hipotesis munasabah yang kekal belum diuji dalam siri ini.',0]]),

H1('H.15  Implikasi kepada penanda aras dan peruntukan'),

H3('Berhenti membandingkan output mentah antara zon'),
P('Ia mengukur obligasi regulatori. Zon dengan ladang tenusu diakreditasi dan status bebas ' +
  'penyakit akan sentiasa kelihatan lebih produktif tanpa mengira usahanya.'),

H3('Laporkan dua nombor, bukan satu'),
rich([['Pisahkan ',0],['kerja bermandat',1],[' (ujian lapangan, pensampelan, vaksinasi) ' +
  'daripada ',0],['kerja pengembangan',1],[' (nasihat, kesihatan gerompok, rawatan, ' +
  'pembiakbakaan, lawat siasat). Yang pertama ditentukan oleh protokol penyakit dan patut ' +
  'dilaporkan berbanding sasaran protokol. Yang kedua ialah perkara yang VetEC benar-benar ' +
  'kawal, dan di situ zon pantai timur berprestasi sama baik atau lebih baik.',0]]),

H3('Nyatakan unit sebelum menjumlahkan'),
P('Jika kesepuluh aliran hendak dijumlahkan, unitnya perlu diselaraskan atau diberi pemberat ' +
  'secara eksplisit. Jumlah tanpa pemberat pada masa ini memberi satu ujian darah berat yang ' +
  'sama dengan satu lawatan nasihat.'),

H3('Semak semula pembacaan tren 2021–2025'),
P('Penurunan 9.3% yang dilaporkan dalam laporan utama bukan kemerosotan prestasi lapangan. ' +
  'Sembilan daripada sepuluh aliran naik. Angka itu patut disertakan dengan pecahan ini ' +
  'setiap kali ia dikemukakan kepada pengurusan.'),

H1('H.16  Batasan'),
bl([['Pengenalan "ujian lapangan" sebagai serosurveilans dan ujian akreditasi ialah inferens ' +
  'daripada kesusasteraan awam dan corak data, bukan daripada definisi DVS. Ia konsisten ' +
  'dengan setiap corak yang diperiksa tetapi belum disahkan.',0]]),
bl([['Penanda "mandat" yang diuji dalam analisis ini dikodkan sebagai empat zon pantai barat ' +
  'lawan tiga zon pantai timur. Korelasinya dengan ujian lapangan (r = +0.976) oleh itu ' +
  'bulat dan TIDAK dilaporkan sebagai bukti. Bukti bukan bulat ialah bahagian lembu tenusu ' +
  '(r = +0.891) dan kesusasteraan luar.',0]]),
bl([['Dengan tujuh zon, perbandingan pantai bergantung pada empat lawan tiga cerapan. ' +
  'Nilai-p patut dibaca sebagai penunjuk arah.',0]]),
bl([['Sumber luar ialah kertas penyelidikan, dokumen WOAH dan laman web agensi. Angka ' +
  'prevalens yang dipetik merujuk tempoh sebelum panel ini (2000–2008 bagi brucellosis) ' +
  'dan digunakan untuk mengenal pasti mekanisme, bukan untuk mengukur keadaan semasa.',0]]),
bl([['Ujian musim menggunakan satu tahun data separa (2026 Jan–Apr) berbanding purata ' +
  'lima tahun. Ia menolak defisit Q1 yang besar tetapi tidak boleh menolak kesan kecil.',0]]),
bl([['Jadual ternakan yang tajuknya terpotong masih dilabel "kambing?" dan tidak digunakan ' +
  'dalam mana-mana dapatan utama Lampiran ini.',0]]),

H1('Sumber luar'),
src('Jabatan Perkhidmatan Veterinar Malaysia — direktori VetEC dan struktur bahagian',
  'https://www.dvs.gov.my/index.php/pages/view/648'),
src('WOAH — status bebas FMD Malaysia, taklimat mesyuarat jawatankuasa kebangsaan',
  'https://rr-asia.woah.org/app/uploads/2021/07/malaysia_fmd_situation_poster_24th_nc_meeting.pdf'),
src('WOAH Terrestrial Animal Health Code, Bab 8.8 — syarat serosurveilans bagi zon bebas FMD dengan vaksinasi',
  'https://www.woah.org/fileadmin/Home/eng/Health_standards/tahc/2024/en_chapitre_fmd.htm'),
src('Tuberkulosis bovin dan serodeteksi di Selangor dan Pahang, Semenanjung Malaysia',
  'https://pmc.ncbi.nlm.nih.gov/articles/PMC8636890/'),
src('Bovine brucellosis trends in Malaysia between 2000 and 2008, BMC Veterinary Research',
  'https://link.springer.com/article/10.1186/1746-6148-9-230'),
src('A Case-Control Study of Risk Factors for Bovine Brucellosis Seropositivity in Peninsular Malaysia, PLOS One',
  'https://journals.plos.org/plosone/article?id=10.1371%2Fjournal.pone.0108673'),
src('Skim Amalan Ladang Ternakan (SALT), Malaysian Agricultural Repository',
  'http://myagric.upm.edu.my/13175/'),
src('Skim Pensijilan Amalan Pertanian Baik Malaysia (myGAP), KPKM',
  'https://www.kpkm.gov.my/en/incentive-and-grant/malaysian-good-agricultural-practice-mygap'),
src('Dairy Sector in Malaysia: A Review of Policies and Programs, FFTC Agricultural Policy Platform',
  'https://ap.fftc.org.tw/article/933'),
src('Northeast Monsoon Flood 2024, Malaysian Red Crescent',
  'https://redcrescent.org.my/disaster-response/northeast-monsoon-flood-2024/'),
src('Malaysia Flood 2024 DREF Operation MDRMY011, ReliefWeb',
  'https://reliefweb.int/report/malaysia/malaysia-flood-2024-dref-operation-mdrmy011'),

new Paragraph({spacing:{before:340},
  border:{top:{style:BorderStyle.SINGLE,size:6,color:RULE}},
  children:[new TextRun({text:'Sumber data: Laporan Log Teknikal 2021–2026 (termasuk lembaran ' +
    'separa 2026 Jan–Apr); Perangkaan Ternakan Malaysia; peta zon VetEC. Lampiran E, F dan G ' +
    'ialah rujukan asas. Sumber luar disenaraikan di atas dan digunakan untuk mengenal pasti ' +
    'mekanisme, bukan untuk menggantikan rekod program DVS dalaman.',
    font:F,size:16,color:INK3,italics:true})]}),

  ]}))
});

Packer.toBuffer(doc).then(b=>{
  fs.writeFileSync('Lampiran-H-Identiti-Zon-Tidak-Diukur.docx',b);
  console.log('ditulis:',b.length,'bait');
});
