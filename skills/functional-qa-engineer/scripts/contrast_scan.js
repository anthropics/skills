() => {
  const parse = c => { const m = c.match(/rgba?\(([^)]+)\)/); if(!m) return null; const p=m[1].split(',').map(x=>parseFloat(x)); return {r:p[0],g:p[1],b:p[2],a:p.length>3?p[3]:1}; };
  const lum = ({r,g,b}) => { const f=v=>{v/=255;return v<=0.03928?v/12.92:Math.pow((v+0.055)/1.055,2.4)}; return 0.2126*f(r)+0.7152*f(g)+0.0722*f(b); };
  const bgOf = el => { let e=el; while(e){ const c=parse(getComputedStyle(e).backgroundColor); if(c&&c.a>0.5) return c; e=e.parentElement; } return {r:13,g:17,b:23,a:1}; };
  const out=[]; const seen=new Set();
  const all=[...document.querySelectorAll('body *')].filter(e=>e.offsetParent!==null && e.getBoundingClientRect().width>0);
  for(const el of all){
    const own=[...el.childNodes].filter(n=>n.nodeType===3 && n.textContent.trim()).map(n=>n.textContent.trim()).join(' ');
    if(!own) continue; const cs=getComputedStyle(el); if(cs.visibility==='hidden'||parseFloat(cs.opacity)===0) continue;
    const fg=parse(cs.color); if(!fg) continue; const bg=bgOf(el);
    const L1=lum(fg), L2=lum(bg); const cr=(Math.max(L1,L2)+0.05)/(Math.min(L1,L2)+0.05);
    const big=parseFloat(cs.fontSize)>=18.6||(parseFloat(cs.fontSize)>=14&&parseInt(cs.fontWeight)>=700);
    if(cr<(big?3:4.5)){ const k=own.slice(0,50)+cr.toFixed(1); if(seen.has(k)) continue; seen.add(k); const r=el.getBoundingClientRect(); out.push(`${cr.toFixed(2)} "${own.slice(0,60)}" fg=${cs.color} bg=rgb(${bg.r},${bg.g},${bg.b}) @${Math.round(r.x)},${Math.round(r.y)}`); }
  }
  // light surfaces left in dark mode
  const light=[]; for(const el of all){ const c=parse(getComputedStyle(el).backgroundColor); if(c&&c.a>0.5&&lum(c)>0.6){ const r=el.getBoundingClientRect(); if(r.width*r.height>2000) light.push(`${el.tagName}.${(el.className||'').toString().slice(0,40)} ${Math.round(r.width)}x${Math.round(r.height)} @${Math.round(r.x)},${Math.round(r.y)} "${(el.innerText||'').trim().slice(0,40).replace(/\n/g,' ')}"`);} }
  return 'LOWCONTRAST '+out.length+'\n'+out.slice(0,40).join('\n')+'\nLIGHT-SURFACES '+light.length+'\n'+light.slice(0,20).join('\n');
}
