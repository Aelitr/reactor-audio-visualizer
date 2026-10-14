'use strict';
const $=id=>document.getElementById(id),canvas=$('core'),g=canvas.getContext('2d'),spec=$('spectrum'),sg=spec.getContext('2d');
let ctx,analyser,splitter,analyserL,analyserR,master,muteGain,stream,source,buffer;

// 全局预初始化超高分辨率音频缓冲区 (fftSize 32768 对应缓冲区大小)
let bins = new Uint8Array(16384);
let wave = new Float32Array(32768);
let waveL = new Float32Array(16384);
let waveR = new Float32Array(16384);

let started=0,offset=0,mode='file',playing=false,loading=false,session=0,rafTime=0,angle=-.32,tilt=.58,zoom=1,drag=null,demoNodes=[],genOsc=null,gain=1.4,roentgenGain=1.0,powerGain=1.0,smoothing=.75,energy=0,current=-1,autoNext=true,isShuffle=false;
let oscResponseGain=1.0, amDepth=0.2, fmDepth=0.5, oscSpeed=1.0, oscVectorZoom=1.0; 
let oscZoom3D=1.0, oscAngleX=0.0, oscAngleY=0.0, oscDrag=null;
let osc2dPanOffset=0, oscDrag2D=null;
let oscMouseX=-1, oscMouseY=-1, oscHovered=false;
let spectrumZoom=1.0; 
let ripples = []; 
const playlist=[];
const favoritesList=[];
let lastPlayedTrackIndex = -1;
let isStoppedAndLocked = false;

const lyricFiles=[]; 
let currentLyrics=[]; 

// 动态注入主题下拉框（Select）样式修复，确保 CRT 与 EL 主题下下拉框背景与文字完美契合
const themeSelectStyleId = 'reactor-theme-select-fix';
if(!document.getElementById(themeSelectStyleId)){
  const styleEl = document.createElement('style');
  styleEl.id = themeSelectStyleId;
  styleEl.textContent = `
    body.crt-theme select, .crt-theme select {
      background-color: #141816 !important;
      color: #deec95 !important;
      border-color: #505948 !important;
    }
    body.crt-theme select option, .crt-theme select option {
      background-color: #141816 !important;
      color: #deec95 !important;
    }
    body.el-theme select, .el-theme select {
      background-color: #1a100b !important;
      color: #ffb03a !important;
      border-color: #593a26 !important;
    }
    body.el-theme select option, .el-theme select option {
      background-color: #1a100b !important;
      color: #ffb03a !important;
    }
  `;
  document.head.appendChild(styleEl);
}

const rods=[];for(let x=-15;x<=15;x++)for(let z=-15;z<=15;z++){const r=Math.hypot(x,z);if(r<=15)rods.push({x,z,r,h:0,seed:Math.abs(Math.sin(x*127.1+z*311.7)),idx:0})}
const countEl=$('count');if(countEl)countEl.textContent=rods.length;

function size(){
  for(const c of [canvas,spec]){
    if(!c)continue;
    const rect=c.getBoundingClientRect(),d=Math.min(devicePixelRatio||1,2);
    if(rect.width && rect.height){
      c.width=Math.round(rect.width*d);
      c.height=Math.round(rect.height*d);
      c.getContext('2d').setTransform(d,0,0,d,0,0);
    }
  }
}
new ResizeObserver(size).observe(canvas);
new ResizeObserver(size).observe(spec);

let cachedCosAngle = Math.cos(angle);
let cachedSinAngle = Math.sin(angle);

function point(x,z,h=0){
  const w=canvas.clientWidth,H=canvas.clientHeight,s=Math.min(w/45,H/37)*zoom;
  const rx=x*cachedCosAngle-z*cachedSinAngle;
  const rz=x*cachedSinAngle+z*cachedCosAngle;
  return [w/2+rx*s, H*.55+rz*s*tilt-h*s];
}

function poly(points,fill,stroke){g.beginPath();points.forEach((p,i)=>i?g.lineTo(...p):g.moveTo(...p));g.closePath();g.fillStyle=fill;g.fill();if(stroke){g.strokeStyle=stroke;g.lineWidth=.55;g.stroke()}}
function ring(r,color,width){g.beginPath();for(let i=0;i<=100;i++){const a=i/100*Math.PI*2,p=point(Math.cos(a)*r,Math.sin(a)*r);i?g.lineTo(...p):g.moveTo(...p)}g.strokeStyle=color;g.lineWidth=width;g.stroke()}

// ===== 点阵光圈（Aperture Dot-Matrix）绘制组件 =====
const dotCanvas=$('dot-aperture-canvas');
const dotCtx=dotCanvas?dotCanvas.getContext('2d'):null;
let lastDotRenderTime = 0;

function sizeDotCanvas(){
  if(!dotCanvas)return;
  const rect=dotCanvas.getBoundingClientRect(),d=Math.min(devicePixelRatio||1,2);
  if(rect.width && rect.height){
    dotCanvas.width=Math.round(rect.width*d);
    dotCanvas.height=Math.round(rect.height*d);
  }
}
if(dotCanvas)new ResizeObserver(sizeDotCanvas).observe(dotCanvas);

function renderDotAperture(t){
  if(!dotCanvas||!dotCtx||currentTheme!=='el')return;
  if(t - lastDotRenderTime < 45) return;
  lastDotRenderTime = t;

  const img=$('cover-img');
  if(img&&img.style.display!=='none')return;

  const w=dotCanvas.clientWidth,h=dotCanvas.clientHeight;
  if(!w||!h)return;

  dotCtx.clearRect(0,0,dotCanvas.width,dotCanvas.height);
  dotCtx.save();
  const d=Math.min(devicePixelRatio||1,2);
  dotCtx.scale(d,d);

  const cols=32, rows=32;
  const gridW=Math.min(w,h)*0.85;
  const dotStep=gridW/cols;
  const startX=(w-gridW)/2 + dotStep/2;
  const startY=(h-gridW)/2 + dotStep/2;

  const cx=cols/2, cy=rows/2;
  const rotAngle=t*0.0008;

  for(let r=0;r<rows;r++){
    for(let c=0;c<cols;c++){
      const x=c-cx+0.5, y=r-cy+0.5;
      const dist=Math.hypot(x,y);
      if(dist>14.5) continue;

      const rx=x*Math.cos(-rotAngle) - y*Math.sin(-rotAngle);
      const ry=x*Math.sin(-rotAngle) + y*Math.cos(-rotAngle);
      const angle=Math.atan2(ry,rx);

      const blades=8;
      let inBlade=false;
      const normalizedAngle=((angle % (Math.PI*2/blades)) + (Math.PI*2/blades)) % (Math.PI*2/blades);

      if(dist>3.5 && dist<=14.0){
        if(normalizedAngle > 0.15 && normalizedAngle < (Math.PI*2/blades - 0.08)){
          const lineVal = rx*Math.cos(0.4) + ry*Math.sin(0.4);
          if(lineVal > -1.5) inBlade=true;
        }
      }

      const px=startX + c*dotStep;
      const py=startY + r*dotStep;

      dotCtx.beginPath();
      dotCtx.arc(px,py,dotStep*0.35,0,Math.PI*2);
      if(inBlade){
        dotCtx.fillStyle='#ffb03a';
      }else{
        dotCtx.fillStyle='rgba(122,80,34,0.18)';
      }
      dotCtx.fill();
    }
  }
  dotCtx.restore();
}

// ===== 模拟示波器专属 Canvas 渲染 =====
const oscCanvas=$('oscilloscope-canvas');
const oscCtx=oscCanvas?oscCanvas.getContext('2d'):null;
function sizeOscCanvas(){
  if(!oscCanvas)return;
  const rect=oscCanvas.getBoundingClientRect(),d=Math.min(devicePixelRatio||1,2);
  if(rect.width && rect.height){
    oscCanvas.width=Math.round(rect.width*d);
    oscCanvas.height=Math.round(rect.height*d);
  }
}
if(oscCanvas)new ResizeObserver(sizeOscCanvas).observe(oscCanvas);

if(oscCanvas){
  oscCanvas.onpointerdown=e=>{
    const style=$('osc-style-select').value;
    if(style==='3d'){
      oscDrag={x:e.clientX,y:e.clientY};
      oscCanvas.setPointerCapture(e.pointerId);
    }else if(style==='2d'){
      oscDrag2D={x:e.clientX,y:e.clientY};
      oscCanvas.setPointerCapture(e.pointerId);
    }
  };
  oscCanvas.onpointermove=e=>{
    const rect=oscCanvas.getBoundingClientRect();
    oscMouseX = e.clientX - rect.left;
    oscMouseY = e.clientY - rect.top;
    oscHovered = true;

    if(oscDrag){
      const dx=e.clientX-oscDrag.x;
      const dy=e.clientY-oscDrag.y;
      oscAngleY += dx*0.01;
      oscAngleX -= dy*0.01;
      oscDrag={x:e.clientX,y:e.clientY};
    }else if(oscDrag2D){
      const dx=e.clientX-oscDrag2D.x;
      const baseLen=wave.length;
      const baseWindow = 4096;
      const samplesToShow = Math.max(32, Math.min(baseLen, Math.round(baseWindow / oscVectorZoom)));
      osc2dPanOffset -= (dx / oscCanvas.clientWidth) * samplesToShow;
      oscDrag2D={x:e.clientX,y:e.clientY};
    }
  };
  oscCanvas.onpointerleave=e=>{
    oscHovered=false;
  };
  oscCanvas.onpointerup=oscCanvas.onpointercancel=e=>{
    oscDrag=null;
    oscDrag2D=null;
    try{oscCanvas.releasePointerCapture(e.pointerId)}catch{}
  };
  oscCanvas.addEventListener('wheel',e=>{
    const style=$('osc-style-select').value;
    if(style==='3d'){
      e.preventDefault();
      oscZoom3D = Math.max(0.4, Math.min(3.0, oscZoom3D - e.deltaY * 0.001));
    }else if(style==='vector-music' || style==='2d' || style==='text-vector' || style==='lissajous'){
      e.preventDefault();
      const factor = e.deltaY < 0 ? 1.12 : 0.88;
      oscVectorZoom = Math.max(0.02, Math.min(50.0, oscVectorZoom * factor));
      const zoomSlider = $('osc-zoom-slider');
      if(zoomSlider) zoomSlider.value = oscVectorZoom;
    }
  },{passive:false});
}

const zoomSliderEl = $('osc-zoom-slider');
if(zoomSliderEl){
  zoomSliderEl.oninput = e => {
    oscVectorZoom = +e.target.value;
  };
}

let cachedTextPoints = null;
let lastInputText = '';

function getTextVectorPoints(text) {
  if (cachedTextPoints && lastInputText === text) return cachedTextPoints;
  lastInputText = text;
  
  const canvas = document.createElement('canvas');
  canvas.width = 280;
  canvas.height = 280;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, 280, 280);
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 2;
  ctx.font = 'bold 38px monospace';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.strokeText(text || 'REACTOR', 140, 140);

  const imgData = ctx.getImageData(0, 0, 280, 280);
  const data = imgData.data;
  const rawPoints = [];

  for (let y = 0; y < 280; y += 2) {
    for (let x = 0; x < 280; x += 2) {
      const i = (y * 280 + x) * 4;
      if (data[i] > 128) {
        rawPoints.push({x: (x - 140) / 110, y: (y - 140) / 110});
      }
    }
  }

  if (rawPoints.length === 0) {
    cachedTextPoints = [{x: 0, y: 0}];
    return cachedTextPoints;
  }

  const ordered = [rawPoints[0]];
  rawPoints.splice(0, 1);

  while (rawPoints.length > 0 && ordered.length < 1500) {
    const current = ordered[ordered.length - 1];
    let nearestIdx = 0;
    let minDist = Infinity;
    for (let i = 0; i < rawPoints.length; i++) {
      const p = rawPoints[i];
      const dist = (p.x - current.x) ** 2 + (p.y - current.y) ** 2;
      if (dist < minDist) {
        minDist = dist;
        nearestIdx = i;
      }
    }
    ordered.push(rawPoints[nearestIdx]);
    rawPoints.splice(nearestIdx, 1);
  }

  cachedTextPoints = ordered;
  return cachedTextPoints;
}

const oscStyleSelect = $('osc-style-select');
if(oscStyleSelect){
  oscStyleSelect.onchange = e => {
    const val = e.target.value;
    const lissajousCtrl = $('lissajous-controls');
    const textLabel = $('osc-text-label');
    if(lissajousCtrl) lissajousCtrl.style.display = val === 'lissajous' ? 'flex' : 'none';
    if(textLabel) textLabel.style.display = val === 'text-vector' ? 'flex' : 'none';
  };
}

// 毫秒级时间格式化辅助函数
function formatMillis(s){
  if(isNaN(s)||s<0)s=0;
  const m=Math.floor(s/60);
  const sec=Math.floor(s%60);
  const ms=Math.floor((s%1)*1000);
  return m.toString().padStart(2,'0')+':'+sec.toString().padStart(2,'0')+'.'+ms.toString().padStart(3,'0');
}

function renderOscilloscope(t){
  if(!oscCanvas||!oscCtx)return;
  const w=oscCanvas.clientWidth,h=oscCanvas.clientHeight;
  if(!w||!h)return;
  oscCtx.save();
  const d=Math.min(devicePixelRatio||1,2);
  oscCtx.scale(d,d);

  oscCtx.fillStyle='#141816';
  oscCtx.fillRect(0,0,w,h);

  oscCtx.strokeStyle='rgba(80, 92, 66, 0.35)';
  oscCtx.lineWidth=1;
  oscCtx.beginPath();
  for(let x=0;x<w;x+=w/8){oscCtx.moveTo(x,0);oscCtx.lineTo(x,h);}
  for(let y=0;y<h;y+=h/6){oscCtx.moveTo(0,y);oscCtx.lineTo(w,y);}
  oscCtx.stroke();

  oscCtx.strokeStyle='rgba(163, 184, 140, 0.2)';
  oscCtx.beginPath();
  oscCtx.moveTo(w/2,0);oscCtx.lineTo(w/2,h);
  oscCtx.moveTo(0,h/2);oscCtx.lineTo(w,h/2);
  oscCtx.stroke();

  const style=$('osc-style-select').value;
  const isActuallyPlaying=playing&&(mode==='file'||mode==='generator'||mode==='system');
  const holdEnabled=$('osc-hold-freeze')?.checked ?? true;
  const isPlaying = isActuallyPlaying || holdEnabled;
  const dynEnergy = (isPlaying && energy) ? energy * oscResponseGain * 3.5 : 0.1;
  const effTime = t * oscSpeed;

  if(style==='text-vector'){
    const textInput = $('osc-text-input');
    const textVal = textInput ? textInput.value : 'REACTOR';
    const points = getTextVectorPoints(textVal);

    oscCtx.beginPath();
    oscCtx.lineWidth=1.8;
    oscCtx.shadowBlur=8;
    oscCtx.shadowColor='#deec95';
    oscCtx.strokeStyle='#deec95';

    const invertX = $('osc-invert-x')?.checked ?? false;
    const invertY = $('osc-invert-y')?.checked ?? false;

    for(let i=0; i<points.length; i++){
      const pt = points[i];
      const xVal = Math.max(-1.0, Math.min(1.0, pt.x * oscVectorZoom));
      const yVal = Math.max(-1.0, Math.min(1.0, pt.y * oscVectorZoom));

      const finalX = invertX ? -xVal : xVal;
      const finalY = invertY ? -yVal : yVal;

      const px = w / 2 + finalX * (w * 0.42);
      const py = h / 2 + finalY * (h * 0.42);

      if(i === 0){oscCtx.moveTo(px, py);}else{oscCtx.lineTo(px, py);}
    }
    oscCtx.stroke();
    oscCtx.shadowBlur=0;

  } else if(style==='lissajous'){
    const fx = parseFloat($('lissajous-fx')?.value) || 1;
    const fy = parseFloat($('lissajous-fy')?.value) || 2;
    const phase = parseFloat($('lissajous-phase')?.value) ?? 1.57;

    oscCtx.beginPath();
    oscCtx.lineWidth=1.8;
    oscCtx.shadowBlur=8;
    oscCtx.shadowColor='#deec95';
    oscCtx.strokeStyle='#deec95';

    const points = 700;
    const invertX = $('osc-invert-x')?.checked ?? false;
    const invertY = $('osc-invert-y')?.checked ?? false;
    const audioMod = (isActuallyPlaying && energy) ? (1.0 + energy * 0.8 * oscResponseGain) : 1.0;

    for(let i = 0; i <= points; i++){
      const theta = (i / points) * Math.PI * 2;
      const timeMod = isActuallyPlaying ? effTime * 0.002 : 0;

      const xVal = Math.sin(theta * fx + timeMod) * oscVectorZoom * 0.7 * audioMod;
      const yVal = Math.sin(theta * fy + phase + timeMod) * oscVectorZoom * 0.7 * audioMod;

      const finalX = invertX ? -xVal : xVal;
      const finalY = invertY ? -yVal : yVal;

      const px = w / 2 + finalX * (w * 0.42);
      const py = h / 2 + finalY * (h * 0.42);

      if(i === 0){oscCtx.moveTo(px, py);}else{oscCtx.lineTo(px, py);}
    }
    oscCtx.stroke();
    oscCtx.shadowBlur=0;

  } else if(style==='vector-music'){
    if(analyserL && analyserR && isActuallyPlaying){
      analyserL.getFloatTimeDomainData(waveL);
      analyserR.getFloatTimeDomainData(waveR);
    } else if(!isActuallyPlaying && holdEnabled && window._lastWaveL && window._lastWaveR){
    } else {
      for(let i=0;i<waveL.length;i++){
        const phase = i * 0.02 + effTime * 0.002;
        waveL[i] = Math.sin(phase * 3) * Math.cos(effTime*0.001)*0.7;
        waveR[i] = Math.cos(phase * 2) * Math.sin(effTime*0.001)*0.7;
      }
    }
    if(isActuallyPlaying && waveL){
      window._lastWaveL = new Float32Array(waveL);
      window._lastWaveR = new Float32Array(waveR);
    }
    const targetWaveL = (!isActuallyPlaying && holdEnabled && window._lastWaveL) ? window._lastWaveL : waveL;
    const targetWaveR = (!isActuallyPlaying && holdEnabled && window._lastWaveR) ? window._lastWaveR : waveR;

    let startIndex = window._lastStartIndex || 0;
    if(isPlaying && targetWaveL){
      let bestIdx = 0;
      let found = false;
      for(let i = 0; i < targetWaveL.length - 20; i++){
        if(targetWaveL[i] <= 0 && targetWaveL[i+1] > 0 && (targetWaveL[i+2] - targetWaveL[i]) > 0.005){
          bestIdx = i;
          found = true;
          break;
        }
      }
      if(found){
        startIndex = Math.round(startIndex * 0.7 + bestIdx * 0.3);
      } else {
        startIndex = 0;
      }
      window._lastStartIndex = startIndex;
    }

    oscCtx.beginPath();
    oscCtx.lineWidth=1.8;
    oscCtx.shadowBlur=8;
    oscCtx.shadowColor='#deec95';
    oscCtx.strokeStyle='#deec95';

    const maxPoints = 900;
    const len = Math.min(targetWaveL.length, startIndex + maxPoints);
    
    const invertX = $('osc-invert-x')?.checked ?? false;
    const invertY = $('osc-invert-y')?.checked ?? false;

    let plottedCount = 0;
    for(let i = startIndex; i < len; i++){
      const xVal = Math.max(-1.0, Math.min(1.0, targetWaveL[i] * (1.0 + amDepth) * oscResponseGain));
      const yVal = Math.max(-1.0, Math.min(1.0, targetWaveR[i] * (1.0 + fmDepth) * oscResponseGain));

      const finalX = invertX ? -xVal : xVal;
      const finalY = invertY ? -yVal : yVal;

      const px = w / 2 + finalX * (w * 0.42 * oscVectorZoom);
      const py = h / 2 + finalY * (h * 0.42 * oscVectorZoom);

      if(plottedCount === 0){
        oscCtx.moveTo(px, py);
      }else{
        oscCtx.lineTo(px, py);
      }
      plottedCount++;
    }
    oscCtx.stroke();
    oscCtx.shadowBlur=0;

  } else if(style==='2d'){
    if(analyser&&isActuallyPlaying){
      analyser.getFloatTimeDomainData(wave);
    } else if(!isActuallyPlaying && holdEnabled && window._lastWave){
    } else {
      for(let i=0;i<wave.length;i++){
        wave[i]=Math.sin(i*0.05)*0.5;
      }
    }
    if(isActuallyPlaying && wave){
      window._lastWave = new Float32Array(wave);
    }
    const targetWave = (!isActuallyPlaying && holdEnabled && window._lastWave) ? window._lastWave : wave;

    oscCtx.beginPath();
    oscCtx.lineWidth=1.5;
    oscCtx.strokeStyle='#deec95';
    
    const baseLen = targetWave.length;
    const baseWindow = 4096;
    const samplesToShow = Math.max(32, Math.min(baseLen, Math.round(baseWindow / oscVectorZoom)));
    
    let startIdx = 0;
    if(isPlaying && targetWave && samplesToShow <= 2048){
      for(let i = 0; i < samplesToShow / 2; i++){
        if(targetWave[i] <= 0 && targetWave[i+1] > 0){
          startIdx = i;
          break;
        }
      }
    } else {
      startIdx = 0;
    }

    const sliceWidth = w / samplesToShow;
    const invertX = $('osc-invert-x')?.checked ?? false;
    const invertY = $('osc-invert-y')?.checked ?? false;

    const step = Math.max(1, Math.floor(samplesToShow / w));

    let plottedCount = 0;
    for(let i = 0; i < samplesToShow; i += step){
      const dataIdx = (startIdx + Math.round(osc2dPanOffset) + i + baseLen * 1000) % baseLen;
      let v = targetWave[dataIdx];
      v = Math.max(-1.1, Math.min(1.1, v));

      const finalYVal = invertY ? -v : v;
      const px = invertX ? (w - i * sliceWidth) : (i * sliceWidth);
      const py = h / 2 - finalYVal * (h * 0.38);

      if(plottedCount === 0){
        oscCtx.moveTo(px, py);
      }else{
        oscCtx.lineTo(px, py);
      }
      plottedCount++;
    }
    oscCtx.stroke();

    // 2D 波形鼠标悬停实时探测与瞬时电压、毫秒级音频时间显示
    if(oscHovered && oscMouseX >= 0 && oscMouseX <= w && oscMouseY >= 0 && oscMouseY <= h){
      const hoveredI = invertX ? Math.round((w - oscMouseX) / sliceWidth) : Math.round(oscMouseX / sliceWidth);
      if(hoveredI >= 0 && hoveredI < samplesToShow){
        const dataIdx = (startIdx + Math.round(osc2dPanOffset) + hoveredI + baseLen * 1000) % baseLen;
        let v = targetWave[dataIdx];
        v = Math.max(-1.1, Math.min(1.1, v));
        const finalYVal = invertY ? -v : v;
        const px = invertX ? (w - hoveredI * sliceWidth) : (hoveredI * sliceWidth);
        const py = h / 2 - finalYVal * (h * 0.38);

        // 计算精确到毫秒的对应音频时间
        const sampleRate = ctx ? ctx.sampleRate : 44100;
        const currentPlaybackTime = (playing && mode==='file' && buffer) ? (offset + ctx.currentTime - started) : offset;
        const sampleTimeOffset = (hoveredI - startIdx) / sampleRate;
        const exactTimeSec = Math.max(0, currentPlaybackTime + sampleTimeOffset);
        const timeStr = formatMillis(exactTimeSec);

        // 垂直探针指示线
        oscCtx.strokeStyle='rgba(255, 176, 58, 0.85)';
        oscCtx.lineWidth=1;
        oscCtx.setLineDash([3, 3]);
        oscCtx.beginPath();
        oscCtx.moveTo(px, 0);
        oscCtx.lineTo(px, h);
        oscCtx.stroke();
        oscCtx.setLineDash([]);

        // 交点高亮圆点
        oscCtx.beginPath();
        oscCtx.arc(px, py, 4.5, 0, Math.PI * 2);
        oscCtx.fillStyle='#ffb03a';
        oscCtx.fill();
        oscCtx.strokeStyle='#141816';
        oscCtx.lineWidth=1.5;
        oscCtx.stroke();

        // 瞬时电压与毫秒级时间悬浮窗
        const tooltipX = Math.min(w - 195, Math.max(10, px + 12));
        const tooltipY = Math.max(10, Math.min(h - 80, py - 48));

        oscCtx.fillStyle='rgba(20, 24, 22, 0.94)';
        oscCtx.strokeStyle='rgba(222, 236, 149, 0.7)';
        oscCtx.lineWidth=1;
        oscCtx.fillRect(tooltipX, tooltipY, 195, 76);
        oscCtx.strokeRect(tooltipX, tooltipY, 195, 76);

        oscCtx.fillStyle='#deec95';
        oscCtx.font='10px monospace';
        oscCtx.textAlign='left';
        oscCtx.textBaseline='top';
        oscCtx.fillText(`[2D WAVEFORM PROBE]`, tooltipX + 8, tooltipY + 6);
        oscCtx.fillText(`采样点索引: #${dataIdx}`, tooltipX + 8, tooltipY + 20);
        oscCtx.fillText(`瞬时电压: ${v >= 0 ? '+' : ''}${v.toFixed(4)} V`, tooltipX + 8, tooltipY + 34);
        oscCtx.fillText(`音频时间: ${timeStr}`, tooltipX + 8, tooltipY + 48);
      }
    }
  } else {
    const rotSpeed = effTime * 0.0015;
    const freqMod = (isPlaying && energy) ? (2.0 + dynEnergy * 3.0 * fmDepth) : 2.0;
    
    oscCtx.beginPath();
    oscCtx.lineWidth=1.8;
    oscCtx.shadowBlur=8;
    oscCtx.shadowColor='#deec95';
    oscCtx.strokeStyle='#deec95';

    const points=180;
    for(let i=0;i<=points;i++){
      const theta=(i/points)*Math.PI*2;
      const binVal = (isPlaying && bins) ? bins[i%bins.length]/255 : 0.5;
      
      const amEnvelope = 1.0 + amDepth * Math.cos(theta * 4 + effTime * 0.002);
      const r = (50 + binVal * 40 * oscResponseGain) * amEnvelope * oscZoom3D;
      
      const fmPhaseShift = fmDepth * Math.sin(theta * 3 + effTime * 0.003) * (1.0 + dynEnergy);
      
      let x3d = r * Math.cos(theta + fmPhaseShift) * freqMod * 0.7;
      let y3d = r * Math.sin(theta * 2 + fmPhaseShift);
      let z3d = r * Math.sin(theta);

      let cosX = Math.cos(oscAngleX), sinX = Math.sin(oscAngleX);
      let y1 = y3d * cosX - z3d * sinX;
      let z1 = y3d * sinX + z3d * cosX;
      let x1 = x3d;

      let cosY = Math.cos(oscAngleY + rotSpeed), sinY = Math.sin(oscAngleY + rotSpeed);
      let x2 = x1 * cosY + z1 * sinY;
      let z2 = -x1 * sinY + z1 * cosY;
      let y2 = y1;

      const fov=200;
      const scale=fov/(fov+z2+100);
      const px = w/2 + x2 * scale;
      const py = h/2 + y2 * scale;

      if(i===0){oscCtx.moveTo(px,py)}else{oscCtx.lineTo(px,py)}
    }
    oscCtx.stroke();
    oscCtx.shadowBlur=0;
  }

  oscCtx.restore();
}

// ===== 频谱窗口滚轮缩放分辨率/频段跨度监听 =====
const spectrumWindowEl = $('spectrum-window');
if(spectrumWindowEl){
  spectrumWindowEl.addEventListener('wheel', e => {
    e.preventDefault();
    spectrumZoom = Math.max(0.4, Math.min(3.0, spectrumZoom - e.deltaY * 0.001));
  }, {passive:false});
}

// ===== IndexedDB 持久化缓存 =====
const DB_NAME='ReactorAudioCacheDB';
const STORE_NAME='cacheStore';

function openCacheDB(){
  return new Promise((resolve,reject)=>{
    const req=indexedDB.open(DB_NAME,2);
    req.onupgradeneeded=e=>{
      const db=e.target.result;
      if(!db.objectStoreNames.contains(STORE_NAME)){
        db.createObjectStore(STORE_NAME);
      }
    };
    req.onsuccess=e=>resolve(e.target.result);
    req.onerror=e=>reject(e.target.error);
  });
}

function saveToCache(key,value){
  return new Promise(async(resolve,reject)=>{
    try{
      const db=await openCacheDB();
      const tx=db.transaction(STORE_NAME,'readwrite');
      tx.objectStore(STORE_NAME).put(value,key);
      tx.oncomplete=()=>resolve(true);
      tx.onerror=e=>reject(e.target.error);
    }catch(e){reject(e)}
  });
}

async function loadFromCache(key){
  try{
    const db=await openCacheDB();
    return new Promise(resolve=>{
      const tx=db.transaction(STORE_NAME,'readonly');
      const req=tx.objectStore(STORE_NAME).get(key);
      req.onsuccess=e=>resolve(e.target.result);
      req.onerror=()=>resolve(null);
    });
  }catch(e){return null}
}

async function persistState(){
  try{
    const serializablePlaylist=playlist.map(item=>({
      name:item.name,
      blob:item.file instanceof Blob ? item.file : null,
      duration:item.duration,
      lyrics:item.lyrics,
      lyricName:item.lyricName,
      isFavorite:item.isFavorite
    }));
    await saveToCache('playlist',serializablePlaylist);
    await saveToCache('lyricFiles',lyricFiles);
    await saveToCache('lastPlayedIndex', current);
  }catch(e){console.error('持久化缓存失败',e)}
}

// ===== 主题切换逻辑与光圈图标定义 =====
const themeSwitchBtn=$('theme-switch-btn');
let currentTheme=localStorage.getItem('reactor_theme')||'crt';

const apertureSVG=`<svg viewBox="0 0 100 100"><path d="M50 0 A50 50 0 1 0 100 50 A50 50 0 0 0 50 0 Z M50 12 A38 38 0 0 1 83 32 L58 41 L50 12 Z M86 36 A38 38 0 0 1 88 64 L65 52 L86 36 Z M85 68 A38 38 0 0 1 59 87 L52 61 L85 68 Z M55 88 A38 38 0 0 1 23 72 L45 61 L55 88 Z M19 68 A38 38 0 0 1 13 39 L37 50 L19 68 Z M15 35 A38 38 0 0 1 40 14 L48 40 L15 35 Z"/></svg>`;

function applyTheme(themeName){
  currentTheme=themeName;
  localStorage.setItem('reactor_theme', themeName);
  const oscTab=$('oscilloscope-tab-btn');
  const oscWindow=$('oscilloscope-window');
  const brandIcon=$('brand-icon-container');
  const dotCanvasEl=$('dot-aperture-canvas');
  const emptyCover=$('cover-empty');

  if(themeName==='el'){
    document.body.classList.replace('crt-theme', 'el-theme') || document.body.classList.add('el-theme');
    themeSwitchBtn.className='theme-switch-btn el';
    themeSwitchBtn.textContent='我们的现在';
    if(oscTab) oscTab.style.display='none';
    if(oscWindow) oscWindow.style.display='none';
    if(brandIcon) brandIcon.innerHTML=apertureSVG;
    if(dotCanvasEl) dotCanvasEl.style.display='block';
    if(emptyCover) emptyCover.querySelector('.crt-blank-text').style.display='none';
  }else{
    document.body.classList.replace('el-theme', 'crt-theme') || document.body.classList.add('crt-theme');
    themeSwitchBtn.className='theme-switch-btn crt';
    themeSwitchBtn.textContent='我们原本的未来';
    if(oscTab) oscTab.style.display='inline-block';
    if(brandIcon) brandIcon.textContent='▦';
    if(dotCanvasEl) dotCanvasEl.style.display='none';
    if(emptyCover) emptyCover.querySelector('.crt-blank-text').style.display='inline-block';
  }
}
applyTheme(currentTheme);

themeSwitchBtn.onclick=()=>{
  applyTheme(currentTheme==='crt'?'el':'crt');
};

async function extractFlacCover(file){
  try{
    const buffer=await file.arrayBuffer();
    const view=new DataView(buffer);
    if(view.getUint32(0,false)!==0x664c6143)return null;
    let offset=4;
    let isLast=false;
    while(!isLast&&offset<view.byteLength){
      const header=view.getUint8(offset);
      isLast=(header&0x80)!==0;
      const type=header&0x7f;
      const length=(view.getUint8(offset+1)<<16)|(view.getUint8(offset+2)<<8)|view.getUint8(offset+3);
      offset+=4;
      if(type===6){
        const mimeLen=view.getUint32(offset+4,false);
        let subOffset=offset+8;
        let mimeString='';
        for(let i=0;i<mimeLen;i++){mimeString+=String.fromCharCode(view.getUint8(subOffset+i))}
        subOffset+=mimeLen;
        const descLen=view.getUint32(subOffset,false);
        subOffset+=4+descLen+16;
        const dataLen=view.getUint32(subOffset,false);
        subOffset+=4;
        const imgBytes=new Uint8Array(buffer,subOffset,dataLen);
        const blob=new Blob([imgBytes],{type:mimeString||'image/jpeg'});
        return URL.createObjectURL(blob);
      }
      offset+=length;
    }
  }catch(e){console.error('FLAC 封面解析异常',e)}
  return null;
}

function parseLrc(content){
  const lines=content.split(/\r?\n/);
  const result=[];
  const timeRegex=/\[(\d{2}):(\d{2})(?:\.(\d{2,3}))?\]/g;
  for(const line of lines){
    timeRegex.lastIndex=0;
    let match;
    const timestamps=[];
    let text=line;
    while((match=timeRegex.exec(line))!==null){
      const min=parseInt(match[1],10);
      const sec=parseInt(match[2],10);
      const ms=match[3]?parseInt(match[3].padEnd(3,'0').slice(0,3),10):0;
      timestamps.push(min*60+sec+ms/1000);
      text=line.slice(timeRegex.lastIndex);
    }
    text=text.trim();
    if(timestamps.length>0&&text){for(const t of timestamps){result.push({time:t,text})}}
  }
  result.sort((a,b)=>a.time-b.time);
  return result;
}

function autoMatchLyricsForTrack(item){
  if(!item)return;
  const cleanTrackName=item.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
  let bestMatch=null;
  for(const lf of lyricFiles){
    const cleanLyricName=lf.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
    if(cleanTrackName===cleanLyricName || cleanTrackName.includes(cleanLyricName) || cleanLyricName.includes(cleanTrackName)){
      bestMatch=lf;
      break;
    }
  }
  if(bestMatch){item.lyrics=bestMatch.parsed;item.lyricName=bestMatch.name}
}

function updateLyricsDisplay(currentTime){
  const container=$('lyrics-container');
  if(!currentLyrics||currentLyrics.length===0){
    container.innerHTML='<div class="rw-empty lyrics-prompt-empty">待导入</div>';
    return;
  }
  let idx=-1;
  for(let i=0;i<currentLyrics.length;i++){if(currentTime>=currentLyrics[i].time){idx=i}else{break}}

  let html='';
  const range=5;
  const start=Math.max(0,(idx===-1?0:idx)-range);
  const end=Math.min(currentLyrics.length-1,(idx===-1?0:idx)+range);
  const activeIdx=idx===-1?0:idx;

  for(let i=start;i<=end;i++){
    let className='lyric-line-item';
    const dist=Math.abs(i-activeIdx);
    if(i===activeIdx){
      className+=' current';
    }else if(dist<=2){
      className+=' near';
    }
    html+=`<div class="${className}" data-time="${currentLyrics[i].time}">${currentLyrics[i].text}</div>`;
  }
  container.innerHTML=html;

  const currentEl=container.querySelector('.lyric-line-item.current');
  if(currentEl){
    container.scrollTo({
      top:currentEl.offsetTop-container.clientHeight/2+currentEl.clientHeight/2,
      behavior:'smooth'
    });
  }
}

function seekToTime(targetTime){
  if(mode==='file'&&buffer){
    targetTime=Math.max(0,Math.min(buffer.duration,targetTime));
    const was=playing;
    stop();
    offset=targetTime;
    $('elapsed').textContent=format(offset);
    $('seek').value=(offset/buffer.duration)*100;
    if(was)start();
  }else{
    offset=Math.max(0,targetTime);
    $('elapsed').textContent=format(offset);
  }
}

$('lyrics-container').onclick=e=>{
  const lineEl=e.target.closest('.lyric-line-item');
  if(!lineEl)return;
  const time=parseFloat(lineEl.getAttribute('data-time'));
  if(!isNaN(time)){
    seekToTime(time);
  }
};

const trackSpecCanvas=$('track-spectrum');
const tsg=trackSpecCanvas.getContext('2d');
function sizeTrackSpec(){
  if(!trackSpecCanvas)return;
  const rect=trackSpecCanvas.getBoundingClientRect(),d=Math.min(devicePixelRatio||1,2);
  if(rect.width && rect.height){
    trackSpecCanvas.width=Math.round(rect.width*d);
    trackSpecCanvas.height=Math.round(rect.height*d);
  }
}
new ResizeObserver(sizeTrackSpec).observe(trackSpecCanvas);

function renderTrackSpectrum(){
  const sw=trackSpecCanvas.clientWidth,sh=trackSpecCanvas.clientHeight;
  if(!sw||!sh)return;
  tsg.clearRect(0,0,trackSpecCanvas.width,trackSpecCanvas.height);
  tsg.save();
  const d=Math.min(devicePixelRatio||1,2);
  tsg.scale(d,d);

  const style=$('spectrum-style').value;
  const isActuallyPlaying=playing&&(mode==='file'||mode==='generator'||mode==='system');
  const holdEnabled=$('osc-hold-freeze')?.checked ?? true;
  const isPlaying = isActuallyPlaying || holdEnabled;

  if(!isPlaying||!analyser){
    if(currentTheme==='el'){
      tsg.beginPath();
      tsg.lineWidth=1.5;
      tsg.strokeStyle='#ffb03a';
      tsg.moveTo(0, sh/2);
      tsg.lineTo(sw, sh/2);
      tsg.stroke();
    }
    tsg.restore();
    return;
  }

  if(style==='bars'){
    if(isActuallyPlaying && analyser){
      analyser.getByteFrequencyData(bins);
      window._lastBins = new Uint8Array(bins);
    }
    const targetBins = (!isActuallyPlaying && holdEnabled && window._lastBins) ? window._lastBins : bins;

    const barCount=36;
    const maxBinIdx=Math.min(targetBins.length, Math.floor((targetBins.length / 2) / spectrumZoom));
    const barWidth=sw/barCount;
    for(let i=0;i<barCount;i++){
      const idx=Math.min(targetBins.length - 1, Math.floor((i/barCount)*maxBinIdx));
      const val=targetBins[idx]/255;
      const h=val*(sh-10);
      tsg.fillStyle=currentTheme==='el'?(i<barCount*0.35?'#ff8800':i<barCount*0.75?'#ffaa22':'#ffb03a'):(i<barCount*0.35?'#d8b975':i<barCount*0.75?'#c3cf87':'#deec95');
      tsg.fillRect(i*barWidth+1,sh-h-2,Math.max(2,barWidth-2),Math.max(2,h));
    }
  }else{
    if(isActuallyPlaying && analyser){
      analyser.getFloatTimeDomainData(wave);
      window._lastWaveSpec = new Float32Array(wave);
    }
    const targetWaveSpec = (!isActuallyPlaying && holdEnabled && window._lastWaveSpec) ? window._lastWaveSpec : wave;

    tsg.beginPath();
    tsg.lineWidth=1.5;
    tsg.strokeStyle=currentTheme==='el'?'#ffb03a':'#deec95';
    
    const baseLen = targetWaveSpec.length;
    const sampleLen = Math.max(32, Math.min(baseLen, Math.round(baseLen / spectrumZoom)));
    const sliceWidth = sw / sampleLen;
    let x=0;
    for(let i=0;i<sampleLen;i++){
      const v = targetWaveSpec[Math.min(baseLen - 1, i)] || 0;
      const y=(v*0.5+0.5)*sh;
      if(i===0){tsg.moveTo(x,y)}else{tsg.lineTo(x,y)}
      x+=sliceWidth;
    }
    tsg.stroke();
  }
  tsg.restore();
}

let lastDOMUpdateTime = 0;

function frame(t){
  const dt=Math.min((t-rafTime)/16.67,3)||1;
  rafTime=t;
  const w=canvas.clientWidth,H=canvas.clientHeight;
  g.clearRect(0,0,w,H);
  
  cachedCosAngle = Math.cos(angle);
  cachedSinAngle = Math.sin(angle);

  const isActuallyPlaying=playing&&(mode==='file'||mode==='generator'||mode==='system');
  const holdEnabled=$('osc-hold-freeze')?.checked ?? true;

  if(analyser&&isActuallyPlaying){
    analyser.getByteFrequencyData(bins);
    window._lastBinsRod = new Uint8Array(bins);
  }
  const targetBinsRod = (!isActuallyPlaying && holdEnabled && window._lastBinsRod) ? window._lastBinsRod : bins;

  let sum=0,peak=0,peakIndex=0;
  if(targetBinsRod)for(let i=0;i<targetBinsRod.length;i++){sum+=targetBinsRod[i];if(targetBinsRod[i]>peak){peak=targetBinsRod[i];peakIndex=i}}
  energy=0;
  if(isActuallyPlaying&&wave){
    analyser.getFloatTimeDomainData(wave);
    window._lastWaveCore = new Float32Array(wave);
  }
  const targetWaveCore = (!isActuallyPlaying && holdEnabled && window._lastWaveCore) ? window._lastWaveCore : wave;
  if(targetWaveCore){for(const v of targetWaveCore)energy+=v*v;energy=Math.sqrt(energy/targetWaveCore.length)}
  
  ring(16.4,currentTheme==='el'?'#110c08':'#060b07',20);ring(16.5,currentTheme==='el'?'#593a26':'#505948',2);ring(16,currentTheme==='el'?'#8c6448':'#878969',1);ring(17.3,currentTheme==='el'?'#382419':'#303a2d',1);
  for(let i=0;i<80;i++){const a=i/80*Math.PI*2;poly([point(Math.cos(a)*15.7,Math.sin(a)*15.7),point(Math.cos(a+.034)*15.7,Math.sin(a+.034)*15.7),point(Math.cos(a+.034)*16.15,Math.sin(a+.034)*16.15),point(Math.cos(a)*16.15,Math.sin(a)*16.15)],i%2?(currentTheme==='el'?'#483120':'#484d31'):(currentTheme==='el'?'#9e6c43':'#adac64'))}
  
  rods.sort((a,b)=>(a.x*cachedSinAngle+a.z*cachedCosAngle)-(b.x*cachedSinAngle+b.z*cachedCosAngle));
  for(const rod of rods){
    let amp=0;
    if(isActuallyPlaying && targetBinsRod){
      const hz=45*Math.pow(320,rod.r/15),idx=Math.max(1,Math.min(targetBinsRod.length-2,Math.round(hz/(ctx?ctx.sampleRate/analyser.fftSize:22050))));
      rod.idx=idx;amp=(targetBinsRod[idx]+targetBinsRod[idx-1]+targetBinsRod[idx+1])/765;amp=Math.pow(amp,1.7)*gain;
    }else if(!isActuallyPlaying && ripples.length > 0){
      const now = performance.now();
      let rippleAmp = 0;
      ripples = ripples.filter(r => now - r.startTime < 1600);
      for(const r of ripples){
        const elapsed = (now - r.startTime) * 0.0035;
        const distToRipple = Math.hypot(rod.x - r.x, rod.z - r.z);
        const waveRadius = elapsed * 16;
        const waveWidth = 2.5;
        if(Math.abs(distToRipple - waveRadius) < waveWidth){
          const attenuation = Math.max(0, 1 - (now - r.startTime) / 1600);
          rippleAmp += (1 - Math.abs(distToRipple - waveRadius) / waveWidth) * 1.5 * attenuation;
        }
      }
      amp = rippleAmp * gain;
    }else if(!playing&&holdEnabled&&rod.lastAmp!==undefined){
      amp=rod.lastAmp;
    }else{
      amp=0;
    }
    rod.lastAmp=amp;
    const target=.07+amp*4.8;rod.h+=(target-rod.h)*(1-Math.pow(.45+smoothing*.53,dt));
    const {x,z,h}=rod,a=point(x-.44,z-.44,h),b=point(x+.44,z-.44,h),c=point(x+.44,z+.44,h),d=point(x-.44,z+.44,h),a0=point(x-.44,z-.44),b0=point(x+.44,z-.44),c0=point(x+.44,z+.44),d0=point(x-.44,z+.44);
    poly([a,a0,b0,b],currentTheme==='el'?'#38281d':'#424838',currentTheme==='el'?'#140d0a':'#111910');
    poly([b,b0,c0,c],currentTheme==='el'?`rgb(${55+amp*40},${42+amp*25},${25+amp*10})`:`rgb(${55+amp*30},${62+amp*30},${44+amp*20})`,currentTheme==='el'?'#1a100b':'#141b12');
    poly([c,c0,d0,d],currentTheme==='el'?'#2e2017':'#333c2b',currentTheme==='el'?'#150e0a':'#131b11');
    poly([d,d0,a0,a],currentTheme==='el'?'#33241b':'#39432f',currentTheme==='el'?'#120c08':'#111910');
    const base=rod.seed>.92?[143,109,81]:rod.seed>.85?[97,118,104]:[139+rod.seed*29,148+rod.seed*22,119+rod.seed*21];
    poly([a,b,c,d],currentTheme==='el'?`rgb(${140+amp*75},${80+amp*45},${20+amp*10})`:`rgb(${base[0]+amp*43},${base[1]+amp*40},${base[2]+amp*24})`,currentTheme==='el'?'#2b1c12':'#232d20');
    const p=point(x,z,h+.01),s=Math.min(w/45,H/37)*zoom;g.beginPath();g.ellipse(p[0],p[1],s*.12,s*.12*tilt,0,0,Math.PI*2);
    g.fillStyle=currentTheme==='el'?'#38281d':'#404735';g.fill();if(s>13&&rod.seed>.6){g.fillStyle=currentTheme==='el'?'#ffd499':'#c3c7a3';g.fillRect(p[0]-s*.3,p[1]-s*.19,1,1)}
  }

  const sw=spec.clientWidth,sh=spec.clientHeight;
  sg.clearRect(0,0,sw,sh);
  for(let i=0;i<48;i++){
    let v=(isPlayableOrHold(isActuallyPlaying,holdEnabled)&&targetBinsRod)?targetBinsRod[Math.min(targetBinsRod.length-1,Math.floor(Math.pow(i/47,2)*700))]/255:0;
    sg.fillStyle=currentTheme==='el'?(i<12?'#ff6600':i<30?'#ff9933':'#ffb03a'):(i<12?'#d8b975':i<30?'#c3cf87':'#95b1a1');
    sg.fillRect(i*sw/48,sh-Math.max(2,v*sh),sw/48-3,Math.max(2,v*sh))
  }

  renderTrackSpectrum();
  renderOscilloscope(t);
  renderDotAperture(t);

  let power=666;
  let roentgenVal = 0.1;

  if(isStoppedAndLocked){
    power = 99999;
    roentgenVal = 3.6;
  } else {
    if(isPlayableOrHold(isActuallyPlaying,holdEnabled)&&analyser){
      const peakRatio = peak ? peak / 255 : 0;
      const dynamicFactor = Math.pow(Math.max(energy * 2.2 * powerGain, peakRatio * powerGain), 1.55);
      power = Math.min(99999, Math.round(400 + dynamicFactor * 99599));
    }
    if(isPlayableOrHold(isActuallyPlaying,holdEnabled)&&analyser){
      const peakRatio = peak ? peak / 255 : 0;
      const dynamicFactor = Math.pow(Math.max(energy * 2.0 * roentgenGain, peakRatio * roentgenGain), 1.5);
      roentgenVal = 0.1 + Math.min(3.5, dynamicFactor * 3.5);
    } else if(ripples.length > 0) {
      roentgenVal = 0.1 + 0.8 * Math.sin(t * 0.005);
    }
    roentgenVal = Math.max(0.1, Math.min(3.6, roentgenVal));
  }

  $('power-num').textContent=power.toLocaleString();
  $('roentgen-num').textContent = roentgenVal.toFixed(1);
  const roentgenPercent = ((roentgenVal - 0.1) / (3.6 - 0.1)) * 100;
  $('roentgen-bar-fill').style.width = roentgenPercent + '%';

  if(t - lastDOMUpdateTime > 100){
    lastDOMUpdateTime = t;
    $('level').innerHTML=((isPlayableOrHold(isActuallyPlaying,holdEnabled)&&energy)?Math.round(20*Math.log10(Math.max(energy,.001))):'—')+'<small>dB</small>';
    $('freq').innerHTML=((isPlayableOrHold(isActuallyPlaying,holdEnabled)&&peak)?Math.round(peakIndex*(ctx?ctx.sampleRate:44100)/analyser.fftSize):'—')+'<small>Hz</small>';
    if(playing && mode!=='system'){
      const seconds=offset+ctx.currentTime-started;
      $('elapsed').textContent=format(seconds);
      if(buffer&&mode==='file' && document.activeElement !== $('seek')) $('seek').value=seconds/buffer.duration*100;
      updateLyricsDisplay(seconds);
    }
  }
  requestAnimationFrame(frame)
}
requestAnimationFrame(frame);

function isPlayableOrHold(isActuallyPlaying, holdEnabled){
  return isActuallyPlaying || holdEnabled;
}

function format(s){return Math.floor(s/60).toString().padStart(2,'0')+':'+Math.floor(s%60).toString().padStart(2,'0')}

function updateCoverDisplay(item){
  const img=$('cover-img'),empty=$('cover-empty'),status=$('rw-status');
  const dotCanvasEl=$('dot-aperture-canvas');
  const crtText=empty.querySelector('.crt-blank-text');

  if(item&&item.coverUrl){
    img.src=item.coverUrl;img.style.display='block';empty.style.display='none';status.textContent='已加载';
  }else{
    img.src='';img.style.display='none';empty.style.display='flex';status.textContent='无封面';
    if(currentTheme==='el'){
      if(dotCanvasEl) dotCanvasEl.style.display='block';
      if(crtText) crtText.style.display='none';
    }else{
      if(dotCanvasEl) dotCanvasEl.style.display='none';
      if(crtText) crtText.style.display='inline-block';
    }
  }
}

/* ===== 播放列表与喜欢功能 ===== */
function renderPlaylist(){
  const ul=$('playlist');if(!ul)return;
  ul.textContent='';
  const keyword=$('playlist-search').value.trim().toLowerCase();
  
  let visibleCount=0;
  playlist.forEach((item,i)=>{
    const matches=!keyword || item.name.toLowerCase().includes(keyword);
    if(matches) visibleCount++;

    const cur=i===current,active=i===current&&playing&&mode==='file';
    const li=document.createElement('li');
    li.className='pl-item'+(cur?' active':'')+(active?' playing':'');
    li.setAttribute('draggable', 'true');
    li.dataset.index = i;
    if(!matches){
      li.style.display='none';
    }

    li.addEventListener('dragstart', e => {
      e.stopPropagation();
      e.dataTransfer.setData('text/plain', i);
      li.classList.add('dragging');
    });
    li.addEventListener('dragend', e => {
      e.stopPropagation();
      li.classList.remove('dragging');
      document.querySelectorAll('.pl-item').forEach(el=>el.classList.remove('drag-over-top', 'drag-over-bottom'));
    });
    li.addEventListener('dragover', e => {
      e.preventDefault();
      e.stopPropagation();
      const rect = li.getBoundingClientRect();
      const mid = rect.top + rect.height / 2;
      if (e.clientY < mid) {
        li.classList.add('drag-over-top');
        li.classList.remove('drag-over-bottom');
      } else {
        li.classList.add('drag-over-bottom');
        li.classList.remove('drag-over-top');
      }
    });
    li.addEventListener('dragleave', e => {
      e.stopPropagation();
      li.classList.remove('drag-over-top', 'drag-over-bottom');
    });
    li.addEventListener('drop', e => {
      e.preventDefault();
      e.stopPropagation();
      const fromIdx = parseInt(e.dataTransfer.getData('text/plain'), 10);
      let toIdx = parseInt(li.dataset.index, 10);
      const rect = li.getBoundingClientRect();
      const mid = rect.top + rect.height / 2;
      if (e.clientY >= mid && fromIdx < toIdx) {
        toIdx++;
      } else if (e.clientY < mid && fromIdx > toIdx) {
      }
      if (!isNaN(fromIdx) && fromIdx !== toIdx) {
        const movedItem = playlist.splice(fromIdx, 1)[0];
        if (fromIdx < toIdx) toIdx--;
        playlist.splice(toIdx, 0, movedItem);
        if (current === fromIdx) {
          current = toIdx;
        } else if (current > fromIdx && current <= toIdx) {
          current--;
        } else if (current < fromIdx && current >= toIdx) {
          current++;
        }
        renderPlaylist();
        persistState();
      }
    });

    const btn=document.createElement('button');
    btn.type='button';btn.className='pl-main';
    btn.setAttribute('aria-label',(active?'暂停 ':'播放 ')+item.name);
    
    const favBtn=document.createElement('button');
    favBtn.type='button';
    favBtn.className='pl-fav-item'+(item.isFavorite?' active':'');
    favBtn.textContent=item.isFavorite?'♥':'♡';
    favBtn.title=item.isFavorite?'取消喜欢':'设为喜欢';
    favBtn.onclick=ev=>{
      ev.stopPropagation();
      item.isFavorite=!item.isFavorite;
      renderPlaylist();
      renderFavoritesWindow();
      persistState();
    };

    btn.innerHTML='<span class="pl-num"></span><span class="pl-info"><strong></strong><small></small></span><span class="pl-play"></span>';
    btn.querySelector('.pl-num').textContent=String(i+1).padStart(2, '0');
    
    const numSpan=btn.querySelector('.pl-num');
    numSpan.after(favBtn);

    btn.querySelector('strong').textContent=item.name;
    btn.querySelector('small').textContent=item.duration?format(item.duration):'--:--';
    btn.querySelector('.pl-play').textContent=active?'❚❚':'▶';
    btn.addEventListener('click',()=>{
      if(active){offset+=ctx.currentTime-started;stop()}
      else playTrack(i);
    });

    const del=document.createElement('button');
    del.type='button';del.className='pl-del';del.textContent='×';
    del.setAttribute('aria-label','移除 '+item.name);
    del.addEventListener('click',ev=>{ev.stopPropagation();removeTrack(i)});

    li.append(btn,del);
    ul.append(li);
  });

  $('playlist-count').textContent=playlist.length+' 首';
  $('playlist-empty').hidden=playlist.length>0 || visibleCount>0;
  renderFavoritesWindow();
  update();
}

function renderFavoritesWindow(){
  const ul=$('favorites-list');
  const emptyEl=$('favorites-empty');
  if(!ul)return;
  ul.textContent='';
  const favItems=playlist.filter(item=>item.isFavorite);

  favItems.forEach((item)=>{
    const originalIdx=playlist.indexOf(item);
    const li=document.createElement('li');
    li.className='pl-item';
    const btn=document.createElement('button');
    btn.type='button';btn.className='pl-main';
    btn.innerHTML='<span class="pl-num"></span><span class="pl-info"><strong></strong><small></small></span><span class="pl-play">▶</span>';
    btn.querySelector('.pl-num').textContent='♥';
    btn.querySelector('strong').textContent=item.name;
    btn.querySelector('small').textContent=item.duration?format(item.duration):'--:--';
    btn.addEventListener('click',()=>{
      playTrack(originalIdx);
    });

    const removeFavBtn=document.createElement('button');
    removeFavBtn.type='button';removeFavBtn.className='pl-del';removeFavBtn.textContent='×';
    removeFavBtn.title='移出收藏';
    removeFavBtn.onclick=ev=>{
      ev.stopPropagation();
      item.isFavorite=false;
      renderPlaylist();
      persistState();
    };

    li.append(btn,removeFavBtn);
    ul.append(li);
  });

  if(emptyEl) emptyEl.style.display = favItems.length === 0 ? 'flex' : 'none';
}

const favWin=$('favorites-window');
if(favWin){
  favWin.addEventListener('dragover', e=>e.preventDefault());
  favWin.addEventListener('drop', e=>{
    e.preventDefault();
    const fromIdx = parseInt(e.dataTransfer.getData('text/plain'), 10);
    if(!isNaN(fromIdx) && playlist[fromIdx]){
      playlist[fromIdx].isFavorite = true;
      renderPlaylist();
      persistState();
    }
  });
}

$('playlist-search').oninput=()=>{
  renderPlaylist();
};

const shuffleBtn=$('shuffle-btn');
if(shuffleBtn){
  shuffleBtn.onclick=()=>{
    isShuffle=!isShuffle;
    shuffleBtn.style.color=isShuffle?'var(--accent)':'var(--muted)';
    shuffleBtn.style.borderColor=isShuffle?'var(--accent)':'var(--line)';
    shuffleBtn.title=isShuffle?'随机播放: 开':'随机播放: 关';
  };
}

const favoritesOpenBtn=$('favorites-open-btn');
if(favoritesOpenBtn){
  favoritesOpenBtn.onclick=()=>{
    const win=$('favorites-window');
    win.style.display = win.style.display==='none' ? 'flex' : 'none';
  };
}

async function playTrack(i){
  const item=playlist[i];if(!item)return;
  stop();
  lastPlayedTrackIndex = current;
  current=i;mode='file';buffer=null;offset=0;
  currentLyrics=item.lyrics||[];
  updateCoverDisplay(item);
  $('trackname').textContent=item.name;
  $('duration').textContent=item.duration?format(item.duration):'--:--';
  $('elapsed').textContent='00:00';$('seek').value=0;
  update();renderPlaylist();
  persistState();
  const token=session;loading=true;
  $('message').textContent='正在读取音频…';
  try{
    await audio();
    let buf=item.buffer;
    if(!buf){
      const arrayBuf=await item.file.arrayBuffer();
      buf=await ctx.decodeAudioData(arrayBuf);
      item.buffer=buf;item.duration=buf.duration;
    }
    if(token!==session)return;
    buffer=buf;loading=false;
    $('duration').textContent=format(buf.duration);
    renderPlaylist();
    await start();
  }catch{
    if(token!==session)return;
    loading=false;
    $('message').textContent='无法读取该文件，请尝试 MP3 或 WAV 音频。';
  }
}

function playNextTrack(){
  if(playlist.length===0)return;
  let next;
  if(isShuffle){
    next=Math.floor(Math.random()*playlist.length);
  }else{
    next=(current+1)%playlist.length;
  }
  playTrack(next);
}

function playPrevTrack(){
  if(playlist.length===0)return;
  let prev = lastPlayedTrackIndex >= 0 ? lastPlayedTrackIndex : (current - 1 + playlist.length) % playlist.length;
  playTrack(prev);
}

$('next-track').onclick=playNextTrack;
$('prev-track').onclick=playPrevTrack;

function removeTrack(i){
  if(i===current&&playing){offset=0;stop()}
  playlist.splice(i,1);
  if(i<current)current--;
  else if(i===current){
    current=-1;buffer=null;currentLyrics=[];
    updateCoverDisplay(null);
    $('duration').textContent='--:--';$('elapsed').textContent='00:00';$('seek').value=0;
    updateLyricsDisplay(0);
  }
  renderPlaylist();update();
  persistState();
}

function handleTrackEnd(){
  if(source){source.onended=null;try{source.disconnect()}catch{}source=null}
  playing=false;offset=0;
  $('seek').value=0;$('elapsed').textContent='00:00';
  
  if(autoNext&&playlist.length>0){
    playNextTrack();
  }else{
    renderPlaylist();update();
  }
}

async function audio(){
  if(!ctx){
    ctx=new AudioContext();
    analyser=ctx.createAnalyser();
    analyser.fftSize=32768; // 提升至最高高分辨率 32768
    analyser.smoothingTimeConstant=.75;
    bins=new Uint8Array(analyser.frequencyBinCount);
    wave=new Float32Array(analyser.fftSize);

    splitter=ctx.createChannelSplitter(2);
    analyserL=ctx.createAnalyser();
    analyserR=ctx.createAnalyser();
    analyserL.fftSize=16384;
    analyserR.fftSize=16384;
    waveL=new Float32Array(16384);
    waveR=new Float32Array(16384);
    
    master=ctx.createGain();
    master.gain.value=.4;
    
    muteGain=ctx.createGain();
    muteGain.gain.value=1.0;
    
    analyser.connect(muteGain);
    muteGain.connect(master);
    master.connect(ctx.destination);
  }
  await ctx.resume();
}

function stop(){
  session++;
  loading=false;
  if(source){source.onended=null;try{source.stop?.()}catch{}source.disconnect();source=null}
  demoNodes.forEach(n=>{try{n.stop?.();n.disconnect()}catch{}});
  demoNodes=[];
  if(genOsc){try{genOsc.stop();genOsc.disconnect()}catch{};genOsc=null}
  if(stream){stream.getTracks().forEach(t=>t.stop());stream=null}
  playing=false;
  
  $('track-container').style.display='flex';
  $('timeline-container').style.display='block';
  $('system-status-banner').style.display='none';
  if(muteGain && ctx) muteGain.gain.setTargetAtTime(1.0, ctx.currentTime, 0.03);

  update();
  renderPlaylist();
}

function stopAndLockPlayback(){
  stop();
  isStoppedAndLocked = true;
  current=-1;
  buffer=null;
  currentLyrics=[];
  updateCoverDisplay(null);
  updateLyricsDisplay(0);
  $('trackname').textContent='REACTOR / 堆芯已紧急停止';
  $('tracksub').textContent='';
  $('elapsed').textContent='00:00';
  $('seek').value=0;
  update();
  renderPlaylist();
  $('message').textContent='堆芯总闸已切断：音频输入已停止。';
}

function update(){
  $('play').textContent=playing?'Ⅱ':'▶';$('play').setAttribute('aria-label',playing?'暂停':'播放');
  
  const machineBtn=$('machine-btn');
  if(machineBtn){
    machineBtn.classList.toggle('active', isStoppedAndLocked);
    machineBtn.title=isStoppedAndLocked?'已满载锁定 (点击解除)':'堆芯总闸: 停止并满载锁定';
  }

  const genBtn=$('generator-btn');
  if(genBtn) genBtn.classList.toggle('selected',mode==='generator');
  const sysBtn=$('system-audio');
  if(sysBtn)sysBtn.classList.toggle('selected',mode==='system');

  $('status').textContent=playing?'运行中 · '+(mode==='generator'?'函数发生器':mode==='system'?'系统音频捕捉':'音频分析'):'待机 · 就绪';
  $('seek').disabled = playlist.length === 0 && !buffer;
}

async function start(){
  if(loading||playing)return;
  isStoppedAndLocked = false; 
  loading=true;const attempt=++session;try{await audio();if(attempt!==session)return;if(mode==='generator'){
    const id=++session;
    loading=true;
    $('message').textContent='函数发生器运行中…';
    master.gain.value=+$('volume').value/100;
    genOsc=ctx.createOscillator();
    genOsc.type='sine';
    const freqVal = parseFloat($('gen-freq-input').value) || 440;
    genOsc.frequency.value = Math.max(10, Math.min(24000, freqVal));
    genOsc.connect(analyser);
    genOsc.start();
    started=ctx.currentTime;
    playing=true;
    update();
    renderPlaylist();
  }else if(mode==='system'){
    const id=++session;
    loading=true;
    $('message').textContent='请在浏览器弹窗中选择并勾选共享音频…';
    const s=await navigator.mediaDevices.getDisplayMedia({video:{displaySurface:"browser"},audio:true});
    if(id!==session){s.getTracks().forEach(t=>t.stop());return}
    const audioTracks=s.getAudioTracks();
    if(audioTracks.length===0){alert('未检测到音频轨道！请确保在弹出的窗口中勾选了“分享音频”或“共享标签页音频”。');s.getTracks().forEach(t=>t.stop());loading=false;return}
    
    const videoTrack = s.getVideoTracks()[0];
    const settings = videoTrack ? videoTrack.getSettings() : {};
    const displaySurface = settings.displaySurface;
    let windowTitle = videoTrack ? videoTrack.label : '外部系统音频';
    if(!windowTitle || windowTitle === 'screen' || windowTitle === 'window'){
      windowTitle = displaySurface === 'browser' ? '共享标签页音频' : '外部系统窗口音频';
    }

    videoTrack.stop();
    stream=s;
    source=ctx.createMediaStreamSource(s);
    source.connect(analyser);
    source.connect(splitter);
    splitter.connect(analyserL, 0);
    splitter.connect(analyserR, 1);
    
    if(muteGain && ctx) muteGain.gain.setTargetAtTime(0.0, ctx.currentTime, 0.03);

    $('trackname').textContent = windowTitle;
    $('tracksub').textContent = '外部系统捕获源';
    $('track-container').style.display = 'flex';
    $('timeline-container').style.display = 'none';
    $('system-status-banner').style.display = 'flex';

    master.gain.value=+$('volume').value/100;
    $('message').textContent='正在实时捕捉外部音频源（已自动静音网页输出防混响），关闭共享即可停止。';
    
    audioTracks[0].onended=()=>{
      stop();
      $('message').textContent='外部音频捕捉已结束。';
    };
  }else{
    master.gain.value=+$('volume').value/100;
    if(mode==='file'&&buffer){
      if(offset>=buffer.duration)offset=0;
      source=ctx.createBufferSource();
      source.buffer=buffer;
      source.connect(analyser);
      source.connect(splitter);
      splitter.connect(analyserL, 0);
      splitter.connect(analyserR, 1);

      source.onended=handleTrackEnd;
      source.start(0,offset)
    }
    $('message').textContent='音频仅在本机处理，不会上传。';
  }
  if(mode!=='generator'){
    started=ctx.currentTime;
    playing=true;
    update();
    renderPlaylist();
  }
}catch(e){
  stop();
  $('message').textContent=mode==='system'?'已取消音频捕捉。':'无法播放此音频，请尝试其他文件。';
}finally{
  if(attempt===session||!playing)loading=false;
}}

$('play').onclick=()=>{
  if(!buffer && playlist.length > 0){
    playTrack(current >= 0 ? current : 0);
    return;
  }
  if(playing){offset+=ctx.currentTime-started;stop()}else start()
};

$('machine-btn').onclick=()=> {
  if(isStoppedAndLocked){
    isStoppedAndLocked = false;
    update();
    $('message').textContent='满载锁定已解除。';
  } else {
    stopAndLockPlayback();
  }
};

document.addEventListener('keydown', e => {
  if (e.code === 'Space' || e.key === ' ') {
    const activeTag = document.activeElement ? document.activeElement.tagName : '';
    if (activeTag === 'INPUT' || activeTag === 'SELECT' || activeTag === 'TEXTAREA') {
      return;
    }
    e.preventDefault();
    $('play').click();
  }
});

function isExternalFileDrag(e) {
  if (!e.dataTransfer || !e.dataTransfer.types) return false;
  return Array.from(e.dataTransfer.types).includes('Files');
}

let dragCounter=0;
const dropOverlay=$('drop-overlay');

window.addEventListener('dragenter',e=>{
  if(!isExternalFileDrag(e)) return;
  e.preventDefault();
  dragCounter++;
  dropOverlay.classList.add('active');
});

window.addEventListener('dragover',e=>{
  if(!isExternalFileDrag(e)) return;
  e.preventDefault();
});

window.addEventListener('dragleave',e=>{
  if(!isExternalFileDrag(e)) return;
  e.preventDefault();
  dragCounter--;
  if(dragCounter<=0){
    dragCounter=0;
    dropOverlay.classList.remove('active');
  }
});

window.addEventListener('drop',async e=>{
  if(!isExternalFileDrag(e)) {
    return;
  }

  e.preventDefault();
  dragCounter=0;
  dropOverlay.classList.remove('active');

  const files=[...e.dataTransfer.files];
  if(!files.length)return;

  const audioFiles=[];
  const lyricFilesList=[];

  files.forEach(f=>{
    const name=f.name.toLowerCase();
    if(name.endsWith('.lrc')||name.endsWith('.txt')){
      lyricFilesList.push(f);
    }else if(f.type.startsWith('audio/')||/\.(mp3|wav|m4a|flac|ogg|aac)$/i.test(name)){
      audioFiles.push(f);
    }
  });

  if(lyricFilesList.length>0){
    for(const f of lyricFilesList){
      try{
        const text=await f.text();
        const parsed=parseLrc(text);
        lyricFiles.push({name:f.name,parsed});
        playlist.forEach(item=>{
          const cleanTrackName=item.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
          const cleanLyricName=f.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
          if(cleanTrackName===cleanLyricName||cleanTrackName.includes(cleanLyricName)||cleanLyricName.includes(cleanTrackName)){
            item.lyrics=parsed;
            item.lyricName=f.name;
          }
        });
      }catch(err){console.error('解析拖入歌词失败',err)}
    }
    if(current>=0&&playlist[current]){
      currentLyrics=playlist[current].lyrics||[];
    }
  }

  if(audioFiles.length>0){
    const startIndex=playlist.length;
    for(const f of audioFiles){
      const item={name:f.name,file:f,buffer:null,duration:0,lyrics:null,lyricName:null,coverUrl:null,isFavorite:false};
      autoMatchLyricsForTrack(item);
      if(f.name.toLowerCase().endsWith('.flac')){item.coverUrl=await extractFlacCover(f)}
      playlist.push(item);
    }
    renderPlaylist();
    await persistState();
    $('message').textContent='已通过拖入添加 '+audioFiles.length+' 个音频与 '+lyricFilesList.length+' 个歌词文件。';
    if(!playing)playTrack(startIndex);
  }else if(lyricFilesList.length>0){
    renderPlaylist();
    await persistState();
    $('message').textContent='已成功导入并匹配 '+lyricFilesList.length+' 个歌词文件。';
  }
});

const oscTabBtn=$('oscilloscope-tab-btn');
const oscWindow=$('oscilloscope-window');
if(oscTabBtn && oscWindow){
  oscTabBtn.onclick = () => {
    if(currentTheme === 'el') return;
    const isHidden = oscWindow.style.display === 'none';
    oscWindow.style.display = isHidden ? 'flex' : 'none';
    if(isHidden){
      oscWindow.classList.remove('embedded');
      const embedBtn = $('oscilloscope-embed');
      if(embedBtn) embedBtn.textContent = '⧉';
      setTimeout(sizeOscCanvas, 20);
    }
    oscTabBtn.classList.toggle('selected', isHidden);
  };
}

const generatorBtn=$('generator-btn');
const generatorWindow=$('generator-window');
if(generatorBtn && generatorWindow){
  generatorBtn.onclick = () => {
    const isHidden = generatorWindow.style.display === 'none';
    generatorWindow.style.display = isHidden ? 'flex' : 'none';
    if(isHidden){
      generatorWindow.classList.remove('embedded');
      const embedBtn = $('generator-embed');
      if(embedBtn) embedBtn.textContent = '⧉';
      
      stop();
      mode='generator';
      offset=0;
      buffer=null;
      current=-1;
      currentLyrics=[];
      updateCoverDisplay(null);
      updateLyricsDisplay(0);
      renderPlaylist();
      const freqVal = $('gen-freq-input').value;
      $('trackname').textContent='GENERATOR / 函数发生器 ('+freqVal+'Hz)';
      $('elapsed').textContent='00:00';
      $('seek').value=0;
      update();
      start();
    }else{
      if(mode==='generator'){
        stop();
        update();
      }
    }
    generatorBtn.classList.toggle('selected', isHidden);
  };
}

function updateGeneratorFrequency(val){
  val = Math.max(10, Math.min(24000, val));
  $('gen-freq-input').value = val;
  $('gen-freq-slider').value = val;
  if(mode==='generator'){
    $('trackname').textContent='GENERATOR / 函数发生器 ('+val+'Hz)';
    if(genOsc&&ctx){
      genOsc.frequency.setTargetAtTime(val, ctx.currentTime, 0.02);
    }
  }
}

$('gen-freq-slider').oninput=e=>{
  updateGeneratorFrequency(+e.target.value);
};

$('gen-freq-input').oninput=e=>{
  const val = parseFloat(e.target.value);
  if(!isNaN(val)){
    updateGeneratorFrequency(val);
  }
};

const sysAudioBtn=$('system-audio');
if(sysAudioBtn){
  sysAudioBtn.onclick=()=>{stop();mode='system';offset=0;buffer=null;current=-1;currentLyrics=[];updateCoverDisplay(null);updateLyricsDisplay(0);renderPlaylist();generatorWindow.style.display='none';if(generatorBtn)generatorBtn.classList.remove('selected');$('trackname').textContent='SYSTEM / 外部系统音频捕捉';$('elapsed').textContent='00:00';update();start()};
}

$('upload').onclick=()=>$('file').click();$('file').onchange=async e=>{
  const files=[...e.target.files];
  e.target.value='';
  if(!files.length)return;
  const startIndex=playlist.length;
  for(const f of files){
    const item={name:f.name,file:f,buffer:null,duration:0,lyrics:null,lyricName:null,coverUrl:null,isFavorite:false};
    autoMatchLyricsForTrack(item);
    if(f.name.toLowerCase().endsWith('.flac')){item.coverUrl=await extractFlacCover(f)}
    playlist.push(item);
  }
  renderPlaylist();
  await persistState();
  generatorWindow.style.display='none';
  if(generatorBtn)generatorBtn.classList.remove('selected');
  $('message').textContent='已添加 '+files.length+' 个音频文件，点击列表即可播放。';
  if(!playing)playTrack(startIndex);
};

$('import-lyric-btn').onclick=e=>{
  e.stopPropagation();
  $('lyric-file').click();
};

$('lyric-file').onchange=async e=>{
  const files=[...e.target.files];
  e.target.value='';
  if(!files.length)return;
  for(const f of files){
    try{
      const text=await f.text();
      const parsed=parseLrc(text);
      const lyricObj={name:f.name,parsed};
      lyricFiles.push(lyricObj);
      playlist.forEach(item=>{
        const cleanTrackName=item.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
        const cleanLyricName=f.name.replace(/\.[^/.]+$/, '').trim().toLowerCase();
        if(cleanTrackName===cleanLyricName || cleanTrackName.includes(cleanLyricName) || cleanLyricName.includes(cleanTrackName)){
          item.lyrics=parsed;
          item.lyricName=f.name;
        }
      });
    }catch(err){console.error('解析歌词失败',err)}
  }
  if(current>=0&&playlist[current]){
    currentLyrics=playlist[current].lyrics||[];
  }
  renderPlaylist();
  await persistState();
  $('message').textContent='成功导入 '+files.length+' 个歌词文件，已自动完成匹配。';
};

$('am-slider').oninput=e=>{ amDepth = +e.target.value; };
$('osc-speed-slider').oninput=e=>{ oscSpeed = +e.target.value; };
$('fm-slider').oninput=e=>{ fmDepth = +e.target.value; };
$('osc-response').oninput=e=>{
  oscResponseGain = +e.target.value;
  $('osc-response-val').textContent = oscResponseGain.toFixed(1) + '×';
};

function toggleResponsePanel(forceState){
  const body=$('response-body');
  const compact=$('response-compact');
  const indicator=$('response-toggle-indicator');
  const isCollapsed = forceState!==undefined ? forceState : (body.style.display!=='none');
  
  if(isCollapsed){
    body.style.display='none';
    compact.style.display='flex';
    indicator.textContent='[展开 ▾]';
    $('compact-gain').textContent=$('gainval').textContent;
    $('compact-smooth').textContent=$('smoothval').textContent;
    $('compact-vol').textContent=$('volumeval').textContent;
  }else{
    body.style.display='block';
    compact.style.display='none';
    indicator.textContent='[收起 ▴]';
  }
}
$('response-header').onclick=()=>toggleResponsePanel();$('expand-quick-btn').onclick=()=>toggleResponsePanel(false);

const responseCompactEl = $('response-compact');
if(responseCompactEl){
  responseCompactEl.addEventListener('wheel', e => {
    e.preventDefault();
    const volSlider = $('volume');
    if(volSlider){
      let val = parseInt(volSlider.value) + (e.deltaY < 0 ? 5 : -5);
      val = Math.max(0, Math.min(100, val));
      volSlider.value = val;
      volSlider.dispatchEvent(new Event('input'));
      $('compact-vol').textContent = val + '%';
    }
  }, {passive:false});
}

function makeDraggable(winId, headerId){
  const win=$(winId), header=$(headerId);
  let drag=null;
  header.onpointerdown=e=>{
    if(win.classList.contains('embedded'))return;
    if(e.target.tagName==='BUTTON'||e.target.tagName==='SELECT'||e.target.closest('button')||e.target.closest('select'))return;
    drag={startX:e.clientX,startY:e.clientY,left:win.offsetLeft,top:win.offsetTop};
    header.setPointerCapture(e.pointerId);
  };
  header.onpointermove=e=>{
    if(!drag)return;
    const dx=e.clientX-drag.startX, dy=e.clientY-drag.startY;
    win.style.left=(drag.left+dx)+'px';
    win.style.top=(drag.top+dy)+'px';
  };
  header.onpointerup=header.onpointercancel=()=>{
    if(drag){saveWindowState(winId);}
    drag=null;
  };
}
makeDraggable('cover-window', 'rw-header');
makeDraggable('spectrum-window', 'sw-header');
makeDraggable('lyrics-window', 'lw-header');
makeDraggable('roentgen-window', 'rw-header-roentgen');
makeDraggable('generator-window', 'rw-header-generator');
makeDraggable('oscilloscope-window', 'rw-header-oscilloscope');
makeDraggable('favorites-window', 'rw-header-favorites');

function saveWindowState(winId){
  const win=$(winId);
  localStorage.setItem(winId+'_state', JSON.stringify({
    left: win.style.left,
    top: win.style.top,
    width: win.style.width,
    height: win.style.height
  }));
}

['cover-window', 'spectrum-window', 'lyrics-window', 'roentgen-window', 'generator-window', 'oscilloscope-window', 'favorites-window'].forEach(winId=>{
  const win=$(winId);
  const savedState=localStorage.getItem(winId+'_state');
  if(savedState){
    try{
      const st=JSON.parse(savedState);
      if(st.left)win.style.left=st.left;
      if(st.top)win.style.top=st.top;
      if(st.width)win.style.width=st.width;
      if(st.height)win.style.height=st.height;
    }catch(e){}
  }
  new ResizeObserver(()=>{
    saveWindowState(winId);
  }).observe(win);
});

$('cover-min').onclick=e=>{
  e.stopPropagation();
  const win=$('cover-window');
  win.classList.toggle('minimized');
  $('cover-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('spectrum-min').onclick=e=>{
  e.stopPropagation();
  const win=$('spectrum-window');
  win.classList.toggle('minimized');
  $('spectrum-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('lyrics-min').onclick=e=>{
  e.stopPropagation();
  const win=$('lyrics-window');
  win.classList.toggle('minimized');
  $('lyrics-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('roentgen-min').onclick=e=>{
  e.stopPropagation();
  const win=$('roentgen-window');
  win.classList.toggle('minimized');
  $('roentgen-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('generator-min').onclick=e=>{
  e.stopPropagation();
  const win=$('generator-window');
  win.classList.toggle('minimized');
  $('generator-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('oscilloscope-min').onclick=e=>{
  e.stopPropagation();
  const win=$('oscilloscope-window');
  win.classList.toggle('minimized');
  $('oscilloscope-min').textContent=win.classList.contains('minimized')?'+':'_';
};
$('favorites-min').onclick=e=>{
  e.stopPropagation();
  const win=$('favorites-window');
  win.classList.toggle('minimized');
  $('favorites-min').textContent=win.classList.contains('minimized')?'+':'_';
};

$('cover-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('cover-window');
  win.classList.toggle('embedded');
  $('cover-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('spectrum-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('spectrum-window');
  win.classList.toggle('embedded');
  $('spectrum-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('lyrics-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('lyrics-window');
  win.classList.toggle('embedded');
  $('lyrics-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('roentgen-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('roentgen-window');
  win.classList.toggle('embedded');
  $('roentgen-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('generator-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('generator-window');
  win.classList.toggle('embedded');
  $('generator-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('oscilloscope-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('oscilloscope-window');
  win.classList.toggle('embedded');
  $('oscilloscope-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};
$('favorites-embed').onclick=e=>{
  e.stopPropagation();
  const win=$('favorites-window');
  win.classList.toggle('embedded');
  $('favorites-embed').textContent=win.classList.contains('embedded')?'▣':'⧉';
};

$('cover-close').onclick=e=>{
  e.stopPropagation();
  $('cover-window').style.display='none';
};
$('lyrics-close').onclick=e=>{
  e.stopPropagation();
  $('lyrics-window').style.display='none';
};
$('roentgen-close').onclick=e=>{
  e.stopPropagation();
  $('roentgen-window').style.display='none';
};
$('generator-close').onclick=e=>{
  e.stopPropagation();
  generatorWindow.style.display='none';
  if(generatorBtn) generatorBtn.classList.remove('selected');
  if(mode==='generator'){
    stop();
    update();
  }
};
$('oscilloscope-close').onclick=e=>{
  e.stopPropagation();
  $('oscilloscope-window').style.display='none';
  if(oscTabBtn) oscTabBtn.classList.remove('selected');
};
$('favorites-close').onclick=e=>{
  e.stopPropagation();
  $('favorites-window').style.display='none';
};
$('toggle-cover-btn').onclick=()=>{
  const win=$('cover-window');
  win.style.display=win.style.display==='none'?'flex':'none';
};
$('toggle-lyrics-btn').onclick=()=>{
  const win=$('lyrics-window');
  win.style.display=win.style.display==='none'?'flex':'none';
};

$('lyric-size').oninput=e=>{
  const val=+e.target.value;
  $('lyric-size-val').textContent=val+'px';
  document.documentElement.style.setProperty('--lyrics-font-size', val+'px');
};
$('power-size').oninput=e=>{
  const val=+e.target.value;
  $('power-size-val').textContent=val+'px';
  document.documentElement.style.setProperty('--power-font-size', val+'px');
};
$('lyrics-opacity').oninput=e=>{
  const val=+e.target.value;
  $('lyrics-opacity-val').textContent=val+'%';
  document.documentElement.style.setProperty('--lyrics-opacity', val/100);
};
$('window-opacity').oninput=e=>{
  const val=+e.target.value;
  $('window-opacity-val').textContent=val+'%';
  document.documentElement.style.setProperty('--window-opacity', val/100);
};
$('spectrum-opacity').oninput=e=>{
  const val=+e.target.value;
  $('spectrum-opacity-val').textContent=val+'%';
  document.documentElement.style.setProperty('--spectrum-opacity', val/100);
};

// 实时拖动预览进度
$('seek').oninput=()=>{
  if(buffer){
    const targetTime = (+$('seek').value / 100) * buffer.duration;
    $('elapsed').textContent = format(targetTime);
  }
};

// 松开或点击时正式跳转播放进度
$('seek').onchange=()=>{
  if(!buffer){
    if(playlist.length > 0){
      playTrack(current >= 0 ? current : 0);
    }
    return;
  }
  const was=playing;
  stop();
  offset=+$('seek').value/100*buffer.duration;
  $('elapsed').textContent=format(offset);
  if(was)start();
};

$('gain').oninput=e=>{gain=+e.target.value;$('gainval').textContent=gain.toFixed(1)+'×'};
$('roentgen-gain').oninput=e=>{roentgenGain=+e.target.value;$('roentgen-gain-val').textContent=roentgenGain.toFixed(1)+'×'};
$('power-gain').oninput=e=>{powerGain=+e.target.value;$('power-gain-val').textContent=powerGain.toFixed(1)+'×'};
$('smooth').oninput=e=>{smoothing=+e.target.value/100;$('smoothval').textContent=e.target.value+'%'};
$('volume').oninput=e=>{$('volumeval').textContent=e.target.value+'%';if(master)master.gain.setTargetAtTime(+e.target.value/100,ctx.currentTime,.03)};

// 反应堆点击交互：仅在播放完全停止（无曲目/堆芯锁定）时才生成波纹扩散，暂停时不生效
canvas.onpointerdown=e=>{
  const rect=canvas.getBoundingClientRect();
  const clickX=e.clientX-rect.left;
  const clickY=e.clientY-rect.top;

  const isActuallyPlaying=playing&&(mode==='file'||mode==='generator'||mode==='system');
  const isCompletelyStopped = !playing && (current === -1 || !buffer || isStoppedAndLocked);

  if(!isActuallyPlaying && isCompletelyStopped){
    let closestRod=rods[0];
    let minDist=Infinity;
    for(const rod of rods){
      const [px,py]=point(rod.x,rod.z,rod.h);
      const dist=Math.hypot(px-clickX,py-clickY);
      if(dist<minDist){
        minDist=dist;
        closestRod=rod;
      }
    }
    if(closestRod){
      ripples.push({x:closestRod.x,z:closestRod.z,startTime:performance.now()});
    }
  }

  drag={x:e.clientX,y:e.clientY};
  try{canvas.setPointerCapture(e.pointerId)}catch{}
};
canvas.onpointermove=e=>{if(!drag)return;angle-=(e.clientX-drag.x)*.006;tilt=Math.max(.25,Math.min(.85,tilt+(e.clientY-drag.y)*.002));drag={x:e.clientX,y:e.clientY}};
canvas.onpointerup=canvas.onpointercancel=e=>{
  drag=null;
  try{canvas.releasePointerCapture(e.pointerId)}catch{}
};
canvas.addEventListener('wheel',e=>{e.preventDefault();zoom=Math.max(.65,Math.min(1.5,zoom-e.deltaY*.001))},{passive:false});
$('reset').onclick=()=>{angle=-.32;tilt=.58;zoom=1};
$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen()}catch{$('message').textContent='当前浏览器不支持全屏。'}};
document.addEventListener('fullscreenchange',()=>{$('fullscreen').textContent=document.fullscreenElement?'退出全屏 ↙':'全屏 ↗'});
window.addEventListener('pagehide',stop);

$('autonext').onchange=e=>{autoNext=e.target.checked};$('playlist-clear').onclick=()=>{
  if(!playlist.length)return;
  if(playing)stop();
  playlist.length=0;current=-1;buffer=null;offset=0;currentLyrics=[];
  updateCoverDisplay(null);
  updateLyricsDisplay(0);
  $('elapsed').textContent='00:00';$('seek').value=0;
  renderPlaylist();update();
  $('message').textContent='播放列表已清空。';
  persistState();
};

async function initCache(){
  try{
    const cachedPlaylist=await loadFromCache('playlist');
    const cachedLyrics=await loadFromCache('lyricFiles');
    const lastIdx=await loadFromCache('lastPlayedIndex');
    if(cachedLyrics&&Array.isArray(cachedLyrics)){
      lyricFiles.push(...cachedLyrics);
    }
    if(cachedPlaylist&&Array.isArray(cachedPlaylist)){
      for(const cached of cachedPlaylist){
        let coverUrl=null;
        if(cached.blob&&cached.name.toLowerCase().endsWith('.flac')){
          coverUrl=await extractFlacCover(cached.blob);
        }
        const item={
          name:cached.name,
          file:cached.blob,
          buffer:null,
          duration:cached.duration,
          lyrics:cached.lyrics,
          lyricName:cached.lyricName,
          coverUrl:coverUrl,
          isFavorite:!!cached.isFavorite
        };
        playlist.push(item);
      }
      playlist.forEach(item=>autoMatchLyricsForTrack(item));
    }
    if(typeof lastIdx==='number'&&lastIdx>=0&&lastIdx<playlist.length){
      current = lastIdx;
      const item = playlist[current];
      if(item){
        $('trackname').textContent = item.name;
        if(item.duration) $('duration').textContent = format(item.duration);
        updateCoverDisplay(item);
        currentLyrics = item.lyrics || [];
      }
    }
  }catch(e){console.error('加载缓存异常',e)}
  renderPlaylist();
  update();
  updateLyricsDisplay(0);
  toggleResponsePanel(true);
}

initCache();