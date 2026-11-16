/* fx.js — VFX layer for "Анальные Скорпионы" (v1.6). Presentation only: never touches app state or the network.
 *
 * Layers (all position:fixed, pointer-events:none, aria-hidden):
 *   #fxBackGL  z:-1   WebGL  — behind the content: the part of the Керри fire that rises above the card (behind the card,
 *                              the legend and the round label), the wish dissolve behind the logo (desktop)
 *   #fxBack    z:-1   2D     — a few slow ambient embers (they rest after a minute without interaction)
 *   #fxFrontGL z:180  WebGL  — the Керри fire inside the portrait niche / phone row (base hidden by the bottom frame,
 *                              burning behind the medallion, check, plaque, name), hero-niche smoke, reset/undo wipe
 *   #fxFront   z:180  2D     — sparks, fuse / smoulder lines, energy traces along outlines, rune circles, light sweeps
 *   Both front layers are lifted to z:1001 (class fx-top) while the splash is visible.
 *
 * Fire and smoke: one fragment shader (GLSL ES 1.00, runs in WebGL2 or WebGL1), warmed up (every kind drawn once into a
 * 1x1 viewport) shortly after load; a lost context is rebuilt on webglcontextrestored.
 *   Fire  = a few wide, unequal licks (about 4-5 across the frame, jittered, each with its own height, width and lean)
 *           growing out of one low turbulent bed, joined with a soft union; turbulent sway growing with height, rising
 *           fBm erosion, blackbody ramp with a broken (not uniform) hot core, premultiplied with low alpha (≈ additive),
 *           dark smoky tips. Its emitter sits below the frame's bottom edge, so the base is never seen; it fades out
 *           toward the side walls; the medallion, check, legend and round label (rows: plaque, name, hero line) occlude.
 *   Smoke = a slowly warped body whose thin outer part erodes into streaks stretched along the rise; dark charcoal /
 *           neutral grey, lit only faintly (bright folds read as marble), alpha-blended.
 *   No smoke at the splash or behind the grid at the roll press (both read as fog); line work carries those beats.
 * Every effect asks for a render scale (0.5 soft smoke .. 1.0x CSS px on desktop / 1.2x on phones for fire and sharp smoke);
 * a GL canvas renders at the highest scale any live effect needs, draws only the effects' own quads and is hidden when
 * none is alive. Without WebGL: sparks + line work only.
 *
 * Phone rows (index.html sets --fx-row:1 on .player-card at <=600px): the card is a horizontal row with a small portrait
 * thumbnail; the Керри fire burns inside the row's frame, weighted to the portrait side (front layer only, the row's
 * plaque / name / hero line / medallion / check occlude it), hero-pick smoke stays in the thumbnail, the header medallion
 * is 40px (tight ring opened toward the title beside it, no dissolve smoke).
 *
 * Magic is line art only: strokes on the element's own visual outline (chamfered plaque, niche rectangle, button) and
 * true circles only around round elements (logo medallion, splash medallion, avatar medallion). No radial sprites.
 *
 * API (window.FX): ambient(on) token() clear() rollStart(o) reveal(card,badge,role,tok) wish(tok)
 *                  heroPick(pi,isRandom) splash(el,ms) sweep(el) achievement(toastEl,socketEl) info()
 * token() starts a reveal generation; clear() bumps it and kills every live effect (ambient embers stay), so timers left
 * over from a cancelled roll (undo / reset / newer roll) draw nothing.
 * Test hooks (capture only): window.__FX_NO_GL forces the fallback, window.__FX_TS slows the FX clock (e.g. 0.25).
 */
(function(){
'use strict';
if(window.FX)return;
var TAU=Math.PI*2,doc=document;
var ROLE_COL={'Танк':'#6f9fd0','Керри':'#eba53a','Мидер':'#b07cf0','Суппорт':'#5fd1b0','Фулл Суппорт':'#2a9a80'};
var GOLD='#f2c46e',ARCANE='#a094c8';

// ---- own PRNG (never consumes the app's Math.random sequence) ----
var seed=((Date.now()^Math.round(performance.now()*1000))>>>0)||1;
function R(){var x=seed;x^=x<<13;x^=x>>>17;x^=x<<5;seed=x>>>0;return seed/4294967296;}
function rr(a,b){return a+(b-a)*R();}
function clamp01(x){return x<0?0:x>1?1:x;}
function eOut(u){u=clamp01(u);return 1-(1-u)*(1-u)*(1-u);}
function eIO(u){u=clamp01(u);return u<.5?4*u*u*u:1-Math.pow(-2*u+2,3)/2;}
var TS=+window.__FX_TS||1,PT0=performance.now();
function now(){return TS===1?performance.now():PT0+(performance.now()-PT0)*TS;}
function hex3(h){h=String(h||'').trim();if(h.charAt(0)!=='#'||h.length<7)return null;var n=parseInt(h.slice(1,7),16);return isFinite(n)?[n>>16&255,n>>8&255,n&255]:null;}
function rgb(c){return 'rgb('+(c[0]|0)+','+(c[1]|0)+','+(c[2]|0)+')';}
function lighten(c,k){return [c[0]+(255-c[0])*k,c[1]+(250-c[1])*k,c[2]+(238-c[2])*k];}

// colour ramps (index = temperature 0..1)
var FIRE=[];(function(){for(var i=0;i<=40;i++){var T=i/40;
  FIRE.push(rgb([255*Math.min(1,1.25*Math.pow(T,.75)),255*Math.min(1,1.05*Math.pow(T,1.9)),255*Math.min(1,.95*Math.pow(T,4))]));}})();
function fireC(T){return FIRE[Math.max(0,Math.min(40,Math.round(T*40)))];}
var MLUT={};
function mlut(col){if(MLUT[col])return MLUT[col];var c=hex3(col)||[224,177,90],L=[];
  for(var i=0;i<=40;i++){var T=i/40,v;if(T>.55){var f=(T-.55)/.45;v=lighten(c,f*f*.92);}else{var m=.3+.7*T/.55;v=[c[0]*m,c[1]*m,c[2]*m];}L.push(rgb(v));}
  return MLUT[col]=L;}

var mq=window.matchMedia?window.matchMedia('(prefers-reduced-motion: reduce)'):null;
var reduced=!!(mq&&mq.matches);
var NO_GL=!!window.__FX_NO_GL;

// ---- state ----
var back=null,front=null,bx=null,fx=null,W=0,H=0,Hc=0,DPR=1,dprSeen=0,small=false,Q=1,ok=false;
var sparks=[],objs=[],embers=[],ambOn=false,raf=0,tmo=0,last=0,gen=0,frontDirty=false;
var CAP_S=320,AMB_N=10,nFrames=0;
var GLB=null,GLF=null;
// render scale an effect asks for: 'hi' = crisp (fire, niche, splash), 'mid' = smoke behind sharp text, 'lo' = soft smoke
function RES(k){return k==='hi'?(small?Math.min(1.2,.5*dprSeen+.25):1):k==='mid'?(small?.8:.75):.5;}

// ================================================================== WebGL smoke / fire
var VS='attribute vec2 aP;uniform vec4 uQuad;uniform vec2 uRes;uniform float uS;'+
'void main(){vec2 px=(uQuad.xy+aP*uQuad.zw)*uS;vec2 c=px/uRes*2.0-1.0;gl_Position=vec4(c.x,-c.y,0.0,1.0);}';
var FS=[
'#ifdef GL_FRAGMENT_PRECISION_HIGH','precision highp float;','#else','precision mediump float;','#endif',
'uniform vec2 uRes;uniform float uS;uniform float uKind;uniform float uT;uniform float uK;',
'uniform vec4 uA;uniform vec4 uB;uniform vec4 uC;uniform vec4 uD;uniform vec2 uSeed;uniform vec4 uM[6];uniform float uN;uniform vec2 uO;',
// 2D simplex noise (Ashima Arts / Stefan Gustavson, MIT)
'vec3 perm(vec3 x){return mod(((x*34.0)+1.0)*x,289.0);}',
'float snoise(vec2 v){const vec4 C=vec4(0.211324865405187,0.366025403784439,-0.577350269189626,0.024390243902439);',
' vec2 i=floor(v+dot(v,C.yy));vec2 x0=v-i+dot(i,C.xx);vec2 i1=(x0.x>x0.y)?vec2(1.0,0.0):vec2(0.0,1.0);',
' vec4 x12=x0.xyxy+C.xxzz;x12.xy-=i1;i=mod(i,289.0);',
' vec3 p=perm(perm(i.y+vec3(0.0,i1.y,1.0))+i.x+vec3(0.0,i1.x,1.0));',
' vec3 m=max(0.5-vec3(dot(x0,x0),dot(x12.xy,x12.xy),dot(x12.zw,x12.zw)),0.0);m=m*m;m=m*m;',
' vec3 x=2.0*fract(p*C.www)-1.0;vec3 h=abs(x)-0.5;vec3 ox=floor(x+0.5);vec3 a0=x-ox;',
' m*=1.79284291400159-0.85373472095314*(a0*a0+h*h);',
' vec3 g;g.x=a0.x*x0.x+h.x*x0.y;g.yz=a0.yz*x12.xz+h.yz*x12.yw;return 130.0*dot(m,g);}',
'const mat2 ROT=mat2(1.6,1.2,-1.2,1.6);',
'float fbm3(vec2 p){float f=0.0,a=0.5;for(int i=0;i<3;i++){f+=a*snoise(p);p=ROT*p;a*=0.5;}return f;}',
'float fbm4(vec2 p){float f=0.0,a=0.5;for(int i=0;i<4;i++){f+=a*snoise(p);p=ROT*p;a*=0.5;}return f;}',
'float sdBox(vec2 p,vec2 b){vec2 d=abs(p)-b;return length(max(d,0.0))+min(max(d.x,d.y),0.0);}',
'float hsh(float n){return fract(sin(n*12.9898+uSeed.x*0.731)*43758.5453);}',
// occluders (page rects / circles that must stay clean): 0 inside, 1 outside. uO=(softness px, floor): soft=0 gives a
// ~1.5 px edge (fire behind a medallion); a wide softness with a floor only thins the smoke over text (undo wipe).
// a circle is encoded as (cx,cy,r,cy-1e4) — i.e. y1<y0, which no rect has
'float occl(vec2 p){float o=1.0;for(int i=0;i<6;i++){if(float(i)<uN){vec4 r=uM[i];float d;',
' if(r.w<r.y)d=length(p-r.xy)-r.z;else{vec2 q=max(r.xy-p,p-r.zw);d=max(q.x,q.y);}o*=mix(uO.y,1.0,smoothstep(-0.5-uO.x,1.5,d));}}return o;}',
'vec3 blackbody(float h){return vec3(min(1.0,1.25*pow(h,0.75)),min(1.0,1.05*pow(h,1.9)),min(1.0,0.95*pow(h,4.0)));}',
// wispy smoke: a slowly warped body whose thin outer part is eroded by noise stretched along the rise direction, so it
// breaks into thin rising streaks. Lit only faintly from above (no bright folds: those read as marble) and kept dark
// charcoal / neutral grey. m = mask (1 deep inside .. 0 outside)
'float fbm4s(vec2 p){float f=0.0,a=0.55;for(int i=0;i<4;i++){f+=a*snoise(p);p=ROT*p;a*=0.42;}return f;}',
'vec4 wispSmoke(float m,vec2 q,float t,vec3 dk,vec3 lt,float op){',
' if(m<0.004)return vec4(0.0);',
' vec2 w=vec2(fbm3(q*0.5+vec2(0.0,t*0.12)),fbm3(q*0.5+vec2(3.1,7.7)+vec2(t*0.1,0.0)));',
' vec2 qq=q+0.55*w;',
' float n=fbm4s(qq)*0.5+0.5;',
// streaks: noise squeezed across and stretched along the rise, sliding up
' float s=fbm3(vec2(qq.x*2.4,qq.y*0.32)+vec2(1.7,-t*0.45))*0.5+0.5;',
' float d=clamp(m*1.15-(1.0-n)*0.6-(1.0-s)*0.75*(1.0-smoothstep(0.3,0.95,m)),0.0,1.0);',
' if(d<0.002)return vec4(0.0);',
' float nl=fbm4s(qq+vec2(0.0,-0.3))*0.5+0.5;',
' float l=clamp(0.42+(n-nl)*0.9,0.0,1.0);',
' vec3 col=mix(dk,lt,l*l);float a=clamp(pow(d,1.35)*op,0.0,0.85);return vec4(col*a,a);}',
// flame licks along an emitter line: one per cell (jittered centre, kept off the side walls), each with its own
// strength, height, width and a constant lean (uD.x) plus a wander that grows toward the tip; neighbours are joined
// with a soft union so their bases merge into one body. so = seed offset, hk = height factor, wk = width factor.
// wgt(x): an optional height / strength envelope along the line (uD.z centre, uD.w width; phone rows weight the
// portrait side). acc = flame body, wide = where its smoke rises
'float wgt(float x){return uD.w>0.0?mix(0.3,1.0,exp(-(x-uD.z)*(x-uD.z)/(uD.w*uD.w))):1.0;}',
'float sunion(float a,float b){return a+b-a*b;}',
'void licks(float xw,float h,float x0,float x1,float cell,float Hm,float t,float so,float hk,float wk,inout float acc,inout float wide){',
' float ci=floor((xw-x0)/cell);',
' for(int j=-1;j<=1;j++){float c=ci+float(j),cs=c+so;',
'  float r1=hsh(cs),r2=hsh(cs+31.7),r3=hsh(cs+57.3),r4=hsh(cs+83.1),r5=hsh(cs+12.9);',
'  float c0=x0+(c+0.5+(r1-0.5)*0.55)*cell;',
'  float inr=step(x0-cell*0.25,c0)*step(c0,x1+cell*0.25);',
'  c0=clamp(c0,x0+cell*0.32,x1-cell*0.32);',
'  float on=inr*smoothstep(uC.z,uC.z+0.15,r3);',
// two classes: about half the licks dominate (0.7..1.0 of the height), the rest stay low (0.28..0.5)
'  float Hc=max(Hm*hk*mix(0.28+0.22*r5,0.7+0.3*r5,step(0.5,r2))*wgt(c0)*(0.74+0.26*snoise(vec2(cs*1.37+uSeed.y,t*2.4))),1.0);',
'  float v=max(h,0.0)/Hc;',
// lean in proportion to the lick's own height (a short lick barely leans, a tall one bends over)
'  float px=c0+(r4-0.5)*uD.x*Hc*v+snoise(vec2(cs*2.71+uSeed.x,t*0.8))*min(cell,Hc)*0.35*v*v;',
'  float d=abs(xw-px);',
'  float w=cell*wk*(0.26+0.3*r1)*mix(1.0,1.25,step(0.5,r2))*pow(clamp(1.0-v,0.0,1.0),0.55);',
'  acc=sunion(acc,on*(1.0-smoothstep(w*0.2,w,d))*(1.0-smoothstep(0.55,1.0,v)));',
'  float ww=cell*(0.45+0.2*r1)*(0.6+0.6*clamp(v,0.0,2.0));',
'  wide=max(wide,on*(1.0-smoothstep(ww*0.2,ww,d))*smoothstep(0.45,0.9,v)*(1.0-smoothstep(1.3,1.9,v)));}}',
// ---- 1 / 7: Керри fire. A few wide, unequal licks over a low turbulent bed rise from an emitter line uB.z px BELOW the
// frame's bottom edge (so the frame always hides their base). kind 1 (front layer) is clipped to the niche (desktop) or
// to the row's inner frame (phone) and fades out toward its side walls; the medallion / check / "ВЫ" tab (and on a row
// its plaque / name / hero line) are occluders: the flames burn behind them. kind 7 (back layer, behind all content) is
// the same field above the card's top edge (desktop): the tallest licks continue behind the card, legend, round label.
// uA frame rect; uB=(maxHeight,cell,emitterDepth,smoke); uC=(intensity,heightScale,fuelThreshold,spreadHalfWidth);
// uD=(lean,bedHeight,envelopeCentre,envelopeWidth)
'vec4 kFire(vec2 p,float back){float t=uT;vec2 n0=uA.xy,n1=uA.zw;float cx=0.5*(n0.x+n1.x),ey=n1.y+uB.z;',
' float clip=back>0.5?1.0-smoothstep(-0.5,0.5,p.y-n0.y):1.0-smoothstep(-0.5,0.5,sdBox(p-0.5*(n0+n1),0.5*(n1-n0)));',
' if(clip<=0.0)return vec4(0.0);',
' float Hm=max(uB.x*uC.y,1.0),cell=uB.y,h=ey-p.y;',
' float lit=1.0-smoothstep(uC.w-24.0,uC.w,abs(p.x-cx));if(lit<=0.0)return vec4(0.0);',
' float wall=smoothstep(1.0,10.0,min(p.x-n0.x,n1.x-p.x));',
' float v0=max(h,0.0)/Hm;',
' float sw=snoise(vec2(p.x/56.0+uSeed.x,h/46.0-t*1.3))*0.62+snoise(vec2(p.x/23.0+uSeed.y,h/20.0-t*2.6))*0.38;',
' float xw=p.x+sw*(1.5+26.0*min(v0*v0,2.5));',
' float acc=0.0,wide=0.0;',
// dominant licks + a row of smaller ones offset between them
' licks(xw,h,n0.x,n1.x,cell,Hm,t,0.0,1.0,1.0,acc,wide);',
' licks(xw,h,n0.x+cell*0.43,n1.x,cell*0.58,Hm,t,91.7,0.48,1.25,acc,wide);',
// the bed: one low turbulent body along the whole line that the licks grow out of
' float bn=snoise(vec2(xw/(cell*0.75)+uSeed.x*3.0,t*1.2))*0.5+0.5;',
' float bh=Hm*uD.y*(0.45+0.75*bn)*wgt(xw);',
' acc=sunion(acc,0.9*(1.0-smoothstep(bh*0.35,bh,h))*step(0.0,h));',
' float n=fbm4(vec2(xw/13.0,h/18.0-t*3.0)+uSeed)*0.5+0.5;',
// a second, faster erosion breaks licks off near the tips
' float n2=snoise(vec2(xw/7.0+uSeed.y,h/9.0-t*4.4))*0.5+0.5;',
' float heat=clamp(acc*1.35-(1.0-n)*(0.32+0.95*min(v0,1.0))-(1.0-n2)*0.42*min(v0,1.0),0.0,1.0)*lit;',
' float oc=occl(p)*clip*(back>0.5?1.0:wall);',
' float I=smoothstep(0.0,0.22,heat)*oc*uC.x;',
// the hot core is a broken band: its temperature wanders along the line, so the base reads as embers + flame, not a
// white strip
' float hb=snoise(vec2(xw/17.0+uSeed.y*2.0,t*1.6))*0.5+0.5;',
' float T=heat*(0.22+0.7*pow(clamp(1.0-v0,0.0,1.0),1.8))*(0.74+0.32*hb);',
' vec3 fc=blackbody(T)*I;',
' float sn=fbm3(vec2(xw/26.0,h/24.0-t*1.2)+uSeed.yx*1.3)*0.5+0.5;',
' float sa=wide*lit*oc*smoothstep(0.42,0.8,sn)*uB.w;',
' vec3 sc=mix(vec3(0.12,0.055,0.03),vec3(0.04,0.039,0.038),smoothstep(0.5,1.2,v0));',
' float fa=I*0.3;',
' return vec4(fc+sc*sa*(1.0-fa),fa+sa*(1.0-fa));}',
// ---- 4: wish dissolve behind the logo: cool charcoal tendrils where the medallion was, thinning fast. uA=(cx,cy,R,-);
// uB title rect
'vec4 kDissolve(vec2 p){float k=uK,t=uT,R=uA.z;vec2 r=p-uA.xy;',
' vec2 q=p/(R*0.75)+uSeed;q.y+=t*0.35;q-=r/(length(r)+1.0)*t*0.25;',
' float e=snoise(q*0.5+vec2(0.0,t*0.2));',
' vec2 tc=0.5*(uB.xy+uB.zw),th=0.5*(uB.zw-uB.xy);',
' float sd=min(length(r)-R*(0.7+0.7*k),sdBox(p-tc,th+vec2(4.0+20.0*k)));',
' float m=1.0-smoothstep(-R*0.55,R*0.35,sd+e*R*0.35);',
' float env=smoothstep(0.0,0.1,k)*(1.0-smoothstep(0.4,1.0,k));',
' return wispSmoke(m*env*0.8,q,t,vec3(0.02,0.022,0.027),vec3(0.2,0.21,0.23),uC.x);}',
// ---- 5: hero niche: a veil of dark smoke (never opaque: the portrait shows through) that clears organically — a slow
// noise field swept by a rising threshold, lower toward the bottom and the middle, so the bottom and centre open first
// and the last wisps hang under the top frame; a few streaks escape over the top border. The medallion / check / pick
// mark are occluders. uA niche rect; uB.x scale; uT seconds
'vec4 kVeil(vec2 p){float t=uT,sc=uB.x;vec2 c=0.5*(uA.xy+uA.zw),hs=0.5*(uA.zw-uA.xy);',
' vec2 q=p/(sc*46.0)+uSeed;q.y+=t*1.6;',
' float inN=1.0-smoothstep(-1.0,0.0,sdBox(p-c,hs));',
' vec2 r=(p-c)/hs;float yb=0.5+0.5*r.y;',
// billowed density, warped, rising; vertical streaks erode it into wisps where it thins
' vec2 w=vec2(fbm3(q*0.7+vec2(0.0,t*0.3)),fbm3(q*0.7+vec2(4.3,1.1)));',
' float n=fbm4s(q+0.8*w)*0.5+0.5;',
' float s=fbm3(vec2(q.x*2.6,q.y*0.4)+w+vec2(0.0,-t*0.8))*0.5+0.5;',
// what stays longest: the dense parts and the top; a soft threshold sweeps it away
' float cf=n*0.55+0.35*(1.0-yb)+0.1*min(length(r),1.4);',
' float f=-0.3+1.5*(1.0-pow(1.0-clamp(t/0.62,0.0,1.0),1.25));',
' float m=smoothstep(f-0.22,f+0.22,cf);',
' float env=smoothstep(0.0,0.05,t)*(1.0-smoothstep(0.52,0.72,t));',
' float dd=clamp(m*(0.35+0.85*smoothstep(0.3,0.8,n))-(1.0-s)*0.45*(1.0-0.6*m),0.0,1.0)*inN*env;',
' float al=clamp(pow(dd,1.2)*0.7,0.0,0.7);',
' vec3 dk=vec3(0.018,0.018,0.021),lt=vec3(0.2,0.2,0.215);',
' vec4 a=vec4(mix(vec3(0.05,0.05,0.055),vec3(0.25,0.25,0.26),0.8*smoothstep(0.35,0.9,n))*al,al);',
' float hT=uA.y-p.y;',
' float e=fbm3(q*0.9+vec2(0.0,t*0.5));',
' float xin=1.0-smoothstep(-10.0*sc,0.0,abs(p.x-c.x)-hs.x);',
' float g=0.35+0.65*smoothstep(0.12,0.42,t);',
' float esc=step(0.0,hT)*(1.0-smoothstep(0.0,30.0*sc*g,hT+e*6.0*sc))*smoothstep(0.16,0.28,t)*(1.0-smoothstep(0.46,0.66,t))*xin;',
' vec4 b=wispSmoke(esc*0.8,q,t,dk,lt,0.6);',
' return (a+b)*occl(p);}',
// ---- 6: smoke wipe across the grid (reset / undo); thinned over the role plaques / names (soft occluders). uA grid rect
'float eio(float u){u=clamp(u,0.0,1.0);return u<0.5?4.0*u*u*u:1.0-pow(-2.0*u+2.0,3.0)/2.0;}',
'vec4 kWipe(vec2 p){float k=uK,t=uT;float xf=mix(uA.x-170.0,uA.z+170.0,eio(k));',
' vec2 q=p/80.0+uSeed;q.x-=t*0.9;float e=snoise(q*0.5+vec2(0.0,t*0.2));',
' float band=1.0-smoothstep(10.0,150.0,abs(p.x-xf+e*80.0));',
' float my=smoothstep(uA.y-20.0,uA.y+40.0,p.y+e*40.0)*(1.0-smoothstep(uA.w-40.0,uA.w+20.0,p.y+e*40.0));',
' return wispSmoke(band*my,q,t,vec3(0.018,0.018,0.02),vec3(0.22,0.22,0.23),uC.x)*occl(p);}',
'void main(){vec2 p=vec2(gl_FragCoord.x,uRes.y-gl_FragCoord.y)/uS;vec4 c;',
' if(uKind<1.5)c=kFire(p,0.0);',
' else if(uKind<4.5)c=kDissolve(p);else if(uKind<5.5)c=kVeil(p);else if(uKind<6.5)c=kWipe(p);else c=kFire(p,1.0);gl_FragColor=c;}'
].join('\n');

function GLL(id,isFront){this.id=id;this.front=!!isFront;this.cv=null;this.gl=null;this.ok=false;this.ready=false;this.tried=false;this.fx=[];this.shown=false;this.S=.5;this.u={};this.ver=0;this.ms=-1;this.warm=false;this.lost=0;this.restored=0;this.drawList=[];}
// Context + program are created at once; with KHR_parallel_shader_compile the link finishes off the main thread and
// prepare() polls for it, otherwise the link is awaited (blocking) on first use or at the warm-up timer.
// A lost context (Android WebView: app backgrounded, memory pressure) is rebuilt on webglcontextrestored: same canvas,
// new program / buffer / state; live effects of that moment are dropped, later ones render again.
GLL.prototype.init=function(before){
  if(this.tried)return this.ok;this.tried=true;
  if(NO_GL||!before||!before.parentNode)return false;
  try{
    var cv=doc.createElement('canvas');cv.id=this.id;cv.className='fx-canvas fx-gl';cv.setAttribute('aria-hidden','true');cv.style.display='none';
    var at={alpha:true,premultipliedAlpha:true,antialias:false,depth:false,stencil:false,preserveDrawingBuffer:false,powerPreference:'low-power'};
    var gl=cv.getContext('webgl2',at),ver=2;
    if(!gl){gl=cv.getContext('webgl',at)||cv.getContext('experimental-webgl',at);ver=1;}
    if(!gl)return false;
    var self=this;
    cv.addEventListener('webglcontextlost',function(e){e.preventDefault();self.lost++;self.ok=false;self.ready=false;self.warm=false;self.fx.length=0;self.drawList.length=0;self.shown=false;cv.style.display='none';},false);
    cv.addEventListener('webglcontextrestored',function(){self.restored++;if(self.build()){self.size();setTimeout(function(){self.finish(!self.par);self.warmUp();},50);}kick();},false);
    before.parentNode.insertBefore(cv,before);
    this.cv=cv;this.gl=gl;this.ver=ver;
    if(this.build())this.size();
  }catch(e){this.ok=false;}
  return this.ok;
};
// compile + link (again after a context loss)
GLL.prototype.build=function(){var gl=this.gl;
  try{
    if(gl.isContextLost&&gl.isContextLost()){this.ok=false;return false;}
    this.t0c=performance.now();this.par=gl.getExtension('KHR_parallel_shader_compile');
    var vs=gl.createShader(gl.VERTEX_SHADER),fs=gl.createShader(gl.FRAGMENT_SHADER);
    gl.shaderSource(vs,VS);gl.compileShader(vs);gl.shaderSource(fs,FS);gl.compileShader(fs);
    var pr=gl.createProgram();gl.attachShader(pr,vs);gl.attachShader(pr,fs);gl.bindAttribLocation(pr,0,'aP');gl.linkProgram(pr);
    this.vs=vs;this.fs=fs;this.pr=pr;this.u={};this.ready=false;this.warm=false;this.ok=true;
  }catch(e){this.ok=false;}
  return this.ok;};
// true once the program is usable; never blocks when the parallel-compile extension is present (unless force)
GLL.prototype.finish=function(force){
  if(this.ready||!this.ok)return this.ready;
  var gl=this.gl;
  if(this.par&&!force&&!gl.getProgramParameter(this.pr,this.par.COMPLETION_STATUS_KHR))return false;
  try{
    if(!gl.getProgramParameter(this.pr,gl.LINK_STATUS)){
      if(!gl.isContextLost()&&window.console)console.warn('FX shader:',gl.getShaderInfoLog(this.fs)||gl.getProgramInfoLog(this.pr));
      this.ok=false;this.fx.length=0;return false;}
    var pr=this.pr;gl.useProgram(pr);
    var buf=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array([0,0,1,0,0,1,1,1]),gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,2,gl.FLOAT,false,0,0);
    var u=this.u;['uRes','uS','uQuad','uKind','uT','uK','uA','uB','uC','uD','uO','uSeed','uM','uN'].forEach(function(n){u[n]=gl.getUniformLocation(pr,n);});
    gl.disable(gl.DEPTH_TEST);gl.enable(gl.BLEND);gl.blendFunc(gl.ONE,gl.ONE_MINUS_SRC_ALPHA);gl.clearColor(0,0,0,0);
    this.ready=true;this.ms=Math.round(performance.now()-this.t0c);
  }catch(e){this.ok=false;}
  return this.ready;
};
// Drivers (and SwiftShader) compile / JIT a program for real on its first draw: draw every effect kind once into a 1x1
// viewport while nothing is on screen, so the first roll's Керри reveal does not pay for it.
GLL.prototype.warmUp=function(){
  if(this.warm||!this.finish(false))return;this.warm=true;
  var gl=this.gl,u=this.u,z=[0,0,0,0];
  try{gl.viewport(0,0,1,1);gl.uniform2f(u.uRes,1,1);gl.uniform1f(u.uS,1);gl.uniform4f(u.uQuad,0,0,1,1);gl.uniform1f(u.uN,0);gl.uniform2f(u.uO,0,0);
    gl.uniform4fv(u.uA,[0,0,1,1]);gl.uniform4fv(u.uB,[1,1,1,0]);gl.uniform4fv(u.uC,[0,1,1,1]);gl.uniform4fv(u.uD,z);gl.uniform2f(u.uSeed,0,0);
    [1,4,5,6,7].forEach(function(k){gl.uniform1f(u.uKind,k);gl.uniform1f(u.uT,.1);gl.uniform1f(u.uK,.1);gl.drawArrays(gl.TRIANGLE_STRIP,0,4);});
    gl.clear(gl.COLOR_BUFFER_BIT);gl.finish();
  }catch(e){}
};
// the backing store follows the highest render scale any live effect asks for (this.S)
GLL.prototype.size=function(){if(!this.ok)return;
  var cw=Math.max(1,Math.round(W*this.S)),ch=Math.max(1,Math.round(Hc*this.S));
  if(this.cv.width!==cw||this.cv.height!==ch){this.cv.width=cw;this.cv.height=ch;}
  this.cv.style.width=W+'px';this.cv.style.height=Hc+'px';};
GLL.prototype.add=function(e){if(!this.ok)return false;if(this.fx.length>=5)this.fx.shift();this.fx.push(e);return true;};
GLL.prototype.busy=function(){return this.ok&&this.fx.length>0;};
// Two phases per frame, so the page layout is read in one go: prepare() (both layers, before any 2D drawing) runs the
// effects' preps — all the layout reads — and only records what to draw; draw() (after the 2D layer) does the canvas
// style writes (show / hide / backing size) and the GL draws.
GLL.prototype.prepare=function(t,ox,oy){
  var L=this.fx,D=this.drawList,i;D.length=0;this.want=0;if(!this.ok){L.length=0;return;}
  for(i=L.length-1;i>=0;i--)if(L[i].dead||t>=L[i].t0+L[i].life*1000)L.splice(i,1);
  if(!this.finish(false))return;              // still compiling in parallel: effects wait (their clocks keep running)
  for(i=0;i<L.length;i++){var e0=L[i];if(e0.late&&!e0.began){e0.began=true;if(t>e0.t0)e0.t0=t;}}   // late: clock starts at the first drawable frame
  for(i=0;i<L.length;i++){var e=L[i];if(t<e.t0)continue;
    this.want=Math.max(this.want,e.res||.5);
    var age=(t-e.t0)/1000;e.N=0;e.age=age;
    if(!e.prep(e,ox,oy,age))continue;
    var x0=Math.max(e.Q[0],0),y0=Math.max(e.Q[1],0),x1=Math.min(e.Q[0]+e.Q[2],W),y1=Math.min(e.Q[1]+e.Q[3],Hc);
    if(x1<=x0||y1<=y0)continue;
    e.q4=[x0,y0,x1-x0,y1-y0];D.push(e);}
};
GLL.prototype.draw=function(){
  if(!this.ok||!this.ready)return;
  var gl=this.gl,u=this.u,D=this.drawList,i;
  if(!this.want){if(this.shown){gl.clear(gl.COLOR_BUFFER_BIT);this.cv.style.display='none';this.shown=false;}return;}
  if(Math.abs(this.want-this.S)>.01){this.S=this.want;this.size();}
  if(!this.shown){this.cv.style.display='block';this.shown=true;}
  gl.viewport(0,0,this.cv.width,this.cv.height);gl.clear(gl.COLOR_BUFFER_BIT);
  gl.uniform2f(u.uRes,this.cv.width,this.cv.height);gl.uniform1f(u.uS,this.S);
  for(i=0;i<D.length;i++){var e=D[i],q=e.q4;
    gl.uniform4f(u.uQuad,q[0],q[1],q[2],q[3]);gl.uniform1f(u.uKind,e.kind);gl.uniform1f(u.uT,e.age);gl.uniform1f(u.uK,e.age/e.life);
    gl.uniform4fv(u.uA,e.A);gl.uniform4fv(u.uB,e.B);gl.uniform4fv(u.uC,e.C);gl.uniform4fv(u.uD,e.D);gl.uniform2f(u.uO,e.O[0],e.O[1]);gl.uniform2f(u.uSeed,e.sx,e.sy);
    gl.uniform4fv(u.uM,e.M);gl.uniform1f(u.uN,e.N);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);}
  D.length=0;
};
GLL.prototype.clear=function(grp){if(grp==null){this.fx.length=0;return;}for(var i=this.fx.length-1;i>=0;i--)if(this.fx[i].grp===grp)this.fx.splice(i,1);};
function glBack(){if(!GLB)GLB=new GLL('fxBackGL',false);GLB.init(back);return GLB.ok?GLB:null;}
function glFront(){if(!GLF)GLF=new GLL('fxFrontGL',true);GLF.init(front);return GLF.ok?GLF:null;}
// timelines start at the API call (callT), not after a possibly slow shader compile
var callT=0;
function glEffect(kind,life,delay,prep,grp,res){return {kind:kind,life:life,t0:(callT||now())+(delay||0),sx:rr(0,40),sy:rr(0,40),A:[0,0,0,0],B:[0,0,0,0],C:[1,0,0,0],D:[0,0,0,0],O:[0,0],Q:[0,0,0,0],
  M:new Float32Array(24),N:0,prep:prep,grp:grp||null,res:res||.5,dead:false,age:0,q4:null};}

// ================================================================== geometry helpers
// layout-size box around the element's visual centre (ignores scale animations such as splash-logo-in)
function box(el){if(!el||!el.getBoundingClientRect||!el.isConnected)return null;var r=el.getBoundingClientRect(),w=el.offsetWidth||r.width,h=el.offsetHeight||r.height;
  if(!w||!h||!r.width)return null;var sx=window.scrollX||0,sy=window.scrollY||0,cx=r.left+sx+r.width/2,cy=r.top+sy+r.height/2;
  return {x:cx-w/2,y:cy-h/2,w:w,h:h,cx:cx,cy:cy,s:1};}
// visual box: the element as painted right now, scale animations included (s = current scale)
function vbox(el){if(!el||!el.getBoundingClientRect||!el.isConnected)return null;var r=el.getBoundingClientRect();if(!r.width||!r.height)return null;
  var sx=window.scrollX||0,sy=window.scrollY||0;return {x:r.left+sx,y:r.top+sy,w:r.width,h:r.height,cx:r.left+sx+r.width/2,cy:r.top+sy+r.height/2,s:r.width/(el.offsetWidth||r.width)};}
// the element's current painted scale from its computed transform (CSS animations included); rotation-proof
function paintScale(el){try{var m=getComputedStyle(el).transform;if(!m||m==='none')return 1;var v=/matrix\(([^)]+)\)/.exec(m);if(!v)return 1;
  var a=v[1].split(',').map(parseFloat);return Math.hypot(a[0],a[1])||1;}catch(e){return 1;}}
function chamferOf(el,def){try{var v=parseFloat(getComputedStyle(el).getPropertyValue('--chamfer'));return isFinite(v)?v:def;}catch(e){return def;}}
function inset(b,d){return {x:b.x+d,y:b.y+d,w:b.w-2*d,h:b.h-2*d,cx:b.cx,cy:b.cy,s:b.s};}
function poly(b,shape,ch){if(shape==='hex'){var c=Math.min(ch,b.h/2);
    return [[b.x+c,b.y],[b.x+b.w-c,b.y],[b.x+b.w,b.y+b.h/2],[b.x+b.w-c,b.y+b.h],[b.x+c,b.y+b.h],[b.x,b.y+b.h/2]];}
  return [[b.x,b.y],[b.x+b.w,b.y],[b.x+b.w,b.y+b.h],[b.x,b.y+b.h]];}
function geom(pts){var L=[0],P=0,n=pts.length;for(var i=0;i<n;i++){var a=pts[i],b=pts[(i+1)%n];P+=Math.hypot(b[0]-a[0],b[1]-a[1]);L.push(P);}return {pts:pts,L:L,P:P};}
function at(G,s){var P=G.P;s=((s%P)+P)%P;var i=0,n=G.pts.length;while(i<n-1&&G.L[i+1]<s)i++;var a=G.pts[i],b=G.pts[(i+1)%n],d=G.L[i+1]-G.L[i]||1,f=(s-G.L[i])/d;
  return [a[0]+(b[0]-a[0])*f,a[1]+(b[1]-a[1])*f];}
// points from the tail (f=0) to the head (f=1) of a trail of length len ending at sHead, moving in direction dir; corners kept exact
function trail(G,sHead,dir,len,n){var sT=sHead-dir*len,fs=[],i;for(i=0;i<=n;i++)fs.push(i/n);
  for(i=0;i<G.pts.length;i++){var f=((((G.L[i]-sT)*dir)%G.P)+G.P)%G.P/len;if(f>0&&f<1)fs.push(f);}
  fs.sort(function(a,b){return a-b;});var out=[];for(i=0;i<fs.length;i++){var p=at(G,sT+dir*fs[i]*len);out.push([p[0],p[1],fs[i]]);}return out;}
// open polylines (fuse, smoulder)
function plen(pts){var L=[0];for(var i=1;i<pts.length;i++)L.push(L[i-1]+Math.hypot(pts[i][0]-pts[i-1][0],pts[i][1]-pts[i-1][1]));return L;}
function pat(pts,L,s){s=Math.max(0,Math.min(L[L.length-1],s));var i=0;while(i<pts.length-2&&L[i+1]<s)i++;var d=L[i+1]-L[i]||1,f=(s-L[i])/d;
  return [pts[i][0]+(pts[i+1][0]-pts[i][0])*f,pts[i][1]+(pts[i+1][1]-pts[i][1])*f];}
function pathPoly(g,pts,ox,oy){g.beginPath();for(var i=0;i<pts.length;i++)g[i?'lineTo':'moveTo'](pts[i][0]-ox,pts[i][1]-oy);g.closePath();}
// clip everything except the given page rects (text that must stay clean)
function clipHoles(g,holes,ox,oy){if(!holes||!holes.length)return;g.beginPath();g.rect(-50,-50,W+100,Hc+100);
  for(var i=0;i<holes.length;i++){var h=holes[i];if(h)g.rect(h.x-ox,h.y-oy,h.w,h.h);}g.clip('evenodd');}
function padBox(b,px,py){return b?{x:b.x-px,y:b.y-py,w:b.w+px*2,h:b.h+py*2}:null;}
// UI that effects keep clean: the role legend badges and the round label (page coords, as painted)
// (read once per frame: several effects ask for it)
var legF=-1,legR=[];
function legendRects(){if(legF===nFrames)return legR;legF=nFrames;legR=[];doc.querySelectorAll('#rolesInfo .rbadge-small,#roundBadge').forEach(function(el){var b=vbox(el);if(b)legR.push(b);});return legR;}
// pass the rects that overlap the effect's quad to the shader as occluders (viewport coords, padded)
// (an entry with .r is a circle: centre cx,cy, radius r)
function fillOcc(e,rects,ox,oy,pad){var n=0,q=e.Q;for(var i=0;i<rects.length&&n<6;i++){var r=rects[i],x0,y0,x1,y1;
  if(r.r!=null){x0=r.cx-ox-r.r-pad;y0=r.cy-oy-r.r-pad;x1=x0+2*(r.r+pad);y1=y0+2*(r.r+pad);}else{x0=r.x-ox-pad;y0=r.y-oy-pad;x1=r.x+r.w-ox+pad;y1=r.y+r.h-oy+pad;}
  if(x1<q[0]||x0>q[0]+q[2]||y1<q[1]||y0>q[1]+q[3])continue;
  if(r.r!=null){e.M[n*4]=r.cx-ox;e.M[n*4+1]=r.cy-oy;e.M[n*4+2]=r.r+pad;e.M[n*4+3]=r.cy-oy-1e4;}
  else{e.M[n*4]=x0;e.M[n*4+1]=y0;e.M[n*4+2]=x1;e.M[n*4+3]=y1;}n++;}e.N=n;}
// phone rows: index.html sets --fx-row:1 on .player-card under its phone breakpoint. The card is then a horizontal row
// and its portrait niche only a small thumbnail, so the Керри fire burns along the whole row (inside its frame) and the
// row's text / plaque / round things are the occluders
function rowMode(card){try{return !!card&&getComputedStyle(card).getPropertyValue('--fx-row').trim()==='1';}catch(e){return false;}}
function textBox(el){if(!el||!el.firstChild)return null;try{var rg=doc.createRange();rg.selectNodeContents(el);var r=rg.getBoundingClientRect();if(!r.width||!r.height)return null;
  var sx=window.scrollX||0,sy=window.scrollY||0;return {x:r.left+sx,y:r.top+sy,w:r.width,h:r.height};}catch(e){return null;}}
function rowOcc(card){var out=[],q=function(s){return card.querySelector(s);},b;
  if((b=box(q('.rbadge'))))out.push(padBox(b,2,2));
  if((b=vbox(q('.avatar'))))out.push({cx:b.cx,cy:b.cy,r:b.w/2+4});
  if((b=textBox(q('.pname'))))out.push(padBox(b,3,1));
  var hs=q('.hsel'),hb=hs&&hs.firstChild?vbox(hs):vbox(q('.hero-hint-btn'));if(hb)out.push(padBox(hb,2,2));
  if((b=vbox(q('.toggle'))))out.push({cx:b.cx,cy:b.cy,r:b.w/2+3});
  if((b=vbox(q('.me-tab'))))out.push(b);
  return out;}
// the round / small things inside a card's niche that flames burn behind (as painted, rings and shadows included)
function nicheOcc(card){var out=[],av=card.querySelector('.avatar'),tg=card.querySelector('.toggle'),me=card.querySelector('.me-tab'),pm=card.querySelector('.pick-mark'),b;
  if((b=vbox(av)))out.push({cx:b.cx,cy:b.cy,r:b.w/2+4});
  if((b=vbox(tg)))out.push({cx:b.cx,cy:b.cy,r:b.w/2+3});
  if((b=vbox(me)))out.push(b);if((b=vbox(pm)))out.push({cx:b.cx,cy:b.cy,r:b.w*.72});
  return out;}

// ================================================================== sparks
// p: x,y page coords; T = temperature (1 white-hot .. 0 dead red); lut = colour ramp; oc: sparks go out inside the
// protected rects (legend, round label, other cards) — oc is the element they came from, which is not protected
function spark(x,y,vx,vy,o){if(sparks.length>=CAP_S)return;
  sparks.push({x:x,y:y,vx:vx,vy:vy,g:o.g==null?380:o.g,dr:o.dr==null?1.2:o.dr,tb:o.tb||0,ph:R()*TAU,age:-(o.delay||0),life:o.life||.6,
    T0:o.T0||1,lut:o.lut||FIRE,w:o.w||1.2,tl:o.tl||.032,cool:o.cool==null?1:o.cool,grp:o.grp||null,oc:o.oc||null});}
function burst(x,y,n,o){n=Math.round(n);for(var i=0;i<n;i++){var a=o.ang==null?rr(0,TAU):o.ang+rr(-o.spread,o.spread),v=rr(o.v0,o.v1);
  spark(x+rr(-(o.jx||0),o.jx||0),y+rr(-(o.jy||0),o.jy||0),Math.cos(a)*v,Math.sin(a)*v,
    {g:o.g,dr:o.dr,tb:o.tb,delay:o.delay?rr(0,o.delay):0,life:rr(o.l0||.4,o.l1||.9),T0:rr(o.T0||.85,1),lut:o.lut,w:rr(o.w0||.9,o.w1||1.5),tl:o.tl,cool:o.cool,grp:o.grp,oc:o.oc});}}
var protF=-1,protR=[];
function prot(){if(protF===nFrames)return protR;protF=nFrames;protR=[];
  doc.querySelectorAll('#rolesInfo .rbadge-small,#roundBadge,.player-card,.player-card .avatar,.player-card .toggle').forEach(function(el){var b=vbox(el);if(b)protR.push({el:el,x:b.x,y:b.y,x1:b.x+b.w,y1:b.y+b.h});});return protR;}
function stepSparks(dt){for(var i=sparks.length-1;i>=0;i--){var p=sparks[i];p.age+=dt;
  if(p.age>=p.life){sparks[i]=sparks[sparks.length-1];sparks.pop();continue;}if(p.age<0)continue;
  var f=Math.exp(-p.dr*dt);p.vx*=f;p.vy*=f;p.vy+=p.g*dt;
  if(p.tb){p.vx+=Math.sin(p.y*.045+p.age*5.3+p.ph)*p.tb*dt;p.vy+=Math.cos(p.x*.04+p.age*4.1+p.ph)*p.tb*.4*dt;}
  p.x+=p.vx*dt;p.y+=p.vy*dt;
  if(p.oc){var P=prot();for(var j=0;j<P.length;j++){var r=P[j];if(r.el!==p.oc&&p.x>r.x&&p.x<r.x1&&p.y>r.y&&p.y<r.y1){p.life=Math.min(p.life,p.age+.05);p.oc=null;break;}}}}}
function drawSpark(g,p,x,y,a){var k=p.age/p.life,T=p.T0*Math.pow(1-k,.75*p.cool),L=p.lut,n=L.length-1,ci=Math.max(0,Math.min(n,Math.round(T*n)));
  var sp=Math.hypot(p.vx,p.vy),len=Math.min(30,Math.max(p.w*1.4,sp*p.tl)),ux=sp?p.vx/sp:0,uy=sp?p.vy/sp:-1,dx=ux*len,dy=uy*len;
  g.lineWidth=p.w;g.globalAlpha=a*.5;g.strokeStyle=L[Math.max(0,ci-10)];g.beginPath();g.moveTo(x-dx,y-dy);g.lineTo(x-dx*.4,y-dy*.4);g.stroke();
  g.lineWidth=p.w*1.1;g.globalAlpha=a;g.strokeStyle=L[ci];g.beginPath();g.moveTo(x-dx*.45,y-dy*.45);g.lineTo(x,y);g.stroke();}
function drawSparks(g,ox,oy){if(!sparks.length)return;g.globalCompositeOperation='lighter';g.lineCap='round';
  for(var i=0;i<sparks.length;i++){var p=sparks[i];if(p.age<0)continue;var k=p.age/p.life,a=k<.05?k/.05:k>.65?(1-k)/.35:1;
    if(p.grp==='splash')a*=splashA;
    if(a>.01)drawSpark(g,p,p.x-ox,p.y-oy,a);}
  g.globalAlpha=1;g.globalCompositeOperation='source-over';}

// ================================================================== line magic (2D objects)
// o: {t0,end,draw(g,t,dt,ox,oy),grp}
function addObj(o){objs.push(o);return o;}
function killGroup(grp){for(var i=objs.length-1;i>=0;i--)if(objs[i].grp===grp)objs.splice(i,1);
  for(i=sparks.length-1;i>=0;i--)if(sparks[i].grp===grp)sparks.splice(i,1);
  if(GLB)GLB.clear(grp);if(GLF)GLF.clear(grp);frontDirty=true;}
// a tapered streak with a small white-hot head; pts from tail to head as [x,y,f]
function streak(g,pts,ox,oy,colS,core,wGlow,wCore,fa){fa=fa==null?1:fa;
  for(var pass=0;pass<2;pass++){g.strokeStyle=pass?core:colS;
    for(var j=1;j<pts.length;j++){var f=pts[j][2],a=Math.pow(f,1.6)*fa;g.globalAlpha=pass?a*.95:a*.2;g.lineWidth=pass?.5+wCore*f:1.5+wGlow*f;
      g.beginPath();g.moveTo(pts[j-1][0]-ox,pts[j-1][1]-oy);g.lineTo(pts[j][0]-ox,pts[j][1]-oy);g.stroke();}}
  var hp=pts[pts.length-1],n=pts.length,q=pts[Math.max(0,n-4)];
  g.globalAlpha=fa;g.strokeStyle='#fffbf0';g.lineWidth=1.5;g.beginPath();g.moveTo(q[0]-ox,q[1]-oy);g.lineTo(hp[0]-ox,hp[1]-oy);g.stroke();
  g.fillStyle='#fffdf6';g.beginPath();g.arc(hp[0]-ox,hp[1]-oy,1.15,0,TAU);g.fill();}
// energy trace: two heads leave one point of the outline, run around it in opposite directions with fading trails,
// meet on the far side (spark burst) and the whole outline flashes once. o.visual: follow the element as painted
// (scale animations included), so the trace sits on the edge while the plaque is still settling.
function trace(o){var t0=now()+(o.delay||0),dur=o.dur||480,fl=o.flash||360,c=hex3(o.col)||[224,177,90],lut=mlut(o.col),
    core=rgb(lighten(c,.55)),colS=rgb(c),acc=[0,0],met=false,lastG=null;
  return addObj({t0:t0,end:t0+dur+fl,draw:function(g,t,dt,ox,oy){
    var b=o.el?(o.visual?vbox(o.el):box(o.el)):null;if(b)lastG=geom(poly(inset(b,.5),o.shape,(o.ch||0)*(b.s||1)));var G=lastG;if(!G)return;
    var u=(t-t0)/dur,P=G.P,s0=o.shape==='hex'?(G.L[1]-G.L[0])/2:G.L[1]/2;if(o.start==='bottom')s0+=P/2;
    var cx=0,cy=0;for(var i=0;i<G.pts.length;i++){cx+=G.pts[i][0];cy+=G.pts[i][1];}cx/=G.pts.length;cy/=G.pts.length;
    g.globalCompositeOperation='lighter';g.lineCap='round';g.lineJoin='round';
    if(u<1){var e=1-Math.pow(1-u,1.7),len=Math.min(P*(o.trail||.3),P/2*e+2);
      for(var d=-1;d<=1;d+=2){var sh=s0+d*e*P/2,pts=trail(G,sh,d,len,22);
        streak(g,pts,ox,oy,colS,core,3.5,1.1);
        var hp=pts[pts.length-1];
        // the heads shed small sparks, thrown outward from the outline
        acc[(d+1)/2]+=dt*48*(o.sparks==null?1:o.sparks)*Q;
        while(acc[(d+1)/2]>=1){acc[(d+1)/2]--;var nx=hp[0]-cx,ny=hp[1]-cy,nl=Math.hypot(nx,ny)||1,an=Math.atan2(ny/nl,nx/nl)+rr(-.9,.9),v=rr(40,150);
          spark(hp[0],hp[1],Math.cos(an)*v,Math.sin(an)*v-rr(0,40),{g:260,dr:2,life:rr(.18,.42),T0:rr(.75,1),lut:lut,w:rr(.8,1.2),tl:.03});}}
    }else{
      if(!met){met=true;var m=at(G,s0+P/2),ny2=m[1]-cy,nx2=m[0]-cx,an2=Math.atan2(ny2,nx2);
        burst(m[0],m[1],(o.burst==null?12:o.burst)*Q+3,{ang:an2,spread:1.1,v0:70,v1:230,g:320,dr:1.6,l0:.25,l1:.6,lut:lut,w0:.8,w1:1.3});}
      var v=clamp01((t-t0-dur)/fl),a2=(1-v)*(1-v);pathPoly(g,G.pts,ox,oy);
      g.strokeStyle=colS;g.globalAlpha=a2*.2;g.lineWidth=3;g.stroke();g.strokeStyle=core;g.globalAlpha=a2*.9;g.lineWidth=1;g.stroke();}
    g.globalAlpha=1;g.globalCompositeOperation='source-over';}});}
// light sweep across a plaque, clipped to its visual outline; narrow and soft so the text stays readable
function sheen(o){var t0=now()+(o.delay||0),dur=o.dur||420;
  return addObj({t0:t0,end:t0+dur,draw:function(g,t,dt,ox,oy){var b=vbox(o.el);if(!b)return;var u=eIO((t-t0)/dur);
    g.save();pathPoly(g,poly(b,'hex',(o.ch||0)*b.s),ox,oy);g.clip();
    var bw=b.w*.2,x=b.x-ox-bw+(b.w+bw*2)*u,y0=b.y-oy,y1=y0+b.h,sk=b.h*.32;
    var gr=g.createLinearGradient(x-bw/2,0,x+bw/2,0);gr.addColorStop(0,'rgba(255,246,226,0)');gr.addColorStop(.5,'rgba(255,246,226,'+(o.a||.24)+')');gr.addColorStop(1,'rgba(255,246,226,0)');
    g.fillStyle=gr;g.beginPath();g.moveTo(x-bw/2+sk,y0);g.lineTo(x+bw/2+sk,y0);g.lineTo(x+bw/2-sk,y1);g.lineTo(x-bw/2-sk,y1);g.closePath();g.fill();g.restore();}});}

// ---- rune circle (true circles only — around a round element)
var GLYPHS=[[[0,0,0,1],[0,.8,.32,1],[0,.5,.32,.72]],[[0,0,0,1],[0,1,.32,.62],[.32,.62,.32,0]],[[0,0,0,1],[0,.72,.3,.5],[.3,.5,0,.28]],
  [[-.26,0,-.26,1],[.26,0,.26,1],[-.26,.7,.26,.3]],[[0,0,0,1],[-.3,.75,.3,.25]],[[0,0,0,1]],[[-.3,.5,0,1],[0,1,.3,.5],[.3,.5,0,0],[0,0,-.3,.5]],
  [[0,0,0,1],[0,1,.3,.74],[0,1,-.3,.74]],[[0,0,0,1],[0,.55,.3,.82],[0,.55,-.3,.82]],[[-.3,0,.3,1],[.3,0,-.3,1]],
  [[0,0,0,1],[0,.92,.28,.72],[.28,.72,0,.5],[0,.5,.28,.3],[.28,.3,0,.08]],[[-.26,1,.26,.5],[.26,.5,-.26,0]]];
// stroke an arc a0..a1 (a1>a0) whose alpha varies with the angle (af), batching runs of equal quantised alpha
function arcA(g,cx,cy,r,a0,a1,af,base){if(a1<=a0)return;
  if(!af){g.globalAlpha=base;g.beginPath();g.arc(cx,cy,r,a0,a1);g.stroke();return;}
  var n=Math.max(1,Math.ceil((a1-a0)/.05)),st=(a1-a0)/n,i=0,qa=function(j){return Math.round(af(a0+(j+.5)*st)*8)/8;};
  while(i<n){var q=qa(i),j=i+1;while(j<n&&qa(j)===q)j++;
    if(q>0){g.globalAlpha=base*q;g.beginPath();g.arc(cx,cy,r,a0+i*st,a0+j*st);g.stroke();}i=j;}}
// o: el, r0, r1, col, delay, dur; holes() page rects kept clean; gap() -> {c:angle,h:half-width} where the ring must
// open (e.g. where it would cross the team name), the open ends fade over ~0.35 rad; clip() -> page rect to stay inside;
// thin: a single ring with sparse ticks (small medallions); vis() -> 0..1 extra multiplier (0 ends the ring);
// track: radii follow the element's painted scale (rim = its unscaled radius) and the centre follows it as painted;
// gate(t): the ring only starts once this returns true (or after maxWait ms). The ring always keeps >= topPad px (default 6)
// clear of the viewport top (it fades out instead of being cut).
function runeRing(o){var tc=now(),t0=o.gate?0:tc+(o.delay||0),dur=o.dur||1200,c=hex3(o.col)||[224,177,90],colS=rgb(c),core=rgb(lighten(c,o.thin?.25:.45)),
    rot0=rr(0,TAU),gl=[],band=o.r1-o.r0,big=!o.thin&&band>=10,ng=0,i,mw=o.maxWait||1000;
  if(big){var gh=band-5,gw=gh*.62;ng=Math.max(8,Math.floor(TAU*(o.r0+band/2)/(gw*2.1)));for(i=0;i<ng;i++)gl.push(GLYPHS[(R()*GLYPHS.length)|0]);}
  var obj=addObj({t0:tc,end:o.gate?tc+mw+dur+50:t0+dur,grp:o.grp||null,draw:function(g,t,dt,ox,oy){
    if(!t0){if(o.gate&&!o.gate(t)&&t-tc<mw)return;t0=t+(o.delay||0);obj.end=t0+dur;}
    if(t<t0)return;
    var b=null,s=1;if(o.el){b=o.track?vbox(o.el):box(o.el);if(!b)return;if(o.track)s=paintScale(o.el);}
    var vis=o.vis?o.vis():1;if(vis<=.005)return;
    var cx=(b?b.cx:o.cx)-ox,cy=(b?b.cy:o.cy)-oy,u=(t-t0)/dur,env=(u<.08?u/.08:u>.5?Math.pow((1-u)/.5,1.5):1)*vis*(o.alpha||1),
      grow=1+.02*eOut(u),ds=(s-1)*(o.rim||0),r0=(o.r0+ds)*grow,r1=(o.r1+ds)*grow,dr=eOut(u/.3),rot=rot0+(t-t0)*.00045,a0=rot,a1=rot+TAU*dr,k;
    var r2=r1+3;env*=clamp01((cy-r2-(o.topPad==null?6:o.topPad))/4);if(env<=.005)return;
    var gp=o.gap?o.gap(cy+oy,r1+4):null,af=null;
    if(gp&&gp.h>0){var gc=gp.c,gh2=gp.h;af=function(th){var d=Math.abs((((th-gc)%TAU)+TAU+Math.PI)%TAU-Math.PI);return clamp01((d-gh2)/.35);};}
    g.save();clipHoles(g,o.holes?o.holes():null,ox,oy);
    if(o.clip){var cr=o.clip();if(cr){g.beginPath();g.rect(cr.x-ox,cr.y-oy,cr.w,cr.h);g.clip();}}
    g.globalCompositeOperation='lighter';g.lineCap='butt';
    var c0=-rot*.8,b0=-rot*1.6;
    for(var pass=0;pass<2;pass++){var base=pass?env*(o.thin?.8:.95):env*.2;g.strokeStyle=pass?core:colS;g.lineWidth=pass?(big?1.05:.9):3;
      arcA(g,cx,cy,r1,a0,a1,af,base);
      if(!o.thin)arcA(g,cx,cy,r0,b0-TAU*dr,b0,af,base);
      // outer hairline in arcs with gaps, counter-rotating
      var na=o.thin?2:3,span=o.thin?TAU/5:TAU/3-.24;
      for(k=0;k<na;k++){var s2=c0+k*TAU/na+.12;arcA(g,cx,cy,r2,s2,s2+span*dr,af,base);}
      var nt=o.thin?12:big?72:36;
      for(k=0;k<nt;k++){if(k/nt>dr)break;var ta=a0+k/nt*TAU,ak=af?Math.round(af(ta)*8)/8:1;if(ak<=0)continue;var tl=o.thin?3:k%6?2:big?5:3.5;
        g.globalAlpha=base*ak;g.beginPath();g.moveTo(cx+Math.cos(ta)*r1,cy+Math.sin(ta)*r1);g.lineTo(cx+Math.cos(ta)*(r1-tl),cy+Math.sin(ta)*(r1-tl));g.stroke();}
      if(big){var gh3=(r1-r0)-5,gw3=gh3*.62,rb=r0+2.5;g.lineCap='round';
        for(k=0;k<ng;k++){if(k/ng>dr)break;var ga=a0+(k+.5)/ng*TAU,ag=af?Math.round(af(ga)*8)/8:1;if(ag<=0)continue;var cs=Math.cos(ga),sn=Math.sin(ga),G=gl[k];
          g.globalAlpha=base*ag;g.beginPath();
          for(var j=0;j<G.length;j++){var sg=G[j];
            g.moveTo(cx+cs*(rb+sg[1]*gh3)-sn*sg[0]*gw3,cy+sn*(rb+sg[1]*gh3)+cs*sg[0]*gw3);
            g.lineTo(cx+cs*(rb+sg[3]*gh3)-sn*sg[2]*gw3,cy+sn*(rb+sg[3]*gh3)+cs*sg[2]*gw3);}
          g.stroke();}
        g.lineCap='butt';}}
    // a bright point rides the drawing edge of the outer ring while it is being drawn
    if(dr<1&&(!af||af(a1)>.5)){g.fillStyle='#fff6e0';g.globalAlpha=env;g.beginPath();g.arc(cx+Math.cos(a1)*r1,cy+Math.sin(a1)*r1,1.3,0,TAU);g.fill();}
    g.restore();}});
  return obj;}
// reduced motion: one brief, subtle outline flash
function flashOutline(el,shape,ch,col,circle){var t0=now(),dur=450,c=rgb(lighten(hex3(col)||[224,177,90],.4));
  return addObj({t0:t0,end:t0+dur,draw:function(g,t,dt,ox,oy){var b=box(el);if(!b)return;var a=Math.pow(1-(t-t0)/dur,2)*.6;
    g.strokeStyle=c;g.globalAlpha=a;g.lineWidth=1.4;
    if(circle){g.beginPath();g.arc(b.cx-ox,b.cy-oy,b.w/2+3,0,TAU);}else pathPoly(g,poly(b,shape,ch),ox,oy);g.stroke();g.globalAlpha=1;}});}
// continuous spawner: fn(k) called rate times per second between t0 and t0+dur
function emitter(delay,dur,rate,fn,grp){var t0=now()+delay,acc=0;
  return addObj({t0:t0,end:t0+dur,grp:grp||null,draw:function(g,t,dt){acc+=dt*rate;var k=(t-t0)/dur;while(acc>=1){acc--;fn(k);}}});}

// ================================================================== Керри fire, 2D parts (crisp at full DPR)
// fuse: the ignition — two white-hot heads run from the centre of the niche's bottom frame to its corners, in step with
// the flames spreading behind it (same 0.3 s spread). nb() = the niche box (the whole row's inner frame on phone)
function fireFuse(card,nb,fd,delay){var t0=now()+(delay||0),acc=0;
  return addObj({t0:t0,end:t0+fd+120,draw:function(g,t,dt,ox,oy){var b=nb();if(!b)return;var u=clamp01((t-t0)/fd),s=b.w/2*eOut(u),y=b.y+b.h-.5;
    g.globalCompositeOperation='lighter';g.lineCap='round';
    for(var d=-1;d<=1;d+=2){var pts=[[b.cx,y],[d<0?b.x+.5:b.x+b.w-.5,y]],L=plen(pts),len=Math.min(s,34),tr=[];
      for(var i=0;i<=14;i++){var f=i/14,p=pat(pts,L,s-len+len*f);tr.push([p[0],p[1],f]);}
      if(s>1)streak(g,tr,ox,oy,FIRE[30],FIRE[38],3,1.2,1-clamp01((t-t0-fd)/120));
      if(u<1){acc+=dt*34*Q;while(acc>=1){acc--;var hp=tr[tr.length-1];spark(hp[0],hp[1]-1,rr(-40,40),-rr(80,190),{g:-20,dr:1.6,tb:120,life:rr(.25,.6),T0:rr(.85,1),lut:FIRE,w:rr(.8,1.2),tl:.03,oc:card});}}}
    g.globalAlpha=1;g.globalCompositeOperation='source-over';}});}
// smoulder: as the flames die the niche's bottom frame breaks into short glowing fragments that flicker, cool to dark
// red and go out — no continuous glowing band
function fireSmoulder(nb,life,delay){var t0=now()+(delay||0),fr=[],n=small?8:13;
  for(var i=0;i<n;i++)fr.push({u:rr(0,1),len:rr(6,15),ts:t0+life*1000*rr(.5,.68),dur:rr(450,950),T0:rr(.62,.82),ph:rr(0,TAU),fq:rr(.009,.02)});
  var end=0;fr.forEach(function(f){end=Math.max(end,f.ts+f.dur);});
  return addObj({t0:t0+life*1000*.48,end:end,draw:function(g,t,dt,ox,oy){var b=nb();if(!b)return;var y=b.y+b.h-.5;
    var pts=[[b.x+.5,y-6],[b.x+.5,y],[b.x+b.w-.5,y],[b.x+b.w-.5,y-6]],L=plen(pts),Lt=L[L.length-1];
    g.globalCompositeOperation='lighter';g.lineCap='round';
    for(var i=0;i<fr.length;i++){var f=fr[i],v=(t-f.ts)/f.dur;if(v<0||v>1)continue;
      var T=f.T0*Math.pow(1-v,.7),a=(v<.12?v/.12:1)*Math.pow(1-v,.5)*(.6+.4*Math.sin(t*f.fq+f.ph));
      var s0=f.u*(Lt-f.len),p0=pat(pts,L,s0),pm=pat(pts,L,s0+f.len/2),p1=pat(pts,L,s0+f.len);
      for(var pass=0;pass<2;pass++){g.strokeStyle=fireC(pass?T:T*.8);g.globalAlpha=pass?a:a*.22;g.lineWidth=pass?1.3:3.2;
        g.beginPath();g.moveTo(p0[0]-ox,p0[1]-oy);g.lineTo(pm[0]-ox,pm[1]-oy);g.lineTo(p1[0]-ox,p1[1]-oy);g.stroke();}}
    g.globalAlpha=1;g.globalCompositeOperation='source-over';}});}

// ================================================================== ambient embers (viewport coords, back layer)
function ember(pre){var life=rr(7,12);return {x:rr(0,W),y:pre?rr(H*.25,H+10):H+rr(4,24),vx:rr(-5,5),vy:-rr(10,24),age:pre?rr(0,life*.75):0,life:life,
  T:rr(.32,.55),w:rr(.8,1.25),ph:rr(0,TAU),fq:rr(.4,1.1),fl:rr(4,10),wb:rr(5,12)};}
function stepEmbers(dt){for(var i=embers.length-1;i>=0;i--){var p=embers[i];p.age+=dt;if(p.age>=p.life||p.y<-20){embers.splice(i,1);continue;}
  p.vx+=Math.sin(p.age*p.fq+p.ph)*p.wb*dt;p.vx*=Math.exp(-.4*dt);p.x+=p.vx*dt;p.y+=p.vy*dt;}
  while(ambOn&&!reduced&&!idle()&&embers.length<AMB_N)embers.push(ember(false));}
// ambient embers rest after a minute without any interaction or effect (the loop then stops entirely) and come back on
// the next pointer / key press or effect
var IDLE_MS=60000,lastAct=0;
function idle(){return now()-lastAct>IDLE_MS;}
function touch(){var was=idle();lastAct=now();if(was&&ambOn&&!reduced&&ok&&!embers.length){for(var i=0;i<AMB_N;i++)embers.push(ember(true));}kick();}
function drawEmbers(g){if(!embers.length)return;g.globalCompositeOperation='lighter';g.lineCap='round';
  for(var i=0;i<embers.length;i++){var p=embers[i],k=p.age/p.life,a=(k<.12?k/.12:k>.6?(1-k)/.4:1)*(.6+.4*Math.sin(p.age*p.fl+p.ph));if(a<.02)continue;
    var T=p.T*(.75+.25*Math.sin(p.age*p.fl*.7+p.ph)),ci=Math.round(T*40),dx=p.vx*.28,dy=p.vy*.28;
    g.globalAlpha=a*.45;g.strokeStyle=FIRE[Math.max(0,ci-8)];g.lineWidth=p.w;g.beginPath();g.moveTo(p.x-dx,p.y-dy);g.lineTo(p.x,p.y);g.stroke();
    g.globalAlpha=a;g.strokeStyle=FIRE[ci];g.lineWidth=p.w*1.1;g.beginPath();g.moveTo(p.x-dx*.25,p.y-dy*.25);g.lineTo(p.x,p.y);g.stroke();}
  g.globalAlpha=1;g.globalCompositeOperation='source-over';}

// ================================================================== loop
// Cleared in two overlapping halves on purpose: Chrome intermittently drops a clearRect that covers the whole canvas
// (seen after undo: the last trace frame stayed frozen on screen; a second full clear or two partial clears always work).
function wipe(g,c){g.setTransform(1,0,0,1,0,0);var h=c.height>>1;g.clearRect(0,0,c.width,h+1);g.clearRect(0,h,c.width,c.height-h);g.setTransform(DPR,0,0,DPR,0,0);}
function glBusy(){return (GLB&&GLB.busy())||(GLF&&GLF.busy());}
function kick(){if(!ok||doc.hidden)return;
  if(tmo){clearTimeout(tmo);tmo=0;}
  if(!raf){last=now();raf=requestAnimationFrame(frame);}}
function tick(){tmo=0;if(!raf&&!doc.hidden)raf=requestAnimationFrame(frame);}
function frame(){
  raf=0;nFrames++;if(doc.hidden)return;
  var t=now();
  if(splashWatch)splashWatch();                  // ties every splash effect to the overlay's own opacity / display
  var busy=sparks.length||objs.length||glBusy(),amb=ambOn&&!reduced&&(embers.length>0||!idle()),ox=window.scrollX||0,oy=window.scrollY||0;
  if(GLB)GLB.prepare(t,ox,oy);                   // layout reads only; the GL draws (and canvas style writes) come last
  if(GLF)GLF.prepare(t,ox,oy);
  if(!busy&&!amb){embers.length=0;wipe(bx,back);if(frontDirty){wipe(fx,front);frontDirty=false;}
    if(GLB)GLB.draw();if(GLF)GLF.draw();return;}   // (draw() also hides a GL canvas once its last effect is gone)
  var dt=(t-last)/1000;last=t;if(dt>.07)dt=.07;if(dt<0)dt=0;
  stepEmbers(dt);stepSparks(dt);
  wipe(bx,back);drawEmbers(bx);
  if(objs.length||sparks.length||frontDirty){
    wipe(fx,front);
    for(var i=objs.length-1;i>=0;i--){var o=objs[i];if(t>=o.end){objs.splice(i,1);continue;}}
    // each object draws inside its own save/restore, so a throwing draw can never leave a clip or transform behind
    for(i=0;i<objs.length;i++){if(t>=objs[i].t0){fx.save();try{objs[i].draw(fx,t,dt,ox,oy);}catch(e){objs[i].end=0;if(window.console)console.warn('FX draw',e&&e.message);}fx.restore();}}
    drawSparks(fx,ox,oy);
    frontDirty=objs.length>0||sparks.length>0;}
  if(GLB)GLB.draw();if(GLF)GLF.draw();
  if(sparks.length||objs.length||glBusy())raf=requestAnimationFrame(frame);
  else if(amb)tmo=setTimeout(tick,80);           // ambient only: ~12 fps (slow embers), no vsync wakeups
}
function resize(){
  if(!ok)return;
  var w=doc.documentElement.clientWidth||window.innerWidth,h=window.innerHeight||doc.documentElement.clientHeight,dpr=window.devicePixelRatio||1;
  H=h;
  if(w===W&&dpr===dprSeen&&h<=Hc)return;      // mobile address bar showing/hiding: keep the (taller) backing store
  // a width change (rotation, window resize) re-lays the cards out (phone rows <-> cards): live effects bound to the old
  // geometry stop (ambient embers stay)
  if(W&&w!==W&&(objs.length||sparks.length||glBusy())){objs.length=0;sparks.length=0;if(GLB)GLB.clear();if(GLF)GLF.clear();}
  Hc=(w===W&&dpr===dprSeen)?Math.max(Hc,h):h;W=w;dprSeen=dpr;
  // phone budget by the SHORTER side, so a landscape phone (844x390) is still a phone
  small=Math.min(W,h)<500||dpr>2;DPR=Math.min(dpr,small?1.5:2);Q=small?.6:1;
  CAP_S=small?170:320;AMB_N=small?6:10;
  [back,front].forEach(function(c){c.width=Math.round(W*DPR);c.height=Math.round(Hc*DPR);c.style.height=Hc+'px';});
  [bx,fx].forEach(function(g){g.setTransform(DPR,0,0,DPR,0,0);});
  if(GLB)GLB.size();if(GLF)GLF.size();
  frontDirty=true;
}
function init(){
  try{
    back=doc.createElement('canvas');back.id='fxBack';back.className='fx-canvas';back.setAttribute('aria-hidden','true');
    front=doc.createElement('canvas');front.id='fxFront';front.className='fx-canvas';front.setAttribute('aria-hidden','true');
    bx=back.getContext('2d');fx=front.getContext('2d');if(!bx||!fx)return;
    doc.body.insertBefore(back,doc.body.firstChild);doc.body.appendChild(front);
    ok=true;resize();
    if(!reduced)doc.documentElement.classList.add('fx-sweep');
    var rz=0;window.addEventListener('resize',function(){if(rz)return;rz=requestAnimationFrame(function(){rz=0;resize();kick();});});
    doc.addEventListener('visibilitychange',function(){if(doc.hidden){if(raf){cancelAnimationFrame(raf);raf=0;}if(tmo){clearTimeout(tmo);tmo=0;}}else kick();});
    if(mq){var on=function(){reduced=mq.matches;doc.documentElement.classList.toggle('fx-sweep',!reduced);if(reduced)embers.length=0;kick();};
      if(mq.addEventListener)mq.addEventListener('change',on);else if(mq.addListener)mq.addListener(on);}
    // compile the shader off the critical path, before the first roll needs it, then draw each kind once (warm-up)
    if(!reduced){glBack();glFront();}
    var tries=0,warm=function(){var pend=false;
      [GLB,GLF].forEach(function(g){if(!g||!g.ok||g.warm)return;g.finish(!g.par||tries>=10);g.warmUp();if(!g.warm)pend=true;});
      if(pend&&++tries<=12)setTimeout(warm,300);};
    setTimeout(warm,900);
    lastAct=now();
    doc.addEventListener('pointerdown',touch,{passive:true});doc.addEventListener('keydown',touch);
  }catch(e){ok=false;}
}
function can(){return ok&&!doc.hidden;}
function guard(fn){return function(){try{touch();callT=now();if(can())fn.apply(null,arguments);kick();}catch(e){if(window.console)console.warn('FX',e);}callT=0;};}

// ---- splash lifetime: every splash effect is multiplied by the overlay's computed opacity and is killed (with the
// fx-top lift) the moment the overlay is transparent or display:none, whatever the timers or a slow shader compile did
var splashA=1,splashWatch=null;
function overlayVis(root){if(!root||!root.isConnected)return 0;try{var cs=getComputedStyle(root);if(cs.display==='none'||cs.visibility==='hidden')return 0;
  var o=parseFloat(cs.opacity);return isFinite(o)?o:1;}catch(e){return 0;}}
function endSplash(){splashWatch=null;splashA=0;killGroup('splash');[front,GLF&&GLF.cv].forEach(function(c){if(c)c.classList.remove('fx-top');});}

// ================================================================== effects
var api={};
api.ambient=function(on){try{ambOn=!!on;if(ambOn&&!reduced&&ok&&!embers.length){for(var i=0;i<AMB_N;i++)embers.push(ember(true));}kick();}catch(e){}};
api.token=function(){return ++gen;};
api.clear=function(){gen++;objs.length=0;sparks.length=0;if(GLB)GLB.clear();if(GLF)GLF.clear();frontDirty=true;kick();};
api.info=function(){return {ok:ok,frames:nFrames,compileMs:[GLB?GLB.ms:-1,GLF?GLF.ms:-1],gl:[GLB?GLB.ver*(GLB.ok?1:0):-1,GLF?GLF.ver*(GLF.ok?1:0):-1],
  glScale:[GLB?GLB.S:0,GLF?GLF.S:0],reduced:reduced,small:small,sparks:sparks.length,objs:objs.length,glfx:[GLB?GLB.fx.length:0,GLF?GLF.fx.length:0],
  warm:[!!(GLB&&GLB.warm),!!(GLF&&GLF.warm)],lost:[GLB?GLB.lost:0,GLF?GLF.lost:0],restored:[GLB?GLB.restored:0,GLF?GLF.restored:0],idle:idle(),embers:embers.length};};

// roll press: the button's outline is traced in gold and throws hot sparks; once the logo's shake has settled a rune
// circle draws itself round the medallion (sized from the painted scale, opened at the bottom where it would cross the
// team name). (No smoke column behind the grid any more: it was the costliest shader and read as soft fog.)
api.rollStart=guard(function(o){
  var btn=o.btn,logo=o.logo;
  var title=doc.querySelector('#logoArea .team-name');
  if(reduced){if(btn)flashOutline(btn,'hex',18,GOLD);else if(logo)flashOutline(logo,null,0,GOLD,true);return;}
  var bb=box(btn);
  if(bb){trace({el:btn,shape:'hex',ch:18,col:'#f5b85a',dur:430,trail:.28,sparks:1.4,burst:10});
    burst(bb.cx,bb.y+2,22*Q,{ang:-Math.PI/2,spread:1.15,v0:140,v1:520,g:700,dr:1.4,jx:bb.w*.36,l0:.4,l1:1,lut:FIRE,T0:.85,w0:.9,w1:1.5,cool:1.2,tl:.02});}
  var lb=box(logo);
  // phone header: a 40px medallion beside the title, close to the viewport top -> a tight thin ring, opened toward the title
  if(lb){var D=lb.w,Rr=D/2,sm=D<70,r0=Rr+(sm?3:4),r1=r0+(D>120?12:sm?5:8),tg=now();
    runeRing({el:logo,track:true,rim:Rr,r0:r0,r1:r1,col:'#e9a54c',dur:1250,maxWait:900,topPad:sm?1:6,
      gate:function(t){return t-tg>250&&paintScale(logo)<=1.02;},
      gap:function(cy,ro){var t=box(title);if(!t)return null;var lc=box(logo)||lb,h;
        if(t.x>=lc.cx+Rr*.5){h=t.x-4-lc.cx;return h<ro?{c:0,h:Math.acos(Math.max(-1,Math.min(1,h/ro)))}:null;}   // title beside it
        h=t.y-4-cy;return h<ro?{c:Math.PI/2,h:Math.acos(Math.max(-1,Math.min(1,h/ro)))}:null;},
      holes:function(){var t=box(title);return t?[padBox(t,4,2)]:null;}});}
});

// run fn once, ms from now, as a cancellable object (killed with everything else by clear())
function later(ms,fn){var t0=now()+ms,done=false;return addObj({t0:t0,end:t0+60,draw:function(){if(!done){done=true;fn();}}});}

// role reveal: once the plaque has landed (~0.44 s into its reveal animation), two heads run round its own chamfered
// outline (as painted) in the role colour, then a light sweep crosses it. Керри answers its plaque: from that same moment
// a fuse runs out along the bottom frame and fire takes the frame — desktop: the portrait niche (the tallest licks
// continue behind the card, legend and round label on the back layer); phone rows: the row's inner frame, weighted to
// the portrait side, behind its plaque / name / hero line. Embers lift off, the frame smoulders out in fragments.
api.reveal=guard(function(card,badge,role,tok){
  if(tok!==undefined&&tok!==gen)return;          // a timer left over from a cancelled roll
  var col=ROLE_COL[role]||'#e0b15a',carry=role==='Керри',mid=role==='Мидер',ch=chamferOf(badge,10);
  if(!box(badge))return;
  if(reduced){flashOutline(badge,'hex',ch,col);return;}
  trace({el:badge,visual:true,shape:'hex',ch:ch,col:col,delay:440,dur:carry?500:mid?460:430,trail:carry?.34:.3,sparks:carry?1.5:mid?1.2:1,burst:carry?16:mid?13:10});
  sheen({el:badge,ch:ch,delay:470,dur:carry?480:420,a:carry?.28:.22});
  if(!carry)return;
  // desktop / 2-column phone: the portrait niche. Phone rows: the row's inner frame (the flames run along the whole row,
  // front layer only, behind its plaque / name / hero line / medallion; nothing above the card, the rows sit 6 px apart)
  var row=rowMode(card),slot=card.querySelector('.slot'),nbf=row?function(){var c=box(card);return c?inset(c,1):null;}:function(){return box(slot);},nb=nbf();if(!nb)return;
  var FD=440,life=2.5,LF=glFront(),LB=row?null:glBack();
  // a few wide, unequal licks (about 4-5 across the frame) over a low bed — never a comb of thin equal tongues
  var Hm=row?nb.h*1.45:nb.h*1.6,cell=row?nb.w/4.6:nb.w/4.4,thr0=row?.14:.2,dep=row?8:10,lean=row?.3:.45,bed=row?.17:.13;
  // one flame field, drawn in two parts with the same seed and clock: inside the frame (front) and above the card (back)
  var prep=function(back){return function(e,ox,oy,a){var b=nbf()||nb,x0=b.x-ox,y0=b.y-oy;
      e.A[0]=x0;e.A[1]=y0;e.A[2]=x0+b.w;e.A[3]=y0+b.h;
      var hs=eOut(a/.3)*(a<1.3?1:1-.85*eIO((a-1.3)/1.0)),thr=thr0+(a>1.15?eIO((a-1.15)/1.05)*(1.08-thr0):0);
      e.B[0]=Hm;e.B[1]=cell;e.B[2]=dep;e.B[3]=.3*(a<2?1:1-clamp01((a-2)/.5));
      // the spread runs out from the centre with the fuse and stops short of the side walls (no flame cut by the clip)
      e.C[0]=a<1.35?1:1-.5*eIO((a-1.35)/1.0);e.C[1]=Math.max(.02,hs);e.C[2]=thr;e.C[3]=(b.w/2-12)*eOut(a/.4)+6;
      e.D[0]=lean;e.D[1]=bed;e.D[2]=row?x0+b.w*.3:0;e.D[3]=row?b.w*.45:0;
      if(back){var top=y0+b.h+dep-Hm*1.9;e.Q[0]=x0;e.Q[1]=top;e.Q[2]=b.w;e.Q[3]=y0+1-top;fillOcc(e,legendRects(),ox,oy,2);}
      else{e.Q[0]=x0-1;e.Q[1]=y0-1;e.Q[2]=b.w+2;e.Q[3]=b.h+2;fillOcc(e,row?rowOcc(card):nicheOcc(card),ox,oy,row?1:0);}
      return true;};};
  var ef=LF?glEffect(1,life,FD,prep(false),null,RES('hi')):null,eb=LB&&ef?glEffect(7,life,FD,prep(true),null,RES('hi')):null;
  if(ef){LF.add(ef);if(eb){eb.sx=ef.sx;eb.sy=ef.sy;LB.add(eb);}}
  fireFuse(card,nbf,380,FD);                     // the fuse runs out with the flames' spread (0.4 s)
  fireSmoulder(nbf,life,FD);
  // embers lift off the flames: hot, buoyant, turbulent; they cool from white-yellow to red and go out on the avatar,
  // the presence check, the legend, the round label or another card
  var rate=(ef?28:56)*Q*(row?1.2:1);
  emitter(FD+60,1500,rate,function(k){if(R()<k*k)return;var b=nbf()||nb,x=b.x+b.w*(row?Math.pow(R(),1.6)*.9+.03:rr(.06,.94)),y=b.y+b.h*rr(ef?(row?.4:.25):.9,ef?.85:1);
    spark(x,y,rr(-25,25),-rr(80,210),{g:-30,dr:1.2,tb:240,life:rr(.6,1.3),T0:rr(.8,1),lut:FIRE,w:rr(.9,1.4),tl:.04,cool:1.1,oc:card});});
  later(FD,function(){var b=nbf()||nb;burst(b.cx,b.y+b.h-2,(ef?14:28)*Q,{ang:-Math.PI/2,spread:.9,v0:110,v1:300,g:380,dr:1.4,jx:b.w*.4,l0:.45,l1:.95,lut:FIRE,T0:.9,w0:1,w1:1.5,delay:.1,oc:card});});
});

// wish phrase: the beat is ordered — cool smoke takes the logo first (the CSS fades the logo in ~0.26 s and the phrase in
// after it), then light runs out along the phrase's two hairlines (only once the logo is below 10 % opacity), then a
// few hot gold motes rise off the text
api.wish=guard(function(tok){
  if(tok!==undefined&&tok!==gen)return;
  var wt=doc.getElementById('wishText');
  if(wt){wt.classList.remove('fx-ignite');void wt.offsetWidth;wt.classList.add('fx-ignite');wt.addEventListener('animationend',function(){wt.classList.remove('fx-ignite');},{once:true});}
  var wb=box(wt);
  if(reduced){if(wb)flashOutline(wt,'rect',0,GOLD);return;}
  var logo=doc.getElementById('logo'),title=doc.querySelector('#logoArea .team-name'),lb=box(logo),tb=box(title),L=glBack();
  // not for the phone header's 40px medallion: scaled to it the smoke is a fine grey band across the header row that
  // only dulls the phrase (seen in capture); there the hairline runs and the motes carry the beat
  if(lb&&L&&lb.w>=70){var R0=lb.w/2;
    L.add(glEffect(4,1.4,0,function(e,ox,oy){var b=box(logo)||lb,t=box(title)||tb||{x:b.cx,y:b.cy,w:1,h:1};
      e.A[0]=b.cx-ox;e.A[1]=b.cy-oy;e.A[2]=R0;e.B[0]=t.x-ox;e.B[1]=t.y-oy;e.B[2]=t.x+t.w-ox;e.B[3]=t.y+t.h-oy;e.C[0]=.6;
      var x0=Math.min(b.cx-R0*2.6,t.x-60),x1=Math.max(b.cx+R0*2.6,t.x+t.w+60),y0=b.cy-R0*2.8,y1=Math.max(b.cy+R0*2,t.y+t.h+50);
      e.Q[0]=x0-ox;e.Q[1]=y0-oy;e.Q[2]=x1-x0;e.Q[3]=y1-y0;return true;},null,RES('mid')));}
  if(!wb)return;
  var la=doc.getElementById('logoArea'),gate=function(){return overlayVis(la)<.1;};
  lineRun(wt,0,GOLD,0,gate);lineRun(wt,1,GOLD,90,gate);
  var rects=[];
  if(wt&&wt.firstChild){try{var rg=doc.createRange();rg.selectNodeContents(wt);rects=Array.prototype.slice.call(rg.getClientRects()).filter(function(r){return r.width>4;});}catch(e){}}
  if(!rects.length)return;
  var sx=window.scrollX||0,sy=window.scrollY||0,lines=rects.map(function(r){return {x:r.left+sx,y:r.top+sy,w:r.width,h:r.height};});
  emitter(550,1900,(small?14:24),function(k){if(R()<k*k)return;var r=lines[(R()*lines.length)|0];
    spark(r.x+r.w*rr(.03,.97),r.y+r.h*rr(.2,.75),rr(-12,12),-rr(30,80),{g:-12,dr:.8,tb:90,life:rr(1,1.9),T0:rr(.6,.85),lut:FIRE,w:rr(.8,1.15),tl:.09,cool:.8});});
});
// light running outward from the centre of one of the wish phrase's hairlines (.wish::before / ::after: 1px, at their
// margin inside the paragraph box — 14px / min(340px,60%) on desktop, smaller on phone — read from the pseudo-element's
// computed style); starts only when gate() allows (logo gone), +delay
function hairline(wt,which){try{var cs=getComputedStyle(wt,which?'::after':'::before');if(cs.display==='none'||cs.content==='none')return {none:true};
  return {m:parseFloat(which?cs.marginBottom:cs.marginTop),w:parseFloat(cs.width)};}catch(e){return null;}}
function lineRun(wt,which,col,delay,gate){var tc=now(),t0=0,dur=620,fl=420,c=hex3(col),colS=rgb(c),core=rgb(lighten(c,.6));
  var o=addObj({t0:tc,end:tc+2600,draw:function(g,t,dt,ox,oy){
    if(!t0){if(gate&&!gate())return;t0=t+delay;o.end=t0+dur+fl;}
    if(t<t0)return;var b=box(wt);if(!b)return;
    var hl=hairline(wt,which);if(hl&&hl.none){o.end=0;return;}   // that hairline is hidden (phone room mode, longest phrases)
    var m=hl&&isFinite(hl.m)?hl.m:14,hw=(hl&&hl.w>0?hl.w:Math.min(340,b.w*.6))/2,u=(t-t0)/dur,x=b.cx-ox,yy=(which?b.y+b.h-m-.5:b.y+m+.5)-oy;
    g.globalCompositeOperation='lighter';g.lineCap='round';
    if(u<1){var e=eOut(u),hx=hw*e,tl=Math.min(hx,hw*.5);
      for(var d=-1;d<=1;d+=2){var gr=g.createLinearGradient(x+d*(hx-tl),0,x+d*hx,0);gr.addColorStop(0,'rgba(0,0,0,0)');gr.addColorStop(1,core);
        g.strokeStyle=gr;g.globalAlpha=.95;g.lineWidth=1.2;g.beginPath();g.moveTo(x+d*(hx-tl),yy);g.lineTo(x+d*hx,yy);g.stroke();
        g.fillStyle='#fff4d8';g.beginPath();g.arc(x+d*hx,yy,1.1,0,TAU);g.fill();}}
    else{var a=Math.pow(1-clamp01((t-t0-dur)/fl),2);g.strokeStyle=colS;g.globalAlpha=a*.55;g.lineWidth=1;g.beginPath();g.moveTo(x-hw,yy);g.lineTo(x+hw,yy);g.stroke();}
    g.globalAlpha=1;g.globalCompositeOperation='source-over';}});}

// hero pick: gold light runs round the portrait niche; inside the niche a veil of smoke (never fully opaque) clears from
// the middle outward by ~0.45 s, and a few tendrils escape over the top frame for ~0.2 s (they stay off the legend).
// random pick: muted arcane trace plus a thin rune circle round the avatar medallion, kept inside the niche
api.heroPick=guard(function(pi,isRandom){
  var s=doc.getElementById('slot-'+pi),sb=box(s);if(!sb)return;
  var col=isRandom?ARCANE:'#ffd27a',card=doc.getElementById('card-'+pi),row=rowMode(card);
  if(reduced){flashOutline(s,'rect',0,col);return;}
  trace({el:s,shape:'rect',col:col,start:'bottom',delay:40,dur:520,trail:.26,sparks:isRandom?.6:.8,burst:isRandom?7:10});
  if(!isRandom){var L=glFront();
    // phone row: the niche is a ~56 px thumbnail, so the smoke grain scales down further
    if(L){var sc=row?Math.min(1.2,Math.max(.42,sb.w/140)):Math.min(1.2,Math.max(.62,sb.w/240)),g0=gen,started=false;
      var go=function(){if(started||g0!==gen||!s.isConnected)return;started=true;callT=now();
        L.add(glEffect(5,.72,0,function(e,ox,oy){var b=box(s)||sb;
          e.A[0]=b.x-ox;e.A[1]=b.y-oy;e.A[2]=b.x+b.w-ox;e.A[3]=b.y+b.h-oy;e.B[0]=sc;
          e.Q[0]=b.x-ox-4;e.Q[1]=b.y-oy-36*sc;e.Q[2]=b.w+8;e.Q[3]=b.h+36*sc;
          // the medallion / check / pick mark stay clean, then the legend above the card
          fillOcc(e,card?nicheOcc(card).concat(legendRects()):legendRects(),ox,oy,1);return true;},null,RES('hi')));
        callT=0;kick();};
      // the veil unveils the portrait, so it waits for the image to be decoded (a first pick loads it from the CDN),
      // at most ~0.3 s; a cancelled roll (clear / new token) in between drops it
      var im=s.querySelector('img.slot-art');
      if(im&&!(im.complete&&im.naturalWidth)){var fire1=function(){go();};
        if(im.decode)im.decode().then(fire1,fire1);else{im.addEventListener('load',fire1,{once:true});im.addEventListener('error',fire1,{once:true});}
        setTimeout(fire1,300);}
      else go();}
  }else{
    var av=doc.getElementById('avatar-'+pi),ab=box(av);
    // phone row: the medallion is a small badge in the thumbnail's corner; its ring may use the row's padding
    if(ab){var r=ab.w/2;runeRing({el:av,r0:r+4,r1:r+6,thin:true,col:ARCANE,alpha:.8,delay:80,dur:1100,clip:function(){return row&&card?box(card):box(s);}});
      burst(ab.cx,ab.cy,6*Q+3,{v0:50,v1:120,g:120,dr:2.2,l0:.25,l1:.55,lut:mlut(ARCANE),w0:.8,w1:1.1,jx:r*.2,jy:r*.2,delay:.2});}
  }
});

// splash: a rune circle draws itself round the medallion and hot embers lift off its rim — no smoke (two rounds of
// splash smoke read as fog banks; the circle and the embers carry the beat). Everything is bound to the overlay.
api.splash=guard(function(el,ms){
  var b=box(el);if(!b)return;
  var root=(el.closest&&el.closest('#splashScreen'))||el.parentNode;
  [front,GLF&&GLF.cv].forEach(function(c){if(c)c.classList.add('fx-top');});
  splashA=1;var st=now();
  splashWatch=function(){splashA=overlayVis(root);if(splashA<=.01&&now()-st>100)endSplash();};
  setTimeout(function(){if(splashWatch)endSplash();},(ms||2700)+600);   // safety net only
  if(reduced){flashOutline(el,null,0,'#e9a54c',true);return;}
  var D=b.w,name=doc.getElementById('splashName');
  var vis=function(){return splashA;};
  runeRing({el:el,r0:D*.57,r1:D*.57+16,col:'#e9a54c',delay:380,dur:1350,grp:'splash',vis:vis,holes:function(){var t=box(name);return t?[padBox(t,6,2)]:null;}});
  emitter(500,700,(small?22:36),function(){var bb=box(el)||b,a=rr(0,TAU),r=D*.53;
    spark(bb.cx+Math.cos(a)*r,bb.cy+Math.sin(a)*r,Math.cos(a)*rr(40,120),Math.sin(a)*rr(40,120)-rr(20,90),{g:-25,dr:1,tb:160,life:rr(.5,.95),T0:rr(.75,1),lut:FIRE,w:rr(.9,1.4),tl:.04,grp:'splash'});},'splash');
});

// achievement toast (restrained): once the plate has landed, gold light runs round its frame (two heads, meet, one
// flash), a thin rune circle draws itself round the emblem's round socket, and a narrow light sweep crosses the plate.
// Line art only — no glow sprites.
api.achievement=guard(function(el,socket){
  if(!box(el))return;
  if(reduced){flashOutline(el,'rect',0,GOLD);return;}
  trace({el:el,visual:true,shape:'rect',col:'#f2c46e',dur:560,trail:.22,sparks:.45,burst:6});
  sheen({el:el,ch:0,delay:420,dur:620,a:.12});
  var sb=box(socket);
  if(sb){var r=sb.w/2;runeRing({el:socket,r0:r+5,r1:r+7,thin:true,col:'#e9a54c',alpha:.85,delay:160,dur:1400});}
});

// reset / undo: a band of wispy smoke passes across the grid (no-op without WebGL)
api.sweep=guard(function(el){
  var b=box(el),L=b&&!reduced?glFront():null;if(!L)return;
  // per card: the name + role plaque area (one rect per card, so five fit), where the smoke only thins to ~25 %
  var textRects=function(){var out=[];doc.querySelectorAll('.player-card').forEach(function(c){var a=textBox(c.querySelector('.pname')),r=box(c.querySelector('.rbadge'));
    if(!a&&!r)return;if(!a)a=r;if(!r)r=a;var x0=Math.min(a.x,r.x),y0=Math.min(a.y,r.y),x1=Math.max(a.x+a.w,r.x+r.w),y1=Math.max(a.y+a.h,r.y+r.h);
    out.push({x:x0-4,y:y0-3,w:x1-x0+8,h:y1-y0+6});});return out;};
  L.add(glEffect(6,1.1,0,function(e,ox,oy){var g=box(el)||b;e.A[0]=g.x-ox;e.A[1]=g.y-oy;e.A[2]=g.x+g.w-ox;e.A[3]=g.y+g.h-oy;e.C[0]=.55;
    e.Q[0]=g.x-ox-170;e.Q[1]=g.y-oy-30;e.Q[2]=g.w+340;e.Q[3]=g.h+60;fillOcc(e,textRects(),ox,oy,0);e.O[0]=14;e.O[1]=.25;return true;},null,RES('mid')));
});

if(doc.body)init();else doc.addEventListener('DOMContentLoaded',init);
window.FX=api;
})();
