import Mathlib
import PEqualNP.Defs
-- Helpers: the accepted proof of L-meta-1625, inlined and compacted; the last theorem derives this step from it.
namespace PEqualNP.Outside.L_meta_1690.P1622
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma Zf {α:Type} (l l':List α) (d:α) (i:ℕ) (h:i< l.length) :
  (l++l').getD i d= l.getD i d:=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_append_left h]
lemma Zp {α:Type} (l:List α) (a d:α):(l++[a]).getD l.length d= a:=by
 simp[List.getD_eq_getElem?_getD]
lemma Z2l {α:Type} (l:List α) (d:α) (i:ℕ) (h:l.length≤ i):l.getD i d= d:=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
def Z0:Gate:=Gate.mk GateOp.or []
def run {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α):List α:=
 gs.foldl (fun w g=>w++[f w g]) w
lemma Z1b {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (g:Gate) (w:List α) :
  run f (gs++[g]) w= run f gs w++[f (run f gs w) g]:=by
 simp[run]
lemma Z22 {α:Type} (f:List α→ Gate→ α) (g1 g2:List Gate) (w:List α) :
  run f (g1++g2) w= run f g2 (run f g1 w):=by
 simp[run]
lemma Zb {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α) :
  (run f gs w).length= w.length+gs.length:=by
 induction gs using List.reverseRecOn with
 | nil=>simp[run]
 | append_singleton gs g ih=>rw[Z1b]; simp[ih]; omega
lemma Z3m {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α) (d:α) (i:ℕ)
  (h:i< w.length):(run f gs w).getD i d= w.getD i d:=by
 induction gs using List.reverseRecOn with
 | nil=>rfl
 | append_singleton gs g ih=>
  rw[Z1b,Zf _ _ _ _ (by rw[Zb]; omega),ih]
lemma Z3n {α:Type} (f:List α→ Gate→ α) (d:α)
  (hf:∀ (g:Gate) (w w':List α),(∀ i∈g.inputs,w.getD i d= w'.getD i d)→ f w g= f w' g)
  (gs:List Gate) (w:List α) (L:ℕ) (hL:w.length= L) (k:ℕ) (hk:k< gs.length)
  (hr:∀ i∈(gs.getD k Z0).inputs,i< L+k) :
  (run f gs w).getD (L+k) d= f (run f gs w) (gs.getD k Z0):=by
 subst hL
 induction gs using List.reverseRecOn with
 | nil=>simp at hk
 | append_singleton gs g ih=>
  rw[Z1b];rcases Nat.lt_or_ge k gs.length with h | h
  ·have e:(gs++[g]).getD k Z0= gs.getD k Z0:=Zf _ _ _ _ h
   rw[e] at hr ⊢;rw[Zf _ _ _ _ (by rw[Zb]; omega),ih h hr]
   apply hf;intro i hi;symm;exact Zf _ _ _ _ (by rw[Zb]; have:=hr i hi; omega)
  ·have hk':k= gs.length:=by
    simp only[List.length_append,List.length_singleton] at hk;omega
   subst hk';have e:(gs++[g]).getD gs.length Z0= g:=Zp _ _ _;rw[e] at hr ⊢;have e2:w.length+gs.length=(run f gs w).length:=(Zb f gs w).symm;rw[e2,Zp];apply hf;intro i hi;symm;exact Zf _ _ _ _ (by rw[Zb]; have:=hr i hi; omega)
def evf (w:List Bool) (g:Gate):Bool:=g.op.eval (g.inputs.map fun i=>w.getD i false)
def ldf (d:List ℕ) (g:Gate):ℕ:=g.lineDegree d
lemma Z4u (g:Gate) (w w':List Bool)
  (h:∀ i∈g.inputs,w.getD i false= w'.getD i false):evf w g= evf w' g:=by
 unfold evf;rw[List.map_congr_left h]
lemma Z4v (g:Gate) (w w':List ℕ)
  (h:∀ i∈g.inputs,w.getD i 0= w'.getD i 0):ldf w g= ldf w' g:=by
 unfold ldf Gate.lineDegree;rw[List.map_congr_left h]
def RBL (n:ℕ) (gs:List Gate):Prop:=
 ∀ j< gs.length,∀ i∈(gs.getD j Z0).inputs,i< n+j
lemma Z1k (n:ℕ) (g1 g2:List Gate) (h1:RBL n g1) (h2:RBL (n+g1.length) g2) :
  RBL n (g1++g2):=by
 intro j hj i hi;rcases Nat.lt_or_ge j g1.length with h | h
 ·rw[Zf _ _ _ _ h] at hi
  exact h1 j h i hi
 ·rw[List.getD_append_right _ _ _ _ h] at hi
  simp only[List.length_append] at hj;have:=h2 (j-g1.length) (by omega) i hi
  omega
lemma Z2a (n:ℕ) (gs:List Gate) (h:∀ g∈gs,g.inputs=[]):RBL n gs:=by
 intro j hj i hi;have hm:gs.getD j Z0∈gs:=by
  rw[List.getD_eq_getElem _ _ hj];exact List.getElem_mem _
 rw[h _ hm] at hi;simp at hi
lemma Z3o (n:ℕ) (gs:List Gate) (g:Gate) (h1:RBL n gs)
  (h2:∀ i∈g.inputs,i< n+gs.length):RBL n (gs++[g]):=by
 apply Z1k _ _ _ h1;intro j hj i hi;simp only[List.length_singleton] at hj;have hj0:j=0:=by omega
 subst hj0;have:=h2 i (by simpa using hi)
 omega
def Z11 (B:ℕ) (st:(ℕ→ ℕ)× List Gate):Prop:=
 (∀ w,st.1 w< B+st.2.length) ∧
 (∀ g∈st.2,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2) ∧
 RBL B st.2
def Zj (B:ℕ) (st:(ℕ→ ℕ)× List Gate) (a src:ℕ):(ℕ→ ℕ)× List Gate:=
 (Function.update st.1 a (B+st.2.length),st.2++[Gate.mk GateOp.or [st.1 a,src]])
def Z23 (B:ℕ) (st:(ℕ→ ℕ)× List Gate) (W tgt side:ℕ):(ℕ→ ℕ)× List Gate:=
 Zj B (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]) tgt (B+st.2.length)
def Z4i:GateOp→ Bool
 | GateOp.and=>true
 | _=>false
def Zy (B:ℕ) (deg:List ℕ) (op:GateOp) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate):(ℕ→ ℕ)× List Gate:=
 if 0< deg.getD W 0 then
  if Z4i op= true∧l.length=2 then
   if 0< deg.getD (l.getD 0 0) 0 then Z23 B st W (l.getD 0 0) (l.getD 1 0)
   else Z23 B st W (l.getD 1 0) (l.getD 0 0)
  else l.foldl (fun s a=>Zj B s a (st.1 W)) st
 else st
def Zn (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (w:ℕ):Bool:=
 (run evf st.2 base).getD (st.1 w) false
lemma Z3d (B:ℕ) (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (a src:ℕ)
  (hB:base.length= B) (hg:Z11 B st) (hs:src< B+st.2.length) :
  Z11 B (Zj B st a src)∧(Zj B st a src).2.length= st.2.length+1 ∧
  (∀ i< B+st.2.length,
   (run evf (Zj B st a src).2 base).getD i false=(run evf st.2 base).getD i false) ∧
  ∀ w,Zn base (Zj B st a src) w =
   (Zn base st w || (decide (w= a) && (run evf st.2 base).getD src false)):=by
 obtain⟨g1,g2,g3⟩:=hg;have hlen:(run evf st.2 base).length= B+st.2.length:=by rw[Zb,hB]
 have hrun:run evf (Zj B st a src).2 base= run evf st.2 base ++
   [((run evf st.2 base).getD (st.1 a) false || (run evf st.2 base).getD src false)]:=by
  simp[Zj,Z1b,evf,GateOp.eval]
 refine⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
 ·intro w
  simp only[Zj,List.length_append,List.length_singleton,Function.update_apply];split_ifs
  ·omega
  ·have:=g1 w
   omega
 ·intro g hg
  simp only[Zj,List.mem_append,List.mem_singleton] at hg;rcases hg with hg | rfl
  ·exact g2 g hg
  ·exact⟨Or.inr rfl,by simp⟩
 ·apply Z3o _ _ _ g3
  intro i hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl | rfl
  ·exact g1 a
  ·exact hs
 ·simp[Zj]
 ·intro i hi
  rw[hrun];exact Zf _ _ _ _ (by omega)
 ·intro w
  unfold Zn;rw[hrun];by_cases hw:w= a
  ·subst hw
   have e:(Zj B st w src).1 w=(run evf st.2 base).length:=by simp[Zj,hlen]
   rw[e,Zp];simp
  ·have e:(Zj B st a src).1 w= st.1 w:=by simp[Zj,hw]
   rw[e,Zf _ _ _ _ (by have:=g1 w; omega)]
   simp[hw]
lemma Z2m {α:Type} (c:Prop) [Decidable c] (a b:α) (h:c):(if c then a else b)= a:=by
 simp[h]
lemma Z31 {α:Type} (c:Prop) [Decidable c] (a b:α) (h:¬ c):(if c then a else b)= b:=by
 simp[h]
lemma Z56 (p q r s:Bool):((p || (q && s)) || (r && s))=(p || ((q || r) && s)):=by
 cases p <;> cases q <;> cases r <;> cases s <;> rfl
lemma Z4w (B:ℕ) (base:List Bool) (src:ℕ) (hB:base.length= B) (l:List ℕ) :
  ∀ (st:(ℕ→ ℕ)× List Gate),Z11 B st→ src< B+st.2.length →
  Z11 B (l.foldl (fun s a=>Zj B s a src) st) ∧
  (l.foldl (fun s a=>Zj B s a src) st).2.length= st.2.length+l.length ∧
  (∀ i< B+st.2.length,
   (run evf (l.foldl (fun s a=>Zj B s a src) st).2 base).getD i false =
    (run evf st.2 base).getD i false) ∧
  ∀ w,Zn base (l.foldl (fun s a=>Zj B s a src) st) w =
   (Zn base st w || (decide (w∈l) && (run evf st.2 base).getD src false)):=by
 induction l with
 | nil=>
  intro st hg _;simp[hg]
 | cons a l ih=>
  intro st hg hs;obtain⟨k1,k2,k3,k4⟩:=Z3d B base st a src hB hg hs;obtain⟨j1,j2,j3,j4⟩:=ih (Zj B st a src) k1 (by omega)
  rw[List.foldl_cons];refine⟨j1,?_,?_,?_⟩
  ·rw[j2,k2,List.length_cons]
   omega
  ·intro i hi
   rw[j3 i (by omega),k3 i hi]
  ·intro w
   rw[j4 w,k4 w,k3 src hs,Z56]
   congr 2
   simp[Bool.decide_or]
lemma Z3e (B:ℕ) (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (W tgt side:ℕ)
  (hB:base.length= B) (hg:Z11 B st) (hs:side< B) :
  Z11 B (Z23 B st W tgt side)∧(Z23 B st W tgt side).2.length= st.2.length+2 ∧
  ∀ w,Zn base (Z23 B st W tgt side) w =
   (Zn base st w || (decide (w= tgt) && (Zn base st W && base.getD side false))):=by
 have hg':=hg;obtain⟨g1,g2,g3⟩:=hg;have hlen:(run evf st.2 base).length= B+st.2.length:=by rw[Zb,hB]
 have hrun:run evf (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base= run evf st.2 base ++
   [((run evf st.2 base).getD (st.1 W) false && (run evf st.2 base).getD side false)]:=by
  simp[Z1b,evf,GateOp.eval]
 have hg1:Z11 B (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]):=by
  refine⟨?_,?_,?_⟩
  ·intro w
   have:=g1 w
   show st.1 w< B+(st.2++[Gate.mk GateOp.and [st.1 W,side]]).length
   simp only[List.length_append,List.length_singleton];omega
  ·intro g hg
   simp only[List.mem_append,List.mem_singleton] at hg;rcases hg with hg | rfl
   ·exact g2 g hg
   ·exact⟨Or.inl rfl,by simp⟩
  ·apply Z3o _ _ _ g3
   intro i hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with h | h
   ·rw[h]; exact g1 W
   ·rw[h]; omega
 obtain⟨k1,k2,_,k4⟩:=Z3d B base (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]])
  tgt (B+st.2.length) hB hg1 (by simp)
 refine⟨k1,?_,?_⟩
 ·unfold Z23
  rw[k2];simp
 ·intro w
  unfold Z23;rw[k4 w];have e1:Zn base (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]) w= Zn base st w:=by
   unfold Zn
   show (run evf (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base).getD (st.1 w) false=_
   rw[hrun];exact Zf _ _ _ _ (by have:=g1 w; omega)
  have e2:(run evf (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]).2 base).getD
    (B+st.2.length) false=(Zn base st W && base.getD side false):=by
   show (run evf (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base).getD _ _=_
   rw[hrun,← hlen,Zp];unfold Zn;rw[Z3m evf st.2 base false side (by omega)]
  rw[e1,e2]
def Z1c (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (bound:ℕ) (A:ℕ→ Bool):Prop:=
 (∀ w< bound,Dp w→ A w= true→ u w= true→ uo= true) ∧
 (∀ w< bound,Dp w→ A w= true→ v w= true→ vo= true) ∧
 (uo= true→ vo= true∨∃ w< bound,Dp w∧A w= true∧u w= true)
lemma Z4x (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W:ℕ) (A:ℕ→ Bool)
  (hD:¬ Dp W) (hI:Z1c Dp u v uo vo (W+1) A):Z1c Dp u v uo vo W A:=by
 obtain⟨h1,h2,h3⟩:=hI;refine⟨fun w hw=>h1 w (by omega),fun w hw=>h2 w (by omega),?_⟩
 intro huo;rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
 ·left; exact h
 ·right
  refine⟨w,?_,hd,ha,hz⟩;rcases Nat.lt_or_ge w W with hlt | hge
  ·exact hlt
  ·have e:w= W:=by omega
   subst e;exact absurd hd hD
lemma Z5n (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W:ℕ) (l:List ℕ)
  (A A':ℕ→ Bool) (hr:∀ i∈l,i< W) (hD:Dp W)
  (hA:∀ w,A' w=(A w || (decide (w∈l) && A W)))
  (hx:∀ w,¬ Dp w→ u w= v w)
  (p1u:∀ i∈l,u i= true→ u W= true) (p1v:∀ i∈l,v i= true→ v W= true)
  (p2:u W= true→ v W= true∨∃ i∈l,u i= true)
  (hI:Z1c Dp u v uo vo (W+1) A):Z1c Dp u v uo vo W A':=by
 obtain⟨h1,h2,h3⟩:=hI;refine⟨?_,?_,?_⟩
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW⟩
  ·exact h1 w (by omega) hd ha hz
  ·exact h1 W (by omega) hD haW (p1u w hm hz)
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW⟩
  ·exact h2 w (by omega) hd ha hz
  ·exact h2 W (by omega) hD haW (p1v w hm hz)
 ·intro huo
  rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
  ·left; exact h
  ·rcases Nat.lt_or_ge w W with hlt | hge
   ·right
    exact⟨w,hlt,hd,by rw[hA,ha]; rfl,hz⟩
   ·have e:w= W:=by omega
    subst e;rcases p2 hz with hvW | ⟨i,hi,hui⟩
    ·left; exact h2 w (by omega) hd ha hvW
    ·by_cases hdi:Dp i
     ·right
      exact⟨i,hr i hi,hdi,by simp[hA,hi,ha],hui⟩
     ·left
      have e:=hx i hdi;exact h2 w (by omega) hd ha (p1v i hi (by rw[← e]; exact hui))
lemma Z3p (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W tgt side:ℕ)
  (A A':ℕ→ Bool) (ht:tgt< W) (hD:Dp W) (hs:¬ Dp side)
  (hA:∀ w,A' w=(A w || (decide (w= tgt) && (A W && v side))))
  (hx:∀ w,¬ Dp w→ u w= v w)
  (hu:u W=(u tgt && u side)) (hv:v W=(v tgt && v side))
  (hI:Z1c Dp u v uo vo (W+1) A):Z1c Dp u v uo vo W A':=by
 obtain⟨h1,h2,h3⟩:=hI;have hsd:=hx side hs;refine⟨?_,?_,?_⟩
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW,hvs⟩
  ·exact h1 w (by omega) hd ha hz
  ·subst hm
   exact h1 W (by omega) hD haW (by rw[hu,hz,hsd,hvs]; rfl)
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW,hvs⟩
  ·exact h2 w (by omega) hd ha hz
  ·subst hm
   exact h2 W (by omega) hD haW (by rw[hv,hz,hvs]; rfl)
 ·intro huo
  rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
  ·left; exact h
  ·rcases Nat.lt_or_ge w W with hlt | hge
   ·right
    exact⟨w,hlt,hd,by rw[hA,ha]; rfl,hz⟩
   ·have e:w= W:=by omega
    subst e;rw[hu] at hz;simp only[Bool.and_eq_true] at hz;have hvs:v side= true:=by rw[← hsd]; exact hz.2
    by_cases hdt:Dp tgt
    ·right
     exact⟨tgt,ht,hdt,by simp[hA,ha,hvs],hz.1⟩
    ·left
     have e:=hx tgt hdt;exact h2 w (by omega) hd ha (by rw[hv,← e,hz.1,hvs]; rfl)
lemma Z2b (B:ℕ) (deg:List ℕ) (base:List Bool) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate) (hB:base.length= B) (hl:l.length≤2)
  (hr:∀ i∈l,i< W) (hg:Z11 B st) (hD:0< deg.getD W 0) :
  Z11 B (l.foldl (fun s a=>Zj B s a (st.1 W)) st) ∧
  (l.foldl (fun s a=>Zj B s a (st.1 W)) st).2.length≤ st.2.length+2 ∧
  ∀ (u v:ℕ→ Bool) (uo vo:Bool),(∀ w,¬ 0< deg.getD w 0→ u w= v w) →
   (∀ i∈l,u i= true→ u W= true)→(∀ i∈l,v i= true→ v W= true) →
   (u W= true→ v W= true∨∃ i∈l,u i= true) →
   Z1c (fun w=>0< deg.getD w 0) u v uo vo (W+1) (Zn base st) →
   Z1c (fun w=>0< deg.getD w 0) u v uo vo W
    (Zn base (l.foldl (fun s a=>Zj B s a (st.1 W)) st)):=by
 obtain⟨j1,j2,_,j4⟩:=Z4w B base (st.1 W) hB l st hg (hg.1 W);refine⟨j1,by omega,?_⟩
 intro u v uo vo hx p1u p1v p2 hI;exact Z5n _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI
lemma Z3f (B:ℕ) (deg:List ℕ) (base:List Bool) (op:GateOp) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate) (hB:base.length= B) (hW:W< B)
  (hop:op= GateOp.and∨op= GateOp.or) (hl:l.length≤2) (hr:∀ i∈l,i< W)
  (hc:op= GateOp.and→ l.length=2→∃ i∈l,deg.getD i 0=0)
  (hg:Z11 B st) :
  Z11 B (Zy B deg op l W st) ∧
  (Zy B deg op l W st).2.length≤ st.2.length+(if 0< deg.getD W 0 then 2 else 0) ∧
  ∀ (u v:ℕ→ Bool) (uo vo:Bool),
   (∀ i< W,¬ 0< deg.getD i 0→ base.getD i false= v i) →
   u W= op.eval (l.map u)→ v W= op.eval (l.map v) →
   (∀ w,¬ 0< deg.getD w 0→ u w= v w) →
   Z1c (fun w=>0< deg.getD w 0) u v uo vo (W+1) (Zn base st) →
   Z1c (fun w=>0< deg.getD w 0) u v uo vo W (Zn base (Zy B deg op l W st)):=by
 by_cases hD:0< deg.getD W 0
 ·rcases hop with rfl | rfl
  ·rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
   ·have e:Zy B deg GateOp.and [] W st
      = ([]:List ℕ).foldl (fun s a=>Zj B s a (st.1 W)) st:=by
     unfold Zy;rw[Z2m _ _ _ hD,Z31 _ _ _ (by simp)]
    rw[e];obtain⟨f1,f2,f3⟩:=Z2b B deg base [] W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
    intro u v uo vo _ hu hv hx hI;refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
    intro _;left;simpa[GateOp.eval] using hv
   ·have e:Zy B deg GateOp.and [a] W st
      = [a].foldl (fun s a=>Zj B s a (st.1 W)) st:=by
     unfold Zy;rw[Z2m _ _ _ hD,Z31 _ _ _ (by simp)]
    rw[e];obtain⟨f1,f2,f3⟩:=Z2b B deg base [a] W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
    intro u v uo vo _ hu hv hx hI;have hu':u W= u a:=by simpa[GateOp.eval] using hu
    have hv':v W= v a:=by simpa[GateOp.eval] using hv
    refine f3 u v uo vo hx ?_ ?_ ?_ hI
    ·intro i hi h
     simp only[List.mem_singleton] at hi;subst hi;rw[hu']; exact h
    ·intro i hi h
     simp only[List.mem_singleton] at hi;subst hi;rw[hv']; exact h
    ·intro h
     right;exact⟨a,by simp,by rw[← hu']; exact h⟩
   ·have e:Zy B deg GateOp.and [a,b] W st
      = if 0< deg.getD a 0 then Z23 B st W a b else Z23 B st W b a:=by
     unfold Zy;rw[Z2m _ _ _ hD,Z2m _ _ _ (by simp[Z4i])]
     rfl
    have ha:a< W:=hr a (by simp)
    have hb:b< W:=hr b (by simp)
    obtain⟨i,hi,hi0⟩:=hc rfl rfl;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rw[e];by_cases hda:0< deg.getD a 0
    ·simp only[hda,↓reduceIte]
     have hdb:¬ 0< deg.getD b 0:=by
      rcases hi with h | h
      ·rw[h] at hi0; omega
      ·rw[h] at hi0; omega
     obtain⟨k1,k2,k3⟩:=Z3e B base st W a b hB hg (by omega)
     refine⟨k1,by simp only[hD,↓reduceIte]; omega,?_⟩
     intro u v uo vo hbv hu hv hx hI;have hu':u W=(u a && u b):=by simpa[GateOp.eval] using hu
     have hv':v W=(v a && v b):=by simpa[GateOp.eval] using hv
     refine Z3p _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI;intro w;rw[k3 w,hbv b hb hdb]
    ·simp only[hda,↓reduceIte]
     obtain⟨k1,k2,k3⟩:=Z3e B base st W b a hB hg (by omega)
     refine⟨k1,by simp only[hD,↓reduceIte]; omega,?_⟩
     intro u v uo vo hbv hu hv hx hI;have hu':u W=(u b && u a):=by
      rw[Bool.and_comm]; simpa[GateOp.eval] using hu
     have hv':v W=(v b && v a):=by
      rw[Bool.and_comm]; simpa[GateOp.eval] using hv
     refine Z3p _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI;intro w;rw[k3 w,hbv a ha hda]
   ·simp at hl
  ·have e:Zy B deg GateOp.or l W st
     = l.foldl (fun s a=>Zj B s a (st.1 W)) st:=by
    unfold Zy;rw[Z2m _ _ _ hD,Z31 _ _ _ (by simp[Z4i])]
   rw[e];obtain⟨f1,f2,f3⟩:=Z2b B deg base l W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
   intro u v uo vo _ hu hv hx hI;have hu':u W= true↔∃ i∈l,u i= true:=by
    rw[hu]; simp[GateOp.eval]
   have hv':v W= true↔∃ i∈l,v i= true:=by
    rw[hv]; simp[GateOp.eval]
   refine f3 u v uo vo hx ?_ ?_ ?_ hI
   ·intro i hi h
    exact hu'.2 ⟨i,hi,h⟩
   ·intro i hi h
    exact hv'.2 ⟨i,hi,h⟩
   ·intro h
    right;exact hu'.1 h
 ·have e:Zy B deg op l W st= st:=by
   unfold Zy;rw[Z31 _ _ _ hD]
  rw[e];refine⟨hg,by simp,?_⟩
  intro u v uo vo _ _ _ _ hI;exact Z4x _ u v uo vo W _ hD hI
def Z12 (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate) :
  ℕ→(ℕ→ ℕ)× List Gate
 | 0=>st0
 | d+1=>Zy B deg (gs.getD (gs.length-1-d) Z0).op
   (gs.getD (gs.length-1-d) Z0).inputs (N+(gs.length-1-d)) (Z12 B N deg gs st0 d)
def cnt (N:ℕ) (deg:List ℕ) (b:ℕ):ℕ:=
 ((Finset.range b).filter (fun k=>0< deg.getD (N+k) 0)).card
lemma Z57 (N:ℕ) (deg:List ℕ) (b:ℕ) :
  cnt N deg (b+1)= cnt N deg b+(if 0< deg.getD (N+b) 0 then 1 else 0):=by
 unfold cnt;rw[Finset.range_add_one,Finset.filter_insert];split_ifs with h
 ·rw[Finset.card_insert_of_notMem (by simp)]
 ·rfl
def Z39 (N:ℕ) (deg:List ℕ) (gs:List Gate):Prop:=
 ∀ k< gs.length,((gs.getD k Z0).op= GateOp.and∨(gs.getD k Z0).op= GateOp.or) ∧
  (gs.getD k Z0).inputs.length≤2∧(∀ i∈(gs.getD k Z0).inputs,i< N+k) ∧
  ((gs.getD k Z0).op= GateOp.and→(gs.getD k Z0).inputs.length=2 →
   ∃ i∈(gs.getD k Z0).inputs,deg.getD i 0=0)
lemma Z3g (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate)
  (hNB:N+gs.length≤ B) (hgs:Z39 N deg gs) (hg0:Z11 B st0) :
  ∀ d≤ gs.length,Z11 B (Z12 B N deg gs st0 d) ∧
   (Z12 B N deg gs st0 d).2.length+2*cnt N deg (gs.length-d)
    ≤ st0.2.length+2*cnt N deg gs.length:=by
 intro d
 induction d with
 | zero=>
  intro _;exact⟨hg0,by simp[Z12]⟩
 | succ d ih=>
  intro hd;obtain⟨i1,i2⟩:=ih (by omega)
  obtain⟨k,hk⟩:∃ k,k= gs.length-1-d:=⟨_,rfl⟩;have hks:k< gs.length:=by omega
  obtain⟨a1,a2,a3,a4⟩:=hgs k hks;have e:Z12 B N deg gs st0 (d+1)= Zy B deg (gs.getD k Z0).op
    (gs.getD k Z0).inputs (N+k) (Z12 B N deg gs st0 d):=by
   rw[hk]; rfl
  obtain⟨p1,p2,_⟩:=Z3f B deg (List.replicate B false) (gs.getD k Z0).op
   (gs.getD k Z0).inputs (N+k) (Z12 B N deg gs st0 d) List.length_replicate
   (by omega) a1 a2 a3 a4 i1
  rw[e];refine⟨p1,?_⟩;have e1:gs.length-d= k+1:=by omega
  have e2:gs.length-(d+1)= k:=by omega
  rw[e1,Z57] at i2;rw[e2];split_ifs at p2 i2 <;> omega
lemma Z58 (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate)
  (base:List Bool) (u v:ℕ→ Bool) (uo vo:Bool)
  (hB:base.length= B) (hNB:N+gs.length≤ B) (hgs:Z39 N deg gs) (hg0:Z11 B st0)
  (hv:∀ i< N+gs.length,¬ 0< deg.getD i 0→ base.getD i false= v i)
  (hu:∀ k< gs.length,u (N+k)=(gs.getD k Z0).op.eval ((gs.getD k Z0).inputs.map u))
  (hvv:∀ k< gs.length,v (N+k)=(gs.getD k Z0).op.eval ((gs.getD k Z0).inputs.map v))
  (hx:∀ w,¬ 0< deg.getD w 0→ u w= v w)
  (hI:Z1c (fun w=>0< deg.getD w 0) u v uo vo (N+gs.length) (Zn base st0)) :
  ∀ d≤ gs.length,Z1c (fun w=>0< deg.getD w 0) u v uo vo (N+(gs.length-d))
   (Zn base (Z12 B N deg gs st0 d)):=by
 intro d
 induction d with
 | zero=>
  intro _;simpa[Z12] using hI
 | succ d ih=>
  intro hd;have i1:=ih (by omega)
  obtain⟨k,hk⟩:∃ k,k= gs.length-1-d:=⟨_,rfl⟩;have hks:k< gs.length:=by omega
  obtain⟨a1,a2,a3,a4⟩:=hgs k hks;have e:Z12 B N deg gs st0 (d+1)= Zy B deg (gs.getD k Z0).op
    (gs.getD k Z0).inputs (N+k) (Z12 B N deg gs st0 d):=by
   rw[hk]; rfl
  obtain⟨_,_,p3⟩:=Z3f B deg base (gs.getD k Z0).op
   (gs.getD k Z0).inputs (N+k) (Z12 B N deg gs st0 d) hB
   (by omega) a1 a2 a3 a4 (Z3g B N deg gs st0 hNB hgs hg0 d (by omega)).1
  have e1:gs.length-d= k+1:=by omega
  have e2:gs.length-(d+1)= k:=by omega
  rw[e1] at i1;rw[e,e2];exact p3 u v uo vo (fun i hi=>hv i (by omega)) (hu k hks) (hvv k hks) hx i1
def wv (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ):Bool:=
 (C.wires (List.ofFn z)).getD w false
lemma Z14 (C:Circuit) (inp:List Bool):C.wires inp= run evf C.gates inp:=rfl
lemma Z13 (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ) (h:w< N) :
  wv C N z w= z ⟨w,h⟩:=by
 unfold wv
 rw[Z14,Z3m _ _ _ _ _ (by simpa using h),
  List.getD_eq_getElem _ _ (by simpa using h)]
 simp
lemma Z4j (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ) (h:N+C.gates.length≤ w) :
  wv C N z w= false:=by
 unfold wv;rw[Z14];exact Z2l _ _ _ (by rw[Zb]; simpa using h)
lemma Z2n (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (hR:ReadsBack N C) (k:ℕ)
  (hk:k< C.gates.length) :
  wv C N z (N+k)=(C.gates.getD k Z0).op.eval ((C.gates.getD k Z0).inputs.map (wv C N z)):=by
 unfold wv;rw[Z14];exact Z3n evf false Z4u C.gates _ N (by simp) k hk (hR k hk)
lemma Z3a (C:Circuit) (N:ℕ) (M:Finset ℕ):C.lineDegrees N M =
  run ldf C.gates ((List.range N).map fun i=>if i∈M then 1 else 0):=rfl
lemma Z1t (C:Circuit) (N:ℕ) (M:Finset ℕ) (w:ℕ) (h:w< N) :
  (C.lineDegrees N M).getD w 0= if w∈M then 1 else 0:=by
 rw[Z3a,Z3m _ _ _ _ _ (by simpa using h),
  List.getD_eq_getElem _ _ (by simpa using h)]
 simp
lemma Z5t (C:Circuit) (N:ℕ) (M:Finset ℕ) (w:ℕ) (h:N+C.gates.length≤ w) :
  (C.lineDegrees N M).getD w 0=0:=by
 rw[Z3a];exact Z2l _ _ _ (by rw[Zb]; simpa using h)
lemma Z59 (C:Circuit) (N:ℕ) (M:Finset ℕ) (hR:ReadsBack N C) (k:ℕ)
  (hk:k< C.gates.length) :
  (C.lineDegrees N M).getD (N+k) 0=(C.gates.getD k Z0).lineDegree (C.lineDegrees N M):=by
 rw[Z3a];exact Z3n ldf 0 Z4v C.gates _ N (by simp) k hk (hR k hk)
lemma Z4y {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) (h:w< n+m)
  (hw:w< n):Fin.append x y ⟨w,h⟩= x ⟨w,hw⟩:=
 Fin.append_left x y ⟨w,hw⟩
lemma Z21 {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) (h:w< n+m)
  (hw:n≤ w):Fin.append x y ⟨w,h⟩= y ⟨w-n,by omega⟩:=by
 have e:(⟨w,h⟩:Fin (n+m))= Fin.natAdd n ⟨w-n,by omega⟩:=by
  ext;simp only[Fin.natAdd_mk];omega
 rw[e,Fin.append_right]
lemma Z5a (C:Circuit) (k:ℕ) (hk:k< C.gates.length):C.gates.getD k Z0∈C.gates:=by
 rw[List.getD_eq_getElem _ _ hk];exact List.getElem_mem _
lemma Z3q (C:Circuit) (hM:Monotone2 C) (k:ℕ) (hk:k< C.gates.length) :
  ((C.gates.getD k Z0).op= GateOp.and∨(C.gates.getD k Z0).op= GateOp.or) ∧
  (C.gates.getD k Z0).inputs.length≤2:=by
 obtain⟨h1,h2⟩:=hM _ (Z5a C k hk);refine⟨?_,h2⟩;simpa using h1
lemma fwd (n m:ℕ) (C:Circuit) (hM:Monotone2 C) (hR:ReadsBack (n+m) C)
  (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) :
  ((C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0=0 →
   wv C (n+m) (Fin.append x y) w= wv C (n+m) (Fin.append x (fun _=>false)) w) ∧
  (wv C (n+m) (Fin.append x (fun _=>false)) w= true →
   wv C (n+m) (Fin.append x y) w= true):=by
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  rcases Nat.lt_or_ge w (n+m) with h | h
  ·rw[Z13 _ _ _ _ h,Z13 _ _ _ _ h,Z1t _ _ _ _ h]
   rcases Nat.lt_or_ge w n with hw | hw
   ·rw[Z4y _ _ _ _ hw,Z4y _ _ _ _ hw]
    exact⟨fun _=>rfl,fun h=>h⟩
   ·rw[Z21 _ (fun _=>false) _ _ hw]
    have:w∈Finset.Ico n (n+m):=by simp; omega
    simp[this]
  ·rcases Nat.lt_or_ge (w-(n+m)) C.gates.length with hk | hk
   ·obtain⟨k,rfl⟩:∃ k,w= n+m+k:=⟨w-(n+m),by omega⟩
    have hk':k< C.gates.length:=by omega
    have hu:=Z2n C (n+m) (Fin.append x y) hR k hk';have hv:=Z2n C (n+m) (Fin.append x (fun _=>false)) hR k hk'
    have hd:=Z59 C (n+m) (Finset.Ico n (n+m)) hR k hk';have hr:∀ i∈(C.gates.getD k Z0).inputs,i< n+m+k:=hR k hk';obtain⟨hop,hl⟩:=Z3q C hM k hk'
    generalize C.gates.getD k Z0= g at hu hv hd hr hop hl
    obtain⟨op,l⟩:=g;simp only at hop hl hr;rw[hu,hv,hd];rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
    ·rcases hop with rfl | rfl <;> simp[GateOp.eval]
    ·obtain⟨a1,a2⟩:=ih a (hr a (by simp))
     rcases hop with rfl | rfl
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.all_cons,
       List.all_nil,id,Bool.and_true,↓reduceIte,add_zero]
      exact⟨a1,a2⟩
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.any_cons,
       List.any_nil,id,Bool.or_false,reduceCtorEq,↓reduceIte,Nat.max_zero]
      exact⟨a1,a2⟩
    ·obtain⟨a1,a2⟩:=ih a (hr a (by simp))
     obtain⟨b1,b2⟩:=ih b (hr b (by simp))
     rcases hop with rfl | rfl
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.all_cons,
       List.all_nil,id,Bool.and_true,↓reduceIte,add_zero]
      constructor
      ·intro h0
       rw[a1 (by omega),b1 (by omega)]
      ·intro hh
       simp only[Bool.and_eq_true] at hh ⊢;exact⟨a2 hh.1,b2 hh.2⟩
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.any_cons,
       List.any_nil,id,Bool.or_false,reduceCtorEq,↓reduceIte,Nat.max_zero]
      constructor
      ·intro h0
       rw[a1 (by omega),b1 (by omega)]
      ·intro hh
       simp only[Bool.or_eq_true] at hh ⊢;exact hh.imp a2 b2
    ·simp at hl
   ·rw[Z4j _ _ _ _ (by omega),Z4j _ _ _ _ (by omega)]
    exact⟨fun _=>rfl,fun h=>h⟩
lemma Z4z (m:ℕ) (w:List Bool) :
  run evf (List.replicate m (Gate.mk GateOp.or [])) w= w++List.replicate m false:=by
 induction m with
 | zero=>simp[run]
 | succ m ih=>
  rw[List.replicate_succ',Z1b,ih,List.replicate_succ',← List.append_assoc];simp[evf,GateOp.eval]
lemma Z5b {n m:ℕ} (x:Fin n→ Bool) :
  List.ofFn (Fin.append x (fun _:Fin m=>false))= List.ofFn x++List.replicate m false:=by
 rw[List.ofFn_fin_append,List.ofFn_const]
lemma Z50 (N s:ℕ) (deg:List ℕ) :
  Set.ncard {j:ℕ | j< s∧0< deg.getD (N+j) 0}= cnt N deg s:=by
 unfold cnt;rw[← Set.ncard_coe_finset]
 congr 1
 ext j;simp
lemma Z5c (n m:ℕ) (C:Circuit) (hM:Monotone2 C) (hR:ReadsBack (n+m) C)
  (hX:∀ j< C.gates.length,(gateAt C j).op= GateOp.and→(gateAt C j).inputs.length=2 →
   ∃ i∈(gateAt C j).inputs,(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0) :
  Z39 (n+m) (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates:=by
 intro k hk;obtain⟨h1,h2⟩:=Z3q C hM k hk;exact⟨h1,h2,hR k hk,hX k hk⟩
lemma Z51 (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (r bound:ℕ) (A:ℕ→ Bool)
  (hA:∀ w,A w= decide (w= r)) (hx:∀ w,¬ Dp w→ u w= v w)
  (hb:u r= true→ r< bound) :
  Z1c Dp u v (u r) (v r) bound A:=by
 refine⟨?_,?_,?_⟩
 ·intro w _ _ ha hz
  rw[hA] at ha;simp only[decide_eq_true_eq] at ha;subst ha;exact hz
 ·intro w _ _ ha hz
  rw[hA] at ha;simp only[decide_eq_true_eq] at ha;subst ha;exact hz
 ·intro h
  by_cases hd:Dp r
  ·right
   exact⟨r,hb h,hd,by simp[hA],h⟩
  ·left
   rw[← hx r hd];exact h
lemma main (n m:ℕ) (C:Circuit) (hM:Monotone2 C) (hR:ReadsBack (n+m) C)
  (hX:∀ j< C.gates.length,(gateAt C j).op= GateOp.and→(gateAt C j).inputs.length=2 →
   ∃ i∈(gateAt C j).inputs,(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0) :
  ∃ (D:Circuit) (o:Fin m→ ℕ),Monotone2 D∧ReadsBack n D ∧
   D.size≤ C.size+3*Set.ncard {j:ℕ | j< C.gates.length ∧
    0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD (n+m+j) 0}+m ∧
   ∀ (x:Fin n→ Bool) (j:Fin m),
    circuitFun (n+m) C (Fin.append x (fun l=>decide (l= j))) =
     (circuitFun (n+m) C (Fin.append x (fun _=>false)) ||
      (D.wires (List.ofFn x)).getD (o j) false):=by
 have hF:=fun (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ)=>fwd n m C hM hR x y w
 have hcf:∀ z:Fin (n+m)→ Bool,circuitFun (n+m) C z= wv C (n+m) z C.output:=
  fun _=>rfl
 rw[Z50];by_cases hout:0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD C.output 0
 ·rcases Nat.lt_or_ge C.output (n+m) with hlt | hge
  ·
   have hdi:=Z1t C (n+m) (Finset.Ico n (n+m)) C.output hlt;have hn:n≤ C.output:=by
    by_contra hcon
    have:C.output∉Finset.Ico n (n+m):=by simp; omega
    rw[hdi] at hout;simp[this] at hout
   refine⟨Circuit.mk [Gate.mk GateOp.and []] 0,
    fun j=>if n+j.val= C.output then n else n+1,?_,?_,?_,?_⟩
   ·intro g hg
    simp only[List.mem_singleton] at hg;subst hg;simp
   ·show RBL n [Gate.mk GateOp.and []]
    exact Z2a _ _ (by simp)
   ·simp only[Circuit.size,List.length_singleton]
    omega
   ·intro x j
    rw[hcf,hcf,Z13 _ _ _ _ hlt,Z13 _ _ _ _ hlt,Z21 _ _ _ _ hn,
     Z21 _ _ _ _ hn]
    have hw:(Circuit.mk [Gate.mk GateOp.and []] 0).wires (List.ofFn x)
      = List.ofFn x++[true]:=by
     simp[Circuit.wires,GateOp.eval]
    rw[hw];have hlen:(List.ofFn x).length= n:=by simp
    by_cases hj:n+j.val= C.output
    ·have e1:(⟨C.output-n,by omega⟩:Fin m)= j:=by
      ext;simp only;omega
     have e2:(List.ofFn x++[true]).getD n false= true:=by
      have h2:=Zp (List.ofFn x) true false;rw[hlen] at h2;exact h2
     simp only[hj,↓reduceIte,e1];rw[e2];simp
    ·have e1:(⟨C.output-n,by omega⟩:Fin m)≠j:=by
      intro hcon;apply hj;rw[← hcon];simp only;omega
     simp only[hj,↓reduceIte,e1,decide_false];rw[Z2l _ _ _ (by simp)]
     rfl
  ·
   have hks:C.output-(n+m)< C.gates.length:=by
    by_contra hcon
    rw[Z5t _ _ _ _ (by omega)] at hout
    omega
   have hcpos:1≤ cnt (n+m) (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates.length:=by
    unfold cnt;apply Finset.card_pos.mpr;refine⟨C.output-(n+m),?_⟩;simp only[Finset.mem_filter,Finset.mem_range];refine⟨hks,?_⟩;have e:n+m+(C.output-(n+m))= C.output:=by omega
    rw[e];exact hout
   have hgs:=Z5c n m C hM hR hX;have hg0:Z11 (n+m+C.gates.length+1)
     ((fun w=>if w= C.output then n+m+C.gates.length else n),([]:List Gate)):=by
    refine⟨?_,?_,?_⟩
    ·intro w
     simp only[List.length_nil];split_ifs <;> omega
    ·intro g hg
     simp at hg
    ·intro j hj
     simp at hj
   obtain⟨q1,q2⟩:=Z3g (n+m+C.gates.length+1) (n+m)
    (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates _ (by omega) hgs hg0
    C.gates.length (le_refl _)
   obtain⟨q11,q12,q13⟩:=q1
   refine⟨Circuit.mk (List.replicate m (Gate.mk GateOp.or [])++(C.gates ++
    ([Gate.mk GateOp.and []]++(Z12 (n+m+C.gates.length+1) (n+m)
     (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates
     ((fun w=>if w= C.output then n+m+C.gates.length else n),([]:List Gate))
     C.gates.length).2))) 0,
    fun j=>(Z12 (n+m+C.gates.length+1) (n+m)
     (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates
     ((fun w=>if w= C.output then n+m+C.gates.length else n),([]:List Gate))
     C.gates.length).1 (n+j.val),?_,?_,?_,?_⟩
   ·intro g hg
    simp only[List.mem_append,List.mem_replicate,List.mem_singleton] at hg;rcases hg with⟨_,rfl⟩ | hg | rfl | hg
    ·simp
    ·exact hM g hg
    ·simp
    ·obtain⟨h1,h2⟩:=q12 g hg
     refine⟨?_,h2⟩;rcases h1 with h1 | h1 <;> simp[h1]
   ·show RBL n _
    apply Z1k
    ·exact Z2a _ _ (by
      intro g hg;simp only[List.mem_replicate] at hg
      rw[hg.2])
    ·rw[List.length_replicate]
     apply Z1k _ _ _ hR;apply Z1k
     ·exact Z2a _ _ (by simp)
     ·exact q13
   ·simp only[Circuit.size,List.length_append,List.length_replicate,List.length_singleton]
    simp only[List.length_nil] at q2;omega
   ·intro x j
    obtain⟨st,hst⟩:∃ st,st= Z12 (n+m+C.gates.length+1) (n+m)
     (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates
     ((fun w=>if w= C.output then n+m+C.gates.length else n),([]:List Gate))
     C.gates.length:=⟨_,rfl⟩
    rw[← hst];obtain⟨base,hbase⟩:∃ base,base =
     C.wires (List.ofFn (Fin.append x (fun _:Fin m=>false)))++[true]:=⟨_,rfl⟩
    have hvl:(C.wires (List.ofFn (Fin.append x (fun _:Fin m=>false)))).length
      = n+m+C.gates.length:=by
     rw[Z14,Zb];simp
    have hBl:base.length= n+m+C.gates.length+1:=by
     rw[hbase,List.length_append,hvl];rfl
    have hw:(Circuit.mk (List.replicate m (Gate.mk GateOp.or [])++(C.gates ++
      ([Gate.mk GateOp.and []]++st.2))) 0).wires (List.ofFn x)= run evf st.2 base:=by
     rw[Z14];simp only[];rw[Z22,Z22,Z22,Z4z,← Z5b,hbase,Z14]
     congr 1
    rw[hw,hcf,hcf];have hv:∀ i< n+m+C.gates.length,
      base.getD i false= wv C (n+m) (Fin.append x (fun _=>false)) i:=by
     intro i hi;rw[hbase,Zf _ _ _ _ (by omega)]
     rfl
    have hT:base.getD (n+m+C.gates.length) false= true:=by
     rw[hbase,← hvl,Zp]
    have hFl:base.getD n false= false:=by
     rw[hv n (by have:=j.isLt; omega),Z13 _ _ _ _ (by have:=j.isLt; omega),
      Z21 _ _ _ _ (le_refl _)]
    have hx:∀ w,¬ 0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0 →
      wv C (n+m) (Fin.append x (fun l=>decide (l= j))) w
       = wv C (n+m) (Fin.append x (fun _=>false)) w:=by
     intro w hw0;exact (hF x _ w).1 (by omega)
    have hI0:=Z51 (fun w=>0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0)
     (wv C (n+m) (Fin.append x (fun l=>decide (l= j))))
     (wv C (n+m) (Fin.append x (fun _=>false))) C.output (n+m+C.gates.length)
     (Zn base ((fun w=>if w= C.output then n+m+C.gates.length else n),([]:List Gate)))
     (by
      intro w;unfold Zn
      show (base).getD (if w= C.output then n+m+C.gates.length else n) false=_
      by_cases hwo:w= C.output
      ·rw[Z2m _ _ _ hwo,hT]; simp[hwo]
      ·rw[Z31 _ _ _ hwo,hFl]; simp[hwo])
     hx
     (by
      intro hu
      by_contra hcon
      rw[Z4j _ _ _ _ (by omega)] at hu
      exact Bool.false_ne_true hu)
    have hfin:=Z58 (n+m+C.gates.length+1) (n+m)
     (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates _ base _ _ _ _ hBl (by omega)
     hgs hg0 (fun i hi _=>hv i hi)
     (fun k hk=>Z2n C (n+m) _ hR k hk) (fun k hk=>Z2n C (n+m) _ hR k hk)
     hx hI0 C.gates.length (le_refl _)
    rw[← hst] at hfin;obtain⟨f1,_,f3⟩:=hfin;have hjlt:n+j.val< n+m:=by have:=j.isLt; omega
    have hdj:0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD (n+j.val) 0:=by
     rw[Z1t _ _ _ _ hjlt];have:n+j.val∈Finset.Ico n (n+m):=by simp
     simp[this]
    have huj:wv C (n+m) (Fin.append x (fun l=>decide (l= j))) (n+j.val)= true:=by
     rw[Z13 _ _ _ _ hjlt,Z21 _ _ _ _ (by omega)]
     simp only[decide_eq_true_eq];ext;simp
    show _=(_ || Zn base st (n+j.val))
    rw[Bool.eq_iff_iff];simp only[Bool.or_eq_true];constructor
    ·intro huo
     rcases f3 huo with h | ⟨w,hw,hd,ha,hz⟩
     ·left; exact h
     ·right
      have hwN:w< n+m:=by omega
      have hwn:n≤ w:=by
       by_contra hcon
       have hd':0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0:=hd;rw[Z1t _ _ _ _ hwN] at hd';have:w∉Finset.Ico n (n+m):=by simp; omega
       simp[this] at hd'
      rw[Z13 _ _ _ _ hwN,Z21 _ _ _ _ hwn] at hz;simp only[decide_eq_true_eq] at hz;have e:w= n+j.val:=by
       rw[← hz];simp only;omega
      rw[← e];exact ha
    ·rintro (h | h)
     ·exact (hF x _ C.output).2 h
     ·exact f1 (n+j.val) (by omega) hdj h huj
 ·
  refine⟨Circuit.mk [] 0,fun _=>n,?_,?_,?_,?_⟩
  ·intro g hg
   simp at hg
  ·intro j hj
   simp at hj
  ·simp[Circuit.size]
  ·intro x j
   rw[hcf,hcf,(hF x _ C.output).1 (by omega)]
   have:((Circuit.mk [] 0).wires (List.ofFn x)).getD n false= false:=by
    apply Z2l;simp[Circuit.wires]
   rw[this];simp
end PEqualNP.Outside.L_meta_1690.P1622
namespace PEqualNP.Outside.L_meta_1690.P1623
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma Z8 {α:Type} (l l':List α) (d:α) (i:ℕ) (h:i< l.length) :
  (l++l').getD i d= l.getD i d:=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_append_left h]
lemma Zk {α:Type} (l:List α) (a d:α):(l++[a]).getD l.length d= a:=by
 simp[List.getD_eq_getElem?_getD]
lemma Z24 {α:Type} (l:List α) (d:α) (i:ℕ) (h:l.length≤ i):l.getD i d= d:=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
def Z3:Gate:=Gate.mk GateOp.or []
def Z1 {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α):List α:=
 gs.foldl (fun w g=>w++[f w g]) w
lemma Zo {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (g:Gate) (w:List α) :
  Z1 f (gs++[g]) w= Z1 f gs w++[f (Z1 f gs w) g]:=by
 simp[Z1]
lemma Z1i {α:Type} (f:List α→ Gate→ α) (g1 g2:List Gate) (w:List α) :
  Z1 f (g1++g2) w= Z1 f g2 (Z1 f g1 w):=by
 simp[Z1]
lemma Z7 {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α) :
  (Z1 f gs w).length= w.length+gs.length:=by
 induction gs using List.reverseRecOn with
 | nil=>simp[Z1]
 | append_singleton gs g ih=>rw[Zo]; simp[ih]; omega
lemma Z1u {α:Type} (f:List α→ Gate→ α) (gs:List Gate) (w:List α) (d:α) (i:ℕ)
  (h:i< w.length):(Z1 f gs w).getD i d= w.getD i d:=by
 induction gs using List.reverseRecOn with
 | nil=>rfl
 | append_singleton gs g ih=>
  rw[Zo,Z8 _ _ _ _ (by rw[Z7]; omega),ih]
lemma Z2q {α:Type} (f:List α→ Gate→ α) (d:α)
  (hf:∀ (g:Gate) (w w':List α),(∀ i∈g.inputs,w.getD i d= w'.getD i d)→ f w g= f w' g)
  (gs:List Gate) (w:List α) (L:ℕ) (hL:w.length= L) (k:ℕ) (hk:k< gs.length)
  (hr:∀ i∈(gs.getD k Z3).inputs,i< L+k) :
  (Z1 f gs w).getD (L+k) d= f (Z1 f gs w) (gs.getD k Z3):=by
 subst hL
 induction gs using List.reverseRecOn with
 | nil=>simp at hk
 | append_singleton gs g ih=>
  rw[Zo];rcases Nat.lt_or_ge k gs.length with h | h
  ·have e:(gs++[g]).getD k Z3= gs.getD k Z3:=Z8 _ _ _ _ h
   rw[e] at hr ⊢;rw[Z8 _ _ _ _ (by rw[Z7]; omega),ih h hr]
   apply hf;intro i hi;symm;exact Z8 _ _ _ _ (by rw[Z7]; have:=hr i hi; omega)
  ·have hk':k= gs.length:=by
    simp only[List.length_append,List.length_singleton] at hk;omega
   subst hk';have e:(gs++[g]).getD gs.length Z3= g:=Zk _ _ _;rw[e] at hr ⊢;have e2:w.length+gs.length=(Z1 f gs w).length:=(Z7 f gs w).symm;rw[e2,Zk];apply hf;intro i hi;symm;exact Z8 _ _ _ _ (by rw[Z7]; have:=hr i hi; omega)
def Z4 (w:List Bool) (g:Gate):Bool:=g.op.eval (g.inputs.map fun i=>w.getD i false)
def Zt (d:List ℕ) (g:Gate):ℕ:=g.lineDegree d
lemma Z3r (g:Gate) (w w':List Bool)
  (h:∀ i∈g.inputs,w.getD i false= w'.getD i false):Z4 w g= Z4 w' g:=by
 unfold Z4;rw[List.map_congr_left h]
lemma Z3s (g:Gate) (w w':List ℕ)
  (h:∀ i∈g.inputs,w.getD i 0= w'.getD i 0):Zt w g= Zt w' g:=by
 unfold Zt Gate.lineDegree;rw[List.map_congr_left h]
def Z1f (n:ℕ) (gs:List Gate):Prop:=
 ∀ j< gs.length,∀ i∈(gs.getD j Z3).inputs,i< n+j
lemma Z28 (n:ℕ) (g1 g2:List Gate) (h1:Z1f n g1) (h2:Z1f (n+g1.length) g2) :
  Z1f n (g1++g2):=by
 intro j hj i hi;rcases Nat.lt_or_ge j g1.length with h | h
 ·rw[Z8 _ _ _ _ h] at hi
  exact h1 j h i hi
 ·rw[List.getD_append_right _ _ _ _ h] at hi
  simp only[List.length_append] at hj;have:=h2 (j-g1.length) (by omega) i hi
  omega
lemma Z2c (n:ℕ) (gs:List Gate) (h:∀ g∈gs,g.inputs=[]):Z1f n gs:=by
 intro j hj i hi;have hm:gs.getD j Z3∈gs:=by
  rw[List.getD_eq_getElem _ _ hj];exact List.getElem_mem _
 rw[h _ hm] at hi;simp at hi
lemma Z2r (n:ℕ) (gs:List Gate) (g:Gate) (h1:Z1f n gs)
  (h2:∀ i∈g.inputs,i< n+gs.length):Z1f n (gs++[g]):=by
 apply Z28 _ _ _ h1;intro j hj i hi;simp only[List.length_singleton] at hj;have hj0:j=0:=by omega
 subst hj0;have:=h2 i (by simpa using hi)
 omega
def Zh (B:ℕ) (st:(ℕ→ ℕ)× List Gate):Prop:=
 (∀ w,st.1 w< B+st.2.length) ∧
 (∀ g∈st.2,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2) ∧
 Z1f B st.2
def Z5 (B:ℕ) (st:(ℕ→ ℕ)× List Gate) (a src:ℕ):(ℕ→ ℕ)× List Gate:=
 (Function.update st.1 a (B+st.2.length),st.2++[Gate.mk GateOp.or [st.1 a,src]])
def Ze (B:ℕ) (st:(ℕ→ ℕ)× List Gate) (W tgt side:ℕ):(ℕ→ ℕ)× List Gate:=
 Z5 B (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]) tgt (B+st.2.length)
def Z1o:GateOp→ Bool
 | GateOp.and=>true
 | _=>false
def Zc (B:ℕ) (deg:List ℕ) (op:GateOp) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate):(ℕ→ ℕ)× List Gate:=
 if 0< deg.getD W 0 then
  if Z1o op= true∧l.length=2 then
   if 0< deg.getD (l.getD 0 0) 0 then Ze B st W (l.getD 0 0) (l.getD 1 0)
   else Ze B st W (l.getD 1 0) (l.getD 0 0)
  else l.foldl (fun s a=>Z5 B s a (st.1 W)) st
 else st
def Z9 (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (w:ℕ):Bool:=
 (Z1 Z4 st.2 base).getD (st.1 w) false
lemma Z2d (B:ℕ) (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (a src:ℕ)
  (hB:base.length= B) (hg:Zh B st) (hs:src< B+st.2.length) :
  Zh B (Z5 B st a src)∧(Z5 B st a src).2.length= st.2.length+1 ∧
  (∀ i< B+st.2.length,
   (Z1 Z4 (Z5 B st a src).2 base).getD i false=(Z1 Z4 st.2 base).getD i false) ∧
  ∀ w,Z9 base (Z5 B st a src) w =
   (Z9 base st w || (decide (w= a) && (Z1 Z4 st.2 base).getD src false)):=by
 obtain⟨g1,g2,g3⟩:=hg;have hlen:(Z1 Z4 st.2 base).length= B+st.2.length:=by rw[Z7,hB]
 have hrun:Z1 Z4 (Z5 B st a src).2 base= Z1 Z4 st.2 base ++
   [((Z1 Z4 st.2 base).getD (st.1 a) false || (Z1 Z4 st.2 base).getD src false)]:=by
  simp[Z5,Zo,Z4,GateOp.eval]
 refine⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
 ·intro w
  simp only[Z5,List.length_append,List.length_singleton,Function.update_apply];split_ifs
  ·omega
  ·have:=g1 w
   omega
 ·intro g hg
  simp only[Z5,List.mem_append,List.mem_singleton] at hg;rcases hg with hg | rfl
  ·exact g2 g hg
  ·exact⟨Or.inr rfl,by simp⟩
 ·apply Z2r _ _ _ g3
  intro i hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl | rfl
  ·exact g1 a
  ·exact hs
 ·simp[Z5]
 ·intro i hi
  rw[hrun];exact Z8 _ _ _ _ (by omega)
 ·intro w
  unfold Z9;rw[hrun];by_cases hw:w= a
  ·subst hw
   have e:(Z5 B st w src).1 w=(Z1 Z4 st.2 base).length:=by simp[Z5,hlen]
   rw[e,Zk];simp
  ·have e:(Z5 B st a src).1 w= st.1 w:=by simp[Z5,hw]
   rw[e,Z8 _ _ _ _ (by have:=g1 w; omega)]
   simp[hw]
lemma Zq {α:Type} (c:Prop) [Decidable c] (a b:α) (h:c):(if c then a else b)= a:=by
 simp[h]
lemma Zx {α:Type} (c:Prop) [Decidable c] (a b:α) (h:¬ c):(if c then a else b)= b:=by
 simp[h]
lemma Z47 (p q r s:Bool):((p || (q && s)) || (r && s))=(p || ((q || r) && s)):=by
 cases p <;> cases q <;> cases r <;> cases s <;> rfl
lemma Z3t (B:ℕ) (base:List Bool) (src:ℕ) (hB:base.length= B) (l:List ℕ) :
  ∀ (st:(ℕ→ ℕ)× List Gate),Zh B st→ src< B+st.2.length →
  Zh B (l.foldl (fun s a=>Z5 B s a src) st) ∧
  (l.foldl (fun s a=>Z5 B s a src) st).2.length= st.2.length+l.length ∧
  (∀ i< B+st.2.length,
   (Z1 Z4 (l.foldl (fun s a=>Z5 B s a src) st).2 base).getD i false =
    (Z1 Z4 st.2 base).getD i false) ∧
  ∀ w,Z9 base (l.foldl (fun s a=>Z5 B s a src) st) w =
   (Z9 base st w || (decide (w∈l) && (Z1 Z4 st.2 base).getD src false)):=by
 induction l with
 | nil=>
  intro st hg _;simp[hg]
 | cons a l ih=>
  intro st hg hs;obtain⟨k1,k2,k3,k4⟩:=Z2d B base st a src hB hg hs;obtain⟨j1,j2,j3,j4⟩:=ih (Z5 B st a src) k1 (by omega)
  rw[List.foldl_cons];refine⟨j1,?_,?_,?_⟩
  ·rw[j2,k2,List.length_cons]
   omega
  ·intro i hi
   rw[j3 i (by omega),k3 i hi]
  ·intro w
   rw[j4 w,k4 w,k3 src hs,Z47]
   congr 2
   simp[Bool.decide_or]
lemma Z2e (B:ℕ) (base:List Bool) (st:(ℕ→ ℕ)× List Gate) (W tgt side:ℕ)
  (hB:base.length= B) (hg:Zh B st) (hs:side< B) :
  Zh B (Ze B st W tgt side)∧(Ze B st W tgt side).2.length= st.2.length+2 ∧
  ∀ w,Z9 base (Ze B st W tgt side) w =
   (Z9 base st w || (decide (w= tgt) && (Z9 base st W && base.getD side false))):=by
 have hg':=hg;obtain⟨g1,g2,g3⟩:=hg;have hlen:(Z1 Z4 st.2 base).length= B+st.2.length:=by rw[Z7,hB]
 have hrun:Z1 Z4 (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base= Z1 Z4 st.2 base ++
   [((Z1 Z4 st.2 base).getD (st.1 W) false && (Z1 Z4 st.2 base).getD side false)]:=by
  simp[Zo,Z4,GateOp.eval]
 have hg1:Zh B (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]):=by
  refine⟨?_,?_,?_⟩
  ·intro w
   have:=g1 w
   show st.1 w< B+(st.2++[Gate.mk GateOp.and [st.1 W,side]]).length
   simp only[List.length_append,List.length_singleton];omega
  ·intro g hg
   simp only[List.mem_append,List.mem_singleton] at hg;rcases hg with hg | rfl
   ·exact g2 g hg
   ·exact⟨Or.inl rfl,by simp⟩
  ·apply Z2r _ _ _ g3
   intro i hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with h | h
   ·rw[h]; exact g1 W
   ·rw[h]; omega
 obtain⟨k1,k2,_,k4⟩:=Z2d B base (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]])
  tgt (B+st.2.length) hB hg1 (by simp)
 refine⟨k1,?_,?_⟩
 ·unfold Ze
  rw[k2];simp
 ·intro w
  unfold Ze;rw[k4 w];have e1:Z9 base (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]) w= Z9 base st w:=by
   unfold Z9
   show (Z1 Z4 (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base).getD (st.1 w) false=_
   rw[hrun];exact Z8 _ _ _ _ (by have:=g1 w; omega)
  have e2:(Z1 Z4 (st.1,st.2++[Gate.mk GateOp.and [st.1 W,side]]).2 base).getD
    (B+st.2.length) false=(Z9 base st W && base.getD side false):=by
   show (Z1 Z4 (st.2++[Gate.mk GateOp.and [st.1 W,side]]) base).getD _ _=_
   rw[hrun,← hlen,Zk];unfold Z9;rw[Z1u Z4 st.2 base false side (by omega)]
  rw[e1,e2]
def Zl (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (bound:ℕ) (A:ℕ→ Bool):Prop:=
 (∀ w< bound,Dp w→ A w= true→ u w= true→ uo= true) ∧
 (∀ w< bound,Dp w→ A w= true→ v w= true→ vo= true) ∧
 (uo= true→ vo= true∨∃ w< bound,Dp w∧A w= true∧u w= true)
lemma Z3u (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W:ℕ) (A:ℕ→ Bool)
  (hD:¬ Dp W) (hI:Zl Dp u v uo vo (W+1) A):Zl Dp u v uo vo W A:=by
 obtain⟨h1,h2,h3⟩:=hI;refine⟨fun w hw=>h1 w (by omega),fun w hw=>h2 w (by omega),?_⟩
 intro huo;rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
 ·left; exact h
 ·right
  refine⟨w,?_,hd,ha,hz⟩;rcases Nat.lt_or_ge w W with hlt | hge
  ·exact hlt
  ·have e:w= W:=by omega
   subst e;exact absurd hd hD
lemma Z4k (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W:ℕ) (l:List ℕ)
  (A A':ℕ→ Bool) (hr:∀ i∈l,i< W) (hD:Dp W)
  (hA:∀ w,A' w=(A w || (decide (w∈l) && A W)))
  (hx:∀ w,¬ Dp w→ u w= v w)
  (p1u:∀ i∈l,u i= true→ u W= true) (p1v:∀ i∈l,v i= true→ v W= true)
  (p2:u W= true→ v W= true∨∃ i∈l,u i= true)
  (hI:Zl Dp u v uo vo (W+1) A):Zl Dp u v uo vo W A':=by
 obtain⟨h1,h2,h3⟩:=hI;refine⟨?_,?_,?_⟩
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW⟩
  ·exact h1 w (by omega) hd ha hz
  ·exact h1 W (by omega) hD haW (p1u w hm hz)
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW⟩
  ·exact h2 w (by omega) hd ha hz
  ·exact h2 W (by omega) hD haW (p1v w hm hz)
 ·intro huo
  rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
  ·left; exact h
  ·rcases Nat.lt_or_ge w W with hlt | hge
   ·right
    exact⟨w,hlt,hd,by rw[hA,ha]; rfl,hz⟩
   ·have e:w= W:=by omega
    subst e;rcases p2 hz with hvW | ⟨i,hi,hui⟩
    ·left; exact h2 w (by omega) hd ha hvW
    ·by_cases hdi:Dp i
     ·right
      exact⟨i,hr i hi,hdi,by simp[hA,hi,ha],hui⟩
     ·left
      have e:=hx i hdi;exact h2 w (by omega) hd ha (p1v i hi (by rw[← e]; exact hui))
lemma Z2s (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (uo vo:Bool) (W tgt side:ℕ)
  (A A':ℕ→ Bool) (ht:tgt< W) (hD:Dp W) (hs:¬ Dp side)
  (hA:∀ w,A' w=(A w || (decide (w= tgt) && (A W && v side))))
  (hx:∀ w,¬ Dp w→ u w= v w)
  (hu:u W=(u tgt && u side)) (hv:v W=(v tgt && v side))
  (hI:Zl Dp u v uo vo (W+1) A):Zl Dp u v uo vo W A':=by
 obtain⟨h1,h2,h3⟩:=hI;have hsd:=hx side hs;refine⟨?_,?_,?_⟩
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW,hvs⟩
  ·exact h1 w (by omega) hd ha hz
  ·subst hm
   exact h1 W (by omega) hD haW (by rw[hu,hz,hsd,hvs]; rfl)
 ·intro w hw hd ha hz
  rw[hA] at ha;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha;rcases ha with ha | ⟨hm,haW,hvs⟩
  ·exact h2 w (by omega) hd ha hz
  ·subst hm
   exact h2 W (by omega) hD haW (by rw[hv,hz,hvs]; rfl)
 ·intro huo
  rcases h3 huo with h | ⟨w,hw,hd,ha,hz⟩
  ·left; exact h
  ·rcases Nat.lt_or_ge w W with hlt | hge
   ·right
    exact⟨w,hlt,hd,by rw[hA,ha]; rfl,hz⟩
   ·have e:w= W:=by omega
    subst e;rw[hu] at hz;simp only[Bool.and_eq_true] at hz;have hvs:v side= true:=by rw[← hsd]; exact hz.2
    by_cases hdt:Dp tgt
    ·right
     exact⟨tgt,ht,hdt,by simp[hA,ha,hvs],hz.1⟩
    ·left
     have e:=hx tgt hdt;exact h2 w (by omega) hd ha (by rw[hv,← e,hz.1,hvs]; rfl)
lemma Z1p (B:ℕ) (deg:List ℕ) (base:List Bool) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate) (hB:base.length= B) (hl:l.length≤2)
  (hr:∀ i∈l,i< W) (hg:Zh B st) (hD:0< deg.getD W 0) :
  Zh B (l.foldl (fun s a=>Z5 B s a (st.1 W)) st) ∧
  (l.foldl (fun s a=>Z5 B s a (st.1 W)) st).2.length≤ st.2.length+2 ∧
  ∀ (u v:ℕ→ Bool) (uo vo:Bool),(∀ w,¬ 0< deg.getD w 0→ u w= v w) →
   (∀ i∈l,u i= true→ u W= true)→(∀ i∈l,v i= true→ v W= true) →
   (u W= true→ v W= true∨∃ i∈l,u i= true) →
   Zl (fun w=>0< deg.getD w 0) u v uo vo (W+1) (Z9 base st) →
   Zl (fun w=>0< deg.getD w 0) u v uo vo W
    (Z9 base (l.foldl (fun s a=>Z5 B s a (st.1 W)) st)):=by
 obtain⟨j1,j2,_,j4⟩:=Z3t B base (st.1 W) hB l st hg (hg.1 W);refine⟨j1,by omega,?_⟩
 intro u v uo vo hx p1u p1v p2 hI;exact Z4k _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI
lemma Z2f (B:ℕ) (deg:List ℕ) (base:List Bool) (op:GateOp) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate) (hB:base.length= B) (hW:W< B)
  (hop:op= GateOp.and∨op= GateOp.or) (hl:l.length≤2) (hr:∀ i∈l,i< W)
  (hc:op= GateOp.and→ l.length=2→∃ i∈l,deg.getD i 0=0)
  (hg:Zh B st) :
  Zh B (Zc B deg op l W st) ∧
  (Zc B deg op l W st).2.length≤ st.2.length+(if 0< deg.getD W 0 then 2 else 0) ∧
  ∀ (u v:ℕ→ Bool) (uo vo:Bool),
   (∀ i< W,¬ 0< deg.getD i 0→ base.getD i false= v i) →
   u W= op.eval (l.map u)→ v W= op.eval (l.map v) →
   (∀ w,¬ 0< deg.getD w 0→ u w= v w) →
   Zl (fun w=>0< deg.getD w 0) u v uo vo (W+1) (Z9 base st) →
   Zl (fun w=>0< deg.getD w 0) u v uo vo W (Z9 base (Zc B deg op l W st)):=by
 by_cases hD:0< deg.getD W 0
 ·rcases hop with rfl | rfl
  ·rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
   ·have e:Zc B deg GateOp.and [] W st
      = ([]:List ℕ).foldl (fun s a=>Z5 B s a (st.1 W)) st:=by
     unfold Zc;rw[Zq _ _ _ hD,Zx _ _ _ (by simp)]
    rw[e];obtain⟨f1,f2,f3⟩:=Z1p B deg base [] W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
    intro u v uo vo _ hu hv hx hI;refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
    intro _;left;simpa[GateOp.eval] using hv
   ·have e:Zc B deg GateOp.and [a] W st
      = [a].foldl (fun s a=>Z5 B s a (st.1 W)) st:=by
     unfold Zc;rw[Zq _ _ _ hD,Zx _ _ _ (by simp)]
    rw[e];obtain⟨f1,f2,f3⟩:=Z1p B deg base [a] W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
    intro u v uo vo _ hu hv hx hI;have hu':u W= u a:=by simpa[GateOp.eval] using hu
    have hv':v W= v a:=by simpa[GateOp.eval] using hv
    refine f3 u v uo vo hx ?_ ?_ ?_ hI
    ·intro i hi h
     simp only[List.mem_singleton] at hi;subst hi;rw[hu']; exact h
    ·intro i hi h
     simp only[List.mem_singleton] at hi;subst hi;rw[hv']; exact h
    ·intro h
     right;exact⟨a,by simp,by rw[← hu']; exact h⟩
   ·have e:Zc B deg GateOp.and [a,b] W st
      = if 0< deg.getD a 0 then Ze B st W a b else Ze B st W b a:=by
     unfold Zc;rw[Zq _ _ _ hD,Zq _ _ _ (by simp[Z1o])]
     rfl
    have ha:a< W:=hr a (by simp)
    have hb:b< W:=hr b (by simp)
    obtain⟨i,hi,hi0⟩:=hc rfl rfl;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rw[e];by_cases hda:0< deg.getD a 0
    ·simp only[hda,↓reduceIte]
     have hdb:¬ 0< deg.getD b 0:=by
      rcases hi with h | h
      ·rw[h] at hi0; omega
      ·rw[h] at hi0; omega
     obtain⟨k1,k2,k3⟩:=Z2e B base st W a b hB hg (by omega)
     refine⟨k1,by simp only[hD,↓reduceIte]; omega,?_⟩
     intro u v uo vo hbv hu hv hx hI;have hu':u W=(u a && u b):=by simpa[GateOp.eval] using hu
     have hv':v W=(v a && v b):=by simpa[GateOp.eval] using hv
     refine Z2s _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI;intro w;rw[k3 w,hbv b hb hdb]
    ·simp only[hda,↓reduceIte]
     obtain⟨k1,k2,k3⟩:=Z2e B base st W b a hB hg (by omega)
     refine⟨k1,by simp only[hD,↓reduceIte]; omega,?_⟩
     intro u v uo vo hbv hu hv hx hI;have hu':u W=(u b && u a):=by
      rw[Bool.and_comm]; simpa[GateOp.eval] using hu
     have hv':v W=(v b && v a):=by
      rw[Bool.and_comm]; simpa[GateOp.eval] using hv
     refine Z2s _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI;intro w;rw[k3 w,hbv a ha hda]
   ·simp at hl
  ·have e:Zc B deg GateOp.or l W st
     = l.foldl (fun s a=>Z5 B s a (st.1 W)) st:=by
    unfold Zc;rw[Zq _ _ _ hD,Zx _ _ _ (by simp[Z1o])]
   rw[e];obtain⟨f1,f2,f3⟩:=Z1p B deg base l W st hB hl hr hg hD;refine⟨f1,by simp only[hD,↓reduceIte]; exact f2,?_⟩
   intro u v uo vo _ hu hv hx hI;have hu':u W= true↔∃ i∈l,u i= true:=by
    rw[hu]; simp[GateOp.eval]
   have hv':v W= true↔∃ i∈l,v i= true:=by
    rw[hv]; simp[GateOp.eval]
   refine f3 u v uo vo hx ?_ ?_ ?_ hI
   ·intro i hi h
    exact hu'.2 ⟨i,hi,h⟩
   ·intro i hi h
    exact hv'.2 ⟨i,hi,h⟩
   ·intro h
    right;exact hu'.1 h
 ·have e:Zc B deg op l W st= st:=by
   unfold Zc;rw[Zx _ _ _ hD]
  rw[e];refine⟨hg,by simp,?_⟩
  intro u v uo vo _ _ _ _ hI;exact Z3u _ u v uo vo W _ hD hI
def Zi (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate) :
  ℕ→(ℕ→ ℕ)× List Gate
 | 0=>st0
 | d+1=>Zc B deg (gs.getD (gs.length-1-d) Z3).op
   (gs.getD (gs.length-1-d) Z3).inputs (N+(gs.length-1-d)) (Zi B N deg gs st0 d)
def Zz (N:ℕ) (deg:List ℕ) (b:ℕ):ℕ:=
 ((Finset.range b).filter (fun k=>0< deg.getD (N+k) 0)).card
lemma Z48 (N:ℕ) (deg:List ℕ) (b:ℕ) :
  Zz N deg (b+1)= Zz N deg b+(if 0< deg.getD (N+b) 0 then 1 else 0):=by
 unfold Zz;rw[Finset.range_add_one,Finset.filter_insert];split_ifs with h
 ·rw[Finset.card_insert_of_notMem (by simp)]
 ·rfl
def Z18 (N:ℕ) (deg:List ℕ) (gs:List Gate):Prop:=
 ∀ k< gs.length,((gs.getD k Z3).op= GateOp.and∨(gs.getD k Z3).op= GateOp.or) ∧
  (gs.getD k Z3).inputs.length≤2∧(∀ i∈(gs.getD k Z3).inputs,i< N+k) ∧
  ((gs.getD k Z3).op= GateOp.and→(gs.getD k Z3).inputs.length=2 →
   ∃ i∈(gs.getD k Z3).inputs,deg.getD i 0=0)
lemma Z2g (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate)
  (hNB:N+gs.length≤ B) (hgs:Z18 N deg gs) (hg0:Zh B st0) :
  ∀ d≤ gs.length,Zh B (Zi B N deg gs st0 d) ∧
   (Zi B N deg gs st0 d).2.length+2*Zz N deg (gs.length-d)
    ≤ st0.2.length+2*Zz N deg gs.length:=by
 intro d
 induction d with
 | zero=>
  intro _;exact⟨hg0,by simp[Zi]⟩
 | succ d ih=>
  intro hd;obtain⟨i1,i2⟩:=ih (by omega)
  obtain⟨k,hk⟩:∃ k,k= gs.length-1-d:=⟨_,rfl⟩;have hks:k< gs.length:=by omega
  obtain⟨a1,a2,a3,a4⟩:=hgs k hks;have e:Zi B N deg gs st0 (d+1)= Zc B deg (gs.getD k Z3).op
    (gs.getD k Z3).inputs (N+k) (Zi B N deg gs st0 d):=by
   rw[hk]; rfl
  obtain⟨p1,p2,_⟩:=Z2f B deg (List.replicate B false) (gs.getD k Z3).op
   (gs.getD k Z3).inputs (N+k) (Zi B N deg gs st0 d) List.length_replicate
   (by omega) a1 a2 a3 a4 i1
  rw[e];refine⟨p1,?_⟩;have e1:gs.length-d= k+1:=by omega
  have e2:gs.length-(d+1)= k:=by omega
  rw[e1,Z48] at i2;rw[e2];split_ifs at p2 i2 <;> omega
lemma Z49 (B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate)
  (base:List Bool) (u v:ℕ→ Bool) (uo vo:Bool)
  (hB:base.length= B) (hNB:N+gs.length≤ B) (hgs:Z18 N deg gs) (hg0:Zh B st0)
  (hv:∀ i< N+gs.length,¬ 0< deg.getD i 0→ base.getD i false= v i)
  (hu:∀ k< gs.length,u (N+k)=(gs.getD k Z3).op.eval ((gs.getD k Z3).inputs.map u))
  (hvv:∀ k< gs.length,v (N+k)=(gs.getD k Z3).op.eval ((gs.getD k Z3).inputs.map v))
  (hx:∀ w,¬ 0< deg.getD w 0→ u w= v w)
  (hI:Zl (fun w=>0< deg.getD w 0) u v uo vo (N+gs.length) (Z9 base st0)) :
  ∀ d≤ gs.length,Zl (fun w=>0< deg.getD w 0) u v uo vo (N+(gs.length-d))
   (Z9 base (Zi B N deg gs st0 d)):=by
 intro d
 induction d with
 | zero=>
  intro _;simpa[Zi] using hI
 | succ d ih=>
  intro hd;have i1:=ih (by omega)
  obtain⟨k,hk⟩:∃ k,k= gs.length-1-d:=⟨_,rfl⟩;have hks:k< gs.length:=by omega
  obtain⟨a1,a2,a3,a4⟩:=hgs k hks;have e:Zi B N deg gs st0 (d+1)= Zc B deg (gs.getD k Z3).op
    (gs.getD k Z3).inputs (N+k) (Zi B N deg gs st0 d):=by
   rw[hk]; rfl
  obtain⟨_,_,p3⟩:=Z2f B deg base (gs.getD k Z3).op
   (gs.getD k Z3).inputs (N+k) (Zi B N deg gs st0 d) hB
   (by omega) a1 a2 a3 a4 (Z2g B N deg gs st0 hNB hgs hg0 d (by omega)).1
  have e1:gs.length-d= k+1:=by omega
  have e2:gs.length-(d+1)= k:=by omega
  rw[e1] at i1;rw[e,e2];exact p3 u v uo vo (fun i hi=>hv i (by omega)) (hu k hks) (hvv k hks) hx i1
def Zg (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ):Bool:=
 (C.wires (List.ofFn z)).getD w false
lemma Zm (C:Circuit) (inp:List Bool):C.wires inp= Z1 Z4 C.gates inp:=rfl
lemma Zv (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ) (h:w< N) :
  Zg C N z w= z ⟨w,h⟩:=by
 unfold Zg
 rw[Zm,Z1u _ _ _ _ _ (by simpa using h),
  List.getD_eq_getElem _ _ (by simpa using h)]
 simp
lemma Z3v (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (w:ℕ) (h:N+C.gates.length≤ w) :
  Zg C N z w= false:=by
 unfold Zg;rw[Zm];exact Z24 _ _ _ (by rw[Z7]; simpa using h)
lemma Z1l (C:Circuit) (N:ℕ) (z:Fin N→ Bool) (hR:ReadsBack N C) (k:ℕ)
  (hk:k< C.gates.length) :
  Zg C N z (N+k)=(C.gates.getD k Z3).op.eval ((C.gates.getD k Z3).inputs.map (Zg C N z)):=by
 unfold Zg;rw[Zm];exact Z2q Z4 false Z3r C.gates _ N (by simp) k hk (hR k hk)
lemma Z25 (C:Circuit) (N:ℕ) (M:Finset ℕ):C.lineDegrees N M =
  Z1 Zt C.gates ((List.range N).map fun i=>if i∈M then 1 else 0):=rfl
lemma Z19 (C:Circuit) (N:ℕ) (M:Finset ℕ) (w:ℕ) (h:w< N) :
  (C.lineDegrees N M).getD w 0= if w∈M then 1 else 0:=by
 rw[Z25,Z1u _ _ _ _ _ (by simpa using h),
  List.getD_eq_getElem _ _ (by simpa using h)]
 simp
lemma Z4a (C:Circuit) (N:ℕ) (M:Finset ℕ) (hR:ReadsBack N C) (k:ℕ)
  (hk:k< C.gates.length) :
  (C.lineDegrees N M).getD (N+k) 0=(C.gates.getD k Z3).lineDegree (C.lineDegrees N M):=by
 rw[Z25];exact Z2q Zt 0 Z3s C.gates _ N (by simp) k hk (hR k hk)
lemma Z3h {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) (h:w< n+m)
  (hw:w< n):Fin.append x y ⟨w,h⟩= x ⟨w,hw⟩:=
 Fin.append_left x y ⟨w,hw⟩
lemma Z1g {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) (h:w< n+m)
  (hw:n≤ w):Fin.append x y ⟨w,h⟩= y ⟨w-n,by omega⟩:=by
 have e:(⟨w,h⟩:Fin (n+m))= Fin.natAdd n ⟨w-n,by omega⟩:=by
  ext;simp only[Fin.natAdd_mk];omega
 rw[e,Fin.append_right]
lemma Z4b (C:Circuit) (k:ℕ) (hk:k< C.gates.length):C.gates.getD k Z3∈C.gates:=by
 rw[List.getD_eq_getElem _ _ hk];exact List.getElem_mem _
lemma Z2t (C:Circuit) (hM:Monotone2 C) (k:ℕ) (hk:k< C.gates.length) :
  ((C.gates.getD k Z3).op= GateOp.and∨(C.gates.getD k Z3).op= GateOp.or) ∧
  (C.gates.getD k Z3).inputs.length≤2:=by
 obtain⟨h1,h2⟩:=hM _ (Z4b C k hk);refine⟨?_,h2⟩;simpa using h1
lemma Z5u (n m:ℕ) (C:Circuit) (hM:Monotone2 C) (hR:ReadsBack (n+m) C)
  (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ) :
  ((C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0=0 →
   Zg C (n+m) (Fin.append x y) w= Zg C (n+m) (Fin.append x (fun _=>false)) w) ∧
  (Zg C (n+m) (Fin.append x (fun _=>false)) w= true →
   Zg C (n+m) (Fin.append x y) w= true):=by
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  rcases Nat.lt_or_ge w (n+m) with h | h
  ·rw[Zv _ _ _ _ h,Zv _ _ _ _ h,Z19 _ _ _ _ h]
   rcases Nat.lt_or_ge w n with hw | hw
   ·rw[Z3h _ _ _ _ hw,Z3h _ _ _ _ hw]
    exact⟨fun _=>rfl,fun h=>h⟩
   ·rw[Z1g _ (fun _=>false) _ _ hw]
    have:w∈Finset.Ico n (n+m):=by simp; omega
    simp[this]
  ·rcases Nat.lt_or_ge (w-(n+m)) C.gates.length with hk | hk
   ·obtain⟨k,rfl⟩:∃ k,w= n+m+k:=⟨w-(n+m),by omega⟩
    have hk':k< C.gates.length:=by omega
    have hu:=Z1l C (n+m) (Fin.append x y) hR k hk';have hv:=Z1l C (n+m) (Fin.append x (fun _=>false)) hR k hk'
    have hd:=Z4a C (n+m) (Finset.Ico n (n+m)) hR k hk';have hr:∀ i∈(C.gates.getD k Z3).inputs,i< n+m+k:=hR k hk';obtain⟨hop,hl⟩:=Z2t C hM k hk'
    generalize C.gates.getD k Z3= g at hu hv hd hr hop hl
    obtain⟨op,l⟩:=g;simp only at hop hl hr;rw[hu,hv,hd];rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
    ·rcases hop with rfl | rfl <;> simp[GateOp.eval]
    ·obtain⟨a1,a2⟩:=ih a (hr a (by simp))
     rcases hop with rfl | rfl
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.all_cons,
       List.all_nil,id,Bool.and_true,↓reduceIte,add_zero]
      exact⟨a1,a2⟩
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.any_cons,
       List.any_nil,id,Bool.or_false,reduceCtorEq,↓reduceIte,Nat.max_zero]
      exact⟨a1,a2⟩
    ·obtain⟨a1,a2⟩:=ih a (hr a (by simp))
     obtain⟨b1,b2⟩:=ih b (hr b (by simp))
     rcases hop with rfl | rfl
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.all_cons,
       List.all_nil,id,Bool.and_true,↓reduceIte,add_zero]
      constructor
      ·intro h0
       rw[a1 (by omega),b1 (by omega)]
      ·intro hh
       simp only[Bool.and_eq_true] at hh ⊢;exact⟨a2 hh.1,b2 hh.2⟩
     ·simp only[Gate.lineDegree,GateOp.eval]
      simp only[List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.any_cons,
       List.any_nil,id,Bool.or_false,reduceCtorEq,↓reduceIte,Nat.max_zero]
      constructor
      ·intro h0
       rw[a1 (by omega),b1 (by omega)]
      ·intro hh
       simp only[Bool.or_eq_true] at hh ⊢;exact hh.imp a2 b2
    ·simp at hl
   ·rw[Z3v _ _ _ _ (by omega),Z3v _ _ _ _ (by omega)]
    exact⟨fun _=>rfl,fun h=>h⟩
lemma Z3w (N s:ℕ) (deg:List ℕ) :
  Set.ncard {j:ℕ | j< s∧0< deg.getD (N+j) 0}= Zz N deg s:=by
 unfold Zz;rw[← Set.ncard_coe_finset]
 congr 1
 ext j;simp
lemma Z4c (n m:ℕ) (C:Circuit) (hM:Monotone2 C) (hR:ReadsBack (n+m) C)
  (hX:∀ j< C.gates.length,(gateAt C j).op= GateOp.and→(gateAt C j).inputs.length=2 →
   ∃ i∈(gateAt C j).inputs,(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0) :
  Z18 (n+m) (C.lineDegrees (n+m) (Finset.Ico n (n+m))) C.gates:=by
 intro k hk;obtain⟨h1,h2⟩:=Z2t C hM k hk;exact⟨h1,h2,hR k hk,hX k hk⟩
lemma Z3x (Dp:ℕ→ Prop) (u v:ℕ→ Bool) (r bound:ℕ) (A:ℕ→ Bool)
  (hA:∀ w,A w= decide (w= r)) (hx:∀ w,¬ Dp w→ u w= v w)
  (hb:u r= true→ r< bound) :
  Zl Dp u v (u r) (v r) bound A:=by
 refine⟨?_,?_,?_⟩
 ·intro w _ _ ha hz
  rw[hA] at ha;simp only[decide_eq_true_eq] at ha;subst ha;exact hz
 ·intro w _ _ ha hz
  rw[hA] at ha;simp only[decide_eq_true_eq] at ha;subst ha;exact hz
 ·intro h
  by_cases hd:Dp r
  ·right
   exact⟨r,hb h,hd,by simp[hA],h⟩
  ·left
   rw[← hx r hd];exact h
lemma Z4l (g:Gate) (d:List ℕ) (h:∀ i∈g.inputs,d.getD i 0=0):Zt d g=0:=by
 have key:∀ l:List ℕ,(∀ i∈l,d.getD i 0=0) →
   (l.map fun i=>d.getD i 0).sum=0∧(l.map fun i=>d.getD i 0).foldr max 0=0:=by
  intro l
  induction l with
  | nil=>intro _; simp
  | cons a l ih=>
   intro hl;obtain⟨i1,i2⟩:=ih (fun i hi=>hl i (List.mem_cons_of_mem _ hi))
   have ha:=hl a (by simp)
   simp only[List.map_cons,List.sum_cons,List.foldr_cons];rw[i1,i2,ha];simp
 unfold Zt Gate.lineDegree;split_ifs
 ·exact (key _ h).1
 ·exact (key _ h).2
lemma Z4d (K:ℕ) (gs:List Gate) (w0:List ℕ) (hK:w0.length= K)
  (h:∀ g∈gs,∀ i∈g.inputs,K≤ i∨w0.getD i 0=0) :
  ∀ i,K≤ i→(Z1 Zt gs w0).getD i 0=0:=by
 induction gs using List.reverseRecOn with
 | nil=>
  intro i hi
  show w0.getD i 0=0
  exact Z24 _ _ _ (by omega)
 | append_singleton gs g ih=>
  have ih':=ih (fun g' hg'=>h g' (List.mem_append_left _ hg'))
  intro i hi;rw[Zo];have hlen:=Z7 Zt gs w0;rcases Nat.lt_trichotomy i (Z1 Zt gs w0).length with hlt | heq | hgt
  ·rw[Z8 _ _ _ _ hlt]
   exact ih' i hi
  ·rw[heq,Zk]
   apply Z4l;intro j hj;rcases Nat.lt_or_ge j K with hjK | hjK
   ·rw[Z1u _ _ _ _ _ (by omega)]
    rcases h g (by simp) j hj with h1 | h1
    ·omega
    ·exact h1
   ·exact ih' j hjK
  ·exact Z24 _ _ _ (by simp only[List.length_append,List.length_singleton]; omega)
def Zu (K:ℕ) (deg:List ℕ) (st:(ℕ→ ℕ)× List Gate):Prop:=
 (∀ w,K≤ st.1 w)∧∀ g∈st.2,∀ i∈g.inputs,K≤ i∨deg.getD i 0=0
lemma Z2u (K B:ℕ) (deg:List ℕ) (st:(ℕ→ ℕ)× List Gate) (a src:ℕ) (hKB:K≤ B)
  (h:Zu K deg st) (hs:K≤ src):Zu K deg (Z5 B st a src):=by
 obtain⟨h1,h2⟩:=h;refine⟨?_,?_⟩
 ·intro w
  simp only[Z5,Function.update_apply];split_ifs
  ·omega
  ·exact h1 w
 ·intro g hg i hi
  simp only[Z5,List.mem_append,List.mem_singleton] at hg;rcases hg with hg | hg
  ·exact h2 g hg i hi
  ·rw[hg] at hi
   simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with e | e
   ·left; rw[e]; exact h1 a
   ·left; rw[e]; exact hs
lemma Z4e (K B:ℕ) (deg:List ℕ) (src:ℕ) (hKB:K≤ B) (hs:K≤ src) (l:List ℕ) :
  ∀ st:(ℕ→ ℕ)× List Gate,Zu K deg st →
   Zu K deg (l.foldl (fun s a=>Z5 B s a src) st):=by
 induction l with
 | nil=>intro st h; exact h
 | cons a l ih=>
  intro st h;rw[List.foldl_cons];exact ih _ (Z2u K B deg st a src hKB h hs)
lemma Z2v (K B:ℕ) (deg:List ℕ) (st:(ℕ→ ℕ)× List Gate) (W tgt side:ℕ)
  (hKB:K≤ B) (h:Zu K deg st) (hd:deg.getD side 0=0) :
  Zu K deg (Ze B st W tgt side):=by
 unfold Ze;obtain⟨h1,h2⟩:=h;apply Z2u K B deg _ _ _ hKB _ (by omega)
 refine⟨h1,?_⟩;intro g hg i hi;simp only[List.mem_append,List.mem_singleton] at hg;rcases hg with hg | hg
 ·exact h2 g hg i hi
 ·rw[hg] at hi
  simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with e | e
  ·left; rw[e]; exact h1 W
  ·right; rw[e]; exact hd
lemma Z4f (K B:ℕ) (deg:List ℕ) (op:GateOp) (l:List ℕ) (W:ℕ)
  (st:(ℕ→ ℕ)× List Gate) (hKB:K≤ B)
  (hc:op= GateOp.and→ l.length=2→∃ i∈l,deg.getD i 0=0)
  (h:Zu K deg st):Zu K deg (Zc B deg op l W st):=by
 unfold Zc;by_cases hD:0< deg.getD W 0
 ·rw[Zq _ _ _ hD]
  by_cases hA:Z1o op= true∧l.length=2
  ·rw[Zq _ _ _ hA]
   have hop:op= GateOp.and:=by
    obtain⟨hA1,_⟩:=hA;cases op <;> first | rfl | (simp[Z1o] at hA1)
   obtain⟨i,hi,hi0⟩:=hc hop hA.2;obtain⟨a,b,rfl⟩:=List.length_eq_two.mp hA.2;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;by_cases hda:0< deg.getD a 0
   ·have e:(if 0< deg.getD ([a,b].getD 0 0) 0
      then Ze B st W ([a,b].getD 0 0) ([a,b].getD 1 0)
      else Ze B st W ([a,b].getD 1 0) ([a,b].getD 0 0))= Ze B st W a b:=
     Zq _ _ _ hda
    rw[e];apply Z2v K B deg st W a b hKB h;rcases hi with e | e
    ·rw[e] at hi0; omega
    ·rw[e] at hi0; exact hi0
   ·have e:(if 0< deg.getD ([a,b].getD 0 0) 0
      then Ze B st W ([a,b].getD 0 0) ([a,b].getD 1 0)
      else Ze B st W ([a,b].getD 1 0) ([a,b].getD 0 0))= Ze B st W b a:=
     Zx _ _ _ hda
    rw[e];apply Z2v K B deg st W b a hKB h;omega
  ·rw[Zx _ _ _ hA]
   exact Z4e K B deg (st.1 W) hKB (h.1 W) l st h
 ·rw[Zx _ _ _ hD]
  exact h
lemma Z4g (K B N:ℕ) (deg:List ℕ) (gs:List Gate) (st0:(ℕ→ ℕ)× List Gate)
  (hKB:K≤ B) (hgs:Z18 N deg gs) (h0:Zu K deg st0) :
  ∀ d≤ gs.length,Zu K deg (Zi B N deg gs st0 d):=by
 intro d
 induction d with
 | zero=>intro _; exact h0
 | succ d ih=>
  intro hd
  show Zu K deg (Zc B deg _ _ _ (Zi B N deg gs st0 d))
  exact Z4f K B deg _ _ _ _ hKB (hgs _ (by omega)).2.2.2 (ih (by omega))
lemma Z32 (n m:ℕ) (G A:List Gate)
  (hA:∀ g∈A,∀ i∈g.inputs,n+m+G.length≤ i ∨
   ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0) :
  ∀ i,n+m+G.length≤ i →
   ((Circuit.mk (G++A) 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0:=by
 intro i hi;rw[Z25]
 show (Z1 Zt (G++A) _).getD i 0=0
 rw[Z1i];exact Z4d _ A _ (by show (Z1 Zt G _).length=_; rw[Z7]; simp) hA i hi
lemma Z4h (w:List Bool) (K:ℕ) (hK:w.length= K) (b:Bool) :
  (w++[b]).getD K false= b:=by
 subst hK;exact Zk _ _ _
lemma Z3i (n m:ℕ) (G:List Gate) (g:Gate) (hg:g.inputs=[])
  (hop:g.op= GateOp.and∨g.op= GateOp.or) :
  (∀ g'∈[g],g'.op∈({GateOp.and,GateOp.or}:Set GateOp)∧g'.inputs.length≤2) ∧
  (∀ k<[g].length,∀ i∈([g].getD k (Gate.mk GateOp.or [])).inputs,i< n+m+G.length+k) ∧
  (∀ k<[g].length,
   ((Circuit.mk (G++[g]) 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD
    (n+m+G.length+k) 0=0) ∧
  (n+m+G.length< n+m+G.length+[g].length ∧
   ((Circuit.mk (G++[g]) 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD
    (n+m+G.length) 0=0) ∧
  ∀ (z:Fin (n+m)→ Bool),((Circuit.mk (G++[g]) 0).wires (List.ofFn z)).getD
   (n+m+G.length) false= g.op.eval []:=by
 have hd:=Z32 n m G [g] (by
  intro g' hg' i hi;simp only[List.mem_singleton] at hg';rw[hg',hg] at hi
  simp at hi)
 refine⟨?_,?_,?_,⟨by simp,hd _ (le_refl _)⟩,?_⟩
 ·intro g' hg'
  simp only[List.mem_singleton] at hg';rw[hg',hg];refine⟨?_,by simp⟩
  rcases hop with h | h <;> simp[h]
 ·exact Z2c _ _ (by
   intro g' hg';simp only[List.mem_singleton] at hg'
   rw[hg',hg])
 ·intro k _
  exact hd _ (by omega)
 ·intro z
  rw[Zm]
  show (Z1 Z4 (G++[g]) _).getD _ _=_
  rw[Zo];have e:Z4 (Z1 Z4 G (List.ofFn z)) g= g.op.eval []:=by
   unfold Z4;rw[hg];rfl
  rw[e];exact Z4h _ _ (by rw[Z7]; simp) _
def Z10 (n m:ℕ) (G:List Gate) (r:ℕ):Prop:=
 Monotone2 (Circuit.mk G 0) →
 ReadsBack (n+m) (Circuit.mk G 0) →
 (∀ j< G.length,(gateAt (Circuit.mk G 0) j).op= GateOp.and →
  (gateAt (Circuit.mk G 0) j).inputs.length=2 →
  ∃ i∈(gateAt (Circuit.mk G 0) j).inputs,
   ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0) →
 r< n+m+G.length →
 ∃ (A:List Gate) (o:Fin m→ ℕ),
  (∀ g∈A,g.op∈({GateOp.and,GateOp.or}:Set GateOp)∧g.inputs.length≤2) ∧
  (∀ k< A.length,∀ i∈(A.getD k (Gate.mk GateOp.or [])).inputs,i< n+m+G.length+k) ∧
  A.length≤3*Set.ncard {j:ℕ | j< G.length ∧
   0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD (n+m+j) 0}+m ∧
  (∀ k< A.length,
   ((Circuit.mk (G++A) 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD
    (n+m+G.length+k) 0=0) ∧
  (∀ j:Fin m,o j< n+m+G.length+A.length ∧
   ((Circuit.mk (G++A) 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD (o j) 0=0) ∧
  ∀ (x:Fin n→ Bool) (y:Fin m→ Bool) (j:Fin m),
   ((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun l=>decide (l= j))))).getD r false =
    (((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun _:Fin m=>false)))).getD r false ||
     ((Circuit.mk (G++A) 0).wires (List.ofFn (Fin.append x y))).getD (o j) false)
lemma Z4m (n m:ℕ) (G:List Gate) (r:ℕ):Z10 n m G r:=by
 intro hM hR hX hr;have hF:=fun (x:Fin n→ Bool) (y:Fin m→ Bool) (w:ℕ)=>
  Z5u n m (Circuit.mk G 0) hM hR x y w
 rw[Z3w];rcases Nat.eq_zero_or_pos m with hm | hm
 ·subst hm
  exact⟨[],fun j=>j.elim0,by simp,by simp,by simp,by simp,fun j=>j.elim0,
   fun x y j=>j.elim0⟩
 by_cases hout:0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD r 0
 ·by_cases hbig:2≤ Zz (n+m) ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m)))
    G.length+m
  ·
   have hgs:Z18 (n+m) ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))) G:=
    Z4c n m (Circuit.mk G 0) hM hR hX
   have hg0:Zh (n+m+G.length+2)
     ((fun w=>if w= r then n+m+G.length else n+m+G.length+1),
      ([]:List Gate)):=by
    refine⟨?_,?_,?_⟩
    ·intro w
     simp only[List.length_nil];split_ifs <;> omega
    ·intro g hg
     simp at hg
    ·intro j hj
     simp at hj
   have hs0:Zu (n+m+G.length)
     ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m)))
     ((fun w=>if w= r then n+m+G.length else n+m+G.length+1),
      ([]:List Gate)):=by
    refine⟨?_,?_⟩
    ·intro w
     show n+m+G.length≤(if w= r then n+m+G.length else n+m+G.length+1)
     split_ifs <;> omega
    ·intro g hg
     simp at hg
   obtain⟨q1,q2⟩:=Z2g (n+m+G.length+2) (n+m)
    ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))) G _ (by omega) hgs hg0
    G.length (le_refl _)
   have q3:=Z4g (n+m+G.length) (n+m+G.length+2) (n+m)
    ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))) G _ (by omega) hgs hs0
    G.length (le_refl _)
   obtain⟨st,hst⟩:∃ st,st= Zi (n+m+G.length+2) (n+m)
    ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))) G
    ((fun w=>if w= r then n+m+G.length else n+m+G.length+1),([]:List Gate))
    G.length:=⟨_,rfl⟩
   rw[← hst] at q1 q2 q3;obtain⟨q11,q12,q13⟩:=q1;obtain⟨q31,q32⟩:=q3;have hsyn:∀ g∈[Gate.mk GateOp.and [],Gate.mk GateOp.or []]++st.2,∀ i∈g.inputs,
     n+m+G.length≤ i ∨
     ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0:=by
    intro g hg i hi;simp only[List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg;rcases hg with (hg | hg) | hg
    ·rw[hg] at hi; simp at hi
    ·rw[hg] at hi; simp at hi
    ·exact q32 g hg i hi
   have hd:=Z32 n m G _ hsyn
   refine⟨[Gate.mk GateOp.and [],Gate.mk GateOp.or []]++st.2,
    fun j=>st.1 (n+j.val),?_,?_,?_,?_,?_,?_⟩
   ·intro g hg
    simp only[List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg;rcases hg with (hg | hg) | hg
    ·rw[hg]; simp
    ·rw[hg]; simp
    ·obtain⟨h1,h2⟩:=q12 g hg
     refine⟨?_,h2⟩;rcases h1 with h1 | h1 <;> simp[h1]
   ·show Z1f (n+m+G.length) _
    apply Z28
    ·exact Z2c _ _ (by
      intro g hg;simp only[List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with hg | hg <;> rw[hg])
    ·exact q13
   ·simp only[List.length_append,List.length_cons,List.length_nil]
    simp only[List.length_nil] at q2;omega
   ·intro k _
    exact hd _ (by omega)
   ·intro j
    refine⟨?_,hd _ (q31 _)⟩;have:=q11 (n+j.val);simp only[List.length_append,List.length_cons,List.length_nil];omega
   ·intro x y j
    obtain⟨base,hbase⟩:∃ base,base =
     (Circuit.mk G 0).wires (List.ofFn (Fin.append x y))++[true,false]:=⟨_,rfl⟩
    have hvl:((Circuit.mk G 0).wires (List.ofFn (Fin.append x y))).length
      = n+m+G.length:=by
     rw[Zm,Z7];simp
    have hBl:base.length= n+m+G.length+2:=by
     rw[hbase,List.length_append,hvl];rfl
    have hw:(Circuit.mk (G++([Gate.mk GateOp.and [],Gate.mk GateOp.or []]++st.2)) 0).wires
      (List.ofFn (Fin.append x y))= Z1 Z4 st.2 base:=by
     rw[Zm]
     show Z1 Z4 (G++([Gate.mk GateOp.and [],Gate.mk GateOp.or []]++st.2)) _=_
     rw[Z1i,Z1i,hbase,Zm]
     congr 1
     show Z1 Z4 [Gate.mk GateOp.and [],Gate.mk GateOp.or []] (Z1 Z4 G _) =
      Z1 Z4 G _++[true,false]
     simp[Z1,Z4,GateOp.eval]
    rw[hw];have hv:∀ i< n+m+G.length,
      ¬ 0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0 →
      base.getD i false= Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false)) i:=by
     intro i hi hi0;rw[hbase,Z8 _ _ _ _ (by omega)]
     exact (hF x y i).1 (by omega)
    have hT:base.getD (n+m+G.length) false= true:=by
     rw[hbase,List.getD_append_right _ _ _ _ (by omega),hvl,Nat.sub_self]
     rfl
    have hFl:base.getD (n+m+G.length+1) false= false:=by
     rw[hbase,List.getD_append_right _ _ _ _ (by omega),hvl,Nat.add_sub_cancel_left]
     rfl
    have hx:∀ w,¬ 0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0 →
      Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j))) w
       = Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false)) w:=by
     intro w hw0;exact (hF x _ w).1 (by omega)
    have hI0:=Z3x
     (fun w=>0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0)
     (Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j))))
     (Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false))) r (n+m+G.length)
     (Z9 base ((fun w=>if w= r then n+m+G.length else n+m+G.length+1),
      ([]:List Gate)))
     (by
      intro w;unfold Z9
      show (base).getD (if w= r then n+m+G.length else n+m+G.length+1) false=_
      by_cases hwo:w= r
      ·rw[Zq _ _ _ hwo,hT]; simp[hwo]
      ·rw[Zx _ _ _ hwo,hFl]; simp[hwo])
     hx (fun _=>hr)
    have hfin:=Z49 (n+m+G.length+2) (n+m)
     ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))) G _ base _ _ _ _ hBl
     (by omega) hgs hg0 hv
     (fun k hk=>Z1l (Circuit.mk G 0) (n+m) _ hR k hk)
     (fun k hk=>Z1l (Circuit.mk G 0) (n+m) _ hR k hk)
     hx hI0 G.length (le_refl _)
    rw[← hst] at hfin;obtain⟨f1,_,f3⟩:=hfin;have hjlt:n+j.val< n+m:=by have:=j.isLt; omega
    have hdj:0<((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m))).getD
      (n+j.val) 0:=by
     rw[Z19 _ _ _ _ hjlt];have:n+j.val∈Finset.Ico n (n+m):=by simp
     simp[this]
    have huj:Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j)))
      (n+j.val)= true:=by
     rw[Zv _ _ _ _ hjlt,Z1g _ _ _ _ (by omega)]
     simp only[decide_eq_true_eq];ext;simp
    show Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j))) r =
     (Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false)) r ||
      Z9 base st (n+j.val))
    rw[Bool.eq_iff_iff];simp only[Bool.or_eq_true];constructor
    ·intro huo
     rcases f3 huo with h | ⟨w,hw,hd,ha,hz⟩
     ·left; exact h
     ·right
      have hwN:w< n+m:=by omega
      have hwn:n≤ w:=by
       by_contra hcon
       have hd':0<((Circuit.mk G 0).lineDegrees (n+m)
        (Finset.Ico n (n+m))).getD w 0:=hd
       rw[Z19 _ _ _ _ hwN] at hd';have:w∉Finset.Ico n (n+m):=by simp; omega
       simp[this] at hd'
      rw[Zv _ _ _ _ hwN,Z1g _ _ _ _ hwn] at hz;simp only[decide_eq_true_eq] at hz;have e:w= n+j.val:=by
       rw[← hz];simp only;omega
      rw[← e];exact ha
    ·rintro (h | h)
     ·exact (hF x _ r).2 h
     ·exact f1 (n+j.val) (by omega) hdj h huj
  ·
   have hrN:r< n+m:=by
    by_contra hcon
    apply hbig;have:1≤ Zz (n+m) ((Circuit.mk G 0).lineDegrees (n+m) (Finset.Ico n (n+m)))
      G.length:=by
     unfold Zz;apply Finset.card_pos.mpr;refine⟨r-(n+m),?_⟩;simp only[Finset.mem_filter,Finset.mem_range];refine⟨by omega,?_⟩
     have e:n+m+(r-(n+m))= r:=by omega
     rw[e];exact hout
    omega
   have hn:n≤ r:=by
    by_contra hcon
    have:r∉Finset.Ico n (n+m):=by simp; omega
    rw[Z19 _ _ _ _ hrN] at hout;simp[this] at hout
   obtain⟨s1,s2,s3,s4,s5⟩:=Z3i n m G (Gate.mk GateOp.and []) rfl (Or.inl rfl)
   refine⟨[Gate.mk GateOp.and []],fun _=>n+m+G.length,s1,s2,?_,s3,
    fun _=>s4,?_⟩
   ·simp only[List.length_singleton]
    omega
   ·intro x y j
    rw[s5]
    show Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j))) r =
     (Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false)) r || _)
    rw[Zv _ _ _ _ hrN,Zv _ _ _ _ hrN,Z1g _ _ _ _ hn,Z1g _ _ _ _ hn];have e1:(⟨r-n,by omega⟩:Fin m)= j:=by
     ext;have:=j.isLt;simp only;omega
    simp[e1,GateOp.eval]
 ·obtain⟨s1,s2,s3,s4,s5⟩:=Z3i n m G (Gate.mk GateOp.or []) rfl (Or.inr rfl)
  refine⟨[Gate.mk GateOp.or []],fun _=>n+m+G.length,s1,s2,?_,s3,
   fun _=>s4,?_⟩
  ·simp only[List.length_singleton]
   omega
  ·intro x y j
   rw[s5]
   show Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun l=>decide (l= j))) r =
    (Zg (Circuit.mk G 0) (n+m) (Fin.append x (fun _=>false)) r || _)
   rw[(hF x _ r).1 (by omega)]
   simp[GateOp.eval]
def Z0:Gate:=Gate.mk GateOp.or []
def W (G:List Gate) (x:List Bool):List Bool:=
 G.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
def val (G:List Gate) (x:List Bool) (i:ℕ):Bool:=(W G x).getD i false
def d0 (n m:ℕ):List ℕ:=
 (List.range (n+m)).map fun i=>if i∈Finset.Ico n (n+m) then 1 else 0
def Dg (G:List Gate) (d:List ℕ):List ℕ:=
 G.foldl (fun d g=>d++[g.lineDegree d]) d
def dg (n m:ℕ) (G:List Gate) (i:ℕ):ℕ:=(Dg G (d0 n m)).getD i 0
def RB (N:ℕ) (G:List Gate):Prop:=
 ∀ j< G.length,∀ i∈(G.getD j Z0).inputs,i< N+j
def Zr (G:List Gate):Prop:=
 ∀ g∈G,g.op∈({GateOp.and,GateOp.or}:Set GateOp)∧g.inputs.length≤2
def NC (n m:ℕ) (G:List Gate):Prop:=
 ∀ j< G.length,(G.getD j Z0).op= GateOp.and→(G.getD j Z0).inputs.length=2 →
  ∃ i∈(G.getD j Z0).inputs,dg n m G i=0
lemma Z3y (G:List Gate) (g:Gate) (x:List Bool) :
  W (G++[g]) x= W G x++[g.op.eval (g.inputs.map (val G x))]:=by
 unfold W;rw[List.foldl_append];rfl
lemma Z26 (G:List Gate) (x:List Bool):(W G x).length= x.length+G.length:=by
 induction G using List.reverseRecOn with
 | nil=>simp[W]
 | append_singleton G g ih=>rw[Z3y]; simp[ih]; omega
lemma Zd (G A:List Gate) (x:List Bool) (i:ℕ) (hi:i< x.length+G.length) :
  val (G++A) x i= val G x i:=by
 induction A using List.reverseRecOn with
 | nil=>simp
 | append_singleton A a ih=>
  rw[← List.append_assoc];unfold val at *;rw[Z3y,List.getD_append _ _ _ _ (by rw[Z26]; simp; omega)]
  exact ih
lemma Z15 (G:List Gate) (x:List Bool) (i:ℕ) (hi:i< x.length) :
  val G x i= x.getD i false:=by
 have:=Zd [] G x i (by simpa using hi)
 simpa[val,W] using this
lemma Z2o (G:List Gate) (g:Gate) (x:List Bool) :
  val (G++[g]) x (x.length+G.length)= g.op.eval (g.inputs.map (val G x)):=by
 unfold val;rw[Z3y,List.getD_append_right _ _ _ _ (by rw[Z26])]
 simp[Z26];rfl
lemma Z33 (N:ℕ) (G:List Gate) (g:Gate) (h:RB N (G++[g])):RB N G:=by
 intro j hj i hi;have:=h j (by simp; omega) i
 rw[List.getD_append _ _ _ _ hj] at this;exact this hi
lemma Zs (G A:List Gate) (k:ℕ) :
  (G++A).getD (G.length+k) Z0= A.getD k Z0:=by
 rw[List.getD_append_right _ _ _ _ (by omega)]
 simp
lemma Z5d (G:List Gate) (x:List Bool) (j:ℕ) (hrb:RB x.length G)
  (hj:j< G.length) :
  val G x (x.length+j) =
   (G.getD j Z0).op.eval ((G.getD j Z0).inputs.map (val G x)):=by
 induction G using List.reverseRecOn with
 | nil=>simp at hj
 | append_singleton G g ih=>
  by_cases hlt:j< G.length
  ·rw[Zd _ _ _ _ (by omega),ih (Z33 _ _ _ hrb) hlt,
    List.getD_append _ _ _ _ hlt]
   congr 1
   apply List.map_congr_left;intro i hi;have:=hrb j hj i (by rw[List.getD_append _ _ _ _ hlt]; exact hi)
   exact (Zd _ _ _ _ (by omega)).symm
  ·have hje:j= G.length:=by simp at hj; omega
   subst hje;have hg:(G++[g]).getD G.length Z0= g:=by
    simp
   rw[Z2o,hg]
   congr 1
   apply List.map_congr_left;intro i hi;have:=hrb G.length hj i (by rw[hg]; exact hi)
   exact (Zd _ _ _ _ (by omega)).symm
lemma Z2p (G:List Gate) (g:Gate) (d:List ℕ) :
  Dg (G++[g]) d= Dg G d++[g.lineDegree (Dg G d)]:=by
 simp[Dg,List.foldl_append]
lemma Z16 (G:List Gate) (d:List ℕ):(Dg G d).length= d.length+G.length:=by
 induction G using List.reverseRecOn with
 | nil=>simp[Dg]
 | append_singleton G g ih=>rw[Z2p]; simp[ih]; omega
lemma Z17 (n m:ℕ):(d0 n m).length= n+m:=by simp[d0]
lemma Z6 (n m:ℕ) (G A:List Gate) (i:ℕ) (hi:i< n+m+G.length) :
  dg n m (G++A) i= dg n m G i:=by
 induction A using List.reverseRecOn with
 | nil=>simp
 | append_singleton A a ih=>
  rw[← List.append_assoc];unfold dg at *;rw[Z2p,List.getD_append _ _ _ _ (by rw[Z16,Z17]; simp; omega)]
  exact ih
lemma Z1q (n m:ℕ) (G:List Gate) (i:ℕ) (hi:i< n+m) :
  dg n m G i= if n≤ i then 1 else 0:=by
 have:=Z6 n m [] G i (by simpa using hi)
 simp only[List.nil_append] at this;rw[this];simp[dg,Dg,d0,hi]
lemma Z1r (g:Gate) (d d':List ℕ)
  (h:∀ i∈g.inputs,d.getD i 0= d'.getD i 0):g.lineDegree d= g.lineDegree d':=by
 have:g.inputs.map (fun i=>d.getD i 0)= g.inputs.map (fun i=>d'.getD i 0):=
  List.map_congr_left h
 unfold Gate.lineDegree;rw[this]
lemma Z34 (n m:ℕ) (G:List Gate) (g:Gate) :
  dg n m (G++[g]) (n+m+G.length)= g.lineDegree (Dg G (d0 n m)):=by
 unfold dg;rw[Z2p,List.getD_append_right _ _ _ _ (by rw[Z16,Z17])]
 simp[Z16,Z17]
lemma Z1n (n m:ℕ) (G:List Gate) (j:ℕ) (hrb:RB (n+m) G) (hj:j< G.length) :
  dg n m G (n+m+j)=(G.getD j Z0).lineDegree (Dg G (d0 n m)):=by
 induction G using List.reverseRecOn with
 | nil=>simp at hj
 | append_singleton G g ih=>
  by_cases hlt:j< G.length
  ·rw[Z6 _ _ _ _ _ (by omega),ih (Z33 _ _ _ hrb) hlt,
    List.getD_append _ _ _ _ hlt]
   apply Z1r;intro i hi;have:=hrb j hj i (by rw[List.getD_append _ _ _ _ hlt]; exact hi)
   exact (Z6 n m G [g] i (by omega)).symm
  ·have hje:j= G.length:=by simp at hj; omega
   subst hje;have hg:(G++[g]).getD G.length Z0= g:=by
    simp
   rw[Z34,hg];apply Z1r;intro i hi;have:=hrb G.length hj i (by rw[hg]; exact hi)
   exact (Z6 n m G [g] i (by omega)).symm
lemma Z1d (g:Gate) (d:List ℕ) (h:g.op= GateOp.and) :
  g.lineDegree d=(g.inputs.map fun i=>d.getD i 0).sum:=by
 unfold Gate.lineDegree;simp[h]
lemma Z1j (g:Gate) (d:List ℕ) (h:g.op= GateOp.or) :
  g.lineDegree d=(g.inputs.map fun i=>d.getD i 0).foldr max 0:=by
 unfold Gate.lineDegree;simp[h]
def xy {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool):List Bool:=List.ofFn (Fin.append x y)
lemma Z2 {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool):(xy x y).length= n+m:=by
 simp[xy]
lemma Z5o {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (i:ℕ) (hi:i< n) :
  (xy x y).getD i false= x ⟨i,hi⟩:=by
 unfold xy;have hl:i<(List.ofFn (Fin.append x y)).length:=by simp; omega
 rw[List.getD_eq_getElem _ _ hl,List.getElem_ofFn];exact Fin.append_left x y ⟨i,hi⟩
lemma Z5e {n m:ℕ} (x:Fin n→ Bool) (y:Fin m→ Bool) (l:Fin m) :
  (xy x y).getD (n+l) false= y l:=by
 unfold xy;have hl:n+(l:ℕ)<(List.ofFn (Fin.append x y)).length:=by simp
 rw[List.getD_eq_getElem _ _ hl,List.getElem_ofFn];exact Fin.append_right x y l
lemma Z35 {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (y:Fin m→ Bool) (i:ℕ)
  (hi:i< n):val G (xy x y) i= x ⟨i,hi⟩:=by
 rw[Z15 _ _ _ (by rw[Z2]; omega),Z5o]
lemma Z4n {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (y:Fin m→ Bool) (l:Fin m) :
  val G (xy x y) (n+l)= y l:=by
 rw[Z15 _ _ _ (by rw[Z2]; omega),Z5e]
lemma Z1e (G:List Gate) (x:List Bool) (i:ℕ) (hi:x.length+G.length≤ i) :
  val G x i= false:=by
 unfold val;exact List.getD_eq_default _ _ (by rw[Z26]; exact hi)
lemma Z1v {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (y:Fin m→ Bool) (j:ℕ)
  (hrb:RB (n+m) G) (hj:j< G.length) :
  val G (xy x y) (n+m+j) =
   (G.getD j Z0).op.eval ((G.getD j Z0).inputs.map (val G (xy x y))):=by
 have:=Z5d G (xy x y) j (by rw[Z2]; exact hrb) hj
 rw[Z2] at this;exact this
lemma Z5v (n m:ℕ) (G:List Gate) (i:ℕ) (hi:n+m+G.length≤ i) :
  dg n m G i=0:=by
 unfold dg;exact List.getD_eq_default _ _ (by rw[Z16,Z17]; exact hi)
lemma Z3k (l:List ℕ) (h:l.length≤2) :
  l=[]∨(∃ a,l=[a])∨∃ a b,l=[a,b]:=by
 match l,h with
 | [],_=>exact Or.inl rfl
 | [a],_=>exact Or.inr (Or.inl ⟨a,rfl⟩)
 | [a,b],_=>exact Or.inr (Or.inr ⟨a,b,rfl⟩)
 | _::_::_::_,h=>simp at h
lemma Z5f (G:List Gate) (j:ℕ) (hj:j< G.length):G.getD j Z0∈G:=by
 rw[List.getD_eq_getElem _ _ hj];exact List.getElem_mem hj
lemma Z36 (G:List Gate) (hm:Zr G) (j:ℕ) (hj:j< G.length) :
  ((G.getD j Z0).op= GateOp.and∨(G.getD j Z0).op= GateOp.or) ∧
   (G.getD j Z0).inputs.length≤2:=by
 have:=hm _ (Z5f G j hj);refine⟨?_,this.2⟩;have h1:=this.1;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at h1;exact h1
lemma Z3z (l:List ℕ) (a:ℕ) (h:a∈l):a≤ l.foldr max 0:=by
 induction l with
 | nil=>simp at h
 | cons b l ih=>
  simp only[List.foldr_cons];rcases List.mem_cons.mp h with h | h
  ·subst h; exact le_max_left _ _
  ·exact le_trans (ih h) (le_max_right _ _)
lemma Z1w (g:Gate) (d:List ℕ) (h:g.lineDegree d=0) :
  ∀ a∈g.inputs,d.getD a 0=0:=by
 intro a ha;have hmem:d.getD a 0∈g.inputs.map (fun i=>d.getD i 0):=List.mem_map.mpr ⟨a,ha,rfl⟩
 unfold Gate.lineDegree at h;split_ifs at h
 ·exact List.sum_eq_zero_iff.mp h _ hmem
 ·have:=Z3z _ _ hmem
  omega
lemma Z3l (n m:ℕ) (G:List Gate) (hrb:RB (n+m) G) (x:Fin n→ Bool)
  (y y':Fin m→ Bool) :
  ∀ i,dg n m G i=0→ val G (xy x y) i= val G (xy x y') i:=by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
  intro hd;by_cases h1:i< n
  ·rw[Z35 _ _ _ _ h1,Z35 _ _ _ _ h1]
  by_cases h2:i< n+m
  ·rw[Z1q _ _ _ _ h2] at hd
   simp[show n≤ i by omega] at hd
  by_cases h3:i< n+m+G.length
  ·obtain⟨j,rfl⟩:∃ j,i= n+m+j:=⟨i-(n+m),by omega⟩
   have hj:j< G.length:=by omega
   rw[Z1v G x y j hrb hj,Z1v G x y' j hrb hj]
   congr 1
   apply List.map_congr_left;intro a ha;have ha':=hrb j hj a ha;apply ih a (by omega)
   rw[Z1n n m G j hrb hj] at hd;exact Z1w _ _ hd a ha
  ·rw[Z1e _ _ _ (by rw[Z2]; omega),Z1e _ _ _ (by rw[Z2]; omega)]
lemma Z62 {m:ℕ} (Y:Finset (Fin m)) (f g:Fin m→ Bool) :
  decide (∃ j∈Y,(f j || g j)= true) =
   (decide (∃ j∈Y,f j= true) || decide (∃ j∈Y,g j= true)):=by
 rw[Bool.eq_iff_iff];simp only[decide_eq_true_eq,Bool.or_eq_true];constructor
 ·rintro⟨j,hj,h | h⟩
  ·exact Or.inl ⟨j,hj,h⟩
  ·exact Or.inr ⟨j,hj,h⟩
 ·rintro (⟨j,hj,h⟩ | ⟨j,hj,h⟩)
  ·exact⟨j,hj,Or.inl h⟩
  ·exact⟨j,hj,Or.inr h⟩
lemma Z5w {m:ℕ} (Y:Finset (Fin m)) (c:Bool) (g:Fin m→ Bool) :
  decide (∃ j∈Y,(c && g j)= true)=(c && decide (∃ j∈Y,g j= true)):=by
 cases c <;> simp
lemma ex_and' {m:ℕ} (Y:Finset (Fin m)) (c:Bool) (g:Fin m→ Bool) :
  decide (∃ j∈Y,(g j && c)= true)=(decide (∃ j∈Y,g j= true) && c):=by
 cases c <;> simp
lemma Z5p {m:ℕ} (Y:Finset (Fin m)) (c bY b0:Bool) (bj:Fin m→ Bool)
  (h:bY=(b0 || decide (∃ j∈Y,bj j= true))) :
  (c && bY)=((c && b0) || decide (∃ j∈Y,(c && bj j)= true)):=by
 rw[Z5w,h];cases c <;> simp
lemma and_lin' {m:ℕ} (Y:Finset (Fin m)) (c bY b0:Bool) (bj:Fin m→ Bool)
  (h:bY=(b0 || decide (∃ j∈Y,bj j= true))) :
  (bY && c)=((b0 && c) || decide (∃ j∈Y,(bj j && c)= true)):=by
 rw[ex_and',h];cases c <;> simp
lemma Z5x {m:ℕ} (Y:Finset (Fin m)) (fY f0:ℕ→ Bool) (fj:Fin m→ ℕ→ Bool)
  (l:List ℕ)
  (h:∀ a∈l,fY a=(f0 a || decide (∃ j∈Y,fj j a= true))) :
  (l.map fY).any id =
   ((l.map f0).any id || decide (∃ j∈Y,(l.map (fj j)).any id= true)):=by
 induction l with
 | nil=>simp
 | cons a l ih=>
  simp only[List.map_cons,List.any_cons,id_eq];rw[ih (fun b hb=>h b (List.mem_cons_of_mem _ hb)),h a List.mem_cons_self,Z62]
  generalize decide (∃ j∈Y,fj j a= true)= p
  generalize decide (∃ j∈Y,(List.map (fj j) l).any id= true)= q
  cases f0 a <;> cases p <;> cases q <;> simp
lemma Z5y (n m:ℕ) (G:List Gate) (hm:Zr G) (hrb:RB (n+m) G) (hnc:NC n m G)
  (x:Fin n→ Bool) (Y:Finset (Fin m)) :
  ∀ i,val G (xy x (fun l=>decide (l∈Y))) i =
   (val G (xy x (fun _:Fin m=>false)) i ||
    decide (∃ j∈Y,val G (xy x (fun l=>decide (l= j))) i= true)):=by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
  by_cases h1:i< n
  ·simp only[Z35 _ _ _ _ h1]
   cases x ⟨i,h1⟩ <;> simp
  by_cases h2:i< n+m
  ·obtain⟨l,rfl⟩:∃ l:Fin m,i= n+(l:ℕ):=⟨⟨i-n,by omega⟩,by simp; omega⟩
   simp only[Z4n];simp
  by_cases h3:i< n+m+G.length
  ·obtain⟨j,rfl⟩:∃ j,i= n+m+j:=⟨i-(n+m),by omega⟩
   have hj:j< G.length:=by omega
   have e:∀ y:Fin m→ Bool,val G (xy x y) (n+m+j) =
     (G.getD j Z0).op.eval ((G.getD j Z0).inputs.map (val G (xy x y))):=
    fun y=>Z1v G x y j hrb hj
   simp only[e];have hr:=hrb j hj;have hc:=hnc j hj;obtain⟨ho,hlen⟩:=Z36 G hm j hj
   generalize G.getD j Z0= g at hr hc ho hlen ⊢
   rcases ho with ho | ho
   ·rcases Z3k _ hlen with h | ⟨a,h⟩ | ⟨a,b,h⟩
    ·simp[ho,h,GateOp.eval]
    ·simp only[ho,h,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
      List.all_nil,Bool.and_true,id_eq]
     exact ih a (hr a (by simp[h]))
    ·simp only[ho,h,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
      List.all_nil,Bool.and_true,id_eq]
     have ha:=hr a (by simp[h])
     have hb:=hr b (by simp[h])
     obtain⟨i,hi,hz⟩:=hc ho (by simp[h])
     rw[h] at hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl | rfl
     ·obtain⟨c,hc0⟩:∃ c,val G (xy x (fun _:Fin m=>false)) i= c:=⟨_,rfl⟩
      have hcY:val G (xy x (fun l=>decide (l∈Y))) i= c:=by
       rw[← hc0]; exact Z3l n m G hrb x _ _ i hz
      have hcj:∀ j:Fin m,val G (xy x (fun l=>decide (l= j))) i= c:=by
       intro j; rw[← hc0]; exact Z3l n m G hrb x _ _ i hz
      simp only[hc0,hcY,hcj];exact Z5p Y c _ _ _ (ih b hb)
     ·obtain⟨c,hc0⟩:∃ c,val G (xy x (fun _:Fin m=>false)) i= c:=⟨_,rfl⟩
      have hcY:val G (xy x (fun l=>decide (l∈Y))) i= c:=by
       rw[← hc0]; exact Z3l n m G hrb x _ _ i hz
      have hcj:∀ j:Fin m,val G (xy x (fun l=>decide (l= j))) i= c:=by
       intro j; rw[← hc0]; exact Z3l n m G hrb x _ _ i hz
      simp only[hc0,hcY,hcj];exact and_lin' Y c _ _ _ (ih a ha)
   ·simp only[ho,GateOp.eval]
    exact Z5x Y _ _ _ g.inputs (fun a ha=>ih a (hr a ha))
  ·have hv:∀ y:Fin m→ Bool,val G (xy x y) i= false:=
    fun y=>Z1e _ _ _ (by rw[Z2]; omega)
   simp only[hv];simp
def cnt (n m:ℕ) (G:List Gate):ℕ:=
 ((Dg G (d0 n m)).drop (n+m)).countP (fun a=>decide (0< a))
lemma Z2y (n m:ℕ) (G:List Gate) (g:Gate) :
  cnt n m (G++[g]) =
   cnt n m G+(if 0< dg n m (G++[g]) (n+m+G.length) then 1 else 0):=by
 rw[Z34];unfold cnt
 rw[Z2p,List.drop_append_of_le_length (by rw[Z16,Z17]; omega),
  List.countP_append]
 simp[List.countP_cons]
lemma Z2w (n m:ℕ) (G:List Gate) (g:Gate) :
  cnt n m (G++[g])≤ cnt n m G+1:=by
 rw[Z2y];split_ifs <;> omega
lemma Z3j (n m:ℕ) (G A:List Gate) :
  cnt n m (G++A)≤ cnt n m G+A.length:=by
 induction A using List.reverseRecOn with
 | nil=>simp
 | append_singleton A a ih=>
  rw[← List.append_assoc];have:=Z2w n m (G++A) a;simp only[List.length_append,List.length_singleton];omega
lemma Z1a (n m:ℕ) (G A:List Gate)
  (h:∀ k< A.length,dg n m (G++A) (n+m+G.length+k)=0) :
  cnt n m (G++A)= cnt n m G:=by
 induction A using List.reverseRecOn with
 | nil=>simp
 | append_singleton A a ih=>
  have h1:cnt n m (G++A)= cnt n m G:=by
   apply ih;intro k hk;have:=h k (by simp; omega)
   rw[← List.append_assoc,Z6 _ _ _ _ _ (by simp; omega)] at this
   exact this
  have h2:=h A.length (by simp)
  rw[← List.append_assoc] at h2 ⊢;rw[Z2y,h1];have e:n+m+(G++A).length= n+m+G.length+A.length:=by simp; omega
  rw[e,h2];simp
lemma Z2h (n m:ℕ) (G:List Gate) :
  Set.ncard {j:ℕ | j< G.length∧0< dg n m G (n+m+j)}≤ cnt n m G:=by
 induction G using List.reverseRecOn with
 | nil=>simp
 | append_singleton G g ih=>
  have hfin:Set.Finite {j:ℕ | j< G.length∧0< dg n m G (n+m+j)}:=
   (Set.finite_Iio G.length).subset (fun j hj=>hj.1)
  rw[Z2y];by_cases hpos:0< dg n m (G++[g]) (n+m+G.length)
  ·have hsub:{j:ℕ | j<(G++[g]).length∧0< dg n m (G++[g]) (n+m+j)} ⊆
     insert G.length {j:ℕ | j< G.length∧0< dg n m G (n+m+j)}:=by
    intro j hj;obtain⟨h1,h2⟩:=hj;by_cases hjl:j< G.length
    ·right
     rw[Z6 _ _ _ _ _ (by omega)] at h2
     exact⟨hjl,h2⟩
    ·left
     simp at h1
     show j= G.length
     omega
   have h1:=Set.ncard_le_ncard hsub (hfin.insert _);have h2:=Set.ncard_insert_le G.length {j:ℕ | j< G.length∧0< dg n m G (n+m+j)};simp only[hpos,ite_true];omega
  ·have hsub:{j:ℕ | j<(G++[g]).length∧0< dg n m (G++[g]) (n+m+j)} ⊆
     {j:ℕ | j< G.length∧0< dg n m G (n+m+j)}:=by
    intro j hj;obtain⟨h1,h2⟩:=hj;by_cases hjl:j< G.length
    ·rw[Z6 _ _ _ _ _ (by omega)] at h2
     exact⟨hjl,h2⟩
    ·simp at h1
     have:j= G.length:=by omega
     subst this;exact absurd h2 hpos
   have h1:=Set.ncard_le_ncard hsub hfin;simp only[hpos,ite_false];omega
lemma Z2i (N:ℕ) (G A:List Gate) (h:RB N G)
  (hA:∀ k< A.length,∀ i∈(A.getD k Z0).inputs,i< N+G.length+k) :
  RB N (G++A):=by
 intro j hj i hi;by_cases hlt:j< G.length
 ·rw[List.getD_append _ _ _ _ hlt] at hi
  exact h j hlt i hi
 ·obtain⟨k,rfl⟩:∃ k,j= G.length+k:=⟨j-G.length,by omega⟩
  rw[Zs] at hi;have:=hA k (by simp at hj; omega) i hi
  omega
lemma Z1z (G A:List Gate) (h:Zr G)
  (hA:∀ g∈A,g.op∈({GateOp.and,GateOp.or}:Set GateOp)∧g.inputs.length≤2) :
  Zr (G++A):=by
 intro g hg;rcases List.mem_append.mp hg with hg | hg
 ·exact h g hg
 ·exact hA g hg
lemma Z2j (n m:ℕ) (G A:List Gate) (hrb:RB (n+m) (G++A)) (h:NC n m G)
  (hA:∀ k< A.length,(A.getD k Z0).op= GateOp.and→(A.getD k Z0).inputs.length=2 →
   ∃ i∈(A.getD k Z0).inputs,dg n m (G++A) i=0) :
  NC n m (G++A):=by
 intro j hj ho hl;by_cases hlt:j< G.length
 ·have hr:=hrb j hj
  rw[List.getD_append _ _ _ _ hlt] at ho hl hr ⊢;obtain⟨i,hi,hz⟩:=h j hlt ho hl;refine⟨i,hi,?_⟩;rw[Z6 _ _ _ _ _ (by have:=hr i hi; omega)]
  exact hz
 ·obtain⟨k,rfl⟩:∃ k,j= G.length+k:=⟨j-G.length,by omega⟩
  rw[Zs] at ho hl ⊢;exact hA k (by simp at hj; omega) ho hl
lemma Z1h (g:Gate) (d:List ℕ) (h:∀ a∈g.inputs,d.getD a 0=0) :
  g.lineDegree d=0:=by
 have e:g.inputs.map (fun i=>d.getD i 0)= g.inputs.map (fun _=>0):=
  List.map_congr_left h
 have e2:∀ l:List ℕ,(l.map (fun _=>0)).foldr max 0=0:=by
  intro l
  induction l with
  | nil=>rfl
  | cons a l ih=>
   show max 0 (List.foldr max 0 (List.map (fun _=>0) l))=0
   rw[ih];rfl
 unfold Gate.lineDegree;rw[e];split_ifs
 ·simp
 ·exact e2 _
lemma Z37 (n m:ℕ) (G A:List Gate) (hm:Zr G) (hrb:RB (n+m) G)
  (hnc:NC n m G)
  (hA1:∀ g∈A,g.op∈({GateOp.and,GateOp.or}:Set GateOp)∧g.inputs.length≤2)
  (hA2:∀ k< A.length,∀ i∈(A.getD k Z0).inputs,i< n+m+G.length+k)
  (hA3:∀ k< A.length,dg n m (G++A) (n+m+G.length+k)=0) :
  Zr (G++A)∧RB (n+m) (G++A)∧NC n m (G++A)∧cnt n m (G++A)= cnt n m G:=by
 have hrb':=Z2i _ G A hrb hA2;refine⟨Z1z G A hm hA1,hrb',?_,Z1a n m G A hA3⟩;apply Z2j n m G A hrb' hnc;intro k hk ho hl;have hz:=hA3 k hk;have e:n+m+G.length+k= n+m+(G.length+k):=by omega
 rw[e,Z1n n m (G++A) (G.length+k) hrb' (by simp; omega),Zs] at hz
 have hall:=Z1w _ _ hz;rcases Z3k _ (le_of_eq hl) with h | ⟨a,h⟩ | ⟨a,b,h⟩
 ·rw[h] at hl; simp at hl
 ·rw[h] at hl; simp at hl
 ·exact⟨a,by rw[h]; exact List.mem_cons_self,hall a (by rw[h]; exact List.mem_cons_self)⟩
def qx (n m:ℕ) (i:ℕ):Bool:=decide (i< n∨n+m≤ i)
def zc (n m:ℕ) (g:Gate):Gate:=
 match g.op with
 | GateOp.or=>Gate.mk GateOp.or (g.inputs.filter (qx n m))
 | _=>if g.inputs.all (qx n m)= true then g else Gate.mk GateOp.or []
lemma Z4o (n m:ℕ) (g:Gate) (h:g.op= GateOp.or) :
  zc n m g= Gate.mk GateOp.or (g.inputs.filter (qx n m)):=by
 simp[zc,h]
lemma Z40 (n m:ℕ) (g:Gate) (h:g.op= GateOp.and) :
  zc n m g= if g.inputs.all (qx n m)= true then g else Gate.mk GateOp.or []:=by
 simp[zc,h]
lemma Z41 (C:List Gate) (f:Gate→ Gate) (j:ℕ) (hj:j< C.length) :
  (C.map f).getD j Z0= f (C.getD j Z0):=by
 rw[List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ hj]
 simp
lemma Z63 (n m:ℕ) (g:Gate) (ho:g.op= GateOp.and∨g.op= GateOp.or) :
  ∀ i∈(zc n m g).inputs,i∈g.inputs∧qx n m i= true:=by
 intro i hi;rcases ho with ho | ho
 ·rw[Z40 n m g ho] at hi
  split_ifs at hi with hall
  ·exact⟨hi,List.all_eq_true.mp hall i hi⟩
  ·simp at hi
 ·rw[Z4o n m g ho] at hi
  exact List.mem_filter.mp hi
lemma Z5q (n m:ℕ) (g:Gate) (ho:g.op= GateOp.and∨g.op= GateOp.or)
  (hl:g.inputs.length≤2) :
  ((zc n m g).op= GateOp.and∨(zc n m g).op= GateOp.or)∧(zc n m g).inputs.length≤2:=by
 rcases ho with ho | ho
 ·rw[Z40 n m g ho]
  split_ifs
  ·exact⟨Or.inl ho,hl⟩
  ·exact⟨Or.inr rfl,by simp⟩
 ·rw[Z4o n m g ho]
  exact⟨Or.inr rfl,le_trans (List.length_filter_le _ _) hl⟩
lemma Z5z (n m:ℕ) (C:List Gate) (hm:Zr C):Zr (C.map (zc n m)):=by
 intro g hg;obtain⟨g0,hg0,rfl⟩:=List.mem_map.mp hg;have h:=hm g0 hg0;have ho:g0.op= GateOp.and∨g0.op= GateOp.or:=by
  have h1:=h.1;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at h1;exact h1
 have:=Z5q n m g0 ho h.2;refine⟨?_,this.2⟩;simp only[Set.mem_insert_iff,Set.mem_singleton_iff];exact this.1
lemma Z5g (n m:ℕ) (C:List Gate) (hm:Zr C) (j:ℕ) (hj:j< C.length) :
  ∀ i∈((C.map (zc n m)).getD j Z0).inputs,
   i∈(C.getD j Z0).inputs∧(i< n∨n+m≤ i):=by
 intro i hi;rw[Z41 C _ j hj] at hi;have:=Z63 n m _ (Z36 C hm j hj).1 i hi;refine⟨this.1,?_⟩;have h2:=this.2;simp only[qx,decide_eq_true_eq] at h2;exact h2
lemma Z5h (n m:ℕ) (C:List Gate) (hm:Zr C) (hrb:RB (n+m) C) :
  RB (n+m) (C.map (zc n m)):=by
 intro j hj i hi;have hj':j< C.length:=by simpa using hj
 exact hrb j hj' i (Z5g n m C hm j hj' i hi).1
lemma Z_dg (n m:ℕ) (C:List Gate) (hm:Zr C) (hrb:RB (n+m) C) :
  ∀ i,(i< n∨n+m≤ i)→ dg n m (C.map (zc n m)) i=0:=by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
  intro hq;by_cases h1:i< n
  ·rw[Z1q _ _ _ _ (by omega)]
   simp; omega
  by_cases h3:i< n+m+C.length
  ·obtain⟨j,rfl⟩:∃ j,i= n+m+j:=⟨i-(n+m),by omega⟩
   have hj:j< C.length:=by omega
   rw[Z1n n m _ j (Z5h n m C hm hrb) (by simpa using hj)]
   apply Z1h;intro a ha;have:=Z5g n m C hm j hj a ha;have hlt:=hrb j hj a this.1;exact ih a (by omega) this.2
  ·exact Z5v _ _ _ _ (by simp; omega)
lemma Z42 {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (a:ℕ) (h1:n≤ a)
  (h2:a< n+m):val G (xy x (fun _:Fin m=>false)) a= false:=by
 have:=Z4n G x (fun _:Fin m=>false) ⟨a-n,by omega⟩
 have e:n+((⟨a-n,by omega⟩:Fin m):ℕ)= a:=by simp; omega
 rw[e] at this;exact this
lemma Z4p (l:List ℕ) (q:ℕ→ Bool) (f f':ℕ→ Bool)
  (h1:∀ a∈l,q a= true→ f a= f' a) (h2:∀ a∈l,q a= false→ f' a= false) :
  ((l.filter q).map f).any id=(l.map f').any id:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>
  have ih':=ih (fun b hb=>h1 b (List.mem_cons_of_mem _ hb))
   (fun b hb=>h2 b (List.mem_cons_of_mem _ hb))
  cases hq:q a
  ·rw[List.filter_cons_of_neg (by simp[hq]),ih']
   simp[h2 a List.mem_cons_self hq]
  ·rw[List.filter_cons_of_pos (by simp[hq])]
   simp only[List.map_cons,List.any_cons,id_eq];rw[ih',h1 a List.mem_cons_self hq]
lemma Z64 (n m:ℕ) (C:List Gate) (hm:Zr C) (hrb:RB (n+m) C)
  (x:Fin n→ Bool) (y:Fin m→ Bool) :
  ∀ i,(i< n∨n+m≤ i) →
   val (C.map (zc n m)) (xy x y) i= val C (xy x (fun _:Fin m=>false)) i:=by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
  intro hq;by_cases h1:i< n
  ·rw[Z35 _ _ _ _ h1,Z35 _ _ _ _ h1]
  by_cases h3:i< n+m+C.length
  ·obtain⟨j,rfl⟩:∃ j,i= n+m+j:=⟨i-(n+m),by omega⟩
   have hj:j< C.length:=by omega
   rw[Z1v _ x y j (Z5h n m C hm hrb) (by simpa using hj),Z1v C x _ j hrb hj,
    Z41 C _ j hj]
   have hr:=hrb j hj;obtain⟨ho,hlen⟩:=Z36 C hm j hj
   generalize C.getD j Z0= g at hr ho hlen ⊢
   rcases ho with ho | ho
   ·rw[Z40 n m g ho]
    split_ifs with hall
    ·congr 1
     apply List.map_congr_left;intro a ha;have hqa:=List.all_eq_true.mp hall a ha;simp only[qx,decide_eq_true_eq] at hqa;exact ih a (by have:=hr a ha; omega) hqa
    ·have hex:∃ a∈g.inputs,qx n m a= false:=by
      by_contra hcon
      apply hall;apply List.all_eq_true.mpr;intro a ha
      by_contra hna
      exact hcon ⟨a,ha,by simpa using hna⟩
     obtain⟨a,ha,hqa⟩:=hex;simp only[qx,decide_eq_false_iff_not,not_or,not_lt,not_le] at hqa;have hv:=Z42 C x a hqa.1 hqa.2;rw[ho];symm;simp only[GateOp.eval,List.map_nil,List.any_nil];apply List.all_eq_false.mpr;exact⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp[hv]⟩
   ·rw[Z4o n m g ho,ho]
    simp only[GateOp.eval];apply Z4p
    ·intro a ha hqa
     simp only[qx,decide_eq_true_eq] at hqa;exact ih a (by have:=hr a ha; omega) hqa
    ·intro a ha hqa
     simp only[qx,decide_eq_false_iff_not,not_or,not_lt,not_le] at hqa;exact Z42 C x a hqa.1 hqa.2
  ·rw[Z1e _ _ _ (by rw[Z2]; simp; omega),
    Z1e _ _ _ (by rw[Z2]; omega)]
def St (n m:ℕ) (G:List Gate):Prop:=Zr G∧RB (n+m) G∧NC n m G
lemma Z3b {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (y:Fin m→ Bool) (j a b:ℕ)
  (hrb:RB (n+m) G) (hj:j< G.length) (hg:G.getD j Z0= Gate.mk GateOp.or [a,b]) :
  val G (xy x y) (n+m+j)=(val G (xy x y) a || val G (xy x y) b):=by
 rw[Z1v G x y j hrb hj,hg];simp[GateOp.eval]
lemma Z27 {n m:ℕ} (G:List Gate) (x:Fin n→ Bool) (y:Fin m→ Bool) (j a b:ℕ)
  (hrb:RB (n+m) G) (hj:j< G.length) (hg:G.getD j Z0= Gate.mk GateOp.and [a,b]) :
  val G (xy x y) (n+m+j)=(val G (xy x y) a && val G (xy x y) b):=by
 rw[Z1v G x y j hrb hj,hg];simp[GateOp.eval]
lemma Z43 (n m:ℕ) (G:List Gate) (j a b:ℕ)
  (hrb:RB (n+m) G) (hj:j< G.length) (hg:G.getD j Z0= Gate.mk GateOp.or [a,b]) :
  dg n m G (n+m+j)= max (dg n m G a) (dg n m G b):=by
 rw[Z1n n m G j hrb hj,hg,Z1j _ _ rfl];simp[dg]
lemma Z3c (n m:ℕ) (G:List Gate) (j a b:ℕ)
  (hrb:RB (n+m) G) (hj:j< G.length) (hg:G.getD j Z0= Gate.mk GateOp.and [a,b]) :
  dg n m G (n+m+j)= dg n m G a+dg n m G b:=by
 rw[Z1n n m G j hrb hj,hg,Z1d _ _ rfl];simp[dg]
def Z1x (N len zu zv b c:ℕ):List Gate:=
 [Gate.mk GateOp.or [zu,b],Gate.mk GateOp.or [zv,c],
  Gate.mk GateOp.and [N+(len+0),N+(len+1)]]
def Z1y (N len yl e:ℕ):List Gate:=
 [Gate.mk GateOp.and [yl,N+(len+2)],Gate.mk GateOp.or [e,N+(len+3)]]
lemma Z5i (n m:ℕ) (G:List Gate) (hst:St n m G) (zu zv b c e:ℕ) (l:Fin m)
  (hzu:zu< n+m+G.length) (hzv:zv< n+m+G.length) (hb:b< n+m+G.length)
  (hc:c< n+m+G.length) (he:e< n+m+G.length)
  (dzu:dg n m G zu=0) (dzv:dg n m G zv=0) (db:dg n m G b=0)
  (dc:dg n m G c=0) (de:dg n m G e≤1) :
  St n m (G++(Z1x (n+m) G.length zu zv b c++Z1y (n+m) G.length (n+l) e)) ∧
  cnt n m (G++(Z1x (n+m) G.length zu zv b c++Z1y (n+m) G.length (n+l) e)) ≤
   cnt n m G+2 ∧
  dg n m (G++(Z1x (n+m) G.length zu zv b c++Z1y (n+m) G.length (n+l) e))
   (n+m+(G.length+4))≤1 ∧
  ∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val (G++(Z1x (n+m) G.length zu zv b c++Z1y (n+m) G.length (n+l) e))
    (xy x y) (n+m+(G.length+4)) =
   (val G (xy x y) e || (y l && ((val G (xy x y) zu || val G (xy x y) b) &&
    (val G (xy x y) zv || val G (xy x y) c)))):=by
 obtain⟨hm,hrb,hnc⟩:=hst;have hl:=l.isLt
 generalize hA1:Z1x (n+m) G.length zu zv b c= A1
 generalize hA2:Z1y (n+m) G.length (n+l) e= A2
 have hlen:(A1++A2).length=5:=by rw[← hA1,← hA2]; rfl
 have hrb':RB (n+m) (G++(A1++A2)):=by
  apply Z2i _ _ _ hrb;intro k hk i hi;rw[hlen] at hk;rw[← hA1,← hA2] at hi
  interval_cases k <;> simp[Z1x,Z1y] at hi <;> omega
 have g0:(G++(A1++A2)).getD (G.length+0) Z0= Gate.mk GateOp.or [zu,b]:=by
  rw[Zs,← hA1,← hA2]; rfl
 have g1:(G++(A1++A2)).getD (G.length+1) Z0= Gate.mk GateOp.or [zv,c]:=by
  rw[Zs,← hA1,← hA2]; rfl
 have g2:(G++(A1++A2)).getD (G.length+2) Z0 =
   Gate.mk GateOp.and [n+m+(G.length+0),n+m+(G.length+1)]:=by
  rw[Zs,← hA1,← hA2]; rfl
 have g3:(G++(A1++A2)).getD (G.length+3) Z0 =
   Gate.mk GateOp.and [n+l,n+m+(G.length+2)]:=by
  rw[Zs,← hA1,← hA2]; rfl
 have g4:(G++(A1++A2)).getD (G.length+4) Z0 =
   Gate.mk GateOp.or [e,n+m+(G.length+3)]:=by
  rw[Zs,← hA1,← hA2]; rfl
 have lt:∀ k<5,G.length+k<(G++(A1++A2)).length:=by
  intro k hk;rw[List.length_append,hlen];omega
 have p:∀ i,i< n+m+G.length→ dg n m (G++(A1++A2)) i= dg n m G i:=
  fun i hi=>Z6 n m G _ i hi
 have d_0:dg n m (G++(A1++A2)) (n+m+(G.length+0))=0:=by
  rw[Z43 n m _ _ zu b hrb' (lt 0 (by omega)) g0,p zu hzu,p b hb,dzu,db]
  rfl
 have d_1:dg n m (G++(A1++A2)) (n+m+(G.length+1))=0:=by
  rw[Z43 n m _ _ zv c hrb' (lt 1 (by omega)) g1,p zv hzv,p c hc,dzv,dc]
  rfl
 have d_2:dg n m (G++(A1++A2)) (n+m+(G.length+2))=0:=by
  rw[Z3c n m _ _ _ _ hrb' (lt 2 (by omega)) g2,d_0,d_1]
 have d_3:dg n m (G++(A1++A2)) (n+m+(G.length+3))=1:=by
  rw[Z3c n m _ _ _ _ hrb' (lt 3 (by omega)) g3,d_2,p _ (by omega),
   Z1q _ _ _ _ (by omega)]
  simp
 have d_4:dg n m (G++(A1++A2)) (n+m+(G.length+4))≤1:=by
  rw[Z43 n m _ _ _ _ hrb' (lt 4 (by omega)) g4,d_3,p e he]
  exact max_le de (le_refl 1)
 have hmono':Zr (G++(A1++A2)):=by
  apply Z1z G _ hm;intro g hg;rw[← hA1,← hA2] at hg
  simp only[Z1x,Z1y,List.cons_append,List.nil_append,List.mem_cons,
   List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
 have hnc':NC n m (G++(A1++A2)):=by
  apply Z2j n m G _ hrb' hnc;intro k hk ho hl2;rw[hlen] at hk;have h0:=g0;have h1:=g1;have h2:=g2;have h3:=g3;have h4:=g4;rw[Zs] at h0 h1 h2 h3 h4
  interval_cases k
  ·rw[h0] at ho; simp at ho
  ·rw[h1] at ho; simp at ho
  ·rw[h2]
   exact⟨n+m+(G.length+0),List.mem_cons_self,d_0⟩
  ·rw[h3]
   exact⟨n+m+(G.length+2),by simp,d_2⟩
  ·rw[h4] at ho; simp at ho
 have hA1len:A1.length=3:=by rw[← hA1]; rfl
 have hA2len:A2.length=2:=by rw[← hA2]; rfl
 have c1:cnt n m (G++A1)= cnt n m G:=by
  apply Z1a;intro k hk;rw[hA1len] at hk
  rw[← Z6 n m (G++A1) A2 _ (by rw[List.length_append,hA1len]; omega),
   List.append_assoc]
  interval_cases k
  ·exact d_0
  ·exact d_1
  ·exact d_2
 have c2:=Z3j n m (G++A1) A2;rw[List.append_assoc,hA2len,c1] at c2;refine⟨⟨hmono',hrb',hnc'⟩,c2,d_4,?_⟩;intro x y;have pv:∀ i,i< n+m+G.length →
   val (G++(A1++A2)) (xy x y) i= val G (xy x y) i:=
  fun i hi=>Zd G _ _ i (by rw[Z2]; exact hi)
 rw[Z3b _ x y _ _ _ hrb' (lt 4 (by omega)) g4,
  Z27 _ x y _ _ _ hrb' (lt 3 (by omega)) g3,
  Z27 _ x y _ _ _ hrb' (lt 2 (by omega)) g2,
  Z3b _ x y _ _ _ hrb' (lt 0 (by omega)) g0,
  Z3b _ x y _ _ _ hrb' (lt 1 (by omega)) g1,
  pv e he,pv zu hzu,pv b hb,pv zv hzv,pv c hc,Z4n]
lemma Z5r {m:ℕ} (P:Fin m→ Bool) (l:ℕ) (hl:l< m) :
  decide (∃ j:Fin m,(j:ℕ)< l+1∧P j= true) =
   (decide (∃ j:Fin m,(j:ℕ)< l∧P j= true) || P ⟨l,hl⟩):=by
 rw[Bool.eq_iff_iff];simp only[decide_eq_true_eq,Bool.or_eq_true];constructor
 ·rintro⟨j,hj,hp⟩
  by_cases h:(j:ℕ)< l
  ·exact Or.inl ⟨j,h,hp⟩
  ·right
   have:j=⟨l,hl⟩:=Fin.ext (by simp; omega)
   rw[← this];exact hp
 ·rintro (⟨j,hj,hp⟩ | hp)
  ·exact⟨j,by omega,hp⟩
  ·exact⟨⟨l,hl⟩,by simp,hp⟩
lemma Z5j (n m:ℕ) (G:List Gate) (hst:St n m G) (zu zv e0:ℕ) (b c:Fin m→ ℕ)
  (hzu:zu< n+m+G.length) (hzv:zv< n+m+G.length)
  (hb:∀ j,b j< n+m+G.length) (hc:∀ j,c j< n+m+G.length)
  (he:e0< n+m+G.length)
  (dzu:dg n m G zu=0) (dzv:dg n m G zv=0) (db:∀ j,dg n m G (b j)=0)
  (dc:∀ j,dg n m G (c j)=0) (de:dg n m G e0≤1) :
  ∀ l≤ m,∃ (H:List Gate) (e:ℕ),
   St n m (G++H)∧H.length=5*l∧cnt n m (G++H)≤ cnt n m G+2*l ∧
   e< n+m+(G++H).length∧dg n m (G++H) e≤1 ∧
   ∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
    val (G++H) (xy x y) e =
     (val G (xy x y) e0 || decide (∃ j:Fin m,(j:ℕ)< l ∧
      (y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
       (val G (xy x y) zv || val G (xy x y) (c j))))= true)):=by
 intro l
 induction l with
 | zero=>
  intro _;refine⟨[],e0,by simpa using hst,rfl,by simp,by simpa using he,by simpa using de,?_⟩
  intro x y;simp
 | succ l ih=>
  intro hl;obtain⟨H,e,hst',hlen,hcnt,he',hde,hval⟩:=ih (by omega)
  have hlt:l< m:=by omega
  have hGH:(G++H).length= G.length+H.length:=List.length_append;obtain⟨s1,s2,s3,s4⟩:=Z5i n m (G++H) hst' zu zv (b ⟨l,hlt⟩) (c ⟨l,hlt⟩) e
   ⟨l,hlt⟩ (by omega) (by omega) (by have:=hb ⟨l,hlt⟩; omega)
   (by have:=hc ⟨l,hlt⟩; omega) he'
   (by rw[Z6 _ _ _ _ _ hzu]; exact dzu) (by rw[Z6 _ _ _ _ _ hzv]; exact dzv)
   (by rw[Z6 _ _ _ _ _ (hb _)]; exact db _)
   (by rw[Z6 _ _ _ _ _ (hc _)]; exact dc _) hde
  refine⟨H++(Z1x (n+m) (G++H).length zu zv (b ⟨l,hlt⟩) (c ⟨l,hlt⟩) ++
   Z1y (n+m) (G++H).length (n+l) e),n+m+((G++H).length+4),?_,?_,?_,?_,?_,?_⟩
  ·rw[← List.append_assoc]; exact s1
  ·rw[List.length_append,hlen]
   show 5*l+5=5*(l+1)
   omega
  ·rw[← List.append_assoc]
   refine le_trans s2 ?_;omega
  ·rw[← List.append_assoc,List.length_append (as:=G++H)]
   show n+m+((G++H).length+4)< n+m+((G++H).length+5)
   omega
  ·rw[← List.append_assoc]; exact s3
  ·intro x y
   have pv:∀ i,i< n+m+G.length→ val (G++H) (xy x y) i= val G (xy x y) i:=
    fun i hi=>Zd G _ _ i (by rw[Z2]; exact hi)
   rw[← List.append_assoc,s4 x y,hval x y,pv zu hzu,pv zv hzv,pv _ (hb _),pv _ (hc _),
    Z5r (fun j:Fin m=>(y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
       (val G (xy x y) zv || val G (xy x y) (c j))))) l hlt,Bool.or_assoc]
lemma adj' (n m:ℕ) (hadj:∀ (G:List Gate) (r:ℕ),Z10 n m G r) (G:List Gate)
  (hst:St n m G) (r:ℕ) (hr:r< n+m+G.length) :
  ∃ (A:List Gate) (o:Fin m→ ℕ),St n m (G++A)∧cnt n m (G++A)= cnt n m G ∧
   A.length≤3*cnt n m G+m ∧
   (∀ j:Fin m,o j< n+m+(G++A).length∧dg n m (G++A) (o j)=0) ∧
   ∀ (x:Fin n→ Bool) (y:Fin m→ Bool) (j:Fin m),
    val G (xy x (fun l=>decide (l= j))) r =
     (val G (xy x (fun _:Fin m=>false)) r || val (G++A) (xy x y) (o j)):=by
 obtain⟨hm,hrb,hnc⟩:=hst;obtain⟨A,o,h1,h2,h3,h4,h5,h6⟩:=hadj G r hm hrb hnc hr;obtain⟨z1,z2,z3,z4⟩:=Z37 n m G A hm hrb hnc h1 h2 h4;have h3':A.length ≤
   3*Set.ncard {j:ℕ | j< G.length∧0< dg n m G (n+m+j)}+m:=h3
 have hle:=Z2h n m G;refine⟨A,o,⟨z1,z2,z3⟩,z4,by omega,?_,h6⟩
 intro j;have:=h5 j;refine⟨?_,this.2⟩;rw[List.length_append];omega
def Wok (n m:ℕ) (C G:List Gate) (w pw:ℕ):Prop:=
 pw< n+m+G.length∧dg n m G pw≤ dg n m C w ∧
 ∀ x:Fin n→ Bool,
  val G (xy x (fun _:Fin m=>false)) pw= val C (xy x (fun _:Fin m=>false)) w ∧
  ∀ j:Fin m,val G (xy x (fun l=>decide (l= j))) pw =
   val C (xy x (fun l=>decide (l= j))) w
lemma Z38 (n m:ℕ) (C G:List Gate) (w pw:ℕ) (h:Wok n m C G w pw)
  (B:List Gate):Wok n m C (G++B) w pw:=by
 obtain⟨h1,h2,h3⟩:=h
 refine⟨by rw[List.length_append]; omega,by rw[Z6 _ _ _ _ _ h1]; exact h2,
  fun x=>⟨?_,fun j => ?_⟩⟩
 ·rw[Zd _ _ _ _ (by rw[Z2]; exact h1)]; exact (h3 x).1
 ·rw[Zd _ _ _ _ (by rw[Z2]; exact h1)]; exact (h3 x).2 j
lemma Z4q (l:List ℕ) (f f':ℕ→ ℕ) (h:∀ a∈l,f a≤ f' a) :
  (l.map f).sum≤(l.map f').sum:=by
 induction l with
 | nil=>simp
 | cons a l ih=>
  have h1:=h a List.mem_cons_self;have h2:=ih (fun b hb=>h b (List.mem_cons_of_mem _ hb))
  simp only[List.map_cons,List.sum_cons];omega
lemma Z44 (l:List ℕ) (f f':ℕ→ ℕ) (h:∀ a∈l,f a≤ f' a) :
  (l.map f).foldr max 0≤(l.map f').foldr max 0:=by
 induction l with
 | nil=>simp
 | cons a l ih=>
  simp only[List.map_cons,List.foldr_cons];exact max_le_max (h a List.mem_cons_self) (ih (fun b hb=>h b (List.mem_cons_of_mem _ hb)))
def Inv (n m:ℕ) (C G:List Gate) (p:ℕ→ ℕ) (i κ:ℕ):Prop:=
 St n m G∧(∃ A,G= C.map (zc n m)++A)∧(∀ w< n+m+i,Wok n m C G w (p w)) ∧
 G.length≤ C.length+i+κ*(6*(i+κ*(2*m+1))+7*m+2) ∧
 cnt n m G≤ i+κ*(2*m+1)
lemma Z52 (n m:ℕ) (C G:List Gate) (p:ℕ→ ℕ) (i κ:ℕ) (hmC:Zr C)
  (hrbC:RB (n+m) C) (hi:i< C.length) (hinv:Inv n m C G p i κ)
  (hnx:(C.getD i Z0).op= GateOp.and→(C.getD i Z0).inputs.length=2 →
   ∃ a∈(C.getD i Z0).inputs,dg n m C a=0) :
  ∃ (G':List Gate) (p':ℕ→ ℕ),Inv n m C G' p' (i+1) κ:=by
 obtain⟨⟨hm,hrb,hnc⟩,⟨A,hA⟩,hw,hsz,hcn⟩:=hinv;have hr:=hrbC i hi;obtain⟨ho,hlen⟩:=Z36 C hmC i hi;have dC:=Z1n n m C i hrbC hi;have vC:∀ (x:Fin n→ Bool) (y:Fin m→ Bool),val C (xy x y) (n+m+i) =
   (C.getD i Z0).op.eval ((C.getD i Z0).inputs.map (val C (xy x y))):=
  fun x y=>Z1v C x y i hrbC hi
 generalize C.getD i Z0= g at hr ho hlen hnx dC vC
 have hin:∀ a∈g.inputs,Wok n m C G a (p a):=
  fun a ha=>hw a (by have:=hr a ha; omega)
 have hrb':RB (n+m) (G++[Gate.mk g.op (g.inputs.map p)]):=by
  apply Z2i _ _ _ hrb;intro k hk b hb;have hk0:k=0:=by simpa using hk
  subst hk0;simp only[List.getD_cons_zero,List.mem_map] at hb;obtain⟨a,ha,rfl⟩:=hb;have:=(hin a ha).1;omega
 have hm':Zr (G++[Gate.mk g.op (g.inputs.map p)]):=by
  apply Z1z G _ hm;intro q hq;have hq':q= Gate.mk g.op (g.inputs.map p):=by simpa using hq
  subst hq';refine⟨?_,by simpa using hlen⟩
  simp only[Set.mem_insert_iff,Set.mem_singleton_iff];exact ho
 have hnc':NC n m (G++[Gate.mk g.op (g.inputs.map p)]):=by
  apply Z2j n m G _ hrb' hnc;intro k hk ho' hl';have hk0:k=0:=by simpa using hk
  subst hk0;simp only[List.getD_cons_zero,List.length_map] at ho' hl' ⊢;obtain⟨a,ha,hz⟩:=hnx ho' hl';refine⟨p a,List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩;rw[Z6 _ _ _ _ _ (hin a ha).1];have:=(hin a ha).2.1;omega
 have hnew:Wok n m C (G++[Gate.mk g.op (g.inputs.map p)]) (n+m+i)
   (n+m+G.length):=by
  refine⟨by simp,?_,fun x=>⟨?_,fun j => ?_⟩⟩
  ·rw[Z34,dC]
   rcases ho with ho | ho
   ·rw[Z1d g _ ho,Z1d (Gate.mk g.op (g.inputs.map p)) _ ho]
    show ((g.inputs.map p).map _).sum≤_
    rw[List.map_map];apply Z4q;intro a ha;exact (hin a ha).2.1
   ·rw[Z1j g _ ho,Z1j (Gate.mk g.op (g.inputs.map p)) _ ho]
    show ((g.inputs.map p).map _).foldr max 0≤_
    rw[List.map_map];apply Z44;intro a ha;exact (hin a ha).2.1
  ·have e:=Z2o G (Gate.mk g.op (g.inputs.map p)) (xy x (fun _:Fin m=>false))
   rw[Z2] at e;rw[e,vC]
   show g.op.eval ((g.inputs.map p).map _)=_
   rw[List.map_map]
   congr 1
   apply List.map_congr_left;intro a ha;exact ((hin a ha).2.2 x).1
  ·have e:=Z2o G (Gate.mk g.op (g.inputs.map p)) (xy x (fun l=>decide (l= j)))
   rw[Z2] at e;rw[e,vC]
   show g.op.eval ((g.inputs.map p).map _)=_
   rw[List.map_map]
   congr 1
   apply List.map_congr_left;intro a ha;exact ((hin a ha).2.2 x).2 j
 refine⟨G++[Gate.mk g.op (g.inputs.map p)],
  fun w=>if w= n+m+i then n+m+G.length else p w,
  ⟨hm',hrb',hnc'⟩,⟨A++[Gate.mk g.op (g.inputs.map p)],by rw[hA,List.append_assoc]⟩,
  ?_,?_,?_⟩
 ·intro w hw'
  by_cases hwe:w= n+m+i
  ·subst hwe
   simp only[↓reduceIte];exact hnew
  ·simp only[hwe,↓reduceIte]
   exact Z38 n m C G w _ (hw w (by omega)) _
 ·simp only[List.length_append,List.length_singleton]
  have:κ*(6*(i+κ*(2*m+1))+7*m+2) ≤
    κ*(6*(i+1+κ*(2*m+1))+7*m+2):=
   Nat.mul_le_mul_left _ (by omega)
  omega
 ·have:=Z2w n m G (Gate.mk g.op (g.inputs.map p))
  omega
lemma add_zero (n m:ℕ) (G:List Gate) (hst:St n m G) (g:Gate)
  (hop:g.op= GateOp.and∨g.op= GateOp.or) (hlen:g.inputs.length≤2)
  (hin:∀ a∈g.inputs,a< n+m+G.length∧dg n m G a=0) :
  St n m (G++[g])∧cnt n m (G++[g])= cnt n m G ∧
   dg n m (G++[g]) (n+m+G.length)=0 ∧
   ∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
    val (G++[g]) (xy x y) (n+m+G.length)= g.op.eval (g.inputs.map (val G (xy x y))):=by
 obtain⟨hm,hrb,hnc⟩:=hst;have hd:dg n m (G++[g]) (n+m+G.length)=0:=by
  rw[Z34];exact Z1h _ _ (fun a ha=>(hin a ha).2)
 obtain⟨z1,z2,z3,z4⟩:=Z37 n m G [g] hm hrb hnc
  (by
   intro q hq;have hq':q= g:=by simpa using hq
   subst hq';refine⟨?_,hlen⟩;simp only[Set.mem_insert_iff,Set.mem_singleton_iff]
   exact hop)
  (by
   intro k hk a ha;have hk0:k=0:=by simpa using hk
   subst hk0;simp only[List.getD_cons_zero] at ha;have:=(hin a ha).1
   omega)
  (by
   intro k hk;have hk0:k=0:=by simpa using hk
   subst hk0
   exact hd)
 refine⟨⟨z1,z2,z3⟩,z4,hd,?_⟩;intro x y;have e:=Z2o G g (xy x y);rw[Z2] at e;exact e
lemma zf (n m:ℕ) (C G3:List Gate) (hmC:Zr C) (hrbC:RB (n+m) C) (B:List Gate)
  (hG3:G3= C.map (zc n m)++B) (Fw:ℕ) (hF1:Fw< n+m+G3.length)
  (hF2:dg n m G3 Fw=0) (hF3:∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val G3 (xy x y) Fw= false) (u:ℕ) (hu:u< n+m+C.length) :
  (if n≤ u∧u< n+m then Fw else u)< n+m+G3.length ∧
  dg n m G3 (if n≤ u∧u< n+m then Fw else u)=0 ∧
  ∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val G3 (xy x y) (if n≤ u∧u< n+m then Fw else u) =
    val C (xy x (fun _:Fin m=>false)) u:=by
 split_ifs with h
 ·exact⟨hF1,hF2,fun x y=>by rw[hF3,Z42 C x u h.1 h.2]⟩
 ·have hq:u< n∨n+m≤ u:=by omega
  subst hG3;refine⟨by simp; omega,?_,fun x y => ?_⟩
  ·rw[Z6 _ _ _ _ _ (by simp; omega)]
   exact Z_dg n m C hmC hrbC u hq
  ·rw[Zd _ _ _ _ (by rw[Z2]; simp; omega)]
   exact Z64 n m C hmC hrbC x y u hq
lemma Z53 {m:ℕ} (P:Fin m→ Bool) (l:Fin m) :
  decide (∃ j:Fin m,(decide (j= l) && P j)= true)= P l:=by
 rw[Bool.eq_iff_iff];simp
lemma Z4r (n m:ℕ) (hadj:∀ (G:List Gate) (r:ℕ),Z10 n m G r)
  (C G:List Gate) (p:ℕ→ ℕ) (i κ:ℕ) (hmC:Zr C)
  (hrbC:RB (n+m) C) (hi:i< C.length) (hinv:Inv n m C G p i κ) (u v:ℕ)
  (hg:C.getD i Z0= Gate.mk GateOp.and [u,v]) (hu:0< dg n m C u)
  (hv:0< dg n m C v) :
  ∃ (G':List Gate) (p':ℕ→ ℕ),Inv n m C G' p' (i+1) (κ+1):=by
 obtain⟨hst,⟨A,hA⟩,hw,hsz,hcn⟩:=hinv;have hr:=hrbC i hi;rw[hg] at hr;have hul:u< n+m+i:=hr u (by simp)
 have hvl:v< n+m+i:=hr v (by simp)
 have wu:=hw u hul;have wv:=hw v hvl;have hold:∀ (H:List Gate),∀ w< n+m+i,
   Wok n m C (G++H) w (p w):=fun H w hlt=>Z38 n m C G w _ (hw w hlt) H
 obtain⟨A1,o1,st1,c1,len1,ho1,eq1⟩:=adj' n m hadj G hst (p u) wu.1;have l1:(G++A1).length= G.length+A1.length:=List.length_append;have pv1:∀ (X:List Bool) (a:ℕ),X.length= n+m→ a< n+m+G.length →
   val (G++A1) X a= val G X a:=
  fun X a hX ha=>Zd G A1 X a (by rw[hX]; exact ha)
 have hG1:∃ B1,G++A1= G++B1:=⟨A1,rfl⟩
 generalize G++A1= G1 at st1 c1 ho1 eq1 l1 pv1 hG1
 obtain⟨A2,o2,st2,c2,len2,ho2,eq2⟩:=
  adj' n m hadj G1 st1 (p v) (by have:=wv.1; omega)
 have l2:(G1++A2).length= G1.length+A2.length:=List.length_append;have pv2:∀ (X:List Bool) (a:ℕ),X.length= n+m→ a< n+m+G1.length →
   val (G1++A2) X a= val G1 X a:=
  fun X a hX ha=>Zd G1 A2 X a (by rw[hX]; exact ha)
 have pd2:∀ a,a< n+m+G1.length→ dg n m (G1++A2) a= dg n m G1 a:=
  fun a ha=>Z6 n m G1 A2 a ha
 have hG2:∃ B2,G1++A2= G++B2:=by
  obtain⟨B1,hB1⟩:=hG1;exact⟨B1++A2,by rw[hB1,List.append_assoc]⟩
 generalize G1++A2= G2 at st2 c2 ho2 eq2 l2 pv2 pd2 hG2
 obtain⟨st3,c3,d3,v3⟩:=add_zero n m G2 st2 (Gate.mk GateOp.or []) (Or.inr rfl)
  (by simp) (by intro a ha; cases ha)
 have l3:(G2++[Gate.mk GateOp.or []]).length= G2.length+1:=by simp
 have pv3:∀ (X:List Bool) (a:ℕ),X.length= n+m→ a< n+m+G2.length →
   val (G2++[Gate.mk GateOp.or []]) X a= val G2 X a:=
  fun X a hX ha=>Zd G2 _ X a (by rw[hX]; exact ha)
 have pd3:∀ a,a< n+m+G2.length →
   dg n m (G2++[Gate.mk GateOp.or []]) a= dg n m G2 a:=
  fun a ha=>Z6 n m G2 _ a ha
 have hG3:∃ B3,G2++[Gate.mk GateOp.or []]= G++B3:=by
  obtain⟨B2,hB2⟩:=hG2;exact⟨B2++[Gate.mk GateOp.or []],by rw[hB2,List.append_assoc]⟩
 have v3':∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val (G2++[Gate.mk GateOp.or []]) (xy x y) (n+m+G2.length)= false:=by
  intro x y;rw[v3];simp[GateOp.eval]
 generalize G2++[Gate.mk GateOp.or []]= G3 at st3 c3 d3 l3 pv3 pd3 hG3 v3'
 have hG3Z:∃ B,G3= C.map (zc n m)++B:=by
  obtain⟨B3,hB3⟩:=hG3;exact⟨A++B3,by rw[hB3,hA,List.append_assoc]⟩
 obtain⟨BZ,hBZ⟩:=hG3Z;obtain⟨zu1,zu2,zu3⟩:=zf n m C G3 hmC hrbC BZ hBZ (n+m+G2.length) (by omega) d3 v3'
  u (by omega)
 obtain⟨zv1,zv2,zv3⟩:=zf n m C G3 hmC hrbC BZ hBZ (n+m+G2.length) (by omega) d3 v3'
  v (by omega)
 generalize (if n≤ u∧u< n+m then n+m+G2.length else u)= zu at zu1 zu2 zu3
 generalize (if n≤ v∧v< n+m then n+m+G2.length else v)= zv at zv1 zv2 zv3
 obtain⟨st4,c4,d4,v4⟩:=add_zero n m G3 st3 (Gate.mk GateOp.and [zu,zv]) (Or.inl rfl)
  (by simp) (by
   intro a ha;simp only[List.mem_cons,List.not_mem_nil,or_false] at ha;rcases ha with rfl | rfl
   ·exact⟨zu1,zu2⟩
   ·exact⟨zv1,zv2⟩)
 have l4:(G3++[Gate.mk GateOp.and [zu,zv]]).length= G3.length+1:=by simp
 have pv4:∀ (X:List Bool) (a:ℕ),X.length= n+m→ a< n+m+G3.length →
   val (G3++[Gate.mk GateOp.and [zu,zv]]) X a= val G3 X a:=
  fun X a hX ha=>Zd G3 _ X a (by rw[hX]; exact ha)
 have pd4:∀ a,a< n+m+G3.length →
   dg n m (G3++[Gate.mk GateOp.and [zu,zv]]) a= dg n m G3 a:=
  fun a ha=>Z6 n m G3 _ a ha
 have hG4:∃ B4,G3++[Gate.mk GateOp.and [zu,zv]]= G++B4:=by
  obtain⟨B3,hB3⟩:=hG3;exact⟨B3++[Gate.mk GateOp.and [zu,zv]],by rw[hB3,List.append_assoc]⟩
 have v4':∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val (G3++[Gate.mk GateOp.and [zu,zv]]) (xy x y) (n+m+G3.length) =
    (val C (xy x (fun _:Fin m=>false)) u && val C (xy x (fun _:Fin m=>false)) v):=by
  intro x y;rw[v4];simp[GateOp.eval,zu3,zv3]
 generalize G3++[Gate.mk GateOp.and [zu,zv]]= G4 at st4 c4 d4 l4 pv4 pd4 hG4 v4'
 have hzu4:∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val G4 (xy x y) zu= val C (xy x (fun _:Fin m=>false)) u:=by
  intro x y;rw[pv4 _ _ (Z2 x y) zu1,zu3]
 have hzv4:∀ (x:Fin n→ Bool) (y:Fin m→ Bool),
   val G4 (xy x y) zv= val C (xy x (fun _:Fin m=>false)) v:=by
  intro x y;rw[pv4 _ _ (Z2 x y) zv1,zv3]
 have hU:∀ (x:Fin n→ Bool) (y:Fin m→ Bool) (j:Fin m),
   (val C (xy x (fun _:Fin m=>false)) u || val G4 (xy x y) (o1 j)) =
    val C (xy x (fun l=>decide (l= j))) u:=by
  intro x y j;have hb:=(ho1 j).1
  rw[pv4 _ _ (Z2 x y) (by omega),pv3 _ _ (Z2 x y) (by omega),
   pv2 _ _ (Z2 x y) hb,← (wu.2.2 x).1,← (wu.2.2 x).2 j]
  exact (eq1 x y j).symm
 have hV:∀ (x:Fin n→ Bool) (y:Fin m→ Bool) (j:Fin m),
   (val C (xy x (fun _:Fin m=>false)) v || val G4 (xy x y) (o2 j)) =
    val C (xy x (fun l=>decide (l= j))) v:=by
  intro x y j;have hb:=(ho2 j).1;have e2:=eq2 x y j
  rw[pv1 _ _ (Z2 x _) wv.1,pv1 _ _ (Z2 x _) wv.1,(wv.2.2 x).1,
   (wv.2.2 x).2 j] at e2
  rw[pv4 _ _ (Z2 x y) (by omega),pv3 _ _ (Z2 x y) hb]
  exact e2.symm
 obtain⟨H,e,st5,lenH,c5,he,hde,hval⟩:=Z5j n m G4 st4 zu zv (n+m+G3.length)
  o1 o2 (by omega) (by omega) (fun j=>by have:=(ho1 j).1; omega)
  (fun j=>by have:=(ho2 j).1; omega) (by omega)
  (by rw[pd4 _ zu1]; exact zu2) (by rw[pd4 _ zv1]; exact zv2)
  (fun j=>by
   have hb:=(ho1 j).1;rw[pd4 _ (by omega),pd3 _ (by omega),pd2 _ hb]
   exact (ho1 j).2)
  (fun j=>by
   have hb:=(ho2 j).1;rw[pd4 _ (by omega),pd3 _ hb]
   exact (ho2 j).2)
  (by omega) m (le_refl m)
 have key:∀ (x:Fin n→ Bool) (y:Fin m→ Bool),val (G4++H) (xy x y) e =
   ((val C (xy x (fun _:Fin m=>false)) u && val C (xy x (fun _:Fin m=>false)) v) ||
    decide (∃ j:Fin m,(y j && (val C (xy x (fun l=>decide (l= j))) u &&
     val C (xy x (fun l=>decide (l= j))) v))= true)):=by
  intro x y;rw[hval x y,v4'];simp only[hzu4,hzv4,hU,hV,Fin.is_lt,true_and]
 have dCi:=Z3c n m C i u v hrbC hi hg;have hnew:Wok n m C (G4++H) (n+m+i) e:=by
  refine⟨he,by omega,fun x=>⟨?_,fun l => ?_⟩⟩
  ·rw[key,Z27 C x _ i u v hrbC hi hg]
   simp
  ·rw[key,Z27 C x _ i u v hrbC hi hg,Z53]
   have h1:=hU x (fun _=>false) l
   have h2:=hV x (fun _=>false) l
   rw[← h1,← h2]
   generalize val C (xy x (fun _:Fin m=>false)) u= a
   generalize val C (xy x (fun _:Fin m=>false)) v= b
   generalize val G4 (xy x (fun _:Fin m=>false)) (o1 l)= c
   generalize val G4 (xy x (fun _:Fin m=>false)) (o2 l)= d
   cases a <;> cases b <;> cases c <;> cases d <;> rfl
 obtain⟨B4,hB4⟩:=hG4;have e1:(κ+1)*(2*m+1)= κ*(2*m+1)+(2*m+1):=by ring
 refine⟨G4++H,fun w=>if w= n+m+i then e else p w,st5,
  ⟨A++B4++H,by rw[hB4,hA]; simp[List.append_assoc]⟩,?_,?_,?_⟩
 ·intro w hw'
  by_cases hwe:w= n+m+i
  ·subst hwe
   simp only[↓reduceIte];exact hnew
  ·simp only[hwe,↓reduceIte]
   rw[hB4,List.append_assoc];exact hold _ w (by omega)
 ·rw[List.length_append,lenH]
  have e3:κ*(6*(i+κ*(2*m+1))+7*m+2) ≤
    κ*(6*(i+1+(κ*(2*m+1)+(2*m+1)))+7*m+2):=
   Nat.mul_le_mul_left _ (by omega)
  have e2:(κ+1)*(6*(i+1+(κ*(2*m+1)+(2*m+1)))+7*m+2) =
    κ*(6*(i+1+(κ*(2*m+1)+(2*m+1)))+7*m+2) +
     (6*(i+1+(κ*(2*m+1)+(2*m+1)))+7*m+2):=by ring
  rw[e1,e2];omega
 ·rw[e1]
  omega
def Z1s (n m:ℕ) (C:List Gate) (j:ℕ):Bool:=
 match (C.getD j Z0).op,(C.getD j Z0).inputs with
 | GateOp.and,[a,b]=>decide (0< dg n m C a) && decide (0< dg n m C b)
 | _,_=>false
lemma Z2x (n m:ℕ) (C:List Gate) (j:ℕ) (h:Z1s n m C j= true) :
  ∃ u v,C.getD j Z0= Gate.mk GateOp.and [u,v]∧0< dg n m C u∧0< dg n m C v:=by
 unfold Z1s at h
 split at h
 ·rename_i a b h1 h2
  simp only[Bool.and_eq_true,decide_eq_true_eq] at h;refine⟨a,b,?_,h.1,h.2⟩;cases hgd:C.getD j Z0 with
  | mk op inp=>
   rw[hgd] at h1 h2;simp only at h1 h2;rw[h1,h2]
 ·simp at h
lemma Z45 (n m:ℕ) (C:List Gate) (j:ℕ) (h:Z1s n m C j= false)
  (ho:(C.getD j Z0).op= GateOp.and) (hl:(C.getD j Z0).inputs.length=2) :
  ∃ a∈(C.getD j Z0).inputs,dg n m C a=0:=by
 rcases Z3k _ (le_of_eq hl) with hs | ⟨a,hs⟩ | ⟨a,b,hs⟩
 ·rw[hs] at hl; simp at hl
 ·rw[hs] at hl; simp at hl
 ·unfold Z1s at h
  rw[ho,hs] at h;simp only[Bool.and_eq_false_iff,decide_eq_false_iff_not,not_lt,Nat.le_zero] at h;rw[hs];rcases h with h | h
  ·exact⟨a,by simp,h⟩
  ·exact⟨b,by simp,h⟩
def kap (n m:ℕ) (C:List Gate) (i:ℕ):ℕ:=
 ((Finset.range i).filter (fun j=>Z1s n m C j= true)).card
lemma Z5k (n m:ℕ) (C:List Gate) (i:ℕ) :
  kap n m C (i+1)= kap n m C i+(if Z1s n m C i= true then 1 else 0):=by
 unfold kap;rw[Finset.range_add_one,Finset.filter_insert];split_ifs with h
 ·rw[Finset.card_insert_of_notMem (by simp)]
 ·rfl
lemma Z60 (n m:ℕ) (C:List Gate) :
  kap n m C C.length≤ Set.ncard {j:ℕ | j< C.length ∧
   (C.getD j Z0).op= GateOp.and∧(C.getD j Z0).inputs.length=2 ∧
   ∀ i∈(C.getD j Z0).inputs,0< dg n m C i}:=by
 unfold kap;rw[← Set.ncard_coe_finset];apply Set.ncard_le_ncard
 ·intro j hj
  simp only[Finset.coe_filter,Finset.mem_range,Set.mem_ofPred_eq] at hj;obtain⟨u,v,hg,hu,hv⟩:=Z2x n m C j hj.2;refine⟨hj.1,?_,?_,?_⟩
  ·rw[hg]
  ·rw[hg]; rfl
  ·rw[hg]
   intro i hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl | rfl
   ·exact hu
   ·exact hv
 ·exact (Set.finite_Iio C.length).subset (fun j hj=>hj.1)
lemma Z5s (n m:ℕ):cnt n m []=0:=by
 unfold cnt;rw[List.drop_eq_nil_of_le (by rw[Z16,Z17]; simp)]
 rfl
lemma Z5l (n m:ℕ) (hadj:∀ (G:List Gate) (r:ℕ),Z10 n m G r)
  (C:List Gate) (hmC:Zr C) (hrbC:RB (n+m) C) :
  ∀ i≤ C.length,∃ (G:List Gate) (p:ℕ→ ℕ),Inv n m C G p i (kap n m C i):=by
 intro i
 induction i with
 | zero=>
  intro _;have hZrb:=Z5h n m C hmC hrbC;have hZd:=Z_dg n m C hmC hrbC;refine⟨C.map (zc n m),fun w=>w,⟨Z5z n m C hmC,hZrb,?_⟩,⟨[],by simp⟩,?_,?_,?_⟩
  ·intro j hj ho hl
   have hj':j< C.length:=by simpa using hj
   rcases Z3k _ (le_of_eq hl) with hs | ⟨a,hs⟩ | ⟨a,b,hs⟩
   ·rw[hs] at hl; simp at hl
   ·rw[hs] at hl; simp at hl
   ·have hin:=Z5g n m C hmC j hj' a (by rw[hs]; exact List.mem_cons_self)
    exact⟨a,by rw[hs]; exact List.mem_cons_self,hZd a hin.2⟩
  ·intro w hw
   refine⟨by show w<_; omega,?_,fun x=>⟨?_,fun j => ?_⟩⟩
   ·rw[Z1q _ _ _ _ (by omega),Z1q _ _ _ _ (by omega)]
   ·rw[Z15 _ _ _ (by rw[Z2]; omega),Z15 _ _ _ (by rw[Z2]; omega)]
   ·rw[Z15 _ _ _ (by rw[Z2]; omega),Z15 _ _ _ (by rw[Z2]; omega)]
  ·simp
  ·have h0:=Z1a n m [] (C.map (zc n m)) (by
    intro k hk
    exact hZd _ (by simp))
   simp only[List.nil_append] at h0;rw[h0,Z5s];omega
 | succ i ih=>
  intro hi;obtain⟨G,p,hinv⟩:=ih (by omega)
  rw[Z5k];cases hc:Z1s n m C i
  ·simp only[Bool.false_eq_true,↓reduceIte,Nat.add_zero]
   exact Z52 n m C G p i _ hmC hrbC (by omega) hinv (Z45 n m C i hc)
  ·simp only[↓reduceIte]
   obtain⟨u,v,hg,hu,hv⟩:=Z2x n m C i hc;exact Z4r n m hadj C G p i _ hmC hrbC (by omega) hinv u v hg hu hv
lemma main (hadj:∀ (n m:ℕ) (G:List Gate) (r:ℕ),Z10 n m G r) :
  (∀ (n m s k:ℕ) (C:Circuit),Monotone2 C→ ReadsBack (n+m) C→ C.size≤ s→ Set.ncard {j:ℕ | j< C.gates.length∧(gateAt C j).op= GateOp.and∧(gateAt C j).inputs.length=2∧∀ i∈(gateAt C j).inputs,0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0}≤ k→∃ M:Circuit,Monotone2 M∧ReadsBack (n+m) M∧(∀ j< M.gates.length,(gateAt M j).op= GateOp.and→(gateAt M j).inputs.length=2→∃ i∈(gateAt M j).inputs,(M.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0=0)∧M.size≤(6*k+3)*s+12*k^2*m+7*k*m+6*k^2+2*k∧Set.ncard {j:ℕ | j< M.gates.length∧0<(M.lineDegrees (n+m) (Finset.Ico n (n+m))).getD (n+m+j) 0}≤ s+k*(2*m+1)∧∀ (x:Fin n→ Bool) (Y:Finset (Fin m)),circuitFun (n+m) M (Fin.append x (fun l=>decide (l∈Y)))=(circuitFun (n+m) C (Fin.append x (fun _=>false)) || decide (∃ j∈Y,circuitFun (n+m) C (Fin.append x (fun l=>decide (l= j)))= true))):=by
 intro n m s k C hM hR hs hk;obtain⟨G,p,hinv⟩:=Z5l n m (hadj n m) C.gates hM hR C.gates.length le_rfl;obtain⟨⟨hm,hrb,hnc⟩,_,hw,hsz,hcn⟩:=hinv;have hκ:kap n m C.gates C.gates.length≤ k:=le_trans (Z60 n m C.gates) hk
 generalize kap n m C.gates C.gates.length= κ at hsz hcn hκ
 have hs':C.gates.length≤ s:=hs
 refine⟨Circuit.mk G (if C.output< n+m+C.gates.length then p C.output
  else n+m+G.length),hm,hrb,hnc,?_,?_,?_⟩
 ·show G.length≤_
  have h1:κ*(6*(C.gates.length+κ*(2*m+1))+7*m+2) ≤
    k*(6*(s+k*(2*m+1))+7*m+2):=
   Nat.mul_le_mul hκ (by have:=Nat.mul_le_mul_right (2*m+1) hκ; omega)
  have h2:k*(6*(s+k*(2*m+1))+7*m+2)+3*s =
    (6*k+3)*s+12*k^2*m+7*k*m+6*k^2+2*k:=by ring
  omega
 ·have h1:=Z2h n m G
  have h2:=Nat.mul_le_mul_right (2*m+1) hκ;exact le_trans h1 (by omega)
 ·intro x Y
  show val G (xy x (fun l=>decide (l∈Y))) _ =
   (val C.gates (xy x (fun _:Fin m=>false)) C.output ||
    decide (∃ j∈Y,val C.gates (xy x (fun l=>decide (l= j))) C.output= true))
  rw[Z5y n m G hm hrb hnc x Y];split_ifs with h
  ·have hwo:=(hw _ h).2.2 x
   simp only[hwo.1,hwo.2]
  ·have e1:∀ y:Fin m→ Bool,val G (xy x y) (n+m+G.length)= false:=
    fun y=>Z1e _ _ _ (by rw[Z2])
   have e2:∀ y:Fin m→ Bool,val C.gates (xy x y) C.output= false:=
    fun y=>Z1e _ _ _ (by rw[Z2]; omega)
   simp only[e1,e2]
end PEqualNP.Outside.L_meta_1690.P1623
namespace PEqualNP.Outside.L_meta_1690.P1624
open PEqualNP.CircuitLowerBounds
def run (gs:List Gate) (x:List Bool):List Bool:=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
lemma Z2z (g:Gate) (gs:List Gate) (x:List Bool) :
  run (g::gs) x= run gs (x++[g.op.eval (g.inputs.map fun i=>x.getD i false)]):=
 rfl
lemma Zb (gs:List Gate) (x:List Bool) :
  (run gs x).length= x.length+gs.length:=by
 induction gs generalizing x with
 | nil=>simp[run]
 | cons g gs ih=>rw[Z2z,ih]; simp; omega
lemma Z30 (gs:List Gate) (x:List Bool) (w:ℕ) (hw:w< x.length) :
  (run gs x).getD w false= x.getD w false:=by
 induction gs generalizing x with
 | nil=>rfl
 | cons g gs ih=>
  rw[Z2z,ih _ (by simp; omega),List.getD_append _ _ _ _ hw]
lemma Z54 (gs:List Gate) (x:List Bool) (j:ℕ) :
  run gs x= run (gs.drop j) (run (gs.take j) x):=by
 simpa only[run,List.foldl_append] using
  congrArg (fun l:List Gate=>run l x) (List.take_append_drop j gs).symm
def Za {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ):Bool:=
 (C.wires (List.ofFn x)).getD w false
lemma Z20 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (p:Fin n) :
  Za C x p= x p:=by
 change (run C.gates (List.ofFn x)).getD p false= x p
 have hp:(p:ℕ)<(List.ofFn x).length:=by simp
 rw[Z30 _ _ _ hp,List.getD_eq_getElem _ _ hp];simp
lemma Z29 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ)
  (hw:n+C.size≤ w):Za C x w= false:=by
 change (run C.gates (List.ofFn x)).getD w false= false
 exact List.getD_eq_default _ _ (by simpa[Zb,Circuit.size] using hw)
lemma Z1m {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ)
  (hn:n≤ w) (hw:w< n+C.size) :
  let g:=C.gates[w-n]'(by unfold Circuit.size at hw; omega)
  Za C x w= g.op.eval (g.inputs.map fun r=>if r< w then Za C x r else false):=by
 let j:=w-n
 have hj:j< C.gates.length:=by unfold j Circuit.size at *; omega
 let g:=C.gates[j]
 let earlier:=run (C.gates.take j) (List.ofFn x)
 have plen:earlier.length= w:=by
  simp[earlier,Zb,Nat.min_eq_left hj.le,j]; omega
 have split:run C.gates (List.ofFn x)= run (g::C.gates.drop (j+1)) earlier:=by
  rw[Z54 C.gates (List.ofFn x) j,List.drop_eq_getElem_cons hj]
 have read (r:ℕ):earlier.getD r false= if r< w then Za C x r else false:=by
  by_cases hr:r< w
  ·rw[ite_eq_left hr]
   change earlier.getD r false=(run C.gates (List.ofFn x)).getD r false
   rw[split];exact (Z30 _ earlier r (by simpa only[plen] using hr)).symm
  ·rw[ite_eq_right hr]
   exact List.getD_eq_default _ _ (by omega)
 change (run C.gates (List.ofFn x)).getD w false =
  g.op.eval (g.inputs.map fun r=>if r< w then Za C x r else false)
 rw (occs:=[1]) [split];rw (occs:=[1]) [Z2z];rw[Z30 _ _ _ (by simp[plen]),List.getD_append_right _ _ _ _ (by omega)]
 simp only[plen,Nat.sub_self,List.getD_cons_zero,read]
lemma Z55 {n:ℕ} (C:Circuit) (k:ℕ) (hk:k< C.gates.length)
  (hop:C.gates[k].op= GateOp.and∨C.gates[k].op= GateOp.or)
  (x y:Fin n→ Bool)
  (h:∀ r∈C.gates[k].inputs,r< n+k→ Za C x r= true→ Za C y r= true) :
  Za C x (n+k)= true→ Za C y (n+k)= true:=by
 have hw:n+k< n+C.size:=by unfold Circuit.size; omega
 have hx:=Z1m C x (n+k) (by omega) hw
 have hy:=Z1m C y (n+k) (by omega) hw
 simp only[Nat.add_sub_cancel_left] at hx hy;rw[hx,hy];have hr (r:ℕ) (hm:r∈C.gates[k].inputs) :
   (if r< n+k then Za C x r else false)= true →
   (if r< n+k then Za C y r else false)= true:=by
  by_cases h':r< n+k
  ·simpa[h'] using h r hm h'
  ·simp[h']
 rcases hop with hop | hop
 ·simp only[hop,GateOp.eval,List.all_eq_true,id_eq]
  intro hx b hb;obtain⟨r,hm,rfl⟩:=List.mem_map.mp hb;exact hr r hm (hx _ (List.mem_map.mpr ⟨r,hm,rfl⟩))
 ·simp only[hop,GateOp.eval,List.any_eq_true,id_eq]
  intro hx;obtain⟨b,hb,rfl⟩:=hx;obtain⟨r,hm,hv⟩:=List.mem_map.mp hb;exact⟨_,List.mem_map.mpr ⟨r,hm,rfl⟩,hr r hm hv⟩
lemma Z46 {n:ℕ} (C:Circuit) (k:ℕ) (hk:k< C.gates.length)
  (hop:C.gates[k].op= GateOp.or) (x:Fin n→ Bool) :
  Za C x (n+k)= true↔∃ r∈C.gates[k].inputs,r< n+k∧Za C x r= true:=by
 have hw:n+k< n+C.size:=by unfold Circuit.size; omega
 have hx:=Z1m C x (n+k) (by omega) hw
 simp only[Nat.add_sub_cancel_left] at hx;rw[hx,hop];simp[GateOp.eval]
lemma Z2k {n:ℕ} (C:Circuit) (k:ℕ) (hk:k< C.gates.length)
  (hop:C.gates[k].op= GateOp.and) (x:Fin n→ Bool) :
  Za C x (n+k)= true↔∀ r∈C.gates[k].inputs,r< n+k∧Za C x r= true:=by
 have hw:n+k< n+C.size:=by unfold Circuit.size; omega
 have hx:=Z1m C x (n+k) (by omega) hw
 simp only[Nat.add_sub_cancel_left] at hx;rw[hx,hop];simp[GateOp.eval]
lemma mono {n:ℕ} (C:Circuit)
  (hC:∀ g∈C.gates,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2)
  (x y:Fin n→ Bool) (h:∀ v,x v= true→ y v= true) (w:ℕ) :
  Za C x w= true→ Za C y w= true:=by
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  by_cases hn:w< n
  ·let p:Fin n:=⟨w,hn⟩
   change Za C x p= true→ Za C y p= true
   simpa only[Z20] using h p
  by_cases hw:w< n+C.gates.length
  ·have hk:w-n< C.gates.length:=by omega
   have hwk:w= n+(w-n):=by omega
   rw[hwk];exact Z55 C (w-n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt=>ih r (by omega)
  ·simp[Z29 C x w (by unfold Circuit.size; omega)]
def Sv {n:ℕ} {ι:Type*} (C:Circuit) (l:ι→ Fin n→ Bool) (y:Fin n→ Bool)
  (p:ι) (w:ℕ):Prop:=
 Za C (l p) w= true∧Za C y w= false
def Zw {n:ℕ} {ι:Type*} (C:Circuit) (T:Finset ι) (l:ι→ Fin n→ Bool)
  (y:Fin n→ Bool) (w:ℕ):Prop:=
 ∃ p∈T,∃ p'∈T,p≠p'∧Sv C l y p w∧Sv C l y p' w
lemma Z4s (L:List ℕ) (hL:L.length≤2) (Q:ℕ→ Prop) :
  (L.length=2∧∀ r∈L,Q r)∨∃ c,∀ r∈L,Q r→ r= c:=by
 rcases L with _ | ⟨a,_ | ⟨b,_ | ⟨c,tl⟩⟩⟩
 ·exact Or.inr ⟨0,fun r hr=>absurd hr (by simp)⟩
 ·exact Or.inr ⟨a,fun r hr _=>by simpa using hr⟩
 ·by_cases ha:Q a
  ·by_cases hb:Q b
   ·refine Or.inl ⟨rfl,fun r hr => ?_⟩
    rcases List.mem_pair.mp hr with rfl | rfl
    ·exact ha
    ·exact hb
   ·refine Or.inr ⟨a,fun r hr hq => ?_⟩
    rcases List.mem_pair.mp hr with rfl | rfl
    ·rfl
    ·exact absurd hq hb
  ·refine Or.inr ⟨b,fun r hr hq => ?_⟩
   rcases List.mem_pair.mp hr with rfl | rfl
   ·exact absurd hq ha
   ·rfl
 ·simp at hL
lemma Z4t {n:ℕ} {ι:Type*} (C:Circuit) (T:Finset ι) (l:ι→ Fin n→ Bool)
  (y:Fin n→ Bool)
  (hC:∀ g∈C.gates,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2)
  (k:ℕ) (hk:k< C.gates.length) (hm:Zw C T l y (n+k)) :
  (∃ r∈C.gates[k].inputs,r< n+k∧∀ p∈T,Sv C l y p (n+k)→ Sv C l y p r) ∨
  (C.gates[k].op= GateOp.or∧C.gates[k].inputs.length=2 ∧
   (∀ r∈C.gates[k].inputs,∃ p∈T,Za C (l p) r= true) ∧
   ∀ p∈T,Sv C l y p (n+k)→∃ r∈C.gates[k].inputs,r< n+k∧Sv C l y p r):=by
 obtain⟨p0,hp0,_,_,_,hs0,_⟩:=hm;rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
 ·left
  have hy:=hs0.2
  by_contra hcon
  have hall:∀ r∈C.gates[k].inputs,r< n+k∧Za C y r= true:=by
   intro r hr
   by_contra hr2
   apply hcon;have hlt:=((Z2k C k hk hop (l p0)).mp hs0.1 r hr).1;refine⟨r,hr,hlt,fun p _ hsp=>⟨((Z2k C k hk hop (l p)).mp hsp.1 r hr).2,?_⟩⟩
   by_contra hne
   exact hr2 ⟨hlt,by simpa using hne⟩
  rw[(Z2k C k hk hop y).mpr hall] at hy;exact Bool.noConfusion hy
 ·have hyall:∀ r∈C.gates[k].inputs,r< n+k→ Za C y r= false:=by
   intro r hr hlt
   by_contra h
   have h2:Za C y (n+k)= true:=
    (Z46 C k hk hop y).mpr ⟨r,hr,hlt,by simpa using h⟩
   rw[hs0.2] at h2;exact Bool.noConfusion h2
  have hsv:∀ p∈T,Sv C l y p (n+k) →
    ∃ r∈C.gates[k].inputs,r< n+k∧Za C (l p) r= true∧Sv C l y p r:=by
   intro p _ hsp;obtain⟨r,hr,hlt,hv⟩:=(Z46 C k hk hop (l p)).mp hsp.1;exact⟨r,hr,hlt,hv,hv,hyall r hr hlt⟩
  rcases Z4s C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
   (fun r=>∃ p∈T,r< n+k∧Za C (l p) r= true) with⟨hlen,hQ⟩ | ⟨c,hc⟩
  ·right
   refine⟨hop,hlen,fun r hr => ?_,fun p hp hsp => ?_⟩
   ·obtain⟨p,hp,_,hv⟩:=hQ r hr
    exact⟨p,hp,hv⟩
   ·obtain⟨r,hr,hlt,_,hs⟩:=hsv p hp hsp
    exact⟨r,hr,hlt,hs⟩
  ·left
   obtain⟨r,hr,hlt,hv,_⟩:=hsv p0 hp0 hs0;have hrc:=hc r hr ⟨p0,hp0,hlt,hv⟩;refine⟨r,hr,hlt,fun p hp hsp => ?_⟩
   obtain⟨r',hr',hlt',hv',hs'⟩:=hsv p hp hsp;have hrc':=hc r' hr' ⟨p,hp,hlt',hv'⟩;rw[hrc,← hrc'];exact hs'
lemma Z5m {n:ℕ} {ι:Type*} (C:Circuit) (T:Finset ι) (l:ι→ Fin n→ Bool)
  (y:Fin n→ Bool)
  (hC:∀ g∈C.gates,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2)
  (W:Finset ℕ)
  (hW:∀ k,∀ hk:k< C.gates.length,Zw C T l y (n+k) →
   C.gates[k].op= GateOp.or→ C.gates[k].inputs.length=2 →
   (∀ r∈C.gates[k].inputs,∃ p∈T,Za C (l p) r= true)→ n+k∈W)
  (hlen:∀ w,Zw C T l y w→ n≤ w∧w< n+C.gates.length)
  (t:ℕ) (F:Finset ℕ) (hF:∀ w∈F,Zw C T l y w→ w< t)
  (T':Finset ι) (hT':T'⊆T) (hs:∀ p∈T',∃ w∈F,Sv C l y p w) :
  T'.card≤ F.card+(W.filter (· < t)).card:=by
 classical
 induction t generalizing F with
 | zero=>
  choose! f hfF hfs using hs
  have hinj:Set.InjOn f T':=by
   intro p hp p' hp' e
   by_contra hne
   have hc:Zw C T l y (f p):=
    ⟨p,hT' hp,p',hT' hp',hne,hfs p hp,by rw[e]; exact hfs p' hp'⟩
   have:=hF (f p) (hfF p hp) hc;omega
  have:=Finset.card_le_card_of_injOn f (fun p hp=>hfF p hp) hinj
  omega
 | succ t ih=>
  have hle:(W.filter (· < t)).card≤(W.filter (· < t+1)).card:=
   Finset.card_le_card fun w hw=>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
     by have:=(Finset.mem_filter.mp hw).2; omega⟩
  by_cases hex:t∈F∧Zw C T l y t
  ·obtain⟨h1,h2⟩:=hlen t hex.2
   have hk:t-n< C.gates.length:=by omega
   have htk:t= n+(t-n):=by omega
   have hm:Zw C T l y (n+(t-n)):=by rw[← htk]; exact hex.2
   have he:=Finset.card_erase_add_one hex.1;rcases Z4t C T l y hC (t-n) hk hm with⟨r,hr,hlt,hall⟩ | ⟨hop,hlen2,hQ,hsv⟩
   ·rw[← htk] at hlt hall
    let F':=insert r (F.erase t)
    have hF':∀ w∈F',Zw C T l y w→ w< t:=by
     intro w hw hg;rcases Finset.mem_insert.mp hw with hw | hw
     ·rw[hw]; exact hlt
     ·have hne:=(Finset.mem_erase.mp hw).1
      have hlt:=hF w (Finset.mem_erase.mp hw).2 hg;omega
    have hs':∀ p∈T',∃ w∈F',Sv C l y p w:=by
     intro p hp;obtain⟨w,hw,hsv⟩:=hs p hp;by_cases h:w= t
     ·subst h
      exact⟨r,Finset.mem_insert_self _ _,hall p (hT' hp) hsv⟩
     ·exact⟨w,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h,hw⟩),hsv⟩
    have hi:=ih F' hF' hs';have hu:=Finset.card_insert_le r (F.erase t)
    change F'.card≤_ at hu
    omega
   ·rw[← htk] at hsv
    have htW:t∈W:=by
     have:=hW (t-n) hk hm hop hlen2 hQ;rwa[← htk] at this
    let P:Finset ℕ:=(C.gates[t-n].inputs.filter (· < t)).toFinset
    have hPcard:P.card≤2:=by
     have h1:=List.toFinset_card_le (C.gates[t-n].inputs.filter (· < t));have h2:=List.length_filter_le (fun r=>decide (r< t)) C.gates[t-n].inputs
     change P.card≤_ at h1
     omega
    let F':=F.erase t∪P
    have hF':∀ w∈F',Zw C T l y w→ w< t:=by
     intro w hw hg;rcases Finset.mem_union.mp hw with hw | hw
     ·have hne:=(Finset.mem_erase.mp hw).1
      have hlt:=hF w (Finset.mem_erase.mp hw).2 hg;omega
     ·have:=(List.mem_filter.mp (List.mem_toFinset.mp hw)).2
      simpa using this
    have hs':∀ p∈T',∃ w∈F',Sv C l y p w:=by
     intro p hp;obtain⟨w,hw,hsvp⟩:=hs p hp;by_cases h:w= t
     ·subst h
      obtain⟨r,hr,hlt,hsr⟩:=hsv p (hT' hp) hsvp
      exact⟨r,Finset.mem_union_right _ (List.mem_toFinset.mpr
       (List.mem_filter.mpr ⟨hr,by simpa using hlt⟩)),hsr⟩
     ·exact⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h,hw⟩),hsvp⟩
    have hi:=ih F' hF' hs';have hu:=Finset.card_union_le (F.erase t) P
    change F'.card≤_ at hu
    have hfilter:W.filter (· < t+1)= insert t (W.filter (· < t)):=by
     ext w;simp only[Finset.mem_filter,Finset.mem_insert];constructor
     ·rintro⟨hg,hlt⟩
      by_cases h:w= t
      ·exact Or.inl h
      ·exact Or.inr ⟨hg,by omega⟩
     ·rintro (rfl | ⟨hg,hlt⟩)
      ·exact⟨htW,by omega⟩
      ·exact⟨hg,by omega⟩
    rw[hfilter,Finset.card_insert_of_notMem (by simp)]
    omega
  ·have hF':∀ w∈F,Zw C T l y w→ w< t:=by
    intro w hw hg;have hne:w≠t:=fun e=>hex ⟨e ▸ hw,e ▸ hg⟩
    have hlt:=hF w hw hg;omega
   have:=ih F hF' hs;omega
lemma Z61 {n:ℕ} {ι:Type*} (C:Circuit)
  (hC:∀ g∈C.gates,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2)
  (T:Finset ι) (l:ι→ Fin n→ Bool) (y:Fin n→ Bool) (o:ℕ)
  (ho:∀ p∈T,Sv C l y p o)
  (hin:∀ w,w< n→¬ Zw C T l y w)
  (K:Finset (Fin C.gates.length))
  (hK:∀ g:Fin C.gates.length,Zw C T l y (n+(g:ℕ))→ g∈K) :
  T.card≤ K.card+1:=by
 classical
 let W:Finset ℕ:=Finset.image (fun g:Fin C.gates.length=>n+(g:ℕ)) K
 have hlen:∀ w,Zw C T l y w→ n≤ w∧w< n+C.gates.length:=by
  intro w hc;refine⟨Nat.le_of_not_lt fun h=>hin w h hc,?_⟩
  by_contra hge
  obtain⟨p,_,_,_,_,hsv,_⟩:=hc;have hm:=Z29 C (l p) w (by unfold Circuit.size; omega)
  have h1:=hsv.1;rw[hm] at h1;exact Bool.noConfusion h1
 have h:=Z5m C T l y hC W
  (fun k hk hm _ _ _=>Finset.mem_image.mpr ⟨(⟨k,hk⟩:Fin C.gates.length),hK ⟨k,hk⟩ hm,rfl⟩)
  hlen (n+C.gates.length) {o}
  (fun w _ hc=>(hlen w hc).2) T (Finset.Subset.refl T)
  (fun p hp=>⟨o,Finset.mem_singleton_self o,ho p hp⟩)
 have h1:=Finset.card_filter_le W (· < n+C.gates.length);have h2:W.card≤ K.card:=Finset.card_image_le;rw[Finset.card_singleton] at h;omega
lemma main:∀ (n m:ℕ) (L A:Fin m→ Finset (Fin n)) (D:Circuit) (o:Fin m→ ℕ),(∀ i j:Fin m,i≠j→(L i∩L j).card≤1)→ PEqualNP.MetaComplexity.Monotone2 D→ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D→(∀ j:Fin m,A j⊆L j)→(∀ (j:Fin m) (p:Fin n),p∈A j→(D.wires (List.ofFn (fun i:Fin n=>decide (i= p)))).getD (o j) false= true)→(∀ j:Fin m,(D.wires (List.ofFn (fun i:Fin n=>decide (i∉L j)))).getD (o j) false= false)→∑ j:Fin m,((A j).card-1)≤ D.size:=by
 classical
 intro n m L A D o hint hmono _ hAL htrue hfalse;have hC:∀ g∈D.gates,(g.op= GateOp.and∨g.op= GateOp.or)∧g.inputs.length≤2:=by
  intro g hg;have h:=hmono g hg;refine⟨?_,h.2⟩;rcases h.1 with h1 | h1
  ·exact Or.inl h1
  ·exact Or.inr h1
 let l:Fin n→ Fin n→ Bool:=fun p i=>decide (i= p)
 let y:Fin m→ Fin n→ Bool:=fun j i=>decide (i∉L j)
 let K:Fin m→ Finset (Fin D.gates.length):=fun j=>
  Finset.univ.filter fun g=>Zw D (A j) l (y j) (n+(g:ℕ))
 have hK:∀ j,(A j).card≤(K j).card+1:=by
  intro j;refine Z61 D hC (A j) l (y j) (o j) (fun p hp=>⟨htrue j p hp,hfalse j⟩) ?_ (K j)
   (fun g hm=>Finset.mem_filter.mpr ⟨Finset.mem_univ g,hm⟩)
  rintro w hw ⟨p,_,p',_,hne,hs1,hs2⟩;have e1:l p ⟨w,hw⟩= true:=(Z20 D (l p) ⟨w,hw⟩).symm.trans hs1.1;have e2:l p' ⟨w,hw⟩= true:=(Z20 D (l p') ⟨w,hw⟩).symm.trans hs2.1;exact hne ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2))
 have hd:∀ i∈(Finset.univ:Finset (Fin m)),∀ j∈(Finset.univ:Finset (Fin m)),
   i≠j→ Disjoint (K i) (K j):=by
  intro i _ j _ hij;refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
  obtain⟨a,ha,b,hb,hab,hsa,hsb⟩:=(Finset.mem_filter.mp hgi).2;obtain⟨c,_,_,_,_,hsc,_⟩:=(Finset.mem_filter.mp hgj).2;have hyj:Za D (y j) (n+(g:ℕ))= false:=hsc.2;have key:∀ p:Fin n,Za D (l p) (n+(g:ℕ))= true→ p∈L j:=by
   intro p hv
   by_contra hn
   have h2:=mono D hC (l p) (y j) (fun v hv'=>by
    have hvp:v= p:=of_decide_eq_true hv';rw[hvp]
    exact decide_eq_true hn) _ hv
   exact Bool.noConfusion (hyj.symm.trans h2)
  exact hab (Finset.card_le_one.mp (hint i j hij) a
   (Finset.mem_inter.mpr ⟨hAL i ha,key a hsa.1⟩) b
   (Finset.mem_inter.mpr ⟨hAL i hb,key b hsb.1⟩))
 have h1:∑ j:Fin m,((A j).card-1)≤∑ j:Fin m,(K j).card:=
  Finset.sum_le_sum fun j _=>by
   have:=hK j;omega
 rw[← Finset.card_biUnion hd] at h1;have h2:=Finset.card_le_univ (Finset.univ.biUnion K);rw[Fintype.card_fin] at h2;exact h1.trans h2
end PEqualNP.Outside.L_meta_1690.P1624
namespace PEqualNP.Outside.L_meta_1690
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma main1625:∀ (n m s k:ℕ) (L:Fin m→ Finset (Fin n)) (C:Circuit),(∀ i j:Fin m,i≠j→(L i∩L j).card≤1)→ Monotone2 C→ ReadsBack (n+m) C→ C.size≤ s→ Set.ncard {j:ℕ | j< C.gates.length∧(gateAt C j).op= GateOp.and∧(gateAt C j).inputs.length=2∧∀ i∈(gateAt C j).inputs,0<(C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD i 0}≤ k→(∀ (x:Fin n→ Bool) (Y:Finset (Fin m)),Y.card≤1→ circuitFun (n+m) C (Fin.append x (fun l=>decide (l∈Y)))= true→∃ j∈Y,∃ p∈L j,x p= true)→(Finset.univ.filter (fun e:Fin n× Fin m=>e.1∈L e.2∧circuitFun (n+m) C (Fin.append (fun i=>decide (i= e.1)) (fun l=>decide (l= e.2)))= true)).card≤(6*k+6)*s+(12*k^2+13*k+2)*m+6*k^2+5*k:=by
 intro n m s k L C hL hmono hrb hs hk hsound;obtain⟨M,hMm,hMrb,hMx,hMs,hMt,hMf⟩:=P1623.main P1623.Z4m n m s k C hmono hrb hs hk;obtain⟨D,o,hDm,hDrb,hDs,hDf⟩:=P1622.main n m M hMm hMrb hMx;have hC0:∀ x:Fin n→ Bool,circuitFun (n+m) C
   (Fin.append x (fun _=>false))= false:=by
  intro x
  by_contra hne
  have h1:=hsound x ∅ (by simp) (by simpa using hne)
  obtain⟨j,hj,_⟩:=h1;simp at hj
 have hM1:∀ (x:Fin n→ Bool) (j:Fin m),circuitFun (n+m) M
   (Fin.append x (fun l=>decide (l= j)))= circuitFun (n+m) C
   (Fin.append x (fun l=>decide (l= j))):=by
  intro x j;have h1:=hMf x {j};simp only[Finset.mem_singleton,exists_eq_left] at h1;rw[h1,hC0];simp
 have hM0:∀ x:Fin n→ Bool,circuitFun (n+m) M
   (Fin.append x (fun _=>false))= false:=by
  intro x;have h1:=hMf x ∅;simp only[Finset.notMem_empty,decide_false,false_and,exists_false,Bool.or_false] at h1;rw[h1,hC0]
 have hD:∀ (x:Fin n→ Bool) (j:Fin m),(D.wires (List.ofFn x)).getD (o j) false =
   circuitFun (n+m) C (Fin.append x (fun l=>decide (l= j))):=by
  intro x j;have h1:=hDf x j;rw[hM1,hM0,Bool.false_or] at h1;exact h1.symm
 have h:=P1624.main n m L (fun j=>(L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)) D o hL hDm hDrb
  (fun j=>Finset.filter_subset _ _)
  (by
   intro j p hp;rw[hD]
   exact (Finset.mem_filter.mp hp).2)
  (by
   intro j;rw[hD]
   by_contra hne
   have h1:=hsound (fun i:Fin n=>decide (i∉L j)) {j} (by simp)
    (by
     have h2:(fun l:Fin m=>decide (l∈({j}:Finset (Fin m))))= fun l=>decide (l= j):=by
      funext l;simp
     rw[h2]
     simpa using hne)
   obtain⟨j',hj',p,hp,hx⟩:=h1;rw[Finset.mem_singleton] at hj';subst hj'
   simp[hp] at hx)
 have hcard:(Finset.univ.filter (fun e:Fin n× Fin m=>e.1∈L e.2 ∧
   circuitFun (n+m) C (Fin.append (fun i=>decide (i= e.1))
    (fun l=>decide (l= e.2)))= true)).card ≤
   ∑ j:Fin m,((L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)).card:=by
  rw[← Finset.card_sigma];refine Finset.card_le_card_of_injOn (fun e=>⟨e.2,e.1⟩) ?_ ?_
  ·intro e he
   have he':=(Finset.mem_filter.mp (Finset.mem_coe.mp he)).2;exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr he'⟩)
  ·intro a _ b _ hab
   simp only[Sigma.mk.injEq,heq_eq_eq] at hab;exact Prod.ext hab.2 hab.1
 have hsum:∑ j:Fin m,((L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)).card ≤
   ∑ j:Fin m,(((L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)).card-1)+m:=by
  have h1:∀ j∈(Finset.univ:Finset (Fin m)),((L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)).card ≤
   (((L j).filter (fun p=>circuitFun (n+m) C
   (Fin.append (fun i=>decide (i= p)) (fun l=>decide (l= j)))= true)).card-1)+1:=by
   intro j _;omega
  have h2:=Finset.sum_le_sum h1;rw[Finset.sum_add_distrib] at h2;simpa using h2
 have hDs':D.size≤(6*k+3)*s+12*k^2*m+7*k*m+6*k^2+2*k +
   3*(s+k*(2*m+1))+m:=by
  have h3:=Nat.mul_le_mul_left 3 hMt;omega
 have hfin:(6*k+3)*s+12*k^2*m+7*k*m+6*k^2+2*k +
   3*(s+k*(2*m+1))+m+m=(6*k+6)*s+(12*k^2+13*k+2)*m+6*k^2+5*k:=by
  ring
 omega
end PEqualNP.Outside.L_meta_1690
theorem PEqualNP.Outside.L_meta_1690 : ∀ (n m k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (y : Fin m → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x y) = decide (∃ j : Fin m, ∃ p ∈ L j, x p = true ∧ y j = true)) → (∑ j : Fin m, (L j).card) ≤ (6 * k + 6) * C.size + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  intro n m k L C hL hM hR hk hC
  have hsound : ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true := by
    intro x Y _ hx
    have key := hC x (fun l => decide (l ∈ Y))
    have h2 := key.symm.trans hx
    obtain ⟨j, p, hp, hxp, hj⟩ := of_decide_eq_true h2
    exact ⟨j, by simpa using hj, p, hp, hxp⟩
  have h := PEqualNP.Outside.L_meta_1690.main1625 n m C.size k L C hL hM hR le_rfl hk hsound
  have hcard : (∑ j : Fin m, (L j).card) ≤ (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun e => (e.2, e.1)) ?_ ?_
    · intro e he
      have he' := Finset.mem_sigma.mp (Finset.mem_coe.mp he)
      have key := hC (fun i => decide (i = e.2)) (fun l => decide (l = e.1))
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'.2,
        key.trans (decide_eq_true ⟨e.1, e.2, he'.2, by simp, by simp⟩)⟩)
    · intro a _ b _ hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      simp only [Prod.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      subst h1
      subst h2
      rfl
  exact le_trans hcard h
