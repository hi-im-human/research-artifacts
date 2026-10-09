import MaximalSupportCells

/-!
# Identify the sorted splice successor and construct all original single cuts

System, 2026-09-19. UNCOMPILED PROOF-SCRIPT DRAFT.

No geometric cycle, adjacency table or OriginalEdge is an input. The first
section is finite indexing: the lexicographic successor in nonempty dependent
blocks advances inside the block, then wraps to the next nonempty block.
The geometric result imported above identifies those pairs with EVERY physical
lateral adjacency. The last section constructs the old hinge/cut records.
-/
open Set
open scoped BigOperators Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open EuclideanPrismatoidCoordinates PolyhedralInputBridge

namespace CyclicCutOrders
noncomputable section

section FiniteBlocks
variable {n : ℕ} [NeZero n] (sizes : Fin n → ℕ) (hsizes : ∀ i,0<sizes i)
abbrev Blocks := Σₗ i : Fin n,Fin (sizes i)

@[simp] lemma ofLex_blocks (g : Blocks sizes) : ofLex g = g := rfl

@[simp] lemma toLex_blocks (g : Σ i : Fin n,Fin (sizes i)) : toLex g = g := rfl

def blockNext (g : Blocks sizes) : Blocks sizes :=
  if h : (ofLex g).2.val+1<sizes (ofLex g).1 then
    toLex ⟨(ofLex g).1,⟨(ofLex g).2.val+1,h⟩⟩
  else toLex ⟨next (ofLex g).1,⟨0,hsizes (next (ofLex g).1)⟩⟩

lemma blocks_lt_iff (g q : Blocks sizes) :
    g<q ↔ (ofLex g).1.val<(ofLex q).1.val ∨
      ((ofLex g).1.val=(ofLex q).1.val ∧ (ofLex g).2.val<(ofLex q).2.val) := by
  change Sigma.Lex (fun a b : Fin n => a<b) (fun _ a b => a<b)
    (ofLex g) (ofLex q) ↔
      (ofLex g).1.val<(ofLex q).1.val ∨
        ((ofLex g).1.val=(ofLex q).1.val ∧ (ofLex g).2.val<(ofLex q).2.val)
  generalize ofLex g = g'
  generalize ofLex q = q'
  rcases g' with ⟨i,k⟩
  rcases q' with ⟨j,l⟩
  rw [Sigma.lex_iff]
  constructor
  · rintro (h | ⟨he,h⟩)
    · exact Or.inl h
    · cases he; exact Or.inr ⟨rfl,h⟩
  · rintro (h | ⟨he,h⟩)
    · exact Or.inl h
    · have hij : i=j := Fin.ext he
      subst j
      exact Or.inr ⟨rfl,h⟩

lemma blocks_le_iff (g q : Blocks sizes) :
    g≤q ↔ (ofLex g).1.val<(ofLex q).1.val ∨
      ((ofLex g).1.val=(ofLex q).1.val ∧ (ofLex g).2.val≤(ofLex q).2.val) := by
  change Sigma.Lex (fun a b : Fin n => a<b) (fun _ a b => a≤b)
    (ofLex g) (ofLex q) ↔
      (ofLex g).1.val<(ofLex q).1.val ∨
        ((ofLex g).1.val=(ofLex q).1.val ∧ (ofLex g).2.val≤(ofLex q).2.val)
  generalize ofLex g = g'
  generalize ofLex q = q'
  rcases g' with ⟨i,k⟩
  rcases q' with ⟨j,l⟩
  rw [Sigma.lex_iff]
  constructor
  · rintro (h | ⟨he,h⟩)
    · exact Or.inl h
    · cases he; exact Or.inr ⟨rfl,h⟩
  · rintro (h | ⟨he,h⟩)
    · exact Or.inl h
    · have hij : i=j := Fin.ext he
      subst j
      exact Or.inr ⟨rfl,h⟩

/-- The arithmetic successor either covers its predecessor in the lex order,
or is the first element immediately after the last element. -/
lemma blockNext_cover_or_wrap (g : Blocks sizes) :
    (g<blockNext sizes hsizes g ∧ ∀ z, g<z → ¬z<blockNext sizes hsizes g) ∨
    ((∀ z : Blocks sizes,z≤g) ∧ (∀ z : Blocks sizes,blockNext sizes hsizes g≤z)) := by
  let i := (ofLex g).1
  let k := (ofLex g).2
  have hi_val : i.val=(ofLex g).1.val := rfl
  have hk_val : k.val=(ofLex g).2.val := rfl
  have hsize : sizes i=sizes (ofLex g).1 := congrArg sizes (by rfl : i=(ofLex g).1)
  by_cases hk : k.val+1<sizes i
  · left
    have hnext : blockNext sizes hsizes g =
        toLex ⟨i,⟨k.val+1,hk⟩⟩ := by
      simp only [blockNext,i,k,dif_pos hk]
    rw [hnext]
    constructor
    · apply (blocks_lt_iff sizes _ _).mpr
      rw [ofLex_toLex]
      dsimp only [i,k]
      exact Or.inr ⟨rfl,by omega⟩
    · intro z hz hzq
      have hz' := (blocks_lt_iff sizes g z).mp hz
      have hzq' := (blocks_lt_iff sizes z (toLex ⟨i,⟨k.val+1,hk⟩⟩)).mp hzq
      rw [ofLex_toLex] at hzq'
      change (ofLex z).1.val < i.val ∨
        ((ofLex z).1.val=i.val ∧ (ofLex z).2.val < k.val+1) at hzq'
      omega
  · have hklast : k.val+1=sizes i := by have := k.isLt; omega
    have hnext := next_val i
    by_cases hi : i.val+1<n
    · left
      have hstep : blockNext sizes hsizes g =
          toLex ⟨next i,⟨0,hsizes (next i)⟩⟩ := by
        simp only [blockNext,i,k,dif_neg hk]
      rw [hstep]
      have hni : (next i).val=i.val+1 := by simp [hnext,hi]
      constructor
      · apply (blocks_lt_iff sizes _ _).mpr
        rw [ofLex_toLex]
        change (ofLex g).1.val < (next i).val ∨
          ((ofLex g).1.val=(next i).val ∧ (ofLex g).2.val < 0)
        exact Or.inl (by omega)
      · intro z hz hzq
        have hz' := (blocks_lt_iff sizes g z).mp hz
        have hzq' := (blocks_lt_iff sizes z
          (toLex ⟨next i,⟨0,hsizes (next i)⟩⟩)).mp hzq
        rw [ofLex_toLex] at hzq'
        change (ofLex z).1.val < (next i).val ∨
          ((ofLex z).1.val=(next i).val ∧ (ofLex z).2.val < 0) at hzq'
        have hzi : (ofLex z).1=i := Fin.ext (by omega)
        have hzlt := (ofLex z).2.isLt
        have hsizesEq : sizes (ofLex z).1=sizes i := congrArg sizes hzi
        omega
    · right
      have hstep : blockNext sizes hsizes g =
          toLex ⟨next i,⟨0,hsizes (next i)⟩⟩ := by
        simp only [blockNext,i,k,dif_neg hk]
      rw [hstep]
      have hilast : i.val+1=n := by have := i.isLt; omega
      have hni : (next i).val=0 := by simp [hnext,hi]
      constructor
      · intro z
        apply (blocks_le_iff sizes _ _).mpr
        by_cases hz : (ofLex z).1.val=i.val
        · have hzi : (ofLex z).1=i := Fin.ext hz
          have hzlt := (ofLex z).2.isLt
          have hsizesEq : sizes (ofLex z).1=sizes i := congrArg sizes hzi
          right
          exact ⟨hz,by omega⟩
        · left
          have := (ofLex z).1.isLt
          omega
      · intro z
        apply (blocks_le_iff sizes _ _).mpr
        rw [ofLex_toLex]
        change (next i).val < (ofLex z).1.val ∨
          ((next i).val=(ofLex z).1.val ∧ 0 ≤ (ofLex z).2.val)
        by_cases hz : (ofLex z).1.val=0
        · exact Or.inr ⟨by omega,by omega⟩
        · exact Or.inl (by omega)

/-- Any increasing finite enumeration has the explicitly computed successor.
No geometric reasoning occurs in this finite-order lemma. -/
lemma ordered_successor {r : ℕ} [NeZero r] (hr : 2≤r)
    (f : Fin r ≃o Blocks sizes) (k : Fin r) :
    f (finRotate r k)=blockNext sizes hsizes (f k) := by
  let g := f k
  let q := blockNext sizes hsizes g
  rcases blockNext_cover_or_wrap sizes hsizes g with ⟨hgq,hcover⟩ | ⟨hgmax,hqmin⟩
  · let l := f.symm q
    have hfl : f l=q := f.apply_symm_apply q
    have hkl : k<l := by
      apply f.lt_iff_lt.mp
      simpa only [hfl] using hgq
    have hk1 : k.val+1<r := by have := l.isLt; change k.val<l.val at hkl; omega
    let j : Fin r := ⟨k.val+1,hk1⟩
    have hjl : j≤l := by change k.val+1≤l.val; change k.val<l.val at hkl; omega
    have he : j=l := by
      by_contra hne
      have hjlt : j<l := lt_of_le_of_ne hjl hne
      apply hcover (f j) (f.lt_iff_lt.mpr (by change k.val < k.val+1; omega))
      change f j<q
      rw [←hfl]
      exact f.lt_iff_lt.mpr hjlt
    have hrot : finRotate r k=j := by
      apply Fin.ext
      simp only [finRotate_apply,Fin.val_add]
      have hone : (1 : Fin r).val=1 := by simp [Fin.val_natCast,Nat.mod_eq_of_lt (by omega : 1<r)]
      rw [hone,Nat.mod_eq_of_lt hk1]
    rw [hrot,he,hfl]
  · have hkmax : k.val+1=r := by
      by_contra hn
      have hk1 : k.val+1<r := by have := k.isLt; omega
      let j : Fin r := ⟨k.val+1,hk1⟩
      have hbad := f.le_iff_le.mp (hgmax (f j))
      change k.val+1≤k.val at hbad
      omega
    have hf0 : f 0=q := by
      apply le_antisymm
      · have hz : (0 : Fin r)≤f.symm q := Fin.zero_le _
        simpa only [f.apply_symm_apply] using f.monotone hz
      · exact hqmin (f 0)
    have hrot : finRotate r k=0 := by
      apply Fin.ext
      simp only [finRotate_apply,Fin.val_add]
      have hone : (1 : Fin r).val=1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1<r)]
      rw [hone,hkmax,Nat.mod_self,Fin.val_zero]
    rw [hrot,hf0]
end FiniteBlocks

section Geometry
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

abbrev sizes (i : Fin nA) := (knots A B i).card-1
lemma sizes_pos (i : Fin nA) : 0<sizes A B i := by
  have := one_lt_knots_card A B i
  dsimp [sizes]
  omega

def nextGap (g : Gap A B) : Gap A B :=
  blockNext (sizes A B) (sizes_pos A B) g

lemma rightKnot_last (g : Gap A B) (hg : ¬g.2.val+1<sizes A B g.1) :
    rightKnot A B g=1 := by
  have hglt := g.2.isLt
  have hlast : g.2.val+1=sizes A B g.1 := by
    dsimp only [sizes] at hglt hg ⊢
    omega
  dsimp [sizes] at hlast
  let hc : (knots A B g.1).card-1+1=(knots A B g.1).card :=
    Nat.sub_add_cancel (one_lt_knots_card A B g.1).le
  let kr := Fin.cast hc g.2.succ
  let k1 := (orderedKnots A B g.1).symm ⟨1,by simp [knots]⟩
  have hk1 : k1≤kr := by
    have hk := k1.isLt
    change k1.val≤g.2.val+1
    omega
  have h1 := (orderedKnots A B g.1).monotone hk1
  have hleft : orderedKnots A B g.1 k1=⟨1,by simp [knots]⟩ :=
    (orderedKnots A B g.1).apply_symm_apply _
  rw [hleft] at h1
  have hle := (knots_subset_Icc A B g.1 (gap_consecutive A B g).2.1).2
  exact le_antisymm hle h1

/-- The right endpoint of a gap is the LEFT endpoint of the next emitted gap,
including both block changes and the final/first seam. -/
lemma rightSide_nextGap (g : Gap A B) :
    rightSide A B g=gapSide A B (nextGap A B g) := by
  by_cases hg : g.2.val+1<sizes A B g.1
  · let q : Gap A B := ⟨g.1,⟨g.2.val+1,hg⟩⟩
    have hng : nextGap A B g=q := by
      unfold nextGap blockNext
      change (if h : g.2.val+1<sizes A B g.1 then ⟨g.1,⟨g.2.val+1,h⟩⟩
        else ⟨next g.1,⟨0,sizes_pos A B (next g.1)⟩⟩)=q
      rw [dif_pos hg]
    have he : rightKnot A B g=leftKnot A B q := by
      dsimp [q]
      unfold rightKnot leftKnot
      apply congrArg (fun x => ((orderedKnots A B g.1) x : ℝ))
      apply Fin.ext
      rfl
    apply Subtype.ext
    change unitRay (normalBlend A g.1 (rightKnot A B g))=
      unitRay (normalBlend A (nextGap A B g).1 (leftKnot A B (nextGap A B g)))
    rw [hng]
    dsimp [q]
    rw [he]
  · have he : nextGap A B g=zeroGap A B (next g.1) := by
      unfold nextGap blockNext
      change (if h : g.2.val+1<sizes A B g.1 then ⟨g.1,⟨g.2.val+1,h⟩⟩
        else ⟨next g.1,⟨0,sizes_pos A B (next g.1)⟩⟩)=zeroGap A B (next g.1)
      rw [dif_neg hg]
      unfold zeroGap
      apply Sigma.ext rfl
      exact heq_of_eq (Fin.ext rfl)
    apply Subtype.ext
    change unitRay (normalBlend A g.1 (rightKnot A B g))=
      unitRay (normalBlend A (nextGap A B g).1 (leftKnot A B (nextGap A B g)))
    rw [rightKnot_last A B g hg,he,leftKnot_zeroGap]
    simpa [normalBlend,zeroGap]

abbrev sideCount := Fintype.card (OrderedGap A B)

lemma three_le_sideCount : 3 ≤ sideCount A B := by
  have hi : Function.Injective (fun i : Fin nA => (zeroGap A B i : OrderedGap A B)) := by
    intro i j h
    exact congrArg Sigma.fst h
  have hcard := Fintype.card_le_of_injective _ hi
  simp only [Fintype.card_fin] at hcard
  exact le_trans A.three_le hcard

instance sideCount_neZero : NeZero (sideCount A B) :=
  ⟨by have := three_le_sideCount A B; omega⟩

def cycle : Fin (sideCount A B) ≃ Side A B := orderedSideEnumeration A B

def enumeratedGap (i : Fin (sideCount A B)) : Gap A B := orderedGaps A B i

lemma cycle_gap (i : Fin (sideCount A B)) :
    cycle A B i=gapSide A B (enumeratedGap A B i) := rfl

lemma rightSide_cycle_successor (i : Fin (sideCount A B)) :
    rightSide A B (enumeratedGap A B i)=cycle A B (finRotate _ i) := by
  rw [rightSide_nextGap,cycle_gap]
  congr 1
  exact (ordered_successor (sizes A B) (sizes_pos A B)
    (le_trans (by norm_num) (three_le_sideCount A B)) (orderedGaps A B) i).symm

/-- THE GEOMETRIC CYCLE: the previously enumerated rays now have an exhaustive
physical-adjacency iff, including the wraparound pair. -/
theorem original_cycle_adjacency {h : ℝ} (hh : 0<h)
    (i j : Fin (sideCount A B)) :
    MaterialAdjacent A B hh (cycle A B i) (cycle A B j) ↔
      j=finRotate _ i ∨ i=finRotate _ j := by
  rw [materialAdjacency_iff_gapEndpoints A B hh]
  constructor
  · rintro ⟨g,hg⟩
    let k := (orderedGaps A B).symm (g : OrderedGap A B)
    have hk : enumeratedGap A B k=g := (orderedGaps A B).apply_symm_apply g
    have hl : gapSide A B g=cycle A B k := by rw [cycle_gap,hk]
    have hr : rightSide A B g=cycle A B (finRotate _ k) := by
      rw [←hk,rightSide_cycle_successor]
    rcases hg with ⟨hi,hj⟩ | ⟨hj,hi⟩
    · have hie : i=k := (cycle A B).injective (hi.trans hl)
      have hje : j=finRotate _ k := (cycle A B).injective (hj.trans hr)
      exact Or.inl (by simpa [hie] using hje)
    · have hje : j=k := (cycle A B).injective (hj.trans hl)
      have hie : i=finRotate _ k := (cycle A B).injective (hi.trans hr)
      exact Or.inr (by simpa [hje] using hie)
  · rintro (rfl | rfl)
    · exact ⟨enumeratedGap A B i,Or.inl ⟨cycle_gap A B i,(rightSide_cycle_successor A B i).symm⟩⟩
    · exact ⟨enumeratedGap A B j,Or.inr ⟨cycle_gap A B j,(rightSide_cycle_successor A B j).symm⟩⟩

/-- An actual edge certificate on each geometric successor pair. -/
def cyclicEdge {h : ℝ} (hh : 0<h) (i : Fin (sideCount A B)) :
    OriginalEdge (certificate A B hh (cycle A B i))
      (certificate A B hh (cycle A B (finRotate _ i))) := by
  have ed := gapOriginalEdge A B hh (enumeratedGap A B i)
  rw [←cycle_gap,rightSide_cycle_successor] at ed
  exact ed

/-- Every certified edge is between cyclic neighbors, not only the ones
constructed by cyclicEdge. -/
theorem everyOriginalEdge_cyclic {h : ℝ} (hh : 0<h)
    (i j : Fin (sideCount A B))
    (ed : OriginalEdge (certificate A B hh (cycle A B i))
      (certificate A B hh (cycle A B j))) :
    j=finRotate _ i ∨ i=finRotate _ j := by
  apply (original_cycle_adjacency A B hh i j).mp
  apply (materialAdjacency_iff_gapEndpoints A B hh _ _).mpr
  exact arbitraryOriginalEdge_covered A B hh _ _ ed

/-! ## Rotate the certified geometric ring, then open exactly its chosen edge. -/

lemma size_restore : sideCount A B-1+1=sideCount A B := by
  have := three_le_sideCount A B
  omega

def positions : Fin (sideCount A B-1+1) ≃ Fin (sideCount A B) :=
  finCongr (size_restore A B)

def order (e : Fin (sideCount A B)) :
    Fin (sideCount A B-1+1) ≃ Side A B :=
  (positions A B).trans ((finCycle (finRotate _ e)).trans (cycle A B))

lemma rotate_commutes_shift (e k : Fin (sideCount A B)) :
    finCycle (finRotate _ e) (finRotate _ k)=
      finRotate _ (finCycle (finRotate _ e) k) := by
  simp only [finRotate_apply,finCycle_apply]
  abel

lemma order_adjacent_positions {h : ℝ} (hh : 0<h) (e : Fin (sideCount A B))
    (i j : Fin (sideCount A B-1+1)) :
    MaterialAdjacent A B hh (order A B e i) (order A B e j) ↔
      positions A B j=finRotate _ (positions A B i) ∨
      positions A B i=finRotate _ (positions A B j) := by
  change MaterialAdjacent A B hh
    (cycle A B (finCycle (finRotate _ e) (positions A B i)))
    (cycle A B (finCycle (finRotate _ e) (positions A B j))) ↔ _
  rw [original_cycle_adjacency A B hh]
  constructor
  · rintro (hj | hi)
    · left
      apply (finCycle (finRotate _ e)).injective
      exact hj.trans (rotate_commutes_shift A B e (positions A B i)).symm
    · right
      apply (finCycle (finRotate _ e)).injective
      exact hi.trans (rotate_commutes_shift A B e (positions A B j)).symm
  · rintro (hj | hi)
    · left
      rw [hj]
      exact rotate_commutes_shift A B e (positions A B i)
    · right
      rw [hi]
      exact rotate_commutes_shift A B e (positions A B j)

lemma position_step (j : Fin (sideCount A B-1)) :
    positions A B j.succ=finRotate _ (positions A B j.castSucc) := by
  have hr := three_le_sideCount A B
  apply Fin.ext
  change j.val+1=(finRotate _ (positions A B j.castSucc)).val
  simp only [finRotate_apply,Fin.val_add]
  have hone : (1 : Fin (sideCount A B)).val=1 := by
    change 1%sideCount A B=1
    exact Nat.mod_eq_of_lt (by omega)
  have hp : (positions A B j.castSucc).val=j.val := rfl
  have hbound : j.val+1<sideCount A B := by have := j.isLt; omega
  rw [hone,hp,Nat.mod_eq_of_lt hbound]

lemma position_wrap : positions A B 0=
    finRotate _ (positions A B (Fin.last (sideCount A B-1))) := by
  have hr := three_le_sideCount A B
  apply Fin.ext
  change 0=(finRotate _ (positions A B (Fin.last (sideCount A B-1)))).val
  simp only [finRotate_apply,Fin.val_add]
  have hone : (1 : Fin (sideCount A B)).val=1 := by
    change 1%sideCount A B=1
    exact Nat.mod_eq_of_lt (by omega)
  have hp : (positions A B (Fin.last (sideCount A B-1))).val=sideCount A B-1 := rfl
  rw [hone,hp]
  change 0=(sideCount A B-1+1)%sideCount A B
  rw [size_restore,Nat.mod_self]

/-- Construct the old OriginalEdge from the independently proved adjacency. -/
def edgeOfAdjacent {h : ℝ} (hh : 0<h) (u v : Side A B)
    (ha : MaterialAdjacent A B hh u v) :
    OriginalEdge (certificate A B hh u) (certificate A B hh v) :=
  Classical.choice (by
    obtain ⟨hne,p,hpu,hpv,ht⟩ := ha
    exact originalEdge_of_shared_interior A B hh u v hne p hpu hpv ht)

def hinge {h : ℝ} (hh : 0<h) (e : Fin (sideCount A B))
    (j : Fin (sideCount A B-1)) :
    OriginalEdge (certificate A B hh (order A B e j.castSucc))
      (certificate A B hh (order A B e j.succ)) :=
  edgeOfAdjacent A B hh _ _
    ((order_adjacent_positions A B hh e _ _).mpr (Or.inl (position_step A B j)))

def cut {h : ℝ} (hh : 0<h) (e : Fin (sideCount A B)) :
    OriginalEdge (certificate A B hh (order A B e (Fin.last (sideCount A B-1))))
      (certificate A B hh (order A B e 0)) :=
  edgeOfAdjacent A B hh _ _
    ((order_adjacent_positions A B hh e _ _).mpr (Or.inl (position_wrap A B)))

/-- Consecutive positions are either one chain link or the one omitted
last/first link. This is exact finite coverage, not a sample of cut orders. -/
lemma position_edge_cases (i j : Fin (sideCount A B-1+1))
    (hj : positions A B j=finRotate _ (positions A B i)) :
    (i=Fin.last _ ∧ j=0) ∨
      ∃ k : Fin (sideCount A B-1), i=k.castSucc ∧ j=k.succ := by
  by_cases hi : i=Fin.last _
  · left
    refine ⟨hi,?_⟩
    apply (positions A B).injective
    rw [hj,hi,←position_wrap]
  · have hil : i.val<sideCount A B-1 := by
      have hilt := i.isLt
      have hine : i.val≠sideCount A B-1 := fun hv => hi (Fin.ext hv)
      omega
    let k : Fin (sideCount A B-1) := ⟨i.val,hil⟩
    have hik : i=k.castSucc := Fin.ext rfl
    right
    refine ⟨k,hik,?_⟩
    apply (positions A B).injective
    rw [hj,hik,←position_step]

/-- All non-cut physical connections occur among the chain hinges. No extra
OriginalEdge or strict-height adjacency can be omitted by rotating the list. -/
theorem all_adjacencies_accounted {h : ℝ} (hh : 0<h) (e : Fin (sideCount A B))
    (u v : Side A B) (ha : MaterialAdjacent A B hh u v) :
    (u=order A B e (Fin.last _) ∧ v=order A B e 0) ∨
    (v=order A B e (Fin.last _) ∧ u=order A B e 0) ∨
    ∃ k : Fin (sideCount A B-1),
      (u=order A B e k.castSucc ∧ v=order A B e k.succ) ∨
      (v=order A B e k.castSucc ∧ u=order A B e k.succ) := by
  let i := (order A B e).symm u
  let j := (order A B e).symm v
  have hi : order A B e i=u := (order A B e).apply_symm_apply u
  have hj : order A B e j=v := (order A B e).apply_symm_apply v
  have ha' : MaterialAdjacent A B hh (order A B e i) (order A B e j) := by
    rw [hi,hj]
    exact ha
  have hadj := (order_adjacent_positions A B hh e i j).mp ha'
  rcases hadj with h | h
  · rcases position_edge_cases A B i j h with ⟨hil,hj0⟩ | ⟨k,hik,hjk⟩
    · exact Or.inl ⟨by simpa [hil] using hi.symm,by simpa [hj0] using hj.symm⟩
    · exact Or.inr (Or.inr ⟨k,Or.inl ⟨by simpa [hik] using hi.symm,by simpa [hjk] using hj.symm⟩⟩)
  · rcases position_edge_cases A B j i h with ⟨hjl,hi0⟩ | ⟨k,hjk,hik⟩
    · exact Or.inr (Or.inl ⟨by simpa [hjl] using hj.symm,by simpa [hi0] using hi.symm⟩)
    · exact Or.inr (Or.inr ⟨k,Or.inr ⟨by simpa [hjk] using hj.symm,by simpa [hik] using hi.symm⟩⟩)


/-- Unordered physical face pairs; the cut is one edge, not two directed links. -/
def SamePair {X : Type*} (u v x y : X) : Prop :=
  (u=x ∧ v=y) ∨ (u=y ∧ v=x)

lemma order_zero (e : Fin (sideCount A B)) :
    order A B e 0=cycle A B (finRotate _ e) := by
  change cycle A B (positions A B 0+finRotate _ e)=_
  have hz : positions A B 0=0 := Fin.ext rfl
  rw [hz,zero_add]

lemma order_last (e : Fin (sideCount A B)) :
    order A B e (Fin.last _)=cycle A B e := by
  change cycle A B (positions A B (Fin.last _)+finRotate _ e)=_
  have hz : positions A B 0=0 := Fin.ext rfl
  have hl : positions A B (Fin.last _)+1=0 := by
    simpa only [finRotate_apply,hz] using (position_wrap A B).symm
  congr 1
  rw [finRotate_apply]
  calc
    positions A B (Fin.last _)+(e+1)=(positions A B (Fin.last _)+1)+e := by abel
    _=e := by rw [hl,zero_add]

/-- Different seam labels enumerate the actual successor edges, rather than
silently selecting the same seam for every returned order. -/
theorem cut_endpoints_original_seam (e : Fin (sideCount A B)) :
    order A B e (Fin.last _)=cycle A B e ∧
    order A B e 0=cycle A B (finRotate _ e) :=
  ⟨order_last A B e,order_zero A B e⟩

lemma chain_pair_not_cut (e : Fin (sideCount A B)) (j : Fin (sideCount A B-1)) :
    ¬ SamePair (order A B e j.castSucc) (order A B e j.succ)
      (order A B e (Fin.last _)) (order A B e 0) := by
  rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
  · have h := congrArg Fin.val ((order A B e).injective h2)
    change j.val+1=0 at h
    omega
  · have h1' := congrArg Fin.val ((order A B e).injective h1)
    have h2' := congrArg Fin.val ((order A B e).injective h2)
    change j.val=0 at h1'
    change j.val+1=sideCount A B-1 at h2'
    have hr := three_le_sideCount A B
    omega

/-- Exact non-cut equivalence: every uncut material adjacency appears in the
chain AND none of the chain pairs is the omitted cut. -/
theorem uncut_iff_chain {h : ℝ} (hh : 0<h) (e : Fin (sideCount A B))
    (u v : Side A B) :
    (MaterialAdjacent A B hh u v ∧
      ¬ SamePair u v (order A B e (Fin.last _)) (order A B e 0)) ↔
    ∃ j : Fin (sideCount A B-1),
      SamePair u v (order A B e j.castSucc) (order A B e j.succ) := by
  constructor
  · rintro ⟨ha,hn⟩
    rcases all_adjacencies_accounted A B hh e u v ha with hcut | hcut | hchain
    · exact False.elim (hn (Or.inl hcut))
    · exact False.elim (hn (Or.inr ⟨hcut.2,hcut.1⟩))
    · obtain ⟨j,hj⟩ := hchain
      refine ⟨j,?_⟩
      exact hj.elim Or.inl (fun z => Or.inr ⟨z.2,z.1⟩)
  · rintro ⟨j,hj⟩
    have hforward := (order_adjacent_positions A B hh e j.castSucc j.succ).mpr
      (Or.inl (position_step A B j))
    rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hforward,chain_pair_not_cut A B e j⟩
    · constructor
      · obtain ⟨hne,p,hp,hq,ht⟩ := hforward
        exact ⟨Ne.symm hne,p,hq,hp,ht⟩
      · intro hbad
        apply chain_pair_not_cut A B e j
        rcases hbad with ⟨h1,h2⟩ | ⟨h1,h2⟩
        · exact Or.inr ⟨h2,h1⟩
        · exact Or.inl ⟨h2,h1⟩

/-- The constructed family of all cut orders and OriginalEdges has the EXACT
input shape expected by the checked recovery theorem. Every non-cut physical
connection is a chain link, and every chain link is a non-cut connection.
No safe-trim existence, full layout or external unfolding theorem is assumed. -/
theorem original_cycle_cut_package {h : ℝ} (hh : 0<h) :
    ∃ n : ℕ, 2≤n ∧
      ∃ S : Type, Finite S ∧ Nonempty S ∧
      ∃ orders : S → (Fin (n+1) ≃ Side A B),
      Nonempty ((e : S) → (j : Fin n) →
        OriginalEdge (certificate A B hh (orders e j.castSucc))
          (certificate A B hh (orders e j.succ))) ∧
      Nonempty ((e : S) →
        OriginalEdge (certificate A B hh (orders e (Fin.last n)))
          (certificate A B hh (orders e 0))) ∧
      (∀ e u v,
        (MaterialAdjacent A B hh u v ∧
          ¬ SamePair u v (orders e (Fin.last n)) (orders e 0)) ↔
        ∃ j : Fin n, SamePair u v (orders e j.castSucc) (orders e j.succ)) := by
  refine ⟨sideCount A B-1,by have := three_le_sideCount A B; omega,
    Fin (sideCount A B),inferInstance,inferInstance,order A B,
    ⟨hinge A B hh⟩,⟨cut A B hh⟩,?_⟩
  exact uncut_iff_chain A B hh

end Geometry
end
end CyclicCutOrders

#print axioms CyclicCutOrders.ordered_successor
#print axioms CyclicCutOrders.rightSide_nextGap
#print axioms CyclicCutOrders.original_cycle_adjacency
#print axioms CyclicCutOrders.cyclicEdge
#print axioms CyclicCutOrders.everyOriginalEdge_cyclic
#print axioms CyclicCutOrders.hinge
#print axioms CyclicCutOrders.cut
#print axioms CyclicCutOrders.all_adjacencies_accounted
#print axioms CyclicCutOrders.cut_endpoints_original_seam
#print axioms CyclicCutOrders.uncut_iff_chain
#print axioms CyclicCutOrders.original_cycle_cut_package
#check @CyclicCutOrders.original_cycle_adjacency
#check @CyclicCutOrders.original_cycle_cut_package
