import NestedBandExternalApplication
import Mathlib.Topology.Constructions

/-!
# The actual cut-open lateral surface and its continuous development

The surface is the quotient of the disjoint union of the recovered opened face
chain by equal-material gluing across every intervening face.  There is no
wraparound generator, so the selected original seam remains duplicated.
-/

open Set
open scoped Pointwise Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CyclicCutOrders NestedBandExternalApplication

namespace CutSurfaceQuotient
noncomputable section
set_option maxHeartbeats 2000000

section Presentation
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h) (e : Fin (sideCount A B))

abbrev FacePiece (i : Fin (sideCount A B-1+1)) :=
  {x : FaceSpace A B h (order A B e i) //
    x ∈ (certificate A B hh (order A B e i)).domain}

abbrev TaggedFacePoint := Σ i, FacePiece A B hh e i

def ambient (z : TaggedFacePoint A B hh e) : PhysicalAmbient :=
  (certificate A B hh (order A B e z.1)).chart z.2.val

def Between (i j k : Fin (sideCount A B-1+1)) : Prop :=
  min i.val j.val ≤ k.val ∧ k.val ≤ max i.val j.val

lemma between_refl (i k : Fin (sideCount A B-1+1))
    (hk : Between A B i i k) : k = i := by
  unfold Between at hk
  apply Fin.ext
  omega

lemma between_symm (i j k : Fin (sideCount A B-1+1)) :
    Between A B i j k ↔ Between A B j i k := by
  simp only [Between, min_comm, max_comm]

lemma between_trans_cover (i j l k : Fin (sideCount A B-1+1))
    (hk : Between A B i l k) :
    Between A B i j k ∨ Between A B j l k := by
  unfold Between at hk ⊢
  omega

/-- Equal physical material, connected through every intervening opened face. -/
def CutRelated (x y : TaggedFacePoint A B hh e) : Prop :=
  ambient A B hh e x = ambient A B hh e y ∧
  ∀ k, Between A B x.1 y.1 k →
    ambient A B hh e x ∈ materialFace A B hh (order A B e k)

lemma cutRelated_refl (x : TaggedFacePoint A B hh e) :
    CutRelated A B hh e x x := by
  constructor
  · rfl
  · intro k hk
    have hki := between_refl A B x.1 k hk
    subst k
    exact ⟨x.2.val, x.2.property, rfl⟩

lemma cutRelated_symm {x y : TaggedFacePoint A B hh e}
    (hxy : CutRelated A B hh e x y) : CutRelated A B hh e y x := by
  constructor
  · exact hxy.1.symm
  · intro k hk
    rw [hxy.1.symm]
    exact hxy.2 k ((between_symm A B y.1 x.1 k).mp hk)

lemma cutRelated_trans {x y z : TaggedFacePoint A B hh e}
    (hxy : CutRelated A B hh e x y) (hyz : CutRelated A B hh e y z) :
    CutRelated A B hh e x z := by
  constructor
  · exact hxy.1.trans hyz.1
  · intro k hk
    rcases between_trans_cover A B x.1 y.1 z.1 k hk with hkxy | hkyz
    · exact hxy.2 k hkxy
    · rw [hxy.1]
      exact hyz.2 k hkyz

def cutSetoid : Setoid (TaggedFacePoint A B hh e) where
  r := CutRelated A B hh e
  iseqv := {
    refl := cutRelated_refl A B hh e
    symm := fun hxy => cutRelated_symm A B hh e hxy
    trans := fun hxy hyz => cutRelated_trans A B hh e hxy hyz }

abbrev CutSurface := Quotient (cutSetoid A B hh e)

def faceInclusion (i : Fin (sideCount A B-1+1)) :
    FacePiece A B hh e i → CutSurface A B hh e :=
  fun x => @Quotient.mk' _ (cutSetoid A B hh e) ⟨i,x⟩

theorem faceInclusion_continuous (i : Fin (sideCount A B-1+1)) :
    Continuous (faceInclusion A B hh e i) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

theorem faceInclusion_injective (i : Fin (sideCount A B-1+1)) :
    Function.Injective (faceInclusion A B hh e i) := by
  intro x y hxy
  have hr : CutRelated A B hh e ⟨i,x⟩ ⟨i,y⟩ :=
    @Quotient.exact _ (cutSetoid A B hh e) _ _ hxy
  apply Subtype.ext
  apply (certificate A B hh (order A B e i)).chart.injective
  exact hr.1

theorem adjacent_cutRelated (j : Fin (sideCount A B-1))
    (x : FacePiece A B hh e j.castSucc)
    (y : FacePiece A B hh e j.succ)
    (hxy : ambient A B hh e ⟨j.castSucc,x⟩ =
      ambient A B hh e ⟨j.succ,y⟩) :
    CutRelated A B hh e ⟨j.castSucc,x⟩ ⟨j.succ,y⟩ := by
  constructor
  · exact hxy
  · intro k hk
    have hcase : k = j.castSucc ∨ k = j.succ := by
      apply Or.imp Fin.ext Fin.ext
      change k.val = j.val ∨ k.val = j.val+1
      simp only [Between] at hk
      have hcast : j.castSucc.val = j.val := rfl
      have hsucc : j.succ.val = j.val+1 := rfl
      omega
    rcases hcase with rfl | rfl
    · exact ⟨x.val,x.property,rfl⟩
    · rw [hxy]
      exact ⟨y.val,y.property,rfl⟩

def ambientPre (z : TaggedFacePoint A B hh e) :
    {p : PhysicalAmbient // p ∈ lateralBoundary (halfspaces A B h)} :=
  ⟨ambient A B hh e z, by
    rw [← constructed_lateral_coverage A B hh]
    exact Set.mem_iUnion.mpr ⟨order A B e z.1,
      ⟨z.2.val,z.2.property,rfl⟩⟩⟩

theorem ambientPre_continuous : Continuous (ambientPre A B hh e) := by
  apply continuous_sigma
  intro i
  apply Continuous.subtype_mk
  exact (certificate A B hh (order A B e i)).chart.continuous.comp continuous_subtype_val

lemma ambientPre_eq_of_cutRelated {x y : TaggedFacePoint A B hh e}
    (hxy : CutRelated A B hh e x y) :
    ambientPre A B hh e x = ambientPre A B hh e y :=
  Subtype.ext hxy.1

def materialProjection : CutSurface A B hh e →
    {p : PhysicalAmbient // p ∈ lateralBoundary (halfspaces A B h)} :=
  Quotient.lift (ambientPre A B hh e)
    (fun _ _ hxy => ambientPre_eq_of_cutRelated A B hh e hxy)

theorem materialProjection_continuous :
    Continuous (materialProjection A B hh e) :=
  (ambientPre_continuous A B hh e).quotient_lift _

@[simp] theorem materialProjection_faceInclusion
    (i : Fin (sideCount A B-1+1)) (x : FacePiece A B hh e i) :
    materialProjection A B hh e (faceInclusion A B hh e i x) =
      ⟨(certificate A B hh (order A B e i)).chart x.val, by
        rw [← constructed_lateral_coverage A B hh]
        exact Set.mem_iUnion.mpr ⟨order A B e i,⟨x.val,x.property,rfl⟩⟩⟩ := by
  apply Subtype.ext
  rfl

theorem materialProjection_surjective :
    Function.Surjective (materialProjection A B hh e) := by
  intro p
  have hp : p.val ∈ ⋃ u, (certificate A B hh u).chart ''
      (certificate A B hh u).domain := by
    rw [constructed_lateral_coverage A B hh]
    exact p.property
  obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hp
  obtain ⟨x,hx,hxp⟩ := hu
  obtain ⟨i,rfl⟩ := (order A B e).surjective u
  let xi : FacePiece A B hh e i := ⟨x,hx⟩
  refine ⟨faceInclusion A B hh e i xi,?_⟩
  apply Subtype.ext
  exact hxp

end Presentation

section Development
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  {A : ReducedConvexPolygon nA} {B : ReducedConvexPolygon nB}
  {h : ℝ} {hh : 0 < h} {e : Fin (sideCount A B)}
  {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  (U : (i : Fin (sideCount A B-1+1)) →
    FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Q)

def developedPre (z : TaggedFacePoint A B hh e) : Q := U z.1 z.2.val

theorem developedPre_continuous :
    Continuous (developedPre (A := A) (B := B) (hh := hh) (e := e) U) := by
  apply continuous_sigma
  intro i
  exact (U i).continuous.comp continuous_subtype_val

lemma fin_chain_eq {n : ℕ} {α : Type*} (f : Fin (n+1) → α)
    {i j : Fin (n+1)} (hij : i.val ≤ j.val)
    (hstep : ∀ k : Fin n, i.val ≤ k.val → k.succ.val ≤ j.val →
      f k.castSucc = f k.succ) : f i = f j := by
  have chain : ∀ k : Fin (n+1), i.val ≤ k.val → k.val ≤ j.val → f i = f k := by
    apply Fin.induction
    · intro hi0 _
      have hi0' : i.val ≤ 0 := by simpa using hi0
      have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi0')
      subst i
      rfl
    · intro k ih hik hkj
      by_cases hi : i.val = k.succ.val
      · have hi' : i = k.succ := Fin.ext hi
        subst i
        rfl
      · have hcast : k.castSucc.val = k.val := rfl
        have hsucc : k.succ.val = k.val+1 := rfl
        have hik' : i.val ≤ k.castSucc.val := by
          change i.val ≤ k.val
          omega
        have hkj' : k.castSucc.val ≤ j.val := by
          change k.val ≤ j.val
          omega
        exact (ih hik' hkj').trans (hstep k hik' hkj)
  exact chain j hij (le_refl _)

lemma developed_eq_forward
    (hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i))
    {x y : TaggedFacePoint A B hh e}
    (hxy : CutRelated A B hh e x y)
    (hij : x.1.val ≤ y.1.val) :
    developedPre U x = developedPre U y := by
  classical
  let rep : (k : Fin (sideCount A B-1+1)) → FacePiece A B hh e k :=
    fun k => if hk : Between A B x.1 y.1 k then
      ⟨Classical.choose (hxy.2 k hk),
        (Classical.choose_spec (hxy.2 k hk)).1⟩
    else
      ⟨(certificate A B hh (order A B e k)).center,
        interior_subset (certificate A B hh (order A B e k)).center_interior⟩
  have rep_chart (k : Fin (sideCount A B-1+1))
      (hk : Between A B x.1 y.1 k) :
      (certificate A B hh (order A B e k)).chart (rep k).val =
        ambient A B hh e x := by
    simp only [rep, dite_eq_left hk]
    exact (Classical.choose_spec (hxy.2 k hk)).2
  have between_of_bounds (k : Fin (sideCount A B-1+1))
      (hxk : x.1.val ≤ k.val) (hky : k.val ≤ y.1.val) :
      Between A B x.1 y.1 k := by
    unfold Between
    rw [min_eq_left hij, max_eq_right hij]
    exact ⟨hxk,hky⟩
  let f : Fin (sideCount A B-1+1) → Q := fun k => U k (rep k).val
  have hchain : f x.1 = f y.1 := by
    apply fin_chain_eq f hij
    intro k hxk hky
    have hcast : k.castSucc.val = k.val := rfl
    have hsucc : k.succ.val = k.val+1 := rfl
    apply hDev.1 k (rep k.castSucc).val (rep k.castSucc).property
      (rep k.succ).val (rep k.succ).property
    exact (rep_chart k.castSucc
      (between_of_bounds k.castSucc hxk (by omega))).trans
      (rep_chart k.succ (between_of_bounds k.succ (by change x.1.val ≤ k.val+1; omega)
        hky)).symm
  calc
    developedPre U x = f x.1 := by
      apply congrArg (U x.1)
      apply (certificate A B hh (order A B e x.1)).chart.injective
      exact (rep_chart x.1
        (between_of_bounds x.1 (le_refl _) hij)).symm
    _ = f y.1 := hchain
    _ = developedPre U y := by
      apply congrArg (U y.1)
      apply (certificate A B hh (order A B e y.1)).chart.injective
      exact (rep_chart y.1
        (between_of_bounds y.1 hij (le_refl _))).trans hxy.1

theorem developed_eq_of_cutRelated
    (hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i))
    {x y : TaggedFacePoint A B hh e}
    (hxy : CutRelated A B hh e x y) :
    developedPre U x = developedPre U y := by
  rcases le_total x.1.val y.1.val with hle | hle
  · exact developed_eq_forward U hDev hxy hle
  · exact (developed_eq_forward U hDev (cutRelated_symm A B hh e hxy) hle).symm

def developed
    (hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i)) : CutSurface A B hh e → Q :=
  Quotient.lift (developedPre U)
    (fun _ _ hxy => developed_eq_of_cutRelated U hDev hxy)

theorem developed_continuous
    (hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i)) :
    Continuous (developed U hDev) :=
  (developedPre_continuous U).quotient_lift
    (fun _ _ hxy => developed_eq_of_cutRelated U hDev hxy)

@[simp] theorem developed_faceInclusion
    (hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i))
    (i : Fin (sideCount A B-1+1)) (x : FacePiece A B hh e i) :
    developed U hDev (faceInclusion A B hh e i x) = U i x.val := rfl

end Development

section SeamGeometry
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

lemma originalEdge_lower_endpoint_raw_vertex
    (u v : Side A B) (huv : u ≠ v)
    (ed : OriginalEdge (certificate A B hh u) (certificate A B hh v)) :
    ∃ j : Fin nB,
      (certificate A B hh u).chart ed.aL = pack (lowerLift (B.vertex j)) := by
  let p := (certificate A B hh u).chart ed.aL
  have hbody : p ∈ (halfspaces A B h).body := ed.aL_mem
  have hphys : p ∈ physicalPrismatoid A B h := by
    rwa [halfspaces_body A B hh] at hbody
  rw [← pack_prismatoid A B h] at hphys
  obtain ⟨q,hq,hqp⟩ := hphys
  have hqval : q = unpack p := by
    have he := congrArg unpack hqp
    exact (coordinateEquiv.symm_apply_apply q).symm.trans he
  rw [hqval, mem_prismatoid_iff A B hh] at hq
  have hz : (unpack p).2 / h = 0 := by
    rw [← height_apply]
    exact ed.a_height
  have hs := hq.2
  rw [hz] at hs
  obtain ⟨⟨b,a⟩,⟨hb,ha⟩,hm⟩ := hs
  have hflat : (unpack p).1 = b := by
    simpa [mixLinear] using hm.symm
  have hheight : (unpack p).2 = 0 := (div_eq_zero_iff).mp hz |>.resolve_right hh.ne'
  have hp : p = pack (lowerLift b) := by
    calc
      p = pack (unpack p) := (coordinateEquiv.apply_symm_apply p).symm
      _ = pack (lowerLift b) := by rw [lowerLift]; congr 1; exact Prod.ext hflat hheight
  have huz : sideRow A B h u.val p = 0 := by
    change (halfspaces A B h).row (Sum.inr u) p = 0
    exact (certificate A B hh u).own_zero ed.aL
  have hvz : sideRow A B h v.val p = 0 := by
    change (halfspaces A B h).row (Sum.inr v) p = 0
    dsimp [p]
    rw [ed.match_a]
    exact (certificate A B hh v).own_zero ed.aR
  rw [hp] at huz hvz
  rw [sideRow_lower] at huz hvz
  unfold supportValue at huz hvz
  have humax : ∀ z ∈ B.body, inner ℝ u.val z ≤ inner ℝ u.val b := by
    intro z hzbody
    have hsupp := supportIndex_max B u.val z hzbody
    linarith
  have hvmax : ∀ z ∈ B.body, inner ℝ v.val z ≤ inner ℝ v.val b := by
    intro z hzbody
    have hsupp := supportIndex_max B v.val z hzbody
    linarith
  have hval : u.val ≠ v.val := fun he => huv (Subtype.ext he)
  obtain ⟨_,j,_,hbj,_,_⟩ := distinct_unit_supports_select_vertex B u.val v.val b
    (side_unit A B u) (side_unit A B v) hval hb humax hvmax
  refine ⟨j,?_⟩
  change p = pack (lowerLift (B.vertex j))
  exact hp.trans (congrArg (fun x => pack (lowerLift x)) hbj)

lemma originalEdge_upper_endpoint_raw_vertex
    (u v : Side A B) (huv : u ≠ v)
    (ed : OriginalEdge (certificate A B hh u) (certificate A B hh v)) :
    ∃ i : Fin nA,
      (certificate A B hh u).chart ed.bL = pack (upperLift h (A.vertex i)) := by
  let p := (certificate A B hh u).chart ed.bL
  have hbody : p ∈ (halfspaces A B h).body := ed.bL_mem
  have hphys : p ∈ physicalPrismatoid A B h := by
    rwa [halfspaces_body A B hh] at hbody
  rw [← pack_prismatoid A B h] at hphys
  obtain ⟨q,hq,hqp⟩ := hphys
  have hqval : q = unpack p := by
    have he := congrArg unpack hqp
    exact (coordinateEquiv.symm_apply_apply q).symm.trans he
  rw [hqval, mem_prismatoid_iff A B hh] at hq
  have hz : (unpack p).2 / h = 1 := by
    rw [← height_apply]
    exact ed.b_height
  have hs := hq.2
  rw [hz] at hs
  obtain ⟨⟨b,a⟩,⟨hb,ha⟩,hm⟩ := hs
  have hflat : (unpack p).1 = a := by
    simpa [mixLinear] using hm.symm
  have hheight : (unpack p).2 = h := (div_eq_one_iff_eq hh.ne').mp hz
  have hp : p = pack (upperLift h a) := by
    calc
      p = pack (unpack p) := (coordinateEquiv.apply_symm_apply p).symm
      _ = pack (upperLift h a) := by rw [upperLift]; congr 1; exact Prod.ext hflat hheight
  have huz : sideRow A B h u.val p = 0 := by
    change (halfspaces A B h).row (Sum.inr u) p = 0
    exact (certificate A B hh u).own_zero ed.bL
  have hvz : sideRow A B h v.val p = 0 := by
    change (halfspaces A B h).row (Sum.inr v) p = 0
    dsimp [p]
    rw [ed.match_b]
    exact (certificate A B hh v).own_zero ed.bR
  rw [hp] at huz hvz
  rw [sideRow_upper A B hh] at huz hvz
  unfold supportValue at huz hvz
  have humax : ∀ z ∈ A.body, inner ℝ u.val z ≤ inner ℝ u.val a := by
    intro z hzbody
    have hsupp := supportIndex_max A u.val z hzbody
    linarith
  have hvmax : ∀ z ∈ A.body, inner ℝ v.val z ≤ inner ℝ v.val a := by
    intro z hzbody
    have hsupp := supportIndex_max A v.val z hzbody
    linarith
  have hval : u.val ≠ v.val := fun he => huv (Subtype.ext he)
  obtain ⟨_,i,_,hai,_,_⟩ := distinct_unit_supports_select_vertex A u.val v.val a
    (side_unit A B u) (side_unit A B v) hval ha humax hvmax
  refine ⟨i,?_⟩
  change p = pack (upperLift h (A.vertex i))
  exact hp.trans (congrArg (fun x => pack (upperLift h x)) hai)

lemma raw_vertex_strict_for_next_edge
    {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n) (j : Fin n) :
    0 < supportValue P (unitRay (outwardNormal P.vertex (next j))) -
      inner ℝ (unitRay (outwardNormal P.vertex (next j))) (P.vertex j) := by
  let k := next j
  have hjk : j ≠ k := (next_ne (by have := P.three_le; omega) j).symm
  have hjkk : j ≠ next k := self_ne_next_next P.three_le j
  have hrowne : P.edgeRow k (P.vertex j) ≠ 0 := by
    intro hz
    rcases (P.vertex_edge_eq_iff k j).mp hz with he | he
    · exact hjk he
    · exact hjkk he
  have hrowle := P.body_edge_nonpos k (P.vertex_mem_body j)
  have hrowlt : P.edgeRow k (P.vertex j) < 0 := lt_of_le_of_ne hrowle hrowne
  have htight := (unit_edge_tight P k).1
  rw [← htight]
  let c := ‖outwardNormal P.vertex k‖⁻¹
  have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr (P.outwardNormal_ne_zero k))
  rw [P.edgeRow_apply, inner_sub_right] at hrowlt
  simp only [unitRay, real_inner_smul_left]
  have hm : 0 < c * (inner ℝ (outwardNormal P.vertex k) (P.vertex k) -
      inner ℝ (outwardNormal P.vertex k) (P.vertex j)) := mul_pos hc (by linarith)
  nlinarith

def lowerMissingSide (j : Fin nB) : Side A B :=
  ⟨unitRay (outwardNormal B.vertex (next j)),
    (mem_mergedRays A B _).2 ⟨Sum.inr (next j), rfl⟩⟩

def upperMissingSide (i : Fin nA) : Side A B :=
  ⟨unitRay (outwardNormal A.vertex (next i)),
    (mem_mergedRays A B _).2 ⟨Sum.inl (next i), rfl⟩⟩

lemma lowerMissingSide_positive (j : Fin nB) :
    0 < sideRow A B h (lowerMissingSide A B j).val
      (pack (lowerLift (B.vertex j))) := by
  rw [sideRow_lower]
  exact raw_vertex_strict_for_next_edge B j

lemma upperMissingSide_positive (hh : 0 < h) (i : Fin nA) :
    0 < sideRow A B h (upperMissingSide A B i).val
      (pack (upperLift h (A.vertex i))) := by
  rw [sideRow_upper A B hh]
  exact raw_vertex_strict_for_next_edge A i

def seamLast (e : Fin (sideCount A B)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    FacePiece A B hh e (Fin.last (sideCount A B-1)) :=
  ⟨AffineMap.lineMap (cut A B hh e).aL (cut A B hh e).bL t,
    lineMap_mem_face
      (certificate A B hh (order A B e (Fin.last _))).domain_convex
      (cut A B hh e).aL_mem (cut A B hh e).bL_mem ht⟩

def seamFirst (e : Fin (sideCount A B)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    FacePiece A B hh e 0 :=
  ⟨AffineMap.lineMap (cut A B hh e).aR (cut A B hh e).bR t,
    lineMap_mem_face
      (certificate A B hh (order A B e 0)).domain_convex
      (cut A B hh e).aR_mem (cut A B hh e).bR_mem ht⟩

lemma seam_ambient_eq (e : Fin (sideCount A B))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ambient A B hh e ⟨Fin.last _, seamLast A B hh e t ht⟩ =
      ambient A B hh e ⟨0, seamFirst A B hh e t ht⟩ := by
  let ed := cut A B hh e
  calc
    _ = AffineMap.lineMap
          ((certificate A B hh (order A B e (Fin.last _))).chart ed.aL)
          ((certificate A B hh (order A B e (Fin.last _))).chart ed.bL) t :=
      (certificate A B hh
        (order A B e (Fin.last _))).chart.toAffineMap.apply_lineMap _ _ _
    _ = AffineMap.lineMap
          ((certificate A B hh (order A B e 0)).chart ed.aR)
          ((certificate A B hh (order A B e 0)).chart ed.bR) t := by
      rw [ed.match_a, ed.match_b]
    _ = _ := ((certificate A B hh
      (order A B e 0)).chart.toAffineMap.apply_lineMap _ _ _).symm

lemma exists_side_not_mem_cut_segment (e : Fin (sideCount A B))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ u : Side A B,
      AffineMap.lineMap
        ((certificate A B hh (order A B e (Fin.last _))).chart
          (cut A B hh e).aL)
        ((certificate A B hh (order A B e (Fin.last _))).chart
          (cut A B hh e).bL) t ∉ materialFace A B hh u := by
  let ed := cut A B hh e
  let u := order A B e (Fin.last (sideCount A B-1))
  let v := order A B e 0
  have huv : u ≠ v := fun he => ed.distinct_rows (congrArg Sum.inr he)
  let p0 := (certificate A B hh u).chart ed.aL
  let p1 := (certificate A B hh u).chart ed.bL
  rcases lt_or_eq_of_le ht.2 with ht1 | ht1
  · obtain ⟨j,hp0⟩ := originalEdge_lower_endpoint_raw_vertex A B hh u v huv ed
    let miss := lowerMissingSide A B j
    refine ⟨miss,?_⟩
    have hlow : 0 < sideRow A B h miss.val p0 := by
      dsimp [p0]
      rw [hp0]
      exact lowerMissingSide_positive A B j
    have hp1face : p1 ∈ materialFace A B hh u := ⟨ed.bL,ed.bL_mem,rfl⟩
    have hp1body := ((mem_materialFace A B hh u p1).mp hp1face).1
    have hupp : 0 ≤ sideRow A B h miss.val p1 := by
      exact hp1body (Sum.inr miss)
    have hpositive : 0 < sideRow A B h miss.val
        (AffineMap.lineMap p0 p1 t) := by
      rw [(sideRow A B h miss.val).apply_lineMap, AffineMap.lineMap_apply_ring]
      nlinarith [ht.1]
    intro hmem
    have hz := ((mem_materialFace A B hh miss _).mp hmem).2
    exact hpositive.ne' hz
  · subst t
    obtain ⟨i,hp1⟩ := originalEdge_upper_endpoint_raw_vertex A B hh u v huv ed
    let miss := upperMissingSide A B i
    refine ⟨miss,?_⟩
    intro hmem
    have hz := ((mem_materialFace A B hh miss _).mp hmem).2
    have hpositive : 0 < sideRow A B h miss.val p1 := by
      dsimp [p1]
      rw [hp1]
      exact upperMissingSide_positive A B hh i
    rw [AffineMap.lineMap_apply_one] at hz
    exact hpositive.ne' hz

theorem seam_copies_ne (e : Fin (sideCount A B))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    faceInclusion A B hh e (Fin.last _) (seamLast A B hh e t ht) ≠
      faceInclusion A B hh e 0 (seamFirst A B hh e t ht) := by
  intro heq
  have hrel : CutRelated A B hh e
      ⟨Fin.last _, seamLast A B hh e t ht⟩
      ⟨0, seamFirst A B hh e t ht⟩ :=
    @Quotient.exact _ (cutSetoid A B hh e) _ _ heq
  obtain ⟨u,hu⟩ := exists_side_not_mem_cut_segment A B hh e t ht
  let k : Fin (sideCount A B-1+1) := (order A B e).symm u
  have hk : Between A B (Fin.last _) 0 k := by
    unfold Between
    have hklt := k.isLt
    have hr := three_le_sideCount A B
    simp only [Fin.val_last, Fin.val_zero, min_eq_right (Nat.zero_le _),
      max_eq_left (Nat.zero_le _)]
    omega
  have hmem := hrel.2 k hk
  have horder : order A B e k = u := (order A B e).apply_symm_apply u
  rw [horder] at hmem
  apply hu
  have hmap := (certificate A B hh
    (order A B e (Fin.last _))).chart.toAffineMap.apply_lineMap
      (cut A B hh e).aL (cut A B hh e).bL t
  change (certificate A B hh (order A B e (Fin.last _))).chart
      (AffineMap.lineMap (cut A B hh e).aL (cut A B hh e).bL t) =
    AffineMap.lineMap
      ((certificate A B hh (order A B e (Fin.last _))).chart (cut A B hh e).aL)
      ((certificate A B hh (order A B e (Fin.last _))).chart (cut A B hh e).bL) t at hmap
  simp only [ambient, seamLast] at hmem
  rw [hmap] at hmem
  exact hmem

end SeamGeometry

section Package
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

structure CutSurfaceDevelopment (e : Fin (sideCount A B)) where
  U : (i : Fin (sideCount A B-1+1)) →
    FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Q
  developmentOn : DevelopmentOn
    (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
    (fun i => (certificate A B hh (order A B e i)).domain)
    (fun i => U i)
  safe : Safe
    (fun i => (certificate A B hh (order A B e i)).domain)
    (fun i => U i)
  developedMap : CutSurface A B hh e → Q
  developedMap_continuous : Continuous developedMap
  materialMap : CutSurface A B hh e →
    {p : PhysicalAmbient // p ∈ lateralBoundary (halfspaces A B h)}
  materialMap_continuous : Continuous materialMap
  materialMap_surjective : Function.Surjective materialMap
  face_injective : ∀ i, Function.Injective (faceInclusion A B hh e i)
  developed_face : ∀ i (x : FacePiece A B hh e i),
    developedMap (faceInclusion A B hh e i x) = U i x.val
  material_face : ∀ i (x : FacePiece A B hh e i),
    (materialMap (faceInclusion A B hh e i x)).val =
      (certificate A B hh (order A B e i)).chart x.val
  seam_material_eq : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
    materialMap (faceInclusion A B hh e (Fin.last _) (seamLast A B hh e t ht)) =
      materialMap (faceInclusion A B hh e 0 (seamFirst A B hh e t ht))
  seam_copies_distinct : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
    faceInclusion A B hh e (Fin.last _) (seamLast A B hh e t ht) ≠
      faceInclusion A B hh e 0 (seamFirst A B hh e t ht)
  cut_segment :
    (((certificate A B hh (order A B e (Fin.last _))).chart ''
        (certificate A B hh (order A B e (Fin.last _))).domain) ∩
      ((certificate A B hh (order A B e 0)).chart ''
        (certificate A B hh (order A B e 0)).domain)) =
      AffineMap.lineMap
        ((certificate A B hh (order A B e (Fin.last _))).chart (cut A B hh e).aL)
        ((certificate A B hh (order A B e (Fin.last _))).chart (cut A B hh e).bL) ''
        Icc (0 : ℝ) 1
  lateral_coverage :
    (⋃ i, (certificate A B hh (order A B e i)).chart ''
      (certificate A B hh (order A B e i)).domain) =
      lateralBoundary (halfspaces A B h)

variable [FiniteDimensional ℝ Q]

theorem exists_continuous_cut_surface_unfolding_from_external_nested_band
    (hNest : A.body ⊆ interior B.body)
    (hExternal : ExternalNestedBandTheorem A B hh Q)
    (hdQ : Module.finrank ℝ Q = 2) :
    ∃ e : Fin (sideCount A B), Nonempty (CutSurfaceDevelopment A B hh Q e) := by
  obtain ⟨e,U,hDev,hSafe,_hAllUncut,_hMaterialGlue,hCut,hCover⟩ :=
    recover_full_face_table_from_external_nested_band A B hh Q hNest hExternal hdQ
  refine ⟨e,⟨{
    U := U
    developmentOn := hDev
    safe := hSafe
    developedMap := developed U hDev
    developedMap_continuous := developed_continuous U hDev
    materialMap := materialProjection A B hh e
    materialMap_continuous := materialProjection_continuous A B hh e
    materialMap_surjective := materialProjection_surjective A B hh e
    face_injective := faceInclusion_injective A B hh e
    developed_face := developed_faceInclusion U hDev
    material_face := fun i x => congrArg Subtype.val
      (materialProjection_faceInclusion A B hh e i x)
    seam_material_eq := ?_
    seam_copies_distinct := seam_copies_ne A B hh e
    cut_segment := hCut
    lateral_coverage := hCover }⟩⟩
  intro t ht
  apply Subtype.ext
  exact seam_ambient_eq A B hh e t ht

end Package

end
end CutSurfaceQuotient

#print axioms CutSurfaceQuotient.cutSetoid
#check @CutSurfaceQuotient.CutSurface
#check @CutSurfaceQuotient.cutSetoid
#check @CutSurfaceQuotient.faceInclusion_injective
#print axioms CutSurfaceQuotient.faceInclusion_injective
#check @CutSurfaceQuotient.materialProjection_surjective
#print axioms CutSurfaceQuotient.materialProjection_surjective
#check @CutSurfaceQuotient.developed_eq_of_cutRelated
#print axioms CutSurfaceQuotient.developed_eq_of_cutRelated
#check @CutSurfaceQuotient.developed_continuous
#print axioms CutSurfaceQuotient.developed_continuous
#check @CutSurfaceQuotient.seam_copies_ne
#print axioms CutSurfaceQuotient.seam_copies_ne
#check @CutSurfaceQuotient.exists_continuous_cut_surface_unfolding_from_external_nested_band
#print axioms CutSurfaceQuotient.exists_continuous_cut_surface_unfolding_from_external_nested_band
