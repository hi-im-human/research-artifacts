import NormalFanSplice

/-!
# Maximal common cells and exhaustive material adjacency

System, 2026-09-19. UNCOMPILED PROOF-SCRIPT DRAFT.

Uses Forge's checked NormalFanSplice at commit-02. No old source is replaced.
The selected A/B support pair has exactly its computed closed gap as its
common normal cell. Among ALL constructed side rays, only its two endpoints
support that pair. Conversely a strict-height contact of two distinct side
faces selects one of these gaps. Thus physical adjacency is characterized by
the gap endpoints without first constructing a second section polygon.

The final lexicographic-successor and rotated-cut packaging are deliberately
separate from this geometric result. See handoff 58 for the whole-cycle job.
-/
open Set
open scoped BigOperators Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice
open EuclideanPrismatoidCoordinates PolyhedralInputBridge

namespace MaximalSupportCells
noncomputable section

section Single
variable {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)

lemma maximizes_pos_smul (w : Plane) (i : Fin n) {c : ℝ} (hc : 0 < c)
    (hm : Maximizes P w i) : Maximizes P (c • w) i := by
  intro x hx
  simpa only [real_inner_smul_left] using
    mul_le_mul_of_nonneg_left (hm x hx) hc.le

lemma singleton_forbids_edgeRay (w : Plane) (i : Fin n)
    (hs : supportFace P w = {P.vertex i}) : ¬ EdgeRay P w := by
  rintro ⟨k,c,hc,he⟩
  have hedge := supportFace_positive_edge_normal P k hc
  rw [← he,hs] at hedge
  have hk : P.vertex k = P.vertex i := by
    have hm : P.vertex k ∈
        AffineMap.lineMap (P.vertex k) (P.vertex (next k)) '' Icc (0 : ℝ) 1 :=
      ⟨0,by norm_num,by simp⟩
    rw [← hedge] at hm
    exact hm
  have hn : P.vertex (next k) = P.vertex i := by
    have hm : P.vertex (next k) ∈
        AffineMap.lineMap (P.vertex k) (P.vertex (next k)) '' Icc (0 : ℝ) 1 :=
      ⟨1,by norm_num,by simp⟩
    rw [← hedge] at hm
    exact hm
  exact P.edge_ne k (hn.trans hk.symm)

lemma strict_vertex_inequality (w : Plane) (i k : Fin n)
    (hs : supportFace P w = {P.vertex i}) (hk : k ≠ i) :
    inner ℝ w (P.vertex k-P.vertex i) < 0 := by
  have hi : P.vertex i ∈ supportFace P w := by rw [hs]; simp
  have hle := hi.2 _ (P.vertex_mem_body k)
  rw [inner_sub_right]
  by_contra hn
  have he : inner ℝ w (P.vertex k) = inner ℝ w (P.vertex i) := by linarith
  have hkm : P.vertex k ∈ supportFace P w := by
    refine ⟨P.vertex_mem_body k,?_⟩
    intro x hx
    rw [he]
    exact hi.2 x hx
  rw [hs] at hkm
  exact hk (raw_vertex_injective P hkm)

/-- At any real scalar, A supports its selected vertex exactly on [0,1]. -/
lemma blend_self_maximizes_iff (i : Fin n) (t : ℝ) :
    Maximizes P (normalBlend P i t) i ↔ t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro hm
    have hd := corner_det_pos P i
    have htwo := (maximizes_iff_two P _ i).mp hm
    rw [blend_back] at htwo
    rw [blend_ahead] at htwo
    constructor <;> nlinarith [htwo.1,htwo.2]
  · exact blend_maximizes P i

/-- An actual edge ray ties the maximizing raw vertex to another raw vertex. -/
lemma edge_ray_other_maximizer (w : Plane) (j : Fin n)
    (hr : EdgeRay P w) (hm : Maximizes P w j) :
    ∃ k : Fin n, k ≠ j ∧ Maximizes P w k := by
  obtain ⟨e,c,hc,he⟩ := hr
  have hs := supportFace_positive_edge_normal P e hc
  rw [← he] at hs
  have heMax : Maximizes P w e := by
    have hx : P.vertex e ∈ supportFace P w := by
      rw [hs]; exact ⟨0,by norm_num,by simp⟩
    exact hx.2
  have hnMax : Maximizes P w (next e) := by
    have hx : P.vertex (next e) ∈ supportFace P w := by
      rw [hs]; exact ⟨1,by norm_num,by simp⟩
    exact hx.2
  by_cases hj : e = j
  · refine ⟨next e,?_,hnMax⟩
    simpa [← hj] using next_ne (le_trans (by norm_num) P.three_le) e
  · exact ⟨e,hj,heMax⟩

/-- Two distinct unit normals cannot support both ends of one real raw edge. -/
lemma unit_eq_of_edge_maxima (u v : Plane) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (k : Fin n) (hu0 : Maximizes P u k) (hu1 : Maximizes P u (next k))
    (hv0 : Maximizes P v k) (hv1 : Maximizes P v (next k)) : u=v := by
  have hun : u ≠ 0 := by intro hz; simpa [hz] using hu
  have hvn : v ≠ 0 := by intro hz; simpa [hz] using hv
  obtain ⟨a,ha,hea⟩ := positive_ray_of_edge_maxima P u hun k hu0 hu1
  obtain ⟨b,hb,heb⟩ := positive_ray_of_edge_maxima P v hvn k hv0 hv1
  have h1 := (unitRay_eq_iff hun (P.outwardNormal_ne_zero k)).mpr ⟨a,ha,hea⟩
  have h2 := (unitRay_eq_iff hvn (P.outwardNormal_ne_zero k)).mpr ⟨b,hb,heb⟩
  simpa [unitRay,hu,hv] using h1.trans h2.symm

/-- If u and v attain their maxima at x, equality for u+v forces equality
for each separately. No strict convexity or precomputed face is assumed. -/
lemma split_sum_support (u v x y : Plane) (hx : x ∈ P.body) (hy : y ∈ P.body)
    (hux : ∀ z ∈ P.body, inner ℝ u z ≤ inner ℝ u x)
    (hvx : ∀ z ∈ P.body, inner ℝ v z ≤ inner ℝ v x)
    (hey : inner ℝ (u+v) y = inner ℝ (u+v) x) :
    (∀ z ∈ P.body, inner ℝ u z ≤ inner ℝ u y) ∧
    (∀ z ∈ P.body, inner ℝ v z ≤ inner ℝ v y) := by
  have hyu := hux y hy
  have hyv := hvx y hy
  rw [inner_add_left,inner_add_left] at hey
  have heu : inner ℝ u y = inner ℝ u x := by linarith
  have hev : inner ℝ v y = inner ℝ v x := by linarith
  constructor
  · intro z hz; rw [heu]; exact hux z hz
  · intro z hz; rw [hev]; exact hvx z hz

/-- The sum of two distinct unit supporting normals selects an actual unique
raw vertex. This bypasses a separate strict-section polygon construction. -/
theorem distinct_unit_supports_select_vertex (u v x : Plane)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : u ≠ v) (hx : x ∈ P.body)
    (hux : ∀ z ∈ P.body, inner ℝ u z ≤ inner ℝ u x)
    (hvx : ∀ z ∈ P.body, inner ℝ v z ≤ inner ℝ v x) :
    u+v ≠ 0 ∧ ∃ i : Fin n, StrictAt P (u+v) i ∧ x=P.vertex i ∧
      Maximizes P u i ∧ Maximizes P v i := by
  have hsum : ∀ z ∈ P.body, inner ℝ (u+v) z ≤ inner ℝ (u+v) x := by
    intro z hz; simp only [inner_add_left]; exact add_le_add (hux z hz) (hvx z hz)
  have hzero : u+v ≠ 0 := by
    intro hz
    have ha := split_sum_support P u v x (P.vertex 0) hx (P.vertex_mem_body 0)
      hux hvx (by simp [hz])
    have hb := split_sum_support P u v x (P.vertex (next 0)) hx
      (P.vertex_mem_body (next 0)) hux hvx (by simp [hz])
    exact huv (unit_eq_of_edge_maxima P u v hu hv 0 ha.1 hb.1 ha.2 hb.2)
  have hnot : ¬ EdgeRay P (u+v) := by
    rintro ⟨k,c,hc,he⟩
    have hedge := supportFace_positive_edge_normal P k hc
    rw [← he] at hedge
    have ha : P.vertex k ∈ supportFace P (u+v) := by
      rw [hedge]; exact ⟨0,by norm_num,by simp⟩
    have hb : P.vertex (next k) ∈ supportFace P (u+v) := by
      rw [hedge]; exact ⟨1,by norm_num,by simp⟩
    have hea := le_antisymm (hsum _ ha.1) (ha.2 x hx)
    have heb := le_antisymm (hsum _ hb.1) (hb.2 x hx)
    have hsa := split_sum_support P u v x _ hx ha.1 hux hvx hea
    have hsb := split_sum_support P u v x _ hx hb.1 hux hvx heb
    exact huv (unit_eq_of_edge_maxima P u v hu hv k hsa.1 hsb.1 hsa.2 hsb.2)
  obtain ⟨i,hi,_⟩ := existsUnique_strict_owner_of_not_edgeRay P (u+v) hzero hnot
  have hxface : x ∈ supportFace P (u+v) := ⟨hx,hsum⟩
  rw [supportFace_of_strict P i _ hi] at hxface
  have hxi : x=P.vertex i := hxface
  exact ⟨hzero,i,hi,hxi,by simpa only [Maximizes,hxi] using hux,
    by simpa only [Maximizes,hxi] using hvx⟩
end Single

section Pair
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

def gapB (g : Gap A B) : Fin nB := Classical.choose (gap_common_support A B g)

lemma gapB_spec (g : Gap A B) :
    (∀ t ∈ Icc (leftKnot A B g) (rightKnot A B g),
      Maximizes A (normalBlend A g.1 t) g.1 ∧
      Maximizes B (normalBlend A g.1 t) (gapB A B g)) ∧
    (∀ t ∈ Ioo (leftKnot A B g) (rightKnot A B g),
      supportFace A (normalBlend A g.1 t) = {A.vertex g.1} ∧
      supportFace B (normalBlend A g.1 t) = {B.vertex (gapB A B g)}) :=
  Classical.choose_spec (gap_common_support A B g)

def mid (g : Gap A B) : ℝ := (leftKnot A B g+rightKnot A B g)/2

lemma mid_mem (g : Gap A B) : mid A B g ∈ Ioo (leftKnot A B g) (rightKnot A B g) := by
  have h := (gap_consecutive A B g).2.2.1
  dsimp [mid]; constructor <;> linarith

lemma inner_knot_edgeRay (i : Fin nA) {t : ℝ}
    (ht : t ∈ knots A B i) (hti : t ∈ Ioo (0 : ℝ) 1) :
    EdgeRay B (normalBlend A i t) := by
  rcases knot_source A B i ht with h0 | h1 | ⟨j,hj,he⟩
  · linarith [hti.1]
  · linarith [hti.2]
  · obtain ⟨_,c,hc,hcEq⟩ := strict_position A i _ hj
    have hcEq' : outwardNormal B.vertex j=c • normalBlend A i t := by
      simpa only [←he] using hcEq
    refine ⟨j,c⁻¹,inv_pos.mpr hc,?_⟩
    rw [hcEq',smul_smul,inv_mul_cancel₀ hc.ne',one_smul]

/-- Each interior endpoint is a real B edge ray, so some OTHER vertex ties
there but loses strictly to the selected gap vertex at the midpoint. -/
lemma boundary_competitor (g : Gap A B) (e : ℝ)
    (he : e=leftKnot A B g ∨ e=rightKnot A B g)
    (he01 : e ∈ Ioo (0 : ℝ) 1) :
    ∃ k : Fin nB, k ≠ gapB A B g ∧
      inner ℝ (normalBlend A g.1 e) (B.vertex k-B.vertex (gapB A B g))=0 ∧
      inner ℝ (normalBlend A g.1 (mid A B g))
        (B.vertex k-B.vertex (gapB A B g)) < 0 := by
  have hcon := gap_consecutive A B g
  have hem : e ∈ knots A B g.1 := he.elim (fun h => by simpa only [h] using hcon.1)
    (fun h => by simpa only [h] using hcon.2.1)
  have hei : e ∈ Icc (leftKnot A B g) (rightKnot A B g) := by
    rcases he with rfl | rfl
    · exact ⟨le_rfl,hcon.2.2.1.le⟩
    · exact ⟨hcon.2.2.1.le,le_rfl⟩
  have hm := ((gapB_spec A B g).1 e hei).2
  obtain ⟨k,hk,hkm⟩ := edge_ray_other_maximizer B _ (gapB A B g)
    (inner_knot_edgeRay A B g.1 hem he01) hm
  refine ⟨k,hk,?_,?_⟩
  · have h1 := hm _ (B.vertex_mem_body k)
    have h2 := hkm _ (B.vertex_mem_body (gapB A B g))
    rw [inner_sub_right]; linarith
  · exact strict_vertex_inequality B _ _ k
      ((gapB_spec A B g).2 _ (mid_mem A B g)).2 hk

lemma blend_zero_affine_identity (i : Fin nA) (d : Plane) (e m t : ℝ)
    (hz : inner ℝ (normalBlend A i e) d=0) :
    (m-e)*inner ℝ (normalBlend A i t) d =
      (t-e)*inner ℝ (normalBlend A i m) d := by
  have he : (m-e)*inner ℝ (normalBlend A i t) d -
      (t-e)*inner ℝ (normalBlend A i m) d =
      (m-t)*inner ℝ (normalBlend A i e) d := by
    simp only [normalBlend,inner_add_left,real_inner_smul_left]
    ring
  rw [hz,mul_zero] at he
  linarith

/-- MAXIMALITY, not only support constancy: the chosen pair's entire scalar
common cell is EXACTLY the computed closed gap, over all real t. -/
theorem maximal_common_cell (g : Gap A B) (t : ℝ) :
    (Maximizes A (normalBlend A g.1 t) g.1 ∧
     Maximizes B (normalBlend A g.1 t) (gapB A B g)) ↔
    t ∈ Icc (leftKnot A B g) (rightKnot A B g) := by
  constructor
  · rintro ⟨ha,hb⟩
    have ht := (blend_self_maximizes_iff A g.1 t).mp ha
    have hcon := gap_consecutive A B g
    have hl := knots_subset_Icc A B g.1 hcon.1
    have hr := knots_subset_Icc A B g.1 hcon.2.1
    have hm := mid_mem A B g
    constructor
    · by_contra hout
      have htl : t < leftKnot A B g := lt_of_not_ge hout
      have hli : leftKnot A B g ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht.1],lt_of_lt_of_le hcon.2.2.1 hr.2⟩
      obtain ⟨k,_,hk0,hkm⟩ := boundary_competitor A B g _ (Or.inl rfl) hli
      have hkt : inner ℝ (normalBlend A g.1 t)
          (B.vertex k-B.vertex (gapB A B g)) ≤ 0 := by
        rw [inner_sub_right]; exact sub_nonpos.mpr (hb _ (B.vertex_mem_body k))
      have he := blend_zero_affine_identity A g.1
        (B.vertex k-B.vertex (gapB A B g)) (leftKnot A B g) (mid A B g) t hk0
      have hn := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hm.1).le hkt
      have hp := mul_pos_of_neg_of_neg (sub_neg.mpr htl) hkm
      linarith
    · by_contra hout
      have hrt : rightKnot A B g < t := lt_of_not_ge hout
      have hri : rightKnot A B g ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt hl.1 hcon.2.2.1,by linarith [ht.2]⟩
      obtain ⟨k,_,hk0,hkm⟩ := boundary_competitor A B g _ (Or.inr rfl) hri
      have hkt : inner ℝ (normalBlend A g.1 t)
          (B.vertex k-B.vertex (gapB A B g)) ≤ 0 := by
        rw [inner_sub_right]; exact sub_nonpos.mpr (hb _ (B.vertex_mem_body k))
      have he := blend_zero_affine_identity A g.1
        (B.vertex k-B.vertex (gapB A B g)) (rightKnot A B g) (mid A B g) t hk0
      have hp := mul_nonneg_of_nonpos_of_nonpos (sub_neg.mpr hm.2).le hkt
      have hn := mul_neg_of_pos_of_neg (sub_pos.mpr hrt) hkm
      linarith
  · exact (gapB_spec A B g).1 t

/-- The same maximality for arbitrary nonzero vectors, not only the scalar
cross-section: positive rescaling is derived inside the proof. -/
theorem common_cell_ray_iff (g : Gap A B) (w : Plane) (hw : w ≠ 0) :
    (Maximizes A w g.1 ∧ Maximizes B w (gapB A B g)) ↔
    ∃ s t : ℝ, 0 < s ∧ t ∈ Icc (leftKnot A B g) (rightKnot A B g) ∧
      w=s • normalBlend A g.1 t := by
  constructor
  · rintro ⟨ha,hb⟩
    obtain ⟨a,b,han,hbn,he⟩ := (normalCone_iff A w g.1).mp ha
    have hs : 0 < a+b := by
      by_contra hn
      have ha0 : a=0 := by linarith
      have hb0 : b=0 := by linarith
      exact hw (by simpa [ha0,hb0] using he)
    let t := b/(a+b)
    have hst : (a+b)*t=b := by dsimp [t]; field_simp [hs.ne']
    have hsa : (a+b)*(1-t)=a := by nlinarith
    have hrep : w=(a+b) • normalBlend A g.1 t := by
      rw [normalBlend,smul_add,smul_smul,smul_smul,hsa,hst]
      exact he
    refine ⟨a+b,t,hs,?_,hrep⟩
    apply (maximal_common_cell A B g t).mp
    exact ⟨maximizes_of_pos_smul A _ g.1 hs (by rw [← hrep]; exact ha),
      maximizes_of_pos_smul B _ (gapB A B g) hs (by rw [← hrep]; exact hb)⟩
  · rintro ⟨s,t,hs,ht,rfl⟩
    have hm := (maximal_common_cell A B g t).mpr ht
    exact ⟨maximizes_pos_smul A _ _ hs hm.1,maximizes_pos_smul B _ _ hs hm.2⟩

lemma knot_ray_mem (i : Fin nA) {t : ℝ} (ht : t ∈ knots A B i) :
    unitRay (normalBlend A i t) ∈ mergedRays A B := by
  rcases knot_source A B i ht with h0 | h1 | ⟨j,hj,he⟩
  · apply (mem_mergedRays A B _).mpr
    exact ⟨Sum.inl (prev i),by simp [h0,normalBlend,inputNormal]⟩
  · apply (mem_mergedRays A B _).mpr
    exact ⟨Sum.inl i,by simp [h1,normalBlend,inputNormal]⟩
  · obtain ⟨_,s,hs,hw⟩ := strict_position A i _ hj
    apply (mem_mergedRays A B _).mpr
    refine ⟨Sum.inr j,?_⟩
    change unitRay (normalBlend A i t)=unitRay (outwardNormal B.vertex j)
    rw [he]
    exact ((unitRay_eq_iff (B.outwardNormal_ne_zero j)
      (normalBlend_ne_zero A i)).mpr ⟨s,hs,hw⟩).symm

def rightSide (g : Gap A B) : Side A B :=
  ⟨unitRay (normalBlend A g.1 (rightKnot A B g)),
    knot_ray_mem A B g.1 (gap_consecutive A B g).2.1⟩

lemma endpointSides_ne (g : Gap A B) : gapSide A B g ≠ rightSide A B g := by
  intro he
  obtain ⟨c,hc,hcEq⟩ := (unitRay_eq_iff
    (normalBlend_ne_zero A g.1) (normalBlend_ne_zero A g.1)).mp (congrArg Subtype.val he)
  have ht := blend_positiveRay_injective A g.1 hc hcEq
  exact (ne_of_lt (gap_consecutive A B g).2.2.1) ht

lemma unitRay_fixed (u : Plane) (hu : ‖u‖=1) : unitRay u=u := by simp [unitRay,hu]

/-- An interior gap direction cannot be any constructed side ray. -/
lemma no_side_ray_inside_gap (g : Gap A B) {t : ℝ}
    (ht : t ∈ Ioo (leftKnot A B g) (rightKnot A B g)) :
    unitRay (normalBlend A g.1 t) ∉ mergedRays A B := by
  intro hm
  obtain ⟨k,hk⟩ := (mem_mergedRays A B _).mp hm
  obtain ⟨c,hc,hcEq⟩ := (unitRay_eq_iff (normalBlend_ne_zero A g.1)
    (inputNormal_ne_zero A B k)).mp hk
  have hs := (gapB_spec A B g).2 t ht
  cases k with
  | inl i => exact singleton_forbids_edgeRay A _ g.1 hs.1 ⟨i,c,hc,hcEq⟩
  | inr j => exact singleton_forbids_edgeRay B _ (gapB A B g) hs.2 ⟨j,c,hc,hcEq⟩

/-- Among ALL merged Side labels, a gap's pair supports exactly its two
boundary sides. This is stronger than just constructing neighboring examples. -/
theorem side_supports_pair_iff (g : Gap A B) (u : Side A B) :
    (Maximizes A u.val g.1 ∧ Maximizes B u.val (gapB A B g)) ↔
    u=gapSide A B g ∨ u=rightSide A B g := by
  constructor
  · intro hm
    obtain ⟨s,t,hs,ht,he⟩ := (common_cell_ray_iff A B g u.val (side_ne_zero A B u)).mp hm
    have hunit : u.val=unitRay (normalBlend A g.1 t) := by
      have hu := (unitRay_eq_iff (side_ne_zero A B u)
        (normalBlend_ne_zero A g.1)).mpr ⟨s,hs,he⟩
      simpa [unitRay,side_unit A B u] using hu
    have hend : t=leftKnot A B g ∨ t=rightKnot A B g := by
      by_contra hn
      push_neg at hn
      have hti : t ∈ Ioo (leftKnot A B g) (rightKnot A B g) :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hn.1),lt_of_le_of_ne ht.2 hn.2⟩
      exact no_side_ray_inside_gap A B g hti (by rw [← hunit]; exact u.property)
    rcases hend with rfl | rfl
    · exact Or.inl (Subtype.ext hunit)
    · exact Or.inr (Subtype.ext hunit)
  · rintro (rfl | rfl)
    all_goals
      have hcon := gap_consecutive A B g
      apply (common_cell_ray_iff A B g _ (side_ne_zero A B _)).mpr
    · exact ⟨‖normalBlend A g.1 (leftKnot A B g)‖⁻¹,leftKnot A B g,
        inv_pos.mpr (norm_pos_iff.mpr (normalBlend_ne_zero A g.1)),
        ⟨le_rfl,hcon.2.2.1.le⟩,rfl⟩
    · exact ⟨‖normalBlend A g.1 (rightKnot A B g)‖⁻¹,rightKnot A B g,
        inv_pos.mpr (norm_pos_iff.mpr (normalBlend_ne_zero A g.1)),
        ⟨hcon.2.2.1.le,le_rfl⟩,rfl⟩

/-- The common support pair cannot disappear and later reappear as another
emitted open gap. This also deals with more than one insertion per A block. -/
theorem supportPair_injective :
    Function.Injective (fun g : Gap A B => (g.1,gapB A B g)) := by
  intro g q he
  have hi : g.1=q.1 := congrArg Prod.fst he
  have hj : gapB A B g=gapB A B q := congrArg Prod.snd he
  have hg := (gapB_spec A B g).1 (leftKnot A B g)
    ⟨le_rfl,(gap_consecutive A B g).2.2.1.le⟩
  have hq := (gapB_spec A B q).1 (leftKnot A B q)
    ⟨le_rfl,(gap_consecutive A B q).2.2.1.le⟩
  have hqg : leftKnot A B g ∈ Icc (leftKnot A B q) (rightKnot A B q) := by
    apply (maximal_common_cell A B q _).mp
    simpa [← hi,← hj] using hg
  have hgq : leftKnot A B q ∈ Icc (leftKnot A B g) (rightKnot A B g) := by
    apply (maximal_common_cell A B g _).mp
    simpa [hi,hj] using hq
  exact gap_eq_of_owner_left_eq A B hi (le_antisymm hgq.1 hqg.1)

/-- Every scalar which is not a knot lies strictly inside an actually sorted
gap. This is finite predecessor search, not a coverage premise. -/
lemma exists_gap_at (i : Fin nA) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnt : t ∉ knots A B i) :
    ∃ g : Gap A B, g.1=i ∧ t ∈ Ioo (leftKnot A B g) (rightKnot A B g) := by
  let S := (knots A B i).filter (fun x => x<t)
  have hS : S.Nonempty := ⟨0,by simp [S,knots,ht.1]⟩
  let l := S.max' hS
  have hlS : l ∈ S := S.max'_mem hS
  have hlK : l ∈ knots A B i := (Finset.mem_filter.mp hlS).1
  have hlt : l<t := (Finset.mem_filter.mp hlS).2
  let kl := (orderedKnots A B i).symm ⟨l,hlK⟩
  let k1 := (orderedKnots A B i).symm ⟨1,by simp [knots]⟩
  have hkl : orderedKnots A B i kl = ⟨l,hlK⟩ :=
    (orderedKnots A B i).apply_symm_apply _
  have hk1 : orderedKnots A B i k1 = ⟨1,by simp [knots]⟩ :=
    (orderedKnots A B i).apply_symm_apply _
  have hl1 : kl<k1 := by
    apply (orderedKnots A B i).lt_iff_lt.mp
    rw [hkl,hk1]
    exact hlt.trans ht.2
  have hbound : kl.val < (knots A B i).card-1 := by
    have hk := k1.isLt
    have hklt : kl.val<k1.val := hl1
    omega
  let g : Gap A B := ⟨i,⟨kl.val,hbound⟩⟩
  have hgl : leftKnot A B g=l := by
    let hc : (knots A B i).card-1+1=(knots A B i).card :=
      Nat.sub_add_cancel (one_lt_knots_card A B i).le
    have hind : Fin.cast hc g.2.castSucc=kl := Fin.ext rfl
    unfold leftKnot
    dsimp only [g]
    rw [hind,hkl]
  refine ⟨g,rfl,by rwa [hgl],?_⟩
  by_contra hn
  have hrle : rightKnot A B g≤t := le_of_not_gt hn
  have hrK := (gap_consecutive A B g).2.1
  have hrne : rightKnot A B g≠t := by
    intro he; apply hnt; simpa [he] using hrK
  have hrt : rightKnot A B g<t := lt_of_le_of_ne hrle hrne
  have hrS : rightKnot A B g ∈ S := Finset.mem_filter.mpr ⟨hrK,hrt⟩
  have hrmax : rightKnot A B g≤l := S.le_max' _ hrS
  have hrl := (gap_consecutive A B g).2.2.1
  rw [hgl] at hrl
  linarith

/-- Independently defined adjacency: two distinct material faces meet at a
strictly interior physical height. No list/successor is in this definition. -/
def MaterialAdjacent {h : ℝ} (hh : 0<h) (u v : Side A B) : Prop :=
  u≠v ∧ ∃ p : PhysicalAmbient,
    p ∈ materialFace A B hh u ∧ p ∈ materialFace A B hh v ∧
    (unpack p).2/h ∈ Ioo (0 : ℝ) 1

def mixedPoint (h t : ℝ) (g : Gap A B) : PhysicalAmbient :=
  pack ((1-t) • lowerLift (B.vertex (gapB A B g)) + t • upperLift h (A.vertex g.1))

lemma mixedPoint_height {h : ℝ} (hh : 0<h) (t : ℝ) (g : Gap A B) :
    (unpack (mixedPoint A B h t g)).2/h=t := by
  change (unpack (pack _)).2/h=t
  simp only [pack,unpack,lowerLift,upperLift]
  change ((1-t)*0+t*h)/h=t
  field_simp [hh.ne']
  <;> ring

lemma mixedPoint_in_face {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (g : Gap A B) (u : Side A B)
    (hu : Maximizes A u.val g.1 ∧ Maximizes B u.val (gapB A B g)) :
    mixedPoint A B h t g ∈ materialFace A B hh u := by
  apply (mem_materialFace A B hh u _).mpr
  constructor
  · rw [halfspaces_body A B hh,← pack_prismatoid A B h]
    refine ⟨_,?_,rfl⟩
    exact (prismatoid_convex A B h)
      (lower_mem_prismatoid A B h (B.vertex_mem_body (gapB A B g)))
      (upper_mem_prismatoid A B h (A.vertex_mem_body g.1))
      (by linarith [ht.2]) ht.1 (by ring)
  · rw [sideRow_apply,mixedPoint_height A B hh t g]
    change rowBound A B t u.val-inner ℝ u.val (unpack (pack _)).1=0
    simp only [pack,unpack,lowerLift,upperLift]
    change rowBound A B t u.val-
      inner ℝ u.val ((1-t) • B.vertex (gapB A B g)+t • A.vertex g.1)=0
    unfold rowBound
    rw [supportValue_at B _ _ hu.2,supportValue_at A _ _ hu.1]
    simp only [inner_add_right,inner_smul_right]
    ring

lemma gap_endpoints_materialAdjacent {h : ℝ} (hh : 0<h) (g : Gap A B) :
    MaterialAdjacent A B hh (gapSide A B g) (rightSide A B g) := by
  refine ⟨endpointSides_ne A B g,mixedPoint A B h (1/2) g,?_,?_,?_⟩
  · exact mixedPoint_in_face A B hh (by norm_num) g _
      ((side_supports_pair_iff A B g _).mpr (Or.inl rfl))
  · exact mixedPoint_in_face A B hh (by norm_num) g _
      ((side_supports_pair_iff A B g _).mpr (Or.inr rfl))
  · rw [mixedPoint_height A B hh]; norm_num

/-- Every actual strict-height contact selects one of the computed open cells.
The sum-normal argument rules out boundary-only/singleton common cells. -/
theorem contact_selects_gap {h : ℝ} (hh : 0<h) (u v : Side A B) (huv : u≠v)
    (p : PhysicalAmbient) (hpu : p ∈ materialFace A B hh u)
    (hpv : p ∈ materialFace A B hh v) (ht : (unpack p).2/h ∈ Ioo (0 : ℝ) 1) :
    ∃ g : Gap A B,
      (Maximizes A u.val g.1 ∧ Maximizes B u.val (gapB A B g)) ∧
      (Maximizes A v.val g.1 ∧ Maximizes B v.val (gapB A B g)) := by
  obtain ⟨hbody,huz⟩ := (mem_materialFace A B hh u p).mp hpu
  obtain ⟨_,hvz⟩ := (mem_materialFace A B hh v p).mp hpv
  have hphys : p ∈ physicalPrismatoid A B h := by
    rwa [halfspaces_body A B hh] at hbody
  rw [←pack_prismatoid A B h] at hphys
  obtain ⟨q,hq,hqp⟩ := hphys
  have hqval : q=unpack p := by
    have he := congrArg unpack hqp
    exact (coordinateEquiv.symm_apply_apply q).symm.trans he
  rw [hqval,mem_prismatoid_iff A B hh] at hq
  obtain ⟨⟨b,a⟩,⟨hb,ha⟩,hm⟩ := hq.2
  have hzu := tight_mixture A B hh u.val p b a hb ha ht hm huz
  have hzv := tight_mixture A B hh v.val p b a hb ha ht hm hvz
  rw [sideRow_lower,sideRow_upper A B hh] at hzu hzv
  have hua : ∀ z ∈ A.body, inner ℝ u.val z ≤ inner ℝ u.val a := by
    intro z hz
    have ht' := supportIndex_max A u.val z hz
    have hs := hzu.2
    unfold supportValue at hs
    linarith
  have hva : ∀ z ∈ A.body, inner ℝ v.val z ≤ inner ℝ v.val a := by
    intro z hz
    have ht' := supportIndex_max A v.val z hz
    have hs := hzv.2
    unfold supportValue at hs
    linarith
  have hub : ∀ z ∈ B.body, inner ℝ u.val z ≤ inner ℝ u.val b := by
    intro z hz
    have ht' := supportIndex_max B u.val z hz
    have hs := hzu.1
    unfold supportValue at hs
    linarith
  have hvb : ∀ z ∈ B.body, inner ℝ v.val z ≤ inner ℝ v.val b := by
    intro z hz
    have ht' := supportIndex_max B v.val z hz
    have hs := hzv.1
    unfold supportValue at hs
    linarith
  have hval : u.val≠v.val := fun he => huv (Subtype.ext he)
  obtain ⟨hw,i,hi,hai,hui,hvi⟩ := distinct_unit_supports_select_vertex A u.val v.val a
    (side_unit A B u) (side_unit A B v) hval ha hua hva
  obtain ⟨_,j,hj,hbj,huj,hvj⟩ := distinct_unit_supports_select_vertex B u.val v.val b
    (side_unit A B u) (side_unit A B v) hval hb hub hvb
  let w := u.val+v.val
  obtain ⟨htpos,s,hs,he⟩ := strict_position A i w hi
  let t := position A i w
  have hnotB : ¬ EdgeRay B w := not_edgeRay_of_strict B w j hj
  have hnotq : ¬ EdgeRay B (normalBlend A i t) := by
    rintro ⟨k,c,hc,hcEq⟩
    apply hnotB
    refine ⟨k,s*c,mul_pos hs hc,?_⟩
    rw [he,hcEq,smul_smul]
  have hnotk : t ∉ knots A B i := fun htk =>
    hnotq (inner_knot_edgeRay A B i htk htpos)
  obtain ⟨g,hgi,hgt⟩ := exists_gap_at A B i htpos hnotk
  have hjmax : Maximizes B (normalBlend A i t) j := by
    apply maximizes_of_pos_smul B _ j hs
    rw [←he]
    exact (maximizes_iff_two B w j).mpr ⟨hj.1.le,hj.2.le⟩
  have hjface : B.vertex j ∈ supportFace B (normalBlend A g.1 t) := by
    refine ⟨B.vertex_mem_body j,?_⟩
    simpa only [Maximizes,hgi] using hjmax
  rw [((gapB_spec A B g).2 t hgt).2] at hjface
  have hjg : j=gapB A B g := raw_vertex_injective B hjface
  refine ⟨g,?_,?_⟩
  · exact ⟨by simpa [hgi] using hui,by simpa [←hjg] using huj⟩
  · exact ⟨by simpa [hgi] using hvi,by simpa [←hjg] using hvj⟩

/-- WHOLE GEOMETRIC ENDPOINT: independently defined physical adjacency is
EXACTLY an unordered endpoint pair of one internally computed gap.
No adjacency, incidence, endpoint, or cycle correctness is an input. -/
theorem materialAdjacency_iff_gapEndpoints {h : ℝ} (hh : 0<h) (u v : Side A B) :
    MaterialAdjacent A B hh u v ↔
    ∃ g : Gap A B,
      (u=gapSide A B g ∧ v=rightSide A B g) ∨
      (v=gapSide A B g ∧ u=rightSide A B g) := by
  constructor
  · rintro ⟨huv,p,hpu,hpv,ht⟩
    obtain ⟨g,hug,hvg⟩ := contact_selects_gap A B hh u v huv p hpu hpv ht
    have hu := (side_supports_pair_iff A B g u).mp hug
    have hv := (side_supports_pair_iff A B g v).mp hvg
    refine ⟨g,?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact False.elim (huv (hu.trans hv.symm))
    · exact Or.inl ⟨hu,hv⟩
    · exact Or.inr ⟨hv,hu⟩
    · exact False.elim (huv (hu.trans hv.symm))
  · rintro ⟨g,hg⟩
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact gap_endpoints_materialAdjacent A B hh g
    · obtain ⟨hne,p,ha,hb,ht⟩ := gap_endpoints_materialAdjacent A B hh g
      exact ⟨Ne.symm hne,p,hb,ha,ht⟩

/-- Every displayed gap edge is a real OriginalEdge, constructed from its
mid-height point using the previously checked certificate adapter. -/
def gapOriginalEdge {h : ℝ} (hh : 0<h) (g : Gap A B) :
    OriginalEdge (certificate A B hh (gapSide A B g))
      (certificate A B hh (rightSide A B g)) :=
  Classical.choice (by
    obtain ⟨hne,p,hpu,hpv,ht⟩ := gap_endpoints_materialAdjacent A B hh g
    exact originalEdge_of_shared_interior A B hh _ _ hne p hpu hpv ht)

/-- No additional certified original edge can hide outside the gap list.
This quantifies over ANY OriginalEdge between the constructed certificates. -/
theorem arbitraryOriginalEdge_covered {h : ℝ} (hh : 0<h) (u v : Side A B)
    (ed : OriginalEdge (certificate A B hh u) (certificate A B hh v)) :
    ∃ g : Gap A B,
      (u=gapSide A B g ∧ v=rightSide A B g) ∨
      (v=gapSide A B g ∧ u=rightSide A B g) := by
  apply (materialAdjacency_iff_gapEndpoints A B hh u v).mp
  have huv : u≠v := by intro he; subst v; exact ed.distinct_rows rfl
  let lo := (certificate A B hh u).chart ed.aL
  let hi := (certificate A B hh u).chart ed.bL
  let p := AffineMap.lineMap lo hi (1/2 : ℝ)
  have hp : p ∈ materialFace A B hh u ∩ materialFace A B hh v := by
    rw [materialFace,materialFace,ed.common_material_edge (faceSpace_finrank A B h u)]
    exact ⟨1/2,by norm_num,rfl⟩
  have hheight : heightLinear h p=(1/2 : ℝ) := by
    have hlo := ed.a_height
    have hhi := ed.b_height
    change heightLinear h lo=0 at hlo
    change heightLinear h hi=1 at hhi
    exact TrimmedFacetWitnesses.height_lineMap (heightLinear h).toAffineMap hlo hhi (1/2)
  refine ⟨huv,p,hp.1,hp.2,?_⟩
  rw [←height_apply,hheight]
  norm_num

end Pair
end
end MaximalSupportCells

#print axioms MaximalSupportCells.distinct_unit_supports_select_vertex
#print axioms MaximalSupportCells.maximal_common_cell
#print axioms MaximalSupportCells.common_cell_ray_iff
#print axioms MaximalSupportCells.side_supports_pair_iff
#print axioms MaximalSupportCells.supportPair_injective
#print axioms MaximalSupportCells.materialAdjacency_iff_gapEndpoints
#print axioms MaximalSupportCells.gapOriginalEdge
#print axioms MaximalSupportCells.arbitraryOriginalEdge_covered
#check @MaximalSupportCells.maximal_common_cell
#check @MaximalSupportCells.materialAdjacency_iff_gapEndpoints
#check @MaximalSupportCells.arbitraryOriginalEdge_covered
