import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import VerifiedAgora.tagger

open Complex Set

variable {z w : ℂ} {c : ℝ}


/-%%
This files gathers definitions and basic properties about rectangles.
%%-/

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

lemma symm_re : Rectangle (w.re + z.im * I) (z.re + w.im * I) = Rectangle z w := by
  simp [Rectangle, uIcc_comm]

end Rectangle

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}[RectangleBorder]\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := uIcc z.re w.re ×ℂ {z.im} ∪ {z.re} ×ℂ uIcc z.im w.im ∪ uIcc z.re w.re ×ℂ {w.im} ∪ {w.re} ×ℂ uIcc z.im w.im

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

@[target]
lemma Square_apply (p : ℂ) (cpos : c > 0) :
    Square p c = Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by
  simp only [Square, Rectangle]
  have h1 : (-↑c - ↑c * I + p).re = -c + p.re := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, Complex.I_im]
  have h2 : (↑c + ↑c * I + p).re = c + p.re := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
  have h3 : (-↑c - ↑c * I + p).im = -c + p.im := by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
  have h4 : (↑c + ↑c * I + p).im = c + p.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [h1, h2, h3, h4, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
@[target, simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, mem_reProdIm, equivRealProdCLM_symm_apply, Set.mem_prod,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero,
    sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, Complex.I_im, add_zero]
@[target, simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm := by rfl
/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. Golfed from mathlib4\#9598.-/
@[target]
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    uIcc z.re w.re ×ℂ uIcc z.im w.im = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  apply Set.eq_of_subset_of_subset
  · intro p hp
    rw [mem_reProdIm] at hp
    obtain ⟨hp_re, hp_im⟩ := hp
    rw [← segment_eq_uIcc, segment_eq_image] at hp_im hp_re
    obtain ⟨t, ht, ht_eq⟩ := hp_im
    obtain ⟨s, hs, hs_eq⟩ := hp_re
    simp only [smul_eq_mul] at ht_eq hs_eq
    have hconv := convex_convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w}
    have h_z : z ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      subset_convexHull ℝ _ (mem_insert z _)
    have h_zw : z.re + w.im * I ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      subset_convexHull ℝ _ (by simp)
    have h_wz : w.re + z.im * I ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      subset_convexHull ℝ _ (by simp)
    have h_w : w ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      subset_convexHull ℝ _ (by simp)
    have hq1 : (↑z.re + ↑p.im * I) ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      hconv.segment_subset h_z h_zw (by
        rw [segment_eq_image]; exact ⟨t, ht, Complex.ext
          (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; ring)
          (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; linarith)⟩)
    have hq2 : (↑w.re + ↑p.im * I) ∈ convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} :=
      hconv.segment_subset h_wz h_w (by
        rw [segment_eq_image]; exact ⟨t, ht, Complex.ext
          (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; ring)
          (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; linarith)⟩)
    apply hconv.segment_subset hq1 hq2
    rw [segment_eq_image]
    exact ⟨s, hs, Complex.ext
      (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; linarith)
      (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; ring)⟩
  · apply convexHull_min
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simp [mem_reProdIm, left_mem_uIcc]
      · simp [mem_reProdIm, left_mem_uIcc, right_mem_uIcc]
      · simp [mem_reProdIm, right_mem_uIcc, left_mem_uIcc]
      · simp [mem_reProdIm, right_mem_uIcc]
    · intro x hx y hy a b ha hb hab
      simp only [mem_reProdIm] at *
      simp only [add_re, smul_re, add_im, smul_im]
      exact ⟨(convex_uIcc z.re w.re) hx.1 hy.1 ha hb hab,
             (convex_uIcc z.im w.im) hx.2 hy.2 ha hb hab⟩
/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
@[target]
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  intro p hp
  rw [Rectangle, mem_reProdIm] at hp
  obtain ⟨hp_re, hp_im⟩ := hp
  rw [← segment_eq_uIcc, segment_eq_image] at hp_im hp_re
  obtain ⟨t, ht, ht_eq⟩ := hp_im
  obtain ⟨s, hs, hs_eq⟩ := hp_re
  simp only [smul_eq_mul] at ht_eq hs_eq
  have hq1 : (↑z.re + ↑p.im * I) ∈ U := U_convex.segment_subset hz hzw (by
    rw [segment_eq_image]; exact ⟨t, ht, Complex.ext
      (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; ring)
      (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; linarith)⟩)
  have hq2 : (↑w.re + ↑p.im * I) ∈ U := U_convex.segment_subset hwz hw (by
    rw [segment_eq_image]; exact ⟨t, ht, Complex.ext
      (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; ring)
      (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; linarith)⟩)
  apply U_convex.segment_subset hq1 hq2
  rw [segment_eq_image]
  exact ⟨s, hs, Complex.ext
    (by simp [smul_re, smul_eq_mul, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]; linarith)
    (by simp [smul_im, smul_eq_mul, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]; ring)⟩
@[target]
lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  simp only [Rectangle, mem_reProdIm, Set.uIcc_of_le zRe_lt_wRe, Set.uIcc_of_le zIm_lt_wIm, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
@[target]
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simp only [Square]
  rw [show -↑(-c) - ↑(-c) * I + p = ↑c + ↑c * I + p by push_cast; ring,
      show ↑(-c) + ↑(-c) * I + p = -↑c - ↑c * I + p by push_cast; ring]
  exact Rectangle.symm
@[target]
theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b := by
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact left_mem_Ioo.mp
  · rw [uIoo_of_gt h]; exact right_mem_Ioo.mp
@[target]
theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b := by
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact right_mem_Ioo.mp
  · rw [uIoo_of_gt h]; exact left_mem_Ioo.mp
@[target]
theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h => Set.left_not_mem_uIoo (h ▸ hc)
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h => Set.right_not_mem_uIoo (h ▸ hc)
@[target]
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩
@[target]
lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := by
  simp [Rectangle, mem_reProdIm, Set.right_mem_uIcc]
@[target]
lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  constructor
  · intro h; exact ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  · rintro ⟨hz', hw'⟩ x hx
    simp only [Rectangle, mem_reProdIm] at *
    exact ⟨Set.uIcc_subset_uIcc hz'.1 hw'.1 hx.1, Set.uIcc_subset_uIcc hz'.2 hw'.2 hx.2⟩
@[target]
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff]
  simp only [Rectangle, mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
             Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  exact ⟨⟨Set.mem_uIcc_of_le (by linarith) (by linarith),
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩,
         ⟨Set.mem_uIcc_of_le (by linarith) (by linarith),
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩⟩
@[target]
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [rect_subset_iff]
  simp only [Rectangle, mem_reProdIm] at *
  exact ⟨⟨Set.mem_uIcc_of_le (by linarith) (by linarith),
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩,
         ⟨Set.mem_uIcc_of_le (by linarith) (by linarith),
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩⟩
@[target]
lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro p hp
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  simp only [Rectangle, mem_reProdIm]
  rcases hp with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · exact ⟨h1, h2 ▸ Set.left_mem_uIcc⟩
  · exact ⟨h1 ▸ Set.left_mem_uIcc, h2⟩
  · exact ⟨h1, h2 ▸ Set.right_mem_uIcc⟩
  · exact ⟨h1 ▸ Set.right_mem_uIcc, h2⟩
/-- Note: try using `by simp` for `h`. -/
@[target]
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  rw [Set.disjoint_singleton_right]
  simp only [Rectangle, mem_reProdIm, not_and_or]
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact Set.not_mem_uIcc_of_lt h1 h2
  · right; exact Set.not_mem_uIcc_of_lt h1 h2
  · left; exact Set.not_mem_uIcc_of_gt h1 h2
  · right; exact Set.not_mem_uIcc_of_gt h1 h2
@[target]
lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  obtain ⟨hre_z, hre_w, him_z, him_w⟩ := h
  rw [Set.disjoint_singleton_right]
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff]
  push_neg
  refine ⟨⟨⟨fun _ => him_z, fun hre => absurd hre hre_z⟩, fun _ => him_w⟩, fun hre => absurd hre hre_w⟩
@[target]
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by
  obtain ⟨h01, h12, h23, h01', h12', h23'⟩ := hz
  rw [Set.subset_diff]
  exact ⟨RectSubRect' h01 h12 h23 h01' h12' h23', rectangle_disjoint_singleton hp⟩
@[target]
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by
  obtain ⟨h01, h12, h23, h01', h12', h23'⟩ := hz
  rw [Set.subset_diff]
  exact ⟨(rectangleBorder_subset_rectangle z₁ z₂).trans (RectSubRect' h01 h12 h23 h01' h12' h23'),
         rectangleBorder_disjoint_singleton hp⟩
@[target]
lemma rectangle_mem_nhds_iff {z w p : ℂ} : Rectangle z w ∈ nhds p ↔
    p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  rw [← mem_interior_iff_mem_nhds, Rectangle, interior_reProdIm]
  simp only [uIcc, uIoo, interior_Icc]
@[target]
lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w) := by
  intro y hy
  refine mem_reProdIm.mpr ?_
  constructor
  · simp [Rectangle]
  · simp; exact hy
@[target]
lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w) := by
  intro y hy
  refine mem_reProdIm.mpr ?_
  constructor
  · simp [Rectangle]
  · simp; exact hy
@[target]
lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (Rectangle z w) := by
  intro x hx
  refine mem_reProdIm.mpr ?_
  constructor
  · simp; exact hx
  · simp [Rectangle]
@[target]
lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (Rectangle z w) := by
  intro x hx
  refine mem_reProdIm.mpr ?_
  constructor
  · simp; exact hx
  · simp [Rectangle]
@[target]
lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (RectangleBorder z w) := by
  intro y hy
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; left; right; exact ⟨trivial, hy⟩
@[target]
lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (RectangleBorder z w) := by
  intro y hy
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  right; exact ⟨trivial, hy⟩
@[target]
lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (RectangleBorder z w) := by
  intro x hx
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; left; left; exact ⟨hx, trivial⟩
@[target]
lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (RectangleBorder z w) := by
  intro x hx
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; right; exact ⟨hx, trivial⟩
@[target]
lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w \ {p}) := by
  intro y hy
  refine ⟨mapsTo_rectangle_left_re z w hy, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_left_re z w hy)
@[target]
lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w \ {p}) := by
  intro y hy
  refine ⟨mapsTo_rectangle_right_re z w hy, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_right_re z w hy)
@[target]
lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (Rectangle z w \ {p}) := by
  intro x hx
  refine ⟨mapsTo_rectangle_left_im z w hx, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_left_im z w hx)
@[target]
lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (Rectangle z w \ {p}) := by
  intro x hx
  refine ⟨mapsTo_rectangle_right_im z w hx, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_right_im z w hx)
@[target]
theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ} (hp : Rectangle z w ∈ nhds p) :
    p ∉ RectangleBorder z w := by
  rw [rectangle_mem_nhds_iff] at hp
  simp only [mem_reProdIm] at hp
  obtain ⟨hp_re, hp_im⟩ := hp
  exact Set.disjoint_singleton_right.mp (rectangleBorder_disjoint_singleton
    ⟨Set.ne_left_of_mem_uIoo hp_re, Set.ne_right_of_mem_uIoo hp_re,
     Set.ne_left_of_mem_uIoo hp_im, Set.ne_right_of_mem_uIoo hp_im⟩)
@[target]
lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ nhds p := by
  rw [Square, rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.sub_im,
    Complex.neg_im, Complex.mul_im, mul_one, zero_add, Complex.ofReal_im, add_zero, neg_mul,
    neg_neg, mul_comm, neg_zero, zero_sub]
  rcases lt_or_gt_of_ne hc with hc | hc
  · constructor
    · rw [uIoo_of_gt (by linarith : c + p.re < -c + p.re)]
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · rw [uIoo_of_gt (by linarith : c + p.im < -c + p.im)]
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · constructor
    · rw [uIoo_of_le (by linarith : -c + p.re ≤ c + p.re)]
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · rw [uIoo_of_le (by linarith : -c + p.im ≤ c + p.im)]
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
@[target]
theorem Complex.nhds_hasBasis_square (p : ℂ) : (nhds p).HasBasis (0 < ·) (Square p ·) := by
  constructor
  intro U
  constructor
  · intro hU
    rw [Metric.mem_nhds_iff] at hU
    obtain ⟨ε, hε, hεU⟩ := hU
    refine ⟨ε / 2, by linarith, fun x hx => hεU ?_⟩
    rw [Metric.mem_ball]
    rw [Square_apply p (by linarith : ε / 2 > 0), mem_reProdIm] at hx
    obtain ⟨hx_re, hx_im⟩ := hx
    rw [Set.mem_Icc] at hx_re hx_im
    rw [Complex.dist_eq, Complex.norm_def]
    rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
    apply Real.sqrt_lt_sqrt (normSq_nonneg _)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    have h1 : (x.re - p.re) ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith [hx_re.1, hx_re.2]
    have h2 : (x.im - p.im) ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith [hx_im.1, hx_im.2]
    nlinarith [sq_nonneg (x.re - p.re), sq_nonneg (x.im - p.im)]
  · intro ⟨c, hc, hcU⟩
    exact Filter.mem_of_superset (square_mem_nhds p hc.ne') hcU
@[target]
lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  simp only [Square]
  apply RectSubRect'
  all_goals simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, add_zero]
  all_goals push_cast
  all_goals linarith
@[target]
lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in nhdsWithin 0 (Set.Ioi 0), Square p c ⊆ Rectangle z w := by
  obtain ⟨δ, hδ, hδU⟩ := (Complex.nhds_hasBasis_square p).mem_iff.mp pInRectInterior
  filter_upwards [Ioc_mem_nhdsGT_of_mem (show (0 : ℝ) ∈ Set.Ico 0 δ from ⟨le_refl _, hδ⟩)]
    with c hc
  exact (square_subset_square hc.1 hc.2).trans hδU

-- Test: unique diagnostic lemma to verify submission detection
private lemma _diagnostic_test_session_9182736455 : True := trivial
