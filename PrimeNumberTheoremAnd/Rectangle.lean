import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import VerifiedAgora.tagger

open Complex Set Topology

open scoped Interval

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
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

@[target]
lemma Square_apply (p : ℂ) (cpos : c > 0) :
    Square p c = Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by sorry
@[target, simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t := by
  ext x
  simp [preimage, equivRealProdCLM]
  rfl
@[target, simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm := rfl
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm := rfl
/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. Golfed from mathlib4\#9598.-/
@[t
@[target]
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by sorry
/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
@[target]
lemma rectangle_in_conv
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by sorry
@[target]
lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤
@[target]
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  unfold Square
  simp [neg_neg, Rectangle.symm]
  ring
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by sorry
@[target]
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  unfold Square
  s
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  unfold Square
  simp [neg_neg, Rectangle.symm]
  ring
@[target]
theorem Set.left_not_mem_uIoo {a
  simp [neg_neg, Rectangle.symm]
  ring
@[target]
theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b := by simp 
@[target]

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b := by
  simp [Set.uIoo]
  intro h
  linarith
@[target]

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a := by
  int
  intro h
  simp [Set.uIoo, h] a
  linarith
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c 
  linarith
@[target]
t
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : 
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b := by
  intr
  intro h
  simp [Set.uIoo, h] at hc
  linarith
@[target]
lemm
  simp [Set.uIoo, h] at hc
  linarith
@[target]
lemma left_mem_rect (z w : ℂ) 
lemm
  simp [Set.uIoo, h] at hc
  linarith
@[target]
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w
  simp [Rectangle]
  co
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := by
  simp [Rectangle]
  constructor <;> 
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := by
  simp [Rectangle]
  constructor <;> simp
@[target]
lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := by
  simp [Rectangle]
  const
lemma right_mem_r
  const
lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := by
  simp [Rectangle]
  constructor <;> simp
@[target]
lemma rect_subset
@[target]
lemma rect_subset_iff {z w z' w' : ℂ} :
    Recta
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by sorry
@[target]
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by sorry
@[target]
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectan
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by sorry
@[target]
lemma rectangleBorder_subset_rectangle (z w : ℂ) :
/-- Note: try
/-- Note: try using `by simp` for `h`. -/
@[target]
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by sorry
@[target]
lemma rectangleBorder_disjoint
@[target]
lemma rectangleBorder_disjoint_singleton {z w
lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by sorry
@[target]
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re 
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
   
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.
    Rectangle z₁ z₂ ⊆ Rect
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by sorry
@[target]
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.
    
    (hz : z₀.re ≤ z₁.
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleB
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by sorry
@[target]
lemma rectangle_mem
@[target]
lemma rectangle_mem_nhds_iff {z w p : ℂ} : Rectangle z w ∈ 𝓝 p ↔
    p ∈ (Set.uIoo z
    p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by sorry
@[targ
    p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by sorry
@[target]
lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I
    M
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) := by sorry
@[target]
lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑
lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y *
@[target]
lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re
  
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) := by sorry
@[target]
lemma mapsTo_rectangle
lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.
    MapsTo (fun (x : ℝ) => ↑x + w.im * I)
@[target]
lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I
    MapsTo (fun (y : 
