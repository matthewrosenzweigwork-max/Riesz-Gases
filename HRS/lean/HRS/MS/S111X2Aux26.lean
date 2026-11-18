import Mathlib

/-!
# S11.1 X2, packet E07 (part 1): parametric time integrals of `C²` families

For a family `g u` of `C²` functions on a normed space `X` whose derivatives of order `≤ 2` are bounded and jointly
continuous in `(u,x)`, `x ↦ ∫ u in a..b, g u x` is `C²`, and its first two derivatives are the integrals of the
derivatives of `g u`.  Also continuity of these integrals in the (upper) limit and the point.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.S111X2

section Leibniz

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Differentiation under an interval integral, for a family continuous in `(u,x)` with continuous bounded
derivatives. -/
theorem s111x2_leibniz1 (g : ℝ → X → F) (a b B : ℝ) (hdiff : ∀ u, Differentiable ℝ (g u))
    (hc : Continuous (fun p : ℝ × X => g p.1 p.2))
    (hc' : Continuous (fun p : ℝ × X => fderiv ℝ (g p.1) p.2))
    (hB : ∀ u x, ‖fderiv ℝ (g u) x‖ ≤ B) (x : X) :
    HasFDerivAt (fun y => ∫ u in a..b, g u y) (∫ u in a..b, fderiv ℝ (g u) x) x := by
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (s := univ)
    (bound := fun _ => B) (F := fun y u => g u y) (F' := fun y u => fderiv ℝ (g u) y)
    univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y =>
      ((hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (hc'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun u _ y _ => hB u y
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun u _ y _ => (hdiff u y).hasFDerivAt

/-- Continuity of the integral in the upper limit and the point. -/
theorem s111x2_cont_param (g : ℝ → X → F) (hc : Continuous (fun p : ℝ × X => g p.1 p.2)) (a : ℝ) :
    Continuous (fun p : ℝ × X => ∫ u in a..p.1, g u p.2) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun q u => g u q.2) (X := ℝ × X) (μ := volume) (a₀ := a) (s := fun q => q.1)
    (hc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))) continuous_fst

theorem s111x2_cont_param' (g : ℝ → X → F) (hc : Continuous (fun p : ℝ × X => g p.1 p.2)) (a b : ℝ) :
    Continuous (fun x : X => ∫ u in a..b, g u x) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x u => g u x) (μ := volume) (by exact hc.comp (continuous_snd.prodMk continuous_fst)) a b

theorem s111x2_intInt_param (g : ℝ → X → F) (hc : Continuous (fun p : ℝ × X => g p.1 p.2)) (x : X) (a b : ℝ) :
    IntervalIntegrable (fun u => g u x) volume a b :=
  (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _

end Leibniz

/-- A family of `C²` functions with bounded, jointly continuous derivatives of order `≤ 2`. -/
structure C2Fam {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (g : ℝ → X → ℝ) (B1 B2 : ℝ) : Prop where
  smooth : ∀ u, ContDiff ℝ 2 (g u)
  b1 : ∀ u x, ‖fderiv ℝ (g u) x‖ ≤ B1
  b2 : ∀ u x, ‖fderiv ℝ (fderiv ℝ (g u)) x‖ ≤ B2
  c0 : Continuous (fun p : ℝ × X => g p.1 p.2)
  c1 : Continuous (fun p : ℝ × X => fderiv ℝ (g p.1) p.2)
  c2 : Continuous (fun p : ℝ × X => fderiv ℝ (fderiv ℝ (g p.1)) p.2)

section C2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {g : ℝ → X → ℝ} {B1 B2 : ℝ}

theorem C2Fam.hasFDerivAt (hg : C2Fam g B1 B2) (a b : ℝ) (x : X) :
    HasFDerivAt (fun y => ∫ u in a..b, g u y) (∫ u in a..b, fderiv ℝ (g u) x) x :=
  s111x2_leibniz1 g a b B1 (fun u => (hg.smooth u).differentiable (by norm_num)) hg.c0 hg.c1 hg.b1 x

theorem C2Fam.hasFDerivAt₂ (hg : C2Fam g B1 B2) (a b : ℝ) (x : X) :
    HasFDerivAt (fun y => ∫ u in a..b, fderiv ℝ (g u) y) (∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) x) x :=
  s111x2_leibniz1 (fun u => fderiv ℝ (g u)) a b B2
    (fun u => ((hg.smooth u).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) hg.c1 hg.c2
    hg.b2 x

theorem C2Fam.fderiv_eq (hg : C2Fam g B1 B2) (a b : ℝ) :
    fderiv ℝ (fun y => ∫ u in a..b, g u y) = fun x => ∫ u in a..b, fderiv ℝ (g u) x :=
  funext fun x => (hg.hasFDerivAt a b x).fderiv

theorem C2Fam.fderiv₂_eq (hg : C2Fam g B1 B2) (a b : ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ (fun y => ∫ u in a..b, g u y)) x = ∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) x := by
  rw [hg.fderiv_eq]; exact (hg.hasFDerivAt₂ a b x).fderiv

theorem C2Fam.contDiff (hg : C2Fam g B1 B2) (a b : ℝ) : ContDiff ℝ 2 (fun y => ∫ u in a..b, g u y) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (hg.hasFDerivAt a b x).differentiableAt, by simp, ?_⟩
  rw [hg.fderiv_eq, contDiff_one_iff_fderiv]
  refine ⟨fun x => (hg.hasFDerivAt₂ a b x).differentiableAt, ?_⟩
  have : fderiv ℝ (fun y => ∫ u in a..b, fderiv ℝ (g u) y) = fun x => ∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) x :=
    funext fun x => (hg.hasFDerivAt₂ a b x).fderiv
  rw [this]
  exact s111x2_cont_param' (fun u => fderiv ℝ (fderiv ℝ (g u))) hg.c2 a b

end C2

end HRS.MS.S111X2
