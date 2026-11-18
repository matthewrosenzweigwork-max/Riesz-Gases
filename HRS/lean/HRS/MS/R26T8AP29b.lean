import HRS.MS.R26T8AP29a
import HRS.MS.R26T8AT3

/-!
# S8.2 T8A P29 (part b): symmetrization of a pair kernel
`sym F = (F + F^swap)/2` keeps `ContDiff 8`, weighted jets and canonicity, is symmetric, and commutes with `pairA` up to the swap
(`pairA` is swap invariant), so symmetrizing `pairInverseW U R` costs no uniqueness argument.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_p29_sym (F : Euc d → Euc d → ℝ) : Euc d → Euc d → ℝ := fun x y => (1 / 2) * (F x y + F y x)

theorem r26t8a_p29_sym_symm (F : Euc d → Euc d → ℝ) (x y : Euc d) : r26t8a_p29_sym F x y = r26t8a_p29_sym F y x := by
  unfold r26t8a_p29_sym; ring

theorem r26t8a_p29_sym_canonical {mu : Measure (Euc d)} {F : Euc d → Euc d → ℝ} (hF : CanonicalPair mu F) :
    CanonicalPair mu (r26t8a_p29_sym F) := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  refine ⟨fun y => ?_, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · exact ((h1 y).add (h2 y)).const_mul (1 / 2)
  · exact ((h2 x).add (h1 x)).const_mul (1 / 2)
  · show ∫ x, (1 / 2) * (F x y + F y x) ∂mu = 0
    rw [integral_const_mul, integral_add (h1 y) (h2 y), h3 y, h4 y]; ring
  · show ∫ y, (1 / 2) * (F x y + F y x) ∂mu = 0
    rw [integral_const_mul, integral_add (h2 x) (h1 x), h4 x, h3 x]; ring

theorem r26t8a_p29_sym_eq (F : Euc d → Euc d → ℝ) :
    Function.uncurry (r26t8a_p29_sym F) = fun w => (1 / 2 : ℝ) •
      (Function.uncurry F w + (Function.uncurry F ∘ (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d))) w) := by
  funext ⟨x, y⟩
  simp [r26t8a_p29_sym, smul_eq_mul]

theorem r26t8a_p29_sym_contDiff {F : Euc d → Euc d → ℝ} (hF : ContDiff ℝ 8 (Function.uncurry F)) :
    ContDiff ℝ 8 (Function.uncurry (r26t8a_p29_sym F)) := by
  have hsw : ContDiff ℝ 8 (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)) :=
    (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)).contDiff
  have h2 : ContDiff ℝ 8 (Function.uncurry F ∘ (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d))) := hF.comp hsw
  rw [r26t8a_p29_sym_eq]
  exact (hF.add h2).const_smul (1 / 2 : ℝ)

theorem r26t8a_p29_sym_jets {F : Euc d → Euc d → ℝ} {B M : ℝ} (hF : ContDiff ℝ 8 (Function.uncurry F))
    (hb : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry F) (x, y)‖ ≤ B * Phase2S82.pairWeight M x y)
    (j : ℕ) (hj : j ≤ 8) (x y : Euc d) :
    ‖iteratedFDeriv ℝ j (Function.uncurry (r26t8a_p29_sym F)) (x, y)‖ ≤ B * Phase2S82.pairWeight M x y := by
  set e := LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d) with he
  have hF8 : ContDiff ℝ 8 (Function.uncurry F ∘ e) := hF.comp e.contDiff
  have hFj : ContDiffAt ℝ (j : WithTop ℕ∞) (Function.uncurry F) (x, y) :=
    (hF.of_le (by exact_mod_cast hj)).contDiffAt
  have hGj : ContDiffAt ℝ (j : WithTop ℕ∞) (Function.uncurry F ∘ e) (x, y) :=
    (hF8.of_le (by exact_mod_cast hj)).contDiffAt
  rw [r26t8a_p29_sym_eq]
  have e1 : iteratedFDeriv ℝ j (fun w => (1 / 2 : ℝ) • (Function.uncurry F w + (Function.uncurry F ∘ e) w)) (x, y) =
      (1 / 2 : ℝ) • (iteratedFDeriv ℝ j (Function.uncurry F) (x, y) + iteratedFDeriv ℝ j (Function.uncurry F ∘ e) (x, y)) := by
    have h := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := (1 / 2 : ℝ))
      (f := fun w => Function.uncurry F w + (Function.uncurry F ∘ e) w) (x := (x, y)) (hFj.add hGj)
    have hadd : iteratedFDeriv ℝ j (fun w => Function.uncurry F w + (Function.uncurry F ∘ e) w) (x, y) =
        iteratedFDeriv ℝ j (Function.uncurry F) (x, y) + iteratedFDeriv ℝ j (Function.uncurry F ∘ e) (x, y) :=
      iteratedFDeriv_add_apply hFj hGj
    rw [← hadd]; exact h
  rw [e1, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have n2 : ‖iteratedFDeriv ℝ j (Function.uncurry F ∘ e) (x, y)‖ = ‖iteratedFDeriv ℝ j (Function.uncurry F) (y, x)‖ :=
    e.norm_iteratedFDeriv_comp_right (Function.uncurry F) (x, y) j
  have h1 := hb j hj x y
  have h2 := hb j hj y x
  have hsw : Phase2S82.pairWeight M y x = Phase2S82.pairWeight M x y := by
    unfold Phase2S82.pairWeight; ring
  rw [hsw] at h2
  calc 1 / 2 * ‖iteratedFDeriv ℝ j (Function.uncurry F) (x, y) + iteratedFDeriv ℝ j (Function.uncurry F ∘ e) (x, y)‖
      ≤ 1 / 2 * (‖iteratedFDeriv ℝ j (Function.uncurry F) (x, y)‖ + ‖iteratedFDeriv ℝ j (Function.uncurry F ∘ e) (x, y)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ B * Phase2S82.pairWeight M x y := by rw [n2]; linarith

end HRS.MS.R26T8A

end
