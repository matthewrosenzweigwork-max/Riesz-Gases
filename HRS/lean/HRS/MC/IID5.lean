import HRS.MC.S7ChaosIIDVocab
import HRS.MC.S7E1Aux3
import HRS.MC.S7E1b

/-!
# iid transfer, part 1: the cutoff kernel coefficient matrix is symmetric Hilbert-Schmidt

For the kernel `hCut d s φ ε` (`ε > 0`) the matrix `s7_kernelCoeff ρ e (hCut d s φ ε)` is symmetric
(Fubini and the symmetry of the kernel) and square summable (Parseval, `e1c_parseval`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.IID

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

theorem kernelCoeff_cut_isSymHS (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e) {ε : ℝ} (hε : 0 < ε) :
    IsSymmetricHS (s7_kernelCoeff ρ e (hCut d s φ ε)) := by
  haveI := isProb_withDensityReal hρ.density
  have hm := E1b.e1b_meas_cut hsd hφ ε
  have hL2 := E1b.e1b_memLp_cut hd hs0 hsd hρ hφ hε
  refine ⟨fun i j => ?_, ?_⟩
  · have hW : MemLp (fun z : Torus d × Torus d => e i z.1 * e j z.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ)) :=
      E0b.e0b_tensor_memLp (he.memLp i) (he.memLp j)
    have hint : Integrable (fun z : Torus d × Torus d => hCut d s φ ε z.1 z.2 * (e i z.1 * e j z.2))
        ((withDensityReal ρ).prod (withDensityReal ρ)) := hL2.integrable_mul hW
    unfold s7_kernelCoeff
    have h1 : ∫ x, ∫ y, hCut d s φ ε x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
        ∫ x, ∫ y, hCut d s φ ε x y * (e i x * e j y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
      simp_rw [mul_assoc]
    rw [h1, integral_integral_swap hint]
    have h2 : ∫ x, ∫ y, hCut d s φ ε x y * e j x * e i y ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
        ∫ x, ∫ y, hCut d s φ ε y x * (e i y * e j x) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [E1b.e1b_symm_cut hsd hφ ε y x]; ring
    rw [h2]
  · exact (E1Aux3.e1c_parseval he hm hL2).summable

end HRS.MC.IID
