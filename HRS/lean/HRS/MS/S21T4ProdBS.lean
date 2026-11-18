import HRS.MS.S21T4ProdBR
import HRS.MS.R2ChaosAux3

/-!
# S13: finite-rank quadratic Gaussian polynomial on every product probability space

No infinite orthonormal basis is assumed. The finite-rank polynomial is formed
using the actual first-chaos field and retains nontrivial atomic laws.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_L2
    (I : ProductGaussian μ) {r : ℕ}
    (u : Fin r → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin r → Fin r → ℝ) :
    MemLp (fun ω : I.Ω => (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) 2 I.P := by
  letI := I.mΩ
  letI := I.prob
  have hη := s21t4_product_eta_bundle I
  have hz : S94GFam I.P (fun i ω => I.η (u i) ω) :=
    s21l_gfam hη hu
  have hzz : ∀ i j : Fin r, MemLp
      (fun ω : I.Ω => I.η (u i) ω * I.η (u j) ω) 2 I.P := by
    intro i j
    have hmeas := ((hη.memLp (u i) (hu i)).aestronglyMeasurable.mul
      (hη.memLp (u j) (hu j)).aestronglyMeasurable)
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    have hi := hz.integrable_sq_mul_sq (Pi.single i 1) (Pi.single j 1)
    convert hi using 1
    funext ω
    simp [s94lin, Pi.single_apply]
    ring
  have hterm : ∀ i j : Fin r, MemLp
      (fun ω : I.Ω => c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) 2 I.P := by
    intro i j
    exact ((hzz i j).sub (memLp_const _)).const_mul _
  have hs : MemLp (fun ω : I.Ω =>
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) 2 I.P :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hterm i j
  exact hs.const_mul _

end HRS.MS.R26T3
