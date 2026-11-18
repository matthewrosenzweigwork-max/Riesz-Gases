import HRS.MC.Sec7Vocab
import HRS.Energy.StaticLimitTiltedGauss
import HRS.Energy.StaticLimitCore

/-!
# Packet `s7_S7z_product_case`, helper 1: the product law at `gamma = 0`

`modulatedGibbs g N 0 mu = mu^{(x)N}`, `meanEmpirical (mu^{(x)N}) = mu`, `zetaE = Ssum Ye`, `ellPt .. 0 r x = Ye r mu x`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.S7z

open HRS HRS.Sec7 HRS.StaticLimitAux

variable {d : ℕ}

theorem s7z_gibbs_zero (g : Torus d → ℝ) (N : ℕ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    modulatedGibbs g N 0 μ = Measure.pi fun _ : Fin N => μ := by
  have h1 : gibbsNormalizer g N 0 μ = 1 := by
    unfold gibbsNormalizer
    simp
  unfold modulatedGibbs
  rw [h1]
  simp

theorem s7z_meanEmpirical_pi (N : ℕ) (hN : 1 ≤ N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    meanEmpirical (Measure.pi fun _ : Fin N => μ) = μ := by
  rw [meanEmpirical_eq_sum]
  have : ∀ i : Fin N, (Measure.pi fun _ : Fin N => μ).map (fun X : Config d N => X i) = μ := by
    intro i
    have := Measure.pi_map_eval (μ := fun _ : Fin N => μ) i
    simpa using this
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel, one_smul]
  · exact_mod_cast (by omega : N ≠ 0)
  · exact ENNReal.natCast_ne_top N

theorem s7z_ell_eq (g : Torus d → ℝ) (μ : Measure (Torus d)) (r : ℝ) (x : Torus d) :
    ellPt g μ 0 r x = Ye r μ x := by
  unfold ellPt Ye NegSobolev.ofMeasureDiff
  congr 1
  funext k
  simp [responseRep, projMean, pair, measureRealCoeff_dirac, Torus.measureRealCoeff]

theorem s7z_zeta_eq {r : ℝ} (hm : (d : ℝ) < 2 * r) (N : ℕ) (hN : 1 ≤ N)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (z : Config d N) :
    zetaE r (Measure.pi fun _ : Fin N => μ) z = Ssum (Ye r μ) N z := by
  unfold zetaE Ssum
  rw [s7z_meanEmpirical_pi N hN μ]
  exact etaE_eq_aux hm μ N hN z

end HRS.MC.Sec7.S7z
