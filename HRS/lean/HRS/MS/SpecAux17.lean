import HRS.MS.SpecAux16
import HRS.MS.PsdAux1

/-!
# S8P: positivity and the operator `Q` (S8.7, packet E1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_qf_self_nonneg`: `q(v,v) ≥ 0` (from `riesz_energy_nonneg` with `f = √ρ v`).
`s8p_Q`: the bounded symmetric nonnegative operator on `Lp ℝ 2 volume` with `⟨Q v, w⟩ = q(v,w)`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

theorem s8p_sqrt_memLp {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) :
    MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
  rw [memLp_two_iff_integrable_sq (h.meas.sqrt.aestronglyMeasurable)]
  refine h.int.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.sq_sqrt (h.nonneg x)]

theorem s8p_qf_self_nonneg {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) (hd : 1 ≤ d)
    (v : Lp ℝ 2 (volume : Measure (Euc d))) : 0 ≤ s8p_qf s ρ v v := by
  set f : Euc d → ℝ := fun x => Real.sqrt (ρ x) * v x with hf
  have hfi : Integrable f := (s8p_sqrt_memLp h).integrable_mul (Lp.memLp v)
  have hI : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume) := by
    refine (s8p_qf_integrable h v v).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [s8p_kern, hf]; ring
  have h1 := HRS.MS.Psd.riesz_energy_nonneg hd h.hs0 hfi hI
  have h2 : ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2)
      ∂(volume.prod volume) = ∫ x, ∫ y, rieszKernel d s (x - y) * f x * f y := by
    rw [integral_prod _ hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  unfold s8p_qf
  have h3 : ∫ p : Euc d × Euc d, s8p_kern d s ρ p * (v p.1 * v p.2) ∂(volume.prod volume) =
      ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2) ∂(volume.prod volume) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by simp only [s8p_kern, hf]; ring)
  rw [h3, h2]; exact h1

end HRS.MS.Spec
