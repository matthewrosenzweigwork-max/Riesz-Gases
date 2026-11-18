import HRS.MS.R26T8AP11g
import HRS.MS.R26T8AP11g14
import HRS.MS.R26T8AP11g15
import HRS.MS.R26T8AP11g17

/-!
# S8.2 T8A P12: `r26t8a_nonlocal_canonical` (Pro contract, verbatim)
`pairJ C μ Q x y = (J1 x y - m(Q)(y)) + (J2 x y - m(Q')(x))` with `Q' = Q^T`; P11g (a), (c) for `Q` and `Q'`,
smoothness/decay of `m` (g14, g7 via P11g (b)) and `∫ m dμ = 0` (g17).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_nonlocal_canonical {d : ℕ} (hd : 2 ≤ d) (a beta M A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q : Euc d → Euc d → ℝ) (hQ : CanonicalPair (HRS.Whole.withDensityReal rho) Q)
    (hreg : Conormal 4 1 M (criticalS d - 2) A Q) :
    CanonicalPair (HRS.Whole.withDensityReal rho)
      (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  haveI := s85_isProb hprob
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  set C0 := critCoeff d a beta rho with hC0
  have hμ1 : μ.real Set.univ = 1 := by simp [Measure.real]
  set Q' : Euc d → Euc d → ℝ := fun x y => Q y x with hQ'
  have hreg' : Conormal 4 1 M (criticalS d - 2) A Q' := r26t8a_f24_conormal_swap hchi hreg
  have hcan' : CanonicalPair μ Q' := ⟨hQ.2.1, hQ.1, hQ.2.2.2, hQ.2.2.1⟩
  obtain ⟨Cr, hCr0, hCr⟩ := r26t8a_nonlocal_rows d hd 2 1 a beta M (criticalS d) ha hbeta hM hsd
  have hR := hCr rho hrho Q A hA hreg
  have hR' := hCr rho hrho Q' A hA hreg'
  dsimp only at hR hR'
  obtain ⟨hRa, hRb, hRc⟩ := hR
  obtain ⟨hRa', hRb', hRc'⟩ := hR'
  have hRcan := hRc hQ
  have hRcan' := hRc' hcan'
  -- centring in the weighted form
  have hw1 : ∀ u, ∫ y, rho y * Q u y = 0 := fun u => by
    rw [← r26t8a_f25_wd_integral hprob (Q u)]; exact hQ.2.2.2 u
  have hw2 : ∀ u, ∫ y, rho y * Q' u y = 0 := fun u => by
    rw [← r26t8a_f25_wd_integral hprob (Q' u)]; exact hcan'.2.2.2 u
  have hZ := r26t8a_g17_mean_zero d hd 2 1 a beta M (criticalS d) ha hbeta hM hsd hrho hA hreg hw1
  have hZ' := r26t8a_g17_mean_zero d hd 2 1 a beta M (criticalS d) ha hbeta hM hsd hrho hA hreg' hw2
  -- integrability of the means
  have hmI : ∀ (R : Euc d → Euc d → ℝ), Conormal (2 + 2) 1 M (criticalS d - 2) A R →
      (∀ j ≤ 2, ∀ y, ‖iteratedFDeriv ℝ j (fun z => ∫ x, oneJ C0 (fun u => R u z) x ∂μ) y‖ ≤
        Cr * A * jbracket y ^ (M + 2)) →
      Integrable (fun z => ∫ x, oneJ C0 (fun u => R u z) x ∂μ) μ := by
    intro R hRr hb
    have hcont : Continuous (fun z => ∫ x, oneJ C0 (fun u => R u z) x ∂μ) :=
      (r26t8a_g14_row_smooth d hd 2 1 a beta M (criticalS d) ha hbeta hM hsd hrho R A hA hRr).continuous
    refine Integrable.mono' ((r26t8a_g15_jb_int hd (by linarith : 0 ≤ M + 2) ha hbeta hrho).const_mul (Cr * A))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have := hb 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hmQ : Integrable (fun z => ∫ x, oneJ C0 (fun u => Q u z) x ∂μ) μ := hmI Q hreg hRb
  have hmQ' : Integrable (fun z => ∫ x, oneJ C0 (fun u => Q' u z) x ∂μ) μ := hmI Q' hreg' hRb'
  -- decomposition of `pairJ`
  have hpair : ∀ x y, pairJ C0 μ Q x y =
      (oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) +
        (oneJ C0 (Q x) y - ∫ y', oneJ C0 (Q x) y' ∂μ) := by
    intro x y
    simp [pairJ, HRS.Whole.projMean, HRS.Whole.pair]
  have hmQ'x : ∀ x, ∫ y', oneJ C0 (Q x) y' ∂μ = ∫ z, oneJ C0 (fun u => Q' u x) z ∂μ := fun x => rfl
  have hcQ : ∀ y, Integrable (fun x => oneJ C0 (fun w => Q w y) x) μ := fun y => (hRa y).1
  have hcQ2 : ∀ x, Integrable (fun y => oneJ C0 (fun w => Q w y) x) μ := fun x => (hRcan x).1
  have hJ2a : ∀ x, Integrable (fun y => oneJ C0 (Q x) y) μ := fun x => (hRa' x).1
  have hJ2c : ∀ y, Integrable (fun x => oneJ C0 (Q x) y) μ := fun y => (hRcan' y).1
  have hJ2z : ∀ y, ∫ x, oneJ C0 (Q x) y ∂μ = 0 := fun y => (hRcan' y).2
  have hJ1z : ∀ x, ∫ y, oneJ C0 (fun w => Q w y) x ∂μ = 0 := fun x => (hRcan x).2
  refine ⟨fun y => ?_, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · -- integrability in `x`
    have e : (fun x => pairJ C0 μ Q x y) = fun x =>
        (oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) +
          (oneJ C0 (Q x) y - ∫ z, oneJ C0 (fun u => Q' u x) z ∂μ) := by
      funext x; rw [hpair, hmQ'x]
    rw [e]
    exact ((hcQ y).sub (integrable_const _)).add ((hJ2c y).sub hmQ')
  · have e : pairJ C0 μ Q x = fun y =>
        (oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) +
          (oneJ C0 (Q x) y - ∫ y', oneJ C0 (Q x) y' ∂μ) := by
      funext y; rw [hpair]
    rw [e]
    exact ((hcQ2 x).sub hmQ).add ((hJ2a x).sub (integrable_const _))
  · have e : (fun x => pairJ C0 μ Q x y) = fun x =>
        (oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) +
          (oneJ C0 (Q x) y - ∫ z, oneJ C0 (fun u => Q' u x) z ∂μ) := by
      funext x; rw [hpair, hmQ'x]
    rw [e]
    have i1 : Integrable (fun x => oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) μ :=
      (hcQ y).sub (integrable_const _)
    have i2 : Integrable (fun x => oneJ C0 (Q x) y - ∫ z, oneJ C0 (fun u => Q' u x) z ∂μ) μ :=
      (hJ2c y).sub hmQ'
    rw [integral_add i1 i2, integral_sub (hcQ y) (integrable_const _), integral_sub (hJ2c y) hmQ',
      integral_const, hJ2z y]
    have : ∫ x, ∫ z, oneJ C0 (fun u => Q' u x) z ∂μ ∂μ = 0 := hZ'
    rw [this, hμ1]; simp
  · have e : pairJ C0 μ Q x = fun y =>
        (oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) +
          (oneJ C0 (Q x) y - ∫ y', oneJ C0 (Q x) y' ∂μ) := by
      funext y; rw [hpair]
    rw [e]
    have i1 : Integrable (fun y => oneJ C0 (fun w => Q w y) x - ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ) μ :=
      (hcQ2 x).sub hmQ
    have i2 : Integrable (fun y => oneJ C0 (Q x) y - ∫ y', oneJ C0 (Q x) y' ∂μ) μ :=
      (hJ2a x).sub (integrable_const _)
    rw [integral_add i1 i2, integral_sub (hcQ2 x) hmQ, integral_sub (hJ2a x) (integrable_const _),
      integral_const, hJ1z x]
    have : ∫ y, ∫ x', oneJ C0 (fun w => Q w y) x' ∂μ ∂μ = 0 := hZ
    rw [this, hμ1]; simp

end HRS.MS.R26T8A
