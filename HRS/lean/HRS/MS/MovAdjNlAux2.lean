import HRS.MS.MovAdjNlAux1

/-!
# S6.7 nonlinear row, package A, packet N1 (part 2): the weak Volterra identity

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67a_gdv`: the right derivative of `g(σ) = ⟨f_{r+σ} √ρ, T(σ) v₀⟩` at `σ ∈ (0,t-r)` is `-k(σ)`,
  `k(σ) = ∫ (R_{r+σ} f_{r+σ}) √ρ (T(σ) v₀)` (`R = s67aR`); uses the stationary duality identity `s67_duality`.
* `s67a_volterra`: `∫ f_r √ρ v₀ = ∫ φ √ρ T(t-r) v₀ + ∫_0^{t-r} k` (FTC for right derivatives with integrable derivative).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63 HRS.MS.MovAdj

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

set_option maxHeartbeats 1600000 in
theorem s67a_gdv (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {ρt : ℝ → Euc d → ℝ} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρt) t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (t - r)) :
    HasDerivWithinAt (fun τ => inner ℝ ((s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
      ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (-(∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x))) (Set.Ici σ) σ := by
  have hσ0 : 0 ≤ σ := hσ.1.le
  have hr1 : 0 < r + σ := by linarith [hr.1, hσ.1]
  have hr2 : r + σ < t := by linarith [hσ.2]
  have hr'mem : r + σ ∈ Set.Icc (0 : ℝ) t := ⟨hr1.le, hr2.le⟩
  obtain ⟨φ', hφ', w, hw, hwd⟩ := s67_T_deriv H ψ0 hψ0 hv hσ0
  obtain ⟨a', ha', ha'def, hAd⟩ := s67a_hdv H hf ht hr hgL hσ
  have hb : HasDerivWithinAt (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) (Set.Ici σ) σ := by
    have h := (Submodule.subtypeL (MovL2Zero ρ)).hasFDerivAt.comp_hasDerivWithinAt σ hwd
    exact h.congr_deriv (by simp)
  have hpair := hAd.inner ℝ hb
  have hclσ : s67clamp r t σ = r + σ := s67clamp_eq hr1.le hr2.le
  have hu : MemCb 2 (f (r + σ)) := hf.isC12TestRd.memCb hr'mem
  have hdual := s67_duality H hu φ' (r + σ)
  obtain ⟨Bf, hBf0, hBgen, -⟩ := s67_time_lip hf
  obtain ⟨B0, hB00, hB0⟩ := s67a_L0_growth H hu (r + σ)
  have I1 : Integrable (fun x => generatorW ((quadraticGradientDyn d s q β).coeff ρt) (r + σ) (f (r + σ)) x *
      (Real.sqrt (ρ x) * φ' x)) :=
    s67a_int_lin H (s67_gen_cont hf hr'mem).aestronglyMeasurable (hBgen _ hr'mem) φ'
  have I2 : Integrable (fun x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (r + σ)
      (f (r + σ)) x * (Real.sqrt (ρ x) * φ' x)) :=
    s67a_int_lin H (s67a_L0_meas H hu (r + σ)) hB0 φ'
  have hsub : ∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x * (Real.sqrt (ρ x) * φ' x) =
      (∫ x, generatorW ((quadraticGradientDyn d s q β).coeff ρt) (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * φ' x)) -
      ∫ x, generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * φ' x) := by
    rw [← integral_sub I1 I2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold s67aR
    ring
  have hφ'' : ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =ᵐ[volume]
      fun x => φ' x := hφ'
  have hmov : ∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x) =
      ∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x * (Real.sqrt (ρ x) * φ' x) := by
    refine integral_congr_ae ?_
    filter_upwards [hφ''] with x hx
    unfold movFun
    rw [hx]
  rw [hmov, hsub]
  refine hpair.congr_deriv ?_
  have hw' : (w : Lp ℝ 2 (volume : Measure (Euc d))) =ᵐ[volume] fun x => movS d s β ρ (⇑φ') x := hw
  have t1 : inner ℝ ((s67a_memLp hf ht r hgL σ).toLp (s67a f ρ r t σ)) (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) =
      -∫ x, f (r + σ) x * (Real.sqrt (ρ x) * movS d s β ρ (⇑φ') x) := by
    rw [inner_neg_right, s67_inner_toLp_left, neg_inj]
    refine integral_congr_ae ?_
    filter_upwards [hw'] with x hx
    unfold s67a
    rw [hclσ, hx]; ring
  have t2 : inner ℝ (ha'.toLp a') ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =
      -∫ x, generatorW ((quadraticGradientDyn d s q β).coeff ρt) (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * φ' x) := by
    rw [s67_inner_toLp_left, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hφ''] with x hx
    rw [hx, ha'def x]
    ring
  rw [t1, t2, hdual]
  ring

end HRS.MS.MovAdjNl
