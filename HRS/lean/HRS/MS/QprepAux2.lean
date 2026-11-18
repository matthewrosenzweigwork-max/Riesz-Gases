import HRS.MS.QprepAux1

/-!
# S4.6 packet A2: uniform thermal data and the uniform static bundle for `Q_{N,γ₀}`

`s46_thermal_data_unif`: the constants of `ThermalData` are uniform for `(a, β)` in a compact subset of `(0,∞)²`
(copy of `s45_thermal_data` with the ranges of `tc6_unif`).  `s46_spherical`: a uniform Gaussian bound gives a uniform
`HasSphericalBound`.  `S46Static` / `s46_static_all`: the calibrated static estimates for
`Q = modulatedGibbs g N γ₀ μ_{a,β}` with one constant for `a, β, γ₀` in compact ranges (S3.3 `euc_static_proof`,
S3.5 `r2_log_static_proof` at inverse temperature `γ₀`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace S46

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s46_thermal_data_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) :
    ∃ C c BU : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, S45.ThermalData d s a β C c BU := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd ham hβm hap hβp
  obtain ⟨S, hS0, hS⟩ := hU 1
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb 0
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (half_pos hc₀)
  refine ⟨max M₀ (S * Cp), c₀ / 2, Mb / βm, fun a ha β hβ => ?_⟩
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have href := hS a β ha.1 ha.2 hβ.1 hβ.2
  have hdr := hMbρ a β ha.1 ha.2 hβ.1 hβ.2
  obtain ⟨hcb, -⟩ := HRS.MS.Tc1.tc1_drift_data hd hs0 hsd ha0 hβ0 hdr
  refine ⟨href.prob, href.smooth, href.pos, le_max_of_le_left hM₀.le,
    half_pos hc₀, fun y => ?_, fun y => ?_, HRS.MS.Tc1.tc1_U_smooth hd hs0 hsd ha0 hβ0, by positivity,
    fun y => ?_, HRS.MS.Tc1.tc1_grad_rho hd hs0 hsd ha0 hβ0⟩
  · rw [abs_of_nonneg (href.prob.nonneg y)]
    refine (href.gauss y).trans ?_
    have : Real.exp (-c₀ * ‖y‖ ^ 2) ≤ Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖y‖])
    calc M₀ * Real.exp (-c₀ * ‖y‖ ^ 2) ≤ M₀ * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hM₀.le
      _ ≤ max M₀ (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have h := href.deriv 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at h
    have hp := hCp ‖y‖ (norm_nonneg _)
    have e : Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2) =
        Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖fderiv ℝ (thermalDensity d s a β) y‖ ≤ S * (1 + ‖y‖) ^ 1 * Real.exp (-c₀ * ‖y‖ ^ 2) := h
      _ = S * (1 + ‖y‖) * Real.exp (-c₀ * ‖y‖ ^ 2) := by rw [pow_one]
      _ ≤ S * (Cp * Real.exp (c₀ / 2 * ‖y‖ ^ 2)) * Real.exp (-c₀ * ‖y‖ ^ 2) := by gcongr
      _ = (S * Cp) * (Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2)) := by ring
      _ = (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [e]
      _ ≤ max M₀ (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have h := hcb.2 0 le_rfl y
    rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ0] at h
    rw [le_div_iff₀ hβm]
    have h1 : Mb * β ≥ Mb * βm := mul_le_mul_of_nonneg_left hβ.1 hMb0
    have h2 : 0 ≤ ‖gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) y‖ := norm_nonneg _
    nlinarith

theorem s46_spherical (hd : 1 ≤ d) {M₀ c : ℝ} (hc : 0 < c) (hM₀ : 0 ≤ M₀) :
    ∃ A : ℝ, ∀ ρ : Euc d → ℝ, (∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) → HasSphericalBound A ρ := by
  set Kc : ℝ := 1 + (d : ℝ) / c with hKc
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hKc0 : 0 < Kc := by positivity
  refine ⟨M₀ * Kc ^ d, fun ρ hρ => Filter.Eventually.of_forall fun x => ?_⟩
  set t : ℝ := ‖x‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have h1 : 1 + t ≤ Kc * Real.exp (c * t / d) := by
    have := Real.add_one_le_exp (c * t / d)
    have h2 : 0 ≤ (d : ℝ) / c := by positivity
    have h3 : 0 ≤ c * t / d := by positivity
    have e : (d : ℝ) / c * (c * t / d) = t := by field_simp
    nlinarith [mul_nonneg h2 h3]
  have hP : (1 + t) ^ d ≤ Kc ^ d * Real.exp (c * t) := by
    calc (1 + t) ^ d ≤ (Kc * Real.exp (c * t / d)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
      _ = Kc ^ d * Real.exp (c * t) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          field_simp
  have hP0 : 0 < (1 + t) ^ d := by positivity
  have hrp : (1 + t) ^ (-(d : ℝ)) = ((1 + t) ^ d)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hrp]
  have h4 : Real.exp (-c * t) * (1 + t) ^ d ≤ Kc ^ d := by
    calc Real.exp (-c * t) * (1 + t) ^ d ≤ Real.exp (-c * t) * (Kc ^ d * Real.exp (c * t)) :=
          mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ = Kc ^ d := by
          have : Real.exp (-c * t) * Real.exp (c * t) = 1 := by rw [← Real.exp_add]; simp
          calc _ = Kc ^ d * (Real.exp (-c * t) * Real.exp (c * t)) := by ring
            _ = _ := by rw [this, mul_one]
  have h5 : Real.exp (-c * t) ≤ Kc ^ d * ((1 + t) ^ d)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hP0]; exact h4
  calc ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hρ x
    _ ≤ M₀ * (Kc ^ d * ((1 + t) ^ d)⁻¹) := mul_le_mul_of_nonneg_left h5 hM₀
    _ = M₀ * Kc ^ d * ((1 + t) ^ d)⁻¹ := by ring

/-- The static facts at particle number `N` for `Q_{N,γ}`. -/
structure S46Static (d : ℕ) (s a β γ C : ℝ) (N : ℕ) : Prop where
  prob : IsProbabilityMeasure (s46_P d s a β γ N)
  exch : IsExchangeable (s46_P d s a β γ N)
  linear : ∀ f : Euc d → ℝ, MemLp f 2 (thermalMeasure d s a β) →
    evariance (linStat f) (s46_P d s a β γ N) ≤
      ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(thermalMeasure d s a β))
  marg : ∃ φ : Euc d → ℝ, Measurable φ ∧
    s46_nu d s a β γ N = (thermalMeasure d s a β).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    (∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧ MemLp (fun x => φ x - 1) 2 (thermalMeasure d s a β) ∧
    l2Norm (thermalMeasure d s a β) (fun x => φ x - 1) ≤ C * HRS.deltaN d s N
  comm : ∀ (Λ : ℝ≥0) (v : Euc d → Euc d), LipschitzWith Λ v →
    QuadraticVarianceBound (commutatorKernel d s v) (s46_P d s a β γ N) (thermalMeasure d s a β)
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N) ∧
    QuadraticVarianceBound (commutatorKernel d s v) (s46_P d s a β γ N) (s46_nu d s a β γ N)
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N)

theorem s46_static_all (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp γm γp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hγp : γm ≤ γp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ N : ℕ, 2 ≤ N → S46Static d s a β γ C N := by
  obtain ⟨c, M₀, m₂, hc, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd ham hβm hap hβp
  obtain ⟨S, hS0, hS⟩ := hU 0
  have hρM : ∀ a β, a ∈ Set.Icc am ap → β ∈ Set.Icc βm βp →
      IsProbDensity (thermalDensity d s a β) ∧
        (∀ x, thermalDensity d s a β x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) ∧
        ∀ x, thermalDensity d s a β x ≤ M₀ := fun a β ha hβ => by
    have href := hS a β ha.1 ha.2 hβ.1 hβ.2
    exact ⟨href.prob, href.gauss, fun x => HRS.MS.TcR.tc2_le_M0 href.prob hc href.gauss x⟩
  have hd1 : 1 ≤ d := by omega
  have hsd2 : (0 : ℝ) < d / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rcases hs0.eq_or_lt with h0 | h0
  · -- s = 0
    subst h0
    obtain ⟨A, hA⟩ := s46_spherical hd1 hc hM₀.le
    obtain ⟨C, hC⟩ := HRS.MS.Wl.r2_log_static_proof hd γm γp A hγm hγp
    obtain ⟨C', hC'⟩ := HRS.MS.Wl.r2_log_static_commutator_proof hd γm γp A hγm hγp
    refine ⟨max (max C C') 0, le_max_right _ _, fun a ha β hβ γ hγ N hN => ?_⟩
    have ha0 : 0 < a := ham.trans_le ha.1
    have hβ0 : 0 < β := hβm.trans_le hβ.1
    have hγ0 : 0 < γ := hγm.trans_le hγ.1
    have hCle : C ≤ max (max C C') 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' ≤ max (max C C') 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C C') 0 := le_max_right _ _
    obtain ⟨hρ, hρg, -⟩ := hρM a β ha hβ
    haveI : IsProbabilityMeasure (thermalMeasure d 0 a β) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC (thermalDensity d 0 a β) hρ (hA _ hρg) γ hγ N hN
    have hcan := s46_P_eq hd le_rfl hsd ha0 hβ0 hγ0 N
    have hδ : HRS.deltaN d 0 N = (N : ℝ)⁻¹ := by
      unfold HRS.deltaN; rw [if_pos hsd2]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d 0) N γ (thermalMeasure d 0 a β)) :=
      S45.s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d 0) N γ (thermalMeasure d 0 a β)) :=
      modulatedGibbs_isExchangeable _ _ _ (S45.s45_rieszKernel_even 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(thermalMeasure d 0 a β) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · unfold s46_nu
      rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      refine ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, ?_⟩, hφ2, ?_⟩
      · refine (hφb x).2.trans ?_
        have hp : (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
            (by have : 0 < γ / (2 * N) := by positivity
                linarith)
        have h1 : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) := Real.rpow_nonneg (by positivity) _
        calc C * (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N)))
            ≤ max (max C C') 0 * (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) :=
              mul_le_mul_of_nonneg_right hCle h1
          _ ≤ max (max C C') 0 * 1 := mul_le_mul_of_nonneg_left hp hC0
          _ = _ := mul_one _
      · rw [hδ]
        refine hφn.trans ?_
        have : C / N = C * (N : ℝ)⁻¹ := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hCle (by positivity)
    · intro Λ v hv
      unfold s46_nu
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' (thermalDensity d 0 a β) hρ (hA _ hρg) γ hγ N hN Λ v hv
      have hb : C' * (Λ : ℝ) ^ 2 / N / N ≤ max (max C C') 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d 0 N / N := by
        rw [hδ]
        have : C' * (Λ : ℝ) ^ 2 / N / N = C' * (Λ : ℝ) ^ 2 * (N : ℝ)⁻¹ / N := by
          field_simp
        rw [this]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩
  · -- 0 < s < d
    obtain ⟨C, hC⟩ := HRS.MS.Wr.euc_static_proof hd h0 hsd γm γp M₀ hγm hγp
    obtain ⟨C', hC'⟩ := HRS.MS.Wr.euc_static_commutator_proof hd h0 hsd γm γp M₀ hγm hγp
    refine ⟨max (max C (C' * s ^ 2)) 0, le_max_right _ _, fun a ha β hβ γ hγ N hN => ?_⟩
    have ha0 : 0 < a := ham.trans_le ha.1
    have hβ0 : 0 < β := hβm.trans_le hβ.1
    have hγ0 : 0 < γ := hγm.trans_le hγ.1
    have hCle : C ≤ max (max C (C' * s ^ 2)) 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' * s ^ 2 ≤ max (max C (C' * s ^ 2)) 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C (C' * s ^ 2)) 0 := le_max_right _ _
    obtain ⟨hρ, -, hM⟩ := hρM a β ha hβ
    haveI : IsProbabilityMeasure (thermalMeasure d s a β) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC (thermalDensity d s a β) hρ hM γ hγ N hN
    have hcan := s46_P_eq hd hs0 hsd ha0 hβ0 hγ0 N
    have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s (by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d s) N γ (thermalMeasure d s a β)) :=
      S45.s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d s) N γ (thermalMeasure d s a β)) :=
      modulatedGibbs_isExchangeable _ _ _ (S45.s45_rieszKernel_even s)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(thermalMeasure d s a β) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · unfold s46_nu
      rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      exact ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans hCle⟩, hφ2,
        hφn.trans (mul_le_mul_of_nonneg_right hCle hδ0)⟩
    · intro Λ v hv
      unfold s46_nu
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' (thermalDensity d s a β) hρ hM γ hγ N hN Λ v hv
      have hb : C' * (s * (Λ : ℝ)) ^ 2 * HRS.deltaN d s N / N ≤
          max (max C (C' * s ^ 2)) 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N := by
        have e : C' * (s * (Λ : ℝ)) ^ 2 = (C' * s ^ 2) * (Λ : ℝ) ^ 2 := by ring
        rw [e]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩

end S46

end
