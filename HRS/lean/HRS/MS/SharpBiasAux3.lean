import HRS.MS.SharpBiasAux2
import HRS.MS.SharpIns
import HRS.MS.StaticInput

/-!
# HRS.MS.SharpBiasAux3 -- S7.1: sup-norm control of `log θ_N` at the rate `N^{-τ}`

Packet S71, namespace `HRS.Whole.S71`, helper prefix `s71_`.  Route of the TeX paragraph "A uniform small
bound for the density ratio" (S L5870-5880), with the sup bound of the convolution term taken from the
existing `wr13d_cv_sup`:

`log θ + log Z = β g*(μ - ν_n) + λ g*ν_n + D_N` (`wr13d_log_theta`), `‖g*(μ - ν_n)‖_∞ ≤ C (2ε)^{1-s/d}` with
`ε = ‖θ-1‖_{L¹} + K√(δ_N/N) ≤ (C + K) δ_N`, hence `(2ε)^{1-s/d} ≤ C N^{-τ}` (`δ_N^{1-1/p} = N^{-τ}`), and
`0 ≤ D_N ≤ C δ_N`.  The normalisation `∫ θ = 1` controls `log Z`.

The second half of the file (`s71_potential_u`, `s71_prefactor_u`, `s71_condA_u`, `s71_pointwise_u`, `s71_main_u`,
`s71_rate_u`) is the uniform-in-`β ∈ [βm, βp]` form of S7.4 (`conditional_density`) and S7.6
(`sharp_insertion_rate`), needed for `sharp_bias_uniform_beta`: the merged proofs fix `β` before the constant.  The
bodies are those of `s74_potential`, `s74_prefactor`, `s76_pointwise`, `s76_main`, `s76_rate_main` (the merged files
are not edited); the only changes are (i) `β` is introduced after the constant, (ii) the inputs are the uniform
`static_input_uniform_beta_proof` and `wr13b_pole_variance` (already uniform for `β ≤ βp`), and (iii) the
`β`-dependent constants are replaced by their (monotone) values at `βp`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S71

open HRS.MS.Wr

variable {d : ℕ} {s : ℝ}

/-! ### Elementary facts -/

theorem s71_exists_N (c e : ℝ) (he : 0 < e) : ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → c * (N : ℝ) ^ (-e) ≤ 1 := by
  have h : Tendsto (fun N : ℕ => c * (N : ℝ) ^ (-e)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop).const_mul c
    simpa using this
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  exact ⟨N1, hN1⟩

theorem s71_real_withDensity {μ : Measure (Euc d)} {f : Euc d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) {A : Set (Euc d)} (hA : MeasurableSet A) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).real A = ∫ x in A, f x ∂μ := by
  rw [Measure.real, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hfi.restrict (ae_of_all _ hf0)]
  exact ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hf0 x)

/-- `|π(A) - μ(A)| ≤ ‖θ - 1‖_{L²(μ)}` for `π = θ μ`. -/
theorem s71_event_theta_one {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {θ : Euc d → ℝ}
    (hθm : Measurable θ) (hθ0 : ∀ x, 0 ≤ θ x) {Cθ : ℝ} (hθC : ∀ x, θ x ≤ Cθ) {A : Set (Euc d)}
    (hA : MeasurableSet A) :
    |(μ.withDensity (fun x => ENNReal.ofReal (θ x))).real A - μ.real A| ≤
      Real.sqrt (∫ x, (θ x - 1) ^ 2 ∂μ) := by
  have hθi : Integrable θ μ :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 x)]; exact hθC x)
  rw [s71_real_withDensity hθ0 hθi hA]
  have h1 : μ.real A = ∫ x in A, (1 : ℝ) ∂μ := by simp [Measure.real]
  rw [h1, ← integral_sub hθi.restrict (integrable_const _)]
  have hh : Integrable (fun x => θ x - 1) μ := hθi.sub (integrable_const _)
  calc |∫ x in A, (θ x - 1) ∂μ| ≤ ∫ x in A, |θ x - 1| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, |θ x - 1| ∂μ := setIntegral_le_integral hh.abs (Eventually.of_forall fun x => abs_nonneg _)
    _ ≤ Real.sqrt (∫ x, (θ x - 1) ^ 2 ∂μ) :=
        s74_abs_integral_le_sqrt μ (hθm.sub_const 1) (B := |Cθ| + 1) (fun x => by
          rw [abs_le]
          have := hθ0 x
          have := hθC x
          have := le_abs_self Cθ
          have := neg_abs_le Cθ
          constructor <;> linarith [abs_nonneg Cθ])

/-- `δ^{1 - s/d} = N^{-τ}`. -/
theorem s71_delta_rpow_tau (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) :
    deltaN d s N ^ (1 - s / (d : ℝ)) = (N : ℝ) ^ (-biasTau d s) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [s74_deltaN hs N, ← Real.rpow_mul hN0.le]
  congr 1
  unfold biasTau biasP
  have : (d : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-! ### The sup bound -/

section Sup

set_option maxHeartbeats 1600000 in
theorem s71_logtheta_sup (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ}
    (hβm : 0 < βm) (hβ : βm ≤ βp) (M : ℝ) :
    ∃ (CL : ℝ) (N1 : ℕ), 0 ≤ CL ∧ 2 ≤ N1 ∧
      ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
        ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, N1 ≤ n + 1 →
          CL * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) ≤ 1 ∧
          ∀ x, |Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤
            CL * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨-, -, -, -, hτ0, -, hτle, hτ1⟩ := s71_theta_pos_exp hd hs hsd
  have hpb1 : 1 < biasP d s := hp1
  have hpb2 : biasP d s < 2 := hp2
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  set Mg : ℝ := max (potentialBound d s M) 0 with hMg
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  obtain ⟨C', hC'1, hνC'⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp0
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set Cν : ℝ := max Cθ C' with hCν
  have hCν1 : 1 ≤ Cν := hCθ1.trans (le_max_left _ _)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨K, hK0, hK⟩ := wr13d_event_bound hd hs0 hsd hβm βp M
  obtain ⟨CS, hCS0, hCS⟩ := wr13d_cv_sup hd1 hs0 hsd M hCν1
  obtain ⟨CD, hCD0, hD⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  obtain ⟨Cc, Nc, hcore⟩ := wr13d_core_L2 hd hs0 hsd hβm hβ M
  set Ke : ℝ := |Cc| + K with hKe
  have hKe0 : 0 ≤ Ke := by positivity
  set a : ℝ := 1 - s / (d : ℝ) with ha_def
  have hdpos : (0 : ℝ) < d := by linarith
  have ha : 0 < a := by
    have : s / (d : ℝ) < 1 := by rw [div_lt_one hdpos]; exact hsd
    rw [ha_def]; linarith
  set CR : ℝ := βp * (CS * (2 * Ke) ^ a) + βp * (Cν * Mg) + CD with hCR
  have hCR0 : 0 ≤ CR := by positivity
  set CL : ℝ := 2 * CR with hCL
  obtain ⟨N2, hN2⟩ := s71_exists_N (2 * Ke) (biasP d s - 1) (by linarith)
  obtain ⟨N3, hN3⟩ := s71_exists_N CL (biasTau d s) hτ0
  refine ⟨CL, max (max Nc N2) (max N3 2), by positivity, (le_max_right _ _).trans' (le_max_right _ _), ?_⟩
  intro ρ hρ hM β hβ1 hββp n hNn
  have hNc : Nc ≤ n + 1 := (le_max_left _ _).trans ((le_max_left _ _).trans hNn)
  have hN2' : N2 ≤ n + 1 := (le_max_right _ _).trans ((le_max_left _ _).trans hNn)
  have hN3' : N3 ≤ n + 1 := (le_max_left _ _).trans ((le_max_right _ _).trans hNn)
  have hn : 1 ≤ n := by
    have : 2 ≤ n + 1 := (le_max_right _ _).trans ((le_max_right _ _).trans hNn)
    omega
  refine ⟨hN3 (n + 1) hN3', ?_⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have hN1r : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hδ : deltaN d s (n + 1) = ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s - 1)) := by
    rw [s74_deltaN hs]; congr 1; simp only [biasP]; ring
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by rw [hδ]; exact Real.rpow_nonneg hNpos.le _
  have hε1 : 2 * (Ke * deltaN d s (n + 1)) ≤ 1 := by
    have := hN2 (n + 1) hN2'
    rw [← hδ] at this
    linarith
  have hδN : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ deltaN d s (n + 1) := by
    rw [hδ, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  haveI hμp := wr13a_isProb_density hρ
  have hθ0 : ∀ x, 0 < wr13d_theta d s n β (withDensityReal ρ) x := s71_theta_pos hd hs0 hsd hρ hM hβ0 n
  have hθm : Measurable (wr13d_theta d s n β (withDensityReal ρ)) := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hθCθ : ∀ x, wr13d_theta d s n β (withDensityReal ρ) x ≤ Cθ :=
    fun x => s71_theta_le hd hs0 hsd hρ hM hβ0 hββp n x
  have hθ1 : ∫ x, wr13d_theta d s n β (withDensityReal ρ) x ∂(withDensityReal ρ) = 1 :=
    s71_theta_integral hd hs0 hsd hρ hM hβ0 n
  have hθint : Integrable (wr13d_theta d s n β (withDensityReal ρ)) (withDensityReal ρ) :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 x)]; exact hθCθ x)
  haveI hνp : IsProbabilityMeasure (cavityMarginal d s (n + 1) β (withDensityReal ρ)) :=
    wr13d_cavMarg_isProb hd hs0 hsd hρ hM hβ0 hn
  have hνle : cavityMarginal d s (n + 1) β (withDensityReal ρ) ≤ ENNReal.ofReal Cν • withDensityReal ρ := by
    refine (hνC' ρ hρ hM β hβ0 hββp (n + 1) (by omega)).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact le_max_right _ _
  -- L² bound of θ - 1
  obtain ⟨hz2, hznorm⟩ := hcore ρ hρ hM β hβ1 hββp n hn hNc
  have hzsq : Real.sqrt (∫ x, (wr13d_theta d s n β (withDensityReal ρ) x - 1) ^ 2 ∂(withDensityReal ρ)) ≤
      |Cc| * deltaN d s (n + 1) :=
    wr13d_sqrt_le_of_eLpNorm hz2 (by positivity)
      (hznorm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)))
  have hTVμ : ∀ A : Set (Euc d), MeasurableSet A →
      |((withDensityReal ρ).withDensity (fun y => ENNReal.ofReal ((fun _ : Euc d => (1 : ℝ)) y))).real A -
        (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A| ≤ Ke * deltaN d s (n + 1) := by
    intro A hA
    have e1 : ((withDensityReal ρ).withDensity (fun y => ENNReal.ofReal ((fun _ : Euc d => (1 : ℝ)) y))) =
        withDensityReal ρ := by simp
    rw [e1]
    have hπeq := wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0 n
    have h1 : |(firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
        (withDensityReal ρ).real A| ≤ |Cc| * deltaN d s (n + 1) := by
      rw [hπeq]
      exact (s71_event_theta_one hθm (fun x => (hθ0 x).le) hθCθ hA).trans hzsq
    have h2 := hK ρ hρ hM β hβ1 hββp n hn A hA
    have hsq : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
      refine Real.sqrt_le_iff.2 ⟨hδ0, ?_⟩
      have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) = deltaN d s (n + 1) * (((n + 1 : ℕ) : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]
      rw [this, sq]
      exact mul_le_mul_of_nonneg_left hδN hδ0
    have h3 : |(withDensityReal ρ).real A - (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A| ≤
        |(firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A| +
        |(firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (withDensityReal ρ).real A| := by
      have := abs_sub ((firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A)
        ((firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (withDensityReal ρ).real A)
      have e : (withDensityReal ρ).real A - (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A =
          ((firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A) -
          ((firstMarginal (modulatedGibbs (rieszKernel d s) (n + 1) β (withDensityReal ρ))).real A -
          (withDensityReal ρ).real A) := by ring
      rw [e]; exact this
    have h4 : K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ K * deltaN d s (n + 1) :=
      mul_le_mul_of_nonneg_left hsq hK0
    have h5 : Ke * deltaN d s (n + 1) = |Cc| * deltaN d s (n + 1) + K * deltaN d s (n + 1) := by
      rw [hKe]; ring
    linarith
  -- the pointwise bound on `log θ + log Z`
  set c : ℝ := Real.log (wr13d_Z d s n β (withDensityReal ρ)) with hc
  set R : ℝ := βp * (CS * (2 * (Ke * deltaN d s (n + 1))) ^ a) + βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) +
    CD * deltaN d s (n + 1) with hRdef
  have hu : ∀ y, |Real.log (wr13d_theta d s n β (withDensityReal ρ) y) + c| ≤ R := by
    intro y
    have hsup' := hCS ρ hρ hM (fun _ => 1) measurable_const (fun _ => one_pos) (fun _ => hCν1)
      (cavityMarginal d s (n + 1) β (withDensityReal ρ)) hνp hνle (Ke * deltaN d s (n + 1)) hε1 hTVμ y
    simp only [mul_one] at hsup'
    have hlog := wr13d_log_theta hd hs0 hsd hρ hM hβ0 hn y
    obtain ⟨-, hD0, hD1, -⟩ := hD ρ hρ hM β hβ1 hββp (n + 1) (by omega) y
    obtain ⟨hg0, hg1⟩ := wr13d_conv_nu_le hd1 hs0 hsd hρ hM hCν0 hνle y
    set gν := ∫ z, rieszKernel d s (y - z) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)) with hgν
    set gμ := convMeasure (rieszKernel d s) (withDensityReal ρ) y with hgμ
    have hgμ' : gμ = ∫ z, rieszKernel d s (y - z) ∂(withDensityReal ρ) := rfl
    have hlamN : β / ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) = β := by
      push_cast; field_simp
    have key : Real.log (wr13d_theta d s n β (withDensityReal ρ) y) + c =
        β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν + insertionDefect d s (n + 1) β (withDensityReal ρ) y := by
      rw [hc]
      linear_combination hlog - gν * hlamN
    rw [key]
    have t1 : |β * (gμ - gν)| ≤ βp * (CS * (2 * (Ke * deltaN d s (n + 1))) ^ a) := by
      rw [abs_mul, abs_of_nonneg hβ0]
      calc β * |gμ - gν| ≤ βp * |gμ - gν| := mul_le_mul_of_nonneg_right hββp (abs_nonneg _)
        _ ≤ βp * (CS * (2 * (Ke * deltaN d s (n + 1))) ^ a) := by
            rw [hgμ']
            exact mul_le_mul_of_nonneg_left hsup' hβp0
    have t2 : |β / ((n + 1 : ℕ) : ℝ) * gν| ≤ βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg (div_nonneg hβ0 hNpos.le) hg0)]
      calc β / ((n + 1 : ℕ) : ℝ) * gν ≤ β / ((n + 1 : ℕ) : ℝ) * (Cν * Mg) :=
            mul_le_mul_of_nonneg_left (hg1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCν0))
              (div_nonneg hβ0 hNpos.le)
        _ ≤ βp / ((n + 1 : ℕ) : ℝ) * (Cν * Mg) :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hββp hNpos.le) (by positivity)
        _ = βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) := by ring
    have t3 : |insertionDefect d s (n + 1) β (withDensityReal ρ) y| ≤ CD * deltaN d s (n + 1) := by
      rw [abs_of_nonneg hD0]; exact hD1
    calc |β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν + insertionDefect d s (n + 1) β (withDensityReal ρ) y|
        ≤ |β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν| + |insertionDefect d s (n + 1) β (withDensityReal ρ) y| :=
          abs_add_le _ _
      _ ≤ (|β * (gμ - gν)| + |β / ((n + 1 : ℕ) : ℝ) * gν|) + |insertionDefect d s (n + 1) β (withDensityReal ρ) y| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  -- normalisation: `|c| ≤ R`
  have hθexp : ∀ y, wr13d_theta d s n β (withDensityReal ρ) y =
      Real.exp (Real.log (wr13d_theta d s n β (withDensityReal ρ) y)) := fun y => (Real.exp_log (hθ0 y)).symm
  have hup : c ≤ R := by
    have h1 : ∀ y, wr13d_theta d s n β (withDensityReal ρ) y ≤ Real.exp (R - c) := fun y => by
      rw [hθexp y]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 (hu y)).2
      linarith
    have h2 : ∫ y, wr13d_theta d s n β (withDensityReal ρ) y ∂(withDensityReal ρ) ≤
        ∫ _y, Real.exp (R - c) ∂(withDensityReal ρ) :=
      integral_mono hθint (integrable_const _) h1
    rw [hθ1] at h2
    simp at h2
    linarith
  have hlow : -R ≤ c := by
    have h1 : ∀ y, Real.exp (-R - c) ≤ wr13d_theta d s n β (withDensityReal ρ) y := fun y => by
      rw [hθexp y]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 (hu y)).1
      linarith
    have h2 : ∫ _y, Real.exp (-R - c) ∂(withDensityReal ρ) ≤
        ∫ y, wr13d_theta d s n β (withDensityReal ρ) y ∂(withDensityReal ρ) :=
      integral_mono (integrable_const _) hθint h1
    rw [hθ1] at h2
    simp at h2
    linarith
  intro x
  have hlogθ : |Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤ 2 * R := by
    have h1 := hu x
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2, hup, hlow]
  -- the rate
  have hR : R ≤ CR * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by
    have e1 : (2 * (Ke * deltaN d s (n + 1))) ^ a = (2 * Ke) ^ a * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by
      rw [← s71_delta_rpow_tau hd hs hsd (by omega : 1 ≤ n + 1), ← Real.mul_rpow (by positivity) hδ0]
      congr 1; ring
    have e2 : βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) ≤ βp * (Cν * Mg) * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have e3 : CD * deltaN d s (n + 1) ≤ CD * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by
      refine mul_le_mul_of_nonneg_left ?_ hCD0
      rw [hδ]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    rw [hRdef, e1]
    have : βp * (CS * ((2 * Ke) ^ a * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s))) =
        βp * (CS * (2 * Ke) ^ a) * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by ring
    rw [this, hCR]
    nlinarith
  calc |Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤ 2 * R := hlogθ
    _ ≤ 2 * (CR * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s)) := by linarith
    _ = CL * ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := by rw [hCL]; ring

end Sup

end HRS.Whole.S71

open ProbabilityTheory Set Metric

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

theorem s71_potential_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β : ℝ, βm ≤ β → β ≤ βp →
      ∀ (m : ℕ) (y : Euc d),
      Integrable (fun Y : EucConfig d (m + 1) =>
        |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y|)
        (HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) ∧
      ∫ Y : EucConfig d (m + 1),
          |s74_u d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β (Fin.tail Y) y|
        ∂(HRS.Whole.cavityLaw d s (m + 2) β (HRS.Whole.withDensityReal ρ)) ≤
      C * ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨C0, hC0⟩ := static_input_uniform_beta_proof hd hs hsd βm βp M hβm hβp
  obtain ⟨Ctr, hCtr⟩ := HRS.Whole.convolution_truncated hd hs hsd M
  set Mg0 : ℝ := HRS.Whole.potentialBound d s M with hMg0def
  set K0p : ℝ := Real.exp (2 * βp * Mg0) with hK0pdef
  refine ⟨βp * (Real.sqrt (|C0| * |Ctr|) + 1) + 2 * βp * (K0p * |Ctr|) +
    βp * ((K0p + 1) * |Ctr| + 2 * |C0|) + 2 * βp * (K0p * Mg0), fun ρ hρ hM β hβ1 hββp m y => ?_⟩
  have hβ : 0 < β := hβm.trans_le hβ1
  have hβp0 : 0 ≤ βp := hβm.le.trans hβp
  set K0 : ℝ := Real.exp (2 * β * Mg0) with hK0def
  have hK0 : 0 ≤ K0 := (Real.exp_pos _).le
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp0 : 0 < p := by linarith
  have hbp : HRS.Whole.biasP d s = p := rfl
  have hbt : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  set lam : ℝ := β / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ.le hN0.le
  have hlamN : lam * Nr = β := by rw [hlamdef]; field_simp
  have hlm : lam * m = β - 2 * lam := by
    have : (m : ℝ) = Nr - 2 := by rw [hNr]; push_cast; ring
    rw [this]; nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  have hSI := hC0 ρ hρ hM β ⟨hβ1, hββp⟩ (m + 2) (by omega)
  set H : ℝ := Nr ^ (1 / p) with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hN1 (by positivity)
  have hH0 : 0 < H := by linarith
  obtain ⟨hT2i, hT2b, hT1i, hT1b⟩ := hCtr ρ hρ hM H hH1 y
  have hψm : Measurable fun z : Euc d => rieszKernel d s (y - z) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  have hψ0 : ∀ z : Euc d, 0 ≤ rieszKernel d s (y - z) := fun z => wr13a_g_nonneg hs0 _
  have hmarg : ∀ j : Fin (m + 1), P.map (fun Y : EucConfig d (m + 1) => Y j) =
      P.map (fun Y : EucConfig d (m + 1) => Y 0) := fun j =>
    (wr13c2_cavityLaw_exchangeable hs0 hconv hβ.le (m + 2)).marginal_eq j ⟨0, by omega⟩
  obtain ⟨hψi, hψbd⟩ := s74_coord_integral hs0 hint hconv hMg hβ.le m 0 hψm hψ0 (hint y)
  set G : ℝ := ∫ Y : EucConfig d (m + 1), rieszKernel d s (y - Y 0) ∂P with hG
  have hG0 : 0 ≤ G := integral_nonneg fun Y => hψ0 _
  have hGle : G ≤ K0 * Mg0 :=
    hψbd.trans (mul_le_mul_of_nonneg_left (hconv y) hK0)
  have hGc := s74_G_close hd hs hsd hρ hM hβ m y hSI (Ctr := Ctr)
    (fun H' hH' => ⟨(hCtr ρ hρ hM H' hH' y).2.2.1, (hCtr ρ hρ hM H' hH' y).2.2.2⟩)
  rw [← hG, hbt] at hGc
  have hvar := s74_hvar hd hs hsd hρ hM hβ m y hSI hH0 hT2i hT2b
  have hTb := s74_T_bound P hmarg hψm hψ0 hψi hH0 hlam
    (κ := β * HRS.Whole.convMeasure (rieszKernel d s) μ y) hvar
  refine ⟨hTb.1, hTb.2.trans ?_⟩
  rw [hbt]
  -- the tail term D
  have hD := (s74_coord_integral hs0 hint hconv hMg hβ.le m 0
    (ψ := fun z => rieszKernel d s (y - z) - min (rieszKernel d s (y - z)) H)
    (hψm.sub (hψm.min measurable_const)) (fun z => sub_nonneg.2 (min_le_left _ _)) hT1i).2
  have hHp : H ^ (1 - HRS.Whole.biasP d s) = Nr ^ (1 / p - 1) := by
    rw [hbp, hH, ← Real.rpow_mul hN0.le]; congr 1; field_simp
  have hHp0 : 0 ≤ Nr ^ (1 / p - 1) := Real.rpow_nonneg hN0.le _
  set X1 : ℝ := Nr ^ (1 / p - 1) with hX1
  set X : ℝ := Nr ^ (-((p - 1) ^ 2 / p)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hN0.le _
  have hX1X : X1 ≤ X := s74_exp1 hp1 hp2 hN1
  have hNinv : Nr ^ (-1 : ℝ) ≤ X := s74_exp2 hp1 hp2 hN1
  have hinv : 1 / Nr ≤ X := by
    have : Nr ^ (-1 : ℝ) = 1 / Nr := by rw [Real.rpow_neg_one, one_div]
    rw [← this]; exact hNinv
  set D : ℝ := ∫ Y : EucConfig d (m + 1), (rieszKernel d s (y - Y 0) -
    min (rieszKernel d s (y - Y 0)) H) ∂P with hDdef
  have hD0 : 0 ≤ D := integral_nonneg fun Y => by
    show (0 : ℝ) ≤ rieszKernel d s (y - Y 0) - min (rieszKernel d s (y - Y 0)) H
    exact sub_nonneg.2 (min_le_left _ _)
  have hDle : D ≤ K0 * (|Ctr| * X1) := by
    refine hD.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    refine hT1b.trans ?_
    rw [hHp]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hHp0
  -- the variance term
  have hH2 : Nr * H ^ (2 - p) = H ^ 2 := by
    have h1 : H ^ p = Nr := by
      rw [hH, ← Real.rpow_mul hN0.le]; rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    calc Nr * H ^ (2 - p) = H ^ p * H ^ (2 - p) := by rw [h1]
      _ = H ^ (p + (2 - p)) := (Real.rpow_add hH0 _ _).symm
      _ = H ^ 2 := by rw [show p + (2 - p) = (2 : ℝ) by ring, Real.rpow_two]
  have hJ : |Ctr * H ^ (2 - HRS.Whole.biasP d s)| = |Ctr| * H ^ (2 - p) := by
    rw [hbp, abs_mul, abs_of_nonneg (Real.rpow_nonneg hH0.le _)]
  have hsqrt : Real.sqrt (|C0| * Nr * |Ctr * H ^ (2 - HRS.Whole.biasP d s)|) =
      Real.sqrt (|C0| * |Ctr|) * H := by
    rw [hJ]
    have : |C0| * Nr * (|Ctr| * H ^ (2 - p)) = (|C0| * |Ctr|) * H ^ 2 := by rw [← hH2]; ring
    rw [this, Real.sqrt_mul (mul_nonneg (abs_nonneg _) (abs_nonneg _)), Real.sqrt_sq hH0.le]
  have hlamH : lam * H = β * X1 := by
    rw [hlamdef, hX1, Real.rpow_sub_one hN0.ne', hH]; field_simp
  -- assemble
  rw [hsqrt]
  have hb1 : lam * (Real.sqrt (|C0| * |Ctr|) * H + H) = β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 := by
    have e : β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 = (Real.sqrt (|C0| * |Ctr|) + 1) * (β * X1) := by ring
    rw [e, ← hlamH]; ring
  have hb2 : 2 * (lam * m * D) ≤ 2 * β * (K0 * (|Ctr| * X1)) := by
    have h1 : lam * m ≤ β := by rw [hlm]; linarith
    have h2 : 0 ≤ lam * m := mul_nonneg hlam hm0
    calc 2 * (lam * m * D) ≤ 2 * (β * (K0 * (|Ctr| * X1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hDle hD0 hβ.le) (by norm_num)
      _ = _ := by ring
  have hb3 : |lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y| ≤
      β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X := by
    have e : lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y =
        β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y) - 2 * lam * G := by
      rw [hlm]; ring
    rw [e]
    have h1 : |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y)| ≤
        β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) := by
      rw [abs_mul, abs_of_pos hβ]; exact mul_le_mul_of_nonneg_left hGc hβ.le
    have h2 : 2 * lam * G ≤ 2 * β * (K0 * Mg0) * X := by
      have : lam ≤ β * X := by
        have : lam = β * (1 / Nr) := by rw [hlamdef]; ring
        rw [this]; exact mul_le_mul_of_nonneg_left hinv hβ.le
      calc 2 * lam * G ≤ 2 * (β * X) * (K0 * Mg0) :=
            mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num)) hGle hG0 (by positivity)
        _ = _ := by ring
    have h3 : 0 ≤ 2 * lam * G := by positivity
    calc |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y) - 2 * lam * G|
        ≤ |β * (G - HRS.Whole.convMeasure (rieszKernel d s) μ y)| + |2 * lam * G| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h3]; exact add_le_add h1 h2
  have hs' : 0 ≤ Real.sqrt (|C0| * |Ctr|) := Real.sqrt_nonneg _
  calc lam * (Real.sqrt (|C0| * |Ctr|) * H + H) + 2 * (lam * m * D) +
        |lam * m * G - β * HRS.Whole.convMeasure (rieszKernel d s) μ y|
      ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 + 2 * β * (K0 * (|Ctr| * X1)) +
        (β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X) := by
        rw [hb1]; linarith
    _ ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X + 2 * β * (K0 * (|Ctr| * X)) +
        (β * (((K0 + 1) * |Ctr| + 2 * |C0|) * X) + 2 * β * (K0 * Mg0) * X) := by
        have h1 : β * (Real.sqrt (|C0| * |Ctr|) + 1) * X1 ≤ β * (Real.sqrt (|C0| * |Ctr|) + 1) * X :=
          mul_le_mul_of_nonneg_left hX1X (by positivity)
        have h2 : 2 * β * (K0 * (|Ctr| * X1)) ≤ 2 * β * (K0 * (|Ctr| * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX1X
            (abs_nonneg _)) hK0) (by positivity)
        linarith
    _ = (β * (Real.sqrt (|C0| * |Ctr|) + 1) + 2 * β * (K0 * |Ctr|) +
        β * ((K0 + 1) * |Ctr| + 2 * |C0|) + 2 * β * (K0 * Mg0)) * X := by ring
    _ ≤ (βp * (Real.sqrt (|C0| * |Ctr|) + 1) + 2 * βp * (K0p * |Ctr|) +
        βp * ((K0p + 1) * |Ctr| + 2 * |C0|) + 2 * βp * (K0p * Mg0)) * X := by
        have hK : K0 ≤ K0p := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith : 2 * β ≤ 2 * βp) hMg)
        refine mul_le_mul_of_nonneg_right ?_ hX0
        gcongr


theorem s71_prefactor_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β : ℝ, βm ≤ β → β ≤ βp →
      ∀ (m : ℕ) (x : Euc d),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Euc d,
        |s74_A d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β t x m y - 1| ≤
          C * ((m + 2 : ℕ) : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨Cu, hCu⟩ := s71_potential_u hd hs hsd hβm hβp M
  set Mg0 : ℝ := HRS.Whole.potentialBound d s M with hMg0def
  set K0p : ℝ := Real.exp (2 * βp * Mg0) with hK0pdef
  set Kjp : ℝ := Real.exp (βp * (K0p * Mg0)) with hKjpdef
  refine ⟨Kjp * K0p * (2 * |Cu| + βp * Mg0), ?_⟩
  intro ρ hρ hM β hβ1 hββp m x t ht y
  have hβ : 0 < β := hβm.trans_le hβ1
  have hβp0 : 0 ≤ βp := hβm.le.trans hβp
  set K0 : ℝ := Real.exp (2 * β * Mg0) with hK0def
  set Kj : ℝ := Real.exp (β * (K0 * Mg0)) with hKjdef
  have hK0 : 0 ≤ K0 := (Real.exp_pos _).le
  have hKj : 0 ≤ Kj := (Real.exp_pos _).le
  haveI hμ := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) μ := fun z =>
    (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hp0 : 0 < p := by linarith
  have hbt : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  rw [hbt]
  set X : ℝ := Nr ^ (-((p - 1) ^ 2 / p)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hN0.le _
  set lam : ℝ := β / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hβ.le hN0.le
  have hinv : 1 / Nr ≤ X := by
    have h : Nr ^ (-1 : ℝ) = 1 / Nr := by rw [Real.rpow_neg_one, one_div]
    rw [← h]; exact s74_exp2 hp1 hp2 hN1
  have hlamX : lam ≤ β * X := by
    have : lam = β * (1 / Nr) := by rw [hlamdef]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hinv hβ.le
  have hK : lam * (t + m) ≤ β := by
    have h := wr13a_lam_mul_le' (r := t + m) (c := 1) hβ.le (N := ((m + 2 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith [ht.2])
    linarith
  haveI hP : IsProbabilityMeasure (HRS.Whole.cavityLaw d s (m + 2) β μ) :=
    wr13a_cavityLaw_isProb hs0 hconv hβ.le (m + 2)
  set P : Measure (EucConfig d (m + 1)) := HRS.Whole.cavityLaw d s (m + 2) β μ with hPdef
  haveI hPL : IsProbabilityMeasure (HRS.Whole.poleLaw d s (m + 2) β μ x t) :=
    wr13c2_poleLaw_isProb hs0 hconv hβ.le ht.1 (m + 2) x
  set PL : Measure (EucConfig d (m + 1)) := HRS.Whole.poleLaw d s (m + 2) β μ x t with hPLdef
  have hZ0 : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ 0 := fun Y => by
    have := s74_Zc_ge hs0 hint hconv hMg hlam hβ.le ht.1 x Y hK
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) this).ne'
  have hZt : ∀ Y : EucConfig d m, s74_Zc d s μ lam β t x Y ≠ ∞ := fun Y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s74_Zc_le hs0 hconv hlam hβ.le ht.1 x Y)
  have htail : Measurable (fun X : EucConfig d (m + 1) => (Fin.tail X : EucConfig d m)) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply j.succ
  set r : EucConfig d (m + 1) → ℝ := fun X => Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) /
    (s74_Zc d s μ lam β t x (Fin.tail X)).toReal with hr
  have hu1 : Measurable (fun X : EucConfig d (m + 1) => s74_u d s μ lam β (Fin.tail X) y) := by
    have h := (s74_u_meas_Y hs0 μ lam β (m := m) y).comp htail
    exact h
  have hZm : Measurable (fun X : EucConfig d (m + 1) => (s74_Zc d s μ lam β t x (Fin.tail X)).toReal) := by
    have h := (s74_Zc_meas hs0 μ lam β t x m).comp htail
    exact h.ennreal_toReal
  have hrm : Measurable r := (Real.measurable_exp.comp hu1.neg).div hZm
  have hr0 : ∀ X, 0 ≤ r X := fun X => div_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hrb : ∀ X, r X ≤ K0 := by
    intro X
    obtain ⟨hlo, hup⟩ := s74_Zr_bounds hs0 hint hconv hMg hlam hβ.le ht.1 x hK (Fin.tail X)
    have hZpos : 0 < (s74_Zc d s μ lam β t x (Fin.tail X)).toReal := lt_of_lt_of_le (Real.exp_pos _) hlo
    simp only [hr]
    rw [div_le_iff₀ hZpos]
    have h1 : Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) ≤ Real.exp (β * Mg0) :=
      Real.exp_le_exp.2 (s74_neg_u_le hs0 hconv hlam hβ.le _ y)
    have h2 : Real.exp (β * Mg0) = K0 * Real.exp (-(β * Mg0)) := by
      rw [hK0def, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-(s74_u d s μ lam β (Fin.tail X) y)) ≤ Real.exp (β * Mg0) := h1
      _ = K0 * Real.exp (-(β * Mg0)) := h2
      _ ≤ K0 * _ := mul_le_mul_of_nonneg_left hlo hK0
  have hri : ∀ κ : Measure (EucConfig d (m + 1)), IsFiniteMeasure κ → Integrable r κ := fun κ _ =>
    Integrable.of_bound (C := K0) hrm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr0 X)]; exact hrb X)
  haveI : IsFiniteMeasure PL := inferInstance
  haveI : IsFiniteMeasure P := inferInstance
  -- A as an integral
  have hA : s74_A d s μ lam β t x m y = ∫ X, r X ∂PL := by
    have ha : s74_a d s μ lam β t x m y = ∫⁻ X : EucConfig d (m + 1),
        ENNReal.ofReal (Real.exp (-(s74_u d s μ lam β (Fin.tail X) y))) *
          (s74_Zc d s μ lam β t x (Fin.tail X))⁻¹ ∂PL :=
      s74_a_eq hs0 hint hconv hMg hβ.le ht.1 ht.2 m x y
    unfold s74_A
    rw [ha, lintegral_congr fun X => s74_ofReal_mul_inv (hZ0 _) (hZt _) (Real.exp_pos _).le]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hr0)
      hrm.aestronglyMeasurable).symm
  -- domination
  have hle : PL ≤ ENNReal.ofReal Kj • P := s74_pole_le hs0 hint hconv hMg hβ.le ht.1 ht.2 m x
  have hrP : Integrable (fun X => |r X - 1|) P :=
    ((hri P inferInstance).sub (integrable_const 1)).abs
  have h1 : |s74_A d s μ lam β t x m y - 1| ≤ ∫ X, |r X - 1| ∂PL := by
    rw [hA]
    have : ∫ X, r X ∂PL - 1 = ∫ X, (r X - 1) ∂PL := by
      rw [integral_sub (hri PL inferInstance) (integrable_const 1)]; simp
    rw [this]
    exact abs_integral_le_integral_abs
  have h2 : ∫ X, |r X - 1| ∂PL ≤ Kj * ∫ X, |r X - 1| ∂P := by
    calc ∫ X, |r X - 1| ∂PL ≤ ∫ X, |r X - 1| ∂(ENNReal.ofReal Kj • P) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun X => abs_nonneg _)
            (hrP.smul_measure ENNReal.ofReal_ne_top)
      _ = Kj * ∫ X, |r X - 1| ∂P := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hKj, smul_eq_mul]
  -- Fubini
  have hT : Measurable (fun q : EucConfig d (m + 1) × Euc d => ((Fin.tail q.1 : EucConfig d m), q.2)) :=
    (htail.comp measurable_fst).prodMk measurable_snd
  have hFm : Measurable (fun q : EucConfig d (m + 1) × Euc d =>
      |s74_u d s μ lam β (Fin.tail q.1) q.2|) := by
    have h := (s74_u_meas2 hs0 μ lam β (m := m)).comp hT
    exact h.abs
  have hcu : 0 ≤ |Cu| * X := mul_nonneg (abs_nonneg _) hX0
  have hCu' : ∀ z : Euc d, Integrable (fun Y : EucConfig d (m + 1) =>
      |s74_u d s μ lam β (Fin.tail Y) z|) P ∧ ∫ Y : EucConfig d (m + 1),
      |s74_u d s μ lam β (Fin.tail Y) z| ∂P ≤ |Cu| * X := fun z =>
    ⟨(hCu ρ hρ hM β hβ1 hββp m z).1, (hCu ρ hρ hM β hβ1 hββp m z).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)⟩
  obtain ⟨hUi, hUb⟩ := s74_fubini_bound P μ
    (fun (Y : EucConfig d (m + 1)) (z : Euc d) => |s74_u d s μ lam β (Fin.tail Y) z|) hFm
    (fun Y z => abs_nonneg _) hcu (fun z => (hCu' z).2) (fun z => (hCu' z).1)
    (fun Y => (s74_u_integrable hs0 hint hconv lam β (Fin.tail Y)).abs)
  have hpt : ∀ X : EucConfig d (m + 1), |r X - 1| ≤ K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
      lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ) := fun X =>
    s74_ratio hs0 hint hconv hMg hlam hβ.le ht.1 ht.2 x hK (Fin.tail X) y
  have hRi : Integrable (fun X : EucConfig d (m + 1) => K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
      lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ)) P :=
    (((hCu ρ hρ hM β hβ1 hββp m y).1.add (integrable_const _)).add hUi).const_mul _
  have h3 : ∫ X, |r X - 1| ∂P ≤ K0 * (|Cu| * X + lam * Mg0 + |Cu| * X) := by
    calc ∫ X, |r X - 1| ∂P ≤ ∫ X : EucConfig d (m + 1), K0 * (|s74_u d s μ lam β (Fin.tail X) y| +
          lam * Mg0 + ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ) ∂P :=
          integral_mono hrP hRi hpt
      _ = K0 * (∫ Y : EucConfig d (m + 1), |s74_u d s μ lam β (Fin.tail Y) y| ∂P + lam * Mg0 +
          ∫ X : EucConfig d (m + 1), ∫ z, |s74_u d s μ lam β (Fin.tail X) z| ∂μ ∂P) := by
          have hA1 : Integrable (fun X : EucConfig d (m + 1) =>
              |s74_u d s μ lam β (Fin.tail X) y|) P := (hCu ρ hρ hM β hβ1 hββp m y).1
          have hA2 : Integrable (fun X : EucConfig d (m + 1) =>
              |s74_u d s μ lam β (Fin.tail X) y| + lam * Mg0) P := hA1.add (integrable_const _)
          rw [integral_const_mul, integral_add hA2 hUi, integral_add hA1 (integrable_const _)]
          simp
      _ ≤ K0 * (|Cu| * X + lam * Mg0 + |Cu| * X) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have := (hCu' y).2
          linarith
  calc |s74_A d s μ lam β t x m y - 1| ≤ ∫ X, |r X - 1| ∂PL := h1
    _ ≤ Kj * ∫ X, |r X - 1| ∂P := h2
    _ ≤ Kj * (K0 * (|Cu| * X + lam * Mg0 + |Cu| * X)) := mul_le_mul_of_nonneg_left h3 hKj
    _ ≤ Kj * (K0 * (|Cu| * X + (β * X) * Mg0 + |Cu| * X)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hKj
        have := mul_le_mul_of_nonneg_right hlamX hMg
        linarith
    _ = Kj * K0 * (2 * |Cu| + β * Mg0) * X := by ring
    _ ≤ Kjp * K0p * (2 * |Cu| + βp * Mg0) * X := by
        have hK : K0 ≤ K0p := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith : 2 * β ≤ 2 * βp) hMg)
        have hKjK : Kj ≤ Kjp := Real.exp_le_exp.2 (by
          have h1 : β * (K0 * Mg0) ≤ βp * (K0p * Mg0) :=
            mul_le_mul hββp (mul_le_mul_of_nonneg_right hK hMg) (mul_nonneg hK0 hMg) (by linarith)
          exact h1)
        refine mul_le_mul_of_nonneg_right ?_ hX0
        gcongr


/-- The one-particle pole density with prefactor `A`, `|A - 1| ≤ C N^{-τ}`, uniformly in `β ∈ [βm, βp]`. -/
theorem s71_condA_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β : ℝ, βm ≤ β → β ≤ βp →
      ∀ N, 2 ≤ N → ∀ (x : Euc d), ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ A : Euc d → ℝ, Measurable A ∧
        HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) =
          (HRS.Whole.withDensityReal ρ).withDensity
            (fun y => ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)) * A y)) ∧
        (∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), 0 ≤ A y) ∧
        ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), |A y - 1| ≤ C * (N : ℝ) ^ (-HRS.Whole.biasTau d s) := by
  obtain ⟨Cp, hCp⟩ := s71_prefactor_u hd hs hsd hβm hβp M
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  refine ⟨Cp, fun ρ hρ hM β hβ1 hββp N hN x t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI hμ := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) (HRS.Whole.withDensityReal ρ) :=
    fun z => (wr13a_potential_bound hd1 hs0 hsd hρ hM z).1
  have hMg := wr13a_potentialBound_nonneg hd1 hs0 hsd hρ hM
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  refine ⟨s74_A d s (HRS.Whole.withDensityReal ρ) (β / ((m + 2 : ℕ) : ℝ)) β t x m,
    s74_A_meas hs0 _ β t x m, ?_, Filter.Eventually.of_forall fun y => s74_A_nonneg _ β t x m y,
    Filter.Eventually.of_forall fun y => hCp ρ hρ hM β hβ1 hββp m x t ht y⟩
  exact s74_firstMarginal_A hs0 hint hconv hMg hβ0 ht.1 ht.2 m x

end HRS.MS.Wr

namespace HRS.MS.S76

open HRS.Whole (rieszKernel EucConfig)
open HRS.MS.Wr (wr13c2_X)

variable {d : ℕ} {s : ℝ}

theorem s71_pointwise_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) (hM0 : 0 ≤ M) :
    ∃ K1 K2 K3 CA : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ K3 ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β : ℝ, βm ≤ β → β ≤ βp →
        ∀ N : ℕ, 3 ≤ N →
        ∀ x : Euc d, ∀ L : ℝ, 1 ≤ L → ∀ t ∈ Ioc (0 : ℝ) 1,
          |Var[wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
              (fun Y => t * wr13c2_X d s N β x Y)] -
            ((N - 1 : ℕ) : ℝ) * s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / N)
              ((β / N) ^ (1 / s) * L) x t| ≤
          K1 * (((N - 1 : ℕ) : ℝ) ^ 2 * (((β / N) ^ ((d : ℝ) / s)) ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) +
            K2 * (((N - 1 : ℕ) : ℝ) * (β / N) ^ ((d : ℝ) / s) * L ^ ((d : ℝ) - 2 * s)) +
            K3 * (((N - 1 : ℕ) : ℝ) * (β / N) ^ ((d : ℝ) / s) * L ^ (((d : ℝ) - 2 * s) / 2) *
              t ^ (((d : ℝ) / s - 2) / 2)) +
            ((N - 1 : ℕ) : ℝ) * (CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) *
              s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / N) ((β / N) ^ (1 / s) * L) x t := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd1
  have h2m : 0 < 2 * s - (d : ℝ) := by linarith
  have hβp0 : 0 < βp := hβm.trans_le hβp
  obtain ⟨C0', hSI⟩ := HRS.MS.Wr.static_input_uniform_beta_proof hd hs hsd βm βp M hβm hβp
  obtain ⟨CA, hCA⟩ := HRS.MS.Wr.s71_condA_u hd hs hsd hβm hβp M
  obtain ⟨Cv, hCvpos, hvar⟩ := HRS.MS.Wr.wr13b_pole_variance hd hs0 hsd βp M
  obtain ⟨Cr, hCr0, hradJ⟩ := HRS.MS.Wr.wr13c_radial_J hd1 hs0 hsd M
  obtain ⟨Cri, hCri0, hradI⟩ := HRS.MS.Wr.wr13c_radial_J_integral hd1 hs0 hsd M
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = max C0' 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C0 := by rw [hC0def]; exact le_max_right _ _
  have hC0' : C0' ≤ C0 := by rw [hC0def]; exact le_max_left _ _
  refine ⟨s76_K1 d s C0 M, s76_K2 d s Cv M, s76_K3 d s βp M Cv Cr, CA, ?_, ?_, ?_, ?_⟩
  · unfold s76_K1; positivity
  · unfold s76_K2
    exact mul_nonneg hCvpos.le (div_nonneg (mul_nonneg hM0 hsA) h2m.le)
  · unfold s76_K3; positivity
  intro ρ hρ hM β hβ1 hββp N hN x L hL t ht
  have hβ : 0 < β := hβm.trans_le hβ1
  haveI hμprob := HRS.MS.Wr.wr13a_isProb_density hρ
  have hconv := HRS.MS.Wr.wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlam0 : 0 < β / (N : ℝ) := by positivity
  have hlamβ : β / (N : ℝ) ≤ β := div_le_self hβ.le hN1
  have hL0 : 0 < L := by linarith
  have hc : 0 < (β / (N : ℝ)) ^ (1 / s) := Real.rpow_pos_of_pos hlam0 _
  have hr : 0 < (β / (N : ℝ)) ^ (1 / s) * L := mul_pos hc hL0
  have hN2 : 2 ≤ N - 1 := by omega
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := ht.2
  have hu0 : 0 < t * (β / (N : ℝ)) := mul_pos ht.1 hlam0
  haveI hQp := HRS.MS.Wr.wr13c2_poleLaw_isProb hs0 hconv hβ.le ht0 N x
  have hex := HRS.MS.Wr.wr13b_poleLaw_exchangeable hs0 hconv hβ.le ht0 N x
  obtain ⟨-, -, -, hpole, -⟩ := hSI ρ hρ hM β ⟨hβ1, hββp⟩ N (by omega)
  obtain ⟨-, hfirst0, hsec0, -⟩ := hpole x t ⟨ht0, ht1⟩
  have hgnn : ∀ y : Euc d, 0 ≤ rieszKernel d s (x - y) := fun y => by
    rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  have hexp1 : ∀ y : Euc d,
      Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)) ≤ 1 := by
    intro y
    refine Real.exp_le_one_iff.2 ?_
    nlinarith [mul_nonneg hu0.le (hgnn y)]
  have hexp2 : ∀ yz : Euc d × Euc d,
      Real.exp (-(t * (β / (N : ℝ))) * (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2))) ≤ 1 := by
    intro yz
    refine Real.exp_le_one_iff.2 ?_
    nlinarith [mul_nonneg hu0.le (add_nonneg (hgnn yz.1) (hgnn yz.2))]
  have hfirst : HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal C0 • HRS.Whole.withDensityReal ρ := by
    refine hfirst0.trans ?_
    rw [← withDensity_const]
    refine withDensity_mono (Filter.Eventually.of_forall fun y => ENNReal.ofReal_le_ofReal ?_)
    calc C0' * Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))
        ≤ C0 * Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)) :=
          mul_le_mul_of_nonneg_right hC0' (Real.exp_pos _).le
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (hexp1 y) hC0
      _ = C0 := mul_one _
  have hsec : HRS.Whole.secondMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal C0 • (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) := by
    refine (hsec0 hN).trans ?_
    rw [← withDensity_const]
    refine withDensity_mono (Filter.Eventually.of_forall fun yz => ENNReal.ofReal_le_ofReal ?_)
    calc C0' * Real.exp (-(t * (β / (N : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))
        ≤ C0 * Real.exp (-(t * (β / (N : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2))) :=
          mul_le_mul_of_nonneg_right hC0' (Real.exp_pos _).le
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (hexp2 yz) hC0
      _ = C0 := mul_one _
  have hvar_t : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
        (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal (Cv * ((N - 1 : ℕ) : ℝ)) * ∫⁻ y, ‖f y‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)))
          ∂(HRS.Whole.withDensityReal ρ) :=
    fun f hf => hvar ρ hρ hM β hβ hββp N (by omega) x t ⟨ht0, ht1⟩ f hf
  have hrad_t := hradJ ρ hρ hM (t * (β / (N : ℝ))) hu0 x
  have hJ0 : 0 ≤ HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))) :=
    zero_le_one.trans (HRS.MS.Wr.wr13c_one_le_J _ hu0)
  have hCore := s76_core hd1 hs0 hsd hds (n := N - 1) hN2
    (Q := HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) hex hρ hM
    (C0 := C0) (Cv := Cv) (Cr := Cr) (J := HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))))
    hC0 hCvpos.le hCr0 hJ0 (lam := β / (N : ℝ)) (r := (β / (N : ℝ)) ^ (1 / s) * L)
    (u := t * (β / (N : ℝ))) hlam0.le hr hu0.le x hfirst hsec hvar_t hrad_t
  -- `J` for `2s > d`
  have hJ : HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))) =
      1 + (t * (β / (N : ℝ))) ^ ((d : ℝ) / s - 2) := by
    unfold HRS.MS.Wr.wr13c_J
    rw [if_neg (not_lt.2 hds.le), if_neg (ne_of_gt hds)]
  have hArith := s76_arith hd1 hs0 hsd hds hβ hM0 hC0 hCvpos.le hCr0 hlam0 hlamβ hL ht.1 ht1
    (Nat.cast_nonneg (N - 1)) (n := ((N - 1 : ℕ) : ℝ)) hJ
  -- the variance of the exponent
  have hXeq : wr13c2_X d s N β x = fun Y : EucConfig d (N - 1) =>
      -(∑ i, (s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i) +
        s76_chi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i))) := by
    funext Y
    unfold wr13c2_X
    calc -(β / (N : ℝ)) * ∑ i, rieszKernel d s (x - Y i)
        = -((β / (N : ℝ)) * ∑ i, rieszKernel d s (x - Y i)) := neg_mul _ _
      _ = -(∑ i, (β / (N : ℝ)) * rieszKernel d s (x - Y i)) := by rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => (s76_psi_add_chi hs0 _ _ x _).symm
  have hVar : Var[wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
        (fun Y => t * wr13c2_X d s N β x Y)] =
      Var[fun Y : EucConfig d (N - 1) => ∑ i, (s76_psi d s (β / (N : ℝ))
          ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i) +
        s76_chi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i));
        HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t] := by
    rw [← HRS.MS.Wr.wr13c2_poleLaw_eq_tilted hs0 hconv hβ.le ht0 N x, hXeq]
    exact variance_fun_neg
  -- the prefactor
  obtain ⟨A, hAm, hAeq, hA0, hA1⟩ := hCA ρ hρ hM β hβ1 hββp N (by omega) x t ⟨ht0, ht1⟩
  have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hwm : Measurable (fun y : Euc d => Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) :=
    Real.measurable_exp.comp (measurable_const.mul hgm)
  have hfpsi : Measurable (fun y : Euc d =>
      s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x y ^ 2) :=
    (s76_psi_meas _ _ x).pow_const 2
  have hint : Integrable (fun y : Euc d =>
      s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x y ^ 2 *
        Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) (HRS.Whole.withDensityReal ρ) := by
    obtain ⟨hi, -⟩ := hradI ρ hρ hM (t * (β / (N : ℝ))) hu0 x
    refine Integrable.mono' (hi.const_mul ((β / (N : ℝ)) ^ 2)) (hfpsi.mul hwm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact s76_psi_sq_w_le hs0 hlam0.le _ _ x y
  have hB := s76_lemmaB (n := N - 1) (by omega)
    (Q := HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t)
    (μ := HRS.Whole.withDensityReal ρ)
    (w := fun y => Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) hwm
    (fun y => (Real.exp_pos _).le) hAm hAeq hA0
    (ε := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) hA1 hfpsi (fun y => sq_nonneg _) hint
  -- combine
  rw [hVar]
  have key : ∀ (Vv mm m0 n R ε : ℝ), |Vv - n * mm| ≤ R → |mm - m0| ≤ ε * m0 → 0 ≤ n →
      |Vv - n * m0| ≤ R + n * (ε * m0) := by
    intro Vv mm m0 n R ε h1 h2 hn
    have e : Vv - n * m0 = (Vv - n * mm) + n * (mm - m0) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left h2 hn
  have hn0 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK3mono : s76_K3 d s β M Cv Cr ≤ s76_K3 d s βp M Cv Cr := by
    unfold s76_K3 s76_K4
    have h1 : β ^ (2 - (d : ℝ) / s) ≤ βp ^ (2 - (d : ℝ) / s) :=
      Real.rpow_le_rpow hβ.le hββp (by
        have : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
        linarith)
    have h2 : 0 ≤ s76_K2 d s Cv M := by unfold s76_K2; positivity
    have h3 : s76_K4 d s β Cv Cr ≤ s76_K4 d s βp Cv Cr := by
      unfold s76_K4
      have : 0 ≤ Cv * Cr := mul_nonneg hCvpos.le hCr0
      exact mul_le_mul_of_nonneg_left (by linarith) this
    unfold s76_K4 at h3
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h3 h2)) (by norm_num)
  have hQ0 : 0 ≤ ((N - 1 : ℕ) : ℝ) * (β / (N : ℝ)) ^ ((d : ℝ) / s) * L ^ (((d : ℝ) - 2 * s) / 2) *
      t ^ (((d : ℝ) / s - 2) / 2) := by positivity
  have hArith' := hArith.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hK3mono hQ0))
  have hfin := key _ _ _ _ _ _ (hCore.trans hArith') hB hn0
  refine hfin.trans (le_of_eq ?_)
  unfold s76_m0
  ring

set_option maxHeartbeats 1600000 in
theorem s71_main_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) (hM0 : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ Λ : ℝ≥0, LipschitzWith Λ ρ → ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, 3 ≤ N →
        ∀ x : Euc d,
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          HRS.Whole.CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t) ∧
        DifferentiableWithinAt ℝ
          (HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x) (Set.Ici 0) 0 ∧
        |HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x /
              ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) -
            2 * HRS.Whole.biasConst d s * ρ x| ≤
          K * ((N : ℝ) ^ (-HRS.Whole.biasTau d s) + Λ * (β / N) ^ (1 / s) * L +
            L ^ (-((2 * s - d) / 2)) +
            (N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s * L ^ (2 * ((d : ℝ) - s))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  obtain ⟨K1, K2, K3, CA, hK1, hK2, hK3, hpt⟩ := s71_pointwise_u hd hs hsd hβm hβp M hM0
  obtain ⟨C0', hSI⟩ := HRS.MS.Wr.static_input_uniform_beta_proof hd hs hsd βm βp M hβm hβp
  obtain ⟨Ck, hCk0, hCk⟩ := s76_kk_tail_le hd1 hs0 hds
  obtain ⟨Cri, hCri0, hradI⟩ := HRS.MS.Wr.wr13c_radial_J_integral hd1 hs0 hsd M
  obtain ⟨hk0, hkint, hK⟩ := s76_kk_facts hd hs hsd
  have hb0 : 0 ≤ HRS.Whole.biasConst d s := by
    have := integral_nonneg (μ := (volume : Measure (Euc d)))
      (f := fun u : Euc d => HRS.Whole.Q34.kk (‖u‖ ^ (-s))) (fun u => hk0 u)
    rw [hK] at this; linarith
  set b : ℝ := HRS.Whole.biasConst d s with hb
  refine ⟨K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b, by positivity, ?_⟩
  intro ρ hρ hM Λ hΛ β hβ1 hββp L hL N hN x
  have hβ : 0 < β := hβm.trans_le hβ1
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  haveI hμprob := HRS.MS.Wr.wr13a_isProb_density hρ
  have hconv := HRS.MS.Wr.wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hlam0 : 0 < β / (N : ℝ) := by positivity
  have hc : 0 < (β / (N : ℝ)) ^ (1 / s) := Real.rpow_pos_of_pos hlam0 _
  -- the first two conclusions
  have hCWD : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HRS.Whole.CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t :=
    fun t ht => ((hSI ρ hρ hM β ⟨hβ1, hββp⟩ N (by omega)).2.2.2.1 x t ht).1
  obtain ⟨hder, hdef⟩ := HRS.MS.Wr.wr13c2_insertionDefect_eq hd hs0 hsd hρ hM hβ.le
    (by omega : 2 ≤ N) x
  refine ⟨hCWD, hder.differentiableWithinAt, ?_⟩
  -- the defect as a weighted integral of the variance
  haveI hP0 := HRS.MS.Wr.wr13a_cavityLaw_isProb hs0 hconv hβ.le N
  obtain ⟨hVint, hDid⟩ := s76_defect_eq
    (P := HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ))
    (HRS.MS.Wr.wr13c2_X_meas hs0 N β x) (HRS.MS.Wr.wr13c2_X_le_zero hs0 hβ.le N x)
    (HRS.MS.Wr.wr13c2_integrable_X hd hs0 hsd hρ hM hβ.le (by omega) x)
  have hD : HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x =
      ∫ t in Ioc (0 : ℝ) 1, (1 - t) * Var[HRS.MS.Wr.wr13c2_X d s N β x;
        (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
          (fun Y => t * HRS.MS.Wr.wr13c2_X d s N β x Y)] := hdef.trans hDid
  -- the diagonal integral
  obtain ⟨hm0int, hm0val⟩ := s76_m0_int hd hs hsd hρ hM hlam0 hL0 x
    (fun u hu => (hradI ρ hρ hM u hu x).1)
  have hcN : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
  have hn2 : (2 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N - 1)
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by linarith
  obtain ⟨hIL0, hIL1⟩ := s76_IL_bounds hd hs hsd hρ hM ((β / (N : ℝ)) ^ (1 / s)) L x
  have hILapp := s76_IL_approx hd hs hsd hρ hM hΛ hc hL0 hCk x
  set IL : ℝ := s76_IL d s ρ ((β / (N : ℝ)) ^ (1 / s)) L x with hIL
  set P : ℝ := (β / (N : ℝ)) ^ ((d : ℝ) / s) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hlam0 _
  set q : ℝ := ((d : ℝ) / s - 2) / 2 with hq
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
  have hqm : -1 < q := by rw [hq]; linarith
  have hq1 : 1 / (q + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; rw [hq]; linarith
  set E0 : ℝ := K1 * (n ^ 2 * (P ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) +
    K2 * (n * P * L ^ ((d : ℝ) - 2 * s)) with hE0
  set E3 : ℝ := K3 * (n * P * L ^ (((d : ℝ) - 2 * s) / 2)) with hE3
  have hLs : 0 ≤ L ^ ((d : ℝ) - s) := Real.rpow_nonneg hL0.le _
  have hLs2 : 0 ≤ L ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hL0.le _
  have hLh : 0 ≤ L ^ (((d : ℝ) - 2 * s) / 2) := Real.rpow_nonneg hL0.le _
  have hE0n : 0 ≤ E0 := by rw [hE0]; positivity
  have hE3n : 0 ≤ E3 := by rw [hE3]; positivity
  have hptt : ∀ t ∈ Ioc (0 : ℝ) 1,
      |Var[HRS.MS.Wr.wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
          (fun Y => t * HRS.MS.Wr.wr13c2_X d s N β x Y)] -
        n * s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x t| ≤
      E0 + E3 * t ^ q + n * (CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) *
        s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x t := by
    intro t ht
    refine (hpt ρ hρ hM β hβ1 hββp N hN x L hL t ht).trans (le_of_eq ?_)
    rw [hE0, hE3]; ring
  have hint := s76_integrate (E0 := E0) (E3 := E3) (q := q) (n := n)
    (ε := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) hE0n hE3n hqm hVint hm0int hptt
  rw [hm0val, ← hD] at hint
  -- division by `n P`
  have hA : 0 < n * P := mul_pos hn0 hP0
  set D : ℝ := HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x with hDdef
  set eps : ℝ := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s) with hepsdef
  have hbiasP : HRS.Whole.biasP d s = (d : ℝ) / s := rfl
  have hdiv : |D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) - IL| ≤
      K1 * (n * P * (L ^ ((d : ℝ) - s)) ^ 2) + K2 * L ^ ((d : ℝ) - 2 * s) +
        K3 * L ^ (((d : ℝ) - 2 * s) / 2) * (1 / (q + 1)) + eps * IL := by
    rw [hbiasP, ← hcN, ← hP]
    have e1 : D / (n * P) - IL = (D - n * (P * IL)) / (n * P) := by
      field_simp
    rw [e1, abs_div, abs_of_pos hA, div_le_iff₀ hA]
    refine hint.trans (le_of_eq ?_)
    rw [hE0, hE3]
    field_simp
  -- the Lipschitz and tail estimates
  have hLpow : L ^ ((d : ℝ) - 2 * s) ≤ L ^ (-((2 * s - d) / 2)) := by
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    linarith
  have hLeq : L ^ (((d : ℝ) - 2 * s) / 2) = L ^ (-((2 * s - d) / 2)) := by
    congr 1; ring
  have hLsq : (L ^ ((d : ℝ) - s)) ^ 2 = L ^ (2 * ((d : ℝ) - s)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have hT1 : 0 ≤ (N : ℝ) ^ (-HRS.Whole.biasTau d s) := Real.rpow_nonneg hNpos.le _
  have hT2 : 0 ≤ (Λ : ℝ) * (β / (N : ℝ)) ^ (1 / s) * L := by positivity
  have hT3 : 0 ≤ L ^ (-((2 * s - d) / 2)) := Real.rpow_nonneg hL0.le _
  have hT4 : 0 ≤ n * P * L ^ (2 * ((d : ℝ) - s)) := by positivity
  have hεIL : eps * IL ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) * (M * (2 * b)) := by
    have h1 : eps ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hT1
    calc eps * IL ≤ (|CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) * IL :=
          mul_le_mul_of_nonneg_right h1 hIL0
      _ ≤ (|CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) * (M * (2 * b)) :=
          mul_le_mul_of_nonneg_left hIL1 (mul_nonneg (abs_nonneg _) hT1)
  have hmain : |D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) - 2 * b * ρ x| ≤
      K1 * (n * P * (L ^ ((d : ℝ) - s)) ^ 2) + K2 * L ^ ((d : ℝ) - 2 * s) +
        K3 * L ^ (((d : ℝ) - 2 * s) / 2) * (1 / (q + 1)) + eps * IL +
      (2 * b * (Λ * (β / (N : ℝ)) ^ (1 / s) * L) + M * (Ck * L ^ ((d : ℝ) - 2 * s))) := by
    have := abs_sub_le (D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s)) IL (2 * b * ρ x)
    linarith
  refine hmain.trans ?_
  -- compare with the right-hand side
  rw [hbiasP, ← hcN, ← hP, hLsq, hLeq]
  have hnn : 0 ≤ M * Ck := mul_nonneg hM0 hCk0
  have hnb : 0 ≤ 2 * b * M * |CA| := by positivity
  have f1 : K2 * L ^ ((d : ℝ) - 2 * s) ≤ K2 * L ^ (-((2 * s - d) / 2)) :=
    mul_le_mul_of_nonneg_left hLpow hK2
  have f2 : K3 * L ^ (-((2 * s - d) / 2)) * (1 / (q + 1)) ≤ 2 * K3 * L ^ (-((2 * s - d) / 2)) := by
    have h0 : 0 ≤ K3 * L ^ (-((2 * s - d) / 2)) := mul_nonneg hK3 hT3
    calc K3 * L ^ (-((2 * s - d) / 2)) * (1 / (q + 1)) ≤ K3 * L ^ (-((2 * s - d) / 2)) * 2 :=
          mul_le_mul_of_nonneg_left hq1 h0
      _ = 2 * K3 * L ^ (-((2 * s - d) / 2)) := by ring
  have f3 : M * (Ck * L ^ ((d : ℝ) - 2 * s)) ≤ M * Ck * L ^ (-((2 * s - d) / 2)) := by
    calc M * (Ck * L ^ ((d : ℝ) - 2 * s)) = (M * Ck) * L ^ ((d : ℝ) - 2 * s) := by ring
      _ ≤ (M * Ck) * L ^ (-((2 * s - d) / 2)) := mul_le_mul_of_nonneg_left hLpow hnn
  have f4 : eps * IL ≤ (2 * b * M * |CA|) * (N : ℝ) ^ (-HRS.Whole.biasTau d s) := by
    calc eps * IL ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) * (M * (2 * b)) := hεIL
      _ = (2 * b * M * |CA|) * (N : ℝ) ^ (-HRS.Whole.biasTau d s) := by ring
  have hKa : K1 ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have hKb : K2 + 2 * K3 + M * Ck ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by
    linarith
  have hKc : 2 * b * M * |CA| ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have hKd : 2 * b ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have g1 := mul_le_mul_of_nonneg_right hKa hT4
  have g3 := mul_le_mul_of_nonneg_right hKb hT3
  have g2 := mul_le_mul_of_nonneg_right hKc hT1
  have g4 := mul_le_mul_of_nonneg_right hKd hT2
  nlinarith [f1, f2, f3, f4, g1, g2, g3, g4]

set_option maxHeartbeats 800000 in
theorem s71_rate_u (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβp : βm ≤ βp) (M : ℝ) (Λ : ℝ≥0) (hM0 : 0 ≤ M) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      LipschitzWith Λ ρ → ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, 3 ≤ N → ∀ x : Euc d,
        |HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x /
              ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) -
            2 * HRS.Whole.biasConst d s * ρ x| ≤ C * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨K, hK0, hmain⟩ := s71_main_u hd hs hsd hβm hβp M hM0
  refine ⟨K * (1 + (Λ : ℝ) * βp ^ (1 / s) + 1 + βp ^ ((d : ℝ) / s)), fun ρ hρ hM hΛ β hβ1 hββp N hN x => ?_⟩
  have hβ : 0 < β := hβm.trans_le hβ1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  set Nr : ℝ := (N : ℝ) with hNr
  set p : ℝ := (d : ℝ) / s with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
  have hp0 : 0 < p := by linarith
  set θ : ℝ := HRS.Whole.biasTheta d s with hθ
  have hθτ : θ ≤ (p - 1) ^ 2 / p := by
    rw [hθ]; exact min_le_left _ _
  have hθ2 : θ ≤ (2 - p) / 8 := by
    rw [hθ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ 3 / (4 * s) := by
    rw [hθ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hτ : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  have hmono : ∀ a : ℝ, θ ≤ a → Nr ^ (-a) ≤ Nr ^ (-θ) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hL1 : 1 ≤ Nr ^ (1 / (4 * s)) := Real.one_le_rpow hN1 (by positivity)
  obtain ⟨-, -, hb⟩ := hmain ρ hρ hM Λ hΛ β hβ1 hββp (Nr ^ (1 / (4 * s))) hL1 N hN x
  refine hb.trans ?_
  have hNθ : 0 ≤ Nr ^ (-θ) := Real.rpow_nonneg hNpos.le _
  -- the four terms
  have t1 : Nr ^ (-HRS.Whole.biasTau d s) ≤ Nr ^ (-θ) := hmono _ (by rw [hτ]; exact hθτ)
  have e2 : (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) = β ^ (1 / s) * Nr ^ (-(3 / (4 * s))) := by
    rw [Real.div_rpow hβ.le hNpos.le, div_eq_mul_inv, ← Real.rpow_neg hNpos.le, mul_assoc,
      ← Real.rpow_add hNpos]
    congr 2
    field_simp
    ring
  have t2 : (Λ : ℝ) * (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) ≤ (Λ : ℝ) * β ^ (1 / s) * Nr ^ (-θ) := by
    rw [mul_assoc, e2, ← mul_assoc]
    have := hmono _ hθ3
    have h0 : 0 ≤ (Λ : ℝ) * β ^ (1 / s) := mul_nonneg (NNReal.coe_nonneg Λ) (Real.rpow_nonneg hβ.le _)
    exact mul_le_mul_of_nonneg_left this h0
  have e3 : (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) = Nr ^ (-((2 - p) / 8)) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    rw [hp]
    field_simp
    ring
  have t3 : (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) ≤ Nr ^ (-θ) := by
    rw [e3]; exact hmono _ hθ2
  have e4 : (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)) = Nr ^ ((p - 1) / 2) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    rw [hp]
    field_simp
    ring
  have hθ4 : θ ≤ (p - 1) / 2 := by
    refine hθτ.trans ?_
    rw [div_le_iff₀ hp0]
    nlinarith
  have t4 : (Nr - 1) * (β / Nr) ^ p * (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)) ≤
      β ^ p * Nr ^ (-θ) := by
    rw [e4, Real.div_rpow hβ.le hNpos.le, div_eq_mul_inv, ← Real.rpow_neg hNpos.le]
    have h1 : (Nr - 1) * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) ≤
        Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) := by
      have : 0 ≤ β ^ p * Nr ^ (-p) := mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hNpos.le _)
      have h2 : 0 ≤ Nr ^ ((p - 1) / 2) := Real.rpow_nonneg hNpos.le _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) this) h2
    have h3 : Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) = β ^ p * Nr ^ (-((p - 1) / 2)) := by
      have : Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2) = Nr ^ (-((p - 1) / 2)) := by
        calc Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2) = Nr ^ (1 : ℝ) * Nr ^ (-p) * Nr ^ ((p - 1) / 2) := by
              rw [Real.rpow_one]
          _ = Nr ^ (1 + -p + (p - 1) / 2) := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          _ = Nr ^ (-((p - 1) / 2)) := by congr 1; ring
      calc Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) = β ^ p * (Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2)) := by
            ring
        _ = _ := by rw [this]
    refine h1.trans (le_of_eq h3 |>.trans ?_)
    exact mul_le_mul_of_nonneg_left (hmono _ hθ4) (Real.rpow_nonneg hβ.le _)
  have hbp : HRS.Whole.biasP d s = p := rfl
  rw [hbp] at hb ⊢
  calc K * (Nr ^ (-HRS.Whole.biasTau d s) + (Λ : ℝ) * (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) +
        (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) +
        (Nr - 1) * (β / Nr) ^ p * (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)))
      ≤ K * (Nr ^ (-θ) + (Λ : ℝ) * β ^ (1 / s) * Nr ^ (-θ) + Nr ^ (-θ) + β ^ p * Nr ^ (-θ)) :=
        mul_le_mul_of_nonneg_left (by linarith [t1, t2, t3, t4]) hK0
    _ = K * (1 + (Λ : ℝ) * β ^ (1 / s) + 1 + β ^ p) * Nr ^ (-θ) := by ring
    _ ≤ K * (1 + (Λ : ℝ) * βp ^ (1 / s) + 1 + βp ^ p) * Nr ^ (-θ) := by
        have h1 : β ^ (1 / s) ≤ βp ^ (1 / s) := Real.rpow_le_rpow hβ.le hββp (by positivity)
        have h2 : β ^ p ≤ βp ^ p := Real.rpow_le_rpow hβ.le hββp hp0.le
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK0) hNθ
        have := mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg Λ)
        linarith

end HRS.MS.S76
