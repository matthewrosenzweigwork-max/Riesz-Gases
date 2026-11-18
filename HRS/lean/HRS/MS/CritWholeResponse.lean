import HRS.Whole.Critical
import HRS.Whole.Q34Aux18
import HRS.MS.SharpBiasAux1

/-!
# S8.1.N1 -- nonconstant continuous density and positivity of the critical bias pairing

Worker S81, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81bd_`.

* `s81bd_density_not_ae_const`: a continuous probability density on `ℝ^d` (`d ≥ 1`) is not
  `ρ dx`-a.e. equal to a constant (no positivity of `ρ` is assumed).
* `s81bd_critical_response`: for a bounded continuous probability density, `d ≥ 2`, `β > 0`, the
  frozen `critBiasDensity d β ρ` lies in `L²_0(ρ dx)` and has strictly positive pairing with `ρ`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

theorem s81bd_sphereArea_pos {d : ℕ} (hd : 1 ≤ d) : 0 < HRS.sphereArea d := by
  unfold HRS.sphereArea
  have h0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos h0
  have := Real.pi_pos
  positivity

theorem s81bd_density_not_ae_const {d : ℕ} (hd : 1 ≤ d)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (hcont : Continuous ρ) (c : ℝ) :
    ¬ (ρ =ᵐ[withDensityReal ρ] (fun _ : Euc d => c)) := by
  intro hae
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (ρ x) ≠ 0 → ρ x = c :=
    (ae_withDensity_iff hm).1 hae
  -- the continuous function `ρ (ρ - c)` vanishes a.e., hence everywhere
  have hg : Continuous fun x => ρ x * (ρ x - c) := hcont.mul (hcont.sub continuous_const)
  have h2 : (fun x => ρ x * (ρ x - c)) =ᵐ[volume] fun _ : Euc d => (0 : ℝ) := by
    filter_upwards [h1] with x hx
    by_cases h0 : ρ x = 0
    · simp [h0]
    · have hpos : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0)
      have := hx (by simpa using hpos)
      simp [this]
  have h3 : ∀ x, ρ x * (ρ x - c) = 0 := fun x =>
    congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hg continuous_const).1 h2) x
  have h4 : ∀ x, ρ x = 0 ∨ ρ x = c := by
    intro x
    rcases mul_eq_zero.1 (h3 x) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  -- connectedness: the continuous density is constant
  have hrange : IsPreconnected (Set.range ρ) := isPreconnected_range hcont
  have key : ∀ x y, ρ x < ρ y → False := by
    intro x y hxy
    have hoc := hrange.Icc_subset ⟨x, rfl⟩ ⟨y, rfl⟩
    have hmid : (ρ x + ρ y) / 2 ∈ Set.range ρ :=
      hoc ⟨by linarith, by linarith⟩
    obtain ⟨z, hz⟩ := hmid
    rcases h4 x with hx | hx <;> rcases h4 y with hy | hy <;> rcases h4 z with hz' | hz' <;>
      linarith
  have hconst : ∀ x, ρ x = ρ 0 := by
    intro x
    rcases lt_trichotomy (ρ x) (ρ 0) with h | h | h
    · exact (key _ _ h).elim
    · exact h
    · exact (key _ _ h).elim
  have hI := hρ.integral_one
  have hfun : ρ = fun _ => ρ 0 := funext hconst
  rw [hfun] at hI
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hinf := measure_univ_of_isAddLeftInvariant (volume : Measure (Euc d))
  simp only [smul_eq_mul, integral_const, Measure.real, hinf, ENNReal.toReal_top, zero_mul] at hI
  exact zero_ne_one hI

theorem s81bd_critical_response {d : ℕ} (hd : 2 ≤ d)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ)
    (hbdd : ∃ M : ℝ, ∀ x, ρ x ≤ M) (hcont : Continuous ρ)
    (β : ℝ) (hβ : 0 < β) :
    MemL2Zero (withDensityReal ρ) (critBiasDensity d β ρ) ∧
      0 < l2Inner (withDensityReal ρ) ρ (critBiasDensity d β ρ) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hM⟩ := hbdd
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : Q34.Q34Hyp d ((d : ℝ) / 2) ρ M :=
    ⟨hd1, by linarith, by linarith, hρ, hM⟩
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hρL : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact hM x)
  have hρi : Integrable ρ (withDensityReal ρ) := hρL.integrable one_le_two
  set ν := withDensityReal ρ with hν
  set g := rieszKernel d ((d : ℝ) / 2) with hg
  set r := responseInverse g ν β ρ with hr
  have hresp : IsResponse g ν β ρ r := S71.s71_resp_spec hq hβ hρL
  have hr0 : MemL2Zero ν r := hresp.1
  set c : ℝ := β ^ 2 * sphereArea d / d with hc
  have hcpos : 0 < c := by
    have := s81bd_sphereArea_pos hd1
    have hdpos : (0 : ℝ) < d := by linarith
    rw [hc]; positivity
  have hcb : critBiasDensity d β ρ = fun x => c * r x := rfl
  rw [hcb]
  refine ⟨⟨hr0.1.const_mul c, ?_⟩, ?_⟩
  · rw [integral_const_mul, hr0.2, mul_zero]
  -- pairing
  have hri : Integrable r ν := hr0.1.integrable one_le_two
  set m := pair ν ρ with hm
  set f := projMean ν ρ with hf
  have hfL : MemL2Zero ν f := S71.s71_memL2Zero_projMean hρL
  have hfr : Integrable (fun x => f x * r x) ν := hfL.1.integrable_mul hr0.1
  have hsplit : l2Inner ν ρ r = l2Inner ν f r := by
    unfold l2Inner
    have : (fun x => ρ x * r x) = fun x => f x * r x + m * r x := by
      funext x; simp only [hf, projMean]; ring
    rw [this, integral_add hfr (hri.const_mul m), integral_const_mul, hr0.2, mul_zero, add_zero]
  have hl : l2Inner ν ρ (fun x => c * r x) = c * l2Inner ν ρ r := by
    unfold l2Inner
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hl]
  refine mul_pos hcpos ?_
  rw [hsplit]
  obtain ⟨-, huniq, hlow, -, -⟩ := Q34.partD hq hβ hfL
  set rf := responseInverse g ν β f with hrf
  have hrf1 : IsResponse g ν β f rf := S71.s71_resp_spec hq hβ hfL.1
  have hr2 : IsResponse g ν β f r := (S71.s71_isResponse_projMean hρi).2 hresp
  have hae : r =ᵐ[ν] rf := huniq _ _ hr2 hrf1
  have heq : l2Inner ν f r = l2Inner ν f rf := by
    unfold l2Inner
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  rw [heq]
  refine lt_of_lt_of_le ?_ hlow
  have hMg0 := Q34.Mg_nonneg hd1 (show ((d : ℝ) / 2) < d by linarith) hM0
  have hden : 0 < 1 + β * Q34.Mg d ((d : ℝ) / 2) M := by positivity
  refine div_pos ?_ hden
  have hsqi : Integrable (fun x => f x ^ 2) ν := hfL.1.integrable_sq
  have hnn : 0 ≤ ∫ x, f x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  rcases hnn.lt_or_eq with hlt | heq0
  · exact hlt
  · exfalso
    have h0 := (integral_eq_zero_iff_of_nonneg (f := fun x => f x ^ 2) (fun x => sq_nonneg _)
      hsqi).1 heq0.symm
    refine s81bd_density_not_ae_const hd1 ρ hρ hcont m ?_
    filter_upwards [h0] with x hx
    have : f x = 0 := by simpa using hx
    simp only [hf, projMean] at this
    linarith

/-- The unconditional part of `critical_whole_marginal`: positivity of the pairing for every `β > 0` and
`L²` membership of the critical bias density (a Lipschitz density is continuous). -/
theorem s81bd_marginal_positivity {d : ℕ} (hd : 2 ≤ d) (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ)
    (hbdd : ∃ M : ℝ, ∀ x, ρ x ≤ M) (hlip : ∃ Λ : ℝ≥0, LipschitzWith Λ ρ) :
    (∀ β : ℝ, 0 < β → 0 < l2Inner (withDensityReal ρ) ρ (critBiasDensity d β ρ)) ∧
      ∀ β : ℝ, 0 < β → MemLp (critBiasDensity d β ρ) 2 (withDensityReal ρ) := by
  obtain ⟨Λ, hΛ⟩ := hlip
  have hcont : Continuous ρ := hΛ.continuous
  exact ⟨fun β hβ => (s81bd_critical_response hd ρ hρ hbdd hcont β hβ).2,
    fun β hβ => (s81bd_critical_response hd ρ hρ hbdd hcont β hβ).1.1⟩

end HRS.Whole.BreakdownS81
