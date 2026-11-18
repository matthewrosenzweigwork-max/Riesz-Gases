import HRS.MS.QsfAux3
import HRS.MS.WrStatic
import HRS.MS.WlStaticTie
import HRS.MS.CanThm
import HRS.MS.Ste
import HRS.MS.ThCorrAux1
import HRS.MS.ThmLog
import HRS.Energy.WeakReference

/-!
# S4.5 packet B3: the static bundle for the canonical Gibbs law of the thermal reference

Namespace `S45`.  For `0 ≤ s < d`, `d ≥ 2`, `a, β > 0` there is `C` such that for every `N ≥ 2` the canonical
Gibbs law `P_N` (`= modulatedGibbs` of the thermal reference by `euc_thermal_canonical_proof` /
`logThermal_canonical_proof`) is an exchangeable probability measure with the calibrated estimates
(`S45Static`): linear variance, density bounds of `m_N = P_N^{(1)}` with respect to `μ`, and the quadratic
variance bound of the commutator kernel of every Lipschitz field for the references `μ` and `m_N`
(`s > 0`: `euc_static_proof`, `euc_static_commutator_proof`; `s = 0`: `r2_log_static_proof`, with
`HasSphericalBound` from `logThermal_stereographic_proof`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The static facts at particle number `N`. -/
structure S45Static (d : ℕ) (s a β C : ℝ) (N : ℕ) : Prop where
  prob : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β)
  exch : IsExchangeable (canonicalGibbs (rieszKernel d s) (confinement a) N β)
  linear : ∀ f : Euc d → ℝ, MemLp f 2 (thermalMeasure d s a β) →
    evariance (linStat f) (canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
      ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(thermalMeasure d s a β))
  marg : ∃ φ : Euc d → ℝ, Measurable φ ∧
    firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β) =
      (thermalMeasure d s a β).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    (∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧ MemLp (fun x => φ x - 1) 2 (thermalMeasure d s a β) ∧
    l2Norm (thermalMeasure d s a β) (fun x => φ x - 1) ≤ C * HRS.deltaN d s N
  comm : ∀ (Λ : ℝ≥0) (v : Euc d → Euc d), LipschitzWith Λ v →
    QuadraticVarianceBound (commutatorKernel d s v)
      (canonicalGibbs (rieszKernel d s) (confinement a) N β) (thermalMeasure d s a β)
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N) ∧
    QuadraticVarianceBound (commutatorKernel d s v)
      (canonicalGibbs (rieszKernel d s) (confinement a) N β)
      (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β))
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N)

theorem s45_modGibbs_prob {g : Euc d → ℝ} {N : ℕ} {β : ℝ} {μ : Measure (Euc d)}
    [IsProbabilityMeasure μ] (h : GibbsWellDefined (fun x y => g (x - y)) N β μ) :
    IsProbabilityMeasure (modulatedGibbs g N β μ) := by
  constructor
  have hZ : 0 < gibbsNormalizer g N β μ := h.normalizer_pos
  have hint : Integrable (fun X : EucConfig d N => Real.exp (-β * N * modulatedEnergy g X μ))
      (Measure.pi fun _ => μ) := h.weight_integrable
  unfold modulatedGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  have : ∫⁻ X, ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g X μ)) ∂(Measure.pi fun _ : Fin N => μ)
      = ENNReal.ofReal (gibbsNormalizer g N β μ) := by
    unfold gibbsNormalizer
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  rw [this]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top

theorem s45_rieszKernel_even (s : ℝ) (x : Euc d) : rieszKernel d s (-x) = rieszKernel d s x := by
  unfold rieszKernel; simp

theorem s45_static_all (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → S45Static d s a β C N := by
  obtain ⟨c, M₀, m₂, hc, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
    (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hS⟩ := hU 0
  have href := hS a β le_rfl le_rfl le_rfl le_rfl
  have hρ : IsProbDensity (thermalDensity d s a β) := href.prob
  have hM : ∀ x, thermalDensity d s a β x ≤ M₀ := fun x =>
    HRS.MS.TcR.tc2_le_M0 hρ hc href.gauss x
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hsd2 : (0 : ℝ) < d / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rcases hs0.eq_or_lt with h0 | h0
  · -- s = 0
    subst h0
    obtain ⟨-, A, hA⟩ := HRS.MS.Thm.logThermal_stereographic_proof hd a β ha hβ
    obtain ⟨C, hC⟩ := HRS.MS.Wl.r2_log_static_proof hd β β A hβ le_rfl
    obtain ⟨C', hC'⟩ := HRS.MS.Wl.r2_log_static_commutator_proof hd β β A hβ le_rfl
    refine ⟨max (max C C') 0, le_max_right _ _, fun N hN => ?_⟩
    have hCle : C ≤ max (max C C') 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' ≤ max (max C C') 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C C') 0 := le_max_right _ _
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC (thermalDensity d 0 a β) hρ hA β ⟨le_rfl, le_rfl⟩ N hN
    have hcan := HRS.MS.Can2.logThermal_canonical_proof hd a β ha hβ N
    have hδ : HRS.deltaN d 0 N = (N : ℝ)⁻¹ := by
      unfold HRS.deltaN; rw [if_pos hsd2]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d 0) N β (thermalMeasure d 0 a β)) :=
      s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d 0) N β (thermalMeasure d 0 a β)) :=
      modulatedGibbs_isExchangeable _ _ _ (s45_rieszKernel_even 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(thermalMeasure d 0 a β) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      refine ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, ?_⟩, hφ2, ?_⟩
      · refine (hφb x).2.trans ?_
        have hp : (1 + ‖x‖ ^ 2) ^ (-(β / (2 * N))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
            (by have : 0 < β / (2 * N) := by positivity
                linarith)
        have h1 : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(β / (2 * N))) := Real.rpow_nonneg (by positivity) _
        calc C * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * N)))
            ≤ max (max C C') 0 * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * N))) :=
              mul_le_mul_of_nonneg_right hCle h1
          _ ≤ max (max C C') 0 * 1 := mul_le_mul_of_nonneg_left hp hC0
          _ = _ := mul_one _
      · rw [hδ]
        refine hφn.trans ?_
        have : C / N = C * (N : ℝ)⁻¹ := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hCle (by positivity)
    · intro Λ v hv
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' (thermalDensity d 0 a β) hρ hA β ⟨le_rfl, le_rfl⟩ N hN Λ v hv
      have hb : C' * (Λ : ℝ) ^ 2 / N / N ≤ max (max C C') 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d 0 N / N := by
        rw [hδ]
        have : C' * (Λ : ℝ) ^ 2 / N / N = C' * (Λ : ℝ) ^ 2 * (N : ℝ)⁻¹ / N := by
          field_simp
        rw [this]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩
  · -- 0 < s < d
    obtain ⟨C, hC⟩ := HRS.MS.Wr.euc_static_proof hd h0 hsd β β M₀ hβ le_rfl
    obtain ⟨C', hC'⟩ := HRS.MS.Wr.euc_static_commutator_proof hd h0 hsd β β M₀ hβ le_rfl
    refine ⟨max (max C (C' * s ^ 2)) 0, le_max_right _ _, fun N hN => ?_⟩
    have hCle : C ≤ max (max C (C' * s ^ 2)) 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' * s ^ 2 ≤ max (max C (C' * s ^ 2)) 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C (C' * s ^ 2)) 0 := le_max_right _ _
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC (thermalDensity d s a β) hρ hM β ⟨le_rfl, le_rfl⟩ N hN
    have hcan := (HRS.MS.Can2.euc_thermal_canonical_proof hd h0 hsd a β ha hβ).1 N
    have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s (by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β)) :=
      s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β)) :=
      modulatedGibbs_isExchangeable _ _ _ (s45_rieszKernel_even s)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(thermalMeasure d s a β) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      exact ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans hCle⟩, hφ2,
        hφn.trans (mul_le_mul_of_nonneg_right hCle hδ0)⟩
    · intro Λ v hv
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' (thermalDensity d s a β) hρ hM β ⟨le_rfl, le_rfl⟩ N hN Λ v hv
      have hb : C' * (s * (Λ : ℝ)) ^ 2 * HRS.deltaN d s N / N ≤
          max (max C (C' * s ^ 2)) 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N := by
        have e : C' * (s * (Λ : ℝ)) ^ 2 = (C' * s ^ 2) * (Λ : ℝ) ^ 2 := by ring
        rw [e]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩

end S45

end
