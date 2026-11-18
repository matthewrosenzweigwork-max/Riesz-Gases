import HRS.MS.FinNoiseAux44
import HRS.MS.S81pFiniteNoise
import HRS.MS.WsStatAux13
import HRS.MS.CritWholeW2Shift

/-!
# S8.1 (worker S81S): the linear input of a canonical realization

`s81s_linear_input`: for the critical model there is a constant `Cin` (depending only on `d, a, β`) such that every canonical
realization satisfies `LinearInputBounds d (d/2) N (withDensityReal ρβ) Cin P (X t)` at every time (the hypothesis `hlin` of the
frozen `finite_noise`).  This is the static input `S45.s45_static_all` transported along the Gibbs law of `X t`; the variance clause of
`LinearInputBounds` is stated for every `f ∈ L²(μ)` (no measurability), which is handled through the absolute continuity of the
marginals with respect to `μ`.

`s81s_deltaN_le`: `deltaN d (d/2) N ≤ 2 N^{-1/2}`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81S

variable {d : ℕ}

theorem s81s_deltaN_le {N : ℕ} (hN : 1 ≤ N) :
    HRS.deltaN d ((d : ℝ) / 2) N ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hs1 : 1 ≤ Real.sqrt N := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
  unfold HRS.deltaN
  rw [if_neg (lt_irrefl _), if_pos rfl]
  have hlog : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have hl2 : Real.log N = 2 * Real.log (Real.sqrt N) := by
    rw [show (N : ℝ) = Real.sqrt N ^ 2 from hsq.symm, Real.log_pow]
    simp [hsq]
  have hl3 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hs
  have hneg : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hN0.le]
  rw [hlog, hneg]
  have hNs : (N : ℝ)⁻¹ = ((Real.sqrt N)⁻¹) ^ 2 := by
    rw [inv_pow, hsq]
  rw [hNs]
  have : (1 + Real.log N) ≤ 2 * Real.sqrt N := by nlinarith
  calc ((Real.sqrt N)⁻¹) ^ 2 * (1 + Real.log N) ≤ ((Real.sqrt N)⁻¹) ^ 2 * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * (Real.sqrt N)⁻¹ := by field_simp

theorem s81s_linStat_eq (f : Euc d → ℝ) {N : ℕ} (Y : EucConfig d N) :
    linStat f Y = (N : ℝ)⁻¹ * ∑ i, f (Y i) := by
  unfold linStat HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, smul_eq_mul]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem s81s_evariance_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X' : Ω → ℝ}
    (h : X =ᵐ[P] X') : evariance X P = evariance X' P := by
  unfold evariance
  rw [integral_congr_ae h]
  exact lintegral_congr_ae (by filter_upwards [h] with ω hω; rw [hω])

theorem s81s_evariance_map_ae {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (P : Measure Ω)
    (Y : Ω → α) (hY : Measurable Y) (g : α → ℝ) (hg : Measurable g) :
    evariance (fun ζ => g (Y ζ)) P = evariance g (P.map Y) :=
  HRS.MS.S21.s21_evariance_map P Y hY g hg

theorem s81s_marg_ac {N : ℕ} (hN : 1 ≤ N) (Γ : Measure (EucConfig d N)) [IsProbabilityMeasure Γ]
    (hex : IsExchangeable Γ) (μ : Measure (Euc d)) (hfm : firstMarginal Γ ≪ μ) (i : Fin N) :
    Γ.map (fun X : EucConfig d N => X i) ≪ μ := by
  intro A hA
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA
  refine measure_mono_null hAA' ?_
  rw [Measure.map_apply (measurable_pi_apply i) hA'm]
  have h1 : meanEmpirical Γ A' = 0 := by
    rw [meanEmpirical_eq_firstMarginal Γ hex hN]
    exact hfm hA'0
  rw [meanEmpirical_apply Γ hA'm] at h1
  have h2 : (∑ j : Fin N, Γ {X | X j ∈ A'}) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top N))
    · exact h
  exact (Finset.sum_eq_zero_iff.1 h2 i (Finset.mem_univ i))

theorem s81s_linear_input (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Cin : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X → ∀ t : ℝ≥0,
        LinearInputBounds d ((d : ℝ) / 2) N (withDensityReal ρβ) Cin P (X t) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨Cs, hCs0, hStat⟩ := S45.s45_static_all hd hs0.le hsd ha hβ
  refine ⟨Cs, fun ρβ hρβ N hN Ω _ P _ X₀ W X hR t => ?_⟩
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.Whole.S78.s78_eq_thermalDensity hd hs0 hsd ha hβ hρβ
  have hμ : withDensityReal ρβ = thermalMeasure d ((d : ℝ) / 2) a β := by rw [hρeq]; rfl
  have hSN := hStat N hN
  have hN1 : 1 ≤ N := by omega
  have hlaw : law P (X t) = canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β :=
    HRS.Whole.S79.s79_law_X_eq hR t
  have hXm : Measurable (X t) := (hR.solution t).adapted t
  haveI := hSN.prob
  rw [hμ]
  obtain ⟨φ, hφm, hfm, hφb, hφL, hφn⟩ := hSN.marg
  refine ⟨⟨φ, hφm, ?_, hφb, hφL, hφn⟩, ?_⟩
  · rw [hlaw]; exact hfm
  · intro f hf
    set μ := thermalMeasure d ((d : ℝ) / 2) a β with hμdef
    set Γ := canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β with hΓ
    have hac : ∀ i : Fin N, Γ.map (fun X : EucConfig d N => X i) ≪ μ := by
      refine s81s_marg_ac hN1 Γ hSN.exch μ ?_
      rw [hfm]; exact withDensity_absolutelyContinuous _ _
    set f' : Euc d → ℝ := hf.aestronglyMeasurable.mk f with hf'
    have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hff' : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
    have hΓae : ∀ᵐ X ∂Γ, ∀ i, f (X i) = f' (X i) := by
      rw [ae_all_iff]
      intro i
      exact ae_of_ae_map (measurable_pi_apply i).aemeasurable ((hac i).ae_le hff')
    have hlsΓ : linStat f =ᵐ[Γ] linStat f' := by
      filter_upwards [hΓae] with X hX
      rw [s81s_linStat_eq, s81s_linStat_eq]
      simp only [hX]
    have hPae : ∀ᵐ ζ ∂P, ∀ i, f (X t ζ i) = f' (X t ζ i) := by
      have : ∀ᵐ X ∂(P.map (X t)), ∀ i, f (X i) = f' (X i) := by
        have : P.map (X t) = Γ := hlaw
        rw [this]; exact hΓae
      exact ae_of_ae_map hXm.aemeasurable this
    have hlsP : (fun ζ => linStat f (X t ζ)) =ᵐ[P] fun ζ => linStat f' (X t ζ) := by
      filter_upwards [hPae] with ζ hζ
      rw [s81s_linStat_eq, s81s_linStat_eq]
      simp only [hζ]
    have hmeas' : Measurable (linStat f' : EucConfig d N → ℝ) := by
      have : (linStat f' : EucConfig d N → ℝ) = fun Y => (N : ℝ)⁻¹ * ∑ i, f' (Y i) :=
        funext fun Y => s81s_linStat_eq f' Y
      rw [this]
      exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hf'm.comp (measurable_pi_apply i))
    calc evariance (fun ζ => linStat f (X t ζ)) P
        = evariance (fun ζ => linStat f' (X t ζ)) P := s81s_evariance_congr hlsP
      _ = evariance (linStat f') (P.map (X t)) := s81s_evariance_map_ae P (X t) hXm _ hmeas'
      _ = evariance (linStat f') Γ := by rw [show P.map (X t) = Γ from hlaw]
      _ = evariance (linStat f) Γ := (s81s_evariance_congr hlsΓ).symm
      _ ≤ _ := hSN.linear f hf

end HRS.Whole.S81S
