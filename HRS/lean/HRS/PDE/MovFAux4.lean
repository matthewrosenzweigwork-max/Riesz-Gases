import HRS.PDE.MovFAux3
import HRS.Equilibrium.PreparationAttractive

/-!
# MOVF Aux4: bridge C for the iid logarithmic preparation (`β₀ = 0`, `s = 0`)

`movf_prepared_initial_Lp_iid`: `‖dμ^{⊗N}/dℚ_{N,β}‖_{L^{p₀}(ℚ_{N,β})} = (Z_β^{p₀-1} Z_γ)^{1/p₀}`, `γ = -(p₀-1)β`; the attractive
partition function is bounded by `log_prep_attractive` (small negative coupling), `Z_β` by `movf_pressure_bounds`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_prepared_initial_Lp_iid (hd : 2 ≤ d) {μ : Torus d → ℝ} (hμ : IsProbDensity μ)
    (hck : Torus.IsCk 2 μ) (hpos : ∀ x, 0 < μ x) {β : ℝ} (hβ : 0 < β) :
    ∃ p₀ C : ℝ, 1 < p₀ ∧ ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d 0 N)) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : ((0 : ℕ) : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  haveI := isProb_withDensityReal hμ
  have hc : Continuous μ := mova_continuous_of_isCk hck
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn (f := μ) hc.continuousOn
  have hΛ' : ∀ x, μ x ≤ Λ := fun x => (le_abs_self _).trans (by simpa using hΛ x trivial)
  obtain ⟨a, ha, C₂, hC₂⟩ := log_prep_attractive hd μ hμ Λ hΛ'
  obtain ⟨C₁, hC₁⟩ := movf_pressure_bounds hd1 (le_refl (0 : ℝ)) hsd' hμ hck hpos (βm := β) (βp := β) hβ
  set p₀ : ℝ := 1 + min 1 (a / β) with hp₀
  have hp₀1 : 1 < p₀ := by
    have : 0 < min 1 (a / β) := lt_min one_pos (div_pos ha hβ)
    linarith
  have hγa : (p₀ - 1) * β ≤ a := by
    have h1 : min 1 (a / β) ≤ a / β := min_le_right _ _
    have : (p₀ - 1) * β ≤ a / β * β := by
      rw [hp₀]; simp only [add_sub_cancel_left]; exact mul_le_mul_of_nonneg_right h1 hβ.le
    rwa [div_mul_cancel₀ _ hβ.ne'] at this
  have hγ0 : 0 < (p₀ - 1) * β := mul_pos (by linarith) hβ
  set C₂' : ℝ := max C₂ 1 with hC₂'
  have hC₂'p : 0 < C₂' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨p₀, (1 / p₀) * (C₁ * (p₀ - 1) + Real.log C₂'), hp₀1, fun N hN => ?_⟩
  have hN0 : 0 < N := by omega
  have hδ : deltaN d 0 N = (N : ℝ)⁻¹ := by
    unfold deltaN
    rw [if_pos (by simpa using (by positivity : (0 : ℝ) < d / 2))]
  have hNδ : (N : ℝ) * deltaN d 0 N = 1 := by
    rw [hδ]; exact mul_inv_cancel₀ (by exact_mod_cast hN0.ne')
  obtain ⟨hm, Cc, hCc⟩ := movf_energy_facts hd1 (le_refl (0 : ℝ)) hsd' hμ hc hN0 (N := N)
  have hF : Measurable fun X : Config d N =>
      (N : ℝ) * modulatedEnergyKernel (periodicRiesz d 0) X (withDensityReal μ) := measurable_const.mul hm
  have hcF : ∀ X : Config d N, -((N : ℝ) * Cc) ≤
      (N : ℝ) * modulatedEnergyKernel (periodicRiesz d 0) X (withDensityReal μ) := fun X => by
    have := hCc X
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hQ : ∀ b : ℝ, 0 ≤ b → modulatedGibbs (periodicRiesz d 0) N b (withDensityReal μ) =
      (Measure.pi fun _ : Fin N => withDensityReal μ).tilted (fun X : Config d N =>
        -b * ((N : ℝ) * modulatedEnergyKernel (periodicRiesz d 0) X (withDensityReal μ))) := by
    intro b hb
    rw [movf_modGibbs_eq_tilted hd1 (le_refl (0 : ℝ)) hsd' hμ hc hN0 hb]
    congr 1
    funext X; ring
  -- the attractive moment
  set Ge : Config d N → ℝ := fun X => Real.exp (-(p₀ * 0 - (p₀ - 1) * β) * ((N : ℝ) *
      modulatedEnergyKernel (periodicRiesz d 0) X (withDensityReal μ))) with hGe
  have hGm : Measurable Ge := Real.measurable_exp.comp (measurable_const.mul hF)
  have hKEeq : ∫⁻ X : Config d N, ENNReal.ofReal (Ge X) ∂(Measure.pi fun _ => withDensityReal μ) =
      PreparationAux.KE (periodicRiesz d 0) N (-((p₀ - 1) * β)) (withDensityReal μ) := by
    unfold PreparationAux.KE
    refine lintegral_congr fun X => ?_
    simp only [hGe]
    congr 2
    ring
  have hKEle : PreparationAux.KE (periodicRiesz d 0) N (-((p₀ - 1) * β)) (withDensityReal μ) ≤
      ENNReal.ofReal C₂ := hC₂ N hN _ ⟨by linarith, by linarith⟩
  have hGfin : ∫⁻ X : Config d N, ENNReal.ofReal (Ge X) ∂(Measure.pi fun _ => withDensityReal μ) ≠ ⊤ := by
    rw [hKEeq]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKEle
  have hGi : Integrable Ge (Measure.pi fun _ : Fin N => withDensityReal μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hGm.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).1 hGfin
  have hZg : ∫ X : Config d N, Ge X ∂(Measure.pi fun _ => withDensityReal μ) ≤ C₂' := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall fun x => (Real.exp_pos _).le)
    rw [hKEeq] at h1
    have h2 : ENNReal.ofReal (∫ X : Config d N, Ge X ∂(Measure.pi fun _ => withDensityReal μ)) ≤
        ENNReal.ofReal C₂' := h1 ▸ hKEle.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact (ENNReal.ofReal_le_ofReal_iff hC₂'p.le).1 h2
  rw [hQ 0 le_rfl, hQ β hβ.le]
  obtain ⟨hac, hnorm⟩ := movf_lp_tilted (Measure.pi fun _ : Fin N => withDensityReal μ) hF hcF
    le_rfl hβ.le hp₀1 hGi
  refine ⟨hac, ?_⟩
  rw [hnorm]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨hb1, hb2⟩ := hC₁ N hN β ⟨le_rfl, le_rfl⟩
  rw [movf_gibbsNormalizer_eq] at hb1 hb2
  have hZ0 : ∫ X : Config d N, Real.exp (-0 * ((N : ℝ) * modulatedEnergyKernel (periodicRiesz d 0) X
      (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ) = 1 := by simp
  rw [hZ0, Real.one_rpow, mul_one]
  set Zb := ∫ X : Config d N, Real.exp (-β * ((N : ℝ) * modulatedEnergyKernel (periodicRiesz d 0) X
    (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ) with hZb
  set Zg := ∫ X : Config d N, Ge X ∂(Measure.pi fun _ => withDensityReal μ) with hZg'
  have hZbp : 0 < Zb := lt_of_lt_of_le (Real.exp_pos _) hb1
  have hZgp : 0 < Zg := integral_exp_pos hGi
  have hp0 : 0 < p₀ := by linarith
  have hZb' : Zb ≤ Real.exp C₁ := by
    have := hb2
    rwa [mul_assoc C₁, hNδ, mul_one] at this
  have e1 : Zb ^ (p₀ - 1) ≤ Real.exp (C₁ * (p₀ - 1)) := by
    rw [Real.exp_mul]; exact Real.rpow_le_rpow hZbp.le hZb' (by linarith)
  have e3 : Zb ^ (p₀ - 1) * Zg ≤ Real.exp (C₁ * (p₀ - 1)) * C₂' := by
    gcongr
  have hexpC : Real.exp ((1 / p₀) * (C₁ * (p₀ - 1) + Real.log C₂') * N * deltaN d 0 N) =
      (Real.exp (C₁ * (p₀ - 1)) * C₂') ^ (1 / p₀) := by
    rw [mul_assoc _ (N : ℝ), hNδ, mul_one, mul_comm, Real.exp_mul, Real.exp_add, Real.exp_log hC₂'p]
  rw [hexpC]
  exact Real.rpow_le_rpow (by positivity) e3 (by positivity)

end HRS

end
