import HRS.MS.R2WinErrAux17
import HRS.MS.WsStatAux2
import HRS.MS.WsStatAux4

/-!
# S10.4 input `hcls`: uniform density, moment, log-moment bounds and the completion constant for the class `IsR2WindowTrajectory`

`s104_hcls`: `S104ClassInput d s a β εstar c₁ C₁` for every `εstar c₁ C₁`, given only the joint measurability of the clamped density along the
nonlinear trajectories (`hjmNL`; for the stationary trajectory it is trivial).  Ingredients: `S21.s21_thermal_bounded` (thermal density
bounded, with log moment), `S21.s21_thermal_second_integrable`, the ratio bound `ρ^t ≤ C₁ρ_β` of `IsResultingSolution`, domination of measures
`withDensityReal (ρ t) ≤ Cr • withDensityReal ρ_β`, and the completion clauses `S21.s21_clause1_stationary/resulting`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

lemma s104_dom_of_le {ρ ρ0 : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hρ0 : HRS.Whole.IsProbDensity ρ0)
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ x, ρ x ≤ c * ρ0 x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal c • HRS.Whole.withDensityReal ρ0 := by
  refine Measure.le_iff.2 fun A hA => ?_
  unfold HRS.Whole.withDensityReal
  rw [Measure.smul_apply, withDensity_apply _ hA, withDensity_apply _ hA,
    smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (hle x)

lemma s104_dom_integral {μ ν : Measure (Euc d)} {c : ℝ} (hc : 0 ≤ c) (h : μ ≤ ENNReal.ofReal c • ν)
    {f : Euc d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f ν) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ c * ∫ x, f x ∂ν := by
  have hfi : Integrable f (ENNReal.ofReal c • ν) := hf.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hfi.mono_measure h, ?_⟩
  calc ∫ x, f x ∂μ ≤ ∫ x, f x ∂(ENNReal.ofReal c • ν) :=
        integral_mono_measure h (Eventually.of_forall hf0) hfi
    _ = c * ∫ x, f x ∂ν := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-- The bounds and the completion constant of `S104ClassInput` (all but the joint measurability of the clamped density). -/
theorem s104_hcls_bounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) :
    ∃ M L Mom C₀c : ℝ, 0 ≤ C₀c ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
    IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ →
    (∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) ∧ (∀ x, ρ t x ≤ M) ∧
      Integrable (fun x => ‖x‖ ^ 2 * ρ t x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ t)) ≤ Mom ∧
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ t)) L)) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀c N) := by
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨0, 0, 0, 0, le_rfl, fun ρβ h => absurd ⟨ρβ, h⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  obtain ⟨Λ, hΛ⟩ := S21.s21_thermal_bounded hd hs0 hsd ha hβ
  obtain ⟨hp0, hb0, hl0⟩ := hΛ ρ0 hρ0
  obtain ⟨C₀s, h0s, hcs⟩ := S21.s21_clause1_stationary hd hs0 hsd ha hβ
  obtain ⟨C₀r, h0r, hcr⟩ := S21.s21_clause1_resulting hd hs0 hsd ha hβ C₁
  have hρeq : ρ0 = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0
  have hsec : Integrable (fun x : Euc d => ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ0) := by
    have := S21.s21_thermal_second_integrable hd hs0 hsd ha hβ
    rw [hρeq]; exact this
  set Cr : ℝ := max C₁ 1 with hCr
  have hCr1 : 1 ≤ Cr := le_max_right _ _
  have hCr0 : 0 ≤ Cr := by linarith
  set I2 : ℝ := ∫ x, ‖x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ0) with hI2
  set Lg : ℝ := ∫ x, Real.log (2 + ‖x‖) ∂(HRS.Whole.withDensityReal ρ0) with hLg
  refine ⟨Cr * |Λ|, Cr * Lg, Cr * I2, max C₀s C₀r, (h0s.trans (le_max_left _ _)), ?_⟩
  intro ρβ hρβ ρ htraj
  have hρβeq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ, hρeq]
  subst hρβeq
  -- common bounds along the trajectory
  have hcommon : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) ∧ (∀ x, ρ t x ≤ Cr * ρβ x) := by
    rcases htraj with hst | ⟨ε, ψ, -, hres⟩
    · intro t ht
      rw [hst]
      exact ⟨hp0, fun x => by nlinarith [hp0.nonneg x]⟩
    · intro t ht
      refine ⟨(hres.global t).density t ⟨ht, le_rfl⟩, fun x => ?_⟩
      exact (hres.ratio t ht x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hp0.nonneg x))
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨hpt, hle⟩ := hcommon t ht
    have hdom := s104_dom_of_le hpt hp0 hCr0 hle
    have hcnn : ∀ x : Euc d, 0 ≤ ‖x‖ ^ 2 := fun x => by positivity
    obtain ⟨hi2, hv2⟩ := s104_dom_integral hCr0 hdom hcnn hsec
    have hlogn : ∀ x : Euc d, 0 ≤ Real.log (2 + ‖x‖) := fun x => Real.log_nonneg (by
      have := norm_nonneg x; linarith)
    obtain ⟨hil, hvl⟩ := s104_dom_integral hCr0 hdom hlogn hl0
    refine ⟨hpt, fun x => ?_, ?_, ?_, fun _ => ⟨hil, hvl⟩⟩
    · exact (hle x).trans (mul_le_mul_of_nonneg_left ((hb0 x).trans (le_abs_self _)) hCr0)
    · have := (HRS.MS.TcR.tc2_integrable_nu hpt (fun x => ‖x‖ ^ 2)).1 hi2
      exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
    · unfold secondMomentOf HRS.Whole.pair
      exact hv2
  · intro N hN t ht X hX
    rcases htraj with hst | ⟨ε, ψ, -, hres⟩
    · have := hcs (max C₀s C₀r) (le_max_left _ _) ρβ hρβ N hN X hX
      rw [hst]; exact this
    · exact hcr (max C₀s C₀r) (le_max_right _ _) ρβ hρβ εstar ε ψ c₁ ρ hres N hN t ht X hX

theorem s104_hcls (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ)
    (hjmNL : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ (ε : ℝ) (ψ : Euc d → ℝ)
      (ρ : ℝ → Euc d → ℝ), IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ T' : ℝ, 0 ≤ T' →
      Measurable fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2) :
    S104ClassInput d s a β εstar c₁ C₁ := by
  obtain ⟨M, L, Mom, C₀c, h0, hB⟩ := s104_hcls_bounds hd hs0 hsd ha hβ εstar c₁ C₁
  refine ⟨M, L, Mom, C₀c, h0, fun ρβ hρβ ρ htraj => ⟨(hB ρβ hρβ ρ htraj).1, (hB ρβ hρβ ρ htraj).2, ?_⟩⟩
  intro T' hT'
  rcases htraj with hst | ⟨ε, ψ, -, hres⟩
  · rw [hst]
    exact (hρβ.2.1).measurable.comp measurable_snd
  · exact hjmNL ρβ hρβ ε ψ ρ hres T' hT'

end HRS.MS.R2WinErr
