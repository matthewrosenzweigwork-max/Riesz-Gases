import HRS.MS.R26T8AP08h
import HRS.MS.R26T8AR1c

/-!
# S8.2 T8A R2: the double centring differs from the function by a smooth correction
`r26t8a_R2_center_smooth`: for `Conormal k b M σ A R` (`σ < d`) the correction `r2CenterKernel μ R - R` is `Conormal k b' M σ' (C A)` for EVERY `(b', σ')`
(`C` independent of them): it equals `-(row mean)(x) - (column mean)(y) + const`, smooth with weighted bounded jets.  Same proof as `r26t8a_f25_center`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_R2_center_smooth {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (k b : ℕ) {σ M : ℝ}
    (hM : 0 ≤ M) (hσd : σ < d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρk : ContDiff ℝ (k : WithTop ℕ∞) ρ) (hρc : Continuous ρ) {Kρ : ℝ} (hKρ0 : 0 ≤ Kρ)
    (hK : ∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ Kρ * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : ℝ}, 0 ≤ A → ∀ {R : Euc d → Euc d → ℝ}, Conormal k b M σ A R → ∀ (b' : ℕ) (σ' : ℝ),
      Conormal k b' M σ' (C * A) (fun x y => r2CenterKernel (HRS.Whole.withDensityReal ρ) R x y - R x y) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  haveI hprob := s85_isProb hρ
  obtain ⟨Crow, hCrow0, hrow⟩ := r26t8a_row_lemma hd k b M σ hM hσd Kρ hKρ0
  obtain ⟨Bq, hBq0, hfub⟩ := r26t8a_f25_fubini hd b hM hσd hρ hρc hKρ0
    (fun y => by
      have := hK 0 (Nat.zero_le _) y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg y)] at this)
  have hKρ : ∀ y : Euc d, ρ y ≤ Kρ * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)) := fun y => by
    have := hK 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg y)] at this
  have hai := r26t8a_f25_a_int hd hρ hρc hM hKρ0 hKρ
  have hjbI : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρ) := by
    rw [r26t8a_f25_wd_integrable hρ]; exact hai
  have hI0 : 0 ≤ ∫ y, ρ y * jbracket y ^ M :=
    integral_nonneg fun y => mul_nonneg (hρ.nonneg y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hMom : ∫ y, jbracket y ^ M ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * jbracket y ^ M :=
    r26t8a_f25_wd_integral hρ _
  refine ⟨2 ^ k * Crow * (2 + ∫ y, ρ y * jbracket y ^ M), by positivity, ?_⟩
  intro A hA R hR b' σ'
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hμ
  have hAI : 0 ≤ A := hA
  obtain ⟨hRfI, hRrowI, hRnorm, hRswap⟩ := hfub hA hR
  have hRT : Conormal k b M σ A (fun x y => R y x) := r26t8a_f24_conormal_swap hchi hR
  obtain ⟨hTfI, hTrowI, hTnorm, hTswap⟩ := hfub hA hRT
  obtain ⟨hYc, hYj⟩ := hrow ρ hρk hK R A hA hR
  obtain ⟨hXc, hXj⟩ := hrow ρ hρk hK (fun x y => R y x) A hA hRT
  set rY : Euc d → ℝ := fun x => ∫ y, R x y ∂μ with hrYd
  set rX : Euc d → ℝ := fun y => ∫ x, R x y ∂μ with hrXd
  have hrY : rY = fun x => ∫ y, ρ y * R x y := funext fun x => r26t8a_f25_wd_integral hρ _
  have hrX : rX = fun y => ∫ x, ρ x * R x y := funext fun y => r26t8a_f25_wd_integral hρ _
  have hrYc : ContDiff ℝ (k : WithTop ℕ∞) rY := by rw [hrY]; exact hYc
  have hrXc : ContDiff ℝ (k : WithTop ℕ∞) rX := by rw [hrX]; exact hXc
  have hrYj : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j rY x‖ ≤ Crow * A * jbracket x ^ M := by
    intro j hj x; rw [hrY]; exact hYj j hj x
  have hrXj : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j rX x‖ ≤ Crow * A * jbracket x ^ M := by
    intro j hj x; rw [hrX]; exact hXj j hj x
  set c0 : ℝ := ∫ x, rY x ∂μ with hc0d
  set Ia : ℝ := ∫ y, ρ y * jbracket y ^ M with hIa
  have hrY0 : ∀ x, ‖rY x‖ ≤ Crow * A * jbracket x ^ M := fun x => by
    have := hrYj 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hrX0 : ∀ x, ‖rX x‖ ≤ Crow * A * jbracket x ^ M := fun x => by
    have := hrXj 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hjbI' : Integrable (fun x : Euc d => Crow * A * jbracket x ^ M) μ := hjbI.const_mul _
  have hrYI : Integrable rY μ :=
    Integrable.mono' hjbI' hrYc.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hrY0)
  have hrXI : Integrable rX μ :=
    Integrable.mono' hjbI' hrXc.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hrX0)
  have hc0b : |c0| ≤ Crow * A * Ia := by
    have h1 : ‖c0‖ ≤ ∫ x, Crow * A * jbracket x ^ M ∂μ :=
      norm_integral_le_of_norm_le hjbI' (Filter.Eventually.of_forall hrY0)
    rw [integral_const_mul, hMom] at h1
    simpa [Real.norm_eq_abs] using h1
  have hpw1 : ∀ x y : Euc d, jbracket x ^ M ≤ HRS.MS.Phase2S82.pairWeight M x y ∧
      1 ≤ HRS.MS.Phase2S82.pairWeight M x y := by
    intro x y
    have h1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
    have h2 : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
    unfold HRS.MS.Phase2S82.pairWeight
    constructor <;> nlinarith
  have hCA : 0 ≤ Crow * A := mul_nonneg hCrow0 hA
  -- the three correction terms
  have hN1 : Conormal k b' M σ' (2 ^ k * (Crow * A)) (fun x y => -(rY x)) := by
    refine r26t8a_conormal_of_smooth hCA ?_ fun j hj x y => ?_
    · exact (hrYc.comp contDiff_fst).neg
    · have e : Function.uncurry (fun x y : Euc d => -(rY x)) = -(fun p : Euc d × Euc d => rY p.1) := rfl
      rw [e, iteratedFDeriv_neg_apply, norm_neg]
      refine ((r26t8a_f13_jet_fst (hrYc.of_le (by exact_mod_cast hj)) (x, y)).trans (hrYj j hj x)).trans ?_
      exact mul_le_mul_of_nonneg_left (hpw1 x y).1 hCA
  have hN2 : Conormal k b' M σ' (2 ^ k * (Crow * A)) (fun x y => -(rX y)) := by
    refine r26t8a_conormal_of_smooth hCA ?_ fun j hj x y => ?_
    · exact (hrXc.comp contDiff_snd).neg
    · have e : Function.uncurry (fun x y : Euc d => -(rX y)) = -(fun p : Euc d × Euc d => rX p.2) := rfl
      rw [e, iteratedFDeriv_neg_apply, norm_neg]
      refine ((r26t8a_f4_jet_snd (hrXc.of_le (by exact_mod_cast hj)) (x, y)).trans (hrXj j hj y)).trans ?_
      have : jbracket y ^ M ≤ HRS.MS.Phase2S82.pairWeight M x y := by
        have h1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
        unfold HRS.MS.Phase2S82.pairWeight
        nlinarith [Real.rpow_nonneg (s83_jb_pos y).le M]
      exact mul_le_mul_of_nonneg_left this hCA
  have hB3 : 0 ≤ Crow * A * Ia := mul_nonneg hCA hI0
  have hN3 : Conormal k b' M σ' (2 ^ k * (Crow * A * Ia)) (fun (_ _ : Euc d) => c0) := by
    refine r26t8a_conormal_of_smooth hB3 ?_ fun j hj x y => ?_
    · exact contDiff_const
    · have e : Function.uncurry (fun _ _ : Euc d => c0) = fun _ : Euc d × Euc d => c0 := rfl
      rw [e]
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact hc0b.trans (by nlinarith [(hpw1 x y).2])
      · rw [r26t8a_f25_jet_const c0 hpos]
        exact mul_nonneg hB3 (by linarith [(hpw1 x y).2])
  have hsum := r26t8a_conormal_add hchi (r26t8a_conormal_add hchi hN1 hN2) hN3
  have hconst : 2 ^ k * (Crow * A) + 2 ^ k * (Crow * A) + 2 ^ k * (Crow * A * Ia) =
      (2 ^ k * Crow * (2 + Ia)) * A := by ring
  rw [hconst] at hsum
  refine r26t8a_conormal_congr (fun x y _ => ?_) hsum
  simp only [r2CenterKernel, hrYd, hrXd, hc0d]
  ring

end HRS.MS.R26T8A
