import HRS.MS.S113X2C10
import HRS.MS.MovSchAux8

/-!
# S11.3 X2 wiring (worker S11W), C11: `S113XLocalizedI` from the two remaining cores

* `S113XQReg`: (core QREG) the moving reference `q_N^t` is, near any compact collision-free set and for `t ∈ [0,T+1]`, the restriction of a
  `C²` positive space-time function on `ℝ × ℝ^{Nd}` (time regularity of the normalizer and of `ρ^t`, extension past `t = 0`).
* `S113XLiouville`: (core LIOUVILLE, Pro D03) propagation of the bound `ν_0 ≤ C₀ dx` of the initial killed law to `ν_t ≤ B dx`, `t ∈ [0,T]`.
* `s113c_localized_of_cores`: the restated core `S113XLocalizedI` follows from these two cores, the removal of the localization
  (part A) and the integrated chain inequality (part B).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)
open HRS.MS.S113BD (s113x_Q s113x_source S113XLocalizedI s113_powerMass s113_powerTilt s113c_Gp s113x_Q_prob s113x_K_pos)

variable {d N : ℕ}

/-- Core QREG. -/
def S113XQReg (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 < T → ∀ K : Set (EucConfig d N), IsCompact K →
      (∀ x ∈ K, x ∉ eucCollisionSet d N) →
      ∃ (qt : ℝ → s113b_E (N * d) → ℝ) (G' : Set (s113b_E (N * d))), s113c_QReg d N s β ρ T K qt G'

/-- Core LIOUVILLE (Pro D03). -/
def S113XLiouville (d : ℕ) (s q β : ℝ) : Prop :=
  0 < β → ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
    MovParticleSetup P d s q β N X₀ W X →
    ∀ D : Set (EucConfig d N), IsOpen D → IsCompact (closure D) → closure D ⊆ (eucCollisionSet d N)ᶜ →
    ∀ chi : EucConfig d N → ℝ, Measurable chi → (∀ z, 0 ≤ chi z) → (∀ z, chi z ≤ 1) →
    ∀ C0 : ℝ, s113a_killedLaw P D X₀ X chi 0 ≤ ENNReal.ofReal C0 • volume →
    ∀ T : ℝ, 0 ≤ T → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal ≤ ENNReal.ofReal B • volume

theorem s113c_Q_facts (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β)
    (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    s113x_Q d s β ρ N t = volume.withDensity (fun x => ENNReal.ofReal (movQDensity d s β N (ρ t) x)) ∧
      (∀ x, 0 < movQDensity d s β N (ρ t) x) ∧ Measurable (movQDensity d s β N (ρ t)) := by
  obtain ⟨hprob, hpos, -, -⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀.le t ht
  have hK := HRS.MS.S113BD.s113x_K_pos hd hs0 hs hβ hq hρ₀ hC₁ hc₀ hNL hf0 hρ hN ht
  refine ⟨HRS.MS.MovSch.s64_modGibbs_density hprob hK, ?_, s113c_movQ_measurable s β (hρ.regular t ht).measurable⟩
  intro x
  unfold movQDensity
  exact mul_pos (mul_pos (inv_pos.2 hK) (Real.exp_pos _)) (Finset.prod_pos fun i _ => hpos _)

/-- Integrability of `q (u/q)^p` for a bounded ratio. -/
theorem s113c_hint {q u : EucConfig d N → ℝ} (hqm : Measurable q) (hq : ∀ x, 0 < q x)
    (hqint : Integrable q volume) (hum : Measurable u) (hu0 : ∀ x, 0 ≤ u x) {Z : ℝ}
    (hZ : ∀ x, u x / q x ≤ Z) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x => q x * (u x / q x) ^ p) volume := by
  refine Integrable.mono' (hqint.mul_const (Z ^ p)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hqm.mul ((hum.div hqm).pow_const p)).aestronglyMeasurable
  · have h0 : 0 ≤ u x / q x := div_nonneg (hu0 x) (hq x).le
    rw [Real.norm_of_nonneg (mul_nonneg (hq x).le (Real.rpow_nonneg h0 p))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 (hZ x) hp) (hq x).le

theorem s113c_q_integrable {q : EucConfig d N → ℝ} (hqm : Measurable q) (hq : ∀ x, 0 < q x)
    (Q : Measure (EucConfig d N)) (hQ : Q = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    [IsProbabilityMeasure Q] : Integrable q volume := by
  have h1 : ∫⁻ x, ENNReal.ofReal (q x) ∂volume ≠ ⊤ := by
    have := measure_univ (μ := Q)
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    rw [this]; exact ENNReal.one_ne_top
  have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hqm).aemeasurable h1
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hq x).le]

end HRS.MS.S113X2C

end
