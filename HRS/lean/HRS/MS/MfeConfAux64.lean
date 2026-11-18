import HRS.MS.MfeConfAux63

/-!
# S.B.1, packet F6 (part 25): the level inequality against the modulated Gibbs measure

`sb1_level_ineq_Q`: `sb1_level_ineq` for the tilt `Ψ_s = -θ log q_s - H` where `q_s = sb1qd k β N ρ_s` is the density of the
modulated Gibbs measure `ℚ_{N,β}(ρ_s dx)` of the kernel `k`: for the flow `μ_s` of the static gradient system,
`H(μ_t | ℚ(ρ_t)) ≤ H(μ_0 | ℚ(ρ_0)) + ∫_0^t ∫ S_s dμ_s ds` with the explicit source `sb1S`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ}

/-- The tilt `Ψ_s = -θ log q_s - H` realising the modulated Gibbs density `q_s` as `exp(-(H + Ψ_s)/θ)`. -/
def sb1Psi (θ : ℝ) (H : EucConfig d N → ℝ) (k : Euc d → ℝ) (β : ℝ) (ρ : ℝ → Euc d → ℝ) (s : ℝ)
    (x : EucConfig d N) : ℝ :=
  -θ * Real.log (sb1qd k β N (ρ s) x) - H x

theorem sb1_exp_psi (hθ : 0 < θ) {k : Euc d → ℝ} {β : ℝ} {ρ : ℝ → Euc d → ℝ} {s : ℝ}
    (hρ : ∀ x, 0 < ρ s x) (hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal (ρ s)))
    (x : EucConfig d N) :
    Real.exp (-θ⁻¹ * (H x + sb1Psi θ H k β ρ s x)) = sb1qd k β N (ρ s) x := by
  unfold sb1Psi
  have : -θ⁻¹ * (H x + (-θ * Real.log (sb1qd k β N (ρ s) x) - H x)) = Real.log (sb1qd k β N (ρ s) x) := by
    field_simp
    ring
  rw [this, Real.exp_log (sb1_qd_pos hρ hK x)]

theorem sb1_level_ineq_Q (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hθ : 0 < θ) {k : Euc d → ℝ} (hk : Measurable k) {β : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρd : ∀ s ∈ Set.Icc (0 : ℝ) T, Whole.IsProbDensity (ρ s))
    (hρp : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ s x)
    (hKp : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal (ρ s)))
    (hΨ : Sb1Tilt θ T b w (sb1Psi θ H k β ρ) Wψ CΨ Bw Kw CS) {DS : ℝ → ℝ} (hDS0 : ∀ s, 0 ≤ DS s)
    (hDSi : IntegrableOn DS (Set.Icc 0 T))
    (hSlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : EucConfig d N,
      |sb1S θ b w Wψ s x - sb1S θ b w Wψ s y| ≤ DS s * ‖x - y‖ * (1 + ‖x‖ + ‖y‖))
    {Lw : ℝ≥0} (hLw : LipschitzWith Lw (w 0)) {C0 : ℝ}
    (hC0 : ∀ x, 0 ≤ H x + sb1Psi θ H k β ρ 0 x + C0)
    (hfin0 : relEntropy (μ 0) (Whole.modulatedGibbs k N β (Whole.withDensityReal (ρ 0))) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    relEntropy (μ t) (Whole.modulatedGibbs k N β (Whole.withDensityReal (ρ t))) ≠ ⊤ ∧
      (relEntropy (μ t) (Whole.modulatedGibbs k N β (Whole.withDensityReal (ρ t)))).toReal ≤
        (relEntropy (μ 0) (Whole.modulatedGibbs k N β (Whole.withDensityReal (ρ 0)))).toReal +
          ∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S θ b w Wψ s y ∂(μ s) := by
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hqe : ∀ s ∈ Set.Icc (0 : ℝ) T, (fun x => Real.exp (-θ⁻¹ * (H x + sb1Psi θ H k β ρ s x))) =
      sb1qd k β N (ρ s) := fun s hs => funext fun x => sb1_exp_psi hθ (hρp s hs) (hKp s hs) x
  have hmod : ∀ s ∈ Set.Icc (0 : ℝ) T, Whole.modulatedGibbs k N β (Whole.withDensityReal (ρ s)) =
      sb1Dm (fun x => Real.exp (-θ⁻¹ * (H x + sb1Psi θ H k β ρ s x))) := fun s hs => by
    rw [hqe s hs]; exact sb1_modGibbs_eq_Dm hk (hρd s hs) (hKp s hs)
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ x, ENNReal.ofReal (Real.exp (-θ⁻¹ * (H x + sb1Psi θ H k β ρ s x))) = 1 := fun s hs => by
    simp only [sb1_exp_psi hθ (hρp s hs) (hKp s hs)]
    exact sb1_qd_lintegral (hρd s hs) (hKp s hs)
  unfold relEntropy at hfin0 ⊢
  rw [hmod 0 hT0] at hfin0
  rw [hmod t ht, hmod 0 hT0]
  exact sb1_level_ineq hP hΨ hθ hDS0 hDSi hSlip hZ hLw hC0 hfin0 ht

end

end HRS.MS.MfeConf
