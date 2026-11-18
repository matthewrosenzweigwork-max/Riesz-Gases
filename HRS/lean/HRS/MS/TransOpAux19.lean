import HRS.MS.TransOpAux18
import HRS.MS.R2ScrAux1

/-!
# S611 packet P4e: the susceptibility covariance under translation

`s611_isResponse_shift`: `HRS.Whole.IsResponse g (T_a μ) γ ψ h ↔ HRS.Whole.IsResponse g μ γ ψ(· + a) h(· + a)` (`T_a μ = μ.map (· + a)`).
`s611_susceptibilityCov_shift`: `C_{T_a μ}(F(· - a), G(· - a)) = C_μ(F, G)` whenever response solutions for `μ` are a.e. unique
(`HRS.Whole.responseInverse` is a `Classical.choose`; uniqueness for `μ = μ_β` is `s98_resp_unique`, and trivial at `γ = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_pair_map (μ : Measure (Euc d)) (a : Euc d) (ψ : Euc d → ℝ) :
    HRS.Whole.pair (μ.map (fun y => y + a)) ψ = HRS.Whole.pair μ (fun y => ψ (y + a)) := by
  unfold HRS.Whole.pair
  exact HRS.MS.A0.a0_integral_shift μ a ψ

theorem s611_projMean_map (μ : Measure (Euc d)) (a : Euc d) (ψ : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.projMean (μ.map (fun y => y + a)) ψ (x + a) = HRS.Whole.projMean μ (fun y => ψ (y + a)) x := by
  unfold HRS.Whole.projMean
  rw [s611_pair_map]

theorem s611_Kop_map (g : Euc d → ℝ) (μ : Measure (Euc d)) (a : Euc d) (h : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.Kop g (μ.map (fun y => y + a)) h (x + a) = HRS.Whole.Kop g μ (fun y => h (y + a)) x := by
  unfold HRS.Whole.Kop
  rw [s611_projMean_map]
  congr 1
  funext y
  rw [HRS.MS.A0.a0_integral_shift μ a (fun y' => g (y + a - y') * h y')]
  simp only [add_sub_add_right_eq_sub]

theorem s611_isResponse_shift (g : Euc d → ℝ) (μ : Measure (Euc d)) (a : Euc d) (γ : ℝ)
    (ψ h : Euc d → ℝ) :
    HRS.Whole.IsResponse g (μ.map (fun y => y + a)) γ ψ h ↔
      HRS.Whole.IsResponse g μ γ (fun x => ψ (x + a)) (fun x => h (x + a)) := by
  have hemb : MeasurableEmbedding (fun y : Euc d => y + a) := measurableEmbedding_addRight a
  unfold HRS.Whole.IsResponse HRS.Whole.MemL2Zero
  rw [hemb.memLp_map_measure_iff, hemb.ae_map_iff]
  have hint : ∫ x, h x ∂(μ.map (fun y => y + a)) = ∫ x, h (x + a) ∂μ :=
    HRS.MS.A0.a0_integral_shift μ a h
  rw [hint]
  have hae : ∀ x, (h (x + a) + γ * HRS.Whole.Kop g (μ.map (fun y => y + a)) h (x + a) =
      HRS.Whole.projMean (μ.map (fun y => y + a)) ψ (x + a)) ↔
      (h (x + a) + γ * HRS.Whole.Kop g μ (fun y => h (y + a)) x = HRS.Whole.projMean μ (fun y => ψ (y + a)) x) := by
    intro x
    rw [s611_Kop_map, s611_projMean_map]
  simp only [hae]
  exact Iff.rfl

theorem s611_responseInverse_shift (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ)
    (huniq : ∀ (ψ h1 h2 : Euc d → ℝ), HRS.Whole.IsResponse g μ γ ψ h1 → HRS.Whole.IsResponse g μ γ ψ h2 → h1 =ᵐ[μ] h2)
    (a : Euc d) (ψ : Euc d → ℝ) :
    (fun z => HRS.Whole.responseInverse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a)) (z + a)) =ᵐ[μ]
      HRS.Whole.responseInverse g μ γ ψ := by
  have hψa : (fun x => (fun y => ψ (y - a)) (x + a)) = ψ := by
    funext x; simp
  by_cases hex : ∃ h, HRS.Whole.IsResponse g μ γ ψ h
  · have h0 : HRS.Whole.IsResponse g μ γ ψ (HRS.Whole.responseInverse g μ γ ψ) := by
      unfold HRS.Whole.responseInverse
      rw [dif_pos hex]
      exact hex.choose_spec
    have hexa : ∃ h, HRS.Whole.IsResponse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a)) h := by
      refine ⟨fun y => HRS.Whole.responseInverse g μ γ ψ (y - a), ?_⟩
      rw [s611_isResponse_shift]
      simp only [add_sub_cancel_right, hψa]
      exact h0
    have h1 : HRS.Whole.IsResponse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a))
        (HRS.Whole.responseInverse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a))) := by
      unfold HRS.Whole.responseInverse
      rw [dif_pos hexa]
      exact hexa.choose_spec
    rw [s611_isResponse_shift, hψa] at h1
    exact huniq ψ _ _ h1 h0
  · have hexa : ¬ ∃ h, HRS.Whole.IsResponse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a)) h := by
      rintro ⟨h, hh⟩
      rw [s611_isResponse_shift, hψa] at hh
      exact hex ⟨_, hh⟩
    have e1 : HRS.Whole.responseInverse g μ γ ψ = 0 := by
      unfold HRS.Whole.responseInverse
      rw [dif_neg hex]
    have e2 : ∀ z, HRS.Whole.responseInverse g (μ.map (fun y => y + a)) γ (fun y => ψ (y - a)) z = 0 := by
      intro z
      unfold HRS.Whole.responseInverse
      rw [dif_neg hexa]
      rfl
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [e1, e2]
    rfl

theorem s611_susceptibilityCov_shift (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ)
    (huniq : ∀ (ψ h1 h2 : Euc d → ℝ), HRS.Whole.IsResponse g μ γ ψ h1 → HRS.Whole.IsResponse g μ γ ψ h2 → h1 =ᵐ[μ] h2)
    (a : Euc d) (F G : Euc d → ℝ) :
    HRS.Whole.susceptibilityCov g (μ.map (fun y => y + a)) γ (fun y => F (y - a)) (fun y => G (y - a)) =
      HRS.Whole.susceptibilityCov g μ γ F G := by
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  rw [HRS.MS.A0.a0_integral_shift]
  refine integral_congr_ae ?_
  filter_upwards [s611_responseInverse_shift g μ γ huniq a G] with z hz
  rw [hz, s611_projMean_map]
  simp only [add_sub_cancel_right]

/-- Uniqueness of the response for `μ_β`, all `γ ≥ 0`. -/
theorem s611_resp_unique (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M₀ c S : ℝ} (hc : 0 < c)
    {N : ℕ} {ρ : Euc d → ℝ} (h : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∀ (ψ h1 h2 : Euc d → ℝ), HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ ψ h1 →
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ ψ h2 → h1 =ᵐ[HRS.Whole.withDensityReal ρ] h2 := by
  intro ψ h1 h2 r1 r2
  rcases hγ.eq_or_lt with h0 | h0
  · subst h0
    filter_upwards [r1.2, r2.2] with x e1 e2
    simp only [zero_mul, add_zero] at e1 e2
    rw [e1, e2]
  · exact HRS.MS.S98.s98_resp_unique hd hs0 hsd hc h h0 r1 r2

end HRS.MS.TransOp

end
