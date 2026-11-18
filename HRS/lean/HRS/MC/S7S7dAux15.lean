import HRS.MC.S7S7dAux14

/-!
# Packet `s7_S7d_uniform_limits`, helper 15: abstract truncation-error estimates
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_int_sub_le (P : Measure Ω) {A B m : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P)
    (hm : Integrable m P) (h : ∀ ω, |A ω - B ω| ≤ m ω) : |∫ ω, A ω ∂P - ∫ ω, B ω ∂P| ≤ ∫ ω, m ω ∂P := by
  rw [← integral_sub hA hB]
  have := norm_integral_le_of_norm_le hm (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact h ω) (μ := P) (f := fun ω => A ω - B ω)
  simpa [Real.norm_eq_abs] using this

/-- the `Y`-weighted truncation error through AM-GM. -/
theorem s7d_amgm_diff (P : Measure Ω) [IsProbabilityMeasure P] {Y A B m : Ω → ℝ}
    (hY : Measurable Y) (hYi : Integrable (fun ω => |Y ω|) P) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ ω, |A ω| ≤ 1) (hBb : ∀ ω, |B ω| ≤ 1) (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω)
    (hm2 : ∀ ω, m ω ≤ 2) (hdiff : ∀ ω, |A ω - B ω| ≤ m ω)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) {C2 T lam : ℝ} (hC : ∫ ω, Y ω ^ 2 ∂P ≤ C2)
    (hT : ∫ ω, m ω ∂P ≤ T) (hlam : 0 < lam) :
    |∫ ω, Y ω * A ω ∂P - ∫ ω, Y ω * B ω ∂P| ≤ (lam * C2 + 2 * T / lam) / 2 := by
  obtain ⟨hI, hbound⟩ := s7d_amgm_int P hY hm hm0 hm2 hY2 hC hT hlam
  have hint : ∀ {Z : Ω → ℝ}, Measurable Z → (∀ ω, |Z ω| ≤ 1) → Integrable (fun ω => Y ω * Z ω) P := by
    intro Z hZ hZb
    refine hYi.mono' (hY.mul hZ).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Y ω| * |Z ω| ≤ |Y ω| * 1 := mul_le_mul_of_nonneg_left (hZb ω) (abs_nonneg _)
      _ = |Y ω| := mul_one _
  have hmi : Integrable (fun ω => |Y ω| * m ω) P := hI
  refine (s7d_int_sub_le P (hint hA hAb) (hint hB hBb) hmi (fun ω => ?_)).trans hbound
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hdiff ω) (abs_nonneg _)

/-- The class of test functions on `E`: continuous, bounded by `1`, `min(2, ‖x-y‖)`-Lipschitz. -/
def s7d_Th {E : Type*} [NormedAddCommGroup E] (Θ : E → ℝ) : Prop :=
  Continuous Θ ∧ (∀ x, |Θ x| ≤ 1) ∧ ∀ x y, |Θ x - Θ y| ≤ min 2 ‖x - y‖

theorem s7d_W_trunc_err (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hr : r = 2 * (d : ℝ) + 6)
    (Yf : ∀ N : ℕ, Config d N → ℝ) {C2 : ℝ}
    (hYm : ∀ N, 1 ≤ N → Measurable (Yf N))
    (hYi : ∀ N, 1 ≤ N → Integrable (fun X => |Yf N X|) (sed_Q d s N γ ρ))
    (hY2 : ∀ N, 1 ≤ N → Integrable (fun X => Yf N X ^ 2) (sed_Q d s N γ ρ))
    (hC2 : ∀ N, 1 ≤ N → ∫ X, Yf N X ^ 2 ∂(sed_Q d s N γ ρ) ≤ C2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : Finset (NonzeroLattice d), ∀ K : Finset (NonzeroLattice d), K₀ ⊆ K → ∀ N : ℕ, 1 ≤ N →
      ∀ Θ : NegSobolev d r → ℝ, s7d_Th Θ →
        |∫ X, Yf N X * Θ (zetaE r (sed_Q d s N γ ρ) X) ∂(sed_Q d s N γ ρ) -
          ∫ X, Yf N X * Θ (truncE K (zetaE r (sed_Q d s N γ ρ) X)) ∂(sed_Q d s N γ ρ)| ≤ δ := by
  obtain ⟨b, hb, hb0, hT⟩ := s7d_W_tail hd hs0 hs hγ hρ hr
  have hC20 : 0 ≤ C2 + 1 := by
    have := hC2 1 le_rfl
    have h0 : 0 ≤ ∫ X, Yf 1 X ^ 2 ∂(sed_Q d s 1 γ ρ) := integral_nonneg fun X => sq_nonneg _
    linarith
  set lam : ℝ := δ / (2 * (C2 + 1)) with hlam
  have hC2pos : 0 < C2 + 1 := by
    have := hC2 1 le_rfl
    have h0 : 0 ≤ ∫ X, Yf 1 X ^ 2 ∂(sed_Q d s 1 γ ρ) := integral_nonneg fun X => sq_nonneg _
    linarith
  have hlampos : 0 < lam := by positivity
  have hev : ∀ᶠ K : Finset (NonzeroLattice d) in atTop, (∑' k, b k) - ∑ k ∈ K, b k < δ * lam / 2 :=
    (tendsto_order.1 (s7d_tail_tendsto hb)).2 _ (by positivity)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨K₀, fun K hK N hN Θ hΘ => ?_⟩
  have hTK := hK₀ K hK
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  obtain ⟨hmeas, hint⟩ := hT N hN K
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hWm := HRS.MC.Sec7.S7c.s7c_zeta_meas hN hr' (sed_Q d s N γ ρ)
  obtain ⟨hΘc, hΘb, hΘl⟩ := hΘ
  have h := s7d_amgm_diff (sed_Q d s N γ ρ) (Y := Yf N)
    (A := fun X => Θ (zetaE r (sed_Q d s N γ ρ) X))
    (B := fun X => Θ (truncE K (zetaE r (sed_Q d s N γ ρ) X)))
    (m := fun X => min 2 ‖zetaE r (sed_Q d s N γ ρ) X - truncE K (zetaE r (sed_Q d s N γ ρ) X)‖)
    (hYm N hN) (hYi N hN) (hΘc.measurable.comp hWm)
    (hΘc.measurable.comp ((s7d_truncE_continuous K).measurable.comp hWm))
    (fun X => hΘb _) (fun X => hΘb _) hmeas
    (fun X => le_min (by norm_num) (norm_nonneg _)) (fun X => min_le_left _ _)
    (fun X => hΘl _ _) (hY2 N hN) (hC2 N hN) hint hlampos
  refine h.trans ?_
  have e1 : lam * C2 ≤ δ / 2 := by
    rw [hlam]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hC2pos, hδ, hC20]
  have e2 : 2 * ((∑' k, b k) - ∑ k ∈ K, b k) / lam ≤ δ := by
    rw [div_le_iff₀ hlampos]
    nlinarith
  linarith

end HRS.MC.Sec7.S7d

end
