import HRS.MC.S7S7dAux1
import HRS.MC.S7S7c
import HRS.MC.S7S7b

/-!
# Packet `s7_S7d_uniform_limits`, helper 3: moments of the centred statistics

Boundedness (for fixed `N`) and measurability of `sed_Y`, and the uniform fourth moment of
`centeredStat` for smooth tests (from `s7b_Y_moment`, `q = 2`), the input of the `W_2` coupling of `WQ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7d_smooth_bdd {u : Torus d → ℝ} (hu : Torus.IsSmooth u) : ∃ T : ℝ, 0 ≤ T ∧ ∀ x, |u x| ≤ T := by
  have hc : Continuous u := HRS.Q66.q66_cont_of_smooth hu
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

theorem s7d_sedY_bdd {N : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q]
    {u : Torus d → ℝ} {T : ℝ} (hu : ∀ x, |u x| ≤ T) (X : Config d N) :
    |sed_Y Q u X| ≤ Real.sqrt N * (2 * T) := by
  unfold sed_Y
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h1 := HRS.MC.SEdge.B5b.b5b_pair_bdd hN hu X
  have h2 : |∫ Y, pair (empirical Y) u ∂Q| ≤ T := by
    have := norm_integral_le_of_norm_le_const (μ := Q) (f := fun Y => pair (empirical Y) u) (C := T)
      (Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs]; exact HRS.MC.SEdge.B5b.b5b_pair_bdd hN hu Y)
    simpa [Real.norm_eq_abs] using this
  calc |pair (empirical X) u - ∫ Y, pair (empirical Y) u ∂Q|
      ≤ |pair (empirical X) u| + |∫ Y, pair (empirical Y) u ∂Q| := abs_sub _ _
    _ ≤ 2 * T := by linarith

theorem s7d_sedY_pow_integrable {N : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N))
    [IsProbabilityMeasure Q] {u : Torus d → ℝ} (hu : Continuous u) {T : ℝ} (hT : ∀ x, |u x| ≤ T)
    (k : ℕ) : Integrable (fun X => |sed_Y Q u X| ^ k) Q := by
  refine Integrable.of_bound ((HRS.MC.Sec7.S7c.s7c_sedY_meas hN Q hu).abs.pow_const k).aestronglyMeasurable
    ((Real.sqrt N * (2 * T)) ^ k) (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (abs_nonneg _) (s7d_sedY_bdd hN Q hT X) k

theorem s7d_fourth_moment (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {ψ : Fin p → Torus d → ℝ}
    (hψ : ∀ a, Torus.IsSmooth (ψ a)) :
    ∃ C4 : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => ‖centeredStat (sed_Q d s N γ ρ) ψ X‖ ^ ((2 : ℝ) + 2)) (sed_Q d s N γ ρ) ∧
      ∫ X, ‖centeredStat (sed_Q d s N γ ρ) ψ X‖ ^ ((2 : ℝ) + 2) ∂(sed_Q d s N γ ρ) ≤ C4 := by
  obtain ⟨C1, hC10, hC1⟩ := HRS.MC.Sec7.S7b.s7b_Y_moment hd hs0 hs hγ hρ 2
  choose T hT0 hT using fun a => s7d_smooth_bdd (hψ a)
  refine ⟨p * (∑ a, C1 * T a ^ (2 * 2)), fun N hN => ?_⟩
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  set Q := sed_Q d s N γ ρ with hQdef
  have hcont : ∀ a, Continuous (ψ a) := fun a => HRS.Q66.q66_cont_of_smooth (hψ a)
  have hpt : ∀ X : Config d N, ‖centeredStat Q ψ X‖ ^ ((2 : ℝ) + 2) ≤
      p * ∑ a, |sed_Y Q (ψ a) X| ^ (2 * 2) := by
    intro X
    rw [s7d_rpow_four]
    have h1 : ‖centeredStat Q ψ X‖ ^ 2 = ∑ a, (sed_Y Q (ψ a) X) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Real.norm_eq_abs, sq_abs]; rfl
    have h2 : ‖centeredStat Q ψ X‖ ^ 4 = (∑ a, (sed_Y Q (ψ a) X) ^ 2) ^ 2 := by
      rw [← h1]; ring
    rw [h2]
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p)) (fun _ => (1 : ℝ))
      (fun a => (sed_Y Q (ψ a) X) ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show 2 * 2 = 4 from rfl, pow_abs, abs_of_nonneg (by positivity)]
    ring
  have hint : Integrable (fun X => p * ∑ a, |sed_Y Q (ψ a) X| ^ (2 * 2)) Q :=
    (integrable_finset_sum _ fun a _ => s7d_sedY_pow_integrable hN Q (hcont a) (hT a) _).const_mul _
  have hmeas : AEStronglyMeasurable (fun X => ‖centeredStat Q ψ X‖ ^ ((2 : ℝ) + 2)) Q := by
    refine (Measurable.pow_const ?_ _).aestronglyMeasurable
    exact (HRS.MC.Sec7.S7c.s7c_cs_meas hN Q ψ hcont).norm
  have hI : Integrable (fun X => ‖centeredStat Q ψ X‖ ^ ((2 : ℝ) + 2)) Q :=
    hint.mono' hmeas (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt X)
  refine ⟨hI, ?_⟩
  calc ∫ X, ‖centeredStat Q ψ X‖ ^ ((2 : ℝ) + 2) ∂Q ≤ ∫ X, p * ∑ a, |sed_Y Q (ψ a) X| ^ (2 * 2) ∂Q :=
        integral_mono hI hint hpt
    _ = p * ∑ a, ∫ X, |sed_Y Q (ψ a) X| ^ (2 * 2) ∂Q := by
        rw [integral_const_mul, integral_finsetSum _ fun a _ =>
          s7d_sedY_pow_integrable hN Q (hcont a) (hT a) _]
    _ ≤ p * ∑ a, C1 * T a ^ (2 * 2) := by
        gcongr with a
        exact hC1 (ψ a) (T a) (hψ a) (hT a) N hN

end HRS.MC.Sec7.S7d

end
