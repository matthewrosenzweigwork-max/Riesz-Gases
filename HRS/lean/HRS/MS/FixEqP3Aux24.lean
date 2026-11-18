import HRS.MS.FixEqP3Aux23

/-!
# S5.7 `fixed_equation` (worker S57P), part 36: the fourth moment of the increments of the difference of two noise fields
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MS.U10

variable {d : ℕ}

theorem s57p_W_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} {W : H → Ω₀ → ℝ} (hI : Sb7Iso Q W) (a b : H) :
    W (a - b) =ᵐ[Q] fun w => W a w - W b w := by
  have := hI.lin 1 (-1) a b
  filter_upwards [this] with w hw
  have e : (1 : ℝ) • a + (-1 : ℝ) • b = a - b := by simp [sub_eq_add_neg]
  rw [e] at hw
  rw [hw]; ring

theorem s57p_diff_moment {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q] {W : H → Ω₀ → ℝ}
    (hI : Sb7Iso Q W) (hlaw : ∀ g, Q.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2))
    {m : ℝ} {X1 X2 : ℝ → Ω₀ → OscDual d m} {κ1 κ2 : ℝ → MultiIndex d → H} {T : ℝ}
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X1 t w) α = W (κ1 t α) w)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X2 t w) α = W (κ2 t α) w)
    (hs1 : ∀ t ∈ Set.Icc (0 : ℝ) T, Summable fun α => ‖κ1 t α‖ ^ 2)
    (hs2 : ∀ t ∈ Set.Icc (0 : ℝ) T, Summable fun α => ‖κ2 t α‖ ^ 2) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ w, ‖(X1 t w - X2 t w) - (X1 s w - X2 s w)‖ₑ ^ 4 ∂Q ≤
      ENNReal.ofReal (M * (∑' α, ‖(κ1 t α - κ2 t α) - (κ1 s α - κ2 s α)‖ ^ 2) ^ 2) := by
  set v : MultiIndex d → H := fun α => κ1 t α - κ2 t α with hv
  set v' : MultiIndex d → H := fun α => κ1 s α - κ2 s α with hv'
  have hsv : Summable fun α => ‖v α‖ ^ 2 := s57p_summable_sub (hs1 t ht) (hs2 t ht)
  have hsv' : Summable fun α => ‖v' α‖ ^ 2 := s57p_summable_sub (hs1 s hs) (hs2 s hs)
  have key := s57p_fourth_moment hI hlaw hM0 hM (m := m) v v' hsv hsv'
  refine le_trans (le_of_eq ?_) key
  refine lintegral_congr_ae ?_
  have c1t := ae_all_iff.2 (h1 t ht)
  have c2t := ae_all_iff.2 (h2 t ht)
  have c1s := ae_all_iff.2 (h1 s hs)
  have c2s := ae_all_iff.2 (h2 s hs)
  have lv : ∀ᵐ w ∂Q, ∀ α, W (v α) w = W (κ1 t α) w - W (κ2 t α) w :=
    ae_all_iff.2 fun α => s57p_W_sub hI _ _
  have lv' : ∀ᵐ w ∂Q, ∀ α, W (v' α) w = W (κ1 s α) w - W (κ2 s α) w :=
    ae_all_iff.2 fun α => s57p_W_sub hI _ _
  filter_upwards [c1t, c2t, c1s, c2s, lv, lv', s57p_ae_memℓp hI v hsv, s57p_ae_memℓp hI v' hsv'] with
    w a1 a2 a3 a4 a5 a6 m1 m2
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, s57p_enorm_sq_sub, s57p_enorm_sq_sub]
  refine congrArg (fun z : ℝ≥0∞ => z ^ 2) (tsum_congr fun α => ?_)
  rw [s57p_coord_ellVec m1, s57p_coord_ellVec m2, a5 α, a6 α]
  have e : OscDual.coord ((X1 t w - X2 t w)) α - OscDual.coord ((X1 s w - X2 s w)) α =
      (OscDual.coord (X1 t w) α - OscDual.coord (X2 t w) α) -
        (OscDual.coord (X1 s w) α - OscDual.coord (X2 s w) α) := rfl
  rw [e, a1 α, a2 α, a3 α, a4 α]

end HRS.MS.FixEq
