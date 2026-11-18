import HRS.MS.Fp81S21RawIncr2
import HRS.MS.Fp81S21RealizePatch

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Classical Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.ProClosureS111 HRS.MS.S111T

/-- Summable coordinate fourth-moment bounds give the raw OscDual norm
fourth-moment bound on the same time interval. -/
theorem fp81s21_raw_increment_norm_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {m : ℝ}
    (Z : ℝ → Ω → OscDual d m)
    (hZmeas : ∀ u : ℝ, Measurable (Z u))
    (L : MultiIndex d → ℝ) (hL0 : ∀ α, 0 ≤ L α) (hLsum : Summable L)
    (H : ℝ) (hH : 0 < H)
    (hcoord4 : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
        ∀ α : MultiIndex d,
          ∫⁻ ω, ‖OscDual.coord (Z t ω) α - OscDual.coord (Z s ω) α‖ₑ ^
            (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * (L α * |t - s|) ^ 2))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) H)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
    ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (3 * (∑' α, L α) ^ 2 * |t - s| ^ 2) := by
  let v : MultiIndex d → ℝ := fun α => L α * |t - s|
  have hv0 : ∀ α, 0 ≤ v α := by
    intro α
    dsimp [v]
    exact mul_nonneg (hL0 α) (abs_nonneg _)
  have hvs : Summable v := by
    have h := hLsum.mul_left |t - s|
    refine h.congr fun α => ?_
    dsimp [v]
    ring
  have hYmeas : Measurable (fun ω => Z t ω - Z s ω) :=
    (hZmeas t).sub (hZmeas s)
  have hcoord : ∀ α : MultiIndex d,
      ∫⁻ ω, ‖OscDual.coord ((Z t ω - Z s ω)) α‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (3 * (v α) ^ 2) := by
    intro α
    have hcoordSub (ω : Ω) :
        OscDual.coord (Z t ω - Z s ω) α =
          OscDual.coord (Z t ω) α - OscDual.coord (Z s ω) α := by
      change s111t_coordCLM d m α (Z t ω - Z s ω) = _
      exact map_sub _ _ _
    calc
      ∫⁻ ω, ‖OscDual.coord (Z t ω - Z s ω) α‖ₑ ^ (4 : ℝ) ∂P =
          ∫⁻ ω, ‖OscDual.coord (Z t ω) α - OscDual.coord (Z s ω) α‖ₑ ^
            (4 : ℝ) ∂P := by
        apply lintegral_congr
        intro ω
        rw [hcoordSub ω]
      _ ≤ ENNReal.ofReal (3 * (v α) ^ 2) := by
        simpa only [v] using hcoord4 s hs t ht α
  have hcore := fp81s21_coord_fourth_to_norm_fourth
    (fun ω => Z t ω - Z s ω) hYmeas v hv0 hvs hcoord
  have htsum : (∑' α : MultiIndex d, v α) =
      (∑' α : MultiIndex d, L α) * |t - s| := by
    simp [v, tsum_mul_right]
  calc
    ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (3 * (∑' α : MultiIndex d, v α) ^ 2) := hcore
    _ = ENNReal.ofReal (3 * (∑' α : MultiIndex d, L α) ^ 2 * |t - s| ^ 2) := by
      congr 1
      rw [htsum]
      ring

#print axioms fp81s21_raw_increment_norm_fourth

end HRS.Fp81.S21

end
