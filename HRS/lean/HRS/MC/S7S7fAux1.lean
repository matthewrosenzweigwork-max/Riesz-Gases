import HRS.MC.S7S7d
import HRS.MC.S7S7e
import HRS.MC.SEdgeB9cancel

/-!
# Packet S7f, helper 1: double and triple series with product weights

Generic lemmas on `Summable`/`tsum` for families bounded by `M * b k * b l (* b j)` with `b` summable, used to
split and recombine the nested series of `S7c`/`S7d`/`S7e`, and the interchange of a double series with an
integral over a probability measure.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

variable {ι : Type*}

theorem s7f_summable2 {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (M : ℝ) :
    Summable (fun p : ι × ι => M * (b p.1 * b p.2)) :=
  (Summable.mul_of_nonneg hb hb (fun k => hb0 k) (fun k => hb0 k)).mul_left M

theorem s7f_tsum2 {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M : ℝ} {u : ι → ι → ℝ}
    (hu : ∀ k l, |u k l| ≤ M * (b k * b l)) :
    Summable (fun p : ι × ι => u p.1 p.2) ∧ (∀ k, Summable (u k)) ∧
      ∑' k, ∑' l, u k l = ∑' p : ι × ι, u p.1 p.2 := by
  have hs : Summable (fun p : ι × ι => u p.1 p.2) :=
    Summable.of_norm_bounded (s7f_summable2 hb hb0 M) (fun p => by
      rw [Real.norm_eq_abs]; exact hu p.1 p.2)
  exact ⟨hs, fun k => hs.prod_factor k, (hs.tsum_prod).symm⟩

theorem s7f_tsum2_swap {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M : ℝ} {u : ι → ι → ℝ}
    (hu : ∀ k l, |u k l| ≤ M * (b k * b l)) :
    ∑' k, ∑' l, u k l = ∑' l, ∑' k, u k l := by
  obtain ⟨hs, -, -⟩ := s7f_tsum2 hb hb0 hu
  exact (hs.tsum_comm).symm

theorem s7f_integral_tsum2 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [Countable ι] {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (M : ℝ) (g : ι → ι → X → ℝ)
    (hint : ∀ k l, Integrable (g k l) μ) (hbd : ∀ k l x, |g k l x| ≤ M * (b k * b l)) :
    ∫ x, ∑' k, ∑' l, g k l x ∂μ = ∑' k, ∑' l, ∫ x, g k l x ∂μ := by
  have hnorm : ∀ p : ι × ι, ∫ x, ‖g p.1 p.2 x‖ ∂μ ≤ M * (b p.1 * b p.2) := by
    intro p
    have := integral_mono_of_nonneg (μ := μ) (f := fun x => ‖g p.1 p.2 x‖)
      (g := fun _ => M * (b p.1 * b p.2)) (Eventually.of_forall fun x => norm_nonneg _)
      (integrable_const _) (Eventually.of_forall fun x => by
        show ‖g p.1 p.2 x‖ ≤ _
        rw [Real.norm_eq_abs]; exact hbd p.1 p.2 x)
    simpa using this
  have hsum : Summable (fun p : ι × ι => ∫ x, ‖g p.1 p.2 x‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun x => norm_nonneg _) hnorm
      (s7f_summable2 hb hb0 M)
  have h := integral_tsum_of_summable_integral_norm (μ := μ) (F := fun (p : ι × ι) x => g p.1 p.2 x)
    (fun p => hint p.1 p.2) hsum
  have hI : ∀ k l, |∫ x, g k l x ∂μ| ≤ M * (b k * b l) := by
    intro k l
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := g k l) (C := M * (b k * b l))
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd k l x)
    simpa using this
  obtain ⟨-, -, e1⟩ := s7f_tsum2 hb hb0 hI
  rw [e1, h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨-, -, e2⟩ := s7f_tsum2 hb hb0 (fun k l => hbd k l x)
  exact e2

theorem s7f_tsum2_sub {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M₁ M₂ : ℝ}
    {u w : ι → ι → ℝ} (hu : ∀ k l, |u k l| ≤ M₁ * (b k * b l)) (hw : ∀ k l, |w k l| ≤ M₂ * (b k * b l)) :
    ∑' k, ∑' l, (u k l - w k l) = (∑' k, ∑' l, u k l) - ∑' k, ∑' l, w k l := by
  obtain ⟨hsu, -, eu⟩ := s7f_tsum2 hb hb0 hu
  obtain ⟨hsw, -, ew⟩ := s7f_tsum2 hb hb0 hw
  obtain ⟨-, -, e⟩ := s7f_tsum2 hb hb0 (u := fun k l => u k l - w k l) (M := M₁ + M₂)
    (fun k l => (abs_sub _ _).trans (by nlinarith [hu k l, hw k l]))
  rw [e, eu, ew]
  exact hsu.tsum_sub hsw

theorem s7f_tsum2_add {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M₁ M₂ : ℝ}
    {u w : ι → ι → ℝ} (hu : ∀ k l, |u k l| ≤ M₁ * (b k * b l)) (hw : ∀ k l, |w k l| ≤ M₂ * (b k * b l)) :
    ∑' k, ∑' l, (u k l + w k l) = (∑' k, ∑' l, u k l) + ∑' k, ∑' l, w k l := by
  obtain ⟨hsu, -, eu⟩ := s7f_tsum2 hb hb0 hu
  obtain ⟨hsw, -, ew⟩ := s7f_tsum2 hb hb0 hw
  obtain ⟨-, -, e⟩ := s7f_tsum2 hb hb0 (u := fun k l => u k l + w k l) (M := M₁ + M₂)
    (fun k l => (abs_add_le _ _).trans (by nlinarith [hu k l, hw k l]))
  rw [e, eu, ew]
  exact hsu.tsum_add hsw

theorem s7f_tsum2_const_mul {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M : ℝ}
    {u : ι → ι → ℝ} (hu : ∀ k l, |u k l| ≤ M * (b k * b l)) (c : ℝ) :
    ∑' k, ∑' l, c * u k l = c * ∑' k, ∑' l, u k l := by
  obtain ⟨hsu, -, eu⟩ := s7f_tsum2 hb hb0 hu
  obtain ⟨-, -, e⟩ := s7f_tsum2 hb hb0 (u := fun k l => c * u k l) (M := |c| * M)
    (fun k l => by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hu k l) (abs_nonneg c))
  rw [e, eu]
  exact tsum_mul_left

theorem s7f_tsum2_abs_le {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) {M : ℝ}
    {u : ι → ι → ℝ} (hu : ∀ k l, |u k l| ≤ M * (b k * b l)) :
    |∑' k, ∑' l, u k l| ≤ M * ∑' p : ι × ι, b p.1 * b p.2 := by
  obtain ⟨hsu, -, eu⟩ := s7f_tsum2 hb hb0 hu
  rw [eu]
  have hs2 : Summable (fun p : ι × ι => b p.1 * b p.2) :=
    Summable.mul_of_nonneg hb hb (fun k => hb0 k) (fun k => hb0 k)
  have := tsum_of_norm_bounded ((hs2.mul_left M).hasSum) (f := fun p : ι × ι => u p.1 p.2)
    (fun p => by rw [Real.norm_eq_abs]; exact hu p.1 p.2)
  rw [← Real.norm_eq_abs]
  rw [tsum_mul_left] at this
  exact this

end HRS.MC.Sec7.S7f

end
