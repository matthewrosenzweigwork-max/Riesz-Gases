import HRS.MC.SEdgeB14Aux1

/-!
# Packet B14, helper 2: algebra (symmetrisation with the cubic cancellation) and the centring split
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B14

open HRS.Sec7
open HRS.MC.SEdge

/-- the centring split of `S * E[(c - A) g]`. -/
theorem b14_split {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (c S : ℝ) (A g : Ω → ℝ)
    (hg : Integrable g Q) (hAg : Integrable (fun X => A X * g X) Q) :
    S * ∫ X, (c - A X) * g X ∂Q =
      S * (c - ∫ Y, A Y ∂Q) * ∫ X, g X ∂Q - ∫ X, S * (A X - ∫ Y, A Y ∂Q) * g X ∂Q := by
  set m := ∫ Y, A Y ∂Q with hm
  have h1 : ∫ X, (c - A X) * g X ∂Q = c * ∫ X, g X ∂Q - ∫ X, A X * g X ∂Q := by
    have : (fun X => (c - A X) * g X) = fun X => c * g X - A X * g X := by
      funext X; ring
    rw [this, integral_sub (hg.const_mul c) hAg, integral_const_mul]
  have h2 : ∫ X, S * (A X - m) * g X ∂Q = S * ∫ X, A X * g X ∂Q - S * m * ∫ X, g X ∂Q := by
    have : (fun X => S * (A X - m) * g X) = fun X => S * (A X * g X) - (S * m) * g X := by
      funext X; ring
    rw [this, integral_sub (hAg.const_mul S) (hg.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [h1, h2]; ring

/-- symmetrisation: the cubic cancellation turns the `R2 + R3` limits into `-(1/2) kappa T`. -/
theorem b14_alg {p : ℕ} (β : ℝ) (T m q κ : Fin p → Fin p → Fin p → ℝ)
    (hT : ∀ a b c, T a b c = T a c b)
    (hcan : ∀ a b c, m a b c + m a c b - β * q a b c = κ a b c) :
    -(∑ a, ∑ b, ∑ c, m a b c * T a c b) + β * ∑ a, (1 / 2) * ∑ b, ∑ c, q a b c * T a b c =
      -(1 / 2) * ∑ a, ∑ b, ∑ c, κ a b c * T a b c := by
  have key : ∀ a, ∑ b, ∑ c, m a b c * T a c b =
      (1 / 2) * (∑ b, ∑ c, κ a b c * T a b c + β * ∑ b, ∑ c, q a b c * T a b c) := by
    intro a
    have e1 : ∑ b, ∑ c, m a b c * T a c b = ∑ b, ∑ c, m a b c * T a b c :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [← hT a b c]
    have e2 : ∑ b, ∑ c, m a b c * T a b c = ∑ b, ∑ c, m a c b * T a b c := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hT a c b]
    have e3 : ∑ b, ∑ c, (m a b c + m a c b) * T a b c =
        ∑ b, ∑ c, (κ a b c + β * q a b c) * T a b c :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
        have := hcan a b c; congr 1; linarith
    have e4 : ∑ b, ∑ c, (m a b c + m a c b) * T a b c =
        ∑ b, ∑ c, m a b c * T a b c + ∑ b, ∑ c, m a c b * T a b c := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
    have e5 : ∑ b, ∑ c, (κ a b c + β * q a b c) * T a b c =
        ∑ b, ∑ c, κ a b c * T a b c + β * ∑ b, ∑ c, q a b c * T a b c := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1]
    linarith
  have per : ∀ a, -(∑ b, ∑ c, m a b c * T a c b) + β * ((1 / 2) * ∑ b, ∑ c, q a b c * T a b c) =
      -(1 / 2) * ∑ b, ∑ c, κ a b c * T a b c := by
    intro a; rw [key a]; ring
  calc -(∑ a, ∑ b, ∑ c, m a b c * T a c b) + β * ∑ a, (1 / 2) * ∑ b, ∑ c, q a b c * T a b c
      = ∑ a, (-(∑ b, ∑ c, m a b c * T a c b) +
          β * ((1 / 2) * ∑ b, ∑ c, q a b c * T a b c)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    _ = ∑ a, (-(1 / 2) * ∑ b, ∑ c, κ a b c * T a b c) := Finset.sum_congr rfl fun a _ => per a
    _ = -(1 / 2) * ∑ a, ∑ b, ∑ c, κ a b c * T a b c := by rw [Finset.mul_sum]


/-- bounded measurable functions. -/
def b14Bdd {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∃ M, ∀ X, |f X| ≤ M

theorem b14Bdd.mul {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : b14Bdd f) (hg : b14Bdd g) :
    b14Bdd (fun X => f X * g X) := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  obtain ⟨hgm, Mg, hMg⟩ := hg
  refine ⟨hfm.mul hgm, Mf * Mg, fun X => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hMf X) (hMg X) (abs_nonneg _) ((abs_nonneg _).trans (hMf X))

theorem b14Bdd.integrable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : b14Bdd f)
    (Q : Measure Ω) [IsFiniteMeasure Q] : Integrable f Q := by
  obtain ⟨hm, M, hM⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM X)

theorem b14_abs_integral_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f : Ω → ℝ} {M : ℝ} (hM : ∀ X, |f X| ≤ M) : |∫ X, f X ∂Q| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := Q) (f := f) (C := M)
    (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM X)
  simpa using this

theorem b14_sqrt_div {N : ℕ} (hN : 1 ≤ N) (K : ℝ) :
    Real.sqrt N * (K / N) = K / Real.sqrt N := by
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have h : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
  generalize Real.sqrt N = t at hpos h ⊢
  rw [h]
  field_simp

theorem b14_tendsto_sqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem b14_Wmeas {d N : ℕ} (hN : 1 ≤ N) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (Q : Measure (Config d N)) :
    Measurable (centeredStat Q φ) := by
  have hφc : ∀ a, Continuous (φ a) := fun a => HRS.Q66.q66_cont_of_smooth (hφ a)
  unfold centeredStat
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
    measurable_const.mul ((B5b.b5b_pair_meas hN (hφc a).measurable).sub measurable_const))

end HRS.MC.SEdge.B14

end
