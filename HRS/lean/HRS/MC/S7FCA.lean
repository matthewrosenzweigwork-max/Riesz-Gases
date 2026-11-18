import HRS.MC.Sec7Vocab

/-!
# FC-A: the exact finite-rank identity (`F:eq:finite-rank-identity`, TeX L8228-8231)

Packet `s7fca` (plan row FC-A of `HRS/MC/Sec7Plan.md`).  Proof of `HRS.MC.Sec7.s7_FC_A_finite_rank_identity`
(the frozen spec in `HRS/MC/Sec7Spec.lean` stays `sorry`; the tie is in `HRS/MC/S7FCATie.lean`).

Route: expand `modulatedEnergy` for the kernel `h(x,y) = sum_ab c_ab f_a(x) f_b(y)`; the `i != j` sum is the full
double sum minus the diagonal, the one-point term is `sum_i int h(x_i,y) dmu`, and the constant term is
`sum_ab c_ab mu(f_a) mu(f_b)`.  Symmetry of `c` is used once, to merge the two cross terms.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCA

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- A measurable real function bounded by `M` is integrable on a finite measure. -/
theorem s7fca_integrable {μ : Measure (Torus d)} [IsFiniteMeasure μ] {g : Torus d → ℝ} {M : ℝ}
    (hg : Measurable g) (hM : ∀ x, |g x| ≤ M) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable M (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hM x)

/-- The empirical pairing: `mu_N(phi) = N⁻¹ sum_i phi(x_i)`. -/
theorem s7fca_pair_empirical {N : ℕ} (X : Config d N) (φ : Torus d → ℝ) :
    pair (empirical X) φ = (1 / (N : ℝ)) * ∑ i, φ (X i) := by
  unfold pair empirical
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  · intro i _
    exact integrable_dirac (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_lt_top)

/-- Exchange of four finite sums, `i j a b -> a b i j`. -/
theorem s7fca_sum_comm4 {n N : ℕ} (g : Fin N → Fin N → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, g i j a b = ∑ a, ∑ b, ∑ i, ∑ j, g i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, g i j a b = ∑ i, ∑ a, ∑ j, ∑ b, g i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, g i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, g i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, g i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- The one-point slice of the kernel: `int h(x,y) dmu(y) = sum_ab c_ab f_a(x) mu(f_b)`. -/
theorem s7fca_slice {n : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (f : Fin n → Torus d → ℝ) (hint : ∀ a, Integrable (f a) μ) (c : Fin n → Fin n → ℝ) (x : Torus d) :
    ∫ y, (∑ a, ∑ b, c a b * f a x * f b y) ∂μ = ∑ a, ∑ b, c a b * f a x * pair μ (f b) := by
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]
      rfl
    · intro b _
      exact (hint b).const_mul _
  · intro a _
    exact integrable_finset_sum _ fun b _ => (hint b).const_mul _

/-- The double integral: `int int h dmu dmu = sum_ab c_ab mu(f_a) mu(f_b)`. -/
theorem s7fca_double {n : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (f : Fin n → Torus d → ℝ) (hint : ∀ a, Integrable (f a) μ) (c : Fin n → Fin n → ℝ) :
    ∫ x, ∫ y, (∑ a, ∑ b, c a b * f a x * f b y) ∂μ ∂μ =
      ∑ a, ∑ b, c a b * (pair μ (f a) * pair μ (f b)) := by
  simp only [s7fca_slice μ f hint c]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_const_mul]
      simp only [pair]
      ring
    · intro b _
      exact ((hint a).const_mul (c a b)).mul_const _
  · intro a _
    exact integrable_finset_sum _ fun b _ => ((hint a).const_mul (c a b)).mul_const _

/-- Algebra: the identity after all integrals and empirical pairings are evaluated. -/
theorem s7fca_core {n N : ℕ} (hN : 1 ≤ N) (c : Fin n → Fin n → ℝ) (hc : ∀ a b, c a b = c b a)
    (u m : Fin n → ℝ) (w : Fin n → Fin n → ℝ) :
    (N : ℝ) * ((1 / (2 * (N : ℝ) ^ 2)) * (∑ a, ∑ b, c a b * (u a * u b - w a b))
        - (1 / (N : ℝ)) * (∑ a, ∑ b, c a b * (u a * m b))
        + (1 / 2) * (∑ a, ∑ b, c a b * (m a * m b))) =
      (1 / 2) * ∑ a, ∑ b, c a b * (Real.sqrt N * ((1 / (N : ℝ)) * u a - m a))
          * (Real.sqrt N * ((1 / (N : ℝ)) * u b - m b))
        - (1 / 2) * ∑ a, ∑ b, c a b * ((1 / (N : ℝ)) * w a b) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hsym : ∑ a, ∑ b, c a b * (m a * u b) = ∑ a, ∑ b, c a b * (u a * m b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hc]
    ring
  have hterm : ∀ a b, c a b * (Real.sqrt N * ((1 / (N : ℝ)) * u a - m a))
      * (Real.sqrt N * ((1 / (N : ℝ)) * u b - m b)) =
        (1 / (N : ℝ)) * (c a b * (u a * u b)) - c a b * (u a * m b)
          - c a b * (m a * u b) + (N : ℝ) * (c a b * (m a * m b)) := by
    intro a b
    have e : c a b * (Real.sqrt N * ((1 / (N : ℝ)) * u a - m a))
        * (Real.sqrt N * ((1 / (N : ℝ)) * u b - m b)) =
          c a b * (Real.sqrt N * Real.sqrt N) * ((1 / (N : ℝ)) * u a - m a)
            * ((1 / (N : ℝ)) * u b - m b) := by ring
    rw [e, hs]
    field_simp
    ring
  simp only [hterm]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsym]
  have hw : ∀ a b, c a b * ((1 / (N : ℝ)) * w a b) = (1 / (N : ℝ)) * (c a b * w a b) :=
    fun a b => by ring
  simp only [hw, ← Finset.mul_sum]
  have hinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0
  linear_combination ((1 / 2 : ℝ) * (N : ℝ)⁻¹ * (∑ a, ∑ b, c a b * (u a * u b))
    - (1 / 2 : ℝ) * (N : ℝ)⁻¹ * (∑ a, ∑ b, c a b * w a b)
    - ∑ a, ∑ b, c a b * (u a * m b)) * hinv

/-- **FC-A (the exact finite-rank identity `F:eq:finite-rank-identity`, TeX L8228-8231)**.  For `h(x,y) = sum_{ab}
c_ab f_a(x) f_b(y)` with bounded measurable `f_a` and a probability measure `mu`:
`N F_N^h(X, mu) = (1/2) sum_ab c_ab eta(f_a) eta(f_b) - (1/2) sum_ab c_ab mu_N(f_a f_b)`,
`eta(f) = sqrt N (mu_N(f) - mu(f))`.  Pure algebra on `modulatedEnergy` (the `i != j` sum is the full double sum
minus the diagonal).  ~150 lines.
REVIEW REPAIR: `c` must be symmetric (`hc`): `modulatedEnergy` uses only the first slot in `-(1/N) sum_i int h(X_i,y) dmu`,
so for non-symmetric `c` the identity fails (n = 2, c_12 = 1). -/
theorem s7_FC_A_finite_rank_identity_proof {N n : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (f : Fin n → Torus d → ℝ) (hf : ∀ a, Measurable (f a))
    (hfb : ∀ a, ∃ M, ∀ x, |f a x| ≤ M) (c : Fin n → Fin n → ℝ) (hc : ∀ a b, c a b = c b a)
    (X : Config d N) :
    (N : ℝ) * modulatedEnergy (fun x y => ∑ a, ∑ b, c a b * f a x * f b y) X μ =
      (1 / 2) * ∑ a, ∑ b, c a b *
          (Real.sqrt N * (pair (empirical X) (f a) - pair μ (f a))) *
          (Real.sqrt N * (pair (empirical X) (f b) - pair μ (f b))) -
        (1 / 2) * ∑ a, ∑ b, c a b * pair (empirical X) (fun x => f a x * f b x) := by
  choose M hM using hfb
  have hint : ∀ a, Integrable (f a) μ := fun a =>
    s7fca_integrable (μ := μ) (hf a) (hM a)
  -- diagonal-removed double sum
  have hsum1 : ∑ i, ∑ j ∈ Finset.univ.erase i, (∑ a, ∑ b, c a b * f a (X i) * f b (X j)) =
      ∑ a, ∑ b, c a b * ((∑ i, f a (X i)) * (∑ i, f b (X i)) - ∑ i, f a (X i) * f b (X i)) := by
    have hdiag : ∀ i, ∑ j ∈ Finset.univ.erase i, (∑ a, ∑ b, c a b * f a (X i) * f b (X j)) =
        ∑ j, (∑ a, ∑ b, c a b * f a (X i) * f b (X j)) - (∑ a, ∑ b, c a b * f a (X i) * f b (X i)) :=
      fun i => Finset.sum_erase_eq_sub (Finset.mem_univ i)
    simp only [hdiag]
    rw [Finset.sum_sub_distrib]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · refine (s7fca_sum_comm4 (fun i j a b => c a b * f a (X i) * f b (X j))).trans ?_
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  have hsum2 : ∑ i, ∫ y, (∑ a, ∑ b, c a b * f a (X i) * f b y) ∂μ =
      ∑ a, ∑ b, c a b * ((∑ i, f a (X i)) * pair μ (f b)) := by
    simp only [s7fca_slice μ f hint c]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  have hdbl := s7fca_double μ f hint c
  simp only [modulatedEnergy, s7fca_pair_empirical]
  rw [hsum1, hsum2, hdbl]
  exact s7fca_core hN c hc (fun a => ∑ i, f a (X i)) (fun a => pair μ (f a))
    (fun a b => ∑ i, f a (X i) * f b (X i))

end HRS.MC.Sec7.FCA

end
