import HRS.MS.Fp81S21JointAvg

/-!
# Uniform smoothing profiles for joint averaging

The profile below is selected only from the common smoothing error, operator
bound, and source-distance sequences.  It is independent of any family of
probability laws or choices of continuous versions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- The common profile obtained by taking the infimum over smoothing scales. -/
def fp81s21_jointAvg_unifProfile (ω K q : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨅ k : ℕ, (2 * ω k + K k * q n)

/-- Nonnegative common inputs give a nonnegative infimum profile, and the
profile tends to zero when the smoothing error and source distance do.  No
uniform bound on `K` is needed: at the selected fixed `k`, `K k` is a finite
real constant. -/
theorem fp81s21_jointAvg_unifProfile_spec
    (ω K q : ℕ → ℝ)
    (hω : ∀ k, 0 ≤ ω k) (hK : ∀ k, 0 ≤ K k) (hq : ∀ n, 0 ≤ q n)
    (hωt : Tendsto ω atTop (𝓝 0)) (hqt : Tendsto q atTop (𝓝 0)) :
    (∀ n, 0 ≤ fp81s21_jointAvg_unifProfile ω K q n) ∧
      Tendsto (fp81s21_jointAvg_unifProfile ω K q) atTop (𝓝 0) := by
  constructor
  · intro n
    change 0 ≤ ⨅ k : ℕ, (2 * ω k + K k * q n)
    apply le_ciInf
    intro k
    exact add_nonneg (mul_nonneg (by norm_num) (hω k))
      (mul_nonneg (hK k) (hq n))
  · change Tendsto (fun n => ⨅ k : ℕ, (2 * ω k + K k * q n)) atTop (𝓝 0)
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [] with n
      exact lt_of_lt_of_le ha (by
        change 0 ≤ ⨅ k : ℕ, (2 * ω k + K k * q n)
        apply le_ciInf
        intro k
        exact add_nonneg (mul_nonneg (by norm_num) (hω k))
          (mul_nonneg (hK k) (hq n)))
    · intro b hb
      have hωevent : ∀ᶠ k : ℕ in atTop, 2 * ω k < b / 2 := by
        have hevent : ∀ᶠ k : ℕ in atTop, ω k < b / 4 :=
          hωt.eventually (Iio_mem_nhds (by positivity))
        filter_upwards [hevent] with k hk
        nlinarith
      obtain ⟨k₀, hk₀⟩ := hωevent.exists
      have hprodlim : Tendsto (fun n => K k₀ * q n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := K k₀)).mul hqt
      have hqevent : ∀ᶠ n : ℕ in atTop, K k₀ * q n < b / 2 :=
        hprodlim.eventually (Iio_mem_nhds (by positivity))
      have hbdd (n : ℕ) :
          BddBelow (Set.range (fun k : ℕ => 2 * ω k + K k * q n)) := by
        refine ⟨0, ?_⟩
        rintro x ⟨k, rfl⟩
        exact add_nonneg (mul_nonneg (by norm_num) (hω k))
          (mul_nonneg (hK k) (hq n))
      filter_upwards [hqevent] with n hn
      calc
        fp81s21_jointAvg_unifProfile ω K q n ≤ 2 * ω k₀ + K k₀ * q n :=
          ciInf_le (hbdd n) k₀
        _ < b := by nlinarith

/-- Uniform family transfer through the smoothing infimum.  A common bound at
every smoothing index yields the same `ofReal` bound for every member of the
family, with a profile independent of the family. -/
theorem fp81s21_jointAvg_unif_family_bound
    {B ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    (μ ν : ι → ℕ → Measure B)
    (ω K q : ℕ → ℝ)
    (hω : ∀ k, 0 ≤ ω k) (hK : ∀ k, 0 ≤ K k) (hq : ∀ n, 0 ≤ q n)
    (hbound : ∀ i k n,
      wassersteinE 2 (μ i n) (ν i n) ≤
        ENNReal.ofReal (2 * ω k + K k * q n)) :
    ∀ i n, wassersteinE 2 (μ i n) (ν i n) ≤
      ENNReal.ofReal (fp81s21_jointAvg_unifProfile ω K q n) := by
  intro i n
  calc
    wassersteinE 2 (μ i n) (ν i n) ≤
        ⨅ k : ℕ, ENNReal.ofReal (2 * ω k + K k * q n) :=
      le_iInf (fun k => hbound i k n)
    _ = ENNReal.ofReal (fp81s21_jointAvg_unifProfile ω K q n) := by
      exact (ENNReal.ofReal_iInf (fun k : ℕ => 2 * ω k + K k * q n)).symm

/-! ## Exported axiom audit -/

#print axioms fp81s21_jointAvg_unifProfile_spec
#print axioms fp81s21_jointAvg_unif_family_bound

end HRS.Fp81.S21
