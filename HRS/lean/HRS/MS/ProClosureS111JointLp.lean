import HRS.MS.R26T6CI16
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Joint representatives of strongly measurable `Lp` families

The parameter space has no measure. The section of the constructed jointly
strongly measurable function represents the prescribed `Lp` vector at every
parameter value. The spatial exceptional set may depend on that parameter.

Use the accepted geometric countably valued approximation, then sum the
successive differences of its representatives. Mathlib's `Lp.coeFn_tsum`
identifies that sum separately at each parameter value.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HRS.MS.ProClosureS111

private theorem countable_range_Lp_jointly_stronglyMeasurable
    {A X E : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [NormedAddCommGroup E] [SecondCountableTopology E]
    (mu : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : A → Lp E p mu) (hQ : StronglyMeasurable Q)
    (hc : (Set.range Q).Countable) :
    StronglyMeasurable (fun z : A × X => (Q z.1 : X → E) z.2) := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (Lp E p mu) := borel (Lp E p mu)
  letI : BorelSpace (Lp E p mu) := ⟨rfl⟩
  letI : Countable (Set.range Q) := hc.to_subtype
  have heval : Measurable (fun z : Set.range Q × X =>
      ((z.1 : Lp E p mu) : X → E) z.2) := by
    exact measurable_from_prod_countable_right
      (fun q => (Lp.stronglyMeasurable (q : Lp E p mu)).measurable)
  have hindex : Measurable (fun z : A × X =>
      (Set.rangeFactorization Q z.1, z.2)) :=
    (hQ.measurable.rangeFactorization.comp measurable_fst).prodMk measurable_snd
  exact (heval.comp hindex).stronglyMeasurable

/-- Every strongly measurable family of `Lp` vectors admits a jointly strongly
measurable representative whose section is correct at every parameter value.
This stronger auxiliary form does not need finiteness of the spatial measure
or finiteness of the exponent. -/
theorem joint_Lp_representative_general
    {A X E : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    (mu : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : A → Lp E p mu) (hF : StronglyMeasurable F) :
    ∃ g : A × X → E, StronglyMeasurable g ∧
      ∀ a, MemLp (fun x => g (a, x)) p mu ∧
        (fun x => g (a, x)) =ᵐ[mu] (F a : X → E) := by
  classical
  obtain ⟨Q, hQ, hQapprox⟩ :=
    HRS.MS.R26T6C.r26t6c_geometric_approximation F hF
  have hQbound : ∀ n a, ‖Q n a - F a‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n a
    simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using hQapprox n a
  have hQjoint : ∀ n, StronglyMeasurable
      (fun z : A × X => (Q n z.1 : X → E) z.2) :=
    fun n => countable_range_Lp_jointly_stronglyMeasurable mu p
      (Q n) (hQ n).1 (hQ n).2
  have hQlim : ∀ a, Tendsto (fun n => Q n a) atTop (𝓝 (F a)) := by
    intro a
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hQbound n a)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  let D : ℕ → A → Lp E p mu := fun n a => Q (n + 1) a - Q n a
  have hDnorm : ∀ a, Summable (fun n => ‖D n a‖) := by
    intro a
    have hgeo : Summable (fun n : ℕ =>
        (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ n) :=
      ((summable_nat_add_iff 1).2 summable_geometric_two).add summable_geometric_two
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
    calc
      ‖D n a‖ = ‖(Q (n + 1) a - F a) + (F a - Q n a)‖ := by
        congr 1
        dsimp [D]
        abel
      _ ≤ ‖Q (n + 1) a - F a‖ + ‖F a - Q n a‖ := norm_add_le _ _
      _ = ‖Q (n + 1) a - F a‖ + ‖Q n a - F a‖ := by rw [norm_sub_rev (F a)]
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ n :=
        add_le_add (hQbound (n + 1) a) (hQbound n a)
  have hDsum : ∀ a, (∑' n, D n a) = F a - Q 0 a := by
    intro a
    have htel : ∀ n, (∑ i ∈ Finset.range n, D i a) = Q n a - Q 0 a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [D]
        abel
    have hsum : HasSum (fun n => D n a) (F a - Q 0 a) := by
      apply hasSum_of_subseq_of_summable (hDnorm a) tendsto_finset_range
      simpa only [htel] using (hQlim a).sub_const (Q 0 a)
    exact hsum.tsum_eq
  let g : A × X → E := fun z => (Q 0 z.1 : X → E) z.2 +
    ∑' n, ((Q (n + 1) z.1 : X → E) z.2 - (Q n z.1 : X → E) z.2)
  have hg : StronglyMeasurable g :=
    (hQjoint 0).add (StronglyMeasurable.tsum
      (fun n => (hQjoint (n + 1)).sub (hQjoint n)))
  refine ⟨g, hg, ?_⟩
  intro a
  have hDfinite : (∑' n, ‖D n a‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.2 (hDnorm a)
  have hDcoe : ∀ᵐ x ∂mu, ∀ n,
      (D n a : X → E) x =
        (Q (n + 1) a : X → E) x - (Q n a : X → E) x := by
    exact ae_all_iff.2 (fun n => Lp.coeFn_sub (Q (n + 1) a) (Q n a))
  have heq : (fun x => g (a, x)) =ᵐ[mu] (F a : X → E) := by
    filter_upwards [Lp.coeFn_tsum hDfinite, hDcoe,
      Lp.coeFn_sub (F a) (Q 0 a)] with x hx hdx hfx
    change (Q 0 a : X → E) x +
      (∑' n, ((Q (n + 1) a : X → E) x - (Q n a : X → E) x)) =
        (F a : X → E) x
    have hseries : (∑' n, ((Q (n + 1) a : X → E) x -
        (Q n a : X → E) x)) = ((∑' n, D n a : Lp E p mu) : X → E) x := by
      exact (tsum_congr (fun n => (hdx n).symm)).trans hx.symm
    rw [hseries, hDsum a, hfx]
    change (Q 0 a : X → E) x +
      ((F a : X → E) x - (Q 0 a : X → E) x) = (F a : X → E) x
    abel
  exact ⟨(memLp_congr_ae heq).2 (Lp.memLp (F a)), heq⟩

/-- The exact finite-measure, finite-exponent I17 interface. There is no measure
on `A`, and the representative equality holds for every `a : A`. -/
theorem joint_Lp_representative
    {A X E : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (mu : Measure X) [IsFiniteMeasure mu]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (F : A → Lp E p mu) (hF : StronglyMeasurable F) :
    ∃ g : A × X → E, StronglyMeasurable g ∧
      ∀ a, MemLp (fun x => g (a, x)) p mu ∧
        (fun x => g (a, x)) =ᵐ[mu] (F a : X → E) := by
  exact joint_Lp_representative_general mu p F hF

end HRS.MS.ProClosureS111
