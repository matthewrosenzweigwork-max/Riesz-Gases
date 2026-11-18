import HRS.Commutator.Whole.LocalAuxSAMP1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Unit cubes and the discrete weight (packet CMX-SAMP, helper file 2)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

variable {d : ℕ}

/-- The unit cube `Q_j = j + [0,1)^d` (same set as `HRS.Commutator.Whole.cube`). -/
def cubeS (d : ℕ) (j : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, (j i : ℝ) ≤ x i ∧ x i < (j i : ℝ) + 1}

/-- The lattice point `j` as a vector. -/
def latV (j : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => (j i : ℝ))

lemma cubeS_eq_preimage (j : Fin d → ℤ) :
    cubeS d j = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      (Set.pi univ fun i => Ico (j i : ℝ) ((j i : ℝ) + 1)) := by
  ext x
  simp [cubeS, Set.mem_pi, forall_and]

lemma measurableSet_cubeS (j : Fin d → ℤ) : MeasurableSet (cubeS d j) := by
  rw [cubeS_eq_preimage]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

lemma volume_cubeS (j : Fin d → ℤ) : volume (cubeS d j) = 1 := by
  rw [cubeS_eq_preimage,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet,
    volume_pi_pi]
  simp

lemma cubeS_disjoint : Pairwise (Function.onFun Disjoint (cubeS d)) := by
  intro j j' hjj'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hjj'
  funext i
  have h1 := hx i
  have h2 := hx' i
  have : (j i : ℝ) = j' i := by
    have a1 : (j i : ℝ) < j' i + 1 := lt_of_le_of_lt h1.1 h2.2
    have a2 : (j' i : ℝ) < j i + 1 := lt_of_le_of_lt h2.1 h1.2
    have b1 : j i < j' i + 1 := by exact_mod_cast a1
    have b2 : j' i < j i + 1 := by exact_mod_cast a2
    have : j i = j' i := by omega
    exact_mod_cast this
  exact_mod_cast this

lemma iUnion_cubeS : (⋃ j : Fin d → ℤ, cubeS d j) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨fun i => ⌊x i⌋, fun i => ?_⟩
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

lemma norm_sub_latV_le {j : Fin d → ℤ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cubeS d j) :
    ‖x - latV j‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(x - latV j) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := hx i
        have : (x - latV j) i = x i - j i := rfl
        rw [this, Real.norm_eq_abs, sq_abs]
        have h0 : 0 ≤ x i - j i := by linarith [h.1]
        have h1 : x i - j i ≤ 1 := by linarith [h.2]
        nlinarith
    _ = d := by simp


lemma tsum_lintegral_cubeS (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∑' k : Fin d → ℤ, ∫⁻ x in cubeS d k, g x = ∫⁻ x, g x := by
  rw [← lintegral_iUnion measurableSet_cubeS cubeS_disjoint, iUnion_cubeS, Measure.restrict_univ]

/-- The discrete weight `(1 + |k|)^{-(d+1)}`. -/
def wtK (d : ℕ) (k : Fin d → ℤ) : ℝ := (1 + ‖latV k‖) ^ (-((d : ℝ) + 1))

lemma wtK_pos (k : Fin d → ℤ) : 0 < wtK d k := Real.rpow_pos_of_pos (by positivity) _

lemma wtK_le_cube (k : Fin d → ℤ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cubeS d k) :
    wtK d k ≤ (1 + Real.sqrt d) ^ ((d : ℝ) + 1) * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h1 : 1 + ‖x‖ ≤ (1 + Real.sqrt d) * (1 + ‖latV k‖) := by
    have := norm_sub_latV_le hx
    have h2 : ‖x‖ ≤ ‖latV k‖ + ‖x - latV k‖ := by
      calc ‖x‖ = ‖(x - latV k) + latV k‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - latV k‖ + ‖latV k‖ := norm_add_le _ _
        _ = _ := add_comm _ _
    nlinarith [norm_nonneg (latV k)]
  have hpos : 0 < 1 + ‖latV k‖ := by positivity
  have hpos' : 0 < 1 + ‖x‖ := by positivity
  unfold wtK
  have h3 : ((1 + ‖x‖) ^ ((d : ℝ) + 1)) ≤ ((1 + Real.sqrt d) * (1 + ‖latV k‖)) ^ ((d : ℝ) + 1) :=
    Real.rpow_le_rpow hpos'.le h1 (by positivity)
  rw [Real.mul_rpow (by positivity) hpos.le] at h3
  rw [Real.rpow_neg hpos.le, Real.rpow_neg hpos'.le]
  have hp1 : 0 < (1 + ‖latV k‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hpos _
  have hp2 : 0 < (1 + ‖x‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hpos' _
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hp1 hp2]
  linarith


lemma tsum_wtK_lt_top : ∑' k : Fin d → ℤ, ENNReal.ofReal (wtK d k) < ⊤ := by
  set C : ℝ := (1 + Real.sqrt d) ^ ((d : ℝ) + 1) with hC
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
    refine integrable_one_add_norm (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) ?_
    rw [finrank_euclideanSpace_fin]; linarith
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_norm).pow_const _)
  have h1 : ∀ k : Fin d → ℤ, ENNReal.ofReal (wtK d k) ≤
      ∫⁻ x in cubeS d k, ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
    intro k
    calc ENNReal.ofReal (wtK d k) = ∫⁻ _x in cubeS d k, ENNReal.ofReal (wtK d k) := by
          rw [setLIntegral_const, volume_cubeS, mul_one]
      _ ≤ _ := by
          refine setLIntegral_mono' (measurableSet_cubeS k) fun x hx => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (wtK_le_cube k hx)
  calc ∑' k : Fin d → ℤ, ENNReal.ofReal (wtK d k)
      ≤ ∑' k : Fin d → ℤ, ∫⁻ x in cubeS d k,
          ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
        ENNReal.tsum_le_tsum h1
    _ = ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
        tsum_lintegral_cubeS _
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
        lintegral_const_mul _ hmeas
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.lintegral_lt_top


instance volume_isNegInvariant_E :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).IsNegInvariant :=
  ⟨(LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin d))).measurePreserving.map_eq⟩

lemma ae_ne_zero_E (hd : 1 ≤ d) : ∀ᵐ x : EuclideanSpace ℝ (Fin d) ∂volume, x ≠ 0 := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  have h0 : volume ({0} : Set (EuclideanSpace ℝ (Fin d))) = 0 := measure_singleton _
  rw [ae_iff]
  simpa using h0

lemma conj_mul (p : ℝ) (hp : 1 < p) : p.conjExponent * (p - 1) = p := by
  have : p - 1 ≠ 0 := by linarith
  rw [Real.conjExponent]; field_simp

/-- The kernel `K` is in `L^{p'}` (`(3.K-bounds)`, `α p > d`). -/
lemma kernel_Lq_lt_top (hd : 1 ≤ d) {α p : ℝ} (hp : 1 < p) (hα : (d : ℝ) < α * p)
    {K : EuclideanSpace ℝ (Fin d) → ℝ} (hKm : AEStronglyMeasurable K volume)
    {C₁ : ℝ} (hK1 : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → ‖x‖ ≤ 1 →
      |K x| ≤ C₁ * ‖x‖ ^ (α - d))
    {C₂ : ℝ} (hK2 : ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ →
      |K x| ≤ C₂ * ‖x‖ ^ (-((d : ℝ) + 1))) :
    ∫⁻ x, ‖K x‖ₑ ^ p.conjExponent < ⊤ := by
  set q := p.conjExponent with hqdef
  have hq := Real.HolderConjugate.conjExponent hp
  have hq1 : 1 < q := hq.symm.lt
  have hq0 : 0 < q := by linarith
  have hqp := conj_mul p hp
  have hfd : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hβ : ((d : ℝ) - α) * q < d := by
    have h1 : 0 < p - 1 := by linarith
    have : ((d : ℝ) - α) * q * (p - 1) < d * (p - 1) := by
      calc ((d : ℝ) - α) * q * (p - 1) = ((d : ℝ) - α) * (q * (p - 1)) := by ring
        _ = ((d : ℝ) - α) * p := by rw [hqp]
        _ < d * (p - 1) := by nlinarith
    exact lt_of_mul_lt_mul_right this h1.le
  have hg1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (-(((d : ℝ) - α) * q)))
      (ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := ((d : ℝ) - α) * q) (r := 1)
      (by rw [hfd]; exact hd) (by rw [hfd]; exact hβ) ?_ ?_
    · exact Eventually.of_forall fun x => by
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hind : Integrable (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      fun x => ‖x‖ ^ (-(((d : ℝ) - α) * q))) :=
    (integrable_indicator_iff measurableSet_ball).2 hg1
  have hg2 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-(((d : ℝ) + 1) * q))) := by
    refine integrable_one_add_norm (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) ?_
    rw [hfd]; nlinarith
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => |K x| ^ q) := by
    set A : ℝ := |C₁| ^ q with hA
    set B : ℝ := |C₂| ^ q * 2 ^ (((d : ℝ) + 1) * q) with hB
    refine ((hind.const_mul A).add (hg2.const_mul B)).mono' ?_ ?_
    · exact (hKm.norm.aemeasurable.pow_const q).aestronglyMeasurable.congr
        (Eventually.of_forall fun x => by simp)
    · filter_upwards [ae_ne_zero_E hd] with x hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      simp only [Pi.add_apply]
      by_cases hx1 : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
      · rw [Set.indicator_of_mem hx1]
        have hxl : ‖x‖ ≤ 1 := by simpa using hx1.out.le
        have h1 := hK1 x hx hxl
        have h2 : |K x| ^ q ≤ (|C₁| * ‖x‖ ^ (α - d)) ^ q := by
          refine Real.rpow_le_rpow (abs_nonneg _) (h1.trans ?_) hq0.le
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hxn.le _)
        rw [Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg hxn.le _), ← Real.rpow_mul hxn.le] at h2
        have h3 : ‖x‖ ^ ((α - d) * q) = ‖x‖ ^ (-(((d : ℝ) - α) * q)) := by
          congr 1; ring
        rw [h3] at h2
        have : 0 ≤ B * (1 + ‖x‖) ^ (-(((d : ℝ) + 1) * q)) := by positivity
        calc |K x| ^ q ≤ A * ‖x‖ ^ (-(((d : ℝ) - α) * q)) := h2
          _ ≤ _ := le_add_of_nonneg_right this
      · rw [Set.indicator_of_notMem hx1]
        have hx1' : 1 ≤ ‖x‖ := by simpa using hx1
        have h1 := hK2 x hx1'
        have h2 : |K x| ^ q ≤ (|C₂| * ‖x‖ ^ (-((d : ℝ) + 1))) ^ q := by
          refine Real.rpow_le_rpow (abs_nonneg _) (h1.trans ?_) hq0.le
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hxn.le _)
        rw [Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg hxn.le _), ← Real.rpow_mul hxn.le] at h2
        have h4 : ‖x‖ ^ (-((d : ℝ) + 1) * q) ≤ 2 ^ (((d : ℝ) + 1) * q) *
            (1 + ‖x‖) ^ (-(((d : ℝ) + 1) * q)) := by
          have h5 : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
          have h6 : (1 + ‖x‖) ^ (((d : ℝ) + 1) * q) ≤ (2 * ‖x‖) ^ (((d : ℝ) + 1) * q) :=
            Real.rpow_le_rpow (by positivity) h5 (by positivity)
          rw [Real.mul_rpow (by norm_num) hxn.le] at h6
          have h7 : 0 < (1 + ‖x‖) ^ (((d : ℝ) + 1) * q) := Real.rpow_pos_of_pos (by positivity) _
          have h8 : 0 < ‖x‖ ^ (((d : ℝ) + 1) * q) := Real.rpow_pos_of_pos hxn _
          rw [neg_mul, Real.rpow_neg hxn.le, Real.rpow_neg (by positivity),
            show (2 : ℝ) ^ (((d : ℝ) + 1) * q) * ((1 + ‖x‖) ^ (((d : ℝ) + 1) * q))⁻¹ =
              2 ^ (((d : ℝ) + 1) * q) / (1 + ‖x‖) ^ (((d : ℝ) + 1) * q) from
              (div_eq_mul_inv _ _).symm, inv_eq_one_div, div_le_div_iff₀ h8 h7]
          linarith
        calc |K x| ^ q ≤ |C₂| ^ q * ‖x‖ ^ (-((d : ℝ) + 1) * q) := h2
          _ ≤ |C₂| ^ q * (2 ^ (((d : ℝ) + 1) * q) * (1 + ‖x‖) ^ (-(((d : ℝ) + 1) * q))) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = _ := by ring
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have e : ∀ x : EuclideanSpace ℝ (Fin d), ‖K x‖ₑ ^ q = ENNReal.ofReal (|K x| ^ q) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  simp_rw [e]
  exact hint.lintegral_lt_top

end HRS.Commutator.Whole.SAMP1
