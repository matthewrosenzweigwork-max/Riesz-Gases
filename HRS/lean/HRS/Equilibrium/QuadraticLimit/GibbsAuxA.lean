import Mathlib

/-!
# Lemma 7.5, `q08_gibbs_approx`: stability of tilted functionals (prefix `q08gl_`)

For a probability space `(Ω, P)`, a weight `a ≥ 0`, a vector statistic `V : ι → Ω → ℝ` and a constant
`z > 0`, the tilted functional `Φ(a, V, z) = z⁻¹ ∫ F(V - z⁻¹ ∫ V a) a dP` is Lipschitz in `(a, V)`
and in `z`; these are the elementary estimates used in the replacement chain of the finite-rank
approximation.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

section ST

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

/-- The tilted functional `z⁻¹ ∫ F (V - z⁻¹ ∫ V a) a dP`. -/
def q08gl_Phi (P : Measure Ω) (F : (ι → ℝ) → ℝ) (a : Ω → ℝ) (V : ι → Ω → ℝ) (z : ℝ) : ℝ :=
  (1 / z) * ∫ ω, F (fun i => V i ω - (1 / z) * ∫ ω', V i ω' * a ω' ∂P) * a ω ∂P

/-- Centering constants. -/
def q08gl_c (P : Measure Ω) (a : Ω → ℝ) (V : ι → Ω → ℝ) (z : ℝ) (i : ι) : ℝ :=
  (1 / z) * ∫ ω, V i ω * a ω ∂P

theorem q08gl_Phi_eq (P : Measure Ω) (F : (ι → ℝ) → ℝ) (a : Ω → ℝ) (V : ι → Ω → ℝ) (z : ℝ) :
    q08gl_Phi P F a V z = (1 / z) * ∫ ω, F (fun i => V i ω - q08gl_c P a V z i) * a ω ∂P := rfl

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : (ι → ℝ) → ℝ) (M K : ℝ)

/-- Lipschitz estimate of the centering constants. -/
theorem q08gl_c_diff (a a' : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (V V' : ι → Ω → ℝ) (z : ℝ) (hz : 0 < z) (i : ι)
    (h1 : Integrable (fun ω => V i ω * a ω) P) (h2 : Integrable (fun ω => V' i ω * a' ω) P)
    (h3 : Integrable (fun ω => (V i ω - V' i ω) * a ω) P)
    (h4 : Integrable (fun ω => V' i ω * (a ω - a' ω)) P) :
    |q08gl_c P a V z i - q08gl_c P a' V' z i| ≤
      (1 / z) * (∫ ω, |V i ω - V' i ω| * a ω ∂P + ∫ ω, |V' i ω| * |a ω - a' ω| ∂P) := by
  unfold q08gl_c
  have e0 : ∫ ω, V i ω * a ω ∂P - ∫ ω, V' i ω * a' ω ∂P =
      ∫ ω, (V i ω - V' i ω) * a ω ∂P + ∫ ω, V' i ω * (a ω - a' ω) ∂P := by
    rw [← integral_add h3 h4, ← integral_sub h1 h2]
    congr 1
    funext ω
    ring
  have e : (1 / z) * ∫ ω, V i ω * a ω ∂P - (1 / z) * ∫ ω, V' i ω * a' ω ∂P =
      (1 / z) * (∫ ω, (V i ω - V' i ω) * a ω ∂P + ∫ ω, V' i ω * (a ω - a' ω) ∂P) := by
    rw [← mul_sub, e0]
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / z)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_integral_le_integral_abs).trans ?_
    refine le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_))
    simp [abs_mul, abs_of_nonneg (ha0 ω)]
  · refine (abs_integral_le_integral_abs).trans ?_
    refine le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_))
    simp [abs_mul]

/-- Stability of the tilted functional under a change of weight and statistic. -/
theorem q08gl_ST_a (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (a a' : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha : Integrable a P) (ha' : Integrable a' P)
    (V V' : ι → Ω → ℝ) (hV : ∀ i, Measurable (V i)) (hV' : ∀ i, Measurable (V' i))
    (z : ℝ) (hz : 0 < z)
    (h1 : ∀ i, Integrable (fun ω => V i ω * a ω) P) (h2 : ∀ i, Integrable (fun ω => V' i ω * a' ω) P)
    (h3 : ∀ i, Integrable (fun ω => (V i ω - V' i ω) * a ω) P)
    (h4 : ∀ i, Integrable (fun ω => V' i ω * (a ω - a' ω)) P) :
    |q08gl_Phi P F a V z - q08gl_Phi P F a' V' z| ≤
      (K / z) * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
        (1 / z) * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
          ∑ i, ∫ ω, |V' i ω| * |a ω - a' ω| ∂P) * ∫ ω, a ω ∂P)
        + (M / z) * ∫ ω, |a ω - a' ω| ∂P := by
  set c : ι → ℝ := q08gl_c P a V z with hc
  set c' : ι → ℝ := q08gl_c P a' V' z with hc'
  set G : Ω → ℝ := fun ω => F (fun i => V i ω - c i) with hG
  set G' : Ω → ℝ := fun ω => F (fun i => V' i ω - c' i) with hG'
  have hGm : Measurable G := hFc.measurable.comp (measurable_pi_iff.2 fun i => (hV i).sub_const _)
  have hG'm : Measurable G' := hFc.measurable.comp (measurable_pi_iff.2 fun i => (hV' i).sub_const _)
  have hGb : ∀ ω, |G ω| ≤ M := fun ω => hM _
  have hG'b : ∀ ω, |G' ω| ≤ M := fun ω => hM _
  have hGa : Integrable (fun ω => G ω * a ω) P :=
    ha.bdd_mul hGm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hGb ω)
  have hG'a' : Integrable (fun ω => G' ω * a' ω) P :=
    ha'.bdd_mul hG'm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hG'b ω)
  have hG'a : Integrable (fun ω => G' ω * a ω) P :=
    ha.bdd_mul hG'm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hG'b ω)
  have hG'aa : Integrable (fun ω => G' ω * (a ω - a' ω)) P :=
    (ha.sub ha').bdd_mul hG'm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hG'b ω)
  have i3 : ∀ i, Integrable (fun ω => |V i ω - V' i ω| * a ω) P := fun i => by
    refine (h3 i).abs.congr (Eventually.of_forall fun ω => ?_)
    simp [abs_mul, abs_of_nonneg (ha0 ω)]
  have i4 : ∀ i, Integrable (fun ω => |V' i ω| * |a ω - a' ω|) P := fun i => by
    refine (h4 i).abs.congr (Eventually.of_forall fun ω => ?_)
    simp [abs_mul]
  have i5 : Integrable (fun ω => |a ω - a' ω|) P := (ha.sub ha').abs
  have hcd : ∀ i, |c i - c' i| ≤ (1 / z) * ((∫ ω, |V i ω - V' i ω| * a ω ∂P) +
      ∫ ω, |V' i ω| * |a ω - a' ω| ∂P) := fun i =>
    q08gl_c_diff P a a' ha0 V V' z hz i (h1 i) (h2 i) (h3 i) (h4 i)
  -- pointwise bound
  have hpt : ∀ ω, |G ω - G' ω| * a ω ≤ K * ((∑ i, |V i ω - V' i ω| * a ω) + (∑ i, |c i - c' i|) * a ω) := by
    intro ω
    have h := hF (fun i => V i ω - c i) (fun i => V' i ω - c' i)
    have h' : ∑ i, |(V i ω - c i) - (V' i ω - c' i)| ≤ ∑ i, |V i ω - V' i ω| + ∑ i, |c i - c' i| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have : (V i ω - c i) - (V' i ω - c' i) = (V i ω - V' i ω) - (c i - c' i) := by ring
      rw [this]; exact abs_sub _ _
    have h0 := ha0 ω
    calc |G ω - G' ω| * a ω ≤ (K * ∑ i, |(V i ω - c i) - (V' i ω - c' i)|) * a ω :=
          mul_le_mul_of_nonneg_right h h0
      _ ≤ (K * (∑ i, |V i ω - V' i ω| + ∑ i, |c i - c' i|)) * a ω :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h' hK0) h0
      _ = K * ((∑ i, |V i ω - V' i ω| * a ω) + (∑ i, |c i - c' i|) * a ω) := by
          have e1 : (∑ i, |V i ω - V' i ω| * a ω) = (∑ i, |V i ω - V' i ω|) * a ω :=
            (Finset.sum_mul ..).symm
          rw [e1]; ring
  have hint1 : ∫ ω, |G ω - G' ω| * a ω ∂P ≤
      K * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) + (∑ i, |c i - c' i|) * ∫ ω, a ω ∂P) := by
    have hI : Integrable (fun ω => K * ((∑ i, |V i ω - V' i ω| * a ω) + (∑ i, |c i - c' i|) * a ω)) P :=
      ((integrable_finsetSum _ fun i _ => i3 i).add (ha.const_mul _)).const_mul _
    have hl : Integrable (fun ω => |G ω - G' ω| * a ω) P := by
      refine ((hGa.sub hG'a).abs).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.sub_apply, ← sub_mul, abs_mul, abs_of_nonneg (ha0 ω)]
    refine (integral_mono hl hI hpt).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (integrable_finsetSum _ fun i _ => i3 i) (ha.const_mul _),
      integral_finsetSum _ fun i _ => i3 i, integral_const_mul]
  have hint2 : |∫ ω, G' ω * (a ω - a' ω) ∂P| ≤ M * ∫ ω, |a ω - a' ω| ∂P := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono (hG'aa.abs) (i5.const_mul _) fun ω => ?_
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right (hG'b ω) (abs_nonneg _)
  have hcs : (∑ i, |c i - c' i|) ≤ (1 / z) * (((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
      ∑ i, ∫ ω, |V' i ω| * |a ω - a' ω| ∂P)) := by
    calc (∑ i, |c i - c' i|) ≤ ∑ i, (1 / z) * ((∫ ω, |V i ω - V' i ω| * a ω ∂P) +
          ∫ ω, |V' i ω| * |a ω - a' ω| ∂P) := Finset.sum_le_sum fun i _ => hcd i
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hmass : 0 ≤ ∫ ω, a ω ∂P := integral_nonneg ha0
  -- difference
  have hdiff : q08gl_Phi P F a V z - q08gl_Phi P F a' V' z =
      (1 / z) * (∫ ω, (G ω - G' ω) * a ω ∂P + ∫ ω, G' ω * (a ω - a' ω) ∂P) := by
    have hGG : Integrable (fun ω => (G ω - G' ω) * a ω) P :=
      (hGa.sub hG'a).congr (Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)
    rw [q08gl_Phi_eq, q08gl_Phi_eq, ← mul_sub, ← integral_sub hGa hG'a', ← integral_add hGG hG'aa]
    congr 2
    funext ω
    ring
  have hA : |∫ ω, (G ω - G' ω) * a ω ∂P| ≤ ∫ ω, |G ω - G' ω| * a ω ∂P := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_)))
    simp [abs_mul, abs_of_nonneg (ha0 ω)]
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / z)]
  have hsum : |∫ ω, (G ω - G' ω) * a ω ∂P + ∫ ω, G' ω * (a ω - a' ω) ∂P| ≤
      K * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
        (1 / z) * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
          ∑ i, ∫ ω, |V' i ω| * |a ω - a' ω| ∂P) * ∫ ω, a ω ∂P) + M * ∫ ω, |a ω - a' ω| ∂P := by
    refine (abs_add_le _ _).trans (add_le_add (hA.trans (hint1.trans ?_)) hint2)
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hK0
    calc (∑ i, |c i - c' i|) * ∫ ω, a ω ∂P ≤ ((1 / z) * ((∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P) +
          ∑ i, ∫ ω, |V' i ω| * |a ω - a' ω| ∂P)) * ∫ ω, a ω ∂P := mul_le_mul_of_nonneg_right hcs hmass
      _ = _ := by ring
  calc 1 / z * |∫ ω, (G ω - G' ω) * a ω ∂P + ∫ ω, G' ω * (a ω - a' ω) ∂P| ≤ 1 / z * _ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Stability of the tilted functional under a change of the normalising constant. -/
theorem q08gl_ST_z (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (a : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha : Integrable a P)
    (V : ι → Ω → ℝ) (hV : ∀ i, Measurable (V i)) (z z' : ℝ) (hz : 0 < z) (hz' : 0 < z') :
    |q08gl_Phi P F a V z - q08gl_Phi P F a V z'| ≤
      |1 / z - 1 / z'| * (M * ∫ ω, a ω ∂P +
        (K / z') * (∑ i, |∫ ω, V i ω * a ω ∂P|) * ∫ ω, a ω ∂P) := by
  set c : ι → ℝ := q08gl_c P a V z with hc
  set c' : ι → ℝ := q08gl_c P a V z' with hc'
  set G : Ω → ℝ := fun ω => F (fun i => V i ω - c i) with hG
  set G' : Ω → ℝ := fun ω => F (fun i => V i ω - c' i) with hG'
  have hGm : Measurable G := hFc.measurable.comp (measurable_pi_iff.2 fun i => (hV i).sub_const _)
  have hG'm : Measurable G' := hFc.measurable.comp (measurable_pi_iff.2 fun i => (hV i).sub_const _)
  have hGb : ∀ ω, |G ω| ≤ M := fun ω => hM _
  have hGa : Integrable (fun ω => G ω * a ω) P :=
    ha.bdd_mul hGm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hGb ω)
  have hG'a : Integrable (fun ω => G' ω * a ω) P :=
    ha.bdd_mul hG'm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM _)
  have hGG : Integrable (fun ω => |G ω - G' ω| * a ω) P := by
    refine ((hGa.sub hG'a).abs).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, ← sub_mul, abs_mul, abs_of_nonneg (ha0 ω)]
  have hcd : ∀ i, |c i - c' i| = |1 / z - 1 / z'| * |∫ ω, V i ω * a ω ∂P| := by
    intro i
    simp only [hc, hc', q08gl_c]
    rw [← mul_sub_right_distrib, abs_mul]
  have hpt : ∀ ω, |G ω - G' ω| * a ω ≤ K * ((∑ i, |c i - c' i|) * a ω) := by
    intro ω
    have h := hF (fun i => V i ω - c i) (fun i => V i ω - c' i)
    have h' : ∑ i, |(V i ω - c i) - (V i ω - c' i)| = ∑ i, |c i - c' i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (V i ω - c i) - (V i ω - c' i) = -(c i - c' i) by ring, abs_neg]
    rw [h'] at h
    calc |G ω - G' ω| * a ω ≤ (K * ∑ i, |c i - c' i|) * a ω := mul_le_mul_of_nonneg_right h (ha0 ω)
      _ = _ := by ring
  have hint : ∫ ω, |G ω - G' ω| * a ω ∂P ≤ K * ((∑ i, |c i - c' i|) * ∫ ω, a ω ∂P) := by
    have hI : Integrable (fun ω => K * ((∑ i, |c i - c' i|) * a ω)) P := (ha.const_mul _).const_mul _
    refine (integral_mono hGG hI hpt).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul]
  have hmass : 0 ≤ ∫ ω, a ω ∂P := integral_nonneg ha0
  have hGint : |∫ ω, G ω * a ω ∂P| ≤ M * ∫ ω, a ω ∂P := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono hGa.abs (ha.const_mul _) fun ω => ?_
    simp only [abs_mul, abs_of_nonneg (ha0 ω)]
    exact mul_le_mul_of_nonneg_right (hGb ω) (ha0 ω)
  have hdiff : q08gl_Phi P F a V z - q08gl_Phi P F a V z' =
      (1 / z - 1 / z') * ∫ ω, G ω * a ω ∂P + (1 / z') * ∫ ω, (G ω - G' ω) * a ω ∂P := by
    rw [q08gl_Phi_eq, q08gl_Phi_eq]
    have : ∫ ω, (G ω - G' ω) * a ω ∂P = ∫ ω, G ω * a ω ∂P - ∫ ω, G' ω * a ω ∂P := by
      rw [← integral_sub hGa hG'a]
      congr 1; funext ω; ring
    rw [this]
    ring
  have hA : |∫ ω, (G ω - G' ω) * a ω ∂P| ≤ ∫ ω, |G ω - G' ω| * a ω ∂P := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_)))
    simp [abs_mul, abs_of_nonneg (ha0 ω)]
  have hsc : (∑ i, |c i - c' i|) = |1 / z - 1 / z'| * ∑ i, |∫ ω, V i ω * a ω ∂P| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hcd i
  rw [hdiff]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / z')]
  calc |1 / z - 1 / z'| * |∫ ω, G ω * a ω ∂P| + 1 / z' * |∫ ω, (G ω - G' ω) * a ω ∂P|
      ≤ |1 / z - 1 / z'| * (M * ∫ ω, a ω ∂P) + 1 / z' * (K * ((∑ i, |c i - c' i|) * ∫ ω, a ω ∂P)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hGint (abs_nonneg _)) ?_
        exact mul_le_mul_of_nonneg_left (hA.trans hint) (by positivity)
    _ = _ := by rw [hsc]; ring

end ST

/-! ### Cauchy-Schwarz -/

theorem q08gl_cs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, |f ω| * |g ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hfa : MemLp (fun ω => |f ω|) 2 P := hf.abs
  have hga : MemLp (fun ω => |g ω|) 2 P := hg.abs
  have hI : Integrable (fun ω => |f ω| * |g ω|) P := hfa.integrable_mul hga
  have hF : Integrable (fun ω => |f ω| ^ 2) P := hfa.integrable_sq
  have hG : Integrable (fun ω => |g ω| ^ 2) P := hga.integrable_sq
  set Fv := ∫ ω, |f ω| ^ 2 ∂P with hFv
  set Gv := ∫ ω, |g ω| ^ 2 ∂P with hGv
  set Iv := ∫ ω, |f ω| * |g ω| ∂P with hIv
  have hq : ∀ t : ℝ, 0 ≤ Fv * (t * t) + (-2 * Iv) * t + Gv := by
    intro t
    have h0 : 0 ≤ ∫ ω, (t * |f ω| - |g ω|) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have e : ∫ ω, (t * |f ω| - |g ω|) ^ 2 ∂P = Fv * (t * t) + (-2 * Iv) * t + Gv := by
      have : ∀ ω, (t * |f ω| - |g ω|) ^ 2 = (t * t) * |f ω| ^ 2 + (-2 * t) * (|f ω| * |g ω|) + |g ω| ^ 2 := by
        intro ω; ring
      simp_rw [this]
      have h1 : Integrable (fun ω => (t * t) * |f ω| ^ 2) P := hF.const_mul _
      have h2 : Integrable (fun ω => (-2 * t) * (|f ω| * |g ω|)) P := hI.const_mul _
      have h12 : Integrable (fun ω => (t * t) * |f ω| ^ 2 + (-2 * t) * (|f ω| * |g ω|)) P := h1.add h2
      rw [integral_add h12 hG, integral_add h1 h2, integral_const_mul, integral_const_mul]
      ring
    rwa [e] at h0
  have hd := discrim_le_zero hq
  have hI2 : Iv ^ 2 ≤ Fv * Gv := by unfold discrim at hd; nlinarith
  have e1 : ∫ ω, |f ω| ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P := by simp_rw [sq_abs]
  have e2 : ∫ ω, |g ω| ^ 2 ∂P = ∫ ω, g ω ^ 2 ∂P := by simp_rw [sq_abs]
  rw [← e1, ← e2, ← Real.sqrt_mul (integral_nonneg fun ω => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le hI2

/-! ### Consequences of the stability estimates in `L²` form -/

section L2form

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : (ι → ℝ) → ℝ) (M K : ℝ)

theorem q08gl_int_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

theorem q08gl_integral_le_sqrt {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have := q08gl_cs P f (fun _ => 1) hf (memLp_const 1)
  simpa using this

/-- Change of weight (in `L¹` and `L²`). -/
theorem q08gl_WC (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (a a' : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha : MemLp a 2 P) (ha' : MemLp a' 2 P)
    (V : ι → Ω → ℝ) (hVm : ∀ i, Measurable (V i)) (hV : ∀ i, MemLp (V i) 2 P) (B₁ τ₁ τ₂ : ℝ)
    (hB : ∀ i, Real.sqrt (∫ ω, V i ω ^ 2 ∂P) ≤ B₁)
    (hτ₁ : ∫ ω, |a ω - a' ω| ∂P ≤ τ₁) (hτ₂ : ∫ ω, (a ω - a' ω) ^ 2 ∂P ≤ τ₂) (z : ℝ) (hz : 0 < z) :
    |q08gl_Phi P F a V z - q08gl_Phi P F a' V z| ≤
      (K / z) * ((1 / z) * (Fintype.card ι * B₁ * Real.sqrt τ₂) * ∫ ω, a ω ∂P) + (M / z) * τ₁ := by
  have h1 : ∀ i, Integrable (fun ω => V i ω * a ω) P := fun i => q08gl_int_mul P (hV i) ha
  have h2 : ∀ i, Integrable (fun ω => V i ω * a' ω) P := fun i => q08gl_int_mul P (hV i) ha'
  have h3 : ∀ i, Integrable (fun ω => (V i ω - V i ω) * a ω) P := fun i => by simp
  have h4 : ∀ i, Integrable (fun ω => V i ω * (a ω - a' ω)) P := fun i =>
    q08gl_int_mul P (hV i) (ha.sub ha')
  have := q08gl_ST_a P F M K hFc hM hK0 hF a a' ha0 (ha.integrable one_le_two) (ha'.integrable one_le_two)
    V V hVm hVm z hz h1 h2 h3 h4
  simp only [sub_self, abs_zero, zero_mul, integral_zero, Finset.sum_const_zero, zero_add] at this
  refine this.trans ?_
  have hα : ∑ i, ∫ ω, |V i ω| * |a ω - a' ω| ∂P ≤ Fintype.card ι * B₁ * Real.sqrt τ₂ := by
    calc ∑ i, ∫ ω, |V i ω| * |a ω - a' ω| ∂P ≤ ∑ _i : ι, B₁ * Real.sqrt τ₂ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (q08gl_cs P (V i) (fun ω => a ω - a' ω) (hV i) (ha.sub ha')).trans ?_
          exact mul_le_mul (hB i) (Real.sqrt_le_sqrt hτ₂) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hB i))
      _ = _ := by simp [mul_assoc]
  have hmass : 0 ≤ ∫ ω, a ω ∂P := integral_nonneg ha0
  have hc : 0 ≤ K / z := by positivity
  have e1 : (M / z) * ∫ ω, |a ω - a' ω| ∂P ≤ (M / z) * τ₁ := by
    refine mul_le_mul_of_nonneg_left hτ₁ ?_
    have : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0))
    positivity
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ hc) e1
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by positivity)) hmass

/-- Change of statistic in `L²`. -/
theorem q08gl_VC (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (a : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha : MemLp a 2 P) (A : ℝ) (hA : ∫ ω, a ω ^ 2 ∂P ≤ A)
    (V V' : ι → Ω → ℝ) (hVm : ∀ i, Measurable (V i)) (hV'm : ∀ i, Measurable (V' i))
    (hV : ∀ i, MemLp (V i) 2 P) (hV' : ∀ i, MemLp (V' i) 2 P) (θ : ℝ)
    (hθ : ∀ i, Real.sqrt (∫ ω, (V i ω - V' i ω) ^ 2 ∂P) ≤ θ) (z : ℝ) (hz : 0 < z) :
    |q08gl_Phi P F a V z - q08gl_Phi P F a V' z| ≤
      (K / z) * (Fintype.card ι * θ * Real.sqrt A +
        (1 / z) * (Fintype.card ι * θ * Real.sqrt A) * ∫ ω, a ω ∂P) := by
  have h1 : ∀ i, Integrable (fun ω => V i ω * a ω) P := fun i => q08gl_int_mul P (hV i) ha
  have h2 : ∀ i, Integrable (fun ω => V' i ω * a ω) P := fun i => q08gl_int_mul P (hV' i) ha
  have h3 : ∀ i, Integrable (fun ω => (V i ω - V' i ω) * a ω) P := fun i =>
    q08gl_int_mul P ((hV i).sub (hV' i)) ha
  have h4 : ∀ i, Integrable (fun ω => V' i ω * (a ω - a ω)) P := fun i => by simp
  have := q08gl_ST_a P F M K hFc hM hK0 hF a a ha0 (ha.integrable one_le_two) (ha.integrable one_le_two)
    V V' hVm hV'm z hz h1 h2 h3 h4
  simp only [sub_self, abs_zero, mul_zero, integral_zero, Finset.sum_const_zero, add_zero, zero_mul] at this
  refine this.trans ?_
  have hα : ∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P ≤ Fintype.card ι * θ * Real.sqrt A := by
    calc ∑ i, ∫ ω, |V i ω - V' i ω| * a ω ∂P ≤ ∑ _i : ι, θ * Real.sqrt A := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := q08gl_cs P (fun ω => V i ω - V' i ω) a ((hV i).sub (hV' i)) ha
          refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_))) (this.trans ?_)
          · simp [abs_of_nonneg (ha0 ω)]
          · exact mul_le_mul (hθ i) (Real.sqrt_le_sqrt hA) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hθ i))
      _ = _ := by simp [mul_assoc]
  have hmass : 0 ≤ ∫ ω, a ω ∂P := integral_nonneg ha0
  have hc : 0 ≤ K / z := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine add_le_add hα ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by positivity)) hmass

end L2form

/-! ### Truncation of the weights -/

section Trunc

theorem q08gl_exp_diff (s t : ℝ) (hst : t ≤ s) : Real.exp s - Real.exp t ≤ Real.exp s * (s - t) := by
  have h := Real.add_one_le_exp (t - s)
  have e : Real.exp t = Real.exp s * Real.exp (t - s) := by rw [← Real.exp_add]; ring_nf
  have hs := Real.exp_pos s
  nlinarith [mul_le_mul_of_nonneg_left h hs.le]

theorem q08gl_exp_abs_diff (s t : ℝ) (R : ℝ) (hs : Real.exp s ≤ R) (ht : Real.exp t ≤ R) :
    |Real.exp s - Real.exp t| ≤ R * |s - t| := by
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h]), abs_of_nonneg (by linarith)]
    exact (q08gl_exp_diff s t h).trans (mul_le_mul_of_nonneg_right hs (by linarith))
  · rw [abs_sub_comm, abs_sub_comm s t, abs_of_nonneg (by linarith [Real.exp_le_exp.2 h]),
      abs_of_nonneg (by linarith)]
    exact (q08gl_exp_diff t s h).trans (mul_le_mul_of_nonneg_right ht (by linarith))

/-- The truncated exponential weight is `βR`-Lipschitz in the exponent. -/
theorem q08gl_trunc_exp_lip (β R x y : ℝ) (hβ : 0 ≤ β) (hR : 0 < R) :
    |min (Real.exp (-β * x)) R - min (Real.exp (-β * y)) R| ≤ β * R * |x - y| := by
  set r := Real.log R with hr
  have hRr : R = Real.exp r := (Real.exp_log hR).symm
  have e : ∀ z : ℝ, min (Real.exp (-β * z)) R = Real.exp (min (-β * z) r) := by
    intro z
    rw [hRr]
    rcases le_total (-β * z) r with h | h
    · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.2 h)]
    · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.2 h)]
  rw [e x, e y]
  have h1 : Real.exp (min (-β * x) r) ≤ R := by rw [hRr]; exact Real.exp_le_exp.2 (min_le_right _ _)
  have h2 : Real.exp (min (-β * y) r) ≤ R := by rw [hRr]; exact Real.exp_le_exp.2 (min_le_right _ _)
  refine (q08gl_exp_abs_diff _ _ R h1 h2).trans ?_
  have : |min (-β * x) r - min (-β * y) r| ≤ |(-β * x) - (-β * y)| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (by simp)
  calc R * |min (-β * x) r - min (-β * y) r| ≤ R * |(-β * x) - (-β * y)| :=
        mul_le_mul_of_nonneg_left this hR.le
    _ = β * R * |x - y| := by
        rw [show (-β * x) - (-β * y) = -(β * (x - y)) by ring, abs_neg, abs_mul, abs_of_nonneg hβ]; ring

/-- `(a - R)₊ ≤ a² / R`. -/
theorem q08gl_tail1 (a R : ℝ) (ha : 0 ≤ a) (hR : 0 < R) : a - min a R ≤ a ^ 2 / R := by
  rw [le_div_iff₀ hR]
  rcases le_total a R with h | h
  · rw [min_eq_left h]; nlinarith [sq_nonneg a]
  · rw [min_eq_right h]; nlinarith [sq_nonneg (a - R)]

/-- `(a - R)₊² ≤ a³ / R`. -/
theorem q08gl_tail2 (a R : ℝ) (ha : 0 ≤ a) (hR : 0 < R) : (a - min a R) ^ 2 ≤ a ^ 3 / R := by
  rw [le_div_iff₀ hR]
  rcases le_total a R with h | h
  · rw [min_eq_left h]; simp; positivity
  · rw [min_eq_right h]
    have h1 : 0 ≤ a - R := by linarith
    have h2 : a - R ≤ a := by linarith
    have h3 : (a - R) ^ 2 ≤ a ^ 2 := by nlinarith
    have h4 : R * (a - R) ^ 2 ≤ a * (a - R) ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
    have h5 : a * (a - R) ^ 2 ≤ a * a ^ 2 := mul_le_mul_of_nonneg_left h3 ha
    nlinarith

end Trunc

end HRS.Q08

end
