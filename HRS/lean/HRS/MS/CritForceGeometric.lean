import HRS.MS.CritForceDefs

/-!
# S8.2.02: geometric root-mean-square summation of the old blocks
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- Minkowski for the `L²` functional on `ℝ≥0∞`-valued functions. -/
lemma s82_minkowski {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    (∫⁻ ζ, (f ζ + g ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ζ, (f ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) + (∫⁻ ζ, (g ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2) hf hg (by norm_num)
  simpa only [ENNReal.rpow_two, Pi.add_apply] using h

lemma s82_geom_finite {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (R : Ω → ℝ≥0∞) (A : ℕ → Ω → ℝ≥0∞) (B q : ℝ)
    (hB : 0 ≤ B) (hq0 : 0 < q) (hq1 : q < 1)
    (hRm : AEMeasurable R P) (hAm : ∀ j, AEMeasurable (A j) P)
    (hR : (∫⁻ ζ, (R ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal B)
    (hA : ∀ j, (∫⁻ ζ, (A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * q ^ j)) (n : ℕ) :
    (∫⁻ ζ, (R ζ + ∑ j ∈ Finset.range n, A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * (1 + (1 - q)⁻¹)) := by
  have key : ∀ n : ℕ, (∫⁻ ζ, (R ζ + ∑ j ∈ Finset.range n, A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal B + ∑ j ∈ Finset.range n, ENNReal.ofReal (B * q ^ j) := by
    intro n
    induction n with
    | zero => simpa using hR
    | succ n ih =>
      have hm : AEMeasurable (fun ζ => R ζ + ∑ j ∈ Finset.range n, A j ζ) P :=
        hRm.add (Finset.aemeasurable_fun_sum _ fun j _ => hAm j)
      have h1 := s82_minkowski P _ (A n) hm (hAm n)
      simp only [Finset.sum_range_succ, ← add_assoc]
      exact h1.trans (add_le_add ih (hA n))
  refine (key n).trans ?_
  have hgeo : ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ :=
    sum_le_hasSum _ (fun j _ => by positivity) (hasSum_geometric_of_lt_one hq0.le hq1)
  have hinv : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity), ← Finset.mul_sum,
    ← ENNReal.ofReal_add hB (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem s82_geometric_L2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ≥0∞) (A : ℕ → Ω → ℝ≥0∞) (B q : ℝ)
    (hB : 0 ≤ B) (hq0 : 0 < q) (hq1 : q < 1)
    (hRm : AEMeasurable R P) (hAm : ∀ j, AEMeasurable (A j) P)
    (hR : (∫⁻ ζ, (R ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal B)
    (hA : ∀ j, (∫⁻ ζ, (A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * q ^ j)) :
    AEMeasurable (fun ζ => R ζ + ∑' j, A j ζ) P ∧
    (∫⁻ ζ, (R ζ + ∑' j, A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * (1 + (1 - q)⁻¹)) := by
  refine ⟨hRm.add (AEMeasurable.tsum hAm), ?_⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = ENNReal.ofReal (B * (1 + (1 - q)⁻¹)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Ω → ℝ≥0∞,
      ∀ n ζ, G n ζ = (R ζ + ∑ j ∈ Finset.range n, A j ζ) ^ 2 := ⟨_, fun _ _ => rfl⟩
  have hGm : ∀ n, AEMeasurable (G n) P := by
    intro n
    have : G n = fun ζ => (R ζ + ∑ j ∈ Finset.range n, A j ζ) ^ 2 := funext (hG n)
    rw [this]
    exact (hRm.add (Finset.aemeasurable_fun_sum _ fun j _ => hAm j)).pow_const 2
  have hGmono : ∀ ζ, Monotone fun n => G n ζ := by
    intro ζ n m hnm
    show G n ζ ≤ G m ζ
    rw [hG, hG]
    exact pow_le_pow_left' (add_le_add le_rfl
      (Finset.sum_le_sum_of_subset (Finset.range_mono hnm))) 2
  have hsup : ∀ ζ, (R ζ + ∑' j, A j ζ) ^ 2 = ⨆ n, G n ζ := by
    intro ζ
    have h1 : R ζ + ∑' j, A j ζ = ⨆ n : ℕ, (R ζ + ∑ j ∈ Finset.range n, A j ζ) := by
      rw [ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
    simp_rw [hG]
    rw [h1]
    exact Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ 2)
      (ENNReal.continuous_pow 2).continuousAt (fun x y hxy => pow_le_pow_left' hxy 2) (by simp)
  have hint : ∫⁻ ζ, (R ζ + ∑' j, A j ζ) ^ 2 ∂P = ⨆ n, ∫⁻ ζ, G n ζ ∂P := by
    simp_rw [hsup]
    exact lintegral_iSup' hGm (Filter.Eventually.of_forall hGmono)
  have hbd : ∀ n, ∫⁻ ζ, G n ζ ∂P ≤ K ^ 2 := by
    intro n
    have h := s82_geom_finite P R A B q hB hq0 hq1 hRm hAm hR hA n
    rw [← hK] at h
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul] at h2
    norm_num at h2
    simpa [hG, ENNReal.rpow_two] using h2
  have hle : ∫⁻ ζ, (R ζ + ∑' j, A j ζ) ^ 2 ∂P ≤ K ^ 2 := by
    rw [hint]; exact iSup_le hbd
  rw [← hK]
  calc (∫⁻ ζ, (R ζ + ∑' j, A j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ (K ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = K := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

end HRS.MS.S82BD
