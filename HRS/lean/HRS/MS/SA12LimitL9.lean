import HRS.MS.SA12LimitL1
import HRS.MS.SA12LimitL2

/-!
# S.A.12 L9: passing the weak equation to the limit
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MS.UniqM1

variable {d : ℕ}

theorem sa12x_cellL2Sum_add_le {p q : Euc d → ℝ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) :
    cellL2Sum (fun x => p x + q x) ≤ cellL2Sum p + cellL2Sum q := by
  have hpq : AEStronglyMeasurable (fun x => p x + q x) volume := hp.add hq
  rw [sa12x_cellL2Sum_eq hpq, sa12x_cellL2Sum_eq hp, sa12x_cellL2Sum_eq hq,
    ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun z => sa12x_cn_add_le p q z

theorem sa12x_cellL2Sum_sub_comm (p q : Euc d → ℝ) :
    cellL2Sum (fun x => p x - q x) = cellL2Sum (fun x => q x - p x) := by
  have h2 : ∀ x, (p x - q x) ^ 2 = (q x - p x) ^ 2 := fun x => by ring
  unfold cellL2Sum
  simp_rw [h2]

theorem sa12x_pair (hd : 1 ≤ d) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {B : ℝ} (hB : 0 ≤ B)
    {u g : Euc d → ℝ} (hu : ulocNormE 0 χ u ≤ ENNReal.ofReal B) (hg : AEStronglyMeasurable g volume)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgδ : cellL2Sum g ≤ ENNReal.ofReal δ) :
    Integrable (fun x => u x * g x) ∧ |∫ x, u x * g x| ≤ B * δ := by
  have hfin : cellL2Sum g < ⊤ := hgδ.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨h1, h2⟩ := cell_pair_bound hd χ hχ B hB u g hu hg hfin
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hδ hgδ) hB)⟩

/-- The fixed-time convergence `∫ Fₙ aₙ → ∫ G a`. -/
theorem sa12x_conv_tendsto (hd : 1 ≤ d) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {B : ℝ} (hB : 0 ≤ B)
    (Fn : ℕ → Euc d → ℝ) (G : Euc d → ℝ)
    (hFn : ∀ n, ulocNormE 0 χ (Fn n) ≤ ENNReal.ofReal B) (hG : ulocNormE 0 χ G ≤ ENNReal.ofReal B)
    (hF : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, Fn n x * ψ x) atTop (𝓝 (∫ x, G x * ψ x)))
    (a : Euc d → ℝ) (an : ℕ → Euc d → ℝ) (ha : AEStronglyMeasurable a volume)
    (han : ∀ n, AEStronglyMeasurable (an n) volume) (haf : cellL2Sum a < ⊤)
    (hop : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, cellL2Sum (fun x => an n x - a x) ≤ ENNReal.ofReal δ) :
    Tendsto (fun n => ∫ x, Fn n x * an n x) atTop (𝓝 (∫ x, G x * a x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (8 * (B + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨ψ', hψ', hψ'δ⟩ := cell_test_density hd a ha haf δ hδ
  have hψm : AEStronglyMeasurable ψ' volume := hψ'.1.continuous.aestronglyMeasurable
  have hamψ : AEStronglyMeasurable (fun x => a x - ψ' x) volume := ha.sub hψm
  have hnamψ : AEStronglyMeasurable (fun x => -(a x - ψ' x)) volume := hamψ.neg
  have hψa : AEStronglyMeasurable (fun x => ψ' x - a x) volume := hψm.sub ha
  have hψ'f : cellL2Sum ψ' < ⊤ := by
    have h1 : ψ' = fun x => a x + (-(a x - ψ' x)) := by funext x; ring
    have h2 := sa12x_cellL2Sum_add_le ha hnamψ
    have h3 : cellL2Sum (fun x => -(a x - ψ' x)) = cellL2Sum (fun x => a x - ψ' x) := by
      unfold cellL2Sum; simp only [neg_sq]
    rw [h3] at h2
    rw [h1]
    exact h2.trans_lt (ENNReal.add_lt_top.2 ⟨haf, hψ'δ.trans_lt ENNReal.ofReal_lt_top⟩)
  have hψ'δ' : cellL2Sum (fun x => ψ' x - a x) ≤ ENNReal.ofReal δ := by
    rw [sa12x_cellL2Sum_sub_comm]; exact hψ'δ
  have e2 : ∀ᶠ n in atTop, dist (∫ x, Fn n x * ψ' x) (∫ x, G x * ψ' x) < ε / 4 :=
    Metric.tendsto_nhds.1 (hF ψ' hψ') _ (by positivity)
  filter_upwards [hop δ hδ, e2] with n hn1 hn2
  have hdn : AEStronglyMeasurable (fun x => an n x - a x) volume := (han n).sub ha
  obtain ⟨i1, b1⟩ := sa12x_pair hd hχ hB (hFn n) hdn hδ.le hn1
  obtain ⟨i2, -⟩ := cell_pair_bound hd χ hχ B hB (Fn n) a (hFn n) ha haf
  obtain ⟨i3, -⟩ := cell_pair_bound hd χ hχ B hB (Fn n) ψ' (hFn n) hψm hψ'f
  obtain ⟨i4, b4⟩ := sa12x_pair hd hχ hB (hFn n) hamψ hδ.le hψ'δ
  obtain ⟨i5, -⟩ := cell_pair_bound hd χ hχ B hB G a hG ha haf
  obtain ⟨i6, -⟩ := cell_pair_bound hd χ hχ B hB G ψ' hG hψm hψ'f
  obtain ⟨i7, b7⟩ := sa12x_pair hd hχ hB hG hψa hδ.le hψ'δ'
  have k1 : ∫ x, Fn n x * an n x = (∫ x, Fn n x * (an n x - a x)) + ∫ x, Fn n x * a x := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have k2 : ∫ x, Fn n x * a x = (∫ x, Fn n x * (a x - ψ' x)) + ∫ x, Fn n x * ψ' x := by
    rw [← integral_add i4 i3]; congr 1; funext x; ring
  have k3 : ∫ x, G x * a x = (∫ x, G x * ψ' x) - ∫ x, G x * (ψ' x - a x) := by
    rw [← integral_sub i6 i7]; congr 1; funext x; ring
  rw [Real.dist_eq] at hn2 ⊢
  rw [abs_lt] at hn2
  rw [abs_lt]
  have b1' := abs_le.1 b1
  have b4' := abs_le.1 b4
  have b7' := abs_le.1 b7
  have hBδ : B * δ ≤ ε / 8 := by
    rw [hδdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [k1, k2, k3]
  constructor <;> linarith [b1'.1, b1'.2, b4'.1, b4'.2, b7'.1, b7'.2, hn2.1, hn2.2]

-- BEGIN SA12.L9
theorem weak_limit_passage (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (B t : ℝ) (ht : 0 < t)
    (A : ℝ → (Euc d → ℝ) → (Euc d → ℝ)) (An : ℕ → ℝ → (Euc d → ℝ) → (Euc d → ℝ))
    (Fn : ℕ → ℝ → Euc d → ℝ) (φn : ℕ → Euc d → ℝ) (G : ℝ → Euc d → ℝ) (φ : Euc d → ℝ)
    (hAmeas : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      AEStronglyMeasurable (A σ ψ) volume ∧ ∀ n, AEStronglyMeasurable (An n σ ψ) volume)
    (hφloc : ∀ R : ℝ, 0 < R → MemLp φ 2 (volume.restrict (Metric.ball 0 R)))
    (hweak : ∀ n, IsWeakSol (An n) t (φn n) (Fn n))
    (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fn n τ) ≤ ENNReal.ofReal B)
    (hGB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B)
    (hF : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ x, Fn n τ x * ψ x) atTop (𝓝 (∫ x, G τ x * ψ x)))
    (hφ : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → Tendsto (fun n => ∫ x, φn n x * ψ x) atTop (𝓝 (∫ x, φ x * ψ x)))
    (hop : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => An n σ ψ x - A σ ψ x) ≤ ENNReal.ofReal δ)
    (hopb : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (A σ ψ) ≤ ENNReal.ofReal K) :
    IsWeakSol A t φ G := by
  set B' : ℝ := max B 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hle : ENNReal.ofReal B ≤ ENNReal.ofReal B' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hFn : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fn n τ) ≤ ENNReal.ofReal B' :=
    fun n τ hτ => (hB n τ hτ).trans hle
  have hG' : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B' :=
    fun τ hτ => (hGB τ hτ).trans hle
  -- a uniform bound on the limit operator, with a nonnegative constant
  have hK : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (A σ ψ) ≤ ENNReal.ofReal K := by
    intro ψ hψ
    obtain ⟨K, hK⟩ := hopb ψ hψ
    exact ⟨max K 0, le_max_right _ _, fun σ hσ =>
      (hK σ hσ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ x, Fn n σ x * An n σ ψ x) atTop (𝓝 (∫ x, G σ x * A σ ψ x)) := by
    intro ψ hψ σ hσ
    obtain ⟨K, -, hK⟩ := hK ψ hψ
    obtain ⟨hA1, hA2⟩ := hAmeas ψ hψ σ hσ
    exact sa12x_conv_tendsto hd hχ hB0 (fun n => Fn n σ) (G σ) (fun n => hFn n σ hσ) (hG' σ hσ)
      (fun ψ' hψ' => hF ψ' hψ' σ hσ) (A σ ψ) (fun n => An n σ ψ) hA1 hA2
      ((hK σ hσ).trans_lt ENNReal.ofReal_lt_top)
      (fun δ hδ => (hop ψ hψ δ hδ).mono fun n hn => hn σ hσ)
  have hpairG : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t, ∃ K : ℝ, 0 ≤ K ∧
      Integrable (fun x => G σ x * A σ ψ x) ∧ |∫ x, G σ x * A σ ψ x| ≤ B' * K := by
    intro ψ hψ σ hσ
    obtain ⟨K, hK0, hK⟩ := hK ψ hψ
    obtain ⟨i, b⟩ := sa12x_pair hd hχ hB0 (hG' σ hσ) (hAmeas ψ hψ σ hσ).1 hK0 (hK σ hσ)
    exact ⟨K, hK0, i, b⟩
  have hmeasn : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ n,
      AEStronglyMeasurable (fun σ => ∫ x, Fn n σ x * An n σ ψ x) (volume.restrict (Icc (0 : ℝ) t)) :=
    fun ψ hψ n => ((hweak n).integrable_σ ψ hψ).aestronglyMeasurable
  have hmeas : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      AEStronglyMeasurable (fun σ => ∫ x, G σ x * A σ ψ x) (volume.restrict (Icc (0 : ℝ) t)) := by
    intro ψ hψ
    exact aestronglyMeasurable_of_tendsto_ae atTop (hmeasn ψ hψ)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hconv ψ hψ σ hσ))
  refine ⟨fun ψ hψ σ hσ => ?_, fun ψ hψ => ?_, fun ψ hψ τ hτ => ?_⟩
  · have hfm := locMass_of_ulocNormE hχ hB0 (hG' σ hσ)
    obtain ⟨K, -, i, -⟩ := hpairG ψ hψ σ hσ
    exact ⟨hfm.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hψ.1.continuous hψ.2, i⟩
  · obtain ⟨K, hK0, hK⟩ := hK ψ hψ
    refine Integrable.of_bound (μ := volume.restrict (Icc (0 : ℝ) t)) (hmeas ψ hψ) (B' * K) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    obtain ⟨-, b⟩ := sa12x_pair hd hχ hB0 (hG' σ hσ) (hAmeas ψ hψ σ hσ).1 hK0 (hK σ hσ)
    rwa [Real.norm_eq_abs]
  · have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
    obtain ⟨K, hK0, hK⟩ := hK ψ hψ
    have hdom : Tendsto (fun n => ∫ σ in Icc (0 : ℝ) τ, ∫ x, Fn n σ x * An n σ ψ x) atTop
        (𝓝 (∫ σ in Icc (0 : ℝ) τ, ∫ x, G σ x * A σ ψ x)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => B' * (K + 1)) ?_ ?_
        (integrable_const _) ?_
      · exact Filter.Eventually.of_forall fun n =>
          (hmeasn ψ hψ n).mono_measure (Measure.restrict_mono hsub le_rfl)
      · filter_upwards [hop ψ hψ 1 one_pos] with n hn
        refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
        have hσ' := hsub hσ
        obtain ⟨hA1, hA2⟩ := hAmeas ψ hψ σ hσ'
        have hdm : AEStronglyMeasurable (fun x => An n σ ψ x - A σ ψ x) volume := (hA2 n).sub hA1
        have h1 := sa12x_cellL2Sum_add_le hA1 hdm
        have h2 : (fun x => A σ ψ x + (An n σ ψ x - A σ ψ x)) = An n σ ψ := by funext x; ring
        rw [h2] at h1
        have h3 : cellL2Sum (An n σ ψ) ≤ ENNReal.ofReal (K + 1) := by
          refine h1.trans ?_
          rw [ENNReal.ofReal_add hK0 zero_le_one]
          exact add_le_add (hK σ hσ') (hn σ hσ')
        obtain ⟨-, b⟩ := sa12x_pair hd hχ hB0 (hFn n σ hσ') (hA2 n) (by linarith) h3
        rwa [Real.norm_eq_abs]
      · exact (ae_restrict_iff' measurableSet_Icc).2
          (Filter.Eventually.of_forall fun σ hσ => hconv ψ hψ σ (hsub hσ))
    refine tendsto_nhds_unique (hF ψ hψ τ hτ) ?_
    refine ((hφ ψ hψ).add hdom).congr fun n => ?_
    exact ((hweak n).eq ψ hψ τ hτ).symm
-- END SA12.L9

end HRS.MH.AdjointRd.Phase2SA12Limit
