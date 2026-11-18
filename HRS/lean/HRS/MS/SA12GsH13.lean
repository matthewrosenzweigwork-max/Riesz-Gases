import HRS.MS.SA12LimitL16

/-!
# S.A.12 H13: passing the weak equation to the limit in `L²`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Global

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

/-- The fixed-time pairing of the operator sequence converges. -/
theorem sa12x_h13_pair {B : ℝ} (hB : 0 ≤ B) (Fn : ℕ → Euc d → ℝ) (G : Euc d → ℝ)
    (hFn : ∀ n, MemLp (Fn n) 2 volume ∧ eLpNorm (Fn n) 2 volume ≤ ENNReal.ofReal B)
    (hG : MemLp G 2 volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, Fn n x * ψ x) atTop (𝓝 (∫ x, G x * ψ x)))
    (a : Euc d → ℝ) (an : ℕ → Euc d → ℝ) (ha : MemLp a 2 volume) (han : ∀ n, MemLp (an n) 2 volume)
    (hop : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, eLpNorm (fun x => an n x - a x) 2 volume ≤ ENNReal.ofReal ε) :
    Tendsto (fun n => ∫ x, Fn n x * an n x) atTop (𝓝 (∫ x, G x * a x)) := by
  have hL2 : ∀ n, (eLpNorm (Fn n) 2 volume).toReal ≤ B := fun n =>
    ENNReal.toReal_le_of_le_ofReal hB (hFn n).2
  have h1 := sa12x_conv_L2 (fun n => (hFn n).1) hG hL2 hconv a ha
  rw [Metric.tendsto_nhds] at h1 ⊢
  intro ε hε
  set δ : ℝ := ε / (4 * (B + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  filter_upwards [h1 (ε / 2) (half_pos hε), hop δ hδ] with n hn1 hn2
  have hdn : MemLp (fun x => an n x - a x) 2 volume := (han n).sub ha
  have b1 := sa12x_cs (hFn n).1 hdn
  have hb1 : |∫ x, Fn n x * (an n x - a x)| ≤ B * δ := by
    refine b1.trans (mul_le_mul (ENNReal.toReal_le_of_le_ofReal hB (hFn n).2)
      (ENNReal.toReal_le_of_le_ofReal hδ.le hn2) ENNReal.toReal_nonneg hB)
  have i1 : Integrable (fun x => Fn n x * (an n x - a x)) volume := (hFn n).1.integrable_mul hdn
  have i2 : Integrable (fun x => Fn n x * a x) volume := (hFn n).1.integrable_mul ha
  have k1 : ∫ x, Fn n x * an n x = (∫ x, Fn n x * (an n x - a x)) + ∫ x, Fn n x * a x := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have hBδ : B * δ ≤ ε / 4 := by
    rw [hδdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [Real.dist_eq] at hn1 ⊢
  rw [k1]
  have b1' := abs_le.1 hb1
  rw [abs_lt] at hn1 ⊢
  constructor <;> linarith [hn1.1, hn1.2, b1'.1, b1'.2]

-- BEGIN SA12.H13
theorem l2_weak_passage (t B : ℝ) (hB : 0≤B) (φ : Euc d → ℝ) (hφ : MemLp φ 2 volume)
    (Fn : ℕ → ℝ → Euc d → ℝ) (G : ℝ → Euc d → ℝ)
    (An : ℕ → ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (A : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (hFn : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, MemLp (Fn n τ) 2 volume ∧ eLpNorm (Fn n τ) 2 volume≤ENNReal.ofReal B)
    (hG : ∀ τ ∈ Icc (0 : ℝ) t, MemLp (G τ) 2 volume ∧ eLpNorm (G τ) 2 volume≤ENNReal.ofReal B)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ x, Fn n τ x*ψ x) atTop (𝓝 (∫ x, G τ x*ψ x)))
    (hw : ∀ n, IsWeakSol (An n) t φ (Fn n))
    (hA : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      (∀ σ ∈ Icc (0 : ℝ) t, MemLp (A σ ψ) 2 volume ∧ ∀ n, MemLp (An n σ ψ) 2 volume) ∧
      (∃ K : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, eLpNorm (A σ ψ) 2 volume≤ENNReal.ofReal K ∧
        ∀ n, eLpNorm (An n σ ψ) 2 volume≤ENNReal.ofReal K) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ σ ∈ Icc (0 : ℝ) t,
        eLpNorm (fun x => An n σ ψ x-A σ ψ x) 2 volume≤ENNReal.ofReal ε) :
    IsWeakSol A t φ G := by
  have hconvA : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ x, Fn n σ x * An n σ ψ x) atTop (𝓝 (∫ x, G σ x * A σ ψ x)) := by
    intro ψ hψ σ hσ
    obtain ⟨hm, -, hop⟩ := hA ψ hψ
    exact sa12x_h13_pair hB (fun n => Fn n σ) (G σ) (fun n => hFn n σ hσ) (hG σ hσ).1
      (fun ψ' hψ' => hconv ψ' hψ' σ hσ) (A σ ψ) (fun n => An n σ ψ) (hm σ hσ).1
      (fun n => (hm σ hσ).2 n) (fun ε hε => (hop ε hε).mono fun n hn => hn σ hσ)
  have hbd : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc (0 : ℝ) t,
      Integrable (fun x => G σ x * A σ ψ x) ∧ |∫ x, G σ x * A σ ψ x| ≤ B * K := by
    intro ψ hψ
    obtain ⟨hm, ⟨K, hK⟩, -⟩ := hA ψ hψ
    refine ⟨max K 0, le_max_right _ _, fun σ hσ => ⟨(hG σ hσ).1.integrable_mul (hm σ hσ).1, ?_⟩⟩
    refine (sa12x_cs (hG σ hσ).1 (hm σ hσ).1).trans (mul_le_mul
      (ENNReal.toReal_le_of_le_ofReal hB (hG σ hσ).2) ?_ ENNReal.toReal_nonneg hB)
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((hK σ hσ).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hmeasn : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ n,
      AEStronglyMeasurable (fun σ => ∫ x, Fn n σ x * An n σ ψ x) (volume.restrict (Icc (0 : ℝ) t)) :=
    fun ψ hψ n => ((hw n).integrable_σ ψ hψ).aestronglyMeasurable
  have hmeas : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      AEStronglyMeasurable (fun σ => ∫ x, G σ x * A σ ψ x) (volume.restrict (Icc (0 : ℝ) t)) := by
    intro ψ hψ
    exact aestronglyMeasurable_of_tendsto_ae atTop (hmeasn ψ hψ)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hconvA ψ hψ σ hσ))
  refine ⟨fun ψ hψ σ hσ => ?_, fun ψ hψ => ?_, fun ψ hψ τ hτ => ?_⟩
  · have hψm : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
    obtain ⟨K, -, hK⟩ := hbd ψ hψ
    exact ⟨(hG σ hσ).1.integrable_mul hψm, (hK σ hσ).1⟩
  · obtain ⟨K, hK0, hK⟩ := hbd ψ hψ
    refine Integrable.of_bound (μ := volume.restrict (Icc (0 : ℝ) t)) (hmeas ψ hψ) (B * K) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs]; exact (hK σ hσ).2
  · have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
    obtain ⟨hm, ⟨K, hK⟩, hop⟩ := hA ψ hψ
    set K' : ℝ := max K 0 with hK'
    have hdom : Tendsto (fun n => ∫ σ in Icc (0 : ℝ) τ, ∫ x, Fn n σ x * An n σ ψ x) atTop
        (𝓝 (∫ σ in Icc (0 : ℝ) τ, ∫ x, G σ x * A σ ψ x)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => B * K') ?_ ?_
        (integrable_const _) ?_
      · exact Filter.Eventually.of_forall fun n =>
          (hmeasn ψ hψ n).mono_measure (Measure.restrict_mono hsub le_rfl)
      · refine Filter.Eventually.of_forall fun n => ?_
        refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
        have hσ' := hsub hσ
        rw [Real.norm_eq_abs]
        refine (sa12x_cs (hFn n σ hσ').1 ((hm σ hσ').2 n)).trans (mul_le_mul
          (ENNReal.toReal_le_of_le_ofReal hB (hFn n σ hσ').2) ?_ ENNReal.toReal_nonneg hB)
        exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
          (((hK σ hσ').2 n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      · exact (ae_restrict_iff' measurableSet_Icc).2
          (Filter.Eventually.of_forall fun σ hσ => hconvA ψ hψ σ (hsub hσ))
    refine tendsto_nhds_unique (hconv ψ hψ τ hτ) ?_
    refine (tendsto_const_nhds.add hdom).congr fun n => ?_
    exact ((hw n).eq ψ hψ τ hτ).symm
-- END SA12.H13

end HRS.MH.AdjointRd.Phase2SA12Global
