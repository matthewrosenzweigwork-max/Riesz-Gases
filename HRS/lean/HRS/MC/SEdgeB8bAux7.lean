import HRS.MC.SEdgeB8bAux6

/-!
# Packet B8b, helper file 7: `L²` passage to the limit in `E[Q_L ψ(Lin^L)]`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS HRS.Sec7 HRS.Q08

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}

theorem b8b_qL_memLp (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    (H : ℕ → ℕ → ℝ) (L : ℕ) : MemLp (b8b_qL S H G L) 2 P := by
  unfold b8b_qL
  have : MemLp (fun ω => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      H i j * (G i ω * G j ω - S i j)) 2 P := by
    refine memLp_finsetSum (p := 2) (f := fun i ω => ∑ j ∈ Finset.range L,
      H i j * (G i ω * G j ω - S i j)) _ fun i hi => ?_
    refine memLp_finsetSum (p := 2) (f := fun j ω => H i j * (G i ω * G j ω - S i j)) _ fun j hj => ?_
    exact ((b8b_GG_memLp P G hGm S hSpsd hlaw (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj)).sub (memLp_const _)).const_mul _
  exact this.const_mul _

theorem b8b_lip {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y, |ψ x - ψ y| ≤ K * ‖x - y‖ := by
  obtain ⟨M, hM⟩ := hψ.2 1 (by norm_num)
  have hM' : ∀ x, ‖fderiv ℝ ψ x‖ ≤ max M 0 := by
    intro x
    have := hM ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_one] at this
    exact this.trans (le_max_left _ _)
  have hd : Differentiable ℝ ψ := hψ.1.differentiable (by norm_num)
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have hL := lipschitzWith_of_nnnorm_fderiv_le (C := Real.toNNReal (max M 0)) hd
    (fun x => by
      rw [← NNReal.coe_le_coe]
      simpa [Real.coe_toNNReal _ (le_max_right M 0)] using hM' x)
  have := hL.dist_le_mul x y
  simpa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (le_max_right M 0)] using this

theorem b8b_psi_L2 (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (α : Fin p → ℕ → ℝ) (Lin : Fin p → Ω → ℝ)
    (hLinm : ∀ a, Measurable (Lin a))
    (hLin : ∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0))
    {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) :
    Tendsto (fun L => eLpNorm (fun ω => ψ (b8b_XL α G L ω) -
      ψ (WithLp.toLp 2 fun a => Lin a ω)) 2 P) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := b8b_lip hψ
  have hψm : Measurable ψ := hψ.1.continuous.measurable
  set d : Fin p → ℕ → Ω → ℝ := fun a L ω => Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω with hd
  have hdm : ∀ a L, Measurable (d a L) := fun a L =>
    (hLinm a).sub (Finset.measurable_sum _ fun i _ => (hGm i).const_mul _)
  have h1 : ∀ a, Tendsto (fun L => eLpNorm (d a L) 2 P) atTop (𝓝 0) := fun a =>
    b8b_eLp_tendsto (fun L => (hdm a L).aestronglyMeasurable) (hLin a)
  have hXm : ∀ L, Measurable (b8b_XL α G L) := fun L => by
    unfold b8b_XL
    fun_prop
  have hbound : ∀ L, eLpNorm (fun ω => ψ (b8b_XL α G L ω) -
      ψ (WithLp.toLp 2 fun a => Lin a ω)) 2 P ≤
      ENNReal.ofReal K * ∑ a, eLpNorm (d a L) 2 P := by
    intro L
    have hpt : ∀ ω, ‖ψ (b8b_XL α G L ω) - ψ (WithLp.toLp 2 fun a => Lin a ω)‖ ≤
        ‖(K • ∑ a, (fun ω => ‖d a L ω‖)) ω‖ := by
      intro ω
      rw [Real.norm_eq_abs]
      refine (hK _ _).trans ?_
      have h2 := b8b_norm_euc_le_sum (b8b_XL α G L ω - WithLp.toLp 2 fun a => Lin a ω)
      have h3 : ∑ a, |(b8b_XL α G L ω - WithLp.toLp 2 fun a => Lin a ω) a| = ∑ a, ‖d a L ω‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [b8b_XL, hd, PiLp.sub_apply, Real.norm_eq_abs]
        rw [← abs_neg]
        congr 1
        ring
      rw [h3] at h2
      have : ‖(K • ∑ a, (fun ω => ‖d a L ω‖)) ω‖ = K * ∑ a, ‖d a L ω‖ := by
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (Finset.sum_nonneg fun _ _ => norm_nonneg _))]
      rw [this]
      exact mul_le_mul_of_nonneg_left h2 hK0
    have hdiffm : AEStronglyMeasurable (fun ω => ψ (b8b_XL α G L ω) -
        ψ (WithLp.toLp 2 fun a => Lin a ω)) P := by
      refine ((hψm.comp (hXm L)).sub (hψm.comp ?_)).aestronglyMeasurable
      fun_prop
    calc eLpNorm (fun ω => ψ (b8b_XL α G L ω) - ψ (WithLp.toLp 2 fun a => Lin a ω)) 2 P
        ≤ eLpNorm (K • ∑ a, (fun ω => ‖d a L ω‖)) 2 P := eLpNorm_mono hdiffm hpt
      _ = ‖K‖ₑ * eLpNorm (∑ a, (fun ω => ‖d a L ω‖)) 2 P := eLpNorm_const_smul _ _ _ _
      _ ≤ ‖K‖ₑ * ∑ a, eLpNorm (fun ω => ‖d a L ω‖) 2 P := by
          gcongr
          exact eLpNorm_sum_le (by norm_num)
      _ = ENNReal.ofReal K * ∑ a, eLpNorm (d a L) 2 P := by
          rw [Real.enorm_eq_ofReal hK0]
          congr 1
          exact Finset.sum_congr rfl fun a _ => eLpNorm_norm _ (hdm a L).aestronglyMeasurable
  have hlim : Tendsto (fun L => ENNReal.ofReal K * ∑ a, eLpNorm (d a L) 2 P) atTop (𝓝 0) := by
    have : Tendsto (fun L => ∑ a, eLpNorm (d a L) 2 P) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun a _ => h1 a
    have := ENNReal.Tendsto.const_mul this (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

end Limit

end HRS.MC.SEdge.B8b
