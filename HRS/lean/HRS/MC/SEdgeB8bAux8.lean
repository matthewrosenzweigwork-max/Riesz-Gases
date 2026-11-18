import HRS.MC.SEdgeB8bAux7

/-!
# Packet B8b, helper file 8: the probabilistic core of the Wick IBP for the chaos limit
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS HRS.Sec7 HRS.Q08

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}

/-- a bounded continuous function built from a continuous bounded one -/
def b8b_bcfOf {E : Type*} [TopologicalSpace E] (F : E → ℝ) (hF : Continuous F) (M : ℝ)
    (hM : ∀ x, |F x| ≤ M) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * M) (by
    intro x y
    rw [Real.dist_eq]
    have := hM x
    have := hM y
    calc |F x - F y| ≤ |F x| + |F y| := abs_sub _ _
      _ ≤ 2 * M := by linarith)

theorem b8b_bcfOf_apply {E : Type*} [TopologicalSpace E] (F : E → ℝ) (hF : Continuous F) (M : ℝ)
    (hM : ∀ x, |F x| ≤ M) (x : E) : b8b_bcfOf F hF M hM x = F x := rfl

theorem b8b_F_bdd {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) (b c : Fin p) :
    ∃ M, ∀ z, |iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c]| ≤ M := by
  obtain ⟨M, hM⟩ := hψ.2 2 le_rfl
  refine ⟨M, fun z => ?_⟩
  have h1 := (iteratedFDeriv ℝ 2 ψ z).le_opNorm ![stdVec b, stdVec c]
  have h2 : ∏ i, ‖(![stdVec b, stdVec c] : Fin 2 → EuclideanSpace ℝ (Fin p)) i‖ = 1 := by
    simp [Fin.prod_univ_two, stdVec]
  rw [h2, mul_one] at h1
  have h3 := hM ⟨z, rfl⟩
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h3

theorem b8b_prob_main (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    (α : Fin p → ℕ → ℝ) (Lin : Fin p → Ω → ℝ) (hLinm : ∀ a, Measurable (Lin a))
    (hLin : ∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L, α a i * G i ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0))
    (H : ℕ → ℕ → ℝ) (Qv : Ω → ℝ) (hQm : Measurable Qv)
    (hQ : Tendsto (fun L => ∫⁻ ω, ‖Qv ω - b8b_qL S H G L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0))
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ a b, Tendsto (fun L => b8b_CL α S L a b) atTop (𝓝 (C a b)))
    (Θ : Fin p → Fin p → ℝ)
    (hΘ : ∀ b c, Tendsto (fun L => b8b_Theta α S H L b c) atTop (𝓝 (Θ b c))) :
    P.map (fun ω => (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 C ∧
      ∀ ψ : EuclideanSpace ℝ (Fin p) → ℝ, MemCb 2 ψ →
        ∫ ω, Qv ω * ψ (WithLp.toLp 2 fun a => Lin a ω) ∂P =
          (1 / 2) * ∑ b, ∑ c, Θ b c *
            ∫ z, iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c] ∂(multivariateGaussian 0 C) := by
  obtain ⟨hpsd, hlawY⟩ := b8b_law P G hGm S hSpsd hlaw α Lin hLinm hLin C hC
  refine ⟨hlawY, fun ψ hψ => ?_⟩
  set Y : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a => Lin a ω with hY
  have hYm : Measurable Y := by rw [hY]; fun_prop
  have hXm : ∀ L, Measurable (b8b_XL α G L) := fun L => by
    unfold b8b_XL
    fun_prop
  have hψc : Continuous ψ := hψ.1.continuous
  have hψm : Measurable ψ := hψc.measurable
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, |ψ x| ≤ M := by
    obtain ⟨M, hM⟩ := hψ.2 0 (Nat.zero_le _)
    exact ⟨M, fun x => by
      have := hM ⟨x, rfl⟩
      simpa using this⟩
  -- L² data
  have hq : ∀ L, MemLp (b8b_qL S H G L) 2 P := fun L => b8b_qL_memLp P G hGm S hSpsd hlaw H L
  have hqm : ∀ L, Measurable (b8b_qL S H G L) := fun L => by
    unfold b8b_qL
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    exact Measurable.const_mul (((hGm i).mul (hGm j)).sub measurable_const) _
  have hqlim' : Tendsto (fun L => eLpNorm (fun ω => Qv ω - b8b_qL S H G L ω) 2 P) atTop (𝓝 0) :=
    b8b_eLp_tendsto (fun L => (hQm.sub (hqm L)).aestronglyMeasurable) hQ
  have hqlim : Tendsto (fun L => eLpNorm (fun ω => b8b_qL S H G L ω - Qv ω) 2 P) atTop (𝓝 0) := by
    refine hqlim'.congr fun L => ?_
    exact eLpNorm_sub_comm (f := Qv) (g := b8b_qL S H G L) (p := 2) (μ := P)
  have hQmem : MemLp Qv 2 P := by
    obtain ⟨L0, hL0⟩ := (hqlim.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
    have h1 : MemLp (fun ω => b8b_qL S H G L0 ω - Qv ω) 2 P :=
      (Set.mem_Iio.1 hL0).trans ENNReal.one_lt_top
    have h2 := (hq L0).sub h1
    refine MemLp.ae_eq (Eventually.of_forall fun ω => ?_) h2
    simp
  -- Lp elements
  set qv : Lp ℝ 2 P := hQmem.toLp Qv with hqv
  set ql : ℕ → Lp ℝ 2 P := fun L => (hq L).toLp (b8b_qL S H G L) with hql
  have hql_t : Tendsto ql atTop (𝓝 qv) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hqlim.congr fun L => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hq L).coeFn_toLp, hQmem.coeFn_toLp] with ω h2 h3
    simp only [Pi.sub_apply, hql, hqv]
    rw [h2, h3]
  -- the test function
  have hψmem : ∀ f : Ω → EuclideanSpace ℝ (Fin p), Measurable f →
      MemLp (fun ω => ψ (f ω)) 2 P := fun f hf =>
    MemLp.of_bound (hψm.comp hf).aestronglyMeasurable M
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM _)
  set pX : ℕ → Lp ℝ 2 P := fun L => (hψmem _ (hXm L)).toLp (fun ω => ψ (b8b_XL α G L ω)) with hpX
  set pY : Lp ℝ 2 P := (hψmem Y hYm).toLp (fun ω => ψ (Y ω)) with hpY
  have hpX_t : Tendsto pX atTop (𝓝 pY) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (b8b_psi_L2 P G hGm α Lin hLinm hLin hψ).congr fun L => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hψmem _ (hXm L)).coeFn_toLp, (hψmem Y hYm).coeFn_toLp] with ω h2 h3
    simp only [Pi.sub_apply, hpX, hpY]
    rw [h2, h3]
  have hlim1 : Tendsto (fun L => ∫ ω, b8b_qL S H G L ω * ψ (b8b_XL α G L ω) ∂P) atTop
      (𝓝 (∫ ω, Qv ω * ψ (Y ω) ∂P)) := by
    have h := Filter.Tendsto.inner (𝕜 := ℝ) hql_t hpX_t
    have e1 : ∀ L, inner ℝ (ql L) (pX L) = ∫ ω, b8b_qL S H G L ω * ψ (b8b_XL α G L ω) ∂P :=
      fun L => q08s_inner_toLp P (hq L) (hψmem _ (hXm L))
    have e2 : inner ℝ qv pY = ∫ ω, Qv ω * ψ (Y ω) ∂P := q08s_inner_toLp P hQmem (hψmem Y hYm)
    simpa only [e1, e2] using h
  -- the limit of the right-hand side
  have hmeas := b8b_inMeasure_XL P G α Lin hGm hLinm hLin
  have hD : ∀ b c, Tendsto (fun L => ∫ ω, iteratedFDeriv ℝ 2 ψ (b8b_XL α G L ω)
        ![stdVec b, stdVec c] ∂P) atTop
      (𝓝 (∫ z, iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c] ∂(multivariateGaussian 0 C))) := by
    intro b c
    obtain ⟨Mb, hMb⟩ := b8b_F_bdd hψ b c
    have h := b8b_bcf_tendsto (P := P) hXm hYm hmeas
      (b8b_bcfOf _ (b8b_cont_F hψ b c) Mb hMb)
    rw [← hlawY, integral_map hYm.aemeasurable (b8b_cont_F hψ b c).aestronglyMeasurable]
    exact h
  have hlim2 : Tendsto (fun L => ∫ ω, b8b_qL S H G L ω * ψ (b8b_XL α G L ω) ∂P) atTop
      (𝓝 ((1 / 2) * ∑ b, ∑ c, Θ b c *
        ∫ z, iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c] ∂(multivariateGaussian 0 C))) := by
    simp_rw [b8b_stage P G hGm S hSpsd hlaw α H _ hψ]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun c _ => ?_)
    exact (hΘ b c).mul (hD b c)
  exact tendsto_nhds_unique hlim1 hlim2

end Main
