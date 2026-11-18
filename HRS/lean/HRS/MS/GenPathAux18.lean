import HRS.MS.GenPathAux17
import HRS.MS.SuppU11Aux1

/-!
# S5.6 packet P5a (part 2): `r ↦ ⟨e, Γ_{r,a}(x)⟩_𝒦` is continuous on `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

open Classical in
theorem s56_feat_inner_cont (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (a : Fin d) (x : Euc d) (e : KSpace d b.m b.T) :
    ContinuousOn (fun r => inner ℝ e (gradFeature (S.coeff N) b.m b.T a r x)) (Set.Icc 0 b.T) := by
  intro r₀ hr₀
  set C := S.coeff N with hCdef
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) b.T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set fc : ℝ → ℝ → OscDual d b.m := fun r t => if r < t then ellVec (d := d) b.m
    (fun α => gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x) else 0 with hfc
  set base : OscDual d b.m := ellVec (d := d) b.m (fun α => gradComp a (oscTestFun b.m α) x) with hbase
  set c₀ : ℝ := inner ℝ e.A₀ base + inner ℝ e.B base with hc₀
  set g : ℝ → OscDual d b.m := fun t => ((e.A' : L2Path d b.m b.T) : ℝ → OscDual d b.m) t with hg
  have hform : ∀ r ∈ Set.Icc (0 : ℝ) b.T, inner ℝ e (gradFeature C b.m b.T a r x) =
      c₀ + ∫ t, inner ℝ (g t) (fc r t) ∂μ := by
    intro r hr
    have hmem : MemLp (fc r) 2 μ := (hC.feature a r hr x).2.2
    show inner ℝ e (KSpace.mk base (if h : MemLp (fun t => if r < t then ellVec (d := d) b.m
        (fun α => gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x) else 0) 2 μ
        then h.toLp _ else 0) base) = _
    rw [dif_pos hmem, HRS.MS.S52.s52_inner_mk, MeasureTheory.L2.inner_def]
    have hae : ∀ᵐ t ∂μ, inner ℝ ((e.A' : L2Path d b.m b.T) t) ((hmem.toLp (fc r)) t) =
        inner ℝ (g t) (fc r t) := by
      filter_upwards [hmem.coeFn_toLp] with t ht
      rw [ht]
    rw [integral_congr_ae hae]
    ring
  -- uniform bound of the feature values
  obtain ⟨Co, hCo0, hCo⟩ := HRS.MS.Go.s55f_orbit_bound b hbv
  set bb : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) with hbb
  have hb0 : ∀ α, 0 ≤ bb α := fun α => Real.rpow_nonneg (oscEigenvalue_pos α).le _
  have hb2 := s56_b_sq_summable b hbv
  have hcoord : ∀ α (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ b.T →
      |gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x| ≤ Co * bb α := by
    intro α r t hr hrt ht
    have := ((hCo S N a r t hr hrt ht α).2 0 (Nat.zero_le _) x)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  set Bf : ℝ := Co * Real.sqrt (∑' α, bb α ^ 2) with hBf
  have hBf0 : 0 ≤ Bf := by positivity
  have hfnorm : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ‖fc r t‖ ≤ Bf := by
    intro r hr t ht
    by_cases hrt : r < t
    · have hmemℓ := (hC.feature a r hr x).2.1 t ⟨hrt, ht.2⟩
      simp only [hfc, hrt, if_true]
      refine HRS.Whole.u11_norm_ellVec_le b.m _ hmemℓ hBf0 ?_
      have hle : ∀ α, (gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x) ^ 2 ≤
          Co ^ 2 * bb α ^ 2 := fun α => by
        have := hcoord α r t hr.1 hrt.le ht.2
        calc _ = |gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x| ^ 2 := (sq_abs _).symm
          _ ≤ (Co * bb α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = _ := by ring
      calc ∑' α, (gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x) ^ 2
          ≤ ∑' α, Co ^ 2 * bb α ^ 2 :=
            hasSum_le hle (s56_sq_summable_of_memℓp hmemℓ).hasSum (hb2.mul_left _).hasSum |>.trans_eq rfl
        _ = Bf ^ 2 := by
            rw [tsum_mul_left, hBf, mul_pow, Real.sq_sqrt (tsum_nonneg fun α => sq_nonneg _)]
    · simp only [hfc, hrt, if_false, norm_zero]; exact hBf0
  have hgmem : MemLp (fun t => g t) 2 μ := Lp.memLp e.A'
  have hmeasF : ∀ r ∈ Set.Icc (0 : ℝ) b.T, AEStronglyMeasurable (fun t => inner ℝ (g t) (fc r t)) μ :=
    fun r hr => hgmem.aestronglyMeasurable.inner (hC.feature a r hr x).2.2.aestronglyMeasurable
  set bound : ℝ → ℝ := fun t => ‖g t‖ * Bf with hbound
  have hbound_int : Integrable bound μ := (hgmem.integrable (by norm_num)).norm.mul_const Bf
  have hcl : ∀ α, ∀ t ∈ Set.Icc (0 : ℝ) b.T, IsClassicalAdjointW C t (generatorW C t (oscTestFun b.m α))
      (fun r => propagatorW C r t (generatorW C t (oscTestFun b.m α))) := fun α t ht => by
    obtain ⟨B, -, h⟩ := HRS.MS.Go.s55m_family b hbv S N α
    exact (h t ht).1
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun r => inner ℝ (g t) (fc r t)) (𝓝[Set.Icc 0 b.T] r₀)
      (𝓝 (inner ℝ (g t) (fc r₀ t))) := by
    have hne : ∀ᵐ t ∂μ, t ≠ r₀ := ae_restrict_of_ae ((Set.countable_singleton r₀).ae_notMem volume)
    filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t htne htI
    rcases lt_or_gt_of_ne htne with htr | htr
    · -- `t < r₀`
      have hev : ∀ᶠ r in 𝓝[Set.Icc 0 b.T] r₀, t < r :=
        nhdsWithin_le_nhds (Ioi_mem_nhds htr)
      have e0 : fc r₀ t = 0 := by simp [hfc, not_lt.2 htr.le]
      have e1 : ∀ᶠ r in 𝓝[Set.Icc 0 b.T] r₀, inner ℝ (g t) (fc r t) = 0 :=
        hev.mono fun r hr => by simp [hfc, not_lt.2 hr.le]
      rw [e0, inner_zero_right]
      exact tendsto_const_nhds.congr' (e1.mono fun r h => h.symm)
    · -- `r₀ < t`
      set γ : MultiIndex d → ℝ := fun α => OscDual.coord (g t) α with hγ
      have hγs : Summable fun α => γ α ^ 2 := s56_sq_summable_of_memℓp (lp.memℓp (g t))
      set F : ℝ → ℝ := fun r => ∑' α, gradComp a (propagatorW C r t (generatorW C t (oscTestFun b.m α))) x * γ α
        with hF
      have hFc : ContinuousOn F (Set.Icc 0 t) :=
        s56_cont_pairing hb2 hb0 Co (fun α => s56_gradComp_cont_r (hcl α t htI) a x)
          (fun α r hr => hcoord α r t hr.1 hr.2 htI.2) hγs
      have hmemnhds : Set.Icc 0 t ∈ 𝓝[Set.Icc 0 b.T] r₀ :=
        mem_nhdsWithin.2 ⟨Set.Iio t, isOpen_Iio, htr, fun r hr => ⟨hr.2.1, hr.1.le⟩⟩
      have hcw : ContinuousWithinAt F (Set.Icc 0 b.T) r₀ :=
        (hFc r₀ ⟨hr₀.1, htr.le⟩).mono_of_mem_nhdsWithin hmemnhds
      have hFeq : ∀ r ∈ Set.Icc (0 : ℝ) b.T, r < t → inner ℝ (g t) (fc r t) = F r := by
        intro r hr hrt
        simp only [hfc, hrt, if_true]
        rw [real_inner_comm, s56_inner_ellVec b.m ((hC.feature a r hr x).2.1 t ⟨hrt, htI.2⟩)]
      have hev : ∀ᶠ r in 𝓝[Set.Icc 0 b.T] r₀, inner ℝ (g t) (fc r t) = F r := by
        rw [eventually_nhdsWithin_iff]
        exact Filter.Eventually.mono (Iio_mem_nhds htr) fun r hrt hrI => hFeq r hrI hrt
      rw [hFeq r₀ hr₀ htr]
      exact hcw.tendsto.congr' (hev.mono fun r h => h.symm)
  have hint : Tendsto (fun r => ∫ t, inner ℝ (g t) (fc r t) ∂μ) (𝓝[Set.Icc 0 b.T] r₀)
      (𝓝 (∫ t, inner ℝ (g t) (fc r₀ t) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound
      (eventually_nhdsWithin_of_forall hmeasF) ?_ hbound_int hlim
    refine eventually_nhdsWithin_of_forall fun r hr => ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc ‖inner ℝ (g t) (fc r t)‖ ≤ ‖g t‖ * ‖fc r t‖ := norm_inner_le_norm _ _
      _ ≤ ‖g t‖ * Bf := mul_le_mul_of_nonneg_left (hfnorm r hr t ht) (norm_nonneg _)
  have hcw : ContinuousWithinAt (fun r => c₀ + ∫ t, inner ℝ (g t) (fc r t) ∂μ) (Set.Icc 0 b.T) r₀ :=
    tendsto_const_nhds.add hint
  exact hcw.congr hform (hform r₀ hr₀)

end HRS.MS.GenPath
