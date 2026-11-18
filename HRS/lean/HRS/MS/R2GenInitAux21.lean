import HRS.MS.R2GenInitAux20

/-!
# S10.5 window comparison, packet B7: continuity in `r` of the pairing of the middle slot of the window feature
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.Go HRS.MS.R2WinErr HRS.MS.GenPath

variable {d : ℕ}

theorem s105_win_mid_cont (C : WholeCoeff d) (k : ℕ) (m T b cdec Cs : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hcd : 0 ≤ cdec) (hCs : 0 ≤ Cs) (hbS : Summable (s104_b d))
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec)
    (hex1 : ∀ α, ∀ t : ℝ, 0 ≤ t → ∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun m α)) f)
    (a : Fin d) (x : Euc d) (g : L2Path d m T)
    (hmem : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), MemLp (fun u : ℝ => if r < b + u then
      ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x)
      else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmemℓ : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ u ∈ Set.Icc (0 : ℝ) T, r < b + u →
      Memℓp (fun α => gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x) 2) :
    ContinuousOn (fun r => ∫ u in Set.Icc (0 : ℝ) T, inner ℝ ((g : ℝ → OscDual d m) u) (if r < b + u then
      ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x)
      else 0)) (Set.Icc (0 : ℝ) (b + T)) := by
  intro r₀ hr₀
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set fc : ℝ → ℝ → OscDual d m := fun r u => if r < b + u then ellVec (d := d) m
    (fun α => gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x) else 0 with hfc
  set Bs : ℝ := Cs * Real.sqrt (∑' α, s104_b d α) with hBs
  have hBs0 : 0 ≤ Bs := by positivity
  have hcb : ∀ r u, 0 ≤ u → r ∈ Set.Icc (0 : ℝ) (b + u) → ∀ α,
      |gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x| ≤ Cs * s104_b d α :=
    fun r u hu hr α => s105_coord_le C (mul_nonneg hCs (s104_b_nonneg α)) hcd (hG' α (b + u) (by linarith)) hr a x
  have hfnorm : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ u ∈ Set.Icc (0 : ℝ) T, ‖fc r u‖ ≤ Bs := by
    intro r hr u hu
    by_cases hru : r < b + u
    · simp only [hfc, hru, if_true]
      have hbd : ∀ α, |gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x| ≤
          Cs * s104_b d α := hcb r u hu.1 ⟨hr.1, hru.le⟩
      exact u11_norm_ellVec_le m _ (hmemℓ r hr u hu hru) hBs0 (s105_sq_sum_le hCs hbd hbS)
    · simp only [hfc, hru, if_false, norm_zero]; exact hBs0
  have hgmem : MemLp (fun u => (g : ℝ → OscDual d m) u) 2 μ := Lp.memLp g
  have hmeasF : ∀ r ∈ Set.Icc (0 : ℝ) (b + T),
      AEStronglyMeasurable (fun u => inner ℝ ((g : ℝ → OscDual d m) u) (fc r u)) μ :=
    fun r hr => hgmem.aestronglyMeasurable.inner (hmem r hr).aestronglyMeasurable
  set bound : ℝ → ℝ := fun u => ‖(g : ℝ → OscDual d m) u‖ * Bs with hbound
  have hbound_int : Integrable bound μ := (hgmem.integrable (by norm_num)).norm.mul_const Bs
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun r => inner ℝ ((g : ℝ → OscDual d m) u) (fc r u))
      (𝓝[Set.Icc (0 : ℝ) (b + T)] r₀) (𝓝 (inner ℝ ((g : ℝ → OscDual d m) u) (fc r₀ u))) := by
    have hne : ∀ᵐ u ∂μ, u ≠ r₀ - b := ae_restrict_of_ae ((Set.countable_singleton (r₀ - b)).ae_notMem volume)
    filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with u hune huI
    rcases lt_or_gt_of_ne (sub_ne_zero.2 (fun h => hune (by linarith)) : u - (r₀ - b) ≠ 0) with hlt | hgt
    · -- `b + u < r₀`
      have hlt' : b + u < r₀ := by linarith
      have hev : ∀ᶠ r in 𝓝[Set.Icc (0 : ℝ) (b + T)] r₀, b + u < r :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hlt')
      have e0 : fc r₀ u = 0 := by simp [hfc, not_lt.2 hlt'.le]
      have e1 : ∀ᶠ r in 𝓝[Set.Icc (0 : ℝ) (b + T)] r₀, inner ℝ ((g : ℝ → OscDual d m) u) (fc r u) = 0 :=
        hev.mono fun r hr => by simp [hfc, not_lt.2 hr.le]
      rw [e0, inner_zero_right]
      exact tendsto_const_nhds.congr' (e1.mono fun r h => h.symm)
    · -- `r₀ < b + u`
      have hgt' : r₀ < b + u := by linarith
      set γ : MultiIndex d → ℝ := fun α => OscDual.coord ((g : ℝ → OscDual d m) u) α with hγ
      have hγs : Summable fun α => γ α ^ 2 := s56_sq_summable_of_memℓp (lp.memℓp _)
      set F : ℝ → ℝ := fun r => ∑' α, gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x * γ α
        with hF
      have hcl : ∀ α, IsClassicalAdjointW C (b + u) (generatorW C (b + u) (oscTestFun m α))
          (fun r => propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) := fun α =>
        HRS.MS.Fcau.propagatorW_isClassical (hex1 α (b + u) (by linarith [huI.1]))
      have hFc : ContinuousOn F (Set.Icc 0 (b + u)) :=
        s56_cont_pairing (s105_b_sq_summable hbS) (fun α => s104_b_nonneg α) Cs
          (fun α => s56_gradComp_cont_r (hcl α) a x) (fun α r hr => hcb r u huI.1 hr α) hγs
      have hmemnhds : Set.Icc 0 (b + u) ∈ 𝓝[Set.Icc (0 : ℝ) (b + T)] r₀ :=
        mem_nhdsWithin.2 ⟨Set.Iio (b + u), isOpen_Iio, hgt', fun r hr => ⟨hr.2.1, hr.1.le⟩⟩
      have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) (b + T)) r₀ :=
        (hFc r₀ ⟨hr₀.1, hgt'.le⟩).mono_of_mem_nhdsWithin hmemnhds
      have hFeq : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), r < b + u →
          inner ℝ ((g : ℝ → OscDual d m) u) (fc r u) = F r := by
        intro r hr hrt
        simp only [hfc, hrt, if_true]
        rw [real_inner_comm, s56_inner_ellVec m (hmemℓ r hr u huI hrt)]
      have hev : ∀ᶠ r in 𝓝[Set.Icc (0 : ℝ) (b + T)] r₀,
          inner ℝ ((g : ℝ → OscDual d m) u) (fc r u) = F r := by
        rw [eventually_nhdsWithin_iff]
        exact Filter.Eventually.mono (Iio_mem_nhds hgt') fun r hrt hrI => hFeq r hrI hrt
      rw [hFeq r₀ hr₀ hgt']
      exact hcw.tendsto.congr' (hev.mono fun r h => h.symm)
  have hint : Tendsto (fun r => ∫ u, inner ℝ ((g : ℝ → OscDual d m) u) (fc r u) ∂μ)
      (𝓝[Set.Icc (0 : ℝ) (b + T)] r₀) (𝓝 (∫ u, inner ℝ ((g : ℝ → OscDual d m) u) (fc r₀ u) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound
      (eventually_nhdsWithin_of_forall hmeasF) ?_ hbound_int hlim
    refine eventually_nhdsWithin_of_forall fun r hr => ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    calc ‖inner ℝ ((g : ℝ → OscDual d m) u) (fc r u)‖ ≤ ‖(g : ℝ → OscDual d m) u‖ * ‖fc r u‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖(g : ℝ → OscDual d m) u‖ * Bs := mul_le_mul_of_nonneg_left (hfnorm r hr u hu) (norm_nonneg _)
  exact hint

end HRS.MS.R2GenInit
