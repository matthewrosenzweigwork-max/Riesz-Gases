import HRS.MS.WsStatAux17

/-!
# S21R packet 2: the GLOBAL filtered modification of a collision-free strong solution

`s21p_filtered_global`: for `d >= 1`, `N >= 2` and a vector Brownian motion `W` with `X 0` independent of `W`, `X 0` a.s. collision free,
and a collision-free strong solution `X` of `quadraticGradientDyn d s a beta` on EVERY horizon `[0,T]`, there are a Brownian filtration
`F`, the coordinates `W'` and an everywhere continuous modification `X'` of `X` (`X'_t = X_t` a.s. for every `t`) that is a strong
solution on every horizon (with the same initial datum `X 0`) and is a filtered solution for `(F, W')`.

This is `s21f_filtered` (WsStatAux17, a single horizon `T`, freezing device) with the maximal solution kept on `[0,infty)`: the maximal
collision-free solution `Y` of `exists_sde_solution_maximal` has lifetime `> n` a.s. for every `n`, hence lifetime `infty` a.s.  Needed
because the frozen statement S2.1 (ii) carries no filtration while the consumers (`MovParticleSetup` of S6.6, `IsR2Realization` of S10.x)
require a filtered solution on all horizons simultaneously.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP1
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

set_option linter.unusedSectionVars false

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

open Classical in
/-- The global modification: `Y` on the good set `G`, `0` off it. -/
def s21p_glob (G : Set Ω) (Y : ℝ → Ω → EucConfig d N) (t : ℝ≥0) (ζ : Ω) : EucConfig d N :=
  if ζ ∈ G then Y t ζ else 0

theorem s21p_glob_of_mem {G : Set Ω} {Y : ℝ → Ω → EucConfig d N} {t : ℝ≥0} {ζ : Ω} (hζ : ζ ∈ G) :
    s21p_glob G Y t ζ = Y t ζ := by
  simp [s21p_glob, hζ]

theorem s21p_glob_of_notMem {G : Set Ω} {Y : ℝ → Ω → EucConfig d N} {t : ℝ≥0} {ζ : Ω} (hζ : ζ ∉ G) :
    s21p_glob G Y t ζ = 0 := by
  simp [s21p_glob, hζ]

theorem s21p_filtered_global (hd : 1 ≤ d) (s a β : ℝ) (hN : 2 ≤ N)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hbrownian : IsVectorBrownian P W) (hindep : IndepFun (X 0) (fun ζ => fun t => W t ζ) P)
    (hinit_distinct : ∀ᵐ ζ ∂P, X 0 ζ ∉ eucCollisionSet d N)
    (hS : ∀ T : ℝ, 0 < T → IsWholeStrongSolution P (quadraticGradientDyn d s a β) T (X 0) W X)
    (hX0m : Measurable (X 0)) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, X' t =ᵐ[P] X t) ∧
      (∀ T : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T (X 0) W X') ∧
      IsWholeFilteredSolution P ℱ W' W X' := by
  classical
  obtain ⟨ℱ, W', hBF, hcomp, hWW', hX₀ℱ, -, -⟩ := ssp1_base P W hbrownian (X 0) hX0m hindep
  have hcoll : MeasurableSet (eucCollisionSet d N) := (ssp1_isClosed_coll d N).measurableSet
  obtain ⟨ω₀, hω₀⟩ := hinit_distinct.exists
  let Y₀ : Ω → EucConfig d N := fun ζ => if X 0 ζ ∈ eucCollisionSet d N then X 0 ω₀ else X 0 ζ
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace Ω := ℱ t
    exact Measurable.ite (hX₀ℱ t hcoll) measurable_const (hX₀ℱ t)
  have hY₀U : ∀ ζ, Y₀ ζ ∈ ssp1_U d N := by
    intro ζ
    by_cases h : X 0 ζ ∈ eucCollisionSet d N
    · simp only [Y₀, h, ↓reduceIte]; exact hω₀
    · simp only [Y₀, h, ↓reduceIte]; exact h
  have hY₀ae : ∀ᵐ ζ ∂P, Y₀ ζ = X 0 ζ := by
    filter_upwards [hinit_distinct] with ζ h
    simp only [Y₀, h, ↓reduceIte]
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, -⟩ := exists_sde_solution_maximal hBF
    (ssp1_U d N) (ssp1_isOpen_U d N) (s21f_b d N s a β) (s21f_locLipschitz s a β)
    (ssp1_sigma d N β⁻¹) Y₀ hY₀m hY₀U
  -- on each horizon `T > 0` the maximal solution agrees with `X` and lives beyond `T`
  have hkeyT : ∀ T : ℝ, 0 < T → ∀ᵐ ζ ∂P, (T : WithTop ℝ) < τ ζ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ζ = X (Real.toNNReal t) ζ := by
    intro T hT
    have hSn := hS T hT
    filter_upwards [hsol.isPathSolution, hSn.eqn, hSn.cont, hSn.no_collision, hSn.init, hWW',
      HRS.IsVectorBrownian.ae_zero hbrownian, hY₀ae] with ζ hpath heqn hcont hnc hinit hw hw0 hY0
    have hXc : Continuous fun t => X t ζ := continuous_pi hcont
    have hzc : Continuous fun r : ℝ => X (Real.toNNReal r) ζ := hXc.comp continuous_real_toNNReal
    have hz : IsPathSolution (s21f_b d N s a β) (ssp1_sigma d N β⁻¹) (fun t => W' t ζ) (Y₀ ζ)
        (T : WithTop ℝ) (fun r => X (Real.toNNReal r) ζ) := by
      refine ⟨by simp only [Real.toNNReal_zero]; rw [hY0], fun t ht htT => ?_⟩
      have htT' : t < T := WithTop.coe_lt_coe.1 htT
      have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
      obtain ⟨hint, heq⟩ := heqn (Real.toNNReal t) (by rw [ht']; exact htT'.le)
      rw [ht'] at hint heq
      have hintE : IntegrableOn (fun r : ℝ => s21f_b d N s a β r (X (Real.toNNReal r) ζ))
          (Set.Icc 0 t) := Integrable.of_eval hint
      refine ⟨hzc.continuousOn, hintE, ?_⟩
      funext i
      have h2 := ssp1_integral_apply hintE i
      have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
      have h3 := heq i
      rw [hW0i, sub_zero, ← hY0] at h3
      rw [ssp1_noise_eq β⁻¹ (fun i j => hw (Real.toNNReal t) i j)]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [h2]
      exact h3
    have hzU : ∀ t ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal t) ζ ∈ ssp1_U d N := fun t ht =>
      hnc (Real.toNNReal t) (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
    exact ssp1_det_domination (ssp1_isOpen_U d N) (s21f_locLipschitz s a β) (hBF.cont ζ) hT
      (hpos ζ) hpath (fun t ht htτ => hmem ζ t ht htτ)
      (fun h K hK hKU t₀ ht₀ => hexit ζ h K hK hKU t₀ ht₀) hz hzc.continuousOn hzU
  have hkeyN : ∀ᵐ ζ ∂P, ∀ n : ℕ, (((n : ℝ) + 1 : ℝ) : WithTop ℝ) < τ ζ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), Y t ζ = X (Real.toNNReal t) ζ := by
    rw [ae_all_iff]
    exact fun n => hkeyT ((n : ℝ) + 1) (by positivity)
  -- the good set
  obtain ⟨G, hGm, hG0, hG⟩ := ssp1_exists_measurable_good P
    (p := fun ζ => ∀ n : ℕ, (((n : ℝ) + 1 : ℝ) : WithTop ℝ) < τ ζ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), Y t ζ = X (Real.toNNReal t) ζ) hkeyN
  have hGt : ∀ t : ℝ, MeasurableSet[ℱ t] G := ssp1_measurableSet_of_null_compl hcomp hGm hG0
  have hGae : ∀ᵐ ζ ∂P, ζ ∈ G := by
    rw [ae_iff]; exact hG0
  have hGall : ∀ ζ ∈ G, ∀ t : ℝ, (t : WithTop ℝ) < τ ζ := by
    intro ζ hζ t
    obtain ⟨n, hn⟩ := exists_nat_gt t
    refine lt_trans (WithTop.coe_lt_coe.2 (by linarith)) ((hG ζ hζ n).1)
  have hYcontn : ∀ ζ ∈ G, ∀ T : ℝ, 0 ≤ T → ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T) :=
    fun ζ hζ T hT => hsol.cont ζ T hT (hGall ζ hζ T)
  have hYU : ∀ ζ ∈ G, ∀ t : ℝ≥0, Y t ζ ∈ ssp1_U d N := fun ζ hζ t =>
    hmem ζ t t.2 (hGall ζ hζ t)
  have hX'adapt : ∀ t : ℝ≥0, Measurable[ℱ t] (s21p_glob G Y t) := by
    intro t
    have h1 : Measurable[ℱ t] (Y t) := hsol.adapted t
    exact Measurable.ite (hGt t) h1 measurable_const
  have hmod : ∀ t : ℝ≥0, s21p_glob G Y t =ᵐ[P] X t := by
    intro t
    filter_upwards [hkeyN, hGae] with ζ hk hζ
    rw [s21p_glob_of_mem hζ]
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    rw [(hk n).2 t ⟨t.2, by linarith⟩, Real.toNNReal_coe]
  -- everywhere continuity
  have hcont : ∀ ζ, Continuous fun t : ℝ≥0 => s21p_glob G Y t ζ := by
    intro ζ
    by_cases hζ : ζ ∈ G
    · rw [continuous_iff_continuousAt]
      intro t0
      have hfr : Continuous fun t : ℝ≥0 => ssp1_freeze ((t0 : ℝ) + 1) G Y t ζ :=
        ssp1_freeze_continuous (by positivity) (fun ζ' hζ' => hYcontn ζ' hζ' _ (by positivity)) ζ
      refine hfr.continuousAt.congr ?_
      have hev : ∀ᶠ t : ℝ≥0 in 𝓝 t0, (t : ℝ) ≤ (t0 : ℝ) + 1 := by
        have : Set.Iio (t0 + 1) ∈ 𝓝 t0 := Iio_mem_nhds (by
          have : (t0 : ℝ≥0) < t0 + 1 := lt_add_of_pos_right _ one_pos
          exact this)
        filter_upwards [this] with t ht
        have : (t : ℝ) < ((t0 + 1 : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 ht
        push_cast at this
        exact this.le
      filter_upwards [hev] with t ht
      rw [ssp1_freeze_of_le ht hζ, s21p_glob_of_mem hζ]
    · have : (fun t : ℝ≥0 => s21p_glob G Y t ζ) = fun _ => 0 := by
        funext t; exact s21p_glob_of_notMem hζ
      rw [this]; exact continuous_const
  have hX'0 : s21p_glob G Y 0 = fun ζ => if ζ ∈ G then Y₀ ζ else 0 := by
    funext ζ
    by_cases hζ : ζ ∈ G
    · rw [s21p_glob_of_mem hζ]; simp [hζ]
      have := hsol.init ζ
      simpa using this
    · rw [s21p_glob_of_notMem hζ]; simp [hζ]
  have hprog : IsProgressive ℱ (ofNNRealTime (s21p_glob G Y)) := by
    refine ssp1_isProgressive_of_continuous hX'adapt (fun t => ?_) hcont
    rw [hX'0]
    let _ : MeasurableSpace Ω := ℱ t
    exact Measurable.ite (hGt t) (hY₀m t) measurable_const
  have hinit : ∀ᵐ ζ ∂P, s21p_glob G Y 0 ζ = X 0 ζ := by
    filter_upwards [hGae, hY₀ae] with ζ hζ hY0
    rw [hX'0]
    simp only [hζ, ite_true]
    exact hY0
  refine ⟨s21p_glob G Y, ℱ, W', hmod, fun T => ⟨hinit, ?_, Filter.Eventually.of_forall fun ζ i =>
    (continuous_apply i).comp (hcont ζ), fun t => (hX'adapt t).mono (ℱ.le t) le_rfl, ?_⟩,
    ⟨hBF, hWW', hX'adapt, hprog⟩⟩
  · -- the equation
    filter_upwards [hsol.eq, hGae, hWW', HRS.IsVectorBrownian.ae_zero hbrownian] with ζ hsq hζ hw hw0 t ht
    have htτ : ((t : ℝ) : WithTop ℝ) < τ ζ := hGall ζ hζ t
    obtain ⟨hint, heq⟩ := hsq (t : ℝ) t.2 htτ
    have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) (t : ℝ),
        s21f_b d N s a β r (s21p_glob G Y (Real.toNNReal r) ζ) = s21f_b d N s a β r (Y r ζ) :=
      fun r hr => by
        rw [s21p_glob_of_mem hζ, Real.coe_toNNReal r hr.1]
    have hintE : IntegrableOn (fun r : ℝ => s21f_b d N s a β r (s21p_glob G Y (Real.toNNReal r) ζ))
        (Set.Icc 0 (t : ℝ)) := hint.congr_fun (fun r hr => (hcongr r hr).symm) measurableSet_Icc
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integrable_comp hintE
    · have hIi : (∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          particleDriftW (quadraticGradientDyn d s a β)
            (s21p_glob G Y (Real.toNNReal r) ζ) i) =
          (∫ r in Set.Icc (0 : ℝ) (t : ℝ), s21f_b d N s a β r (Y r ζ)) i := by
        rw [ssp1_integral_apply hint i]
        exact setIntegral_congr_fun measurableSet_Icc (fun r hr => congrFun (hcongr r hr) i)
      have h3 := congrFun heq i
      simp only [ofNNRealTime_apply, Real.toNNReal_coe] at h3
      rw [ssp1_noise_eq β⁻¹ (fun i j => hw t i j)] at h3
      have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
      simp only [Pi.add_apply, Pi.smul_apply] at h3
      show s21p_glob G Y t ζ i = s21p_glob G Y 0 ζ i + _ +
        Real.sqrt (2 * β⁻¹) • (W t ζ i - W 0 ζ i)
      rw [s21p_glob_of_mem hζ, hX'0, hW0i, sub_zero, hIi]
      simp only [hζ, ite_true]
      exact h3
  · -- no collisions
    filter_upwards [hGae] with ζ hζ t _
    rw [s21p_glob_of_mem hζ]
    exact hYU ζ hζ t

end HRS.MS.S21
