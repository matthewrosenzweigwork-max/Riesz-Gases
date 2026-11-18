import HRS.MP.SelfSimP1Free
import HRS.MS.WsStatAux16

/-!
# S21 packet FS: the filtered version of a collision-free strong solution of the quadratic gradient dynamics

`s21f_filtered`: for `d >= 2`, `N >= 2`, `T > 0` and a collision-free strong solution `X` of `quadraticGradientDyn d s a beta` driven by a
vector Brownian motion `W` with `X_0` independent of `W` (and `X_0` a.s. collision free, which follows from `no_collision` at `t = 0`),
there are a Brownian filtration `F` (the augmented filtration of `(X_0, W')`), the coordinates `W'` and an everywhere continuous
modification `X'` of `X` (`X'_t = X_t` a.s. for `t <= T`) that is again an `IsWholeStrongSolution` and moreover an
`IsWholeFilteredSolution` for `(F, W')`.

This is `ss_P1_free` (S.A.28 packet P1, confinement `V = 0`) with the drift `b - grad V`, `V = confinement a` (a smooth gradient, so the
drift is still `C^1` on the collision-free set): the proof is the same line by line (maximal solution `exists_sde_solution_maximal`,
deterministic domination `ssp1_det_domination`, freezing device).  The frozen statement of S2.1 (i) does not carry a filtration, so this
step is needed to apply the S5 machinery (`IsWholeFilteredSolution` is a hypothesis of `general_paths`, repair P10, but not of S2.1 (i)).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP1
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

variable {d N : ℕ}

/-- The drift as a vector field on `EucConfig d N`. -/
def s21f_b (d N : ℕ) (s a β : ℝ) : ℝ → EucConfig d N → EucConfig d N :=
  fun _ Ξ i => particleDriftW (quadraticGradientDyn d s a β) Ξ i

theorem s21f_drift_contDiffOn (s a β : ℝ) :
    ContDiffOn ℝ 1 (fun Ξ : EucConfig d N => s21f_b d N s a β 0 Ξ) (ssp1_U d N) := by
  have hMv : ContDiff ℝ 1 (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (-1 : Matrix (Fin d) (Fin d) ℝ))).contDiff
  refine contDiffOn_pi.2 fun i => ?_
  have hV : ∀ x : Euc d, gradient (quadraticGradientDyn d s a β).V x = a • x := fun x =>
    movtr_gradient_confinement a x
  have e : (fun Ξ : EucConfig d N => s21f_b d N s a β 0 Ξ i) = fun Ξ =>
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (Ξ i - Ξ j)) - a • Ξ i := by
    funext Ξ
    simp only [s21f_b, particleDriftW, hV]
    rfl
  show ContDiffOn ℝ 1 (fun Ξ : EucConfig d N => s21f_b d N s a β 0 Ξ i) (ssp1_U d N)
  rw [e]
  refine ContDiffOn.sub (ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)) ?_
  · have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    refine hMv.comp_contDiffOn ((ssp1_rkg_contDiffOn (d := d) s).comp
      (f := fun Ξ : EucConfig d N => Ξ i - Ξ j) ?_ ?_)
    · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
    · intro Ξ hΞ h
      exact hΞ ⟨i, j, hij, sub_eq_zero.1 h⟩
  · exact ((contDiff_apply ℝ (Euc d) i).const_smul a).contDiffOn

theorem s21f_locLipschitz (s a β : ℝ) :
    IsLocLipschitzDrift (ssp1_U d N) (s21f_b d N s a β) := by
  have hC := s21f_drift_contDiffOn (d := d) (N := N) s a β
  refine ⟨?_, fun K hKc hKU T => ?_⟩
  · exact hC.continuousOn.comp continuousOn_snd (fun p hp => hp.2)
  · have hloc : LocallyLipschitzOn K (fun Ξ : EucConfig d N => s21f_b d N s a β 0 Ξ) := by
      intro x hx
      obtain ⟨L, t, ht, hL⟩ := ((hC x (hKU hx)).contDiffAt
        ((ssp1_isOpen_U d N).mem_nhds (hKU hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
    obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
    exact ⟨L, fun _ _ => hL⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem s21f_filtered (hd : 1 ≤ d) (s a β : ℝ) (N : ℕ) (hN : 2 ≤ N) (T : ℝ) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hinit_meas : Measurable X₀) (hinit_distinct : ∀ᵐ ζ ∂P, X₀ ζ ∉ eucCollisionSet d N)
    (hbrownian : IsVectorBrownian P W) (hindep : IndepFun X₀ (fun ζ => fun t => W t ζ) P)
    (hS : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t) ∧
      IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X' ∧
      IsWholeFilteredSolution P ℱ W' W X' := by
  classical
  obtain ⟨ℱ, W', hBF, hcomp, hWW', hX₀ℱ, -, -⟩ := ssp1_base P W hbrownian X₀ hinit_meas hindep
  have hcoll : MeasurableSet (eucCollisionSet d N) := (ssp1_isClosed_coll d N).measurableSet
  obtain ⟨ω₀, hω₀⟩ := hinit_distinct.exists
  -- an `ℱ_0`-measurable collision-free initial datum
  let Y₀ : Ω → EucConfig d N := fun ζ => if X₀ ζ ∈ eucCollisionSet d N then X₀ ω₀ else X₀ ζ
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace Ω := ℱ t
    exact Measurable.ite (hX₀ℱ t hcoll) measurable_const (hX₀ℱ t)
  have hY₀U : ∀ ζ, Y₀ ζ ∈ ssp1_U d N := by
    intro ζ
    by_cases h : X₀ ζ ∈ eucCollisionSet d N
    · simp only [Y₀, h, ↓reduceIte]; exact hω₀
    · simp only [Y₀, h, ↓reduceIte]; exact h
  have hY₀ae : ∀ᵐ ζ ∂P, Y₀ ζ = X₀ ζ := by
    filter_upwards [hinit_distinct] with ζ h
    simp only [Y₀, h, ↓reduceIte]
  -- the maximal collision-free solution for `(ℱ, W')`
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, -⟩ := exists_sde_solution_maximal hBF
    (ssp1_U d N) (ssp1_isOpen_U d N) (s21f_b d N s a β) (s21f_locLipschitz s a β)
    (ssp1_sigma d N β⁻¹) Y₀ hY₀m hY₀U
  -- it equals `X` on `[0,T]` and lives beyond `T`
  have hkey : ∀ᵐ ζ ∂P, (T : WithTop ℝ) < τ ζ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ζ = X (Real.toNNReal t) ζ := by
    filter_upwards [hsol.isPathSolution, hS.eqn, hS.cont, hS.no_collision, hS.init, hWW',
      HRS.IsVectorBrownian.ae_zero hbrownian, hY₀ae] with ζ hpath heqn hcont hnc hinit hw hw0 hY0
    have hXc : Continuous fun t => X t ζ := continuous_pi hcont
    have hzc : Continuous fun r : ℝ => X (Real.toNNReal r) ζ := hXc.comp continuous_real_toNNReal
    have hz : IsPathSolution (s21f_b d N s a β) (ssp1_sigma d N β⁻¹) (fun t => W' t ζ) (Y₀ ζ)
        (T : WithTop ℝ) (fun r => X (Real.toNNReal r) ζ) := by
      refine ⟨by simp only [Real.toNNReal_zero]; rw [hinit, hY0], fun t ht htT => ?_⟩
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
      rw [hW0i, sub_zero, hinit, ← hY0] at h3
      rw [ssp1_noise_eq β⁻¹ (fun i j => hw (Real.toNNReal t) i j)]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [h2]
      exact h3
    have hzU : ∀ t ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal t) ζ ∈ ssp1_U d N := fun t ht =>
      hnc (Real.toNNReal t) (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
    exact ssp1_det_domination (ssp1_isOpen_U d N) (s21f_locLipschitz s a β) (hBF.cont ζ) hT
      (hpos ζ) hpath (fun t ht htτ => hmem ζ t ht htτ)
      (fun h K hK hKU t₀ ht₀ => hexit ζ h K hK hKU t₀ ht₀) hz hzc.continuousOn hzU
  -- the good set
  obtain ⟨G, hGm, hG0, hG⟩ := ssp1_exists_measurable_good P
    (p := fun ζ => (T : WithTop ℝ) < τ ζ) (hkey.mono fun ζ h => h.1)
  have hGt : ∀ t : ℝ, MeasurableSet[ℱ t] G := ssp1_measurableSet_of_null_compl hcomp hGm hG0
  have hGae : ∀ᵐ ζ ∂P, ζ ∈ G := by
    rw [ae_iff]; exact hG0
  have hYcont : ∀ ζ ∈ G, ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T) := fun ζ hζ =>
    hsol.cont ζ T hT.le (hG ζ hζ)
  have hYU : ∀ ζ ∈ G, ∀ t : ℝ≥0, (t : ℝ) ≤ T → Y t ζ ∈ ssp1_U d N := fun ζ hζ t ht =>
    hmem ζ t t.2 (lt_of_le_of_lt (by exact_mod_cast ht) (hG ζ hζ))
  have hX'eq : ∀ ζ ∈ G, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ssp1_freeze T G Y (Real.toNNReal t) ζ = Y t ζ := fun ζ hζ t ht0 htT => by
    rw [ssp1_freeze_of_le (by rw [Real.coe_toNNReal t ht0]; exact htT) hζ, Real.coe_toNNReal t ht0]
  have hX'0 : ∀ ζ ∈ G, ssp1_freeze T G Y 0 ζ = Y₀ ζ := fun ζ hζ => by
    have := hX'eq ζ hζ 0 le_rfl hT.le
    simpa [hsol.init ζ] using this
  have h2 : ∀ᵐ ζ ∂P, ssp1_freeze T G Y 0 ζ = X₀ ζ := by
    filter_upwards [hGae, hY₀ae] with ζ hζ hY0
    rw [hX'0 ζ hζ, hY0]
  have hX'adapt : ∀ t : ℝ≥0, Measurable[ℱ t] (ssp1_freeze T G Y t) :=
    ssp1_freeze_adapted hGt hsol.adapted
  have hmod : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ssp1_freeze T G Y t =ᵐ[P] X t := by
    intro t ht
    filter_upwards [hkey, hGae] with ζ hk hζ
    rw [ssp1_freeze_of_le ht hζ, hk.2 t ⟨t.2, ht⟩, Real.toNNReal_coe]

  have hprog : IsProgressive ℱ (ofNNRealTime (ssp1_freeze T G Y)) := by
    refine ssp1_isProgressive_of_continuous hX'adapt (fun t => ?_)
      (ssp1_freeze_continuous hT.le hYcont)
    have e : ssp1_freeze T G Y 0 = fun ζ => if ζ ∈ G then Y₀ ζ else 0 := by
      funext ζ
      by_cases hζ : ζ ∈ G
      · rw [hX'0 ζ hζ]; simp [hζ]
      · rw [ssp1_freeze_of_notMem hζ]; simp [hζ]
    rw [e]
    let _ : MeasurableSpace Ω := ℱ t
    exact Measurable.ite (hGt t) (hY₀m t) measurable_const

  have hcont : ∀ ζ, Continuous fun t => ssp1_freeze T G Y t ζ := ssp1_freeze_continuous hT.le hYcont
  have heqn : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun r : ℝ => particleDriftW (quadraticGradientDyn d s a β)
        (ssp1_freeze T G Y (Real.toNNReal r) ζ) i) (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, ssp1_freeze T G Y t ζ i = ssp1_freeze T G Y 0 ζ i +
        (∫ r in Set.Icc (0 : ℝ) t, particleDriftW (quadraticGradientDyn d s a β)
          (ssp1_freeze T G Y (Real.toNNReal r) ζ) i) +
        Real.sqrt (2 * (quadraticGradientDyn d s a β).invβ) • (W t ζ i - W 0 ζ i) := by
    filter_upwards [hsol.eq, hGae, hWW', HRS.IsVectorBrownian.ae_zero hbrownian] with ζ hsq hζ hw hw0 t ht
    have htτ : ((t : ℝ) : WithTop ℝ) < τ ζ := lt_of_le_of_lt (by exact_mod_cast ht) (hG ζ hζ)
    obtain ⟨hint, heq⟩ := hsq (t : ℝ) t.2 htτ
    have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) (t : ℝ),
        s21f_b d N s a β r (ssp1_freeze T G Y (Real.toNNReal r) ζ) = s21f_b d N s a β r (Y r ζ) :=
      fun r hr => by rw [hX'eq ζ hζ r hr.1 (hr.2.trans ht)]
    have hintE : IntegrableOn (fun r : ℝ => s21f_b d N s a β r (ssp1_freeze T G Y (Real.toNNReal r) ζ))
        (Set.Icc 0 (t : ℝ)) := hint.congr_fun (fun r hr => (hcongr r hr).symm) measurableSet_Icc
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integrable_comp hintE
    · have hIi : (∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          particleDriftW (quadraticGradientDyn d s a β)
            (ssp1_freeze T G Y (Real.toNNReal r) ζ) i) =
          (∫ r in Set.Icc (0 : ℝ) (t : ℝ), s21f_b d N s a β r (Y r ζ)) i := by
        rw [ssp1_integral_apply hint i]
        exact setIntegral_congr_fun measurableSet_Icc (fun r hr => congrFun (hcongr r hr) i)
      have h3 := congrFun heq i
      simp only [ofNNRealTime_apply, Real.toNNReal_coe] at h3
      rw [ssp1_noise_eq β⁻¹ (fun i j => hw t i j)] at h3
      have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
      have hXt := ssp1_freeze_of_le (T := T) (Y := Y) ht hζ
      simp only [Pi.add_apply, Pi.smul_apply] at h3
      show ssp1_freeze T G Y t ζ i = ssp1_freeze T G Y 0 ζ i + _ +
        Real.sqrt (2 * β⁻¹) • (W t ζ i - W 0 ζ i)
      rw [hXt, hX'0 ζ hζ, hW0i, sub_zero, hIi]
      exact h3

  have hnc : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ssp1_freeze T G Y t ζ ∉ eucCollisionSet d N := by
    filter_upwards [hGae] with ζ hζ t ht
    rw [ssp1_freeze_of_le ht hζ]
    exact hYU ζ hζ t ht


  exact ⟨ssp1_freeze T G Y, ℱ, W', hmod, ⟨h2, heqn, Filter.Eventually.of_forall fun ζ i =>
    (continuous_apply i).comp (hcont ζ), fun t => (hX'adapt t).mono (ℱ.le t) le_rfl, hnc⟩,
    ⟨hBF, hWW', hX'adapt, hprog⟩⟩

end HRS.MS.S21
