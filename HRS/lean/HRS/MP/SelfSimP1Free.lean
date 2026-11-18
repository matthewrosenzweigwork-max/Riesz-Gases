import HRS.MP.SelfSimP1Base
import HRS.MP.SelfSimSpec

/-!
# S.A.28 packet P1, collision-free branch (`ss_P1_free`)

`ss_P1_filtered_version` of `HRS/MP/SelfSimSpec.lean` for the first alternative of `SelectedFlowRd.flow`
(collision-free strong solution).  Route (shorter than the regularisation of the spec): the particle drift is
`C¹` (hence locally Lipschitz) on the open collision-free set `U`; the maximal strong solution `(τ, Y)` in `U`
for the Brownian filtration of `(X₀, W')` (`exists_sde_solution_maximal`) coincides path by path with the given
collision-free solution `X` on `[0,T]` (deterministic uniqueness `ode_additive_unique`), and `τ > T` a.s.
(`X([0,T])` is a compact subset of `U` and `Y` leaves every compact subset of `U` before `τ`).  The modification
`X'` is `Y` frozen after `T` on a measurable set of full measure (`ssp1_freeze`), `0` off it.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP1

variable {d N : ℕ}

/-! ### The drift and the noise vectors -/

/-- The collision-free configurations. -/
def ssp1_U (d N : ℕ) : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ

theorem ssp1_isClosed_coll (d N : ℕ) : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i, ⋃ j, ⋃ _ : i ≠ j, {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => ?_
  exact isClosed_eq (continuous_apply i) (continuous_apply j)

theorem ssp1_isOpen_U (d N : ℕ) : IsOpen (ssp1_U d N) := (ssp1_isClosed_coll d N).isOpen_compl

/-- The dynamics of the spec: `M = -1`, `V = 0`. -/
def ssp1_D (d : ℕ) (s invβ : ℝ) : WholeDyn d := ⟨s, -1, fun _ => 0, invβ⟩

/-- The drift as a vector field on `EucConfig d N`. -/
def ssp1_b (d N : ℕ) (s invβ : ℝ) : ℝ → EucConfig d N → EucConfig d N :=
  fun _ Ξ i => particleDriftW (ssp1_D d s invβ) Ξ i

/-- The noise vectors `σ_{(i,j)} = √(2 invβ) e_{i,j}`. -/
def ssp1_sigma (d N : ℕ) (invβ : ℝ) (ij : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * invβ) • Pi.single ij.1 (EuclideanSpace.single ij.2 1)

theorem ssp1_sum_sigma (invβ : ℝ) (w : (Fin N × Fin d) → ℝ) :
    ∑ ij, w ij • ssp1_sigma d N invβ ij =
      Real.sqrt (2 * invβ) • (fun i : Fin N => (WithLp.toLp 2 fun j => w (i, j) : Euc d)) := by
  funext i
  ext j
  simp [ssp1_sigma, Pi.single_apply, Fintype.sum_prod_type, Finset.sum_apply, mul_comm]

theorem ssp1_gradient_zero : gradient (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by
  funext x; simp [gradient]

/-- `∇g` is smooth off the origin. -/
theorem ssp1_rkg_contDiffOn (s : ℝ) :
    ContDiffOn ℝ 1 (rieszKernelGrad d s) {x : Euc d | x ≠ 0} := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (rieszKernel d s)) {x : Euc d | x ≠ 0} :=
    (rieszKernel_contDiffOn (d := d) (s := s)).fderiv_of_isOpen isOpen_ne (by norm_num)
  have : rieszKernelGrad d s =
      (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (rieszKernel d s) := by
    funext x; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h1

/-- The drift is `C¹` on the collision-free set. -/
theorem ssp1_drift_contDiffOn (s invβ : ℝ) :
    ContDiffOn ℝ 1 (fun Ξ : EucConfig d N => ssp1_b d N s invβ 0 Ξ) (ssp1_U d N) := by
  have hMv : ContDiff ℝ 1 (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (-1 : Matrix (Fin d) (Fin d) ℝ))).contDiff
  refine contDiffOn_pi.2 fun i => ?_
  have e : (fun Ξ : EucConfig d N => ssp1_b d N s invβ 0 Ξ i) = fun Ξ =>
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (Ξ i - Ξ j)) := by
    funext Ξ
    simp only [ssp1_b, particleDriftW, ssp1_D, ssp1_gradient_zero, sub_zero]
  show ContDiffOn ℝ 1 (fun Ξ : EucConfig d N => ssp1_b d N s invβ 0 Ξ i) (ssp1_U d N)
  rw [e]
  refine ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)
  have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
  refine hMv.comp_contDiffOn ((ssp1_rkg_contDiffOn (d := d) s).comp
    (f := fun Ξ : EucConfig d N => Ξ i - Ξ j) ?_ ?_)
  · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
  · intro Ξ hΞ h
    exact hΞ ⟨i, j, hij, sub_eq_zero.1 h⟩

/-- The drift is continuous and locally Lipschitz on the collision-free set. -/
theorem ssp1_locLipschitz (s invβ : ℝ) :
    IsLocLipschitzDrift (ssp1_U d N) (ssp1_b d N s invβ) := by
  have hC := ssp1_drift_contDiffOn (d := d) (N := N) s invβ
  refine ⟨?_, fun K hKc hKU T => ?_⟩
  · exact hC.continuousOn.comp continuousOn_snd (fun p hp => hp.2)
  · have hloc : LocallyLipschitzOn K (fun Ξ : EucConfig d N => ssp1_b d N s invβ 0 Ξ) := by
      intro x hx
      obtain ⟨L, t, ht, hL⟩ := ((hC x (hKU hx)).contDiffAt
        ((ssp1_isOpen_U d N).mem_nhds (hKU hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
    obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
    exact ⟨L, fun _ _ => hL⟩

/-! ### The deterministic domination step -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- If a path solution `z` on `[0,T)` stays (with its closure `z([0,T])`) in the open set `U` and a maximal
`U`-valued solution `y` of lifetime `τ` leaves every compact subset of `U` before `τ`, then `T < τ` and
`y = z` on `[0,T]`. -/
theorem ssp1_det_domination {U : Set E} (hU : IsOpen U) {b : ℝ → E → E} (hb : IsLocLipschitzDrift U b)
    {σ : ι → E} {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) {y₀ : E} {τ : WithTop ℝ} {y z : ℝ → E}
    {T : ℝ} (hT : 0 < T) (hpos : 0 < τ)
    (hy : IsPathSolution b σ w y₀ τ y) (hyU : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ U)
    (hexit : τ < ⊤ → ∀ K : Set E, IsCompact K → K ⊆ U → ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ∧ y t ∉ K)
    (hz : IsPathSolution b σ w y₀ (T : WithTop ℝ) z) (hzc : ContinuousOn z (Set.Icc 0 T))
    (hzU : ∀ t ∈ Set.Icc (0 : ℝ) T, z t ∈ U) :
    (T : WithTop ℝ) < τ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, y t = z t := by
  have huniq := ode_additive_unique U hU b hb σ w hw y₀ hy hz hyU
    (fun t ht htT => hzU t ⟨ht, (WithTop.coe_lt_coe.1 htT).le⟩)
  have hTτ : (T : WithTop ℝ) < τ := by
    by_contra hcon
    have hτT : τ ≤ (T : WithTop ℝ) := not_lt.1 hcon
    have hτtop : τ < ⊤ := lt_of_le_of_lt hτT (WithTop.coe_lt_top T)
    have hK : IsCompact (z '' Set.Icc 0 T) := isCompact_Icc.image_of_continuousOn hzc
    obtain ⟨t, ht0, htτ, htK⟩ := hexit hτtop _ hK (by rintro _ ⟨u, hu, rfl⟩; exact hzU u hu) 0
      (by simpa using hpos)
    have htT : t < T := WithTop.coe_lt_coe.1 (lt_of_lt_of_le htτ hτT)
    exact htK ⟨t, ⟨ht0.le, htT.le⟩, (huniq t ht0.le (lt_min htτ (WithTop.coe_lt_coe.2 htT))).symm⟩
  refine ⟨hTτ, ?_⟩
  have hyc : ContinuousOn y (Set.Icc 0 T) := (hy.2 T hT.le hTτ).1
  have hEq : Set.EqOn y z (Set.Ico 0 T) := fun t ht =>
    huniq t ht.1 (lt_min (lt_of_le_of_lt (by exact_mod_cast ht.2.le) hTτ) (WithTop.coe_lt_coe.2 ht.2))
  exact Set.EqOn.of_subset_closure hEq hyc hzc Set.Ico_subset_Icc_self
    (by rw [closure_Ico hT.ne])

end Det

/-! ### Coordinates of the equation -/

theorem ssp1_noise_eq (invβ : ℝ) {w' : (Fin N × Fin d) → ℝ} {w : Fin N → Euc d}
    (h : ∀ i j, w' (i, j) = w i j) :
    ∑ ij, w' ij • ssp1_sigma d N invβ ij = Real.sqrt (2 * invβ) • w := by
  rw [ssp1_sum_sigma]
  congr 1
  funext i
  ext j
  exact h i j

theorem ssp1_integral_apply {f : ℝ → EucConfig d N} {S : Set ℝ} (hf : IntegrableOn f S) (i : Fin N) :
    (∫ r in S, f r) i = ∫ r in S, f r i := by
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm hf
  simpa using this.symm

/-! ### The main theorem -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Packet P1, collision-free branch.**  The conclusion of `ss_P1_filtered_version` for a pathwise unique
collision-free strong solution (the pathwise-uniqueness hypothesis is not needed: the maximal solution of
the SDE in the collision-free set is compared with `X` path by path). -/
theorem ss_P1_free (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hinit_meas : Measurable X₀) (hinit_distinct : ∀ᵐ ζ ∂P, X₀ ζ ∉ eucCollisionSet d N)
    (hbrownian : IsVectorBrownian P W) (hindep : IndepFun X₀ (fun ζ => fun t => W t ζ) P)
    (h1 : IsWholeStrongSolution P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X ∧
      WholePathwiseUnique P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t) ∧ (∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ) ∧
      SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
        T ℱ W' W X' ∧
      SSNoCollision P T X' := by
  classical
  obtain ⟨hS, -⟩ := h1
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
    (ssp1_U d N) (ssp1_isOpen_U d N) (ssp1_b d N s invβ) (ssp1_locLipschitz s invβ)
    (ssp1_sigma d N invβ) Y₀ hY₀m hY₀U
  -- it equals `X` on `[0,T]` and lives beyond `T`
  have hkey : ∀ᵐ ζ ∂P, (T : WithTop ℝ) < τ ζ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ζ = X (Real.toNNReal t) ζ := by
    filter_upwards [hsol.isPathSolution, hS.eqn, hS.cont, hS.no_collision, hS.init, hWW',
      HRS.IsVectorBrownian.ae_zero hbrownian, hY₀ae] with ζ hpath heqn hcont hnc hinit hw hw0 hY0
    have hXc : Continuous fun t => X t ζ := continuous_pi hcont
    have hzc : Continuous fun r : ℝ => X (Real.toNNReal r) ζ := hXc.comp continuous_real_toNNReal
    have hz : IsPathSolution (ssp1_b d N s invβ) (ssp1_sigma d N invβ) (fun t => W' t ζ) (Y₀ ζ)
        (T : WithTop ℝ) (fun r => X (Real.toNNReal r) ζ) := by
      refine ⟨by simp only [Real.toNNReal_zero]; rw [hinit, hY0], fun t ht htT => ?_⟩
      have htT' : t < T := WithTop.coe_lt_coe.1 htT
      have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
      obtain ⟨hint, heq⟩ := heqn (Real.toNNReal t) (by rw [ht']; exact htT'.le)
      rw [ht'] at hint heq
      have hintE : IntegrableOn (fun r : ℝ => ssp1_b d N s invβ r (X (Real.toNNReal r) ζ))
          (Set.Icc 0 t) := Integrable.of_eval hint
      refine ⟨hzc.continuousOn, hintE, ?_⟩
      funext i
      have h2 := ssp1_integral_apply hintE i
      have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
      have h3 := heq i
      rw [hW0i, sub_zero, hinit, ← hY0] at h3
      rw [ssp1_noise_eq invβ (fun i j => hw (Real.toNNReal t) i j)]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [h2]
      exact h3
    have hzU : ∀ t ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal t) ζ ∈ ssp1_U d N := fun t ht =>
      hnc (Real.toNNReal t) (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
    exact ssp1_det_domination (ssp1_isOpen_U d N) (ssp1_locLipschitz s invβ) (hBF.cont ζ) hT
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
  refine ⟨ssp1_freeze T G Y, ℱ, W', ?_, h2, ⟨⟨hBF, hWW', hX'adapt, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- modification
    intro t ht
    filter_upwards [hkey, hGae] with ζ hk hζ
    rw [ssp1_freeze_of_le ht hζ, hk.2 t ⟨t.2, ht⟩, Real.toNNReal_coe]
  · -- progressive
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
  · -- continuity
    exact ssp1_freeze_continuous hT.le hYcont
  · -- distinct start
    filter_upwards [h2, hinit_distinct] with ζ h h'
    rw [h]; exact h'
  · -- the integrated equation
    filter_upwards [hsol.eq, hGae, hWW', HRS.IsVectorBrownian.ae_zero hbrownian] with ζ hsq hζ hw hw0 t ht
    have htτ : ((t : ℝ) : WithTop ℝ) < τ ζ := lt_of_le_of_lt (by exact_mod_cast ht) (hG ζ hζ)
    obtain ⟨hint, heq⟩ := hsq (t : ℝ) t.2 htτ
    have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) (t : ℝ),
        ssp1_b d N s invβ r (ssp1_freeze T G Y (Real.toNNReal r) ζ) = ssp1_b d N s invβ r (Y r ζ) :=
      fun r hr => by rw [hX'eq ζ hζ r hr.1 (hr.2.trans ht)]
    have hintE : IntegrableOn (fun r : ℝ => ssp1_b d N s invβ r (ssp1_freeze T G Y (Real.toNNReal r) ζ))
        (Set.Icc 0 (t : ℝ)) := hint.congr_fun (fun r hr => (hcongr r hr).symm) measurableSet_Icc
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integrable_comp hintE
    · have hIi : (∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d)
            (ssp1_freeze T G Y (Real.toNNReal r) ζ) i) =
          (∫ r in Set.Icc (0 : ℝ) (t : ℝ), ssp1_b d N s invβ r (Y r ζ)) i := by
        rw [ssp1_integral_apply hint i]
        exact setIntegral_congr_fun measurableSet_Icc (fun r hr => congrFun (hcongr r hr) i)
      have h3 := congrFun heq i
      simp only [ofNNRealTime_apply, Real.toNNReal_coe] at h3
      rw [ssp1_noise_eq invβ (fun i j => hw t i j)] at h3
      have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
      have hXt := ssp1_freeze_of_le (T := T) (Y := Y) ht hζ
      simp only [Pi.add_apply, Pi.smul_apply] at h3
      show ssp1_freeze T G Y t ζ i = ssp1_freeze T G Y 0 ζ i + _ +
        Real.sqrt (2 * invβ) • (W t ζ i - W 0 ζ i)
      rw [hXt, hX'0 ζ hζ, hW0i, sub_zero, hIi]
      exact h3
  · -- null contact occupation
    filter_upwards [hGae] with ζ hζ
    have : {r : ℝ | r ∈ Set.Icc 0 T ∧ ssp1_freeze T G Y (Real.toNNReal r) ζ ∈ eucCollisionSet d N} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hr
      rw [hX'eq ζ hζ r hr.1 hr.2]
      exact hmem ζ r hr.1 (lt_of_le_of_lt (by exact_mod_cast hr.2) (hG ζ hζ))
    rw [this]; exact measure_empty
  · -- no collision
    filter_upwards [hGae] with ζ hζ t ht
    rw [ssp1_freeze_of_le ht hζ]
    exact hYU ζ hζ t ht

end Main

end HRS.MP.SelfSimP1
