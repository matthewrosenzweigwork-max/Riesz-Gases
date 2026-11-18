import HRS.MS.MfeConfAux15
import HRS.MP.SelfSimP4Reg

/-!
# S.B.1, packet F4: regularised strong solutions `X^M = X` on `[0,S]` for the confined particle system

Whole-space transplant of `HRS.MP.SelfSimP4Impl.p4_regularised_flow_proof` to the particle drift
`b(Ξ)_i = -(1/N)∑_{j≠i} ∇g(ξ_i-ξ_j) - ∇V(ξ_i)` (`M = -I`) with `V ∈ C³`, `‖D²V‖ ≤ B` (so that `∇V` is globally Lipschitz) and the
truncated kernels `g_M` (`IsP4Kernel`, from `p4_kernel_proof`):

* `sb1DriftM D k N`: the regularised drift; `sb1_particleDrift_eq`: for `k = g` it is `particleDriftW`;
* `sb1_driftM_isLip`: it is globally Lipschitz;
* `sb1_ident`: if `X` is a collision-free strong solution on `[0,S]` and `Y^M` are the global strong solutions with the same noise
  and initial value, then a.s. `Y^M = X` on `[0,S]` for all `M ≥ M(ω)`;
* `sb1_regularised_flow`: hence the setwise convergence of the laws (the hypothesis of the entropy lower semicontinuity step).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-- The regularised drift `b_k(Ξ)_i = -(1/N) ∑_{j≠i} ∇k(ξ_i-ξ_j) - ∇V(ξ_i)`. -/
def sb1DriftM (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (Ξ : Whole.EucConfig d N) :
    Whole.EucConfig d N :=
  fun i => -((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j)) - gradient D.V (Ξ i)

theorem sb1_particleDrift_eq (D : Whole.WholeDyn d) (hM : D.M = -1) (N : ℕ) :
    Whole.particleDriftW (N := N) D = sb1DriftM D (Whole.rieszKernel d D.s) N := by
  funext Ξ i
  unfold Whole.particleDriftW sb1DriftM
  rw [hM]
  simp only [sb1_matVec_neg_one, Finset.sum_neg_distrib, smul_neg]
  rfl

theorem sb1_driftM_eq (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ)
    (Ξ : Whole.EucConfig d N) (hΞ : ∀ i j, i ≠ j → r₀ < ‖Ξ i - Ξ j‖) :
    sb1DriftM D k N Ξ = sb1DriftM D (Whole.rieszKernel d s) N Ξ := by
  have hg : ∀ x : Euc d, r₀ < ‖x‖ → gradient k x = gradient (Whole.rieszKernel d s) x := by
    intro x hx
    have hev : k =ᶠ[𝓝 x] Whole.rieszKernel d s := by
      have : {y : Euc d | r₀ < ‖y‖} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_norm).mem_nhds hx
      filter_upwards [this] with y hy using hk.eq_far y hy.le
    unfold gradient
    rw [hev.fderiv_eq]
  have hs : ∀ i, ∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) =
      ∑ j ∈ Finset.univ.erase i, gradient (Whole.rieszKernel d s) (Ξ i - Ξ j) := fun i =>
    Finset.sum_congr rfl fun j hj => hg _ (hΞ i j (Finset.ne_of_mem_erase hj).symm)
  funext i
  simp only [sb1DriftM, hs i]

theorem sb1_gradV_lip {V : Euc d → ℝ} {B : ℝ} (P : Sb1Pot V B) :
    LipschitzWith (Real.toNNReal B) (gradient V) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (P.c3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ V) (s := Set.univ) (C := B)
    (fun z _ => hd z) (fun z _ => by rw [sb1_norm_fderiv_fderiv]; exact P.bd z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  have e : gradient V x - gradient V y = (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ V x - fderiv ℝ V y) := by
    unfold gradient; simp
  rw [dist_eq_norm, dist_eq_norm, e, LinearIsometryEquiv.norm_map, Real.coe_toNNReal _ P.B_nonneg]
  exact h

theorem sb1_driftM_lip (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {B : ℝ} (P : Sb1Pot D.V B) (N : ℕ) :
    ∃ K : ℝ≥0, LipschitzWith K (sb1DriftM D k N) := by
  obtain ⟨K1, hK1⟩ := p4k_drift_lip_gen hk N 1
  have hK := hK1 0 (by unfold HRS.Whole.AppendixALemmas.aSelfSim; simp)
  have hVl := sb1_gradV_lip P
  have ha0 : HRS.Whole.AppendixALemmas.aSelfSim s 0 = 1 := by
    unfold HRS.Whole.AppendixALemmas.aSelfSim; simp
  have hi : ∀ (Ψ : Whole.EucConfig d N) (i : Fin N), sb1DriftM D k N Ψ i =
      p4Drift k s N 0 Ψ i + (1 / 2 : ℝ) • Ψ i - gradient D.V (Ψ i) := by
    intro Ψ i
    unfold sb1DriftM p4Drift
    rw [ha0]
    abel
  refine ⟨K1 + 1 + Real.toNNReal B, LipschitzWith.of_dist_le_mul fun Ξ Ξ' => ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have a1 : dist (p4Drift k s N 0 Ξ i) (p4Drift k s N 0 Ξ' i) ≤ K1 * dist Ξ Ξ' :=
    (dist_le_pi_dist _ _ i).trans (hK.dist_le_mul Ξ Ξ')
  have a2 : dist (Ξ i) (Ξ' i) ≤ dist Ξ Ξ' := dist_le_pi_dist Ξ Ξ' i
  have a3 : dist (gradient D.V (Ξ i)) (gradient D.V (Ξ' i)) ≤ Real.toNNReal B * dist (Ξ i) (Ξ' i) :=
    hVl.dist_le_mul _ _
  rw [hi Ξ i, hi Ξ' i]
  have hd0 : 0 ≤ dist Ξ Ξ' := dist_nonneg
  have a4 : dist ((1 / 2 : ℝ) • Ξ i) ((1 / 2 : ℝ) • Ξ' i) ≤ dist Ξ Ξ' := by
    rw [dist_smul₀]
    simp only [norm_div, norm_one, Real.norm_ofNat]
    nlinarith
  calc dist (p4Drift k s N 0 Ξ i + (1 / 2 : ℝ) • Ξ i - gradient D.V (Ξ i))
        (p4Drift k s N 0 Ξ' i + (1 / 2 : ℝ) • Ξ' i - gradient D.V (Ξ' i))
      ≤ dist (p4Drift k s N 0 Ξ i + (1 / 2 : ℝ) • Ξ i) (p4Drift k s N 0 Ξ' i + (1 / 2 : ℝ) • Ξ' i) +
        dist (gradient D.V (Ξ i)) (gradient D.V (Ξ' i)) := dist_sub_sub_le _ _ _ _
    _ ≤ (dist (p4Drift k s N 0 Ξ i) (p4Drift k s N 0 Ξ' i) +
          dist ((1 / 2 : ℝ) • Ξ i) ((1 / 2 : ℝ) • Ξ' i)) +
        dist (gradient D.V (Ξ i)) (gradient D.V (Ξ' i)) :=
        add_le_add (dist_add_add_le _ _ _ _) le_rfl
    _ ≤ (K1 * dist Ξ Ξ' + dist Ξ Ξ') + Real.toNNReal B * dist Ξ Ξ' := by
        refine add_le_add (add_le_add a1 a4) (a3.trans ?_)
        exact mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = ((K1 + 1 + Real.toNNReal B : ℝ≥0) : ℝ) * dist Ξ Ξ' := by push_cast; ring

theorem sb1_driftM_isLip (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {B : ℝ} (P : Sb1Pot D.V B) (N : ℕ) : HRS.IsLipschitzDrift (fun _ : ℝ => sb1DriftM D k N) := by
  obtain ⟨K, hK⟩ := sb1_driftM_lip D hk P N
  exact ⟨(hK.continuous.comp continuous_snd).continuousOn, fun T => ⟨K, fun t _ => hK⟩⟩

/-- **Identification** `Y^M = X` on `[0,S]` for `M ≥ M(ω)`. -/
theorem sb1_ident (D : Whole.WholeDyn d) (hM : D.M = -1) {B : ℝ} (P : Sb1Pot D.V B) {S : ℝ} (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D S X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d D.s (1 / ((M : ℝ) + 1)) (gM M))
    {Ys : ℕ → ℝ → Ω → Whole.EucConfig d N}
    (hYs : ∀ M, IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (gM M) N)
      (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) (Ys M)) :
    ∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ S → Ys M (t : ℝ) ζ = X t ζ := by
  have hpaths : ∀ᵐ ζ ∂Pm, ∀ M, IsPathSolution (fun _ => sb1DriftM D (gM M) N) (p4r_sigma d N D.invβ)
      (fun t => W' t ζ) (X 0 ζ) ⊤ (fun t => Ys M t ζ) :=
    ae_all_iff.2 fun M => (hYs M).isPathSolution
  filter_upwards [hX.eqn, hX.cont, hX.no_collision, hF.coords, hpaths] with ζ heqn hcont hnoc hcoord hpath
  have hcontX : Continuous fun t : ℝ≥0 => X t ζ := continuous_pi hcont
  have hsep := p4r_sep hS hcontX (fun t ht i j hij hEq => hnoc t ht ⟨i, j, hij, hEq⟩)
  filter_upwards [hsep] with M hMsep
  have hagree : ∀ r ∈ Set.Icc (0 : ℝ) S, (fun _ : ℝ => sb1DriftM D (gM M) N) r (X (Real.toNNReal r) ζ) =
      (fun _ : ℝ => Whole.particleDriftW D) r (X (Real.toNNReal r) ζ) := fun r hr => by
    show sb1DriftM D (gM M) N _ = Whole.particleDriftW D _
    rw [sb1_particleDrift_eq D hM N]
    exact sb1_driftM_eq D (hgM M) N _ (fun i j hij => hMsep i j hij (Real.toNNReal r)
      (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2))
  have hyM := p4r_isPathSolution D.invβ S (fun _ => sb1DriftM D (gM M) N) (fun t => X t ζ) hcontX
    (fun t => W' t ζ) (fun t => W t ζ) (fun t i j => hcoord t i j) (funext fun k => by
      simpa using congrFun (hF.brownian.zero ζ) k)
    (p4r_eqn_congr (b := fun _ => Whole.particleDriftW D) (y := fun t => X t ζ) (w := fun t => W t ζ)
      hagree heqn)
  have hu := ode_additive_unique Set.univ isOpen_univ (fun _ => sb1DriftM D (gM M) N)
    (sb1_driftM_isLip D (hgM M) P N).toLoc (p4r_sigma d N D.invβ) (fun t => W' t ζ)
    (hF.brownian.cont ζ) (X 0 ζ) hyM (hpath M) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  have hEq : Set.EqOn (fun u : ℝ => Ys M u ζ) (fun u : ℝ => X (Real.toNNReal u) ζ) (Set.Ico 0 S) :=
    fun u hu0 => (hu u hu0.1 (by simpa using hu0.2)).symm
  have hc1 : ContinuousOn (fun u : ℝ => Ys M u ζ) (Set.Icc 0 S) :=
    (hYs M).cont ζ S hS.le (WithTop.coe_lt_top S)
  have hc2 : ContinuousOn (fun u : ℝ => X (Real.toNNReal u) ζ) (Set.Icc 0 S) :=
    (hcontX.comp continuous_real_toNNReal).continuousOn
  have hEq' := Set.EqOn.of_subset_closure hEq hc1 hc2 Set.Ico_subset_Icc_self
    (by rw [closure_Ico hS.ne])
  intro t ht
  have := hEq' ⟨NNReal.coe_nonneg t, ht⟩
  simpa using this

/-- **F4**: regularised strong solutions, equal to `X` on `[0,S]` for `M ≥ M(ω)`, and the setwise convergence of the laws. -/
theorem sb1_regularised_flow (D : Whole.WholeDyn d) (hM : D.M = -1) {B : ℝ} (P : Sb1Pot D.V B) {S : ℝ}
    (hS : 0 < S) {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D S X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d D.s (1 / ((M : ℝ) + 1)) (gM M)) :
    ∃ YM : ℕ → ℝ≥0 → Ω → Whole.EucConfig d N,
      (∀ M, P4AddSol Pm D.invβ (fun _ => sb1DriftM D (gM M) N) S ℱ W' W (YM M)) ∧
      (∀ M ζ, YM M 0 ζ = X 0 ζ) ∧
      (∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ S → YM M t ζ = X t ζ) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ A : Set (Whole.EucConfig d N), MeasurableSet A →
        Tendsto (fun M => law Pm (YM M (Real.toNNReal τ)) A) atTop (𝓝 (law Pm (X (Real.toNNReal τ)) A)) := by
  have hW' : IsBrownianFiltration Pm (p4r_shiftFil ℱ) W' := p4r_shiftFil_brownian hF.brownian
  have hY0 : ∀ t : ℝ, Measurable[p4r_shiftFil ℱ t] (X 0) := fun t =>
    (hF.adapted 0).mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → Whole.EucConfig d N,
      IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (gM M) N) (p4r_sigma d N D.invβ)
        (X 0) (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW' _ (sb1_driftM_isLip D (hgM M) P N) _ hY0
  choose Ys hYs using hex
  have hae := sb1_ident D hM P hS hX hF hgM hYs
  refine ⟨fun M t ζ => Ys M (t : ℝ) ζ, fun M => p4r_addSol hF (hYs M),
    fun M ζ => (hYs M).init ζ, hae, ?_⟩
  intro τ hτ A hA
  have hτS : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ S := by rw [Real.coe_toNNReal _ hτ.1]; exact hτ.2
  have hmeas : ∀ M, Measurable fun ζ => Ys M ((Real.toNNReal τ : ℝ≥0) : ℝ) ζ := fun M =>
    ((hYs M).adapted _).mono ((p4r_shiftFil ℱ).le _) le_rfl
  have hmY : Measurable (X (Real.toNNReal τ)) := (hF.adapted _).mono (ℱ.le _) le_rfl
  simp only [Measure.map_apply (hmeas _) hA, Measure.map_apply hmY hA]
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop (hmY hA)
    (fun M => hmeas M hA) ?_
  filter_upwards [hae] with ζ h
  filter_upwards [h] with M hM
  simp only [Set.mem_preimage, hM _ hτS]

end HRS.MS.MfeConf
