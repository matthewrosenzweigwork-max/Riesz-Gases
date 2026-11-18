import HRS.Stochastic.Particle
import HRS.Stochastic.Bridge
import HRS.Stochastic.Wiener
import HRS.Stochastic.DDSCore
import HRS.Dynamics.ParticleWellposed
import HRS.Stochastic.SelectedFlow

/-!
# Packet E213E, L1: a global filtered strong solution on the given space

`e213e_exists_global_filtered`: for a probability space carrying a vector Brownian motion `W` and an
independent a.s. collision-free initial datum `X₀` (`d ≥ 2`, `Sym M ≤ 0`, `V ∈ C²`) there is a process `X` which is a
strong solution on every horizon `T`, driven by the given `W`, together with a Brownian filtration
`(ℱ, W')` carrying `W` to which `X` is adapted and progressive.  Copy-adapt of
`HRS.MD.EQLawFlow.eqlaw_exists_filtered` and `HRS.exists_isStrongSolution_of_maximal`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213E

open HRS

variable {d N : ℕ}

theorem e213e_exists_global_filtered {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (hd : 2 ≤ d) (hM : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V)
    (X₀ : Ω → Config d N) (hX₀ : Measurable X₀)
    (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    ∃ X : ℝ≥0 → Ω → Config d N, (∀ T : ℝ, IsStrongSolution P D T X₀ W X) ∧
      ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
        IsFilteredSolution P ℱ W' W X := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hK : KernelLocal d D.s := kernelLocal_of_two_le hd D.hs0 D.hsd
  have hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D hK.smoothOffZero hV
  obtain ⟨W', hW'm, hWW', hBF, hX₀ℱ⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  set ℱ := generatedFiltration P X₀ hX₀ W' hW'm with hℱ
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, X₀ ω₀ ∉ collisionSet d N := hdist.exists
  let rep : Ω → Fin N → Euc d := fun ω i => Torus.rep (X₀ ω i)
  have hmk : ∀ ω, (fun i => Torus.mk (rep ω i)) = X₀ ω := fun ω =>
    funext fun i => Torus.mk_rep _
  have hcoll : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  let Y₀ : Ω → Fin N → Euc d := fun ω => if X₀ ω ∈ collisionSet d N then rep ω₀ else rep ω
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace Ω := ℱ t
    have hrep : Measurable rep := measurable_pi_iff.2 fun i =>
      (measurable_torusRep d).comp ((measurable_pi_apply i).comp (hX₀ℱ t))
    exact Measurable.ite (hX₀ℱ t hcoll) measurable_const hrep
  have hY₀0 : ∀ ω, Y₀ ω ∈ liftedFree d N := by
    intro ω
    show (fun i => Torus.mk (Y₀ ω i)) ∉ collisionSet d N
    by_cases h : X₀ ω ∈ collisionSet d N
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω₀]
      exact hω₀
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω]
      exact h
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω := by
    filter_upwards [hdist] with ω h
    simp only [Y₀, h, ↓reduceIte]
    exact hmk ω
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, hmax⟩ := exists_sde_solution_maximal hBF
    (liftedFree d N) (isOpen_liftedFree d N) (fun _ Z => liftedDrift D Z) hb (liftedNoise D) Y₀
    hY₀m hY₀0
  have htop : ∀ᵐ ω ∂P, τ ω = ⊤ :=
    (particle_no_collision_dge2 D hd hM hV hBF ⟨hY₀m, hstop, hpos, hsol, hmem, hexit⟩).2
  have hAmeas : MeasurableSet {ω | τ ω ≠ ⊤} := by
    have : {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, {ω | τ ω ≤ ((n : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
        obtain ⟨n, hn⟩ := exists_nat_ge r
        exact ⟨n, by rw [← hr]; exact_mod_cast hn⟩
      · rintro ⟨n, hn⟩ h
        rw [h] at hn
        exact absurd hn (by simp)
    rw [this]
    exact MeasurableSet.iUnion fun n => ℱ.le _ _ (hstop (n : ℝ))
  have hA0 : P {ω | τ ω ≠ ⊤} = 0 := ae_iff.1 htop
  have hAt : ∀ t : ℝ, MeasurableSet[ℱ t] {ω | τ ω = ⊤} := fun t => by
    have := (hBF.complete t _ hAmeas hA0).compl
    have e : {ω | τ ω = ⊤} = {ω | τ ω ≠ ⊤}ᶜ := by ext ω; simp
    rw [e]
    exact this
  let Yg : ℝ → Ω → Fin N → Euc d := fun t ω => if τ ω = ⊤ then Y t ω else Y₀ ω
  have hsolTop : IsAdditiveSDESolution P ℱ W' (fun _ Z => liftedDrift D Z) (liftedNoise D) Y₀
      (fun _ => ⊤) Yg := by
    refine ⟨fun t => ?_, fun ω => ?_, fun ω t ht _ => ?_, ?_⟩
    · let _ : MeasurableSpace Ω := ℱ t
      exact Measurable.ite (hAt t) (hsol.adapted t) (hY₀m t)
    · by_cases h : τ ω = ⊤
      · simp only [Yg, h, ↓reduceIte]; exact hsol.init ω
      · simp only [Yg, h, ↓reduceIte]
    · by_cases h : τ ω = ⊤
      · simp only [Yg, h, ↓reduceIte]
        exact hsol.cont ω t ht (by rw [h]; exact WithTop.coe_lt_top _)
      · simp only [Yg, h, ↓reduceIte]
        exact continuousOn_const
    · filter_upwards [hsol.eq, htop] with ω h1 h2 t ht _
      simp only [Yg, h2, ↓reduceIte]
      exact h1 t ht (by rw [h2]; exact WithTop.coe_lt_top _)
  have hfree : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Yg t ω ∈ liftedFree d N := by
    filter_upwards [htop] with ω h t ht
    simp only [Yg, h, ↓reduceIte]
    exact hmem ω t ht (by rw [h]; exact WithTop.coe_lt_top _)
  have hS : ∀ T : ℝ, IsStrongSolution P D T X₀ W (projectPath fun t ω => Yg (t : ℝ) ω) := by
    intro T
    have hS := isStrongSolution_of_sde P ℱ D W hW W' hBF hWW' Y₀ Yg hsolTop hfree T
    refine { hS with init := ?_ }
    filter_upwards [hS.init, hY₀ae] with ω h1 h2
    rw [h1]
    exact h2
  set X : ℝ≥0 → Ω → Config d N := projectPath fun t ω => Yg (t : ℝ) ω with hXdef
  refine ⟨X, hS, ℱ, W', hBF, hWW', ?_, ?_⟩
  · intro t
    have hm : Measurable[ℱ t] (Yg (t : ℝ)) := hsolTop.adapted (t : ℝ)
    let _ : MeasurableSpace Ω := ℱ t
    exact measurable_pi_iff.2 fun i =>
      Torus.continuous_mk.measurable.comp ((measurable_pi_apply i).comp hm)
  · have hXad : ∀ t : ℝ, Measurable[ℱ t] (ofNNRealTime X t) := by
      intro t
      have hm : Measurable[ℱ t] (Yg ((Real.toNNReal t : ℝ≥0) : ℝ)) := by
        rcases le_or_gt 0 t with ht | ht
        · rw [Real.coe_toNNReal t ht]
          exact hsolTop.adapted t
        · have h0 : ((Real.toNNReal t : ℝ≥0) : ℝ) = 0 := by
            simp [Real.toNNReal_of_nonpos ht.le]
          rw [h0]
          have : Yg 0 = Y₀ := funext fun ω => hsolTop.init ω
          rw [this]
          exact hY₀m t
      let _ : MeasurableSpace Ω := ℱ t
      exact measurable_pi_iff.2 fun i =>
        Torus.continuous_mk.measurable.comp ((measurable_pi_apply i).comp hm)
    have hXc : ∀ ω, Continuous fun t : ℝ => ofNNRealTime X t ω := by
      intro ω
      have hYc : Continuous fun t : ℝ≥0 => Yg (t : ℝ) ω :=
        continuous_nnreal_of_continuousOn_Icc _ fun t ht =>
          hsolTop.cont ω t ht (WithTop.coe_lt_top _)
      have hXc' : Continuous fun t : ℝ≥0 => X t ω :=
        continuous_pi fun i => Torus.continuous_mk.comp ((continuous_apply i).comp hYc)
      exact hXc'.comp continuous_real_toNNReal
    exact (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hXad t).stronglyMeasurable) hXc).isProgressive

end HRS.MC.E213E
