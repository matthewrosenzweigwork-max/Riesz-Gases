import HRS.Stochastic.Particle
import HRS.Stochastic.SelectedFlow

/-!
# Packet CEPC1: a contact-allowing integrated solution agrees with the maximal solution until its first contact

Pathwise uniqueness of the additive-noise ODE on the open region `liftedFree` (`ode_additive_unique`) applied to
the two lifts after a lattice shift of the initial lift (template: `pathwiseUnique_of_locLipschitz`).  The
vocabulary `cep_NoContactBefore` is duplicated from `HRS/MC/CepaSpec.lean` (same body) so that this file does not
import the spec file.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepC1

open HRS

/-- `X` has no contact on `[0, σ)` along the path `ω`.  Same body as `HRS.MC.Cepa.cep_NoContactBefore`. -/
def cep_NoContactBefore {Ω : Type*} {d N : ℕ} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) (σ : WithTop ℝ) : Prop :=
  ∀ t : ℝ≥0, (((t : ℝ)) : WithTop ℝ) < σ → X t ω ∉ collisionSet d N

section Det

variable {d N : ℕ}

/-- Deterministic core: a path `yX` satisfying the integrated equation on `[0,T]` and lying in `liftedFree`
before `σ` coincides with a path solution `y` (also in `liftedFree`) up to `min σ τ` (and `T`). -/
theorem cepc1_det (D : DynData d)
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    {T : ℝ} {w : ℝ≥0 → (Fin N × Fin d) → ℝ} (hw : Continuous w)
    {y₀ : Fin N → Euc d} {yX : ℝ≥0 → Fin N → Euc d} (hX0 : yX 0 = y₀)
    (hXeq : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      IntegrableOn (fun s : ℝ => liftedDrift D (yX (Real.toNNReal s))) (Set.Icc 0 (t : ℝ)) ∧
      yX t = y₀ + (∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (yX (Real.toNNReal s))) +
        ∑ k, w t k • liftedNoise (N := N) D k)
    {σ : WithTop ℝ}
    (hXU : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < σ → yX (Real.toNNReal t) ∈ liftedFree d N)
    {τ : WithTop ℝ} {y : ℝ → Fin N → Euc d}
    (hy : IsPathSolution (fun _ Z => liftedDrift D Z) (liftedNoise D) w y₀ τ y)
    (hyU : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ liftedFree d N) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T → (t : WithTop ℝ) < σ → (t : WithTop ℝ) < τ →
      yX (Real.toNNReal t) = y t := by
  set τX : WithTop ℝ := min σ (T : WithTop ℝ) with hτX
  have hτXσ : ∀ t : ℝ, (t : WithTop ℝ) < τX → (t : WithTop ℝ) < σ ∧ t < T := by
    intro t ht
    rw [hτX] at ht
    exact ⟨lt_of_lt_of_le ht (min_le_left _ _), by exact_mod_cast lt_of_lt_of_le ht (min_le_right _ _)⟩
  have hpX : IsPathSolution (fun _ Z => liftedDrift D Z) (liftedNoise D) w y₀ τX
      (fun t => yX (Real.toNNReal t)) := by
    refine ⟨by simpa using hX0, fun t ht htτ => ?_⟩
    have htT : t < T := (hτXσ t htτ).2
    have hcoe : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht
    obtain ⟨hint, heq⟩ := hXeq (Real.toNNReal t) (by rw [hcoe]; exact htT.le)
    rw [hcoe] at hint heq
    refine ⟨?_, hint, heq⟩
    have hF : ContinuousOn (fun s : ℝ => y₀ + (∫ u in (0 : ℝ)..s, liftedDrift D (yX (Real.toNNReal u)))
        + addNoise (liftedNoise (N := N) D) w s) (Set.Icc 0 t) := by
      refine (continuousOn_const.add ?_).add (continuous_addNoise (liftedNoise (N := N) D) hw).continuousOn
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t)
        (μ := volume) (f := fun u => liftedDrift D (yX (Real.toNNReal u)))
        (by rwa [Set.uIcc_of_le ht])
      rwa [Set.uIcc_of_le ht] at this
    refine hF.congr fun s hs => ?_
    have hs0 : 0 ≤ s := hs.1
    have hcs : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
    obtain ⟨_, heqs⟩ := hXeq (Real.toNNReal s) (by rw [hcs]; exact hs.2.trans htT.le)
    rw [hcs] at heqs
    rw [heqs, setIntegral_Icc_eq_interval hs0]
    rfl
  have huniq := ode_additive_unique (liftedFree d N) (isOpen_liftedFree d N)
    (fun _ Z => liftedDrift D Z) hb (liftedNoise D) w hw y₀ hpX hy
    (fun t ht htτ => hXU t ht (hτXσ t htτ).1) hyU
  intro t ht htT htσ htτ
  have hlt : ∀ u : ℝ, 0 ≤ u → u < t → yX (Real.toNNReal u) = y u := by
    intro u hu hut
    refine huniq u hu ?_
    refine lt_min ?_ ?_
    · rw [hτX]
      exact lt_min (lt_trans (by exact_mod_cast hut) htσ)
        (by exact_mod_cast hut.trans_le htT)
    · exact lt_trans (by exact_mod_cast hut) htτ
  have hcoe : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht
  obtain ⟨_, heq⟩ := hXeq (Real.toNNReal t) (by rw [hcoe]; exact htT)
  rw [hcoe] at heq
  obtain ⟨_, _, heq'⟩ := hy.2 t ht htτ
  rw [heq, heq']
  have hint : ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (yX (Real.toNNReal s)) =
      ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (y s) := by
    calc ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (yX (Real.toNNReal s))
        = ∫ s in Set.Ico (0 : ℝ) t, liftedDrift D (yX (Real.toNNReal s)) :=
          (setIntegral_congr_set Ico_ae_eq_Icc).symm
      _ = ∫ s in Set.Ico (0 : ℝ) t, liftedDrift D (y s) :=
          setIntegral_congr_fun measurableSet_Ico fun s hs => by simp only [hlt s hs.1 hs.2]
      _ = ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (y s) := setIntegral_congr_set Ico_ae_eq_Icc
  rw [hint]

end Det

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- **C1 (a contact-allowing integrated solution coincides with the maximal solution until its first contact)**. -/
theorem cep_C1_agree_until_contact_proof [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hW : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    (hW'c : ∀ ω, Continuous fun t => W' t ω)
    (hX : IsContactStrongSolution P D T X₀ W X)
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω) :
    ∀ᵐ ω ∂P, ∀ σ : WithTop ℝ, cep_NoContactBefore X ω σ → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (((t : ℝ)) : WithTop ℝ) < σ → (((t : ℝ)) : WithTop ℝ) < τ ω →
        X t ω = fun i => Torus.mk (Y (t : ℝ) ω i) := by
  obtain ⟨Yx, hYeq, rfl⟩ := hX.lift
  filter_upwards [hYeq, hX.init, hW, hY.sol.isPathSolution, hY.sol.eq, hY₀] with ω hω hi hWω hps hyeq hy0
  intro σ hσ t htT htσ htτ
  set c : Fin N → Euc d := Yx 0 ω - Y₀ ω with hcdef
  have hmk : ∀ i, Torus.mk (c i) = 0 := by
    intro i
    have h1 := congrFun (hi.trans hy0.symm) i
    have h2 : Torus.mk (Yx 0 ω i) = Torus.mk (Y₀ ω i) := h1
    simp [hcdef, mk_sub', h2]
  -- the noise terms
  have hWe : ∀ s : ℝ≥0, toCoords W s ω = W' s ω := by
    intro s; funext ij; exact (hWω s ij.1 ij.2).symm
  have hnoise : ∀ s : ℝ≥0, ∑ k, W' s ω k • liftedNoise (N := N) D k =
      Real.sqrt (2 * D.invβ) • W s ω := by
    intro s
    rw [← hWe s, sum_liftedNoise, ofCoords_toCoords]
  have hW0 : Real.sqrt (2 * D.invβ) • W 0 ω = 0 := by
    have h0 : ((0 : ℝ) : WithTop ℝ) < τ ω := by simpa using hY.pos ω
    obtain ⟨_, he⟩ := hyeq 0 le_rfl h0
    have hi0 := hY.sol.init ω
    have : ∑ k, ofNNRealTime W' 0 ω k • liftedNoise (N := N) D k = 0 := by
      have he' : Y 0 ω = Y₀ ω + 0 + ∑ k, ofNNRealTime W' 0 ω k • liftedNoise (N := N) D k := by
        rw [he]; simp
      rw [hi0] at he'
      simpa using he'.symm
    simpa [ofNNRealTime, hnoise] using this
  have key : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      IntegrableOn (fun u : ℝ => liftedDrift D (Yx (Real.toNNReal u) ω - c)) (Set.Icc 0 (s : ℝ)) ∧
      Yx s ω - c = Y₀ ω + (∫ u in Set.Icc (0 : ℝ) s, liftedDrift D (Yx (Real.toNNReal u) ω - c)) +
        ∑ k, W' s ω k • liftedNoise (N := N) D k := by
    intro s hs
    obtain ⟨hint, heq⟩ := hω s hs
    have hd : ∀ u, liftedDrift D (Yx (Real.toNNReal u) ω - c) = liftedDrift D (Yx (Real.toNNReal u) ω) :=
      fun u => liftedDrift_sub_of_mk_eq_zero D _ c hmk
    simp only [hd]
    have hintE : IntegrableOn (fun u : ℝ => liftedDrift D (Yx (Real.toNNReal u) ω))
        (Set.Icc 0 (s : ℝ)) := Integrable.of_eval hint
    refine ⟨hintE, ?_⟩
    rw [hnoise s]
    funext i
    have h2 : (∫ u in Set.Icc (0 : ℝ) s, liftedDrift D (Yx (Real.toNNReal u) ω)) i =
        ∫ u in Set.Icc (0 : ℝ) s, liftedDrift D (Yx (Real.toNNReal u) ω) i := by
      have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm
        hintE
      simpa using this.symm
    have h1 := heq i
    have h3 : Real.sqrt (2 * D.invβ) • W 0 ω i = 0 := by
      simpa using congrFun hW0 i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hcdef] at h1 h3 ⊢
    rw [h2]
    have h1' : Yx s ω i = (Yx 0 ω i + ∫ u in Set.Icc (0 : ℝ) s,
        liftedDrift D (Yx (Real.toNNReal u) ω) i) + Real.sqrt (2 * D.invβ) • W s ω i := by
      rw [smul_sub, h3, sub_zero] at h1
      exact h1
    rw [h1']
    abel
  have hdet := cepc1_det D hb (T := T) (w := fun s => W' s ω) (hW'c ω) (y₀ := Y₀ ω)
    (yX := fun s => Yx s ω - c) (by simp [hcdef]) (fun s hs => key s hs) (σ := σ)
    (fun u hu huσ => by
      show (fun i => Torus.mk ((Yx (Real.toNNReal u) ω - c) i)) ∉ collisionSet d N
      rw [mkPi_sub_of_mk_eq_zero _ c hmk]
      have := hσ (Real.toNNReal u) (by rw [Real.coe_toNNReal _ hu]; exact huσ)
      exact this)
    (y := fun s => Y s ω) (τ := τ ω) hps (fun s hs hsτ => hY.mem ω s hs hsτ)
    (t : ℝ) t.2 htT htσ htτ
  simp only [Real.toNNReal_coe] at hdet
  rw [← hdet]
  exact (mkPi_sub_of_mk_eq_zero _ c hmk).symm

end Main

end HRS.MC.CepC1
