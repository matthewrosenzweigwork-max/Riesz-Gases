import HRS.MP.SelfSimP1Base
import HRS.MP.SelfSimP1CepaMap
import HRS.MP.SelfSimSpec

/-!
# MPP1CEPA (c): assembly of the Cépa-Lépingle branch of packet P1 (`ss_P1_cepa`)

`ss_P1_filtered_version` of `HRS/MP/SelfSimSpec.lean` for the second alternative of `SelectedFlowRd.flow`
(`d = 1`, `s = 0`, `IsWholeCepaLepingleFlow`).  The modification `X'` is the given flow frozen after `T` on a measurable
set `G` of full measure (`ssp1_freeze`); on `G`, for every `s ≤ T`, `X_s = (F_s(X₀, W'|[0,s]))_s` for the Borel solution
map `F_s` of `ssp1c_solution_map` (deterministic uniqueness `ssp1c_unique`), so `X_s` is `ℱ_s`-measurable by completeness
of the Brownian filtration of `(X₀, W')` (`ssp1_base`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.SelfSim
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.SelfSimP1

section SolLemmas

variable {N : ℕ}

/-- `ssp1c_Sol` only sees the paths on `[0,T]`. -/
theorem ssp1c_Sol_congr {invβ T : ℝ} (hT : 0 ≤ T) {x₀ : EucConfig 1 N} {w w' p p' : ℝ → EucConfig 1 N}
    (hw : ∀ r ∈ Icc (0 : ℝ) T, w r = w' r) (hp : ∀ r ∈ Icc (0 : ℝ) T, p r = p' r)
    (h : ssp1c_Sol invβ T x₀ w p) : ssp1c_Sol invβ T x₀ w' p' := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hp 0 h0]; exact h.init
  · intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    obtain ⟨hint, heq⟩ := h.eqn t ht
    have hcg : ∀ r ∈ Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (p r) = particleDriftW (ssp1c_D invβ) (p' r) :=
      fun r hr => by rw [hp r (hsub hr)]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (hint i).congr_fun (fun r hr => by dsimp only; rw [hp r (hsub hr)]) measurableSet_Icc
    · have e1 := heq i
      rw [hp t ht, hp 0 h0, hw t ht, hw 0 h0] at e1
      rw [e1]
      congr 2
      exact setIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [hp r (hsub hr)])
  · have : {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ p' r ∈ eucCollisionSet 1 N} =
        {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ p r ∈ eucCollisionSet 1 N} := by
      ext r
      simp only [mem_setOf_eq]
      exact and_congr_right fun hr => by rw [hp r hr]
    rw [this]; exact h.occ
  · obtain ⟨π, hπ⟩ := h.ord
    refine ⟨π, fun t ht j k k' hk => ?_⟩
    rw [← hp t ht]
    exact hπ t ht j k k' hk

/-- Restriction of a solution on `[0,T]` to a shorter horizon. -/
theorem ssp1c_Sol_mono {invβ T s : ℝ} (hs : s ≤ T) {x₀ : EucConfig 1 N} {w p : ℝ → EucConfig 1 N}
    (h : ssp1c_Sol invβ T x₀ w p) : ssp1c_Sol invβ s x₀ w p := by
  refine ⟨h.init, fun t ht => h.eqn t ⟨ht.1, ht.2.trans hs⟩, ?_, ?_⟩
  · refine measure_mono_null ?_ h.occ
    rintro r ⟨hr, hc⟩
    exact ⟨⟨hr.1, hr.2.trans hs⟩, hc⟩
  · obtain ⟨π, hπ⟩ := h.ord
    exact ⟨π, fun t ht => hπ t ⟨ht.1, ht.2.trans hs⟩⟩

end SolLemmas


section Adapted

variable {N : ℕ}

attribute [local instance] ssp1c_pathMeas ssp1c_pathBorel

/-- The noise vector `(W'_{(i,j)})` as a configuration of `ℝ^N`. -/
def ssp1c_vec (v : Fin N × Fin 1 → ℝ) : EucConfig 1 N := fun i => WithLp.toLp 2 fun j => v (i, j)

theorem ssp1c_continuous_vec : Continuous (ssp1c_vec (N := N)) :=
  continuous_pi fun i => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => continuous_apply (i, j))

/-- **Adaptedness of the solution.**  In a complete filtration for which `X₀` and the Brownian coordinates `W'` are
adapted, a continuous process which is almost surely an ordered null-occupation solution of the Cépa-Lépingle equation
driven by `W'` is adapted on `[0,T]`. -/
theorem ssp1c_adapted_of_sol {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) {ℱ : Filtration ℝ mΩ}
    (hℱ : IsCompleteFiltration P ℱ) (invβ T : ℝ) (X₀ : Ω → EucConfig 1 N) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀)
    (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (hW'c : ∀ ζ, Continuous fun t => W' t ζ)
    (hW'ℱ : ∀ s : ℝ≥0, ∀ t : ℝ, (s : ℝ) ≤ t → Measurable[ℱ t] (W' s))
    (X : ℝ≥0 → Ω → EucConfig 1 N) (hXm : ∀ t, Measurable (X t)) (G : Set Ω) (hGae : ∀ᵐ ζ ∂P, ζ ∈ G)
    (hG : ∀ ζ ∈ G, X₀ ζ ∉ eucCollisionSet 1 N ∧ Continuous (fun t => X t ζ) ∧
      ssp1c_Sol invβ T (X₀ ζ) (fun r => ssp1c_vec (W' (Real.toNNReal r) ζ)) (fun r => X (Real.toNNReal r) ζ)) :
    ∀ s : ℝ≥0, (s : ℝ) ≤ T → Measurable[ℱ s] (X s) := by
  intro s hsT
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2
  obtain ⟨F, hF, hFx⟩ := ssp1c_solution_map (N := N) (T := (s : ℝ)) invβ hs0
  -- the noise path as a random element of the path space
  let Wc : Ω → ssp1c_PS (s : ℝ) N := fun ζ =>
    ⟨fun t => ssp1c_vec (W' (Real.toNNReal t.1) ζ),
      ssp1c_continuous_vec.comp ((hW'c ζ).comp (continuous_real_toNNReal.comp continuous_subtype_val))⟩
  have hWc : Measurable[ℱ s] Wc := by
    let _ : MeasurableSpace Ω := ℱ s
    refine ssp1c_measurable_of_eval hs0 fun t => ?_
    have h1 : Measurable[ℱ s] (W' (Real.toNNReal t.1)) :=
      hW'ℱ _ _ (by rw [Real.coe_toNNReal _ t.2.1]; exact t.2.2)
    have h2 : Measurable (ssp1c_vec (N := N)) := ssp1c_continuous_vec.measurable
    exact h2.comp h1
  let Z : Ω → EucConfig 1 N := fun ζ => (F (X₀ ζ, Wc ζ)) ⟨(s : ℝ), hs0, le_rfl⟩
  have hZ : Measurable[ℱ s] Z := by
    let _ : MeasurableSpace Ω := ℱ s
    have h1 : Measurable fun ζ => (X₀ ζ, Wc ζ) := (hX₀ s).prodMk hWc
    have h2 : Continuous fun g : ssp1c_PS (s : ℝ) N => g ⟨(s : ℝ), hs0, le_rfl⟩ := continuous_eval_const _
    exact h2.measurable.comp (hF.comp h1)
  have hae : Z =ᵐ[P] X s := by
    filter_upwards [hGae] with ζ hζ
    obtain ⟨hx₀, hcont, hsol⟩ := hG ζ hζ
    let xs : ssp1c_PS (s : ℝ) N := ⟨fun t => X (Real.toNNReal t.1) ζ,
      hcont.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
    have hsol' : ssp1c_Sol invβ (s : ℝ) (X₀ ζ) (ssp1c_ext hs0 (Wc ζ)) (ssp1c_ext hs0 xs) := by
      refine ssp1c_Sol_congr hs0 (fun r hr => ?_) (fun r hr => ?_) (ssp1c_Sol_mono hsT hsol)
      · rw [ssp1c_ext_of_mem hs0 (Wc ζ) hr]; rfl
      · rw [ssp1c_ext_of_mem hs0 xs hr]; rfl
    have := hFx (X₀ ζ) (Wc ζ) xs hx₀ hsol'
    show (F (X₀ ζ, Wc ζ)) ⟨(s : ℝ), hs0, le_rfl⟩ = X s ζ
    rw [this]
    simp [xs]
  exact hℱ.measurable_of_ae_eq (s : ℝ) hZ (hXm s) hae

end Adapted


section Main

/-- **P1, Cépa-Lépingle branch** (`d = 1`, `s = 0`): the conclusion of `ss_P1_filtered_version` with `SSOrdered`,
from the fields of `SelectedFlowRd` and the second alternative `IsWholeCepaLepingleFlow` of `flow`. -/
theorem ss_P1_cepa {d : ℕ} (s : ℝ) (N : ℕ) (invβ : ℝ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hinit_meas : Measurable X₀) (hinit_distinct : ∀ᵐ ζ ∂P, X₀ ζ ∉ eucCollisionSet d N)
    (hbrownian : IsVectorBrownian P W) (hindep : IndepFun X₀ (fun ζ => fun t => W t ζ) P)
    (hd1 : d = 1) (hs : s = 0)
    (hcepa : IsWholeCepaLepingleFlow P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t) ∧ (∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ) ∧
      SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
        T ℱ W' W X' ∧
      SSOrdered P T X' := by
  subst hd1
  subst hs
  classical
  have hT0 : 0 ≤ T := hT.le
  obtain ⟨ℱ, W', hBF, hcomp, hWW', hX₀ℱ, hW'ℱ, -⟩ := ssp1_base P W hbrownian X₀ hinit_meas hindep
  obtain ⟨π, hπm, hπo⟩ := hcepa.ordered
  have hC := hcepa.toContact
  -- the good set
  obtain ⟨G, hGm, hG0, hG⟩ := ssp1_exists_measurable_good P
    (p := fun ζ => X₀ ζ ∉ eucCollisionSet 1 N ∧ X 0 ζ = X₀ ζ ∧ (∀ i, Continuous fun t => X t ζ i) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T →
        (∀ i, IntegrableOn (fun r : ℝ => particleDriftW (⟨0, -1, fun _ => 0, invβ⟩ : WholeDyn 1)
          (X (Real.toNNReal r) ζ) i) (Icc 0 (t : ℝ))) ∧
        ∀ i, X t ζ i = X 0 ζ i + (∫ r in Icc (0 : ℝ) t, particleDriftW
          (⟨0, -1, fun _ => 0, invβ⟩ : WholeDyn 1) (X (Real.toNNReal r) ζ) i) +
          Real.sqrt (2 * invβ) • (W t ζ i - W 0 ζ i)) ∧
      volume {r : ℝ | r ∈ Icc 0 T ∧ X (Real.toNNReal r) ζ ∈ eucCollisionSet 1 N} = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ j : Fin 1, ∀ k k' : Fin N, k ≤ k' →
        X t ζ (π ζ k) j ≤ X t ζ (π ζ k') j) ∧
      (∀ t i j, W' t ζ (i, j) = W t ζ i j))
    (by
      filter_upwards [hinit_distinct, hC.init, hC.cont, hC.eqn, hcepa.occupation, hπo, hWW']
        with ζ h1 h2 h3 h4 h5 h6 h7
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩)
  have hGae : ∀ᵐ ζ ∂P, ζ ∈ G := by rw [ae_iff]; exact hG0
  have hGt : ∀ t : ℝ, MeasurableSet[ℱ t] G := ssp1_measurableSet_of_null_compl hcomp hGm hG0
  have hXc : ∀ ζ ∈ G, Continuous fun t : ℝ≥0 => X t ζ := fun ζ hζ => continuous_pi (hG ζ hζ).2.2.1
  -- the solution property on `G`
  have hSol : ∀ ζ ∈ G, ssp1c_Sol invβ T (X₀ ζ) (fun r => ssp1c_vec (W' (Real.toNNReal r) ζ))
      (fun r => X (Real.toNNReal r) ζ) := by
    intro ζ hζ
    obtain ⟨-, hinit, -, heqn, hocc, hord, hw⟩ := hG ζ hζ
    have hvec : ∀ t : ℝ≥0, ssp1c_vec (W' t ζ) = W t ζ := fun t => by
      funext i; ext j; simp [ssp1c_vec, hw t i j]
    refine ⟨by simpa using hinit, fun t ht => ?_, hocc, ⟨π ζ, fun t ht j k k' hk => ?_⟩⟩
    · have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
      obtain ⟨hint, heq⟩ := heqn (Real.toNNReal t) (by rw [ht']; exact ht.2)
      rw [ht'] at hint heq
      refine ⟨hint, fun i => ?_⟩
      have h3 := heq i
      simp only [Real.toNNReal_zero, hvec]
      exact h3
    · have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
      exact hord (Real.toNNReal t) (by rw [ht']; exact ht.2) j k k' hk
  have hXad : ∀ s : ℝ≥0, (s : ℝ) ≤ T → Measurable[ℱ s] (X s) := by
    refine ssp1c_adapted_of_sol P hcomp invβ T X₀ hX₀ℱ W' hBF.cont hW'ℱ X hC.adapted G hGae
      (fun ζ hζ => ⟨(hG ζ hζ).1, hXc ζ hζ, hSol ζ hζ⟩)
  have hX0meas : ∀ t : ℝ, Measurable[ℱ t] (X 0) := fun t =>
    hcomp.measurable_of_ae_eq t (hX₀ℱ t) (hC.adapted 0)
      (by filter_upwards [hC.init] with ζ h; exact h.symm)
  -- the frozen modification
  let Y : ℝ → Ω → EucConfig 1 N := fun r ζ => X (Real.toNNReal (min r T)) ζ
  have hYad : ∀ r : ℝ, Measurable[ℱ r] (Y r) := by
    intro r
    by_cases hr : 0 ≤ r
    · have hc : ((Real.toNNReal (min r T) : ℝ≥0) : ℝ) = min r T := Real.coe_toNNReal _ (le_min hr hT0)
      have h1 := hXad (Real.toNNReal (min r T)) (by rw [hc]; exact min_le_right _ _)
      exact Measurable.mono h1 (ℱ.mono (by rw [hc]; exact min_le_left _ _)) le_rfl
    · have h0 : Real.toNNReal (min r T) = 0 :=
        Real.toNNReal_of_nonpos ((min_le_left _ _).trans (not_le.1 hr).le)
      show Measurable[ℱ r] (fun ζ => X (Real.toNNReal (min r T)) ζ)
      rw [h0]; exact hX0meas r
  have hYcont : ∀ ζ ∈ G, ContinuousOn (fun t => Y t ζ) (Icc 0 T) := fun ζ hζ =>
    ((hXc ζ hζ).comp (continuous_real_toNNReal.comp (continuous_id.min continuous_const))).continuousOn
  have hX'adapt : ∀ t : ℝ≥0, Measurable[ℱ t] (ssp1_freeze T G Y t) := ssp1_freeze_adapted hGt hYad
  have hmod : ∀ ζ ∈ G, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ssp1_freeze T G Y t ζ = X t ζ := by
    intro ζ hζ t ht
    rw [ssp1_freeze_of_le ht hζ]
    show X (Real.toNNReal (min (t : ℝ) T)) ζ = X t ζ
    rw [min_eq_left ht, Real.toNNReal_coe]
  have hmodr : ∀ ζ ∈ G, ∀ r : ℝ, 0 ≤ r → r ≤ T →
      ssp1_freeze T G Y (Real.toNNReal r) ζ = X (Real.toNNReal r) ζ := fun ζ hζ r h0 hT' =>
    hmod ζ hζ _ (by rw [Real.coe_toNNReal r h0]; exact hT')
  have hX'0 : ∀ ζ ∈ G, ssp1_freeze T G Y 0 ζ = X 0 ζ := fun ζ hζ => by
    simpa using hmodr ζ hζ 0 le_rfl hT0
  have hinit' : ∀ᵐ ζ ∂P, ssp1_freeze T G Y 0 ζ = X₀ ζ := by
    filter_upwards [hGae, hC.init] with ζ hζ h
    rw [hX'0 ζ hζ, h]
  refine ⟨ssp1_freeze T G Y, ℱ, W', ?_, hinit', ⟨⟨hBF, hWW', hX'adapt, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    filter_upwards [hGae] with ζ hζ
    exact hmod ζ hζ t ht
  · -- progressive
    refine ssp1_isProgressive_of_continuous hX'adapt (fun t => ?_) (ssp1_freeze_continuous hT0 hYcont)
    have e : ssp1_freeze T G Y 0 = fun ζ => if ζ ∈ G then X 0 ζ else 0 := by
      funext ζ
      by_cases hζ : ζ ∈ G
      · rw [hX'0 ζ hζ]; simp [hζ]
      · rw [ssp1_freeze_of_notMem hζ]; simp [hζ]
    rw [e]
    let _ : MeasurableSpace Ω := ℱ t
    exact Measurable.ite (hGt t) (hX0meas t) measurable_const
  · exact ssp1_freeze_continuous hT0 hYcont
  · filter_upwards [hinit', hinit_distinct] with ζ h h'
    rw [h]; exact h'
  · -- the integrated equation
    filter_upwards [hGae] with ζ hζ t ht
    obtain ⟨-, hinit, -, heqn, -, -, -⟩ := hG ζ hζ
    obtain ⟨hint, heq⟩ := heqn t ht
    have hcongr : ∀ r ∈ Icc (0 : ℝ) (t : ℝ), ssp1_freeze T G Y (Real.toNNReal r) ζ = X (Real.toNNReal r) ζ :=
      fun r hr => hmodr ζ hζ r hr.1 (hr.2.trans ht)
    refine ⟨fun i => (hint i).congr_fun (fun r hr => ?_) measurableSet_Icc, fun i => ?_⟩
    · dsimp only
      rw [hcongr r hr]
    · have hI : (∫ r in Icc (0 : ℝ) (t : ℝ), particleDriftW (⟨0, -1, fun _ => 0, invβ⟩ : WholeDyn 1)
          (ssp1_freeze T G Y (Real.toNNReal r) ζ) i) =
          ∫ r in Icc (0 : ℝ) (t : ℝ), particleDriftW (⟨0, -1, fun _ => 0, invβ⟩ : WholeDyn 1)
          (X (Real.toNNReal r) ζ) i :=
        setIntegral_congr_fun measurableSet_Icc (fun r hr => by rw [hcongr r hr])
      show ssp1_freeze T G Y t ζ i = ssp1_freeze T G Y 0 ζ i + _ + _
      rw [hmod ζ hζ t ht, hX'0 ζ hζ, hI]
      exact heq i
  · -- null contact occupation
    filter_upwards [hGae] with ζ hζ
    obtain ⟨-, -, -, -, hocc, -, -⟩ := hG ζ hζ
    have : {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ ssp1_freeze T G Y (Real.toNNReal r) ζ ∈ eucCollisionSet 1 N} =
        {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ X (Real.toNNReal r) ζ ∈ eucCollisionSet 1 N} := by
      ext r
      simp only [mem_setOf_eq]
      exact and_congr_right fun hr => by rw [hmodr ζ hζ r hr.1 hr.2]
    rw [this]; exact hocc
  · -- ordering
    refine ⟨π, hπm, ?_⟩
    filter_upwards [hGae] with ζ hζ t ht j k k' hk
    obtain ⟨-, -, -, -, -, hord, -⟩ := hG ζ hζ
    rw [hmod ζ hζ t ht]
    exact hord t ht j k k' hk

end Main

end HRS.MP.SelfSimP1
