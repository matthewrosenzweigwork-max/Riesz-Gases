import HRS.MC.CepP4

/-!
# Packet P5, Aux1: the lifted space-time measure has density `ghat` on the covering open set
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem ghat_add_lat (f : ℝ → Config d N → ℝ) (T : ℝ) (p : ℝ × (Fin N → Euc d)) (w : Fin N → Lattice d) :
    ghat f T (p + (0, lat w)) = ghat f T p := by
  by_cases hp : p ∈ Ioo 0 T ×ˢ liftedFree d N
  · have hp' := (mem_O_add_lat T p w).2 hp
    rw [ghat_of_mem hp, ghat_of_mem hp']
    show f (p.1 + 0) (mkC (p.2 + lat w)) = f p.1 (mkC p.2)
    rw [add_zero, mkC_add_lat]
  · have hp' : p + (0, lat w) ∉ Ioo 0 T ×ˢ liftedFree d N := fun h => hp ((mem_O_add_lat T p w).1 h)
    unfold ghat
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']

/-- The tile of the covering space with integer part `w`. -/
def Ztile (d N : ℕ) (w : Fin N → Lattice d) : Set (ℝ × (Fin N → Euc d)) := {p | flo p.2 = w}

theorem measurableSet_Ztile (w : Fin N → Lattice d) : MeasurableSet (Ztile d N w) := by
  have : Ztile d N w = (fun p : ℝ × (Fin N → Euc d) => p.2 - lat w) ⁻¹' cubeQ d N := by
    ext p; simp [Ztile, flo_eq_iff]
  rw [this]
  exact measurableSet_cubeQ.preimage (measurable_snd.sub measurable_const)

theorem rhoCov_base [IsProbabilityMeasure P] {T : ℝ} {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {f : ℝ → Config d N → ℝ}
    (hgm : Measurable (ghat f T))
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))))
    {A : Set (ℝ × (Fin N → Euc d))} (hA : MeasurableSet A) (hAc : A ⊆ cubeSet d N)
    (hAO : A ⊆ Ioo 0 T ×ˢ liftedFree d N) :
    rhoCov (rhoM P T X) A = ∫⁻ p in A, ENNReal.ofReal (ghat f T p) := by
  set ρ := rhoM P T X with hρdef
  set S : Set (ℝ × Config d N) := psi 0 ⁻¹' A with hS
  have hSm : MeasurableSet S := measurable_psi 0 hA
  have hSsub : S ⊆ Ioo 0 T ×ˢ (collisionSet d N)ᶜ := by
    intro q hq
    have h := hAO hq
    rw [psi_zero_apply] at h
    refine ⟨h.1, ?_⟩
    have h2 : (fun i => Torus.mk (repC q.2 i)) ∉ collisionSet d N := h.2
    rwa [show (fun i => Torus.mk (repC q.2 i)) = q.2 from mk_repC q.2] at h2
  have hlift : lift0 S = A := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : Gm p ∈ psi 0 ⁻¹' A := h1
      simp only [mem_preimage, psi_zero_apply, Gm] at h3
      rw [repC_mkC_of_mem h2.2] at h3
      exact h3
    · intro hp
      refine ⟨?_, hAc hp⟩
      show (psi 0 (Gm p)) ∈ A
      simp only [psi_zero_apply, Gm]
      rw [repC_mkC_of_mem (hAc hp).2]
      exact hp
  have hmeasF : Measurable (fun y : ℝ × Config d N => ENNReal.ofReal (fhat f T y)) :=
    ENNReal.measurable_ofReal.comp (measurable_fhat' hgm)
  calc rhoCov ρ A = ρ S := rhoCov_cube ρ hA hAc
    _ = ∫⁻ t in Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} := rhoM_apply T hm hXm hSm
    _ = ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) :=
        hρ S hSm hSsub
    _ = ∫⁻ p in S, ENNReal.ofReal (fhat f T p) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
        refine setLIntegral_congr_fun hSm (fun q hq => ?_)
        rw [fhat_eq (hSsub hq).1 (hSsub hq).2]
    _ = ∫⁻ p in lift0 S, ENNReal.ofReal (fhat f T (Gm p)) :=
        (lintegral_lift0 (F := fun y : ℝ × Config d N => ENNReal.ofReal (fhat f T y)) hmeasF hSm).symm
    _ = ∫⁻ p in A, ENNReal.ofReal (ghat f T p) := by
        rw [hlift]
        refine setLIntegral_congr_fun hA (fun p hp => ?_)
        show ENNReal.ofReal (ghat f T (p.1, repC (mkC p.2))) = _
        rw [repC_mkC_of_mem (hAc hp).2]

end HRS.MC.CepP5
