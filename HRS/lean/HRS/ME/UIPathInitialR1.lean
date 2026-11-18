import HRS.ME.UIPath

/-!
# Packet IR1: `exists_indep_gaussian`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

lemma p_ir1_hasLaw_incr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (p : ℕ) :
    HasLaw (fun ω => (WithLp.toLp 2 (fun k : Fin p => B (((k : ℕ) + 1 : ℕ) : ℝ≥0) ω - B ((k : ℕ) : ℝ≥0) ω) :
      EuclideanSpace ℝ (Fin p))) (stdGaussian (EuclideanSpace ℝ (Fin p))) P := by
  have hind : iIndepFun (fun (i : ℕ) ω => B ((i + 1 : ℕ) : ℝ≥0) ω - B (i : ℝ≥0) ω) P :=
    hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0)) Nat.mono_cast
  have hind' : iIndepFun (fun (k : Fin p) ω => B (((k : ℕ) + 1 : ℕ) : ℝ≥0) ω - B ((k : ℕ) : ℝ≥0) ω) P :=
    hind.precomp (g := fun k : Fin p => (k : ℕ)) Fin.val_injective
  have hl : ∀ k : Fin p, HasLaw (fun ω => B (((k : ℕ) + 1 : ℕ) : ℝ≥0) ω - B ((k : ℕ) : ℝ≥0) ω)
      (gaussianReal 0 1) P := by
    intro k
    have := hB.hasLaw_sub (((k : ℕ) + 1 : ℕ) : ℝ≥0) ((k : ℕ) : ℝ≥0)
    convert this using 2
    rw [Real.nndist_eq]
    apply NNReal.eq
    simp
  have h2 := hind'.hasLaw_pi hl
  have h3 : HasLaw (WithLp.toLp 2 : (Fin p → ℝ) → EuclideanSpace ℝ (Fin p))
      (stdGaussian (EuclideanSpace ℝ (Fin p))) (Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact h3.comp h2

theorem exists_indep_gaussian (hd : 1 ≤ d) (S : ParticleSeq d) (n : ℕ) (D : DynData d) (T' : ℝ)
    (h : IsParticleSystem (S.P n) D T' (S.X₀ n) (S.W n) (S.X n)) {p : ℕ}
    (Γ : Matrix (Fin p) (Fin p) ℝ) :
    ∃ G : S.Ω n → EuclideanSpace ℝ (Fin p), AEMeasurable G (S.P n) ∧
      law (S.P n) G = ProbabilityTheory.multivariateGaussian 0 Γ ∧
      ProbabilityTheory.IndepFun (S.X₀ n) G (S.P n) := by
  classical
  let i0 : Fin (n + 2) := 0
  let j0 : Fin d := ⟨0, hd⟩
  have hBm : IsBrownianReal (fun t ω => S.W n t ω i0 j0) (S.P n) := h.brownian.1 i0 j0
  have hZ := p_ir1_hasLaw_incr hBm.toIsPreBrownianReal p
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Γ)
  let F : (ℝ≥0 → Fin (n + 2) → Euc d) → EuclideanSpace ℝ (Fin p) := fun w =>
    A (WithLp.toLp 2 fun k : Fin p => w (((k : ℕ) + 1 : ℕ) : ℝ≥0) i0 j0 - w ((k : ℕ) : ℝ≥0) i0 j0)
  have hF : Measurable F := by
    have : ∀ (t : ℝ≥0), Measurable fun w : ℝ≥0 → Fin (n + 2) → Euc d => w t i0 j0 := by
      intro t
      have h1 : Measurable fun w : ℝ≥0 → Fin (n + 2) → Euc d => w t i0 :=
        (measurable_pi_apply i0).comp (measurable_pi_apply t)
      exact (EuclideanSpace.proj j0 (𝕜 := ℝ)).continuous.measurable.comp h1
    unfold F
    refine A.continuous.measurable.comp ?_
    refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
    exact measurable_pi_iff.2 fun k => (this _).sub (this _)
  refine ⟨fun ω => F (fun t => S.W n t ω), ?_, ?_, ?_⟩
  · exact (A.continuous.measurable.comp_aemeasurable hZ.aemeasurable)
  · have : (fun ω => F (fun t => S.W n t ω)) = A ∘ (fun ω => (WithLp.toLp 2 (fun k : Fin p =>
        S.W n (((k : ℕ) + 1 : ℕ) : ℝ≥0) ω i0 j0 - S.W n ((k : ℕ) : ℝ≥0) ω i0 j0) :
          EuclideanSpace ℝ (Fin p))) := rfl
    rw [this]
    have hA : HasLaw A (ProbabilityTheory.multivariateGaussian 0 Γ)
        (stdGaussian (EuclideanSpace ℝ (Fin p))) :=
      ⟨A.continuous.measurable.aemeasurable, by simp [ProbabilityTheory.multivariateGaussian, A]⟩
    exact (hA.comp hZ).map_eq
  · exact h.indep.comp measurable_id hF

end HRS.ME.UIPathInitial
