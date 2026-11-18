import HRS.MS.R2InterpAux63

/-!
# S10.2 (worker S102), part 64 (packet G5): abstract core against a cumulative tensor path of bounded variation (port of `S7PIG5_core`)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.R2Interp

open HRS HRS.Sec7 HRS.MC.Sec7.S7PIG5

section Core

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

set_option maxSynthPendingDepth 3 in
/-- The abstract core, bounded variation version. -/
theorem s102_G5core_bv (T : ℝ) (hT : 0 < T) (Pj : ℕ → (B →L[ℝ] B)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hTconv : ∀ v : TensorDual B 2, v ∈ projTensor B 2 →
      Tendsto (fun L => tensorPow 2 (Pj L) v) atTop (𝓝 v))
    (Jc : ℝ → TensorDual B 2) (hJc0 : Jc 0 = 0)
    (hmem : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → Jc b - Jc a ∈ projTensor B 2)
    (hBVJ : BoundedVariationOn Jc (Set.Icc 0 T))
    (M : ℝ → B [×2]→L[ℝ] ℝ) (ML : ℕ → ℝ → B [×2]→L[ℝ] ℝ)
    (hM : ContinuousOn M (Set.Icc 0 T)) (hML : ∀ L, ContinuousOn (ML L) (Set.Icc 0 T))
    (hMu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Set.Icc (0 : ℝ) T, ‖ML L τ - M τ‖ ≤ ε) :
    ∃ I : ℝ, IsRS T (fun τ a b => (Jc b - Jc a) (M τ)) I ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b => tensorPow 2 (Pj L) (Jc b - Jc a) (ML L τ)) (IL L)) ∧
        Tendsto IL atTop (𝓝 I) := by
  have : CompleteSpace (projTensor B 2) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hJm : ∀ s : ℝ, 0 ≤ s → s ≤ T → Jc s ∈ projTensor B 2 := fun s hs hsT => by
    have := hmem 0 s le_rfl hs hsT
    rwa [hJc0, sub_zero] at this
  let F : ℝ → projTensor B 2 := fun s =>
    ⟨Jc (Set.projIcc 0 T hT.le s), hJm _ (Set.projIcc 0 T hT.le s).2.1 (Set.projIcc 0 T hT.le s).2.2⟩
  have hFc : ∀ s ∈ Set.Icc (0 : ℝ) T, ((F s : projTensor B 2) : TensorDual B 2) = Jc s := by
    intro s hs
    show Jc (Set.projIcc 0 T hT.le s) = Jc s
    rw [Set.projIcc_of_mem hT.le hs]
  have hF0 : F 0 = 0 := by
    apply Subtype.ext
    rw [hFc 0 ⟨le_rfl, hT.le⟩]
    exact hJc0
  have hFd : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T →
      (((F b - F a : projTensor B 2)) : TensorDual B 2) = Jc b - Jc a := by
    intro a b ha hb
    rw [Submodule.coe_sub, hFc a ha, hFc b hb]
  have hBV : BoundedVariationOn F (Set.Icc 0 T) := by
    have h1 : eVariationOn F (Set.Icc 0 T) = eVariationOn (fun x => ((F x : projTensor B 2) : TensorDual B 2))
        (Set.Icc 0 T) := by
      unfold eVariationOn
      simp only [Subtype.edist_eq]
    unfold BoundedVariationOn
    rw [h1]
    refine ne_top_of_le_ne_top hBVJ ?_
    have := eVariationOn.comp_le_of_monotoneOn Jc (fun x => ((Set.projIcc (0 : ℝ) T hT.le x : Set.Icc (0 : ℝ) T) : ℝ))
      (t := Set.Icc 0 T) (s := Set.Icc 0 T) (((Subtype.mono_coe _).comp (Set.monotone_projIcc hT.le)).monotoneOn _)
      (fun x _ => (Set.projIcc 0 T hT.le x).2)
    exact this
  let Pj' : ℕ → (projTensor B 2 →L[ℝ] projTensor B 2) := fun L =>
    ((tensorPow 2 (Pj L)).comp (projTensor B 2).subtypeL).codRestrict (projTensor B 2)
      (fun e => S7PIG5_tensorPow_mem 2 (Pj L) e.2)
  have hK : ∀ L, ‖Pj' L‖ ≤ 1 := by
    intro L
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun e => ?_)
    have h1 : ‖Pj' L e‖ = ‖tensorPow 2 (Pj L) (e : TensorDual B 2)‖ := rfl
    rw [h1, one_mul]
    calc ‖tensorPow 2 (Pj L) (e : TensorDual B 2)‖ ≤ ‖tensorPow 2 (Pj L)‖ * ‖(e : TensorDual B 2)‖ :=
          (tensorPow 2 (Pj L)).le_opNorm _
      _ ≤ 1 * ‖(e : TensorDual B 2)‖ :=
          mul_le_mul_of_nonneg_right (q17_precomp_norm 2 (Pj L) (hP1 L)) (norm_nonneg _)
      _ = ‖e‖ := by rw [one_mul]; rfl
  have hconv' : ∀ e : projTensor B 2, Tendsto (fun L => Pj' L e) atTop (𝓝 e) := fun e =>
    tendsto_subtype_rng.2 (hTconv e e.2)
  have hA : ContinuousOn (fun τ => S7PIG5_evL B (M τ)) (Set.Icc 0 T) :=
    (S7PIG5_evL B).continuous.comp_continuousOn hM
  have hAL : ∀ L, ContinuousOn (fun τ => S7PIG5_evL B (ML L τ)) (Set.Icc 0 T) := fun L =>
    (S7PIG5_evL B).continuous.comp_continuousOn (hML L)
  have hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖S7PIG5_evL B (ML L u) - S7PIG5_evL B (M u)‖ ≤ ε := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := hMu ε hε
    refine ⟨L₀, fun L hL u hu => ?_⟩
    rw [← map_sub]
    exact (S7PIG5_evL_norm _).trans (hL₀ L hL u hu)
  obtain ⟨I, hI, IL, hIL, hlim⟩ := measure_projection_proof Pj' 1 hK hconv' T hT F hBV hF0
    (fun τ => S7PIG5_evL B (M τ)) (fun L τ => S7PIG5_evL B (ML L τ)) hA hAL hAu
  refine ⟨I, S7PIG5_rs_congr hI ?_, IL, fun L => S7PIG5_rs_congr (hIL L) ?_, hlim⟩
  · intro τ a b ha haτ hτb hbT
    have hb : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (haτ.trans hτb), hbT⟩
    have ha' : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, (haτ.trans hτb).trans hbT⟩
    show (S7PIG5_evL B (M τ)) (F b - F a) = (Jc b - Jc a) (M τ)
    rw [S7PIG5_evL_apply, hFd a b ha' hb]
  · intro τ a b ha haτ hτb hbT
    have hb : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (haτ.trans hτb), hbT⟩
    have ha' : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, (haτ.trans hτb).trans hbT⟩
    show (S7PIG5_evL B (ML L τ)) (Pj' L (F b - F a)) = tensorPow 2 (Pj L) (Jc b - Jc a) (ML L τ)
    rw [S7PIG5_evL_apply]
    show tensorPow 2 (Pj L) (((F b - F a : projTensor B 2)) : TensorDual B 2) (ML L τ) = _
    rw [hFd a b ha' hb]

end Core

end HRS.MS.R2Interp

end
