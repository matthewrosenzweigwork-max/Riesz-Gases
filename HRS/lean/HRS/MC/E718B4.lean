import HRS.MC.E718B3

/-!
# Row 7.18 (packet e718b), file 4: the process along an orthonormal sequence is a standard Gaussian sequence
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.MC.E718B

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : H → Ω → ℝ}

lemma IsIsonormal.stdSeq (hW : IsIsonormal P W) (g : ℕ → H) (hg : Orthonormal ℝ g) :
    HRS.IsStdGaussianSeq P (fun i => W (g i)) := by
  have hpi : ∀ N : ℕ, 0 < N → P.map (fun ω (k : Fin N) => W (g k) ω) =
      Measure.pi (fun _ : Fin N => gaussianReal 0 1) := fun N hN =>
    hW.law_pi hN (fun k : Fin N => g k) (hg.comp _ Fin.val_injective)
  have hmeas : ∀ i, AEMeasurable (W (g i)) P := fun i => hW.aemeasurable_W _ (hg.ne_zero i)
  have hlaw : ∀ i, HRS.law P (W (g i)) = gaussianReal 0 1 := by
    intro i
    have h1 := hpi (i + 1) (Nat.succ_pos i)
    have h2 : P.map (W (g i)) =
        (P.map (fun ω (k : Fin (i + 1)) => W (g k) ω)).map (fun z => z (Fin.last i)) := by
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply _).aemeasurable
        (hW.aemeasurable_vecf (fun k : Fin (i + 1) => g k) (hg.comp _ Fin.val_injective))]
      rfl
    unfold HRS.law
    rw [h2, h1]
    exact (measurePreserving_eval (fun _ : Fin (i + 1) => gaussianReal 0 1) (Fin.last i)).map_eq
  refine ⟨?_, hlaw⟩
  rw [iIndepFun_iff_finset]
  intro s
  set N := s.sup id + 1 with hN
  have hind : iIndepFun (fun k : Fin N => W (g k)) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun k : Fin N => W (g k)) (fun k => hmeas k), hpi N (Nat.succ_pos _)]
    congr 1
    ext k : 1
    exact (hlaw k).symm
  have hlt : ∀ x : s, (x : ℕ) < N := fun x => Nat.lt_succ_of_le (Finset.le_sup (f := id) x.2)
  exact hind.precomp (g := fun x : s => (⟨x, hlt x⟩ : Fin N)) (fun x y hxy => Subtype.ext (by
    simpa using congrArg Fin.val hxy))

end

end HRS.MC.E718B
