import HRS.MS.SA12C14

/-!
# S.A.12(c), packet E7.03 (part 4): measurability of the remainder kernel on the cube

`ρ_v(z) = D^βγ_L(z) - χ̂(v-z) D^β g(z)` is continuous on the open set of off-lattice points; the centred cube is
contained in that set up to the single point `0`, hence `ρ_v` is `AEStronglyMeasurable` on the cube.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_contOn_iter {f : Euc d → ℝ} {U : Set (Euc d)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) : ContinuousOn (iteratedFDeriv ℝ n f) U := by
  have h1 := hf.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top) hU.uniqueDiffOn
  exact h1.congr (iteratedFDerivWithin_of_isOpen n hU).symm

theorem sa12c_pd_contOn {f : Euc d → ℝ} {U : Set (Euc d)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {n : ℕ} (β : Fin n → Fin d) : ContinuousOn (partialDeriv β f) U :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
    (fun l => (EuclideanSpace.single (β l) (1 : ℝ) : Euc d))).continuous.comp_continuousOn
    (sa12c_contOn_iter hU hf n)

theorem sa12c_cube_sub_U {L : ℝ} (hL : 0 < L) :
    sa12cCube d L ⊆ {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k} ∪ {0} := by
  intro z hz
  by_cases hU : ∀ k : Fin d → ℤ, z ≠ L • latticePt k
  · exact Or.inl hU
  · right
    push Not at hU
    obtain ⟨k, hk⟩ := hU
    have hz0 : z = 0 := by
      ext i
      have h := abs_le.1 (hz i)
      have hki : z i = L * (k i : ℝ) := by
        rw [hk]; simp [latticePt]
      rw [hki] at h ⊢
      have h1 : -(1 / 2 : ℝ) ≤ (k i : ℝ) := by
        by_contra hc; push Not at hc; nlinarith [h.1]
      have h2 : (k i : ℝ) < 1 := by
        by_contra hc; push Not at hc; nlinarith [h.2]
      have h3 : k i = 0 := by
        have : -1 < k i := by exact_mod_cast (by linarith : (-1 : ℝ) < k i)
        have : k i < 1 := by exact_mod_cast h2
        omega
      simp [h3]
    simp [hz0]

theorem sa12c_aesm_cube (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) {f : Euc d → ℝ}
    (hf : ContinuousOn f {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k}) :
    AEStronglyMeasurable f (volume.restrict (sa12cCube d L)) := by
  have hUo := HRS.MS.Ker1.ker1_isOpen_offLattice (d := d) hL
  have h1 : AEStronglyMeasurable f (volume.restrict {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k}) :=
    hf.aestronglyMeasurable hUo.measurableSet
  haveI : NeZero d := ⟨by omega⟩
  have h0 : (volume : Measure (Euc d)).restrict {0} = 0 := by
    rw [Measure.restrict_eq_zero]; exact measure_singleton _
  have h2 : AEStronglyMeasurable f ((volume : Measure (Euc d)).restrict
      {x : Euc d | ∀ k : Fin d → ℤ, x ≠ L • latticePt k} + (volume : Measure (Euc d)).restrict {0}) :=
    h1.add_measure (by rw [h0]; exact aestronglyMeasurable_zero_measure f)
  refine h2.mono_measure ?_
  refine (Measure.restrict_mono (sa12c_cube_sub_U hL) le_rfl).trans ?_
  exact Measure.restrict_union_le _ _

end HRS.MH.AdjointRd.Phase2SA12C
