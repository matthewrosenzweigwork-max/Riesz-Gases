import HRS.MS.SA16E1Geo2

/-!
# S.A.16 E1: `charFlow_geometry`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

/-- E1: the additive-noise flow is a diffeomorphism with bounds independent
of the entire noise path. This is a deterministic finite-regularity result. -/
theorem charFlow_geometry (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (B T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ b, DriftBounds d k B b →
      ∀ ν : ℝ, 0 ≤ ν → ∀ w : ℝ≥0 → Fin d → ℝ, Continuous w → w 0=0 →
      ∀ t ∈ Icc (0 : ℝ) T,
      Function.Bijective (charFlow d b ν w t) ∧
      ContDiff ℝ k (charFlow d b ν w t) ∧
      ContDiff ℝ k (Function.invFun (charFlow d b ν w t)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x,
        ‖iteratedFDeriv ℝ j (charFlow d b ν w t) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ j (Function.invFun (charFlow d b ν w t)) x‖ ≤ C) ∧
      (∀ x, |LinearMap.det (fderiv ℝ (charFlow d b ν w t) x).toLinearMap|=
        Real.exp (-(∫ r in Icc (0 : ℝ) t,
          movDiv (b r) (charFlow d b ν w r x)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨C, hCpos, hC⟩ := HRS.MS.SA16E1.e1_det d m T (max B 0) hT (le_max_right _ _)
  refine ⟨C, hCpos, fun b hb ν hν w hw hw0 t ht => ?_⟩
  obtain ⟨Λg, -, hDB⟩ := e1_driftBounds hb ν hw (T := T)
  have hflow := e1_negFlow hk hb ν hw hw0 T
  set Ψ : ℝ → Euc d → Euc d := fun τ y => charFlow d b ν w τ y - e1a d ν w τ with hΨ
  have hdb : ∀ s ∈ Icc (0:ℝ) T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (e1bt d ν w b s) x‖ ≤ max B 0 := fun s hs j h1 h2 x =>
    (e1_hdb hb ν w s hs j h1 h2 x).trans (le_max_left _ _)
  obtain ⟨hΨb, hΦ⟩ := hC Λg (e1bt d ν w b) hDB hdb Ψ hflow t ht
  obtain ⟨Φ, hΦ1, hΦ2, -⟩ := HRS.MS.FlowA.flow_invertible hT hDB hflow t ht
  obtain ⟨hΦcd, hΦb⟩ := hΦ Φ hΦ1 hΦ2
  have hX : charFlow d b ν w t = fun y => Ψ t y + e1a d ν w t := by
    funext y; simp [hΨ]
  have hΨcd : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ t) :=
    HRS.MS.FlowB.flow_contDiff hT hDB hflow t ht
  have hinj : Function.Injective (charFlow d b ν w t) := by
    intro y y' h
    rw [hX] at h
    have h' : Ψ t y = Ψ t y' := add_right_cancel h
    rw [← hΦ1 y, ← hΦ1 y', h']
  have hsurj : Function.Surjective (charFlow d b ν w t) := by
    intro z
    refine ⟨Φ (z - e1a d ν w t), ?_⟩
    rw [hX]
    simp only [hΦ2, sub_add_cancel]
  have hinv : Function.invFun (charFlow d b ν w t) = fun z => Φ (z + (-(e1a d ν w t))) := by
    funext z
    obtain ⟨y, rfl⟩ := hsurj z
    rw [Function.leftInverse_invFun hinj y, hX]
    simp [hΦ1]
  refine ⟨⟨hinj, hsurj⟩, ?_, ?_, ?_, ?_⟩
  · rw [hX]; exact hΨcd.add contDiff_const
  · rw [hinv]; exact hΦcd.comp (contDiff_id.add contDiff_const)
  · intro j hj1 hjm x
    refine ⟨?_, ?_⟩
    · rw [hX, e1_ifd_add_const hj1 (hΨcd.of_le (by exact_mod_cast hjm))]
      exact hΨb j hj1 hjm x
    · rw [hinv, iteratedFDeriv_comp_add_right]
      exact hΦb j hj1 hjm _
  · intro x
    have hf : fderiv ℝ (charFlow d b ν w t) x =
        fderiv ℝ (fun y => charFlow d b ν w t y - e1a d ν w t) x := by
      rw [fderiv_sub_const]
    rw [hf, e1_det_formula hT hb ν hw hw0 x ht, abs_of_pos (Real.exp_pos _),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]

end HRS.Whole.AppendixA.Phase2SA16Evolution
