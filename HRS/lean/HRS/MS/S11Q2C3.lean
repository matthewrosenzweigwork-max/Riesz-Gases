import HRS.MS.S113X2C13

/-!
# S11.3 Liouville (worker S11Q2), C3: the cut-off drift

For a bounded set `D` with closure compact in the collision-free set, a bounded globally Lipschitz field `b~` on `EucConfig d N` which
agrees with the physical drift `b = particleDriftW (quadraticGradientDyn d s q β)` on `closure D`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S11Q2

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B HRS.MS.S113X2C
open HRS.MC.CepP3 (Jc)

theorem s11q2_cutoff_drift (d N : ℕ) (s q β : ℝ) {D : Set (EucConfig d N)} (hDc : IsCompact (closure D))
    (hfree : closure D ⊆ (eucCollisionSet d N)ᶜ) :
    ∃ (bt : EucConfig d N → EucConfig d N) (L M : ℝ), 0 ≤ L ∧ 0 ≤ M ∧ (∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖) ∧
      (∀ x, ‖bt x‖ ≤ M) ∧ Continuous bt ∧
      ∀ x ∈ closure D, bt x = particleDriftW (quadraticGradientDyn d s q β) x := by
  set e := Jc d N with he
  have hKE : IsCompact (e ⁻¹' closure D) := (e.toHomeomorph.isCompact_preimage).2 hDc
  have hUE : IsOpen {z | e z ∉ eucCollisionSet d N} := (s113a_isOpen_free d N).preimage e.continuous
  obtain ⟨θ', G, hθ', hθ'c, hθ'U, -, hGo, hKG, hθ'G⟩ :=
    s113c_cutoff hKE hUE (fun z hz => hfree hz)
  set θ : EucConfig d N → ℝ := fun x => θ' (e.symm x) with hθ
  have hθd : ContDiff ℝ ∞ θ := hθ'.comp e.symm.contDiff
  have hθc : HasCompactSupport θ := hθ'c.comp_homeomorph e.symm.toHomeomorph
  have hts : ∀ x ∈ tsupport θ, x ∉ eucCollisionSet d N := by
    intro x hx
    have : e.symm x ∈ tsupport θ' := by
      have h1 : tsupport θ = e.symm ⁻¹' tsupport θ' := by
        unfold tsupport
        rw [show Function.support θ = e.symm ⁻¹' Function.support θ' from rfl]
        exact (e.symm.toHomeomorph.preimage_closure _).symm
      rw [h1] at hx; exact hx
    have := hθ'U this
    simpa using this
  set b : EucConfig d N → EucConfig d N := fun x => particleDriftW (quadraticGradientDyn d s q β) x with hb
  have hbd : ContDiffOn ℝ ∞ b (eucCollisionSet d N)ᶜ := s113a_drift_contDiffOn (N := N) s q β
  set bt : EucConfig d N → EucConfig d N := fun x => θ x • b x with hbt
  have hbtd : ContDiff ℝ ∞ bt := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport θ
    · exact (hθd.contDiffAt.smul (hbd.contDiffAt ((s113a_isOpen_free d N).mem_nhds (hts z hz))))
    · have hev : θ =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
      have : bt =ᶠ[𝓝 z] fun _ => (0 : EucConfig d N) := by
        filter_upwards [hev] with w hw
        simp [hbt, hw]
      exact (contDiffAt_const).congr_of_eventuallyEq this
  have hbtc : HasCompactSupport bt := hθc.smul_right
  obtain ⟨L, hL⟩ := hbtd.lipschitzWith_of_hasCompactSupport hbtc (by simp)
  obtain ⟨M, hM⟩ := (hbtd.continuous).bounded_above_of_compact_support hbtc
  refine ⟨bt, max (L : ℝ) 0, max M 0, le_max_right _ _, le_max_right _ _, fun x y => ?_, fun x => (hM x).trans (le_max_left _ _),
    hbtd.continuous, fun x hx => ?_⟩
  · have := hL.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have h1 : θ x = 1 := by
      simp only [hθ]
      refine hθ'G _ (hKG ?_)
      show e (e.symm x) ∈ closure D
      simpa using hx
    simp [hbt, h1, hb]

end HRS.MS.S11Q2

end
