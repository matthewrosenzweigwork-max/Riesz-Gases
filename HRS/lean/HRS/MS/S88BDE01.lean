import Mathlib

/-!
# S8.8.E01: right-derivative uniqueness for an eigen-orbit

`s88_right_eigen_orbit`: a curve `g` continuous on `[0,∞)` with right derivative `-ω g(t)` at every `t ≥ 0`
satisfies `g t = e^{-ωt} g 0`.  Proof: `h(t) = e^{ωt} g(t)` has right derivative `0` on `[0,t)` and is continuous on
`[0,t]`, hence constant (`constant_of_has_deriv_right_zero`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S88Breakdown

theorem s88_right_eigen_orbit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : ℝ → E) (ω : ℝ)
    (hcont : ContinuousOn g (Set.Ici (0 : ℝ)))
    (hder : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt g ((-ω) • g t) (Set.Ici t) t) :
    ∀ t : ℝ, 0 ≤ t → g t = Real.exp (-ω * t) • g 0 := by
  intro t ht
  set h : ℝ → E := fun s => Real.exp (ω * s) • g s with hh
  have hc : ContinuousOn h (Set.Icc 0 t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).smul
      (hcont.mono Set.Icc_subset_Ici_self)
  have hd : ∀ x ∈ Set.Ico 0 t, HasDerivWithinAt h 0 (Set.Ici x) x := by
    intro x hx
    have h1 : HasDerivWithinAt (fun s : ℝ => Real.exp (ω * s)) (Real.exp (ω * x) * ω)
        (Set.Ici x) x := by
      have := ((hasDerivAt_id x).const_mul ω).exp
      simpa [mul_comm] using this.hasDerivWithinAt
    have h2 := h1.smul (hder x hx.1)
    convert h2 using 1
    rw [smul_smul, ← add_smul, show Real.exp (ω * x) * -ω + Real.exp (ω * x) * ω = 0 by ring,
      zero_smul]
  have key := constant_of_has_deriv_right_zero hc hd t ⟨ht, le_rfl⟩
  have e0 : h 0 = g 0 := by simp [hh]
  rw [e0] at key
  have : g t = Real.exp (-ω * t) • h t := by
    simp only [hh, smul_smul, ← Real.exp_add]
    simp
  rw [this, key]

end HRS.MS.S88Breakdown
