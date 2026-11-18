import HRS.MS.S104gJc2

/-!
# S10.4 packet S104G, part 4: joint continuity of `(t,r,x) ↦ ∇u₁(t) r (x)`

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_contOn_gradient`: the gradient of a classical adjoint solution is continuous in `(r,x)` on `[0,t] × ℝ^d`.
`s104g_jcont`: `(t,r,x) ↦ ∇u₁(t) r (x)` is continuous on `{0 ≤ r ≤ t ≤ T0}` when `u₁ t` is a classical adjoint solution for every `t ∈ [0,T0]`, the
difference quotients in `t` converge in `C^1` (`u₂` the limit, `‖∇u₂‖ ≤ Gb`), and `u₁ t` is Lipschitz in `r` towards its terminal value in the `C^1` sup norm.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole

variable {d : ℕ}

theorem s104g_contOn_gradient {C : WholeCoeff d} {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ContinuousOn (fun p : ℝ × Euc d => gradient (f p.1) p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
  have h1 : Continuous (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) := by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (hf.cont_c2 1 (by norm_num))
    have h2 := (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h
    refine h2.congr fun p => ?_
    simp [HRS.fderiv_eq_curry, gradient]
  have hq : Continuous (fun p : ℝ × Euc d => (Set.projIcc (0 : ℝ) t ht p.1, p.2)) :=
    ((continuous_projIcc).comp continuous_fst).prodMk continuous_snd
  refine (h1.comp hq).continuousOn.congr fun p hp => ?_
  simp [Set.projIcc_of_mem ht hp.1]

theorem s104g_jcont {C : WholeCoeff d} {u1 u2 : ℝ → ℝ → Euc d → ℝ} {T0 Gb M : ℝ} (hGb : 0 ≤ Gb) (hM : 0 ≤ M)
    (hcl : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∃ g : Euc d → ℝ, IsClassicalAdjointW C t g (u1 t))
    (hsm2 : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 1 (u2 t r))
    (dq : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ 1 (fun y => h⁻¹ * (u1 (t + h) r y - u1 t r y) - u2 t r y) x‖ ≤ e)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ 1 (u2 t r) x‖ ≤ Gb)
    (hMl : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x,
      ‖iteratedFDeriv ℝ 1 (fun y => u1 t r y - u1 t t y) x‖ ≤ M * (t - r)) :
    ContinuousOn (fun q : ℝ × ℝ × Euc d => gradient (u1 q.1 q.2.1) q.2.2)
      {q : ℝ × ℝ × Euc d | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0} := by
  have hsm1 : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (u1 t r) := by
    intro t ht r hr
    obtain ⟨g, hg⟩ := hcl t ht
    exact hg.c2 r hr
  have hLip := s104g_lipT hsm1 hsm2 dq (Gb := Gb) (fun t ht r hr x => by
    rw [s104g_norm_gradient, ← norm_iteratedFDeriv_one]; exact hb t ht r hr x)
  refine s104g_jcont_abstract (G := fun t r x => gradient (u1 t r) x) hGb hM ?_ hLip ?_
  · intro t ht
    obtain ⟨g, hg⟩ := hcl t ht
    exact s104g_contOn_gradient ht.1 hg
  · intro t ht r hr hrt x
    have hd1 : DifferentiableAt ℝ (u1 t r) x :=
      ((hsm1 t ht r ⟨hr, hrt⟩).differentiable (by norm_num)).differentiableAt
    have hd0 : DifferentiableAt ℝ (u1 t t) x :=
      ((hsm1 t ht t ⟨ht.1, le_rfl⟩).differentiable (by norm_num)).differentiableAt
    show ‖gradient (u1 t r) x - gradient (u1 t t) x‖ ≤ _
    rw [← s104g_gradient_sub hd1 hd0, s104g_norm_gradient, ← norm_iteratedFDeriv_one]
    exact hMl t ht r ⟨hr, hrt⟩ x

end HRS.MS.R2WinOrbNL

end
