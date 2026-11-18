import HRS.MS.R2WinOrbAux10

/-!
# S10.3 (stationary half), part 11: the cosine coefficient of an orbit family is `C^k` with the integrated-by-parts bound

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  Hypotheses `s103_famHyp`: a family `F a t` (`a ≤ 2`, `t ∈ [0,T0]`) of `C^k` functions with uniform
`C^j` bounds `A` and `C^j`-sup difference quotients converging to the next member.
* `s103_jet_cos_bound`: `‖∫_0^T e_n(u) D^jF 0 (b+u)(x) du‖ ≤ s103_cosBound T A n`.
* `s103_window_core`: `x ↦ ∫_0^T e_n(u) F 0 (b+u)(x) du` is `C^k` with all `D^j`, `j ≤ k`, bounded by `s103_cosBound T A n`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

/-- Hypotheses on the orbit family. -/
structure s103_famHyp (F : ℕ → ℝ → Euc d → ℝ) (k : ℕ) (T0 A : ℝ) : Prop where
  cd : ∀ a ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) T0, ContDiff ℝ k (F a t)
  bd : ∀ a ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (F a t) x‖ ≤ A
  dq : ∀ a < 2, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
    t + h ∈ Set.Icc (0 : ℝ) T0 → ∀ j ≤ k, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (F a (t + h) y - F a t y) - F (a + 1) t y) x‖ ≤ ε

theorem s103_famHyp.deriv {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} {T0 A : ℝ} (H : s103_famHyp F k T0 A) {a : ℕ}
    (ha : a < 2) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T0, HasDerivWithinAt (fun τ => iteratedFDeriv ℝ j (F a τ) x)
      (iteratedFDeriv ℝ j (F (a + 1) t) x) (Set.Icc 0 T0) t :=
  s103_hasDeriv_iter (fun τ hτ => (H.cd a (by omega) τ hτ).of_le (by exact_mod_cast hj))
    (fun τ hτ => (H.cd (a + 1) (by omega) τ hτ).of_le (by exact_mod_cast hj))
    (fun t ht ε hε => by
      obtain ⟨δ, hδ, h⟩ := H.dq a ha t ht ε hε
      exact ⟨δ, hδ, fun h' h0 hd ht' x => h h' h0 hd ht' j hj x⟩) x

theorem s103_famHyp.val {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} {T0 A : ℝ} (H : s103_famHyp F k T0 A) {a : ℕ}
    (ha : a < 2) (x : Euc d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T0, HasDerivWithinAt (fun τ => F a τ x) (F (a + 1) t x) (Set.Icc 0 T0) t :=
  s103_hasDeriv_val (fun τ hτ => (H.cd a (by omega) τ hτ).of_le (by simp))
    (fun τ hτ => (H.cd (a + 1) (by omega) τ hτ).of_le (by simp))
    (fun t ht ε hε => by
      obtain ⟨δ, hδ, h⟩ := H.dq a ha t ht ε hε
      exact ⟨δ, hδ, fun h' h0 hd ht' x => h h' h0 hd ht' 0 (Nat.zero_le _) x⟩) x

theorem s103_jet_cos_bound {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} {T0 A b T : ℝ} (H : s103_famHyp F k T0 A)
    (hb : 0 ≤ b) (hT : 0 < T) (hbT : b + T ≤ T0) (hA : 0 ≤ A) {j : ℕ} (hj : j ≤ k) (x : Euc d) (n : ℕ) :
    ‖∫ p in Set.Icc (0 : ℝ) T, r2CosBasis T n p • iteratedFDeriv ℝ j (F 0 (b + p)) x‖ ≤
      s103_cosBound T A n := by
  have hIcc : ∀ p ∈ Set.Icc (0 : ℝ) T, b + p ∈ Set.Icc (0 : ℝ) T0 := fun p hp =>
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
  by_cases hn : n = 0
  · subst hn
    have hle := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) T)
      (f := fun p => r2CosBasis T 0 p • iteratedFDeriv ℝ j (F 0 (b + p)) x) (C := 1 / Real.sqrt T * A)
      (by simp) (fun p hp => by
        rw [norm_smul, Real.norm_eq_abs]
        have h1 := s103_cos_abs_le hT 0 p
        simp only [if_true] at h1
        exact mul_le_mul h1 (H.bd 0 (by norm_num) (b + p) (hIcc p hp) j hj x) (norm_nonneg _)
          (one_div_pos.2 (Real.sqrt_pos.2 hT)).le)
    refine hle.trans (le_of_eq ?_)
    have : (volume : Measure ℝ).real (Set.Icc (0 : ℝ) T) = T := by
      simp [Measure.real, Real.volume_Icc, hT.le]
    rw [this]
    unfold s103_cosBound
    simp only [if_true]
    ring
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    set lam : ℝ := (n : ℝ) * Real.pi / T with hlam
    have hlam0 : 0 < lam := by positivity
    have hsin : Real.sin (lam * T) = 0 := by
      have : lam * T = (n : ℝ) * Real.pi := by rw [hlam]; field_simp
      rw [this]; exact Real.sin_nat_mul_pi n
    set Ψ : ℝ → (Euc d [×j]→L[ℝ] ℝ) := fun u => iteratedFDeriv ℝ j (F 0 (b + u)) x with hΨ
    set Ψ1 : ℝ → (Euc d [×j]→L[ℝ] ℝ) := fun u => iteratedFDeriv ℝ j (F 1 (b + u)) x with hΨ1
    set Ψ2 : ℝ → (Euc d [×j]→L[ℝ] ℝ) := fun u => iteratedFDeriv ℝ j (F 2 (b + u)) x with hΨ2
    have hid : ∀ u : ℝ, HasDerivWithinAt (fun u : ℝ => b + u) 1 (Set.Icc (0 : ℝ) T) u := fun u =>
      ((hasDerivAt_id u).const_add b).hasDerivWithinAt
    have hmap : Set.MapsTo (fun u : ℝ => b + u) (Set.Icc (0 : ℝ) T) (Set.Icc (0 : ℝ) T0) := fun u hu => hIcc u hu
    have h0 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt Ψ (Ψ1 u) (Set.Icc 0 T) u := fun u hu => by
      have h := (H.deriv (a := 0) (by norm_num) hj x (b + u) (hIcc u hu)).scomp u (hid u) hmap
      rw [one_smul] at h
      exact h
    have h1 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt Ψ1 (Ψ2 u) (Set.Icc 0 T) u := fun u hu => by
      have h := (H.deriv (a := 1) (by norm_num) hj x (b + u) (hIcc u hu)).scomp u (hid u) hmap
      rw [one_smul] at h
      exact h
    have key := s103_ibp hlam0 hT hsin h0 h1 (A1 := A) (A2 := A)
      (fun u hu => H.bd 1 (by norm_num) (b + u) (hIcc u hu) j hj x)
      (fun u hu => H.bd 2 (by norm_num) (b + u) (hIcc u hu) j hj x)
    have e : ∫ p in Set.Icc (0 : ℝ) T, r2CosBasis T n p • iteratedFDeriv ℝ j (F 0 (b + p)) x =
        Real.sqrt (2 / T) • ∫ u in (0 : ℝ)..T, Real.cos (lam * u) • Ψ u := by
      rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Icc (fun p hp => ?_)
      simp only [r2CosBasis, hn, if_false, hΨ, hlam, smul_smul]
      congr 2
      ring_nf
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    unfold s103_cosBound
    simp only [hn, if_false]
    exact mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg _)

end HRS.MS.R2WinOrb

end
