import HRS.MS.Fp81S21QwinUniform2
import HRS.MS.R2WinOrbAux11

/-!
# HRS S2.1(iii), SOL26 packet 27c: derivative-valued cosine integration by parts

This file packages the existing Banach-valued integration-by-parts estimate for the
spatial jets of a time-dependent orbit family. The endpoints are retained explicitly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R2WinOrb

/-- Banach-valued cosine integration by parts with both endpoint first derivatives.
The second derivative is bounded uniformly on the interval; the resulting estimate is
`(‖g'(T)‖ + ‖g'(0)‖ + T sup ‖g''‖) / lam²`. -/
theorem fp81s21_qwin_cos_ibp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    (hsin : Real.sin (lam * T) = 0)
    {g g' g'' : ℝ → E}
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g (g' t) (Set.Icc 0 T) t)
    (hg' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g' (g'' t) (Set.Icc 0 T) t)
    {B₁ B₂ : ℝ}
    (hB₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖g' t‖ ≤ B₁)
    (hB₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖g'' t‖ ≤ B₂) :
    ‖∫ t in (0 : ℝ)..T, Real.cos (lam * t) • g t‖ ≤
      (2 * B₁ + T * B₂) / lam ^ 2 := by
  exact HRS.MS.R2WinOrb.s103_ibp hlam hT hsin hg hg' hB₁ hB₂

/-- Apply the same estimate pointwise to a spatial jet of an orbit family.
The family hypothesis provides the within-interval time derivatives of every jet. -/
theorem fp81s21_qwin_cos_jet_ibp
    {d : ℕ} {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} {T₀ A b T : ℝ}
    (H : HRS.MS.R2WinOrb.s103_famHyp F k T₀ A)
    (hb : 0 ≤ b) (hT : 0 < T) (hbT : b + T ≤ T₀)
    {j : ℕ} (hj : j ≤ k) (x : Euc d) (n : ℕ) (hn : 1 ≤ n)
    {B₁ B₂ : ℝ}
    (hB₁ : ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖iteratedFDeriv ℝ j (F 1 (b + u)) x‖ ≤ B₁)
    (hB₂ : ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖iteratedFDeriv ℝ j (F 2 (b + u)) x‖ ≤ B₂) :
    ‖∫ u in (0 : ℝ)..T,
      Real.cos (((n : ℝ) * Real.pi / T) * u) •
        iteratedFDeriv ℝ j (F 0 (b + u)) x‖ ≤
      (2 * B₁ + T * B₂) / ((n : ℝ) * Real.pi / T) ^ 2 := by
  let lam : ℝ := (n : ℝ) * Real.pi / T
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hsin : Real.sin (lam * T) = 0 := by
    have hlamT : lam * T = (n : ℝ) * Real.pi := by
      dsimp [lam]
      field_simp
    rw [hlamT]
    exact Real.sin_nat_mul_pi n
  have hIcc : ∀ u ∈ Set.Icc (0 : ℝ) T, b + u ∈ Set.Icc (0 : ℝ) T₀ := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2, hbT]⟩
  have hid : ∀ u : ℝ,
      HasDerivWithinAt (fun u : ℝ => b + u) 1 (Set.Icc (0 : ℝ) T) u := by
    intro u
    exact ((hasDerivAt_id u).const_add b).hasDerivWithinAt
  have hmap : Set.MapsTo (fun u : ℝ => b + u)
      (Set.Icc (0 : ℝ) T) (Set.Icc (0 : ℝ) T₀) := fun u hu => hIcc u hu
  set Ψ : ℝ → (Euc d [×j]→L[ℝ] ℝ) :=
    fun u => iteratedFDeriv ℝ j (F 0 (b + u)) x
  set Ψ₁ : ℝ → (Euc d [×j]→L[ℝ] ℝ) :=
    fun u => iteratedFDeriv ℝ j (F 1 (b + u)) x
  set Ψ₂ : ℝ → (Euc d [×j]→L[ℝ] ℝ) :=
    fun u => iteratedFDeriv ℝ j (F 2 (b + u)) x
  have h0 : ∀ u ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ (Ψ₁ u) (Set.Icc 0 T) u := by
    intro u hu
    have h := (H.deriv (a := 0) (by norm_num) hj x (b + u) (hIcc u hu)).scomp u
      (hid u) hmap
    rw [one_smul] at h
    exact h
  have h1 : ∀ u ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ₁ (Ψ₂ u) (Set.Icc 0 T) u := by
    intro u hu
    have h := (H.deriv (a := 1) (by norm_num) hj x (b + u) (hIcc u hu)).scomp u
      (hid u) hmap
    rw [one_smul] at h
    exact h
  have hbound1 : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖Ψ₁ u‖ ≤ B₁ := hB₁
  have hbound2 : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖Ψ₂ u‖ ≤ B₂ := hB₂
  have hmain := HRS.MS.R2WinOrb.s103_ibp hlam hT hsin h0 h1 hbound1 hbound2
  simpa [lam, Ψ] using hmain




/-- Differentiation under the cosine-window integral, with the spatial jet left
inside the integral. This is the identity needed to apply the previous lemma to
the actual window coefficient. -/
theorem fp81s21_qwin_window_jet_eq
    {d : ℕ} {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} {T₀ A b T : ℝ}
    (H : HRS.MS.R2WinOrb.s103_famHyp F k T₀ A)
    (hb : 0 ≤ b) (hT : 0 < T) (hbT : b + T ≤ T₀)
    (hk : 1 ≤ k) {n j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ContDiff ℝ k
        (fun x => ∫ u in Set.Icc (0 : ℝ) T,
          r2CosBasis T n u * F 0 (b + u) x) ∧
      iteratedFDeriv ℝ j
          (fun x => ∫ u in Set.Icc (0 : ℝ) T,
            r2CosBasis T n u * F 0 (b + u) x) x =
        ∫ u in Set.Icc (0 : ℝ) T,
          r2CosBasis T n u • iteratedFDeriv ℝ j (F 0 (b + u)) x := by
  set cl : ℝ → ℝ := fun u => b + max 0 (min u T) with hcl
  have hcl_cont : Continuous cl := by
    simp only [hcl]
    fun_prop
  have hcl_mem : ∀ u, cl u ∈ Set.Icc (0 : ℝ) T₀ := fun u => by
    constructor
    · have h := le_max_left 0 (min u T)
      simp only [hcl]
      linarith [hb]
    · have h : max 0 (min u T) ≤ T := max_le hT.le (min_le_right _ _)
      simp only [hcl]
      linarith
  have hcl_eq : ∀ u ∈ Set.Icc (0 : ℝ) T, cl u = b + u := by
    intro u hu
    simp [hcl, min_eq_left hu.2, max_eq_right hu.1]
  have hjc : ∀ j' ≤ k, ∀ x',
      ContinuousOn (fun τ => iteratedFDeriv ℝ j' (F 0 τ) x')
        (Set.Icc (0 : ℝ) T₀) := by
    intro j' hj' x' t ht
    exact (H.deriv (a := 0) (by norm_num) hj' x' t ht).continuousWithinAt
  have hvc : ∀ x', ContinuousOn (fun τ => F 0 τ x') (Set.Icc (0 : ℝ) T₀) := by
    intro x' t ht
    exact (H.val (a := 0) (by norm_num) x' t ht).continuousWithinAt
  set w : ℝ → ℝ := r2CosBasis T n with hw
  have hwc : Continuous w := s103_cosBasis_continuous T n
  set W : ℝ := if n = 0 then 1 / Real.sqrt T else Real.sqrt (2 / T) with hW
  have hW0 : 0 ≤ W := by
    simp only [hW]
    split_ifs
    · exact (one_div_pos.2 (Real.sqrt_pos.2 hT)).le
    · exact Real.sqrt_nonneg _
  set g : ℝ → Euc d → ℝ := fun u => w u • F 0 (cl u) with hg
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have hgcd : ∀ u, ContDiff ℝ k (g u) := by
    intro u
    exact (H.cd 0 (by norm_num) (cl u) (hcl_mem u)).const_smul (w u)
  have hgjet : ∀ u j', j' ≤ k → ∀ x',
      iteratedFDeriv ℝ j' (g u) x' =
        w u • iteratedFDeriv ℝ j' (F 0 (cl u)) x' := by
    intro u j' hj' x'
    exact iteratedFDeriv_const_smul_apply
      (((H.cd 0 (by norm_num) (cl u) (hcl_mem u)).of_le
        (by exact_mod_cast hj')).contDiffAt)
  have hint : ∀ x', Integrable (fun u => g u x') ν := by
    intro x'
    have hcont : Continuous (fun u => g u x') := by
      have hF : Continuous (fun u => F 0 (cl u) x') :=
        (hvc x').comp_continuous hcl_cont hcl_mem
      exact hwc.smul hF
    exact hcont.integrableOn_Icc
  have hmeas : ∀ j' ≤ k, ∀ x',
      AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j' (g u) x') ν := by
    intro j' hj' x'
    have hcont : Continuous (fun u => iteratedFDeriv ℝ j' (g u) x') := by
      have hF : Continuous
          (fun u => iteratedFDeriv ℝ j' (F 0 (cl u)) x') :=
        (hjc j' hj' x').comp_continuous hcl_cont hcl_mem
      have heq : (fun u => iteratedFDeriv ℝ j' (g u) x') =
          fun u => w u • iteratedFDeriv ℝ j' (F 0 (cl u)) x' :=
        funext fun u => hgjet u j' hj' x'
      rw [heq]
      exact hwc.smul hF
    exact hcont.aestronglyMeasurable
  have hbound : ∀ j', 1 ≤ j' → j' ≤ k → ∀ u x',
      ‖iteratedFDeriv ℝ j' (g u) x'‖ ≤ W * A := by
    intro j' hj' hj u x'
    rw [hgjet u j' hj x', norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa [w, W] using s103_cos_abs_le hT n u)
      (H.bd 0 (by norm_num) (cl u) (hcl_mem u) j' hj x')
      (norm_nonneg _) hW0
  obtain ⟨hCD, hDj⟩ := contDiff_integral_dominated
    (B := Euc d) ν g k hk hgcd hint hmeas
    (fun _ _ => W * A) (fun _ _ _ => integrable_const _) hbound
  have hfun : (fun x' => ∫ u, g u x' ∂ν) =
      fun x' => ∫ u in Set.Icc (0 : ℝ) T,
        r2CosBasis T n u * F 0 (b + u) x' := by
    funext x'
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    simp [hg, hcl_eq u hu, hw]
  rw [hfun] at hCD hDj
  refine ⟨hCD, ?_⟩
  rw [hDj j hj x]
  have hset : (∫ u, iteratedFDeriv ℝ j (g u) x ∂ν) =
      ∫ u in Set.Icc (0 : ℝ) T,
        r2CosBasis T n u • iteratedFDeriv ℝ j (F 0 (b + u)) x := by
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    simp [hgjet u j hj x, hcl_eq u hu, hw]
  exact hset

#print axioms fp81s21_qwin_cos_ibp
#print axioms fp81s21_qwin_cos_jet_ibp
#print axioms fp81s21_qwin_window_jet_eq

end HRS.Fp81.S21

end
