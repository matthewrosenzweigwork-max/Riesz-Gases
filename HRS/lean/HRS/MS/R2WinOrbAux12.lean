import HRS.MS.R2WinOrbAux11

/-!
# S10.3 (stationary half), part 12: regularity and bound of a cosine coefficient of an orbit family

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_window_core`: under `s103_famHyp`, the function
`x ↦ ∫_0^T e_n(u) F 0 (b+u)(x) du` is `C^k` and all its derivatives `D^j`, `j ≤ k`, are bounded by `s103_cosBound T A n`
(differentiation under the integral sign, `contDiff_integral_dominated`, then `s103_jet_cos_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem s103_window_core {F : ℕ → ℝ → Euc d → ℝ} {k : ℕ} (hk : 1 ≤ k) {T0 A b T : ℝ}
    (H : s103_famHyp F k T0 A) (hb : 0 ≤ b) (hT : 0 < T) (hbT : b + T ≤ T0) (hA : 0 ≤ A) (n : ℕ) :
    ContDiff ℝ k (fun x => ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F 0 (b + u) x) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F 0 (b + u) x) x‖ ≤ s103_cosBound T A n := by
  set cl : ℝ → ℝ := fun u => b + max 0 (min u T) with hcl
  have hcl_cont : Continuous cl := by simp only [hcl]; fun_prop
  have hcl_mem : ∀ u, cl u ∈ Set.Icc (0 : ℝ) T0 := fun u =>
    ⟨by have := le_max_left 0 (min u T); simp only [hcl]; linarith,
     by have : max 0 (min u T) ≤ T := max_le hT.le (min_le_right _ _)
        simp only [hcl]; linarith⟩
  have hcl_eq : ∀ u ∈ Set.Icc (0 : ℝ) T, cl u = b + u := fun u hu => by
    simp only [hcl, min_eq_left hu.2, max_eq_right hu.1]
  have hjc : ∀ j ≤ k, ∀ x, ContinuousOn (fun τ => iteratedFDeriv ℝ j (F 0 τ) x) (Set.Icc (0 : ℝ) T0) :=
    fun j hj x t ht => (H.deriv (a := 0) (by norm_num) hj x t ht).continuousWithinAt
  have hvc : ∀ x, ContinuousOn (fun τ => F 0 τ x) (Set.Icc (0 : ℝ) T0) :=
    fun x t ht => (H.val (a := 0) (by norm_num) x t ht).continuousWithinAt
  set w : ℝ → ℝ := r2CosBasis T n with hw
  have hwc : Continuous w := s103_cosBasis_continuous T n
  set W : ℝ := if n = 0 then 1 / Real.sqrt T else Real.sqrt (2 / T) with hW
  have hW0 : 0 ≤ W := by
    simp only [hW]; split_ifs
    · exact (one_div_pos.2 (Real.sqrt_pos.2 hT)).le
    · exact Real.sqrt_nonneg _
  set g : ℝ → Euc d → ℝ := fun u => w u • F 0 (cl u) with hg
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have hgcd : ∀ u, ContDiff ℝ k (g u) := fun u => (H.cd 0 (by norm_num) _ (hcl_mem u)).const_smul (w u)
  have hgjet : ∀ u j, j ≤ k → ∀ x, iteratedFDeriv ℝ j (g u) x = w u • iteratedFDeriv ℝ j (F 0 (cl u)) x := by
    intro u j hj x
    exact iteratedFDeriv_const_smul_apply
      (((H.cd 0 (by norm_num) _ (hcl_mem u)).of_le (by exact_mod_cast hj)).contDiffAt)
  have hint : ∀ x, Integrable (fun u => g u x) ν := by
    intro x
    have hcont : Continuous (fun u => g u x) := by
      have : Continuous (fun u => F 0 (cl u) x) :=
        (hvc x).comp_continuous hcl_cont hcl_mem
      exact hwc.mul this
    exact hcont.integrableOn_Icc
  have hmeas : ∀ j ≤ k, ∀ x, AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (g u) x) ν := by
    intro j hj x
    have hcont : Continuous (fun u => iteratedFDeriv ℝ j (g u) x) := by
      have h1 : Continuous (fun u => iteratedFDeriv ℝ j (F 0 (cl u)) x) :=
        (hjc j hj x).comp_continuous hcl_cont hcl_mem
      have : (fun u => iteratedFDeriv ℝ j (g u) x) = fun u => w u • iteratedFDeriv ℝ j (F 0 (cl u)) x :=
        funext fun u => hgjet u j hj x
      rw [this]
      exact hwc.smul h1
    exact hcont.aestronglyMeasurable
  have hbound : ∀ j, 1 ≤ j → j ≤ k → ∀ p x, ‖iteratedFDeriv ℝ j (g p) x‖ ≤ W * A := by
    intro j _ hj p x
    rw [hgjet p j hj x, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (s103_cos_abs_le hT n p) (H.bd 0 (by norm_num) _ (hcl_mem p) j hj x)
      (norm_nonneg _) hW0
  obtain ⟨hCD, hDj⟩ := contDiff_integral_dominated (B := Euc d) ν g k hk hgcd hint hmeas
    (fun _ _ => W * A) (fun _ _ _ => integrable_const _) hbound
  have hfun : (fun x => ∫ p, g p x ∂ν) = fun x => ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F 0 (b + u) x := by
    funext x
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    simp only [hg, hcl_eq u hu, hw]
    rfl
  rw [hfun] at hCD hDj
  refine ⟨hCD, fun j hj x => ?_⟩
  rw [hDj j hj x]
  have : ∫ p, iteratedFDeriv ℝ j (g p) x ∂ν =
      ∫ p in Set.Icc (0 : ℝ) T, r2CosBasis T n p • iteratedFDeriv ℝ j (F 0 (b + p)) x := by
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    simp only [hgjet u j hj x, hcl_eq u hu, hw]
  rw [this]
  exact s103_jet_cos_bound H hb hT hbT hA hj x n

end HRS.MS.R2WinOrb

end
