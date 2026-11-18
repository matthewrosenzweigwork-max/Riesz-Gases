import HRS.MS.S104eC0

/-!
# S104E route C, packet C5 part A: Hölder interpolation and Hölder membership of `C^{j+2}_b` functions

`interp_hol`: `HolB j η B f` with all jets `≤ j+1` bounded by `ε` gives `HolB j η' (max ε ((2ε)^{1-η'/η} B^{η'/η})) f` for `η' < η`
(so time continuity in the sup norm of the jets plus `HolB η`-boundedness gives time continuity in the `η'`-norm).
`holB_of_bd`: `Bd (j+2) M f → HolB j η (2M) f` for `0 < η ≤ 1`.
-/

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem min_le_rpow_mul {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    calc a = a ^ (1 - θ) * a ^ θ := by rw [← Real.rpow_add' ha (by linarith)]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab h0) (Real.rpow_nonneg ha _)
  · rw [min_eq_right hab]
    calc b = b ^ (1 - θ) * b ^ θ := by rw [← Real.rpow_add' hb (by linarith)]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ := by
        refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb hab (by linarith)) (Real.rpow_nonneg hb _)

theorem interp_hol {j : ℕ} {η η' B ε : ℝ} (hη' : 0 < η') (hηη : η' < η) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    {f : Euc d → ℝ} (hf : HolB j η B f) (hs : ∀ i ≤ j + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ ε) :
    HolB j η' (max ε ((2 * ε) ^ (1 - η' / η) * B ^ (η' / η))) f := by
  have hη : 0 < η := hη'.trans hηη
  set θ : ℝ := η' / η with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hη]; exact hηη.le
  refine ⟨⟨hf.1.1, fun i hi x => (hs i hi x).trans (le_max_left _ _)⟩, fun x z => ?_⟩
  have h2 : ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x‖ ≤ 2 * ε := by
    refine (norm_sub_le _ _).trans ?_
    have := hs (j + 1) le_rfl (x + z); have := hs (j + 1) le_rfl x; linarith
  have h3 := hf.2 x z
  have hz : 0 ≤ ‖z‖ ^ η := Real.rpow_nonneg (norm_nonneg _) _
  have hmin : ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x‖ ≤
      min (2 * ε) (B * ‖z‖ ^ η) := le_min h2 h3
  refine hmin.trans ((min_le_rpow_mul (by positivity) (by positivity) hθ0 hθ1).trans ?_)
  rw [Real.mul_rpow hB hz, ← Real.rpow_mul (norm_nonneg _), show η * θ = η' by rw [hθ]; field_simp]
  calc (2 * ε) ^ (1 - θ) * (B ^ θ * ‖z‖ ^ η') = ((2 * ε) ^ (1 - θ) * B ^ θ) * ‖z‖ ^ η' := by ring
    _ ≤ max ε ((2 * ε) ^ (1 - θ) * B ^ θ) * ‖z‖ ^ η' :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem holB_of_bd {j : ℕ} {η M : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {f : Euc d → ℝ} (hf : Bd (j + 2) M f) :
    HolB j η (2 * M) f := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2 0 (Nat.zero_le _) 0)
  refine ⟨⟨hf.1.of_le (by exact_mod_cast (by omega : j + 1 ≤ j + 2)),
    fun i hi x => (hf.2 i (by omega) x).trans (by linarith)⟩, fun x z => ?_⟩
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) f) :=
    hf.1.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j + 1 < j + 2))
  have hmv : ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x‖ ≤ M * ‖z‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ (j + 1) f) (s := Set.univ)
      (C := M) (fun y _ => hdiff y) (fun y _ => by
        rw [norm_fderiv_iteratedFDeriv]; exact hf.2 (j + 2) le_rfl y) convex_univ (mem_univ x) (mem_univ (x + z))
    simpa using this
  have h2 : ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x‖ ≤ 2 * M := by
    refine (norm_sub_le _ _).trans ?_
    have := hf.2 (j + 1) (by omega) (x + z); have := hf.2 (j + 1) (by omega) x; linarith
  rcases le_or_gt 1 ‖z‖ with h | h
  · refine h2.trans ?_
    have : 1 ≤ ‖z‖ ^ η := Real.one_le_rpow h hη0.le
    nlinarith
  · refine hmv.trans ?_
    rcases (norm_nonneg z).eq_or_lt with hz0 | hzp
    · rw [← hz0]
      have : (0 : ℝ) ^ η = 0 := Real.zero_rpow hη0.ne'
      rw [this]; simp
    have h1 : ‖z‖ ≤ ‖z‖ ^ η := by
      calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖z‖ ^ η := Real.rpow_le_rpow_of_exponent_ge hzp h.le hη1
    nlinarith [norm_nonneg z]

end HRS.MS.S104e.C
