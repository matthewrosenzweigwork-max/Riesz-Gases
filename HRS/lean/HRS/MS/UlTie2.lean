import HRS.MS.UlOrbit
import HRS.Whole.Adjoint

/-!
# UL-6 tie: `ul_adjoint_orbit_bounds` (S5.1, part 2)

`ul_adjoint_orbit_bounds_proof` has exactly the type of the frozen statement `HRS.Whole.ul_adjoint_orbit_bounds`
(the frozen declaration is `unproved`; a warning is expected).

* `k₀ = ⌊4 + d/2⌋ + 1`, the threshold of part 1; the common level is `K = max k₀ (⌊k + d/2⌋ + 1)`, so that every
  admissible `k₁` satisfies `K ≤ k₁` (`k₁ ≥ k₀` and `k + d/2 < k₁`).
* `J` is the output of `ul6_orbit_ul` for `K` (it depends on `d, s, k` only, not on `k₁`, `T`, `ν`, `Q`, `ρ`, `c`):
  `‖L^a f‖_{H^K_ul} ≤ C ‖f‖_{Σ^J}` for `a ≤ 3`.  Every level-`k₁` evolution is a level-`K` evolution
  (`ul6_mono_level`), and at level `K` the evolutions are unique (`ul_evolution_unique`), so the `C_b^k` bound is
  `ul6_cb_bound` (`ulClosure_cb`, `K > k + d/2`).
* the existence of `F` is `ul6_exists_F` (`ul_evolution_exists` at level `k₁`); the difference quotients are
  `ul6_main_diff`.
-/

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.Whole Set

theorem ul_adjoint_orbit_bounds_proof : type_of% @HRS.Whole.ul_adjoint_orbit_bounds := by
  intro d hd s hs0 hsd θ hθ k
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  set K₁ : ℕ := ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hK₁
  set K : ℕ := max K₁ (⌊(k : ℝ) + (d : ℝ) / 2⌋₊ + 1) with hK
  have hK4 : (4 : ℝ) + (d : ℝ) / 2 < K := by
    have h1 : (4 : ℝ) + (d : ℝ) / 2 < K₁ := by
      rw [hK₁]; push_cast; exact Nat.lt_floor_add_one _
    exact h1.trans_le (by exact_mod_cast le_max_left _ _)
  have hkK : (k : ℝ) + (d : ℝ) / 2 < K := by
    have h1 : (k : ℝ) + (d : ℝ) / 2 < ((⌊(k : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    exact h1.trans_le (by exact_mod_cast le_max_right _ _)
  obtain ⟨J, hJ⟩ := ul6_orbit_ul hd hs0 hsd hθ K
  refine ⟨K₁, J, fun k₁ hk₁ hkk₁ T ν Q ρ c hT hν hρ hcσ => ?_⟩
  obtain ⟨σ, hσ, hc⟩ := hcσ
  have O : UlOrb d s ν ρ σ c θ := ⟨hd, hs0, hsd, hν, hρ.2, hσ, hc, hθ⟩
  have hKk₁ : K ≤ k₁ := by
    refine max_le hk₁ ?_
    have : ⌊(k : ℝ) + (d : ℝ) / 2⌋₊ < k₁ := (Nat.floor_lt (by positivity)).2 hkk₁
    omega
  have hk₁4 : (4 : ℝ) + (d : ℝ) / 2 < k₁ := hK4.trans_le (by exact_mod_cast hKk₁)
  obtain ⟨Cfin, hCfin0, hCfin⟩ := hJ ν Q ρ hρ.2 σ hσ c hc
  obtain ⟨C, hC0, hC⟩ := ul6_cb_sum O Q hK4 hkK hCfin0 (fun f a ha => hCfin f a ha) T hT
  refine ⟨C, fun f => ?_⟩
  intro Cf
  refine ⟨ul6_exists_F O Q hk₁4 hT f, fun F hF => ⟨fun t ht => hC f F k₁ hKk₁ hF t ht, ?_⟩⟩
  intro a ha3 t ht ε hε
  exact ul6_main_diff O Q hK4 hkK hKk₁ hT f F hF a ha3 t ht ε hε

end HRS.MS.Ul
