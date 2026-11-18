import HRS.MS.R2WinOrbAux13

/-!
# S10.3 (stationary half), part 14: the window tests `f_{b,n,α}` of the stationary coefficient

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_window_tests`: `f_{b,n,α} ∈ C_b^k` and `‖f_{b,n,α}‖_{C_b^k} ≤ C_w (1+n)^{-5/4} b_α`
for all `b ≥ 0`, `n`, `α` (with the orbit family of `s103_family`, no existence hypothesis needed).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem s103_window_tests {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) {T : ℝ} (hT : 0 < T) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (α : MultiIndex d) (b : ℝ), 0 ≤ b → ∀ n : ℕ,
      MemCb (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ))
        ((24 * d + 240 : ℕ) : ℝ) T b n α) ∧
      cbNorm (4 * d + 42) (r2WindowTest ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ))
        ((24 * d + 240 : ℕ) : ℝ) T b n α) ≤ Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b d α := by
  obtain ⟨C, c, hC0, hc, horb⟩ := s103_orbit_iter hd hs0 hsd hq hβ hρ
  set M0 : ℝ := max (T * (1 / Real.sqrt T) * C)
    (4 * (Real.sqrt (2 / T) * ((2 * C + T * C) * T ^ 2 / Real.pi ^ 2))) with hM0
  have hM00 : 0 ≤ M0 := le_trans (by positivity) (le_max_left _ _)
  refine ⟨((4 * d + 42 : ℕ) + 1 : ℝ) * M0, by positivity, fun α b hb n => ?_⟩
  set Cf := (quadraticGradientDyn d s q β).coeff (fun _ => ρβ) with hCf
  have hb0 := s103_b_nonneg α
  have hA : 0 ≤ C * s103_b d α := mul_nonneg hC0 hb0
  obtain ⟨F, hF0, hFcl, hFdq⟩ := s103_family hd hs0 hsd hq hβ hρ α (T0 := b + T) (by linarith)
  set F' : ℕ → ℝ → Euc d → ℝ := fun a => if h : a < 4 then F ⟨a, h⟩ else fun _ _ => 0 with hF'
  have hF'eq : ∀ (a : ℕ) (h : a < 4), F' a = F ⟨a, h⟩ := fun a h => by simp [hF', h]
  have Hfam : s103_famHyp F' (4 * d + 42) (b + T) (C * s103_b d α) := by
    have hcb : ∀ a ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) (b + T),
        ContDiff ℝ (4 * d + 42 : ℕ) (F' a t) ∧ r2CbNormE (4 * d + 42) (F' a t) ≤ ENNReal.ofReal (C * s103_b d α) := by
      intro a ha t ht
      obtain ⟨u, hu, hFu⟩ := hFcl ⟨a, by omega⟩ t ht
      have := horb α t ht.1 a ha u hu 0 ⟨le_rfl, ht.1⟩
      rw [hF'eq a (by omega), hFu]
      exact this
    refine ⟨fun a ha t ht => (hcb a ha t ht).1, fun a ha t ht j hj x =>
      s103_cb_of_E hA (hcb a ha t ht).2 j hj x, fun a ha t ht ε hε => ?_⟩
    obtain ⟨δ, hδ, hh⟩ := hFdq ⟨a, by omega⟩ (by simpa using (by omega : a < 3)) t ht ε hε
    refine ⟨δ, hδ, fun h h0 hd' ht' j hj x => ?_⟩
    rw [hF'eq a (by omega), hF'eq (a + 1) (by omega)]
    exact hh h h0 hd' ht' j hj x
  obtain ⟨hcd, hdb⟩ := s103_window_core (by omega : 1 ≤ 4 * d + 42) Hfam hb hT le_rfl hA n
  set G : Euc d → ℝ := fun x => ∫ u in Set.Icc (0 : ℝ) T, r2CosBasis T n u * F' 0 (b + u) x with hG
  set cn : ℝ := (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) with hcn
  have hcn0 : 0 ≤ cn := by positivity
  have hfun : r2WindowTest Cf ((24 * d + 240 : ℕ) : ℝ) T b n α = fun x => cn * G x := by
    funext x
    unfold r2WindowTest
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    have h1 := hF0 (b + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [hF'eq 0 (by norm_num)]
    have h1' : F ⟨0, by norm_num⟩ (b + u) = propagatorW Cf 0 (b + u) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := h1
    rw [h1']
  rw [hfun]
  have e : (fun x => cn * G x) = cn • G := rfl
  have hjet : ∀ j ≤ 4 * d + 42, ∀ x, ‖iteratedFDeriv ℝ j (fun x => cn * G x) x‖ ≤ cn * s103_cosBound T (C * s103_b d α) n := by
    intro j hj x
    rw [e, iteratedFDeriv_const_smul_apply ((hcd.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hcn0]
    exact mul_le_mul_of_nonneg_left (hdb j hj x) hcn0
  refine ⟨⟨contDiff_const.mul hcd, fun j hj => ⟨cn * s103_cosBound T (C * s103_b d α) n, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hjet j hj x
  · unfold cbNorm
    have hB : ∀ j ≤ 4 * d + 42, (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => cn * G x) z‖) ≤
        cn * s103_cosBound T (C * s103_b d α) n := fun j hj => ciSup_le fun z => hjet j hj z
    calc ∑ j ∈ Finset.range (4 * d + 42 + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => cn * G x) z‖)
        ≤ ∑ j ∈ Finset.range (4 * d + 42 + 1), cn * s103_cosBound T (C * s103_b d α) n :=
          Finset.sum_le_sum fun j hj => hB j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = ((4 * d + 42 : ℕ) + 1 : ℝ) * (cn * (s103_b d α * s103_cosBound T C n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, s103_cosBound_mul]; push_cast; ring
      _ ≤ ((4 * d + 42 : ℕ) + 1 : ℝ) * (s103_b d α * (M0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := s103_cosBound_arith hT hC0 n
          calc cn * (s103_b d α * s103_cosBound T C n) = s103_b d α * (cn * s103_cosBound T C n) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this hb0
      _ = _ := by ring

end HRS.MS.R2WinOrb

end
