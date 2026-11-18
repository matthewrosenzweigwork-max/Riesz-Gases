import HRS.MS.WadAux111

/-!
# S8.3, packet S8F-12: weighted jet bounds of `U_t φ` for `C_c^∞` data

`s8f_Ulim_cc_bounds`: for `φ ∈ C_c^∞` with `‖D^iφ(y)‖ ≤ ν ⟨y⟩^M` (`i ≤ N`) and `0 < t ≤ T`, the function `s85_Ulim t φ` is `C^∞`, its derivatives of order
`≤ N` are bounded by `K ν ⟨y⟩^M`, and those of order `1..N+1` by `K ν t^{-3/4} ⟨y⟩^M` (`K` independent of `t, ν, φ`).
(`U_t φ = f_0 + const` for the classical solution `f`; `s8f_cl_deriv`; the zero order is the existing sup bound `s85_Ulim_wsup`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_iter_add_const {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) {i : ℕ} (hi : i ≠ 0) :
    iteratedFDeriv ℝ i (fun x => f x + c) = iteratedFDeriv ℝ i f := by
  funext x
  have hfi : ContDiff ℝ i f := hf.of_le (by exact_mod_cast le_top)
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (x := x) (i := i) (f := f) (g := fun _ => c)
    hfi.contDiffAt contDiff_const.contDiffAt
  simp only [Pi.add_def] at this ⊢
  rw [this, iteratedFDeriv_const_of_ne hi]
  simp

theorem s8f_Ulim_cc_bounds {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t ν : ℝ} {φ : Euc d → ℝ}, 0 < t → t ≤ T → S85Cc φ → 0 ≤ ν →
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ ν * jbracket y ^ M) →
      (∀ j : ℕ, ContDiff ℝ j (s85_Ulim a β ρβ M t φ)) ∧
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t φ) y‖ ≤ K * ν * jbracket y ^ M) ∧
      (∀ i, 1 ≤ i → i ≤ N + 1 → ∀ y,
        ‖iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t φ) y‖ ≤ K * ν * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨lam, Kcl, hlam, hKcl, hcl⟩ := s8f_cl_deriv hd ha hβ hT hM hρ N
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_wsup H
  set dd : ℝ := ((d : ℝ) + 1) ^ (N + 1) with hdd
  have hdd1 : 1 ≤ dd := one_le_pow₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set E : ℝ := Real.exp (lam * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hlam hT.le)
  refine ⟨max Kb (dd * Kcl * E), le_max_of_le_left hKb0, ?_⟩
  intro t ν φ ht htT hφ hν hb
  obtain ⟨f, hf⟩ := s85_exists_cl hd ha hβ hρ ht.le hφ
  have hcd := hcl ht htT hφ hf hν hb
  obtain ⟨c, hc⟩ : ∃ c, s85_Ulim a β ρβ M t φ = fun x => f 0 x + c := by
    obtain ⟨c, hc⟩ := s8d_Ucc_eq_add hd ha hβ hρ ht.le hf
    refine ⟨c, funext fun x => ?_⟩
    rw [s85_Ulim_cc H ht.le htT hφ x, hc]
  have hsm : ∀ j : ℕ, ContDiff ℝ j (f 0) := fun j =>
    s8f_cl_smooth_cc hd ha hβ hρ hT.le hφ ⟨ht.le, htT⟩ j hf
  have hsmU : ∀ j : ℕ, ContDiff ℝ j (s85_Ulim a β ρβ M t φ) := fun j => by
    rw [hc]; exact (hsm j).add contDiff_const
  have hfinf : ContDiff ℝ ∞ (f 0) := contDiff_infty.2 hsm
  have hit : ∀ i, i ≠ 0 → iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t φ) = iteratedFDeriv ℝ i (f 0) := by
    intro i hi; rw [hc]; exact s8f_iter_add_const hfinf c hi
  have hj : ∀ y : Euc d, 0 ≤ jbracket y ^ M := fun y => Real.rpow_nonneg (s83_jb_pos y).le _
  refine ⟨hsmU, fun i hi y => ?_, fun i hi1 hiN y => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- order zero
      have hφ0 : Wt M ν φ := fun y => by
        have := hb 0 (Nat.zero_le _) y
        rwa [norm_iteratedFDeriv_zero] at this
      have hw := hKb ht.le htT (s85_Cc_memCM M hφ)
      have hw2 : weightedSupE 0 (-M) (s85_Ulim a β ρβ M t φ) ≤ ENNReal.ofReal (Kb * ν) := by
        refine hw.trans ?_
        rw [ENNReal.ofReal_mul hKb0]
        exact mul_le_mul' le_rfl ((s83_wsup0_le_iff hν φ).2 hφ0)
      have := (s83_wsup0_le_iff (mul_nonneg hKb0 hν) _).1 hw2 y
      rw [norm_iteratedFDeriv_zero]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hν) (hj y)
    · rw [hit i hipos.ne']
      have hpart : ∀ idx : Fin i → Fin d, |partialDeriv idx (f 0) y| ≤ Kcl * ν * jbracket y ^ M :=
        fun idx => (hcd.1 i hi idx y)
      have := s83_norm_iter_le_card (K := Kcl * ν * jbracket y ^ M)
        (mul_nonneg (mul_nonneg hKcl hν) (hj y)) i (f 0) y hpart
      refine this.trans ?_
      have hdi : (d : ℝ) ^ i ≤ dd := by
        calc (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
          _ ≤ ((d : ℝ) + 1) ^ (N + 1) :=
            pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) (by omega)
      have hmx : dd * Kcl ≤ max Kb (dd * Kcl * E) := by
        refine le_max_of_le_right ?_
        nlinarith [mul_nonneg (by linarith : 0 ≤ dd) hKcl]
      calc (d : ℝ) ^ i * (Kcl * ν * jbracket y ^ M) ≤ dd * (Kcl * ν * jbracket y ^ M) :=
            mul_le_mul_of_nonneg_right hdi (mul_nonneg (mul_nonneg hKcl hν) (hj y))
        _ = (dd * Kcl) * ν * jbracket y ^ M := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmx hν) (hj y)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [hit (k + 1) (by omega)]
    have hpart : ∀ idx : Fin (k + 1) → Fin d, |partialDeriv idx (f 0) y| ≤
        Kcl * ν * (E * t ^ (-(3 / 4 : ℝ))) * jbracket y ^ M :=
      fun idx => hcd.2 k (by omega) idx y
    have hnn : 0 ≤ Kcl * ν * (E * t ^ (-(3 / 4 : ℝ))) * jbracket y ^ M :=
      mul_nonneg (mul_nonneg (mul_nonneg hKcl hν) (mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _))) (hj y)
    have := s83_norm_iter_le_card (K := Kcl * ν * (E * t ^ (-(3 / 4 : ℝ))) * jbracket y ^ M) hnn (k + 1) (f 0) y hpart
    refine this.trans ?_
    have hdi : (d : ℝ) ^ (k + 1) ≤ dd := by
      calc (d : ℝ) ^ (k + 1) ≤ ((d : ℝ) + 1) ^ (k + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ ((d : ℝ) + 1) ^ (N + 1) :=
          pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) (by omega)
    have hmx : dd * Kcl * E ≤ max Kb (dd * Kcl * E) := le_max_right _ _
    have ht34 : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg ht.le _
    calc (d : ℝ) ^ (k + 1) * (Kcl * ν * (E * t ^ (-(3 / 4 : ℝ))) * jbracket y ^ M)
        ≤ dd * (Kcl * ν * (E * t ^ (-(3 / 4 : ℝ))) * jbracket y ^ M) :=
          mul_le_mul_of_nonneg_right hdi hnn
      _ = (dd * Kcl * E) * ν * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmx hν) ht34) (hj y)

end HRS.MS.Wad
