import HRS.MS.FeatDecAux6

/-!
# S8.5 `feature_decay`, part 7 (S85 packet): weighted base data `∂_a φ_α`

`s85_base_weighted`: `‖D^j ∂_a φ_α(x)‖ ≤ Cb λ_α^{(J-m)/2} ⟨x⟩^{-(s+2+j)}` for `j ≤ n` (Hermite functions are Schwartz,
`s52b_weighted`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj HRS.MS.S52B

variable {d : ℕ}

theorem s85_base_weighted {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) (m : ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∃ J : ℕ, (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 ∧ ∀ (α : MultiIndex d) (a : Fin d),
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (oscTestFun m α) x) ∧
      ∀ j ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤
        Cb * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * jbracket x ^ (-(s + 2 + (j : ℝ))) := by
  set N : ℕ := ⌈s + 2 + n⌉₊ with hN
  have hN1 : s + 2 + (n : ℝ) ≤ N := Nat.le_ceil _
  choose C hC0 hC using s52b_weighted (d := d) N
  set Cb : ℝ := ∑ j ∈ Finset.range (n + 2), C j with hCb
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun j _ => hC0 j
  set J : ℕ := N + ⌊((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hJ
  have hJle : (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 := by
    have hN2 : (N : ℝ) < s + 2 + (n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hf : (⌊((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    simp only [hJ]; push_cast at hf ⊢; linarith
  refine ⟨Cb, hCb0, J, hJle, fun α a => ?_⟩
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  rw [← hf]
  have hfs : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (⇑f : Euc d → ℝ) :=
    s85_cdiff_nat (f.smooth _) (n + 1)
  have hfs' : ContDiff ℝ (n + 1) (⇑f : Euc d → ℝ) := by exact_mod_cast hfs
  rw [s85_gradComp_eq]
  refine ⟨?_, fun j hj x => ?_⟩
  · have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ (⇑f : Euc d → ℝ)) :=
      hfs'.fderiv_right (m := (n : WithTop ℕ∞)) (by push_cast; exact le_refl _)
    exact h1.clm_apply (contDiff_const (c := EuclideanSpace.single a (1 : ℝ)))
  · have h1 := u2_fderiv_apply_bound hfs' (EuclideanSpace.single a (1 : ℝ)) j hj x
    rw [EuclideanSpace.norm_single, norm_one, one_mul] at h1
    refine h1.trans ?_
    have h2 := hC (j + 1) f x
    have hw : 0 < (1 + ‖x‖) ^ N := by positivity
    have hjb : jbracket x ^ (s + 2 + (j : ℝ)) ≤ (1 + ‖x‖) ^ N := by
      calc jbracket x ^ (s + 2 + (j : ℝ)) ≤ (1 + ‖x‖) ^ (s + 2 + (j : ℝ)) :=
            Real.rpow_le_rpow (u2_jb_pos x).le (u2_jb_le x)
              (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
        _ ≤ (1 + ‖x‖) ^ (N : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
              (by have : (j : ℝ) ≤ n := by exact_mod_cast hj
                  linarith)
        _ = (1 + ‖x‖) ^ N := Real.rpow_natCast _ _
    have hjbp : 0 < jbracket x ^ (s + 2 + (j : ℝ)) := Real.rpow_pos_of_pos (u2_jb_pos x) _
    have hidx : N + ⌊((j + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 ≤ J := by
      have : ⌊((j + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊((n + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ :=
        Nat.floor_le_floor (by
          have : ((j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
          linarith)
      omega
    have hosc : oscNorm ((N + ⌊((j + 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ oscNorm (J : ℝ) f :=
      ul6_osc_mono hidx f
    have hCj : C (j + 1) ≤ Cb :=
      Finset.single_le_sum (f := C) (fun _ _ => hC0 _) (Finset.mem_range.2 (by omega))
    have hosc0 : 0 ≤ oscNorm (J : ℝ) f := Real.sqrt_nonneg _
    have h3 : ‖iteratedFDeriv ℝ (j + 1) (⇑f : Euc d → ℝ) x‖ ≤
        C (j + 1) * oscNorm (J : ℝ) f * ((1 + ‖x‖) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hw]
      calc ‖iteratedFDeriv ℝ (j + 1) (⇑f : Euc d → ℝ) x‖ * (1 + ‖x‖) ^ N
          = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ (j + 1) (⇑f : Euc d → ℝ) x‖ := by ring
        _ ≤ _ := h2
        _ ≤ _ := mul_le_mul_of_nonneg_left hosc (hC0 _)
    refine h3.trans ?_
    rw [Real.rpow_neg (u2_jb_pos x).le, ← hfN J]
    have h4 : C (j + 1) * oscNorm (J : ℝ) f ≤ Cb * oscNorm (J : ℝ) f :=
      mul_le_mul_of_nonneg_right hCj hosc0
    have hinv : ((1 + ‖x‖) ^ N)⁻¹ ≤ (jbracket x ^ (s + 2 + (j : ℝ)))⁻¹ :=
      inv_anti₀ hjbp hjb
    calc C (j + 1) * oscNorm (J : ℝ) f * ((1 + ‖x‖) ^ N)⁻¹
        ≤ Cb * oscNorm (J : ℝ) f * (jbracket x ^ (s + 2 + (j : ℝ)))⁻¹ := by
          apply mul_le_mul h4 hinv (by positivity) (by positivity)
      _ = _ := rfl

end HRS.MS.S85
