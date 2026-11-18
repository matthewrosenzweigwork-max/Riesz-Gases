import HRS.MS.WadAux114

/-!
# S8.3, packet S8F-15: gain of one derivative, and the gain from `C_M` to `C_M^j` at time `1`

`s8f_gain`: for `0 < t ≤ 1` and `f ∈ C_M^k`: `U_t f ∈ C_M^{k+1}` and `‖U_t f‖_{M,k+1} ≤ K t^{-3/4} ‖f‖_{M,k}` (`s8f_extend` with the bounds
of `s8f_Ulim_cc_bounds` of orders `1..k+1`).
`s8f_gain_chain`: `U_1 = (U_{1/j})^j` gives, for `j ≥ 1` and `g ∈ C_M`: `U_1 g ∈ C_M^j` and `‖U_1 g‖_{M,j} ≤ C ‖g‖_{M,0}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_gain {a β M : ℝ} {ρβ : Euc d → ℝ} (H1 : S85Hyp d a β 1 M ρβ) (hMpos : 0 < M) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ {f : Euc d → ℝ}, MemCMj M k f →
      MemCMj M (k + 1) (s85_Ulim a β ρβ M t f) ∧
        weightedSupE (k + 1) (-M) (s85_Ulim a β ρβ M t f) ≤
          ENNReal.ofReal (K * t ^ (-(3 / 4 : ℝ))) * weightedSupE k (-M) f := by
  obtain ⟨K1, hK10, hK1⟩ := s8f_Ulim_cc_bounds H1 k
  set cd : ℝ := ((d : ℝ) + 1) ^ k with hcd
  have hcd0 : 0 ≤ cd := by positivity
  refine ⟨K1 * cd, by positivity, ?_⟩
  intro t ht htT f hf
  have hfM := s8f_memCM_of_memCMj hf
  have ht34 : 1 ≤ t ^ (-(3 / 4 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htT (by norm_num)
  have ht34' : 0 ≤ t ^ (-(3 / 4 : ℝ)) := by linarith
  have hfin := s83_wsup_ne_top hf
  set W : ℝ := (weightedSupE k (-M) f).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hWe : weightedSupE k (-M) f ≤ ENNReal.ofReal W := by rw [hW, ENNReal.ofReal_toReal hfin]
  obtain ⟨hdec, hfν⟩ := s8f_jet_data H1.2.2.2.2.1 hf
  have hext := s8f_extend H1 hMpos ht htT k (k + 1) (K' := K1 * t ^ (-(3 / 4 : ℝ)))
    (by positivity)
    (fun {ν ψ} hψ hν hb i hi y => by
      obtain ⟨-, h2, h3⟩ := hK1 ht htT hψ hν hb
      have hj : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · refine (h2 i (by omega) y).trans ?_
        have : 0 ≤ K1 * ν * jbracket y ^ M := by positivity
        calc K1 * ν * jbracket y ^ M ≤ K1 * ν * jbracket y ^ M * t ^ (-(3 / 4 : ℝ)) :=
              le_mul_of_one_le_right this ht34
          _ = _ := by ring
      · have hi' : i = k + 1 := by omega
        subst hi'
        refine (h3 (k + 1) (by omega) le_rfl y).trans (le_of_eq ?_)
        ring)
    (fun {ψ} hψ j' => by
      obtain ⟨ν, hν, hb⟩ := s8f_cc_jet_bound hψ k H1.2.2.2.2.1
      exact (hK1 ht htT hψ hν hb).1 j')
    hfM hf.1 hdec (ν := cd * W) (by positivity) (fun i hi y => hfν hW0 hWe i hi y)
  refine ⟨hext.1, ?_⟩
  have hbd : weightedSupE (k + 1) (-M) (s85_Ulim a β ρβ M t f) ≤
      ENNReal.ofReal (K1 * cd * t ^ (-(3 / 4 : ℝ)) * W) := by
    rw [s83_wsup_le_iff (by positivity) (k + 1)]
    intro i hi idx x
    refine (s83_abs_partial_le i idx _ x).trans ?_
    refine (hext.2 i hi x).trans (le_of_eq ?_)
    ring
  refine hbd.trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (le_of_eq (by rw [mul_assoc])) ?_
  rw [hW, ENNReal.ofReal_toReal hfin]

theorem s8f_memCMj_zero {M : ℝ} {g : Euc d → ℝ} (hg : MemCM M g) : MemCMj M 0 g := by
  refine ⟨contDiff_zero.2 hg.1, fun i hi idx => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simpa [partialDeriv] using hg.2

theorem s8f_gain_chain {a β M : ℝ} {ρβ : Euc d → ℝ} (H1 : S85Hyp d a β 1 M ρβ) (hMpos : 0 < M) (j : ℕ)
    (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d → ℝ}, MemCM M g →
      MemCMj M j (s85_Ulim a β ρβ M 1 g) ∧
        weightedSupE j (-M) (s85_Ulim a β ρβ M 1 g) ≤ ENNReal.ofReal C * weightedSupE 0 (-M) g := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have key : ∀ i : ℕ, i ≤ j → ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d → ℝ}, MemCM M g →
      MemCMj M i (s85_Ulim a β ρβ M ((i : ℝ) / j) g) ∧
        weightedSupE i (-M) (s85_Ulim a β ρβ M ((i : ℝ) / j) g) ≤
          ENNReal.ofReal C * weightedSupE 0 (-M) g := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, zero_le_one, fun {g} hg => ?_⟩
      have e : s85_Ulim a β ρβ M (((0 : ℕ) : ℝ) / j) g = g := funext fun x => by
        simpa using s85_Ulim_at_zero H1 hg x
      rw [e]
      refine ⟨s8f_memCMj_zero hg, ?_⟩
      simp
    | succ i ih =>
      intro hi
      obtain ⟨C, hC0, hC⟩ := ih (by omega)
      obtain ⟨K, hK0, hK⟩ := s8f_gain H1 hMpos i
      have hs1 : (1 : ℝ) / j ≤ 1 := by rw [div_le_one hj0]; exact hjR
      have hs0 : (0 : ℝ) < 1 / j := by positivity
      refine ⟨K * ((1 / (j : ℝ)) ^ (-(3 / 4 : ℝ))) * C, by positivity, fun {g} hg => ?_⟩
      obtain ⟨hmem, hbd⟩ := hC hg
      have hti : ((i : ℝ) / j) + 0 ≥ 0 := by positivity
      have hsum : (1 : ℝ) / j + (i : ℝ) / j = ((i + 1 : ℕ) : ℝ) / j := by push_cast; ring
      have hle : (1 : ℝ) / j + (i : ℝ) / j ≤ 1 := by
        rw [hsum, div_le_one hj0]; exact_mod_cast hi
      have e : s85_Ulim a β ρβ M (((i + 1 : ℕ) : ℝ) / j) g =
          s85_Ulim a β ρβ M (1 / (j : ℝ)) (s85_Ulim a β ρβ M ((i : ℝ) / j) g) := funext fun x => by
        rw [← hsum]
        exact s85_semigroup H1 hMpos hs0.le (by positivity) hle hg x
      rw [e]
      obtain ⟨hmem2, hbd2⟩ := hK hs0 hs1 hmem
      refine ⟨hmem2, hbd2.trans ?_⟩
      calc ENNReal.ofReal (K * (1 / (j : ℝ)) ^ (-(3 / 4 : ℝ))) *
            weightedSupE i (-M) (s85_Ulim a β ρβ M ((i : ℝ) / j) g)
          ≤ ENNReal.ofReal (K * (1 / (j : ℝ)) ^ (-(3 / 4 : ℝ))) *
            (ENNReal.ofReal C * weightedSupE 0 (-M) g) := mul_le_mul' le_rfl hbd
        _ = ENNReal.ofReal (K * (1 / (j : ℝ)) ^ (-(3 / 4 : ℝ)) * C) * weightedSupE 0 (-M) g := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  obtain ⟨C, hC0, hC⟩ := key j le_rfl
  refine ⟨C, hC0, fun {g} hg => ?_⟩
  have e1 : ((j : ℕ) : ℝ) / j = 1 := div_self hj0.ne'
  rw [e1] at hC
  exact hC hg

end HRS.MS.Wad
