import HRS.MS.WadAux113

/-!
# S8.3, packet S8F-14: clause (3) of the frozen `weighted_adjoint_decay` for all `j`

`s8f_clause3_ulim`: for `s85_Ulim`, `0 ≤ t ≤ T` and `f ∈ C_M^j`: `U_t f ∈ C_M^j` and `‖U_t f‖_{C_M^j} ≤ K ‖f‖_{C_M^j}`.
`s8f_clause3`: `S8eC3 M U` for every `U` with `IsWeightedSemigroup` (`s85_semigroup_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_memCM_of_memCMj {M : ℝ} {j : ℕ} {f : Euc d → ℝ} (hf : MemCMj M j f) : MemCM M f := by
  refine ⟨hf.1.continuous, ?_⟩
  have := hf.2 0 (Nat.zero_le _) (fun i => i.elim0)
  simpa [partialDeriv] using this

theorem s8f_jet_data {M : ℝ} (hM : 0 ≤ M) {j : ℕ} {f : Euc d → ℝ} (hf : MemCMj M j f) :
    (∀ i ≤ j, Tendsto (fun x => ‖iteratedFDeriv ℝ i f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0)) ∧
    ∀ {W : ℝ}, 0 ≤ W → weightedSupE j (-M) f ≤ ENNReal.ofReal W →
      ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ ((d : ℝ) + 1) ^ j * W * jbracket y ^ M := by
  refine ⟨fun i hi => ((s83_memCMj_iff M j f).1 hf).2 i hi |>.2, fun {W} hW hWe i hi y => ?_⟩
  have hpart := (s83_wsup_le_iff hW j f).1 hWe
  have hj : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have := s83_norm_iter_le_card (K := W * jbracket y ^ M) (mul_nonneg hW hj) i f y
    (fun idx => hpart i hi idx y)
  refine this.trans ?_
  have hdi : (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ j :=
    calc (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
      _ ≤ ((d : ℝ) + 1) ^ j := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hi
  calc (d : ℝ) ^ i * (W * jbracket y ^ M) ≤ ((d : ℝ) + 1) ^ j * (W * jbracket y ^ M) :=
        mul_le_mul_of_nonneg_right hdi (mul_nonneg hW hj)
    _ = _ := by ring

theorem s8f_clause3_ulim {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) (j : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {t : ℝ}, 0 ≤ t → t ≤ T → ∀ {f : Euc d → ℝ}, MemCMj M j f →
      MemCMj M j (s85_Ulim a β ρβ M t f) ∧
        weightedSupE j (-M) (s85_Ulim a β ρβ M t f) ≤ ENNReal.ofReal K * weightedSupE j (-M) f := by
  obtain ⟨K1, hK10, hK1⟩ := s8f_Ulim_cc_bounds H j
  set cd : ℝ := ((d : ℝ) + 1) ^ j with hcd
  have hcd0 : 0 ≤ cd := by positivity
  refine ⟨max 1 (K1 * cd), le_max_left _ _, ?_⟩
  intro t ht htT f hf
  have hfM := s8f_memCM_of_memCMj hf
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have : s85_Ulim a β ρβ M 0 f = f := funext fun x => s85_Ulim_at_zero H hfM x
    rw [this]
    exact ⟨hf, le_mul_of_one_le_left bot_le (by rw [ENNReal.one_le_ofReal]; exact le_max_left _ _)⟩
  have hfin := s83_wsup_ne_top hf
  set W : ℝ := (weightedSupE j (-M) f).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hWe : weightedSupE j (-M) f ≤ ENNReal.ofReal W := by rw [hW, ENNReal.ofReal_toReal hfin]
  obtain ⟨hdec, hfν⟩ := s8f_jet_data H.2.2.2.2.1 hf
  have hext := s8f_extend H hMpos htpos htT j j hK10
    (fun {ν ψ} hψ hν hb => (hK1 htpos htT hψ hν hb).2.1)
    (fun {ψ} hψ j' => by
      obtain ⟨ν, hν, hb⟩ := s8f_cc_jet_bound hψ j H.2.2.2.2.1
      exact (hK1 htpos htT hψ hν hb).1 j')
    hfM hf.1 hdec (ν := cd * W) (by positivity) (fun i hi y => by
      exact hfν hW0 hWe i hi y)
  refine ⟨hext.1, ?_⟩
  have hbd : weightedSupE j (-M) (s85_Ulim a β ρβ M t f) ≤ ENNReal.ofReal (K1 * cd * W) := by
    rw [s83_wsup_le_iff (by positivity) j]
    intro i hi idx x
    refine (s83_abs_partial_le i idx _ x).trans ?_
    have := hext.2 i hi x
    refine this.trans (le_of_eq ?_)
    ring
  refine hbd.trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (K1 * cd) * ENNReal.ofReal W
      ≤ ENNReal.ofReal (max 1 (K1 * cd)) * weightedSupE j (-M) f := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) ?_
        rw [hW, ENNReal.ofReal_toReal hfin]

theorem s8f_clause3 (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M)
    {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) : S8eC3 M U := by
  intro j T hT
  have H : S85Hyp d a β (T + 1) M ρβ := ⟨hd, ha, hβ, by linarith, hMpos.le, hρ⟩
  obtain ⟨K, hK1, hK⟩ := s8f_clause3_ulim H hMpos j
  refine ⟨K, fun t ht f hf => ?_⟩
  rw [s85_semigroup_unique hd ha hβ hρ hMpos hU ht.1 (s8f_memCM_of_memCMj hf)]
  exact hK ht.1 (ht.2.trans (by linarith)) hf

end HRS.MS.Wad
