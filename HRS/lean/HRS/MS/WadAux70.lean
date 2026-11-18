import HRS.MS.WadAux69

/-!
# S8.3, packet S8D-2, part 16: clause (2a) of `weighted_adjoint_decay`

`s8d_clause2a`: for `M > 0` there are `C_d, c > 0` with, for all `t ≥ 1` and `f ∈ C_M`,
`‖U_t P_μ f‖_{C_M} ≤ C_d e^{-ct} ‖f‖_{C_M}` for the extension `U = s85_Ulim`; and for every `U` satisfying
`IsWeightedSemigroup` (they coincide with `s85_Ulim` on `C_M`, `s85_semigroup_unique`).  This is the first
conjunct of the second part of the frozen statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_wsup_le_of_Wt {M Φ : ℝ} {g : Euc d → ℝ} (h : Wt M Φ g) :
    weightedSupE 0 (-M) g ≤ ENNReal.ofReal Φ := by
  rw [s83_wsup0_eq]
  refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  have h1 := h x
  rw [Real.norm_eq_abs] at h1
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have e : jbracket x ^ (-M) * jbracket x ^ M = 1 := by
    rw [← Real.rpow_add (s83_jb_pos x)]; simp
  have hq : 0 ≤ jbracket x ^ (-M) := Real.rpow_nonneg (s83_jb_pos x).le _
  calc jbracket x ^ (-M) * |g x| ≤ jbracket x ^ (-M) * (Φ * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ = Φ * (jbracket x ^ (-M) * jbracket x ^ M) := by ring
    _ = Φ := by rw [e, mul_one]

theorem s8d_memCM_projMean {μ : Measure (Euc d)} {M : ℝ} (hM : 0 < M) {f : Euc d → ℝ} (hf : MemCM M f) :
    MemCM M (HRS.Whole.projMean μ f) :=
  s8d_memCM_sub_const hM hf _

theorem s8d_clause2a_Ulim (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ Cd c : ℝ, 0 < c ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ {f : Euc d → ℝ}, MemCM M f →
      weightedSupE 0 (-M) (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cd * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  have hM := hMpos.le
  obtain ⟨κ, Cc, hκ0, hκ1, hCc0, hdec⟩ := s8d_decay_iter hd ha hβ hρ hMpos
  have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hM, hρ⟩
  obtain ⟨K1, hK10, hK1⟩ := s85_Ulim_wsup H1
  have hlogneg : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  refine ⟨K1 * Cc / κ, -Real.log κ, by linarith, fun {t} ht1 {f} hf => ?_⟩
  set n : ℕ := ⌊t⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast ht1)
  have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  set s : ℝ := t - n with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have Ht : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hM, hρ⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Φf : ℝ := (weightedSupE 0 (-M) f).toReal with hΦf
  have hwf : Wt M Φf f := s83_wt_of_memCM hf
  have hΦf0 : 0 ≤ Φf := hwf.nonneg
  have hfin : weightedSupE 0 (-M) f ≠ ⊤ := s83_wsup0_ne_top hf
  have hΦfe : ENNReal.ofReal Φf = weightedSupE 0 (-M) f := ENNReal.ofReal_toReal hfin
  set g := HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f with hg
  have hgM : MemCM M g := s8d_memCM_projMean hMpos hf
  have hnT : (n : ℝ) ≤ t := hnt
  -- `U_n g = U_n f - μ f`
  have hUn : s85_Ulim a β ρβ M (n : ℝ) g = fun x => s85_Ulim a β ρβ M (n : ℝ) f x -
      ∫ z, f z ∂(HRS.Whole.withDensityReal ρβ) := by
    funext x
    exact s8d_Ulim_shift Ht hMpos hnR hnT hf _ x
  have hzW := hdec n hf hwf
  have hzM : MemCM M (fun x => s85_Ulim a β ρβ M (n : ℝ) f x - ∫ z, f z ∂(HRS.Whole.withDensityReal ρβ)) :=
    s8d_memCM_sub_const hMpos (s85_Ulim_memCM Ht hMpos hnR hnT hf) _
  -- semigroup law
  have hsg : s85_Ulim a β ρβ M t g = s85_Ulim a β ρβ M s (s85_Ulim a β ρβ M (n : ℝ) g) := by
    funext x
    have := s85_semigroup Ht hMpos (t := s) (s := (n : ℝ)) hs0 hnR (by rw [hs]; linarith) hgM x
    have e : s + (n : ℝ) = t := by rw [hs]; ring
    rw [e] at this
    exact this
  rw [hsg, hUn]
  have h1 := hK1 hs0 hs1 hzM
  have h2 := s8d_wsup_le_of_Wt hzW
  have hκn : κ ^ n ≤ κ⁻¹ * Real.exp (-(-Real.log κ) * t) := by
    have e1 : Real.exp (-(-Real.log κ) * t) = κ ^ t := by
      rw [Real.rpow_def_of_pos hκ0]; congr 1; ring
    rw [e1]
    have e2 : κ ^ (n : ℝ) ≤ κ ^ (t - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hκ0 hκ1.le (by linarith)
    rw [Real.rpow_natCast] at e2
    refine e2.trans (le_of_eq ?_)
    rw [Real.rpow_sub hκ0, Real.rpow_one]; field_simp
  calc _ ≤ ENNReal.ofReal K1 * weightedSupE 0 (-M) _ := h1
    _ ≤ ENNReal.ofReal K1 * ENNReal.ofReal (Cc * κ ^ n * Φf) := by gcongr
    _ = ENNReal.ofReal (K1 * Cc * κ ^ n) * ENNReal.ofReal Φf := by
        rw [← ENNReal.ofReal_mul hK10, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    _ ≤ ENNReal.ofReal (K1 * Cc / κ * Real.exp (-(-Real.log κ) * t)) * weightedSupE 0 (-M) f := by
        rw [hΦfe]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        calc K1 * Cc * κ ^ n ≤ K1 * Cc * (κ⁻¹ * Real.exp (-(-Real.log κ) * t)) :=
              mul_le_mul_of_nonneg_left hκn (mul_nonneg hK10 hCc0)
          _ = K1 * Cc / κ * Real.exp (-(-Real.log κ) * t) := by field_simp

/-- **Clause (2a) of the frozen statement** (first conjunct of the part `∀ U, IsWeightedSemigroup … → …`). -/
theorem s8d_clause2a (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M)
    {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) :
    ∃ Cd c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ f : Euc d → ℝ, MemCM M f →
      weightedSupE 0 (-M) (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cd * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  obtain ⟨Cd, c, hc, h⟩ := s8d_clause2a_Ulim hd ha hβ hρ hMpos
  refine ⟨Cd, c, hc, fun t ht f hf => ?_⟩
  rw [s85_semigroup_unique hd ha hβ hρ hMpos hU (by linarith) (s8d_memCM_projMean hMpos hf)]
  exact h ht hf

end HRS.MS.Wad
