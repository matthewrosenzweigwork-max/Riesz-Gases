import HRS.MS.WadAux115

/-!
# S8.3, packet S8F-16: clause (2b) of the frozen statement for all `j`

`s8f_prev_decay`: for `t ≥ 1` and `f ∈ C_M`, `g = U_{t-1} P_μ f ∈ C_M` and `‖g‖_{M,0} ≤ C_g e^{-ct} ‖f‖_{M,0}` (clause (2a) for `t - 1 ≥ 1`, finite-time
bound for `1 ≤ t < 2`; this is the first half of the proof of `s8d_clause2b_one`).
`s8f_clause2b_ulim`: `U_t P_μ f ∈ C_M^j` with `‖·‖_{M,j} ≤ C_j e^{-ct} ‖f‖_{M,0}` (`t ≥ 1`): `U_t = U_1 U_{t-1}` and `s8f_gain_chain`.
`s8f_clause2b`: `S8eC2b a β ρβ M U` for every `U` with `IsWeightedSemigroup`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s8f_prev_decay (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ Cg c : ℝ, 0 ≤ Cg ∧ 0 < c ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ {f : Euc d → ℝ}, MemCM M f →
      MemCM M (s85_Ulim a β ρβ M (t - 1) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
      weightedSupE 0 (-M) (s85_Ulim a β ρβ M (t - 1)
        (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cg * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  have hM := hMpos.le
  obtain ⟨Cd, c, hc, h2a⟩ := s8d_clause2a_Ulim hd ha hβ hρ hMpos
  have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hM, hρ⟩
  obtain ⟨K1, hK10, hK1⟩ := s85_Ulim_wsup H1
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  obtain ⟨mM, hmM0, hmM⟩ : ∃ mM : ℝ, 0 ≤ mM ∧ mM = ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    ⟨_, integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _, rfl⟩
  obtain ⟨Cg, hCg0, hCg⟩ : ∃ Cg : ℝ, 0 ≤ Cg ∧ Cg = max (max Cd 0 * Real.exp c) (K1 * (1 + mM) * Real.exp (2 * c)) :=
    ⟨_, le_max_of_le_left (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le), rfl⟩
  refine ⟨Cg, c, hCg0, hc, fun {t} ht {f} hf => ?_⟩
  have hM1 : (0 : ℝ) ≤ t - 1 := by linarith
  have Ht : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hM, hρ⟩
  obtain ⟨Φf, hΦf⟩ : ∃ Φf : ℝ, Φf = (weightedSupE 0 (-M) f).toReal := ⟨_, rfl⟩
  have hwf : Wt M Φf f := by rw [hΦf]; exact s83_wt_of_memCM hf
  have hΦf0 : 0 ≤ Φf := hwf.nonneg
  have hfin : weightedSupE 0 (-M) f ≠ ⊤ := s83_wsup0_ne_top hf
  have hΦfe : ENNReal.ofReal Φf = weightedSupE 0 (-M) f := by rw [hΦf]; exact ENNReal.ofReal_toReal hfin
  set Pf := HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f with hPf
  have hPfM : MemCM M Pf := s8d_memCM_projMean hMpos hf
  set g := s85_Ulim a β ρβ M (t - 1) Pf with hg_def
  have hgM : MemCM M g := s85_Ulim_memCM Ht hMpos hM1 (by linarith) hPfM
  have hsg : s85_Ulim a β ρβ M t Pf = s85_Ulim a β ρβ M 1 g := by
    funext x
    have := s85_semigroup Ht hMpos (t := 1) (s := t - 1) zero_le_one hM1 (by linarith) hPfM x
    have e : (1 : ℝ) + (t - 1) = t := by ring
    rw [e] at this
    exact this
  -- size of `g`
  obtain ⟨Φg, hΦg⟩ : ∃ Φg : ℝ, Φg = (weightedSupE 0 (-M) g).toReal := ⟨_, rfl⟩
  have hwg : Wt M Φg g := by rw [hΦg]; exact s83_wt_of_memCM hgM
  have hΦg0 : 0 ≤ Φg := hwg.nonneg
  have hgfin : weightedSupE 0 (-M) g ≠ ⊤ := s83_wsup0_ne_top hgM
  have hΦg_le : Φg ≤ Cg * Real.exp (-c * t) * Φf := by
    have hexp0 : 0 < Real.exp (-c * t) := Real.exp_pos _
    by_cases ht2 : 2 ≤ t
    · -- decay at time `t - 1 ≥ 1`
      have h1 := h2a (t := t - 1) (by linarith) hf
      have h2 : Φg ≤ max Cd 0 * Real.exp (-c * (t - 1)) * Φf := by
        rw [hΦg]
        have h3 : weightedSupE 0 (-M) g ≤ ENNReal.ofReal (max Cd 0 * Real.exp (-c * (t - 1))) *
            weightedSupE 0 (-M) f :=
          h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.exp_pos _).le)) le_rfl)
        have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h3
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le), ← hΦf] at h4
      have e : Real.exp (-c * (t - 1)) = Real.exp c * Real.exp (-c * t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e] at h2
      refine h2.trans ?_
      have : max Cd 0 * (Real.exp c * Real.exp (-c * t)) * Φf ≤ Cg * Real.exp (-c * t) * Φf := by
        have hh : max Cd 0 * Real.exp c ≤ Cg := by rw [hCg]; exact le_max_left _ _
        nlinarith [mul_nonneg hexp0.le hΦf0, mul_le_mul_of_nonneg_right hh (mul_nonneg hexp0.le hΦf0)]
      calc _ = max Cd 0 * (Real.exp c * Real.exp (-c * t)) * Φf := by ring
        _ ≤ _ := this
    · -- `1 ≤ t < 2`: bounded propagation
      push Not at ht2
      have h1 := hK1 (t := t - 1) hM1 (by linarith) hPfM
      have hwPf : Wt M ((1 + mM) * Φf) Pf := fun x => by
        have h1 := hwf x
        have hc' : |∫ z, f z ∂(HRS.Whole.withDensityReal ρβ)| ≤ Φf * mM := by
          have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := f)
            (bd := fun z => Φf * jbracket z ^ M) (hjint.const_mul Φf) (fun z => by
              have := hwf z; rwa [Real.norm_eq_abs] at this)
          rw [integral_const_mul] at this
          rw [hmM]; exact this
        have hj := Real.one_le_rpow (s83_one_le_jb x) hM
        rw [Real.norm_eq_abs] at h1 ⊢
        have h2 : |Pf x| ≤ |f x| + |∫ z, f z ∂(HRS.Whole.withDensityReal ρβ)| := abs_sub _ _
        have h3 : |Pf x| = |f x - ∫ z, f z ∂(HRS.Whole.withDensityReal ρβ)| := rfl
        nlinarith [mul_nonneg hΦf0 hmM0]
      have h2 : weightedSupE 0 (-M) g ≤ ENNReal.ofReal (K1 * ((1 + mM) * Φf)) := by
        refine h1.trans ?_
        rw [ENNReal.ofReal_mul hK10]
        exact mul_le_mul' le_rfl (s8d_wsup_le_of_Wt hwPf)
      have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      rw [ENNReal.toReal_ofReal (mul_nonneg hK10 (mul_nonneg (by linarith) hΦf0))] at h4
      have h5 : Φg ≤ K1 * ((1 + mM) * Φf) := by rw [hΦg]; exact h4
      refine h5.trans ?_
      have hexp2 : Real.exp (2 * c) * Real.exp (-c * t) ≥ 1 := by
        rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
      have hh : K1 * (1 + mM) * Real.exp (2 * c) ≤ Cg := by rw [hCg]; exact le_max_right _ _
      have hK1m : 0 ≤ K1 * (1 + mM) := mul_nonneg hK10 (by linarith)
      nlinarith [mul_nonneg hK1m hΦf0, mul_le_mul_of_nonneg_right hh (mul_nonneg hexp0.le hΦf0),
        mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hK1m hΦf0)]
  refine ⟨hgM, ?_⟩
  have hge : weightedSupE 0 (-M) g = ENNReal.ofReal Φg := by
    rw [hΦg]; exact (ENNReal.ofReal_toReal hgfin).symm
  rw [hge, ← hΦfe, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hΦg_le

theorem s8f_clause2b_ulim (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) (j : ℕ) :
    ∃ Cj c : ℝ, 0 < c ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ {f : Euc d → ℝ}, MemCM M f →
      MemCMj M j (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
      weightedSupE j (-M) (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cj * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · obtain ⟨Cd, c, hc, h⟩ := s8d_clause2a_Ulim hd ha hβ hρ hMpos
    refine ⟨Cd, c, hc, fun {t} ht {f} hf => ⟨?_, h ht hf⟩⟩
    have Ht : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hMpos.le, hρ⟩
    exact s8f_memCMj_zero (s85_Ulim_memCM Ht hMpos (by linarith) le_rfl (s8d_memCM_projMean hMpos hf))
  · obtain ⟨Cg, c, hCg0, hc, hprev⟩ := s8f_prev_decay hd ha hβ hρ hMpos
    have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hMpos.le, hρ⟩
    obtain ⟨Cgain, hCgain0, hgain⟩ := s8f_gain_chain H1 hMpos j hj
    refine ⟨Cgain * Cg, c, hc, fun {t} ht {f} hf => ?_⟩
    obtain ⟨hgM, hg0⟩ := hprev ht hf
    have Ht : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hMpos.le, hρ⟩
    have hPfM := s8d_memCM_projMean (μ := HRS.Whole.withDensityReal ρβ) hMpos hf
    have hsg : s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f) =
        s85_Ulim a β ρβ M 1 (s85_Ulim a β ρβ M (t - 1)
          (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) := funext fun x => by
      have := s85_semigroup Ht hMpos (t := 1) (s := t - 1) zero_le_one (by linarith) (by linarith) hPfM x
      have e : (1 : ℝ) + (t - 1) = t := by ring
      rw [e] at this
      exact this
    rw [hsg]
    obtain ⟨hmem, hbd⟩ := hgain hgM
    refine ⟨hmem, hbd.trans ?_⟩
    calc ENNReal.ofReal Cgain * weightedSupE 0 (-M) (s85_Ulim a β ρβ M (t - 1)
          (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f))
        ≤ ENNReal.ofReal Cgain * (ENNReal.ofReal (Cg * Real.exp (-c * t)) * weightedSupE 0 (-M) f) :=
          mul_le_mul' le_rfl hg0
      _ = ENNReal.ofReal (Cgain * Cg * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCgain0, mul_assoc]

theorem s8f_clause2b (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M)
    {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) :
    S8eC2b a β ρβ M U := by
  intro j
  obtain ⟨Cj, c, hc, h⟩ := s8f_clause2b_ulim hd ha hβ hρ hMpos j
  refine ⟨Cj, c, hc, fun t ht f hf => ?_⟩
  rw [s85_semigroup_unique hd ha hβ hρ hMpos hU (by linarith) (s8d_memCM_projMean hMpos hf)]
  exact h ht hf

end HRS.MS.Wad
