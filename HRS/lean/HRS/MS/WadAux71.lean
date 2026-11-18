import HRS.MS.WadAux70

/-!
# S8.3, packet S8D-2, part 17: clause (2b) for `j = 1`

`s8d_clause2b_one`: for `t ≥ 1` and `f ∈ C_M`, `U_t P f ∈ C_M^1` and
`‖U_t P f‖_{C_M^1} ≤ C_1 e^{-ct} ‖f‖_{C_M}` (the case `j = 1` of the second conjunct, for `s85_Ulim`; the case `j = 0`
is `s8d_clause2a`).  Proof: `U_t P f = U_1 (U_{t-1} P f)`, positive-time smoothing `s8d_smoothing` at time `1`
applied to `U_{t-1} P f` (decay `s8d_clause2a_Ulim`, bounded propagation for `t - 1 < 1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_pd_le {h : Euc d → ℝ} (k : ℕ) (i : Fin k → Fin d) (x : Euc d) :
    |partialDeriv i h x| ≤ ‖iteratedFDeriv ℝ k h x‖ := by
  unfold partialDeriv
  have := (iteratedFDeriv ℝ k h x).le_opNorm (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
  have hp : ∏ l : Fin k, ‖(EuclideanSpace.single (i l) (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [hp, mul_one, Real.norm_eq_abs] at this
  exact this

theorem s8d_wsup1_le {M B : ℝ} {h : Euc d → ℝ} (h0 : ∀ x, ‖h x‖ ≤ B * jbracket x ^ M)
    (hD : ∀ x, ‖fderiv ℝ h x‖ ≤ B * jbracket x ^ M) : weightedSupE 1 (-M) h ≤ ENNReal.ofReal B := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  have hq : 0 ≤ jbracket x ^ (-M) := Real.rpow_nonneg (s83_jb_pos x).le _
  have e : jbracket x ^ (-M) * jbracket x ^ M = 1 := by
    rw [← Real.rpow_add (s83_jb_pos x)]; simp
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by have := j.2; omega
  have hbd : ‖iteratedFDeriv ℝ (j : ℕ) h x‖ ≤ B * jbracket x ^ M := by
    rcases hj with hj | hj
    · rw [hj, norm_iteratedFDeriv_zero]; exact h0 x
    · rw [hj, norm_iteratedFDeriv_one]; exact hD x
  calc jbracket x ^ (-M) * |partialDeriv i h x| ≤ jbracket x ^ (-M) * (B * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_left ((s8d_pd_le (j : ℕ) i x).trans hbd) hq
    _ = B := by rw [mul_left_comm, e, mul_one]

set_option maxHeartbeats 1600000 in
theorem s8d_clause2b_one (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ C1 c : ℝ, 0 < c ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ {f : Euc d → ℝ}, MemCM M f →
      MemCMj M 1 (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
      weightedSupE 1 (-M) (s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (C1 * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  have hM := hMpos.le
  obtain ⟨Cd, c, hc, h2a⟩ := s8d_clause2a_Ulim hd ha hβ hρ hMpos
  have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hM, hρ⟩
  obtain ⟨Ks, hKs0, hKs⟩ := s8d_smoothing H1 hMpos
  obtain ⟨K1, hK10, hK1⟩ := s85_Ulim_wsup H1
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_bound H1
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  obtain ⟨mM, hmM0, hmM⟩ : ∃ mM : ℝ, 0 ≤ mM ∧ mM = ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    ⟨_, integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _, rfl⟩
  obtain ⟨Cg, hCg0, hCg⟩ : ∃ Cg : ℝ, 0 ≤ Cg ∧ Cg = max (max Cd 0 * Real.exp c) (K1 * (1 + mM) * Real.exp (2 * c)) :=
    ⟨_, le_max_of_le_left (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le), rfl⟩
  obtain ⟨B0, hB00, hB0⟩ : ∃ B0 : ℝ, 0 ≤ B0 ∧ B0 = max Ks Kb := ⟨_, le_max_of_le_left hKs0, rfl⟩
  refine ⟨B0 * Cg, c, hc, fun {t} ht {f} hf => ?_⟩
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
  -- smoothing and zero order bounds for `U_1 g`
  obtain ⟨hC1, hgrad, -⟩ := hKs one_pos le_rfl hgM hwg
  have hzero : ∀ x, ‖s85_Ulim a β ρβ M 1 g x‖ ≤ Kb * Φg * jbracket x ^ M := fun x => by
    have := hKb zero_le_one le_rfl hgM (s85_zero_memCM M) (Φ := Φg) (fun w => by simpa using hwg w) x
    rw [s85_Ulim_zero_fun H1 zero_le_one le_rfl, sub_zero] at this
    rw [Real.norm_eq_abs]; exact this
  rw [hsg]
  refine ⟨hC1, ?_⟩
  have hB := s8d_wsup1_le (M := M) (B := B0 * Φg) (h := s85_Ulim a β ρβ M 1 g)
    (fun x => (hzero x).trans (by
      have := Real.rpow_nonneg (s83_jb_pos x).le M
      rw [hB0]; nlinarith [mul_nonneg (le_max_right Ks Kb |>.trans' hKb0) hΦg0, mul_nonneg hΦg0 this,
        mul_le_mul_of_nonneg_right (le_max_right Ks Kb) (mul_nonneg hΦg0 this)]))
    (fun x => (hgrad x).trans (by
      have := Real.rpow_nonneg (s83_jb_pos x).le M
      rw [Real.one_rpow, mul_one, hB0]
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left Ks Kb) (mul_nonneg hΦg0 this)]))
  refine hB.trans ?_
  rw [← hΦfe, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_left hΦg_le hB00
  nlinarith [this]

end HRS.MS.Wad
