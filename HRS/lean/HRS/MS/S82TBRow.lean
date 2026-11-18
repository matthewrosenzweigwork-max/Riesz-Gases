import HRS.MS.S82TJRow

/-!
# S8.2 (S82T): second moment of the once-pinned row `sum_j K(x, X_j)` for a repeated-pair kernel
`|K(x,y)| <= A <x>^M <y>^M pole(x,y)^2` (not canonical: the conditional mean is bounded directly by
domination of the one-site marginals by `C0 nu_x`, row 3 of `weighted_radial_rows`).  Variance part: row 4
(`pole^4` against the pin cutoff, factor `N^2`).  Result `E S^2 <= C A^2 <x>^{4M} N^3`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82Q

theorem s82t_B_row {d : ℕ} (hd : 2 ≤ d) {a beta M C0 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ DB : ℝ, 0 ≤ DB ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      ∀ A : ℝ, 0 ≤ A → ∀ K : Euc d → Euc d → ℝ, Measurable (Function.uncurry K) →
      (∀ x y, x ≠ y → |K x y| ≤ A * Phase2S82.pairWeight M x y * pole x y ^ 2) →
      ∀ m : ℕ, ∀ x : Euc d,
        ∫⁻ X', ENNReal.ofReal ((∑ j, K x (X' j)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 2) (m + 1)
            (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) ≤
          ENNReal.ofReal (DB * A ^ 2 * jbracket x ^ (4 * M) * ((m + 2 : ℕ) : ℝ) ^ 3) := by
  obtain ⟨C4, hC4, hr4⟩ := weighted_radial_rows d hd beta (2 * M) G c hbeta (by linarith) hG hc q hq
  obtain ⟨C3, hC3, hr3⟩ := weighted_radial_rows d hd beta M G c hbeta hM hG hc q hq
  refine ⟨4 * C0 ^ 2 * C4 + 12 * C0 ^ 2 * C3 ^ 2, by positivity, ?_⟩
  intro h hW A hA K hKm hKb m x
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 2 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  have hL2 := s82t_logN_sq_le (N := N) (by omega)
  let pins1 : Fin (0 + 1) → Euc d := (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d)
  have hpinsum : ∀ z : Euc d, ∑ j, q (z - pins1 j) = q (z - x) := by
    intro z
    simp [pins1, Fin.sum_univ_succ]
  have hqx : ∀ z : Euc d, q (z - x) = q (x - z) := fun z => by
    rw [show z - x = -(x - z) by abel, hq.even]
  set ψ : Euc d → ℝ := K x with hψdef
  have hψm : Measurable ψ := hKm.comp (measurable_const.prodMk measurable_id)
  have hae : ∀ᵐ z ∂mu, z ≠ x := s82q_ae_ne hd rho x
  have hψb : ∀ᵐ z ∂mu, |ψ z| ≤ (A * jbracket x ^ M) * (jbracket z ^ M * pole x z ^ 2) :=
    hae.mono fun z hz => by
      have := hKb x z (Ne.symm hz)
      calc |ψ z| ≤ A * Phase2S82.pairWeight M x z * pole x z ^ 2 := this
        _ = _ := by unfold Phase2S82.pairWeight; ring
  have hPx := s82q_jb_rpow_one_le hM x
  set Pw := jbracket x ^ M with hPwdef
  set L := logN N with hLdef
  have hjbx : jbracket x ^ (2 * M) = Pw ^ 2 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  set nu := s82q_nu q mu beta N pins1 with hnu
  have hwm : Measurable (fun z : Euc d => ENNReal.ofReal
      (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => hq.measurable.comp (measurable_id.sub measurable_const))))
  -- (I) weighted second moment of psi (row 4)
  set BS : ℝ := A ^ 2 * Pw ^ 2 * (C4 * Pw ^ 2 * ((N : ℕ) : ℝ) ^ 2) with hBS
  have hBS0 : 0 ≤ BS := by positivity
  have hSl : ∫⁻ z, ENNReal.ofReal (ψ z ^ 2) ∂nu ≤ ENNReal.ofReal BS := by
    rw [hnu]
    unfold s82q_nu
    have hfm : Measurable (fun z => ENNReal.ofReal (ψ z ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hψm.pow_const 2)
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
    have hrow := (hr4 rho hρ hρG N hN x).2.2.2.1
    calc ∫⁻ z, (fun z => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) z *
            ENNReal.ofReal (ψ z ^ 2) ∂mu
        = ∫⁻ z, ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)) * ψ z ^ 2) ∂mu := by
          refine lintegral_congr fun z => ?_
          simp only
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (A ^ 2 * Pw ^ 2) *
            ∫⁻ z, ENNReal.ofReal (jbracket z ^ (2 * M) * pole x z ^ 4 *
              Real.exp (-(beta / N) * q (x - z))) ∂mu := by
          refine s82q_lint_scale _ _ _ _ (by positivity) (hψb.mono fun z hz => ?_)
          rw [hpinsum z, hqx z]
          have hB0 : 0 ≤ (A * Pw) * (jbracket z ^ M * pole x z ^ 2) := by
            have := s82q_jb_rpow_nonneg M z
            positivity
          have h2 : ψ z ^ 2 ≤ ((A * Pw) * (jbracket z ^ M * pole x z ^ 2)) ^ 2 := by
            calc ψ z ^ 2 = |ψ z| ^ 2 := (sq_abs _).symm
              _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hz 2
          have e : ((A * Pw) * (jbracket z ^ M * pole x z ^ 2)) ^ 2 =
              (A ^ 2 * Pw ^ 2) * (jbracket z ^ (2 * M) * pole x z ^ 4) := by
            rw [← s82q_jb_rpow_pow M z 2 |>.trans (by norm_num : jbracket z ^ (((2 : ℕ) : ℝ) * M) =
              jbracket z ^ (2 * M))]
            ring
          have hex := (Real.exp_pos (-(beta / N) * q (x - z))).le
          calc Real.exp (-(beta / N) * q (x - z)) * ψ z ^ 2
              ≤ Real.exp (-(beta / N) * q (x - z)) *
                ((A ^ 2 * Pw ^ 2) * (jbracket z ^ (2 * M) * pole x z ^ 4)) := by
                rw [← e]; exact mul_le_mul_of_nonneg_left h2 hex
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (A ^ 2 * Pw ^ 2) *
            ENNReal.ofReal (C4 * jbracket x ^ (2 * M) * ((N : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hrow bot_le
      _ = ENNReal.ofReal BS := by
          rw [← ENNReal.ofReal_mul (by positivity), hjbx]
  have hψ2 : Integrable (fun z => ψ z ^ 2) nu := by
    have := s82q_memLp_two_of_lintegral (P := nu) hψm.aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSl)
    exact (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).1 this
  have hψ2int : ∫ z, ψ z ^ 2 ∂nu ≤ BS := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      (hψm.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hBS0 hSl
  -- (II) first absolute moment under nu (row 3), then under every marginal by domination
  set B1 : ℝ := A * Pw * (C3 * Pw * L) with hB1
  have hB10 : 0 ≤ B1 := by positivity
  have hAbs : ∫⁻ z, ENNReal.ofReal |ψ z| ∂nu ≤ ENNReal.ofReal B1 := by
    rw [hnu]
    unfold s82q_nu
    have hfm : Measurable (fun z => ENNReal.ofReal |ψ z|) :=
      ENNReal.measurable_ofReal.comp hψm.abs
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
    have hrow := (hr3 rho hρ hρG N hN x).2.2.1
    calc ∫⁻ z, (fun z => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) z *
            ENNReal.ofReal |ψ z| ∂mu
        = ∫⁻ z, ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)) * |ψ z|) ∂mu := by
          refine lintegral_congr fun z => ?_
          simp only
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (A * Pw) *
            ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * pole x z ^ 2 *
              Real.exp (-(beta / N) * q (x - z))) ∂mu := by
          refine s82q_lint_scale _ _ _ _ (by positivity) (hψb.mono fun z hz => ?_)
          rw [hpinsum z, hqx z]
          have hex := (Real.exp_pos (-(beta / N) * q (x - z))).le
          calc Real.exp (-(beta / N) * q (x - z)) * |ψ z|
              ≤ Real.exp (-(beta / N) * q (x - z)) *
                ((A * Pw) * (jbracket z ^ M * pole x z ^ 2)) :=
                mul_le_mul_of_nonneg_left hz hex
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (A * Pw) * ENNReal.ofReal (C3 * jbracket x ^ M * L) :=
          mul_le_mul_of_nonneg_left hrow bot_le
      _ = ENNReal.ofReal B1 := by
          rw [← ENNReal.ofReal_mul (by positivity), hB1]
  set M1 : ℝ := C0 * B1 with hM1
  have hM10 : 0 ≤ M1 := by positivity
  have hmean : ∀ i : Fin (m + 1), |∫ z, ψ z ∂((referenceLaw q h mu beta N (m + 1) pins1).map
      (fun X => X i))| ≤ M1 := by
    intro i
    have hdom := s82q_marg_le_nu hW hbeta hN (p := 0 + 1) (m := m) (by omega) (by omega) pins1 i
    refine (abs_integral_le_integral_abs).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => abs_nonneg _) hψm.abs.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hM10 ?_
    calc ∫⁻ z, ENNReal.ofReal |ψ z| ∂((referenceLaw q h mu beta N (m + 1) pins1).map (fun X => X i))
        ≤ ∫⁻ z, ENNReal.ofReal |ψ z| ∂(ENNReal.ofReal C0 • nu) := lintegral_mono' hdom le_rfl
      _ = ENNReal.ofReal C0 * ∫⁻ z, ENNReal.ofReal |ψ z| ∂nu := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal B1 := mul_le_mul_of_nonneg_left hAbs bot_le
      _ = ENNReal.ofReal M1 := (ENNReal.ofReal_mul hC0.le).symm
  -- (III) assembly
  have hmain := (s82q_sum_sq hW hbeta hN (p := 0 + 1) (m := m) (by omega) (by omega) (by omega)
    pins1 ψ hψm hψ2 M1 hmean).2
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hx4 : jbracket x ^ (4 * M) = Pw ^ 4 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ N)
  have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hPw0 : 0 ≤ Pw := by linarith
  have hA1 : 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * ∫ z, ψ z ^ 2 ∂nu ≤
      4 * C0 ^ 2 * ((N : ℕ) : ℝ) * BS := by
    calc 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * ∫ z, ψ z ^ 2 ∂nu
        ≤ 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * BS := mul_le_mul_of_nonneg_left hψ2int (by positivity)
      _ ≤ 4 * C0 ^ 2 * ((N : ℕ) : ℝ) * BS := by
          refine mul_le_mul_of_nonneg_right ?_ hBS0
          exact mul_le_mul_of_nonneg_left hm1 (by positivity)
  have hA2 : (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ 12 * C0 ^ 2 * C3 ^ 2 * A ^ 2 * Pw ^ 4 * ((N : ℕ) : ℝ) ^ 3 := by
    have hmM : ((m + 1 : ℕ) : ℝ) * M1 ≤ ((N : ℕ) : ℝ) * M1 := mul_le_mul_of_nonneg_right hm1 hM10
    have h1 : (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ (((N : ℕ) : ℝ) * M1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmM 2
    have h2 : (((N : ℕ) : ℝ) * M1) ^ 2 = C0 ^ 2 * C3 ^ 2 * A ^ 2 * Pw ^ 4 * ((N : ℕ) : ℝ) ^ 2 * L ^ 2 := by
      rw [hM1, hB1]; ring
    have h3 : ((N : ℕ) : ℝ) ^ 2 * L ^ 2 ≤ ((N : ℕ) : ℝ) ^ 2 * (12 * ((N : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    calc (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ _ := h1
      _ = C0 ^ 2 * C3 ^ 2 * A ^ 2 * Pw ^ 4 * (((N : ℕ) : ℝ) ^ 2 * L ^ 2) := by rw [h2]; ring
      _ ≤ C0 ^ 2 * C3 ^ 2 * A ^ 2 * Pw ^ 4 * (((N : ℕ) : ℝ) ^ 2 * (12 * ((N : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring
  calc 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * ∫ z, ψ z ^ 2 ∂nu + (((m + 1 : ℕ) : ℝ) * M1) ^ 2
      ≤ 4 * C0 ^ 2 * ((N : ℕ) : ℝ) * BS +
          12 * C0 ^ 2 * C3 ^ 2 * A ^ 2 * Pw ^ 4 * ((N : ℕ) : ℝ) ^ 3 := add_le_add hA1 hA2
    _ = _ := by rw [hx4, hBS]; ring

end HRS.MS.S82T
