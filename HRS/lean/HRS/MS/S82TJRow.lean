import HRS.MS.S82TRow
import HRS.MS.S82QT3
import HRS.MS.S82QSum
import HRS.MS.S82QPairT

/-!
# S8.2 (S82T): second moment of the once-pinned row `sum_j K(x, X_j)` for a canonical `J`-type kernel
`|K(x,y)| <= A <x>^M <y>^M pole(x,y)`, `int K(x,y) dmu(y) = 0`.  Variance part: row 3 of `weighted_radial_rows`
(`pole^2` against the pin cutoff, factor `log(eN)`); conditional mean: `PinComparison`, canonical zero mean,
`s82q_row_pole` (factor `<x>^M`) and the capped single-anchor row `s82t_row_cap`.  Result
`E S^2 <= C A^2 <x>^{4M} N log(eN)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82Q

theorem s82t_J_row {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ DJ : ℝ, 0 ≤ DJ ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ K : Euc d → Euc d → ℝ,
      Measurable (Function.uncurry K) →
      (∀ x y, x ≠ y → |K x y| ≤ A * Phase2S82.pairWeight M x y * pole x y) →
      (∀ x, Integrable (K x) (HRS.Whole.withDensityReal rho)) →
      (∀ x, ∫ y, K x y ∂HRS.Whole.withDensityReal rho = 0) →
      ∀ m : ℕ, ∀ x : Euc d,
        ∫⁻ X', ENNReal.ofReal ((∑ j, K x (X' j)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 2) (m + 1)
            (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) ≤
          ENNReal.ofReal (DJ * A ^ 2 * jbracket x ^ (4 * M) * ((m + 2 : ℕ) : ℝ) * logN (m + 2)) := by
  obtain ⟨C3, hC3, hr3⟩ := weighted_radial_rows d hd beta (2 * M) G c hbeta (by linarith) hG hc q hq
  obtain ⟨C2, hC2, hr2⟩ := s82q_row_pole d hd M G c hM hG hc beta hbeta q hq
  obtain ⟨C4, hC4, hr4⟩ := s82t_row_cap d hd M G c hM hG hc q hq
  refine ⟨4 * C0 ^ 2 * C3 + C1 ^ 2 * (C2 + C4) ^ 2, ?_, ?_⟩
  · positivity
  intro h hW hP A hA K hKm hKb hKi hK0 m x
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 2 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  have hδ := s82p2_deltaN_nonneg (N := N) (by omega)
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  have hLN := s82q_logN_le (N := N) (by omega)
  let pins1 : Fin (0 + 1) → Euc d := (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d)
  have hpinsum : ∀ z : Euc d, ∑ j, q (z - pins1 j) = q (z - x) := by
    intro z
    simp [pins1, Fin.sum_univ_succ]
  have hqx : ∀ z : Euc d, q (z - x) = q (x - z) := fun z => by
    rw [show z - x = -(x - z) by abel, hq.even]
  have hprob : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins1) :=
    hW.probability N hN (0 + 1) (m + 1) (by omega) (by omega) pins1
  set ψ : Euc d → ℝ := K x with hψdef
  have hψm : Measurable ψ := hKm.comp (measurable_const.prodMk measurable_id)
  have hae : ∀ᵐ z ∂mu, z ≠ x := s82q_ae_ne hd rho x
  have hψb : ∀ᵐ z ∂mu, |ψ z| ≤ (A * jbracket x ^ M) * (jbracket z ^ M * pole x z) :=
    hae.mono fun z hz => by
      have := hKb x z (Ne.symm hz)
      calc |ψ z| ≤ A * Phase2S82.pairWeight M x z * pole x z := this
        _ = _ := by unfold Phase2S82.pairWeight; ring
  have hψi : Integrable ψ mu := hKi x
  have hψ0 : ∫ z, ψ z ∂mu = 0 := hK0 x
  have hPx := s82q_jb_rpow_one_le hM x
  set Pw := jbracket x ^ M with hPwdef
  set L := logN N with hLdef
  have hjbx : jbracket x ^ (2 * M) = Pw ^ 2 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  -- (I) weighted second moment of psi
  set nu := s82q_nu q mu beta N pins1 with hnu
  have hwm : Measurable (fun z : Euc d => ENNReal.ofReal
      (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => hq.measurable.comp (measurable_id.sub measurable_const))))
  set BS : ℝ := A ^ 2 * Pw ^ 2 * (C3 * Pw ^ 2 * L) with hBS
  have hBS0 : 0 ≤ BS := by positivity
  have hSl : ∫⁻ z, ENNReal.ofReal (ψ z ^ 2) ∂nu ≤ ENNReal.ofReal BS := by
    rw [hnu]
    unfold s82q_nu
    have hfm : Measurable (fun z => ENNReal.ofReal (ψ z ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hψm.pow_const 2)
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
    have hrow := (hr3 rho hρ hρG N hN x).2.2.1
    calc ∫⁻ z, (fun z => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)))) z *
            ENNReal.ofReal (ψ z ^ 2) ∂mu
        = ∫⁻ z, ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins1 j)) * ψ z ^ 2) ∂mu := by
          refine lintegral_congr fun z => ?_
          simp only
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (A ^ 2 * Pw ^ 2) *
            ∫⁻ z, ENNReal.ofReal (jbracket z ^ (2 * M) * pole x z ^ 2 *
              Real.exp (-(beta / N) * q (x - z))) ∂mu := by
          refine s82q_lint_scale _ _ _ _ (by positivity) (hψb.mono fun z hz => ?_)
          rw [hpinsum z, hqx z]
          have hB0 : 0 ≤ (A * Pw) * (jbracket z ^ M * pole x z) := by
            have := s82q_jb_rpow_nonneg M z
            have := s82q_pole_ge_one x z
            positivity
          have h2 : ψ z ^ 2 ≤ ((A * Pw) * (jbracket z ^ M * pole x z)) ^ 2 := by
            calc ψ z ^ 2 = |ψ z| ^ 2 := (sq_abs _).symm
              _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hz 2
          have e : ((A * Pw) * (jbracket z ^ M * pole x z)) ^ 2 =
              (A ^ 2 * Pw ^ 2) * (jbracket z ^ (2 * M) * pole x z ^ 2) := by
            rw [← s82q_jb_rpow_pow M z 2 |>.trans (by norm_num : jbracket z ^ (((2 : ℕ) : ℝ) * M) =
              jbracket z ^ (2 * M))]
            ring
          have hex := (Real.exp_pos (-(beta / N) * q (x - z))).le
          calc Real.exp (-(beta / N) * q (x - z)) * ψ z ^ 2
              ≤ Real.exp (-(beta / N) * q (x - z)) *
                ((A ^ 2 * Pw ^ 2) * (jbracket z ^ (2 * M) * pole x z ^ 2)) := by
                rw [← e]; exact mul_le_mul_of_nonneg_left h2 hex
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (A ^ 2 * Pw ^ 2) * ENNReal.ofReal (C3 * jbracket x ^ (2 * M) * L) :=
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
  -- (II) the conditional mean of psi under every one-site marginal
  set cap : Euc d → ℝ := fun z => min 1 ((1 + q (x - z)) / N) with hcapdef
  have hcap_eq : ∀ z : Euc d, min 1 ((1 + ∑ j, q (z - pins1 j)) / N) = cap z := by
    intro z
    simp only [hcapdef]
    rw [hpinsum z, hqx z]
  have hcap0 : ∀ z, 0 ≤ cap z := fun z =>
    le_min zero_le_one (div_nonneg (by have := hq.nonneg (x - z); linarith) hNr.le)
  have hcap1 : ∀ z, cap z ≤ 1 := fun z => min_le_left _ _
  have hcapm : Measurable cap :=
    measurable_const.min ((measurable_const.add (hq.measurable.comp (measurable_const.sub measurable_id))).div_const _)
  have hfac : ∀ z, 0 ≤ C1 * Phase2S82.deltaN N + C1 * cap z := fun z =>
    add_nonneg (mul_nonneg hC1 hδ) (mul_nonneg hC1 (hcap0 z))
  have hint' : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z)) mu := by
    refine hψi.abs.mul_bdd (c := C1 * Phase2S82.deltaN N + C1)
      ((measurable_const.add (measurable_const.mul hcapm)).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfac z)]
    nlinarith [mul_le_mul_of_nonneg_left (hcap1 z) hC1]
  have hint : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins1 j)) / N))) mu := by
    simpa only [hcap_eq] using hint'
  set M1 : ℝ := A * C1 * (C2 + C4) * Pw ^ 2 * (L / N) with hM1
  have hM10 : 0 ≤ M1 := by
    have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
    have := add_nonneg hC2 hC4
    positivity
  have hdel : Phase2S82.deltaN N = L / N := rfl
  have hE1 : ∫ z, |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins1 j)) / N)) ∂mu ≤ M1 := by
    simp_rw [hcap_eq]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => mul_nonneg (abs_nonneg _) (hfac z))
      hint'.1]
    refine ENNReal.toReal_le_of_le_ofReal hM10 ?_
    have hT0 : ∀ z, 0 ≤ pole x z := fun z => by have := s82q_pole_ge_one x z; linarith
    have hg0 : ∀ z, 0 ≤ Phase2S82.deltaN N * (jbracket z ^ M * pole x z) := fun z =>
      mul_nonneg hδ (mul_nonneg (s82q_jb_rpow_nonneg M z) (hT0 z))
    have hh0 : ∀ z, 0 ≤ jbracket z ^ M * pole x z * cap z := fun z =>
      mul_nonneg (mul_nonneg (s82q_jb_rpow_nonneg M z) (hT0 z)) (hcap0 z)
    have hgm : Measurable (fun z => Phase2S82.deltaN N * (jbracket z ^ M * pole x z)) :=
      measurable_const.mul ((s82q_measurable_jb M).mul (s82q_measurable_pole x))
    have hhm : Measurable (fun z => jbracket z ^ M * pole x z * cap z) :=
      ((s82q_measurable_jb M).mul (s82q_measurable_pole x)).mul hcapm
    have h1 : ∫⁻ z, ENNReal.ofReal (Phase2S82.deltaN N * (jbracket z ^ M * pole x z)) ∂mu ≤
        ENNReal.ofReal (Phase2S82.deltaN N * (C2 * Pw)) := by
      refine (s82q_lint_scale mu _ (fun z => jbracket z ^ M * pole x z) (Phase2S82.deltaN N) hδ
        (ae_of_all _ fun z => le_refl _)).trans ?_
      rw [ENNReal.ofReal_mul hδ]
      exact mul_le_mul_of_nonneg_left (hr2 rho hρ hρG x) bot_le
    have h2 : ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * pole x z * cap z) ∂mu ≤
        ENNReal.ofReal (C4 * Pw * L / N) := hr4 rho hρ hρG N hN x
    have hB1 : 0 ≤ Phase2S82.deltaN N * (C2 * Pw) := by positivity
    have hB2 : 0 ≤ C4 * Pw * L / N := by
      have : 0 ≤ L := by linarith
      positivity
    refine (s82q_split2 mu (fun z => |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z))
      (fun z => Phase2S82.deltaN N * (jbracket z ^ M * pole x z))
      (fun z => jbracket z ^ M * pole x z * cap z) (A * Pw * C1) (by positivity)
      hgm hhm hg0 hh0 (hψb.mono fun z hz => ?_) _ _ hB1 hB2 h1 h2).trans (le_of_eq ?_)
    · have hfz := hfac z
      calc |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z)
          ≤ ((A * Pw) * (jbracket z ^ M * pole x z)) * (C1 * Phase2S82.deltaN N + C1 * cap z) :=
            mul_le_mul_of_nonneg_right hz hfz
        _ = _ := by ring
    · congr 1
      rw [hdel, hM1]
      ring
  have hmean : ∀ i : Fin (m + 1), |∫ z, ψ z ∂((referenceLaw q h mu beta N (m + 1) pins1).map
      (fun X => X i))| ≤ M1 := fun i =>
    (s82p2_marg_mean_abs_le hP hN (p := 0 + 1) (n := m + 1) (by omega) (by omega) (by omega)
      pins1 i hprob ψ hψm hψi hψ0 hint).trans hE1
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
  have hA2 : (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ C1 ^ 2 * (C2 + C4) ^ 2 * A ^ 2 * Pw ^ 4 * ((N : ℕ) : ℝ) * L := by
    have hmM : ((m + 1 : ℕ) : ℝ) * M1 ≤ ((N : ℕ) : ℝ) * M1 := mul_le_mul_of_nonneg_right hm1 hM10
    have h1 : (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ (((N : ℕ) : ℝ) * M1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmM 2
    have h2 : (((N : ℕ) : ℝ) * M1) ^ 2 = C1 ^ 2 * (C2 + C4) ^ 2 * A ^ 2 * Pw ^ 4 * L ^ 2 := by
      rw [hM1]
      first | (field_simp; ring) | field_simp
    have h3 : L ^ 2 ≤ ((N : ℕ) : ℝ) * L := by nlinarith
    calc (((m + 1 : ℕ) : ℝ) * M1) ^ 2 ≤ _ := h1
      _ = C1 ^ 2 * (C2 + C4) ^ 2 * A ^ 2 * Pw ^ 4 * L ^ 2 := h2
      _ ≤ C1 ^ 2 * (C2 + C4) ^ 2 * A ^ 2 * Pw ^ 4 * (((N : ℕ) : ℝ) * L) := by
          gcongr
      _ = _ := by ring
  calc 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * ∫ z, ψ z ^ 2 ∂nu + (((m + 1 : ℕ) : ℝ) * M1) ^ 2
      ≤ 4 * C0 ^ 2 * ((N : ℕ) : ℝ) * BS +
          C1 ^ 2 * (C2 + C4) ^ 2 * A ^ 2 * Pw ^ 4 * ((N : ℕ) : ℝ) * L := add_le_add hA1 hA2
    _ = _ := by rw [hx4, hBS]; ring

end HRS.MS.S82T
