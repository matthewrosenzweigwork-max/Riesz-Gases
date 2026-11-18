import HRS.MS.S82QT2

/-!
# S8.2 (S82Q): R07, inner row bound (assembly)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

lemma s82q_jb_rpow_pow {d : ℕ} (M : ℝ) (x : Euc d) (k : ℕ) :
    (jbracket x ^ M) ^ k = jbracket x ^ ((k : ℝ) * M) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (HRS.MS.S82N.s82n_jb_pos x).le, mul_comm]

lemma s82q_jb_rpow_one_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (x : Euc d) : 1 ≤ jbracket x ^ M :=
  Real.one_le_rpow (HRS.MS.S82N.s82n_jb_one_le x) hM

theorem s82q_inner_mean {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ Gt : Euc d → Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d × Euc d => Gt p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) Gt →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |Gt x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ m : ℕ, ∀ x y : Euc d, x ≠ y → ∀ i : Fin (m + 1),
        |∫ z, Gt x y z ∂((referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 3) (m + 1)
            (Fin.cons y (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) :
              Fin (1 + 1) → Euc d)).map (fun X => X i))| ≤
          Cm * A * jbracket x ^ M * jbracket y ^ M * (jbracket x ^ M + jbracket y ^ M) *
            pole x y * (logN (m + 3) / ((m + 3 : ℕ) : ℝ)) := by
  obtain ⟨C2, hC2, hr2⟩ := s82q_row_triple d hd M G c hM hG hc beta hbeta q hq
  obtain ⟨C3, hC3, hr3⟩ := s82q_row_triple_cap d hd M G c hM hG hc q hq
  refine ⟨|C1| * (C2 + C3), by positivity, ?_⟩
  intro h hW hP A hA Gt hGm hGc hGb m x y hxy i
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 3 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  have hδ := s82p2_deltaN_nonneg (N := N) (by omega)
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  have hLN := s82q_logN_le (N := N) (by omega)
  let pins2 : Fin (1 + 1) → Euc d :=
    Fin.cons y (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d)
  have hpinsum : ∀ z : Euc d, ∑ j, q (z - pins2 j) = q (z - y) + q (z - x) := by
    intro z
    simp [pins2, Fin.sum_univ_succ]
  have hprob : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins2) :=
    hW.probability N hN (1 + 1) (m + 1) (by omega) (by omega) pins2
  set ψ : Euc d → ℝ := Gt x y with hψdef
  have hψm : Measurable ψ :=
    hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hae : ∀ᵐ z ∂mu, z ≠ x ∧ z ≠ y := (s82q_ae_ne hd rho x).and (s82q_ae_ne hd rho y)
  have hψb : ∀ᵐ z ∂mu, |ψ z| ≤
      (A * jbracket x ^ M * jbracket y ^ M) * (jbracket z ^ M * triplePole x y z) :=
    hae.mono fun z hz => by
      have := hGb x y z hxy (Ne.symm hz.1) (Ne.symm hz.2)
      calc |ψ z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z := this
        _ = _ := by ring
  have hψi : Integrable ψ mu := (hGc.2 x y hxy).1
  have hψ0 : ∫ z, ψ z ∂mu = 0 := (hGc.2 x y hxy).2
  have hPx := s82q_jb_rpow_one_le hM x
  have hQy := s82q_jb_rpow_one_le hM y
  have hP1 := s82q_pole_ge_one x y
  set Pw := jbracket x ^ M with hPwdef
  set Qw := jbracket y ^ M with hQwdef
  set pp := pole x y with hppdef
  set L := logN N with hLdef
  have hjbx : jbracket x ^ (2 * M) = Pw ^ 2 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  have hjby : jbracket y ^ (2 * M) = Qw ^ 2 := by rw [hQwdef, s82q_jb_rpow_pow]; norm_num
  -- (II) the conditional mean of psi under every one-site marginal
  set cap : Euc d → ℝ := fun z => min 1 ((1 + q (x - z) + q (y - z)) / N) with hcapdef
  have hcap_eq : ∀ z : Euc d, min 1 ((1 + ∑ j, q (z - pins2 j)) / N) = cap z := by
    intro z
    simp only [hcapdef]
    rw [hpinsum z, show z - y = -(y - z) by abel, show z - x = -(x - z) by abel, hq.even, hq.even]
    have : 1 + (q (y - z) + q (x - z)) = 1 + q (x - z) + q (y - z) := by ring
    rw [this]
  have hcap0 : ∀ z, 0 ≤ cap z := fun z =>
    le_min zero_le_one (div_nonneg (by
      have := hq.nonneg (x - z); have := hq.nonneg (y - z); linarith) hNr.le)
  have hcap1 : ∀ z, cap z ≤ 1 := fun z => min_le_left _ _
  have hcapm : Measurable cap :=
    measurable_const.min (((measurable_const.add (hq.measurable.comp (measurable_const.sub measurable_id))).add
      (hq.measurable.comp (measurable_const.sub measurable_id))).div_const _)
  have hfac : ∀ z, 0 ≤ C1 * Phase2S82.deltaN N + C1 * cap z := fun z =>
    add_nonneg (mul_nonneg hC1 hδ) (mul_nonneg hC1 (hcap0 z))
  have hint' : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z)) mu := by
    refine hψi.abs.mul_bdd (c := C1 * Phase2S82.deltaN N + C1)
      ((measurable_const.add (measurable_const.mul hcapm)).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfac z)]
    nlinarith [mul_le_mul_of_nonneg_left (hcap1 z) hC1]
  have hint : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins2 j)) / N))) mu := by
    simpa only [hcap_eq] using hint'
  set M1 : ℝ := A * C1 * (C2 + C3) * Pw * Qw * (Pw + Qw) * pp * (L / N) with hM1
  have hM10 : 0 ≤ M1 := by
    have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
    have := add_nonneg hC2 hC3
    positivity
  have hdel : Phase2S82.deltaN N = L / N := rfl
  have hE1 : ∫ z, |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins2 j)) / N)) ∂mu ≤ M1 := by
    simp_rw [hcap_eq]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => mul_nonneg (abs_nonneg _) (hfac z))
      hint'.1]
    refine ENNReal.toReal_le_of_le_ofReal hM10 ?_
    have hT0 : ∀ z, 0 ≤ triplePole x y z := fun z => by
      have := s82q_pole_ge_one x z; have := s82q_pole_ge_one y z
      unfold triplePole; positivity
    have hg0 : ∀ z, 0 ≤ Phase2S82.deltaN N * (jbracket z ^ M * triplePole x y z) := fun z =>
      mul_nonneg hδ (mul_nonneg (s82q_jb_rpow_nonneg M z) (hT0 z))
    have hh0 : ∀ z, 0 ≤ jbracket z ^ M * triplePole x y z * cap z := fun z =>
      mul_nonneg (mul_nonneg (s82q_jb_rpow_nonneg M z) (hT0 z)) (hcap0 z)
    have hgm : Measurable (fun z => Phase2S82.deltaN N * (jbracket z ^ M * triplePole x y z)) :=
      measurable_const.mul ((s82q_measurable_jb M).mul (s82q_measurable_triplePole x y))
    have hhm : Measurable (fun z => jbracket z ^ M * triplePole x y z * cap z) :=
      ((s82q_measurable_jb M).mul (s82q_measurable_triplePole x y)).mul hcapm
    have h1 : ∫⁻ z, ENNReal.ofReal (Phase2S82.deltaN N * (jbracket z ^ M * triplePole x y z)) ∂mu ≤
        ENNReal.ofReal (Phase2S82.deltaN N * (C2 * (Pw + Qw) * pp)) := by
      refine (s82q_lint_scale mu _ (fun z => jbracket z ^ M * triplePole x y z) (Phase2S82.deltaN N) hδ
        (ae_of_all _ fun z => le_refl _)).trans ?_
      rw [ENNReal.ofReal_mul hδ]
      exact mul_le_mul_of_nonneg_left (hr2 rho hρ hρG x y hxy) bot_le
    have h2 : ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * triplePole x y z * cap z) ∂mu ≤
        ENNReal.ofReal (C3 * (Pw + Qw) * pp * L / N) := hr3 rho hρ hρG N hN x y hxy
    have hB1 : 0 ≤ Phase2S82.deltaN N * (C2 * (Pw + Qw) * pp) := by positivity
    have hB2 : 0 ≤ C3 * (Pw + Qw) * pp * L / N := by
      have : 0 ≤ L := by linarith
      positivity
    refine (s82q_split2 mu (fun z => |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z))
      (fun z => Phase2S82.deltaN N * (jbracket z ^ M * triplePole x y z))
      (fun z => jbracket z ^ M * triplePole x y z * cap z) (A * Pw * Qw * C1) (by positivity)
      hgm hhm hg0 hh0 (hψb.mono fun z hz => ?_) _ _ hB1 hB2 h1 h2).trans (le_of_eq ?_)
    · have hfz := hfac z
      calc |ψ z| * (C1 * Phase2S82.deltaN N + C1 * cap z)
          ≤ ((A * Pw * Qw) * (jbracket z ^ M * triplePole x y z)) * (C1 * Phase2S82.deltaN N + C1 * cap z) :=
            mul_le_mul_of_nonneg_right hz hfz
        _ = _ := by ring
    · congr 1
      rw [hdel, hM1]
      field_simp
  have hmean : ∀ i : Fin (m + 1), |∫ z, ψ z ∂((referenceLaw q h mu beta N (m + 1) pins2).map
      (fun X => X i))| ≤ M1 := fun i =>
    (s82p2_marg_mean_abs_le hP hN (p := 1 + 1) (n := m + 1) (by omega) (by omega) (by omega)
      pins2 i hprob ψ hψm hψi hψ0 hint).trans hE1
  have hfinal := hmean i
  have hM1' : M1 = (|C1| * (C2 + C3)) * A * jbracket x ^ M * jbracket y ^ M *
      (jbracket x ^ M + jbracket y ^ M) * pole x y * (logN (m + 3) / ((m + 3 : ℕ) : ℝ)) := by
    rw [hM1, abs_of_nonneg hC1]; ring
  rw [← hM1']
  exact hfinal

theorem s82q_inner {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ Cin : ℝ, 0 ≤ Cin ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ Gt : Euc d → Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d × Euc d => Gt p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) Gt →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |Gt x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ m : ℕ, ∀ x y : Euc d, x ≠ y →
        ∫⁻ Y, ENNReal.ofReal ((∑ k, Gt x y (Y k)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 3) (m + 1)
            (Fin.cons y (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) :
              Fin (1 + 1) → Euc d) ≤
          ENNReal.ofReal (Cin * A ^ 2 * jbracket x ^ (4 * M) * jbracket y ^ (4 * M) *
            pole x y ^ 2 * ((m + 3 : ℕ) : ℝ) * logN (m + 3)) := by
  obtain ⟨CS, hCS, hrS⟩ := s82q_row_triple_sq d hd (2 * M) G c (by linarith) hG hc beta hbeta q hq
  obtain ⟨Cm, hCm, hCmb⟩ := s82q_inner_mean hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq G c hG hc hρ hρG
  refine ⟨8 * C0 ^ 2 * CS + 4 * Cm ^ 2, by positivity, ?_⟩
  intro h hW hP A hA Gt hGm hGc hGb m x y hxy
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 3 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  have hδ := s82p2_deltaN_nonneg (N := N) (by omega)
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  have hLN := s82q_logN_le (N := N) (by omega)
  let pins2 : Fin (1 + 1) → Euc d :=
    Fin.cons y (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d)
  have hpinsum : ∀ z : Euc d, ∑ j, q (z - pins2 j) = q (z - y) + q (z - x) := by
    intro z
    simp [pins2, Fin.sum_univ_succ]
  have hprob : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins2) :=
    hW.probability N hN (1 + 1) (m + 1) (by omega) (by omega) pins2
  set ψ : Euc d → ℝ := Gt x y with hψdef
  have hψm : Measurable ψ :=
    hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hae : ∀ᵐ z ∂mu, z ≠ x ∧ z ≠ y := (s82q_ae_ne hd rho x).and (s82q_ae_ne hd rho y)
  have hψb : ∀ᵐ z ∂mu, |ψ z| ≤
      (A * jbracket x ^ M * jbracket y ^ M) * (jbracket z ^ M * triplePole x y z) :=
    hae.mono fun z hz => by
      have := hGb x y z hxy (Ne.symm hz.1) (Ne.symm hz.2)
      calc |ψ z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z := this
        _ = _ := by ring
  have hψi : Integrable ψ mu := (hGc.2 x y hxy).1
  have hψ0 : ∫ z, ψ z ∂mu = 0 := (hGc.2 x y hxy).2
  have hPx := s82q_jb_rpow_one_le hM x
  have hQy := s82q_jb_rpow_one_le hM y
  have hP1 := s82q_pole_ge_one x y
  set Pw := jbracket x ^ M with hPwdef
  set Qw := jbracket y ^ M with hQwdef
  set pp := pole x y with hppdef
  set L := logN N with hLdef
  have hjbx : jbracket x ^ (2 * M) = Pw ^ 2 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  have hjby : jbracket y ^ (2 * M) = Qw ^ 2 := by rw [hQwdef, s82q_jb_rpow_pow]; norm_num
  -- (I) weighted second moment of psi
  set nu := s82q_nu q mu beta N pins2 with hnu
  have hwm : Measurable (fun z : Euc d => ENNReal.ofReal
      (Real.exp (-(beta / N) * ∑ j, q (z - pins2 j)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => hq.measurable.comp (measurable_id.sub measurable_const))))
  set BS : ℝ := A ^ 2 * (Pw ^ 2 * Qw ^ 2) * (CS * (Pw ^ 2 + Qw ^ 2) * pp ^ 2 * L) with hBS
  have hBS0 : 0 ≤ BS := by positivity
  have hSl : ∫⁻ z, ENNReal.ofReal (ψ z ^ 2) ∂nu ≤ ENNReal.ofReal BS := by
    rw [hnu]
    unfold s82q_nu
    have hfm : Measurable (fun z => ENNReal.ofReal (ψ z ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hψm.pow_const 2)
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
    have hrow := hrS rho hρ hρG N hN x y hxy
    calc ∫⁻ z, (fun z => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins2 j)))) z *
            ENNReal.ofReal (ψ z ^ 2) ∂mu
        = ∫⁻ z, ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (z - pins2 j)) * ψ z ^ 2) ∂mu := by
          refine lintegral_congr fun z => ?_
          simp only
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (A ^ 2 * (Pw ^ 2 * Qw ^ 2)) *
            ∫⁻ z, ENNReal.ofReal (jbracket z ^ (2 * M) * triplePole x y z ^ 2 *
              Real.exp (-(beta / N) * (q (z - y) + q (z - x)))) ∂mu := by
          refine s82q_lint_scale _ _ _ _ (by positivity) (hψb.mono fun z hz => ?_)
          rw [hpinsum z]
          have hB0 : 0 ≤ (A * Pw * Qw) * (jbracket z ^ M * triplePole x y z) := by
            have := s82q_jb_rpow_nonneg M z
            have hT0 : 0 ≤ triplePole x y z := by
              have := s82q_pole_ge_one x z; have := s82q_pole_ge_one y z
              unfold triplePole; positivity
            positivity
          have h2 : ψ z ^ 2 ≤ ((A * Pw * Qw) * (jbracket z ^ M * triplePole x y z)) ^ 2 := by
            calc ψ z ^ 2 = |ψ z| ^ 2 := (sq_abs _).symm
              _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hz 2
          have e : ((A * Pw * Qw) * (jbracket z ^ M * triplePole x y z)) ^ 2 =
              (A ^ 2 * (Pw ^ 2 * Qw ^ 2)) * (jbracket z ^ (2 * M) * triplePole x y z ^ 2) := by
            rw [← s82q_jb_rpow_pow M z 2 |>.trans (by norm_num : jbracket z ^ (((2 : ℕ) : ℝ) * M) =
              jbracket z ^ (2 * M))]
            ring
          have hex := (Real.exp_pos (-(beta / N) * (q (z - y) + q (z - x)))).le
          calc Real.exp (-(beta / N) * (q (z - y) + q (z - x))) * ψ z ^ 2
              ≤ Real.exp (-(beta / N) * (q (z - y) + q (z - x))) *
                ((A ^ 2 * (Pw ^ 2 * Qw ^ 2)) * (jbracket z ^ (2 * M) * triplePole x y z ^ 2)) := by
                rw [← e]; exact mul_le_mul_of_nonneg_left h2 hex
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (A ^ 2 * (Pw ^ 2 * Qw ^ 2)) *
            ENNReal.ofReal (CS * (jbracket x ^ (2 * M) + jbracket y ^ (2 * M)) * pp ^ 2 * L) :=
          mul_le_mul_of_nonneg_left hrow bot_le
      _ = ENNReal.ofReal BS := by
          rw [← ENNReal.ofReal_mul (by positivity), hjbx, hjby]
  have hψ2 : Integrable (fun z => ψ z ^ 2) nu := by
    have := s82q_memLp_two_of_lintegral (P := nu) hψm.aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSl)
    exact (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).1 this
  have hψ2int : ∫ z, ψ z ^ 2 ∂nu ≤ BS := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      (hψm.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hBS0 hSl
  -- (III) assembly
  set M1 : ℝ := A * Cm * Pw * Qw * (Pw + Qw) * pp * (L / N) with hM1
  have hmean : ∀ i : Fin (m + 1), |∫ z, ψ z ∂((referenceLaw q h mu beta N (m + 1) pins2).map
      (fun X => X i))| ≤ M1 := fun i =>
    (hCmb h hW hP A hA Gt hGm hGc hGb m x y hxy i).trans (le_of_eq (by rw [hM1]; ring))
  have hM10 : 0 ≤ M1 := by
    have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
    positivity
  have hmain := (s82q_sum_sq hW hbeta hN (p := 1 + 1) (m := m) (by omega) (by omega) (by omega)
    pins2 ψ hψm hψ2 M1 hmean).2
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hx4 : jbracket x ^ (4 * M) = Pw ^ 4 := by rw [hPwdef, s82q_jb_rpow_pow]; norm_num
  have hy4 : jbracket y ^ (4 * M) = Qw ^ 4 := by rw [hQwdef, s82q_jb_rpow_pow]; norm_num
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ N)
  have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have halg := s82q_inner_alg C0 Cm CS A Pw Qw pp L ((N : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) hCS
    hA hPx hQy hP1 hL1 hLN hm0 hm1
  calc 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * ∫ z, ψ z ^ 2 ∂nu + (((m + 1 : ℕ) : ℝ) * M1) ^ 2
      ≤ 4 * C0 ^ 2 * ((m + 1 : ℕ) : ℝ) * BS + (((m + 1 : ℕ) : ℝ) * M1) ^ 2 := by
        gcongr
    _ ≤ _ := halg
    _ = _ := by rw [hx4, hy4]; ring

end HRS.MS.S82Q
