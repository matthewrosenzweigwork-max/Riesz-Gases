import HRS.MS.S82QT3
import HRS.MS.S82QDisS

/-!
# S8.2 (S82Q): R07, the once-pinned outer row: mean of `R_x = sum_{j != k} G(x, Y_j, Y_k)`
Under `Y ~ R_{m+2}^{x}` (`N = m + 3`), the mean of `R_x` is obtained from the signed disintegration over one
coordinate, the conditional mean of each twice-pinned row (`s82q_inner_mean`) and the pole rows:
`|E R_x| <= C A N log(eN) <x>^{3M}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- Second moment from variance and mean. -/
lemma s82q_second_moment {E : Type*} [MeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P]
    {F : E → ℝ} (hF : MemLp F 2 P) (V : ℝ≥0∞) (hV : evariance F P ≤ V) (mm : ℝ)
    (hmm : |∫ x, F x ∂P| ≤ mm) :
    ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂P ≤ V + ENNReal.ofReal (mm ^ 2) := by
  have hev := evariance_def' (μ := P) hF.aestronglyMeasurable
  have hL : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂P = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂P := by
    simp_rw [s82p2_enorm_sq]
  rw [hL]
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂P ≤ evariance F P + ENNReal.ofReal ((∫ x, F x ∂P) ^ 2) := by
    rw [hev]
    exact le_tsub_add
  refine h1.trans (add_le_add hV (ENNReal.ofReal_le_ofReal ?_))
  exact sq_le_sq.2 (hmm.trans (le_abs_self _))

lemma s82q_rpow_add_nat {d : ℕ} (M : ℝ) (hM : 0 ≤ M) (x : Euc d) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    jbracket x ^ (u * M) * jbracket x ^ (v * M) = jbracket x ^ ((u + v) * M) := by
  rw [← Real.rpow_add (HRS.MS.S82N.s82n_jb_pos x)]
  congr 1
  ring

/-- Mean of the once-pinned outer row. -/
theorem s82q_outer_mean {d : ℕ} (hd : 2 ≤ d) {a beta M C0 C1 : ℝ} (hM : 0 ≤ M) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) {rho : Euc d → ℝ} (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ Cmean : ℝ, 0 ≤ Cmean ∧ ∀ (h : ℕ → Euc d → ℝ), WeakReferenceSetup d a beta rho q h C0 →
      PinComparison beta rho q h C1 → ∀ A : ℝ, 0 ≤ A → ∀ Gt : Euc d → Euc d → Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d × Euc d => Gt p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) Gt →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |Gt x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ m : ℕ, ∀ x : Euc d,
      (∀ i : Fin (m + 2), MemLp (s82q_prow (fun y w => Gt x y w) i) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 3) (m + 2)
          (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d))) →
      |∫ Y, Phase2S82.pairSum (fun y w => Gt x y w) Y
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 3) (m + 2)
            (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d)| ≤
        Cmean * A * jbracket x ^ (3 * M) * ((m + 3 : ℕ) : ℝ) * logN (m + 3) := by
  obtain ⟨Cm, hCm, hmean⟩ := s82q_inner_mean hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq G c hG hc hρ hρG
  obtain ⟨Cp1, hCp1, hpole1⟩ := s82q_row_pole d hd M G c hM hG hc beta hbeta q hq
  obtain ⟨Cp2, hCp2, hpole2⟩ := s82q_row_pole d hd (2 * M) G c (by linarith) hG hc beta hbeta q hq
  refine ⟨|C0| * Cm * (Cp1 + Cp2), by positivity, ?_⟩
  intro h hW hP A hA Gt hGm hGc hGb m x hrowL
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  set N := m + 3 with hNdef
  have hN : 2 ≤ N := by omega
  have hC0 := hW.positive
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := s82q_logN_nonneg (N := N) (by omega)
  let pins1 : Fin (0 + 1) → Euc d := Fin.cons x (fun i : Fin 0 => i.elim0)
  set Kx : Euc d → Euc d → ℝ := fun y w => Gt x y w with hKx
  have hKxm : Measurable (Function.uncurry Kx) :=
    hGm.comp (measurable_const.prodMk measurable_id)
  have hψm : ∀ z : Euc d, Measurable (Gt x z) := fun z =>
    hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h1 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 2) pins1) :=
    hW.probability N hN (0 + 1) (m + 2) (by omega) (by omega) pins1
  have h0 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1)
      (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)) := fun z =>
    hW.probability N hN (0 + 1 + 1) (m + 1) (by omega) (by omega) _
  set ref1 := referenceLaw q h mu beta N (m + 2) pins1 with href1
  have hint_i : ∀ i : Fin (m + 2), Integrable (s82q_prow Kx i) ref1 := fun i =>
    (hrowL i).integrable one_le_two
  have hsum : ∫ Y, Phase2S82.pairSum Kx Y ∂ref1 = ∑ i, ∫ Y, s82q_prow Kx i Y ∂ref1 := by
    have : (fun Y : EucConfig d (m + 2) => Phase2S82.pairSum Kx Y) =
        fun Y => ∑ i, s82q_prow Kx i Y := rfl
    rw [this]
    exact integral_finset_sum _ fun i _ => hint_i i
  set Pw := jbracket x ^ M with hPw
  set L := logN N with hL
  have hPw1 : 1 ≤ Pw := s82q_jb_rpow_one_le hM x
  have hmarg_dom : ∀ i : Fin (m + 2), ref1.map (fun Y => Y i) ≤ ENNReal.ofReal C0 • mu := fun i =>
    (s82q_marg_le_nu hW hbeta hN (p := 0 + 1) (by omega) (by omega) pins1 i).trans
      (Measure.le_iff.2 fun s hs => by
        rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (Measure.le_iff.1 (s82q_nu_le q hW.short.nonneg mu beta hbeta N pins1) s hs) bot_le)
  have hmarg_dom2 : ∀ (z : Euc d) (j : Fin (m + 1)), (referenceLaw q h mu beta N (m + 1)
      (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)).map (fun X => X j) ≤ ENNReal.ofReal C0 • mu :=
    fun z j => (s82q_marg_le_nu hW hbeta hN (p := 0 + 1 + 1) (by omega) (by omega) _ j).trans
      (Measure.le_iff.2 fun s hs => by
        rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (Measure.le_iff.1 (s82q_nu_le q hW.short.nonneg mu beta hbeta N _) s hs) bot_le)
  -- the profile B
  set B : Euc d → ℝ := fun z => ((m + 1 : ℕ) : ℝ) * (Cm * A * (Pw * jbracket z ^ M *
    (Pw + jbracket z ^ M) * pole x z) * (L / N)) with hBdef
  have hB0 : ∀ z, 0 ≤ B z := fun z => by
    have := s82q_jb_rpow_nonneg M z
    have := s82q_pole_ge_one x z
    have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
    simp only [hBdef]
    positivity
  have hBm : Measurable B := by
    simp only [hBdef]
    exact measurable_const.mul ((measurable_const.mul (((measurable_const.mul (s82q_measurable_jb M)).mul
      (measurable_const.add (s82q_measurable_jb M))).mul (s82q_measurable_pole x))).mul measurable_const)
  -- lintegral of B against mu
  have hjj : ∀ z : Euc d, jbracket z ^ M * jbracket z ^ M = jbracket z ^ (2 * M) := fun z => by
    rw [← Real.rpow_add (HRS.MS.S82N.s82n_jb_pos z)]; congr 1; ring
  have hP23 : jbracket x ^ (2 * M) * Pw = jbracket x ^ (3 * M) := by
    rw [hPw, ← Real.rpow_add (HRS.MS.S82N.s82n_jb_pos x)]; congr 1; ring
  have hBint_mu : ∫⁻ z, ENNReal.ofReal (B z) ∂mu ≤ ENNReal.ofReal
      (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) * ((Cp1 + Cp2) * jbracket x ^ (3 * M))) := by
    have hcc : 0 ≤ ((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) := by
      have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
      positivity
    have hr1 := hpole1 rho hρ hρG x
    have hr2 := hpole2 rho hρ hρG x
    have g1 : ∫⁻ z, ENNReal.ofReal (jbracket x ^ (2 * M) * (jbracket z ^ M * pole x z)) ∂mu ≤
        ENNReal.ofReal (jbracket x ^ (2 * M) * (Cp1 * Pw)) := by
      refine (s82q_lint_scale mu _ (fun z => jbracket z ^ M * pole x z) _
        (s82q_jb_rpow_nonneg _ x) (ae_of_all _ fun z => le_refl _)).trans ?_
      rw [ENNReal.ofReal_mul (s82q_jb_rpow_nonneg _ x)]
      exact mul_le_mul_of_nonneg_left hr1 bot_le
    have g2 : ∫⁻ z, ENNReal.ofReal (Pw * (jbracket z ^ (2 * M) * pole x z)) ∂mu ≤
        ENNReal.ofReal (Pw * (Cp2 * jbracket x ^ (2 * M))) := by
      refine (s82q_lint_scale mu _ (fun z => jbracket z ^ (2 * M) * pole x z) _
        (s82q_jb_rpow_nonneg _ x) (ae_of_all _ fun z => le_refl _)).trans ?_
      rw [ENNReal.ofReal_mul (s82q_jb_rpow_nonneg _ x)]
      exact mul_le_mul_of_nonneg_left hr2 bot_le
    refine le_trans (s82q_split2 mu B (fun z => jbracket x ^ (2 * M) * (jbracket z ^ M * pole x z))
      (fun z => Pw * (jbracket z ^ (2 * M) * pole x z)) _ hcc
      (measurable_const.mul ((s82q_measurable_jb M).mul (s82q_measurable_pole x)))
      (measurable_const.mul ((s82q_measurable_jb (2 * M)).mul (s82q_measurable_pole x)))
      (fun z => mul_nonneg (s82q_jb_rpow_nonneg _ x) (mul_nonneg (s82q_jb_rpow_nonneg _ z)
        (by linarith [s82q_pole_ge_one x z])))
      (fun z => mul_nonneg (by linarith) (mul_nonneg (s82q_jb_rpow_nonneg _ z)
        (by linarith [s82q_pole_ge_one x z])))
      (ae_of_all _ fun z => ?_) _ _ (mul_nonneg (s82q_jb_rpow_nonneg _ x) (mul_nonneg hCp1 (by linarith)))
      (mul_nonneg (by linarith) (mul_nonneg hCp2 (s82q_jb_rpow_nonneg _ x))) g1 g2) (le_of_eq ?_)
    · simp only [hBdef]
      have hz := hjj z
      have e : jbracket x ^ (2 * M) = Pw * Pw := by
        rw [hPw, ← Real.rpow_add (HRS.MS.S82N.s82n_jb_pos x)]; congr 1; ring
      rw [e, ← hz]
      apply le_of_eq
      ring
    · congr 1
      rw [← hP23]
      ring
  have hnn : 0 ≤ C0 * (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) * ((Cp1 + Cp2) *
      jbracket x ^ (3 * M))) := by
    have : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
    have := s82q_jb_rpow_nonneg (3 * M) x
    have := add_nonneg hCp1 hCp2
    positivity
  have hper : ∀ i : Fin (m + 2), |∫ Y, s82q_prow Kx i Y ∂ref1| ≤
      C0 * (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) * ((Cp1 + Cp2) * jbracket x ^ (3 * M))) := by
    intro i
    have hprow_m : Measurable (s82q_prow Kx i) := s82q_prow_measurable hKxm i
    rw [s82q_disint_integral hW.short.measurable hW.short.even beta N (hW.hmeas N) pins1 i h1 h0
      _ hprow_m (hint_i i)]
    simp_rw [s82q_prow_insertNth]
    have hac := Measure.absolutelyContinuous_of_le_smul (hmarg_dom i)
    have hae : ∀ᵐ z ∂(ref1.map (fun Y => Y i)),
        ‖∫ X', ∑ j, Kx z (X' j) ∂referenceLaw q h mu beta N (m + 1)
          (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)‖ ≤ B z := by
      filter_upwards [hac.ae_le (s82q_ae_ne hd rho x)] with z hz
      have hxz : x ≠ z := Ne.symm hz
      have hψi : Integrable (Gt x z) mu := (hGc.2 x z hxz).1
      have hjint : ∀ j : Fin (m + 1), Integrable (fun X' : Fin (m + 1) → Euc d => Gt x z (X' j))
          (referenceLaw q h mu beta N (m + 1) (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)) := by
        intro j
        have h2 : Integrable (Gt x z) ((referenceLaw q h mu beta N (m + 1)
            (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)).map (fun X => X j)) :=
          (hψi.smul_measure ENNReal.ofReal_ne_top).mono_measure (hmarg_dom2 z j)
        exact (integrable_map_measure (hψm z).aestronglyMeasurable
          (measurable_pi_apply j).aemeasurable).1 h2
      rw [Real.norm_eq_abs]
      show |∫ X' : Fin (m + 1) → Euc d, ∑ j, Gt x z (X' j) ∂(referenceLaw q h mu beta N (m + 1)
        (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d))| ≤ B z
      rw [integral_finset_sum _ (fun j _ => hjint j)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hj : ∀ j : Fin (m + 1), |∫ X', Gt x z (X' j) ∂referenceLaw q h mu beta N (m + 1)
          (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)| ≤
          Cm * A * jbracket x ^ M * jbracket z ^ M * (jbracket x ^ M + jbracket z ^ M) *
            pole x z * (logN (m + 3) / ((m + 3 : ℕ) : ℝ)) := fun j => by
        rw [← integral_map (measurable_pi_apply j).aemeasurable (hψm z).aestronglyMeasurable]
        exact hmean h hW hP A hA Gt hGm hGc hGb m x z hxz j
      calc ∑ j : Fin (m + 1), |∫ X', Gt x z (X' j) ∂referenceLaw q h mu beta N (m + 1)
            (Fin.cons z pins1 : Fin (0 + 1 + 1) → Euc d)|
          ≤ ∑ j : Fin (m + 1), (Cm * A * jbracket x ^ M * jbracket z ^ M *
            (jbracket x ^ M + jbracket z ^ M) * pole x z * (logN (m + 3) / ((m + 3 : ℕ) : ℝ))) :=
            Finset.sum_le_sum fun j _ => hj j
        _ = B z := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            simp only [hBdef, hPw, hL, hNdef]
            ring
    have hBlint : ∫⁻ z, ENNReal.ofReal (B z) ∂(ref1.map (fun Y => Y i)) ≤ ENNReal.ofReal
        (C0 * (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) * ((Cp1 + Cp2) * jbracket x ^ (3 * M)))) := by
      calc ∫⁻ z, ENNReal.ofReal (B z) ∂(ref1.map (fun Y => Y i))
          ≤ ∫⁻ z, ENNReal.ofReal (B z) ∂(ENNReal.ofReal C0 • mu) :=
            lintegral_mono' (hmarg_dom i) le_rfl
        _ = ENNReal.ofReal C0 * ∫⁻ z, ENNReal.ofReal (B z) ∂mu := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) *
              ((Cp1 + Cp2) * jbracket x ^ (3 * M))) := mul_le_mul_of_nonneg_left hBint_mu bot_le
        _ = _ := (ENNReal.ofReal_mul hC0.le).symm
    have hBint : Integrable B (ref1.map (fun Y => Y i)) :=
      ⟨hBm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hB0)).2
        (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBlint))⟩
    have hnorm := norm_integral_le_of_norm_le hBint hae
    rw [Real.norm_eq_abs] at hnorm
    refine hnorm.trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hB0) hBm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hnn hBlint
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hper i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) ^ 2 := by
    rw [hNdef]; push_cast; nlinarith
  have hLN0 : 0 ≤ L / N := div_nonneg (by linarith) hNr.le
  have key : ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (L / N) ≤ N * L := by
    calc ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (L / N) ≤ ((N : ℕ) : ℝ) ^ 2 * (L / N) :=
          mul_le_mul_of_nonneg_right hm hLN0
      _ = N * L := by field_simp
  have hP3 := s82q_jb_rpow_nonneg (3 * M) x
  have hCC := add_nonneg hCp1 hCp2
  calc ((m + 2 : ℕ) : ℝ) * (C0 * (((m + 1 : ℕ) : ℝ) * (Cm * A * (L / N)) *
        ((Cp1 + Cp2) * jbracket x ^ (3 * M))))
      = (C0 * Cm * A * (Cp1 + Cp2) * jbracket x ^ (3 * M)) *
          (((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (L / N)) := by ring
    _ ≤ (C0 * Cm * A * (Cp1 + Cp2) * jbracket x ^ (3 * M)) * (N * L) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by rw [abs_of_pos hC0]; ring

end HRS.MS.S82Q
