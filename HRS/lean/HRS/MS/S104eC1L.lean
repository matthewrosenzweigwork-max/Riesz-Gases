import HRS.MS.S104eC1I

/-!
# S104E route C, packet C1 (part L): uniform strong continuity in `h` on `[0,H]` (`VolHyp.P_strong`, two-point form)

`s104c1_close2`: for `φ` continuous, bounded, vanishing at infinity, the Gaussian averages `G_{c,s} φ` are uniformly
close for nearby parameters `(c,s)`, `(c',s')` in `[c_min,∞) × [0,s_max]`.
`c1_P_strong`: `sup_x ‖D^i P_h f - D^i P_{h'} f‖ ≤ ε` for `|h-h'| < δ`, `h,h' ∈ [0,H]`, `f ∈ Bd (j+1)` with vanishing jets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Wad
variable {d : ℕ}

set_option maxHeartbeats 2000000 in
theorem s104c1_close2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Euc d → F} (hφ : Continuous φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (hv : Tendsto (fun y => ‖φ y‖) (cocompact (Euc d)) (𝓝 0)) {cmin smax : ℝ} (hcmin : 0 < cmin)
    (hsmax : 0 ≤ smax) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c s c' s' : ℝ, cmin ≤ c → cmin ≤ c' → 0 ≤ s → s ≤ smax → 0 ≤ s' → s' ≤ smax →
      |c - c'| < δ → |s - s'| < δ → ∀ x : Euc d,
      ‖(∫ z, φ (c • x + s • z) ∂(stdGaussian (Euc d))) - ∫ z, φ (c' • x + s' • z) ∂(stdGaussian (Euc d))‖
        ≤ ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ε₁ : ℝ := ε / 4 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨R, hR0, hR⟩ := s104c1_cocompact_small hv hε₁0
  have hU : UniformContinuous φ :=
    hφ.uniformContinuous_of_tendsto_cocompact (tendsto_zero_iff_norm_tendsto_zero.2 hv)
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuous_iff.1 hU ε₁ hε₁0
  set m1 : ℝ := ∫ z : Euc d, ‖z‖ ∂(stdGaussian (Euc d)) with hm1
  have hm10 : 0 ≤ m1 := integral_nonneg fun _ => norm_nonneg _
  set Z : ℝ := 8 * (M * m1 + 1) / ε with hZ
  have hZ0 : 0 < Z := by positivity
  set R₂ : ℝ := (R + smax * Z + 1) / cmin with hR₂
  have hR₂0 : 0 < R₂ := by positivity
  set δ : ℝ := η / (R₂ + Z + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, fun c s c' s' hc hc' hs hs1 hs' hs1' hcc hss x => ?_⟩
  have hpt : ∀ z : Euc d, ‖φ (c • x + s • z) - φ (c' • x + s' • z)‖ ≤ 2 * ε₁ + (2 * M / Z) * ‖z‖ := by
    intro z
    have hlin : 0 ≤ (2 * M / Z) * ‖z‖ := mul_nonneg (div_nonneg (by linarith) hZ0.le) (norm_nonneg _)
    by_cases hz : ‖z‖ ≤ Z
    · by_cases hx : ‖x‖ ≤ R₂
      · have hd : dist (c • x + s • z) (c' • x + s' • z) < η := by
          rw [dist_eq_norm]
          have e : c • x + s • z - (c' • x + s' • z) = (c - c') • x + (s - s') • z := by
            rw [sub_smul, sub_smul]; abel
          rw [e]
          refine (norm_add_le _ _).trans_lt ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          have h1 : |c - c'| * ‖x‖ ≤ δ * R₂ :=
            mul_le_mul hcc.le hx (norm_nonneg _) hδ0.le
          have h2 : |s - s'| * ‖z‖ ≤ δ * Z :=
            mul_le_mul hss.le hz (norm_nonneg _) hδ0.le
          have h3 : δ * R₂ + δ * Z < η := by
            have : δ * (R₂ + Z) = η * ((R₂ + Z) / (R₂ + Z + 1)) := by
              rw [hδ]; field_simp
            have h4 : (R₂ + Z) / (R₂ + Z + 1) < 1 := by
              rw [div_lt_one (by positivity)]; linarith
            nlinarith
          linarith
        have := hη hd
        rw [dist_eq_norm] at this
        linarith
      · push Not at hx
        have hxR : R₂ * cmin = R + smax * Z + 1 := by rw [hR₂]; field_simp
        have hbig : ∀ (c₀ s₀ : ℝ), cmin ≤ c₀ → 0 ≤ s₀ → s₀ ≤ smax → R < ‖c₀ • x + s₀ • z‖ := by
          intro c₀ s₀ hc₀ hs₀ hs₀1
          have h1 : ‖c₀ • x‖ ≤ ‖c₀ • x + s₀ • z‖ + ‖s₀ • z‖ := by
            calc ‖c₀ • x‖ = ‖(c₀ • x + s₀ • z) - s₀ • z‖ := by rw [add_sub_cancel_right]
              _ ≤ _ := norm_sub_le _ _
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < c₀)] at h1
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₀] at h1
          have h2 : cmin * ‖x‖ ≤ c₀ * ‖x‖ := mul_le_mul_of_nonneg_right hc₀ (norm_nonneg _)
          have h3 : cmin * R₂ < cmin * ‖x‖ := mul_lt_mul_of_pos_left hx hcmin
          have h4 : s₀ * ‖z‖ ≤ smax * Z := mul_le_mul hs₀1 hz (norm_nonneg _) hsmax
          nlinarith
        have h1 := hR _ (hbig c s hc hs hs1)
        have h2 := hR _ (hbig c' s' hc' hs' hs1')
        calc ‖φ (c • x + s • z) - φ (c' • x + s' • z)‖ ≤ ‖φ (c • x + s • z)‖ + ‖φ (c' • x + s' • z)‖ :=
              norm_sub_le _ _
          _ ≤ ε₁ + ε₁ := add_le_add h1 h2
          _ ≤ _ := by linarith
    · push Not at hz
      have h1 : ‖φ (c • x + s • z) - φ (c' • x + s' • z)‖ ≤ 2 * M :=
        (norm_sub_le _ _).trans (by linarith [hM (c • x + s • z), hM (c' • x + s' • z)])
      have h2 : 2 * M ≤ (2 * M / Z) * ‖z‖ := by
        calc 2 * M = (2 * M / Z) * Z := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hz.le (div_nonneg (by linarith) hZ0.le)
      linarith
  have hint : ∀ (c₀ s₀ : ℝ), Integrable (fun z : Euc d => φ (c₀ • x + s₀ • z)) (stdGaussian (Euc d)) :=
    fun c₀ s₀ => Integrable.of_bound (C := M) (hφ.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hM _)
  rw [← integral_sub (hint c s) (hint c' s')]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hrhs : Integrable (fun z : Euc d => 2 * ε₁ + (2 * M / Z) * ‖z‖) (stdGaussian (Euc d)) :=
    (integrable_const _).add (s104c1_int_norm.const_mul _)
  have hlhs : Integrable (fun z : Euc d => ‖φ (c • x + s • z) - φ (c' • x + s' • z)‖)
      (stdGaussian (Euc d)) := ((hint c s).sub (hint c' s')).norm
  refine (integral_mono hlhs hrhs hpt).trans ?_
  rw [integral_add (integrable_const _) (s104c1_int_norm.const_mul _), integral_const, integral_const_mul]
  have hu1 : (stdGaussian (Euc d)).real univ = 1 := by simp [Measure.real]
  rw [hu1, one_smul, ← hm1]
  have key : (2 * M / Z) * m1 ≤ ε / 4 := by
    calc (2 * M / Z) * m1 = (ε / 4) * ((M * m1) / (M * m1 + 1)) := by rw [hZ]; field_simp; ring
      _ ≤ (ε / 4) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (div_le_one (by positivity)).2 (by linarith)
      _ = ε / 4 := mul_one _
  linarith

theorem s104c1_exp_lip {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : |Real.exp x - Real.exp y| ≤ |x - y| := by
  have key : ∀ x y : ℝ, x ≤ y → y ≤ 0 → Real.exp y - Real.exp x ≤ y - x := by
    intro x y hxy hy
    have h1 := Real.add_one_le_exp (x - y)
    have h2 : Real.exp x = Real.exp (x - y) * Real.exp y := by rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp y ≤ 1 := by rw [Real.exp_le_one_iff]; exact hy
    have h4 := Real.exp_pos y
    have h5 : Real.exp y * (x - y + 1) ≤ Real.exp x := by rw [h2]; nlinarith
    nlinarith
  rcases le_total x y with h | h
  · have h1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.2 h
    rw [abs_of_nonpos (by linarith : Real.exp x - Real.exp y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    have := key x y h hy; linarith
  · have h1 : Real.exp y ≤ Real.exp x := Real.exp_le_exp.2 h
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp x - Real.exp y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    have := key y x h hx; linarith

theorem s104c1_pow_lip {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ n * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg (pow_nonneg hy0 n)]
    have h1 : x * |x ^ n - y ^ n| ≤ n * |x - y| :=
      calc x * |x ^ n - y ^ n| ≤ 1 * |x ^ n - y ^ n| := mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact ih
    have h2 : |x - y| * y ^ n ≤ |x - y| := by
      calc |x - y| * y ^ n ≤ |x - y| * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hy0 hy1) (abs_nonneg _)
        _ = _ := mul_one _
    push_cast
    linarith

theorem s104c1_strong2_i {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) (H : ℝ) {N : ℕ} {B : ℝ} {f : Euc d → ℝ}
    (hf : Bd N B f) (hv : VanB N f) {i : ℕ} (hi : i ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc (0 : ℝ) H, ∀ h' ∈ Icc (0 : ℝ) H, |h - h'| < δ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h' f) x‖ ≤ ε := by
  have hφc : Continuous (iteratedFDeriv ℝ i f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hB : 0 ≤ B := hf.nonneg
  obtain ⟨δ1, hδ1, hclose⟩ := s104c1_close2 hφc (fun y => hf.2 i hi y) (hv i hi)
    (cmin := Real.exp (-a * H)) (smax := Real.sqrt (ν / a)) (Real.exp_pos _) (Real.sqrt_nonneg _)
    (half_pos hε)
  obtain ⟨δ2, hδ2, hms⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (s104c1_ms_cont a ν).continuousOn) δ1 hδ1
  refine ⟨min (min (δ1 / a) δ2) (ε / (2 * (N + 1) * (a + 1) * (B + 1))), by positivity, ?_⟩
  intro h hh h' hh' hdist x
  have h1 : |h - h'| < δ1 / a := hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : |h - h'| < δ2 := hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : |h - h'| < ε / (2 * (N + 1) * (a + 1) * (B + 1)) := hdist.trans_le (min_le_right _ _)
  set c : ℝ := Real.exp (-a * h) with hc
  set c' : ℝ := Real.exp (-a * h') with hc'
  set s : ℝ := s83_ms a ν h with hs
  set s' : ℝ := s83_ms a ν h' with hs'
  have hcpos : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := by rw [hc, Real.exp_le_one_iff]; nlinarith [hh.1]
  have hc'1 : c' ≤ 1 := by rw [hc', Real.exp_le_one_iff]; nlinarith [hh'.1]
  have hcmin : Real.exp (-a * H) ≤ c := Real.exp_le_exp.2 (by nlinarith [hh.2])
  have hcmin' : Real.exp (-a * H) ≤ c' := Real.exp_le_exp.2 (by nlinarith [hh'.2])
  have hcc : |c - c'| ≤ a * |h - h'| := by
    have := s104c1_exp_lip (x := -a * h) (y := -a * h') (by nlinarith [hh.1]) (by nlinarith [hh'.1])
    rw [show -a * h - -a * h' = -a * (h - h') by ring, abs_mul, abs_neg, abs_of_pos ha] at this
    exact this
  have hcc1 : |c - c'| < δ1 := by
    have : a * |h - h'| < δ1 := by rwa [lt_div_iff₀ ha, mul_comm] at h1
    linarith
  have hss : |s - s'| < δ1 := by
    have := hms h hh h' hh' (by rw [Real.dist_eq]; exact h2)
    rwa [Real.dist_eq] at this
  have hs0 : 0 ≤ s := s83_ms_nonneg _ _ _
  have hs'0 : 0 ≤ s' := s83_ms_nonneg _ _ _
  have hI := hclose c s c' s' hcmin hcmin' hs0 (s83_ms_le ha hν.le hh.1) hs'0 (s83_ms_le ha hν.le hh'.1)
    hcc1 hss x
  rw [s104c1_Drep ha hν.le hf hh.1 hi x, s104c1_Drep ha hν.le hf hh'.1 hi x]
  set I := ∫ z, iteratedFDeriv ℝ i f (c • x + s • z) ∂(stdGaussian (Euc d)) with hI1
  set I' := ∫ z, iteratedFDeriv ℝ i f (c' • x + s' • z) ∂(stdGaussian (Euc d)) with hI2
  have e : c ^ i • I - c' ^ i • I' = c ^ i • (I - I') + (c ^ i - c' ^ i) • I' := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hcpos i)]
  have hpow1 : c ^ i ≤ 1 := pow_le_one₀ hcpos.le hc1
  have t1 : c ^ i * ‖I - I'‖ ≤ ε / 2 :=
    calc c ^ i * ‖I - I'‖ ≤ 1 * (ε / 2) := mul_le_mul hpow1 hI (norm_nonneg _) zero_le_one
      _ = ε / 2 := one_mul _
  have hI'B : ‖I'‖ ≤ B := by
    refine (norm_integral_le_of_norm_le_const (C := B) (Filter.Eventually.of_forall fun z => hf.2 i hi _)).trans ?_
    simp
  have t2 : |c ^ i - c' ^ i| * ‖I'‖ ≤ ε / 2 := by
    have h4 : |c ^ i - c' ^ i| ≤ i * (a * |h - h'|) :=
      (s104c1_pow_lip hcpos.le hc1 (Real.exp_pos _).le hc'1 i).trans
        (mul_le_mul_of_nonneg_left hcc (Nat.cast_nonneg _))
    have h5 : |h - h'| * (2 * (N + 1) * (a + 1) * (B + 1)) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at h3
    have hi1 : (i : ℝ) ≤ N := by exact_mod_cast hi
    have e2 : (i : ℝ) * a * B ≤ ((N : ℝ) + 1) * (a + 1) * (B + 1) := by
      have e1 : (i : ℝ) ≤ N + 1 := by linarith
      have e2 : a ≤ a + 1 := by linarith
      have e3 : B ≤ B + 1 := by linarith
      exact mul_le_mul (mul_le_mul e1 e2 ha.le (by positivity)) e3 hB (by positivity)
    have hd0 : 0 ≤ |h - h'| := abs_nonneg _
    calc |c ^ i - c' ^ i| * ‖I'‖ ≤ (i * (a * |h - h'|)) * B :=
          mul_le_mul h4 hI'B (norm_nonneg _) (by positivity)
      _ = |h - h'| * ((i : ℝ) * a * B) := by ring
      _ ≤ |h - h'| * (((N : ℝ) + 1) * (a + 1) * (B + 1)) := mul_le_mul_of_nonneg_left e2 hd0
      _ ≤ ε / 2 := by nlinarith
  linarith

theorem c1_P_strong (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) (H : ℝ) {N : ℕ} {B : ℝ} {f : Euc d → ℝ}
    (hf : Bd N B f) (hv : VanB N f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc (0 : ℝ) H, ∀ h' ∈ Icc (0 : ℝ) H, |h - h'| < δ → ∀ i ≤ N, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h' f) x‖ ≤ ε := by
  have hex : ∀ i : ℕ, ∃ δ : ℝ, 0 < δ ∧ (i ≤ N → ∀ h ∈ Icc (0 : ℝ) H, ∀ h' ∈ Icc (0 : ℝ) H, |h - h'| < δ →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x -
        iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h' f) x‖ ≤ ε) := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨δ, hδ, hh⟩ := s104c1_strong2_i ha hν H hf hv hi hε
      exact ⟨δ, hδ, fun _ => hh⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose δ hδ0 hδ using hex
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, by simp⟩ δ, ?_, fun h hh h' hh' hlt i hi x => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hδ0 i
  · exact hδ i hi h hh h' hh' (hlt.trans_le (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))) x

end HRS.MS.S104e.C
