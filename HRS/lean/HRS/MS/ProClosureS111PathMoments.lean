import HRS.MP.KolmChentsov

/-!
Quantitative path-norm control for the exact continuous modification used
by the physical shared Gaussian law. The dyadic increment bound is retained
as a random variable, so its L4 norm controls the full observation-path norm.
This is an auxiliary analytic lift. The physical all-start dyadic moment
bound is not assumed to have been constructed by this module.
-/

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.ProClosureS111
open HRS.MP.KC HRS.Whole.AppendixALemmas

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
variable {Omega : Type*} [MeasurableSpace Omega]

/-- An explicit norm bound for the constructed path, on each dyadic-good
event. The initial observation is retained, including the endpoint zero. -/
theorem continuous_modification_norm_le
    (X : ℝ → Omega → E) {T r lam : ℝ}
    (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) (hlam : 0 ≤ lam)
    {w : Omega} (hw : w ∈ mkc_G X T r lam) :
    ‖contPathOf T (fun t => mkc_Zc X T r t w)‖ ≤
      ‖X 0 w‖ + mkc_c r * lam := by
  have hc : 0 ≤ mkc_c r := by
    unfold mkc_c
    positivity
  have hz0 : mkc_Zc X T r 0 w = X 0 w := by
    have hconv := mkc_Zc_tendsto X T r hT hr0 hr1 hlam hw
      (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT.le⟩)
    have hconst : Tendsto (fun _ : ℕ => X 0 w) atTop
        (𝓝 (mkc_Zc X T r 0 w)) := by
      simpa only [mkc_pt, mkc_idx, zero_mul, zero_div, Nat.floor_zero,
        Nat.cast_zero, mul_zero, div_zero] using hconv
    exact tendsto_nhds_unique hconst tendsto_const_nhds
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg hc hlam))).2
  intro t
  rw [mkc_contPathOf_apply X hT hr0 hr1 w t]
  have hdiff := mkc_Zc_dist_le X T r hT hr0 hr1 hlam hw t.property
    (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT.le⟩) 0
    (by simpa only [sub_zero, abs_of_nonneg t.property.1, pow_zero, div_one]
        using t.property.2)
  simp only [pow_zero, mul_one, hz0] at hdiff
  calc
    ‖mkc_Zc X T r t w‖ = ‖(mkc_Zc X T r t w - X 0 w) + X 0 w‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖mkc_Zc X T r t w - X 0 w‖ + ‖X 0 w‖ := norm_add_le _ _
    _ ≤ mkc_c r * lam + ‖X 0 w‖ := add_le_add hdiff le_rfl
    _ = ‖X 0 w‖ + mkc_c r * lam := add_comm _ _

/-- L4 control of the continuous modification follows from an L4 dyadic
envelope and the actual initial observation. Unlike a tail bound with
exponent four, this hypothesis retains the endpoint L4 integrability. -/
theorem continuous_modification_memLp_four
    (P : Measure Omega) (X : ℝ → Omega → E) {T r : ℝ}
    (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hX : ∀ t, Measurable (X t)) (hX0 : MemLp (X 0) 4 P)
    (lam : Omega → ℝ) (hlam : MemLp lam 4 P)
    (hnonneg : ∀ᵐ w ∂P, 0 ≤ lam w)
    (hgood : ∀ᵐ w ∂P, w ∈ mkc_G X T r (lam w)) :
    MemLp (fun w => contPathOf T (fun t => mkc_Zc X T r t w)) 4 P := by
  have hm : Measurable (fun w => contPathOf T (fun t => mkc_Zc X T r t w)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    have he : (fun w => contPathOf T (fun q => mkc_Zc X T r q w) t) =
        fun w => mkc_Zc X T r t w := by
      funext w
      exact mkc_contPathOf_apply X hT hr0 hr1 w t
    rw [he]
    exact mkc_Zc_meas X T r hT hr0 hr1 hX t
  have hb : MemLp (fun w => ‖X 0 w‖ + mkc_c r * lam w) 4 P :=
    hX0.norm.add (hlam.const_mul (mkc_c r))
  refine hb.mono' hm.aestronglyMeasurable ?_
  filter_upwards [hnonneg, hgood] with w hw hgw
  exact continuous_modification_norm_le X hT hr0 hr1 hw hgw

/-- A countable family with summable fourth moments has one L4 envelope.
The envelope is constructed as the fourth root of the pointwise sum of
fourth powers. The simultaneous domination has one common full-measure set. -/
theorem exists_fourth_moment_envelope_with_integral
    {J : Type*} [Countable J] (P : Measure Omega)
    (f : J → Omega → ℝ) (hf : ∀ j, Measurable (f j))
    (henergy : (∑' j, ∫⁻ w, ENNReal.ofReal (|f j w| ^ 4) ∂P) < ⊤) :
    ∃ lam : Omega → ℝ, (∀ w, 0 ≤ lam w) ∧ MemLp lam 4 P ∧
      (∀ᵐ w ∂P, ∀ j, |f j w| ≤ lam w) ∧
      (∫⁻ w, ENNReal.ofReal (lam w ^ 4) ∂P) =
        ∑' j, ∫⁻ w, ENNReal.ofReal (|f j w| ^ 4) ∂P := by
  let S : Omega → ℝ≥0∞ := fun w => ∑' j, ENNReal.ofReal (|f j w| ^ 4)
  have hterm : ∀ j, AEMeasurable (fun w => ENNReal.ofReal (|f j w| ^ 4)) P :=
    fun j => ((hf j).abs.pow_const 4).aemeasurable.ennreal_ofReal
  have hSm : AEMeasurable S P := AEMeasurable.ennreal_tsum hterm
  have hSint : (∫⁻ w, S w ∂P) < ⊤ := by
    dsimp only [S]
    rw [lintegral_tsum hterm]
    exact henergy
  have hSfinite : ∀ᵐ w ∂P, S w ≠ ⊤ :=
    (ae_lt_top' hSm hSint.ne).mono fun _ hw => hw.ne
  let lam : Omega → ℝ := fun w => (S w).toReal ^ (1 / 4 : ℝ)
  have hlam0 : ∀ w, 0 ≤ lam w := fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hlam4 : ∀ w, lam w ^ 4 = (S w).toReal := by
    intro w
    dsimp only [lam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  have hlamm : AEStronglyMeasurable lam P :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp_aestronglyMeasurable
      hSm.ennreal_toReal.aestronglyMeasurable
  have hnorm : ∀ᵐ w ∂P, ‖lam w‖ₑ ^ (4 : ℝ) = S w := by
    filter_upwards [hSfinite] with w hw
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hlam0 w)]
    exact (ENNReal.rpow_natCast _ 4).trans
      ((ENNReal.ofReal_pow (hlam0 w) 4).symm.trans
        (by rw [hlam4, ENNReal.ofReal_toReal hw]))
  have hlamLp : MemLp lam 4 P := by
    change eLpNorm lam 4 P < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hlamm).2
    have hi : (∫⁻ w, ‖lam w‖ₑ ^ (4 : ℝ) ∂P) < ⊤ := by
      rw [lintegral_congr_ae hnorm]
      exact hSint
    simpa only [ENNReal.toReal_ofNat] using hi
  refine ⟨lam, hlam0, hlamLp, ?_, ?_⟩
  · filter_upwards [hSfinite] with w hw j
    have hterm_le : ENNReal.ofReal (|f j w| ^ 4) ≤ S w := by
      change ENNReal.ofReal (|f j w| ^ 4) ≤ ∑' i, ENNReal.ofReal (|f i w| ^ 4)
      exact ENNReal.le_tsum (f := fun i => ENNReal.ofReal (|f i w| ^ 4)) j
    have hp : |f j w| ^ 4 ≤ lam w ^ 4 := by
      rw [hlam4]
      exact (ENNReal.ofReal_le_iff_le_toReal hw).1 hterm_le
    apply (sq_le_sq₀ (abs_nonneg _) (hlam0 w)).1
    apply (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).1
    convert hp using 1 <;> ring
  · have he : ∀ᵐ w ∂P, ENNReal.ofReal (lam w ^ 4) = S w := by
      filter_upwards [hSfinite] with w hw
      rw [hlam4, ENNReal.ofReal_toReal hw]
    rw [lintegral_congr_ae he]
    exact lintegral_tsum hterm

/-- The original qualitative envelope conclusion. -/
theorem exists_fourth_moment_envelope
    {J : Type*} [Countable J] (P : Measure Omega)
    (f : J → Omega → ℝ) (hf : ∀ j, Measurable (f j))
    (henergy : (∑' j, ∫⁻ w, ENNReal.ofReal (|f j w| ^ 4) ∂P) < ⊤) :
    ∃ lam : Omega → ℝ, (∀ w, 0 ≤ lam w) ∧ MemLp lam 4 P ∧
      ∀ᵐ w ∂P, ∀ j, |f j w| ≤ lam w := by
  obtain ⟨lam, hlam0, hlam, hbound, _⟩ :=
    exists_fourth_moment_envelope_with_integral P f hf henergy
  exact ⟨lam, hlam0, hlam, hbound⟩

/-- Finite summed fourth moment of the scaled dyadic edges suffices for
L4 integrability of the exact continuous modification. -/
theorem continuous_modification_memLp_four_of_increment_energy
    (P : Measure Omega) (X : ℝ → Omega → E) {T r : ℝ}
    (hT : 0 < T) (hr0 : 0 < r) (hr1 : r < 1)
    (hX : ∀ t, Measurable (X t)) (hX0 : MemLp (X 0) 4 P)
    (henergy : (∑' j : (Σ n : ℕ, Fin (2 ^ n)),
      ∫⁻ w, ENNReal.ofReal
        ((‖X (mkc_pt T j.1 ((j.2 : ℕ) + 1)) w - X (mkc_pt T j.1 (j.2 : ℕ)) w‖ / r ^ j.1) ^ 4) ∂P) < ⊤) :
    MemLp (fun w => contPathOf T (fun t => mkc_Zc X T r t w)) 4 P := by
  let f : (Σ n : ℕ, Fin (2 ^ n)) → Omega → ℝ := fun j w =>
    ‖X (mkc_pt T j.1 ((j.2 : ℕ) + 1)) w - X (mkc_pt T j.1 (j.2 : ℕ)) w‖ / r ^ j.1
  have hf : ∀ j, Measurable (f j) := fun j =>
    ((hX _).sub (hX _)).norm.div_const _
  have hf0 : ∀ j w, 0 ≤ f j w := fun _ _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
  obtain ⟨lam, hlam0, hlam, hbound⟩ := exists_fourth_moment_envelope P f hf
    (by simpa only [abs_of_nonneg (hf0 _ _)] using henergy)
  apply continuous_modification_memLp_four P X hT hr0.le hr1 hX hX0 lam hlam
    (ae_of_all _ hlam0)
  filter_upwards [hbound] with w hw
  intro n k hk
  have hb := hw (⟨n, ⟨k, hk⟩⟩ : (Σ n : ℕ, Fin (2 ^ n)))
  rw [abs_of_nonneg (hf0 _ _)] at hb
  exact (div_le_iff₀ (pow_pos hr0 n)).1 hb

/-- The fourth-increment estimate used by the physical Gaussian path
construction gives a finite fourth-moment dyadic envelope. The strict
condition on r is precisely the convergence of the geometric series. -/
theorem fourth_increment_energy_bound
    (P : Measure Omega) (X : ℝ → Omega → E) {T r C : ℝ}
    (hT : 0 < T) (hr0 : 0 < r) (hC : 0 ≤ C) (hr : 1 < 2 * r ^ 4)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    (∑' j : (Σ n : ℕ, Fin (2 ^ n)),
      ∫⁻ w, ENNReal.ofReal
        ((‖X (mkc_pt T j.1 ((j.2 : ℕ) + 1)) w -
          X (mkc_pt T j.1 (j.2 : ℕ)) w‖ / r ^ j.1) ^ 4) ∂P) ≤ ENNReal.ofReal (C * T ^ 2 / (1 - 1 / (2 * r ^ 4))) := by
  let q : ℝ := 1 / (2 * r ^ 4)
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (div_lt_one (by positivity)).2 hr
  have hsum : Summable (fun n : ℕ => C * T ^ 2 * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (C * T ^ 2)
  have hsingle : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      (∫⁻ w, ENNReal.ofReal
        ((‖X (mkc_pt T n ((k : ℕ) + 1)) w - X (mkc_pt T n k) w‖ / r ^ n) ^ 4) ∂P) ≤
      ENNReal.ofReal (C * (T / (2 : ℝ) ^ n) ^ 2 / (r ^ n) ^ 4) := by
    intro n k
    let W : ℝ := 1 / (r ^ n) ^ 4
    have hW : 0 ≤ W := by dsimp only [W]; positivity
    have he : (fun w => ENNReal.ofReal
        ((‖X (mkc_pt T n ((k : ℕ) + 1)) w - X (mkc_pt T n k) w‖ / r ^ n) ^ 4)) =
        fun w => ENNReal.ofReal W * ENNReal.ofReal
          (‖X (mkc_pt T n ((k : ℕ) + 1)) w - X (mkc_pt T n k) w‖ ^ 4) := by
      funext w
      rw [← ENNReal.ofReal_mul hW]
      congr 1
      dsimp only [W]
      rw [div_pow]
      ring
    rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hbase := hmom _ (mkc_pt_mem hT n k k.isLt.le)
      _ (mkc_pt_mem hT n ((k : ℕ) + 1) k.isLt)
    rw [mkc_pt_succ_sub, abs_of_pos (by positivity)] at hbase
    calc
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal (C * (T / (2 : ℝ) ^ n) ^ 2) :=
        by gcongr <;> exact hbase
      _ = ENNReal.ofReal (C * (T / (2 : ℝ) ^ n) ^ 2 / (r ^ n) ^ 4) := by
        rw [← ENNReal.ofReal_mul hW]
        congr 1
        dsimp only [W]
        ring
  have hlevel : ∀ n : ℕ,
      (∑' k : Fin (2 ^ n), ∫⁻ w, ENNReal.ofReal
        ((‖X (mkc_pt T n ((k : ℕ) + 1)) w - X (mkc_pt T n k) w‖ / r ^ n) ^ 4) ∂P) ≤
        ENNReal.ofReal (C * T ^ 2 * q ^ n) := by
    intro n
    calc
      _ ≤ ∑' _k : Fin (2 ^ n),
          ENNReal.ofReal (C * (T / (2 : ℝ) ^ n) ^ 2 / (r ^ n) ^ 4) :=
        ENNReal.tsum_le_tsum (hsingle n)
      _ = ENNReal.ofReal ((2 : ℝ) ^ n *
          (C * (T / (2 : ℝ) ^ n) ^ 2 / (r ^ n) ^ 4)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp [ENNReal.ofReal_pow]
      _ = ENNReal.ofReal (C * T ^ 2 * q ^ n) := by
        congr 1
        have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
        have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr0.ne'
        have hp : (2 * r ^ 4) ^ n = (2 : ℝ) ^ n * (r ^ n) ^ 4 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 4 n]
        dsimp only [q]
        simp only [div_pow, one_pow, hp]
        field_simp [h2, hrn]
        <;> ring
  rw [ENNReal.tsum_sigma']
  calc
    _ ≤ ∑' n, ENNReal.ofReal (C * T ^ 2 * q ^ n) := ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (∑' n, C * T ^ 2 * q ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = ENNReal.ofReal (C * T ^ 2 / (1 - q)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      congr 1

/-- Finiteness follows from the explicit dyadic fourth-moment bound. -/
theorem fourth_increment_energy_finite
    (P : Measure Omega) (X : ℝ → Omega → E) {T r C : ℝ}
    (hT : 0 < T) (hr0 : 0 < r) (hC : 0 ≤ C) (hr : 1 < 2 * r ^ 4)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    (∑' j : (Σ n : ℕ, Fin (2 ^ n)),
      ∫⁻ w, ENNReal.ofReal
        ((‖X (mkc_pt T j.1 ((j.2 : ℕ) + 1)) w -
          X (mkc_pt T j.1 (j.2 : ℕ)) w‖ / r ^ j.1) ^ 4) ∂P) < ⊤ :=
  (fourth_increment_energy_bound P X hT hr0 hC hr hmom).trans_lt ENNReal.ofReal_lt_top

/-- Fourth moments of the initial value and the actual fourth-increment
estimate imply fourth moments of the full continuous-path norm. This
retains the endpoint exponent four rather than lowering it in the
Kolmogorov probability-tail argument. -/
theorem continuous_modification_memLp_four_of_fourth_increments
    (P : Measure Omega) (X : ℝ → Omega → E) {T r C : ℝ}
    (hT : 0 < T) (hr0 : 0 < r) (hr1 : r < 1) (hr : 1 < 2 * r ^ 4)
    (hX : ∀ t, Measurable (X t)) (hX0 : MemLp (X 0) 4 P)
    (hC : 0 ≤ C)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    MemLp (fun w => contPathOf T (fun t => mkc_Zc X T r t w)) 4 P :=
  continuous_modification_memLp_four_of_increment_energy P X hT hr0 hr1 hX hX0
    (fourth_increment_energy_finite P X hT hr0 hC hr hmom)


/-- An explicit fourth-moment bound for the entire continuous path. The
constant depends only on the initial fourth moment, the increment constant,
the interval length, and the fixed dyadic parameter. It is therefore uniform
whenever those physical inputs are uniform. -/
theorem continuous_modification_fourth_moment_bound
    (P : Measure Omega) (X : ℝ → Omega → E) {T r C : ℝ}
    (hT : 0 < T) (hr0 : 0 < r) (hr1 : r < 1) (hr : 1 < 2 * r ^ 4)
    (hX : ∀ t, Measurable (X t)) (hX0 : MemLp (X 0) 4 P)
    (hC : 0 ≤ C)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    (∫ w, ‖contPathOf T (fun t => mkc_Zc X T r t w)‖ ^ 4 ∂P) ≤
      8 * ((∫ w, ‖X 0 w‖ ^ 4 ∂P) +
        (mkc_c r) ^ 4 * (C * T ^ 2 / (1 - 1 / (2 * r ^ 4)))) := by
  let B : ℝ := C * T ^ 2 / (1 - 1 / (2 * r ^ 4))
  have hq1 : 1 / (2 * r ^ 4) < 1 := (div_lt_one (by positivity)).2 hr
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (mul_nonneg hC (sq_nonneg T)) (sub_nonneg.mpr hq1.le)
  let f : (Σ n : ℕ, Fin (2 ^ n)) → Omega → ℝ := fun j w =>
    ‖X (mkc_pt T j.1 ((j.2 : ℕ) + 1)) w - X (mkc_pt T j.1 (j.2 : ℕ)) w‖ / r ^ j.1
  have hf : ∀ j, Measurable (f j) := fun j =>
    ((hX _).sub (hX _)).norm.div_const _
  have hf0 : ∀ j w, 0 ≤ f j w := fun _ _ =>
    div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
  have henergy : (∑' j, ∫⁻ w, ENNReal.ofReal (|f j w| ^ 4) ∂P) ≤
      ENNReal.ofReal B := by
    simpa only [abs_of_nonneg (hf0 _ _)] using
      fourth_increment_energy_bound P X hT hr0 hC hr hmom
  obtain ⟨lam, hlam0, hlam, hbound, henergy_eq⟩ :=
    exists_fourth_moment_envelope_with_integral P f hf
      (henergy.trans_lt ENNReal.ofReal_lt_top)
  have hgood : ∀ᵐ w ∂P, w ∈ mkc_G X T r (lam w) := by
    filter_upwards [hbound] with w hw
    intro n k hk
    have hb := hw (⟨n, ⟨k, hk⟩⟩ : (Σ n : ℕ, Fin (2 ^ n)))
    rw [abs_of_nonneg (hf0 _ _)] at hb
    exact (div_le_iff₀ (pow_pos hr0 n)).1 hb
  let Y := fun w => contPathOf T (fun t => mkc_Zc X T r t w)
  have hY4 : MemLp Y 4 P :=
    continuous_modification_memLp_four P X hT hr0.le hr1 hX hX0 lam hlam
      (ae_of_all _ hlam0) hgood
  have hYi : Integrable (fun w => ‖Y w‖ ^ 4) P :=
    hY4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hXi : Integrable (fun w => ‖X 0 w‖ ^ 4) P :=
    hX0.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hlam_i : Integrable (fun w => lam w ^ 4) P := by
    simpa only [Real.norm_of_nonneg (hlam0 _)] using
      hlam.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hlam_bound : (∫ w, lam w ^ 4 ∂P) ≤ B := by
    have he : ENNReal.ofReal (∫ w, lam w ^ 4 ∂P) =
        ∫⁻ w, ENNReal.ofReal (lam w ^ 4) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hlam_i (ae_of_all _ fun w => by positivity)
    have hb : ENNReal.ofReal (∫ w, lam w ^ 4 ∂P) ≤ ENNReal.ofReal B := by
      rw [he, henergy_eq]
      exact henergy
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hb
  have hc : 0 ≤ mkc_c r := by
    unfold mkc_c
    positivity
  have hquartic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (a - b))
      (show 0 ≤ 7 * a ^ 2 + 10 * a * b + 7 * b ^ 2 by positivity)]
  have hpoint : ∀ᵐ w ∂P, ‖Y w‖ ^ 4 ≤
      8 * (‖X 0 w‖ ^ 4 + (mkc_c r) ^ 4 * lam w ^ 4) := by
    filter_upwards [hgood] with w hw
    have hn := continuous_modification_norm_le X hT hr0.le hr1 (hlam0 w) hw
    calc
      _ ≤ (‖X 0 w‖ + mkc_c r * lam w) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 4
      _ ≤ 8 * (‖X 0 w‖ ^ 4 + (mkc_c r * lam w) ^ 4) :=
        hquartic _ _ (norm_nonneg _) (mul_nonneg hc (hlam0 w))
      _ = 8 * (‖X 0 w‖ ^ 4 + (mkc_c r) ^ 4 * lam w ^ 4) := by rw [mul_pow]
  have hright : Integrable (fun w =>
      8 * (‖X 0 w‖ ^ 4 + (mkc_c r) ^ 4 * lam w ^ 4)) P :=
    (hXi.add (hlam_i.const_mul ((mkc_c r) ^ 4))).const_mul 8
  have hi := integral_mono_ae hYi hright hpoint
  rw [integral_const_mul, integral_add hXi (hlam_i.const_mul ((mkc_c r) ^ 4)),
    integral_const_mul] at hi
  exact hi.trans (by gcongr <;> exact hlam_bound)


#print axioms exists_fourth_moment_envelope_with_integral
#print axioms fourth_increment_energy_bound
#print axioms continuous_modification_fourth_moment_bound
#print axioms continuous_modification_norm_le
#print axioms continuous_modification_memLp_four
#print axioms exists_fourth_moment_envelope
#print axioms continuous_modification_memLp_four_of_increment_energy
#print axioms fourth_increment_energy_finite
#print axioms continuous_modification_memLp_four_of_fourth_increments

end HRS.MS.ProClosureS111
