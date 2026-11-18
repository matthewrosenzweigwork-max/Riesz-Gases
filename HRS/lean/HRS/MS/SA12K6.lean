import HRS.MS.SA12K5

/-!
# S.A.12 C1, the mollified periodic density

Periodization facts (`perL` is periodic and preserves the integral), a Tonelli lemma for cube integrals of a
mollification, and the properties of `moll η μ0` needed for `PerData`: periodic, smooth, nonnegative, unit mass on
the period box, jet bounds, the nearest-lattice decay, and the cube `L¹` bounds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

theorem sa12k_perL_periodic (L : ℝ) (f : Euc d → ℝ) :
    ∀ (x : Euc d) (k : Fin d → ℤ), perL L f (x + L • latticePt k) = perL L f x := by
  intro x k
  unfold perL
  have e : ∀ z : Fin d → ℤ, f (x + L • latticePt k - L • latticePt z) =
      (fun z' : Fin d → ℤ => f (x - L • latticePt z')) ((Equiv.subRight k) z) := by
    intro z
    show f (x + L • latticePt k - L • latticePt z) = f (x - L • latticePt (z - k))
    congr 1
    ext i
    simp [latticePt, mul_sub]
    ring
  simp_rw [e]
  exact (Equiv.subRight k).tsum_eq (fun z' : Fin d → ℤ => f (x - L • latticePt z'))

theorem sa12k_perL_integral (L : ℝ) (hL : 0 < L) {f : Euc d → ℝ}
    (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) :
    ∫ x in periodBox d L, perL L f x = ∫ x, f x := by
  have h1 : ∫ x in periodBox d L, perL L f x = ∫ x in centeredBox d L, perL L f x :=
    (sa12v_centered_eq L hL (sa12k_perL_periodic L f)).symm
  have h2 : ∫ x in centeredBox d L, perL L f x = ∫ x in centeredBox d L, f x := by
    refine setIntegral_congr_fun (sa12v_centered_meas L) fun x hx => ?_
    have hU : x ∈ tca_U L 0 := by
      intro i
      have := hx i
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, sub_zero]
      rw [abs_lt]
      constructor <;> linarith [this.1, this.2]
    have := tca_perL_eq_on L hL f hv 0 x hU
    rw [this, tca_latticePt_zero, smul_zero, sub_zero]
  have h3 : ∫ x in centeredBox d L, f x = ∫ x, f x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    apply hv
    have : ∃ i, ¬ (-(L / 2) ≤ x i ∧ x i < L / 2) := by
      by_contra h
      push Not at h
      exact hx h
    obtain ⟨i, hi⟩ := this
    have h4 : L / 2 ≤ |x i| := by
      by_contra h
      push Not at h
      rw [abs_lt] at h
      exact hi ⟨by linarith [h.1], by linarith [h.2]⟩
    have h5 := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at h5
    linarith
  rw [h1, h2, h3]

variable {δ : ℝ} {η : Euc d → ℝ}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Tonelli for the cube integral of a mollification. -/
theorem sa12k_set_moll_le (hη : SA12KMoll δ η) {g : Euc d → W} (hg : Continuous g) {B : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) {A : Set (Euc d)} (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (x : Euc d) {E : ℝ} (hE : ∀ u : Euc d, ‖u‖ ≤ δ → ∫ z in A, ‖g (x - u - z)‖ ≤ E) :
    ∫ z in A, ‖sa12k_moll η g (x - z)‖ ≤ E := by
  haveI : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hAfin⟩
  set F : Euc d → Euc d → ℝ := fun z u => η u * ‖g (x - z - u)‖ with hF
  have hFc : Continuous (Function.uncurry F) := by
    refine (hη.smooth.continuous.comp continuous_snd).mul ?_
    exact (hg.comp ((continuous_const.sub continuous_fst).sub continuous_snd)).norm
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hFint : Integrable (Function.uncurry F) ((volume.restrict A).prod volume) := by
    have hd : Integrable (fun p : Euc d × Euc d => (1 : ℝ) * η p.2)
        ((volume.restrict A).prod volume) :=
      Integrable.mul_prod (f := fun _ => (1 : ℝ)) (g := η) (integrable_const _) hη.integrable
    refine Integrable.mono' (hd.const_mul B) hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖η p.2 * ‖g (x - p.1 - p.2)‖‖ ≤ B * (1 * η p.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hη.nonneg _) (norm_nonneg _))]
    nlinarith [hη.nonneg p.2, hB (x - p.1 - p.2)]
  have hswap := integral_integral_swap (μ := volume.restrict A) (ν := (volume : Measure (Euc d))) hFint
  have hFz : ∀ z, Integrable (F z) := by
    intro z
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hη.smooth.continuous.mul (hg.comp (continuous_const.sub continuous_id)).norm
    · exact hη.compact.mul_right
  have hpt : ∀ z, ‖sa12k_moll η g (x - z)‖ ≤ ∫ u, F z u := by
    intro z
    unfold sa12k_moll
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) (hFz z)
      (Filter.Eventually.of_forall fun u => ?_)
    show ‖η u • g (x - z - u)‖ ≤ η u * ‖g (x - z - u)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη.nonneg u)]
  have hmc : Continuous (fun z => ‖sa12k_moll η g (x - z)‖) :=
    ((sa12k_moll_contDiff hη hg).continuous.comp (continuous_const.sub continuous_id)).norm
  have hmint : Integrable (fun z => ‖sa12k_moll η g (x - z)‖) (volume.restrict A) := by
    refine Integrable.mono' (integrable_const B) hmc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_norm]
    exact sa12k_moll_norm_le hη hg hB _
  calc ∫ z in A, ‖sa12k_moll η g (x - z)‖ ≤ ∫ z in A, ∫ u, F z u :=
        integral_mono hmint hFint.integral_prod_left hpt
    _ = ∫ u, ∫ z in A, F z u := hswap
    _ ≤ ∫ u, η u * E := by
        refine integral_mono hFint.integral_prod_right (hη.integrable.mul_const E) fun u => ?_
        show ∫ z in A, η u * ‖g (x - z - u)‖ ≤ η u * E
        rw [integral_const_mul]
        by_cases hu : δ < ‖u‖
        · rw [hη.support u hu]; simp
        · refine mul_le_mul_of_nonneg_left ?_ (hη.nonneg u)
          have := hE u (not_lt.1 hu)
          simpa only [sub_right_comm] using this
    _ = E := by rw [integral_mul_const, hη.integral_one, one_mul]

/-- The period box has finite measure and is measurable. -/
theorem sa12k_box_fin (L : ℝ) : volume (periodBox d L) < ⊤ := sa12v_box_finite L

theorem sa12k_Q_fin (L : ℝ) : volume (tcb_Q d L) < ⊤ := tcb_measure_Q_lt_top L

/-- A shifted period box integral of a periodic function. -/
theorem sa12k_box_shift (L : ℝ) (hL : 0 < L) {Φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), Φ (x + L • latticePt k) = Φ x) (u : Euc d) :
    ∫ x in periodBox d L, Φ (x - u) = ∫ x in periodBox d L, Φ x := by
  have h := sa12c20_cell_shift L hL hper (-u)
  rw [← h]
  have hset : periodBox d L = (fun x : Euc d => x - u) ⁻¹'
      {z : Euc d | ∀ i, (-u) i ≤ z i ∧ z i < (-u) i + L} := by
    ext x
    simp only [periodBox, Set.mem_setOf_eq, Set.mem_preimage, PiLp.neg_apply, PiLp.sub_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  conv_lhs => rw [hset]
  exact (measurePreserving_sub_right (volume : Measure (Euc d)) u).setIntegral_preimage_emb
    (MeasurableEquiv.subRight u).measurableEmbedding Φ _

/-- Unit mass of the mollified density on the period box. -/
theorem sa12k_moll_box_integral (hη : SA12KMoll δ η) (L : ℝ) (hL : 0 < L) {μ0 : Euc d → ℝ}
    (hc : Continuous μ0) {B : ℝ} (hB : ∀ y, |μ0 y| ≤ B)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), μ0 (x + L • latticePt k) = μ0 x) :
    ∫ x in periodBox d L, sa12k_moll η μ0 x = ∫ x in periodBox d L, μ0 x := by
  haveI : IsFiniteMeasure (volume.restrict (periodBox d L)) := ⟨by simpa using sa12k_box_fin (d := d) L⟩
  set F : Euc d → Euc d → ℝ := fun x u => η u * μ0 (x - u) with hF
  have hFc : Continuous (Function.uncurry F) := by
    refine (hη.smooth.continuous.comp continuous_snd).mul ?_
    exact hc.comp (continuous_fst.sub continuous_snd)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (periodBox d L)).prod volume) := by
    have hd : Integrable (fun p : Euc d × Euc d => (1 : ℝ) * η p.2)
        ((volume.restrict (periodBox d L)).prod volume) :=
      Integrable.mul_prod (f := fun _ => (1 : ℝ)) (g := η) (integrable_const _) hη.integrable
    refine Integrable.mono' (hd.const_mul B) hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖η p.2 * μ0 (p.1 - p.2)‖ ≤ B * (1 * η p.2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hη.nonneg _)]
    nlinarith [hη.nonneg p.2, hB (p.1 - p.2)]
  have hswap := integral_integral_swap (μ := volume.restrict (periodBox d L))
    (ν := (volume : Measure (Euc d))) hFint
  have e1 : ∫ x in periodBox d L, sa12k_moll η μ0 x = ∫ x in periodBox d L, ∫ u, F x u := by
    refine setIntegral_congr_fun (sa12c20_box_meas L) fun x _ => ?_
    show ∫ u, η u • μ0 (x - u) = ∫ u, η u * μ0 (x - u)
    simp only [smul_eq_mul]
  rw [e1, hswap]
  have e2 : ∀ u, ∫ x in periodBox d L, F x u = η u * ∫ x in periodBox d L, μ0 x := by
    intro u
    show ∫ x in periodBox d L, η u * μ0 (x - u) = _
    rw [integral_const_mul, sa12k_box_shift L hL hper u]
  simp_rw [e2]
  rw [integral_mul_const, hη.integral_one, one_mul]

theorem sa12k_jb_le (w u : Euc d) : jbracket w ≤ jbracket (w - u) + ‖u‖ := by
  unfold jbracket
  set r : ℝ := ‖w - u‖ with hr
  set t : ℝ := ‖u‖ with ht
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hw : ‖w‖ ≤ r + t := by
    have := norm_sub_le_norm_sub_add_norm_sub w (w - u) 0
    calc ‖w‖ = ‖(w - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
  have hs : r ≤ Real.sqrt (1 + r ^ 2) := by
    have := Real.abs_le_sqrt (x := r) (y := 1 + r ^ 2) (by linarith)
    exact (le_abs_self r).trans this
  have hsq : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : ‖w‖ ^ 2 ≤ (r + t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  nlinarith [mul_le_mul_of_nonneg_left hs ht0]

theorem sa12k_g_shift {w u : Euc d} (hu : ‖u‖ ≤ 1) :
    tca_g (w - u) ≤ (2 : ℝ) ^ ((d : ℝ) + 3) * tca_g w := by
  unfold tca_g
  have h1 : jbracket w ≤ 2 * jbracket (w - u) := by
    have := sa12k_jb_le w u
    have h2 := tca_one_le_jbracket (w - u)
    linarith
  have hb : 0 < jbracket (w - u) := tca_jbracket_pos _
  have ha : 0 < jbracket w := tca_jbracket_pos _
  have h3 : jbracket w / 2 ≤ jbracket (w - u) := by linarith
  have h4 : jbracket (w - u) ^ (-((d : ℝ) + 3)) ≤ (jbracket w / 2) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  refine h4.trans (le_of_eq ?_)
  rw [Real.div_rpow ha.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
    mul_comm]

/-- The nearest lattice point. -/
theorem sa12k_near (L : ℝ) (hL : 0 < L) (x : Euc d) :
    ∃ k : Fin d → ℤ, (∀ i, |x i - L * (k i : ℝ)| ≤ L / 2) ∧ ‖x - L • latticePt k‖ ≤ ‖x‖ := by
  refine ⟨fun i => ⌊x i / L + 1 / 2⌋, fun i => ?_, ?_⟩
  · have h1 := Int.floor_le (x i / L + 1 / 2)
    have h2 := Int.lt_floor_add_one (x i / L + 1 / 2)
    have hx : x i = L * (x i / L) := by field_simp
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_lt_mul_of_pos_left h2 hL]
  · have hc : ∀ i, |(x - L • latticePt (fun i => ⌊x i / L + 1 / 2⌋)) i| ≤ |x i| := by
      intro i
      have h1 := Int.floor_le (x i / L + 1 / 2)
      have h2 := Int.lt_floor_add_one (x i / L + 1 / 2)
      have hx : x i = L * (x i / L) := by field_simp
      simp only [PiLp.sub_apply, PiLp.smul_apply, latticePt, smul_eq_mul]
      set k : ℝ := ((⌊x i / L + 1 / 2⌋ : ℤ) : ℝ) with hk
      by_cases hxi : |x i| < L / 2
      · have hxi' := abs_lt.1 hxi
        have hz : ⌊x i / L + 1 / 2⌋ = 0 := by
          rw [Int.floor_eq_zero_iff]
          constructor
          · have : -(L / 2) < x i := hxi'.1
            have h5 : -(1 / 2) < x i / L := by rw [lt_div_iff₀ hL]; linarith
            linarith
          · have : x i < L / 2 := hxi'.2
            have h5 : x i / L < 1 / 2 := by rw [div_lt_iff₀ hL]; linarith
            linarith
        rw [hk, hz]
        simp
      · push Not at hxi
        have e3 : |x i - L * k| ≤ L / 2 := by
          rw [abs_le]
          constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_lt_mul_of_pos_left h2 hL]
        exact e3.trans hxi
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2


/-- Nearest-lattice decay of the jets of the mollified periodization. -/
theorem sa12k_moll_decay (L : ℝ) (hL : 7 ≤ L) (hη : SA12KMoll δ η) (hδ : δ ≤ 1)
    {f : Euc d → ℝ} (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) {n : ℕ}
    (hμcd : ContDiff ℝ (n : WithTop ℕ∞) (perL L f)) {B Bμ : ℝ}
    (hfB : ∀ j ≤ n, ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ B * tca_g w)
    (hμB : ∀ j ≤ n, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (perL L f) y‖ ≤ Bμ) :
    ∀ j ≤ n, ∀ x : Euc d, ∃ k : Fin d → ℤ,
      jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
        ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) x‖ ≤ (2 : ℝ) ^ ((d : ℝ) + 3) * B := by
  intro j hj x
  have hL0 : 0 < L := by linarith
  obtain ⟨k, hk, -⟩ := sa12k_near L hL0 x
  refine ⟨k, ?_⟩
  have hB0 : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hfB 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (tcb_g_pos 0)
  have h1 := sa12k_moll_iter hη hμcd hμB j hj
  have hcont : Continuous (iteratedFDeriv ℝ j (perL L f)) :=
    hμcd.continuous_iteratedFDeriv (by exact_mod_cast hj)
  have hE : ‖sa12k_moll η (iteratedFDeriv ℝ j (perL L f)) x‖ ≤
      (2 : ℝ) ^ ((d : ℝ) + 3) * B * tca_g (x - L • latticePt k) := by
    refine sa12k_moll_norm_le_local hη hcont x fun u hu => ?_
    have hu1 : ‖u‖ ≤ 1 := hu.trans hδ
    have hU : x - u ∈ tca_U L k := by
      intro i
      have h2 := hk i
      have h3 : |u i| ≤ 1 := by
        have := PiLp.norm_apply_le u i
        rw [Real.norm_eq_abs] at this
        linarith
      show |(x - u) i - L * (k i : ℝ)| < 2 * L / 3
      have : (x - u) i - L * (k i : ℝ) = (x i - L * (k i : ℝ)) - u i := by simp; ring
      rw [this]
      calc |(x i - L * (k i : ℝ)) - u i| ≤ |x i - L * (k i : ℝ)| + |u i| := abs_sub _ _
        _ < 2 * L / 3 := by linarith
    rw [tca_perL_iter_norm L hL0 f hv k (x - u) hU j]
    refine (hfB j hj _).trans ?_
    have := sa12k_g_shift (w := x - L • latticePt k) hu1
    have e : x - u - L • latticePt k = x - L • latticePt k - u := by abel
    rw [e]
    calc B * tca_g (x - L • latticePt k - u)
        ≤ B * ((2 : ℝ) ^ ((d : ℝ) + 3) * tca_g (x - L • latticePt k)) :=
          mul_le_mul_of_nonneg_left this hB0
      _ = _ := by ring
  rw [congrFun h1 x]
  have hjb : 0 ≤ jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) :=
    Real.rpow_nonneg (tca_jbracket_pos _).le _
  calc jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
        ‖sa12k_moll η (iteratedFDeriv ℝ j (perL L f)) x‖
      ≤ jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
          ((2 : ℝ) ^ ((d : ℝ) + 3) * B * tca_g (x - L • latticePt k)) :=
        mul_le_mul_of_nonneg_left hE hjb
    _ = (2 : ℝ) ^ ((d : ℝ) + 3) * B *
          (jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * tca_g (x - L • latticePt k)) := by ring
    _ = (2 : ℝ) ^ ((d : ℝ) + 3) * B := by rw [tca_g_mul, mul_one]


end HRS.MH.AdjointRd.Phase2SA12Construction
