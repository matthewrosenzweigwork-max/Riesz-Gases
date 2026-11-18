import HRS.MS.SA12LimitL7
import HRS.MH.ScreenedA3a

/-!
# S.A.12 L11 (part A): quantitative decay bound of the weak operator on a localized test and its `ℓ¹(L²)` size
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12y_jb_near {w x : Euc d} (hx : ‖x - w‖ ≤ 1) : jbracket w ≤ 2 * jbracket x := by
  unfold jbracket
  have h1 : ‖w‖ ≤ ‖x‖ + 1 := by
    have := norm_sub_le_norm_sub_add_norm_sub w x 0
    have h2 : ‖w - x‖ = ‖x - w‖ := norm_sub_rev _ _
    calc ‖w‖ = ‖(w - x) + x‖ := by simp
      _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ _ := by rw [h2]; linarith
  have h2 : 1 + ‖w‖ ^ 2 ≤ 4 * (1 + ‖x‖ ^ 2) := by
    nlinarith [norm_nonneg w, norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith

theorem sa12y_jb_cell {k : ℝ} (hk : 1 ≤ k) (z : Fin d → ℤ) :
    jbracket (latticePt z) ≤ k * jbracket (k⁻¹ • latticePt z) := by
  unfold jbracket
  have hk0 : 0 < k := by linarith
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hk0.le]
  have : (k⁻¹ * ‖latticePt z‖) ^ 2 = k⁻¹ ^ 2 * ‖latticePt z‖ ^ 2 := by ring
  rw [this, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have h1 : k ^ 2 * (k⁻¹ ^ 2) = 1 := by field_simp
  have h2 : (1 : ℝ) ≤ k ^ 2 := by nlinarith
  nlinarith [sq_nonneg ‖latticePt z‖]

/-- Pointwise decay `|g| ≤ c ⟨x⟩^{-(d+3)}` bounds `cellL2Sum g` linearly in `c`. -/
theorem sa12y_cell_decay (hd : 1 ≤ d) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ (g : Euc d → ℝ) (c : ℝ), 0 ≤ c →
      (∀ x, |g x| ≤ c * jbracket x ^ (-((d : ℝ) + 3))) → cellL2Sum g ≤ ENNReal.ofReal (CA * c) := by
  set kk : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hkk
  have hk1 : 1 ≤ kk := by
    rw [hkk]
    have : (1 : ℝ) ≤ Real.sqrt d := by
      rw [Real.one_le_sqrt]; exact_mod_cast hd
    have h2 : (1 : ℤ) ≤ ⌈Real.sqrt d⌉ := by
      rw [Int.one_le_ceil_iff]; exact lt_of_lt_of_le zero_lt_one this
    exact_mod_cast h2
  set E : ℝ := 2 ^ ((d : ℝ) + 3) * kk ^ ((d : ℝ) + 3) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set S : ℝ≥0∞ := ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) with hS
  have hSt : S < ⊤ := HRS.MH.Screened.cellWeight_tsum_lt_top_proof hd
  set v : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 1) with hv
  have hvt : v < ⊤ := measure_ball_lt_top
  set W : ℝ≥0∞ := v ^ (1 / 2 : ℝ) with hW
  have hWt : W < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvt.ne
  refine ⟨E * S.toReal * W.toReal, by positivity, fun g c hc hg => ?_⟩
  have hcell : ∀ z : Fin d → ℤ, (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c * E * cellWeight d z) * W := by
    intro z
    have hcw : 0 ≤ cellWeight d z := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hpt : ∀ x ∈ Metric.ball (cellPt d z) 1, |g x| ≤ c * E * cellWeight d z := by
      intro x hx
      have hxn : ‖x - cellPt d z‖ ≤ 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le
      have hjb := sa12y_jb_near hxn
      have hjbx : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)
      have hjbw : 0 < jbracket (cellPt d z) := Real.sqrt_pos.2 (by positivity)
      have hjl : 0 < jbracket (latticePt z) := Real.sqrt_pos.2 (by positivity)
      have hp : 0 ≤ (d : ℝ) + 3 := by positivity
      have h1 : jbracket x ^ (-((d : ℝ) + 3)) ≤ (jbracket (cellPt d z) / 2) ^ (-((d : ℝ) + 3)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h2 : (jbracket (cellPt d z) / 2) ^ (-((d : ℝ) + 3)) =
          2 ^ ((d : ℝ) + 3) * jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) := by
        rw [Real.div_rpow hjbw.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg hjbw.le, div_eq_mul_inv, inv_inv, mul_comm]
      have h3 : jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) ≤
          kk ^ ((d : ℝ) + 3) * cellWeight d z := by
        have hc := sa12y_jb_cell (d := d) hk1 z
        have hcp : cellPt d z = kk⁻¹ • latticePt z := rfl
        rw [← hcp] at hc
        have h4 : jbracket (latticePt z) / kk ≤ jbracket (cellPt d z) := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have h5 := Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by linarith : -((d : ℝ) + 3) ≤ 0)
        refine h5.trans (le_of_eq ?_)
        unfold cellWeight
        rw [Real.div_rpow hjl.le (by linarith), Real.rpow_neg hjl.le, Real.rpow_neg (by linarith : (0 : ℝ) ≤ kk)]
        field_simp
      calc |g x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)) := hg x
        _ ≤ c * (2 ^ ((d : ℝ) + 3) * (kk ^ ((d : ℝ) + 3) * cellWeight d z)) := by
            refine mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans ?_)) hc
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = c * E * cellWeight d z := by rw [hE]; ring
    have hint : ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2) ≤
        ENNReal.ofReal ((c * E * cellWeight d z) ^ 2) * v := by
      calc ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)
          ≤ ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal ((c * E * cellWeight d z) ^ 2) := by
            refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← sq_abs (g x)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx) 2
        _ = ENNReal.ofReal ((c * E * cellWeight d z) ^ 2) * volume (Metric.ball (cellPt d z) 1) := by
            rw [setLIntegral_const]
        _ = _ := by rw [hv, Measure.addHaar_ball_center]
    calc (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((c * E * cellWeight d z) ^ 2) * v) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hint (by norm_num)
      _ = ENNReal.ofReal (c * E * cellWeight d z) * W := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hW,
            ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
  unfold cellL2Sum
  calc ∑' z : Fin d → ℤ, (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal (c * E * cellWeight d z) * W := ENNReal.tsum_le_tsum hcell
    _ = ENNReal.ofReal (c * E) * S * W := by
        rw [ENNReal.tsum_mul_right, hS, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun z => ?_
        have hcw : 0 ≤ cellWeight d z := Real.rpow_nonneg (Real.sqrt_nonneg _) _
        rw [ENNReal.ofReal_mul (show 0 ≤ c * E by positivity)]
    _ = ENNReal.ofReal (E * S.toReal * W.toReal * c) := by
        have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
        have hW0 : 0 ≤ W.toReal := ENNReal.toReal_nonneg
        rw [show E * S.toReal * W.toReal * c = (c * E) * S.toReal * W.toReal by ring,
          ENNReal.ofReal_mul (show 0 ≤ c * E * S.toReal by positivity),
          ENNReal.ofReal_mul (show 0 ≤ c * E by positivity),
          ENNReal.ofReal_toReal hSt.ne, ENNReal.ofReal_toReal hWt.ne]
    _ ≤ _ := le_rfl

/-- Quantitative version of `UniqT3.conv_bound`: the constants depend only on `(d, s)`, `R0` and `M`. -/
theorem sa12y_conv_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (R0 M : ℝ) (h : Euc d → ℝ), 0 ≤ R0 → 0 ≤ M →
      (∀ t, h t ≠ 0 → ‖t‖ ≤ R0) → (∀ t, |h t| ≤ M) → ∀ r : Euc d,
      |HRS.Whole.convFun (rieszKernel d s) h r| ≤
        M * (G + (‖r‖ + R0) * (volume (Metric.closedBall (0 : Euc d) R0)).toReal) := by
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := HRS.MS.UniqT3.g_dom (d := d) hs0 hsd
  refine ⟨∫ z, G0 z, integral_nonneg hG0n, fun R0 M h hR hM0 hsupp hM r => ?_⟩
  set g := rieszKernel d s with hg
  set Vcb : ℝ := (volume (Metric.closedBall (0 : Euc d) R0)).toReal with hVcb
  have hcbi : Integrable ((Metric.closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  set bd : Euc d → ℝ := fun t => M * G0 (r - t) + M * (‖r‖ + R0) *
    (Metric.closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t with hbd
  have hbdi : Integrable bd := ((hG0i.comp_sub_left r).const_mul M).add (hcbi.const_mul _)
  have hle : ∀ t, ‖g (r - t) * h t‖ ≤ bd t := by
    intro t
    by_cases ht : h t = 0
    · rw [ht, mul_zero, norm_zero]
      have : 0 ≤ M * (‖r‖ + R0) * (Metric.closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t := by
        exact mul_nonneg (mul_nonneg hM0 (add_nonneg (norm_nonneg _) hR))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      exact add_nonneg (mul_nonneg hM0 (hG0n _)) this
    · have htn : ‖t‖ ≤ R0 := hsupp t ht
      have htc : t ∈ Metric.closedBall (0 : Euc d) R0 := by simpa using htn
      have h1 : ‖r - t‖ ≤ ‖r‖ + R0 := (norm_sub_le _ _).trans (by linarith)
      rw [norm_mul, Real.norm_eq_abs, hbd]
      simp only [Set.indicator_of_mem htc, mul_one]
      calc |g (r - t)| * ‖h t‖ ≤ (G0 (r - t) + (‖r‖ + R0)) * M :=
            mul_le_mul ((hgG _).trans (by linarith)) (by simpa using hM t) (norm_nonneg _)
              (by linarith [hG0n (r - t), norm_nonneg r, norm_nonneg t])
        _ = _ := by ring
  have h1 := norm_integral_le_of_norm_le hbdi (Filter.Eventually.of_forall hle)
  have h2 : ∫ t, bd t = M * (∫ z, G0 z) + M * (‖r‖ + R0) * Vcb := by
    rw [hbd, integral_add ((hG0i.comp_sub_left r).const_mul M) (hcbi.const_mul _),
      integral_const_mul, integral_const_mul, integral_sub_left_eq_self G0 volume r,
      integral_indicator Metric.isClosed_closedBall.measurableSet]
    simp [hVcb, Measure.real]
  rw [Real.norm_eq_abs] at h1
  calc _ = |∫ t, g (r - t) * h t| := rfl
    _ ≤ _ := h1
    _ = _ := h2
    _ = _ := by ring

theorem sa12y_D1D1_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ) (i j : Fin d) (x : Euc d) :
    |HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i φ) x| ≤ ‖iteratedFDeriv ℝ 2 φ x‖ := by
  unfold HRS.MS.UniqT3.D1
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  have h := (iteratedFDeriv ℝ 2 φ x).le_opNorm ![EuclideanSpace.single j (1:ℝ), EuclideanSpace.single i (1:ℝ)]
  rw [iteratedFDeriv_two_apply] at h
  simp [Fin.prod_univ_two] at h
  simpa [Real.norm_eq_abs] using h

theorem sa12y_D1_le {φ : Euc d → ℝ} (i : Fin d) (x : Euc d) :
    |HRS.MS.UniqT3.D1 i φ x| ≤ ‖iteratedFDeriv ℝ 1 φ x‖ := by
  refine (HRS.MS.UniqN2b.n2b_D1_le i φ x).trans (le_of_eq ?_)
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := φ) (x := x)
  simpa using this


set_option maxHeartbeats 1600000 in
theorem sa12y_weakOp_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : Euc d → ℝ) (A : ℝ), ContDiff ℝ ∞ φ →
      tsupport φ ⊆ Metric.closedBall (0 : Euc d) R → 0 ≤ A →
      (∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ A) → ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
      |(D.coeff μ).ν * Laplacian.laplacian φ x - movDiv (fun y => φ y • (D.coeff μ).drift r y) x -
        nonlocalTestRd (D.coeff μ) r φ x| ≤ K * A * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  subst hDs
  have hs0' : 0 ≤ D.s := hs0
  have hsd' : D.s < d := hsd
  have hμ : CoeffHypRd D.s m Λ T μ := hD.hμ
  have hl := rieszKernel_locallyIntegrable (d := d) hs0' hsd'
  obtain ⟨G, hG0, hG⟩ := sa12y_conv_bound (d := d) hs0' hsd'
  set V : ℝ := (volume (Metric.closedBall (0 : Euc d) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hR0 : 0 ≤ R := by linarith
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  set Cb : ℝ := |HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀| with hCb
  have hCb0 : 0 ≤ Cb := abs_nonneg _
  set Mabs : ℝ := ∑ i, ∑ j, |D.M j i| with hMabs
  have hMabs0 : 0 ≤ Mabs := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set Kf1 : ℝ := (max 1 D.s * 2 ^ (D.s + 1)) * V with hKf1
  set Kf2 : ℝ := (max 1 D.s * (D.s + 3) * 2 ^ (D.s + 2)) * V with hKf2
  have hKf1' : 0 ≤ Kf1 := by rw [hKf1]; positivity
  have hKf2' : 0 ≤ Kf2 := by rw [hKf2]; positivity
  set Kk : ℝ := (G + 3 * R * V) + Kf1 + Kf2 with hKk
  have hRV : 0 ≤ 3 * R * V := by positivity
  have hKk0 : 0 ≤ Kk := by rw [hKk]; positivity
  set Jr : ℝ := (1 + R) ^ ((d : ℝ) + 3) with hJr
  have hJr0 : 0 ≤ Jr := by rw [hJr]; positivity
  set L1 : ℝ := |D.invβ| * d + d * Cb * (2 + R) with hL1
  have hL10 : 0 ≤ L1 := by rw [hL1]; positivity
  refine ⟨L1 * Jr + Mabs * (2 * Cρ * Kk), by positivity, fun φ A hφ hsupp hA hjet r hr x => ?_⟩
  obtain ⟨hb1, hb1', hb0, hρ1, hρ0, hρ1'⟩ :=
    HRS.MS.UniqE1.e1_coeff hd hs0' hsd' m MB Λ ΛV G₀ hD.hM hD.hV hμ hr
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφc : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall _ _) (isClosed_tsupport φ) hsupp
  have hsupp' : Function.support φ ⊆ Metric.closedBall (0 : Euc d) R :=
    (subset_tsupport φ).trans hsupp
  have hj0 : ∀ y, |φ y| ≤ A := fun y => by
    have := hjet 0 (by norm_num) y
    simpa using this
  have hj1 : ∀ i y, |HRS.MS.UniqT3.D1 i φ y| ≤ A := fun i y =>
    (sa12y_D1_le i y).trans (hjet 1 (by norm_num) y)
  have hj2 : ∀ i j y, |HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i φ) y| ≤ A := fun i j y =>
    (sa12y_D1D1_le hφ2 i j y).trans (hjet 2 le_rfl y)
  have hout : ∀ y : Euc d, R < ‖y‖ → φ y = 0 ∧ (∀ i, HRS.MS.UniqT3.D1 i φ y = 0) ∧
      ∀ i j, HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i φ) y = 0 := by
    intro y hy
    have hyn : y ∉ tsupport φ := fun h => by
      have := hsupp h
      rw [mem_closedBall_zero_iff] at this
      linarith
    have h0 : ∀ n, iteratedFDeriv ℝ n φ y = 0 := fun n => by
      by_contra hne
      exact hyn (support_iteratedFDeriv_subset (𝕜 := ℝ) n hne)
    refine ⟨image_eq_zero_of_notMem_tsupport hyn, fun i => ?_, fun i j => ?_⟩
    · have := sa12y_D1_le (φ := φ) i y
      rw [h0 1, norm_zero] at this
      exact abs_nonpos_iff.1 this
    · have := sa12y_D1D1_le hφ2 i j y
      rw [h0 2, norm_zero] at this
      exact abs_nonpos_iff.1 this
  have hint : ∫ y, |φ y| ≤ A * V := by
    have hind : Integrable ((Metric.closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc ∫ y, |φ y| ≤ ∫ y, A * (Metric.closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ)) y :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hind.const_mul A)
            (Eventually.of_forall fun y => by
              by_cases hy : y ∈ Metric.closedBall (0 : Euc d) R
              · simpa [Set.indicator_of_mem hy] using hj0 y
              · have : φ y = 0 := by
                  by_contra hne; exact hy (hsupp' hne)
                simp [Set.indicator_of_notMem hy, this])
      _ = A * V := by
          rw [integral_const_mul, integral_indicator Metric.isClosed_closedBall.measurableSet]
          simp [hV, Measure.real]
  -- kernel bounds
  have hK1 : ∀ (i : Fin d) (y : Euc d), |kernelConvDeriv d D.s i φ y| ≤ Kk * A := by
    intro i y
    by_cases hy : ‖y‖ ≤ 2 * R
    · have := hG R A (HRS.MS.UniqT3.D1 i φ) hR0 hA
        (fun t ht => by
          by_contra hne; push Not at hne
          exact ht ((hout t hne).2.1 i)) (hj1 i) y
      have h2 : |kernelConvDeriv d D.s i φ y| ≤ A * (G + (‖y‖ + R) * V) := this
      refine h2.trans ?_
      have : (‖y‖ + R) * V ≤ 3 * R * V := mul_le_mul_of_nonneg_right (by linarith) hV0
      nlinarith [mul_nonneg hA hKf1', mul_nonneg hA hKf2', mul_nonneg hA hG0]
    · push Not at hy
      have := HRS.MS.UniqN0.n0_far_bound hs0' i hφ1 hφc (c := 0) hR hsupp' (y := y) (by simpa using hy.le)
      simp only [sub_zero] at this
      have hy1 : 1 ≤ ‖y‖ := by linarith
      have hp : ‖y‖ ^ (-D.s - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
      have hc0 : 0 ≤ max 1 D.s * 2 ^ (D.s + 1) := by positivity
      calc |kernelConvDeriv d D.s i φ y| ≤ (max 1 D.s * 2 ^ (D.s + 1)) * (∫ x, |φ x|) * ‖y‖ ^ (-D.s - 1) := this
        _ ≤ (max 1 D.s * 2 ^ (D.s + 1)) * (A * V) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hint hc0) hp (by positivity) (by positivity)
        _ = Kf1 * A := by rw [hKf1]; ring
        _ ≤ Kk * A := by
            refine mul_le_mul_of_nonneg_right ?_ hA
            rw [hKk]; linarith [hRV, hG0, hKf2']
  have hK2 : ∀ (i j : Fin d) (y : Euc d),
      |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) y| ≤ Kk * A := by
    intro i j y
    by_cases hy : ‖y‖ ≤ 2 * R
    · rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0' hsd' hφ2 hφc i j y]
      have := hG R A (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i φ)) hR0 hA
        (fun t ht => by
          by_contra hne; push Not at hne
          exact ht ((hout t hne).2.2 i j)) (hj2 i j) y
      refine this.trans ?_
      have : (‖y‖ + R) * V ≤ 3 * R * V := mul_le_mul_of_nonneg_right (by linarith) hV0
      nlinarith [mul_nonneg hA hKf1', mul_nonneg hA hKf2', mul_nonneg hA hG0]
    · push Not at hy
      have := HRS.MS.UniqN0.n0_far_grad_bound hs0' hsd' i j hφ2 hφc (c := 0) hR hsupp' (y := y)
        (by simpa using hy.le)
      simp only [sub_zero] at this
      have hy1 : 1 ≤ ‖y‖ := by linarith
      have hp : ‖y‖ ^ (-D.s - 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
      have hc0 : 0 ≤ max 1 D.s * (D.s + 3) * 2 ^ (D.s + 2) := by positivity
      have h3 : |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) y| ≤
          (max 1 D.s * (D.s + 3) * 2 ^ (D.s + 2)) * (∫ x, |φ x|) * ‖y‖ ^ (-D.s - 2) := this
      calc _ ≤ _ := h3
        _ ≤ (max 1 D.s * (D.s + 3) * 2 ^ (D.s + 2)) * (A * V) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hint hc0) hp (by positivity) (by positivity)
        _ = Kf2 * A := by rw [hKf2]; ring
        _ ≤ Kk * A := by
            refine mul_le_mul_of_nonneg_right ?_ hA
            rw [hKk]; linarith [hRV, hG0, hKf1']
  -- the nonlocal term
  have hnl : nonlocalTestRd (D.coeff μ) r φ x = ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      (HRS.MS.UniqT3.D1 j (μ r) x * kernelConvDeriv d D.s i φ x + μ r x *
        HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) x) := by
    unfold nonlocalTestRd
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hg : ∀ y, gradient (HRS.Whole.convFun (rieszKernel d D.s) φ) y i =
        kernelConvDeriv d D.s i φ y := by
      intro y
      rw [q09_gradient_apply]
      exact HRS.MS.UniqT3.convFun_D1 hl hφ1 hφc i y
    show D.M j i * partialDeriv (fun _ : Fin 1 => j)
      (fun y => μ r y * gradient (HRS.Whole.convFun (rieszKernel d D.s) φ) y i) x = _
    congr 1
    simp only [hg]
    unfold partialDeriv
    rw [iteratedFDeriv_one_apply]
    rw [HRS.MS.UniqN2b.n2b_fderiv_prod hs0' hsd' hρ1 hφ2 hφc i j x,
      ← HRS.MS.UniqN1c.n1c_D1_kcd hs0' hsd' hφ2 hφc i j x]
  have hjb0 : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)
  have hjbl : jbracket x ≤ 1 + ‖x‖ := by
    unfold jbracket
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg x]
  have hpow : (1 + ‖x‖) ^ (-((d : ℝ) + 3)) ≤ jbracket x ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos hjb0 hjbl (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hjp0 : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg hjb0.le _
  have hnlb : |nonlocalTestRd (D.coeff μ) r φ x| ≤
      Mabs * (2 * Cρ * Kk) * A * jbracket x ^ (-((d : ℝ) + 3)) := by
    set u : ℝ := (1 + ‖x‖) ^ (-((d : ℝ) + 3)) with hu
    have hu0 : 0 ≤ u := Real.rpow_nonneg (by positivity) _
    have hd1 : ∀ j, |HRS.MS.UniqT3.D1 j (μ r) x| ≤ Cρ * u := fun j =>
      (HRS.MS.UniqN2b.n2b_D1_le j (μ r) x).trans (hρ1' x)
    have hterm : ∀ i j : Fin d,
        |HRS.MS.UniqT3.D1 j (μ r) x * kernelConvDeriv d D.s i φ x + μ r x *
          HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) x| ≤
          2 * Cρ * Kk * A * jbracket x ^ (-((d : ℝ) + 3)) := by
      intro i j
      calc _ ≤ |HRS.MS.UniqT3.D1 j (μ r) x * kernelConvDeriv d D.s i φ x| +
            |μ r x * HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) x| := abs_add_le _ _
        _ = |HRS.MS.UniqT3.D1 j (μ r) x| * |kernelConvDeriv d D.s i φ x| +
            |μ r x| * |HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i φ) x| := by
            rw [abs_mul, abs_mul]
        _ ≤ (Cρ * u) * (Kk * A) + (Cρ * u) * (Kk * A) :=
            add_le_add (mul_le_mul (hd1 j) (hK1 i x) (abs_nonneg _) (by positivity))
              (mul_le_mul (hρ0 x) (hK2 i j x) (abs_nonneg _) (by positivity))
        _ = 2 * Cρ * Kk * A * u := by ring
        _ ≤ 2 * Cρ * Kk * A * jbracket x ^ (-((d : ℝ) + 3)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
    rw [hnl]
    calc _ ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i| * (2 * Cρ * Kk * A * jbracket x ^ (-((d : ℝ) + 3))) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hterm i j) (abs_nonneg _)
      _ = Mabs * (2 * Cρ * Kk * A * jbracket x ^ (-((d : ℝ) + 3))) := by
          rw [hMabs, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ = _ := by ring
  -- the local terms
  set b : Euc d → Euc d := meanFieldDriftW D (μ r) with hbdef
  have hdr : (D.coeff μ).drift r = b := rfl
  have hvc : ContDiff ℝ 1 b := contDiff_euclidean.2 hb1
  have hmov : movDiv (fun y => φ y • b y) x =
      ∑ i, (b x i * HRS.MS.UniqT3.D1 i φ x + φ x * HRS.MS.UniqT3.D1 i (fun w => b w i) x) := by
    unfold movDiv
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbd : DifferentiableAt ℝ b x := hvc.differentiable (by norm_num) x
    have hφd : DifferentiableAt ℝ φ x := hφ1.differentiable (by norm_num) x
    have h1 := hφd.hasFDerivAt.smul hbd.hasFDerivAt
    rw [show fderiv ℝ (fun y => φ y • b y) x = _ from h1.fderiv]
    have h2 : fderiv ℝ (fun w => b w i) x = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ b x) :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hbd.hasFDerivAt).fderiv
    unfold HRS.MS.UniqT3.D1
    rw [h2]
    simp
    ring
  have hlap : Laplacian.laplacian φ x = ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i φ) x :=
    HRS.MS.UniqT3.lap_eq hφ2 x
  have hloc : |(D.coeff μ).ν * Laplacian.laplacian φ x - movDiv (fun y => φ y • b y) x| ≤
      L1 * A * Jr * jbracket x ^ (-((d : ℝ) + 3)) := by
    by_cases hx : ‖x‖ ≤ R
    · have hnu : (D.coeff μ).ν = D.invβ := rfl
      have hlapb : |Laplacian.laplacian φ x| ≤ d * A := by
        rw [hlap]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc _ ≤ ∑ _i : Fin d, A := Finset.sum_le_sum fun i _ => hj2 i i x
          _ = d * A := by simp
      have hmovb : |movDiv (fun y => φ y • b y) x| ≤ d * (A * Cb * (2 + R)) := by
        rw [hmov]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc _ ≤ ∑ _i : Fin d, (A * Cb * (2 + R)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have e1 : |b x i| ≤ Cb * (1 + R) := by
                refine (hb0 i x).trans ?_
                calc _ ≤ |HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀| * (1 + ‖x‖) :=
                      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
                  _ ≤ Cb * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hCb0
              have e2 : |HRS.MS.UniqT3.D1 i (fun w => b w i) x| ≤ Cb := (hb1' i x).trans (le_abs_self _)
              calc _ ≤ |b x i * HRS.MS.UniqT3.D1 i φ x| + |φ x * HRS.MS.UniqT3.D1 i (fun w => b w i) x| :=
                    abs_add_le _ _
                _ = |b x i| * |HRS.MS.UniqT3.D1 i φ x| + |φ x| * |HRS.MS.UniqT3.D1 i (fun w => b w i) x| := by
                    rw [abs_mul, abs_mul]
                _ ≤ (Cb * (1 + R)) * A + A * Cb :=
                    add_le_add (mul_le_mul e1 (hj1 i x) (abs_nonneg _) (by positivity))
                      (mul_le_mul (hj0 x) e2 (abs_nonneg _) hA)
                _ = A * Cb * (2 + R) := by ring
          _ = d * (A * Cb * (2 + R)) := by simp
      have hbase : |(D.coeff μ).ν * Laplacian.laplacian φ x - movDiv (fun y => φ y • b y) x| ≤ L1 * A := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, hnu]
        calc _ ≤ |D.invβ| * (d * A) + d * (A * Cb * (2 + R)) :=
              add_le_add (mul_le_mul_of_nonneg_left hlapb (abs_nonneg _)) hmovb
          _ = L1 * A := by rw [hL1]; ring
      have hone : 1 ≤ Jr * jbracket x ^ (-((d : ℝ) + 3)) := by
        have hjR : jbracket x ≤ 1 + R := hjbl.trans (by linarith)
        have h1 : (1 + R) ^ (-((d : ℝ) + 3)) ≤ jbracket x ^ (-((d : ℝ) + 3)) :=
          Real.rpow_le_rpow_of_nonpos hjb0 hjR (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
        have h2 : Jr * (1 + R) ^ (-((d : ℝ) + 3)) = 1 := by
          rw [hJr, ← Real.rpow_add (by linarith)]; simp
        calc (1 : ℝ) = Jr * (1 + R) ^ (-((d : ℝ) + 3)) := h2.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hJr0
      calc _ ≤ L1 * A := hbase
        _ = L1 * A * 1 := by ring
        _ ≤ L1 * A * (Jr * jbracket x ^ (-((d : ℝ) + 3))) :=
            mul_le_mul_of_nonneg_left hone (by positivity)
        _ = _ := by ring
    · push Not at hx
      obtain ⟨h0, h1, h2⟩ := hout x hx
      have hl0 : Laplacian.laplacian φ x = 0 := by rw [hlap]; simp [h2]
      have hm0 : movDiv (fun y => φ y • b y) x = 0 := by rw [hmov]; simp [h0, h1]
      rw [hl0, hm0]
      simp only [mul_zero, sub_zero, abs_zero]
      positivity
  rw [hdr]
  calc _ ≤ |(D.coeff μ).ν * Laplacian.laplacian φ x - movDiv (fun y => φ y • b y) x| +
        |nonlocalTestRd (D.coeff μ) r φ x| := abs_sub _ _
    _ ≤ L1 * A * Jr * jbracket x ^ (-((d : ℝ) + 3)) +
        Mabs * (2 * Cρ * Kk) * A * jbracket x ^ (-((d : ℝ) + 3)) := add_le_add hloc hnlb
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Limit
