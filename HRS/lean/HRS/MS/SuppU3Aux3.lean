import HRS.MS.QMul
import HRS.MS.UlocMWAux2
import HRS.MS.UniqM1
import HRS.MS.SobMulAux1

/-!
# U3, part 3: the `H^m` norm of a product is lower semicontinuous under pointwise limits with uniform `C_b^m` bound

`u3_sobE_prod_limit`: if `h_n ∈ C_b^m` with `‖h_n‖_{C_b^m} ≤ A` and `h_n → h` pointwise, then
`‖h u‖_{H^m} ≤ C A ‖u‖_{H^m}` for every `u` with finite `H^m` norm (`C = C(d,m)`).  Route: the multiplier estimate
`QMul.sobolevNormE_mul_cb_le` for `h_n`, `L²` convergence by dominated convergence, Fatou on the Fourier side
(`QMul.qm_fatou`).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.SuppU3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem u3_cb_sup_le {m : ℕ} {θ : Euc d → ℝ} (hθ : HRS.MemCb m θ) {j : ℕ} (hj : j ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ j θ x‖ ≤ HRS.cbNorm m θ := by
  refine (le_ciSup (hθ.2 j hj) x).trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j θ z‖)
    (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem u3_lint_sq_real {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = eLpNorm f 2 volume ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Parseval for `fourierL2`, in `ℝ≥0∞`. -/
theorem u3_parseval {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    ∫⁻ ξ, ‖fourierL2 f ξ‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have h1 := HRS.MS.UlocMW.um_sobE_sq hf 0
  rw [HRS.MS.UniqM1.sobolevNormE_zero_eq hf, ← u3_lint_sq_real hf] at h1
  simp only [Real.rpow_zero, one_mul] at h1
  rw [h1]
  refine lintegral_congr fun ξ => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem u3_sobE_prod_limit (d m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (hn : ℕ → Euc d → ℝ) (h : Euc d → ℝ),
    (∀ n, HRS.MemCb m (hn n)) → (∀ n, HRS.cbNorm m (hn n) ≤ A) →
    (∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x))) →
    ∀ u : Euc d → ℝ, HRS.Whole.sobolevNormE (m : ℝ) u ≠ ⊤ →
      HRS.Whole.sobolevNormE (m : ℝ) (fun x => h x * u x) ≤
        ENNReal.ofReal (C * A) * HRS.Whole.sobolevNormE (m : ℝ) u := by
  obtain ⟨C, hC, hmul⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  refine ⟨C, hC, fun A hn h hcb hA hlim u hu => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans ((u3_cb_sup_le (hcb 0) (Nat.zero_le m) 0).trans (hA 0))
  have hbd : ∀ n x, ‖hn n x‖ ≤ A := fun n x => by
    have := (u3_cb_sup_le (hcb n) (Nat.zero_le m) x).trans (hA n)
    simpa using this
  have hbdh : ∀ x, ‖h x‖ ≤ A := fun x =>
    le_of_tendsto' ((hlim x).norm) (fun n => hbd n x)
  have hmeas : Measurable h :=
    measurable_of_tendsto_metrizable (fun n => ((hcb n).1.continuous).measurable)
      (tendsto_pi_nhds.2 hlim)
  have hu2 : MemLp u 2 volume :=
    HRS.MS.UniqM1.memLp_of_sobolevNormE_lt_top (lt_top_iff_ne_top.2 hu)
  have hmemw : ∀ (g : Euc d → ℝ), AEStronglyMeasurable g volume → (∀ x, ‖g x‖ ≤ A) →
      MemLp (fun x => g x * u x) 2 volume := fun g hg hgb =>
    hu2.of_le_mul (c := A) (hg.mul hu2.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _))
  have hw : MemLp (fun x => h x * u x) 2 volume := hmemw h hmeas.aestronglyMeasurable hbdh
  have hwn : ∀ n, MemLp (fun x => hn n x * u x) 2 volume := fun n =>
    hmemw _ (hcb n).1.continuous.aestronglyMeasurable (hbd n)
  set S : ℝ≥0∞ := HRS.Whole.sobolevNormE (m : ℝ) u with hS
  set B0 : ℝ≥0∞ := (ENNReal.ofReal (C * A) * S) ^ 2 with hB0
  -- the Fourier transforms
  set G : Euc d → ℂ := fourierL2 (fun x => h x * u x) with hG
  set Gn : ℕ → Euc d → ℂ := fun n => fourierL2 (fun x => hn n x * u x) with hGn
  have hGL : MemLp G 2 volume := memLp_fourierL2 hw
  have hGnL : ∀ n, MemLp (Gn n) 2 volume := fun n => memLp_fourierL2 (hwn n)
  -- (1) convergence in L²
  have hconv : Tendsto (fun n => ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) atTop (𝓝 0) := by
    have e1 : ∀ n, ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2 =
        ∫⁻ x, ‖hn n x * u x - h x * u x‖ₑ ^ 2 := by
      intro n
      have hsub := fourierL2_sub (hwn n) hw
      have hwd : MemLp (fun x => hn n x * u x - h x * u x) 2 volume := (hwn n).sub hw
      rw [← u3_parseval hwd]
      refine lintegral_congr_ae ?_
      filter_upwards [hsub] with ξ hξ
      rw [hξ]
    simp_rw [e1]
    have hb : ∀ n x, ‖hn n x * u x - h x * u x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 * A) ^ 2) * ‖u x‖ₑ ^ 2 := by
      intro n x
      have h1 : ‖hn n x * u x - h x * u x‖ ≤ 2 * A * ‖u x‖ := by
        rw [← sub_mul, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖hn n x - h x‖ ≤ ‖hn n x‖ + ‖h x‖ := norm_sub_le _ _
          _ ≤ 2 * A := by linarith [hbd n x, hbdh x]
      calc ‖hn n x * u x - h x * u x‖ₑ ^ 2 = ENNReal.ofReal (‖hn n x * u x - h x * u x‖ ^ 2) := by
            rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
        _ ≤ ENNReal.ofReal ((2 * A * ‖u x‖) ^ 2) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
        _ = ENNReal.ofReal ((2 * A) ^ 2) * ‖u x‖ₑ ^ 2 := by
            rw [mul_pow, ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
              ENNReal.ofReal_pow (norm_nonneg _)]
    have hfin : ∫⁻ x, ENNReal.ofReal ((2 * A) ^ 2) * ‖u x‖ₑ ^ 2 ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, u3_lint_sq_real hu2]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top hu2.eLpNorm_lt_top.ne)
    have := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖hn n x * u x - h x * u x‖ₑ ^ 2) (f := fun _ => (0 : ℝ≥0∞))
      (bound := fun x => ENNReal.ofReal ((2 * A) ^ 2) * ‖u x‖ₑ ^ 2)
      (fun n => by
        have : AEStronglyMeasurable (fun x => hn n x * u x - h x * u x) volume :=
          ((hwn n).aestronglyMeasurable.sub hw.aestronglyMeasurable)
        exact this.enorm.pow_const 2)
      (fun n => Filter.Eventually.of_forall (hb n)) hfin
      (Filter.Eventually.of_forall fun x => by
        have h1 : Tendsto (fun n => hn n x * u x - h x * u x) atTop (𝓝 (h x * u x - h x * u x)) :=
          ((hlim x).mul_const (u x)).sub_const _
        rw [sub_self] at h1
        have h2 := ((continuous_enorm.tendsto 0).comp h1)
        simp only [enorm_zero] at h2
        have h3 := (ENNReal.continuous_pow 2).tendsto 0 |>.comp h2
        simpa [Function.comp_def] using h3)
    simpa using this
  -- (2) uniform bound
  have hB : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖Gn n ξ‖ ^ 2) ≤ B0 := by
    intro n
    have h1 := HRS.MS.UlocMW.um_sobE_sq (hwn n) (m : ℝ)
    simp only [Real.rpow_natCast] at h1
    rw [← h1, hB0]
    have h2 := hmul (hn n) (hcb n) u
    have h3 : HRS.Whole.sobolevNormE (m : ℝ) (fun x => hn n x * u x) ≤ ENNReal.ofReal (C * A) * S := by
      refine h2.trans ?_
      gcongr
      exact hA n
    exact pow_le_pow_left₀ zero_le h3 2
  have hfat := HRS.MS.QMul.qm_fatou m (G := G) (Gn := Gn) hGL hGnL hconv hB
    (tendsto_const_nhds (x := B0))
  have h5 := HRS.MS.UlocMW.um_sobE_sq hw (m : ℝ)
  simp only [Real.rpow_natCast] at h5
  rw [← h5, hB0] at hfat
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2:ℕ) ≠ 0)).1 hfat

end HRS.MS.SuppU3
