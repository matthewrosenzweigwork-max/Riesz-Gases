import HRS.MS.SA12LimitL11A

/-!
# S.A.12 L8 (helper): smallness of `cellL2Sum` from decay plus local smallness

If `|h(x)| ≤ c ⟨x⟩^{-(d+3)}` for all `x` and `|h| ≤ η₀` on a large ball, then `cellL2Sum h ≤ δ`:
the cells far out are controlled by the summable weights `⟨cellPt z⟩^{-(d+3)}`, the finitely many near cells
by the local bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The local `L²` norm of a function bounded on the unit ball. -/
theorem sa12k_cn_const (g : Euc d → ℝ) (A : ℝ) (hA : 0 ≤ A) (z : Fin d → ℤ)
    (hg : ∀ x ∈ Metric.ball (cellPt d z) 1, |g x| ≤ A) :
    (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal A * (volume (Metric.ball (0 : Euc d) 1)) ^ (1 / 2 : ℝ) := by
  have hint : ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2) ≤
      ENNReal.ofReal (A ^ 2) * volume (Metric.ball (0 : Euc d) 1) := by
    calc ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)
        ≤ ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (A ^ 2) := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← sq_abs (g x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hg x hx) 2
      _ = ENNReal.ofReal (A ^ 2) * volume (Metric.ball (cellPt d z) 1) := by
          rw [setLIntegral_const]
      _ = _ := by rw [Measure.addHaar_ball_center]
  calc (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (A ^ 2) * volume (Metric.ball (0 : Euc d) 1)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal A * (volume (Metric.ball (0 : Euc d) 1)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hA,
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-- The local `L²` norm of a function with decay, with the weight `⟨cellPt z⟩^{-(d+3)}`. -/
theorem sa12k_cn_decay (hd : 1 ≤ d) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (g : Euc d → ℝ) (c : ℝ), 0 ≤ c → ∀ z : Fin d → ℤ,
      (∀ x, |g x| ≤ c * jbracket x ^ (-((d : ℝ) + 3))) →
      (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (c * E * cellWeight d z) * (volume (Metric.ball (0 : Euc d) 1)) ^ (1 / 2 : ℝ) := by
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
  refine ⟨E, hE0, fun g c hc z hg => ?_⟩
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
      have hc' := sa12y_jb_cell (d := d) hk1 z
      have hcp : cellPt d z = kk⁻¹ • latticePt z := rfl
      rw [← hcp] at hc'
      have h4 : jbracket (latticePt z) / kk ≤ jbracket (cellPt d z) := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have h5 := Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by linarith : -((d : ℝ) + 3) ≤ 0)
      refine h5.trans (le_of_eq ?_)
      unfold cellWeight
      rw [Real.div_rpow hjl.le (by linarith), Real.rpow_neg hjl.le,
        Real.rpow_neg (by linarith : (0 : ℝ) ≤ kk)]
      field_simp
    calc |g x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)) := hg x
      _ ≤ c * (2 ^ ((d : ℝ) + 3) * (kk ^ ((d : ℝ) + 3) * cellWeight d z)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans ?_)) hc
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = c * E * cellWeight d z := by rw [hE]; ring
  exact sa12k_cn_const g _ (by positivity) z hpt

set_option maxHeartbeats 2000000 in
theorem sa12k_cell_small (hd : 1 ≤ d) (c : ℝ) (hc : 0 ≤ c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R η₀ : ℝ, 0 < η₀ ∧ ∀ h : Euc d → ℝ,
      (∀ x, |h x| ≤ c * jbracket x ^ (-((d : ℝ) + 3))) → (∀ x : Euc d, ‖x‖ ≤ R → |h x| ≤ η₀) →
        cellL2Sum h ≤ ENNReal.ofReal δ := by
  obtain ⟨E, hE0, hcell⟩ := sa12k_cn_decay hd
  set v : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 1) with hv
  have hvt : v < ⊤ := measure_ball_lt_top
  set W : ℝ≥0∞ := v ^ (1 / 2 : ℝ) with hW
  have hWt : W < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvt.ne
  have hSt : ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) < ⊤ :=
    HRS.MH.Screened.cellWeight_tsum_lt_top_proof hd
  set Kc : ℝ≥0∞ := ENNReal.ofReal (c * E) * W with hKc
  have hKt : Kc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWt
  set ε'' : ℝ≥0∞ := ENNReal.ofReal ((δ / 2) / (Kc.toReal + 1)) with hε''
  have hε''pos : 0 < ε'' := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨F, hF⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hSt.ne).eventually
    (gt_mem_nhds hε''pos)).exists
  set R : ℝ := 1 + ∑ z ∈ F, ‖cellPt d z‖ with hR
  set η₀ : ℝ := (δ / 2) / (((F.card : ℝ) + 1) * (W.toReal + 1)) with hη₀
  have hη₀pos : 0 < η₀ := by positivity
  refine ⟨R, η₀, hη₀pos, fun h hdec hnear => ?_⟩
  -- the cell bounds
  set b : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
    if z ∈ F then ENNReal.ofReal η₀ * W else ENNReal.ofReal (c * E * cellWeight d z) * W with hb
  have hcb : ∀ z : Fin d → ℤ, (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (h x ^ 2)) ^ (1 / 2 : ℝ) ≤
      b z := by
    intro z
    by_cases hz : z ∈ F
    · simp only [hb, hz, if_true]
      refine sa12k_cn_const h η₀ hη₀pos.le z fun x hx => hnear x ?_
      have hxn : ‖x - cellPt d z‖ ≤ 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le
      have h1 : ‖x‖ ≤ ‖cellPt d z‖ + 1 := by
        calc ‖x‖ = ‖(x - cellPt d z) + cellPt d z‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - cellPt d z‖ + ‖cellPt d z‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have h2 : ‖cellPt d z‖ ≤ ∑ z' ∈ F, ‖cellPt d z'‖ :=
        Finset.single_le_sum (f := fun z' => ‖cellPt d z'‖) (fun _ _ => norm_nonneg _) hz
      rw [hR]; linarith
    · simp only [hb, hz, ite_false]
      exact hcell h c hc z hdec
  have hnear_sum : ∑ z ∈ F, b z ≤ ENNReal.ofReal (δ / 2) := by
    have e0 : ∑ z ∈ F, b z = ∑ z ∈ F, ENNReal.ofReal η₀ * W :=
      Finset.sum_congr rfl (fun z hz => by simp only [hb, hz, if_true])
    have e1 : ∑ z ∈ F, b z = (F.card : ℝ≥0∞) * (ENNReal.ofReal η₀ * W) := by
      rw [e0, Finset.sum_const, nsmul_eq_mul]
    have hWr : 0 ≤ W.toReal := ENNReal.toReal_nonneg
    have hcard : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
    have e2 : (F.card : ℝ≥0∞) * (ENNReal.ofReal η₀ * W) =
        ENNReal.ofReal ((F.card : ℝ) * η₀ * W.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hWt.ne, mul_assoc]
    rw [e1, e2]
    refine ENNReal.ofReal_le_ofReal ?_
    have hden : 0 < ((F.card : ℝ) + 1) * (W.toReal + 1) := by positivity
    have h3 : (F.card : ℝ) * W.toReal ≤ ((F.card : ℝ) + 1) * (W.toReal + 1) := by nlinarith
    have h4 : (F.card : ℝ) * η₀ * W.toReal = η₀ * ((F.card : ℝ) * W.toReal) := by ring
    rw [h4]
    calc η₀ * ((F.card : ℝ) * W.toReal) ≤ η₀ * (((F.card : ℝ) + 1) * (W.toReal + 1)) :=
          mul_le_mul_of_nonneg_left h3 hη₀pos.le
      _ = δ / 2 := by rw [hη₀]; field_simp
  have htail : ∑' z : ↑((F : Set (Fin d → ℤ))ᶜ), b z ≤ ENNReal.ofReal (δ / 2) := by
    have e : ∀ z : ↑((F : Set (Fin d → ℤ))ᶜ), b z = Kc * ENNReal.ofReal (cellWeight d z) := by
      intro z
      have hz : (z : Fin d → ℤ) ∉ F := z.2
      simp only [hb, hz, ite_false]
      have hcw : 0 ≤ cellWeight d z := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [ENNReal.ofReal_mul (by positivity), hKc]
      ring
    have h1 : ∑' z : ↑((F : Set (Fin d → ℤ))ᶜ), b z =
        Kc * ∑' z : ↑((F : Set (Fin d → ℤ))ᶜ), ENNReal.ofReal (cellWeight d z) := by
      rw [tsum_congr e]; exact ENNReal.tsum_mul_left
    have h2 : Kc * ∑' z : ↑((F : Set (Fin d → ℤ))ᶜ), ENNReal.ofReal (cellWeight d z) ≤ Kc * ε'' :=
      mul_le_mul' le_rfl hF.le
    have h3 : Kc * ε'' = ENNReal.ofReal (Kc.toReal * ((δ / 2) / (Kc.toReal + 1))) := by
      rw [hε'', ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKt.ne]
    have h4 : ENNReal.ofReal (Kc.toReal * ((δ / 2) / (Kc.toReal + 1))) ≤ ENNReal.ofReal (δ / 2) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hKr : 0 ≤ Kc.toReal := ENNReal.toReal_nonneg
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [h1]; exact h2.trans (h3.le.trans h4)
  have hsplit : ∑' z, b z = ∑ z ∈ F, b z + ∑' z : ↑((F : Set (Fin d → ℤ))ᶜ), b z :=
    (ENNReal.sum_add_tsum_compl F b).symm
  unfold cellL2Sum
  have hle : ∑' z : Fin d → ℤ, (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (h x ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ∑' z, b z := ENNReal.tsum_le_tsum hcb
  have hfin : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [hsplit] at hle
  exact hle.trans ((add_le_add hnear_sum htail).trans hfin.le)

end HRS.MH.AdjointRd.Phase2SA12Limit
