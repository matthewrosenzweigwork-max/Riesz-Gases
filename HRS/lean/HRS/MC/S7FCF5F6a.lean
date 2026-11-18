import HRS.MC.S7FCF5Defs
import HRS.MC.S7FCF5BD
import HRS.MC.S7FCW3F2

/-!
# Proof of F6a (`fcf5_F6a_B_section_moment`): `L^q` bound of one time section of `ℬ_N^t`

Route.  The coordinates of `quadFieldTilde` are the commutator modes `c_k = N F^{h_{e_k}}(X_t, μ^t)`.  F2
(`s7_FC_F2_B_proof`) gives `E |c_k|^q ≤ C ⟨k⟩^{2q}`; `‖ofSeq r c‖ₑ² ≤ ∑_k ⟨k⟩^{-2r} |c_k|²` holds for every `c`;
the deterministic weighted Jensen inequality `D1` (`fcf5_D1_weighted_sum_proof`) and `lintegral_tsum` bound
`E ‖ℬ̃‖ₑ^{q'}`.  The centring is pointwise: `‖∫F‖ₑ ≤ ∫⁻‖F‖ₑ`, and Jensen on the probability space bounds
`(∫⁻‖ℬ̃‖ₑ)^{q'}`.  `D1` needs `2 ≤ q'`, so the moment is proved for `q' = max q 2`, and `x^q ≤ 1 + x^{q'}`
transfers it to `q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5F

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The commutator coefficient of the mode `k` at time `t` (the integrand of F2). -/
def S7FCF5F_c (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (k : NonzeroLattice d)
    (ω : Ω) : ℝ :=
  (N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) (X t.toNNReal ω) (withDensityReal (R.ρ t))

/-- The (uncentred) quadratic field `ℬ̃_N^t` of the particle configuration at time `t`. -/
def S7FCF5F_B (R : Regime d) (r : ℝ) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ω : Ω) :
    NegSobolev d r :=
  quadFieldTilde r R.D.s (withDensityReal (R.ρ t)) (X t.toNNReal ω)

/-- The right-hand side of `D1` with `S_k = ‖c_k‖ₑ`, as a function of the coefficient sequence. -/
def S7FCF5F_H (d : ℕ) (r q : ℝ) (c : NonzeroLattice d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fcf5Z d r ^ (q / 2 - 1)) *
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k|) ^ q

/-- The constant `Z^{q/2-1} · C₂ · Z` with `Z = fcf5Z d r`. -/
def S7FCF5F_Ch (d : ℕ) (r q C2 : ℝ) : ℝ :=
  fcf5Z d r ^ (q / 2 - 1) * (C2 * fcf5Z d r)

/-- The final real constant `2^{q-1} (Ch + Ch)`. -/
def S7FCF5F_Cc (d : ℕ) (r q C2 : ℝ) : ℝ :=
  (2 : ℝ) ^ (q - 1) * (S7FCF5F_Ch d r q C2 + S7FCF5F_Ch d r q C2)

/-! ## Elementary helpers -/

theorem S7FCF5F_rpow_sq {x : ℝ} (hx : 0 < x) (m : ℝ) : (x ^ (-m)) ^ 2 = x ^ (-2 * m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

theorem S7FCF5F_exp_id {x : ℝ} (hx : 0 < x) (r q C2 : ℝ) :
    x ^ (4 - 2 * r - 2 * q) * (C2 * x ^ (2 * q)) = C2 * x ^ (4 - 2 * r) := by
  have e : x ^ (4 - 2 * r - 2 * q) * x ^ (2 * q) = x ^ (4 - 2 * r) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc x ^ (4 - 2 * r - 2 * q) * (C2 * x ^ (2 * q)) = C2 * (x ^ (4 - 2 * r - 2 * q) * x ^ (2 * q)) := by ring
    _ = C2 * x ^ (4 - 2 * r) := by rw [e]

theorem S7FCF5F_rpow_cancel (x : ℝ≥0∞) {q : ℝ} (hq : q ≠ 0) :
    (x ^ q) ^ (1 / q) = x ∧ (x ^ (1 / q)) ^ q = x := by
  constructor
  · rw [← ENNReal.rpow_mul, mul_one_div_cancel hq, ENNReal.rpow_one]
  · rw [← ENNReal.rpow_mul, one_div_mul_cancel hq, ENNReal.rpow_one]

theorem S7FCF5F_two_rpow (p : ℝ) (hp : 0 ≤ p) : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp, ENNReal.ofReal_ofNat]

theorem S7FCF5F_rpow_le_one_add (x : ℝ≥0∞) {q q' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') :
    x ^ q ≤ 1 + x ^ q' := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hq).trans le_self_add
  · have h1 : 1 ≤ x := le_of_lt (not_le.1 hx)
    exact (ENNReal.rpow_le_rpow_of_exponent_le h1 hqq).trans le_add_self

theorem S7FCF5F_Cc_nonneg (r q C2 : ℝ) (hC2 : 0 ≤ C2) : 0 ≤ S7FCF5F_Cc d r q C2 := by
  have hZ : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hCh : 0 ≤ S7FCF5F_Ch d r q C2 :=
    mul_nonneg (Real.rpow_nonneg hZ _) (mul_nonneg hC2 hZ)
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg hCh hCh)

/-! ## The `ℓ²`-norm of an embedded sequence -/

/-- `‖ofSeq m c‖ₑ² ≤ ∑_k ⟨k⟩^{-2m} |c_k|²` for every `c` (equality when the weighted sequence is in `ℓ²`,
and `ofSeq = 0` otherwise). -/
theorem S7FCF5F_enorm_sq_le (m : ℝ) (c : NonzeroLattice d → ℝ) :
    ‖(NegSobolev.ofSeq m c : NegSobolev d m)‖ₑ ^ 2 ≤
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * (ENNReal.ofReal |c k|) ^ 2 := by
  by_cases h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2
  · have hF := NegSobolev.coord_sq (NegSobolev.ofSeq m c : NegSobolev d m)
    have hcoord : ∀ k, NegSobolev.coord (NegSobolev.ofSeq m c : NegSobolev d m) k =
        Lattice.jp k.1 ^ (-m) * c k := fun k => NegSobolev.coord_ofSeq_of_mem c h k
    have hsum : Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * m) * c k ^ 2) := by
      refine hF.1.congr fun k => ?_
      rw [hcoord k, mul_pow, S7FCF5F_rpow_sq (Torus.jp_pos k.1) m]
    have hnorm : ‖(NegSobolev.ofSeq m c : NegSobolev d m)‖ ^ 2 =
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * m) * c k ^ 2 := by
      rw [hF.2]
      exact tsum_congr fun k => by rw [hcoord k, mul_pow, S7FCF5F_rpow_sq (Torus.jp_pos k.1) m]
    refine le_of_eq ?_
    calc ‖(NegSobolev.ofSeq m c : NegSobolev d m)‖ₑ ^ 2
        = ENNReal.ofReal (‖(NegSobolev.ofSeq m c : NegSobolev d m)‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ = ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * m) * c k ^ 2) := by rw [hnorm]
      _ = ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * c k ^ 2) :=
          ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _))
            hsum
      _ = ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * (ENNReal.ofReal |c k|) ^ 2 :=
          tsum_congr fun k => by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
              ENNReal.ofReal_mul (Real.rpow_nonneg (Torus.jp_pos k.1).le _)]
  · have h0 : (NegSobolev.ofSeq m c : NegSobolev d m) = 0 := by
      unfold NegSobolev.ofSeq
      exact dif_neg h
    rw [h0, enorm_zero]
    simp

/-! ## Jensen on a probability space -/

/-- Jensen (Hölder with the constant function `1`): `(∫⁻ K)^p ≤ ∫⁻ K^p` on a probability space, `p > 1`. -/
theorem S7FCF5F_jensen {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : Ω → ℝ≥0∞} (hK : Measurable K) {p : ℝ} (hp : 1 < p) :
    (∫⁻ ω, K ω ∂P) ^ p ≤ ∫⁻ ω, K ω ^ p ∂P := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have h1 : ∫⁻ ω, K ω ∂P ≤ (∫⁻ ω, K ω ^ p ∂P) ^ (1 / p) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hK.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simpa using h
  have hp0 : p ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  calc (∫⁻ ω, K ω ∂P) ^ p ≤ ((∫⁻ ω, K ω ^ p ∂P) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h1 (by linarith)
    _ = ∫⁻ ω, K ω ^ p ∂P := (S7FCF5F_rpow_cancel _ hp0).2

/-! ## The weighted-sum bound -/

theorem S7FCF5F_H_meas {Ω : Type} [MeasurableSpace Ω] (r q : ℝ) (c : NonzeroLattice d → Ω → ℝ)
    (hc : ∀ k, Measurable (c k)) :
    Measurable (fun ω => S7FCF5F_H d r q (fun k => c k ω)) := by
  unfold S7FCF5F_H
  refine measurable_const.mul (Measurable.ennreal_tsum (f := fun (k : NonzeroLattice d) (ω : Ω) =>
    ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k ω|) ^ q) fun k => ?_)
  exact measurable_const.mul (((continuous_abs.measurable.comp (hc k)).ennreal_ofReal).pow_const q)

/-- The `L^1`-type bound of `H`, from F2 coefficientwise. -/
theorem S7FCF5F_H_lint {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (r q C2 : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    (hq : 2 ≤ q) (hC2 : 0 ≤ C2) (c : NonzeroLattice d → Ω → ℝ) (hc : ∀ k, Measurable (c k))
    (hF : ∀ k : NonzeroLattice d, Integrable (fun ω => |c k ω| ^ q) P ∧
      ∫ ω, |c k ω| ^ q ∂P ≤ C2 * Lattice.jp k.1 ^ (2 * q)) :
    ∫⁻ ω, S7FCF5F_H d r q (fun k => c k ω) ∂P ≤ ENNReal.ofReal (S7FCF5F_Ch d r q C2) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hsum : Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r)) :=
    HRS.MC.Sec7.S7FCF5B.fcf5_D1a_summable_proof r hr
  have hZ : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _
  have hZp : 0 ≤ fcf5Z d r ^ (q / 2 - 1) := Real.rpow_nonneg hZ _
  have hmk : ∀ k : NonzeroLattice d, Measurable (fun ω => |c k ω|) :=
    fun k => continuous_abs.measurable.comp (hc k)
  have hterm : ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k ω|) ^ q ∂P ≤
        ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r)) := by
    intro k
    obtain ⟨hint, hbd⟩ := hF k
    have ha : 0 ≤ Lattice.jp k.1 ^ (4 - 2 * r - 2 * q) := Real.rpow_nonneg (hjp k).le _
    have hnn : 0 ≤ᵐ[P] fun ω => |c k ω| ^ q :=
      ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _
    have e1 : ∀ ω, (ENNReal.ofReal |c k ω|) ^ q = ENNReal.ofReal (|c k ω| ^ q) := fun ω =>
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0
    simp only [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
      ← ENNReal.ofReal_mul ha]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← S7FCF5F_exp_id (hjp k) r q C2]
    exact mul_le_mul_of_nonneg_left hbd ha
  have hT : ∑' k : NonzeroLattice d, ENNReal.ofReal (C2 * Lattice.jp k.1 ^ (4 - 2 * r)) =
      ENNReal.ofReal (C2 * fcf5Z d r) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (f := fun k : NonzeroLattice d => C2 * Lattice.jp k.1 ^ (4 - 2 * r))
      (fun k => mul_nonneg hC2 (Real.rpow_nonneg (hjp k).le _)) (hsum.mul_left C2), tsum_mul_left]
    rfl
  dsimp only [S7FCF5F_H]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum (f := fun (k : NonzeroLattice d) (ω : Ω) =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k ω|) ^ q) fun k =>
      (measurable_const.mul (((continuous_abs.measurable.comp (hc k)).ennreal_ofReal).pow_const q)).aemeasurable]
  dsimp only [S7FCF5F_Ch]
  refine le_trans (mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hterm) zero_le) ?_
  rw [hT, ENNReal.ofReal_mul hZp]

/-- The centring and Jensen step: with `B = ‖ℬ̃‖ₑ`, `(∫⁻ B)^q ≤ ∫⁻ H` and `∫⁻ Z^q ≤ 2^{q-1}(∫⁻ H + (∫⁻ B)^q)`
whenever `B^q ≤ H` (`H` measurable) and `Z ≤ B + ∫⁻ B`. -/
theorem S7FCF5F_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B H Z : Ω → ℝ≥0∞) {q : ℝ} (hq : 1 < q) (hH : Measurable H) (hBH : ∀ ω, B ω ^ q ≤ H ω)
    (hZ : ∀ ω, Z ω ≤ B ω + ∫⁻ ω', B ω' ∂P) :
    (∫⁻ ω, B ω ∂P) ^ q ≤ ∫⁻ ω, H ω ∂P ∧
      ∫⁻ ω, Z ω ^ q ∂P ≤ (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, H ω ∂P + (∫⁻ ω', B ω' ∂P) ^ q) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hq1 : q ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hK : ∀ ω, B ω ≤ H ω ^ (1 / q) := fun ω => by
    calc B ω = (B ω ^ q) ^ (1 / q) := (S7FCF5F_rpow_cancel _ hq1).1.symm
      _ ≤ H ω ^ (1 / q) := ENNReal.rpow_le_rpow (hBH ω) (div_nonneg zero_le_one hq0)
  have hβ : ∫⁻ ω, B ω ∂P ≤ ∫⁻ ω, H ω ^ (1 / q) ∂P := lintegral_mono hK
  have hJ := S7FCF5F_jensen P (hH.pow_const (1 / q)) hq
  have hJ' : ∫⁻ ω, (H ω ^ (1 / q)) ^ q ∂P = ∫⁻ ω, H ω ∂P :=
    lintegral_congr fun ω => (S7FCF5F_rpow_cancel _ hq1).2
  have hβq : (∫⁻ ω, B ω ∂P) ^ q ≤ ∫⁻ ω, H ω ∂P :=
    (ENNReal.rpow_le_rpow hβ hq0).trans (hJ.trans hJ'.le)
  refine ⟨hβq, ?_⟩
  have hpt : ∀ ω, Z ω ^ q ≤ (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) := by
    intro ω
    calc Z ω ^ q ≤ (B ω + ∫⁻ ω', B ω' ∂P) ^ q := ENNReal.rpow_le_rpow (hZ ω) hq0
      _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (B ω ^ q + (∫⁻ ω', B ω' ∂P) ^ q) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq.le
      _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) :=
          mul_le_mul_of_nonneg_left (add_le_add (hBH ω) le_rfl) zero_le
  calc ∫⁻ ω, Z ω ^ q ∂P
      ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) ∂P := lintegral_mono hpt
    _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, H ω ∂P + (∫⁻ ω', B ω' ∂P) ^ q) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top),
          lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-! ## The core estimate (exponent `q ≥ 2`) -/

theorem S7FCF5F_core (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ht : 0 ≤ t) (hXt : Measurable (X t.toNNReal))
    (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hF2 : ∀ k : NonzeroLattice d, Integrable (fun ω => |S7FCF5F_c R X t k ω| ^ q) P ∧
      ∫ ω, |S7FCF5F_c R X t k ω| ^ q ∂P ≤ C2 * Lattice.jp k.1 ^ (2 * q)) :
    ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (S7FCF5F_Cc d r q C2) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hq2 : (0 : ℝ) ≤ q / 2 := by linarith
  have hq1 : q ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hZ0 : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _
  have hsd : R.D.s < d := alltime_hsd R
  have hρ : IsProbDensity (R.ρ t) := (alltime_traj R t).mf.density t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal hρ
  -- measurability of the coefficients
  have hcm : ∀ k : NonzeroLattice d, Measurable (fun ω => S7FCF5F_c R X t k ω) := by
    intro k
    have hh := (HRS.MC.Sec7.S7FCW3.s7fcw3_hT_meas_symm hsd (HRS.FieldSingAux.isSmooth_realMode k)).1
    have hME := HRS.MC.Sec7.S7FCW3.s7fcw3_me_meas (N := N) (hTransport d R.D.s (Torus.realMode k)) hh
      (withDensityReal (R.ρ t))
    exact (hME.comp hXt).const_mul (N : ℝ)
  -- the bound of the norm of one section by `H`
  have hnormB : ∀ ω, ‖S7FCF5F_B R r X t ω‖ₑ ^ q ≤ S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω) := by
    intro ω
    have h1 : ‖S7FCF5F_B R r X t ω‖ₑ ^ 2 ≤
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) *
          (ENNReal.ofReal |S7FCF5F_c R X t k ω|) ^ 2 :=
      S7FCF5F_enorm_sq_le r (fun k => S7FCF5F_c R X t k ω)
    have h2 : ‖S7FCF5F_B R r X t ω‖ₑ ^ q = (‖S7FCF5F_B R r X t ω‖ₑ ^ 2) ^ (q / 2) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    have h3 := HRS.MC.Sec7.S7FCF5B.fcf5_D1_weighted_sum_proof (d := d) r hr q hq
      (fun k => ENNReal.ofReal |S7FCF5F_c R X t k ω|)
    rw [h2]
    exact (ENNReal.rpow_le_rpow h1 hq2).trans h3
  -- the bound of the norm of one section by `H`, centring and Jensen
  have hHm : Measurable (fun ω => S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω)) :=
    S7FCF5F_H_meas r q (fun k ω => S7FCF5F_c R X t k ω) hcm
  have hHint : ∫⁻ ω, S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω) ∂P ≤
      ENNReal.ofReal (S7FCF5F_Ch d r q C2) :=
    S7FCF5F_H_lint P r q C2 hr hq hC2 (fun k ω => S7FCF5F_c R X t k ω) hcm hF2
  have hZ : ∀ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ≤
      ‖S7FCF5F_B R r X t ω‖ₑ + ∫⁻ ω', ‖S7FCF5F_B R r X t ω'‖ₑ ∂P := by
    intro ω
    show ‖S7FCF5F_B R r X t ω - ∫ ω', S7FCF5F_B R r X t ω' ∂P‖ₑ ≤ _
    exact enorm_sub_le.trans (add_le_add le_rfl (enorm_integral_le_lintegral_enorm (S7FCF5F_B R r X t)))
  obtain ⟨hβq, hmain⟩ := S7FCF5F_tail P (fun ω => ‖S7FCF5F_B R r X t ω‖ₑ)
    (fun ω => S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω))
    (fun ω => ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ)
    (by linarith : 1 < q) hHm hnormB hZ
  have hCh : 0 ≤ S7FCF5F_Ch d r q C2 := mul_nonneg (Real.rpow_nonneg hZ0 _) (mul_nonneg hC2 hZ0)
  unfold S7FCF5F_Cc
  calc ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ q ∂P
      ≤ (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω) ∂P +
          (∫⁻ ω', ‖S7FCF5F_B R r X t ω'‖ₑ ∂P) ^ q) := hmain
    _ = ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * (∫⁻ ω, S7FCF5F_H d r q (fun k => S7FCF5F_c R X t k ω) ∂P +
          (∫⁻ ω', ‖S7FCF5F_B R r X t ω'‖ₑ ∂P) ^ q) := by
        rw [S7FCF5F_two_rpow (q - 1) (by linarith)]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * (ENNReal.ofReal (S7FCF5F_Ch d r q C2) +
          ENNReal.ofReal (S7FCF5F_Ch d r q C2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hHint (hβq.trans hHint)) zero_le
    _ = ENNReal.ofReal ((2 : ℝ) ^ (q - 1) * (S7FCF5F_Ch d r q C2 + S7FCF5F_Ch d r q C2)) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ENNReal.ofReal_add hCh hCh]

/-! ## Assembly: F6a for every `q ≥ 1` -/

theorem fcf5_F6a_B_section_moment_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      FCPrepared R P X₀ W X → ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal C := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  obtain ⟨C2, hC2⟩ := HRS.MC.Sec7.S7FCW3.s7_FC_F2_B_proof R (max q 2) (le_trans hq (le_max_left _ _))
  refine ⟨1 + S7FCF5F_Cc d r (max q 2) (max C2 0), ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep t ht
  have hXt : Measurable (X t.toNNReal) := (hprep.solution t).adapted t.toNNReal
  have hF2 : ∀ k : NonzeroLattice d, Integrable (fun ω => |S7FCF5F_c R X t k ω| ^ (max q 2)) P ∧
      ∫ ω, |S7FCF5F_c R X t k ω| ^ (max q 2) ∂P ≤ max C2 0 * Lattice.jp k.1 ^ (2 * max q 2) := by
    intro k
    obtain ⟨hi, hb⟩ := hC2 N hN P X₀ W X hprep t ht k
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Torus.jp_pos k.1).le _))⟩
  have hcore := S7FCF5F_core R r hr (max q 2) (le_max_right _ _) P X t ht hXt (max C2 0)
    (le_max_right _ _) hF2
  have hCc : 0 ≤ S7FCF5F_Cc d r (max q 2) (max C2 0) :=
    S7FCF5F_Cc_nonneg r (max q 2) (max C2 0) (le_max_right _ _)
  calc ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ q ∂P
      ≤ ∫⁻ ω, (1 + ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ (max q 2)) ∂P :=
        lintegral_mono fun ω => S7FCF5F_rpow_le_one_add _ hq0 (le_max_left _ _)
    _ = 1 + ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X t ω‖ₑ ^ (max q 2) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal (S7FCF5F_Cc d r (max q 2) (max C2 0)) := add_le_add le_rfl hcore
    _ = ENNReal.ofReal (1 + S7FCF5F_Cc d r (max q 2) (max C2 0)) := by
        rw [ENNReal.ofReal_add zero_le_one hCc, ENNReal.ofReal_one]

end HRS.MC.Sec7.S7FCF5F

end
