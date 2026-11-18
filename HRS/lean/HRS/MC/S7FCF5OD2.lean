import HRS.MC.S7FCF5MC1b
import HRS.MC.S7FCF5BD
import HRS.MC.S7FCF5F6a

/-!
# Proof of D2 (`fcf5_D2_Shat_moment`): the `L^q` bound of the `E_r`-supremum over the window

Route.  For every `t`, the `E_r`-norm of `etaE` is `√N` times the norm of the embedded sequence of the coefficients
`⟨k⟩^{-r} (μ_N(e_k) - μ^t(e_k))`, so `‖η^t‖ₑ² ≤ ∑_k ⟨k⟩^{-2r} |η^t(e_k)|²` (`S7FCF5F_enorm_sq_le`).  Bounding
each `|η^t(e_k)|` by the window supremum `S_k` of the mode `e_k` (for rational `t`) and taking the supremum over
the countable window times gives `Ŝ² ≤ ∑_k ⟨k⟩^{-2r} S_k²`.  The deterministic weighted Jensen inequality `D1`
gives `Ŝ^{q'} ≤ Z^{q'/2-1} ∑_k ⟨k⟩^{4-2r-2q'} S_k^{q'}` with `q' = max q 2 ≥ 2`; `lintegral_tsum` (measurability of
`S_k` from `S7FCF5M_fixed_meas`) and C1b at exponent `q'` bound its moment by `Z^{q'/2-1} Z C`.  Finally
`x^q ≤ 1 + x^{q'}` transfers the bound to `q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5O

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The window supremum of the `k`-th mode `S_k = sup_{t ∈ a+ℚ∩[0,T]} ‖η_N^t(e_k)‖ₑ` (the quantity of C1b). -/
def S7FCF5O_Sk (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (a T : ℝ)
    (k : NonzeroLattice d) (ω : Ω) : ℝ≥0∞ :=
  ⨆ s ∈ fcf5Rat a T, ‖fcf5Eta R X (Torus.realMode k) s ω‖ₑ

/-- `N · |c|² = ‖√N · c‖ₑ²` (the scalar `√N` of `etaE`, squared). -/
theorem S7FCF5O_sqrt_term (N : ℕ) (c : ℝ) :
    ENNReal.ofReal N * (ENNReal.ofReal |c|) ^ 2 = ‖Real.sqrt N * c‖ₑ ^ 2 := by
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (N : ℝ)),
    ENNReal.ofReal_mul (Real.sqrt_nonneg (N : ℝ)), mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg (N : ℝ)),
    Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The `E_r`-norm of `etaE` as a weighted sum of the squared mode coefficients:
`‖√N (μ_N - μ)‖ₑ² ≤ ∑_k ⟨k⟩^{-2m} ‖√N (μ_N(e_k) - μ(e_k))‖ₑ²`. -/
theorem S7FCF5O_etaE_sq_le (m : ℝ) {N : ℕ} (Y : Config d N) (μ : Measure (Torus d)) :
    ‖etaE m Y μ‖ₑ ^ 2 ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) *
      ‖Real.sqrt N * (pair (empirical Y) (Torus.realMode k) - pair μ (Torus.realMode k))‖ₑ ^ 2 := by
  set c : NonzeroLattice d → ℝ := fun k =>
    Torus.measureRealCoeff (empirical Y) k - Torus.measureRealCoeff μ k with hc
  set F : NegSobolev d m := NegSobolev.ofSeq m c with hFdef
  have hF : etaE m Y μ = Real.sqrt N • F := rfl
  have hsq := HRS.MC.Sec7.S7FCF5F.S7FCF5F_enorm_sq_le m c
  have h1 : ‖etaE m Y μ‖ₑ ^ 2 = ENNReal.ofReal (‖etaE m Y μ‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h2 : ‖F‖ₑ ^ 2 = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h3 : ‖etaE m Y μ‖ ^ 2 = N * ‖F‖ ^ 2 := by
    rw [hF, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnorm : ‖etaE m Y μ‖ₑ ^ 2 = ENNReal.ofReal N * ‖F‖ₑ ^ 2 := by
    rw [h1, h2, h3, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc ‖etaE m Y μ‖ₑ ^ 2 = ENNReal.ofReal N * ‖F‖ₑ ^ 2 := hnorm
    _ ≤ ENNReal.ofReal N * ∑' k : NonzeroLattice d,
          ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * (ENNReal.ofReal |c k|) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq zero_le
    _ = ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) *
          ‖Real.sqrt N * (pair (empirical Y) (Torus.realMode k) - pair μ (Torus.realMode k))‖ₑ ^ 2 := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun k => ?_
        calc ENNReal.ofReal N * (ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * (ENNReal.ofReal |c k|) ^ 2)
            = ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * (ENNReal.ofReal N * (ENNReal.ofReal |c k|) ^ 2) := by
              ring
          _ = ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) *
                ‖Real.sqrt N * (pair (empirical Y) (Torus.realMode k) - pair μ (Torus.realMode k))‖ₑ ^ 2 := by
              exact congrArg (fun x => ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m)) * x)
                (S7FCF5O_sqrt_term N (c k))

/-- The rational power identity: `ofReal (x^(A-B)) · ofReal (c x^B) = ofReal (x^A) · ofReal c` for `x > 0`. -/
theorem S7FCF5O_term (x c A B : ℝ) (hx : 0 < x) (hc : 0 ≤ c) :
    ENNReal.ofReal (x ^ (A - B)) * ENNReal.ofReal (c * x ^ B) = ENNReal.ofReal (x ^ A) * ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _)]
  congr 1
  have e : x ^ (A - B) * x ^ B = x ^ A := by
    rw [← Real.rpow_add hx, sub_add_cancel]
  calc x ^ (A - B) * (c * x ^ B) = c * (x ^ (A - B) * x ^ B) := by ring
    _ = x ^ A * c := by rw [e]; ring

/-- Measurability of the window supremum of one mode (countable supremum of `S7FCF5M_fixed_meas`). -/
theorem S7FCF5O_Sk_meas (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : FCPrepared R P X₀ W X) (a T : ℝ) (ha : 0 ≤ a) (k : NonzeroLattice d) :
    Measurable (S7FCF5O_Sk R X a T k) := by
  haveI : Countable (fcf5Rat a T) := (HRS.MC.Sec7.S7FCF5M.S7FCF5M_rat_countable a T).to_subtype
  have hk : Measurable (Torus.realMode k : Torus d → ℝ) :=
    (HRS.FieldSingAux.continuous_realMode k).measurable
  have hterm : ∀ s : fcf5Rat a T, Measurable fun ω => ‖fcf5Eta R X (Torus.realMode k) s.1 ω‖ₑ :=
    fun s => HRS.MC.Sec7.S7FCF5M.S7FCF5M_fixed_meas R P X₀ W X hprep (Torus.realMode k) hk (Real.sqrt 2)
      (fun x => Torus.abs_realMode_le k x) (t := s.1)
      (le_trans ha (HRS.MC.Sec7.S7FCF5M.S7FCF5M_rat_mem s.2).1)
  have heq : S7FCF5O_Sk R X a T k = fun ω => ⨆ s : fcf5Rat a T, ‖fcf5Eta R X (Torus.realMode k) s.1 ω‖ₑ := by
    funext ω
    exact (iSup_subtype'' (fcf5Rat a T) (fun t => ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ)).symm
  rw [heq]
  exact Measurable.iSup fun s => hterm s

theorem fcf5_D2_Shat_moment_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      FCPrepared R P X₀ W X → ∀ a : ℝ, 0 ≤ a →
        ∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P ≤ ENNReal.ofReal C := by
  -- the exponent `q' = max q 2` (D1 needs `2 ≤ q'`)
  obtain ⟨q', hq'def⟩ : ∃ q' : ℝ, q' = max q 2 := ⟨_, rfl⟩
  have hq'2 : 2 ≤ q' := by rw [hq'def]; exact le_max_right _ _
  have hqq' : q ≤ q' := by rw [hq'def]; exact le_max_left _ _
  have hq'1 : 1 ≤ q' := by linarith
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨Cb, hCb⟩ := HRS.MC.Sec7.S7FCF5M.fcf5_C1b_mode_sup_proof R T hT q' hq'1
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (4 - 2 * r) :=
    HRS.MC.Sec7.S7FCF5B.fcf5_D1a_summable_proof r hr
  have hZ : 0 ≤ fcf5Z d r := tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _
  have hZeq : ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) =
      ENNReal.ofReal (fcf5Z d r) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg (hjp k).le _) hsum).symm
  obtain ⟨Cb', hCb'def⟩ : ∃ C : ℝ, C = max Cb 0 := ⟨_, rfl⟩
  have hCb'0 : 0 ≤ Cb' := by rw [hCb'def]; exact le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = fcf5Z d r ^ (q' / 2 - 1) * (fcf5Z d r * Cb') := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (Real.rpow_nonneg hZ _) (mul_nonneg hZ hCb'0)
  refine ⟨1 + K, ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep a ha
  -- (1) pointwise: the `E_r`-supremum is at most the weighted `ℓ²`-sum of the mode suprema
  have hŜ : ∀ ω, fcf5Shat R r a T X ω ≤
      (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * S7FCF5O_Sk R X a T k ω ^ 2) ^
        (1 / 2 : ℝ) := by
    intro ω
    unfold fcf5Shat
    refine iSup₂_le fun t ht => ?_
    have hsq : ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ ^ 2 ≤
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * S7FCF5O_Sk R X a T k ω ^ 2 := by
      refine (S7FCF5O_etaE_sq_le r (X t.toNNReal ω) (withDensityReal (R.ρ t))).trans ?_
      refine ENNReal.tsum_le_tsum fun k => ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left' ?_ 2) zero_le
      show ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ ≤ ⨆ s ∈ fcf5Rat a T, ‖fcf5Eta R X (Torus.realMode k) s ω‖ₑ
      exact le_iSup_of_le t (le_iSup (fun _ : t ∈ fcf5Rat a T => ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ) ht)
    calc ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ
        = (‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow hsq (by norm_num)
  -- (2) the deterministic weighted Jensen inequality D1 at exponent `q'`
  have hD1 : ∀ ω, fcf5Shat R r a T X ω ^ q' ≤
      ENNReal.ofReal (fcf5Z d r ^ (q' / 2 - 1)) *
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) *
          S7FCF5O_Sk R X a T k ω ^ q' := by
    intro ω
    calc fcf5Shat R r a T X ω ^ q'
        ≤ ((∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) *
            S7FCF5O_Sk R X a T k ω ^ 2) ^ (1 / 2 : ℝ)) ^ q' :=
          ENNReal.rpow_le_rpow (hŜ ω) (by linarith)
      _ = (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) *
            S7FCF5O_Sk R X a T k ω ^ 2) ^ (q' / 2) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
      _ ≤ _ := HRS.MC.Sec7.S7FCF5B.fcf5_D1_weighted_sum_proof r hr q' hq'2 (fun k => S7FCF5O_Sk R X a T k ω)
  -- (3) moments of the mode suprema (C1b at exponent `q'`) and the `k`-sum
  have hSk_meas : ∀ k : NonzeroLattice d, Measurable (S7FCF5O_Sk R X a T k) :=
    fun k => S7FCF5O_Sk_meas R P X₀ W X hprep a T ha k
  have hCk : ∀ k : NonzeroLattice d,
      ∫⁻ ω, S7FCF5O_Sk R X a T k ω ^ q' ∂P ≤ ENNReal.ofReal (Cb' * Lattice.jp k.1 ^ (2 * q')) := fun k =>
    (hCb N hN P X₀ W X hprep a ha k).trans (ENNReal.ofReal_le_ofReal
      (by rw [hCb'def]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hjp k).le _)))
  have hper : ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) * S7FCF5O_Sk R X a T k ω ^ q' ∂P ≤
        ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) * ENNReal.ofReal Cb' := fun k => by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) * ∫⁻ ω, S7FCF5O_Sk R X a T k ω ^ q' ∂P
        ≤ ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) *
            ENNReal.ofReal (Cb' * Lattice.jp k.1 ^ (2 * q')) := mul_le_mul_of_nonneg_left (hCk k) zero_le
      _ = ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) * ENNReal.ofReal Cb' :=
          S7FCF5O_term (Lattice.jp k.1) Cb' (4 - 2 * r) (2 * q') (hjp k) hCb'0
  have hG : ∫⁻ ω, fcf5Shat R r a T X ω ^ q' ∂P ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, fcf5Shat R r a T X ω ^ q' ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (fcf5Z d r ^ (q' / 2 - 1)) *
            ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) *
              S7FCF5O_Sk R X a T k ω ^ q' ∂P := lintegral_mono hD1
      _ = ENNReal.ofReal (fcf5Z d r ^ (q' / 2 - 1)) *
            ∑' k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q')) *
              S7FCF5O_Sk R X a T k ω ^ q' ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_tsum fun k => ((((hSk_meas k).pow_const q').const_mul _).aemeasurable)]
      _ ≤ ENNReal.ofReal (fcf5Z d r ^ (q' / 2 - 1)) *
            ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r)) * ENNReal.ofReal Cb' :=
          mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hper) zero_le
      _ = ENNReal.ofReal K := by
          rw [ENNReal.tsum_mul_right, hZeq, hK, ENNReal.ofReal_mul (Real.rpow_nonneg hZ _),
            ENNReal.ofReal_mul hZ]
  -- (4) from `q'` to `q` by `x^q ≤ 1 + x^{q'}`
  have hfin : ∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P ≤ ENNReal.ofReal (1 + K) := by
    calc ∫⁻ ω, fcf5Shat R r a T X ω ^ q ∂P
        ≤ ∫⁻ ω, (1 + fcf5Shat R r a T X ω ^ q') ∂P :=
          lintegral_mono fun ω => HRS.MC.Sec7.S7FCF5F.S7FCF5F_rpow_le_one_add _ hq0 hqq'
      _ = 1 + ∫⁻ ω, fcf5Shat R r a T X ω ^ q' ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal K := add_le_add le_rfl hG
      _ = ENNReal.ofReal (1 + K) := by
          rw [ENNReal.ofReal_add zero_le_one hK0, ENNReal.ofReal_one]
  exact hfin

end HRS.MC.Sec7.S7FCF5O

end
