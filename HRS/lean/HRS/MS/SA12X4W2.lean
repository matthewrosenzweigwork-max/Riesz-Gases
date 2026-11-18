import HRS.MS.SA12X3C15K
import HRS.MS.SA12Z3NearN7E

/-!
# S.A.12 (SA12X4) W2: weight comparability on the fine lattice and rescaling of the regime parameter `ν₀`

* `sa12x4_jbracket_peetre`: `⟨x-y⟩^{-p} ≤ (√2⟨y⟩)^p ⟨x⟩^{-p}` for `wt_z = ⟨cellPt z⟩^{-(d+3)}` (Peetre).
* `sa12x4_shift_weight`: `∑_z wt_z ∑_{k∈E} u(z+k) ≤ c_E ∑_z wt_z u(z)` for `u ≥ 0`.
* `sa12x4_regime_scale`: the regime survives `ν₀ ↦ qν₀` (`0 < q ≤ 1`) and the rate changes by a factor depending only on `q, θ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12x4_jbracket_peetre (p : ℝ) (hp : 0 ≤ p) (x y : Euc d) :
    jbracket (x - y) ^ (-p) ≤ (Real.sqrt 2 * jbracket y) ^ p * jbracket x ^ (-p) := by
  have h1 : ∀ v : Euc d, 1 ≤ jbracket v := fun v => by
    unfold jbracket
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖v‖])
  have hx0 : 0 < jbracket x := lt_of_lt_of_le one_pos (h1 x)
  have hxy0 : 0 < jbracket (x - y) := lt_of_lt_of_le one_pos (h1 (x - y))
  have hy0 : 0 < jbracket y := lt_of_lt_of_le one_pos (h1 y)
  have hpe : jbracket x ≤ Real.sqrt 2 * jbracket y * jbracket (x - y) := by
    unfold jbracket
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hn : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      have := norm_add_le (x - y) y
      simpa using this
    have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have h0' : 0 ≤ ‖y‖ := norm_nonneg _
    have : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), norm_nonneg x]
    nlinarith [sq_nonneg (‖x - y‖ * ‖y‖)]
  have h2 : jbracket x ^ p ≤ (Real.sqrt 2 * jbracket y) ^ p * jbracket (x - y) ^ p := by
    rw [← Real.mul_rpow (by positivity) hxy0.le]
    exact Real.rpow_le_rpow hx0.le hpe hp
  rw [Real.rpow_neg hxy0.le, Real.rpow_neg hx0.le]
  have hxp : 0 < jbracket x ^ p := Real.rpow_pos_of_pos hx0 p
  have hxyp : 0 < jbracket (x - y) ^ p := Real.rpow_pos_of_pos hxy0 p
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hxyp hxp]
  nlinarith [h2]

theorem sa12x4_shift_weight (E : Finset (Fin d → ℤ)) :
    ∃ cE : ℝ, 0 ≤ cE ∧ ∀ u : (Fin d → ℤ) → ℝ≥0∞,
      ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ∑ k ∈ E, u (z + k) ≤
        ENNReal.ofReal cE * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * u z := by
  classical
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set wt : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-p)) with hwt
  set c : (Fin d → ℤ) → ℝ := fun k => (Real.sqrt 2 * jbracket (cellPt d k)) ^ p with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    rw [hc]; exact Real.rpow_nonneg (by unfold jbracket; positivity) _
  refine ⟨∑ k ∈ E, c k, Finset.sum_nonneg fun k _ => hc0 k, fun u => ?_⟩
  have hshift : ∀ k : Fin d → ℤ, ∑' z, wt z * u (z + k) ≤ ENNReal.ofReal (c k) * ∑' z, wt z * u z := by
    intro k
    have e1 : ∑' z, wt z * u (z + k) = ∑' z, wt (z - k) * u z := by
      rw [← (Equiv.addRight k).tsum_eq (fun z' => wt (z' - k) * u z')]
      refine tsum_congr fun z => ?_
      simp
    rw [e1, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun z => ?_
    rw [← mul_assoc]
    gcongr
    have hpe := sa12x4_jbracket_peetre p hp0 (cellPt d z) (cellPt d k)
    have : cellPt d z - cellPt d k = cellPt d (z - k) := by
      have := HRS.MH.AdjointRd.Phase2SA12Near.sa12z3_cellPt_add (d := d) (z - k) k
      rw [sub_add_cancel] at this
      rw [this]; abel
    rw [this] at hpe
    simp only [hwt]
    rw [← ENNReal.ofReal_mul (hc0 k)]
    exact ENNReal.ofReal_le_ofReal (by simp only [hc]; exact hpe)
  calc ∑' z, wt z * ∑ k ∈ E, u (z + k) = ∑' z, ∑ k ∈ E, wt z * u (z + k) :=
        tsum_congr fun z => Finset.mul_sum _ _ _
    _ = ∑ k ∈ E, ∑' z, wt z * u (z + k) := (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable))
    _ ≤ ∑ k ∈ E, ENNReal.ofReal (c k) * ∑' z, wt z * u z := Finset.sum_le_sum fun k _ => hshift k
    _ = ENNReal.ofReal (∑ k ∈ E, c k) * ∑' z, wt z * u z := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun k _ => hc0 k]

theorem sa12x4_regime_scale {Rg : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν ν₀ : ℝ}
    (hR : RdRegimeHolds Rg d s M ν ν₀) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (θ : ℝ) :
    RdRegimeHolds Rg d s M ν (q * ν₀) ∧
      ∀ C : ℝ, 0 ≤ C →
        Rg.lambdaM C (q * ν₀) θ ≤ Rg.lambdaM (max 1 (q ^ (-(θ / (2 - θ)))) * C) ν₀ θ := by
  cases Rg with
  | R3 =>
    obtain ⟨h1, h2, h3⟩ := hR
    refine ⟨⟨h1, mul_pos hq0 h2, by nlinarith⟩, fun C hC => ?_⟩
    show C * (1 + (q * ν₀) ^ (-(θ / (2 - θ)))) ≤ (max 1 (q ^ (-(θ / (2 - θ)))) * C) * (1 + ν₀ ^ (-(θ / (2 - θ))))
    rw [Real.mul_rpow hq0.le h2.le]
    set e := -(θ / (2 - θ)) with he
    have hu : 0 < ν₀ ^ e := Real.rpow_pos_of_pos h2 e
    have hqe : 0 < q ^ e := Real.rpow_pos_of_pos hq0 e
    set K := max 1 (q ^ e) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    have hKq : q ^ e ≤ K := le_max_right _ _
    nlinarith [mul_nonneg hC (sub_nonneg.2 hK1), mul_nonneg hC (mul_nonneg (sub_nonneg.2 hKq) hu.le)]
  | R2b _ => exact absurd hR id
  | R1 => exact ⟨hR, fun C hC => by
      simp only [PDE.Regime.lambdaM]; nlinarith [le_max_left 1 (q ^ (-(θ / (2 - θ))))]⟩
  | R2a => exact ⟨hR, fun C hC => by
      simp only [PDE.Regime.lambdaM]; nlinarith [le_max_left 1 (q ^ (-(θ / (2 - θ))))]⟩
  | R2c => exact ⟨hR, fun C hC => by
      simp only [PDE.Regime.lambdaM]; nlinarith [le_max_left 1 (q ^ (-(θ / (2 - θ))))]⟩

end HRS.MH.AdjointRd.Phase2SA12X4
