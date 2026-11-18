import HRS.MC.S7FCF5JB

/-!
# H2, part A: generic coefficient/centring estimates (prefix `S7FCH2_`)

Route (see `S7FCH2D.lean` for the assembly).  For a measurable coefficient family `c_k(ω)` with
`∫⁻ |c_k|^q ≤ w_k` (`q ≥ 2`):

* `S7FCH2_H_lint`: `∫⁻ H(c) ≤ Z^{q/2-1} ∑_k ⟨k⟩^{4-2r-2q} w_k` (`H` is `S7FCF5F_H`, the weighted-sum majorant of `‖ofSeq r c‖^q`);
* `S7FCH2_enorm_le_H`: `‖ofSeq r c‖ₑ^q ≤ H(c)` pointwise;
* `S7FCH2_tail_ae`: the centred-field estimate (Jensen on the probability space, a.e. hypotheses);
* `S7FCH2_memlp_of_H_lt_top`: `H(c) < ⊤` forces the weighted sequence into `ℓ²` (so `ofSeq` is honest);
* `S7FCH2_ofSeq_sub`: `ofSeq` is additive on honest sequences.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J

variable {d : ℕ}

/-- The unscaled weighted sum `H'(c) = ∑_k ⟨k⟩^{4-2r-2q} |c_k|^q` (`S7FCF5F_H` is `Z^{q/2-1} H'`). -/
def S7FCH2_H' (d : ℕ) (r q : ℝ) (c : NonzeroLattice d → ℝ) : ℝ≥0∞ :=
  ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k|) ^ q

theorem S7FCH2_H_eq (r q : ℝ) (c : NonzeroLattice d → ℝ) :
    S7FCF5F_H d r q c = ENNReal.ofReal (fcf5Z d r ^ (q / 2 - 1)) * S7FCH2_H' d r q c := rfl

/-- `∫⁻ H'(c) ≤ ∑_k ⟨k⟩^{4-2r-2q} w_k` when `∫⁻ |c_k|^q ≤ w_k`. -/
theorem S7FCH2_H'_lint {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (r q : ℝ) (hq : 2 ≤ q)
    (c : NonzeroLattice d → Ω → ℝ) (hc : ∀ k, Measurable (c k)) (w : NonzeroLattice d → ℝ≥0∞)
    (hw : ∀ k, ∫⁻ ω, ENNReal.ofReal (|c k ω| ^ q) ∂P ≤ w k) :
    ∫⁻ ω, S7FCH2_H' d r q (fun k => c k ω) ∂P ≤
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * w k := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  dsimp only [S7FCH2_H']
  rw [lintegral_tsum (f := fun (k : NonzeroLattice d) (ω : Ω) =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k ω|) ^ q) fun k =>
      (measurable_const.mul (((continuous_abs.measurable.comp (hc k)).ennreal_ofReal).pow_const q)).aemeasurable]
  refine ENNReal.tsum_le_tsum fun k => ?_
  have e1 : ∀ ω, (ENNReal.ofReal |c k ω|) ^ q = ENNReal.ofReal (|c k ω| ^ q) := fun ω =>
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0
  simp only [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  exact hw k

theorem S7FCH2_H'_meas {Ω : Type} [MeasurableSpace Ω] (r q : ℝ) (c : NonzeroLattice d → Ω → ℝ)
    (hc : ∀ k, Measurable (c k)) : Measurable (fun ω => S7FCH2_H' d r q (fun k => c k ω)) := by
  refine Measurable.ennreal_tsum (f := fun (k : NonzeroLattice d) (ω : Ω) =>
    ENNReal.ofReal (Lattice.jp k.1 ^ (4 - 2 * r - 2 * q)) * (ENNReal.ofReal |c k ω|) ^ q) fun k => ?_
  exact measurable_const.mul (((continuous_abs.measurable.comp (hc k)).ennreal_ofReal).pow_const q)

/-- `‖ofSeq r c‖ₑ^q ≤ H(c)` for every coefficient sequence (`q ≥ 2`). -/
theorem S7FCH2_enorm_le_H (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q)
    (c : NonzeroLattice d → ℝ) :
    ‖(NegSobolev.ofSeq r c : NegSobolev d r)‖ₑ ^ q ≤ S7FCF5F_H d r q c := by
  have hq2 : (0 : ℝ) ≤ q / 2 := by linarith
  have h1 : ‖(NegSobolev.ofSeq r c : NegSobolev d r)‖ₑ ^ 2 ≤
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * (ENNReal.ofReal |c k|) ^ 2 :=
    S7FCF5F_enorm_sq_le r c
  have h2 : ‖(NegSobolev.ofSeq r c : NegSobolev d r)‖ₑ ^ q =
      (‖(NegSobolev.ofSeq r c : NegSobolev d r)‖ₑ ^ 2) ^ (q / 2) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have h3 := HRS.MC.Sec7.S7FCF5B.fcf5_D1_weighted_sum_proof (d := d) r hr q hq
    (fun k => ENNReal.ofReal |c k|)
  rw [h2]
  exact (ENNReal.rpow_le_rpow h1 hq2).trans h3

/-- Jensen and centring, with all hypotheses a.e.: if `B^q ≤ H` and `Z ≤ B + ∫⁻ B` a.e. (`H` measurable), then
`(∫⁻ B)^q ≤ ∫⁻ H` and `∫⁻ Z^q ≤ 2^{q-1}(∫⁻ H + (∫⁻ B)^q)`. -/
theorem S7FCH2_tail_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B H Z : Ω → ℝ≥0∞) {q : ℝ} (hq : 1 < q) (hH : Measurable H) (hBH : ∀ᵐ ω ∂P, B ω ^ q ≤ H ω)
    (hZ : ∀ᵐ ω ∂P, Z ω ≤ B ω + ∫⁻ ω', B ω' ∂P) :
    (∫⁻ ω, B ω ∂P) ^ q ≤ ∫⁻ ω, H ω ∂P ∧
      ∫⁻ ω, Z ω ^ q ∂P ≤ (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, H ω ∂P + (∫⁻ ω', B ω' ∂P) ^ q) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hq1 : q ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hK : ∀ᵐ ω ∂P, B ω ≤ H ω ^ (1 / q) := by
    filter_upwards [hBH] with ω h
    calc B ω = (B ω ^ q) ^ (1 / q) := (S7FCF5F_rpow_cancel _ hq1).1.symm
      _ ≤ H ω ^ (1 / q) := ENNReal.rpow_le_rpow h (div_nonneg zero_le_one hq0)
  have hβ : ∫⁻ ω, B ω ∂P ≤ ∫⁻ ω, H ω ^ (1 / q) ∂P := lintegral_mono_ae hK
  have hJ := S7FCF5F_jensen P (hH.pow_const (1 / q)) hq
  have hJ' : ∫⁻ ω, (H ω ^ (1 / q)) ^ q ∂P = ∫⁻ ω, H ω ∂P :=
    lintegral_congr fun ω => (S7FCF5F_rpow_cancel _ hq1).2
  have hβq : (∫⁻ ω, B ω ∂P) ^ q ≤ ∫⁻ ω, H ω ∂P :=
    (ENNReal.rpow_le_rpow hβ hq0).trans (hJ.trans hJ'.le)
  refine ⟨hβq, ?_⟩
  have hpt : ∀ᵐ ω ∂P, Z ω ^ q ≤ (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) := by
    filter_upwards [hBH, hZ] with ω h1 h2
    calc Z ω ^ q ≤ (B ω + ∫⁻ ω', B ω' ∂P) ^ q := ENNReal.rpow_le_rpow h2 hq0
      _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (B ω ^ q + (∫⁻ ω', B ω' ∂P) ^ q) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq.le
      _ ≤ (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 le_rfl) zero_le
  calc ∫⁻ ω, Z ω ^ q ∂P
      ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * (H ω + (∫⁻ ω', B ω' ∂P) ^ q) ∂P := lintegral_mono_ae hpt
    _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ ω, H ω ∂P + (∫⁻ ω', B ω' ∂P) ^ q) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top),
          lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- If `H(c) < ⊤` then the weighted coefficient sequence is square summable, so `ofSeq` is honest. -/
theorem S7FCH2_memlp_of_H_lt_top (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (q : ℝ) (hq : 2 ≤ q)
    (c : NonzeroLattice d → ℝ) (h : S7FCH2_H' d r q c < ⊤) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * c k) 2 := by
  have hq2 : (0 : ℝ) < q / 2 := by linarith
  have h3 := HRS.MC.Sec7.S7FCF5B.fcf5_D1_weighted_sum_proof (d := d) r hr q hq
    (fun k => ENNReal.ofReal |c k|)
  have hX : ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * (ENNReal.ofReal |c k|) ^ 2 < ⊤ := by
    have h4 : (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) *
        (ENNReal.ofReal |c k|) ^ 2) ^ (q / 2) < ⊤ :=
      lt_of_le_of_lt h3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)
    exact (ENNReal.rpow_lt_top_iff_of_pos hq2).1 h4
  rw [Torus.memℓp_two_iff]
  have hterm : ∀ k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r)) * (ENNReal.ofReal |c k|) ^ 2 =
      ENNReal.ofReal ((Lattice.jp k.1 ^ (-r) * c k) ^ 2) := by
    intro k
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, ← ENNReal.ofReal_mul (Real.rpow_nonneg (Torus.jp_pos k.1).le _),
      mul_pow, S7FCF5F_rpow_sq (Torus.jp_pos k.1)]
  simp only [hterm] at hX
  have hs := ENNReal.summable_toReal hX.ne
  refine hs.congr fun k => ?_
  exact ENNReal.toReal_ofReal (sq_nonneg _)

/-- `ofSeq` is additive on honest sequences. -/
theorem S7FCH2_ofSeq_sub (m : ℝ) (c₁ c₂ : NonzeroLattice d → ℝ)
    (h₁ : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c₁ k) 2)
    (h₂ : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c₂ k) 2) :
    (NegSobolev.ofSeq m (fun k => c₁ k - c₂ k) : NegSobolev d m) =
      NegSobolev.ofSeq m c₁ - NegSobolev.ofSeq m c₂ := by
  have h₃ : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (c₁ k - c₂ k)) 2 := by
    have := h₁.sub h₂
    convert this using 1
    funext k
    simp [mul_sub]
  have e3 := NegSobolev.ofSeq_of_mem (m := m) (fun k => c₁ k - c₂ k) h₃
  have e1 := NegSobolev.ofSeq_of_mem (m := m) c₁ h₁
  have e2 := NegSobolev.ofSeq_of_mem (m := m) c₂ h₂
  show (NegSobolev.ofSeq m (fun k => c₁ k - c₂ k) : lp (fun _ : NonzeroLattice d => ℝ) 2) =
    (NegSobolev.ofSeq m c₁ : lp (fun _ : NonzeroLattice d => ℝ) 2) -
      (NegSobolev.ofSeq m c₂ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  rw [e3, e1, e2]
  apply Subtype.ext
  funext k
  simp only [mul_sub]
  rfl

end HRS.MC.Sec7.S7FCH2

end
