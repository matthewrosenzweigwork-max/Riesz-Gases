import HRS.Sections.QuenchAux21
import HRS.Sections.QuenchAux16

/-!
# Packet QUENCH (Q27), part 22: `E sup_{t ≤ T} ‖Z^{a+t}‖² < ∞` for `m > d/2 + 1`

Coordinates `coord(Z^{a+t}) = ⟨j⟩^{-m}(G_j(a+t) + e^{-λ_j(a+t)} Y_j)`; Doob for `G_j` and summation with weights
`⟨j⟩^{-2m}` (Prop. 7.13 proof: "Doob's inequality ... Summing with weights ... when `m > d/2+1`").
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

lemma coord_eq_fc {m : ℝ} (F : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.coord F j = Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j := by
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _), neg_add_cancel, Real.rpow_zero, one_mul]

lemma add_sq_le_ennreal (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simpa [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num] using h

lemma iSup_dense_eq {G : ℝ → ℝ} (hc : Continuous fun u => G (max u 0)) {T' : ℝ} {D : Set ℝ}
    (hDs : D ⊆ Set.Icc 0 T') (hDd : Set.Icc 0 T' ⊆ closure D) :
    (⨆ q ∈ D, ‖G q‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T', ‖G t‖ₑ := by
  have h1 := iSup_Icc_enorm_eq_of_dense hc hDs hDd
  have e1 : (⨆ t ∈ Set.Icc (0 : ℝ) T', ‖G (max t 0)‖ₑ) = (⨆ t ∈ Set.Icc (0 : ℝ) T', ‖G t‖ₑ) := by
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    rw [max_eq_left ht.1]
  have e2 : (⨆ q ∈ D, ‖G (max q 0)‖ₑ) = (⨆ q ∈ D, ‖G q‖ₑ) := by
    refine iSup_congr fun q => iSup_congr fun hq => ?_
    rw [max_eq_left (hDs hq).1]
  calc (⨆ q ∈ D, ‖G q‖ₑ) = (⨆ q ∈ D, ‖G (max q 0)‖ₑ) := e2.symm
    _ = (⨆ t ∈ Set.Icc (0 : ℝ) T', ‖G (max t 0)‖ₑ) := h1.symm
    _ = _ := e1

section Window

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
/-- Per-mode integral bound for the (dense-sup) supremum of the noise. -/
lemma mode_sup_bound (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) {T' : ℝ} (hT' : 0 ≤ T')
    {D : Set ℝ} (hDs : D ⊆ Set.Icc 0 T') (hDd : Set.Icc 0 T' ⊆ closure D) :
    ∫⁻ ω, (⨆ q ∈ D, ‖ncoord s β Y Z j q ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal (16 * sigmaMode β j ^ 2 * T') := by
  have hN := ouNoise_of_modeField hd hs0 hsd hβ mf j
  have hlam := lamMode_pos hd hs0 hsd hβ j
  have hv := varMode_pos hd hs0 hsd hβ j
  have hσ := sigmaMode_sq hd hs0 hsd hβ j
  have hσ0 := sigmaMode_pos hβ j
  refine le_trans (le_of_eq ?_) (sup_G_lintegral hN hv hlam hσ hσ0 hT')
  refine lintegral_congr_ae ?_
  filter_upwards [hN.cont] with ω hc
  rw [iSup_dense_eq hc hDs hDd]

include hd hs0 hsd hβ in
lemma window_coeff_summable (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (A : ℝ) (hA : 0 ≤ A) :
    Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-(2 * m)) *
      (2 * (16 * sigmaMode β j ^ 2 * A + varMode d s β₀ j.1)) := by
  have hs := summable_jp_rpow (d := d) (m - 1) (by linarith)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hs.mul_left (64 * A / β + 2))
  · have := varMode_pos hd hs0 hsd hβ₀ j
    have := Torus.jp_pos j.1
    positivity
  · have hjp := Torus.jp_pos j.1
    have hjp1 := Torus.jp_ge_one j.1
    have hv1 := varMode_le_one hd hs0 hsd hβ₀ j
    have hsig : sigmaMode β j ^ 2 ≤ (2 / β) * Lattice.jp j.1 ^ 2 := by
      unfold sigmaMode
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold Lattice.jp
      rw [Real.sq_sqrt (by positivity)]
      have : (2 * Real.pi * Lattice.enorm j.1) ^ 2 = 4 * Real.pi ^ 2 * Lattice.enorm j.1 ^ 2 := by ring
      linarith
    have hjp2 : Lattice.jp j.1 ^ (-(2 * m)) * Lattice.jp j.1 ^ 2 = Lattice.jp j.1 ^ (-(2 * (m - 1))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjp]
      congr 1; push_cast; ring
    have hbound : 2 * (16 * sigmaMode β j ^ 2 * A + varMode d s β₀ j.1) ≤
        (64 * A / β + 2) * Lattice.jp j.1 ^ 2 := by
      have h1 : 16 * sigmaMode β j ^ 2 * A ≤ 16 * ((2 / β) * Lattice.jp j.1 ^ 2) * A := by
        gcongr
      have h2 : varMode d s β₀ j.1 ≤ Lattice.jp j.1 ^ 2 := by nlinarith
      have h3 : 16 * ((2 / β) * Lattice.jp j.1 ^ 2) * A = (32 * A / β) * Lattice.jp j.1 ^ 2 := by
        field_simp; ring
      have h4 : (64 * A / β + 2) * Lattice.jp j.1 ^ 2 = 2 * ((32 * A / β) * Lattice.jp j.1 ^ 2) + 2 * Lattice.jp j.1 ^ 2 := by ring
      rw [h4]
      linarith [h1, h2, h3]
    calc Lattice.jp j.1 ^ (-(2 * m)) * (2 * (16 * sigmaMode β j ^ 2 * A + varMode d s β₀ j.1))
        ≤ Lattice.jp j.1 ^ (-(2 * m)) * ((64 * A / β + 2) * Lattice.jp j.1 ^ 2) := by
          gcongr
      _ = (64 * A / β + 2) * Lattice.jp j.1 ^ (-(2 * (m - 1))) := by
          rw [← hjp2]; ring

include hd hs0 hsd hβ in
lemma lintegral_fcY_sq (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    ∫⁻ ω, ‖NegSobolev.fourierCoeff (Y ω) j‖ₑ ^ 2 ∂P = ENNReal.ofReal (varMode d s β₀ j.1) := by
  have hm2 := memLp2_fcY mf j
  have hint : Integrable (fun ω => (NegSobolev.fourierCoeff (Y ω) j) ^ 2) P := by
    have : Integrable (fun ω => NegSobolev.fourierCoeff (Y ω) j * NegSobolev.fourierCoeff (Y ω) j) P :=
      hm2.integrable_mul hm2
    simpa [sq] using this
  have e : ∀ ω, ‖NegSobolev.fourierCoeff (Y ω) j‖ₑ ^ 2 = ENNReal.ofReal ((NegSobolev.fourierCoeff (Y ω) j) ^ 2) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
  congr 1
  have := mf.covY j j
  simp only [if_true] at this
  simp_rw [sq]
  exact this

include hd hs0 hsd hβ in
theorem window_dom (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (mf : ModeField d s β β₀ m P Z Y)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) :
    ∃ H : Ω → ℝ, Integrable H P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Z (a + t) ω‖ ^ 2 ≤ H ω := by
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) (a + T))
  set S : NonzeroLattice d → Ω → ℝ≥0∞ := fun j ω => ⨆ q ∈ D, ‖ncoord s β Y Z j q ω‖ₑ with hS
  set yy : NonzeroLattice d → Ω → ℝ≥0∞ := fun j ω => ‖NegSobolev.fourierCoeff (Y ω) j‖ₑ with hyy
  set B : NonzeroLattice d → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) * (S j ω + yy j ω) with hB
  have hSm : ∀ j, AEMeasurable (S j) P := fun j =>
    AEMeasurable.biSup D hDc fun q _ => (aemeas_ncoord mf j q).enorm
  have hym : ∀ j, AEMeasurable (yy j) P := fun j => (aemeas_fc mf j).enorm
  have hBm : ∀ j, AEMeasurable (B j) P := fun j => ((hSm j).add (hym j)).const_mul _
  refine winData_dom (T := T) (Wt := fun t ω => Z (a + t) ω) (fun t => mf.meas (a + t)) B hBm ?_ ?_
  · filter_upwards [ae_all_iff.2 fun j => (ouNoise_of_modeField hd hs0 hsd hβ mf j).cont] with ω hc j t ht
    have hlam := lamMode_pos hd hs0 hsd hβ j
    have hat : 0 ≤ a + t := by linarith [ht.1]
    have hcoord : NegSobolev.coord (Z (a + t) ω) j = Lattice.jp j.1 ^ (-m) *
        (ncoord s β Y Z j (a + t) ω + Real.exp (-(lamMode d s β j.1) * (a + t)) *
          NegSobolev.fourierCoeff (Y ω) j) := by
      rw [coord_eq_fc]; simp only [ncoord]; ring
    rw [hcoord, enorm_mul, Real.enorm_of_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)]
    simp only [hB, hS, hyy]
    refine mul_le_mul' le_rfl ?_
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hG := hc j
      have hDsub : D ⊆ Set.Icc 0 (a + T) := hDs
      rw [iSup_dense_eq hG hDsub hDd]
      exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) (a + T)) => ‖ncoord s β Y Z j t ω‖ₑ) (a + t)
        ⟨hat, by linarith [ht.2]⟩
    · rw [enorm_mul]
      have : ‖Real.exp (-(lamMode d s β j.1) * (a + t))‖ₑ ≤ 1 := by
        rw [Real.enorm_of_nonneg (Real.exp_pos _).le]
        have hx : -(lamMode d s β j.1) * (a + t) ≤ 0 := by nlinarith [mul_nonneg hlam.le hat]
        have := Real.exp_le_one_iff.2 hx
        simpa using this
      calc ‖Real.exp (-(lamMode d s β j.1) * (a + t))‖ₑ * ‖NegSobolev.fourierCoeff (Y ω) j‖ₑ
          ≤ 1 * ‖NegSobolev.fourierCoeff (Y ω) j‖ₑ := by gcongr
        _ = _ := one_mul _
  · -- the sum of the second moments
    have hterm : ∀ j : NonzeroLattice d, ∫⁻ ω, (B j ω) ^ 2 ∂P ≤ ENNReal.ofReal (Lattice.jp j.1 ^ (-(2 * m)) *
        (2 * (16 * sigmaMode β j ^ 2 * (a + T) + varMode d s β₀ j.1))) := by
      intro j
      have hS2 := mode_sup_bound hd hs0 hsd hβ mf j (T' := a + T) (by linarith) (D := D) hDs hDd
      have hy2 := lintegral_fcY_sq hd hs0 hsd hβ mf j
      have h1 : ∀ ω, (B j ω) ^ 2 ≤ ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) ^ 2 * (2 * (S j ω ^ 2 + yy j ω ^ 2)) := by
        intro ω
        simp only [hB, mul_pow]
        exact mul_le_mul' le_rfl (add_sq_le_ennreal _ _)
      calc ∫⁻ ω, (B j ω) ^ 2 ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) ^ 2 * (2 * (S j ω ^ 2 + yy j ω ^ 2)) ∂P :=
            lintegral_mono h1
        _ = ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) ^ 2 * (2 * (∫⁻ ω, S j ω ^ 2 ∂P + ∫⁻ ω, yy j ω ^ 2 ∂P)) := by
            rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
              lintegral_const_mul' _ _ (by simp), lintegral_add_left' ((hSm j).pow_const 2)]
        _ ≤ ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) ^ 2 * (2 * (ENNReal.ofReal (16 * sigmaMode β j ^ 2 * (a + T)) +
              ENNReal.ofReal (varMode d s β₀ j.1))) := by
            exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add hS2 hy2.le))
        _ = ENNReal.ofReal (Lattice.jp j.1 ^ (-(2 * m)) *
            (2 * (16 * sigmaMode β j ^ 2 * (a + T) + varMode d s β₀ j.1))) := by
            have hv := varMode_pos hd hs0 hsd hβ₀ j
            have hsg : 0 ≤ 16 * sigmaMode β j ^ 2 * (a + T) := by positivity
            have hjp : 0 ≤ Lattice.jp j.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos _).le _
            rw [← ENNReal.ofReal_pow hjp, ← ENNReal.ofReal_add hsg hv.le,
              show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [Torus.jp_rpow_sq, show 2 * -m = -(2*m) by ring]
    have hsumm := window_coeff_summable hd hs0 hsd hβ hβ₀ hm (a + T) (by linarith)
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => ?_) hsumm]
    · exact ENNReal.ofReal_lt_top
    · have := varMode_pos hd hs0 hsd hβ₀ j
      have := Torus.jp_pos j.1
      positivity

end Window

end Qch

end HRS
