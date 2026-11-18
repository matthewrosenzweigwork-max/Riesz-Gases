import HRS.Commutator.Torus.TINHOMAux1

/-!
# T-INHOM helpers, part 2: the kernel `K = ∇g_>` on the Fourier side; weights; the convolution `K * b`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- The Bessel-weighted sum without the factor `η^d`: `sobSqT η t F = η^d · tinhomS η t F`. -/
def tinhomS (η t : ℝ) (F : Lattice d → ℂ) : ℝ≥0∞ :=
  ∑' k : Lattice d, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ t) * ‖F k‖ₑ ^ 2

lemma tinhom_sobSqT_eq (η t : ℝ) (F : Lattice d → ℂ) :
    sobSqT η t F = ENNReal.ofReal (η ^ d) * tinhomS η t F := rfl

lemma tinhomS_mono {η t : ℝ} {F G : Lattice d → ℂ} (h : ∀ k, ‖F k‖ₑ ≤ ‖G k‖ₑ) :
    tinhomS η t F ≤ tinhomS η t G := by
  unfold tinhomS
  refine ENNReal.tsum_le_tsum fun k => ?_
  gcongr
  exact h k

/-! ### scalar weight inequalities -/

lemma tinhom_wt1 {α τ : ℝ} (hα : 1 ≤ α) (hτ : 1 ≤ τ) :
    τ ^ (2 - 4 * α) ≤ 2 ^ α * (1 + τ ^ 2) ^ (-α) := by
  have hτ0 : 0 < τ := by linarith
  have h1 : τ ^ (2 - 4 * α) ≤ τ ^ (-(2 * α)) := by
    apply Real.rpow_le_rpow_of_exponent_le hτ
    linarith
  have h2 : 1 + τ ^ 2 ≤ 2 * τ ^ 2 := by nlinarith
  have h3 : (2 * τ ^ 2) ^ (-α) ≤ (1 + τ ^ 2) ^ (-α) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have h4 : (2 * τ ^ 2) ^ (-α) = 2 ^ (-α) * τ ^ (-(2 * α)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [show (τ ^ 2 : ℝ) = τ ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hτ0.le]
    congr 1; push_cast; ring
  have h5 : 2 ^ (-α) * τ ^ (-(2 * α)) ≤ (1 + τ ^ 2) ^ (-α) := by rw [← h4]; exact h3
  have h6 : (0 : ℝ) < 2 ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have h7 : (2 : ℝ) ^ α * 2 ^ (-α) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc τ ^ (2 - 4 * α) ≤ τ ^ (-(2 * α)) := h1
    _ = 2 ^ α * (2 ^ (-α) * τ ^ (-(2 * α))) := by rw [← mul_assoc, h7, one_mul]
    _ ≤ 2 ^ α * (1 + τ ^ 2) ^ (-α) := by gcongr

lemma tinhom_wt2 {α τ θ : ℝ} (hα : 0 < α) (hθ : 0 < θ) (hτ : θ ≤ τ) :
    τ ^ (-(2 * α)) ≤ (1 + 1 / θ ^ 2) ^ α * (1 + τ ^ 2) ^ (-α) := by
  have hτ0 : 0 < τ := by linarith
  have h1 : 1 + τ ^ 2 ≤ τ ^ 2 * (1 + 1 / θ ^ 2) := by
    have : 1 ≤ τ ^ 2 / θ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have e : τ ^ 2 * (1 + 1 / θ ^ 2) = τ ^ 2 + τ ^ 2 / θ ^ 2 := by ring
    rw [e]; linarith
  have h2 : (τ ^ 2 * (1 + 1 / θ ^ 2)) ^ (-α) ≤ (1 + τ ^ 2) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  have h3 : (τ ^ 2 * (1 + 1 / θ ^ 2)) ^ (-α) = τ ^ (-(2 * α)) * (1 + 1 / θ ^ 2) ^ (-α) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [show (τ ^ 2 : ℝ) = τ ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hτ0.le]
    congr 1; push_cast; ring
  have hc : (0 : ℝ) < (1 + 1 / θ ^ 2) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hc' : (1 + 1 / θ ^ 2) ^ α * (1 + 1 / θ ^ 2) ^ (-α) = 1 := by
    rw [← Real.rpow_add (by positivity)]; simp
  calc τ ^ (-(2 * α)) = (1 + 1 / θ ^ 2) ^ α * ((1 + 1 / θ ^ 2) ^ (-α) * τ ^ (-(2 * α))) := by
        rw [← mul_assoc, hc', one_mul]
    _ ≤ (1 + 1 / θ ^ 2) ^ α * (1 + τ ^ 2) ^ (-α) := by
        rw [mul_comm ((1 + 1 / θ ^ 2) ^ (-α)), ← h3] at *
        gcongr

/-! ### the kernel `K_i = (∇g_>)_i` -/

lemma tinhom_ghi_int (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η) (i : Fin d) :
    Integrable (fun x : Torus d => ghiForceT s η x i) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := (tkr_ghi_integrable hd2 hs0 hsd1 hη i).re
  simpa using this

lemma tinhom_ghi_fcoef (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (i : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => ghiForceT s η x i) k = (1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact tkr_ghi_coef hd2 hs0 hsd1 hη i k

lemma tinhom_ghi_fcoef_zero (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (i : Fin d) {k : Lattice d} (hk : η * Lattice.enorm k ≤ 1) :
    Torus.fcoef (fun x => ghiForceT s η x i) k = 0 := by
  rw [tinhom_ghi_fcoef hd hs0 hsd hη, tkrChi_eq_one hk hη]
  simp

/-- `|K̂_i(k)|² ≲ η^{4α-2}(1+4π²η²|k|²)^{-α}` (`η|k| > 1`, `α = (d-s)/2`). -/
lemma tinhom_ghi_fcoef_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ (i : Fin d) (k : Lattice d),
      ‖Torus.fcoef (fun x => ghiForceT s η x i) k‖ ^ 2 ≤
        C * η ^ (2 * ((d : ℝ) - s) - 2) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(((d : ℝ) - s) / 2)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα1 : 1 ≤ α := by rw [hαdef]; linarith
  have hrc : (0 : ℝ) ≤ |rieszConst d s| := abs_nonneg _
  refine ⟨(rieszConst d s) ^ 2 * 2 ^ α + 1, by positivity, fun η hη i k => ?_⟩
  have hCpos : 0 ≤ (rieszConst d s) ^ 2 * 2 ^ α := by positivity
  by_cases hk : η * Lattice.enorm k ≤ 1
  · rw [tinhom_ghi_fcoef_zero hd hs0 hsd hη i hk]
    rw [norm_zero]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    positivity
  · push Not at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [text_enorm_zero] at hk
      linarith
    set E := Lattice.enorm k with hE
    have hE0 : 0 < E := ten_enorm_pos hk0
    have hη1 : 1 < η * E := hk
    rw [tinhom_ghi_fcoef hd hs0 hsd hη]
    -- the size of the coefficient
    have hχ0 : 0 ≤ tkrChi η k := Whole.cmxFB_chi_nonneg _
    have hχ1 : tkrChi η k ≤ 1 := Whole.cmxFB_chi_le_one _
    have hki : |((k i : ℤ) : ℝ)| ≤ E := HRS.KernelAux.abs_coord_le_enorm k i
    have hnorm : ‖(1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k‖ ≤
        |rieszConst d s| * (2 * Real.pi * E) ^ (1 + (s - (d : ℝ))) := by
      have h1 : ‖(1 - ((tkrChi η k : ℝ) : ℂ))‖ ≤ 1 := by
        rw [show (1 - ((tkrChi η k : ℝ) : ℂ)) = (((1 - tkrChi η k : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      have hbase : 0 < 2 * Real.pi * E := by positivity
      have h2 : ‖tkrCI d s i k‖ = 2 * Real.pi * |((k i : ℤ) : ℝ)| *
          (|rieszConst d s| * (2 * Real.pi * E) ^ (s - (d : ℝ))) := by
        unfold tkrCI
        have hcI : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ =
            2 * Real.pi * |((k i : ℤ) : ℝ)| := by
          simp [norm_mul, abs_of_pos Real.pi_pos]
        rw [norm_mul, hcI, Complex.norm_real, Real.norm_eq_abs]
        congr 1
        unfold rieszCoeff
        simp only [hk0, if_false]
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase.le _)]
      rw [norm_mul]
      calc ‖(1 - ((tkrChi η k : ℝ) : ℂ))‖ * ‖tkrCI d s i k‖ ≤ 1 * ‖tkrCI d s i k‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszConst d s| * (2 * Real.pi * E) ^ (s - (d : ℝ))) := by
            rw [one_mul, h2]
        _ ≤ (2 * Real.pi * E) * (|rieszConst d s| * (2 * Real.pi * E) ^ (s - (d : ℝ))) := by
            gcongr
        _ = |rieszConst d s| * (2 * Real.pi * E) ^ (1 + (s - (d : ℝ))) := by
            rw [Real.rpow_add hbase, Real.rpow_one]; ring
    have hsq : ‖(1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k‖ ^ 2 ≤
        (rieszConst d s) ^ 2 * (2 * Real.pi * E) ^ (2 - 4 * α) := by
      have hbase : 0 < 2 * Real.pi * E := by positivity
      calc _ ≤ (|rieszConst d s| * (2 * Real.pi * E) ^ (1 + (s - (d : ℝ)))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = (rieszConst d s) ^ 2 * ((2 * Real.pi * E) ^ (1 + (s - (d : ℝ)))) ^ 2 := by
            rw [mul_pow, sq_abs]
        _ = (rieszConst d s) ^ 2 * (2 * Real.pi * E) ^ (2 - 4 * α) := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
            congr 1
            rw [hαdef]; push_cast; ring
    -- the weight
    have hτ : 1 ≤ 2 * Real.pi * η * E := by nlinarith [Real.pi_gt_three]
    have hw := tinhom_wt1 hα1 hτ
    have e1 : (2 * Real.pi * E) ^ (2 - 4 * α) =
        η ^ (4 * α - 2) * (2 * Real.pi * η * E) ^ (2 - 4 * α) := by
      have : (2 * Real.pi * η * E) = η * (2 * Real.pi * E) := by ring
      rw [this, Real.mul_rpow hη.le (by positivity), ← mul_assoc,
        show (η ^ (4 * α - 2) : ℝ) * η ^ (2 - 4 * α) = 1 by
          rw [← Real.rpow_add hη]; simp]
      ring
    have e2 : (1 + (2 * Real.pi * η * E) ^ 2) = 1 + 4 * Real.pi ^ 2 * η ^ 2 * E ^ 2 := by ring
    rw [e2] at hw
    have hexp : 2 * ((d : ℝ) - s) - 2 = 4 * α - 2 := by rw [hαdef]; ring
    rw [hexp]
    have hX : 0 ≤ η ^ (4 * α - 2) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * E ^ 2) ^ (-α) := by positivity
    calc ‖(1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k‖ ^ 2
        ≤ (rieszConst d s) ^ 2 * (2 * Real.pi * E) ^ (2 - 4 * α) := hsq
      _ = (rieszConst d s) ^ 2 * η ^ (4 * α - 2) * (2 * Real.pi * η * E) ^ (2 - 4 * α) := by
          rw [e1]; ring
      _ ≤ (rieszConst d s) ^ 2 * η ^ (4 * α - 2) *
            (2 ^ α * (1 + 4 * Real.pi ^ 2 * η ^ 2 * E ^ 2) ^ (-α)) := by gcongr
      _ = ((rieszConst d s) ^ 2 * 2 ^ α) *
            (η ^ (4 * α - 2) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * E ^ 2) ^ (-α)) := by ring
      _ ≤ ((rieszConst d s) ^ 2 * 2 ^ α + 1) *
            (η ^ (4 * α - 2) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * E ^ 2) ^ (-α)) := by
          nlinarith
      _ = _ := by ring

end HRS.Commutator.TorusNote
