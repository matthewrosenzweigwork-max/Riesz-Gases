import HRS.Commutator.Torus.TINHOMAux2

/-!
# T-INHOM helpers, part 3: `L²` bounds for `K * b`, for the low part `a₀`, and comparison of `Ḣ^{-α}` and `H^{-α}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma tinhom_ghi_meas (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η) (i : Fin d) :
    Measurable fun x : Torus d => ghiForceT s η x i := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp (tkr_ghi_measurable hd2 hs0 hsd1 hη)

/-- `K_i * g = 0` for `g` with Fourier support in `η|k| ≤ 1`. -/
lemma tinhom_conv_low_ae (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (i : Fin d) {g : Torus d → ℝ} (hg : Integrable g)
    (hsupp : ∀ k : Lattice d, 1 < η * Lattice.enorm k → Torus.fcoef g k = 0) :
    textConv (fun z => ghiForceT s η z i) g =ᵐ[volume] 0 := by
  have hK := tinhom_ghi_int hd hs0 hsd hη i
  refine text_ae_eq_zero_of_fcoef (text_integrable_conv hK hg) (fun k => ?_)
  rw [text_fcoef_conv hK hg]
  by_cases hk : η * Lattice.enorm k ≤ 1
  · rw [tinhom_ghi_fcoef_zero hd hs0 hsd hη i hk, zero_mul]
  · rw [hsupp k (not_le.1 hk), mul_zero]

/-- `‖K_i * b‖₂² ≲ η^{2(d-s)-2} ∑ (1+4π²η²|k|²)^{-α}|b̂(k)|²`. -/
lemma tinhom_Kb_L2 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ (i : Fin d) (b : Torus d → ℝ), Continuous b →
      eLpNorm (textConv (fun z => ghiForceT s η z i) b) 2 volume ^ 2 ≤
        ENNReal.ofReal (C * η ^ (2 * ((d : ℝ) - s) - 2)) *
          tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) := by
  obtain ⟨C, hC, hbound⟩ := tinhom_ghi_fcoef_bound hd hs0 hsd
  refine ⟨C, hC, fun η hη i b hb => ?_⟩
  have hK := tinhom_ghi_int hd hs0 hsd hη i
  have hKm := tinhom_ghi_meas hd hs0 hsd hη i
  obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
  have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
  have hbi : Integrable b := (HRS.PDE.R2Aux.memLp_of_continuous_real hb).integrable (by norm_num)
  have hconv_m := tinhom_conv_meas hKm hb.measurable
  have hmem : MemLp (textConv (fun z => ghiForceT s η z i) b) 2 volume :=
    MemLp.of_bound hconv_m.aestronglyMeasurable ((∫ z, |ghiForceT s η z i|) * Bb)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact tinhom_conv_bdd hK hBb' x)
  rw [← tprod_parseval_enn hmem]
  unfold tinhomS
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [text_fcoef_conv hK hbi, enorm_mul, mul_pow, tinhom_enorm_sq_eq (Torus.fcoef (fun z => ghiForceT s η z i) k)]
  have h1 := hbound η hη i k
  have e : ENNReal.ofReal (C * η ^ (2 * ((d : ℝ) - s) - 2)) *
      (ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-Whole.alphaE d s)) *
        ‖Torus.fcoef b k‖ₑ ^ 2) =
      ENNReal.ofReal (C * η ^ (2 * ((d : ℝ) - s) - 2) *
        (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-Whole.alphaE d s)) * ‖Torus.fcoef b k‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (p := C * η ^ (2 * ((d : ℝ) - s) - 2)) (by positivity)]
    ring
  rw [e]
  gcongr
  exact h1

/-- The low part: `‖a₀‖₂² ≲ ∑ (1+4π²η²|k|²)^{-α}|â₀(k)|²` for Fourier support in `η|k| ≤ θ`. -/
lemma tinhom_a0_L2 {a : Torus d → ℝ} (ha : Continuous a) {η θ α : ℝ} (hη : 0 < η) (hα : 0 ≤ α)
    (hsupp : ∀ k : Lattice d, θ < η * Lattice.enorm k → Torus.fcoef a k = 0) :
    eLpNorm a 2 volume ^ 2 ≤ ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * θ ^ 2) ^ α) *
      tinhomS η (-α) (fun k => Torus.fcoef a k) := by
  have hmem := HRS.PDE.R2Aux.memLp_of_continuous_real ha
  rw [← tprod_parseval_enn hmem]
  unfold tinhomS
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hz : Torus.fcoef a k = 0
  · simp [hz]
  · have hle : η * Lattice.enorm k ≤ θ := by
      by_contra hcon
      exact hz (hsupp k (not_le.1 hcon))
    have hw : 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * θ ^ 2 := by
      have h0 : 0 ≤ η * Lattice.enorm k := mul_nonneg hη.le (norm_nonneg _)
      have h1 : (η * Lattice.enorm k) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ h0 hle 2
      nlinarith [Real.pi_pos]
    have hpos : 0 < 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by positivity
    have hmain : 1 ≤ (1 + 4 * Real.pi ^ 2 * θ ^ 2) ^ α *
        (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-α) := by
      have h1 : (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ α ≤
          (1 + 4 * Real.pi ^ 2 * θ ^ 2) ^ α := Real.rpow_le_rpow hpos.le hw hα
      have h2 : (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-α) =
          ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ α)⁻¹ := Real.rpow_neg hpos.le _
      rw [h2, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos _), one_mul]
      exact h1
    calc ‖Torus.fcoef a k‖ₑ ^ 2 = ENNReal.ofReal 1 * ‖Torus.fcoef a k‖ₑ ^ 2 := by simp
      _ ≤ ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * θ ^ 2) ^ α *
            (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-α)) * ‖Torus.fcoef a k‖ₑ ^ 2 := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- Comparison of the homogeneous and inhomogeneous sums for coefficients supported in `η|k| > θ`. -/
lemma tinhom_hom_le {F : Lattice d → ℂ} {η θ α : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hα : 0 < α)
    (hsupp : ∀ k : Lattice d, η * Lattice.enorm k ≤ θ → F k = 0) :
    homSqT (-α) F ≤ ENNReal.ofReal ((1 + 1 / (2 * Real.pi * θ) ^ 2) ^ α * η ^ (2 * α)) *
      tinhomS η (-α) F := by
  unfold homSqT tinhomS
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    by_cases hz : F k = 0
    · simp [hz]
    · have hlt : θ < η * Lattice.enorm k := by
        by_contra hcon
        exact hz (hsupp k (not_lt.1 hcon))
      have hen : 0 < Lattice.enorm k := ten_enorm_pos hk
      set τ := 2 * Real.pi * η * Lattice.enorm k with hτ
      have hτθ : 2 * Real.pi * θ ≤ τ := by
        rw [hτ]; nlinarith [Real.pi_pos]
      have hw := tinhom_wt2 (α := α) hα (by positivity : 0 < 2 * Real.pi * θ) hτθ
      have hτ0 : 0 < τ := by rw [hτ]; positivity
      have e1 : (2 * Real.pi * Lattice.enorm k) ^ (2 * (-α)) = η ^ (2 * α) * τ ^ (-(2 * α)) := by
        have h : 2 * Real.pi * Lattice.enorm k = η⁻¹ * τ := by rw [hτ]; field_simp
        rw [h, Real.mul_rpow (by positivity) hτ0.le, Real.inv_rpow hη.le, ← Real.rpow_neg hη.le]
        congr 2 <;> ring
      have e2 : 1 + τ ^ 2 = 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by rw [hτ]; ring
      rw [e2] at hw
      have hC0 : 0 ≤ (1 + 1 / (2 * Real.pi * θ) ^ 2) ^ α := by positivity
      calc ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (2 * (-α))) * ‖F k‖ₑ ^ 2
          ≤ ENNReal.ofReal ((1 + 1 / (2 * Real.pi * θ) ^ 2) ^ α * η ^ (2 * α) *
              (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-α)) * ‖F k‖ₑ ^ 2 := by
            gcongr
            rw [e1]
            calc η ^ (2 * α) * τ ^ (-(2 * α)) ≤
                η ^ (2 * α) * ((1 + 1 / (2 * Real.pi * θ) ^ 2) ^ α * (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-α)) := by
                  gcongr
              _ = _ := by ring
        _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

end HRS.Commutator.TorusNote
