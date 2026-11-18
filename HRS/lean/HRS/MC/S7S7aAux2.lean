import HRS.MC.S7S7aAux1

/-!
# Packet `s7_S7a_mode_data`, helper 2: Sobolev-norm calculus (pointwise comparison, linear combinations,
multiplication by a smooth function, smoothing by the Riesz kernel with an explicit constant)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ}

theorem s7a_hs_le {a b : ℝ} {x y : Coeff d} {C : ℝ} (hC : 0 ≤ C) (hy : MemHs b y)
    (h : ∀ k, sobWeight a k * ‖x k‖ ^ 2 ≤ C ^ 2 * (sobWeight b k * ‖y k‖ ^ 2)) :
    MemHs a x ∧ HRS.PDE.hsNorm a x ≤ C * HRS.PDE.hsNorm b y := by
  have hmem : MemHs a x :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg a k) (sq_nonneg _)) h
      (hy.mul_left (C ^ 2))
  refine ⟨hmem, ?_⟩
  have h2 : hsNormSq a x ≤ C ^ 2 * hsNormSq b y := by
    unfold hsNormSq
    rw [← tsum_mul_left]
    exact hmem.tsum_le_tsum h (hy.mul_left _)
  unfold HRS.PDE.hsNorm
  calc Real.sqrt (hsNormSq a x) ≤ Real.sqrt (C ^ 2 * hsNormSq b y) := Real.sqrt_le_sqrt h2
    _ = C * Real.sqrt (hsNormSq b y) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

theorem s7a_hs_lincomb {m : ℝ} {V u : Torus d → ℝ} (hV : Continuous V) (hu : Continuous u)
    (hVm : MemHs m (coeffOf V)) (hum : MemHs m (coeffOf u)) (A B c : ℝ) :
    HRS.PDE.hsNorm m (coeffOf (fun x => A * V x + B * u x + c)) ≤
      |A| * HRS.PDE.hsNorm m (coeffOf V) + |B| * HRS.PDE.hsNorm m (coeffOf u) + |c| := by
  rw [coeffOf_lincomb hV hu]
  have h1 : MemHs m (fun k => (A : ℂ) * coeffOf V k) := memHs_smul hVm _
  have h2 : MemHs m (fun k => (B : ℂ) * coeffOf u k) := memHs_smul hum _
  have h3 : MemHs m (fun k => (c : ℂ) * deltaCoeff (0 : Lattice d) k) :=
    memHs_smul (deltaCoeff_memHs m 0) _
  have e1 := hsNorm_add_le m (memHs_add h1 h2) h3
  have e2 := hsNorm_add_le m h1 h2
  rw [hsNorm_smul, hsNorm_smul] at e2
  rw [hsNorm_smul, hsNorm_delta] at e1
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_one] at e1 e2
  exact e1.trans (by linarith)

theorem s7a_mul_smooth (hd : 0 < d) {w : Torus d → ℝ} (hw : Torus.IsSmooth w) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Torus d → ℝ, Continuous u → MemHs (n : ℝ) (coeffOf u) →
      MemHs (n : ℝ) (coeffOf (fun x => w x * u x)) ∧
        HRS.PDE.hsNorm (n : ℝ) (coeffOf (fun x => w x * u x)) ≤ C * HRS.PDE.hsNorm (n : ℝ) (coeffOf u) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C, hC0, hC⟩ := MFProduct.exists_product_bound (d := d) ((n + d : ℕ) : ℝ) (n : ℝ) (n : ℝ)
    (Nat.cast_nonneg n) (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) le_rfl
    (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hwH : MemHs ((n + d : ℕ) : ℝ) (coeffOf w) :=
    memHs_of_isCk (n + d) w (HRS.Q66.q66_isCk_of_smooth hw _)
  have hwc : Continuous w := HRS.Q66.q66_cont_of_smooth hw
  refine ⟨C * HRS.PDE.hsNorm ((n + d : ℕ) : ℝ) (coeffOf w), mul_nonneg hC0 (Real.sqrt_nonneg _),
    fun u hu hum => ?_⟩
  have hmul : coeffOf (fun x => w x * u x) = mulCoeff (coeffOf w) (coeffOf u) :=
    coeffOf_mul w u (MFProduct.memLp_two_real hwc) (MFProduct.memLp_two_real hu)
  rw [hmul]
  obtain ⟨h1, h2⟩ := hC _ _ hwH hum
  exact ⟨h1, by simpa [mul_assoc] using h2⟩

theorem s7a_sobWeight_mono {a b : ℝ} (hab : a ≤ b) (k : Lattice d) : sobWeight a k ≤ sobWeight b k := by
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (by
    have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    linarith) hab

theorem s7a_conv_step (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (n : ℕ) (h : Torus d → ℝ), Continuous h → MemHs (n : ℝ) (coeffOf h) →
      MemHs ((n : ℝ) + 1) (coeffOf (convFun (periodicRiesz d s) h)) ∧
        HRS.PDE.hsNorm ((n : ℝ) + 1) (coeffOf (convFun (periodicRiesz d s) h)) ≤
          C0 * HRS.PDE.hsNorm (n : ℝ) (coeffOf h) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  set C0 : ℝ := |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0, hC00, fun n h hc hmem => ?_⟩
  have hcoef : ∀ k, coeffOf (convFun (periodicRiesz d s) h) k =
      (rieszCoeff d s k : ℂ) * coeffOf h k := by
    intro k
    unfold coeffOf
    rw [MFAux.funFourierCoeff_convFun F.integrable hc k, F.fourierCoeff k]
  refine s7a_hs_le hC00 hmem (fun k => ?_)
  rw [hcoef k, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := abs_rieszCoeff_le_sobWeight (d := d) s hsd k
  set W : ℝ := sobWeight (-(((d : ℝ) - s) / 2)) k with hW
  have hW0 : 0 ≤ W := MFProduct.sobWeight_nonneg _ k
  have hWW : sobWeight ((n : ℝ) + ((d : ℝ) - s)) k * W ^ 2 = sobWeight (n : ℝ) k := by
    rw [hW, sq, MFProduct.sobWeight_mul, MFProduct.sobWeight_mul]
    congr 1
    ring
  have hg2 : |rieszCoeff d s k| ^ 2 ≤ (C0 * W) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hmono : sobWeight ((n : ℝ) + 1) k ≤ sobWeight ((n : ℝ) + ((d : ℝ) - s)) k :=
    s7a_sobWeight_mono (by linarith) k
  have hw0 : 0 ≤ sobWeight ((n : ℝ) + 1) k := MFProduct.sobWeight_nonneg _ k
  calc sobWeight ((n : ℝ) + 1) k * (|rieszCoeff d s k| * ‖coeffOf h k‖) ^ 2
      = sobWeight ((n : ℝ) + 1) k * (|rieszCoeff d s k| ^ 2 * ‖coeffOf h k‖ ^ 2) := by ring
    _ ≤ sobWeight ((n : ℝ) + 1) k * ((C0 * W) ^ 2 * ‖coeffOf h k‖ ^ 2) := by gcongr
    _ ≤ sobWeight ((n : ℝ) + ((d : ℝ) - s)) k * ((C0 * W) ^ 2 * ‖coeffOf h k‖ ^ 2) := by gcongr
    _ = C0 ^ 2 * (sobWeight (n : ℝ) k * ‖coeffOf h k‖ ^ 2) := by
        rw [← hWW]; ring

end HRS.MC.Sec7.S7a

end
