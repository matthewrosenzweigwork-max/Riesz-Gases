import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldProductB
import HRS.PDE.MeanFieldDefs
import HRS.PDE.EnergySymbol

/-!
# Mean-field equation: mild formulation, bilinear estimate and heat smoothing (package MF-01, P5a)

* `heatMult`, `nlCoeff`, `mfRhsCoeff_eq`: the heat multiplier `e^{-ν4π²|k|²t}` and the nonlinear
  part of `mfRhsCoeff`;
* `hs_mult`: boundedness of a Fourier multiplier `H^a → H^{a+b}`;
* `heatMult_smoothing`: heat smoothing `‖e^{τνΔ}c‖_{H^{a+b}} ≤ C(1+(ντ)^{-b/2})‖c‖_{H^a}` and the
  contraction `‖e^{τνΔ}c‖_{H^a} ≤ ‖c‖_{H^a}`;
* `exists_nl_lipschitz'`: the bilinear estimate for `nlCoeff` (the plan's `exists_nl_lipschitz` is
  false as stated; see the docstring of the corrected variant);
* `isMFSolutionHK_iff_mild`: variation of constants, mode by mode.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE
namespace MFLocal

variable {d : ℕ}

/-- Heat multiplier `e^{-ν 4π²|k|² t}`. -/
noncomputable def heatMult (ν t : ℝ) (k : Lattice d) : ℝ :=
  Real.exp (-ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * t)

/-- The nonlinear part `Div(ρ ∇(V + g⋆ρ))` of `mfRhsCoeff`. -/
noncomputable def nlCoeff (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ρc : Coeff d) : Coeff d :=
  fun k => ∑ j : Fin d, derivCoeff j
    (mulCoeff ρc (fun k' => derivCoeff j (coeffOf V) k' + gradRieszCoeff d s j ρc k')) k

theorem mfRhsCoeff_eq (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (invβ : ℝ) (ρc : Coeff d) (k : Lattice d) :
    mfRhsCoeff d s V invβ ρc k = (invβ : ℂ) * laplaceCoeff ρc k + nlCoeff d s V ρc k := rfl

/-! ### Fourier multipliers -/

/-- A Fourier multiplier with `sobWeight b k ‖m k‖² ≤ B²` maps `H^a → H^{a+b}` with norm `≤ B`. -/
theorem hs_mult (m : Lattice d → ℂ) (a b B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ k, sobWeight b k * ‖m k‖ ^ 2 ≤ B ^ 2) (c : Coeff d) (hc : MemHs a c) :
    MemHs (a + b) (fun k => m k * c k) ∧
      hsNorm (a + b) (fun k => m k * c k) ≤ B * hsNorm a c := by
  have hle : ∀ k, sobWeight (a + b) k * ‖m k * c k‖ ^ 2 ≤ B ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) := by
    intro k
    rw [norm_mul, mul_pow, ← MFProduct.sobWeight_mul a b k]
    have h0 := MFProduct.sobWeight_nonneg a k
    have h1 : 0 ≤ ‖c k‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (hm k) (mul_nonneg h0 h1)]
  have hsum : Summable fun k => B ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) := hc.mul_left _
  have hmem : MemHs (a + b) (fun k => m k * c k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
      hle hsum
  refine ⟨hmem, ?_⟩
  unfold hsNorm hsNormSq
  calc Real.sqrt (∑' k, sobWeight (a + b) k * ‖m k * c k‖ ^ 2)
      ≤ Real.sqrt (B ^ 2 * ∑' k, sobWeight a k * ‖c k‖ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [← tsum_mul_left]
        exact hmem.tsum_le_tsum hle hsum
    _ = B * Real.sqrt (∑' k, sobWeight a k * ‖c k‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]

/-! ### Heat smoothing -/

theorem rpow_le_mul_exp (b x : ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    x ^ b ≤ (max b 1) ^ b * Real.exp x := by
  set c := max b 1 with hc
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc0 : 0 < c := by linarith
  have hbc : b ≤ c := le_max_left _ _
  rcases hx.eq_or_lt with h0 | hxp
  · subst h0
    rw [Real.exp_zero, mul_one]
    rcases hb.eq_or_lt with hb0 | hbp
    · subst hb0; simp
    · rw [Real.zero_rpow hbp.ne']; exact Real.rpow_nonneg hc0.le _
  · have h1 : x / c ≤ Real.exp (x / c - 1) := by
      have := Real.add_one_le_exp (x / c - 1)
      linarith
    have h2 : (x / c) ^ b ≤ Real.exp (x / c - 1) ^ b :=
      Real.rpow_le_rpow (by positivity) h1 hb
    rw [← Real.exp_mul] at h2
    have h3 : x ^ b = c ^ b * (x / c) ^ b := by
      rw [← Real.mul_rpow hc0.le (by positivity)]
      congr 1; field_simp
    rw [h3]
    refine mul_le_mul_of_nonneg_left (h2.trans (Real.exp_le_exp.mpr ?_)) (Real.rpow_nonneg hc0.le _)
    have : (x / c - 1) * b ≤ x / c * c := by
      have : x / c * b ≤ x / c * c := mul_le_mul_of_nonneg_left hbc (by positivity)
      nlinarith
    calc (x / c - 1) * b ≤ x / c * c := this
      _ = x := by field_simp

/-- Pointwise heat-smoothing bound. -/
theorem heat_pointwise (b : ℝ) (hb : 0 ≤ b) (X y : ℝ) (hX : 0 < X) (hy : 0 ≤ y) :
    (1 + y) ^ b * Real.exp (-X * y) ^ 2 ≤
      (2 ^ (b / 2) * (max b 1) ^ (b / 2) * (1 + X ^ (-(b / 2)))) ^ 2 := by
  set c := max b 1 with hc
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc0 : 0 < c := by linarith
  set Z := X ^ (-(b / 2)) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hX _
  have hZZ : X ^ b * (Z * Z) = 1 := by
    rw [hZ, ← Real.rpow_add hX, ← Real.rpow_add hX]
    have : b + (-(b / 2) + -(b / 2)) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hAA : (2 : ℝ) ^ (b / 2) * 2 ^ (b / 2) = 2 ^ b := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hCC : c ^ (b / 2) * c ^ (b / 2) = c ^ b := by
    rw [← Real.rpow_add hc0]; congr 1; ring
  -- (1+y)^b ≤ 2^b (1 + y^b)
  have h1 : (1 + y) ^ b ≤ 2 ^ b * (1 + y ^ b) := by
    have : 1 + y ≤ 2 * max 1 y := by
      rcases le_total 1 y with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (1 + y) ^ b ≤ (2 * max 1 y) ^ b := Real.rpow_le_rpow (by linarith) this hb
      _ = 2 ^ b * (max 1 y) ^ b := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 ^ b * (1 + y ^ b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total 1 y with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg (zero_le_one : (0 : ℝ) ≤ 1) b]
        · rw [max_eq_left h, Real.one_rpow]; linarith [Real.rpow_nonneg hy b]
  -- y^b e^{-2Xy} ≤ c^b Z²
  have h2 : y ^ b * Real.exp (-X * y) ^ 2 ≤ c ^ b * (Z * Z) := by
    have hexp : Real.exp (-X * y) ^ 2 = Real.exp (-(2 * (X * y))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 := rpow_le_mul_exp b (X * y) hb (by positivity)
    rw [Real.mul_rpow hX.le hy] at h3
    have h4 : X ^ b * y ^ b * Real.exp (-(2 * (X * y))) ≤ c ^ b := by
      calc X ^ b * y ^ b * Real.exp (-(2 * (X * y)))
          ≤ c ^ b * Real.exp (X * y) * Real.exp (-(2 * (X * y))) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = c ^ b * Real.exp (-(X * y)) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ c ^ b * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc0.le _)
            rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hX.le hy]
        _ = c ^ b := mul_one _
    rw [hexp]
    have hXb : 0 < X ^ b := Real.rpow_pos_of_pos hX _
    calc y ^ b * Real.exp (-(2 * (X * y)))
        = (Z * Z) * (X ^ b * y ^ b * Real.exp (-(2 * (X * y)))) := by
          have : (Z * Z) * X ^ b = 1 := by rw [mul_comm]; exact hZZ
          calc y ^ b * Real.exp (-(2 * (X * y)))
              = ((Z * Z) * X ^ b) * (y ^ b * Real.exp (-(2 * (X * y)))) := by rw [this, one_mul]
            _ = _ := by ring
      _ ≤ (Z * Z) * c ^ b := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = c ^ b * (Z * Z) := by ring
  have h5 : Real.exp (-X * y) ^ 2 ≤ 1 := by
    have : Real.exp (-X * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hX.le hy]
    have h0 := (Real.exp_pos (-X * y)).le
    nlinarith
  have hcb : 1 ≤ c ^ b := Real.one_le_rpow hc1 hb
  have hW0 : 0 ≤ Real.exp (-X * y) ^ 2 := sq_nonneg _
  calc (1 + y) ^ b * Real.exp (-X * y) ^ 2
      ≤ 2 ^ b * (1 + y ^ b) * Real.exp (-X * y) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hW0
    _ = 2 ^ b * (Real.exp (-X * y) ^ 2 + y ^ b * Real.exp (-X * y) ^ 2) := by ring
    _ ≤ 2 ^ b * (1 + c ^ b * (Z * Z)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ (2 ^ (b / 2) * c ^ (b / 2) * (1 + Z)) ^ 2 := by
        have : (2 ^ (b / 2) * c ^ (b / 2) * (1 + Z)) ^ 2 =
            (2 ^ (b / 2) * 2 ^ (b / 2)) * ((c ^ (b / 2) * c ^ (b / 2)) * (1 + Z) ^ 2) := by ring
        rw [this, hAA, hCC]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hz : 0 ≤ Z := hZ0.le
        nlinarith [mul_nonneg hz hz, mul_le_mul_of_nonneg_right hcb (mul_nonneg hz hz)]

/-- Heat smoothing and contraction: for `ν > 0`, `b ≥ 0` there is `C` with, for all `τ > 0`,
`‖e^{τνΔ}c‖_{H^{a+b}} ≤ C (1 + (ντ)^{-b/2}) ‖c‖_{H^a}` and `‖e^{τνΔ}c‖_{H^a} ≤ ‖c‖_{H^a}`. -/
theorem heatMult_smoothing (ν : ℝ) (hν : 0 < ν) (a b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ c : Coeff d, MemHs a c →
      (MemHs (a + b) (fun k => (heatMult ν τ k : ℂ) * c k) ∧
        hsNorm (a + b) (fun k => (heatMult ν τ k : ℂ) * c k) ≤
          C * (1 + (ν * τ) ^ (-(b / 2))) * hsNorm a c) ∧
      (MemHs a (fun k => (heatMult ν τ k : ℂ) * c k) ∧
        hsNorm a (fun k => (heatMult ν τ k : ℂ) * c k) ≤ hsNorm a c) := by
  refine ⟨2 ^ (b / 2) * (max b 1) ^ (b / 2), by positivity, fun τ hτ c hc => ⟨?_, ?_⟩⟩
  · have hX : 0 < ν * τ := mul_pos hν hτ
    have hB : 0 ≤ 2 ^ (b / 2) * (max b 1) ^ (b / 2) * (1 + (ν * τ) ^ (-(b / 2))) := by positivity
    have := hs_mult (fun k : Lattice d => (heatMult ν τ k : ℂ)) a b _ hB (fun k => ?_) c hc
    · exact ⟨this.1, this.2⟩
    · have h := heat_pointwise b hb (ν * τ) (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) hX (by positivity)
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold heatMult sobWeight
      convert h using 4
      ring
  · have hB : (0 : ℝ) ≤ 1 := zero_le_one
    have := hs_mult (fun k : Lattice d => (heatMult ν τ k : ℂ)) a 0 1 hB (fun k => ?_) c hc
    · simpa using this
    · have hh : heatMult ν τ k ≤ 1 := by
        unfold heatMult
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * τ := by positivity
        nlinarith
      have h0 : 0 ≤ heatMult ν τ k := (Real.exp_pos _).le
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sobWeight_zero]
      nlinarith

/-! ### Elementary `H^m` calculus -/

theorem hsNorm_nonneg (m : ℝ) (c : Coeff d) : 0 ≤ hsNorm m c := Real.sqrt_nonneg _

theorem memHs_mono {m n : ℝ} (hmn : m ≤ n) {c : Coeff d} (hc : MemHs n c) : MemHs m c := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (MFProduct.sobWeight_nonneg m k) (sq_nonneg _)) (fun k => ?_) hc
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]) hmn

theorem memHs_zero_coeff (m : ℝ) : MemHs m (0 : Coeff d) := by
  simp [MemHs]

theorem hsNorm_zero_coeff (m : ℝ) : hsNorm m (0 : Coeff d) = 0 := by
  simp [hsNorm, hsNormSq]

theorem sobWeight_half_sq' (m : ℝ) (k : Lattice d) (x : ℂ) :
    sobWeight m k * ‖x‖ ^ 2 = (sobWeight (m / 2) k * ‖x‖) ^ 2 := by
  rw [mul_pow, MFProduct.sobWeight_half_sq]

theorem hsNorm_eq_sqrt (m : ℝ) (c : Coeff d) :
    hsNorm m c = Real.sqrt (∑' k, (sobWeight (m / 2) k * ‖c k‖) ^ 2) := by
  unfold hsNorm hsNormSq
  congr 1; exact tsum_congr fun k => sobWeight_half_sq' m k _

/-- Triangle inequality in `H^m`. -/
theorem memHs_add_le (m : ℝ) {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    MemHs m (f + g) ∧ hsNorm m (f + g) ≤ hsNorm m f + hsNorm m g := by
  set P : Lattice d → ℝ := fun k => sobWeight (m / 2) k * ‖f k‖ with hP
  set Q : Lattice d → ℝ := fun k => sobWeight (m / 2) k * ‖g k‖ with hQ
  have hP0 : ∀ k, 0 ≤ P k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hP2 : Summable fun k => P k ^ 2 := hf.congr fun k => sobWeight_half_sq' m k _
  have hQ2 : Summable fun k => Q k ^ 2 := hg.congr fun k => sobWeight_half_sq' m k _
  obtain ⟨hs, hle⟩ := MFProduct.minkowski_sq P Q hP0 hQ0 hP2 hQ2
  have hpt : ∀ k, sobWeight m k * ‖(f + g) k‖ ^ 2 ≤ (P k + Q k) ^ 2 := by
    intro k
    rw [sobWeight_half_sq']
    have : sobWeight (m / 2) k * ‖(f + g) k‖ ≤ P k + Q k := by
      have h := norm_add_le (f k) (g k)
      have hw := MFProduct.sobWeight_nonneg (m / 2) k
      calc sobWeight (m / 2) k * ‖(f + g) k‖ ≤ sobWeight (m / 2) k * (‖f k‖ + ‖g k‖) :=
            mul_le_mul_of_nonneg_left h hw
        _ = _ := by simp only [hP, hQ]; ring
    exact pow_le_pow_left₀ (mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)) this 2
  have hmem : MemHs m (f + g) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
      hpt hs
  refine ⟨hmem, ?_⟩
  rw [hsNorm_eq_sqrt, hsNorm_eq_sqrt m f, hsNorm_eq_sqrt m g]
  refine le_trans (Real.sqrt_le_sqrt ?_) hle
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ hs
  · rw [← sobWeight_half_sq']; exact hpt k
  · exact hmem.congr fun k => sobWeight_half_sq' m k _

theorem memHs_neg {m : ℝ} {f : Coeff d} (hf : MemHs m f) : MemHs m (-f) := by
  simpa [MemHs] using hf

theorem memHs_sub_aux {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    MemHs m (f - g) := by
  rw [sub_eq_add_neg]; exact (memHs_add_le m hf (memHs_neg hg)).1

/-- Triangle inequality for finite sums. -/
theorem memHs_finsum_le {ι : Type*} (m : ℝ) (S : Finset ι) (F : ι → Coeff d)
    (hF : ∀ i ∈ S, MemHs m (F i)) :
    MemHs m (fun k => ∑ i ∈ S, F i k) ∧
      hsNorm m (fun k => ∑ i ∈ S, F i k) ≤ ∑ i ∈ S, hsNorm m (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨memHs_zero_coeff m, le_of_eq (hsNorm_zero_coeff m)⟩
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have h := memHs_add_le m (hF a (Finset.mem_insert_self a S)) ih1
    simp only [Finset.sum_insert ha]
    exact ⟨h.1, h.2.trans (by linarith)⟩

/-! ### Multiplication: linearity -/

theorem mulCoeff_diff_aux {a a' c c' : Coeff d} (ha : MemHs 0 a) (ha' : MemHs 0 a')
    (hc : MemHs 0 c) (hc' : MemHs 0 c') :
    mulCoeff a c - mulCoeff a' c' = mulCoeff (a - a') c + mulCoeff a' (c - c') := by
  funext k
  have h1 : Summable fun j => (a (k - j) - a' (k - j)) * c j :=
    summable_mulCoeff (a - a') c (memHs_sub_aux ha ha') hc k
  have h2 : Summable fun j => a' (k - j) * (c j - c' j) :=
    summable_mulCoeff a' (c - c') ha' (memHs_sub_aux hc hc') k
  have h3 := summable_mulCoeff a c ha hc k
  have h4 := summable_mulCoeff a' c' ha' hc' k
  simp only [mulCoeff, Pi.sub_apply, Pi.add_apply]
  rw [← h3.tsum_sub h4, ← h1.tsum_add h2]
  refine tsum_congr fun j => ?_
  ring

/-! ### Derivative and Riesz-gradient multipliers -/

/-- `∂_j : H^m → H^{m-1}` is a contraction. -/
theorem hs_deriv (j : Fin d) (m : ℝ) (c : Coeff d) (hc : MemHs m c) :
    MemHs (m + -1) (derivCoeff j c) ∧ hsNorm (m + -1) (derivCoeff j c) ≤ hsNorm m c := by
  have := hs_mult (fun k : Lattice d => (2 * Real.pi * Complex.I * (k j : ℂ))) m (-1) 1
    zero_le_one (fun k => ?_) c hc
  · rw [one_mul] at this
    exact this
  · have hW : 0 < sobWeight 1 k := sobWeight_pos 1 k
    have h1 : ‖(2 * Real.pi * Complex.I * (k j : ℂ))‖ = |2 * Real.pi * (k j : ℝ)| := by
      simp [Complex.norm_I, abs_of_pos Real.pi_pos, abs_mul]
    rw [h1]
    have h2 := abs_two_pi_le_rad k j
    have h3 := rad_sq_le k
    have h4 : |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ sobWeight 1 k := by
      have : |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ rad k ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
      unfold sobWeight; rw [Real.rpow_one]; linarith
    have h5 : sobWeight (-1) k = (sobWeight 1 k)⁻¹ := by
      unfold sobWeight; rw [Real.rpow_neg_one, Real.rpow_one]
    rw [h5, one_pow]
    calc (sobWeight 1 k)⁻¹ * |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ (sobWeight 1 k)⁻¹ * sobWeight 1 k :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hW.le)
      _ = 1 := inv_mul_cancel₀ hW.ne'

/-- `∂_i g * : H^m → H^{m + δ' - 1}` for `δ' ≤ min (d - s) 1`. -/
theorem hs_gradRiesz (s : ℝ) (i : Fin d) (m δ' : ℝ) (h1 : δ' ≤ 1) (h2 : δ' ≤ (d : ℝ) - s)
    (c : Coeff d) (hc : MemHs m c) :
    MemHs (m + (δ' - 1)) (gradRieszCoeff d s i c) ∧
      hsNorm (m + (δ' - 1)) (gradRieszCoeff d s i c) ≤ |rieszConst d s| * hsNorm m c := by
  have := hs_mult (fun k : Lattice d =>
      (2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) m (δ' - 1)
    |rieszConst d s| (abs_nonneg _) (fun k => ?_) c hc
  · have e : (fun k : Lattice d => (2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ) * c k) = gradRieszCoeff d s i c := by
      funext k; simp [gradRieszCoeff, derivCoeff, rieszMult, mul_assoc]
    rwa [e] at this
  · by_cases hk : k = 0
    · subst hk
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · have hr : 1 ≤ rad k := one_le_rad k hk
      have hr0 : 0 < rad k := by linarith
      have hn := norm_symS_le s i k hk
      set e : ℝ := s - (d : ℝ) + 1 with he
      set W : ℝ := 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hW
      have hW1 : 1 ≤ W := by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]
      have hrr : rad k * rad k ≤ W := by
        have := rad_sq_le k
        nlinarith
      have hrr1 : 1 ≤ rad k * rad k := by nlinarith
      have key : sobWeight (δ' - 1) k * (rad k ^ e * rad k ^ e) ≤ 1 := by
        rw [← Real.mul_rpow hr0.le hr0.le]
        have hWb : sobWeight (δ' - 1) k = W ^ (δ' - 1) := rfl
        rw [hWb]
        rcases le_or_gt 0 e with he0 | he0
        · have h6 : (rad k * rad k) ^ e ≤ W ^ e :=
            Real.rpow_le_rpow (by positivity) hrr he0
          calc W ^ (δ' - 1) * (rad k * rad k) ^ e
              ≤ W ^ (δ' - 1) * W ^ e :=
                mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg (by linarith) _)
            _ = W ^ ((δ' - 1) + e) := (Real.rpow_add (by linarith) _ _).symm
            _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by rw [he]; linarith)
        · have h6 : (rad k * rad k) ^ e ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hrr1 he0.le
          have h7 : W ^ (δ' - 1) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
          calc W ^ (δ' - 1) * (rad k * rad k) ^ e
              ≤ 1 * 1 := mul_le_mul h7 h6 (Real.rpow_nonneg (by positivity) _)
                (by norm_num)
            _ = 1 := by norm_num
      have hsq : ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)‖ ^ 2 ≤
          |rieszConst d s| ^ 2 * (rad k ^ e * rad k ^ e) := by
        calc _ ≤ (|rieszConst d s| * rad k ^ e) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hn 2
          _ = _ := by ring
      calc sobWeight (δ' - 1) k * ‖(2 * Real.pi * Complex.I * (k i : ℂ)) *
            ((rieszCoeff d s k : ℝ) : ℂ)‖ ^ 2
          ≤ sobWeight (δ' - 1) k * (|rieszConst d s| ^ 2 * (rad k ^ e * rad k ^ e)) :=
            mul_le_mul_of_nonneg_left hsq (MFProduct.sobWeight_nonneg _ k)
        _ = |rieszConst d s| ^ 2 * (sobWeight (δ' - 1) k * (rad k ^ e * rad k ^ e)) := by ring
        _ ≤ |rieszConst d s| ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left key (sq_nonneg _)
        _ = _ := mul_one _

/-! ### The bilinear estimate -/

theorem gradRieszCoeff_sub_aux (s : ℝ) (i : Fin d) (c₁ c₂ : Coeff d) :
    gradRieszCoeff d s i (c₁ - c₂) = gradRieszCoeff d s i c₁ - gradRieszCoeff d s i c₂ := by
  funext k
  simp only [gradRieszCoeff, rieszMult, derivCoeff, Pi.sub_apply]
  ring

theorem derivCoeff_sub_aux (j : Fin d) (a b : Coeff d) :
    derivCoeff j (a - b) = derivCoeff j a - derivCoeff j b := by
  funext k
  simp only [derivCoeff, Pi.sub_apply]
  ring

/-- **Corrected bilinear estimate.**  The plan's `exists_nl_lipschitz` (with the right-hand side
`C (‖ρ‖ + ‖ρ'‖) ‖ρ - ρ'‖` and `V ∈ C²`) is false as stated: the part `∑_j ∂_j(ρ ∂_jV)` of `nlCoeff`
is linear in `ρ`, so for `ρ = 0`, `ρ' = ε δ_k` the left side is of order `ε` while the right side is of
order `ε²` as soon as `V` is not constant; moreover `V ∈ C²` does not put `∂_jV` in `H^{K-1+δ'}`
for large `K`.  Here the right side is `C (1 + ‖ρ‖ + ‖ρ'‖) ‖ρ - ρ'‖` and `V` is assumed to satisfy
`V̂ ∈ H^{K+δ'}` (e.g. `V ∈ C^{K+2}` with `K` an integer, `δ' < 1`). -/
theorem exists_nl_lipschitz' (_hd : 1 ≤ d) (s : ℝ) (_hs0 : 0 ≤ s) (_hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (δ' : ℝ) (hδ0 : 0 ≤ δ')
    (hδ : δ' < min ((d : ℝ) - s) 1) (hV : MemHs (K + δ') (coeffOf V)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρc ρc' : Coeff d, MemHs K ρc → MemHs K ρc' →
      MemHs (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ∧
      hsNorm (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ≤
        C * (1 + hsNorm K ρc + hsNorm K ρc') * hsNorm K (ρc - ρc') := by
  have hδ1 : δ' < (d : ℝ) - s := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδ2 : δ' < 1 := lt_of_lt_of_le hδ (min_le_right _ _)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set c0 : ℝ := K - 1 + δ' with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; linarith
  have hc0K : c0 ≤ K := by rw [hc0]; linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨P, hP0, hP⟩ := MFProduct.exists_product_bound (d := d) K c0 c0 hc00 hc0K le_rfl (by linarith)
  -- the potential part
  have hv : ∀ j : Fin d, MemHs c0 (derivCoeff j (coeffOf V)) := by
    intro j
    have := (hs_deriv j (K + δ') (coeffOf V) hV).1
    rwa [show K + δ' + -1 = c0 by rw [hc0]; ring] at this
  set Mv : ℝ := ∑ j : Fin d, hsNorm c0 (derivCoeff j (coeffOf V)) with hMv
  have hMv0 : 0 ≤ Mv := Finset.sum_nonneg fun j _ => hsNorm_nonneg _ _
  set Cg : ℝ := |rieszConst d s| with hCg
  -- the interaction part
  have hG : ∀ (j : Fin d) (ρ : Coeff d), MemHs K ρ →
      MemHs c0 (gradRieszCoeff d s j ρ) ∧ hsNorm c0 (gradRieszCoeff d s j ρ) ≤ Cg * hsNorm K ρ := by
    intro j ρ hρ
    have := hs_gradRiesz s j K δ' hδ2.le hδ1.le ρ hρ
    rwa [show K + (δ' - 1) = c0 by rw [hc0]; ring] at this
  refine ⟨P * (Mv + d * Cg), by positivity, fun ρ ρ' hρ hρ' => ?_⟩
  have hΔ : MemHs K (ρ - ρ') := memHs_sub_aux hρ hρ'
  set Δ : Coeff d := ρ - ρ' with hΔdef
  have hρ0 : MemHs 0 ρ := memHs_mono hK0 hρ
  have hρ'0 : MemHs 0 ρ' := memHs_mono hK0 hρ'
  -- per-mode estimates
  have hmode : ∀ j : Fin d,
      MemHs (K - 2 + δ') (derivCoeff j (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
          mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ'))) ∧
        hsNorm (K - 2 + δ') (derivCoeff j (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
          mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ'))) ≤
        P * hsNorm K Δ * (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) +
          P * hsNorm K ρ' * (Cg * hsNorm K Δ) := by
    intro j
    obtain ⟨hGρ, hGρn⟩ := hG j ρ hρ
    obtain ⟨hGρ', -⟩ := hG j ρ' hρ'
    obtain ⟨hGΔ, hGΔn⟩ := hG j Δ hΔ
    have hvj := hv j
    obtain ⟨hw, hwn⟩ := memHs_add_le c0 hvj hGρ
    have hw' := (memHs_add_le c0 hvj hGρ').1
    have hid : mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
        mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ') =
        mulCoeff Δ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) +
          mulCoeff ρ' (gradRieszCoeff d s j Δ) := by
      rw [mulCoeff_diff_aux hρ0 hρ'0 (memHs_mono hc00 hw) (memHs_mono hc00 hw')]
      congr 2
      rw [hΔdef, gradRieszCoeff_sub_aux]
      abel
    rw [hid]
    obtain ⟨hA, hAn⟩ := hP Δ _ hΔ hw
    obtain ⟨hB, hBn⟩ := hP ρ' _ hρ' hGΔ
    obtain ⟨hE, hEn⟩ := memHs_add_le c0 hA hB
    obtain ⟨hF, hFn⟩ := hs_deriv j c0 _ hE
    rw [show c0 + -1 = K - 2 + δ' by rw [hc0]; ring] at hF hFn
    refine ⟨hF, hFn.trans (hEn.trans ?_)⟩
    have h1 : P * hsNorm K Δ * hsNorm c0 (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) ≤
        P * hsNorm K Δ * (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) :=
      mul_le_mul_of_nonneg_left (hwn.trans (by linarith)) (by positivity [hsNorm_nonneg K Δ])
    have h2 : P * hsNorm K ρ' * hsNorm c0 (gradRieszCoeff d s j Δ) ≤
        P * hsNorm K ρ' * (Cg * hsNorm K Δ) :=
      mul_le_mul_of_nonneg_left hGΔn (by positivity [hsNorm_nonneg K ρ'])
    linarith
  -- assemble
  have hsum : nlCoeff d s V ρ - nlCoeff d s V ρ' = fun k => ∑ j : Fin d, derivCoeff j
      (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
        mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ')) k := by
    funext k
    simp only [nlCoeff, Pi.sub_apply, ← Finset.sum_sub_distrib, derivCoeff_sub_aux]
    rfl
  rw [hsum]
  obtain ⟨h1, h2⟩ := memHs_finsum_le (K - 2 + δ') Finset.univ _ (fun j _ => (hmode j).1)
  refine ⟨h1, h2.trans ?_⟩
  refine (Finset.sum_le_sum fun j _ => (hmode j).2).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : ∑ j : Fin d, (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) =
      Mv + d * (Cg * hsNorm K ρ) := by
    rw [Finset.sum_add_distrib, hMv]
    simp
  rw [e1]
  have hx := hsNorm_nonneg K ρ
  have hy := hsNorm_nonneg K ρ'
  have hz := hsNorm_nonneg K Δ
  have hCg0 : 0 ≤ Cg := abs_nonneg _
  have hdC : 0 ≤ (d : ℝ) * Cg := by positivity
  have hPz : 0 ≤ P * hsNorm K Δ := mul_nonneg hP0 hz
  nlinarith [mul_nonneg hPz (mul_nonneg hMv0 hx), mul_nonneg hPz (mul_nonneg hMv0 hy),
    mul_nonneg hPz hdC]

/-! ### Variation of constants for a scalar linear ODE with integrable forcing -/

theorem tri_swap (φ' : ℝ → ℝ) (hφ' : Continuous φ') (g : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hg : IntegrableOn g (Set.Icc 0 t)) :
    ∫ σ in (0 : ℝ)..t, φ' σ • ∫ r in (0 : ℝ)..σ, g r =
      ∫ r in (0 : ℝ)..t, (∫ σ in r..t, φ' σ) • g r := by
  have hgI : IntegrableOn g (Set.Ioc 0 t) := hg.mono_set Set.Ioc_subset_Icc_self
  have hφI : IntegrableOn φ' (Set.Ioc 0 t) :=
    (hφ'.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  set H : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => φ' p.1 • g p.2) with hHdef
  have hH : Integrable H ((volume.restrict (Set.Ioc 0 t)).prod (volume.restrict (Set.Ioc 0 t))) := by
    have := Integrable.smul_prod hφI hgI
    exact this.indicator (measurableSet_le measurable_snd measurable_fst)
  have hswap := integral_integral_swap (f := fun σ r => H (σ, r)) hH
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  have e1 : ∀ σ ∈ Set.Ioc 0 t, ∫ r in Set.Ioc 0 t, H (σ, r) =
      φ' σ • ∫ r in Set.Ioc (0 : ℝ) σ, g r := by
    intro σ hσ
    have : (fun r => H (σ, r)) = Set.indicator (Set.Iic σ) (fun r => φ' σ • g r) := by
      funext r
      by_cases h : r ≤ σ <;> simp [hHdef, h]
    simp only [this]
    rw [setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, min_eq_right hσ.2,
      integral_smul]
  have e2 : ∀ r ∈ Set.Ioc 0 t, ∫ σ in Set.Ioc 0 t, H (σ, r) =
      (∫ σ in r..t, φ' σ) • g r := by
    intro r hr
    have : (fun σ => H (σ, r)) = Set.indicator (Set.Ici r) (fun σ => φ' σ • g r) := by
      funext σ
      by_cases h : r ≤ σ <;> simp [hHdef, h]
    simp only [this]
    rw [setIntegral_indicator measurableSet_Ici]
    have hset : Set.Ioc 0 t ∩ Set.Ici r = Set.Icc r t := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hr.1 h1, h2⟩, h1⟩
    rw [hset, integral_smul_const, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr.2]
  calc ∫ σ in Set.Ioc 0 t, φ' σ • ∫ r in (0 : ℝ)..σ, g r
      = ∫ σ in Set.Ioc 0 t, φ' σ • ∫ r in Set.Ioc (0 : ℝ) σ, g r :=
        setIntegral_congr_fun measurableSet_Ioc fun σ hσ => by
          simp only [intervalIntegral.integral_of_le hσ.1.le]
    _ = ∫ σ in Set.Ioc 0 t, ∫ r in Set.Ioc 0 t, H (σ, r) :=
        (setIntegral_congr_fun measurableSet_Ioc fun σ hσ => (e1 σ hσ).symm)
    _ = ∫ r in Set.Ioc 0 t, ∫ σ in Set.Ioc 0 t, H (σ, r) := hswap
    _ = ∫ r in Set.Ioc 0 t, (∫ σ in r..t, φ' σ) • g r :=
        setIntegral_congr_fun measurableSet_Ioc fun r hr => e2 r hr

/-- The mild-formula function `e^{-λτ}(u₀ + ∫₀^τ e^{λσ} f σ dσ)`. -/
noncomputable def mildFn (lam : ℝ) (u0 : ℂ) (f : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ((Real.exp (-lam * τ) : ℝ) : ℂ) * (u0 + ∫ σ in (0 : ℝ)..τ, ((Real.exp (lam * σ) : ℝ) : ℂ) * f σ)

theorem integrableOn_exp_mul (lam : ℝ) (f : ℝ → ℂ) (t : ℝ) (hf : IntegrableOn f (Set.Icc 0 t)) :
    IntegrableOn (fun σ => ((Real.exp (lam * σ) : ℝ) : ℂ) * f σ) (Set.Icc 0 t) := by
  exact IntegrableOn.continuousOn_mul (g := fun σ => ((Real.exp (lam * σ) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn hf isCompact_Icc

theorem continuousOn_mildFn (lam : ℝ) (u0 : ℂ) (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IntegrableOn f (Set.Icc 0 t)) : ContinuousOn (mildFn lam u0 f) (Set.Icc 0 t) := by
  have hg := integrableOn_exp_mul lam f t hf
  have hQ : ContinuousOn (fun τ => ∫ σ in (0 : ℝ)..τ, ((Real.exp (lam * σ) : ℝ) : ℂ) * f σ)
      (Set.Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t)
      (f := fun σ => ((Real.exp (lam * σ) : ℝ) : ℂ) * f σ) (μ := volume)
      (by rwa [Set.uIcc_of_le ht])
    rwa [Set.uIcc_of_le ht] at this
  refine ContinuousOn.mul ?_ (continuousOn_const.add hQ)
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).continuousOn

/-- `mildFn` solves the integrated equation (Fubini on the triangle). -/
theorem mildFn_integrated (lam : ℝ) (u0 : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t, 0 ≤ t → IntegrableOn f (Set.Icc 0 t)) (t : ℝ) (ht : 0 ≤ t) :
    mildFn lam u0 f t = u0 + ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * mildFn lam u0 f σ + f σ) := by
  set g : ℝ → ℂ := fun σ => ((Real.exp (lam * σ) : ℝ) : ℂ) * f σ with hgdef
  have hft := hf t ht
  have hg : IntegrableOn g (Set.Icc 0 t) := integrableOn_exp_mul lam f t hft
  set Q : ℝ → ℂ := fun τ => ∫ σ in (0 : ℝ)..τ, g σ with hQdef
  have hQc : ContinuousOn Q (Set.Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t) (f := g)
      (μ := volume) (by rwa [Set.uIcc_of_le ht])
    rwa [Set.uIcc_of_le ht] at this
  set ψ : ℝ → ℝ := fun σ => Real.exp (-lam * σ) with hψ
  set φ' : ℝ → ℝ := fun σ => -lam * ψ σ with hφ'
  have hψc : Continuous ψ := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hφ'c : Continuous φ' := continuous_const.mul hψc
  have hψd : ∀ x, HasDerivAt ψ (φ' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -lam * y) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    refine (h1.exp).congr_deriv ?_
    simp only [hφ', hψ]; ring
  have hint_φ : ∀ a b : ℝ, ∫ σ in a..b, φ' σ = ψ b - ψ a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hψd x)
      (hφ'c.intervalIntegrable _ _)
  -- the integrand
  have hint_eq : ∀ σ, -(lam : ℂ) * mildFn lam u0 f σ + f σ = φ' σ • (u0 + Q σ) + f σ := by
    intro σ
    simp only [mildFn, hφ', hψ, hQdef, hgdef, Complex.real_smul]
    push_cast
    ring
  simp_rw [hint_eq]
  have hI1 : IntervalIntegrable (fun σ => φ' σ • u0) volume 0 t :=
    (hφ'c.smul continuous_const).intervalIntegrable (0 : ℝ) t
  have hI2 : IntervalIntegrable (fun σ => φ' σ • Q σ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht]
    exact hφ'c.continuousOn.smul hQc
  have hI3 : IntervalIntegrable f volume 0 t := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  have hsplit : ∫ σ in (0 : ℝ)..t, (φ' σ • (u0 + Q σ) + f σ) =
      (∫ σ in (0 : ℝ)..t, φ' σ • u0) + (∫ σ in (0 : ℝ)..t, φ' σ • Q σ) +
        ∫ σ in (0 : ℝ)..t, f σ := by
    simp_rw [smul_add]
    rw [intervalIntegral.integral_add (hI1.add hI2) hI3, intervalIntegral.integral_add hI1 hI2]
  have hA : ∫ σ in (0 : ℝ)..t, φ' σ • u0 = (ψ t - ψ 0) • u0 := by
    rw [intervalIntegral.integral_smul_const, hint_φ]
  have hgI : IntervalIntegrable g volume 0 t := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  have hψg : ∀ r, ψ r • g r = f r := by
    intro r
    simp only [hψ, hgdef, Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hB : ∫ σ in (0 : ℝ)..t, φ' σ • Q σ = ψ t • (∫ r in (0 : ℝ)..t, g r) -
      ∫ r in (0 : ℝ)..t, f r := by
    have h1 := tri_swap φ' hφ'c g t ht hg
    have h2 : ∀ r, (∫ σ in r..t, φ' σ) • g r = ψ t • g r - ψ r • g r := by
      intro r; rw [hint_φ, sub_smul]
    simp_rw [h2] at h1
    have h3 : IntervalIntegrable (fun r => ψ r • g r) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr
        (hg.continuousOn_smul hψc.continuousOn isCompact_Icc)
    have hX : IntervalIntegrable (fun r => ψ t • g r) volume 0 t := hgI.smul (ψ t)
    have h4 : ∫ r in (0 : ℝ)..t, (ψ t • g r - ψ r • g r) =
        (∫ r in (0 : ℝ)..t, ψ t • g r) - ∫ r in (0 : ℝ)..t, ψ r • g r :=
      intervalIntegral.integral_sub hX h3
    rw [show (∫ σ in (0 : ℝ)..t, φ' σ • Q σ) = _ from h1, h4, intervalIntegral.integral_smul]
    simp_rw [hψg]
  rw [hsplit, hA, hB]
  have hψ0 : ψ 0 = 1 := by simp [hψ]
  show ((ψ t : ℝ) : ℂ) * (u0 + ∫ σ in (0 : ℝ)..t, g σ) = u0 + ((ψ t - ψ 0) • u0 +
    ((ψ t • (∫ r in (0 : ℝ)..t, g r)) - ∫ r in (0 : ℝ)..t, f r) + ∫ r in (0 : ℝ)..t, f r)
  rw [hψ0]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- A continuous solution of `w(t) = -λ ∫₀ᵗ w` on `[0,T]` vanishes. -/
theorem ode_zero (lam : ℝ) (T : ℝ) (hT : 0 ≤ T) (w : ℝ → ℂ) (hw : ContinuousOn w (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc 0 T, w t = -(lam : ℂ) * ∫ σ in (0 : ℝ)..t, w σ) :
    ∀ t ∈ Set.Icc 0 T, w t = 0 := by
  set W : ℝ → ℂ := fun t => ∫ σ in (0 : ℝ)..t, w σ with hW
  have hderivW : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt W (w x) (Set.Ici x) x := by
    intro x hx
    have hxT : x ∈ Set.Icc 0 T := ⟨hx.1, hx.2.le⟩
    have hII : IntervalIntegrable w volume 0 x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hx.1]
      exact hw.mono (Set.Icc_subset_Icc le_rfl hx.2.le)
    have hmem : Set.Icc 0 T ∈ 𝓝[Set.Ioi x] x := Icc_mem_nhdsGT_of_mem hx
    have hmeas : StronglyMeasurableAtFilter w (𝓝[Set.Ioi x] x) volume :=
      ⟨Set.Icc 0 T, hmem, hw.aestronglyMeasurable measurableSet_Icc⟩
    have hb : ContinuousWithinAt w (Set.Ioi x) x :=
      (hw x hxT).mono_of_mem_nhdsWithin hmem
    exact intervalIntegral.integral_hasDerivWithinAt_right hII hmeas hb
  set z : ℝ → ℂ := fun t => ((Real.exp (lam * t) : ℝ) : ℂ) * w t with hz
  have hexpd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ((Real.exp (lam * t) : ℝ) : ℂ))
      (((lam * Real.exp (lam * x) : ℝ) : ℂ)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => lam * y) lam x := by
      simpa using (hasDerivAt_id x).const_mul lam
    exact (h1.exp.congr_deriv (by ring)).ofReal_comp
  have hzc : ContinuousOn z (Set.Icc 0 T) :=
    ContinuousOn.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn hw
  have hzd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt z 0 (Set.Ici x) x := by
    intro x hx
    have hy := ((hexpd x).hasDerivWithinAt (s := Set.Icc x T)).mul
      (((hderivW x hx).mono Set.Icc_subset_Ici_self).const_mul (-(lam : ℂ)))
    have hwx := h x ⟨hx.1, hx.2.le⟩
    have h0 : ((lam * Real.exp (lam * x) : ℝ) : ℂ) * (-(lam : ℂ) * W x) +
        ((Real.exp (lam * x) : ℝ) : ℂ) * (-(lam : ℂ) * w x) = 0 := by
      rw [hwx]; simp only [hW]; push_cast; ring
    rw [h0] at hy
    have hz' : HasDerivWithinAt z 0 (Set.Icc x T) x := by
      refine hy.congr (fun t ht => ?_) ?_
      · simp only [hz, hW]
        rw [h t ⟨hx.1.trans ht.1, ht.2⟩]
        rfl
      · simp only [hz, hW]
        rw [h x ⟨hx.1, hx.2.le⟩]
        rfl
    exact hz'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hx.2)
  intro t ht
  have h1 := constant_of_has_deriv_right_zero hzc hzd t ht
  have h0 : w 0 = 0 := by
    rw [h 0 ⟨le_rfl, hT⟩]; simp
  have h2 : z t = 0 := by rw [h1]; simp [hz, h0]
  simp only [hz] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by exact_mod_cast (Real.exp_pos _).ne')
  · exact h3

theorem mildFn_eq (lam : ℝ) (u0 : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    mildFn lam u0 f t = ((Real.exp (-lam * t) : ℝ) : ℂ) * u0 +
      ∫ σ in (0 : ℝ)..t, ((Real.exp (-lam * (t - σ)) : ℝ) : ℂ) * f σ := by
  unfold mildFn
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun σ _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

/-- Variation of constants for a scalar linear ODE with an integrable forcing. -/
theorem mild_iff_aux' (lam : ℝ) (u0 : ℂ) (u f : ℝ → ℂ) (hu : ContinuousOn u (Set.Ici 0))
    (hf : ∀ t, 0 ≤ t → IntegrableOn f (Set.Icc 0 t)) :
    (∀ t, 0 ≤ t → u t = u0 + ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * u σ + f σ)) ↔
      ∀ t, 0 ≤ t → u t = mildFn lam u0 f t := by
  constructor
  · intro h T hT
    set w : ℝ → ℂ := fun t => u t - mildFn lam u0 f t with hw
    have huc : ContinuousOn u (Set.Icc 0 T) := hu.mono Set.Icc_subset_Ici_self
    have hmc : ContinuousOn (mildFn lam u0 f) (Set.Icc 0 T) :=
      continuousOn_mildFn lam u0 f T hT (hf T hT)
    have hwc : ContinuousOn w (Set.Icc 0 T) := huc.sub hmc
    have key : ∀ t ∈ Set.Icc 0 T, w t = -(lam : ℂ) * ∫ σ in (0 : ℝ)..t, w σ := by
      intro t ht
      have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
      have hIu : IntervalIntegrable u volume 0 t := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le ht.1]; exact huc.mono hsub
      have hIm : IntervalIntegrable (mildFn lam u0 f) volume 0 t := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le ht.1]; exact hmc.mono hsub
      have hIf : IntervalIntegrable f volume 0 t := by
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hf t ht.1)
      have hA := (hIu.const_mul (-(lam : ℂ))).add hIf
      have hB := (hIm.const_mul (-(lam : ℂ))).add hIf
      have hut := h t ht.1
      have hmt := mildFn_integrated lam u0 f hf t ht.1
      have hI : ∫ σ in (0 : ℝ)..t, w σ = (∫ σ in (0 : ℝ)..t, u σ) -
          ∫ σ in (0 : ℝ)..t, mildFn lam u0 f σ := intervalIntegral.integral_sub hIu hIm
      calc w t = (∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * u σ + f σ)) -
            ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * mildFn lam u0 f σ + f σ) := by
            simp only [hw]; rw [hut, hmt]; ring
        _ = ∫ σ in (0 : ℝ)..t, ((-(lam : ℂ) * u σ + f σ) -
            (-(lam : ℂ) * mildFn lam u0 f σ + f σ)) := (intervalIntegral.integral_sub hA hB).symm
        _ = ∫ σ in (0 : ℝ)..t, -(lam : ℂ) * w σ := by
            refine intervalIntegral.integral_congr fun σ _ => ?_
            simp only [hw]; ring
        _ = -(lam : ℂ) * ∫ σ in (0 : ℝ)..t, w σ := intervalIntegral.integral_const_mul _ _
    have := ode_zero lam T hT w hwc key T ⟨hT, le_rfl⟩
    simpa [hw, sub_eq_zero] using this
  · intro h t ht
    rw [h t ht, mildFn_integrated lam u0 f hf t ht]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le ht] at hσ
    rw [h σ hσ.1]

theorem mild_iff_aux (lam : ℝ) (u0 : ℂ) (u f : ℝ → ℂ) (hu : ContinuousOn u (Set.Ici 0))
    (hf : ∀ t, 0 ≤ t → IntegrableOn f (Set.Icc 0 t)) :
    (∀ t, 0 ≤ t → u t = u0 + ∫ σ in (0 : ℝ)..t, (-(lam : ℂ) * u σ + f σ)) ↔
      ∀ t, 0 ≤ t → u t = ((Real.exp (-lam * t) : ℝ) : ℂ) * u0 +
        ∫ σ in (0 : ℝ)..t, ((Real.exp (-lam * (t - σ)) : ℝ) : ℂ) * f σ := by
  rw [mild_iff_aux' lam u0 u f hu hf]
  exact forall_congr' fun t => imp_congr_right fun _ => by rw [mildFn_eq]

/-! ### The mild formulation -/

theorem heatMult_eq (ν τ : ℝ) (k : Lattice d) :
    heatMult ν τ k = Real.exp (-(ν * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) * τ) := by
  unfold heatMult; congr 1; ring

theorem norm_coeff_mul_sqrt_le (m : ℝ) {c : Coeff d} (hc : MemHs m c) (k : Lattice d) :
    ‖c k‖ * Real.sqrt (sobWeight m k) ≤ hsNorm m c := by
  have h1 : sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c := hc.le_tsum k fun j _ =>
    mul_nonneg (MFProduct.sobWeight_nonneg m j) (sq_nonneg _)
  calc ‖c k‖ * Real.sqrt (sobWeight m k)
      = Real.sqrt (sobWeight m k * ‖c k‖ ^ 2) := by
        rw [Real.sqrt_mul (MFProduct.sobWeight_nonneg m k), Real.sqrt_sq (norm_nonneg _), mul_comm]
    _ ≤ hsNorm m c := Real.sqrt_le_sqrt h1

/-- Modewise continuity of a path continuous into `H^m`. -/
theorem continuousOn_mode {m : ℝ} {ρc : ℝ → Coeff d} {S : Set ℝ} (h : ContinuousInHsOn m ρc S)
    (k : Lattice d) : ContinuousOn (fun t => ρc t k) S := by
  intro τ0 hτ0
  have hw : 0 < Real.sqrt (sobWeight m k) := Real.sqrt_pos.mpr (sobWeight_pos m k)
  have hT := h.2 τ0 hτ0
  have hbd : ∀ τ ∈ S, ‖ρc τ k - ρc τ0 k‖ ≤ hsNorm m (ρc τ - ρc τ0) / Real.sqrt (sobWeight m k) := by
    intro τ hτ
    rw [le_div_iff₀ hw]
    exact norm_coeff_mul_sqrt_le m (memHs_sub_aux (h.1 τ hτ) (h.1 τ0 hτ0)) k
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbd) ?_
  simpa using hT.div_const (Real.sqrt (sobWeight m k))

theorem mfRhsCoeff_mode (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (invβ : ℝ) (c : Coeff d) (k : Lattice d) :
    mfRhsCoeff d s V invβ c k =
      -((invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) : ℝ) : ℂ) * c k + nlCoeff d s V c k := by
  rw [mfRhsCoeff_eq]
  unfold laplaceCoeff
  push_cast
  ring

set_option linter.unusedVariables false in
/-- Duhamel ⇔ integrated form: a continuous `H^K` path solves the integrated equation iff it
solves the mild equation `ρ̂(t) = e^{tνΔ}ρ̂⁰ + ∫₀ᵗ e^{(t-σ)νΔ} nl(ρ̂(σ)) dσ` modewise. -/
theorem isMFSolutionHK_iff_mild (d : ℕ) (s : ℝ) (V ρ₀ : Torus d → ℝ) (invβ K : ℝ)
    (hν : 0 ≤ invβ) (ρc : ℝ → Coeff d) (hcont : ContinuousInHsOn K ρc (Set.Ici 0))
    (hint : ∀ k, ∀ t, 0 ≤ t → IntegrableOn (fun σ => nlCoeff d s V (ρc σ) k) (Set.Icc 0 t)) :
    IsMFSolutionHK d s V invβ K ρ₀ ρc ↔
      (ρc 0 = coeffOf ρ₀ ∧ ∀ k, ∀ t, 0 ≤ t →
        ρc t k = (heatMult invβ t k : ℂ) * coeffOf ρ₀ k +
          ∫ σ in (0 : ℝ)..t, (heatMult invβ (t - σ) k : ℂ) * nlCoeff d s V (ρc σ) k) := by
  have hmode : ∀ k, ContinuousOn (fun t => ρc t k) (Set.Ici 0) := continuousOn_mode hcont
  have hrhs : ∀ k, ∀ t, 0 ≤ t →
      IntegrableOn (fun σ => mfRhsCoeff d s V invβ (ρc σ) k) (Set.Icc 0 t) := by
    intro k t ht
    have : IntegrableOn (fun σ => -((invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) : ℝ) : ℂ) *
        ρc σ k + nlCoeff d s V (ρc σ) k) (Set.Icc 0 t) := by
      refine IntegrableOn.add ?_ (hint k t ht)
      exact (continuousOn_const.mul ((hmode k).mono Set.Icc_subset_Ici_self)).integrableOn_Icc
    exact this.congr_fun (fun σ _ => (mfRhsCoeff_mode d s V invβ (ρc σ) k).symm) measurableSet_Icc
  have hiff : ∀ k, (∀ t, 0 ≤ t → ρc t k = coeffOf ρ₀ k +
        ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V invβ (ρc σ) k) ↔
      ∀ t, 0 ≤ t → ρc t k = (heatMult invβ t k : ℂ) * coeffOf ρ₀ k +
          ∫ σ in (0 : ℝ)..t, (heatMult invβ (t - σ) k : ℂ) * nlCoeff d s V (ρc σ) k := by
    intro k
    have := mild_iff_aux (invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) (coeffOf ρ₀ k)
      (fun t => ρc t k) (fun σ => nlCoeff d s V (ρc σ) k) (hmode k) (hint k)
    simp_rw [heatMult_eq]
    simp_rw [← mfRhsCoeff_mode] at this
    exact this
  constructor
  · intro H
    exact ⟨H.init, fun k => (hiff k).mp (H.eq k)⟩
  · rintro ⟨h0, hm⟩
    exact ⟨h0, hcont, hrhs, fun k => (hiff k).mpr (hm k)⟩

/-! ### Minkowski's integral inequality for the `H^m` norm -/

/-- Minkowski: `‖∫ F‖_{H^m} ≤ ∫ ‖F‖_{H^m}` for a coefficientwise interval integral of a family of
`H^m` sequences with integrable modes and integrable `H^m` norm. -/
theorem hsNorm_intervalIntegral_le (m : ℝ) (F : ℝ → Coeff d) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ σ ∈ Set.Icc a b, MemHs m (F σ))
    (hmode : ∀ k, IntervalIntegrable (fun σ => F σ k) volume a b)
    (hnorm : IntervalIntegrable (fun σ => hsNorm m (F σ)) volume a b) :
    MemHs m (fun k => ∫ σ in a..b, F σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, F σ k) ≤ ∫ σ in a..b, hsNorm m (F σ) := by
  set A : Lattice d → ℂ := fun k => ∫ σ in a..b, F σ k with hA
  set B : ℝ := ∫ σ in a..b, hsNorm m (F σ) with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hab fun σ _ => hsNorm_nonneg _ _
  have hw0 : ∀ k : Lattice d, 0 ≤ sobWeight m k := fun k => MFProduct.sobWeight_nonneg m k
  have key : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 ≤ B ^ 2 := by
    intro S
    set N : ℝ := ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 with hN
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)
    rcases hN0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    set H : ℝ → ℂ := fun σ => ∑ k ∈ S, ((sobWeight m k : ℝ) : ℂ) * conj (A k) * F σ k with hH
    have hHint : IntervalIntegrable H volume a b := by
      have := IntervalIntegrable.sum S fun k _ =>
        (hmode k).const_mul (((sobWeight m k : ℝ) : ℂ) * conj (A k))
      convert this using 1
      funext σ
      simp [hH, Finset.sum_apply, mul_assoc]
    have hI : ∫ σ in a..b, H σ = (N : ℂ) := by
      simp only [hH]
      rw [intervalIntegral.integral_finsetSum fun k _ => (hmode k).const_mul _]
      simp_rw [intervalIntegral.integral_const_mul]
      simp only [hN]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (conj (A k)) * A k = ((‖A k‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hA]
      simp only at this ⊢
      rw [mul_assoc, this]
      push_cast; ring
    have hpt : ∀ σ ∈ Set.Icc a b, ‖H σ‖ ≤ Real.sqrt N * hsNorm m (F σ) := by
      intro σ hσ
      have h1 : ‖H σ‖ ≤ ∑ k ∈ S, (Real.sqrt (sobWeight m k) * ‖A k‖) *
          (Real.sqrt (sobWeight m k) * ‖F σ k‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 k),
          RCLike.norm_conj]
        have := Real.mul_self_sqrt (hw0 k)
        linear_combination (-(‖A k‖ * ‖F σ k‖)) * this
      refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_)
      refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · refine le_of_eq (congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => ?_))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
      · unfold hsNorm hsNormSq
        refine Real.sqrt_le_sqrt ?_
        have hs := hmem σ hσ
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
          (hs.sum_le_tsum S fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
    have h2 : N ≤ Real.sqrt N * B := by
      calc N = ‖(N : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
        _ = ‖∫ σ in a..b, H σ‖ := by rw [hI]
        _ ≤ ∫ σ in a..b, ‖H σ‖ := intervalIntegral.norm_integral_le_integral_norm hab
        _ ≤ ∫ σ in a..b, Real.sqrt N * hsNorm m (F σ) :=
            intervalIntegral.integral_mono_on hab hHint.norm (hnorm.const_mul _) hpt
        _ = Real.sqrt N * B := intervalIntegral.integral_const_mul _ _
    have h3 : Real.sqrt N ≤ B := by
      have hs := Real.sqrt_pos.mpr hpos
      have : Real.sqrt N * Real.sqrt N ≤ Real.sqrt N * B := by
        rwa [Real.mul_self_sqrt hN0]
      exact le_of_mul_le_mul_left this hs
    calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  have hnn : 0 ≤ fun k : Lattice d => sobWeight m k * ‖A k‖ ^ 2 := fun k => mul_nonneg (hw0 k) (sq_nonneg _)
  have hsum : MemHs m A := summable_of_sum_le hnn key
  refine ⟨hsum, ?_⟩
  unfold hsNorm hsNormSq
  exact Real.sqrt_le_iff.mpr ⟨hB0, Real.tsum_le_of_sum_le hnn key⟩

/-- Minkowski for a path continuous into `H^m`. -/
theorem hsNorm_intervalIntegral_le_of_cont (m : ℝ) (F : ℝ → Coeff d) {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousInHsOn m F (Set.Icc a b)) :
    MemHs m (fun k => ∫ σ in a..b, F σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, F σ k) ≤ ∫ σ in a..b, hsNorm m (F σ) := by
  refine hsNorm_intervalIntegral_le m F hab hF.1 (fun k => ?_) ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact continuousOn_mode hF k
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    intro σ0 hσ0
    have hT := hF.2 σ0 hσ0
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun σ hσ => ?_) hT
    have h1 := memHs_add_le m (hF.1 σ0 hσ0) (memHs_sub_aux (hF.1 σ hσ) (hF.1 σ0 hσ0))
    have h2 := memHs_add_le m (hF.1 σ hσ) (memHs_sub_aux (hF.1 σ0 hσ0) (hF.1 σ hσ))
    have e1 : F σ0 + (F σ - F σ0) = F σ := by abel
    have e2 : F σ + (F σ0 - F σ) = F σ0 := by abel
    have e3 : hsNorm m (F σ0 - F σ) = hsNorm m (F σ - F σ0) := by
      unfold hsNorm hsNormSq
      simp only [Pi.sub_apply, norm_sub_rev (F σ0 _)]
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h2.2, h1.2]

end MFLocal
end HRS.PDE
