import HRS.PDE.Toolbox

/-!
# Fourier product toolbox: Wiener algebra, Young inequality, Fourier–Moser (package MF-01, P3a)

Coefficient-side (`Coeff d = Lattice d → ℂ`) statements:

* `young_nonneg`, `l2_conv_l1`: `‖a ∗ b‖_{ℓ²} ≤ ‖a‖_{ℓ¹} ‖b‖_{ℓ²}` for `mulCoeff`;
* `wienerNorm`, `wienerNormW`: (weighted) `ℓ¹` norms;
* `sobWeight_add_le`, `hsNorm_mulCoeff_le` (Fourier–Moser), `wienerNorm_mulCoeff_le`,
  `wienerNormW_mulCoeff_le` (Wiener algebras), `exists_wienerW_le_hsNorm` (`H^a ⊂ A_b`),
  `exp_wienerW` (exponential in `A_a`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFProduct

variable {d : ℕ}

/-- Wiener-algebra norm `∑ ‖c k‖` (junk `0` when not summable, so always guard by `Summable`). -/
noncomputable def wienerNorm (c : Coeff d) : ℝ := ∑' k, ‖c k‖

/-- Weighted `ℓ¹` norm `∑ sobWeight (a/2) k ‖c k‖` (`A_a`). -/
noncomputable def wienerNormW (a : ℝ) (c : Coeff d) : ℝ := ∑' k, sobWeight (a / 2) k * ‖c k‖

/-! ### Nonnegative real convolution on `ℤ^d`: Tonelli and Young -/

/-- Convolution of real sequences on the lattice. -/
def conv (u v : Lattice d → ℝ) (k : Lattice d) : ℝ := ∑' j, u (k - j) * v j

theorem tonelli_conv (u w : Lattice d → ℝ) (hu0 : ∀ k, 0 ≤ u k) (hw0 : ∀ k, 0 ≤ w k)
    (hu : Summable u) (hw : Summable w) :
    (∀ k, Summable fun j => u (k - j) * w j) ∧ Summable (conv u w) ∧
      ∑' k, conv u w k = (∑' k, u k) * ∑' k, w k := by
  have hsh : ∀ j : Lattice d, Summable fun k => u (k - j) * w j := fun j =>
    ((Equiv.subRight j).summable_iff.mpr hu).mul_right (w j)
  have hshs : ∀ j : Lattice d, ∑' k, u (k - j) * w j = (∑' k, u k) * w j := fun j => by
    rw [tsum_mul_right]
    congr 1
    exact (Equiv.subRight j).tsum_eq u
  have hF : Summable (fun p : Lattice d × Lattice d => u (p.2 - p.1) * w p.1) := by
    have hnn : (0 : Lattice d × Lattice d → ℝ) ≤ fun p => u (p.2 - p.1) * w p.1 :=
      fun p => mul_nonneg (hu0 _) (hw0 _)
    refine (summable_prod_of_nonneg hnn).mpr ⟨hsh, ?_⟩
    simp only [hshs]
    exact hw.mul_left _
  have hF' : Summable (fun p : Lattice d × Lattice d => u (p.1 - p.2) * w p.2) :=
    (Equiv.summable_iff (Equiv.prodComm (Lattice d) (Lattice d))
      (f := fun p : Lattice d × Lattice d => u (p.2 - p.1) * w p.1)).mpr hF
  have hnn' : (0 : Lattice d × Lattice d → ℝ) ≤ fun p => u (p.1 - p.2) * w p.2 :=
    fun p => mul_nonneg (hu0 _) (hw0 _)
  have h2 := (summable_prod_of_nonneg hnn').mp hF'
  refine ⟨h2.1, h2.2, ?_⟩
  have e1 : ∑' k, conv u w k = ∑' k, ∑' j, u (k - j) * w j := rfl
  rw [e1]
  have hc := Summable.tsum_comm (f := fun (j k : Lattice d) => u (k - j) * w j) hF
  rw [hc]
  simp_rw [hshs]
  rw [tsum_mul_left]

theorem conv_nonneg {u v : Lattice d → ℝ} (hu0 : ∀ k, 0 ≤ u k) (hv0 : ∀ k, 0 ≤ v k) (k : Lattice d) :
    0 ≤ conv u v k :=
  tsum_nonneg fun _ => mul_nonneg (hu0 _) (hv0 _)

/-- Young's inequality `ℓ¹ ∗ ℓ² ⊂ ℓ²` for nonnegative sequences on the lattice. -/
theorem young_nonneg (u v : Lattice d → ℝ) (hu0 : ∀ k, 0 ≤ u k) (hv0 : ∀ k, 0 ≤ v k)
    (hu : Summable u) (hv : Summable fun k => v k ^ 2) :
    (∀ k, Summable fun j => u (k - j) * v j) ∧ Summable (fun k => conv u v k ^ 2) ∧
      ∑' k, conv u v k ^ 2 ≤ (∑' k, u k) ^ 2 * ∑' k, v k ^ 2 := by
  obtain ⟨hT1, hT2, hT3⟩ := tonelli_conv u (fun j => v j ^ 2) hu0 (fun _ => sq_nonneg _) hu hv
  have key : ∀ k, (Summable fun j => u (k - j) * v j) ∧
      conv u v k ^ 2 ≤ (∑' k, u k) * conv u (fun j => v j ^ 2) k := by
    intro k
    have hs2 : Summable fun j => (Real.sqrt (u (k - j))) ^ 2 := by
      refine ((Equiv.subLeft k).summable_iff.mpr hu).congr fun j => ?_
      simp [Real.sq_sqrt (hu0 _)]
    have ht2 : Summable fun j => (Real.sqrt (u (k - j)) * v j) ^ 2 := by
      refine (hT1 k).congr fun j => ?_
      rw [mul_pow, Real.sq_sqrt (hu0 _)]
    have hcs := Torus.cs_tsum (fun j => Real.sqrt (u (k - j))) (fun j => Real.sqrt (u (k - j)) * v j)
      (fun _ => Real.sqrt_nonneg _) (fun j => mul_nonneg (Real.sqrt_nonneg _) (hv0 _)) hs2 ht2
    have hprod : ∀ j, Real.sqrt (u (k - j)) * (Real.sqrt (u (k - j)) * v j) = u (k - j) * v j := by
      intro j
      rw [← mul_assoc, Real.mul_self_sqrt (hu0 _)]
    simp_rw [hprod] at hcs
    refine ⟨hcs.1, ?_⟩
    have e1 : ∑' j, (Real.sqrt (u (k - j))) ^ 2 = ∑' k, u k := by
      rw [← (Equiv.subLeft k).tsum_eq u]
      refine tsum_congr fun j => ?_
      simp [Real.sq_sqrt (hu0 _)]
    have e2 : ∑' j, (Real.sqrt (u (k - j)) * v j) ^ 2 = conv u (fun j => v j ^ 2) k := by
      refine tsum_congr fun j => ?_
      rw [mul_pow, Real.sq_sqrt (hu0 _)]
    rw [e1, e2] at hcs
    have h0 : 0 ≤ conv u v k := conv_nonneg hu0 hv0 k
    have h1 : conv u v k ≤ Real.sqrt (∑' k, u k) * Real.sqrt (conv u (fun j => v j ^ 2) k) := hcs.2
    calc conv u v k ^ 2 ≤ (Real.sqrt (∑' k, u k) * Real.sqrt (conv u (fun j => v j ^ 2) k)) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = (∑' k, u k) * conv u (fun j => v j ^ 2) k := by
          rw [mul_pow, Real.sq_sqrt (tsum_nonneg hu0),
            Real.sq_sqrt (conv_nonneg hu0 (fun _ => sq_nonneg _) k)]
  have hsum : Summable (fun k => conv u v k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => (key k).2) (hT2.mul_left _)
  refine ⟨fun k => (key k).1, hsum, ?_⟩
  calc ∑' k, conv u v k ^ 2 ≤ ∑' k, (∑' k, u k) * conv u (fun j => v j ^ 2) k :=
        hsum.tsum_le_tsum (fun k => (key k).2) (hT2.mul_left _)
    _ = (∑' k, u k) ^ 2 * ∑' k, v k ^ 2 := by
        rw [tsum_mul_left]
        have : ∑' k, conv u (fun j => v j ^ 2) k = (∑' k, u k) * ∑' k, v k ^ 2 := hT3
        rw [this]; ring

theorem conv_comm (u v : Lattice d → ℝ) (k : Lattice d) : conv u v k = conv v u k := by
  unfold conv
  rw [← (Equiv.subLeft k).tsum_eq (fun j => u (k - j) * v j)]
  refine tsum_congr fun j => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-! ### Coefficient-level Young inequality -/

theorem norm_mulCoeff_le_conv (a b : Coeff d) (k : Lattice d)
    (h : Summable fun j => ‖a (k - j)‖ * ‖b j‖) :
    ‖mulCoeff a b k‖ ≤ conv (fun k => ‖a k‖) (fun k => ‖b k‖) k := by
  unfold mulCoeff conv
  have h' : Summable fun j => ‖a (k - j) * b j‖ := h.congr fun j => (norm_mul _ _).symm
  refine (norm_tsum_le_tsum_norm h').trans (le_of_eq (tsum_congr fun j => norm_mul _ _))

/-- **Young's inequality** `ℓ¹ ∗ ℓ² ⊂ ℓ²` for coefficient convolution:
`‖a ∗ b‖_{ℓ²} ≤ ‖a‖_{ℓ¹} ‖b‖_{ℓ²}`. -/
theorem l2_conv_l1 (a b : Coeff d) (ha : Summable fun k => ‖a k‖) (hb : MemHs 0 b) :
    (∀ k, Summable fun j => ‖a (k - j)‖ * ‖b j‖) ∧ MemHs 0 (mulCoeff a b) ∧
      hsNormSq 0 (mulCoeff a b) ≤ (∑' k, ‖a k‖) ^ 2 * hsNormSq 0 b := by
  rw [memHs_zero_iff] at hb
  obtain ⟨h1, h2, h3⟩ := young_nonneg (fun k => ‖a k‖) (fun k => ‖b k‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) ha hb
  have hle : ∀ k, ‖mulCoeff a b k‖ ^ 2 ≤ conv (fun k => ‖a k‖) (fun k => ‖b k‖) k ^ 2 := fun k =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_mulCoeff_le_conv a b k (h1 k)) 2
  have hs : Summable fun k => ‖mulCoeff a b k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle h2
  refine ⟨h1, (memHs_zero_iff _).mpr hs, ?_⟩
  rw [hsNormSq_zero, hsNormSq_zero]
  exact (hs.tsum_le_tsum hle h2).trans h3

theorem hsNorm_zero_mulCoeff_le (a b : Coeff d) (ha : Summable fun k => ‖a k‖) (hb : MemHs 0 b) :
    hsNorm 0 (mulCoeff a b) ≤ (∑' k, ‖a k‖) * hsNorm 0 b := by
  obtain ⟨-, -, h⟩ := l2_conv_l1 a b ha hb
  unfold hsNorm
  have h0 : 0 ≤ ∑' k, ‖a k‖ := tsum_nonneg fun _ => norm_nonneg _
  calc Real.sqrt (hsNormSq 0 (mulCoeff a b))
      ≤ Real.sqrt ((∑' k, ‖a k‖) ^ 2 * hsNormSq 0 b) := Real.sqrt_le_sqrt h
    _ = (∑' k, ‖a k‖) * Real.sqrt (hsNormSq 0 b) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0]

/-! ### Weights -/

theorem sobWeight_half_sq (a : ℝ) (k : Lattice d) : sobWeight (a / 2) k ^ 2 = sobWeight a k := by
  unfold sobWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast; ring

theorem sobWeight_nonneg (m : ℝ) (k : Lattice d) : 0 ≤ sobWeight m k :=
  (sobWeight_posC m k).le

theorem one_le_sobWeight {m : ℝ} (hm : 0 ≤ m) (k : Lattice d) : 1 ≤ sobWeight m k := by
  unfold sobWeight
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k), Real.pi_pos]) hm

theorem sobWeight_add_le (a : ℝ) (ha : 0 ≤ a) (j k : Lattice d) :
    sobWeight (a / 2) (j + k) ≤ 2 ^ a * (sobWeight (a / 2) j + sobWeight (a / 2) k) := by
  have h1 : Lattice.enorm (j + k) ≤ Lattice.enorm j + Lattice.enorm k := by
    have := enorm_le_add (j + k) j
    rwa [add_sub_cancel_left] at this
  have h0 : 0 ≤ Lattice.enorm (j + k) := norm_nonneg _
  have h2 : Lattice.enorm (j + k) ^ 2 ≤ 2 * Lattice.enorm j ^ 2 + 2 * Lattice.enorm k ^ 2 := by
    nlinarith [sq_nonneg (Lattice.enorm j - Lattice.enorm k), norm_nonneg (Lattice.toEuc j),
      norm_nonneg (Lattice.toEuc k)]
  set A := 1 + 4 * Real.pi ^ 2 * Lattice.enorm j ^ 2 with hA
  set B := 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hB
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [sq_nonneg (Real.pi * Lattice.enorm j)]
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]
  have hC : 1 + 4 * Real.pi ^ 2 * Lattice.enorm (j + k) ^ 2 ≤ 4 * max A B := by
    have : 4 * Real.pi ^ 2 * Lattice.enorm (j + k) ^ 2 ≤
        2 * (4 * Real.pi ^ 2 * Lattice.enorm j ^ 2) + 2 * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) := by
      nlinarith [Real.pi_pos, sq_nonneg Real.pi]
    have h3 : A ≤ max A B := le_max_left _ _
    have h4 : B ≤ max A B := le_max_right _ _
    rw [hA] at h3; rw [hB] at h4
    linarith
  have hM : (0 : ℝ) ≤ max A B := by positivity
  have hpos : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm (j + k) ^ 2 := by positivity
  have ha2 : 0 ≤ a / 2 := by positivity
  unfold sobWeight
  calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm (j + k) ^ 2) ^ (a / 2)
      ≤ (4 * max A B) ^ (a / 2) := Real.rpow_le_rpow hpos.le hC ha2
    _ = 2 ^ a * (max A B) ^ (a / 2) := by
        rw [Real.mul_rpow (by norm_num) hM]
        congr 1
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        congr 1; ring
    _ ≤ 2 ^ a * (A ^ (a / 2) + B ^ (a / 2)) := by
        gcongr
        rcases le_total A B with h | h
        · rw [max_eq_right h]
          have : 0 ≤ A ^ (a / 2) := Real.rpow_nonneg (by linarith) _
          linarith
        · rw [max_eq_left h]
          have : 0 ≤ B ^ (a / 2) := Real.rpow_nonneg (by linarith) _
          linarith

theorem summable_conv_comm {u v : Lattice d → ℝ} (k : Lattice d)
    (h : Summable fun j => u (k - j) * v j) : Summable fun j => v (k - j) * u j := by
  have := (Equiv.subLeft k).summable_iff.mpr h
  refine this.congr fun j => ?_
  simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-! ### `ℓ²` bookkeeping -/

theorem minkowski_sq (P Q : Lattice d → ℝ) (hP0 : ∀ k, 0 ≤ P k) (hQ0 : ∀ k, 0 ≤ Q k)
    (hP : Summable fun k => P k ^ 2) (hQ : Summable fun k => Q k ^ 2) :
    Summable (fun k => (P k + Q k) ^ 2) ∧
      Real.sqrt (∑' k, (P k + Q k) ^ 2) ≤ Real.sqrt (∑' k, P k ^ 2) + Real.sqrt (∑' k, Q k ^ 2) := by
  obtain ⟨hPQ, hcs⟩ := Torus.cs_tsum P Q hP0 hQ0 hP hQ
  have e : ∀ k, (P k + Q k) ^ 2 = P k ^ 2 + 2 * (P k * Q k) + Q k ^ 2 := fun k => by ring
  have hs : Summable (fun k => (P k + Q k) ^ 2) := by
    simp_rw [e]
    exact (hP.add (hPQ.mul_left 2)).add hQ
  refine ⟨hs, ?_⟩
  have hval : ∑' k, (P k + Q k) ^ 2 = ∑' k, P k ^ 2 + 2 * ∑' k, P k * Q k + ∑' k, Q k ^ 2 := by
    simp_rw [e]
    rw [((hP.add (hPQ.mul_left 2)).tsum_add hQ), hP.tsum_add (hPQ.mul_left 2), tsum_mul_left]
  set sP := Real.sqrt (∑' k, P k ^ 2)
  set sQ := Real.sqrt (∑' k, Q k ^ 2)
  have hP' : sP ^ 2 = ∑' k, P k ^ 2 := Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)
  have hQ' : sQ ^ 2 = ∑' k, Q k ^ 2 := Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [hval, ← hP', ← hQ']
  nlinarith [hcs]

theorem sq_summable_le_mul {m R : Lattice d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hm0 : ∀ k, 0 ≤ m k)
    (hle : ∀ k, m k ≤ C * R k) (hR : Summable fun k => R k ^ 2) :
    Summable (fun k => m k ^ 2) ∧ Real.sqrt (∑' k, m k ^ 2) ≤ C * Real.sqrt (∑' k, R k ^ 2) := by
  have hle2 : ∀ k, m k ^ 2 ≤ C ^ 2 * R k ^ 2 := fun k => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (hm0 k) (hle k) 2
  have hs : Summable (fun k => m k ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle2 (hR.mul_left _)
  refine ⟨hs, ?_⟩
  calc Real.sqrt (∑' k, m k ^ 2) ≤ Real.sqrt (∑' k, C ^ 2 * R k ^ 2) :=
        Real.sqrt_le_sqrt (hs.tsum_le_tsum hle2 (hR.mul_left _))
    _ = C * Real.sqrt (∑' k, R k ^ 2) := by
        rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

/-- Fourier–Moser (Wiener-algebra form): `‖fg‖_{H^a} ≤ 2^a (‖f‖_{H^a} ‖ĝ‖_{ℓ¹} + ‖f̂‖_{ℓ¹} ‖g‖_{H^a})`. -/
theorem hsNorm_mulCoeff_le (a : ℝ) (ha : 0 ≤ a) (f g : Coeff d)
    (hf : MemHs a f) (hg : MemHs a g) (hf1 : Summable fun k => ‖f k‖)
    (hg1 : Summable fun k => ‖g k‖) :
    MemHs a (mulCoeff f g) ∧
      hsNorm a (mulCoeff f g) ≤ 2 ^ a * (hsNorm a f * wienerNorm g + wienerNorm f * hsNorm a g) := by
  set w : Lattice d → ℝ := sobWeight (a / 2) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sobWeight_nonneg _ k
  have hF2 : Summable fun k => (w k * ‖f k‖) ^ 2 := hf.congr fun k => by
    rw [mul_pow, hw, sobWeight_half_sq]
  have hG2 : Summable fun k => (w k * ‖g k‖) ^ 2 := hg.congr fun k => by
    rw [mul_pow, hw, sobWeight_half_sq]
  have hnF : hsNorm a f = Real.sqrt (∑' k, (w k * ‖f k‖) ^ 2) := by
    unfold hsNorm hsNormSq
    congr 1; exact tsum_congr fun k => by rw [mul_pow, hw, sobWeight_half_sq]
  have hnG : hsNorm a g = Real.sqrt (∑' k, (w k * ‖g k‖) ^ 2) := by
    unfold hsNorm hsNormSq
    congr 1; exact tsum_congr fun k => by rw [mul_pow, hw, sobWeight_half_sq]
  -- the two Young pieces
  obtain ⟨hQs, hQ2, hQb⟩ := young_nonneg (fun k => ‖f k‖) (fun k => w k * ‖g k‖)
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hf1 hG2
  obtain ⟨hPs, hP2, hPb⟩ := young_nonneg (fun k => ‖g k‖) (fun k => w k * ‖f k‖)
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hg1 hF2
  set Q := conv (fun k => ‖f k‖) (fun k => w k * ‖g k‖) with hQ
  set P := conv (fun k => w k * ‖f k‖) (fun k => ‖g k‖) with hP
  have hPeq : ∀ k, P k = conv (fun k => ‖g k‖) (fun k => w k * ‖f k‖) k := fun k =>
    conv_comm _ _ k
  have hP2' : Summable fun k => P k ^ 2 := by
    simp_rw [hPeq]; exact hP2
  have hP0 : ∀ k, 0 ≤ P k := fun k =>
    conv_nonneg (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) (fun _ => norm_nonneg _) k
  have hQ0 : ∀ k, 0 ≤ Q k :=
    conv_nonneg (fun _ => norm_nonneg _) (fun k => mul_nonneg (hw0 k) (norm_nonneg _))
  obtain ⟨hPQs, hPQb⟩ := minkowski_sq P Q hP0 hQ0 hP2' hQ2
  -- pointwise bound
  have hpt : ∀ k, w k * ‖mulCoeff f g k‖ ≤ 2 ^ a * (P k + Q k) := by
    intro k
    have hS : Summable fun j => ‖f (k - j)‖ * ‖g j‖ :=
      (tonelli_conv (fun k => ‖f k‖) (fun k => ‖g k‖) (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _) hf1 hg1).1 k
    have ht1 : Summable fun j => (w (k - j) * ‖f (k - j)‖) * ‖g j‖ := by
      exact summable_conv_comm (u := fun k => ‖g k‖) (v := fun k => w k * ‖f k‖) k (hPs k)
    have ht2 : Summable fun j => ‖f (k - j)‖ * (w j * ‖g j‖) := hQs k
    have hnm := norm_mulCoeff_le_conv f g k hS
    have hterm : ∀ j, w k * (‖f (k - j)‖ * ‖g j‖) ≤
        2 ^ a * ((w (k - j) * ‖f (k - j)‖) * ‖g j‖ + ‖f (k - j)‖ * (w j * ‖g j‖)) := by
      intro j
      have h1 : w k ≤ 2 ^ a * (w (k - j) + w j) := by
        have := sobWeight_add_le a ha (k - j) j
        rwa [sub_add_cancel] at this
      have h2 : 0 ≤ ‖f (k - j)‖ * ‖g j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc w k * (‖f (k - j)‖ * ‖g j‖) ≤ (2 ^ a * (w (k - j) + w j)) * (‖f (k - j)‖ * ‖g j‖) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
    calc w k * ‖mulCoeff f g k‖ ≤ w k * conv (fun k => ‖f k‖) (fun k => ‖g k‖) k :=
          mul_le_mul_of_nonneg_left hnm (hw0 k)
      _ = ∑' j, w k * (‖f (k - j)‖ * ‖g j‖) := by unfold conv; rw [tsum_mul_left]
      _ ≤ ∑' j, 2 ^ a * ((w (k - j) * ‖f (k - j)‖) * ‖g j‖ + ‖f (k - j)‖ * (w j * ‖g j‖)) :=
          (hS.mul_left _).tsum_le_tsum hterm ((ht1.add ht2).mul_left _)
      _ = 2 ^ a * (P k + Q k) := by
          rw [tsum_mul_left, ht1.tsum_add ht2]
          rfl
  have hm0 : ∀ k, 0 ≤ w k * ‖mulCoeff f g k‖ := fun k => mul_nonneg (hw0 k) (norm_nonneg _)
  have h2a : (0 : ℝ) ≤ 2 ^ a := by positivity
  obtain ⟨hms, hmb⟩ := sq_summable_le_mul h2a hm0 hpt hPQs
  have hmem : MemHs a (mulCoeff f g) := hms.congr fun k => by
    rw [mul_pow, hw, sobWeight_half_sq]
  refine ⟨hmem, ?_⟩
  have hnM : hsNorm a (mulCoeff f g) = Real.sqrt (∑' k, (w k * ‖mulCoeff f g k‖) ^ 2) := by
    unfold hsNorm hsNormSq
    congr 1; exact tsum_congr fun k => by rw [mul_pow, hw, sobWeight_half_sq]
  have hsP : Real.sqrt (∑' k, P k ^ 2) ≤ wienerNorm g * hsNorm a f := by
    have : ∑' k, P k ^ 2 ≤ (∑' k, ‖g k‖) ^ 2 * ∑' k, (w k * ‖f k‖) ^ 2 := by
      simp_rw [hPeq]; exact hPb
    refine (Real.sqrt_le_sqrt this).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (tsum_nonneg fun _ => norm_nonneg _), hnF]
    rfl
  have hsQ : Real.sqrt (∑' k, Q k ^ 2) ≤ wienerNorm f * hsNorm a g := by
    refine (Real.sqrt_le_sqrt hQb).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (tsum_nonneg fun _ => norm_nonneg _), hnG]
    rfl
  rw [hnM]
  calc Real.sqrt (∑' k, (w k * ‖mulCoeff f g k‖) ^ 2)
      ≤ 2 ^ a * Real.sqrt (∑' k, (P k + Q k) ^ 2) := hmb
    _ ≤ 2 ^ a * (Real.sqrt (∑' k, P k ^ 2) + Real.sqrt (∑' k, Q k ^ 2)) := by gcongr
    _ ≤ 2 ^ a * (wienerNorm g * hsNorm a f + wienerNorm f * hsNorm a g) := by gcongr
    _ = _ := by ring

/-- The Wiener algebra is an algebra: `‖f̂ * ĝ‖_{ℓ¹} ≤ ‖f̂‖_{ℓ¹} ‖ĝ‖_{ℓ¹}`. -/
theorem wienerNorm_mulCoeff_le (f g : Coeff d) (hf : Summable fun k => ‖f k‖)
    (hg : Summable fun k => ‖g k‖) :
    (Summable fun k => ‖mulCoeff f g k‖) ∧ wienerNorm (mulCoeff f g) ≤ wienerNorm f * wienerNorm g := by
  obtain ⟨h1, h2, h3⟩ := tonelli_conv (fun k => ‖f k‖) (fun k => ‖g k‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hf hg
  have hle : ∀ k, ‖mulCoeff f g k‖ ≤ conv (fun k => ‖f k‖) (fun k => ‖g k‖) k := fun k =>
    norm_mulCoeff_le_conv f g k (h1 k)
  have hs : Summable fun k => ‖mulCoeff f g k‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle h2
  exact ⟨hs, (hs.tsum_le_tsum hle h2).trans (le_of_eq h3)⟩

/-- Weighted Wiener algebra `A_a` is an algebra with constant `2^{a/2}` (hence `2^a`). -/
theorem wienerNormW_mulCoeff_le' (a : ℝ) (ha : 0 ≤ a) (f g : Coeff d)
    (hf : Summable fun k => sobWeight (a / 2) k * ‖f k‖)
    (hg : Summable fun k => sobWeight (a / 2) k * ‖g k‖) :
    (Summable fun k => sobWeight (a / 2) k * ‖mulCoeff f g k‖) ∧
      wienerNormW a (mulCoeff f g) ≤ 2 ^ (a / 2) * wienerNormW a f * wienerNormW a g := by
  set w : Lattice d → ℝ := sobWeight (a / 2) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sobWeight_nonneg _ k
  have hw1 : ∀ k, 1 ≤ w k := fun k => one_le_sobWeight (by positivity) k
  have hf1 : Summable fun k => ‖f k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by have := hw1 k; nlinarith [norm_nonneg (f k)]) hf
  have hg1 : Summable fun k => ‖g k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by have := hw1 k; nlinarith [norm_nonneg (g k)]) hg
  obtain ⟨h1, h2, h3⟩ := tonelli_conv (fun k => w k * ‖f k‖) (fun k => w k * ‖g k‖)
    (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hf hg
  have hS : ∀ k, Summable fun j => ‖f (k - j)‖ * ‖g j‖ := fun k =>
    (tonelli_conv (fun k => ‖f k‖) (fun k => ‖g k‖) (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _) hf1 hg1).1 k
  have h2a : (0 : ℝ) ≤ 2 ^ (a / 2) := by positivity
  have hpt : ∀ k, w k * ‖mulCoeff f g k‖ ≤
      2 ^ (a / 2) * conv (fun k => w k * ‖f k‖) (fun k => w k * ‖g k‖) k := by
    intro k
    have hnm := norm_mulCoeff_le_conv f g k (hS k)
    have hterm : ∀ j, w k * (‖f (k - j)‖ * ‖g j‖) ≤
        2 ^ (a / 2) * ((w (k - j) * ‖f (k - j)‖) * (w j * ‖g j‖)) := by
      intro j
      have h1 : w k ≤ 2 ^ (a / 2) * w j * w (k - j) := by
        have := sobWeight_le_peetre (a / 2) k j
        rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ a / 2)] at this
      have h2 : 0 ≤ ‖f (k - j)‖ * ‖g j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc w k * (‖f (k - j)‖ * ‖g j‖) ≤ (2 ^ (a / 2) * w j * w (k - j)) * (‖f (k - j)‖ * ‖g j‖) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
    calc w k * ‖mulCoeff f g k‖ ≤ w k * conv (fun k => ‖f k‖) (fun k => ‖g k‖) k :=
          mul_le_mul_of_nonneg_left hnm (hw0 k)
      _ = ∑' j, w k * (‖f (k - j)‖ * ‖g j‖) := by unfold conv; rw [tsum_mul_left]
      _ ≤ ∑' j, 2 ^ (a / 2) * ((w (k - j) * ‖f (k - j)‖) * (w j * ‖g j‖)) :=
          (((hS k).mul_left _)).tsum_le_tsum hterm ((h1 k).mul_left _)
      _ = _ := by rw [tsum_mul_left]; rfl
  have hs : Summable fun k => w k * ‖mulCoeff f g k‖ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hpt (h2.mul_left _)
  refine ⟨hs, ?_⟩
  unfold wienerNormW
  calc ∑' k, sobWeight (a / 2) k * ‖mulCoeff f g k‖ = ∑' k, w k * ‖mulCoeff f g k‖ := rfl
    _ ≤ ∑' k, 2 ^ (a / 2) * conv (fun k => w k * ‖f k‖) (fun k => w k * ‖g k‖) k :=
        hs.tsum_le_tsum hpt (h2.mul_left _)
    _ = 2 ^ (a / 2) * ((∑' k, w k * ‖f k‖) * ∑' k, w k * ‖g k‖) := by rw [tsum_mul_left, h3]
    _ = _ := by ring

/-- Weighted Wiener algebra `A_a` is an algebra with constant `2^a`. -/
theorem wienerNormW_mulCoeff_le (a : ℝ) (ha : 0 ≤ a) (f g : Coeff d)
    (hf : Summable fun k => sobWeight (a / 2) k * ‖f k‖)
    (hg : Summable fun k => sobWeight (a / 2) k * ‖g k‖) :
    (Summable fun k => sobWeight (a / 2) k * ‖mulCoeff f g k‖) ∧
      wienerNormW a (mulCoeff f g) ≤ 2 ^ a * wienerNormW a f * wienerNormW a g := by
  obtain ⟨hs, hb⟩ := wienerNormW_mulCoeff_le' a ha f g hf hg
  refine ⟨hs, hb.trans ?_⟩
  have hF : 0 ≤ wienerNormW a f := tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ k) (norm_nonneg _)
  have hG : 0 ≤ wienerNormW a g := tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ k) (norm_nonneg _)
  have h2 : (2 : ℝ) ^ (a / 2) ≤ 2 ^ a :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  gcongr

theorem sobWeight_mul (m n : ℝ) (k : Lattice d) :
    sobWeight m k * sobWeight n k = sobWeight (m + n) k := by
  unfold sobWeight
  rw [← Real.rpow_add (by positivity)]

/-- `H^a ⊂ A_b` for `a - b > d/2`: `‖ĉ‖_{A_b} ≤ C ‖c‖_{H^a}`. -/
theorem exists_wienerW_le_hsNorm (a b : ℝ) (hb : 0 ≤ b) (hab : (d : ℝ) / 2 < a - b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Coeff d, MemHs a c →
      (Summable fun k => sobWeight (b / 2) k * ‖c k‖) ∧ wienerNormW b c ≤ C * hsNorm a c := by
  have hd : (d : ℝ) < 2 * (a - b) := by linarith
  have hS : Summable fun k : Lattice d => sobWeight (b - a) k := by
    rw [Torus.summable_lattice_iff]
    refine (summable_jp_rpow (d := d) (a - b) hd).congr fun k => ?_
    simp only [sobWeight_eq_jp]
    congr 1; ring
  refine ⟨Real.sqrt (∑' k : Lattice d, sobWeight (b - a) k), Real.sqrt_nonneg _, fun c hc => ?_⟩
  have hs2 : Summable fun k : Lattice d => (sobWeight ((b - a) / 2) k) ^ 2 :=
    hS.congr fun k => (sobWeight_half_sq _ k).symm
  have ht2 : Summable fun k => (sobWeight (a / 2) k * ‖c k‖) ^ 2 := hc.congr fun k => by
    rw [mul_pow, sobWeight_half_sq]
  obtain ⟨h1, h2⟩ := Torus.cs_tsum (fun k => sobWeight ((b - a) / 2) k)
    (fun k => sobWeight (a / 2) k * ‖c k‖) (fun k => sobWeight_nonneg _ k)
    (fun k => mul_nonneg (sobWeight_nonneg _ k) (norm_nonneg _)) hs2 ht2
  have e : ∀ k : Lattice d, sobWeight ((b - a) / 2) k * (sobWeight (a / 2) k * ‖c k‖) =
      sobWeight (b / 2) k * ‖c k‖ := fun k => by
    rw [← mul_assoc, sobWeight_mul]
    congr 2; ring
  simp_rw [e] at h1 h2
  refine ⟨h1, ?_⟩
  unfold wienerNormW
  refine h2.trans (le_of_eq ?_)
  congr 1
  · congr 1; exact tsum_congr fun k => sobWeight_half_sq _ k
  · unfold hsNorm hsNormSq
    congr 1; exact tsum_congr fun k => by rw [mul_pow, sobWeight_half_sq]

/-! ### The exponential in the weighted Wiener algebra -/

theorem hasSum_exp_real (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem coeffOf_one (k : Lattice d) : coeffOf (fun _ : Torus d => (1 : ℝ)) k = deltaCoeff 0 k := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  simp only [Complex.ofReal_one, mul_one]
  have := Torus.integral_mode (d := d) (-k)
  change ∫ x, Torus.mode (-k) x = _ at this
  simp only [Torus.mode] at this
  rw [this]
  unfold deltaCoeff
  by_cases hk : k = 0
  · simp [hk]
  · have : -k ≠ 0 := fun h => hk (neg_eq_zero.mp h)
    simp [hk, this]

theorem norm_series_le (c : Coeff d) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    ‖series c x‖ ≤ ∑' k, ‖c k‖ := by
  unfold series
  have h : Summable fun k => ‖c k * Torus.mode k x‖ := hs.congr fun k => by simp [Torus.norm_mode]
  refine (norm_tsum_le_tsum_norm h).trans (le_of_eq (tsum_congr fun k => by simp [Torus.norm_mode]))

theorem abs_toFun_le (c : Coeff d) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    |toFun c x| ≤ ∑' k, ‖c k‖ :=
  (Complex.abs_re_le_norm _).trans (norm_series_le c hs x)

theorem continuous_toFun (c : Coeff d) (hs : Summable fun k => ‖c k‖) : Continuous (toFun c) := by
  have : Continuous (series c) := by
    unfold series
    refine continuous_tsum (u := fun k => ‖c k‖) (fun k => continuous_const.mul (Torus.continuous_mode k))
      hs fun k x => by simp [Torus.norm_mode]
  exact Complex.continuous_re.comp this

theorem memLp_two_real {f : Torus d → ℝ} (hf : Continuous f) : MemLp f 2 volume :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem coeffOf_pow_succ (c : Coeff d) (hreal : IsRealCoeff c) (hs : Summable fun k => ‖c k‖)
    (n : ℕ) :
    coeffOf (fun x => toFun c x ^ (n + 1)) = mulCoeff c (coeffOf (fun x => toFun c x ^ n)) := by
  have hu := continuous_toFun c hs
  have h := coeffOf_mul (toFun c) (fun x => toFun c x ^ n) (memLp_two_real hu)
    (memLp_two_real (hu.pow n))
  rw [coeffOf_toFun c hreal hs] at h
  rw [← h]
  congr 1
  funext x
  exact pow_succ' _ _

theorem coeffOf_pow_zero (g : Torus d → ℝ) : coeffOf (fun x => g x ^ 0) = deltaCoeff 0 := by
  funext k
  simpa using coeffOf_one k

theorem sobWeight_zero_lattice (m : ℝ) : sobWeight m (0 : Lattice d) = 1 := by
  have h : Lattice.enorm (0 : Lattice d) = 0 := by
    unfold Lattice.enorm Lattice.toEuc
    simp
    rfl
  simp [sobWeight, h]

theorem hasSum_weighted_delta (m : ℝ) :
    HasSum (fun k : Lattice d => sobWeight m k * ‖deltaCoeff 0 k‖) 1 := by
  have h : (fun k : Lattice d => sobWeight m k * ‖deltaCoeff 0 k‖) = fun k => if k = 0 then 1 else 0 := by
    funext k
    by_cases hk : k = 0
    · simp [hk, deltaCoeff, sobWeight_zero_lattice]
    · simp [hk, deltaCoeff]
  rw [h]
  exact hasSum_ite_eq 0 (1 : ℝ)

theorem wienerNormW_pow (a : ℝ) (ha : 0 ≤ a) (c : Coeff d) (hreal : IsRealCoeff c)
    (hc : Summable fun k => sobWeight (a / 2) k * ‖c k‖) (n : ℕ) :
    (Summable fun k => sobWeight (a / 2) k * ‖coeffOf (fun x => toFun c x ^ n) k‖) ∧
      wienerNormW a (coeffOf (fun x => toFun c x ^ n)) ≤ (2 ^ a * wienerNormW a c) ^ n := by
  have hs : Summable fun k => ‖c k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by have := one_le_sobWeight (m := a / 2) (by positivity) k
                   nlinarith [norm_nonneg (c k)]) hc
  induction n with
  | zero =>
    rw [coeffOf_pow_zero]
    refine ⟨(hasSum_weighted_delta (a / 2)).summable, ?_⟩
    unfold wienerNormW
    rw [(hasSum_weighted_delta (a / 2)).tsum_eq]
    simp
  | succ n ih =>
    rw [coeffOf_pow_succ c hreal hs]
    obtain ⟨h1, h2⟩ := wienerNormW_mulCoeff_le a ha c _ hc ih.1
    refine ⟨h1, h2.trans ?_⟩
    have hW : 0 ≤ wienerNormW a c :=
      tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ k) (norm_nonneg _)
    have h2a : (0 : ℝ) ≤ 2 ^ a := by positivity
    calc 2 ^ a * wienerNormW a c * wienerNormW a (coeffOf fun x => toFun c x ^ n)
        ≤ 2 ^ a * wienerNormW a c * (2 ^ a * wienerNormW a c) ^ n := by
          gcongr; exact ih.2
      _ = _ := by ring

theorem hasSum_coeffOf_exp (c : Coeff d) (hs : Summable fun k => ‖c k‖)
    (k : Lattice d) :
    HasSum (fun n : ℕ => coeffOf (fun x => toFun c x ^ n) k / (n.factorial : ℂ))
      (coeffOf (fun x => Real.exp (toFun c x)) k) := by
  set S := ∑' k, ‖c k‖ with hS
  set F : ℕ → Torus d → ℂ := fun n x =>
    UnitAddTorus.mFourier (-k) x * (((toFun c x ^ n / (n.factorial : ℝ) : ℝ)) : ℂ) with hF
  have hu := continuous_toFun c hs
  have hint : ∀ n, Integrable (F n) := fun n =>
    ((UnitAddTorus.mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp ((hu.pow n).div_const _))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ n x, ‖F n x‖ ≤ S ^ n / (n.factorial : ℝ) := by
    intro n x
    have h1 : ‖UnitAddTorus.mFourier (-k) x‖ = 1 := Torus.norm_mode (-k) x
    simp only [hF, norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_pow, Nat.abs_cast]
    gcongr
    exact abs_toFun_le c hs x
  have hsum : Summable fun n => ∫ x, ‖F n x‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (Real.summable_pow_div_factorial S)
    calc ∫ x, ‖F n x‖ ≤ ∫ _x : Torus d, S ^ n / (n.factorial : ℝ) :=
          integral_mono (hint n).norm (integrable_const _) (hnorm n)
      _ = S ^ n / (n.factorial : ℝ) := by simp
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ n, ∫ x, F n x = coeffOf (fun x => toFun c x ^ n) k / (n.factorial : ℂ) := by
    intro n
    have : ∀ x, F n x = ((n.factorial : ℂ))⁻¹ *
        (UnitAddTorus.mFourier (-k) x * (((toFun c x ^ n : ℝ)) : ℂ)) := by
      intro x
      simp only [hF]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul]
    unfold coeffOf
    rw [funFourierCoeff_eq_int]
    ring
  have e2 : ∀ x, ∑' n, F n x = UnitAddTorus.mFourier (-k) x * ((Real.exp (toFun c x) : ℝ) : ℂ) := by
    intro x
    have h1 : HasSum (fun n : ℕ => (((toFun c x ^ n / (n.factorial : ℝ) : ℝ)) : ℂ))
        ((Real.exp (toFun c x) : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr (hasSum_exp_real _)
    exact (h1.mul_left (UnitAddTorus.mFourier (-k) x)).tsum_eq
  simp_rw [e1] at h
  simp_rw [e2] at h
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  exact h

/-- Exponential of a function with coefficients in `A_a`: `coeffOf (exp ∘ toFun c)` is the
coefficient-series `∑ c^{*n}/n!`, lies in `A_a`, with `‖·‖_{A_a} ≤ exp(2^a ‖c‖_{A_a})`. -/
theorem exp_wienerW (a : ℝ) (ha : 0 ≤ a) (c : Coeff d) (hreal : IsRealCoeff c)
    (hc : Summable fun k => sobWeight (a / 2) k * ‖c k‖) :
    (Summable fun k => sobWeight (a / 2) k * ‖coeffOf (fun x => Real.exp (toFun c x)) k‖) ∧
      wienerNormW a (coeffOf (fun x => Real.exp (toFun c x))) ≤ Real.exp (2 ^ a * wienerNormW a c) := by
  have hs : Summable fun k => ‖c k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by have := one_le_sobWeight (m := a / 2) (by positivity) k
                   nlinarith [norm_nonneg (c k)]) hc
  set w : Lattice d → ℝ := sobWeight (a / 2) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sobWeight_nonneg _ k
  have hw1 : ∀ k, 1 ≤ w k := fun k => one_le_sobWeight (by positivity) k
  set P : ℕ → Coeff d := fun n => coeffOf (fun x => toFun c x ^ n) with hP
  set E : Coeff d := coeffOf (fun x => Real.exp (toFun c x)) with hE
  set K : ℝ := 2 ^ a * wienerNormW a c with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ wienerNormW a c :=
      tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ k) (norm_nonneg _)
    positivity
  have hPW := wienerNormW_pow a ha c hreal hc
  -- the double family `G n k = w k ‖P n k‖ / n!`
  set G : ℕ → Lattice d → ℝ := fun n k => w k * ‖P n k‖ / (n.factorial : ℝ) with hG
  have hG0 : ∀ n k, 0 ≤ G n k := fun n k => by
    have := hw0 k
    positivity
  have hGk : ∀ n, Summable fun k => G n k := fun n => ((hPW n).1).div_const _
  have hGs : ∀ n, ∑' k, G n k ≤ K ^ n / (n.factorial : ℝ) := by
    intro n
    have : ∑' k, G n k = wienerNormW a (P n) / (n.factorial : ℝ) := by
      unfold wienerNormW; rw [tsum_div_const]
    rw [this]
    exact div_le_div_of_nonneg_right (hPW n).2 (by positivity)
  have hGn : Summable fun n => ∑' k, G n k :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (hG0 n)) hGs (Real.summable_pow_div_factorial K)
  have hGsum : Summable (Function.uncurry G) := by
    have hnn : (0 : ℕ × Lattice d → ℝ) ≤ Function.uncurry G := fun p => hG0 p.1 p.2
    exact (summable_prod_of_nonneg hnn).mpr ⟨hGk, hGn⟩
  have hGsum' : Summable (fun p : Lattice d × ℕ => G p.2 p.1) :=
    (Equiv.summable_iff (Equiv.prodComm (ℕ) (Lattice d))
      (f := fun p : Lattice d × ℕ => G p.2 p.1)).mp (by exact hGsum)
  have hnn' : (0 : Lattice d × ℕ → ℝ) ≤ fun p => G p.2 p.1 := fun p => hG0 p.2 p.1
  obtain ⟨hGn', hGk'⟩ := (summable_prod_of_nonneg hnn').mp hGsum'
  -- pointwise
  have hpt : ∀ k, w k * ‖E k‖ ≤ ∑' n, G n k := by
    intro k
    have hnorm : Summable fun n : ℕ => ‖P n k‖ / (n.factorial : ℝ) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hGn' k)
      have h1 := hw1 k
      have : ‖P n k‖ ≤ w k * ‖P n k‖ := by nlinarith [norm_nonneg (P n k)]
      exact div_le_div_of_nonneg_right this (by positivity)
    have h1 : ‖E k‖ ≤ ∑' n : ℕ, ‖P n k‖ / (n.factorial : ℝ) := by
      have hh : HasSum (fun n : ℕ => P n k / (n.factorial : ℂ)) (E k) := hasSum_coeffOf_exp c hs k
      rw [← hh.tsum_eq]
      have hn : Summable fun n : ℕ => ‖P n k / (n.factorial : ℂ)‖ :=
        hnorm.congr fun n => by simp
      refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq (tsum_congr fun n => ?_))
      simp
    calc w k * ‖E k‖ ≤ w k * ∑' n : ℕ, ‖P n k‖ / (n.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (hw0 k)
      _ = ∑' n, G n k := by
          rw [← tsum_mul_left]
          exact tsum_congr fun n => by simp only [hG]; ring
  have hsumE : Summable fun k => w k * ‖E k‖ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (norm_nonneg _)) hpt hGk'
  refine ⟨hsumE, ?_⟩
  have hcomm : ∑' k, ∑' n, G n k = ∑' n, ∑' k, G n k :=
    (Summable.tsum_comm (f := fun (k : Lattice d) (n : ℕ) => G n k) hGsum').symm
  have hexp : ∑' n : ℕ, K ^ n / (n.factorial : ℝ) = Real.exp K := (hasSum_exp_real K).tsum_eq
  unfold wienerNormW
  calc ∑' k, sobWeight (a / 2) k * ‖E k‖ ≤ ∑' k, ∑' n, G n k := hsumE.tsum_le_tsum hpt hGk'
    _ = ∑' n, ∑' k, G n k := hcomm
    _ ≤ ∑' n : ℕ, K ^ n / (n.factorial : ℝ) :=
        hGn.tsum_le_tsum hGs (Real.summable_pow_div_factorial K)
    _ = Real.exp K := hexp

end HRS.PDE.MFProduct
