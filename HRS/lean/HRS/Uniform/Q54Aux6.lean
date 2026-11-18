import HRS.Uniform.Q54Aux5
import HRS.PDE.HsAnalysis

/-!
# Q54, part 6: the forward generator on trigonometric polynomials at a real Sobolev index

* `gen_trig_bound` (E1): `∑_{k∈S} ⟨k⟩^{2a} ‖(𝓛v)_k‖² ≤ (2ν² + C) ‖v‖²_{H^{a+2}}`;
* `gen_form_trig` (E2): `Re ⟨𝓛 v, v⟩_{H^a} ≤ C ‖v‖²_{H^a} - (ν₀/2) ‖v‖²_{H^{a+1}}` when `ν ≥ ν₀ > 0`.

Both at an arbitrary real index `a` (`K ≥ d + |a| + 4`), uniformly in the coefficients subject to `GenHyp`.
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

open HRS HRS.PDE

variable {d : ℕ}

theorem jp_sq' (k : Lattice d) : Lattice.jp k ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  unfold Lattice.jp
  rw [Real.sq_sqrt (by positivity)]

theorem hsNormSq_trig {n : ℕ} {v : Coeff d} (hv : IsTrigPoly n v) (r : ℝ) :
    hsNormSq r v = ∑ k ∈ boxFin d n, sobWeight r k * ‖v k‖ ^ 2 := by
  unfold hsNormSq
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hv hk]; simp

theorem sobWeight_two_add (a : ℝ) (k : Lattice d) :
    sobWeight (a + 2) k = sobWeight a k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
  unfold sobWeight
  have h : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  rw [show a + 2 = a + (2 : ℕ) by norm_num, Real.rpow_add h, Real.rpow_natCast]

theorem sobWeight_one_add (a : ℝ) (k : Lattice d) :
    sobWeight (a + 1) k = sobWeight a k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) := by
  unfold sobWeight
  have h : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  rw [Real.rpow_add_one h.ne']

theorem gen_trig_bound (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d) (μ : Torus d → ℝ), GenHyp d s K MB Bμ BV D μ →
      ∀ (n : ℕ) (v : Coeff d), IsTrigPoly n v → ∀ S : Finset (Lattice d),
        ∑ k ∈ S, sobWeight a k * ‖forwardGen D μ v k‖ ^ 2 ≤ (2 * D.invβ ^ 2 + C) * hsNormSq (a + 2) v := by
  obtain ⟨A, hA0, hAbd⟩ := genEntry_bound s hsd K MB Bμ BV hMB hBμ hBV
  set e : ℝ := max (s - d + 1) 0 with he
  have he0 : 0 ≤ e := le_max_right _ _
  have he1 : e ≤ 1 := max_le (by linarith) zero_le_one
  obtain ⟨C₁, hC₁, hE1⟩ := weighted_E1 (d := d) a (1 + e) (K - 1 - e) A hA0 (by linarith)
    (by linarith [abs_nonneg a])
  refine ⟨2 * C₁, by positivity, fun D μ h n v hv S => ?_⟩
  have hM := hAbd D μ h
  have key := hE1 (genEntry D μ) hM v (boxFin d n) S
  have hmem : MemHs (a + 2) v := memHs_of_isTrigPolyE hv _
  -- pointwise splitting
  have hpt : ∀ k, sobWeight a k * ‖forwardGen D μ v k‖ ^ 2 ≤
      2 * (D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2) +
        2 * (Lattice.jp k ^ (2 * a) * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2) := by
    intro k
    rw [forwardGen_trig_eq D μ v hv k]
    have h1 : ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k‖ ^ 2 ≤ D.invβ ^ 2 * (1 + 4 * Real.pi ^ 2 *
        Lattice.enorm k ^ 2) ^ 2 * ‖v k‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      unfold laplaceCoeff
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
        linarith
      have h0 : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
      calc D.invβ ^ 2 * ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖) ^ 2
          = D.invβ ^ 2 * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖v k‖ ^ 2 := by ring
        _ ≤ D.invβ ^ 2 * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖v k‖ ^ 2 := by
          gcongr
    have h2 := norm_add_le (((D.invβ : ℝ) : ℂ) * laplaceCoeff v k)
      (∑ l ∈ boxFin d n, genEntry D μ k l * v l)
    have h3 : ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k + ∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2 ≤
        2 * ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k‖ ^ 2 +
          2 * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2 := by
      have := sq_nonneg (‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k‖ -
        ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖)
      nlinarith [norm_nonneg (((D.invβ : ℝ) : ℂ) * laplaceCoeff v k),
        norm_nonneg (∑ l ∈ boxFin d n, genEntry D μ k l * v l),
        norm_nonneg (((D.invβ : ℝ) : ℂ) * laplaceCoeff v k +
          ∑ l ∈ boxFin d n, genEntry D μ k l * v l)]
    have hw := sobWeight_nonnegE a k
    have hw2 : sobWeight a k * (D.invβ ^ 2 * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖v k‖ ^ 2) =
        D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2 := by
      rw [sobWeight_two_add]; ring
    have hwj : sobWeight a k = Lattice.jp k ^ (2 * a) := sobWeight_eq_jp a k
    calc sobWeight a k * ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k +
          ∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2
        ≤ sobWeight a k * (2 * ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k‖ ^ 2 +
          2 * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2) := mul_le_mul_of_nonneg_left h3 hw
      _ = 2 * (sobWeight a k * ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff v k‖ ^ 2) +
          2 * (Lattice.jp k ^ (2 * a) * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2) := by
          rw [← hwj]; ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h1 hw
          rw [hw2] at this
          linarith
  have hS1 : ∑ k ∈ S, D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2 ≤ D.invβ ^ 2 * hsNormSq (a + 2) v := by
    calc ∑ k ∈ S, D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2
        = D.invβ ^ 2 * ∑ k ∈ S, sobWeight (a + 2) k * ‖v k‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ D.invβ ^ 2 * hsNormSq (a + 2) v :=
          mul_le_mul_of_nonneg_left (sum_le_hsNormSq hmem S) (sq_nonneg _)
  have hS2 : ∑ l ∈ boxFin d n, Lattice.jp l ^ (2 * a + 2 * (1 + e)) * ‖v l‖ ^ 2 ≤ hsNormSq (a + 2) v := by
    rw [hsNormSq_trig hv]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [sobWeight_eq_jp]
    refine mul_le_mul_of_nonneg_right (rpow_mono' (Torus.jp_ge_one l) (by linarith)) (sq_nonneg _)
  calc ∑ k ∈ S, sobWeight a k * ‖forwardGen D μ v k‖ ^ 2
      ≤ ∑ k ∈ S, (2 * (D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2) +
        2 * (Lattice.jp k ^ (2 * a) * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = 2 * ∑ k ∈ S, D.invβ ^ 2 * sobWeight (a + 2) k * ‖v k‖ ^ 2 +
        2 * ∑ k ∈ S, Lattice.jp k ^ (2 * a) * ‖∑ l ∈ boxFin d n, genEntry D μ k l * v l‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (D.invβ ^ 2 * hsNormSq (a + 2) v) + 2 * (C₁ * hsNormSq (a + 2) v) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hS1 (by norm_num))
          (mul_le_mul_of_nonneg_left (key.trans (mul_le_mul_of_nonneg_left hS2 hC₁)) (by norm_num))
    _ = (2 * D.invβ ^ 2 + 2 * C₁) * hsNormSq (a + 2) v := by ring

end HRS.Uniform.Q54
