import HRS.MS.QsfIbp4

/-!
# S4.5 packet B2, part 5: the uniform bound of the integrand, continuity in `X`, pointwise limit in `ε`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- The `ε`-integrand. -/
def s45_I (s a β ε : ℝ) (v : Euc d → Euc d) (F : EucConfig d N → ℝ) (X : EucConfig d N) : ℝ :=
  s45_w s a β ε X * (((∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
    β * (F X * (∑ i, a * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫)))

theorem s45_div_le {v : Euc d → Euc d} {Dv : ℝ} (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) (x : Euc d) :
    |s45_div v x| ≤ d * Dv := by
  unfold s45_div
  calc |∑ a : Fin d, (fderiv ℝ v x (EuclideanSpace.single a (1 : ℝ))) a|
      ≤ ∑ a : Fin d, |(fderiv ℝ v x (EuclideanSpace.single a (1 : ℝ))) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin d, Dv := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (s45_abs_coord_le _ _).trans ?_
        calc ‖fderiv ℝ v x (EuclideanSpace.single a (1 : ℝ))‖
            ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.single a (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ Dv * 1 := by
              rw [EuclideanSpace.norm_single]; simp only [norm_one, mul_one]; exact hDv x
          _ = Dv := mul_one _
    _ = d * Dv := by simp

theorem s45_lip {v : Euc d → Euc d} (hv : Differentiable ℝ v) {Dv : ℝ} (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv)
    (x y : Euc d) : ‖v x - v y‖ ≤ Dv * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hv z) (fun z _ => hDv z)
    (mem_univ y) (mem_univ x)

/-- **Uniform domination of the integrand.** -/
theorem s45_I_le {s : ℝ} (hs0 : 0 ≤ s) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N)
    {v : Euc d → Euc d} (hv : Differentiable ℝ v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv)
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ} {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ X : EucConfig d N,
      |s45_I s a β ε v F X| ≤ K * (1 + ‖X‖) * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hDv0 : 0 ≤ Dv := (norm_nonneg _).trans (hDv 0)
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  have hDF0 : 0 ≤ DF := (norm_nonneg _).trans (hDF 0)
  obtain ⟨Cw, hCw0, hCw⟩ := s45_w_le (d := d) (N := N) (s := s) ha hβ hN
  obtain ⟨CP, hCP0, hCP⟩ := s45_pair_w_le (d := d) (N := N) hs0 ha hβ hN hDv0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨Cw * (N * (d * Dv) * BF + DF * Bv) + β * BF * N * a * Bv * Cw + β * BF * N * CP,
    by positivity, fun ε hε hε1 X => ?_⟩
  set E : ℝ := Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hw := hCw ε hε hε1 X
  have hw0 := (s45_w_pos s a β ε X).le
  set A : ℝ := ((∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) with hA
  set B : ℝ := ∑ i, a * ⟪X i, v (X i)⟫ with hB
  set P : ℝ := (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
    ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫ with hP
  have hvf : ‖(fun k => v (X k) : EucConfig d N)‖ ≤ Bv :=
    (pi_norm_le_iff_of_nonneg hBv0).2 fun k => hBv _
  have hA1 : |A| ≤ N * (d * Dv) * BF + DF * Bv := by
    have h1 : |∑ k, s45_div v (X k)| ≤ N * (d * Dv) := by
      calc |∑ k, s45_div v (X k)| ≤ ∑ k, |s45_div v (X k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin N, (d * Dv) := Finset.sum_le_sum fun k _ => s45_div_le hDv _
        _ = N * (d * Dv) := by simp
    have h2 : |fderiv ℝ F X (fun k => v (X k))| ≤ DF * Bv := by
      calc |fderiv ℝ F X (fun k => v (X k))| = ‖fderiv ℝ F X (fun k => v (X k))‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ F X‖ * ‖(fun k => v (X k) : EucConfig d N)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ DF * Bv := mul_le_mul (hDF X) hvf (norm_nonneg _) hDF0
    calc |A| ≤ |(∑ k, s45_div v (X k)) * F X| + |fderiv ℝ F X (fun k => v (X k))| := abs_add_le _ _
      _ ≤ N * (d * Dv) * BF + DF * Bv := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul h1 (hBF X) (abs_nonneg _) (by positivity)) h2
  have hB1 : |B| ≤ N * a * ‖X‖ * Bv := by
    calc |B| ≤ ∑ i, |a * ⟪X i, v (X i)⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, a * (‖X‖ * Bv) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg ha.le]
          refine mul_le_mul_of_nonneg_left ?_ ha.le
          calc |⟪X i, v (X i)⟫| ≤ ‖X i‖ * ‖v (X i)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖X‖ * Bv := mul_le_mul (norm_le_pi_norm X i) (hBv _) (norm_nonneg _) (norm_nonneg _)
      _ = N * a * ‖X‖ * Bv := by simp; ring
  have hP1 : s45_w s a β ε X * |P| ≤ N * CP * E := by
    have hterm : ∀ i j : Fin N, j ∈ Finset.univ.filter (fun j => i < j) →
        s45_w s a β ε X * |⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫| ≤ CP * E := by
      intro i j hj
      have hij : i < j := by simpa using hj
      exact hCP ε hε hε1 X i j hij _ (s45_lip hv hDv _ _)
    have hsum : s45_w s a β ε X * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫| ≤ CP * E * ((N : ℝ) * N) := by
      calc s45_w s a β ε X * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫|
          ≤ s45_w s a β ε X * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
              |⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫| := by
            refine mul_le_mul_of_nonneg_left ?_ hw0
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
              s45_w s a β ε X * |⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫| := by
            simp_rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), CP * E :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hterm i j hj
        _ = (CP * E) * ∑ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [mul_comm]
        _ ≤ CP * E * ((N : ℝ) * N) :=
            mul_le_mul_of_nonneg_left (s45_card_pairs_le N) (by positivity)
    rw [hP, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    calc s45_w s a β ε X * (1 / (N : ℝ) * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫|)
        = 1 / (N : ℝ) * (s45_w s a β ε X * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫|) := by ring
      _ ≤ 1 / (N : ℝ) * (CP * E * ((N : ℝ) * N)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = N * CP * E := by field_simp
  unfold s45_I
  rw [← hA, ← hB, ← hP]
  have hF1 := hBF X
  have e1 : |s45_w s a β ε X * (A - β * (F X * (B + P)))| ≤
      s45_w s a β ε X * |A| + β * |F X| * (s45_w s a β ε X * |B|) +
        β * |F X| * (s45_w s a β ε X * |P|) := by
    rw [abs_mul, abs_of_pos (s45_w_pos s a β ε X)]
    have : |A - β * (F X * (B + P))| ≤ |A| + β * |F X| * (|B| + |P|) := by
      calc |A - β * (F X * (B + P))| ≤ |A| + |β * (F X * (B + P))| := abs_sub _ _
        _ = |A| + β * (|F X| * |B + P|) := by
            rw [abs_mul, abs_of_pos hβ, abs_mul]
        _ ≤ |A| + β * (|F X| * (|B| + |P|)) := by
            gcongr; exact abs_add_le _ _
        _ = _ := by ring
    calc s45_w s a β ε X * |A - β * (F X * (B + P))|
        ≤ s45_w s a β ε X * (|A| + β * |F X| * (|B| + |P|)) :=
          mul_le_mul_of_nonneg_left this hw0
      _ = _ := by ring
  refine e1.trans ?_
  have t1 : s45_w s a β ε X * |A| ≤ Cw * E * (N * (d * Dv) * BF + DF * Bv) :=
    mul_le_mul hw hA1 (abs_nonneg _) (by positivity)
  have t2 : β * |F X| * (s45_w s a β ε X * |B|) ≤
      β * BF * (Cw * E * (N * a * ‖X‖ * Bv)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hF1 hβ.le) ?_ (by positivity) (by positivity)
    exact mul_le_mul hw hB1 (abs_nonneg _) (by positivity)
  have t3 : β * |F X| * (s45_w s a β ε X * |P|) ≤ β * BF * (N * CP * E) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hF1 hβ.le) hP1 (by positivity) (by positivity)
  have hn : 0 ≤ ‖X‖ := norm_nonneg _
  have c1 : 0 ≤ Cw * (N * (d * Dv) * BF + DF * Bv) := by positivity
  have c2 : 0 ≤ β * BF * N * a * Bv * Cw := by positivity
  have c3 : 0 ≤ β * BF * N * CP := by positivity
  calc _ ≤ Cw * E * (N * (d * Dv) * BF + DF * Bv) + β * BF * (Cw * E * (N * a * ‖X‖ * Bv)) +
        β * BF * (N * CP * E) := add_le_add (add_le_add t1 t2) t3
    _ = E * (Cw * (N * (d * Dv) * BF + DF * Bv) + β * BF * N * a * Bv * Cw * ‖X‖ +
        β * BF * N * CP) := by ring
    _ ≤ E * ((Cw * (N * (d * Dv) * BF + DF * Bv) + β * BF * N * a * Bv * Cw + β * BF * N * CP) *
        (1 + ‖X‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        nlinarith [mul_nonneg c1 hn, mul_nonneg c3 hn]
    _ = _ := by ring

end S45

end
