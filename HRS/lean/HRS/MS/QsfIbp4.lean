import HRS.MS.QsfIbp3

/-!
# S4.5 packet B2, part 4: uniform-in-`ε` domination of the integrand

The pair term `⟨∇g_ε(z), v(x) - v(y)⟩` of a Lipschitz field `v` is bounded by `σ L u^{-s/2}`,
`u = |z|²+ε²`; against the weight (`s > 0`: the factor `e^{-(β/N) g_ε}` kills `u^{-s/2} = g_ε`; `s = 0`:
`u^0 = 1`) it is dominated by `C e^{-(βa/4)‖X‖²}` uniformly for `ε ∈ (0,1]`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

theorem s45_sigma_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ movtr_sigma s := by
  unfold movtr_sigma; split_ifs <;> linarith

theorem s45_F_norm_eq {s : ℝ} (hs0 : 0 ≤ s) (ε : ℝ) (z : Euc d) :
    ‖s45_F s ε z‖ = movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * ‖z‖ := by
  unfold s45_F
  rw [norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (s45_sigma_nonneg hs0) (Real.rpow_nonneg (by positivity) _))]

theorem s45_pair_inner_le {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (z w : Euc d) {L : ℝ}
    (hL0 : 0 ≤ L) (hw : ‖w‖ ≤ L * ‖z‖) :
    |⟪s45_F s ε z, w⟫| ≤ movtr_sigma s * L * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) := by
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hσ := s45_sigma_nonneg hs0
  set u := ‖z‖ ^ 2 + ε ^ 2 with hu_def
  have h1 : |⟪s45_F s ε z, w⟫| ≤ ‖s45_F s ε z‖ * ‖w‖ := abs_real_inner_le_norm _ _
  rw [s45_F_norm_eq hs0] at h1
  have hup : 0 ≤ u ^ (-s / 2 - 1) := Real.rpow_nonneg hu.le _
  have h2 : movtr_sigma s * u ^ (-s / 2 - 1) * ‖z‖ * ‖w‖ ≤
      movtr_sigma s * u ^ (-s / 2 - 1) * ‖z‖ * (L * ‖z‖) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have h3 : ‖z‖ ^ 2 ≤ u := by rw [hu_def]; nlinarith [sq_nonneg ε]
  have h4 : u ^ (-s / 2 - 1) * u = u ^ (-s / 2) := by
    rw [Real.rpow_sub_one hu.ne']; field_simp
  calc |⟪s45_F s ε z, w⟫| ≤ movtr_sigma s * u ^ (-s / 2 - 1) * ‖z‖ * ‖w‖ := h1
    _ ≤ movtr_sigma s * u ^ (-s / 2 - 1) * ‖z‖ * (L * ‖z‖) := h2
    _ = movtr_sigma s * L * (u ^ (-s / 2 - 1) * ‖z‖ ^ 2) := by ring
    _ ≤ movtr_sigma s * L * (u ^ (-s / 2 - 1) * u) := by
        gcongr
    _ = _ := by rw [h4]

theorem s45_exp_mul_le {c : ℝ} (hc : 0 < c) (g : ℝ) (hg : 0 ≤ g) :
    g * Real.exp (-(c * g)) ≤ 1 / c := by
  have h := Real.add_one_le_exp (c * g - 1)
  have h2 : c * g ≤ Real.exp (c * g - 1) := by linarith
  have h3 : Real.exp (c * g - 1) = Real.exp (c * g) * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h5 : 0 < Real.exp (c * g) := Real.exp_pos _
  have h6 : c * g * Real.exp (-(c * g)) ≤ 1 := by
    rw [Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_one h5]
    calc c * g ≤ Real.exp (c * g - 1) := h2
      _ = Real.exp (c * g) * Real.exp (-1) := h3
      _ ≤ Real.exp (c * g) * 1 := mul_le_mul_of_nonneg_left h4 h5.le
      _ = Real.exp (c * g) := mul_one _
  rw [le_div_iff₀ hc]
  nlinarith

theorem s45_gEps_nonneg {s : ℝ} (hs : s ≠ 0) (ε : ℝ) (z : Euc d) : 0 ≤ movtr_gEps d s ε z := by
  unfold movtr_gEps
  simp only [hs, ite_false]
  exact Real.rpow_nonneg (by positivity) _

theorem s45_H_ge_pair {s : ℝ} (hs : s ≠ 0) (a ε : ℝ) (ha : 0 ≤ a) (X : EucConfig d N) (i j : Fin N)
    (hij : i < j) :
    ∑ i, confinement a (X i) + (1 / (N : ℝ)) * movtr_gEps d s ε (X i - X j) ≤ s45_H s a ε X := by
  unfold s45_H
  have hN : 0 ≤ 1 / (N : ℝ) := by positivity
  have hsum : movtr_gEps d s ε (X i - X j) ≤
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), movtr_gEps d s ε (X i - X j) := by
    have h1 : movtr_gEps d s ε (X i - X j) ≤
        ∑ j' ∈ Finset.univ.filter (fun j' => i < j'), movtr_gEps d s ε (X i - X j') :=
      Finset.single_le_sum (f := fun j' => movtr_gEps d s ε (X i - X j'))
        (fun j' _ => s45_gEps_nonneg hs ε _) (by simp [hij])
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun i' => ∑ j' ∈ Finset.univ.filter (fun j' => i' < j'),
      movtr_gEps d s ε (X i' - X j')) (fun i' _ => Finset.sum_nonneg fun j' _ =>
        s45_gEps_nonneg hs ε _) (Finset.mem_univ i)
  have := mul_le_mul_of_nonneg_left hsum hN
  linarith

/-- Weighted bound of the pair term, uniform in `ε ∈ (0,1]`. -/
theorem s45_pair_w_le {s : ℝ} (hs0 : 0 ≤ s) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N)
    {L : ℝ} (hL0 : 0 ≤ L) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ X : EucConfig d N, ∀ i j : Fin N, i < j →
      ∀ w : Euc d, ‖w‖ ≤ L * ‖X i - X j‖ →
        s45_w s a β ε X * |⟪s45_F s ε (X i - X j), w⟫| ≤ CP * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by
  obtain ⟨Cw, hCw0, hCw⟩ := s45_w_le (d := d) (N := N) (s := s) ha hβ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hs : s = 0
  · subst hs
    refine ⟨L * Cw, by positivity, fun ε hε hε1 X i j hij w hw => ?_⟩
    have h1 := s45_pair_inner_le hs0 hε (X i - X j) w hL0 hw
    simp only [movtr_sigma, ite_true, neg_zero, zero_div, Real.rpow_zero, mul_one, one_mul] at h1
    calc s45_w 0 a β ε X * |⟪s45_F 0 ε (X i - X j), w⟫| ≤ s45_w 0 a β ε X * L :=
          mul_le_mul_of_nonneg_left h1 (s45_w_pos _ _ _ _ _).le
      _ ≤ (Cw * Real.exp (-((β * a / 4) * ‖X‖ ^ 2))) * L :=
          mul_le_mul_of_nonneg_right (hCw ε hε hε1 X) hL0
      _ = L * Cw * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by ring
  · have hσ := s45_sigma_nonneg hs0
    refine ⟨movtr_sigma s * L * (1 / (β / N)), by positivity, fun ε hε hε1 X i j hij w hw => ?_⟩
    have h1 := s45_pair_inner_le hs0 hε (X i - X j) w hL0 hw
    have hg : movtr_gEps d s ε (X i - X j) = (‖X i - X j‖ ^ 2 + ε ^ 2) ^ (-s / 2) := by
      unfold movtr_gEps; simp only [hs, ite_false]
    rw [← hg] at h1
    set g := movtr_gEps d s ε (X i - X j) with hgdef
    have hg0 : 0 ≤ g := s45_gEps_nonneg hs ε _
    have hconf : (a / 2) * ‖X‖ ^ 2 ≤ ∑ i, confinement a (X i) := by
      unfold confinement
      calc (a / 2) * ‖X‖ ^ 2 ≤ (a / 2) * ∑ i, ‖X i‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (s45_norm_sq_le_sum X) (by positivity)
        _ = ∑ i, a * ‖X i‖ ^ 2 / 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hH := s45_H_ge_pair hs a ε ha.le X i j hij
    have hw1 : s45_w s a β ε X ≤ Real.exp (-(β * a / 2 * ‖X‖ ^ 2)) *
        Real.exp (-((β / N) * g)) := by
      unfold s45_w
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : β * ((a / 2) * ‖X‖ ^ 2) ≤ β * ∑ i, confinement a (X i) :=
        mul_le_mul_of_nonneg_left hconf hβ.le
      have h2 : β * (∑ i, confinement a (X i) + (1 / (N : ℝ)) * g) ≤ β * s45_H s a ε X :=
        mul_le_mul_of_nonneg_left hH hβ.le
      have h3 : β * (∑ i, confinement a (X i) + (1 / (N : ℝ)) * g) =
          β * ∑ i, confinement a (X i) + (β / N) * g := by ring
      have h4 : β * ((a / 2) * ‖X‖ ^ 2) = β * a / 2 * ‖X‖ ^ 2 := by ring
      linarith
    have hcg : g * Real.exp (-((β / N) * g)) ≤ 1 / (β / N) := s45_exp_mul_le (by positivity) g hg0
    calc s45_w s a β ε X * |⟪s45_F s ε (X i - X j), w⟫|
        ≤ (Real.exp (-(β * a / 2 * ‖X‖ ^ 2)) * Real.exp (-((β / N) * g))) *
            (movtr_sigma s * L * g) :=
          mul_le_mul hw1 h1 (abs_nonneg _) (by positivity)
      _ = movtr_sigma s * L * Real.exp (-(β * a / 2 * ‖X‖ ^ 2)) *
            (g * Real.exp (-((β / N) * g))) := by ring
      _ ≤ movtr_sigma s * L * Real.exp (-(β * a / 2 * ‖X‖ ^ 2)) * (1 / (β / N)) :=
          mul_le_mul_of_nonneg_left hcg (by positivity)
      _ ≤ movtr_sigma s * L * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) * (1 / (β / N)) := by
          gcongr
          nlinarith [sq_nonneg ‖X‖, mul_pos hβ ha]
      _ = _ := by ring

end S45

end
