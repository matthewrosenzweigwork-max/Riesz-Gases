import HRS.Main.GFB3Aux1
import HRS.Uniform.Comparison
import HRS.PDE.MeanFieldPairInverse
import HRS.PDE.EnergyTorusSqrt

/-!
# Packet GFB3, part 2: the trace-duality test function `x ↦ ∑_j B(b_{x,j}, b_{x,j})`

For a bounded bilinear form `B` on `E_γ` the function `F_B(x) = ∑_j B(b_{x,j}, b_{x,j})` is `C^{d+1}` with all derivatives
up to that order bounded by `C ‖B‖` (`gfb3_bVec_iter_bound` and the Leibniz bound), hence it has finite `Ḣ^α`-seminorm
(`α ≤ d/2`) bounded by `C ‖B‖`, and `|ΔF_B| ≤ C ‖B‖`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform

variable {d : ℕ}

/-! ### Explicit Fourier decay from a derivative bound -/

open HRS.Torus in
theorem gfb3_fcoef_decay {φ : Torus d → ℝ} {n : ℕ} (hd : ContDiff ℝ n (lift φ)) {B₀ : ℝ}
    (hB₀ : ∀ y : Euc d, ‖iteratedFDeriv ℝ n (lift φ) y‖ ≤ B₀) (k : NonzeroLattice d) :
    ‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n ≤ B₀ * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n := by
  have hG : Per (lift φ) := fun y n => lift_periodic φ y n
  have hpi := Real.pi_pos
  have hk0 : 0 < Lattice.enorm k.1 := by
    have := (jp_le_enorm k)
    have h1 := jp_ge_one k.1
    by_contra h
    have : Lattice.enorm k.1 ≤ 0 := not_lt.mp h
    nlinarith
  set e : Euc d := (Lattice.enorm k.1)⁻¹ • Lattice.toEuc k.1 with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hk0]
    exact inv_mul_cancel₀ hk0.ne'
  have hdot : Lattice.dot k.1 e = Lattice.enorm k.1 := by
    rw [dot_eq_inner, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    unfold Lattice.enorm
    field_simp
  let m : Fin n → Euc d := fun _ => e
  set g := descend (fun z => iteratedFDeriv ℝ n (lift φ) z m) with hg
  have hper : Per (fun z => iteratedFDeriv ℝ n (lift φ) z m) := hG.iteratedFDeriv_apply m
  have hbd : ∀ x, |g x| ≤ B₀ := by
    intro x
    rw [hg, ← mk_rep x, descend_mk hper]
    have h1 := (iteratedFDeriv ℝ n (lift φ) (rep x)).le_opNorm m
    have h2 : ∏ i, ‖m i‖ = 1 := by simp [m, hne]
    rw [h2, mul_one] at h1
    exact (Real.norm_eq_abs _ ▸ h1).trans (hB₀ (rep x))
  have h1 := norm_fcoef_le_of_bound hbd k.1
  rw [hg, fcoef_iteratedFDeriv hG hd k.1 n le_rfl m, descend_lift] at h1
  have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by simp [Complex.norm_I]
  rw [norm_mul, norm_mul, norm_pow, h2, norm_prod] at h1
  simp only [m, hdot, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0] at h1
  have h3 : Lattice.jp k.1 ^ n ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (jp_pos _).le ?_ n
    have := jp_le_enorm k
    calc Lattice.jp k.1 ≤ (1 + 2 * Real.pi) * Lattice.enorm k.1 := this
      _ = _ := by field_simp
  calc ‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n
      ≤ ‖fcoef φ k.1‖ * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * ((2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n * ‖fcoef φ k.1‖) := by ring
    _ ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * B₀ := by gcongr
    _ = _ := by ring

/-- The constant of the homogeneous Sobolev bound. -/
def gfb3_Chom (d : ℕ) (α : ℝ) : ℝ :=
  ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ (d + 1) *
    Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) - α))))

theorem gfb3_hom_bound (α : ℝ) (hα0 : 0 ≤ α) (hα : 2 * α ≤ d) {F : Torus d → ℝ}
    (hd : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) (Torus.lift F)) {K : ℝ}
    (hK : ∀ y : Euc d, ‖iteratedFDeriv ℝ (d + 1) (Torus.lift F) y‖ ≤ K) :
    HasFiniteHomSobolev α F ∧ homSobolev α F ≤ gfb3_Chom d α * K := by
  set n : ℕ := d + 1 with hn
  set c : ℝ := (1 + 2 * Real.pi) / (2 * Real.pi) with hc
  have hc0 : 0 ≤ c := by positivity
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hS : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - α))) :=
    summable_jp_rpow _ (by
      have : (n : ℝ) = d + 1 := by rw [hn]; push_cast; ring
      rw [this]; linarith)
  have hterm : ∀ k : NonzeroLattice d,
      (2 * Real.pi * Lattice.enorm k.1) ^ (2 * α) * ‖Torus.fcoef F k.1‖ ^ 2 ≤
        (K * c ^ n) ^ 2 * Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - α))) := by
    intro k
    have hj := Torus.jp_pos k.1
    have hdec := gfb3_fcoef_decay hd hK k
    have h1 : ‖Torus.fcoef F k.1‖ ≤ K * c ^ n * (Lattice.jp k.1 ^ n)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      exact hdec
    have h2 : ‖Torus.fcoef F k.1‖ ^ 2 ≤ (K * c ^ n) ^ 2 * ((Lattice.jp k.1 ^ n)⁻¹) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (2 * Real.pi * Lattice.enorm k.1) ^ (2 * α) ≤ Lattice.jp k.1 ^ (2 * α) :=
      Real.rpow_le_rpow (by unfold Lattice.enorm; positivity) (Torus.two_pi_enorm_le_jp k.1) (by linarith)
    have h4 : Lattice.jp k.1 ^ (2 * α) * ((Lattice.jp k.1 ^ n)⁻¹) ^ 2 =
        Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - α))) := by
      have e1 : ((Lattice.jp k.1 ^ n)⁻¹) ^ 2 = Lattice.jp k.1 ^ (-(2 * (n : ℝ))) := by
        rw [Real.rpow_neg hj.le, mul_comm, Real.rpow_mul hj.le, Real.rpow_two, Real.rpow_natCast, inv_pow]
      rw [e1, ← Real.rpow_add hj]
      congr 1
      ring
    calc (2 * Real.pi * Lattice.enorm k.1) ^ (2 * α) * ‖Torus.fcoef F k.1‖ ^ 2
        ≤ Lattice.jp k.1 ^ (2 * α) * ((K * c ^ n) ^ 2 * ((Lattice.jp k.1 ^ n)⁻¹) ^ 2) :=
          mul_le_mul h3 h2 (sq_nonneg _) (Real.rpow_nonneg hj.le _)
      _ = (K * c ^ n) ^ 2 * (Lattice.jp k.1 ^ (2 * α) * ((Lattice.jp k.1 ^ n)⁻¹) ^ 2) := by ring
      _ = _ := by rw [h4]
  have hsum : Summable fun k : NonzeroLattice d =>
      (2 * Real.pi * Lattice.enorm k.1) ^ (2 * α) * ‖Torus.fcoef F k.1‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (by unfold Lattice.enorm; positivity) _)
      (sq_nonneg _)) hterm (hS.mul_left _)
  refine ⟨hsum, ?_⟩
  unfold homSobolev homSobolevSq
  have hle : ∑' k : NonzeroLattice d, (2 * Real.pi * Lattice.enorm k.1) ^ (2 * α) * ‖Torus.fcoef F k.1‖ ^ 2 ≤
      (K * c ^ n) ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - α))) := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm (hS.mul_left _)
  refine (Real.sqrt_le_sqrt hle).trans ?_
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  unfold gfb3_Chom
  rw [← hn, ← hc]
  nlinarith [Real.sqrt_nonneg (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - α)))),
    pow_nonneg hc0 n]

/-! ### The test function and its derivative bounds -/

/-- `F_B(x) = ∑_j B(b_{x,j}, b_{x,j})`. -/
def gfb3_F (γ : ℝ) (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) (x : Torus d) : ℝ :=
  ∑ j : Fin d, B (bVec γ j x) (bVec γ j x)

/-- The bound of the `i`-th derivative of `F_B / ‖B‖`. -/
def gfb3_Cn (d : ℕ) (γ : ℝ) (i : ℕ) : ℝ :=
  d * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * (∑' k, gfb3_majorant d γ l k) *
    (∑' k, gfb3_majorant d γ (i - l) k)

lemma gfb3_lift_F (γ : ℝ) (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) :
    Torus.lift (gfb3_F γ B) = fun y : Euc d => ∑ j : Fin d, B (bVec γ j (Torus.mk y)) (bVec γ j (Torus.mk y)) :=
  rfl

lemma gfb3_F_contDiff (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) + n + 1 < γ)
    (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) :
    ContDiff ℝ n (Torus.lift (gfb3_F γ B)) := by
  rw [gfb3_lift_F]
  refine ContDiff.sum fun j _ => ?_
  exact B.isBoundedBilinearMap.contDiff.comp ((gfb3_bVec_contDiff n hγ j).prodMk (gfb3_bVec_contDiff n hγ j))

lemma gfb3_F_iter_bound (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) + n + 1 < γ)
    (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) (i : ℕ) (hi : i ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (Torus.lift (gfb3_F γ B)) y‖ ≤ ‖B‖ * gfb3_Cn d γ i := by
  rw [gfb3_lift_F]
  have hcd : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContDiff ℝ i
      (fun y : Euc d => B (bVec γ j (Torus.mk y)) (bVec γ j (Torus.mk y))) := by
    intro j _
    exact (B.isBoundedBilinearMap.contDiff.comp ((gfb3_bVec_contDiff n hγ j).prodMk
      (gfb3_bVec_contDiff n hγ j))).of_le (by exact_mod_cast hi)
  rw [iteratedFDeriv_sum hcd]
  simp only [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin d, ‖iteratedFDeriv ℝ i (fun y : Euc d => B (bVec γ j (Torus.mk y))
      (bVec γ j (Torus.mk y))) y‖ ≤ ‖B‖ * (gfb3_Cn d γ i / d) := by
    intro j
    have hb := B.norm_iteratedFDeriv_le_of_bilinear (gfb3_bVec_contDiff n hγ j)
      (gfb3_bVec_contDiff n hγ j) y (n := i) (by exact_mod_cast hi)
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg B))
    have hd0 : (d : ℝ) ≠ 0 := by
      have : 0 < d := Fin.pos j
      positivity
    unfold gfb3_Cn
    rw [mul_div_cancel_left₀ _ hd0]
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 := gfb3_bVec_iter_bound n hγ j l (hl'.trans hi) y
    have h2 := gfb3_bVec_iter_bound n hγ j (i - l) ((Nat.sub_le _ _).trans hi) y
    have hch : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _)
      (mul_nonneg hch ((norm_nonneg _).trans h1))
  calc _ ≤ ∑ _j : Fin d, ‖B‖ * (gfb3_Cn d γ i / d) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = ‖B‖ * gfb3_Cn d γ i := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp [gfb3_Cn]
        · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : (d : ℝ) ≠ 0 := by positivity
          field_simp

end HRS.GF
