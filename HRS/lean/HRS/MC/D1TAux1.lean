import HRS.Kernel.Riesz
import HRS.MC.Per
import HRS.MC.D1F

/-!
# Packet D1T, auxiliary file 1: a uniform theta bound and the lattice tail bound for `ψ̂(tk)²`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
open Complex (I)

namespace HRS.MC.D1T

open HRS

/-- Uniform version of `theta_dim_bound`: the heat kernel on `𝕋^d` is bounded, uniformly in `u ∈ (0,1]`,
away from the origin (here: some normalised coordinate has modulus `≥ δ`). -/
theorem d1t_theta_unif (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ 1 / 2) →
      (∃ i0, δ ≤ |y i0|) →
      ‖∑' k : Lattice d, ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) *
          Torus.mode k (fun i => ((y i : ℝ) : UnitAddCircle))‖ ≤ M := by
  set B := ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 / 8) * (n : ℝ) ^ 2) with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => (Real.exp_pos _).le
  set c := Real.pi ^ 2 * δ ^ 2 / 2 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨(Real.pi * B) ^ d * ((d.factorial : ℝ) / c ^ d), fun u hu hu1 y hy1 ⟨i0, hi0⟩ => ?_⟩
  set x : Torus d := fun i => ((y i : ℝ) : UnitAddCircle) with hx
  set f : Fin d → ℤ → ℂ := fun i n =>
    Complex.exp (2 * Real.pi * I * n * (y i) - u * (n : ℂ) ^ 2) with hf
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    refine (summable_exp_sq u hu).congr fun m => ?_
    simp only [hf]
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m : ℂ)) = ((m : ℝ) : ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d, ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x =
      ∏ i, f i (k i) := by
    intro k
    symm
    rw [hx, mode_eq_prod]
    have h2 : ∏ i, f i (k i) = (∏ i, Complex.exp (-((u : ℂ) * ((k i : ℤ) : ℂ) ^ 2))) *
        ∏ i, Complex.exp (2 * Real.pi * I * (k i : ℤ) * (y i : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hf]
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
    congr 2
    push_cast
    rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  have hδ' : ∀ i (n : ℤ), |y i| ^ 2 ≤ ((n : ℝ) - y i) ^ 2 := by
    intro i n
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have := Int.one_le_abs h
        exact_mod_cast this
      have h2 : |(n : ℝ)| - |y i| ≤ |(n : ℝ) - y i| := abs_sub_abs_le_abs_sub (n : ℝ) (y i)
      have h3 := hy1 i
      have h4 : |y i| ≤ |(n : ℝ) - y i| := by linarith
      rw [← sq_abs ((n : ℝ) - y i)]
      exact pow_le_pow_left₀ (abs_nonneg _) h4 2
  have hre : ∑' k : Lattice d, ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x =
      ∏ i, ∑' n : ℤ, f i n := by
    simp_rw [hterm]
    exact hhas.tsum_eq
  show ‖∑' k : Lattice d, ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x‖ ≤ _
  rw [hre, norm_prod]
  have hbd : ∀ i, ‖∑' n : ℤ, f i n‖ ≤
      Real.sqrt (Real.pi / u) * B * Real.exp (-(Real.pi ^ 2 * |y i| ^ 2 / (2 * u))) :=
    fun i => theta_bound u (y i) |y i| hu hu1 (hy1 i) (hδ' i)
  refine (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbd i)).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  have hsq : Real.sqrt (Real.pi / u) * B ≤ Real.pi * B * (1 / u) := by
    have h1 : 1 ≤ Real.pi / u := by
      rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
    have h2 : Real.sqrt (Real.pi / u) ≤ Real.pi / u :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    calc Real.sqrt (Real.pi / u) * B ≤ (Real.pi / u) * B := by gcongr
      _ = _ := by ring
  have hexp : Real.exp (-∑ i, Real.pi ^ 2 * |y i| ^ 2 / (2 * u)) ≤ Real.exp (-(c * (1 / u))) := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.pi ^ 2 * |y i0| ^ 2 / (2 * u) ≤ ∑ i, Real.pi ^ 2 * |y i| ^ 2 / (2 * u) :=
      Finset.single_le_sum (f := fun i => Real.pi ^ 2 * |y i| ^ 2 / (2 * u)) (fun i _ => by positivity)
        (Finset.mem_univ i0)
    have h2 : Real.pi ^ 2 * δ ^ 2 / (2 * u) ≤ Real.pi ^ 2 * |y i0| ^ 2 / (2 * u) := by
      gcongr
    have e : c * (1 / u) = Real.pi ^ 2 * δ ^ 2 / (2 * u) := by rw [hc]; field_simp
    rw [e]; linarith
  have hexp' : Real.exp (∑ i, -(Real.pi ^ 2 * |y i| ^ 2 / (2 * u))) ≤ Real.exp (-(c * (1 / u))) := by
    rw [Finset.sum_neg_distrib]; exact hexp
  have h0 : 0 ≤ Real.sqrt (Real.pi / u) * B := mul_nonneg (Real.sqrt_nonneg _) hB0
  calc (Real.sqrt (Real.pi / u) * B) ^ d * Real.exp (∑ i, -(Real.pi ^ 2 * |y i| ^ 2 / (2 * u)))
      ≤ (Real.pi * B * (1 / u)) ^ d * Real.exp (-(c * (1 / u))) :=
        mul_le_mul (pow_le_pow_left₀ h0 hsq d) hexp' (Real.exp_pos _).le (by positivity)
    _ = (Real.pi * B) ^ d * ((1 / u) ^ d * Real.exp (-(c * (1 / u)))) := by rw [mul_pow]; ring
    _ ≤ (Real.pi * B) ^ d * ((d.factorial : ℝ) / c ^ d) := by
        gcongr
        exact pow_exp_bound c hcpos d (1 / u) (by positivity)


variable {d : ℕ}

/-- `b_t(k) = ψ̂(tk)²` for `k ≠ 0` and `0` at `k = 0`. -/
def d1tB (ψ : Euc d → ℝ) (t : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2

theorem d1tB_nonneg (ψ : Euc d → ℝ) (t : ℝ) (k : Lattice d) : 0 ≤ d1tB ψ t k := by
  unfold d1tB; split_ifs <;> positivity

/-- Lattice tail bound: `∑_{k ≠ 0} ψ̂(tk)² ≤ K t^{-2(d+1)}` for every `t > 0`. -/
theorem d1t_tail {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      Summable (d1tB ψ t) ∧ ∑' k, d1tB ψ t k ≤ K * (t ^ (2 * (d + 1)))⁻¹ := by
  set q : ℕ := d + 1 with hq
  obtain ⟨C0, hC0, hdec⟩ := Per.per_psiHat_decay hψ q
  set A : ℝ := 1 + 2 * Real.pi with hA
  have hApos : 0 < A := by positivity
  set m : ℝ := (q : ℝ) with hm
  have hm2 : (d : ℝ) < 2 * m := by
    rw [hm, hq]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hbs := summable_jp_rpow (d := d) m hm2
  set B : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun k => by unfold Lattice.jp; positivity
  set K : ℝ := C0 ^ 2 * A ^ (2 * q) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * B, mul_nonneg hK0 hB0, fun t ht => ?_⟩
  have hpt : ∀ k : NonzeroLattice d, d1tB ψ t k.1
      ≤ K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    have hjp1 : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
    have hjp : 0 < Lattice.jp k.1 := lt_of_lt_of_le one_pos hjp1
    have hje : Lattice.jp k.1 ≤ A * Lattice.enorm k.1 := jp_le_enorm k
    have he : 0 < Lattice.enorm k.1 := by
      by_contra h
      have : Lattice.enorm k.1 ≤ 0 := not_lt.mp h
      nlinarith
    have hfc : d1tB ψ t k.1 = fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 := by
      unfold d1tB; simp [k.2]
    rw [hfc]
    set X : ℝ := fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 with hX
    have hnorm : ‖t • Lattice.toEuc k.1‖ = t * Lattice.enorm k.1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; rfl
    have hd1 := hdec (t • Lattice.toEuc k.1)
    rw [hnorm] at hd1
    have hd2 : X * (t * Lattice.enorm k.1) ^ (2 * q) ≤ C0 ^ 2 := by
      have h3 : ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2 ≤ C0 ^ 2 :=
        pow_le_pow_left₀ (by positivity) hd1 2
      have e1 : ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2
          = (t * Lattice.enorm k.1) ^ (2 * q) * fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 := by
        rw [mul_pow, sq_abs, ← pow_mul, mul_comm q 2]
      calc X * (t * Lattice.enorm k.1) ^ (2 * q)
          = ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2 := by
            rw [e1, hX]; ring
        _ ≤ C0 ^ 2 := h3
    have hjq : Lattice.jp k.1 ^ (2 * q) ≤ A ^ (2 * q) * Lattice.enorm k.1 ^ (2 * q) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hjp.le hje _
    have hXP : X * (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q)) ≤ K := by
      calc X * (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q))
          ≤ X * (t ^ (2 * q) * (A ^ (2 * q) * Lattice.enorm k.1 ^ (2 * q))) := by
            gcongr
        _ = A ^ (2 * q) * (X * (t * Lattice.enorm k.1) ^ (2 * q)) := by rw [mul_pow]; ring
        _ ≤ A ^ (2 * q) * C0 ^ 2 := by gcongr
        _ = K := by rw [hK]; ring
    have hrpow : Lattice.jp k.1 ^ (-(2 * m)) = 1 / Lattice.jp k.1 ^ (2 * q) := by
      have : -(2 * m) = -((2 * q : ℕ) : ℝ) := by rw [hm]; push_cast; ring
      rw [this, Real.rpow_neg hjp.le, Real.rpow_natCast, one_div]
    rw [hrpow]
    have hP : 0 < t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q) := by positivity
    have hXle : X ≤ K / (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q)) := by
      rw [le_div_iff₀ hP]; exact hXP
    calc X ≤ K / (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q)) := hXle
      _ = K * (t ^ (2 * q))⁻¹ * (1 / Lattice.jp k.1 ^ (2 * q)) := by
          field_simp
  have hsum0 : Summable fun k : NonzeroLattice d =>
      K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) := hbs.mul_left _
  have hsumNZ : Summable fun k : NonzeroLattice d => d1tB ψ t k.1 :=
    Summable.of_nonneg_of_le (fun k => d1tB_nonneg ψ t k.1) hpt hsum0
  have hsum : Summable (d1tB ψ t) := (Torus.summable_lattice_iff _).mpr hsumNZ
  refine ⟨hsum, ?_⟩
  rw [Torus.tsum_lattice _ hsum]
  have h0 : d1tB ψ t 0 = 0 := by unfold d1tB; simp
  rw [h0, zero_add]
  calc ∑' k : NonzeroLattice d, d1tB ψ t k.1
      ≤ ∑' k : NonzeroLattice d, K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) :=
        hsumNZ.tsum_le_tsum hpt hsum0
    _ = K * (t ^ (2 * q))⁻¹ * B := by rw [tsum_mul_left]
    _ = K * B * (t ^ (2 * q))⁻¹ := by ring

/-- Fourier inversion for `P φ_t - ∫ φ` at a point. -/
theorem d1t_inversion (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (x : Torus d) :
    HasSum (fun k : Lattice d => d1tB ψ t k * Torus.cosMode k x) (Per.perQ ψ t x) := by
  obtain ⟨K, -, hK⟩ := d1t_tail hψ
  have hc : Continuous (Per.perQ ψ t) := (Per.per_fdlPer_continuous hψ ht).sub continuous_const
  have hfc : ∀ k, Torus.fcoef (Per.perQ ψ t) k = ((d1tB ψ t k : ℝ) : ℂ) := by
    intro k
    rw [Per.per_fcoef_Q hd hψ ht]
    unfold d1tB
    split_ifs <;> simp
  have hs : Summable fun k : Lattice d => ‖Torus.fcoef (Per.perQ ψ t) k‖ := by
    refine (hK t ht).1.congr fun k => ?_
    rw [hfc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d1tB_nonneg ψ t k)]
  have h := Torus.hasSum_fcoef_series hc hs x
  have h2 := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h2
  have h3 : (fun k : Lattice d => (Torus.fcoef (Per.perQ ψ t) k * Torus.mode k x).re)
      = fun k => d1tB ψ t k * Torus.cosMode k x := by
    funext k
    rw [hfc, Complex.re_ofReal_mul]
    rfl
  rw [h3] at h2
  exact h2

end HRS.MC.D1T
