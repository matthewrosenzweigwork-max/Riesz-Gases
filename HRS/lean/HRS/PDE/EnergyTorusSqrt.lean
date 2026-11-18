import HRS.PDE.EnergyTorusDeriv
import HRS.PDE.Toolbox.CoeffL2
import HRS.PDE.EnergySymbol
import HRS.Analysis.Category

/-!
# `H¹` multiplication by `√μ` (summability of the weighted dissipation)

For `0 ≤ μ ∈ C²(𝕋^d)` the function `√μ` is Lipschitz, and multiplication by it maps `H¹` to `H¹`.
We obtain this from the `C¹` product bound (`mulCoeff_memHs_one`) applied to `√(μ+ε)` and a
lower-semicontinuity argument as `ε → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ET

variable {d : ℕ}

theorem norm_iteratedFDeriv_le_cbNorm {φ : Torus d → ℝ} {k j : ℕ} (hjk : j ≤ k)
    (hφ : Torus.IsCk k φ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ Torus.cbNorm k φ := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift j φ (hφ.of_le (by exact_mod_cast hjk))
  refine (le_ciSup hbdd x).trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))

/-- The regularised square root. -/
def sqrtEps (μ : Torus d → ℝ) (ε : ℝ) : Torus d → ℝ := fun x => Real.sqrt (μ x + ε)

theorem sqrtEps_cb {μ : Torus d → ℝ} (hμ : Torus.IsCk 2 μ) (hnn : ∀ x, 0 ≤ μ x) {Λ : ℝ}
    (hΛ : Torus.cbNorm 2 μ ≤ Λ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Torus.IsCk 1 (sqrtEps μ ε) ∧
      Torus.cbNorm 1 (sqrtEps μ ε) ≤ Real.sqrt (Λ + 1) + Real.sqrt (Λ / 2) := by
  set f := Torus.lift μ with hfdef
  have hf2 : ContDiff ℝ 2 f := by exact_mod_cast hμ
  have hf1 : ContDiff ℝ 1 f := hf2.of_le (by norm_num)
  have hnn' : ∀ y, 0 ≤ f y := fun y => hnn _
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg 2 μ).trans hΛ
  have hlift : Torus.lift (sqrtEps μ ε) = fun y => Real.sqrt (f y + ε) := rfl
  have hcd : ContDiff ℝ 1 (fun y => Real.sqrt (f y + ε)) :=
    (hf1.add contDiff_const).sqrt (fun y => (by have := hnn' y; positivity))
  have hIs : Torus.IsCk 1 (sqrtEps μ ε) := by
    unfold Torus.IsCk; rw [hlift]; exact_mod_cast hcd
  refine ⟨hIs, ?_⟩
  -- value bound
  have hval : ∀ y, f y ≤ Λ := by
    intro y
    have h0 := norm_iteratedFDeriv_le_cbNorm (k := 2) (j := 0) (by norm_num) hμ y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    exact (le_abs_self _).trans (h0.trans hΛ)
  -- Lipschitz bound of the derivative of f
  have hDf : Differentiable ℝ (fderiv ℝ f) := by
    have := hf2.fderiv_right (m := 1) (by norm_num)
    exact this.differentiable (by norm_num)
  have hlipf : LipschitzWith (Real.toNNReal Λ) (fun x => fderiv ℝ (fun y => f y + ε) x) := by
    have : (fun x => fderiv ℝ (fun y => f y + ε) x) = fderiv ℝ f := by
      funext x; exact fderiv_add_const ε
    rw [this]
    refine lipschitzWith_of_nnnorm_fderiv_le hDf fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hΛ0]
    have h2 := norm_iteratedFDeriv_le_cbNorm (k := 2) (j := 2) le_rfl hμ x
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1), norm_iteratedFDeriv_one] at h2
    exact h2.trans hΛ
  have hsl := sqrt_lipschitz (E := Euc d) (fun y => f y + ε) (hf1.add contDiff_const)
    (fun y => by have := hnn' y; positivity) Λ hΛ0 hlipf
  have hder : ∀ x, ‖fderiv ℝ (fun y => Real.sqrt (f y + ε)) x‖ ≤ Real.sqrt (Λ / 2) := by
    intro x
    have := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hsl
    rwa [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at this
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  refine add_le_add (Real.iSup_le (fun x => ?_) (Real.sqrt_nonneg _))
    (Real.iSup_le (fun x => ?_) (Real.sqrt_nonneg _))
  · rw [hlift, norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith [hval x])
  · rw [hlift, norm_iteratedFDeriv_one]
    exact hder x


/-! ### Convergence as `ε → 0` -/

theorem coeffOf_sub_fun {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    coeffOf (fun x => f x - g x) = coeffOf f - coeffOf g := by
  funext k
  rw [coeffOf_eq_coeffOfC, coeffOf_eq_coeffOfC, coeffOf_eq_coeffOfC, Pi.sub_apply,
    coeffOfC_eq_integral', coeffOfC_eq_integral', coeffOfC_eq_integral', ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.ofReal_sub]; ring
  · exact ((Torus.continuous_mode k).star.mul
      (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((Torus.continuous_mode k).star.mul
      (Complex.continuous_ofReal.comp hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem mulCoeff_sub_left {a a' c : Coeff d} (ha : MemHs 0 a) (ha' : MemHs 0 a') (hc : MemHs 0 c) :
    mulCoeff (a - a') c = mulCoeff a c - mulCoeff a' c := by
  funext k
  simp only [mulCoeff, Pi.sub_apply, sub_mul]
  exact Summable.tsum_sub (summable_mulCoeff a c ha hc k) (summable_mulCoeff a' c ha' hc k)

theorem abs_sqrtEps_sub_le {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    |Real.sqrt (x + ε) - Real.sqrt x| ≤ Real.sqrt ε := by
  have h1 : Real.sqrt x ≤ Real.sqrt (x + ε) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (x + ε) ≤ Real.sqrt x + Real.sqrt ε := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hx
    have := Real.sq_sqrt hε
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg ε)]
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem sqrtEps_continuous {μ : Torus d → ℝ} (hμ : Continuous μ) (hnn : ∀ x, 0 ≤ μ x) (ε : ℝ)
    (hε : 0 ≤ ε) : Continuous (sqrtEps μ ε) :=
  Real.continuous_sqrt.comp (hμ.add continuous_const)

theorem tendsto_sqrtEps_mulCoeff {μ : Torus d → ℝ} (hμ : Continuous μ) (hnn : ∀ x, 0 ≤ μ x)
    {c : Coeff d} (hc : MemHs 1 c) (k : Lattice d) :
    Tendsto (fun n : ℕ => mulCoeff (coeffOf (sqrtEps μ (1 / ((n : ℝ) + 1)))) c k) atTop
      (𝓝 (mulCoeff (coeffOf (fun x => Real.sqrt (μ x))) c k)) := by
  have hc0 : MemHs 0 c := hc.mono (by norm_num)
  have hsq : Continuous fun x => Real.sqrt (μ x) := Real.continuous_sqrt.comp hμ
  have hε : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖mulCoeff (coeffOf (sqrtEps μ (1 / ((n : ℝ) + 1)))) c k -
      mulCoeff (coeffOf (fun x => Real.sqrt (μ x))) c k‖ ≤
      Real.sqrt (1 / ((n : ℝ) + 1)) * Real.sqrt (hsNormSq 0 c) := by
    intro n
    set e := 1 / ((n : ℝ) + 1) with he
    have hce := sqrtEps_continuous hμ hnn e (hε n)
    have hsub : coeffOf (fun x => sqrtEps μ e x - Real.sqrt (μ x)) =
        coeffOf (sqrtEps μ e) - coeffOf (fun x => Real.sqrt (μ x)) :=
      coeffOf_sub_fun hce hsq
    have hlin : mulCoeff (coeffOf (sqrtEps μ e)) c - mulCoeff (coeffOf fun x => Real.sqrt (μ x)) c =
        mulCoeff (coeffOf (fun x => sqrtEps μ e x - Real.sqrt (μ x))) c := by
      rw [hsub, mulCoeff_sub_left (coeffOf_memHs_zero hce).1 (coeffOf_memHs_zero hsq).1 hc0]
    have hbc : Continuous fun x => sqrtEps μ e x - Real.sqrt (μ x) := hce.sub hsq
    obtain ⟨hm, hm'⟩ := mulCoeff_l2_bound hbc hc0
    have hsup : Torus.supNorm (fun x => sqrtEps μ e x - Real.sqrt (μ x)) ≤ Real.sqrt e := by
      refine ciSup_le fun x => ?_
      rw [Real.norm_eq_abs]
      exact abs_sqrtEps_sub_le (hnn x) (hε n)
    have h1 : ‖(mulCoeff (coeffOf (fun x => sqrtEps μ e x - Real.sqrt (μ x))) c) k‖ ^ 2 ≤
        hsNormSq 0 (mulCoeff (coeffOf (fun x => sqrtEps μ e x - Real.sqrt (μ x))) c) := by
      have := sobWeight_mul_sq_le_hsNormSq hm k
      rwa [sobWeight_zero, one_mul] at this
    have h2 : hsNormSq 0 (mulCoeff (coeffOf (fun x => sqrtEps μ e x - Real.sqrt (μ x))) c) ≤
        (Real.sqrt e * Real.sqrt (hsNormSq 0 c)) ^ 2 := by
      refine hm'.trans ?_
      rw [mul_pow, Real.sq_sqrt (hsNormSq_nonnegE _ _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (supNorm_nonneg _) hsup 2)
        (hsNormSq_nonnegE _ _) |>.trans_eq (by rw [Real.sq_sqrt (hε n)])
    rw [← Pi.sub_apply, hlin]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h1.trans h2)
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have := ((Real.continuous_sqrt.tendsto 0).comp h0).mul_const (Real.sqrt (hsNormSq 0 c))
  simpa using this


/-- **Multiplication by `√μ` on `H¹`.** -/
theorem sqrt_mulCoeff_memHs_one {μ : Torus d → ℝ} (hμ : Torus.IsCk 2 μ) (hnn : ∀ x, 0 ≤ μ x)
    {Λ : ℝ} (hΛ : Torus.cbNorm 2 μ ≤ Λ) {c : Coeff d} (hc : MemHs 1 c) :
    MemHs 1 (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) c) ∧
      hsNormSq 1 (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) c) ≤
        (2 * (d : ℝ) + 2) * (Real.sqrt (Λ + 1) + Real.sqrt (Λ / 2)) ^ 2 * hsNormSq 1 c := by
  have hcont : Continuous μ := continuous_of_isCk (hμ.of_le (by norm_num))
  set Q := Real.sqrt (Λ + 1) + Real.sqrt (Λ / 2) with hQ
  refine memHs_of_sum_le fun S => ?_
  have hlim : Tendsto (fun n : ℕ => ∑ k ∈ S, sobWeight 1 k *
      ‖mulCoeff (coeffOf (sqrtEps μ (1 / ((n : ℝ) + 1)))) c k‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, sobWeight 1 k * ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) c k‖ ^ 2)) := by
    refine tendsto_finset_sum _ fun k _ => ?_
    exact ((tendsto_sqrtEps_mulCoeff hcont hnn hc k).norm.pow 2).const_mul _
  refine le_of_tendsto' hlim fun n => ?_
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hck, hcb⟩ := sqrtEps_cb hμ hnn hΛ hε hε1
  obtain ⟨h1, h2⟩ := mulCoeff_memHs_one hck hc
  refine (sum_le_hsNormSq h1 S).trans (h2.trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonnegE _ _)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (cbNorm_nonneg 1 _) hcb 2

/-- `0 ≤ 𝔪_q ≤ K sobWeight 1`. -/
theorem symbolK_le_sobWeight (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    (k : Lattice d) :
    0 ≤ symbolK d s q k ∧
      symbolK d s q k ≤ ((∑ i, |q i|) ^ 2 * |rieszConst d s|) * sobWeight 1 k := by
  refine ⟨symbolK_nonneg hd hs0 hsd q k, ?_⟩
  have hinner : inner ℝ q (Lattice.toEuc k) = ∑ i, q i * ((k i : ℤ) : ℝ) := by
    simp [PiLp.inner_apply, Lattice.toEuc, mul_comm]
  set A := ∑ i, |q i| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  set g := rieszCoeff d s k with hg
  have h1 : |2 * Real.pi * inner ℝ q (Lattice.toEuc k)| ≤ A * Lattice.jp k := by
    rw [hinner, Finset.mul_sum, hA, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hpi : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
    have := two_pi_abs_coord_le_jp k i
    calc |2 * Real.pi * (q i * ((k i : ℤ) : ℝ))| = |q i| * (2 * Real.pi * |((k i : ℤ) : ℝ)|) := by
          rw [abs_mul (2 * Real.pi), hpi, abs_mul]; ring
      _ ≤ |q i| * Lattice.jp k := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have h2 : |2 * Real.pi * inner ℝ q (Lattice.toEuc k) * g| ≤ A * (|rieszConst d s| * Lattice.jp k) := by
    rw [hinner, Finset.mul_sum, Finset.sum_mul, hA, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hpi : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
    have := abs_rieszCoeff_mul_le s hsd.le k i
    calc |2 * Real.pi * (q i * ((k i : ℤ) : ℝ)) * g|
        = |q i| * (|g| * (2 * Real.pi * |((k i : ℤ) : ℝ)|)) := by
          rw [abs_mul, abs_mul (2 * Real.pi), hpi, abs_mul]; ring
      _ ≤ |q i| * (|rieszConst d s| * Lattice.jp k) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hjp : sobWeight (1 : ℝ) k = Lattice.jp k ^ 2 := by
    rw [sobWeight_eq_jp]; norm_num
  have hsK : symbolK d s q k = (2 * Real.pi * inner ℝ q (Lattice.toEuc k)) *
      (2 * Real.pi * inner ℝ q (Lattice.toEuc k) * g) := by
    unfold symbolK; rw [← hg]; ring
  calc symbolK d s q k ≤ |symbolK d s q k| := le_abs_self _
    _ = |2 * Real.pi * inner ℝ q (Lattice.toEuc k)| *
        |2 * Real.pi * inner ℝ q (Lattice.toEuc k) * g| := by rw [hsK, abs_mul]
    _ ≤ (A * Lattice.jp k) * (A * (|rieszConst d s| * Lattice.jp k)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hA0 (Real.sqrt_nonneg _))
    _ = (A ^ 2 * |rieszConst d s|) * sobWeight 1 k := by rw [hjp]; ring

/-- Summability of the retained dissipation for `H¹` data: `√μ u ∈ H¹`. -/
theorem summable_symbolK_sqrt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    {μ : Torus d → ℝ} (hμ : Torus.IsCk 2 μ) (hnn : ∀ x, 0 ≤ μ x) {Λ : ℝ}
    (hΛ : Torus.cbNorm 2 μ ≤ Λ) {c : Coeff d} (hc : MemHs 1 c) :
    Summable fun k => symbolK d s q k *
      ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) c k‖ ^ 2 := by
  obtain ⟨hw, -⟩ := sqrt_mulCoeff_memHs_one hμ hnn hΛ hc
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (symbolK_le_sobWeight hd hs0 hsd q k).1
    (sq_nonneg _)) (fun k => ?_) (hw.mul_left ((∑ i, |q i|) ^ 2 * |rieszConst d s|))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (symbolK_le_sobWeight hd hs0 hsd q k).2 (sq_nonneg _)

end HRS.PDE.ET
