import HRS.MC.S7FCDefs

/-!
# S7FCH1B1: Fourier-side algebra for the Gaussian side of a finite-rank field (H1b, part 1)

Helper lemmas for `s7_FC_H1b_gauss` (`HRS/MC/S7FCPlan.lean`), all sorry-free:

* `S7FCH1_tail_tendsto`: tails of a summable nonnegative family along finite sets vanish;
* `S7FCH1_smooth_props`: a smooth torus function is continuous with summable Fourier coefficients;
* `S7FCH1_wsum`: `jp^{2s} (funRealCoeff φ)^2` is summable for every smooth `φ` and every real `s`;
* `S7FCH1_wick_eq`: the Wick coefficients of the pair kernel `K.toFun` are
  `wickCoeff μ K.toFun k l = ∑_{ij} c_ij u_i(k) u_j(l)` with `u_i = funRealCoeff (K.f i)`
  (the `μ`-centring is invisible since `∫ e_k = 0` for `k ≠ 0`);
* `S7FCH1_hs`: the Hilbert-Schmidt summability `∑ wickCoeff² < ∞` needed by `tailHS`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- Tails of a summable nonnegative family along finite sets tend to zero. -/
theorem S7FCH1_tail_tendsto {α : Type*} [DecidableEq α] (g : α → ℝ) (hg : Summable g) :
    Tendsto (fun T : Finset α => ∑' a, if a ∈ T then 0 else g a) atTop (𝓝 0) := by
  have h1 : ∀ T : Finset α,
      HasSum (fun a => if a ∈ T then 0 else g a) (∑' a, g a - ∑ a ∈ T, g a) := by
    intro T
    have h2 : HasSum (fun a => if a ∈ T then g a else 0) (∑ a ∈ T, g a) := by
      have e : ∑ a ∈ T, (if a ∈ T then g a else 0) = ∑ a ∈ T, g a :=
        Finset.sum_congr rfl fun a ha => by simp [ha]
      rw [← e]
      exact hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    have h3 := hg.hasSum.sub h2
    convert h3 using 1
    funext a
    by_cases ha : a ∈ T <;> simp [ha]
  have h4 : Tendsto (fun T : Finset α => ∑ a ∈ T, g a) atTop (𝓝 (∑' a, g a)) := hg.hasSum
  have h5 := (tendsto_const_nhds (x := ∑' a, g a)).sub h4
  rw [sub_self] at h5
  exact h5.congr fun T => ((h1 T).tsum_eq).symm

/-- A `C^∞` function on the torus is continuous and has absolutely summable Fourier coefficients. -/
theorem S7FCH1_smooth_props {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous φ ∧ Summable (fun k : Lattice d => ‖Torus.fcoef φ k‖) := by
  have hC : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) φ := hφ
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => hC.of_le (by exact_mod_cast le_top)
  exact ⟨Torus.continuous_of_continuous_lift (hd 0).continuous, Torus.summable_fcoef_of_contDiff hd⟩

/-- Weighted decay of the real Fourier coefficients of a smooth function: `jp^{2s} u_k^2` is summable for every `s`. -/
theorem S7FCH1_wsum {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (s : ℝ) :
    Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * s) * Torus.funRealCoeff φ k ^ 2) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have hC : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) φ := hφ
  have hd : ∀ m : ℕ, ContDiff ℝ m (Torus.lift φ) := fun m => hC.of_le (by exact_mod_cast le_top)
  have hcont : Continuous φ := Torus.continuous_of_continuous_lift (hd 0).continuous
  have hint : Integrable φ := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨B₀, hB₀⟩ := Torus.fcoef_pow_decay (hd (n + (d + 1)))
  have hsum : Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * ((d : ℝ) + 1)))) :=
    summable_jp_rpow _ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _)) (fun k => ?_)
    (hsum.mul_left (2 * B₀ ^ 2))
  set j := Lattice.jp k.1 with hj_def
  have hj1 : 1 ≤ j := Torus.jp_ge_one k.1
  have hjpos : 0 < j := by linarith
  set a := ‖Torus.fcoef φ k.1‖ with ha_def
  have ha0 : 0 ≤ a := norm_nonneg _
  have hBa : a * j ^ (n + (d + 1)) ≤ |B₀| := le_trans (hB₀ k) (le_abs_self _)
  have hu2 : Torus.funRealCoeff φ k ^ 2 ≤ 2 * a ^ 2 := by
    have h := Torus.abs_funRealCoeff_le hint k
    have hsq : Torus.funRealCoeff φ k ^ 2 ≤ (Real.sqrt 2 * a) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc Torus.funRealCoeff φ k ^ 2 ≤ (Real.sqrt 2 * a) ^ 2 := hsq
      _ = 2 * a ^ 2 := by rw [mul_pow, h2]
  have hw : j ^ (2 * s) ≤ j ^ (2 * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
  have hwn : j ^ (2 * (n : ℝ)) = j ^ (2 * n) := by
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hneg : j ^ (-(2 * ((d : ℝ) + 1))) = ((j ^ (d + 1)) ^ 2)⁻¹ := by
    rw [show (-(2 * ((d : ℝ) + 1))) = -((2 * (d + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hjpos.le, Real.rpow_natCast, ← pow_mul]
    congr 1
    ring
  rw [hneg]
  set J := j ^ (d + 1) with hJ_def
  have hJpos : 0 < J := pow_pos hjpos _
  have hpow : j ^ (n + (d + 1)) = j ^ n * J := pow_add j n (d + 1)
  rw [hpow] at hBa
  have hprod : (a * (j ^ n * J)) ^ 2 ≤ B₀ ^ 2 := by
    have h0 : 0 ≤ a * (j ^ n * J) := by positivity
    calc (a * (j ^ n * J)) ^ 2 ≤ |B₀| ^ 2 := pow_le_pow_left₀ h0 hBa 2
      _ = B₀ ^ 2 := sq_abs _
  have hJ2 : 0 < J ^ 2 := by positivity
  have key : (j ^ n) ^ 2 * a ^ 2 ≤ B₀ ^ 2 / J ^ 2 := by
    rw [le_div_iff₀ hJ2]
    calc (j ^ n) ^ 2 * a ^ 2 * J ^ 2 = (a * (j ^ n * J)) ^ 2 := by ring
      _ ≤ B₀ ^ 2 := hprod
  have hgoal : j ^ (2 * n) * (2 * a ^ 2) ≤ 2 * B₀ ^ 2 * (J ^ 2)⁻¹ := by
    have e1 : j ^ (2 * n) = (j ^ n) ^ 2 := by rw [← pow_mul]; ring_nf
    rw [e1, show 2 * B₀ ^ 2 * (J ^ 2)⁻¹ = 2 * (B₀ ^ 2 / J ^ 2) by ring]
    nlinarith [key]
  have hu0 : 0 ≤ Torus.funRealCoeff φ k ^ 2 := sq_nonneg _
  calc j ^ (2 * s) * Torus.funRealCoeff φ k ^ 2
      ≤ j ^ (2 * n) * Torus.funRealCoeff φ k ^ 2 := by
        rw [← hwn]; exact mul_le_mul_of_nonneg_right hw hu0
    _ ≤ j ^ (2 * n) * (2 * a ^ 2) := mul_le_mul_of_nonneg_left hu2 (by positivity)
    _ ≤ 2 * B₀ ^ 2 * (J ^ 2)⁻¹ := hgoal

/-- Summability of `u_k^2` for a smooth function (the case `s = 0` of `S7FCH1_wsum`). -/
theorem S7FCH1_sq_summable {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable (fun k : NonzeroLattice d => Torus.funRealCoeff φ k ^ 2) := by
  have h := S7FCH1_wsum hφ 0
  simpa using h

/-- The centred real Fourier coefficient: `∫ (f - μ(f)) e_k = ∫ f e_k` for `k ≠ 0`. -/
theorem S7FCH1_centred_coeff (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) (k : NonzeroLattice d) :
    ∫ x, (f x - ∫ z, f z ∂μ) * Torus.realMode k x = Torus.funRealCoeff f k := by
  have hek : Continuous (Torus.realMode k) := Torus.continuous_realMode k
  have hI1 : Integrable (fun x => Torus.realMode k x * f x) :=
    (hek.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI2 : Integrable (fun x => (∫ z, f z ∂μ) * Torus.realMode k x) :=
    (hek.const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : (fun x => (f x - ∫ z, f z ∂μ) * Torus.realMode k x) =
      fun x => Torus.realMode k x * f x - (∫ z, f z ∂μ) * Torus.realMode k x := by
    funext x; ring
  rw [e, integral_sub hI1 hI2, integral_const_mul, Torus.integral_realMode k, mul_zero, sub_zero]
  rfl

/-- Integrals of finite double sums of integrable functions. -/
theorem S7FCH1_int_dsum {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] (μ : Measure Ω)
    (g : ι → ι → Ω → ℝ) (hg : ∀ i j, Integrable (g i j) μ) :
    ∫ y, ∑ i, ∑ j, g i j y ∂μ = ∑ i, ∑ j, ∫ y, g i j y ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hg i j))]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hg i j)

/-- The centred pair kernel of a finite-rank kernel (`canonicalCenter`) is the centred tensor
`∑_{ij} c_ij (f_i(x) - μ(f_i)) (f_j(y) - μ(f_j))`. -/
theorem S7FCH1_canonicalCenter (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (K : FRKernel d)
    (x y : Torus d) :
    HRS.canonicalCenter μ K.toFun x y =
      ∑ i, ∑ j, K.c i j * ((K.f i x - ∫ z, K.f i z ∂μ) * (K.f j y - ∫ z, K.f j z ∂μ)) := by
  have hcf : ∀ i, Continuous (K.f i) := fun i => (S7FCH1_smooth_props (K.smooth i)).1
  have iμ : ∀ g : Torus d → ℝ, Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e1 : ∀ x0 : Torus d, ∫ y', K.toFun x0 y' ∂μ =
      ∑ i, ∑ j, K.c i j * K.f i x0 * ∫ z, K.f j z ∂μ := by
    intro x0
    have hY : ∀ i j, Integrable (fun z => K.c i j * K.f i x0 * K.f j z) μ :=
      fun i j => (iμ _ (hcf j)).const_mul _
    have e : (fun y' => K.toFun x0 y') = fun y' => ∑ i, ∑ j, K.c i j * K.f i x0 * K.f j y' := rfl
    rw [e, S7FCH1_int_dsum μ (fun i j z => K.c i j * K.f i x0 * K.f j z) hY]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have e2 : ∀ y0 : Torus d, ∫ x', K.toFun x' y0 ∂μ =
      ∑ i, ∑ j, K.c i j * (∫ z, K.f i z ∂μ) * K.f j y0 := by
    intro y0
    have hX : ∀ i j, Integrable (fun z => K.c i j * K.f i z * K.f j y0) μ :=
      fun i j => ((iμ _ (hcf i)).const_mul _).mul_const _
    have e : (fun x' => K.toFun x' y0) = fun x' => ∑ i, ∑ j, K.c i j * K.f i x' * K.f j y0 := rfl
    rw [e, S7FCH1_int_dsum μ (fun i j z => K.c i j * K.f i z * K.f j y0) hX]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, integral_const_mul]
  have e3 : ∫ x', ∫ y', K.toFun x' y' ∂μ ∂μ =
      ∑ i, ∑ j, K.c i j * (∫ z, K.f i z ∂μ) * ∫ z, K.f j z ∂μ := by
    simp only [e1]
    rw [S7FCH1_int_dsum μ (fun i j z => K.c i j * K.f i z * ∫ z', K.f j z' ∂μ)]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const, integral_const_mul]
    · intro i j
      exact ((iμ _ (hcf i)).const_mul _).mul_const _
  unfold HRS.canonicalCenter
  rw [e1 x, e2 y, e3]
  have hK : K.toFun x y = ∑ i, ∑ j, K.c i j * K.f i x * K.f j y := rfl
  rw [hK]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The Wick coefficients of the pair kernel of a finite-rank field:
`ĥ°_{kl} = ∑_{ij} c_ij u_i(k) u_j(l)`, `u_i = funRealCoeff (K.f i)`. -/
theorem S7FCH1_wick_eq (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (K : FRKernel d)
    (k l : NonzeroLattice d) :
    wickCoeff μ K.toFun k l =
      ∑ i, ∑ j, K.c i j * Torus.funRealCoeff (K.f i) k * Torus.funRealCoeff (K.f j) l := by
  have hcf : ∀ i, Continuous (K.f i) := fun i => (S7FCH1_smooth_props (K.smooth i)).1
  have hek : Continuous (Torus.realMode k) := Torus.continuous_realMode k
  have hel : Continuous (Torus.realMode l) := Torus.continuous_realMode l
  have iμ : ∀ g : Torus d → ℝ, Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the centred factors
  set a : Fin K.n → Torus d → ℝ := fun i x => (K.f i x - ∫ z, K.f i z ∂μ) * Torus.realMode k x with ha
  set b : Fin K.n → Torus d → ℝ := fun j y => (K.f j y - ∫ z, K.f j z ∂μ) * Torus.realMode l y with hb
  have ha_c : ∀ i, Continuous (a i) := fun i => ((hcf i).sub continuous_const).mul hek
  have hb_c : ∀ j, Continuous (b j) := fun j => ((hcf j).sub continuous_const).mul hel
  have ha_i : ∀ i, Integrable (a i) := fun i => (ha_c i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb_i : ∀ j, Integrable (b j) := fun j => (hb_c j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the integrand as a double sum of products
  have step : ∀ x y, HRS.canonicalCenter μ K.toFun x y * Torus.realMode k x * Torus.realMode l y =
      ∑ i, ∑ j, (K.c i j * a i x) * b j y := by
    intro x y
    rw [S7FCH1_canonicalCenter]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ha, hb]
    ring
  have inner : ∀ x, ∫ y, HRS.canonicalCenter μ K.toFun x y * Torus.realMode k x * Torus.realMode l y =
      ∑ i, ∑ j, (K.c i j * a i x) * ∫ y, b j y := by
    intro x
    simp only [step]
    rw [S7FCH1_int_dsum (volume : Measure (Torus d)) (fun i j y => (K.c i j * a i x) * b j y)
      (fun i j => ((hb_i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  unfold wickCoeff
  simp only [inner]
  have outer := S7FCH1_int_dsum (volume : Measure (Torus d)) (fun i j x => (K.c i j * a i x) * ∫ y, b j y)
    (fun i j => ((ha_i i).const_mul _).mul_const _)
  rw [outer]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  have hA : ∫ x, a i x = Torus.funRealCoeff (K.f i) k := S7FCH1_centred_coeff μ (hcf i) k
  have hB : ∫ y, b j y = Torus.funRealCoeff (K.f j) l := S7FCH1_centred_coeff μ (hcf j) l
  rw [hA, hB]

/-- Two-level Cauchy-Schwarz: `(∑_{ij} f_ij)² ≤ n² ∑_{ij} f_ij²`. -/
theorem S7FCH1_cs2 {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j) ^ 2 ≤ (n : ℝ) * n * ∑ i, ∑ j, (f i j) ^ 2 := by
  have h1 : ∀ i, (∑ j, f i j) ^ 2 ≤ (n : ℝ) * ∑ j, (f i j) ^ 2 := fun i => by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun j => f i j)
  have h2 : (∑ i, ∑ j, f i j) ^ 2 ≤ (n : ℝ) * ∑ i, (∑ j, f i j) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ∑ j, f i j)
  calc (∑ i, ∑ j, f i j) ^ 2 ≤ (n : ℝ) * ∑ i, (∑ j, f i j) ^ 2 := h2
    _ ≤ (n : ℝ) * ∑ i, (n : ℝ) * ∑ j, (f i j) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h1 i) (Nat.cast_nonneg n)
    _ = (n : ℝ) * n * ∑ i, ∑ j, (f i j) ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]

/-- Hilbert-Schmidt summability of the Wick coefficients of a finite-rank kernel. -/
theorem S7FCH1_hs (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (K : FRKernel d) :
    Summable (fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff μ K.toFun p.1 p.2 ^ 2) := by
  have hw : (fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff μ K.toFun p.1 p.2 ^ 2) =
      fun p => (∑ i, ∑ j, K.c i j * Torus.funRealCoeff (K.f i) p.1 * Torus.funRealCoeff (K.f j) p.2) ^ 2 := by
    funext p
    rw [S7FCH1_wick_eq]
  rw [hw]
  have hterm : ∀ i j, Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      (K.c i j * Torus.funRealCoeff (K.f i) p.1 * Torus.funRealCoeff (K.f j) p.2) ^ 2) := by
    intro i j
    have h := ((S7FCH1_sq_summable (K.smooth i)).mul_of_nonneg (S7FCH1_sq_summable (K.smooth j))
      (fun k => sq_nonneg _) (fun l => sq_nonneg _)).mul_left ((K.c i j) ^ 2)
    refine h.congr (fun p => ?_)
    ring
  have hsum : Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      ∑ i, ∑ j, (K.c i j * Torus.funRealCoeff (K.f i) p.1 * Torus.funRealCoeff (K.f j) p.2) ^ 2) :=
    summable_sum (fun i _ => summable_sum (fun j _ => hterm i j))
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) (hsum.mul_left ((K.n : ℝ) * K.n))
  exact S7FCH1_cs2 (fun i j => K.c i j * Torus.funRealCoeff (K.f i) p.1 * Torus.funRealCoeff (K.f j) p.2)

end HRS.MC.Sec7.S7FCH1

end
