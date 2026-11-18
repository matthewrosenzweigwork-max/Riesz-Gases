import HRS.Uniform.Q54Aux10

/-!
# Q54c, part 2: Riesz representation of a bounded functional on smooth test functions

`rieszElt r ℓ` is the element of `E_r = H^{-r}_0` whose (unweighted) real Fourier coefficients are
`ℓ(e_k)`.  If `ℓ` is linear on smooth functions, vanishes on constants, and `|ℓ φ| ≤ B ‖φ‖_{H^r}`, then
`‖rieszElt r ℓ‖ ≤ B` and `eval (rieszElt r ℓ) φ = ℓ φ` for every smooth `φ` (`riesz_functional`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q48b HRS.Uniform.Q54

variable {d : ℕ}

/-- The Riesz element of a functional on test functions: coefficients `ℓ(e_k)`. -/
def rieszElt (r : ℝ) (ℓ : (Torus d → ℝ) → ℝ) : NegSobolev d r :=
  NegSobolev.ofSeq r fun k => ℓ (Torus.realMode k)

theorem _root_.HRS.NegSobolev.coord_sub' {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k :=
  congrFun (lp.coeFn_sub (E := fun _ : NonzeroLattice d => ℝ) (p := 2)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G)) k

/-- Hypotheses of the Riesz lemma. -/
structure RieszHyp (r B : ℝ) (ℓ : (Torus d → ℝ) → ℝ) : Prop where
  hB : 0 ≤ B
  lin : ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ → ∀ α β : ℝ,
    ℓ (fun x => α * φ x + β * ψ x) = α * ℓ φ + β * ℓ ψ
  bd : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → |ℓ φ| ≤ B * sobolevNorm r φ
  const : ∀ c : ℝ, ℓ (fun _ => c) = 0

theorem RieszHyp.finsum {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ)
    (F : Finset (NonzeroLattice d)) (α : NonzeroLattice d → ℝ) :
    ℓ (q48bTest F α) = ∑ k ∈ F, α k * ℓ (Torus.realMode k) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have e : q48bTest (∅ : Finset (NonzeroLattice d)) α = fun _ => (0 : ℝ) := by
      funext x; simp [q48bTest]
    rw [e, h.const]; simp
  | insert a F ha ih =>
    have e1 : q48bTest (insert a F) α =
        fun x => α a * Torus.realMode a x + 1 * q48bTest F α x := by
      funext x; simp only [q48bTest, Finset.sum_insert ha]; ring
    rw [e1, h.lin _ _ (q48b_isSmooth_realMode a) (q48bTest_smooth F α), ih,
      Finset.sum_insert ha]
    ring

theorem RieszHyp.smul {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (α : ℝ) :
    ℓ (fun x => α * φ x) = α * ℓ φ := by
  have := h.lin φ (fun _ => 0) hφ (isSmooth_const' 0) α 0
  simpa [h.const] using this

theorem RieszHyp.sub {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    ℓ (fun x => φ x - ψ x) = ℓ φ - ℓ ψ := by
  have := h.lin φ ψ hφ hψ 1 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

/-- the finite section bound `∑_{F} ⟨k⟩^{-2r} c_k² ≤ B²`. -/
theorem RieszHyp.sec_le {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ)
    (F : Finset (NonzeroLattice d)) :
    ∑ k ∈ F, q48bW k ^ (-2 * r) * ℓ (Torus.realMode k) ^ 2 ≤ B ^ 2 := by
  classical
  set S : ℝ := ∑ k ∈ F, q48bW k ^ (-2 * r) * ℓ (Torus.realMode k) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos k).le _) (sq_nonneg _)
  set φ : Torus d → ℝ := q48bTest F fun k => q48bW k ^ (-2 * r) * ℓ (Torus.realMode k) with hφ
  have h1 : ℓ φ = S := by
    rw [hφ, h.finsum, hS]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h2 : sobolevNorm r φ = Real.sqrt S := by
    rw [hφ, q48bTest_sobolevNorm, hS]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw := q48bW_pos k
    have : q48bW k ^ (2 * r) * (q48bW k ^ (-2 * r) * ℓ (Torus.realMode k)) ^ 2 =
        q48bW k ^ (-2 * r) * ℓ (Torus.realMode k) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (q48bW k ^ (-2 * r)) 2, ← Real.rpow_mul hw.le]
      rw [← mul_assoc, ← Real.rpow_add hw]
      have e : 2 * r + (-2 * r * ((2 : ℕ) : ℝ)) = -2 * r := by push_cast; ring
      rw [e]
    exact this
  have h3 := h.bd φ (by rw [hφ]; exact q48bTest_smooth _ _)
  rw [h1, h2] at h3
  have h4 : S ≤ B * Real.sqrt S := by
    refine le_trans (le_abs_self S) h3
  have h5 : Real.sqrt S ≤ B := by
    by_cases hz : S = 0
    · rw [hz]; simpa using h.hB
    · have hp : 0 < Real.sqrt S := Real.sqrt_pos.2 (lt_of_le_of_ne hS0 (Ne.symm hz))
      have : Real.sqrt S * Real.sqrt S ≤ B * Real.sqrt S := by
        rw [Real.mul_self_sqrt hS0]; exact h4
      exact le_of_mul_le_mul_right this hp
  calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2

theorem RieszHyp.memℓp {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * ℓ (Torus.realMode k)) 2 := by
  rw [Torus.memℓp_two_iff]
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ (Lattice.jp k.1 ^ (-r) * ℓ (Torus.realMode k)) ^ 2 :=
    fun k => sq_nonneg _
  refine summable_of_sum_le hnn (c := B ^ 2) fun F => ?_
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (h.sec_le F)
  have hw := q48bW_pos k
  show (Lattice.jp k.1 ^ (-r) * ℓ (Torus.realMode k)) ^ 2 =
    q48bW k ^ (-2 * r) * ℓ (Torus.realMode k) ^ 2
  rw [mul_pow, Torus.jp_rpow_sq]
  unfold q48bW
  rw [show 2 * -r = -2 * r by ring]

theorem rieszElt_coord {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ) (k : NonzeroLattice d) :
    NegSobolev.coord (rieszElt r ℓ) k = Lattice.jp k.1 ^ (-r) * ℓ (Torus.realMode k) :=
  NegSobolev.coord_ofSeq_of_mem _ h.memℓp k

theorem rieszElt_fourierCoeff {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ)
    (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (rieszElt r ℓ) k = ℓ (Torus.realMode k) := by
  unfold NegSobolev.fourierCoeff
  rw [rieszElt_coord h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem rieszElt_norm_le {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ) :
    ‖rieszElt r ℓ‖ ≤ B := by
  have hsq := (NegSobolev.coord_sq (rieszElt r ℓ))
  have h1 : ‖rieszElt r ℓ‖ ^ 2 ≤ B ^ 2 := by
    rw [hsq.2]
    refine hsq.1.tsum_le_of_sum_le fun F => ?_
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (h.sec_le F)
    rw [rieszElt_coord h, mul_pow, Torus.jp_rpow_sq]
    have hw := q48bW_pos k
    unfold q48bW
    rw [show 2 * -r = -2 * r by ring]
  exact le_of_sq_le_sq h1 h.hB

/-- The Riesz element represents `ℓ` on smooth test functions. -/
theorem rieszElt_eval {r B : ℝ} {ℓ : (Torus d → ℝ) → ℝ} (h : RieszHyp r B ℓ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) : NegSobolev.eval (rieszElt r ℓ) φ = ℓ φ := by
  classical
  set c : NonzeroLattice d → ℝ := fun k => ℓ (Torus.realMode k) with hc
  have hMS : MemSobolev r φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ r
  have hL2 : MemLp φ 2 (volume : Measure (Torus d)) := hMS.1
  -- ℓ ignores the mean
  have hmean : ℓ φ = ℓ (fun x => φ x - Torus.mean φ) := by
    have := h.sub hφ (isSmooth_const' (Torus.mean φ))
    rw [this, h.const]; ring
  set φ₀ : Torus d → ℝ := fun x => φ x - Torus.mean φ with hφ₀
  have hφ₀s : Torus.IsSmooth φ₀ := isSmooth_sub' hφ (isSmooth_const' _)
  have hφ₀c : ∀ k, Torus.funRealCoeff φ₀ k = Torus.funRealCoeff φ k := by
    intro k
    have := q48b_funRealCoeff_add_const (g := φ) hL2 (-Torus.mean φ) k
    simpa [hφ₀, sub_eq_add_neg] using this
  -- the coefficient sum
  have hcs : Summable fun k => c k * Torus.funRealCoeff φ k := by
    have h1 : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-r) * c k) ^ 2 :=
      (Torus.memℓp_two_iff _).1 h.memℓp
    have h2 : Summable fun k : NonzeroLattice d =>
        (Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k) ^ 2 :=
      (Torus.memℓp_two_iff _).1 (memℓp_wseqF hMS)
    refine Summable.of_norm_bounded ((h1.add h2).mul_left (1 / 2)) fun k => ?_
    have hj := Real.rpow_pos_of_pos (Torus.jp_pos k.1) r
    have hj' := Real.rpow_pos_of_pos (Torus.jp_pos k.1) (-r)
    have e : c k * Torus.funRealCoeff φ k =
        (Lattice.jp k.1 ^ (-r) * c k) * (Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k) := by
      have : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ r = 1 := by
        rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
      calc c k * Torus.funRealCoeff φ k = (Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ r) *
          (c k * Torus.funRealCoeff φ k) := by rw [this, one_mul]
        _ = _ := by ring
    rw [Real.norm_eq_abs, e, abs_mul]
    nlinarith [sq_abs (Lattice.jp k.1 ^ (-r) * c k), sq_abs (Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k),
      sq_nonneg (|Lattice.jp k.1 ^ (-r) * c k| - |Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k|),
      abs_nonneg (Lattice.jp k.1 ^ (-r) * c k), abs_nonneg (Lattice.jp k.1 ^ r * Torus.funRealCoeff φ k)]
  have hev : NegSobolev.eval (rieszElt r ℓ) φ = ∑' k, c k * Torus.funRealCoeff φ k := by
    unfold NegSobolev.eval
    refine tsum_congr fun k => ?_
    rw [rieszElt_fourierCoeff h]
  rw [hev, hmean]
  -- approximate by partial Fourier sums
  set φF : Finset (NonzeroLattice d) → (Torus d → ℝ) :=
    fun F => q48bTest F (fun k => Torus.funRealCoeff φ k) with hφF
  have hφFs : ∀ F, Torus.IsSmooth (φF F) := fun F => q48bTest_smooth _ _
  have hA : Tendsto (fun F : Finset (NonzeroLattice d) => ℓ (φF F)) atTop
      (𝓝 (∑' k, c k * Torus.funRealCoeff φ k)) := by
    have := hcs.hasSum
    refine this.congr fun F => ?_
    rw [hφF, h.finsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdiff : ∀ F, |ℓ φ₀ - ℓ (φF F)| ≤ B * Real.sqrt (∑' k : NonzeroLattice d,
      (if k ∈ F then 0 else Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2)) := by
    intro F
    have hd := h.bd (fun x => φ₀ x - φF F x) (isSmooth_sub' hφ₀s (hφFs F))
    rw [h.sub hφ₀s (hφFs F)] at hd
    refine hd.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) h.hB)
    unfold sobolevNorm
    have hmean0 : Torus.mean (fun x => φ₀ x - φF F x) = 0 := by
      have h1 : Torus.mean φ₀ = 0 := by
        unfold Torus.mean
        simp only [hφ₀]
        rw [integral_sub (q48b_integrable_cont (q48b_continuous_of_isSmooth hφ)) (integrable_const _)]
        simp [Torus.mean]
      have h2 : Torus.mean (φF F) = 0 := q48bTest_mean _ _
      have h3 : Torus.mean (fun x => φ₀ x - φF F x) = Torus.mean φ₀ - Torus.mean (φF F) := by
        unfold Torus.mean
        exact integral_sub (q48b_integrable_cont (q48b_continuous_of_isSmooth hφ₀s))
          (q48b_integrable_cont (q48bTest_continuous _ _))
      rw [h3, h1, h2]; ring
    rw [hmean0]
    congr 1
    rw [zero_pow two_ne_zero, zero_add]
    refine tsum_congr fun k => ?_
    have hc1 : Torus.funRealCoeff (fun x => φ₀ x - φF F x) k =
        Torus.funRealCoeff φ₀ k - Torus.funRealCoeff (φF F) k :=
      funRealCoeff_sub' (q48b_continuous_of_isSmooth hφ₀s |>.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
        ((q48bTest_continuous _ _).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) k
    rw [hc1, hφ₀c, hφF, q48bTest_coeff]
    by_cases hk : k ∈ F
    · simp [hk]
    · simp [hk]
  have htail : Tendsto (fun F : Finset (NonzeroLattice d) => B * Real.sqrt (∑' k : NonzeroLattice d,
      (if k ∈ F then 0 else Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2))) atTop (𝓝 0) := by
    have := tail_tendsto (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff φ k ^ 2)
      (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)) hMS.2
    have h2 := (Real.continuous_sqrt.tendsto 0).comp this
    simpa using h2.const_mul B
  have hB' : Tendsto (fun F : Finset (NonzeroLattice d) => ℓ (φF F)) atTop (𝓝 (ℓ φ₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun F => norm_nonneg _) (fun F => ?_) htail
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hdiff F
  exact tendsto_nhds_unique hA hB'

end HRS.Uniform.Q54c
