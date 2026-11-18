import HRS.MS.MovBridgeAux8

/-!
# MOV-2b, part 1: Hermite coefficient multipliers on `L²` and the `Σ^r` scale

Namespace `HRS.MS.MovLin`, helpers `mov2b_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`).

For a bounded real sequence `c : ℕ^d → ℝ` and `g ∈ L²(ℝ^d)` the multiplier
`mov2b_mult c g = ∑_α c_α ⟨g,h_α⟩ h_α ∈ L²` (an element of `Lp ℝ 2`; `HasSum` in `Lp` through the Hilbert
basis `exists_hermiteHilbertBasisD`).  Facts proved:

* `mov2b_mult_coeff`: `⟨mult c g, h_α⟩ = c_α ⟨g, h_α⟩` (genuine integrals).
* `mov2b_mult_bound`: for `g ∈ Σ^r`, `b ≥ 0`, `K ≥ 0` with `λ_α^{b/2} |c_α| ≤ K`:
  `MemOsc (r+b) (mult c g)` and `‖mult c g‖_{Σ^{r+b}} ≤ K ‖g‖_{Σ^r}`.
* `mov2b_mult_sub`, `mov2b_mult_one`, `mov2b_mult_mult`: linearity in `c`, `mult 1 g = g` a.e., and
  `mult c (mult c' g) = mult (c c') g` (equality in `Lp`).
* `mov2b_spec_bound`: for `q > 0`, `0 < t ≤ 1`, `b ≥ 0`: `λ_α^{b/2} e^{-t q |α|} ≤ K_b t^{-b/2}`.
* a.e. invariance of `hermiteCoeff`, `MemOsc`, `oscNorm`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

/-! ## A fixed Hilbert basis -/

/-- The Hilbert basis of `L²(ℝ^d)` consisting of the `hermiteLpD α` (chosen once). -/
def mov2b_basis (d : ℕ) : HilbertBasis (MultiIndex d) ℝ (Lp ℝ 2 (volume : Measure (Euc d))) :=
  Classical.choose (exists_hermiteHilbertBasisD (d := d))

lemma mov2b_basis_apply (α : MultiIndex d) : mov2b_basis d α = hermiteLpD α :=
  Classical.choose_spec (exists_hermiteHilbertBasisD (d := d)) α

lemma mov2b_coeff_eq_repr {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    hermiteCoeff g α = (mov2b_basis d).repr (hg.toLp g) α := by
  rw [HilbertBasis.repr_apply_apply, mov2b_basis_apply, OscSpace.inner_hermiteLpD_toLp g hg α]

lemma mov2b_coeff_sq_summable {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
    Summable fun α : MultiIndex d => hermiteCoeff g α ^ 2 := by
  have := lp_two_summable (ι := MultiIndex d) ((mov2b_basis d).repr (hg.toLp g))
  refine this.congr fun α => ?_
  rw [mov2b_coeff_eq_repr hg α]

lemma mov2b_memℓp_mul {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) :
    Memℓp (fun α => c α * hermiteCoeff g α) 2 := by
  obtain ⟨K, hK⟩ := hc
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_)
    ((mov2b_coeff_sq_summable hg).mul_left (K ^ 2))
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by
    rw [← sq_abs (c α)]; exact pow_le_pow_left₀ (abs_nonneg _) (hK α) 2) (sq_nonneg _)

/-! ## The multiplier -/

/-- The Hermite multiplier `∑_α c_α ⟨g,h_α⟩ h_α ∈ L²` (junk `0` if the series is not summable). -/
def mov2b_mult (c : MultiIndex d → ℝ) (g : Euc d → ℝ) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  ∑' α, (c α * hermiteCoeff g α) • hermiteLpD α

lemma mov2b_mult_hasSum {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) :
    HasSum (fun α => (c α * hermiteCoeff g α) • hermiteLpD α)
      ((mov2b_basis d).repr.symm ⟨fun α => c α * hermiteCoeff g α, mov2b_memℓp_mul hg hc⟩) := by
  have := (mov2b_basis d).hasSum_repr_symm ⟨fun α => c α * hermiteCoeff g α, mov2b_memℓp_mul hg hc⟩
  simpa [mov2b_basis_apply] using this

lemma mov2b_mult_eq {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) :
    mov2b_mult c g =
      (mov2b_basis d).repr.symm ⟨fun α => c α * hermiteCoeff g α, mov2b_memℓp_mul hg hc⟩ :=
  (mov2b_mult_hasSum hg hc).tsum_eq

/-- The Hermite coefficients of `mult c g` are `c_α ⟨g,h_α⟩`. -/
theorem mov2b_mult_coeff {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) (α : MultiIndex d) :
    hermiteCoeff (⇑(mov2b_mult c g) : Euc d → ℝ) α = c α * hermiteCoeff g α := by
  rw [mov2b_coeff_eq_repr (Lp.memLp (mov2b_mult c g)) α, Lp.toLp_coeFn, mov2b_mult_eq hg hc,
    LinearIsometryEquiv.apply_symm_apply]

theorem mov2b_mult_memLp (c : MultiIndex d → ℝ) (g : Euc d → ℝ) :
    MemLp (⇑(mov2b_mult c g) : Euc d → ℝ) 2 (volume : Measure (Euc d)) :=
  Lp.memLp _

/-- The multiplier only depends on the Hermite coefficients of `g`. -/
lemma mov2b_mult_congr {g g' : Euc d → ℝ} (h : ∀ α, hermiteCoeff g α = hermiteCoeff g' α)
    (c : MultiIndex d → ℝ) : mov2b_mult c g = mov2b_mult c g' := by
  unfold mov2b_mult
  exact tsum_congr fun α => by rw [h α]

/-- `mult c (mult c' g) = mult (c c') g`, equality in `Lp` (hence of representatives). -/
theorem mov2b_mult_mult {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c c' : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) (hc' : ∃ K, ∀ α, |c' α| ≤ K) :
    mov2b_mult c (⇑(mov2b_mult c' g) : Euc d → ℝ) = mov2b_mult (fun α => c α * c' α) g := by
  unfold mov2b_mult
  refine tsum_congr fun α => ?_
  have := mov2b_mult_coeff hg hc' α
  unfold mov2b_mult at this
  rw [this]
  congr 1
  ring

/-- Linearity in the multiplier. -/
theorem mov2b_mult_sub {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    {c c' : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K) (hc' : ∃ K, ∀ α, |c' α| ≤ K) :
    mov2b_mult c g - mov2b_mult c' g = mov2b_mult (fun α => c α - c' α) g := by
  have h1 := mov2b_mult_hasSum hg hc
  have h2 := mov2b_mult_hasSum hg hc'
  have e : (fun α => ((c α - c' α) * hermiteCoeff g α) • hermiteLpD α) =
      fun α => (c α * hermiteCoeff g α) • hermiteLpD α -
        (c' α * hermiteCoeff g α) • hermiteLpD α := by
    funext α; rw [← sub_smul, sub_mul]
  have h3 : HasSum (fun α => ((c α - c' α) * hermiteCoeff g α) • hermiteLpD α)
      ((mov2b_basis d).repr.symm ⟨fun α => c α * hermiteCoeff g α, mov2b_memℓp_mul hg hc⟩ -
        (mov2b_basis d).repr.symm ⟨fun α => c' α * hermiteCoeff g α, mov2b_memℓp_mul hg hc'⟩) := by
    rw [e]; exact h1.sub h2
  unfold mov2b_mult
  rw [h1.tsum_eq, h2.tsum_eq, h3.tsum_eq]

/-- `mult 1 g = g` in `L²`. -/
theorem mov2b_mult_one {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
    mov2b_mult (fun _ => (1 : ℝ)) g = hg.toLp g := by
  have hc : ∃ K : ℝ, ∀ _α : MultiIndex d, |(fun _ : MultiIndex d => (1 : ℝ)) _α| ≤ K := ⟨1, fun _ => by simp⟩
  rw [mov2b_mult_eq hg hc]
  have : (⟨fun α => (fun _ : MultiIndex d => (1 : ℝ)) α * hermiteCoeff g α,
      mov2b_memℓp_mul hg hc⟩ : lp (fun _ : MultiIndex d => ℝ) 2) = (mov2b_basis d).repr (hg.toLp g) := by
    ext α
    show 1 * hermiteCoeff g α = _
    rw [one_mul, mov2b_coeff_eq_repr hg α]
  rw [this, LinearIsometryEquiv.symm_apply_apply]

theorem mov2b_mult_one_ae {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
    (⇑(mov2b_mult (fun _ => (1 : ℝ)) g) : Euc d → ℝ) =ᵐ[volume] g := by
  rw [mov2b_mult_one hg]
  exact hg.coeFn_toLp

/-! ## `Σ^r` bounds for multipliers -/

lemma mov2b_osc_term (r b : ℝ) (α : MultiIndex d) (x y : ℝ) :
    oscEigenvalue d α ^ (r + b) * (y * x) ^ 2 =
      oscEigenvalue d α ^ r * x ^ 2 * (oscEigenvalue d α ^ (b / 2) * y) ^ 2 := by
  have h := oscEv_pos α
  rw [Real.rpow_add h, mul_pow (oscEigenvalue d α ^ (b / 2)), rpow_half_sq _ _ h]
  ring

theorem mov2b_mult_bound {g : Euc d → ℝ} {r : ℝ} (hg : MemOsc r g) {b : ℝ} (hb : 0 ≤ b)
    {K : ℝ} (hK : 0 ≤ K) {c : MultiIndex d → ℝ}
    (hc : ∀ α, oscEigenvalue d α ^ (b / 2) * |c α| ≤ K) :
    MemOsc (r + b) (⇑(mov2b_mult c g) : Euc d → ℝ) ∧
      oscNorm (r + b) (⇑(mov2b_mult c g) : Euc d → ℝ) ≤ K * oscNorm r g := by
  have hcb : ∃ K', ∀ α, |c α| ≤ K' := by
    refine ⟨K, fun α => ?_⟩
    have h1 : 1 ≤ oscEigenvalue d α ^ (b / 2) :=
      Real.one_le_rpow (oscEv_one_le α) (by linarith)
    calc |c α| = 1 * |c α| := (one_mul _).symm
      _ ≤ oscEigenvalue d α ^ (b / 2) * |c α| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ K := hc α
  have hcoef := mov2b_mult_coeff hg.1 hcb
  have hterm : ∀ α, oscEigenvalue d α ^ (r + b) * hermiteCoeff (⇑(mov2b_mult c g) : Euc d → ℝ) α ^ 2 ≤
      K ^ 2 * (oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2) := by
    intro α
    rw [hcoef α, mul_comm (c α), mov2b_osc_term]
    have h0 : 0 ≤ oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
    have h1 : (oscEigenvalue d α ^ (b / 2) * c α) ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (oscEv_pos α).le _)]
      exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (abs_nonneg _)) (hc α) 2
    nlinarith
  have hnn : ∀ α, 0 ≤ oscEigenvalue d α ^ (r + b) * hermiteCoeff (⇑(mov2b_mult c g) : Euc d → ℝ) α ^ 2 :=
    fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have hsum : Summable fun α => oscEigenvalue d α ^ (r + b) *
      hermiteCoeff (⇑(mov2b_mult c g) : Euc d → ℝ) α ^ 2 :=
    Summable.of_nonneg_of_le hnn hterm (hg.2.mul_left (K ^ 2))
  refine ⟨⟨mov2b_mult_memLp c g, hsum⟩, ?_⟩
  unfold oscNorm
  calc Real.sqrt (∑' α, oscEigenvalue d α ^ (r + b) *
        hermiteCoeff (⇑(mov2b_mult c g) : Euc d → ℝ) α ^ 2)
      ≤ Real.sqrt (K ^ 2 * ∑' α, oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← tsum_mul_left]
        exact hsum.tsum_le_tsum hterm (hg.2.mul_left (K ^ 2))
    _ = K * Real.sqrt (∑' α, oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]

/-- Exact norm formula: the square of the `Σ^r` norm of a multiplier is the weighted coefficient series. -/
theorem mov2b_mult_norm {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) {r : ℝ}
    {c : MultiIndex d → ℝ} (hc : ∃ K, ∀ α, |c α| ≤ K)
    (hs : Summable fun α : MultiIndex d => oscEigenvalue d α ^ r * (c α * hermiteCoeff g α) ^ 2) :
    MemOsc r (⇑(mov2b_mult c g) : Euc d → ℝ) ∧
      oscNorm r (⇑(mov2b_mult c g) : Euc d → ℝ) =
        Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ r * (c α * hermiteCoeff g α) ^ 2) := by
  have hcoef := mov2b_mult_coeff hg hc
  refine ⟨⟨mov2b_mult_memLp c g, hs.congr fun α => by rw [hcoef α]⟩, ?_⟩
  unfold oscNorm
  congr 1
  exact tsum_congr fun α => by rw [hcoef α]

/-! ## A.e. invariance -/

lemma mov2b_hermiteCoeff_congr {f f' : Euc d → ℝ} (h : f =ᵐ[volume] f') (α : MultiIndex d) :
    hermiteCoeff f α = hermiteCoeff f' α := by
  unfold hermiteCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

lemma mov2b_memOsc_congr {f f' : Euc d → ℝ} (h : f =ᵐ[volume] f') (r : ℝ) (hf : MemOsc r f) :
    MemOsc r f' := by
  refine ⟨hf.1.ae_eq h, hf.2.congr fun α => ?_⟩
  rw [mov2b_hermiteCoeff_congr h α]

lemma mov2b_oscNorm_congr {f f' : Euc d → ℝ} (h : f =ᵐ[volume] f') (r : ℝ) :
    oscNorm r f = oscNorm r f' := by
  unfold oscNorm
  congr 1
  exact tsum_congr fun α => by rw [mov2b_hermiteCoeff_congr h α]

/-! ## The spectral bound `λ^{b/2} e^{-tq|α|} ≤ K_b t^{-b/2}` -/

/-- `v^p e^{-v} ≤ 1 + ⌈p⌉!` for `v ≥ 0`, `p ≥ 0`. -/
lemma mov2b_rpow_exp_le (p : ℝ) (hp : 0 ≤ p) (v : ℝ) (hv : 0 ≤ v) :
    v ^ p * Real.exp (-v) ≤ 1 + ((⌈p⌉₊).factorial : ℝ) := by
  have hn : (0 : ℝ) < ((⌈p⌉₊).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 < Real.exp (-v) := Real.exp_pos _
  rcases le_total v 1 with h | h
  · have : v ^ p ≤ 1 := Real.rpow_le_one hv h hp
    calc v ^ p * Real.exp (-v) ≤ 1 * 1 :=
          mul_le_mul this he1 he0.le zero_le_one
      _ ≤ _ := by linarith
  · have h1 : v ^ p ≤ v ^ ((⌈p⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil p)
    rw [Real.rpow_natCast] at h1
    have h2 := Real.pow_div_factorial_le_exp v hv ⌈p⌉₊
    have h3 : v ^ ⌈p⌉₊ ≤ ((⌈p⌉₊).factorial : ℝ) * Real.exp v := by
      rwa [div_le_iff₀ hn, mul_comm] at h2
    calc v ^ p * Real.exp (-v) ≤ v ^ ⌈p⌉₊ * Real.exp (-v) := mul_le_mul_of_nonneg_right h1 he0.le
      _ ≤ (((⌈p⌉₊).factorial : ℝ) * Real.exp v) * Real.exp (-v) :=
          mul_le_mul_of_nonneg_right h3 he0.le
      _ = ((⌈p⌉₊).factorial : ℝ) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := by linarith

/-- The constant `K_b` of the spectral bound. -/
def mov2b_K (d : ℕ) (q b : ℝ) : ℝ :=
  ((d : ℝ) + 2) ^ (b / 2) * Real.exp q * (q ^ (-(b / 2)) * (1 + ((⌈b / 2⌉₊).factorial : ℝ)))

lemma mov2b_K_nonneg (d : ℕ) {q : ℝ} (hq : 0 < q) (b : ℝ) : 0 ≤ mov2b_K d q b := by
  unfold mov2b_K
  have : (0 : ℝ) ≤ (d : ℝ) + 2 := by positivity
  positivity

/-- `|α| = k` ⇒ `λ_α ≤ (d+2)(k+1)`. -/
lemma mov2b_ev_le (α : MultiIndex d) :
    oscEigenvalue d α ≤ ((d : ℝ) + 2) * ((α.degree : ℝ) + 1) := by
  unfold oscEigenvalue
  have : (0 : ℝ) ≤ α.degree := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

/-- **Spectral bound.** For `q > 0`, `0 < t ≤ 1`, `b ≥ 0`:
`λ_α^{b/2} e^{-t q |α|} ≤ K_b t^{-b/2}` with `K_b = mov2b_K d q b` (depends on `d, q, b` only). -/
theorem mov2b_spec_bound {q : ℝ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (α : MultiIndex d) :
    oscEigenvalue d α ^ (b / 2) * Real.exp (-(t * q * (α.degree : ℝ))) ≤
      mov2b_K d q b * t ^ (-(b / 2)) := by
  set k : ℝ := (α.degree : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hp : 0 ≤ b / 2 := by linarith
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hlam := oscEv_pos α
  -- step 1: λ^{b/2} ≤ (d+2)^{b/2} (k+1)^{b/2}
  have s1 : oscEigenvalue d α ^ (b / 2) ≤ ((d : ℝ) + 2) ^ (b / 2) * (k + 1) ^ (b / 2) := by
    rw [← Real.mul_rpow hd2.le (by linarith)]
    exact Real.rpow_le_rpow hlam.le (mov2b_ev_le α) hp
  -- step 2: e^{-tqk} ≤ e^q e^{-tq(k+1)}
  have s2 : Real.exp (-(t * q * k)) ≤ Real.exp q * Real.exp (-(t * q * (k + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_pos ht hq, mul_le_mul_of_nonneg_right ht1 hq.le]
  -- step 3: (k+1)^{b/2} e^{-tq(k+1)} ≤ (tq)^{-b/2} (1 + ⌈b/2⌉!)
  have htq : 0 < t * q := mul_pos ht hq
  have s3 : (k + 1) ^ (b / 2) * Real.exp (-(t * q * (k + 1))) ≤
      (t * q) ^ (-(b / 2)) * (1 + ((⌈b / 2⌉₊).factorial : ℝ)) := by
    have hv : 0 ≤ t * q * (k + 1) := by positivity
    have h := mov2b_rpow_exp_le (b / 2) hp (t * q * (k + 1)) hv
    rw [Real.mul_rpow htq.le (by linarith)] at h
    have e : (t * q) ^ (-(b / 2)) * (t * q) ^ (b / 2) = 1 := by
      rw [← Real.rpow_add htq]; simp
    calc (k + 1) ^ (b / 2) * Real.exp (-(t * q * (k + 1)))
        = (t * q) ^ (-(b / 2)) * (((t * q) ^ (b / 2) * (k + 1) ^ (b / 2)) *
            Real.exp (-(t * q * (k + 1)))) := by
          rw [← mul_assoc, ← mul_assoc, e, one_mul]
      _ ≤ (t * q) ^ (-(b / 2)) * (1 + ((⌈b / 2⌉₊).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg htq.le _)
  have hq' : (t * q) ^ (-(b / 2)) = t ^ (-(b / 2)) * q ^ (-(b / 2)) := Real.mul_rpow ht.le hq.le
  have hA : 0 ≤ ((d : ℝ) + 2) ^ (b / 2) := Real.rpow_nonneg hd2.le _
  have hE : 0 ≤ Real.exp (-(t * q * (k + 1))) := (Real.exp_pos _).le
  have hkp : 0 ≤ (k + 1) ^ (b / 2) := Real.rpow_nonneg (by linarith) _
  calc oscEigenvalue d α ^ (b / 2) * Real.exp (-(t * q * k))
      ≤ (((d : ℝ) + 2) ^ (b / 2) * (k + 1) ^ (b / 2)) *
          (Real.exp q * Real.exp (-(t * q * (k + 1)))) :=
        mul_le_mul s1 s2 (Real.exp_pos _).le (mul_nonneg hA hkp)
    _ = (((d : ℝ) + 2) ^ (b / 2) * Real.exp q) *
          ((k + 1) ^ (b / 2) * Real.exp (-(t * q * (k + 1)))) := by ring
    _ ≤ (((d : ℝ) + 2) ^ (b / 2) * Real.exp q) *
          ((t * q) ^ (-(b / 2)) * (1 + ((⌈b / 2⌉₊).factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left s3 (mul_nonneg hA (Real.exp_pos _).le)
    _ = mov2b_K d q b * t ^ (-(b / 2)) := by
        rw [hq']; unfold mov2b_K; ring

end HRS.MS.MovLin
