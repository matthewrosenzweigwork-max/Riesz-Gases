import HRS.MS.MovLinAux1

/-!
# MOV-2b, part 2: the shifted oscillator `S_0` and its semigroup `e^{-t S_0}` on `Σ^r`

Namespace `HRS.MS.MovLin`, helpers `mov2b_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`, TeX L4278-4343):
"the oscillator spectral formula gives `‖e^{-tS_0}‖_{Σ^r→Σ^{r+b}} ≤ C_b t^{-b/2}`, `0 < t ≤ 1`".

## Conventions (thermal data of `Moving.lean`)

`ν = β⁻¹`, `q' = β q` (so `∇ log ρ_* = -q' x + B`, `ν q' = q`), `ℓ = √(q'/2) = √(β q / 2)`.
`S_0 u = ν(-Δ u + (q'/2)² |x|² u) - ν q' (d/2) u` (`mov_S0`).  On the dilated Hermite functions
`h_α(ℓ x)` it is diagonal: `S_0 (h_α(ℓ ·)) = q |α| h_α(ℓ ·)` (`mov_S0_hermite_dil`).

## What is proved (all for `d` arbitrary, `β > 0`, `q > 0`)

* `mov_expS0 β q t f` is the semigroup `e^{-tS_0}`: `f ↦ x ↦ M_t(f(ℓ⁻¹ ·))(ℓ x)`, `M_t` the Hermite multiplier
  `h_α ↦ e^{-tq|α|} h_α` (`mov2b_mult`), i.e. the coefficientwise multiplier `e^{-tq|α|}` on the dilated Hermite
  coefficients `⟨f, ℓ^{d/2} h_α(ℓ ·)⟩` (`mov_expS0_dcoeff`; uniqueness `mov_expS0_unique`).  For `f ∈ L²` this is a
  genuine element of `L²`; the representative of an `L²`-class is the one given by `Lp` coercion, so statements
  about `mov_expS0` are either about `MemOsc`/`oscNorm`/Hermite coefficients (representative independent) or
  `=ᵐ`/exact equalities that are explicitly proved.
* `mov_expS0_bound` (the `t^{-b/2}` smoothing): for all real `r`, real `b ≥ 0` there is `C ≥ 0` (depending on
  `d, β, q, r, b` only) with: for `0 < t ≤ 1` and `f ∈ Σ^r`, `e^{-tS_0} f ∈ Σ^{r+b}` and
  `‖e^{-tS_0} f‖_{Σ^{r+b}} ≤ C t^{-b/2} ‖f‖_{Σ^r}`.
* `mov_expS0_bounded`: uniform bound `‖e^{-tS_0} f‖_{Σ^r} ≤ C_r ‖f‖_{Σ^r}`, all `t ≥ 0`.
* `mov_expS0_continuous`: strong continuity on `Σ^r` (with the junk-trap guard `MemOsc r` of the difference).
* `mov_expS0_zero`, `mov_expS0_add`: `e^{-0S_0} f = f` a.e. and `e^{-sS_0} e^{-tS_0} f = e^{-(s+t)S_0} f`
  (exact equality of functions), for `f ∈ L²`, `s, t ≥ 0`.
* `mov_expS0_span`: the action on the span of the dilated Hermite functions.
* `mov_S0_hermite_dil`: the diagonalisation of `S_0`.

The constants of the dilation `Σ^r → Σ^r` come from `mo_dilate`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

/-! ## Definitions -/

/-- The spectral multiplier `α ↦ e^{-t q |α|}`. -/
def mov2b_c (q t : ℝ) (α : MultiIndex d) : ℝ := Real.exp (-(t * q * (α.degree : ℝ)))

/-- `e^{-tS_0}` in terms of a general dilation parameter `l > 0` and rate `q`:
`f ↦ (M_t (f(l⁻¹ ·)))(l ·)`. -/
def mov2b_T (l q t : ℝ) (f : Euc d → ℝ) : Euc d → ℝ :=
  fun x => (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) (l • x)

/-- The dilation parameter `ℓ = √(β q / 2) = √(q'/2)` of the thermal data. -/
def mov_dil (β q : ℝ) : ℝ := Real.sqrt (β * q / 2)

/-- The semigroup `e^{-tS_0}` of the shifted oscillator `S_0` (thermal data `β, q`). -/
def mov_expS0 (β q t : ℝ) (f : Euc d → ℝ) : Euc d → ℝ :=
  mov2b_T (mov_dil β q) q t f

/-- The shifted oscillator `S_0 u = ν(-Δu + (q'/2)² |x|² u) - ν q' (d/2) u`, `ν = β⁻¹`, `q' = β q`. -/
def mov_S0 (d : ℕ) (β q : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  β⁻¹ * (-(Laplacian.laplacian u x) + (β * q / 2) ^ 2 * ‖x‖ ^ 2 * u x) -
    β⁻¹ * (β * q) * (d / 2) * u x

lemma mov_dil_pos {β q : ℝ} (hβ : 0 < β) (hq : 0 < q) : 0 < mov_dil β q :=
  Real.sqrt_pos.2 (by positivity)

lemma mov_dil_sq {β q : ℝ} (hβ : 0 < β) (hq : 0 < q) : mov_dil β q ^ 2 = β * q / 2 :=
  Real.sq_sqrt (by positivity)

lemma mov2b_c_pos (q t : ℝ) (α : MultiIndex d) : 0 < mov2b_c q t α := Real.exp_pos _

lemma mov2b_c_le_one {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (α : MultiIndex d) : mov2b_c q t α ≤ 1 := by
  unfold mov2b_c
  apply Real.exp_le_one_iff.2
  have : 0 ≤ t * q * (α.degree : ℝ) := by positivity
  linarith

lemma mov2b_c_bdd {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    ∃ K, ∀ α : MultiIndex d, |mov2b_c q t α| ≤ K :=
  ⟨1, fun α => by rw [abs_of_pos (mov2b_c_pos q t α)]; exact mov2b_c_le_one hq ht α⟩

lemma mov2b_c_add (q s t : ℝ) (α : MultiIndex d) : mov2b_c q s α * mov2b_c q t α = mov2b_c q (s + t) α := by
  unfold mov2b_c; rw [← Real.exp_add]; congr 1; ring

lemma mov2b_c_zero (q : ℝ) : (mov2b_c q 0 : MultiIndex d → ℝ) = fun _ => 1 := by
  funext α; simp [mov2b_c]

/-! ## Scaling lemmas -/

lemma mov2b_ae_comp_smul {P : Euc d → Prop} {l : ℝ} (hl : 0 < l)
    (h : ∀ᵐ y ∂(volume : Measure (Euc d)), P y) : ∀ᵐ x ∂(volume : Measure (Euc d)), P (l • x) := by
  have hmap : Measure.map (fun x : Euc d => l • x) (volume : Measure (Euc d)) =
      ENNReal.ofReal |(l ^ Module.finrank ℝ (Euc d))⁻¹| • (volume : Measure (Euc d)) :=
    Measure.map_addHaar_smul volume hl.ne'
  have h' : ∀ᵐ y ∂(Measure.map (fun x : Euc d => l • x) (volume : Measure (Euc d))), P y := by
    rw [hmap]; exact Measure.ae_smul_measure h _
  exact ae_of_ae_map (measurable_const_smul l).aemeasurable h'

/-- Dilated Hermite coefficient `⟨f, ℓ^{d/2} h_α(ℓ ·)⟩`. -/
def mov2b_dcoeff (l : ℝ) (f : Euc d → ℝ) (α : MultiIndex d) : ℝ :=
  ∫ x, f x * (Real.sqrt (l ^ d) * hermiteFunD α (l • x))

lemma mov2b_dcoeff_eq {l : ℝ} (hl : 0 < l) (f : Euc d → ℝ) (α : MultiIndex d) :
    mov2b_dcoeff l f α =
      Real.sqrt (l ^ d) * (l ^ d)⁻¹ * hermiteCoeff (fun y => f (l⁻¹ • y)) α := by
  unfold mov2b_dcoeff hermiteCoeff
  have h := Measure.integral_comp_smul (volume : Measure (Euc d))
    (fun y => f (l⁻¹ • y) * hermiteFunD α y) l
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  have e : (fun x => f x * (Real.sqrt (l ^ d) * hermiteFunD α (l • x))) =
      fun x => Real.sqrt (l ^ d) * (fun y => f (l⁻¹ • y) * hermiteFunD α y) (l • x) := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hl.ne']; ring
  rw [e, integral_const_mul, h, abs_of_nonneg (by positivity)]
  beta_reduce
  ring

/-! ## The bound, general form -/

lemma mov2b_dil_both (r : ℝ) {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, MemOsc r f →
      (MemOsc r (fun x => f (l • x)) ∧ oscNorm r (fun x => f (l • x)) ≤ C * oscNorm r f) ∧
      (MemOsc r (fun x => f (l⁻¹ • x)) ∧ oscNorm r (fun x => f (l⁻¹ • x)) ≤ C * oscNorm r f) := by
  have ha : 0 < min l l⁻¹ := lt_min hl (inv_pos.2 hl)
  obtain ⟨C, hC, h⟩ := mo_dilate (d := d) r ha (min_le_max (a := l) (b := l⁻¹))
  refine ⟨C, hC, fun f hf => ⟨h l (min_le_left _ _) (le_max_left _ _) f hf,
    h l⁻¹ (min_le_right _ _) (le_max_right _ _) f hf⟩⟩

theorem mov2b_T_bound_gen {l : ℝ} (hl : 0 < l) (q r b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t K : ℝ), 0 ≤ K →
      (∀ α : MultiIndex d, oscEigenvalue d α ^ (b / 2) * Real.exp (-(t * q * (α.degree : ℝ))) ≤ K) →
      ∀ f : Euc d → ℝ, MemOsc r f →
        MemOsc (r + b) (mov2b_T l q t f) ∧ oscNorm (r + b) (mov2b_T l q t f) ≤ C * K * oscNorm r f := by
  obtain ⟨C1, hC1, h1⟩ := mov2b_dil_both (d := d) r hl
  obtain ⟨C2, hC2, h2⟩ := mov2b_dil_both (d := d) (r + b) hl
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, fun t K hK hspec f hf => ?_⟩
  obtain ⟨hg, hgn⟩ := (h1 f hf).2
  have hcK : ∀ α : MultiIndex d, oscEigenvalue d α ^ (b / 2) * |mov2b_c q t α| ≤ K := fun α => by
    rw [abs_of_pos (mov2b_c_pos q t α)]; exact hspec α
  obtain ⟨hM, hMn⟩ := mov2b_mult_bound hg hb hK hcK
  obtain ⟨hD, hDn⟩ := (h2 _ hM).1
  refine ⟨hD, ?_⟩
  show oscNorm (r + b) (fun x => (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) (l • x)) ≤ _
  calc _ ≤ C2 * oscNorm (r + b) (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) := hDn
    _ ≤ C2 * (K * oscNorm r (fun y => f (l⁻¹ • y))) := mul_le_mul_of_nonneg_left hMn hC2
    _ ≤ C2 * (K * (C1 * oscNorm r f)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgn hK) hC2
    _ = C2 * C1 * K * oscNorm r f := by ring

/-- **Smoothing** `Σ^r → Σ^{r+b}`, `‖e^{-tS_0}‖ ≤ C_b t^{-b/2}` for `0 < t ≤ 1` (generic `l, q`). -/
theorem mov2b_T_smoothing {l : ℝ} (hl : 0 < l) {q : ℝ} (hq : 0 < q) (r b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ f : Euc d → ℝ, MemOsc r f →
      MemOsc (r + b) (mov2b_T l q t f) ∧
        oscNorm (r + b) (mov2b_T l q t f) ≤ C * t ^ (-(b / 2)) * oscNorm r f := by
  obtain ⟨C, hC, h⟩ := mov2b_T_bound_gen (d := d) hl q r b hb
  refine ⟨C * mov2b_K d q b, mul_nonneg hC (mov2b_K_nonneg d hq b), fun t ht ht1 f hf => ?_⟩
  have hK : 0 ≤ mov2b_K d q b * t ^ (-(b / 2)) :=
    mul_nonneg (mov2b_K_nonneg d hq b) (Real.rpow_nonneg ht.le _)
  obtain ⟨h1, h2⟩ := h t _ hK (fun α => mov2b_spec_bound hq ht ht1 hb α) f hf
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  ring

/-- Uniform bound on `Σ^r` for all `t ≥ 0`. -/
theorem mov2b_T_bounded {l : ℝ} (hl : 0 < l) {q : ℝ} (hq : 0 < q) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : Euc d → ℝ, MemOsc r f →
      MemOsc r (mov2b_T l q t f) ∧ oscNorm r (mov2b_T l q t f) ≤ C * oscNorm r f := by
  obtain ⟨C, hC, h⟩ := mov2b_T_bound_gen (d := d) hl q r 0 le_rfl
  refine ⟨C, hC, fun t ht f hf => ?_⟩
  obtain ⟨h1, h2⟩ := h t 1 zero_le_one (fun α => by
    rw [zero_div, Real.rpow_zero, one_mul]
    apply Real.exp_le_one_iff.2
    have : 0 ≤ t * q * (α.degree : ℝ) := by positivity
    linarith) f hf
  rw [add_zero] at h1 h2
  exact ⟨h1, by simpa using h2⟩

/-! ## Coefficients, semigroup law -/

lemma mov2b_memLp_inv {l : ℝ} (hl : 0 < l) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    MemLp (fun y => f (l⁻¹ • y)) 2 (volume : Measure (Euc d)) :=
  mova3c_comp_smul_memLp hf (inv_pos.2 hl)

lemma mov2b_T_inner {l : ℝ} (hl : 0 < l) (q t : ℝ) (f : Euc d → ℝ) :
    (fun y => mov2b_T l q t f (l⁻¹ • y)) =
      (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) := by
  funext y
  simp only [mov2b_T, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]

theorem mov2b_T_memLp {l : ℝ} (hl : 0 < l) (q t : ℝ) (f : Euc d → ℝ) :
    MemLp (mov2b_T l q t f) 2 (volume : Measure (Euc d)) :=
  mova3c_comp_smul_memLp (mov2b_mult_memLp _ _) hl

/-- The dilated Hermite coefficients of `e^{-tS_0} f` are `e^{-tq|α|}` times those of `f`. -/
theorem mov2b_T_dcoeff {l : ℝ} (hl : 0 < l) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    mov2b_dcoeff l (mov2b_T l q t f) α = mov2b_c q t α * mov2b_dcoeff l f α := by
  rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl, mov2b_T_inner hl,
    mov2b_mult_coeff (mov2b_memLp_inv hl hf) (mov2b_c_bdd hq ht) α]
  ring

/-- `L²` functions with the same Hermite coefficients agree a.e. -/
lemma mov2b_ae_eq_of_coeff {u v : Euc d → ℝ} (hu : MemLp u 2 (volume : Measure (Euc d)))
    (hv : MemLp v 2 (volume : Measure (Euc d)))
    (h : ∀ α, hermiteCoeff u α = hermiteCoeff v α) : u =ᵐ[volume] v := by
  have : hu.toLp u = hv.toLp v := by
    apply (mov2b_basis d).repr.injective
    ext α
    rw [← mov2b_coeff_eq_repr hu, ← mov2b_coeff_eq_repr hv, h α]
  exact hu.coeFn_toLp.symm.trans ((Lp.ext_iff.1 this).trans hv.coeFn_toLp)

/-- Uniqueness: an `L²` function whose dilated coefficients are `e^{-tq|α|}` times those of `f`
equals `e^{-tS_0} f` a.e.  (So `e^{-tS_0}` is exactly the coefficientwise multiplier on the dilated basis.) -/
theorem mov2b_T_unique {l : ℝ} (hl : 0 < l) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) {f u : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hu : MemLp u 2 (volume : Measure (Euc d)))
    (h : ∀ α, mov2b_dcoeff l u α = mov2b_c q t α * mov2b_dcoeff l f α) :
    u =ᵐ[volume] mov2b_T l q t f := by
  have hpre : 0 < Real.sqrt (l ^ d) * (l ^ d)⁻¹ := by positivity
  have hcoef : ∀ α, hermiteCoeff (fun y => u (l⁻¹ • y)) α =
      hermiteCoeff (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) α := by
    intro α
    have := h α
    rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl] at this
    rw [mov2b_mult_coeff (mov2b_memLp_inv hl hf) (mov2b_c_bdd hq ht) α]
    have h3 : (Real.sqrt (l ^ d) * (l ^ d)⁻¹) * hermiteCoeff (fun y => u (l⁻¹ • y)) α =
        (Real.sqrt (l ^ d) * (l ^ d)⁻¹) * (mov2b_c q t α * hermiteCoeff (fun y => f (l⁻¹ • y)) α) := by
      rw [this]; ring
    exact mul_left_cancel₀ hpre.ne' h3
  have hae := mov2b_ae_eq_of_coeff (mov2b_memLp_inv hl hu) (mov2b_mult_memLp _ _) hcoef
  have := mov2b_ae_comp_smul hl hae
  filter_upwards [this] with x hx
  simp only [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hx
  exact hx

/-- Semigroup law (exact equality of functions). -/
theorem mov2b_T_add {l : ℝ} (hl : 0 < l) {q s t : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    mov2b_T l q s (mov2b_T l q t f) = mov2b_T l q (s + t) f := by
  have h1 : (fun y => mov2b_T l q t f (l⁻¹ • y)) =
      (⇑(mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) := mov2b_T_inner hl q t f
  funext x
  change (⇑(mov2b_mult (mov2b_c q s) (fun y => mov2b_T l q t f (l⁻¹ • y))) : Euc d → ℝ) (l • x) =
    (⇑(mov2b_mult (mov2b_c q (s + t)) (fun y => f (l⁻¹ • y))) : Euc d → ℝ) (l • x)
  rw [h1, mov2b_mult_mult (mov2b_memLp_inv hl hf) (mov2b_c_bdd hq hs) (mov2b_c_bdd hq ht)]
  have : (fun α : MultiIndex d => mov2b_c q s α * mov2b_c q t α) = mov2b_c q (s + t) :=
    funext fun α => mov2b_c_add q s t α
  rw [this]

theorem mov2b_T_zero {l : ℝ} (hl : 0 < l) (q : ℝ) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) : mov2b_T l q 0 f =ᵐ[volume] f := by
  have h1 := mov2b_mult_one_ae (mov2b_memLp_inv hl hf)
  rw [← mov2b_c_zero q] at h1
  have := mov2b_ae_comp_smul hl h1
  filter_upwards [this] with x hx
  simp only [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hx
  exact hx

/-! ## Strong continuity -/

lemma mov2b_T_sub_ae {l : ℝ} (hl : 0 < l) {q s t : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    (fun x => mov2b_T l q s f x - mov2b_T l q t f x) =ᵐ[volume]
      fun x => (⇑(mov2b_mult (fun α => mov2b_c q s α - mov2b_c q t α)
        (fun y => f (l⁻¹ • y))) : Euc d → ℝ) (l • x) := by
  have hg := mov2b_memLp_inv hl hf
  have h1 := mov2b_mult_sub hg (mov2b_c_bdd hq hs) (mov2b_c_bdd hq ht)
  have h2 := Lp.coeFn_sub (mov2b_mult (mov2b_c q s) (fun y => f (l⁻¹ • y)))
    (mov2b_mult (mov2b_c q t) (fun y => f (l⁻¹ • y)))
  rw [h1] at h2
  have := mov2b_ae_comp_smul hl h2
  filter_upwards [this] with x hx
  rw [hx]
  rfl

theorem mov2b_T_continuous {l : ℝ} (hl : 0 < l) {q : ℝ} (hq : 0 < q) {r : ℝ} {f : Euc d → ℝ}
    (hf : MemOsc r f) {t0 : ℝ} (ht0 : 0 ≤ t0) :
    (∀ t : ℝ, 0 ≤ t → MemOsc r (fun x => mov2b_T l q t f x - mov2b_T l q t0 f x)) ∧
      Tendsto (fun t : ℝ => oscNorm r (fun x => mov2b_T l q t f x - mov2b_T l q t0 f x))
        (𝓝[Set.Ici 0] t0) (𝓝 0) := by
  obtain ⟨C1, hC1, h1⟩ := mov2b_dil_both (d := d) r hl
  have hg : MemOsc r (fun y => f (l⁻¹ • y)) := ((h1 f hf).2).1
  set g : Euc d → ℝ := fun y => f (l⁻¹ • y) with hgdef
  set e : ℝ → MultiIndex d → ℝ := fun t α => mov2b_c q t α - mov2b_c q t0 α with hedef
  have he1 : ∀ t, 0 ≤ t → ∀ α, |e t α| ≤ 1 := by
    intro t ht α
    have a1 := mov2b_c_pos q t α
    have a2 := mov2b_c_pos q t0 α
    have b1 := mov2b_c_le_one hq.le ht α
    have b2 := mov2b_c_le_one hq.le ht0 α
    rw [abs_le]; constructor <;> simp only [hedef] <;> linarith
  have hebd : ∀ t, 0 ≤ t → ∃ K, ∀ α : MultiIndex d, |e t α| ≤ K := fun t ht => ⟨1, he1 t ht⟩
  have hsum : ∀ t, 0 ≤ t → Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2 := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _)
      (sq_nonneg _)) (fun α => ?_) hg.2
    rw [mul_pow, ← mul_assoc, mul_comm (oscEigenvalue d α ^ r), mul_assoc]
    have : (e t α) ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (he1 t ht α)
    have h0 : 0 ≤ oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
    nlinarith
  have hnorm : ∀ t, 0 ≤ t → MemOsc r (⇑(mov2b_mult (e t) g) : Euc d → ℝ) ∧
      oscNorm r (⇑(mov2b_mult (e t) g) : Euc d → ℝ) =
        Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2) :=
    fun t ht => mov2b_mult_norm hg.1 (hebd t ht) (hsum t ht)
  have hdil : ∀ t, 0 ≤ t → MemOsc r (fun x => (⇑(mov2b_mult (e t) g) : Euc d → ℝ) (l • x)) ∧
      oscNorm r (fun x => (⇑(mov2b_mult (e t) g) : Euc d → ℝ) (l • x)) ≤
        C1 * oscNorm r (⇑(mov2b_mult (e t) g) : Euc d → ℝ) :=
    fun t ht => ((h1 _ (hnorm t ht).1).1)
  have hae : ∀ t, 0 ≤ t → (fun x => mov2b_T l q t f x - mov2b_T l q t0 f x) =ᵐ[volume]
      fun x => (⇑(mov2b_mult (e t) g) : Euc d → ℝ) (l • x) :=
    fun t ht => mov2b_T_sub_ae hl hq.le ht ht0 hf.1
  refine ⟨fun t ht => mov2b_memOsc_congr (hae t ht).symm r (hdil t ht).1, ?_⟩
  -- the limit of the series
  have hlim : Tendsto (fun t : ℝ => ∑' α : MultiIndex d,
      oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2) (𝓝[Set.Ici 0] t0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Set.Ici 0] t0)
      (f := fun (t : ℝ) (α : MultiIndex d) => oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun α => oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2) hg.2
      (fun α => by
        have hc : Continuous fun t : ℝ => oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2 := by
          simp only [hedef, mov2b_c]
          fun_prop
        have := (hc.tendsto t0).mono_left (nhdsWithin_le_nhds (s := Set.Ici 0))
        simpa [hedef] using this)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht k
        have ht' : 0 ≤ t := ht
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (oscEv_pos k).le _) (sq_nonneg _))]
        rw [mul_pow, ← mul_assoc, mul_comm (oscEigenvalue d k ^ r), mul_assoc]
        have : (e t k) ^ 2 ≤ 1 := by
          rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (he1 t ht' k)
        have h0 : 0 ≤ oscEigenvalue d k ^ r * hermiteCoeff g k ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (oscEv_pos k).le _) (sq_nonneg _)
        nlinarith)
    simpa using this
  have hsq : Tendsto (fun t : ℝ => C1 * Real.sqrt (∑' α : MultiIndex d,
      oscEigenvalue d α ^ r * (e t α * hermiteCoeff g α) ^ 2)) (𝓝[Set.Ici 0] t0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    have := this.const_mul C1
    simpa using this
  refine squeeze_zero' ?_ ?_ hsq
  · exact Eventually.of_forall fun t => by unfold oscNorm; exact Real.sqrt_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 ≤ t := ht
    rw [mov2b_oscNorm_congr (hae t ht') r]
    refine (hdil t ht').2.trans ?_
    rw [(hnorm t ht').2]

/-! ## Action on the dilated Hermite span -/

lemma mov2b_hermiteCoeff_finsum (F : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) (α : MultiIndex d) :
    hermiteCoeff (fun y : Euc d => ∑ β ∈ F, a β * hermiteFunD β y) α = if α ∈ F then a α else 0 := by
  unfold hermiteCoeff
  have h1 : (fun x : Euc d => (∑ β ∈ F, a β * hermiteFunD β x) * hermiteFunD α x) =
      fun x => ∑ β ∈ F, a β * (hermiteFunD β x * hermiteFunD α x) := by
    funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun β _ => by ring
  rw [h1, integral_finset_sum _ (fun β _ => (integrable_hermiteFunD_mul β α).const_mul (a β))]
  simp_rw [integral_const_mul, hermiteFunD_orthonormal]
  simp [Finset.sum_ite_eq']

lemma mov2b_memLp_span {l : ℝ} (hl : 0 < l) (F : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    MemLp (fun x : Euc d => ∑ β ∈ F, a β * hermiteFunD β (l • x)) 2 (volume : Measure (Euc d)) :=
  memLp_finsetSum (f := fun β x => a β * hermiteFunD β (l • x)) F (fun β _ =>
    (mova3c_comp_smul_memLp (memLp_hermiteFunD β) hl).const_mul (a β))

lemma mov2b_dcoeff_span {l : ℝ} (hl : 0 < l) (F : Finset (MultiIndex d)) (a : MultiIndex d → ℝ)
    (α : MultiIndex d) :
    mov2b_dcoeff l (fun x : Euc d => ∑ β ∈ F, a β * hermiteFunD β (l • x)) α =
      Real.sqrt (l ^ d) * (l ^ d)⁻¹ * (if α ∈ F then a α else 0) := by
  rw [mov2b_dcoeff_eq hl, ← mov2b_hermiteCoeff_finsum F a α]
  congr 2
  funext y
  simp only [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]

/-- **Action on the Hermite span.**  `e^{-tS_0}` multiplies the coefficient of `h_α(ℓ ·)` by `e^{-tq|α|}`
(equality a.e.; a finite combination of dilated Hermite functions is mapped to the same combination). -/
theorem mov2b_T_span {l : ℝ} (hl : 0 < l) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t)
    (F : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    mov2b_T l q t (fun x : Euc d => ∑ β ∈ F, a β * hermiteFunD β (l • x)) =ᵐ[volume]
      fun x => ∑ β ∈ F, (mov2b_c q t β * a β) * hermiteFunD β (l • x) := by
  symm
  refine mov2b_T_unique hl hq ht (mov2b_memLp_span hl F a) (mov2b_memLp_span hl F _) fun α => ?_
  rw [mov2b_dcoeff_span hl, mov2b_dcoeff_span hl]
  by_cases h : α ∈ F <;> simp [h] <;> ring

/-! ## Diagonalisation of `S_0` on the dilated Hermite functions -/

lemma mov2b_laplacian_comp_smul {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (l : ℝ) (x : Euc d) :
    Laplacian.laplacian (fun y => u (l • y)) x = l ^ 2 * Laplacian.laplacian u (l • x) := by
  set g : Euc d →L[ℝ] Euc d := l • ContinuousLinearMap.id ℝ (Euc d) with hgdef
  have hg : (fun y => u (l • y)) = u ∘ g := by funext y; simp [g]
  rw [hg]
  have h1 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (u ∘ g)) x
  have h2 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis u) (g x)
  rw [h1, show g x = l • x by simp [g]] at *
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right g hu x (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have e : (fun j : Fin 2 => g (![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] j)) =
      fun j => l • (![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] j) := by
    funext j; simp [g]
  rw [e, ContinuousMultilinearMap.map_smul_univ]
  simp [pow_two]
  left
  rw [show g x = l • x by simp [g]]

/-- **Diagonalisation.**  With `ℓ = √(βq/2)`: `S_0 (h_α(ℓ ·)) = q |α| h_α(ℓ ·)` pointwise. -/
theorem mov_S0_hermite_dil {β q : ℝ} (hβ : 0 < β) (hq : 0 < q) (α : MultiIndex d) (x : Euc d) :
    mov_S0 d β q (fun y => hermiteFunD α (mov_dil β q • y)) x =
      q * (α.degree : ℝ) * hermiteFunD α (mov_dil β q • x) := by
  set l := mov_dil β q with hl
  have hl2 : l ^ 2 = β * q / 2 := mov_dil_sq hβ hq
  have hc : ContDiff ℝ 2 (hermiteFunD (d := d) α) := (contDiff_hermiteFunD α).of_le (by simp)
  unfold mov_S0
  rw [mov2b_laplacian_comp_smul hc l x]
  have hosc := oscillatorOp_hermiteFunD α (l • x)
  unfold oscillatorOp oscEigenvalue at hosc
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hl2] at hosc
  have hlap : Laplacian.laplacian (hermiteFunD α) (l • x) =
      hermiteFunD α (l • x) + β * q / 2 * ‖x‖ ^ 2 * hermiteFunD α (l • x) -
        (2 * (α.degree : ℝ) + d + 1) * hermiteFunD α (l • x) := by
    linarith
  rw [hlap, hl2]
  field_simp
  ring

/-! ## The thermal-data statements -/

section Thermal

variable {β q : ℝ}

/-- **Smoothing of `e^{-tS_0}`** (S6.2, TeX L4338-4339): for real `r` and real `b ≥ 0` there is `C = C(d,β,q,r,b)`
such that for `0 < t ≤ 1`, `f ∈ Σ^r`: `e^{-tS_0} f ∈ Σ^{r+b}` and
`‖e^{-tS_0} f‖_{Σ^{r+b}} ≤ C t^{-b/2} ‖f‖_{Σ^r}`. -/
theorem mov_expS0_bound (hβ : 0 < β) (hq : 0 < q) (r b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ f : Euc d → ℝ, MemOsc r f →
      MemOsc (r + b) (mov_expS0 β q t f) ∧
        oscNorm (r + b) (mov_expS0 β q t f) ≤ C * t ^ (-(b / 2)) * oscNorm r f :=
  mov2b_T_smoothing (mov_dil_pos hβ hq) hq r b hb

/-- Uniform boundedness on `Σ^r` for all `t ≥ 0`. -/
theorem mov_expS0_bounded (hβ : 0 < β) (hq : 0 < q) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : Euc d → ℝ, MemOsc r f →
      MemOsc r (mov_expS0 β q t f) ∧ oscNorm r (mov_expS0 β q t f) ≤ C * oscNorm r f :=
  mov2b_T_bounded (mov_dil_pos hβ hq) hq r

/-- Strong continuity on `Σ^r` for `t ≥ 0` (the differences are in `Σ^r`, so the norm is not a junk value). -/
theorem mov_expS0_continuous (hβ : 0 < β) (hq : 0 < q) {r : ℝ} {f : Euc d → ℝ} (hf : MemOsc r f)
    {t0 : ℝ} (ht0 : 0 ≤ t0) :
    (∀ t : ℝ, 0 ≤ t → MemOsc r (fun x => mov_expS0 β q t f x - mov_expS0 β q t0 f x)) ∧
      Tendsto (fun t : ℝ => oscNorm r (fun x => mov_expS0 β q t f x - mov_expS0 β q t0 f x))
        (𝓝[Set.Ici 0] t0) (𝓝 0) :=
  mov2b_T_continuous (mov_dil_pos hβ hq) hq hf ht0

/-- `e^{-0·S_0} f = f` (a.e.) for `f ∈ L²`. -/
theorem mov_expS0_zero (hβ : 0 < β) (hq : 0 < q) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) : mov_expS0 β q 0 f =ᵐ[volume] f :=
  mov2b_T_zero (mov_dil_pos hβ hq) q hf

/-- Semigroup law `e^{-sS_0} e^{-tS_0} f = e^{-(s+t)S_0} f` (equality of functions), `f ∈ L²`, `s, t ≥ 0`. -/
theorem mov_expS0_add (hβ : 0 < β) (hq : 0 < q) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) :
    mov_expS0 β q s (mov_expS0 β q t f) = mov_expS0 β q (s + t) f :=
  mov2b_T_add (mov_dil_pos hβ hq) hq.le hs ht hf

/-- `e^{-tS_0} f ∈ L²` for `f ∈ L²`. -/
theorem mov_expS0_memLp (hβ : 0 < β) (hq : 0 < q) (t : ℝ) (f : Euc d → ℝ) :
    MemLp (mov_expS0 β q t f) 2 (volume : Measure (Euc d)) :=
  mov2b_T_memLp (mov_dil_pos hβ hq) q t f

/-- **Coefficientwise multiplier.**  In the dilated Hermite basis `ℓ^{d/2} h_α(ℓ ·)`, `ℓ = √(βq/2)`,
`e^{-tS_0}` multiplies the `α`-th coefficient by `e^{-tq|α|}`. -/
theorem mov_expS0_dcoeff (hβ : 0 < β) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    mov2b_dcoeff (mov_dil β q) (mov_expS0 β q t f) α =
      Real.exp (-(t * q * (α.degree : ℝ))) * mov2b_dcoeff (mov_dil β q) f α :=
  mov2b_T_dcoeff (mov_dil_pos hβ hq) hq.le ht hf α

/-- Uniqueness: `e^{-tS_0} f` is the (a.e. unique) `L²` function with these dilated coefficients. -/
theorem mov_expS0_unique (hβ : 0 < β) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) {f u : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hu : MemLp u 2 (volume : Measure (Euc d)))
    (h : ∀ α, mov2b_dcoeff (mov_dil β q) u α =
      Real.exp (-(t * q * (α.degree : ℝ))) * mov2b_dcoeff (mov_dil β q) f α) :
    u =ᵐ[volume] mov_expS0 β q t f :=
  mov2b_T_unique (mov_dil_pos hβ hq) hq.le ht hf hu h

/-- **Action on the Hermite span.**  For a finite combination of the dilated Hermite functions
`h_α(ℓ ·)`: `e^{-tS_0} ∑ a_α h_α(ℓ ·) = ∑ e^{-tq|α|} a_α h_α(ℓ ·)` a.e.; in particular
`e^{-tS_0} h_α(ℓ ·) = e^{-tq|α|} h_α(ℓ ·)` a.e. (compare `mov_S0_hermite_dil`: `S_0 h_α(ℓ ·) = q|α| h_α(ℓ ·)`). -/
theorem mov_expS0_span (hβ : 0 < β) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) (F : Finset (MultiIndex d))
    (a : MultiIndex d → ℝ) :
    mov_expS0 β q t (fun x : Euc d => ∑ γ ∈ F, a γ * hermiteFunD γ (mov_dil β q • x)) =ᵐ[volume]
      fun x => ∑ γ ∈ F, (Real.exp (-(t * q * (γ.degree : ℝ))) * a γ) *
        hermiteFunD γ (mov_dil β q • x) :=
  mov2b_T_span (mov_dil_pos hβ hq) hq.le ht F a

end Thermal

end HRS.MS.MovLin
