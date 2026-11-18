import Mathlib

/-!
# Packet PI-E, part 1: operator interpolation (Hadamard three lines) and duality for weighted matrices

Pure matrix statements (no project dependencies).  For a real matrix `T` over an index type with positive weights `w`,
`pieFinBd (pieWmat w T σ) A` says that the conjugated matrix `w^σ T w^{-σ}` has finite-section `ℓ²` operator norm
`≤ A`.  `pie_interp`: the bound at two exponents interpolates (complex interpolation, Mathlib's three lines
theorem).  `pie_dual`: the transposed action on sequences `a ↦ (∑'_j a_j T_{jk})_k` obeys the same bound for the dual
weights `w^{-σ}`.
-/

open Finset Complex

noncomputable section

namespace HRS.MC.Sec7.PIE

variable {ι : Type*}

/-- finite-section operator bound for a real matrix -/
def pieFinBd (S : ι → ι → ℝ) (A : ℝ) : Prop :=
  ∀ (K J : Finset ι) (x : ι → ℝ),
    ∑ j ∈ J, (∑ k ∈ K, S j k * x k) ^ 2 ≤ A ^ 2 * ∑ k ∈ K, x k ^ 2

/-- the matrix `w^σ T w^{-σ}` -/
def pieWmat (w : ι → ℝ) (T : ι → ι → ℝ) (σ : ℝ) : ι → ι → ℝ :=
  fun j k => w j ^ σ * T j k * w k ^ (-σ)

lemma pie_finBd_complex {S : ι → ι → ℝ} {A : ℝ} (h : pieFinBd S A) (K J : Finset ι) (X : ι → ℂ) :
    ∑ j ∈ J, ‖∑ k ∈ K, (S j k : ℂ) * X k‖ ^ 2 ≤ A ^ 2 * ∑ k ∈ K, ‖X k‖ ^ 2 := by
  have h1 := h K J (fun k => (X k).re)
  have h2 := h K J (fun k => (X k).im)
  have e : ∀ j, ‖∑ k ∈ K, (S j k : ℂ) * X k‖ ^ 2 =
      (∑ k ∈ K, S j k * (X k).re) ^ 2 + (∑ k ∈ K, S j k * (X k).im) ^ 2 := by
    intro j
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.re_sum, Complex.im_sum, sq]
  have e2 : ∀ k, ‖X k‖ ^ 2 = (X k).re ^ 2 + (X k).im ^ 2 := by
    intro k
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp_rw [e, e2, Finset.sum_add_distrib, mul_add]
  exact add_le_add h1 h2

/-- `w_j^σ w_k^{-σ} = exp(σ (log w_j - log w_k))` -/
lemma pie_rpow_ratio {w : ι → ℝ} (hw : ∀ i, 0 < w i) (σ : ℝ) (j k : ι) :
    w j ^ σ * w k ^ (-σ) = Real.exp (σ * (Real.log (w j) - Real.log (w k))) := by
  rw [Real.rpow_def_of_pos (hw j), Real.rpow_def_of_pos (hw k), ← Real.exp_add]
  congr 1; ring

/-- a phase-twisted bound along a vertical line -/
lemma pie_phase_bound {w : ι → ℝ} (hw : ∀ i, 0 < w i) {T : ι → ι → ℝ} {c A : ℝ} (hA : 0 ≤ A)
    (hc : pieFinBd (pieWmat w T c) A) (K J : Finset ι) (x y : ι → ℝ) (τ : ℝ) :
    ‖∑ j ∈ J, ∑ k ∈ K, ((y j * T j k * x k : ℝ) : ℂ) *
        cexp (((c : ℂ) + (τ : ℂ) * Complex.I) * ((Real.log (w j) - Real.log (w k) : ℝ) : ℂ))‖ ≤
      A * Real.sqrt (∑ j ∈ J, y j ^ 2) * Real.sqrt (∑ k ∈ K, x k ^ 2) := by
  set L : ι → ℝ := fun i => Real.log (w i) with hL
  set Y : ι → ℂ := fun j => (y j : ℂ) * cexp ((τ : ℂ) * Complex.I * (L j : ℂ)) with hY
  set X : ι → ℂ := fun k => (x k : ℂ) * cexp (-((τ : ℂ) * Complex.I * (L k : ℂ))) with hX
  have hterm : ∀ j k, ((y j * T j k * x k : ℝ) : ℂ) *
        cexp (((c : ℂ) + (τ : ℂ) * Complex.I) * ((L j - L k : ℝ) : ℂ)) =
      Y j * ((pieWmat w T c j k : ℝ) : ℂ) * X k := by
    intro j k
    have h1 : ((pieWmat w T c j k : ℝ) : ℂ) = (T j k : ℂ) * cexp ((c : ℂ) * ((L j - L k : ℝ) : ℂ)) := by
      unfold pieWmat
      have := pie_rpow_ratio hw c j k
      have h2 : ((w j ^ c * T j k * w k ^ (-c) : ℝ) : ℂ) =
          (T j k : ℂ) * ((w j ^ c * w k ^ (-c) : ℝ) : ℂ) := by push_cast; ring
      rw [h2, this, Complex.ofReal_exp]
      congr 2
      push_cast; ring
    rw [h1]
    simp only [hY, hX]
    rw [show ((c : ℂ) + (τ : ℂ) * Complex.I) * ((L j - L k : ℝ) : ℂ) =
        (c : ℂ) * ((L j - L k : ℝ) : ℂ) + (τ * Complex.I * (L j : ℂ)) + (-(τ * Complex.I * (L k : ℂ))) by
      push_cast; ring, Complex.exp_add, Complex.exp_add]
    push_cast
    ring
  have hsum : ∑ j ∈ J, ∑ k ∈ K, ((y j * T j k * x k : ℝ) : ℂ) *
        cexp (((c : ℂ) + (τ : ℂ) * Complex.I) * ((L j - L k : ℝ) : ℂ)) =
      ∑ j ∈ J, Y j * ∑ k ∈ K, ((pieWmat w T c j k : ℝ) : ℂ) * X k := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm]; ring
  rw [hsum]
  have hnY : ∀ j, ‖Y j‖ = |y j| := by
    intro j
    simp only [hY, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (τ : ℂ) * Complex.I * (L j : ℂ) = ((τ * L j : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnX : ∀ k, ‖X k‖ = |x k| := by
    intro k
    simp only [hX, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show -((τ : ℂ) * Complex.I * (L k : ℂ)) = ((-(τ * L k) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  set G : ι → ℂ := fun j => ∑ k ∈ K, ((pieWmat w T c j k : ℝ) : ℂ) * X k with hG
  calc ‖∑ j ∈ J, Y j * G j‖ ≤ ∑ j ∈ J, ‖Y j‖ * ‖G j‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
    _ ≤ Real.sqrt (∑ j ∈ J, ‖Y j‖ ^ 2) * Real.sqrt (∑ j ∈ J, ‖G j‖ ^ 2) := by
        rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
        refine Real.le_sqrt_of_sq_le ?_
        exact Finset.sum_mul_sq_le_sq_mul_sq J (fun j => ‖Y j‖) (fun j => ‖G j‖)
    _ ≤ Real.sqrt (∑ j ∈ J, y j ^ 2) * (A * Real.sqrt (∑ k ∈ K, x k ^ 2)) := by
        have h1 : ∑ j ∈ J, ‖Y j‖ ^ 2 = ∑ j ∈ J, y j ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hnY, sq_abs]
        have h2 : ∑ j ∈ J, ‖G j‖ ^ 2 ≤ A ^ 2 * ∑ k ∈ K, x k ^ 2 := by
          have := pie_finBd_complex hc K J X
          have h3 : ∑ k ∈ K, ‖X k‖ ^ 2 = ∑ k ∈ K, x k ^ 2 :=
            Finset.sum_congr rfl fun k _ => by rw [hnX, sq_abs]
          rw [h3] at this
          exact this
        rw [h1]
        gcongr
        calc Real.sqrt (∑ j ∈ J, ‖G j‖ ^ 2) ≤ Real.sqrt (A ^ 2 * ∑ k ∈ K, x k ^ 2) :=
              Real.sqrt_le_sqrt h2
          _ = A * Real.sqrt (∑ k ∈ K, x k ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA]
    _ = _ := by ring

lemma pie_exp_decomp (a b : ℝ) (z : ℂ) :
    (a : ℂ) + z * ((b - a : ℝ) : ℂ) =
      ((a + z.re * (b - a) : ℝ) : ℂ) + ((z.im * (b - a) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- complex interpolation of the finite-section bounds -/
theorem pie_interp {w : ι → ℝ} (hw : ∀ i, 0 < w i) {T : ι → ι → ℝ} {a b A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (ha : pieFinBd (pieWmat w T a) A) (hb : pieFinBd (pieWmat w T b) B) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    pieFinBd (pieWmat w T ((1 - θ) * a + θ * b)) (A ^ (1 - θ) * B ^ θ) := by
  classical
  intro K J x
  set σ := (1 - θ) * a + θ * b with hσ
  set L : ι → ℝ := fun i => Real.log (w i) with hL
  set y : ι → ℝ := fun j => ∑ k ∈ K, pieWmat w T σ j k * x k with hy
  set f : ℂ → ℂ := fun z => ∑ j ∈ J, ∑ k ∈ K, ((y j * T j k * x k : ℝ) : ℂ) *
      cexp (((a : ℂ) + z * ((b - a : ℝ) : ℂ)) * ((L j - L k : ℝ) : ℂ)) with hf
  set c0 : ℝ := Real.sqrt (∑ j ∈ J, y j ^ 2) * Real.sqrt (∑ k ∈ K, x k ^ 2) with hc0
  have hc0nn : 0 ≤ c0 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- boundary bounds
  have hline : ∀ (s : ℝ) (Aₛ : ℝ), 0 ≤ Aₛ → pieFinBd (pieWmat w T (a + s * (b - a))) Aₛ →
      ∀ z : ℂ, z.re = s → ‖f z‖ ≤ Aₛ * c0 := by
    intro s Aₛ hAₛ hs z hz
    have := pie_phase_bound hw hAₛ hs K J x y (z.im * (b - a))
    simp only [hf]
    rw [pie_exp_decomp a b z, hz]
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    rw [hc0]; ring
  have hl0 : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ A * c0 := by
    refine hline 0 A hA ?_
    simpa using ha
  have hl1 : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ B * c0 := by
    refine hline 1 B hB ?_
    simpa using hb
  -- differentiability
  have hdiff : Differentiable ℂ f := by
    simp only [hf]
    fun_prop
  -- boundedness on the closed strip
  have hbdd : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ j ∈ J, ∑ k ∈ K, |y j * T j k * x k| *
      Real.exp ((|a| + |b - a|) * (|L j| + |L k|)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
    simp only [Function.comp, hf]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    gcongr
    have : (((a : ℂ) + z * ((b - a : ℝ) : ℂ)) * ((L j - L k : ℝ) : ℂ)).re =
        (a + z.re * (b - a)) * (L j - L k) := by simp
    rw [this]
    calc (a + z.re * (b - a)) * (L j - L k) ≤ |(a + z.re * (b - a)) * (L j - L k)| := le_abs_self _
      _ = |a + z.re * (b - a)| * |L j - L k| := abs_mul _ _
      _ ≤ (|a| + |b - a|) * (|L j| + |L k|) := by
          gcongr
          · calc |a + z.re * (b - a)| ≤ |a| + |z.re * (b - a)| := abs_add_le _ _
              _ ≤ |a| + |b - a| := by
                  rw [abs_mul, abs_of_nonneg hz'.1]
                  have := abs_nonneg (b - a)
                  nlinarith [hz'.2]
          · calc |L j - L k| ≤ |L j| + |-L k| := by rw [sub_eq_add_neg]; exact abs_add_le _ _
              _ = |L j| + |L k| := by rw [abs_neg]
  have hθmem : ((θ : ℝ) : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    show (0 : ℝ) ≤ ((θ : ℝ) : ℂ).re ∧ ((θ : ℝ) : ℂ).re ≤ 1
    simpa using ⟨h0, h1⟩
  have hmain := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f hθmem
    (hdiff.diffContOnCl) hbdd hl0 hl1
  have hre : ((θ : ℝ) : ℂ).re = θ := by simp
  rw [hre] at hmain
  -- value at θ
  have hfθ : f (θ : ℂ) = ((∑ j ∈ J, y j ^ 2 : ℝ) : ℂ) := by
    simp only [hf]
    have hexp : ∀ j k, cexp (((a : ℂ) + (θ : ℂ) * ((b - a : ℝ) : ℂ)) * ((L j - L k : ℝ) : ℂ)) =
        ((w j ^ σ * w k ^ (-σ) : ℝ) : ℂ) := by
      intro j k
      rw [pie_rpow_ratio hw σ j k, Complex.ofReal_exp]
      congr 1
      simp only [hσ]
      push_cast
      ring
    simp_rw [hexp]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq, hy]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold pieWmat
    push_cast
    ring
  have hS2 : ∑ j ∈ J, y j ^ 2 ≤ A ^ (1 - θ) * B ^ θ * c0 := by
    have h2 : ‖f (θ : ℂ)‖ = ∑ j ∈ J, y j ^ 2 := by
      rw [hfθ, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [← h2]
    refine hmain.trans (le_of_eq ?_)
    rw [Real.mul_rpow hA hc0nn, Real.mul_rpow hB hc0nn]
    have hc : c0 ^ (1 - θ) * c0 ^ θ = c0 := by
      rw [← Real.rpow_add' hc0nn (by norm_num)]; simp
    calc A ^ (1 - θ) * c0 ^ (1 - θ) * (B ^ θ * c0 ^ θ) =
        A ^ (1 - θ) * B ^ θ * (c0 ^ (1 - θ) * c0 ^ θ) := by ring
      _ = _ := by rw [hc]
  -- conclude
  set D : ℝ := A ^ (1 - θ) * B ^ θ with hD
  have hDnn : 0 ≤ D := mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)
  set S2 : ℝ := ∑ j ∈ J, y j ^ 2 with hS2def
  set X : ℝ := ∑ k ∈ K, x k ^ 2 with hX
  have hS2nn : 0 ≤ S2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun k _ => sq_nonneg _
  show S2 ≤ D ^ 2 * X
  have hsq : Real.sqrt S2 ^ 2 = S2 := Real.sq_sqrt hS2nn
  have hsqX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hXnn
  rcases (Real.sqrt_nonneg S2).eq_or_lt with h | h
  · have : S2 = 0 := by rw [← hsq, ← h]; ring
    rw [this]; positivity
  · have : Real.sqrt S2 ≤ D * Real.sqrt X := by
      have h3 : S2 ≤ D * (Real.sqrt S2 * Real.sqrt X) := hS2
      rw [← hsq] at h3
      nlinarith
    calc S2 = Real.sqrt S2 ^ 2 := hsq.symm
      _ ≤ (D * Real.sqrt X) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
      _ = D ^ 2 * X := by rw [mul_pow, hsqX]

/-- `ℓ²` bounds from finite-section bounds: summability of the squares of a column / of a row combination -/
lemma pie_col_summable {S : ι → ι → ℝ} {A : ℝ} (hS : pieFinBd S A) (k : ι) :
    Summable fun j => S j k ^ 2 := by
  refine summable_of_sum_le (c := A ^ 2) (fun j => sq_nonneg _) fun J => ?_
  have := hS {k} J (fun _ => 1)
  simpa using this

/-- Duality for the transposed action: the bound `pieFinBd (w^σ T w^{-σ}) A` yields
`‖(w^{-σ} ∑'_j a_j T_{jk})_k‖_{ℓ²} ≤ A ‖(w^{-σ} a_j)_j‖_{ℓ²}`. -/
theorem pie_dual {w : ι → ℝ} (hw : ∀ i, 0 < w i) {T : ι → ι → ℝ} {σ A : ℝ} (hA : 0 ≤ A)
    (hH : pieFinBd (pieWmat w T σ) A) (a : ι → ℝ) (ha : Summable fun j => (w j ^ (-σ) * a j) ^ 2) :
    Summable (fun k => (w k ^ (-σ) * ∑' j, a j * T j k) ^ 2) ∧
      ∑' k, (w k ^ (-σ) * ∑' j, a j * T j k) ^ 2 ≤ A ^ 2 * ∑' j, (w j ^ (-σ) * a j) ^ 2 := by
  classical
  set S := pieWmat w T σ with hSdef
  set c : ι → ℝ := fun j => w j ^ (-σ) * a j with hc
  set C : ℝ := ∑' j, c j ^ 2 with hCdef
  have hCnn : 0 ≤ C := tsum_nonneg fun j => sq_nonneg _
  have hcS : ∀ j k, c j * S j k = w k ^ (-σ) * (a j * T j k) := by
    intro j k
    simp only [hc, hSdef, pieWmat]
    have : w j ^ (-σ) * w j ^ σ = 1 := by
      rw [← Real.rpow_add (hw j)]; simp
    calc w j ^ (-σ) * a j * (w j ^ σ * T j k * w k ^ (-σ))
        = (w j ^ (-σ) * w j ^ σ) * (a j * T j k * w k ^ (-σ)) := by ring
      _ = _ := by rw [this]; ring
  -- the columns of S are square summable, hence `c_j S_jk` is summable
  have hcolsum : ∀ k, Summable fun j => c j * S j k := by
    intro k
    refine Summable.of_norm_bounded (g := fun j => (c j ^ 2 + S j k ^ 2) / 2)
      (((ha.add (pie_col_summable hH k))).div_const 2) fun j => ?_
    rw [Real.norm_eq_abs]
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (c j - S j k), sq_nonneg (c j + S j k)]
  set v : ι → ℝ := fun k => w k ^ (-σ) * ∑' j, a j * T j k with hv
  have hvS : ∀ k, v k = ∑' j, c j * S j k := by
    intro k
    simp only [hv]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => (hcS j k).symm
  -- main finite estimate
  have hfin : ∀ K : Finset ι, ∑ k ∈ K, v k ^ 2 ≤ A ^ 2 * C := by
    intro K
    set V : ℝ := ∑ k ∈ K, v k ^ 2 with hV
    set g : ι → ℝ := fun j => ∑ k ∈ K, S j k * v k with hg
    have hgsq : ∀ J : Finset ι, ∑ j ∈ J, g j ^ 2 ≤ A ^ 2 * V := fun J => hH K J v
    have hgsum : Summable fun j => g j ^ 2 :=
      summable_of_sum_le (fun j => sq_nonneg _) hgsq
    have hgtsum : ∑' j, g j ^ 2 ≤ A ^ 2 * V := Real.tsum_le_of_sum_le (fun j => sq_nonneg _) hgsq
    have hVeq : V = ∑' j, c j * g j := by
      have : ∀ k ∈ K, Summable fun j => v k * (c j * S j k) := fun k _ =>
        (hcolsum k).mul_left (v k)
      calc V = ∑ k ∈ K, v k * v k := by simp [hV, sq]
        _ = ∑ k ∈ K, ∑' j, v k * (c j * S j k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [tsum_mul_left, ← hvS k]
        _ = ∑' j, ∑ k ∈ K, v k * (c j * S j k) := (Summable.tsum_finsetSum this).symm
        _ = ∑' j, c j * g j := by
            refine tsum_congr fun j => ?_
            simp only [hg]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
    have hVnn : 0 ≤ V := Finset.sum_nonneg fun k _ => sq_nonneg _
    rcases hA.eq_or_lt with hA0 | hApos
    · have hg0 : ∀ j, g j = 0 := by
        intro j
        have := (hgsum.le_tsum j (fun i _ => sq_nonneg _))
        rw [← hA0] at hgtsum
        have h2 : g j ^ 2 ≤ 0 := by nlinarith
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h2 (sq_nonneg _))
      have : V = 0 := by rw [hVeq]; simp [hg0]
      rw [this, ← hA0]; simp
    · set x : ι → ℝ := fun k => v k / A with hx
      set h : ι → ℝ := fun j => ∑ k ∈ K, S j k * x k with hh
      have hgh : ∀ j, g j = A * h j := by
        intro j
        simp only [hg, hh, hx, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
      have hxsq : ∑ k ∈ K, x k ^ 2 = V / A ^ 2 := by
        simp only [hx, hV, div_pow, Finset.sum_div]
      have hhsq : ∀ J : Finset ι, ∑ j ∈ J, h j ^ 2 ≤ V := fun J => by
        have := hH K J x
        rw [hxsq] at this
        calc _ ≤ A ^ 2 * (V / A ^ 2) := this
          _ = V := by field_simp
      have hhsum : Summable fun j => h j ^ 2 := summable_of_sum_le (fun j => sq_nonneg _) hhsq
      have hhts : ∑' j, h j ^ 2 ≤ V := Real.tsum_le_of_sum_le (fun j => sq_nonneg _) hhsq
      have hAc : Summable fun j => (A * c j) ^ 2 :=
        (ha.mul_left (A ^ 2)).congr fun j => (mul_pow A (c j) 2).symm
      have hAcC : ∑' j, (A * c j) ^ 2 = A ^ 2 * C := by
        rw [tsum_congr fun j => mul_pow A (c j) 2, tsum_mul_left]
      have hcg : ∀ j, c j * g j ≤ ((A * c j) ^ 2 + h j ^ 2) / 2 := by
        intro j; rw [hgh j]; nlinarith [sq_nonneg (A * c j - h j)]
      have hsumB : Summable fun j => ((A * c j) ^ 2 + h j ^ 2) / 2 := (hAc.add hhsum).div_const 2
      have hsum1 : Summable fun j => c j * g j := by
        refine Summable.of_norm_bounded hsumB fun j => ?_
        rw [Real.norm_eq_abs]
        refine abs_le.2 ⟨?_, hcg j⟩
        rw [hgh j]; nlinarith [sq_nonneg (A * c j + h j)]
      have h6 : V ≤ (A ^ 2 * C + V) / 2 := by
        rw [hVeq]
        refine (Summable.tsum_le_tsum hcg hsum1 hsumB).trans ?_
        rw [tsum_div_const, Summable.tsum_add hAc hhsum, hAcC]
        linarith
      linarith
  have hsum : Summable fun k => v k ^ 2 :=
    summable_of_sum_le (fun k => sq_nonneg _) hfin
  exact ⟨hsum, Real.tsum_le_of_sum_le (fun k => sq_nonneg _) hfin⟩

end HRS.MC.Sec7.PIE

end
