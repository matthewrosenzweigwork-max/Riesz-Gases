import HRS.Whole.Oscillator
import HRS.MS.MovInterpAux1

/-!
# MOVA3 (spike): Stein interpolation on the Hermite scale `Σ → Σ` (`mo_interp_osc`)

Brief MOV-A3a of `docs/MOV_PLAN.md`.  `mo_Hspan d` is the real linear span of the Hermite
functions `hermiteFunD α` (finite combinations).

* `mo_interp_osc`: if a map `T` is linear on `mo_Hspan d` with values in `L²`, and satisfies
  `‖T f‖_{Σ^{s_i}} ≤ M_i ‖f‖_{Σ^{r_i}}` for `i = 0, 1` on `mo_Hspan d`, then for every
  `θ ∈ [0,1]` the same holds with `(r_θ, s_θ, M_0^{1-θ} M_1^θ)` (affine combinations).

Statement adjustments relative to the sketch of the brief (all harmless): none of substance.
`T` is only a function `(Euc d → ℝ) → (Euc d → ℝ)`; linearity is required only on the span
(`hlin`), `MemLp (T f) 2` on the span (`hL2`; it is part of `MemOsc` and is not implied by the
coefficient bounds).  `M0, M1 ≥ 0` are not assumed: they follow from `h0, h1` applied to a single
Hermite function (`mova3_nonneg_of_bound`), so the `rpow`s in the conclusion are honest.
No junk values: `oscNorm` of every element is controlled by `MemOsc` in the conclusion.

Proof: the coefficients `K α β = ⟨T h_α, h_β⟩ = hermiteCoeff (T (hermiteFunD α)) β` turn the
hypotheses into the finite-section bounds `mova3_Hop` of `MovInterpAux1`, whose interpolation
theorem `mova3_matrix_interp` (three-lines theorem) is then transferred back.
-/

noncomputable section

open MeasureTheory Finset
open HRS.Whole
open HRS.MS.MovInterp

namespace HRS.MS.MovOsc

variable {d : ℕ}

/-- The span of the Hermite functions (finite combinations). -/
abbrev mo_Hspan (d : ℕ) : Submodule ℝ (Euc d → ℝ) :=
  Submodule.span ℝ (Set.range (hermiteFunD (d := d)))

/-- Finite Hermite combination `∑_{α ∈ S} c_α h_α`. -/
def mova3_comb (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : Euc d → ℝ :=
  fun x => ∑ α ∈ S, c α * hermiteFunD α x

lemma mova3_hermite_mem (α : MultiIndex d) : hermiteFunD α ∈ mo_Hspan d :=
  Submodule.subset_span ⟨α, rfl⟩

lemma mova3_comb_mem (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    mova3_comb S c ∈ mo_Hspan d := by
  have : mova3_comb S c = ∑ α ∈ S, c α • hermiteFunD α := by
    funext x; simp [mova3_comb, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (mova3_hermite_mem α)

lemma mova3_exists_comb {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) :
    ∃ (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ), f = mova3_comb S c := by
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hf
  refine ⟨c.support, c, ?_⟩
  rw [← hc]; funext x; simp [Finsupp.sum, mova3_comb, Finset.sum_apply]

lemma mova3_coeff_comb (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) (β : MultiIndex d) :
    hermiteCoeff (mova3_comb S c) β = if β ∈ S then c β else 0 := by
  unfold hermiteCoeff mova3_comb
  have : ∀ x : Euc d, (∑ α ∈ S, c α * hermiteFunD α x) * hermiteFunD β x =
      ∑ α ∈ S, c α * (hermiteFunD α x * hermiteFunD β x) := by
    intro x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun α _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ (fun α _ => (integrable_hermiteFunD_mul α β).const_mul (c α))]
  simp_rw [integral_const_mul, hermiteFunD_orthonormal]
  simp [Finset.sum_ite_eq']

lemma mova3_tsum_comb (r : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    ∑' α, oscEigenvalue d α ^ r * hermiteCoeff (mova3_comb S c) α ^ 2 =
      ∑ α ∈ S, oscEigenvalue d α ^ r * c α ^ 2 := by
  rw [tsum_eq_sum (s := S)]
  · exact Finset.sum_congr rfl fun α hα => by rw [mova3_coeff_comb, if_pos hα]
  · intro α hα; rw [mova3_coeff_comb, if_neg hα]; simp

lemma mova3_oscNorm_comb (r : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    oscNorm r (mova3_comb S c) = Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ r * c α ^ 2) := by
  unfold oscNorm; rw [mova3_tsum_comb]

section LinearMap

variable {T : (Euc d → ℝ) → (Euc d → ℝ)}

lemma mova3_T_zero
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g) :
    T 0 = 0 := by
  have h := hlin 0 (zero_mem _) 0 (zero_mem _) 1
  rw [smul_zero, add_zero, one_smul] at h
  funext x
  have := congrFun h x
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  linarith

lemma mova3_T_comb
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    T (mova3_comb S c) = fun x => ∑ α ∈ S, c α * T (hermiteFunD α) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : mova3_comb (∅ : Finset (MultiIndex d)) c = 0 := by funext x; simp [mova3_comb]
    rw [this, mova3_T_zero hlin]; funext x; simp
  | insert a S ha ih =>
    have e : mova3_comb (insert a S) c = c a • hermiteFunD a + mova3_comb S c := by
      funext x; simp [mova3_comb, Finset.sum_insert ha]
    rw [e, hlin _ (mova3_hermite_mem a) _ (mova3_comb_mem S c) (c a), ih]
    funext x; simp [Finset.sum_insert ha]

lemma mova3_coeff_T_comb
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) (β : MultiIndex d) :
    hermiteCoeff (T (mova3_comb S c)) β =
      ∑ α ∈ S, c α * hermiteCoeff (T (hermiteFunD α)) β := by
  rw [mova3_T_comb hlin]
  unfold hermiteCoeff
  have : ∀ x : Euc d, (∑ α ∈ S, c α * T (hermiteFunD α) x) * hermiteFunD β x =
      ∑ α ∈ S, c α * (T (hermiteFunD α) x * hermiteFunD β x) := by
    intro x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun α _ => by ring
  simp_rw [this]
  have hint : ∀ α ∈ S, Integrable (fun x => T (hermiteFunD α) x * hermiteFunD β x)
      (volume : Measure (Euc d)) := fun α _ =>
    (hL2 _ (mova3_hermite_mem α)).integrable_mul (memLp_hermiteFunD β)
  rw [integral_finsetSum _ (fun α hα => (hint α hα).const_mul (c α))]
  simp_rw [integral_const_mul]

/-- The hypothesis `‖T f‖_s ≤ M ‖f‖_r` on the span gives the finite-section bound. -/
lemma mova3_Hop_of_bound
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {r s M : ℝ}
    (h : ∀ f ∈ mo_Hspan d, MemOsc s (T f) ∧ oscNorm s (T f) ≤ M * oscNorm r f) :
    mova3_Hop (oscEigenvalue d) (fun α β => hermiteCoeff (T (hermiteFunD α)) β) r s M := by
  intro S S' c
  obtain ⟨hmem, hnorm⟩ := h _ (mova3_comb_mem S c)
  have hnn : ∀ β, 0 ≤ oscEigenvalue d β ^ s * hermiteCoeff (T (mova3_comb S c)) β ^ 2 :=
    fun β => mul_nonneg (Real.rpow_nonneg (oscEv_pos β).le _) (sq_nonneg _)
  have h1 : ∑ β ∈ S', oscEigenvalue d β ^ s * hermiteCoeff (T (mova3_comb S c)) β ^ 2 ≤
      oscNorm s (T (mova3_comb S c)) ^ 2 := by
    have : oscNorm s (T (mova3_comb S c)) ^ 2 =
        ∑' β, oscEigenvalue d β ^ s * hermiteCoeff (T (mova3_comb S c)) β ^ 2 :=
      Real.sq_sqrt (tsum_nonneg hnn)
    rw [this]
    exact hmem.2.sum_le_tsum S' (fun β _ => hnn β)
  have h2 : oscNorm s (T (mova3_comb S c)) ^ 2 ≤ (M * oscNorm r (mova3_comb S c)) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  have h3 : oscNorm r (mova3_comb S c) ^ 2 = ∑ α ∈ S, oscEigenvalue d α ^ r * c α ^ 2 := by
    rw [mova3_oscNorm_comb]
    exact Real.sq_sqrt (Finset.sum_nonneg fun α _ =>
      mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))
  have h4 : ∀ β, hermiteCoeff (T (mova3_comb S c)) β =
      ∑ α ∈ S, c α * hermiteCoeff (T (hermiteFunD α)) β := mova3_coeff_T_comb hlin hL2 S c
  simp_rw [h4] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = M ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ r * c α ^ 2 := by rw [mul_pow, h3]

/-- `M ≥ 0` is forced by the bound on a single Hermite function. -/
lemma mova3_nonneg_of_bound [Nonempty (MultiIndex d)] {r s M : ℝ}
    (h : ∀ f ∈ mo_Hspan d, MemOsc s (T f) ∧ oscNorm s (T f) ≤ M * oscNorm r f) : 0 ≤ M := by
  classical
  obtain ⟨α0⟩ := (inferInstance : Nonempty (MultiIndex d))
  obtain ⟨-, hn⟩ := h _ (mova3_comb_mem {α0} (fun _ => 1))
  have hq : 0 < oscNorm r (mova3_comb {α0} (fun _ => 1)) := by
    rw [mova3_oscNorm_comb]
    simp only [Finset.sum_singleton, one_pow, mul_one]
    exact Real.sqrt_pos.2 (Real.rpow_pos_of_pos (oscEv_pos α0) _)
  by_contra hM
  push_neg at hM
  have := mul_neg_of_neg_of_pos hM hq
  have h0 : 0 ≤ oscNorm s (T (mova3_comb {α0} (fun _ => 1))) := Real.sqrt_nonneg _
  linarith

end LinearMap

/-- **Stein interpolation on the Hermite scale** (`Σ → Σ`), abstract form.  See the file docstring. -/
theorem mo_interp_osc {T : (Euc d → ℝ) → (Euc d → ℝ)}
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {r0 r1 s0 s1 M0 M1 : ℝ}
    (h0 : ∀ f ∈ mo_Hspan d, MemOsc s0 (T f) ∧ oscNorm s0 (T f) ≤ M0 * oscNorm r0 f)
    (h1 : ∀ f ∈ mo_Hspan d, MemOsc s1 (T f) ∧ oscNorm s1 (T f) ≤ M1 * oscNorm r1 f)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ f ∈ mo_Hspan d,
      MemOsc ((1 - θ) * s0 + θ * s1) (T f) ∧
        oscNorm ((1 - θ) * s0 + θ * s1) (T f) ≤
          M0 ^ (1 - θ) * M1 ^ θ * oscNorm ((1 - θ) * r0 + θ * r1) f := by
  intro f hf
  have : Nonempty (MultiIndex d) := ⟨fun _ => 0⟩
  have hM0 := mova3_nonneg_of_bound h0
  have hM1 := mova3_nonneg_of_bound h1
  have H0 := mova3_Hop_of_bound hlin hL2 h0
  have H1 := mova3_Hop_of_bound hlin hL2 h1
  have Hθ := mova3_matrix_interp oscEv_pos hM0 hM1 hθ.1 hθ.2 H0 H1
  obtain ⟨S, c, rfl⟩ := mova3_exists_comb hf
  set B := M0 ^ (1 - θ) * M1 ^ θ with hB
  have hBn : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set ρ := (1 - θ) * r0 + θ * r1 with hρ
  have hnn : ∀ β, 0 ≤ oscEigenvalue d β ^ σ * hermiteCoeff (T (mova3_comb S c)) β ^ 2 :=
    fun β => mul_nonneg (Real.rpow_nonneg (oscEv_pos β).le _) (sq_nonneg _)
  have hbound : ∀ S' : Finset (MultiIndex d),
      ∑ β ∈ S', oscEigenvalue d β ^ σ * hermiteCoeff (T (mova3_comb S c)) β ^ 2 ≤
        B ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ ρ * c α ^ 2 := by
    intro S'
    have := Hθ S S' c
    simp_rw [← mova3_coeff_T_comb hlin hL2] at this
    exact this
  have hsum : Summable fun β => oscEigenvalue d β ^ σ * hermiteCoeff (T (mova3_comb S c)) β ^ 2 :=
    summable_of_sum_le hnn hbound
  refine ⟨⟨hL2 _ hf, hsum⟩, ?_⟩
  have htsum := Real.tsum_le_of_sum_le hnn hbound
  rw [mova3_oscNorm_comb]
  unfold oscNorm
  calc Real.sqrt (∑' β, oscEigenvalue d β ^ σ * hermiteCoeff (T (mova3_comb S c)) β ^ 2)
      ≤ Real.sqrt (B ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ ρ * c α ^ 2) := Real.sqrt_le_sqrt htsum
    _ = B * Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ρ * c α ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hBn]

end HRS.MS.MovOsc
