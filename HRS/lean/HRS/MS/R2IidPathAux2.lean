import HRS.MS.R2IidPathAux1

/-!
# S11P, helper file 2: the Hilbert space `K = ℓ²(ℕ × MultiIndex d)` and the synthesis map `J : K → C([0,T]; B_m)`

`J z (t) = c⁻¹ ∑_{n,α} κ_n e_n(t) z_{n,α} δ_α` with `κ_n = (1+n²)^{-3/8}` and `c` large enough that `‖J‖ ≤ 1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.Whole

/-- `K = ℓ²(ℕ × ℕ^d)`. -/
def s11p_K (d : ℕ) : Type := lp (fun _ : ℕ × MultiIndex d => ℝ) 2

namespace s11p_K

variable {d : ℕ}

instance : NormedAddCommGroup (s11p_K d) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ × MultiIndex d => ℝ) 2))

instance : InnerProductSpace ℝ (s11p_K d) :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : ℕ × MultiIndex d => ℝ) 2))

instance : CompleteSpace (s11p_K d) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℕ × MultiIndex d => ℝ) 2))

instance : MeasurableSpace (s11p_K d) := borel _

instance : BorelSpace (s11p_K d) := ⟨rfl⟩

instance : SecondCountableTopology (s11p_K d) :=
  haveI : TopologicalSpace.SeparableSpace (s11p_K d) :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ × MultiIndex d)
  UniformSpace.secondCountable_of_separable _

/-- The coordinate `z_{n,α}`. -/
def c (z : s11p_K d) (q : ℕ × MultiIndex d) : ℝ := (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from z) q

/-- The element with prescribed square-summable coordinates. -/
def mk (f : ℕ × MultiIndex d → ℝ) (h : Summable fun q => f q ^ 2) : s11p_K d :=
  (⟨f, memℓp_two_iff.2 h⟩ : lp (fun _ : ℕ × MultiIndex d => ℝ) 2)

theorem c_mk (f : ℕ × MultiIndex d → ℝ) (h : Summable fun q => f q ^ 2) (q) : c (mk f h) q = f q := rfl

theorem c_add (z w : s11p_K d) (q) : c (z + w) q = c z q + c w q := rfl
theorem c_sub (z w : s11p_K d) (q) : c (z - w) q = c z q - c w q := rfl
theorem c_smul (r : ℝ) (z : s11p_K d) (q) : c (r • z) q = r * c z q := rfl
theorem c_zero (q : ℕ × MultiIndex d) : c (0 : s11p_K d) q = 0 := rfl

theorem c_sq_summable (z : s11p_K d) : Summable fun q => c z q ^ 2 := lp_two_summable
  (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from z)

theorem norm_sq_eq (z : s11p_K d) : ‖z‖ ^ 2 = ∑' q, c z q ^ 2 :=
  lp_two_norm_sq (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from z)

theorem ext_c {z w : s11p_K d} (h : ∀ q, c z q = c w q) : z = w :=
  lp.ext (funext h)

/-- The inner product in coordinates. -/
theorem inner_eq (z w : s11p_K d) : inner ℝ z w = ∑' q, c z q * c w q := by
  show inner ℝ (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from z)
    (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from w) = _
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  simp [c, mul_comm]

end s11p_K

section Basis

variable {d : ℕ}

/-- The identity isometry `K ≃ ℓ²`. -/
def s11p_repr (d : ℕ) : s11p_K d ≃ₗᵢ[ℝ] lp (fun _ : ℕ × MultiIndex d => ℝ) 2 where
  toFun := id
  invFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  norm_map' := fun _ => rfl

/-- The standard Hilbert basis of `K` indexed by `ℕ × ℕ^d`. -/
def s11p_basis0 (d : ℕ) : HilbertBasis (ℕ × MultiIndex d) ℝ (s11p_K d) :=
  HilbertBasis.ofRepr (s11p_repr d)

theorem s11p_basis0_apply (q : ℕ × MultiIndex d) :
    (s11p_basis0 d q : s11p_K d) =
      (show s11p_K d from lp.single (E := fun _ : ℕ × MultiIndex d => ℝ) 2 q (1 : ℝ)) := by
  classical
  rw [← HilbertBasis.repr_symm_single]; rfl

/-- A Hilbert basis indexed by `ℕ`. -/
def s11p_basis (σ : ℕ ≃ ℕ × MultiIndex d) : HilbertBasis ℕ ℝ (s11p_K d) :=
  HilbertBasis.mk (v := fun n => (s11p_basis0 d (σ n) : s11p_K d))
    ((s11p_basis0 d).orthonormal.comp σ σ.injective) (by
      have h := (s11p_basis0 d).dense_span
      have e : Set.range (fun n => (s11p_basis0 d (σ n) : s11p_K d)) =
          Set.range (s11p_basis0 d) := σ.surjective.range_comp (s11p_basis0 d)
      rw [e, h])

theorem s11p_inner_basis (σ : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (u : s11p_K d) :
    inner ℝ (s11p_basis σ n) u = u.c (σ n) := by
  rw [s11p_basis, HilbertBasis.coe_mk, s11p_basis0_apply]
  show inner ℝ (lp.single (E := fun _ : ℕ × MultiIndex d => ℝ) 2 (σ n) (1 : ℝ))
    (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from u) = _
  rw [lp.inner_single_left]
  simp [s11p_K.c]

theorem s11p_exists_equiv : Nonempty (ℕ ≃ ℕ × MultiIndex d) := by
  haveI : Infinite (ℕ × MultiIndex d) := Infinite.of_injective (fun n : ℕ => ((n, 0) : ℕ × MultiIndex d))
    (fun a b hab => by simpa using hab)
  exact nonempty_equiv_of_countable

end Basis

section Bil

variable {d : ℕ}

/-- The fibre `n ↦ z_{n,α}` as an element of `ℓ²(ℕ)`. -/
def s11p_fib (z : s11p_K d) (α : MultiIndex d) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => z.c (n, α), memℓp_two_iff.2 ((s11p_K.c_sq_summable z).comp_injective
    (i := fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) (fun a b hab => by simpa using hab))⟩

theorem s11p_fib_apply (z : s11p_K d) (α : MultiIndex d) (n : ℕ) : s11p_fib z α n = z.c (n, α) := rfl

theorem s11p_fib_norm_sq (z : s11p_K d) (α : MultiIndex d) :
    ‖s11p_fib z α‖ ^ 2 = ∑' n, z.c (n, α) ^ 2 := lp_two_norm_sq _

theorem s11p_fib_sq_summable (z : s11p_K d) : Summable fun α : MultiIndex d => ‖s11p_fib z α‖ ^ 2 := by
  have h := (s11p_K.c_sq_summable z).comp_injective (i := (Prod.swap : MultiIndex d × ℕ → ℕ × MultiIndex d)) Prod.swap_injective
  have h2 := h.prod
  refine h2.congr fun α => ?_
  rw [s11p_fib_norm_sq]
  rfl

theorem s11p_fib_tsum (z : s11p_K d) : ∑' α : MultiIndex d, ‖s11p_fib z α‖ ^ 2 = ‖z‖ ^ 2 := by
  have h := (s11p_K.c_sq_summable z).comp_injective (i := (Prod.swap : MultiIndex d × ℕ → ℕ × MultiIndex d)) Prod.swap_injective
  rw [s11p_K.norm_sq_eq]
  have e1 : ∑' p : MultiIndex d × ℕ, z.c p.swap ^ 2 = ∑' q : ℕ × MultiIndex d, z.c q ^ 2 :=
    (Equiv.prodComm (MultiIndex d) ℕ).tsum_eq (fun q => z.c q ^ 2)
  rw [← e1]
  have h' := h.tsum_prod
  simp only [Function.comp_apply] at h'
  rw [h']
  refine tsum_congr fun α => ?_
  rw [s11p_fib_norm_sq]
  rfl

/-- `α ↦ ∑_n a_n z_{n,α}`. -/
def s11p_bcoord (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) : ℝ :=
  ∑' n, a n * z.c (n, α)

theorem s11p_bcoord_eq_inner (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord a z α = inner ℝ a (s11p_fib z α) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp [s11p_bcoord, s11p_fib_apply, mul_comm]

theorem s11p_bcoord_sq_le (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord a z α ^ 2 ≤ ‖a‖ ^ 2 * ‖s11p_fib z α‖ ^ 2 := by
  rw [s11p_bcoord_eq_inner, ← mul_pow]
  have := abs_real_inner_le_norm a (s11p_fib z α)
  calc inner ℝ a (s11p_fib z α) ^ 2 = |inner ℝ a (s11p_fib z α)| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2

theorem s11p_bcoord_sq_summable (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) :
    Summable fun α => s11p_bcoord a z α ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (s11p_bcoord_sq_le a z)
    ((s11p_fib_sq_summable z).mul_left _)

theorem s11p_bcoord_tsum_le (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) :
    ∑' α, s11p_bcoord a z α ^ 2 ≤ ‖a‖ ^ 2 * ‖z‖ ^ 2 := by
  calc ∑' α, s11p_bcoord a z α ^ 2 ≤ ∑' α : MultiIndex d, ‖a‖ ^ 2 * ‖s11p_fib z α‖ ^ 2 :=
        Summable.tsum_le_tsum (s11p_bcoord_sq_le a z) (s11p_bcoord_sq_summable a z)
          ((s11p_fib_sq_summable z).mul_left _)
    _ = ‖a‖ ^ 2 * ‖z‖ ^ 2 := by rw [tsum_mul_left, s11p_fib_tsum]

theorem s11p_ext_coord {M : ℝ} {u v : OscDual d M} (h : ∀ α, OscDual.coord u α = OscDual.coord v α) :
    u = v := lp.ext (funext h)

/-- `∑_{n,α} a_n z_{n,α} δ_α ∈ B_M`. -/
def s11p_bil (M : ℝ) (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) : OscDual d M :=
  (⟨s11p_bcoord a z, memℓp_two_iff.2 (s11p_bcoord_sq_summable a z)⟩ : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s11p_coord_bil (M : ℝ) (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    OscDual.coord (s11p_bil M a z) α = s11p_bcoord a z α := rfl

theorem s11p_norm_bil_le (M : ℝ) (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) :
    ‖s11p_bil M a z‖ ≤ ‖a‖ * ‖z‖ := by
  have h1 : ‖s11p_bil M a z‖ ^ 2 = ∑' α, s11p_bcoord a z α ^ 2 :=
    lp_two_norm_sq (show lp (fun _ : MultiIndex d => ℝ) 2 from s11p_bil M a z)
  have h2 : ‖s11p_bil M a z‖ ^ 2 ≤ (‖a‖ * ‖z‖) ^ 2 := by
    rw [h1, mul_pow]; exact s11p_bcoord_tsum_le a z
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem s11p_bcoord_add_left (a a' : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord (a + a') z α = s11p_bcoord a z α + s11p_bcoord a' z α := by
  simp_rw [s11p_bcoord_eq_inner, inner_add_left]

theorem s11p_bcoord_smul_left (r : ℝ) (a : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord (r • a) z α = r * s11p_bcoord a z α := by
  simp_rw [s11p_bcoord_eq_inner, real_inner_smul_left]

theorem s11p_bcoord_sub_left (a a' : lp (fun _ : ℕ => ℝ) 2) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord (a - a') z α = s11p_bcoord a z α - s11p_bcoord a' z α := by
  simp_rw [s11p_bcoord_eq_inner, inner_sub_left]

theorem s11p_fib_add (z w : s11p_K d) (α : MultiIndex d) : s11p_fib (z + w) α = s11p_fib z α + s11p_fib w α :=
  lp.ext (funext fun n => rfl)

theorem s11p_fib_smul (r : ℝ) (z : s11p_K d) (α : MultiIndex d) : s11p_fib (r • z) α = r • s11p_fib z α :=
  lp.ext (funext fun n => rfl)

theorem s11p_bcoord_add_right (a : lp (fun _ : ℕ => ℝ) 2) (z w : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord a (z + w) α = s11p_bcoord a z α + s11p_bcoord a w α := by
  simp_rw [s11p_bcoord_eq_inner, s11p_fib_add, inner_add_right]

theorem s11p_bcoord_smul_right (a : lp (fun _ : ℕ => ℝ) 2) (r : ℝ) (z : s11p_K d) (α : MultiIndex d) :
    s11p_bcoord a (r • z) α = r * s11p_bcoord a z α := by
  simp_rw [s11p_bcoord_eq_inner, s11p_fib_smul, real_inner_smul_right]

/-- `a ↦ bil a z` as a continuous linear map. -/
def s11p_bilCLM (M : ℝ) (z : s11p_K d) : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] OscDual d M :=
  LinearMap.mkContinuous
    { toFun := fun a => s11p_bil M a z
      map_add' := fun a a' => s11p_ext_coord fun α => by
        simp only [s11p_coord_bil, s11p_bcoord_add_left]; rfl
      map_smul' := fun r a => s11p_ext_coord fun α => by
        simp only [s11p_coord_bil, s11p_bcoord_smul_left]; rfl }
    ‖z‖ (fun a => by
      show ‖s11p_bil M a z‖ ≤ ‖z‖ * ‖a‖
      rw [mul_comm]; exact s11p_norm_bil_le M a z)

theorem s11p_bilCLM_apply (M : ℝ) (z : s11p_K d) (a : lp (fun _ : ℕ => ℝ) 2) :
    s11p_bilCLM M z a = s11p_bil M a z := rfl

end Bil

section Synth

variable {T : ℝ}

theorem s11p_cos_sq_le (hT : 0 < T) (n : ℕ) (t : ℝ) : r2CosBasis T n t ^ 2 ≤ 2 / T := by
  have h := s11p_cos_bound hT n t
  calc r2CosBasis T n t ^ 2 = |r2CosBasis T n t| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt (2 / T) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 2 / T := Real.sq_sqrt (by positivity)

theorem s11p_aVec_sq_summable (hT : 0 < T) (t : ℝ) :
    Summable fun n : ℕ => (s11p_kap n * r2CosBasis T n t) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    (s11p_kap_sq_summable.mul_right (2 / T))
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (s11p_cos_sq_le hT n t) (sq_nonneg _)

/-- The vector `(κ_n e_n(t))_n ∈ ℓ²(ℕ)`. -/
def s11p_aVec (hT : 0 < T) (t : ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => s11p_kap n * r2CosBasis T n t, memℓp_two_iff.2 (s11p_aVec_sq_summable hT t)⟩

theorem s11p_aVec_apply (hT : 0 < T) (t : ℝ) (n : ℕ) : s11p_aVec hT t n = s11p_kap n * r2CosBasis T n t := rfl

/-- A bound for `‖(κ_n e_n(t))_n‖`. -/
def s11p_aBound (T : ℝ) : ℝ := Real.sqrt (∑' n : ℕ, s11p_kap n ^ 2 * (2 / T))

theorem s11p_aVec_norm_le (hT : 0 < T) (t : ℝ) : ‖s11p_aVec hT t‖ ≤ s11p_aBound T := by
  unfold s11p_aBound
  rw [lp_two_norm_eq]
  apply Real.sqrt_le_sqrt
  refine Summable.tsum_le_tsum (fun n => ?_) (s11p_aVec_sq_summable hT t)
    (s11p_kap_sq_summable.mul_right (2 / T))
  show (s11p_kap n * r2CosBasis T n t) ^ 2 ≤ _
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (s11p_cos_sq_le hT n t) (sq_nonneg _)

theorem s11p_aBound_nonneg (T : ℝ) : 0 ≤ s11p_aBound T := Real.sqrt_nonneg _

theorem s11p_aVec_continuous (hT : 0 < T) : Continuous fun t : ℝ => s11p_aVec hT t := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Summable fun n : ℕ => 4 * (s11p_kap n ^ 2 * (2 / T)) :=
    (s11p_kap_sq_summable.mul_right (2 / T)).mul_left 4
  have key : Tendsto (fun t : ℝ => ∑' n : ℕ, (s11p_kap n * r2CosBasis T n t - s11p_kap n * r2CosBasis T n t₀) ^ 2)
      (𝓝 t₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t₀)
      (f := fun (t : ℝ) (n : ℕ) => (s11p_kap n * r2CosBasis T n t - s11p_kap n * r2CosBasis T n t₀) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun n => 4 * (s11p_kap n ^ 2 * (2 / T))) hb
      (fun n => by
        have h2 : Continuous fun t : ℝ =>
            (s11p_kap n * r2CosBasis T n t - s11p_kap n * r2CosBasis T n t₀) ^ 2 :=
          ((continuous_const.mul (s11p_cos_continuous T n)).sub continuous_const).pow 2
        simpa using h2.tendsto t₀)
      (Filter.Eventually.of_forall fun t n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 := s11p_cos_sq_le hT n t
        have h2 := s11p_cos_sq_le hT n t₀
        have h3 : 0 ≤ s11p_kap n ^ 2 := sq_nonneg _
        nlinarith [sq_nonneg (s11p_kap n * r2CosBasis T n t + s11p_kap n * r2CosBasis T n t₀),
          mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h3])
    simpa using this
  have e : (fun t : ℝ => ‖s11p_aVec hT t - s11p_aVec hT t₀‖) = fun t => Real.sqrt (∑' n : ℕ,
      (s11p_kap n * r2CosBasis T n t - s11p_kap n * r2CosBasis T n t₀) ^ 2) := by
    funext t
    rw [lp_two_norm_eq]
    rfl
  rw [e]
  simpa using key.sqrt

end Synth

section J

variable {d : ℕ} {T : ℝ}

/-- The normalising constant: `‖J‖ ≤ 1`. -/
def s11p_cJ (T : ℝ) : ℝ := 1 + s11p_aBound T

theorem s11p_cJ_pos (T : ℝ) : 0 < s11p_cJ T := by
  have := s11p_aBound_nonneg T
  unfold s11p_cJ; linarith

/-- `J z (t)` as an element of `B_M`. -/
def s11p_Jpt (hT : 0 < T) (M : ℝ) (z : s11p_K d) (t : ℝ) : OscDual d M :=
  (s11p_cJ T)⁻¹ • s11p_bil M (s11p_aVec hT t) z

theorem s11p_Jpt_continuous (hT : 0 < T) (M : ℝ) (z : s11p_K d) :
    Continuous fun t : ℝ => s11p_Jpt hT M z t := by
  unfold s11p_Jpt
  exact (continuous_const : Continuous fun _ : ℝ => (s11p_cJ T)⁻¹).smul
    ((s11p_bilCLM M z).continuous.comp (s11p_aVec_continuous hT))

theorem s11p_Jpt_norm_le (hT : 0 < T) (M : ℝ) (z : s11p_K d) (t : ℝ) : ‖s11p_Jpt hT M z t‖ ≤ ‖z‖ := by
  unfold s11p_Jpt
  have hc := s11p_cJ_pos T
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
  have h1 := s11p_norm_bil_le M (s11p_aVec hT t) z
  have h2 := s11p_aVec_norm_le hT t
  have h3 : ‖s11p_bil M (s11p_aVec hT t) z‖ ≤ s11p_aBound T * ‖z‖ :=
    h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have h4 : s11p_aBound T ≤ s11p_cJ T := by unfold s11p_cJ; linarith
  calc (s11p_cJ T)⁻¹ * ‖s11p_bil M (s11p_aVec hT t) z‖ ≤ (s11p_cJ T)⁻¹ * (s11p_cJ T * ‖z‖) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))
    _ = ‖z‖ := by field_simp

theorem s11p_Jpt_add (hT : 0 < T) (M : ℝ) (z w : s11p_K d) (t : ℝ) :
    s11p_Jpt hT M (z + w) t = s11p_Jpt hT M z t + s11p_Jpt hT M w t := by
  refine s11p_ext_coord fun α => ?_
  show _ = OscDual.coord (s11p_Jpt hT M z t) α + OscDual.coord (s11p_Jpt hT M w t) α
  show (s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) (z + w) α = (s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) z α +
    (s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) w α
  rw [s11p_bcoord_add_right]; ring

theorem s11p_Jpt_smul (hT : 0 < T) (M : ℝ) (r : ℝ) (z : s11p_K d) (t : ℝ) :
    s11p_Jpt hT M (r • z) t = r • s11p_Jpt hT M z t := by
  refine s11p_ext_coord fun α => ?_
  show (s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) (r • z) α = r * ((s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) z α)
  rw [s11p_bcoord_smul_right]; ring

/-- The synthesis map `J : K → C([0,T]; B_M)`. -/
def s11p_J (hT : 0 < T) (M : ℝ) : s11p_K d →L[ℝ] OscPath d M T :=
  LinearMap.mkContinuous
    { toFun := fun z => (show OscPath d M T from
        (⟨fun t : Set.Icc (0 : ℝ) T => s11p_Jpt hT M z t,
          (s11p_Jpt_continuous hT M z).comp continuous_subtype_val⟩ : C(Set.Icc (0 : ℝ) T, OscDual d M)))
      map_add' := fun z w => by
        refine ContinuousMap.ext fun t => ?_
        exact s11p_Jpt_add hT M z w t
      map_smul' := fun r z => by
        refine ContinuousMap.ext fun t => ?_
        exact s11p_Jpt_smul hT M r z t }
    1 (fun z => by
      show ‖(⟨fun t : Set.Icc (0 : ℝ) T => s11p_Jpt hT M z t,
          (s11p_Jpt_continuous hT M z).comp continuous_subtype_val⟩ : C(Set.Icc (0 : ℝ) T, OscDual d M))‖ ≤ 1 * ‖z‖
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
      exact fun t => s11p_Jpt_norm_le hT M z t)

theorem s11p_J_at (hT : 0 < T) (M : ℝ) (z : s11p_K d) (t : Set.Icc (0 : ℝ) T) :
    OscPath.at' (s11p_J hT M z) t = s11p_Jpt hT M z t := rfl

theorem s11p_J_coord (hT : 0 < T) (M : ℝ) (z : s11p_K d) (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s11p_J hT M z) t) α = (s11p_cJ T)⁻¹ * ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * z.c (n, α) := by
  show (s11p_cJ T)⁻¹ * s11p_bcoord (s11p_aVec hT t) z α = _
  unfold s11p_bcoord
  simp only [s11p_aVec_apply]

theorem s11p_J_norm_le (hT : 0 < T) (M : ℝ) : ‖(s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end J

section Vec

variable {d : ℕ} {T : ℝ}

theorem s11p_c_eq_inner (z : s11p_K d) (q : ℕ × MultiIndex d) :
    z.c q = inner ℝ (show s11p_K d from lp.single (E := fun _ : ℕ × MultiIndex d => ℝ) 2 q (1 : ℝ)) z := by
  show _ = inner ℝ (lp.single (E := fun _ : ℕ × MultiIndex d => ℝ) 2 q (1 : ℝ))
    (show lp (fun _ : ℕ × MultiIndex d => ℝ) 2 from z)
  rw [lp.inner_single_left]
  simp [s11p_K.c]

theorem s11p_vec_sq_summable (hT : 0 < T) (t : ℝ) (α : MultiIndex d) :
    Summable fun q : ℕ × MultiIndex d =>
      (if q.2 = α then (s11p_cJ T)⁻¹ * (s11p_kap q.1 * r2CosBasis T q.1 t) else 0) ^ 2 := by
  classical
  set F : ℕ × MultiIndex d → ℝ := fun q =>
    (if q.2 = α then (s11p_cJ T)⁻¹ * (s11p_kap q.1 * r2CosBasis T q.1 t) else 0) ^ 2 with hF
  have hinj : Function.Injective (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) := fun a b hab => by simpa using hab
  have hz : ∀ q ∉ Set.range (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)), F q = 0 := by
    intro q hq
    have : q.2 ≠ α := fun h => hq ⟨q.1, Prod.ext rfl h.symm⟩
    simp [hF, this]
  refine (hinj.summable_iff hz).1 ?_
  have e : (F ∘ fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) =
      fun n => ((s11p_cJ T)⁻¹) ^ 2 * (s11p_kap n * r2CosBasis T n t) ^ 2 := by
    funext n; simp [hF, mul_pow]
  rw [e]
  exact (s11p_aVec_sq_summable hT t).mul_left _

/-- `v_{t,α} ∈ K` with `⟨v_{t,α}, z⟩ = (J z)(t)_α`. -/
def s11p_vec (hT : 0 < T) (t : ℝ) (α : MultiIndex d) : s11p_K d :=
  open Classical in
  s11p_K.mk (fun q => if q.2 = α then (s11p_cJ T)⁻¹ * (s11p_kap q.1 * r2CosBasis T q.1 t) else 0)
    (s11p_vec_sq_summable hT t α)

theorem s11p_inner_vec (hT : 0 < T) (M : ℝ) (z : s11p_K d) (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    inner ℝ (s11p_vec hT t α) z = OscDual.coord (OscPath.at' (s11p_J hT M z) t) α := by
  classical
  rw [s11p_J_coord, s11p_K.inner_eq]
  have hinj : Function.Injective (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) := fun a b hab => by simpa using hab
  have hsupp : Function.support (fun q : ℕ × MultiIndex d => (s11p_vec hT t α).c q * z.c q) ⊆
      Set.range (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) := by
    intro q hq
    by_contra hqr
    apply hq
    have : q.2 ≠ α := fun h => hqr ⟨q.1, Prod.ext rfl h.symm⟩
    simp [s11p_vec, s11p_K.c_mk, this]
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [s11p_vec, s11p_K.c_mk, ite_true]
  ring

end Vec

section Data

variable {d : ℕ}

/-- The data of the orbit features: continuous functions `f_q` with a summable sup-envelope. -/
structure S11pData (d : ℕ) where
  f : ℕ × MultiIndex d → Euc d → ℝ
  w : ℕ × MultiIndex d → ℝ
  hw : Summable w
  hfw : ∀ q x, |f q x| ≤ w q
  hfc : ∀ q, Continuous (f q)

namespace S11pData

variable (D : S11pData d) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

theorem w_nonneg (q : ℕ × MultiIndex d) : 0 ≤ D.w q := (abs_nonneg _).trans (D.hfw q 0)

theorem w_le_tsum (q : ℕ × MultiIndex d) : D.w q ≤ ∑' p, D.w p :=
  D.hw.le_tsum q (fun p _ => D.w_nonneg p)

theorem wsq_summable : Summable fun q => D.w q ^ 2 := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) (D.hw.mul_left (∑' p, D.w p))
  rw [sq]
  exact mul_le_mul_of_nonneg_right (D.w_le_tsum q) (D.w_nonneg q)

theorem int_abs_le (q : ℕ × MultiIndex d) : |∫ y, D.f q y ∂μ| ≤ D.w q := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := D.f q) (C := D.w q)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using D.hfw q y)
  simpa [Real.norm_eq_abs, Measure.real] using this

theorem coef_abs_le (q : ℕ × MultiIndex d) (x : Euc d) : |D.f q x - ∫ y, D.f q y ∂μ| ≤ 2 * D.w q := by
  refine (abs_sub _ _).trans ?_
  linarith [D.hfw q x, D.int_abs_le μ q]

theorem Ysq_summable (c0 : ℝ) (x : Euc d) :
    Summable fun q => (c0 * (D.f q x - ∫ y, D.f q y ∂μ)) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) (D.wsq_summable.mul_left (4 * c0 ^ 2))
  have h := D.coef_abs_le μ q x
  have h2 : (D.f q x - ∫ y, D.f q y ∂μ) ^ 2 ≤ (2 * D.w q) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (c0 * (D.f q x - ∫ y, D.f q y ∂μ)) ^ 2 = c0 ^ 2 * (D.f q x - ∫ y, D.f q y ∂μ) ^ 2 := by ring
    _ ≤ c0 ^ 2 * (2 * D.w q) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = 4 * c0 ^ 2 * D.w q ^ 2 := by ring

/-- `Y_x = c0 (f_q(x) - μ f_q)_q ∈ K`. -/
def Y (c0 : ℝ) (x : Euc d) : s11p_K d :=
  s11p_K.mk (fun q => c0 * (D.f q x - ∫ y, D.f q y ∂μ)) (D.Ysq_summable μ c0 x)

theorem Y_c (c0 : ℝ) (x : Euc d) (q : ℕ × MultiIndex d) :
    (D.Y μ c0 x).c q = c0 * (D.f q x - ∫ y, D.f q y ∂μ) := rfl

/-- A bound for `‖Y_x‖`. -/
def Cb (c0 : ℝ) : ℝ := 2 * |c0| * Real.sqrt (∑' q, D.w q ^ 2)

theorem norm_Y_le (c0 : ℝ) (x : Euc d) : ‖D.Y μ c0 x‖ ≤ D.Cb c0 := by
  have h1 : ‖D.Y μ c0 x‖ ^ 2 ≤ D.Cb c0 ^ 2 := by
    rw [s11p_K.norm_sq_eq]
    unfold Cb
    rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun q => sq_nonneg _), mul_pow, sq_abs]
    calc ∑' q, (D.Y μ c0 x).c q ^ 2 ≤ ∑' q, 4 * c0 ^ 2 * D.w q ^ 2 :=
          Summable.tsum_le_tsum (fun q => ?_) (s11p_K.c_sq_summable _) (D.wsq_summable.mul_left _)
      _ = _ := by rw [tsum_mul_left]; ring
    rw [Y_c]
    have h := D.coef_abs_le μ q x
    have h2 : (D.f q x - ∫ y, D.f q y ∂μ) ^ 2 ≤ (2 * D.w q) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (c0 * (D.f q x - ∫ y, D.f q y ∂μ)) ^ 2 = c0 ^ 2 * (D.f q x - ∫ y, D.f q y ∂μ) ^ 2 := by ring
      _ ≤ c0 ^ 2 * (2 * D.w q) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 4 * c0 ^ 2 * D.w q ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold Cb; positivity) two_ne_zero).1 h1

theorem Cb_nonneg (c0 : ℝ) : 0 ≤ D.Cb c0 := by unfold Cb; positivity

theorem Y_continuous (c0 : ℝ) : Continuous (D.Y μ c0) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Summable fun q : ℕ × MultiIndex d => 4 * c0 ^ 2 * D.w q ^ 2 := D.wsq_summable.mul_left _
  have key : Tendsto (fun x => ∑' q : ℕ × MultiIndex d,
      ((D.Y μ c0 x).c q - (D.Y μ c0 x₀).c q) ^ 2) (𝓝 x₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 x₀)
      (f := fun (x : Euc d) (q : ℕ × MultiIndex d) => ((D.Y μ c0 x).c q - (D.Y μ c0 x₀).c q) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun q => 4 * c0 ^ 2 * D.w q ^ 2) hb
      (fun q => by
        have h2 : Continuous fun x : Euc d => ((D.Y μ c0 x).c q - (D.Y μ c0 x₀).c q) ^ 2 := by
          simp only [Y_c]
          exact (((continuous_const.mul ((D.hfc q).sub continuous_const))).sub continuous_const).pow 2
        simpa using h2.tendsto x₀)
      (Filter.Eventually.of_forall fun x q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simp only [Y_c]
        have h1 := D.hfw q x
        have h2 := D.hfw q x₀
        have e : c0 * (D.f q x - ∫ y, D.f q y ∂μ) - c0 * (D.f q x₀ - ∫ y, D.f q y ∂μ) =
            c0 * (D.f q x - D.f q x₀) := by ring
        rw [e]
        have h3 : (D.f q x - D.f q x₀) ^ 2 ≤ (2 * D.w q) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith)) 2
        calc (c0 * (D.f q x - D.f q x₀)) ^ 2 = c0 ^ 2 * (D.f q x - D.f q x₀) ^ 2 := by ring
          _ ≤ c0 ^ 2 * (2 * D.w q) ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = 4 * c0 ^ 2 * D.w q ^ 2 := by ring)
    simpa using this
  have e : (fun x => ‖D.Y μ c0 x - D.Y μ c0 x₀‖) = fun x => Real.sqrt (∑' q : ℕ × MultiIndex d,
      ((D.Y μ c0 x).c q - (D.Y μ c0 x₀).c q) ^ 2) := by
    funext x
    exact lp_two_norm_eq (ι := ℕ × MultiIndex d) (D.Y μ c0 x - D.Y μ c0 x₀)
  rw [e]
  simpa using key.sqrt

theorem Y_integral_zero (c0 : ℝ) : ∫ x, D.Y μ c0 x ∂μ = 0 := by
  have hcont := D.Y_continuous μ c0
  have hint : Integrable (D.Y μ c0) μ :=
    Integrable.of_bound hcont.aestronglyMeasurable (D.Cb c0) (Filter.Eventually.of_forall (D.norm_Y_le μ c0))
  refine s11p_K.ext_c fun q => ?_
  rw [s11p_c_eq_inner, ← integral_inner hint]
  simp_rw [← s11p_c_eq_inner, Y_c]
  have hi : Integrable (D.f q) μ :=
    Integrable.of_bound (D.hfc q).aestronglyMeasurable (D.w q)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using D.hfw q y)
  rw [integral_const_mul, integral_sub hi (integrable_const _)]
  simp [s11p_K.c_zero]

theorem tail_bound (c0 : ℝ) (σ : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (x : Euc d) :
    (inner ℝ (s11p_basis σ n) (D.Y μ c0 x)) ^ 2 ≤ 4 * c0 ^ 2 * D.w (σ n) ^ 2 := by
  rw [s11p_inner_basis, Y_c]
  have h := D.coef_abs_le μ (σ n) x
  have h2 : (D.f (σ n) x - ∫ y, D.f (σ n) y ∂μ) ^ 2 ≤ (2 * D.w (σ n)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc _ = c0 ^ 2 * (D.f (σ n) x - ∫ y, D.f (σ n) y ∂μ) ^ 2 := by ring
    _ ≤ c0 ^ 2 * (2 * D.w (σ n)) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem tail_summable (c0 : ℝ) (σ : ℕ ≃ ℕ × MultiIndex d) :
    Summable fun n => 4 * c0 ^ 2 * D.w (σ n) ^ 2 :=
  (D.wsq_summable.mul_left (4 * c0 ^ 2)).comp_injective σ.injective

theorem exists_gaussian (c0 : ℝ) : ∃ G : Measure (s11p_K d), IsProbabilityMeasure G ∧
    HRS.IsCenteredGaussian G ∧
    ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (D.Y μ c0)) x y := by
  have hcont := D.Y_continuous μ c0
  have hYL : MemLp (D.Y μ c0) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable (D.Cb c0) (Filter.Eventually.of_forall (D.norm_Y_le μ c0))
  obtain ⟨htc, -⟩ := HRS.isTraceClassCov_covarianceBilin μ (D.Y μ c0) hYL (D.Y_integral_zero μ c0)
  obtain ⟨γ, hp, hg, hcov⟩ := HRS.exists_centeredGaussian_of_traceClass _ htc
  exact ⟨γ, hp, hg, hcov⟩

end S11pData

end Data

section Orbit

variable {d : ℕ} (C : WholeCoeff d) (M : ℝ) {T : ℝ}

theorem s11p_abs_le_cbNorm {k : ℕ} {φ : Euc d → ℝ} (h : MemCb k φ) (x : Euc d) : |φ x| ≤ cbNorm k φ := by
  unfold cbNorm
  have h0 : |φ x| ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 φ z‖ := by
    have := le_ciSup (h.2 0 (Nat.zero_le _)) x
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  refine h0.trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))

/-- The orbit features `f_{n,α}` as an `S11pData`. -/
def s11p_orbitData {k : ℕ} (hmem : ∀ n α, MemCb k (r2CosOrbitTest C M T n α))
    (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C M T q.1 q.2)) : S11pData d where
  f q := r2CosOrbitTest C M T q.1 q.2
  w q := cbNorm k (r2CosOrbitTest C M T q.1 q.2)
  hw := hsum
  hfw q x := s11p_abs_le_cbNorm (hmem q.1 q.2) x
  hfc q := (hmem q.1 q.2).1.continuous

theorem s11p_orbit_hasSum (hT : 0 < T) {k : ℕ} (hmem : ∀ n α, MemCb k (r2CosOrbitTest C M T n α))
    (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C M T q.1 q.2))
    (hcont : ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun M α) x) (Set.Icc (0 : ℝ) T))
    (α : MultiIndex d) (x : Euc d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasSum (fun n => s11p_kap n * r2CosBasis T n t * (s11p_orbitData C M hmem hsum).f (n, α) x)
      (propagatorW C 0 t (oscTestFun M α) x) := by
  set D := s11p_orbitData C M hmem hsum with hD
  have hb : Summable fun n : ℕ => D.f (n, α) x := by
    refine Summable.of_norm_bounded ((D.hw.comp_injective
      (i := fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) (fun a b hab => by simpa using hab))) fun n => ?_
    rw [Real.norm_eq_abs]
    exact D.hfw (n, α) x
  exact s11p_cos_expand hT (fun t => propagatorW C 0 t (oscTestFun M α) x) (hcont α x) _ hb
    (fun n => rfl) t ht

end Orbit

section Pair

variable {d : ℕ} {T : ℝ} (D : S11pData d) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

/-- The abstract series hypothesis: `U α t = ∑_n κ_n e_n(t) f_{n,α}`. -/
def S11pSeries (D : S11pData d) (T : ℝ) (U : MultiIndex d → ℝ → Euc d → ℝ) : Prop :=
  ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ x : Euc d,
    HasSum (fun n => s11p_kap n * r2CosBasis T n t * D.f (n, α) x) (U α t x)

variable {D} {U : MultiIndex d → ℝ → Euc d → ℝ}

theorem s11p_term_abs_le (hT : 0 < T) (n : ℕ) (α : MultiIndex d) (t : ℝ) (x : Euc d) :
    |s11p_kap n * r2CosBasis T n t * D.f (n, α) x| ≤ Real.sqrt (2 / T) * D.w (n, α) := by
  rw [abs_mul, abs_mul, abs_of_pos (s11p_kap_pos n)]
  have h1 := s11p_cos_bound hT n t
  have h2 := s11p_kap_le_one n
  have h4 := D.hfw (n, α) x
  have h5 := D.w_nonneg (n, α)
  calc s11p_kap n * |r2CosBasis T n t| * |D.f (n, α) x| ≤ (1 * Real.sqrt (2 / T)) * D.w (n, α) :=
        mul_le_mul (mul_le_mul h2 h1 (abs_nonneg _) zero_le_one) h4 (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem s11p_series_summable_w (D : S11pData d) (α : MultiIndex d) :
    Summable fun n : ℕ => D.w (n, α) :=
  D.hw.comp_injective (i := fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) (fun a b hab => by simpa using hab)

theorem s11p_term_summable (hT : 0 < T) (α : MultiIndex d) (t : ℝ) (x : Euc d) :
    Summable fun n : ℕ => ‖s11p_kap n * r2CosBasis T n t * D.f (n, α) x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact s11p_term_abs_le hT n α t x)
    ((s11p_series_summable_w D α).mul_left (Real.sqrt (2 / T)))

theorem s11p_U_continuous (hT : 0 < T) (hU : S11pSeries D T U) (α : MultiIndex d) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) : Continuous (U α t) := by
  have : U α t = fun x => ∑' n, s11p_kap n * r2CosBasis T n t * D.f (n, α) x :=
    funext fun x => (hU α t ht x).tsum_eq.symm
  rw [this]
  exact continuous_tsum (u := fun n : ℕ => Real.sqrt (2 / T) * D.w (n, α)) (fun n => continuous_const.mul (D.hfc _))
    ((s11p_series_summable_w D α).mul_left (Real.sqrt (2 / T))) fun n x => by
      rw [Real.norm_eq_abs]; exact s11p_term_abs_le hT n α t x

theorem s11p_U_bound (hT : 0 < T) (hU : S11pSeries D T U) (α : MultiIndex d) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ Cb : ℝ, ∀ x, |U α t x| ≤ Cb := by
  refine ⟨∑' n : ℕ, Real.sqrt (2 / T) * D.w (n, α), fun x => ?_⟩
  calc |U α t x| = ‖∑' n, s11p_kap n * r2CosBasis T n t * D.f (n, α) x‖ := by
        rw [(hU α t ht x).tsum_eq, Real.norm_eq_abs]
    _ ≤ ∑' n, ‖s11p_kap n * r2CosBasis T n t * D.f (n, α) x‖ :=
        norm_tsum_le_tsum_norm (s11p_term_summable hT α t x)
    _ ≤ _ := Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs]; exact s11p_term_abs_le hT n α t x)
        (s11p_term_summable hT α t x) ((s11p_series_summable_w D α).mul_left (Real.sqrt (2 / T)))

theorem s11p_mu_series (hT : 0 < T) (hU : S11pSeries D T U) (α : MultiIndex d) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasSum (fun n => s11p_kap n * r2CosBasis T n t * ∫ y, D.f (n, α) y ∂μ) (∫ y, U α t y ∂μ) := by
  set F : ℕ → Euc d → ℝ := fun n y => s11p_kap n * r2CosBasis T n t * D.f (n, α) y with hF
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    Integrable.of_bound (C := Real.sqrt (2 / T) * D.w (n, α))
      (continuous_const.mul (D.hfc _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact s11p_term_abs_le hT n α t y)
  have hsum : Summable fun n => ∫ y, ‖F n y‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_)
      ((s11p_series_summable_w D α).mul_left (Real.sqrt (2 / T)))
    calc ∫ y, ‖F n y‖ ∂μ ≤ ∫ _y, Real.sqrt (2 / T) * D.w (n, α) ∂μ :=
          integral_mono (hFi n).norm (integrable_const _) fun y => by
            rw [Real.norm_eq_abs]; exact s11p_term_abs_le hT n α t y
      _ = _ := by simp
  have h := integral_tsum_of_summable_integral_norm hFi hsum
  have hsum2 : Summable fun n => ∫ y, F n y ∂μ :=
    Summable.of_norm_bounded hsum (fun n => norm_integral_le_integral_norm _)
  have e1 : ∫ y, U α t y ∂μ = ∫ y, ∑' n, F n y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => (hU α t ht y).tsum_eq.symm)
  have e2 : (fun n => s11p_kap n * r2CosBasis T n t * ∫ y, D.f (n, α) y ∂μ) = fun n => ∫ y, F n y ∂μ := by
    funext n
    simp only [hF]
    rw [integral_const_mul]
  rw [e2, e1, ← h]
  exact hsum2.hasSum

theorem s11p_tsum_vec (hT : 0 < T) (z : s11p_K d) (t : ℝ) (α : MultiIndex d) :
    ∑' q, (s11p_vec hT t α).c q * z.c q =
      (s11p_cJ T)⁻¹ * ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * z.c (n, α) := by
  classical
  have hinj : Function.Injective (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) := fun a b hab => by simpa using hab
  have hsupp : Function.support (fun q : ℕ × MultiIndex d => (s11p_vec hT t α).c q * z.c q) ⊆
      Set.range (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) := by
    intro q hq
    by_contra hqr
    apply hq
    have : q.2 ≠ α := fun h => hqr ⟨q.1, Prod.ext rfl h.symm⟩
    simp [s11p_vec, s11p_K.c_mk, this]
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [s11p_vec, s11p_K.c_mk, ite_true]
  ring

theorem s11p_inner_vec_Y (hT : 0 < T) (hU : S11pSeries D T U) (α : MultiIndex d) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    inner ℝ (s11p_vec hT t α) (D.Y μ (s11p_cJ T) x) = U α t x - ∫ y, U α t y ∂μ := by
  rw [s11p_K.inner_eq, s11p_tsum_vec hT]
  have hc := (s11p_cJ_pos T).ne'
  have e : ∀ n : ℕ, s11p_kap n * r2CosBasis T n t * (D.Y μ (s11p_cJ T) x).c (n, α) =
      s11p_cJ T * (s11p_kap n * r2CosBasis T n t * D.f (n, α) x -
        s11p_kap n * r2CosBasis T n t * ∫ y, D.f (n, α) y ∂μ) := by
    intro n; rw [D.Y_c]; ring
  simp_rw [e]
  rw [tsum_mul_left, ((hU α t ht x).sub (s11p_mu_series μ hT hU α t ht)).tsum_eq]
  field_simp

theorem s11p_susc (g : Euc d → ℝ) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    (φ : Euc d → ℝ) :
    susceptibilityCov g μ 0 φ ψ = ∫ x, (φ x - ∫ y, φ y ∂μ) * (ψ x - ∫ y, ψ y ∂μ) ∂μ := by
  have h := s11iid_resp_ae μ g hψc hC
  unfold susceptibilityCov l2Inner
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]
  simp [projMean, pair]

/-- Second moments of a Gaussian on `K` against the covariance of `Y#μ`. -/
theorem s11p_gauss_pair (c0 : ℝ) (G : Measure (s11p_K d)) [IsProbabilityMeasure G]
    (hg : HRS.IsCenteredGaussian G)
    (hcov : ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (D.Y μ c0)) x y) (a b : s11p_K d) :
    Integrable (fun z : s11p_K d => inner ℝ a z * inner ℝ b z) G ∧
      ∫ z, inner ℝ a z * inner ℝ b z ∂G =
        ∫ x, inner ℝ a (D.Y μ c0 x) * inner ℝ b (D.Y μ c0 x) ∂μ := by
  haveI := hg.1
  have hcont := D.Y_continuous μ c0
  have hYae : AEMeasurable (D.Y μ c0) μ := hcont.aemeasurable
  have hYL : MemLp (D.Y μ c0) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable (D.Cb c0) (Filter.Eventually.of_forall (D.norm_Y_le μ c0))
  have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
  have hn : Integrable (fun z : s11p_K d => ‖z‖ ^ 2) G := by
    have := hmem.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hint : Integrable (fun F : s11p_K d => inner ℝ a F * inner ℝ b F) G := by
    refine (hn.const_mul (‖a‖ * ‖b‖)).mono' ?_ (Filter.Eventually.of_forall fun F => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a F‖ * ‖inner ℝ b F‖ ≤ (‖a‖ * ‖F‖) * (‖b‖ * ‖F‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
              (by positivity)
        _ = ‖a‖ * ‖b‖ * ‖F‖ ^ 2 := by ring
  refine ⟨hint, ?_⟩
  have h1 : ∫ F, inner ℝ a F * inner ℝ b F ∂G = covarianceBilin G a b := by
    rw [covarianceBilin_apply hmem, HRS.HilbertCLTAux.gaussian_mean_zero hg]
    simp
  have hmemY : MemLp id 2 (μ.map (D.Y μ c0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hYae).mpr hYL
  have hmean : (μ.map (D.Y μ c0))[id] = 0 := by
    show ∫ z, id z ∂(μ.map (D.Y μ c0)) = 0
    rw [integral_map hYae aestronglyMeasurable_id]
    exact D.Y_integral_zero μ c0
  have h2 : covarianceBilin (μ.map (D.Y μ c0)) a b =
      ∫ x, inner ℝ a (D.Y μ c0 x) * inner ℝ b (D.Y μ c0 x) ∂μ := by
    rw [covarianceBilin_apply hmemY, hmean]
    simp only [sub_zero]
    rw [integral_map hYae (by fun_prop)]
  rw [h1, hcov, h2]

end Pair

end HRS.Whole
