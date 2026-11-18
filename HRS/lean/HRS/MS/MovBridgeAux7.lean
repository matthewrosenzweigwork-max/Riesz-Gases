import HRS.MS.MovBridgeAux6

/-!
# MOVA3C, part 1: Hermite span inside the Schwartz space, the word norm, and `B3` (`C_b^N` multipliers on `Σ^s`)

Namespace `HRS.MS.MovOsc`, helpers `mova3c_`.  Infrastructure for S6.1 (not manuscript rows).

* `mova3c_hspan_schwartz`: every element of `mo_Hspan d` is (the coercion of) a Schwartz map.  Proof: the
  Gaussian is Schwartz (decay of iterated derivatives by induction from `fderiv G = G • (-innerSL)`), and
  `h_{α+e_j} = (2√((α_j+1)/2))⁻¹ (x_j - ∂_j) h_α`.
* `mova3c_dual_ext`: the duality extension.  If `T'` is the formal adjoint of `T` and `‖T' g‖_{Σ^σ} ≤ B ‖g‖_{Σ^σ}`
  on the Hermite span, then `‖T f‖_{Σ^{-σ}} ≤ B ‖f‖_{Σ^{-σ}}` for every `f ∈ Σ^{-σ}` (with `T f ∈ L²`).
* `mova3c_W_mult`, `mova3c_int_endpoint`: the integer endpoint `‖θ w‖_{Σ^n} ≤ C A ‖w‖_{Σ^n}` for Schwartz `w`,
  by induction on the word norm `mova1_W` (`G_j (θ w) = θ G_j w + (∂_j θ) w`).
* `mova3c_interp_span`, `mova3c_span_bound`: the real index `0 ≤ σ ≤ N` on the Hermite span by `mo_interp_osc`.
* `mo_mult_cb` (**B3**): for real `s` with `|s| ≤ N`, `θ` smooth of temperate growth (qualitative only) with
  all coordinate partial derivatives of order `≤ N` bounded by `A` (`mova3b2_Q N 0 A θ`) and every
  `f ∈ Σ^s`: `θ f ∈ Σ^s` and `‖θ f‖_{Σ^s} ≤ C A ‖f‖_{Σ^s}`, `C = C(d, s, N)`.  `mo_mult_memCb` is the form
  with `HRS.MemCb N θ`, `A = HRS.cbNorm N θ`.

Adjustment relative to the sketch (harmless): the multiplier carries the qualitative hypothesis
`θ.HasTemperateGrowth` (as in `mo_bridge2`), so that `θ w` is Schwartz for Schwartz `w`; constants never
depend on it.  The hypothesis is automatic for `C_b^∞` multipliers.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole HRS.MS.MovInterp

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ## The Gaussian is a Schwartz function -/

/-- `x ↦ e^{-‖x‖²/2}`. -/
def mova3c_G (x : Euc d) : ℝ := Real.exp (-(‖x‖ ^ 2 / 2))

lemma mova3c_G_contDiff : ContDiff ℝ ∞ (mova3c_G : Euc d → ℝ) := by
  unfold mova3c_G
  exact Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const 2).neg

/-- The continuous linear map `x ↦ -⟪x, ·⟫`. -/
def mova3c_L : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
  -(isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap

/-- `∇ G = G • (-x)`. -/
lemma mova3c_fderiv_G (x : Euc d) :
    fderiv ℝ (mova3c_G : Euc d → ℝ) x = mova3c_G x • mova3c_L x := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := (h1.const_mul (-(1 / 2 : ℝ))).exp
  have e : (mova3c_G : Euc d → ℝ) = fun y => Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2) := by
    funext y; simp only [mova3c_G]; congr 1; ring
  have h3 : HasFDerivAt (mova3c_G : Euc d → ℝ) (mova3c_G x • mova3c_L x) x := by
    rw [e]
    convert h2 using 1
    ext y
    have : (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap x y = inner ℝ x y :=
      rfl
    simp only [mova3c_L, e, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, this,
      smul_eq_mul, innerSL_apply_apply, nsmul_eq_mul]
    ring_nf
  exact h3.fderiv

/-- The scalar bound `(1+t)^k e^{-t²/2} ≤ C`. -/
lemma mova3c_gauss_scalar (k : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    (1 + t) ^ k * Real.exp (-(t ^ 2 / 2)) ≤ C := by
  refine ⟨2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ)), fun t ht => ?_⟩
  have he : 0 < Real.exp (-(t ^ 2 / 2)) := Real.exp_pos _
  have he1 : Real.exp (-(t ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    calc (1 + t) ^ k * Real.exp (-(t ^ 2 / 2)) ≤ 2 ^ k * 1 :=
          mul_le_mul h1 he1 he.le (by positivity)
      _ ≤ _ := by
          rw [mul_one]
          have : (0 : ℝ) ≤ 2 ^ k * (k.factorial : ℝ) := by positivity
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  · have h1 : (1 + t) ^ k ≤ 2 ^ k * t ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) k
    have h2 : t ^ k ≤ t ^ (2 * k) := pow_le_pow_right₀ h (by omega)
    have h3 : (t ^ 2 / 2) ^ k / k.factorial ≤ Real.exp (t ^ 2 / 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) k
    have h4 : t ^ (2 * k) ≤ 2 ^ k * k.factorial * Real.exp (t ^ 2 / 2) := by
      have : t ^ (2 * k) = 2 ^ k * (t ^ 2 / 2) ^ k := by
        rw [pow_mul, div_pow]; field_simp
      rw [this]
      have h5 : (t ^ 2 / 2) ^ k ≤ k.factorial * Real.exp (t ^ 2 / 2) := by
        rwa [div_le_iff₀ hfac, mul_comm] at h3
      calc 2 ^ k * (t ^ 2 / 2) ^ k ≤ 2 ^ k * (k.factorial * Real.exp (t ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = _ := by ring
    have hex : Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 + t) ^ k * Real.exp (-(t ^ 2 / 2))
        ≤ (2 ^ k * (2 ^ k * k.factorial * Real.exp (t ^ 2 / 2))) * Real.exp (-(t ^ 2 / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ he.le
          calc (1 + t) ^ k ≤ 2 ^ k * t ^ k := h1
            _ ≤ 2 ^ k * t ^ (2 * k) := mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2 ^ k * (2 ^ k * k.factorial) * (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2))) := by ring
      _ = 2 ^ k * (2 ^ k * k.factorial) := by rw [hex, mul_one]
      _ ≤ _ := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- Decay of all iterated derivatives of the Gaussian (induction on the order). -/
lemma mova3c_G_decay (n : ℕ) : ∀ k : ℕ, ∃ C : ℝ, ∀ i ≤ n, ∀ x : Euc d,
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i (mova3c_G : Euc d → ℝ) x‖ ≤ C := by
  induction n with
  | zero =>
    intro k
    obtain ⟨C, hC⟩ := mova3c_gauss_scalar k
    refine ⟨C, fun i hi x => ?_⟩
    have : i = 0 := by omega
    subst this
    rw [norm_iteratedFDeriv_zero]
    unfold mova3c_G
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hC ‖x‖ (norm_nonneg _)
  | succ n ih =>
    intro k
    obtain ⟨l, C0, hC0, hL⟩ := (mova3c_L (d := d)).hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
    obtain ⟨C1, hC1⟩ := ih (k + l)
    obtain ⟨C2, hC2⟩ := ih k
    refine ⟨max C2 (2 ^ n * C0 * C1), fun i hi x => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (hC2 i (by omega) x).trans (le_max_left _ _)
    · have hi' : i = n + 1 := by omega
      subst hi'
      have hfd : fderiv ℝ (mova3c_G : Euc d → ℝ) = fun y => mova3c_G y • mova3c_L y :=
        funext mova3c_fderiv_G
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      have hsm := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := (n : ℕ∞ω))
        (f := (mova3c_G : Euc d → ℝ)) (g := fun y => mova3c_L y)
        (mova3c_G_contDiff.of_le (by exact_mod_cast le_top))
        ((mova3c_L (d := d)).contDiff.of_le (by exact_mod_cast le_top)) x le_rfl
      have hpos : (0 : ℝ) ≤ (1 + ‖x‖) ^ k := by positivity
      calc (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (fun y => mova3c_G y • mova3c_L y) x‖
          ≤ (1 + ‖x‖) ^ k * ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (mova3c_G : Euc d → ℝ) x‖ * (C0 * (1 + ‖x‖) ^ l) := by
            refine mul_le_mul_of_nonneg_left (hsm.trans (sum_le_sum fun i hi => ?_)) hpos
            exact mul_le_mul_of_nonneg_left (hL (n - i) (Nat.sub_le _ _) x) (by positivity)
        _ = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * C0 *
              ((1 + ‖x‖) ^ (k + l) * ‖iteratedFDeriv ℝ i (mova3c_G : Euc d → ℝ) x‖) := by
            rw [mul_sum]
            refine sum_congr rfl fun i _ => ?_
            rw [pow_add]; ring
        _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * C0 * C1 := by
            refine sum_le_sum fun i hi => ?_
            exact mul_le_mul_of_nonneg_left (hC1 i (by have := mem_range.1 hi; omega) x)
              (by positivity)
        _ = 2 ^ n * C0 * C1 := by
            rw [← sum_mul, ← sum_mul]
            have : ∑ i ∈ range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
              exact_mod_cast Nat.sum_range_choose n
            rw [this]
        _ ≤ _ := le_max_right _ _

/-- The Gaussian as a Schwartz map. -/
def mova3c_Gs : 𝓢R where
  toFun := mova3c_G
  smooth' := mova3c_G_contDiff
  decay' k n := by
    obtain ⟨C, hC⟩ := mova3c_G_decay (d := d) n k
    refine ⟨C, fun x => ?_⟩
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (hC n le_rfl x)
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) k

@[simp] lemma mova3c_Gs_apply (x : Euc d) : (mova3c_Gs : 𝓢R) x = mova3c_G x := rfl

/-! ## Hermite functions are Schwartz -/

lemma mova3c_hermite_zero (x : Euc d) :
    hermiteFunD (0 : MultiIndex d) x = hermiteConst 0 ^ d * mova3c_G x := by
  have h1 : ∀ y : ℝ, hermiteFun 0 y = hermiteConst 0 * gauss y := by
    intro y
    rw [hermiteFun_eq]
    simp [hermitePoly]
  unfold hermiteFunD
  simp only [Pi.zero_apply, h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  unfold gauss mova3c_G
  rw [← Real.exp_sum, EuclideanSpace.norm_sq_eq]
  congr 1
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  simp [sq_abs]

lemma mova3c_hermite_schwartz : ∀ (n : ℕ) (α : MultiIndex d), MultiIndex.degree α = n →
    ∃ φ : 𝓢R, (⇑φ : Euc d → ℝ) = hermiteFunD α := by
  intro n
  induction n with
  | zero =>
    intro α hα
    rw [mova1_degree_eq_zero hα]
    refine ⟨(hermiteConst 0 ^ d) • mova3c_Gs, ?_⟩
    funext x
    rw [mova3c_hermite_zero]
    simp
  | succ n ih =>
    intro α hα
    obtain ⟨j, hj⟩ := mova1_exists_pos hα
    obtain ⟨φ, hφ⟩ := ih (mova1_dn j α) (by have := mova1_dn_degree j α hj; omega)
    have hup := mova1_up_dn j α hj
    set β := mova1_dn j α with hβ
    have hpos : 0 < Real.sqrt (((β j : ℝ) + 1) / 2) := Real.sqrt_pos.2 (by positivity)
    refine ⟨(2 * Real.sqrt (((β j : ℝ) + 1) / 2))⁻¹ • (mova1_X j φ - mova1_D j φ), ?_⟩
    funext x
    have hd : DifferentiableAt ℝ (hermiteFunD β) x :=
      ((contDiff_hermiteFunD β).differentiable (by simp)) x
    have e1 := mova1_x_hD β j x
    have e2 := congrFun (mova3b1_Dj_hermite β j) x
    have e3 : fderiv ℝ (hermiteFunD β) x (EuclideanSpace.single j (1 : ℝ)) =
        mova3b1_Dj j (hermiteFunD β) x := rfl
    simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, mova1_X_apply, mova1_D_apply, hφ,
      smul_eq_mul]
    rw [e3, e2, e1, ← hup]
    field_simp
    ring

lemma mova3c_hspan_schwartz {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) :
    ∃ φ : 𝓢R, (⇑φ : Euc d → ℝ) = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, rfl⟩ := hf
    exact mova3c_hermite_schwartz _ α rfl
  | zero => exact ⟨0, rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, rfl⟩ := hg
    exact ⟨φ + ψ, rfl⟩
  | smul a f _ hf =>
    obtain ⟨φ, rfl⟩ := hf
    exact ⟨a • φ, rfl⟩

/-! ## Duality extension -/

/-- **Duality extension.**  Let `T'` be the formal adjoint of `T` (`∫ (T f) g = ∫ f (T' g)` for `f, g ∈ L²`),
with `T` mapping `L²` to `L²`, and suppose `‖T' g‖_{Σ^σ} ≤ B ‖g‖_{Σ^σ}` for every finite Hermite sum `g`.
Then `‖T f‖_{Σ^{-σ}} ≤ B ‖f‖_{Σ^{-σ}}` for every `f ∈ Σ^{-σ}` (and `T f ∈ Σ^{-σ}`). -/
theorem mova3c_dual_ext (σ : ℝ) {T T' : (Euc d → ℝ) → (Euc d → ℝ)} {B : ℝ} (hB0 : 0 ≤ B)
    (hT2 : ∀ f, MemLp f 2 (volume : Measure (Euc d)) → MemLp (T f) 2 (volume : Measure (Euc d)))
    (hadj : ∀ f g, MemLp f 2 (volume : Measure (Euc d)) → MemLp g 2 (volume : Measure (Euc d)) →
      ∫ x, T f x * g x = ∫ x, f x * T' g x)
    (hB : ∀ g ∈ mo_Hspan d, MemOsc σ (T' g) ∧ oscNorm σ (T' g) ≤ B * oscNorm σ g) :
    ∀ f, MemOsc (-σ) f → MemOsc (-σ) (T f) ∧ oscNorm (-σ) (T f) ≤ B * oscNorm (-σ) f := by
  intro f hf
  refine mo_memOsc_neg_of_dual_bdd σ (hT2 f hf.1) (M := B * oscNorm (-σ) f) ?_
  rintro t ⟨S, a, hg, rfl⟩
  have hmem : mo_hsum S a ∈ mo_Hspan d := mova3_comb_mem S a
  rw [hadj f _ hf.1 (mova2_hsum_memLp S a)]
  have h0 : 0 ≤ oscNorm (-σ) f := Real.sqrt_nonneg _
  calc |∫ x, f x * T' (mo_hsum S a) x|
      ≤ oscNorm (-σ) f * oscNorm σ (T' (mo_hsum S a)) := mo_dual_le σ hf (hB _ hmem).1
    _ ≤ oscNorm (-σ) f * (B * oscNorm σ (mo_hsum S a)) :=
        mul_le_mul_of_nonneg_left (hB _ hmem).2 h0
    _ ≤ oscNorm (-σ) f * (B * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hB0) h0
    _ = B * oscNorm (-σ) f := by ring

/-! ## The word norm -/

lemma mova3c_W_smul : ∀ (n : ℕ) (c : ℝ) (w : 𝓢R), mova1_W n (c • w) = |c| * mova1_W n w := by
  intro n
  induction n with
  | zero => intro c w; exact mova1_n2_smul c w
  | succ n ih =>
    intro c w
    show mova1_W n (c • w) + ∑ j : Fin d, mova1_W n (mova1_X j (c • w) + mova1_D j (c • w)) =
      |c| * (mova1_W n w + ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w))
    have : ∀ j : Fin d, mova1_X j (c • w) + mova1_D j (c • w) = c • (mova1_X j w + mova1_D j w) := by
      intro j; rw [map_smul, map_smul, smul_add]
    simp_rw [this, ih]
    rw [mul_add, Finset.mul_sum]

lemma mova3c_W_le_osc (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : 𝓢R, mova1_W n w ≤ K * oscNorm (n : ℝ) w := by
  obtain ⟨K1, hK1, h1⟩ := mova1_W_le (d := d) n 0 (fun f : 𝓢R => f) mova1_low_id
  obtain ⟨Cu, hCu, hu⟩ := mova1_upper (d := d) n
  refine ⟨K1 * Cu, mul_nonneg hK1 hCu, fun w => ?_⟩
  calc mova1_W n w ≤ K1 * mo_S (n + 0) w := h1 w
    _ ≤ K1 * (Cu * oscNorm (n : ℝ) w) := by
        rw [Nat.add_zero]; exact mul_le_mul_of_nonneg_left (hu w) hK1
    _ = _ := by ring

lemma mova3c_W_mono (n : ℕ) (w : 𝓢R) : mova1_W n w ≤ mova1_W (n + 1) w := by
  show mova1_W n w ≤ mova1_W n w + ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w)
  have : 0 ≤ ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w) :=
    Finset.sum_nonneg fun j _ => mova1_W_nonneg n _
  linarith

/-- Leibniz rule for `x_j + ∂_j` with the multiplier on the left. -/
lemma mova3c_G_bsm (j : Fin d) {b : Euc d → ℝ} (hb : b.HasTemperateGrowth) (w : 𝓢R) :
    mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w) =
      mova3b2_bsm b (mova1_X j w + mova1_D j w) + mova3b2_bsm (mova3b1_Dj j b) w := by
  ext x
  have hf : (⇑(mova3b2_bsm b w) : Euc d → ℝ) = fun x => b x * w x :=
    funext (mova3b2_bsm_apply hb w)
  have h1 : DifferentiableAt ℝ b x := (hb.1.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ w x := w.differentiableAt
  simp only [SchwartzMap.add_apply, mova1_X_apply, mova1_D_apply, hf,
    mova3b2_bsm_apply hb, mova3b2_bsm_apply (mova3b2_tg_Dj j hb)]
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have : mova3b1_Dj j b x = fderiv ℝ b x (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [this]; ring

/-- The word norm of `θ w`, `θ` with all coordinate derivatives of order `≤ n` bounded by `A`. -/
theorem mova3c_W_mult (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ),
    b.HasTemperateGrowth → mova3b2_Q n 0 A b → ∀ w : 𝓢R,
      mova1_W n (mova3b2_bsm b w) ≤ C * A * mova1_W n w := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun A hA b hb hQ w => ?_⟩
    have := mova3b2_W_zero_mult hA hb hQ w
    rw [← mova3b2_hn_zero] at this
    simpa [mova1_W] using this
  | succ n ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    refine ⟨((d : ℝ) + 1) * C, by positivity, fun A hA b hb hQ w => ?_⟩
    have hQn : mova3b2_Q n 0 A b := mova3b2_Q_mono_K (Nat.le_succ n) hQ
    have hWn := mova3c_W_mono n w
    have hW0 : 0 ≤ mova1_W n w := mova1_W_nonneg n w
    have T1 : mova1_W n (mova3b2_bsm b w) ≤ C * A * mova1_W n w := hCb A hA b hb hQn w
    have T2 : ∀ j : Fin d, mova1_W n (mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w)) ≤
        C * A * mova1_W n (mova1_X j w + mova1_D j w) + C * A * mova1_W n w := by
      intro j
      rw [mova3c_G_bsm j hb w]
      refine (mova3b2_W_add n _ _).trans (add_le_add (hCb A hA b hb hQn _) ?_)
      exact hCb A hA _ (mova3b2_tg_Dj j hb) (hQ.2 j) w
    show mova1_W n (mova3b2_bsm b w) + ∑ j : Fin d,
      mova1_W n (mova1_X j (mova3b2_bsm b w) + mova1_D j (mova3b2_bsm b w)) ≤
        ((d : ℝ) + 1) * C * A * (mova1_W n w + ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w))
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => T2 j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hS0 : 0 ≤ ∑ j : Fin d, mova1_W n (mova1_X j w + mova1_D j w) :=
      Finset.sum_nonneg fun j _ => mova1_W_nonneg n _
    have hCA : 0 ≤ C * A := mul_nonneg hC hA
    nlinarith [mul_nonneg hCA hS0, mul_nonneg hCA hW0, mul_nonneg hCA (Nat.cast_nonneg d : (0 : ℝ) ≤ d),
      mul_nonneg (mul_nonneg hCA (Nat.cast_nonneg d : (0 : ℝ) ≤ d)) hW0]

/-! ## The integer endpoint -/

/-- **Integer endpoint of `B3`.**  `‖θ w‖_{Σ^n} ≤ C A ‖w‖_{Σ^n}` for Schwartz `w`, `θ` smooth of temperate
growth with all coordinate partial derivatives of order `≤ n` bounded by `A`; `C = C(d, n)`. -/
theorem mova3c_int_endpoint (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ),
    b.HasTemperateGrowth → mova3b2_Q n 0 A b → ∀ w : 𝓢R,
      MemOsc (n : ℝ) (fun x => b x * w x) ∧
        oscNorm (n : ℝ) (fun x => b x * w x) ≤ C * A * oscNorm (n : ℝ) w := by
  obtain ⟨C1, hC1, h1⟩ := mova3c_W_mult (d := d) n
  obtain ⟨C2, hC2, h2⟩ := mova1_lower_W (d := d) n
  obtain ⟨K, hK, h3⟩ := mova3c_W_le_osc (d := d) n
  refine ⟨C2 * C1 * K, by positivity, fun A hA b hb hQ w => ?_⟩
  have hf : (fun x => b x * w x) = ⇑(mova3b2_bsm b w) := (funext (mova3b2_bsm_apply hb w)).symm
  rw [hf]
  refine ⟨memOsc_schwartz _ _, ?_⟩
  calc oscNorm (n : ℝ) (⇑(mova3b2_bsm b w)) ≤ C2 * mova1_W n (mova3b2_bsm b w) := h2 _
    _ ≤ C2 * (C1 * A * mova1_W n w) := mul_le_mul_of_nonneg_left (h1 A hA b hb hQ w) hC2
    _ ≤ C2 * (C1 * A * (K * oscNorm (n : ℝ) w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h3 w) (mul_nonneg hC1 hA)) hC2
    _ = _ := by ring

/-! ## Interpolation between integer indices on the Hermite span -/

/-- `mo_interp_osc` between the integers `k` and `k+1`, with the geometric mean bounded by the maximum. -/
lemma mova3c_interp_span {T : (Euc d → ℝ) → (Euc d → ℝ)}
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {k : ℕ} {M0 M1 : ℝ}
    (h0 : ∀ f ∈ mo_Hspan d, MemOsc (k : ℝ) (T f) ∧ oscNorm (k : ℝ) (T f) ≤ M0 * oscNorm (k : ℝ) f)
    (h1 : ∀ f ∈ mo_Hspan d, MemOsc ((k + 1 : ℕ) : ℝ) (T f) ∧
      oscNorm ((k + 1 : ℕ) : ℝ) (T f) ≤ M1 * oscNorm ((k + 1 : ℕ) : ℝ) f)
    {σ : ℝ} (hσ0 : (k : ℝ) ≤ σ) (hσ1 : σ ≤ (k : ℝ) + 1) :
    ∀ f ∈ mo_Hspan d, MemOsc σ (T f) ∧ oscNorm σ (T f) ≤ max M0 M1 * oscNorm σ f := by
  have : Nonempty (MultiIndex d) := ⟨fun _ => 0⟩
  have hM0 : 0 ≤ M0 := mova3_nonneg_of_bound h0
  have hM1 : 0 ≤ M1 := mova3_nonneg_of_bound h1
  intro f hf
  set θ : ℝ := σ - k with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hT := mo_interp_osc hlin hL2 (r0 := (k : ℝ)) (r1 := ((k + 1 : ℕ) : ℝ)) (s0 := (k : ℝ))
    (s1 := ((k + 1 : ℕ) : ℝ)) h0 h1 (θ := θ) ⟨hθ0, hθ1⟩ f hf
  have hσ : (1 - θ) * (k : ℝ) + θ * ((k + 1 : ℕ) : ℝ) = σ := by
    rw [hθ]; push_cast; ring
  rw [hσ] at hT
  refine ⟨hT.1, hT.2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  set m := max M0 M1 with hm
  have hm0 : 0 ≤ m := le_trans hM0 (le_max_left _ _)
  calc M0 ^ (1 - θ) * M1 ^ θ ≤ m ^ (1 - θ) * m ^ θ :=
        mul_le_mul (Real.rpow_le_rpow hM0 (le_max_left _ _) (by linarith))
          (Real.rpow_le_rpow hM1 (le_max_right _ _) hθ0) (Real.rpow_nonneg hM1 _)
          (Real.rpow_nonneg hm0 _)
    _ = m := by
        rw [← Real.rpow_add' hm0 (by linarith : (1 - θ) + θ ≠ 0)]; simp

/-- **`B3` on the Hermite span**, real index `0 ≤ σ ≤ N`. -/
theorem mova3c_span_bound (σ : ℝ) (hσ : 0 ≤ σ) (N : ℕ) (hN : σ ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (b : Euc d → ℝ), b.HasTemperateGrowth →
      mova3b2_Q N 0 A b → ∀ f ∈ mo_Hspan d,
        MemOsc σ (fun x => b x * f x) ∧
          oscNorm σ (fun x => b x * f x) ≤ C * A * oscNorm σ f := by
  set n0 : ℕ := ⌊σ⌋₊ with hn0
  have hn0s : (n0 : ℝ) ≤ σ := Nat.floor_le hσ
  by_cases hint : (n0 : ℝ) = σ
  · obtain ⟨C0, hC0, h0⟩ := mova3c_int_endpoint (d := d) n0
    refine ⟨C0, hC0, fun A hA b hb hQ f hf => ?_⟩
    have hn0N : n0 ≤ N := by exact_mod_cast hint.le.trans hN
    obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
    rw [← hint]
    exact h0 A hA b hb (mova3b2_Q_mono_K hn0N hQ) φ
  · have hlt : (n0 : ℝ) < σ := lt_of_le_of_ne hn0s hint
    have hn1N : n0 + 1 ≤ N := by
      have : (n0 : ℝ) < N := hlt.trans_le hN
      exact_mod_cast this
    have hs1 : σ < (n0 : ℝ) + 1 := Nat.lt_floor_add_one σ
    obtain ⟨C0, hC0, h0⟩ := mova3c_int_endpoint (d := d) n0
    obtain ⟨C1, hC1, h1⟩ := mova3c_int_endpoint (d := d) (n0 + 1)
    refine ⟨max C0 C1, le_trans hC0 (le_max_left _ _), fun A hA b hb hQ f hf => ?_⟩
    have hn0N : n0 ≤ N := by omega
    have hbA := fun x => mova3b2_Q_abs hQ x
    have hT := mova3c_interp_span (d := d) (T := fun f x => b x * f x)
      (fun f _ g _ c => by funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
      (fun f hf => mova3b2_mulL2 hb.1.continuous.measurable hbA (mova3_hspan_memLp hf))
      (k := n0) (M0 := C0 * A) (M1 := C1 * A)
      (fun f hf => by
        obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
        have := h0 A hA b hb (mova3b2_Q_mono_K hn0N hQ) φ
        exact ⟨this.1, by simpa [mul_assoc] using this.2⟩)
      (fun f hf => by
        obtain ⟨φ, rfl⟩ := mova3c_hspan_schwartz hf
        have := h1 A hA b hb (mova3b2_Q_mono_K hn1N hQ) φ
        exact ⟨this.1, by simpa [mul_assoc] using this.2⟩)
      hn0s hs1.le f hf
    refine ⟨hT.1, hT.2.trans (le_of_eq ?_)⟩
    rw [← max_mul_of_nonneg C0 C1 hA]

/-! ## `B3` for all real indices -/

lemma mova3c_mult_L2 {θ : Euc d → ℝ} (hθ : Measurable θ) {A : ℝ} (hA : ∀ x, |θ x| ≤ A)
    {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    MemLp (fun x => θ x * f x) 2 (volume : Measure (Euc d)) :=
  mova3b2_mulL2 hθ hA hf

/-- **`B3`: a `C_b^N` multiplier acts boundedly on `Σ^s`, every real `s` with `|s| ≤ N`.**
`C = C(d, s, N)`.  `θ` is smooth of temperate growth (qualitative only) and all coordinate partial
derivatives of order `≤ N` are bounded by `A` (`mova3b2_Q N 0 A θ`).  For every `f ∈ Σ^s`:
`θ f ∈ Σ^s` and `‖θ f‖_{Σ^s} ≤ C A ‖f‖_{Σ^s}`. -/
theorem mo_mult_cb (s : ℝ) (N : ℕ) (hs : |s| ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (θ : Euc d → ℝ), θ.HasTemperateGrowth →
      mova3b2_Q N 0 A θ → ∀ f : Euc d → ℝ, MemOsc s f →
        MemOsc s (fun x => θ x * f x) ∧
          oscNorm s (fun x => θ x * f x) ≤ C * A * oscNorm s f := by
  obtain ⟨C, hC, hspan⟩ := mova3c_span_bound (d := d) |s| (abs_nonneg s) N hs
  refine ⟨C, hC, fun A hA θ hθ hQ => ?_⟩
  have hbA := fun x => mova3b2_Q_abs hQ x
  have hmeas : Measurable θ := hθ.1.continuous.measurable
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  have hadj : ∀ f g : Euc d → ℝ, MemLp f 2 (volume : Measure (Euc d)) →
      MemLp g 2 (volume : Measure (Euc d)) →
      ∫ x, (fun x => θ x * f x) x * g x = ∫ x, f x * (fun x => θ x * g x) x := by
    intro f g _ _
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only []; ring)
  have hneg := mova3c_dual_ext (d := d) |s| (T := fun f x => θ x * f x) (T' := fun g x => θ x * g x)
    hCA (fun f hf => mova3c_mult_L2 hmeas hbA hf) hadj (fun g hg => hspan A hA θ hθ hQ g hg)
  have hpos := mova3c_dual_ext (d := d) (-|s|) (T := fun f x => θ x * f x) (T' := fun g x => θ x * g x)
    hCA (fun f hf => mova3c_mult_L2 hmeas hbA hf) hadj
    (fun g hg => hneg g (mova3b1_hspan_memOsc _ hg))
  rw [neg_neg] at hpos
  intro f hf
  rcases le_total 0 s with h | h
  · have hs' : |s| = s := abs_of_nonneg h
    rw [hs'] at hpos
    exact hpos f hf
  · have hs' : -|s| = s := by rw [abs_of_nonpos h]; ring
    rw [hs'] at hneg
    exact hneg f hf

/-- `B3` in the repository's `C_b^N` form: `HRS.MemCb N θ`, `A = HRS.cbNorm N θ`. -/
theorem mo_mult_memCb (s : ℝ) (N : ℕ) (hs : |s| ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Euc d → ℝ), θ.HasTemperateGrowth → HRS.MemCb N θ →
      ∀ f : Euc d → ℝ, MemOsc s f →
        MemOsc s (fun x => θ x * f x) ∧
          oscNorm s (fun x => θ x * f x) ≤ C * HRS.cbNorm N θ * oscNorm s f := by
  obtain ⟨C, hC, h⟩ := mo_mult_cb (d := d) s N hs
  refine ⟨C, hC, fun θ hθ hcb f hf => ?_⟩
  have hterm : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i θ x‖ ≤ HRS.cbNorm N θ := by
    intro i hi x
    unfold HRS.cbNorm
    have h1 : ‖iteratedFDeriv ℝ i θ x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ i θ z‖ :=
      le_ciSup (hcb.2 i hi) x
    have h2 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ i θ z‖) ≤
        ∑ k ∈ Finset.range (N + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ k θ z‖ :=
      Finset.single_le_sum (f := fun k => ⨆ z : Euc d, ‖iteratedFDeriv ℝ k θ z‖)
        (fun k _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
    exact h1.trans h2
  have hA : 0 ≤ HRS.cbNorm N θ :=
    Finset.sum_nonneg fun k _ => Real.iSup_nonneg fun z => norm_nonneg _
  have hQ : mova3b2_Q N 0 (HRS.cbNorm N θ) θ :=
    mova3b2_Q_of_iter hθ.1 fun k hk x => by simpa using hterm k hk x
  exact h (HRS.cbNorm N θ) hA θ hθ hQ f hf

end HRS.MS.MovOsc
