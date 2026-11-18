import HRS.Commutator.Whole.ExternalAuxMult4
import HRS.Commutator.Whole.RieszAux

/-!
# Dyadic pieces of a Fourier multiplier `(2π|ξ|)^s` applied to a Schwartz function (packet X-HLS, part 6)

For `f : ℝ^d → ℂ` smooth with rapidly decaying derivatives (the Fourier transform of a Schwartz
function), `s ∈ ℝ` and `j ∈ ℤ`, the piece `P^s_j = 𝓕⁻[(2π|ξ|)^s ρ(2^{-j}ξ) f(ξ)]`
(`ρ = χ - χ(2 ·)` supported in `1/2 ≤ |η| ≤ 2`) satisfies, uniformly in `j`,
`|P^s_j(x)| ≲ 2^{j(d+s)} (1+2^j|x|)^{-N} (1+2^j)^{-N}`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- The Fourier-side symbol of the piece. -/
def cmxHLS_sym (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (ξ : Euc d) : ℂ :=
  ((((2 * Real.pi * ‖ξ‖) ^ s * cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) : ℝ)) : ℂ) * f ξ

/-- The dyadic piece. -/
def cmxHLS_piece (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (x : Euc d) : ℂ := 𝓕⁻ (cmxHLS_sym s f j) x

/-- The rescaled symbol `θ_j(η) = (2π|η|)^s ρ(η) f(2^j η)`. -/
def cmxHLS_theta (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (η : Euc d) : ℂ :=
  ((((2 * Real.pi * ‖η‖) ^ s * cmxMY_rho η : ℝ)) : ℂ) * f (((2 : ℝ) ^ j) • η)

lemma cmxHLS_fourierInv_comp_smul (θ : Euc d → ℂ) {c : ℝ} (hc : 0 < c) (x : Euc d) :
    𝓕⁻ (fun ξ => θ (c⁻¹ • ξ)) x = ((c ^ d : ℝ)) • 𝓕⁻ θ (c • x) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  have h := cmxMY_fourier_comp_smul θ (c := c⁻¹) (inv_pos.2 hc) (-x)
  rw [h, inv_inv, inv_pow, inv_inv, smul_neg]

lemma cmxHLS_sym_eq (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (ξ : Euc d) :
    cmxHLS_sym s f j ξ = ((((2 : ℝ) ^ j) ^ s : ℝ) : ℂ) *
      cmxHLS_theta s f j ((((2 : ℝ) ^ j)⁻¹) • ξ) := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold cmxHLS_sym cmxHLS_theta
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have h1 : (2 * Real.pi * ‖ξ‖) ^ s =
      ((2 : ℝ) ^ j) ^ s * (2 * Real.pi * ‖((2 : ℝ) ^ j)⁻¹ • ξ‖) ^ s := by
    have : 2 * Real.pi * ‖ξ‖ = (2 : ℝ) ^ j * (2 * Real.pi * ‖((2 : ℝ) ^ j)⁻¹ • ξ‖) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
      field_simp
    rw [this, Real.mul_rpow hc.le (by positivity)]
  rw [h1]
  push_cast
  ring

lemma cmxHLS_piece_eq (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (x : Euc d) :
    cmxHLS_piece s f j x = ((((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d : ℝ) : ℂ) *
      𝓕⁻ (cmxHLS_theta s f j) (((2 : ℝ) ^ j) • x) := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold cmxHLS_piece
  have h1 : cmxHLS_sym s f j = fun ξ => ((((2 : ℝ) ^ j) ^ s : ℝ) : ℂ) *
      cmxHLS_theta s f j ((((2 : ℝ) ^ j)⁻¹) • ξ) := funext (cmxHLS_sym_eq s f j)
  rw [h1]
  have h2 : 𝓕⁻ (fun ξ : Euc d => ((((2 : ℝ) ^ j) ^ s : ℝ) : ℂ) *
      cmxHLS_theta s f j ((((2 : ℝ) ^ j)⁻¹) • ξ)) x =
      ((((2 : ℝ) ^ j) ^ s : ℝ) : ℂ) * 𝓕⁻ (fun ξ : Euc d => cmxHLS_theta s f j ((((2 : ℝ) ^ j)⁻¹) • ξ)) x := by
    simp only [Real.fourierInv_eq', smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    ring
  rw [h2, cmxHLS_fourierInv_comp_smul _ hc, Complex.real_smul]
  push_cast
  ring


/-- Iterated derivatives of a dilated function. -/
lemma cmxHLS_iter_scale {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℕ) (η : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y => f (c • y)) η‖ ≤ ‖iteratedFDeriv ℝ n f (c • η)‖ * |c| ^ n := by
  set g : Euc d →L[ℝ] Euc d := c • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hgy : ∀ y, g y = c • y := fun y => by simp [hg]
  have hfun : (fun y => f (c • y)) = f ∘ g := by funext y; simp [hgy]
  rw [hfun, g.iteratedFDeriv_comp_right hf η (by exact_mod_cast le_top), hgy]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  calc ‖g‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ := by rw [hg]; exact norm_smul_le c (ContinuousLinearMap.id ℝ (Euc d))
    _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ = |c| := by simp

/-- `g_s(η) = (2π|η|)^s ρ(η)`, a smooth function supported in `1/2 ≤ |η| ≤ 2`. -/
def cmxHLS_g (s : ℝ) (η : Euc d) : ℂ := ((((2 * Real.pi * ‖η‖) ^ s * cmxMY_rho η : ℝ)) : ℂ)

lemma cmxHLS_g_contDiff (s : ℝ) : ContDiff ℝ ∞ (cmxHLS_g s : Euc d → ℂ) := by
  refine cmxMY_contDiff_of_away_real (E := ℂ) (r := 1 / 2) (by norm_num) (fun η hη => ?_)
    (fun η hη => ?_)
  · unfold cmxHLS_g
    have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have h1 : ContDiffAt ℝ ∞ (fun η : Euc d => (2 * Real.pi * ‖η‖) ^ s) η :=
      ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (contDiffAt_norm ℝ hη))
        (by positivity)
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp η
      (h1.mul cmxMY_rho_contDiff.contDiffAt)
  · unfold cmxHLS_g
    rw [cmxMY_rho_eq_zero_of_le hη.le]; simp

lemma cmxHLS_g_supp (s : ℝ) (η : Euc d) (hη : 2 < ‖η‖) : cmxHLS_g s η = 0 := by
  unfold cmxHLS_g
  rw [cmxMY_rho_eq_zero_of_ge hη.le]; simp

lemma cmxHLS_theta_eq (s : ℝ) (f : Euc d → ℂ) (j : ℤ) :
    cmxHLS_theta s f j = fun η => cmxHLS_g s η * f (((2 : ℝ) ^ j) • η) := rfl

lemma cmxHLS_theta_contDiff {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ) (j : ℤ) :
    ContDiff ℝ ∞ (cmxHLS_theta s f j) := by
  rw [cmxHLS_theta_eq]
  exact (cmxHLS_g_contDiff s).mul (hf.comp (contDiff_const_smul _))

lemma cmxHLS_theta_supp (f : Euc d → ℂ) (s : ℝ) (j : ℤ) (η : Euc d) (hη : 2 < ‖η‖) :
    cmxHLS_theta s f j η = 0 := by
  rw [cmxHLS_theta_eq]; simp only [cmxHLS_g_supp s η hη, zero_mul]


lemma cmxHLS_g_deriv_zero (s : ℝ) (i : ℕ) (η : Euc d) (hη : ‖η‖ < 1 / 2) :
    iteratedFDeriv ℝ i (cmxHLS_g s : Euc d → ℂ) η = 0 := by
  by_contra h
  have hsub : tsupport (cmxHLS_g s : Euc d → ℂ) ⊆ {η : Euc d | 1 / 2 ≤ ‖η‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro y hy
    by_contra h'
    have h'' : ‖y‖ < 1 / 2 := by simpa using h'
    apply hy
    unfold cmxHLS_g
    rw [cmxMY_rho_eq_zero_of_le h''.le]; simp
  have := hsub (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i (subset_closure h))
  simp only [mem_setOf_eq] at this
  linarith

lemma cmxHLS_theta_deriv {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f)
    (hdec : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n f ξ‖ ≤ C)
    (s : ℝ) (n N' : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (η : Euc d),
      (1 + (2 : ℝ) ^ j) ^ N' * ‖iteratedFDeriv ℝ n (cmxHLS_theta s f j) η‖ ≤ C := by
  choose G hG0 hG using fun i => cmxMY_bdd_deriv (cmxHLS_g s : Euc d → ℂ) (cmxHLS_g_contDiff s)
    (cmxHLS_g_supp s) i
  choose Cf hCf0 hCf using fun m => hdec m (N' + n)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * G i * (2 ^ (N' + n) * Cf (n - i)),
    Finset.sum_nonneg fun i _ => by have := hG0 i; have := hCf0 (n - i); positivity, fun j η => ?_⟩
  set c : ℝ := (2 : ℝ) ^ j with hcdef
  have hc : 0 < c := zpow_pos (by norm_num) j
  have hmul := norm_iteratedFDeriv_mul_le (cmxHLS_g_contDiff s) (hf.comp (contDiff_const_smul c)) η
    (n := n) (by exact_mod_cast le_top)
  rw [cmxHLS_theta_eq]
  calc (1 + c) ^ N' * ‖iteratedFDeriv ℝ n (fun y => cmxHLS_g s y * f (c • y)) η‖
      ≤ (1 + c) ^ N' * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cmxHLS_g s) η‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖ := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (1 + c) ^ N' * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cmxHLS_g s) η‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  by_cases hη : ‖η‖ < 1 / 2
  · rw [cmxHLS_g_deriv_zero s i η hη]
    simp only [norm_zero, mul_zero, zero_mul]
    have := hG0 i; have := hCf0 (n - i); positivity
  · have hη' : 1 / 2 ≤ ‖η‖ := not_lt.1 hη
    have h1 : ‖iteratedFDeriv ℝ i (cmxHLS_g s) η‖ ≤ G i := hG i η
    have h2 := cmxHLS_iter_scale hf c (n - i) η
    have h3 := hCf (n - i) (c • η)
    have h4 : (1 + c) / 2 ≤ 1 + ‖c • η‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]; nlinarith
    have h5 : (1 + c) ^ (N' + n) ≤ 2 ^ (N' + n) * (1 + ‖c • η‖) ^ (N' + n) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h6 : c ^ (n - i) ≤ (1 + c) ^ n := by
      calc c ^ (n - i) ≤ (1 + c) ^ (n - i) := pow_le_pow_left₀ hc.le (by linarith) _
        _ ≤ (1 + c) ^ n := pow_le_pow_right₀ (by linarith) (by omega)
    have hnn : 0 ≤ ‖iteratedFDeriv ℝ (n - i) f (c • η)‖ := norm_nonneg _
    have h7 : (1 + c) ^ N' * ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖ ≤
        2 ^ (N' + n) * Cf (n - i) := by
      calc (1 + c) ^ N' * ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖
          ≤ (1 + c) ^ N' * (‖iteratedFDeriv ℝ (n - i) f (c • η)‖ * c ^ (n - i)) := by
            rw [abs_of_pos hc] at h2; gcongr
        _ ≤ (1 + c) ^ N' * (‖iteratedFDeriv ℝ (n - i) f (c • η)‖ * (1 + c) ^ n) := by gcongr
        _ = (1 + c) ^ (N' + n) * ‖iteratedFDeriv ℝ (n - i) f (c • η)‖ := by rw [pow_add]; ring
        _ ≤ (2 ^ (N' + n) * (1 + ‖c • η‖) ^ (N' + n)) * ‖iteratedFDeriv ℝ (n - i) f (c • η)‖ := by
            gcongr
        _ = 2 ^ (N' + n) * ((1 + ‖c • η‖) ^ (N' + n) * ‖iteratedFDeriv ℝ (n - i) f (c • η)‖) := by ring
        _ ≤ 2 ^ (N' + n) * Cf (n - i) := by gcongr
    calc (1 + c) ^ N' * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cmxHLS_g s) η‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖)
        = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cmxHLS_g s) η‖ *
          ((1 + c) ^ N' * ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖) := by ring
      _ ≤ (n.choose i : ℝ) * G i * (2 ^ (N' + n) * Cf (n - i)) := by
          have hGi := hG0 i
          have hX : 0 ≤ (1 + c) ^ N' * ‖iteratedFDeriv ℝ (n - i) (fun y => f (c • y)) η‖ := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h7 hX (by positivity)


lemma cmxHLS_theta_decay {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f)
    (hdec : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n f ξ‖ ≤ C)
    (s : ℝ) (N N' : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (j : ℤ) (y : Euc d),
      (1 + (2 : ℝ) ^ j) ^ N' * (‖𝓕⁻ (cmxHLS_theta s f j) y‖ * (1 + ‖y‖) ^ N) ≤ M := by
  choose C hC0 hC using fun i => cmxHLS_theta_deriv hf hdec s i N'
  set V : ℝ := (volume (closedBall (0 : Euc d) 2)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have key : ∀ (n : ℕ) (j : ℤ) (y : Euc d), (1 + (2 : ℝ) ^ j) ^ N' * (‖y‖ ^ n * ‖𝓕⁻ (cmxHLS_theta s f j) y‖)
      ≤ (2 * (n : ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1), C i * V := by
    intro n j y
    have hc : 0 < (1 + (2 : ℝ) ^ j) ^ N' := by positivity
    have hd := cmxMY_decay (cmxHLS_theta s f j) (cmxHLS_theta_contDiff hf s j)
      (cmxHLS_theta_supp f s j) n (fun i => C i * ((1 + (2 : ℝ) ^ j) ^ N')⁻¹)
      (fun i _ η => by
        have := hC i j η
        rw [← div_eq_mul_inv, le_div_iff₀ hc]
        linarith) y
    calc (1 + (2 : ℝ) ^ j) ^ N' * (‖y‖ ^ n * ‖𝓕⁻ (cmxHLS_theta s f j) y‖)
        ≤ (1 + (2 : ℝ) ^ j) ^ N' * ((2 * (n : ℝ) + 2) ^ n *
          ∑ i ∈ Finset.range (n + 1), C i * ((1 + (2 : ℝ) ^ j) ^ N')⁻¹ * V) :=
          mul_le_mul_of_nonneg_left hd hc.le
      _ = (2 * (n : ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1), C i * V := by
          have hs : ∑ i ∈ Finset.range (n + 1), C i * ((1 + (2 : ℝ) ^ j) ^ N')⁻¹ * V =
              ((1 + (2 : ℝ) ^ j) ^ N')⁻¹ * ∑ i ∈ Finset.range (n + 1), C i * V := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hs]
          field_simp
          exact Finset.sum_congr rfl fun i _ => by ring
  set K : ℕ → ℝ := fun n => (2 * (n : ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1), C i * V with hK
  have hK0 : ∀ n, 0 ≤ K n := fun n =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i) hV0)
  refine ⟨2 ^ N * (K 0 + K N), mul_nonneg (by positivity) (add_nonneg (hK0 0) (hK0 N)),
    fun j y => ?_⟩
  have h0 : (1 + (2 : ℝ) ^ j) ^ N' * ‖𝓕⁻ (cmxHLS_theta s f j) y‖ ≤ K 0 := by
    have := key 0 j y
    simp only [pow_zero, one_mul] at this
    simpa [hK] using this
  have hN := key N j y
  have h2 := cmxMY_one_add_pow_le ‖y‖ (norm_nonneg y) N
  have hc : 0 ≤ (1 + (2 : ℝ) ^ j) ^ N' := by positivity
  have hn : 0 ≤ ‖𝓕⁻ (cmxHLS_theta s f j) y‖ := norm_nonneg _
  calc (1 + (2 : ℝ) ^ j) ^ N' * (‖𝓕⁻ (cmxHLS_theta s f j) y‖ * (1 + ‖y‖) ^ N)
      ≤ (1 + (2 : ℝ) ^ j) ^ N' * (‖𝓕⁻ (cmxHLS_theta s f j) y‖ * (2 ^ N * (1 + ‖y‖ ^ N))) := by
        gcongr
    _ = 2 ^ N * ((1 + (2 : ℝ) ^ j) ^ N' * ‖𝓕⁻ (cmxHLS_theta s f j) y‖ +
          (1 + (2 : ℝ) ^ j) ^ N' * (‖y‖ ^ N * ‖𝓕⁻ (cmxHLS_theta s f j) y‖)) := by ring
    _ ≤ 2 ^ N * (K 0 + K N) :=
        mul_le_mul_of_nonneg_left (add_le_add h0 hN) (by positivity)


/-- The pointwise bound for the dyadic pieces. -/
theorem cmxHLS_piece_bound {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f)
    (hdec : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n f ξ‖ ≤ C)
    (s : ℝ) (N N' : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (j : ℤ) (x : Euc d),
      (1 + (2 : ℝ) ^ j) ^ N' * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ N * ‖cmxHLS_piece s f j x‖) ≤
        M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) := by
  obtain ⟨M, hM0, hM⟩ := cmxHLS_theta_decay hf hdec s N N'
  refine ⟨M, hM0, fun j x => ?_⟩
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h1 := hM j (((2 : ℝ) ^ j) • x)
  rw [norm_smul, Real.norm_of_nonneg hc.le] at h1
  rw [cmxHLS_piece_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (1 + (2 : ℝ) ^ j) ^ N' * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ N *
        (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d *
          ‖𝓕⁻ (cmxHLS_theta s f j) (((2 : ℝ) ^ j) • x)‖))
      = (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) * ((1 + (2 : ℝ) ^ j) ^ N' *
          (‖𝓕⁻ (cmxHLS_theta s f j) (((2 : ℝ) ^ j) • x)‖ * (1 + (2 : ℝ) ^ j * ‖x‖) ^ N)) := by ring
    _ ≤ (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) * M :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) := by ring

end HRS.Commutator.Whole
