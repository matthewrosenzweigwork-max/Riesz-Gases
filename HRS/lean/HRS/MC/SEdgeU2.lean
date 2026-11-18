import HRS.MC.SEdgeVocab

/-!
# Packet U2: Lipschitz dependence of the Stein solution on the frequency
(relocated proof of `sed_U2_stein_lipschitz`).

The Stein solution is `f = -∫ steinG F p dν(p)`, hence `D^j f(x) = -∫ ouA^j • D^j F(ouA x + ouS y) dν`
(`iteratedFDeriv_steinSolG`); the difference in `t` is bounded pointwise inside the integral, so no
differentiation in `t` is needed.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.U2

open HRS HRS.Sec7

/-! ### `cos`, `sin` and their negatives -/

def u2P (g : ℝ → ℝ) : Prop :=
  g = Real.cos ∨ g = (fun y => -Real.cos y) ∨ g = Real.sin ∨ g = (fun y => -Real.sin y)

theorem u2P_deriv {g : ℝ → ℝ} (hg : u2P g) : u2P (deriv g) := by
  rcases hg with rfl | rfl | rfl | rfl
  · right; right; right
    funext y; simp [Real.deriv_cos]
  · right; right; left
    funext y
    rw [deriv.fun_neg, Real.deriv_cos]
    simp
  · left
    exact Real.deriv_sin
  · right; left
    funext y
    rw [deriv.fun_neg, Real.deriv_sin]

theorem u2P_iter (n : ℕ) {g : ℝ → ℝ} (hg : u2P g) : u2P (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact u2P_deriv ih

theorem u2P_bound {g : ℝ → ℝ} (hg : u2P g) (y : ℝ) : |g y| ≤ 1 := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Real.abs_cos_le_one y
  · simpa using Real.abs_cos_le_one y
  · exact Real.abs_sin_le_one y
  · simpa using Real.abs_sin_le_one y

theorem u2P_lip {g : ℝ → ℝ} (hg : u2P g) (a b : ℝ) : |g a - g b| ≤ |a - b| := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Real.abs_cos_sub_cos_le a b
  · have := Real.abs_cos_sub_cos_le a b
    rw [← abs_neg] at this
    simpa [neg_sub, sub_eq_add_neg, add_comm] using this
  · have := Real.lipschitzWith_sin.dist_le_mul a b
    simpa [Real.dist_eq] using this
  · have := Real.lipschitzWith_sin.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at this
    simp only [NNReal.coe_one, one_mul] at this
    rw [← abs_neg] at this
    simpa [neg_sub, sub_eq_add_neg, add_comm] using this

theorem u2P_contDiff {g : ℝ → ℝ} (hg : u2P g) : ContDiff ℝ ⊤ g := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Real.contDiff_cos
  · exact Real.contDiff_cos.neg
  · exact Real.contDiff_sin
  · exact Real.contDiff_sin.neg

/-! ### derivatives of `g (t * z 0)` -/

abbrev E1 := EuclideanSpace ℝ (Fin 1)

def u2L (t : ℝ) : E1 →L[ℝ] ℝ := t • EuclideanSpace.proj (0 : Fin 1)

lemma u2L_apply (t : ℝ) (z : E1) : u2L t z = t * z 0 := by simp [u2L]

lemma u2_iter_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g) (t : ℝ) (j : ℕ) (y : E1) (m : Fin j → E1) :
    iteratedFDeriv ℝ j (fun z => g (u2L t z)) y m =
      (∏ i, (t * m i 0)) * iteratedDeriv j g (t * y 0) := by
  have hcd : ContDiff ℝ j g := hg.of_le le_top
  have e := (u2L t).iteratedFDeriv_comp_right (f := g) hcd y (i := j) le_rfl
  have e' : (fun z => g (u2L t z)) = g ∘ u2L t := rfl
  rw [e', e, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h1 : (fun i => u2L t (m i)) = fun i => (t * m i 0) • (1 : ℝ) := by
    ext i; simp [u2L_apply]
  rw [h1, ContinuousMultilinearMap.map_smul_univ, iteratedDeriv_eq_iteratedFDeriv, u2L_apply]
  simp [smul_eq_mul]

lemma u2_diff_bound {g : ℝ → ℝ} (hg : u2P g) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (T : ℝ)
    (hT : 0 < T) (t t' : ℝ) (ht : |t| ≤ T) (ht' : |t'| ≤ T) (y : E1) :
    ‖iteratedFDeriv ℝ j (fun z => g (u2L t z)) y - iteratedFDeriv ℝ j (fun z => g (u2L t' z)) y‖ ≤
      3 * (1 + T) ^ 2 * |t - t'| * (1 + ‖y‖) := by
  have hgi := u2P_iter j hg
  set D := iteratedDeriv j g (t * y 0) with hD
  set D' := iteratedDeriv j g (t' * y 0) with hD'
  have hDb : |D| ≤ 1 := u2P_bound hgi _
  have hDd : |D - D'| ≤ |t - t'| * |y 0| := by
    refine (u2P_lip hgi _ _).trans (le_of_eq ?_)
    rw [← sub_mul, abs_mul]
  have hy0 : |y 0| ≤ ‖y‖ := by
    have := PiLp.norm_apply_le y 0
    simpa [Real.norm_eq_abs] using this
  have hpow : |t ^ j - t' ^ j| ≤ 2 * (1 + T) * |t - t'| := by
    interval_cases j
    · simp; nlinarith [abs_nonneg (t - t')]
    · have : t ^ 2 - t' ^ 2 = (t - t') * (t + t') := by ring
      rw [this, abs_mul]
      have h2 : |t + t'| ≤ 2 * (1 + T) := by
        have := abs_add_le t t'
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg (t - t'))]
  have hT' : |t'| ^ j ≤ (1 + T) ^ 2 := by
    calc |t'| ^ j ≤ (1 + T) ^ j := pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
      _ ≤ (1 + T) ^ 2 := pow_le_pow_right₀ (by linarith) hj2
  have hA : |t ^ j * D - t' ^ j * D'| ≤ 3 * (1 + T) ^ 2 * |t - t'| * (1 + ‖y‖) := by
    have e : t ^ j * D - t' ^ j * D' = (t ^ j - t' ^ j) * D + t' ^ j * (D - D') := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have h1 : |t ^ j - t' ^ j| * |D| ≤ 2 * (1 + T) * |t - t'| := by
      calc _ ≤ |t ^ j - t' ^ j| * 1 := mul_le_mul_of_nonneg_left hDb (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hpow
    have h2 : |t'| ^ j * |D - D'| ≤ (1 + T) ^ 2 * (|t - t'| * ‖y‖) := by
      calc _ ≤ (1 + T) ^ 2 * |D - D'| := mul_le_mul_of_nonneg_right hT' (abs_nonneg _)
        _ ≤ (1 + T) ^ 2 * (|t - t'| * |y 0|) := mul_le_mul_of_nonneg_left hDd (by positivity)
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hy0 (abs_nonneg _)
    have hs : (1 : ℝ) ≤ 1 + T := by linarith
    have h3 : 2 * (1 + T) ≤ 2 * (1 + T) ^ 2 := by nlinarith
    have h4 := abs_nonneg (t - t')
    have h5 : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith [mul_nonneg h4 h5, mul_nonneg h4 (sq_nonneg (1 + T)), mul_nonneg (mul_nonneg h4 h5) (sq_nonneg (1 + T))]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [sub_apply, u2_iter_comp (u2P_contDiff hg),
    u2_iter_comp (u2P_contDiff hg)]
  have hprod : ∀ s : ℝ, ∏ i : Fin j, (s * m i 0) = s ^ j * ∏ i : Fin j, m i 0 := by
    intro s
    rw [Finset.prod_mul_distrib]; simp
  rw [hprod, hprod]
  have e2 : t ^ j * (∏ i : Fin j, m i 0) * iteratedDeriv j g (t * y 0) -
      t' ^ j * (∏ i : Fin j, m i 0) * iteratedDeriv j g (t' * y 0) =
      (∏ i : Fin j, m i 0) * (t ^ j * D - t' ^ j * D') := by rw [hD, hD']; ring
  rw [Real.norm_eq_abs, e2, abs_mul]
  have hpm : |∏ i : Fin j, m i 0| ≤ ∏ i, ‖m i‖ := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
    have := PiLp.norm_apply_le (m i) 0
    simpa [Real.norm_eq_abs] using this
  calc _ ≤ (∏ i, ‖m i‖) * (3 * (1 + T) ^ 2 * |t - t'| * (1 + ‖y‖)) :=
        mul_le_mul hpm hA (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := mul_comm _ _


theorem u2_memCb {g : ℝ → ℝ} (hg : u2P g) (t : ℝ) : MemCb 5 (fun z : E1 => g (u2L t z)) := by
  refine ⟨((u2P_contDiff hg).of_le le_top).comp (u2L t).contDiff, fun j hj => ?_⟩
  refine ⟨‖u2L t‖ ^ j, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcd : ContDiff ℝ j g := (u2P_contDiff hg).of_le le_top
  have e := (u2L t).iteratedFDeriv_comp_right (f := g) hcd x (i := j) le_rfl
  have e' : iteratedFDeriv ℝ j (fun x => g (u2L t x)) x = iteratedFDeriv ℝ j (g ∘ u2L t) x := rfl
  show ‖iteratedFDeriv ℝ j (fun x => g (u2L t x)) x‖ ≤ ‖u2L t‖ ^ j
  rw [e', e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ‖iteratedFDeriv ℝ j g (u2L t x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact u2P_bound (u2P_iter j hg) _
  calc ‖iteratedFDeriv ℝ j g (u2L t x)‖ * ‖u2L t‖ ^ j ≤ 1 * ‖u2L t‖ ^ j :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖u2L t‖ ^ j := one_mul _

def u2h (σ : Bool) : ℝ → ℝ := if σ then Real.cos else Real.sin

lemma u2h_P (σ : Bool) : u2P (u2h σ) := by
  cases σ
  · right; right; left; rfl
  · left; rfl

lemma sed_Ucf_eq (σ : Bool) (t : ℝ) : sed_Ucf σ t = fun z : E1 => u2h σ (u2L t z) := by
  funext z
  cases σ <;> simp [sed_Ucf, u2h, u2L_apply]

lemma u2_int {γ : Measure E1} [IsProbabilityMeasure γ] {Φ : E1 → ℝ} (hΦ : MemCb 5 Φ) (j : ℕ)
    (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (x : E1) :
    Integrable (fun p => iteratedFDeriv ℝ j (steinG Φ p) x) (steinNu γ) :=
  (steinG_bound_int (γ := γ) hΦ j hj1).mono' (steinG_meas hΦ j hj5 x)
    (Filter.Eventually.of_forall fun p => steinG_bound hΦ j hj1 hj5 p x)


theorem sed_U2_stein_lipschitz_proof (v : ℝ) (hv : 0 ≤ v) (T : ℝ) (hT : 0 < T) (σ : Bool) :
    ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ t t' : ℝ, |t| ≤ T → |t'| ≤ T →
      ∀ x : EuclideanSpace ℝ (Fin 1),
      ‖iteratedFDeriv ℝ j (steinSolution (multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))
            (fun z : EuclideanSpace ℝ (Fin 1) => z) (sed_Ucf σ t)) x -
          iteratedFDeriv ℝ j (steinSolution (multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))
            (fun z : EuclideanSpace ℝ (Fin 1) => z) (sed_Ucf σ t')) x‖ ≤
        K * |t - t'| * (1 + ‖x‖) := by
  set P : Measure E1 := multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v) with hP
  have hγ1 : Integrable (fun y : E1 => ‖y‖) P := IsGaussian.integrable_id.norm
  have hF : ∀ t, MemCb 5 (sed_Ucf σ t) := fun t => by
    rw [sed_Ucf_eq]; exact u2_memCb (u2h_P σ) t
  have hf : ∀ t, steinSolution P (fun z : E1 => z) (sed_Ucf σ t) = steinSolG P (sed_Ucf σ t) := by
    intro t
    have := steinSolution_eq_steinSolG P (fun z : E1 => z) aemeasurable_id (hF t)
    rwa [show P.map (fun z : E1 => z) = P from Measure.map_id] at this
  set m1 : ℝ := ∫ y, ‖y‖ ∂P with hm1
  have hm1n : 0 ≤ m1 := integral_nonneg fun _ => norm_nonneg _
  refine ⟨3 * (1 + T) ^ 2 * (1 + m1), ?_⟩
  intro j hj1 hj2 t t' ht ht' x
  have hj5 : j ≤ 5 := by omega
  rw [hf t, hf t', iteratedFDeriv_steinSolG (hF t) hγ1 j hj5 x,
    iteratedFDeriv_steinSolG (hF t') hγ1 j hj5 x, neg_sub_neg, norm_sub_rev,
    ← integral_sub (u2_int (hF t) j hj1 hj5 x) (u2_int (hF t') j hj1 hj5 x)]
  set Mt : ℝ := 3 * (1 + T) ^ 2 * |t - t'| with hMt
  have hMt0 : 0 ≤ Mt := by positivity
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hint : Integrable (fun p : ℝ × E1 => Real.exp (-(j : ℝ) * p.1) * (Mt * ((1 + ‖x‖) + ‖p.2‖)))
      (steinNu P) :=
    (integrable_exp_neg_mul (j : ℝ) hj0).mul_prod
      (((integrable_const (1 + ‖x‖)).add hγ1).const_mul Mt)
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [ae_steinNu_pos (γ := P)] with p hp
    rw [iteratedFDeriv_steinG _ (hF t).1 p j hj1 hj5, iteratedFDeriv_steinG _ (hF t').1 p j hj1 hj5,
      ← smul_sub, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (ouA_pos _), ouA_pow]
    have hb := u2_diff_bound (u2h_P σ) j hj1 hj2 T hT t t' ht ht'
      (ouA p.1 • x + ouS p.1 • p.2)
    rw [← sed_Ucf_eq σ t, ← sed_Ucf_eq σ t'] at hb
    have hz : ‖ouA p.1 • x + ouS p.1 • p.2‖ ≤ ‖x‖ + ‖p.2‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (ouA_pos _),
        abs_of_nonneg (ouS_nonneg _)]
      have h1 := ouA_le_one hp.le
      have h2 := ouS_le_one hp.le
      nlinarith [norm_nonneg x, norm_nonneg p.2, ouA_pos p.1, ouS_nonneg p.1]
    refine mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.exp_pos _).le
    have : 3 * (1 + T) ^ 2 * |t - t'| * (1 + ‖ouA p.1 • x + ouS p.1 • p.2‖) =
        Mt * (1 + ‖ouA p.1 • x + ouS p.1 • p.2‖) := rfl
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hMt0
    linarith
  · rw [integral_prod_mul (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := P)
      (fun u : ℝ => Real.exp (-(j : ℝ) * u)) (fun y : E1 => Mt * ((1 + ‖x‖) + ‖y‖))]
    have hI := integral_exp_mul_Ioi (a := -(j : ℝ)) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at hI
    rw [hI, integral_const_mul, integral_add (integrable_const _) hγ1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← hm1]
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have e1 : -1 / -(j : ℝ) = (j : ℝ)⁻¹ := by field_simp
    have hinv : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj1'
    have hq : 0 ≤ Mt * (1 + ‖x‖ + m1) := by positivity
    calc (-1 / -(j : ℝ)) * (Mt * (1 + ‖x‖ + m1)) = (j : ℝ)⁻¹ * (Mt * (1 + ‖x‖ + m1)) := by
          rw [e1]
      _ ≤ 1 * (Mt * (1 + ‖x‖ + m1)) := mul_le_mul_of_nonneg_right hinv hq
      _ ≤ _ := by
          rw [one_mul, hMt]
          nlinarith [mul_nonneg hMt0 (mul_nonneg hm1n (norm_nonneg x))]


end HRS.MC.SEdge.U2
