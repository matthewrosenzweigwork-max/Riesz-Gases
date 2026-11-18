import HRS.Commutator.Torus.NRSTAux19
import HRS.Commutator.Torus.LEIBTAux12
import HRS.Commutator.Whole.XNRSAux37

/-!
# NRS-T, part 20: transference error bound for an arbitrary temperate symbol
(copy of `LEIBTAux4`-`LEIBTAux12` with the Bessel symbol replaced by an arbitrary symbol `θ`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Fourier multiplier of symbol `θ` applied to `W`, in integral form. -/
def nrstg_T (θ : 𝔼 → ℂ) (W : SchwartzMap 𝔼 ℂ) (x : 𝔼) : ℂ :=
  ∫ ξ : 𝔼, leibt_e x ξ * (θ ξ * 𝓕 (⇑W) ξ)

lemma nrstg_m_bound (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) :
    ∃ (C₀ : ℝ) (k₀ : ℕ), 0 ≤ C₀ ∧ ∀ ξ : 𝔼, ‖θ ξ‖ ≤ C₀ * (1 + ‖ξ‖) ^ k₀ := by
  obtain ⟨k₀, C₀, hC₀, hb⟩ := hθ.norm_iteratedFDeriv_le_uniform 0
  exact ⟨C₀, k₀, hC₀, fun ξ => by simpa using hb 0 le_rfl ξ⟩

/-- The difference of symbols `ζ ↦ m(a + tζ) - m(a)`. -/
def nrstg_theta (θ : 𝔼 → ℂ) (a : 𝔼) (t : ℝ) (ζ : 𝔼) : ℂ := θ (a + t • ζ) - θ a

lemma nrstg_theta_bound (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (n₀ : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (a : 𝔼) (t : ℝ), 0 < t → t ≤ 1 → ∀ n ≤ n₀, ∀ ζ : 𝔼,
      ‖iteratedFDeriv ℝ n (nrstg_theta θ a t) ζ‖ ≤
        C * t * (1 + ‖a‖) ^ k * (1 + ‖ζ‖) ^ (k + 1) := by
  have hT := hθ
  obtain ⟨k₀, C₀, hC₀, hb⟩ := hT.norm_iteratedFDeriv_le_uniform (max n₀ 1)
  refine ⟨C₀, k₀, hC₀, fun a t ht ht1 n hn ζ => ?_⟩
  have hsm : ContDiff ℝ ∞ (θ : 𝔼 → ℂ) := hT.1
  have h1a : (1 : ℝ) ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
  have h1z : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hprod : 1 + ‖a + t • ζ‖ ≤ (1 + ‖a‖) * (1 + ‖ζ‖) := by
    have : ‖a + t • ζ‖ ≤ ‖a‖ + ‖ζ‖ := by
      calc ‖a + t • ζ‖ ≤ ‖a‖ + ‖t • ζ‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ‖ζ‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          calc t * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr
            _ = ‖ζ‖ := one_mul _
    nlinarith [norm_nonneg a, norm_nonneg ζ]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · -- n = 0: mean value inequality
    rw [norm_iteratedFDeriv_zero]
    unfold nrstg_theta
    set B : ℝ := C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀ with hB
    have hbound : ∀ x ∈ Metric.closedBall a (t * ‖ζ‖), ‖fderiv ℝ (θ) x‖ ≤ B := by
      intro x hx
      have hx1 : ‖x‖ ≤ ‖a‖ + t * ‖ζ‖ := by
        have := mem_closedBall_iff_norm.1 hx
        calc ‖x‖ = ‖(x - a) + a‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
          _ ≤ t * ‖ζ‖ + ‖a‖ := by linarith
          _ = ‖a‖ + t * ‖ζ‖ := by ring
      have h2 := hb 1 (by omega) x
      rw [norm_iteratedFDeriv_one] at h2
      refine h2.trans ?_
      rw [hB]
      gcongr
      have : t * ‖ζ‖ ≤ ‖ζ‖ := by
        calc t * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr
          _ = ‖ζ‖ := one_mul _
      nlinarith [norm_nonneg a, norm_nonneg ζ]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := θ)
      (s := Metric.closedBall a (t * ‖ζ‖)) (x := a) (y := a + t • ζ)
      (fun x _ => (hsm.differentiable (by simp)) x) hbound (convex_closedBall _ _)
      (Metric.mem_closedBall_self (by positivity))
      (by
        rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht])
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hmv
    refine hmv.trans ?_
    rw [hB, mul_pow]
    have e1 : (1 + ‖ζ‖) ^ (k₀ + 1) = (1 + ‖ζ‖) ^ k₀ * (1 + ‖ζ‖) := pow_succ _ _
    have e2 : ‖ζ‖ ≤ 1 + ‖ζ‖ := by linarith
    calc C₀ * ((1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ k₀) * (t * ‖ζ‖)
        = C₀ * t * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ζ‖) := by ring
      _ ≤ C₀ * t * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * (1 + ‖ζ‖)) := by gcongr
      _ = _ := by rw [e1]
  · -- n ≥ 1: the constant disappears, scaling gives `t^n`
    have hg : ContDiff ℝ ∞ (fun z : 𝔼 => θ (a + z)) := hsm.comp (contDiff_const.add contDiff_id)
    have hg2 : ContDiff ℝ ∞ (fun z : 𝔼 => θ (a + t • z)) :=
      hsm.comp (contDiff_const.add (contDiff_id.const_smul t))
    have hth : nrstg_theta θ a t = (fun z : 𝔼 => θ (a + t • z)) - fun _ => θ a := rfl
    have e1 : iteratedFDeriv ℝ n (nrstg_theta θ a t) ζ = iteratedFDeriv ℝ n (fun z : 𝔼 => θ (a + t • z)) ζ := by
      rw [hth, iteratedFDeriv_sub_apply (hg2.of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    have e2 : iteratedFDeriv ℝ n (fun z : 𝔼 => θ (a + t • z)) ζ =
        t ^ n • iteratedFDeriv ℝ n (fun z : 𝔼 => θ (a + z)) (t • ζ) := by
      have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := n) (f := fun z : 𝔼 => θ (a + z)) t
        (hg.of_le (by exact_mod_cast le_top))
      exact congrFun this ζ
    have e3 : iteratedFDeriv ℝ n (fun z : 𝔼 => θ (a + z)) (t • ζ) =
        iteratedFDeriv ℝ n (θ) (a + t • ζ) := iteratedFDeriv_comp_add_left n a (t • ζ)
    rw [e1, e2, e3, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht]
    have h2 := hb n (le_trans hn (le_max_left _ _)) (a + t • ζ)
    have htn : t ^ n ≤ t := by
      calc t ^ n ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hnpos
        _ = t := pow_one t
    calc t ^ n * ‖iteratedFDeriv ℝ n (θ) (a + t • ζ)‖
        ≤ t * (C₀ * (1 + ‖a + t • ζ‖) ^ k₀) := by gcongr
      _ ≤ t * (C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀) := by gcongr
      _ = C₀ * t * (1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ k₀ := by rw [mul_pow]; ring
      _ ≤ C₀ * t * (1 + ‖a‖) ^ k₀ * (1 + ‖ζ‖) ^ (k₀ + 1) := by
        gcongr
        exact Nat.le_succ _


/-- The Schwartz function `(m(a + t·) - m(a)) ψ`. -/
def nrstg_rho (θ : 𝔼 → ℂ) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (nrstg_theta θ a t) ψ

lemma nrstg_theta_temperate (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (a : 𝔼) (t : ℝ) : (nrstg_theta θ a t).HasTemperateGrowth := by
  have h1 : (fun ζ : 𝔼 => a + t • ζ).HasTemperateGrowth := by fun_prop
  have h2 := hθ.comp h1
  have h3 : (fun _ : 𝔼 => θ a).HasTemperateGrowth := Function.HasTemperateGrowth.const _
  exact h2.sub h3

lemma nrstg_rho_apply (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) (ζ : 𝔼) :
    nrstg_rho θ ψ a t ζ = nrstg_theta θ a t ζ * ψ ζ := by
  unfold nrstg_rho
  rw [SchwartzMap.smulLeftCLM_apply_apply (nrstg_theta_temperate θ hθ a t), smul_eq_mul]

lemma nrstg_rho_decay (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (ψ : SchwartzMap 𝔼 ℂ) (K : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (a : 𝔼) (t : ℝ), 0 < t → t ≤ 1 → ∀ w : 𝔼,
      (1 + ‖w‖) ^ K * ‖(𝓕⁻ (nrstg_rho θ ψ a t) : SchwartzMap 𝔼 ℂ) w‖ ≤ C * t * (1 + ‖a‖) ^ k := by
  obtain ⟨kk, nn, C₁, hC₁, hdec⟩ := leibt_invF_decay' (d := d) K
  obtain ⟨Cθ, kθ, hCθ, hθb⟩ := nrstg_theta_bound (d := d) θ hθ nn
  set S₀ := ((Finset.Iic (kk + (kθ + 1), nn)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ with hS₀
  have hS₀0 : 0 ≤ S₀ := by positivity
  refine ⟨C₁ * (Cθ * 2 ^ nn * 2 ^ (kk + (kθ + 1)) * S₀), kθ, by positivity, fun a t ht ht1 w => ?_⟩
  refine (hdec _ w).trans ?_
  have hsup : ((Finset.Iic (kk, nn)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) (nrstg_rho θ ψ a t) ≤
      Cθ * t * (1 + ‖a‖) ^ kθ * 2 ^ nn * 2 ^ (kk + (kθ + 1)) * S₀ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun ⟨k, n⟩ hkn => ?_
    rw [Finset.mem_Iic] at hkn
    have hkn1 : k ≤ kk := hkn.1
    have hkn2 : n ≤ nn := hkn.2
    show SchwartzMap.seminorm ℂ k n (nrstg_rho θ ψ a t) ≤ _
    have hA : 0 ≤ Cθ * t * (1 + ‖a‖) ^ kθ := by positivity
    have h := leibt_seminorm_mul (nrstg_theta θ a t) (nrstg_theta_temperate θ hθ a t) ψ k n (kθ + 1) hA
      (fun i hi ζ => by
        have := hθb a t ht ht1 i (hi.trans hkn2) ζ
        simpa [mul_assoc] using this)
    refine h.trans ?_
    have hmono : ((Finset.Iic (k + (kθ + 1), n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ ≤ S₀ := by
      refine Seminorm.le_def.1 (Finset.sup_mono ?_) ψ
      intro x hx
      rw [Finset.mem_Iic] at hx ⊢
      exact ⟨le_trans hx.1 (by omega), le_trans hx.2 hkn2⟩
    have h2n : (2 : ℝ) ^ n ≤ 2 ^ nn := pow_le_pow_right₀ (by norm_num) hkn2
    have h2k : (2 : ℝ) ^ (k + (kθ + 1)) ≤ 2 ^ (kk + (kθ + 1)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 ≤ ((Finset.Iic (k + (kθ + 1), n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ := by positivity
    gcongr
  refine le_trans (mul_le_mul_of_nonneg_left hsup hC₁) (le_of_eq ?_)
  ring


lemma nrstg_shift_bound (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (ψ : SchwartzMap 𝔼 ℂ) :
    ∃ (B : ℝ) (k₀ : ℕ), 0 ≤ B ∧ ∀ (N : ℝ), 1 ≤ N → ∀ a : 𝔼,
      Integrable (fun ζ : 𝔼 => θ (a + N⁻¹ • ζ) * ψ ζ) ∧
      ∫ ζ : 𝔼, ‖θ (a + N⁻¹ • ζ) * ψ ζ‖ ≤ B * (1 + ‖a‖) ^ k₀ := by
  obtain ⟨C₀, k₀, hC₀, hm⟩ := nrstg_m_bound (d := d) θ hθ
  set J : ℝ := ∫ ζ : 𝔼, (1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖ with hJ
  have hJint := leibt_psi_integrable ψ k₀
  have hJ0 : 0 ≤ J := integral_nonneg fun ζ => by positivity
  refine ⟨C₀ * J, k₀, by positivity, fun N hN a => ?_⟩
  have hN0 : 0 < N := by linarith
  have hbd : ∀ ζ : 𝔼, ‖θ (a + N⁻¹ • ζ) * ψ ζ‖ ≤
      C₀ * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖) := by
    intro ζ
    rw [norm_mul]
    have h1 : ‖a + N⁻¹ • ζ‖ ≤ ‖a‖ + ‖ζ‖ := by
      calc ‖a + N⁻¹ • ζ‖ ≤ ‖a‖ + ‖N⁻¹ • ζ‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ‖ζ‖ := by
          gcongr
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hN0]
          calc N⁻¹ * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr; exact inv_le_one_of_one_le₀ hN
            _ = ‖ζ‖ := one_mul _
    have h2 : 1 + ‖a + N⁻¹ • ζ‖ ≤ (1 + ‖a‖) * (1 + ‖ζ‖) := by
      nlinarith [norm_nonneg a, norm_nonneg ζ]
    have h3 := hm (a + N⁻¹ • ζ)
    calc ‖θ (a + N⁻¹ • ζ)‖ * ‖ψ ζ‖ ≤ (C₀ * (1 + ‖a + N⁻¹ • ζ‖) ^ k₀) * ‖ψ ζ‖ := by gcongr
      _ ≤ (C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀) * ‖ψ ζ‖ := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hcont : Continuous fun ζ : 𝔼 => θ (a + N⁻¹ • ζ) * ψ ζ := by
    have := hθ.1.continuous
    exact (this.comp (continuous_const.add (continuous_const_smul _))).mul ψ.continuous
  have hint : Integrable (fun ζ : 𝔼 => θ (a + N⁻¹ • ζ) * ψ ζ) :=
    ((hJint.const_mul (C₀ * (1 + ‖a‖) ^ k₀))).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  calc ∫ ζ : 𝔼, ‖θ (a + N⁻¹ • ζ) * ψ ζ‖
      ≤ ∫ ζ : 𝔼, C₀ * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖) :=
        integral_mono hint.norm (hJint.const_mul _) hbd
    _ = C₀ * J * (1 + ‖a‖) ^ k₀ := by
        rw [integral_const_mul, hJ]; ring


/-- The shifted-symbol integral `Φ(a, x) = ∫ e_{N⁻¹x}(ζ) m(a + N⁻¹ζ) ψ(ζ) dζ`. -/
def nrstg_Phi (θ : 𝔼 → ℂ) (ψ : SchwartzMap 𝔼 ℂ) (N : ℝ) (a x : 𝔼) : ℂ :=
  ∫ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (θ (a + N⁻¹ • ζ) * ψ ζ)

lemma nrstg_series_bessel (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (χ : SchwartzMap 𝔼 ℂ) {N : ℝ} (hN : 1 ≤ N) {ι : Type*} [Countable ι]
    (c : ι → ℂ) (lam : ι → 𝔼) (hc : ∀ k : ℕ, Summable fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k)
    (W : SchwartzMap 𝔼 ℂ) (hW : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (W y))
    (x : 𝔼) :
    HasSum (fun i => c i * (leibt_e (lam i) x * nrstg_Phi θ (𝓕 χ) N (lam i) x))
      (nrstg_T θ W x) := by
  have hN0 : 0 < N := by linarith
  set ψ : SchwartzMap 𝔼 ℂ := 𝓕 χ with hψ
  have hc0 : Summable fun i => ‖c i‖ := by simpa using hc 0
  obtain ⟨B, k₀, hB, hsh⟩ := nrstg_shift_bound (d := d) θ hθ ψ
  have hFT := leibt_series_fourier χ hN0 c lam hc0 W hW
  set F : ι → 𝔼 → ℂ := fun i ξ => leibt_e x ξ * (θ ξ * (c i * (((N ^ d : ℝ) : ℂ) *
    ψ (N • (ξ - lam i))))) with hF
  have hNd : (0 : ℝ) < N ^ d := by positivity
  have hmcont : Continuous (θ : 𝔼 → ℂ) := hθ.1.continuous
  have hcontF : ∀ i, Continuous (F i) := by
    intro i
    have := leibt_continuous_e x
    simp only [hF]
    have h2 : Continuous fun ξ : 𝔼 => ψ (N • (ξ - lam i)) :=
      ψ.continuous.comp (continuous_const_smul N |>.comp (continuous_id.sub continuous_const))
    exact this.mul (hmcont.mul (continuous_const.mul (continuous_const.mul h2)))
  -- the change of variables for each term
  have hcov : ∀ i, ∫ ξ, F i ξ = c i * (leibt_e (lam i) x * nrstg_Phi θ ψ N (lam i) x) := by
    intro i
    have e : ∀ ξ : 𝔼, F i ξ = c i * (leibt_e x ξ * (θ ξ * (((N ^ d : ℝ) : ℂ) * ψ (N • (ξ - lam i))))) := by
      intro ξ; simp only [hF]; ring
    simp_rw [e]
    rw [integral_const_mul, leibt_cov (θ) (fun ζ => ψ ζ) hN0 (lam i) x, leibt_e_comm x (lam i)]
    rfl
  have hnormF : ∀ i ξ, ‖F i ξ‖ = ‖c i‖ * (N ^ d) * ‖θ ξ * ψ (N • (ξ - lam i))‖ := by
    intro i ξ
    simp only [hF, norm_mul, leibt_norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNd]
    ring
  have hint : ∀ i, Integrable (F i) := by
    intro i
    have h1 := (hsh N hN (lam i)).1
    have h2 : Integrable (fun ξ : 𝔼 => θ ξ * ψ (N • (ξ - lam i))) := by
      refine leibt_integrable_cov _ hN0 (lam i) ?_
      have e : ∀ ζ : 𝔼, θ (lam i + N⁻¹ • ζ) * ψ (N • (lam i + N⁻¹ • ζ - lam i)) =
          θ (lam i + N⁻¹ • ζ) * ψ ζ := by
        intro ζ
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
      simp_rw [e]
      exact h1
    refine (h2.norm.const_mul (‖c i‖ * N ^ d)).mono' (hcontF i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => (hnormF i ξ).le)
  have hintnorm : ∀ i, ∫ ξ, ‖F i ξ‖ = ‖c i‖ * ∫ ζ : 𝔼, ‖θ (lam i + N⁻¹ • ζ) * ψ ζ‖ := by
    intro i
    simp_rw [hnormF]
    rw [integral_const_mul]
    rw [leibt_cov0 (fun ξ : 𝔼 => ‖θ ξ * ψ (N • (ξ - lam i))‖) hN0 (lam i)]
    have e : ∀ ζ : 𝔼, ‖θ (lam i + N⁻¹ • ζ) * ψ (N • (lam i + N⁻¹ • ζ - lam i))‖ =
        ‖θ (lam i + N⁻¹ • ζ) * ψ ζ‖ := by
      intro ζ
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
    simp_rw [e]
    rw [smul_eq_mul, ← mul_assoc, mul_assoc (‖c i‖), mul_inv_cancel₀ hNd.ne', mul_one]
  have hsum : Summable fun i => ∫ ξ, ‖F i ξ‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun ξ => norm_nonneg _) (fun i => ?_)
      ((hc k₀).mul_left B)
    rw [hintnorm]
    have := (hsh N hN (lam i)).2
    calc ‖c i‖ * ∫ ζ : 𝔼, ‖θ (lam i + N⁻¹ • ζ) * ψ ζ‖
        ≤ ‖c i‖ * (B * (1 + ‖lam i‖) ^ k₀) := by gcongr
      _ = B * (‖c i‖ * (1 + ‖lam i‖) ^ k₀) := by ring
  have h1 := hasSum_integral_of_summable_integral_norm hint hsum
  have h2 : ∀ ξ, ∑' i, F i ξ = leibt_e x ξ * (θ ξ * 𝓕 (⇑W) ξ) := by
    intro ξ
    have := (hFT ξ).mul_left (θ ξ)
    have := this.mul_left (leibt_e x ξ)
    exact this.tsum_eq
  have h3 : ∫ ξ, ∑' i, F i ξ = nrstg_T θ W x := by
    simp_rw [h2]
    rfl
  rw [h3] at h1
  simpa only [hcov] using h1


lemma nrstg_invF_rho (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) (w : 𝔼) :
    (𝓕⁻ (nrstg_rho θ ψ a t) : SchwartzMap 𝔼 ℂ) w =
      ∫ ζ : 𝔼, leibt_e w ζ * (nrstg_theta θ a t ζ * ψ ζ) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [leibt_e_comm w v, nrstg_rho_apply θ hθ]
  rfl

lemma nrstg_error_bound (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (χ : SchwartzMap 𝔼 ℂ) (K : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (c : Lattice d → ℂ) (lam : Lattice d → 𝔼)
      (hc : ∀ k : ℕ, Summable fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k)
      (G W : 𝔼 → ℂ) (Wc : SchwartzMap 𝔼 ℂ) (hWc : ⇑Wc = W)
      (hG : ∀ y, HasSum (fun i => c i * θ (lam i) * leibt_e (lam i) y) (G y))
      {N : ℝ} (hN : 1 ≤ N)
      (hW : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (W y)) (x : 𝔼),
      ‖nrstg_T θ Wc x - G x * χ (N⁻¹ • x)‖ ≤
        C * (∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹ := by
  obtain ⟨C, k, hC, hdec⟩ := nrstg_rho_decay (d := d) θ hθ (𝓕 χ) K
  refine ⟨C, k, hC, fun c lam hc G W Wc hWc hG {N} hN hW x => ?_⟩
  have hN0 : 0 < N := by linarith
  have hNinv0 : 0 < N⁻¹ := inv_pos.2 hN0
  have hNinv1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  set ψ : SchwartzMap 𝔼 ℂ := 𝓕 χ with hψ
  have hW' : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (Wc y) := by
    intro y; rw [hWc]; exact hW y
  have hA := nrstg_series_bessel θ hθ χ hN c lam hc Wc hW' x
  have hB : HasSum (fun i => c i * θ (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x)) (G x * χ (N⁻¹ • x)) :=
    (hG x).mul_right _
  have hD := hA.sub hB
  obtain ⟨B, k₀, hB0, hsh⟩ := nrstg_shift_bound (d := d) θ hθ ψ
  -- termwise identification
  have hterm : ∀ i, c i * (leibt_e (lam i) x * nrstg_Phi θ ψ N (lam i) x) -
      c i * θ (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x) =
      c i * leibt_e (lam i) x * (𝓕⁻ (nrstg_rho θ ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x) := by
    intro i
    rw [nrstg_invF_rho θ hθ]
    have hint1 : Integrable (fun ζ : 𝔼 => leibt_e (N⁻¹ • x) ζ * (θ (lam i + N⁻¹ • ζ) * ψ ζ)) := by
      have h1 := (hsh N hN (lam i)).1
      refine (h1.norm).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
      · have := leibt_continuous_e (N⁻¹ • x)
        have hm := hθ.1.continuous
        exact (this.mul ((hm.comp (continuous_const.add (continuous_const_smul _))).mul ψ.continuous)).aestronglyMeasurable
      · rw [norm_mul, leibt_norm_e, one_mul]
    have hint2 : Integrable (fun ζ : 𝔼 => θ (lam i) * (leibt_e (N⁻¹ • x) ζ * ψ ζ)) := by
      refine (((ψ.integrable.norm).const_mul ‖θ (lam i)‖)).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
      · have := leibt_continuous_e (N⁻¹ • x)
        exact (continuous_const.mul (this.mul ψ.continuous)).aestronglyMeasurable
      · rw [norm_mul, norm_mul, leibt_norm_e, one_mul]
    have e1 : ∫ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (nrstg_theta θ (lam i) N⁻¹ ζ * ψ ζ) =
        nrstg_Phi θ ψ N (lam i) x - θ (lam i) * χ (N⁻¹ • x) := by
      unfold nrstg_Phi
      have hpt : ∀ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (nrstg_theta θ (lam i) N⁻¹ ζ * ψ ζ) =
          leibt_e (N⁻¹ • x) ζ * (θ (lam i + N⁻¹ • ζ) * ψ ζ) -
            θ (lam i) * (leibt_e (N⁻¹ • x) ζ * ψ ζ) := by
        intro ζ; simp only [nrstg_theta]; ring
      simp_rw [hpt]
      rw [integral_sub hint1 hint2, integral_const_mul, ← leibt_fourier_inversion χ (N⁻¹ • x)]
    rw [e1]
    ring
  have hbound : ∀ i, ‖c i * (leibt_e (lam i) x * nrstg_Phi θ ψ N (lam i) x) -
      c i * θ (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x)‖ ≤
      ‖c i‖ * (1 + ‖lam i‖) ^ k * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by
    intro i
    rw [hterm, norm_mul, norm_mul, leibt_norm_e, mul_one]
    have h1 := hdec (lam i) N⁻¹ hNinv0 hNinv1 (N⁻¹ • x)
    have hpos : 0 < (1 + ‖N⁻¹ • x‖) ^ K := by positivity
    have h2 : ‖(𝓕⁻ (nrstg_rho θ ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖ ≤
        C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹ := by
      rw [← mul_le_mul_iff_of_pos_left hpos]
      calc (1 + ‖N⁻¹ • x‖) ^ K * ‖(𝓕⁻ (nrstg_rho θ ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖
          ≤ C * N⁻¹ * (1 + ‖lam i‖) ^ k := h1
        _ = (1 + ‖N⁻¹ • x‖) ^ K * (C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by
          field_simp
    calc ‖c i‖ * ‖(𝓕⁻ (nrstg_rho θ ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖
        ≤ ‖c i‖ * (C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by gcongr
      _ = _ := by ring
  have hsumk : HasSum (fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹))
      ((∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹)) :=
    (hc k).hasSum.mul_right _
  have := hD.norm_le_of_bounded hsumk hbound
  calc ‖nrstg_T θ Wc x - G x * χ (N⁻¹ • x)‖
      ≤ (∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := this
    _ = _ := by ring


end HRS.Commutator.TorusNote
