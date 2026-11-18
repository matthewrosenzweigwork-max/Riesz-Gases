import HRS.MS.FixEqP1Aux1
import HRS.MS.LimFieldAux1
import HRS.MP.RdLimitGauss
import HRS.MP.KolmChentsov

/-!
# S5.7 `fixed_equation` (worker S57P), part 2: Gaussian ell^2-valued noise from an isonormal process (packet P4 core, partial)

Helper lemmas (prefix `s57p_`): `ellVec` coordinates and measurability, a.s. `ell^2`-membership of `(W(v_alpha))_alpha`
when `sum ||v_alpha||^2 < infty`, the norm identity in `OscDual`, and the Gaussian fourth-moment bound
`E ||X(v) - X(v')||^4 <= M (sum ||v_alpha - v'_alpha||^2)^2` (`s57p_fourth_moment`), the input of the
Kolmogorov-Chentsov theorem (`HRS/MP/KolmChentsov.lean`) that gives the a.s. continuous version.

Remaining for P4 (not in this file): apply `mkc_Zc_ae_eq`/`mkc_continuous` to obtain the continuous version
`s57p_noise_exists`; identify `eval (X t) phi` with the Wiener integral for `phi` in `Sigma^m`; instantiate with the kernels
`1_{r<=t} sqrt(2 q rho_r) grad U^{r,t} phi_alpha` of the two families on a common `L^2([0,T] x R^d; R^d)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

open HRS HRS.Whole

variable {d : ℕ}

theorem s57p_coord_ellVec {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) (α : MultiIndex d) :
    OscDual.coord (ellVec m c : OscDual d m) α = c α := by
  have e : (ellVec m c : OscDual d m) = (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
    simp [ellVec, h]
    rfl
  rw [e]
  rfl

theorem s57p_memℓp_iff {c : MultiIndex d → ℝ} :
    Memℓp c 2 ↔ ∑' α, ENNReal.ofReal (c α ^ 2) < ⊤ := by
  have hsq : ∀ α, ‖c α‖ ^ ((2 : ℝ≥0∞).toReal) = c α ^ 2 := by
    intro α
    simp [Real.norm_eq_abs, sq_abs]
  rw [memℓp_gen_iff (by simp)]
  simp_rw [hsq]
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hs]
    exact ENNReal.ofReal_lt_top
  · intro hlt
    have := ENNReal.summable_toReal (f := fun α => ENNReal.ofReal (c α ^ 2)) hlt.ne
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this

theorem s57p_ellVec_of_mem {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) :
    (ellVec m c : OscDual d m) = (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
  simp [ellVec, h]
  rfl

theorem s57p_ellVec_of_not_mem {m : ℝ} {c : MultiIndex d → ℝ} (h : ¬ Memℓp c 2) :
    (ellVec m c : OscDual d m) = 0 := by
  simp [ellVec, h]

theorem s57p_measurable_ellVec {m : ℝ} {Ω : Type*} [MeasurableSpace Ω] (c : MultiIndex d → Ω → ℝ)
    (hc : ∀ α, Measurable (c α)) :
    Measurable (fun w => ellVec m (fun α => c α w) : Ω → OscDual d m) := by
  classical
  let Good : Set Ω := {w | Memℓp (fun α => c α w) 2}
  have hGood : MeasurableSet Good := by
    have : Good = {w | ∑' α, ENNReal.ofReal (c α w ^ 2) < ⊤} := by
      ext w
      exact s57p_memℓp_iff
    rw [this]
    exact measurableSet_lt (Measurable.ennreal_tsum fun α =>
      ENNReal.measurable_ofReal.comp ((hc α).pow_const 2)) measurable_const
  let sg : MultiIndex d → ℝ → OscDual d m := fun α x => (lp.single 2 α x : lp (fun _ : MultiIndex d => ℝ) 2)
  have hsum : ∀ w ∈ Good, HasSum (fun α => sg α (c α w)) (ellVec m (fun α => c α w) : OscDual d m) := by
    intro w hw
    have hw' : Memℓp (fun α => c α w) 2 := hw
    rw [s57p_ellVec_of_mem hw']
    exact lp.hasSum_single (E := fun _ : MultiIndex d => ℝ) (p := 2) (by simp)
      (⟨fun α => c α w, hw'⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
  have hsgm : ∀ α, Measurable fun x : ℝ => sg α x := by
    intro α
    have e : (fun x : ℝ => sg α x) = fun x : ℝ => x • sg α 1 := by
      funext x
      have := lp.single_smul (p := 2) (E := fun _ : MultiIndex d => ℝ) α x (1 : ℝ)
      have h2 : (lp.single 2 α x : lp (fun _ : MultiIndex d => ℝ) 2) = x • lp.single 2 α 1 := by
        simpa using this
      exact h2
    rw [e]
    exact (continuous_id.smul continuous_const).measurable
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (F : Finset (MultiIndex d)) w => if w ∈ Good then ∑ α ∈ F, sg α (c α w) else 0)
    (fun F => Measurable.ite hGood (Finset.measurable_sum _ fun α _ => (hsgm α).comp (hc α)) measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro w
  by_cases hw : w ∈ Good
  · simp only [hw, if_true]
    exact hsum w hw
  · simp only [hw, if_false]
    have hw' : ¬ Memℓp (fun α => c α w) 2 := hw
    rw [s57p_ellVec_of_not_mem hw']
    exact tendsto_const_nhds

open HRS.MS.U10 in
theorem s57p_ae_memℓp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q] {W : H → Ω₀ → ℝ}
    (hI : Sb7Iso Q W) (v : MultiIndex d → H) (hv : Summable fun α => ‖v α‖ ^ 2) :
    ∀ᵐ w ∂Q, Memℓp (fun α => W (v α) w) 2 := by
  have hξm : ∀ α, Measurable (W (v α)) := fun α => hI.meas _
  have hξ2 : ∀ α, ∫ w, W (v α) w ^ 2 ∂Q = ‖v α‖ ^ 2 := by
    intro α
    have := hI.inner (v α) (v α)
    rw [real_inner_self_eq_norm_sq] at this
    simpa [sq] using this
  have hξint : ∀ α, Integrable (fun w => W (v α) w ^ 2) Q := fun α => (hI.memLp (v α)).integrable_sq
  have hSm : Measurable fun w => ∑' α, ENNReal.ofReal (W (v α) w ^ 2) :=
    Measurable.ennreal_tsum fun α => ENNReal.measurable_ofReal.comp ((hξm α).pow_const 2)
  have hlint : ∫⁻ w, ∑' α, ENNReal.ofReal (W (v α) w ^ 2) ∂Q < ⊤ := by
    rw [lintegral_tsum (μ := Q) (f := fun α w => ENNReal.ofReal (W (v α) w ^ 2))
      fun α => (ENNReal.measurable_ofReal.comp ((hξm α).pow_const 2)).aemeasurable]
    have : ∀ α, ∫⁻ w, ENNReal.ofReal (W (v α) w ^ 2) ∂Q = ENNReal.ofReal (‖v α‖ ^ 2) := by
      intro α
      rw [← ofReal_integral_eq_lintegral_ofReal (hξint α) (ae_of_all _ fun w => sq_nonneg _), hξ2 α]
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hv]
    exact ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top hSm hlint.ne] with w hw
  exact s57p_memℓp_iff.2 hw

theorem s57p_enorm_sq_sub {m : ℝ} (u v : OscDual d m) :
    ‖u - v‖ₑ ^ 2 = ∑' α, ENNReal.ofReal ((OscDual.coord u α - OscDual.coord v α) ^ 2) := by
  set f : lp (fun _ : MultiIndex d => ℝ) 2 := (u : lp (fun _ : MultiIndex d => ℝ) 2) - v with hf
  have h2 : ‖f‖ ^ (2 : ℝ) = ∑' α, ‖f α‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : MultiIndex d => ℝ) (by simp) f
  have hsum : Summable fun α => ‖f α‖ ^ (2 : ℝ) := by
    simpa using (memℓp_gen_iff (p := 2) (f := f) (by simp)).1 f.2
  have e1 : ‖u - v‖ₑ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rfl
  rw [e1]
  have e3 : ‖f‖ ^ 2 = ∑' α, (f α) ^ 2 := by
    have := h2
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at this
    simpa using this
  rw [e3, ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) (by simpa [Real.rpow_two] using hsum)]
  rfl

theorem s57p_summable_sub {H : Type} [NormedAddCommGroup H] {v v' : MultiIndex d → H}
    (hv : Summable fun α => ‖v α‖ ^ 2) (hv' : Summable fun α => ‖v' α‖ ^ 2) :
    Summable fun α => ‖v α - v' α‖ ^ 2 := by
  have hg : Summable fun α => 2 * ‖v α‖ ^ 2 + 2 * ‖v' α‖ ^ 2 := (hv.mul_left 2).add (hv'.mul_left 2)
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) hg
  have h := norm_sub_le (v α) (v' α)
  nlinarith [norm_nonneg (v α), norm_nonneg (v' α), norm_nonneg (v α - v' α), sq_nonneg (‖v α‖ - ‖v' α‖)]

open HRS.MS.U10 in
theorem s57p_fourth_moment {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q] {W : H → Ω₀ → ℝ}
    (hI : Sb7Iso Q W) (hlaw : ∀ g, Q.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2))
    {m : ℝ} (v v' : MultiIndex d → H) (hv : Summable fun α => ‖v α‖ ^ 2)
    (hv' : Summable fun α => ‖v' α‖ ^ 2) :
    ∫⁻ w, ‖(ellVec m (fun α => W (v α) w) : OscDual d m) - ellVec m (fun α => W (v' α) w)‖ₑ ^ 4 ∂Q ≤
      ENNReal.ofReal (M * (∑' α, ‖v α - v' α‖ ^ 2) ^ 2) := by
  have hsub := s57p_summable_sub hv hv'
  set f : MultiIndex d → Ω₀ → ℝ≥0∞ := fun α w => ENNReal.ofReal ((W (v α) w - W (v' α) w) ^ 2) with hf
  have hfm : ∀ α, Measurable (f α) := fun α =>
    ENNReal.measurable_ofReal.comp (((hI.meas _).sub (hI.meas _)).pow_const 2)
  have hae : ∀ᵐ w ∂Q, ‖(ellVec m (fun α => W (v α) w) : OscDual d m) - ellVec m (fun α => W (v' α) w)‖ₑ ^ 4 =
      (∑' α, f α w) ^ 2 := by
    filter_upwards [s57p_ae_memℓp hI v hv, s57p_ae_memℓp hI v' hv'] with w h1 h2
    have e : ∑' α, ENNReal.ofReal ((OscDual.coord (ellVec m (fun α => W (v α) w) : OscDual d m) α -
        OscDual.coord (ellVec m (fun α => W (v' α) w) : OscDual d m) α) ^ 2) = ∑' α, f α w :=
      tsum_congr fun α => by rw [s57p_coord_ellVec h1, s57p_coord_ellVec h2]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, s57p_enorm_sq_sub, e]
  rw [lintegral_congr_ae hae]
  set mm : MultiIndex d → ℝ≥0∞ := fun α => ENNReal.ofReal (Real.sqrt M * ‖v α - v' α‖ ^ 2) with hmm
  have hterm : ∀ α, ∫⁻ w, f α w ^ 2 ∂Q ≤ mm α ^ 2 := by
    intro α
    have hZ : (fun w => W (v α) w - W (v' α) w) =ᵐ[Q] W (v α - v' α) := by
      have := hI.lin 1 (-1) (v α) (v' α)
      filter_upwards [this] with w hw
      have e : (1 : ℝ) • v α + (-1 : ℝ) • v' α = v α - v' α := by simp [sub_eq_add_neg]
      rw [e] at hw
      rw [hw]; ring
    have e1 : ∀ w, f α w ^ 2 = ‖W (v α) w - W (v' α) w‖ₑ ^ 4 := by
      intro w
      rw [hf]
      simp only
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, ← ENNReal.ofReal_pow (sq_nonneg _)]
      congr 1
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
    have e2 : ∫⁻ w, f α w ^ 2 ∂Q = ∫⁻ w, ‖W (v α - v' α) w‖ₑ ^ 4 ∂Q := by
      simp_rw [e1]
      refine lintegral_congr_ae ?_
      filter_upwards [hZ] with w hw
      rw [hw]
    rw [e2, ← lintegral_map (f := fun y : ℝ => ‖y‖ₑ ^ 4) (by fun_prop) (hI.meas _), hlaw]
    refine (hM _ (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hmm]
    simp only
    rw [← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))]
    congr 1
    rw [mul_pow, Real.sq_sqrt hM0, ← pow_mul]
  have key := HRS.MP.RdLGS.rlg_sq_tsum (P := Q) f hfm mm hterm
  refine key.trans (le_of_eq ?_)
  rw [hmm]
  simp only
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
    (hsub.mul_left _), tsum_mul_left,
    ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun α => sq_nonneg _))]
  congr 1
  rw [mul_pow, Real.sq_sqrt hM0]
end HRS.MS.FixEq
