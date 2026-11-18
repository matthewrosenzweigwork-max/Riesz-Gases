import HRS.MS.UlMildAux2

/-!
# UL-4 (S5.1 infrastructure, supplement foundation packet): the mild solution in `E_k`, part 3

Not a manuscript row.  Files: `UlMildAux1` (semigroup law `ul4_semigroup`, time continuity of `ouSg`,
averaging of families `ul4_avg_gen`, the weighted time-integral Minkowski bound `ul4_time_bound`,
localisation and derivative bounds in `H_uloc`), `UlMildAux2` (the perturbation `ulPert u = ⟨c,∇u⟩ - ulNL u`,
its `C_b^4 → C_b^2` regularity, and the smoothing estimate `ul4_pert_est`:
`‖P_t ulPert u‖_{H^k_ul} ≤ K t^{-γ} ‖u‖_{H^k_ul}` on `UlClosure k θ`, `0 < t ≤ T`,
`γ = max(1, 2-(d-s))/2 ∈ [1/2, 1)`, by TC-3 for the near part of `ulNL` and the UL-3 gain for the rest),
`UlMildAux3` (this file: the Duhamel operator `ulD`, its norm bound `ul4_D_bound`, closure toolkit,
uniqueness, Picard existence).  All indices satisfy `4 + d/2 < k` (the plan's `k₀ = ⌈d/2⌉ + 6` does).

Main declarations (`ν > 0`, `0 ≤ s < d`, `ρ` Schwartz, `c` smooth with bounded derivatives, `θ` an `IsUlCutoff`):

* `ul_mild_unique` (no extra hypothesis): two families in `C([0,T]; E_k)` (values in `UlClosure k θ`,
  strongly continuous in `ulNormE k θ`) satisfying the mild equation
  `u τ x = ouSg Q ν τ f x + ∫ σ in 0..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x` for the same `f`
  coincide on `[0,T]` (weighted-in-time contraction `ul4_D_bound`, `Θ_λ → 0`, iteration of the factor `1/4`).
* `ul_mild_exists_of_adm`: Picard existence with the bound `‖u τ‖_k ≤ C ‖f‖_k` (`C` independent of `f`),
  strong continuity and the mild equation, under the hypothesis `UlDuhamelAdm` (`G1`):
  the Duhamel operator `w ↦ (τ ↦ ∫_0^τ P_{τ-σ} ulPert (w σ) dσ)` maps closure-valued, uniformly strongly
  continuous families on `[0,T]` into such families.  `ul_mild_exists` of the plan is this statement with `G1`
  discharged.  `G1` is NOT proved here (it needs (a) continuity in `τ` by the translation identity
  `v(τ₂) - v(τ₁) = ulD (w(·+h) - w) τ₁ τ₁ + ulD w h τ₂`, `h = τ₂ - τ₁`, with `ul4_D_bound` applied
  with `t0 = τ₂`, and (b) membership of `v(τ)` in `UlClosure`: Riemann sums of the `E_k`-valued continuous map
  `σ ↦ P_{τ-σ} ulPert (w σ)` on `[0, τ-η]`, which needs `ulPert g ∈ UlClosure` for `g ∈ C_c^∞ + const`
  (decay of `ulNL g` from `tail_conv`) and `P_t ulPert (UlClosure) ⊆ UlClosure`, then `η → 0`).
* `ul4_pert_est`, `ul4_D_bound`, `ul4_closure_tsum`, `ul4_P_ureg` are the reusable estimates.

Adjustments of the plan statements (documented, harmless): the data class index is `4 + d/2 < k`
(`ulClosure_cb` at `j = 4` gives `ulPert (w σ) ∈ C_b^2`); `ρ` Schwartz is `∃ ψ : SchwartzMap, ⇑ψ = ρ`;
`ul_mild_unique` quantifies the two solutions separately with the same `f` and needs no `2 ≤ d`;
strong continuity is the pointwise `ε-δ` form on `[0,T]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

/-! ### Toolkit for `UlClosure` -/

section Closure
variable {k : ℕ} {θ : Euc d → ℝ}

theorem ul4_scal (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ (a : ℝ) (u : Euc d → ℝ),
      ulNormE k θ (fun x => a * u x) ≤ ENNReal.ofReal (Cm * |a|) * ulNormE k θ u := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Cs, hCs, hsc⟩ := ul3_scalar k χ
  refine ⟨Ce * Cs * Ce, by positivity, fun a u => ?_⟩
  calc ulNormE k θ (fun x => a * u x) ≤ ENNReal.ofReal Ce * ulocNormE k χ (fun x => a * u x) := (hequ _).1
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal (Cs * |a|) * ulocNormE k χ u) := mul_le_mul' le_rfl (hsc a u)
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal (Cs * |a|) * (ENNReal.ofReal Ce * ulNormE k θ u)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hequ u).2)
    _ = ENNReal.ofReal (Ce * Cs * Ce * |a|) * ulNormE k θ u := by
        rw [ul4_ofReal_mul_mul (a := Cs * |a|) (b := Ce) (by positivity),
          ul4_ofReal_mul_mul (a := Ce) (b := Cs * |a| * Ce) hCe.le]; congr 2; ring

theorem ul4_closure_zero : UlClosure k θ (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun ε hε => ⟨fun _ => 0, ⟨fun _ => 0, 0, contDiff_const,
    HasCompactSupport.zero, by funext x; simp⟩, ?_⟩⟩
  have : ulNormE k θ (fun x : Euc d => (0 : ℝ) - 0) = 0 := by
    simp [ulNormE, HRS.MS.UlocCut.uc_zero]
  rw [this]; exact bot_le

theorem ul4_closure_approx {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (h : ∀ ε : ℝ, 0 < ε → ∃ e, UlClosure k θ e ∧ ulNormE k θ (fun x => f x - e x) ≤ ENNReal.ofReal ε) :
    UlClosure k θ f := by
  refine ⟨hf, fun ε hε => ?_⟩
  obtain ⟨e, he, h1⟩ := h (ε / 2) (by positivity)
  obtain ⟨g, hg, h2⟩ := he.2 (ε / 2) (by positivity)
  refine ⟨g, hg, ?_⟩
  have : (fun x => f x - g x) = fun x => (f x - e x) + (e x - g x) := by funext x; ring
  rw [this]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem ul4_ccc_add {g₁ g₂ : Euc d → ℝ} (h₁ : IsCcInftyPlusConst g₁) (h₂ : IsCcInftyPlusConst g₂) :
    IsCcInftyPlusConst (fun x => g₁ x + g₂ x) := by
  obtain ⟨a, c, ha, hac, rfl⟩ := h₁
  obtain ⟨b, e, hb, hbc, rfl⟩ := h₂
  exact ⟨fun x => a x + b x, c + e, ha.add hb, hac.add hbc, by funext x; ring⟩

theorem ul4_ccc_smul (r : ℝ) {g : Euc d → ℝ} (h : IsCcInftyPlusConst g) :
    IsCcInftyPlusConst (fun x => r * g x) := by
  obtain ⟨a, c, ha, hac, rfl⟩ := h
  refine ⟨fun x => r * a x, r * c, contDiff_const.mul ha, ?_, by funext x; ring⟩
  exact hac.mul_left

theorem ul4_closure_add {f g : Euc d → ℝ} (hf : UlClosure k θ f) (hg : UlClosure k θ g) :
    UlClosure k θ (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun ε hε => ?_⟩
  obtain ⟨e1, he1, h1⟩ := hf.2 (ε / 2) (by positivity)
  obtain ⟨e2, he2, h2⟩ := hg.2 (ε / 2) (by positivity)
  refine ⟨fun x => e1 x + e2 x, ul4_ccc_add he1 he2, ?_⟩
  have : (fun x => f x + g x - (e1 x + e2 x)) = fun x => (f x - e1 x) + (g x - e2 x) := by funext x; ring
  rw [this]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem ul4_closure_smul (hθ : IsUlCutoff θ) (r : ℝ) {f : Euc d → ℝ} (hf : UlClosure k θ f) :
    UlClosure k θ (fun x => r * f x) := by
  obtain ⟨Cm, hCm, hsc⟩ := ul4_scal k θ hθ
  refine ⟨contDiff_const.mul hf.1, fun ε hε => ?_⟩
  obtain ⟨e, he, h1⟩ := hf.2 (ε / (Cm * |r| + 1)) (by positivity)
  refine ⟨fun x => r * e x, ul4_ccc_smul r he, ?_⟩
  have : (fun x => r * f x - r * e x) = fun x => r * (f x - e x) := by funext x; ring
  rw [this]
  refine (hsc r _).trans ?_
  calc ENNReal.ofReal (Cm * |r|) * ulNormE k θ (fun x => f x - e x)
      ≤ ENNReal.ofReal (Cm * |r|) * ENNReal.ofReal (ε / (Cm * |r| + 1)) := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (Cm * |r| * (ε / (Cm * |r| + 1))) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hCm.le (abs_nonneg r)]

theorem ul4_closure_sub (hθ : IsUlCutoff θ) {f g : Euc d → ℝ} (hf : UlClosure k θ f)
    (hg : UlClosure k θ g) : UlClosure k θ (fun x => f x - g x) := by
  have := ul4_closure_add hf (ul4_closure_smul hθ (-1) hg)
  convert this using 2; ring

theorem ul4_closure_sum {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ)
    (h : ∀ i ∈ S, UlClosure k θ (f i)) : UlClosure k θ (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ul4_closure_zero (k := k) (θ := θ)
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact ul4_closure_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Series in the closure.**  A series of `UlClosure` elements with summable norms has a sum in
`UlClosure` with the corresponding norm bound. -/
theorem ul4_closure_tsum (hk : (2 : ℝ) + (d : ℝ) / 2 < k) (hθ : IsUlCutoff θ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ a : ℕ → Euc d → ℝ, (∀ n, UlClosure k θ (a n)) →
      Summable (fun n => (ulNormE k θ (a n)).toReal) →
      UlClosure k θ (fun x => ∑' n, a n x) ∧
      ulNormE k θ (fun x => ∑' n, a n x) ≤ ENNReal.ofReal (Ct * ∑' n, (ulNormE k θ (a n)).toReal) := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 2 hk θ hθ
  refine ⟨Ce * Ce, by positivity, fun a ha hs => ?_⟩
  set nrm : ℕ → ℝ := fun n => (ulNormE k θ (a n)).toReal with hnrm
  have hfin : ∀ n, ulNormE k θ (a n) < ⊤ := fun n => ul0_ulNormE_lt_top_of_closure k θ hθ (ha n)
  have hnrm0 : ∀ n, 0 ≤ nrm n := fun n => ENNReal.toReal_nonneg
  have hpt : ∀ n x, |a n x| ≤ Ccb * nrm n := fun n x => by
    have := ul3_cb_apply (hcb _ (ha n)).1 (Nat.zero_le 2) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (hcb _ (ha n)).2
  have hsum : ∀ x, Summable fun n => a n x := fun x =>
    Summable.of_norm_bounded (hs.mul_left Ccb) fun n => by rw [Real.norm_eq_abs]; exact hpt n x
  set f : Euc d → ℝ := fun x => ∑' n, a n x with hf
  -- smoothness
  have hC2 : ContDiff ℝ 2 f := by
    have := contDiff_tsum (𝕜 := ℝ) (N := (2 : ℕ∞)) (f := a) (v := fun _ n => Ccb * nrm n)
      (fun n => by exact_mod_cast (hcb _ (ha n)).1.1)
      (fun _ _ => hs.mul_left Ccb)
      (fun j n x hj => ((ul3_cb_apply (hcb _ (ha n)).1 (by exact_mod_cast hj) x).trans (hcb _ (ha n)).2))
    exact_mod_cast this
  -- tails
  have hmem : ∀ N, UlClosure k θ (fun x => ∑ n ∈ Finset.range N, a n x) := fun N =>
    ul4_closure_sum _ _ fun n _ => ha n
  have hlsc : ∀ N, ulocNormE k χ (fun x => f x - ∑ n ∈ Finset.range N, a n x) ≤
      ENNReal.ofReal (Ce * ∑' n, nrm (n + N)) := by
    intro N
    have hsN : Summable fun n => nrm (n + N) := (summable_nat_add_iff N).2 hs
    have hlim : ∀ x, Tendsto (fun M => ∑ n ∈ Finset.range M, a (n + N) x) atTop
        (𝓝 (f x - ∑ n ∈ Finset.range N, a n x)) := by
      intro x
      have h1 := ((summable_nat_add_iff N).2 (hsum x)).hasSum.tendsto_sum_nat
      have h2 := (hsum x).sum_add_tsum_nat_add N
      rw [hf]; simp only
      rw [← h2]; simpa using h1
    have hpart : ∀ M, ∑ n ∈ Finset.range M, nrm (n + N) ≤ ∑' n, nrm (n + N) := fun M =>
      hsN.sum_le_tsum _ (fun _ _ => hnrm0 _)
    refine ulocNormE_lsc k χ hχ (fun M x => ∑ n ∈ Finset.range M, a (n + N) x) _
      (Ccb * ∑' n, nrm (n + N)) (fun M x => ?_) hlim _ (fun M => ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun n _ => hpt (n + N) x).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hpart M) hCcb.le
    · refine (ul4_uloc_sum k χ _ _).trans ?_
      have h1 : ∀ n, ulocNormE k χ (a n) ≤ ENNReal.ofReal (Ce * nrm n) := fun n =>
        ((hequ _).2).trans (by
          rw [ENNReal.ofReal_mul hCe.le, hnrm, ENNReal.ofReal_toReal (hfin n).ne])
      refine (Finset.sum_le_sum fun n _ => h1 (n + N)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg hCe.le (hnrm0 _)), ← Finset.mul_sum]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpart M) hCe.le)
  have hnorm : ∀ N, ulNormE k θ (fun x => f x - ∑ n ∈ Finset.range N, a n x) ≤
      ENNReal.ofReal (Ce * Ce * ∑' n, nrm (n + N)) := fun N => by
    refine ((hequ _).1).trans ?_
    calc ENNReal.ofReal Ce * ulocNormE k χ _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Ce * ∑' n, nrm (n + N)) :=
          mul_le_mul' le_rfl (hlsc N)
      _ = _ := by rw [← ENNReal.ofReal_mul hCe.le]; congr 1; ring
  refine ⟨ul4_closure_approx hC2 fun ε hε => ?_, ?_⟩
  · have htail : Tendsto (fun N => ∑' n, nrm (n + N)) atTop (𝓝 0) := tendsto_sum_nat_add nrm
    obtain ⟨N, hN⟩ := (htail.const_mul (Ce * Ce)).eventually (Iio_mem_nhds (by simpa using hε : Ce * Ce * 0 < ε)) |>.exists
    refine ⟨_, hmem N, (hnorm N).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact hN.le
  · have := hnorm 0
    simpa [hf] using this

end Closure

/-! ### The weight integral `Θ_λ = ∫_0^T r^{-γ} e^{-λ r} dr` -/

/-- `∫_0^T r^{-γ} e^{-λ r} dr` -/
def ul4Th (γ T lam : ℝ) : ℝ := ∫ r in (0 : ℝ)..T, r ^ (-γ) * Real.exp (-(lam * r))

theorem ul4_Th_int {γ : ℝ} (hγ : γ < 1) (T lam : ℝ) {a b : ℝ} :
    IntervalIntegrable (fun r : ℝ => r ^ (-γ) * Real.exp (-(lam * r))) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn
    (by fun_prop)

theorem ul4_Th_nonneg {γ : ℝ} {T : ℝ} (hT : 0 ≤ T) (lam : ℝ) : 0 ≤ ul4Th γ T lam :=
  intervalIntegral.integral_nonneg hT fun r hr => by
    have := Real.rpow_nonneg hr.1 (-γ); positivity

theorem ul4_Th_tendsto {γ : ℝ} (hγ : γ < 1) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun lam => ul4Th γ T lam) atTop (𝓝 0) := by
  have hI : IntervalIntegrable (fun r : ℝ => r ^ (-γ)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := 0) (b := T)
    (F := fun (lam : ℝ) (r : ℝ) => r ^ (-γ) * Real.exp (-(lam * r))) (f := fun _ => (0 : ℝ))
    (l := atTop) (fun r => ‖r ^ (-γ)‖)
    (Filter.Eventually.of_forall fun lam => by
      rw [uIoc_of_le hT]; exact (ul4_Th_int hγ T lam (a := 0) (b := T)).1.aestronglyMeasurable) ?_ hI.norm ?_
  · simpa [ul4Th] using h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le hT] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-(lam * r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.1])
    rw [Real.norm_eq_abs] at *
    nlinarith [abs_nonneg (r ^ (-γ))]
  · refine Filter.Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le hT] at hr
    have : Tendsto (fun lam : ℝ => Real.exp (-(lam * r))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hr.1))
    simpa using this.const_mul (r ^ (-γ))

theorem ul4_rpow_anti {γ : ℝ} (hγ : 0 ≤ γ) {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    x ^ (-γ) ≤ y ^ (-γ) := by
  rw [Real.rpow_neg (hy.le.trans hxy), Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hy γ) (Real.rpow_le_rpow hy.le hxy hγ)

/-- `∫_0^τ (τ-σ)^{-γ} e^{λσ} dσ ≤ e^{λτ} Θ_λ` -/
theorem ul4_weight_int {γ : ℝ} (hγ : γ < 1) {τ T lam : ℝ} (hτ : 0 ≤ τ) (hτT : τ ≤ T) :
    ∫ σ in (0 : ℝ)..τ, (τ - σ) ^ (-γ) * Real.exp (lam * σ) ≤ Real.exp (lam * τ) * ul4Th γ T lam := by
  have e : ∀ σ : ℝ, (τ - σ) ^ (-γ) * Real.exp (lam * σ) =
      Real.exp (lam * τ) * ((τ - σ) ^ (-γ) * Real.exp (-(lam * (τ - σ)))) := fun σ => by
    rw [← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := τ)
    (fun r : ℝ => r ^ (-γ) * Real.exp (-(lam * r))) τ
  simp only [sub_self, sub_zero] at h1
  rw [h1, ul4Th]
  refine intervalIntegral.integral_mono_interval le_rfl hτ hτT ?_ (ul4_Th_int hγ T lam)
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => by
    have := Real.rpow_nonneg hr.1.le (-γ)
    show 0 ≤ r ^ (-γ) * Real.exp (-(lam * r))
    positivity)

/-! ### The Duhamel operator -/

/-- `w` is a strongly continuous family in `UlClosure k θ` on `[0,τ]`. -/
structure UlReg (k : ℕ) (θ : Euc d → ℝ) (τ : ℝ) (w : ℝ → Euc d → ℝ) : Prop where
  mem : ∀ σ ∈ Icc 0 τ, UlClosure k θ (w σ)
  cont : ∀ σ₀ ∈ Icc 0 τ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc 0 τ, |σ - σ₀| < δ →
    ulNormE k θ (fun x => w σ x - w σ₀ x) ≤ ENNReal.ofReal ε

/-- The shifted Duhamel integral `∫_0^τ P_{t0-σ}(ulPert (w σ)) dσ`. -/
def ulD (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (c : Euc d → Euc d) (w : ℝ → Euc d → ℝ) (τ t0 : ℝ) (x : Euc d) : ℝ :=
  ∫ σ in (0 : ℝ)..τ, ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x

section Duhamel
variable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
  (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) {c : Euc d → Euc d} (hc : IsSmoothBounded c)
  (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : (4 : ℝ) + (d : ℝ) / 2 < k)
  {θ : Euc d → ℝ} (hθ : IsUlCutoff θ)

include hs0 hsd hρ hc hk hθ in
/-- `ulPert (w σ)` is continuous in `σ` for the sup norm -/
theorem ul4_g_cont {τ : ℝ} {w : ℝ → Euc d → ℝ} (hw : UlReg k θ τ w) {σ₀ : ℝ} (h0 : σ₀ ∈ Icc 0 τ)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc 0 τ, |σ - σ₀| < δ → ∀ x,
      |ulPert s M ρ c (w σ) x - ulPert s M ρ c (w σ₀) x| ≤ ε := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 hk θ hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb hs0 hsd M ρ hρ hc
  obtain ⟨δ, hδ, hw'⟩ := hw.cont σ₀ h0 (ε / (Cp * Ccb + 1)) (by positivity)
  refine ⟨δ, hδ, fun σ hσ hσδ x => ?_⟩
  have hd := hcb _ (ul4_closure_sub hθ (hw.mem σ hσ) (hw.mem σ₀ h0))
  rw [← ul4_pert_sub hs0 hsd M ρ hρ c (hcb _ (hw.mem σ hσ)).1 (hcb _ (hw.mem σ₀ h0)).1 x]
  refine ((hpcb _ hd.1).2 x).trans ?_
  have h1 : (ulNormE k θ (fun x => w σ x - w σ₀ x)).toReal ≤ ε / (Cp * Ccb + 1) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hw' σ hσ hσδ)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc Cp * cbNorm 4 (fun x => w σ x - w σ₀ x) ≤ Cp * (Ccb * (ε / (Cp * Ccb + 1))) :=
        mul_le_mul_of_nonneg_left (hd.2.trans (mul_le_mul_of_nonneg_left h1 hCcb.le)) hCp0
    _ ≤ ε := by
        rw [← mul_assoc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hCp0 hCcb.le]

include hs0 hsd hρ hc hν hk hθ in
/-- the integrand of `ulD` is continuous in `σ` -/
theorem ul4_Phi_cont {τ t0 : ℝ} (hτ : τ ≤ t0) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ τ w) (x : Euc d) :
    ContinuousOn (fun σ => ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x) (Icc 0 τ) := by
  intro σ₀ h0
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 hk θ hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb hs0 hsd M ρ hρ hc
  have hg2 : ∀ σ ∈ Icc 0 τ, MemCb 2 (ulPert s M ρ c (w σ)) := fun σ hσ =>
    (hpcb _ (hcb _ (hw.mem σ hσ)).1).1
  have hgT : ContinuousOn (fun s' => ouSg Q ν s' (ulPert s M ρ c (w σ₀)) x) (Ici 0) :=
    ul4_ouSg_cont_time Q hν (hg2 σ₀ h0).1 (M := cbNorm 2 (ulPert s M ρ c (w σ₀)))
      (fun i hi y => ul3_cb_apply (hg2 σ₀ h0) hi y) x
  have hT0 : ContinuousWithinAt (fun σ => ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ₀)) x) (Icc 0 τ) σ₀ :=
    (hgT.comp (continuous_const.sub continuous_id).continuousOn fun σ hσ =>
      mem_Ici.2 (by show (0 : ℝ) ≤ t0 - σ; linarith [hσ.2])) σ₀ h0
  rw [Metric.continuousWithinAt_iff] at hT0 ⊢
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := ul4_g_cont hs0 hsd M ρ hρ hc hk hθ hw h0 (half_pos hε)
  obtain ⟨δ2, hδ2, h2⟩ := hT0 (ε / 2) (half_pos hε)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun σ hσ hdist => ?_⟩
  have hd1 : |σ - σ₀| < δ1 := lt_of_lt_of_le (by simpa [Real.dist_eq] using hdist) (min_le_left _ _)
  have hd2 : dist σ σ₀ < δ2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hm1 := (hg2 σ hσ).1.continuous.measurable
  have hm0 := (hg2 σ₀ h0).1.continuous.measurable
  obtain ⟨B1, hB1⟩ := ul3C_bdd_of_cb (hg2 σ hσ)
  obtain ⟨B0, hB0⟩ := ul3C_bdd_of_cb (hg2 σ₀ h0)
  have e : ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x - ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ₀)) x =
      ouSg Q ν (t0 - σ) (fun y => ulPert s M ρ c (w σ) y - ulPert s M ρ c (w σ₀) y) x := by
    rw [ul3C_sub_lin Q ν _ hm1 hm0 hB1 hB0]
  have h3 : |ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x - ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ₀)) x|
      ≤ ε / 2 := by
    rw [e]; exact ul4_ouSg_abs_le Q ν _ (fun y => h1 σ hσ hd1 y) x
  have h4 := h2 hσ hd2
  rw [Real.dist_eq] at h4 ⊢
  calc _ = |(ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x - ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ₀)) x) +
        (ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ₀)) x - ouSg Q ν (t0 - σ₀) (ulPert s M ρ c (w σ₀)) x)| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

include hs0 hsd hρ hc hν hk hθ in
/-- **Norm bound of the Duhamel integral.**  If `‖w σ‖_k ≤ W e^{λσ}` on `[0,τ]` then
`‖∫_0^τ P_{t0-σ} ulPert(w σ) dσ‖_k ≤ K_G W e^{λτ} Θ_λ` (`0 < τ ≤ t0 ≤ T`). -/
theorem ul4_D_bound (T : ℝ) :
    ∃ KG : ℝ, 0 < KG ∧ ∀ {τ t0 : ℝ}, 0 < τ → τ ≤ t0 → t0 ≤ T → ∀ {w : ℝ → Euc d → ℝ},
      UlReg k θ τ w → ∀ {lam W : ℝ}, 0 ≤ lam → 0 ≤ W →
      (∀ σ ∈ Icc 0 τ, ulNormE k θ (w σ) ≤ ENNReal.ofReal (W * Real.exp (lam * σ))) →
      ulNormE k θ (fun x => ulD Q ν s M ρ c w τ t0 x) ≤
        ENNReal.ofReal (KG * W * Real.exp (lam * τ) * ul4Th (ul4gam d s) T lam) := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨K, hK, hest⟩ := ul4_pert_est hs0 hsd M ρ hρ hc Q hν T k hk θ hθ
  obtain ⟨Ctb, hCtb, htb⟩ := ul4_time_bound k χ hχ
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 hk θ hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb hs0 hsd M ρ hρ hc
  obtain ⟨γ0, γ1⟩ := ul4_gam_bounds hsd
  set γ := ul4gam d s with hγ
  refine ⟨Ce * Ctb * Ce * K, by positivity, fun {τ t0} hτ hτt hT0 {w} hw {lam W} hlam hW0 hW => ?_⟩
  have hT : 0 ≤ T := by linarith
  have hΘ0 : 0 ≤ ul4Th γ T lam := ul4_Th_nonneg hT lam
  set KG : ℝ := Ce * Ctb * Ce * K with hKG
  have hKG0 : 0 < KG := by positivity
  set cl : ℝ → ℝ := fun σ => max 0 (min σ τ) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ σ, cl σ ∈ Icc 0 τ := fun σ => ⟨le_max_left _ _, max_le hτ.le (min_le_right _ _)⟩
  have hcle : ∀ σ ∈ Icc 0 τ, cl σ = σ := fun σ hσ => by
    simp only [hcl, min_eq_left hσ.2, max_eq_right hσ.1]
  have hg2 : ∀ σ ∈ Icc 0 τ, MemCb 2 (ulPert s M ρ c (w σ)) := fun σ hσ =>
    (hpcb _ (hcb _ (hw.mem σ hσ)).1).1
  set Fc : ℝ → Euc d → ℝ := fun σ x =>
    ouSg Q ν (t0 - cl σ) (ulPert s M ρ c (w (cl σ))) x with hFc
  have hFcont : ∀ x, Continuous fun σ => Fc σ x := fun x =>
    (ul4_Phi_cont hs0 hsd M ρ hρ hc Q hν hk hθ hτt hw x).comp_continuous hclc hclm
  have hFmeas : ∀ σ, Measurable (Fc σ) := fun σ =>
    ul4_ouSg_measurable Q ν _ (hg2 (cl σ) (hclm σ)).1.continuous
  have hFm : Measurable (Function.uncurry Fc) :=
    measurable_uncurry_of_continuous_of_measurable hFcont hFmeas
  have key : ∀ η : ℝ, 0 < η → ulNormE k θ (fun x => ulD Q ν s M ρ c w τ t0 x) ≤
      ENNReal.ofReal (KG * (W + η) * Real.exp (lam * τ) * ul4Th γ T lam) := by
    intro η hη
    set W' : ℝ := W + η with hW'
    have hW'0 : 0 < W' := by positivity
    have hEτ : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp (by positivity)
    -- sup bound
    have hFB : ∀ σ ∈ Ioo 0 τ, ∀ x, |Fc σ x| ≤ Cp * (Ccb * (W' * Real.exp (lam * τ))) := by
      intro σ hσ x
      have hσ' : σ ∈ Icc 0 τ := Ioo_subset_Icc_self hσ
      simp only [hFc, hcle σ hσ']
      obtain ⟨hcb4, hcbn⟩ := hcb _ (hw.mem σ hσ')
      refine (ul4_ouSg_abs_le Q ν _ (fun y => (hpcb _ hcb4).2 y) x).trans ?_
      have h2 : (ulNormE k θ (w σ)).toReal ≤ W' * Real.exp (lam * τ) := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hW σ hσ')
        rw [ENNReal.toReal_ofReal (by positivity)] at this
        refine this.trans ?_
        gcongr
        · linarith
        · exact hσ'.2
      exact mul_le_mul_of_nonneg_left (hcbn.trans (mul_le_mul_of_nonneg_left h2 hCcb.le)) hCp0
    have hFn : ∀ σ ∈ Ioo 0 τ, ulocNormE k χ (Fc σ) ≤
        ENNReal.ofReal (Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) := by
      intro σ hσ
      have hσ' := Ioo_subset_Icc_self hσ
      have e : Fc σ = fun x => ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)) x := by
        funext x; simp only [hFc, hcle σ hσ']
      rw [e]
      have ht : t0 - σ ∈ Ioc 0 T := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      refine (hequ _).2.trans ?_
      calc ENNReal.ofReal Ce * ulNormE k θ (ouSg Q ν (t0 - σ) (ulPert s M ρ c (w σ)))
          ≤ ENNReal.ofReal Ce * (ENNReal.ofReal (K * (t0 - σ) ^ (-γ)) * ulNormE k θ (w σ)) :=
            mul_le_mul' le_rfl (hest _ ht _ (hw.mem σ hσ'))
        _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal (K * (τ - σ) ^ (-γ)) *
              ENNReal.ofReal (W' * Real.exp (lam * σ))) := by
            refine mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ((hW σ hσ').trans
              (ENNReal.ofReal_le_ofReal ?_)))
            · exact mul_le_mul_of_nonneg_left (ul4_rpow_anti (by linarith) (by linarith [hσ.2])
                (by linarith)) hK.le
            · exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = ENNReal.ofReal (Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg (by linarith [hσ.2]) _)),
              ← ENNReal.ofReal_mul hCe.le]
            congr 1; ring
    have ha_meas : Measurable (fun σ : ℝ => Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) :=
      measurable_const.mul (((measurable_const.sub measurable_id).pow_const (-γ)).mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
    have hint0 : IntervalIntegrable (fun σ : ℝ => (τ - σ) ^ (-γ)) volume 0 τ := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := -γ) (by linarith) (a := 0) (b := τ)).comp_sub_left τ
      simpa using this.symm
    have ha_int : IntervalIntegrable
        (fun σ : ℝ => Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) volume 0 τ :=
      (hint0.mul_continuousOn (by fun_prop : ContinuousOn (fun σ : ℝ => Real.exp (lam * σ)) _)).const_mul _
    have ha0 : 0 < Ce * K * W' * τ ^ (-γ) := by positivity
    have hal : ∀ σ ∈ Ioo 0 τ, Ce * K * W' * τ ^ (-γ) ≤
        Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ)) := fun σ hσ => by
      have h1 : τ ^ (-γ) ≤ (τ - σ) ^ (-γ) :=
        ul4_rpow_anti (by linarith) (by linarith [hσ.2]) (by linarith [hσ.1])
      have h2 : 1 ≤ Real.exp (lam * σ) := Real.one_le_exp (by nlinarith [hσ.1])
      calc Ce * K * W' * τ ^ (-γ) = Ce * K * W' * (τ ^ (-γ) * 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by norm_num)
            (Real.rpow_nonneg (by linarith [hσ.2]) _)) (by positivity)
    have htb' := htb hτ Fc hFm _ hFB _ ha_meas ha_int _ ha0 hal hFn
    have hD : ∀ x, ulD Q ν s M ρ c w τ t0 x = ∫ σ in (0 : ℝ)..τ, Fc σ x := by
      intro x
      unfold ulD
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [uIcc_of_le hτ.le] at hσ
      simp only [hFc, hcle σ hσ]
    have hD' : (fun x => ulD Q ν s M ρ c w τ t0 x) = fun x => ∫ σ in (0 : ℝ)..τ, Fc σ x := funext hD
    rw [hD']
    refine ((hequ _).1).trans ?_
    have hI : (∫ σ in (0 : ℝ)..τ, Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) ≤
        Ce * K * W' * (Real.exp (lam * τ) * ul4Th γ T lam) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (ul4_weight_int γ1 hτ.le (hτt.trans hT0)) (by positivity)
    calc ENNReal.ofReal Ce * ulocNormE k χ (fun x => ∫ σ in (0 : ℝ)..τ, Fc σ x)
        ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Ctb * ∫ σ in (0 : ℝ)..τ,
            Ce * K * W' * ((τ - σ) ^ (-γ) * Real.exp (lam * σ))) := mul_le_mul' le_rfl htb'
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Ctb * (Ce * K * W' * (Real.exp (lam * τ) * ul4Th γ T lam))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hI hCtb.le))
      _ = ENNReal.ofReal (KG * W' * Real.exp (lam * τ) * ul4Th γ T lam) := by
          rw [← ENNReal.ofReal_mul hCe.le]; congr 1; rw [hKG]; ring
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  set A : ℝ := KG * Real.exp (lam * τ) * ul4Th γ T lam with hA
  have hA0 : 0 ≤ A := by positivity
  set δ : ℝ := (ε : ℝ) / (A + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine (key δ hδ0).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) hε'.le]
  apply ENNReal.ofReal_le_ofReal
  have : (A + 1) * δ = ε := by rw [hδ]; field_simp
  nlinarith [mul_nonneg hA0 hδ0.le]

theorem ul4_reg_mono {τ τ' : ℝ} (h : τ' ≤ τ) {w : ℝ → Euc d → ℝ} (hw : UlReg k θ τ w) :
    UlReg k θ τ' w :=
  ⟨fun σ hσ => hw.mem σ ⟨hσ.1, hσ.2.trans h⟩, fun σ₀ h0 ε hε => by
    obtain ⟨δ, hδ, hh⟩ := hw.cont σ₀ ⟨h0.1, h0.2.trans h⟩ ε hε
    exact ⟨δ, hδ, fun σ hσ => hh σ ⟨hσ.1, hσ.2.trans h⟩⟩⟩

theorem ul4_neg (hθ : IsUlCutoff θ) : ∃ Cn : ℝ, 0 < Cn ∧ ∀ f : Euc d → ℝ,
    ulNormE k θ (fun x => -f x) ≤ ENNReal.ofReal Cn * ulNormE k θ f := by
  obtain ⟨Cm, hCm, hsc⟩ := ul4_scal k θ hθ
  refine ⟨Cm, hCm, fun f => ?_⟩
  have := hsc (-1) f
  simpa [neg_one_mul] using this

/-- a strongly continuous family is bounded on a compact interval -/
theorem ul4_bdd (hθ : IsUlCutoff θ) {T : ℝ} {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) :
    ∃ W : ℝ, ∀ σ ∈ Icc 0 T, ulNormE k θ (w σ) ≤ ENNReal.ofReal W := by
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  set φ : ℝ → ℝ := fun σ => (ulNormE k θ (w σ)).toReal with hφ
  have hfin : ∀ σ ∈ Icc 0 T, ulNormE k θ (w σ) < ⊤ := fun σ hσ =>
    ul0_ulNormE_lt_top_of_closure k θ hθ (hw.mem σ hσ)
  have hcont : ContinuousOn φ (Icc 0 T) := by
    intro σ₀ h0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hw.cont σ₀ h0 (ε / (Cn + 2)) (by positivity)
    refine ⟨δ, hδ, fun σ hσ hd => ?_⟩
    have h1 := h σ hσ (by simpa [Real.dist_eq] using hd)
    have h2 : ulNormE k θ (fun x => w σ₀ x - w σ x) ≤ ENNReal.ofReal (Cn * (ε / (Cn + 2))) := by
      have e : (fun x => w σ₀ x - w σ x) = fun x => -(w σ x - w σ₀ x) := by funext x; ring
      rw [e]
      refine (hneg _).trans ?_
      rw [ENNReal.ofReal_mul hCn.le]
      exact mul_le_mul' le_rfl h1
    have h3 := ul0_ulNormE_sub_le k θ (w σ) (w σ₀)
    have h4 := ul0_ulNormE_sub_le k θ (w σ₀) (w σ)
    have hf1 := hfin σ hσ
    have hf0 := hfin σ₀ h0
    have t1 : (ulNormE k θ (fun x => w σ x - w σ₀ x)).toReal ≤ ε / (Cn + 2) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have t2 : (ulNormE k θ (fun x => w σ₀ x - w σ x)).toReal ≤ Cn * (ε / (Cn + 2)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have u1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1,
      hf0.ne⟩) h3
    have u2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2,
      hf1.ne⟩) h4
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hf0.ne] at u1
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2) hf1.ne] at u2
    rw [Real.dist_eq, abs_lt]
    simp only [hφ]
    have hp : 0 < ε / (Cn + 2) := by positivity
    have : (Cn + 2) * (ε / (Cn + 2)) = ε := by field_simp
    constructor <;> nlinarith [mul_pos hCn hp]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun σ hσ => ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin σ hσ).ne]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa [hφ, abs_of_nonneg ENNReal.toReal_nonneg] using hC σ hσ))

theorem ul4_reg_sub (hθ : IsUlCutoff θ) {τ : ℝ} {u u' : ℝ → Euc d → ℝ} (hu : UlReg k θ τ u)
    (hu' : UlReg k θ τ u') : UlReg k θ τ (fun σ y => u σ y - u' σ y) := by
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  refine ⟨fun σ hσ => ul4_closure_sub hθ (hu.mem σ hσ) (hu'.mem σ hσ), fun σ₀ h0 ε hε => ?_⟩
  obtain ⟨δ1, hδ1, h1⟩ := hu.cont σ₀ h0 (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hu'.cont σ₀ h0 (ε / (2 * Cn)) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun σ hσ hd => ?_⟩
  have e : (fun x => (u σ x - u' σ x) - (u σ₀ x - u' σ₀ x)) =
      fun x => (u σ x - u σ₀ x) + (-(u' σ x - u' σ₀ x)) := by funext x; ring
  rw [e]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  have a1 := h1 σ hσ (lt_of_lt_of_le hd (min_le_left _ _))
  have a2 := (hneg _).trans (mul_le_mul' (le_refl (ENNReal.ofReal Cn))
    (h2 σ hσ (lt_of_lt_of_le hd (min_le_right _ _))))
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal Cn * ENNReal.ofReal (ε / (2 * Cn)) := add_le_add a1 a2
    _ = ENNReal.ofReal (ε / 2 + ε / 2) := by
        rw [← ENNReal.ofReal_mul hCn.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp
    _ = ENNReal.ofReal ε := by congr 1; ring

include hs0 hsd hρ hc hν hk hθ in
theorem ul4_D_sub {τ t0 : ℝ} (hτ : 0 ≤ τ) (hτt : τ ≤ t0) {u u' : ℝ → Euc d → ℝ} (hu : UlReg k θ τ u)
    (hu' : UlReg k θ τ u') (x : Euc d) :
    ulD Q ν s M ρ c (fun σ y => u σ y - u' σ y) τ t0 x =
      ulD Q ν s M ρ c u τ t0 x - ulD Q ν s M ρ c u' τ t0 x := by
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 hk θ hθ
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb hs0 hsd M ρ hρ hc
  unfold ulD
  rw [← intervalIntegral.integral_sub
    ((ul4_Phi_cont hs0 hsd M ρ hρ hc Q hν hk hθ hτt hu x).intervalIntegrable_of_Icc hτ)
    ((ul4_Phi_cont hs0 hsd M ρ hρ hc Q hν hk hθ hτt hu' x).intervalIntegrable_of_Icc hτ)]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hτ] at hσ
  have hg4 := fun v (hv : UlReg k θ τ v) => (hcb _ (hv.mem σ hσ)).1
  have e : ulPert s M ρ c (fun y => u σ y - u' σ y) = fun y => ulPert s M ρ c (u σ) y - ulPert s M ρ c (u' σ) y := by
    funext y; exact ul4_pert_sub hs0 hsd M ρ hρ c (hg4 u hu) (hg4 u' hu') y
  simp only [e]
  obtain ⟨B1, hB1⟩ := ul3C_bdd_of_cb ((hpcb _ (hg4 u hu)).1)
  obtain ⟨B2, hB2⟩ := ul3C_bdd_of_cb ((hpcb _ (hg4 u' hu')).1)
  rw [ul3C_sub_lin Q ν _ ((hpcb _ (hg4 u hu)).1.1.continuous.measurable)
    ((hpcb _ (hg4 u' hu')).1.1.continuous.measurable) hB1 hB2]

end Duhamel

/-- **`ul_mild_unique`**: two mild solutions in `C([0,T]; E_k)` with the same datum coincide. -/
theorem ul_mild_unique {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k) (T ν : ℝ) (hν : 0 < ν)
    (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (c : Euc d → Euc d) (hc : IsSmoothBounded c) (f : Euc d → ℝ) (u u' : ℝ → Euc d → ℝ)
    (hu : ∀ τ ∈ Icc 0 T, UlClosure k θ (u τ)) (hu' : ∀ τ ∈ Icc 0 T, UlClosure k θ (u' τ))
    (hcu : ∀ τ₀ ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc 0 T, |τ - τ₀| < δ →
      ulNormE k θ (fun x => u τ x - u τ₀ x) ≤ ENNReal.ofReal ε)
    (hcu' : ∀ τ₀ ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc 0 T, |τ - τ₀| < δ →
      ulNormE k θ (fun x => u' τ x - u' τ₀ x) ≤ ENNReal.ofReal ε)
    (heq : ∀ τ ∈ Icc 0 T, ∀ x, u τ x = ouSg Q ν τ f x +
      ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x)
    (heq' : ∀ τ ∈ Icc 0 T, ∀ x, u' τ x = ouSg Q ν τ f x +
      ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u' σ)) x) :
    ∀ τ ∈ Icc 0 T, u τ = u' τ := by
  by_cases hT : 0 ≤ T
  swap
  · intro τ hτ; exact absurd (hτ.1.trans hτ.2) hT
  have hU : UlReg k θ T u := ⟨hu, hcu⟩
  have hU' : UlReg k θ T u' := ⟨hu', hcu'⟩
  set w : ℝ → Euc d → ℝ := fun σ y => u σ y - u' σ y with hwdef
  have hw : UlReg k θ T w := ul4_reg_sub hθ hU hU'
  have hweq : ∀ τ ∈ Icc 0 T, ∀ x, w τ x = ulD Q ν s M ρ c w τ τ x := by
    intro τ hτ x
    rw [ul4_D_sub hs0 hsd M ρ hρ hc Q hν hk hθ hτ.1 le_rfl (ul4_reg_mono hτ.2 hU) (ul4_reg_mono hτ.2 hU') x]
    simp only [hwdef, ulD]
    rw [heq τ hτ x, heq' τ hτ x]; ring
  obtain ⟨W0, hW0⟩ := ul4_bdd hθ hw
  set W1 : ℝ := max W0 0 with hW1
  have hW10 : 0 ≤ W1 := le_max_right _ _
  have hW1b : ∀ σ ∈ Icc 0 T, ulNormE k θ (w σ) ≤ ENNReal.ofReal W1 := fun σ hσ =>
    (hW0 σ hσ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  obtain ⟨KG, hKG, hD⟩ := ul4_D_bound hs0 hsd M ρ hρ hc Q hν hk hθ T
  obtain ⟨γ0, γ1⟩ := ul4_gam_bounds hsd
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ KG * ul4Th (ul4gam d s) T lam ≤ 1 / 4 := by
    have h := (ul4_Th_tendsto γ1 hT).const_mul KG
    rw [mul_zero] at h
    obtain ⟨lam, hl⟩ := ((h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨lam, hl.2, hl.1.le⟩
  have key : ∀ n : ℕ, ∀ σ ∈ Icc 0 T,
      ulNormE k θ (w σ) ≤ ENNReal.ofReal (W1 * (1 / 4) ^ n * Real.exp (lam * σ)) := by
    intro n
    induction n with
    | zero =>
      intro σ hσ
      refine (hW1b σ hσ).trans (ENNReal.ofReal_le_ofReal ?_)
      have : 1 ≤ Real.exp (lam * σ) := Real.one_le_exp (by nlinarith [hσ.1])
      simpa using mul_le_mul_of_nonneg_left this hW10
    | succ n ih =>
      intro σ hσ
      rcases hσ.1.eq_or_lt with h0 | hpos
      · subst h0
        have : w 0 = fun _ => 0 := by
          funext x; rw [hweq 0 hσ x]; simp [ulD]
        rw [this]
        have hz : ulNormE k θ (fun _ : Euc d => (0 : ℝ)) = 0 := by
          simp [ulNormE, HRS.MS.UlocCut.uc_zero]
        rw [hz]; exact bot_le
      · have hfun : w σ = fun x => ulD Q ν s M ρ c w σ σ x := funext (hweq σ hσ)
        rw [hfun]
        refine (hD hpos le_rfl hσ.2 (ul4_reg_mono hσ.2 hw) hlam0 (by positivity)
          (fun σ' hσ' => ih σ' ⟨hσ'.1, hσ'.2.trans hσ.2⟩)).trans (ENNReal.ofReal_le_ofReal ?_)
        have hE := (Real.exp_pos (lam * σ)).le
        have hΘ : KG * ul4Th (ul4gam d s) T lam ≤ 1 / 4 := hlam
        calc KG * (W1 * (1 / 4) ^ n) * Real.exp (lam * σ) * ul4Th (ul4gam d s) T lam
            = (W1 * (1 / 4) ^ n * Real.exp (lam * σ)) * (KG * ul4Th (ul4gam d s) T lam) := by ring
          _ ≤ (W1 * (1 / 4) ^ n * Real.exp (lam * σ)) * (1 / 4) :=
              mul_le_mul_of_nonneg_left hΘ (by positivity)
          _ = W1 * (1 / 4) ^ (n + 1) * Real.exp (lam * σ) := by ring
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 0 (by simpa using (by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity] :
    (d : ℝ) / 2 < k)) θ hθ
  intro τ hτ
  have hw0 : ∀ x, w τ x = 0 := by
    intro x
    obtain ⟨hmem, hnorm⟩ := hcb _ (hw.mem τ hτ)
    have hfin := ul0_ulNormE_lt_top_of_closure k θ hθ (hw.mem τ hτ)
    have hle : ∀ n : ℕ, (ulNormE k θ (w τ)).toReal ≤ W1 * Real.exp (lam * τ) * (1 / 4) ^ n := fun n => by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (key n τ hτ)
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      linarith [this]
    have ht : Tendsto (fun n : ℕ => W1 * Real.exp (lam * τ) * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul (W1 * Real.exp (lam * τ))
    have h0 : (ulNormE k θ (w τ)).toReal ≤ 0 := ge_of_tendsto' ht hle
    have h1 := ul3_cb_apply hmem (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    have h2 : |w τ x| ≤ 0 := h1.trans (hnorm.trans (by nlinarith [ENNReal.toReal_nonneg (a := ulNormE k θ (w τ))]))
    exact abs_nonpos_iff.1 h2
  funext x
  have := hw0 x
  simp only [hwdef] at this
  linarith

/-! ### Uniformly strongly continuous families and the existence assembly -/

/-- a closure-valued family on `[0,T]`, uniformly strongly continuous in `ulNormE` -/
structure UlUReg (k : ℕ) (θ : Euc d → ℝ) (T : ℝ) (w : ℝ → Euc d → ℝ) : Prop where
  mem : ∀ σ ∈ Icc 0 T, UlClosure k θ (w σ)
  unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc 0 T, ∀ σ' ∈ Icc 0 T, |σ - σ'| < δ →
    ulNormE k θ (fun x => w σ x - w σ' x) ≤ ENNReal.ofReal ε

theorem UlUReg.toReg {k : ℕ} {θ : Euc d → ℝ} {T : ℝ} {w : ℝ → Euc d → ℝ} (h : UlUReg k θ T w) :
    UlReg k θ T w :=
  ⟨h.mem, fun σ₀ h0 ε hε => by
    obtain ⟨δ, hδ, h'⟩ := h.unif ε hε
    exact ⟨δ, hδ, fun σ hσ hd => h' σ hσ σ₀ h0 hd⟩⟩

/-- **The missing lemma (`G1`).**  The Duhamel operator `w ↦ (τ ↦ ∫_0^τ P_{τ-σ} ulPert (w σ) dσ)` maps
closure-valued, uniformly strongly continuous families on `[0,T]` into such families.  Not proved
in this packet (see the docstring of `ul_mild_exists_of_adm`). -/
def UlDuhamelAdm (Q : Matrix (Fin d) (Fin d) ℝ) (ν s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (ρ : Euc d → ℝ) (c : Euc d → Euc d) (k : ℕ) (θ : Euc d → ℝ) (T : ℝ) : Prop :=
  ∀ w : ℝ → Euc d → ℝ, UlUReg k θ T w → UlUReg k θ T (fun τ y => ulD Q ν s M ρ c w τ τ y)

/-- the free evolution `σ ↦ P_σ f` is a uniformly strongly continuous family -/
theorem ul4_P_ureg (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (k : ℕ) (θ : Euc d → ℝ)
    (hθ : IsUlCutoff θ) (hk : (2 : ℝ) + (d : ℝ) / 2 < k) {T : ℝ} {f : Euc d → ℝ}
    (hf : UlClosure k θ f) : UlUReg k θ T (fun σ => ouSg Q ν σ f) := by
  have hk0 : (d : ℝ) / 2 < k := by linarith [(by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)]
  obtain ⟨C, hC, hbd⟩ := ul3C_ulNorm_bdd Q ν T k θ hθ hk0
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  obtain ⟨hfc, Bf, hBf⟩ := ul3C_closure_bdd k θ hθ hk0 hf
  refine ⟨fun σ hσ => ouSg_mem_ulClosure Q hν hσ.1 k θ hθ hk hf, fun ε hε => ?_⟩
  set ε' : ℝ := ε / (C * (Cn + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨τ0, hτ0, h0⟩ := ouSg_strongCont Q hν k θ hθ hk0 hf hε'0
  have key : ∀ a ∈ Icc (0 : ℝ) T, ∀ h ∈ Icc (0 : ℝ) τ0,
      ulNormE k θ (fun x => ouSg Q ν (a + h) f x - ouSg Q ν a f x) ≤ ENNReal.ofReal (C * ε') := by
    intro a ha h hh
    have hdiff : UlClosure k θ (fun x => ouSg Q ν h f x - f x) :=
      ul4_closure_sub hθ (ouSg_mem_ulClosure Q hν hh.1 k θ hθ hk hf) hf
    have e : (fun x => ouSg Q ν (a + h) f x - ouSg Q ν a f x) =
        ouSg Q ν a (fun y => ouSg Q ν h f y - f y) := by
      funext x
      rw [ul3C_sub_lin Q ν a (ul4_ouSg_measurable Q ν h hfc) hfc.measurable
        (fun y => ul4_ouSg_abs_le Q ν h hBf y) hBf, ul4_semigroup Q hν.le ha.1 hh.1 hfc hBf x]
    rw [e]
    refine (hbd a ha _ hdiff).trans ?_
    rw [ENNReal.ofReal_mul hC.le]
    exact mul_le_mul' le_rfl (h0 h hh)
  refine ⟨τ0, hτ0, fun σ hσ σ' hσ' hd => ?_⟩
  have hd' : |σ - σ'| < τ0 := hd
  have hmain : ∀ a ∈ Icc (0 : ℝ) T, ∀ b : ℝ, a ≤ b → b - a < τ0 →
      ulNormE k θ (fun x => ouSg Q ν b f x - ouSg Q ν a f x) ≤ ENNReal.ofReal (C * ε') := by
    intro a ha b hab hba
    have := key a ha (b - a) ⟨by linarith, hba.le⟩
    simpa using this
  rcases le_total σ' σ with hle | hle
  · refine (hmain σ' hσ' σ hle (by rw [abs_of_nonneg (by linarith)] at hd'; exact hd')).trans
      (ENNReal.ofReal_le_ofReal ?_)
    calc C * ε' ≤ C * (ε / (C * (Cn + 1))) * (Cn + 1) := by
          rw [hε']; nlinarith [mul_pos hC hε'0]
      _ = ε := by field_simp
  · have e : (fun x => ouSg Q ν σ f x - ouSg Q ν σ' f x) =
        fun x => -(ouSg Q ν σ' f x - ouSg Q ν σ f x) := by funext x; ring
    rw [e]
    refine (hneg _).trans ?_
    have h1 := hmain σ hσ σ' hle (by rw [abs_of_nonpos (by linarith)] at hd'; linarith)
    calc ENNReal.ofReal Cn * ulNormE k θ (fun x => ouSg Q ν σ' f x - ouSg Q ν σ f x)
        ≤ ENNReal.ofReal Cn * ENNReal.ofReal (C * ε') := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (Cn * (C * ε')) := (ENNReal.ofReal_mul hCn.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          rw [hε']
          have : Cn * (C * (ε / (C * (Cn + 1)))) = (Cn / (Cn + 1)) * ε := by field_simp
          rw [this]
          have : Cn / (Cn + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith

theorem ul4_ureg_add {k : ℕ} {θ : Euc d → ℝ} {T : ℝ} {a b : ℝ → Euc d → ℝ} (ha : UlUReg k θ T a)
    (hb : UlUReg k θ T b) : UlUReg k θ T (fun σ y => a σ y + b σ y) := by
  refine ⟨fun σ hσ => ul4_closure_add (ha.mem σ hσ) (hb.mem σ hσ), fun ε hε => ?_⟩
  obtain ⟨δ1, hδ1, h1⟩ := ha.unif (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hb.unif (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun σ hσ σ' hσ' hd => ?_⟩
  have e : (fun x => (a σ x + b σ x) - (a σ' x + b σ' x)) =
      fun x => (a σ x - a σ' x) + (b σ x - b σ' x) := by funext x; ring
  show ulNormE k θ (fun x => (a σ x + b σ x) - (a σ' x + b σ' x)) ≤ _
  rw [e]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add (h1 σ hσ σ' hσ' (lt_of_lt_of_le hd (min_le_left _ _)))
          (h2 σ hσ σ' hσ' (lt_of_lt_of_le hd (min_le_right _ _)))
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- the Picard iterates `u_0 = P_σ f`, `u_{n+1} = ulD u_n` -/
def ul4Pic (Q : Matrix (Fin d) (Fin d) ℝ) (ν s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (c : Euc d → Euc d) (f : Euc d → ℝ) : ℕ → ℝ → Euc d → ℝ
  | 0 => fun σ => ouSg Q ν σ f
  | n + 1 => fun σ x => ulD Q ν s M ρ c (ul4Pic Q ν s M ρ c f n) σ σ x

/-- **Existence of the mild solution, given the admissibility `G1` of the Duhamel operator.** -/
theorem ul_mild_exists_of_adm {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k) (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν)
    (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (c : Euc d → Euc d) (hc : IsSmoothBounded c) (hAdm : UlDuhamelAdm Q ν s M ρ c k θ T) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, UlClosure k θ f → ∃ u : ℝ → Euc d → ℝ,
      (∀ τ ∈ Icc 0 T, UlClosure k θ (u τ) ∧
        ulNormE k θ (u τ) ≤ ENNReal.ofReal C * ulNormE k θ f) ∧
      (∀ τ₀ ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc 0 T, |τ - τ₀| < δ →
        ulNormE k θ (fun x => u τ x - u τ₀ x) ≤ ENNReal.ofReal ε) ∧
      (∀ τ ∈ Icc 0 T, ∀ x, u τ x = ouSg Q ν τ f x +
        ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u σ)) x) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hk2 : (2 : ℝ) + (d : ℝ) / 2 < k := by linarith
  have hk0 : (d : ℝ) / 2 < k := by linarith
  obtain ⟨KG, hKG, hD⟩ := ul4_D_bound hs0 hsd M ρ hρ hc Q hν hk hθ T
  obtain ⟨γ0, γ1⟩ := ul4_gam_bounds hsd
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ KG * ul4Th (ul4gam d s) T lam ≤ 1 / 4 := by
    have h := (ul4_Th_tendsto γ1 hT).const_mul KG
    rw [mul_zero] at h
    obtain ⟨lam, hl⟩ := ((h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨lam, hl.2, hl.1.le⟩
  obtain ⟨C0, hC0, hP⟩ := ul3C_ulNorm_bdd Q ν T k θ hθ hk0
  obtain ⟨Ct, hCt, htsum⟩ := ul4_closure_tsum hk2 hθ
  refine ⟨Ct * (4 / 3) * Real.exp (lam * T) * C0, fun f hf => ?_⟩
  have hfin : ulNormE k θ f < ⊤ := ul0_ulNormE_lt_top_of_closure k θ hθ hf
  set u : ℕ → ℝ → Euc d → ℝ := ul4Pic Q ν s M ρ c f with hu
  set W : ℝ := C0 * (ulNormE k θ f).toReal with hW
  have hW0 : 0 ≤ W := by positivity
  have hUR : ∀ n, UlUReg k θ T (u n) := by
    intro n
    induction n with
    | zero => exact ul4_P_ureg Q hν k θ hθ hk2 hf
    | succ n ih => exact hAdm _ ih
  have hB : ∀ n : ℕ, ∀ σ ∈ Icc 0 T,
      ulNormE k θ (u n σ) ≤ ENNReal.ofReal (W * (1 / 4) ^ n * Real.exp (lam * σ)) := by
    intro n
    induction n with
    | zero =>
      intro σ hσ
      have e : ulNormE k θ (u 0 σ) ≤ ENNReal.ofReal W := by
        refine (hP σ hσ f hf).trans (le_of_eq ?_)
        rw [hW, ENNReal.ofReal_mul hC0.le, ENNReal.ofReal_toReal hfin.ne]
      refine e.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 1 ≤ Real.exp (lam * σ) := Real.one_le_exp (by nlinarith [hσ.1])
      simpa using mul_le_mul_of_nonneg_left this hW0
    | succ n ih =>
      intro σ hσ
      rcases hσ.1.eq_or_lt with h0 | hpos
      · subst h0
        have : u (n + 1) 0 = fun _ => 0 := by funext x; simp [hu, ul4Pic, ulD]
        rw [this]
        have hz : ulNormE k θ (fun _ : Euc d => (0 : ℝ)) = 0 := by
          simp [ulNormE, HRS.MS.UlocCut.uc_zero]
        rw [hz]; exact bot_le
      · have hfun : u (n + 1) σ = fun x => ulD Q ν s M ρ c (u n) σ σ x := rfl
        rw [hfun]
        refine (hD hpos le_rfl hσ.2 (ul4_reg_mono hσ.2 (hUR n).toReg) hlam0 (by positivity)
          (fun σ' hσ' => ih σ' ⟨hσ'.1, hσ'.2.trans hσ.2⟩)).trans (ENNReal.ofReal_le_ofReal ?_)
        have hE := (Real.exp_pos (lam * σ)).le
        calc KG * (W * (1 / 4) ^ n) * Real.exp (lam * σ) * ul4Th (ul4gam d s) T lam
            = (W * (1 / 4) ^ n * Real.exp (lam * σ)) * (KG * ul4Th (ul4gam d s) T lam) := by ring
          _ ≤ (W * (1 / 4) ^ n * Real.exp (lam * σ)) * (1 / 4) :=
              mul_le_mul_of_nonneg_left hlam (by positivity)
          _ = W * (1 / 4) ^ (n + 1) * Real.exp (lam * σ) := by ring
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 0 (by simpa using hk0) θ hθ
  obtain ⟨Cn, hCn, hneg⟩ := ul4_neg (k := k) hθ
  have hnrm : ∀ N n : ℕ, ∀ σ ∈ Icc 0 T, (ulNormE k θ (u (n + N) σ)).toReal ≤
      W * Real.exp (lam * σ) * (1 / 4) ^ N * (1 / 4) ^ n := fun N n σ hσ => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB (n + N) σ hσ)
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    refine this.trans (le_of_eq ?_); rw [pow_add]; ring
  have hgs : ∀ (a : ℝ), Summable fun n : ℕ => a * (1 / 4 : ℝ) ^ n := fun a =>
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsumx : ∀ σ ∈ Icc 0 T, ∀ x, Summable fun n => u n σ x := fun σ hσ x => by
    refine Summable.of_norm_bounded (hgs (Ccb * (W * Real.exp (lam * σ)))) fun n => ?_
    have h1 := ul3_cb_apply (hcb _ ((hUR n).mem σ hσ)).1 (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 := hnrm 0 n σ hσ
    simp only [add_zero, pow_zero, mul_one] at h2
    refine h1.trans (((hcb _ ((hUR n).mem σ hσ)).2).trans ?_)
    calc Ccb * (ulNormE k θ (u n σ)).toReal ≤ Ccb * (W * Real.exp (lam * σ) * (1 / 4) ^ n) :=
          mul_le_mul_of_nonneg_left h2 hCcb.le
      _ = _ := by ring
  have htail : ∀ N : ℕ, ∀ σ ∈ Icc 0 T, UlClosure k θ (fun x => ∑' n, u (n + N) σ x) ∧
      ulNormE k θ (fun x => ∑' n, u (n + N) σ x) ≤
        ENNReal.ofReal (Ct * (W * (1 / 4) ^ N * (4 / 3)) * Real.exp (lam * σ)) := by
    intro N σ hσ
    have hs : Summable fun n => (ulNormE k θ (u (n + N) σ)).toReal :=
      Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) (hnrm N · σ hσ)
        (hgs (W * Real.exp (lam * σ) * (1 / 4) ^ N))
    obtain ⟨h1, h2⟩ := htsum (fun n => u (n + N) σ) (fun n => (hUR _).mem σ hσ) hs
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc Ct * ∑' n, (ulNormE k θ (u (n + N) σ)).toReal
        ≤ Ct * ∑' n : ℕ, W * Real.exp (lam * σ) * (1 / 4) ^ N * (1 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (hs.tsum_le_tsum (hnrm N · σ hσ)
            (hgs (W * Real.exp (lam * σ) * (1 / 4) ^ N))) hCt.le
      _ = _ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  set ut : ℝ → Euc d → ℝ := fun σ x => ∑' n, u n σ x with hut
  set S : ℕ → ℝ → Euc d → ℝ := fun N σ y => ∑ n ∈ Finset.range N, u n σ y with hSdef
  have hdec : ∀ N : ℕ, ∀ σ ∈ Icc 0 T, ∀ x, ut σ x - S N σ x = ∑' n, u (n + N) σ x :=
    fun N σ hσ x => by
      have := (hsumx σ hσ x).sum_add_tsum_nat_add N
      simp only [hut, hSdef]; linarith
  have hS : ∀ N : ℕ, 1 ≤ N → UlUReg k θ T (S N) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simpa [hSdef] using hUR 0
    | succ N hN ih =>
      have e : S (N + 1) = fun σ y => S N σ y + u N σ y := by
        funext σ y; simp only [hSdef, Finset.sum_range_succ]
      rw [e]; exact ul4_ureg_add ih (hUR N)
  have hcN : ∀ N : ℕ, ∀ σ ∈ Icc 0 T, UlClosure k θ (fun x => ut σ x - S N σ x) ∧
      ulNormE k θ (fun x => ut σ x - S N σ x) ≤
        ENNReal.ofReal (Ct * (W * (1 / 4) ^ N * (4 / 3)) * Real.exp (lam * σ)) := fun N σ hσ => by
    have e : (fun x => ut σ x - S N σ x) = fun x => ∑' n, u (n + N) σ x := funext (hdec N σ hσ)
    rw [e]; exact htail N σ hσ
  have hutU : UlUReg k θ T ut := by
    refine ⟨fun σ hσ => by simpa [hSdef] using ((hcN 0 σ hσ).1), fun ε hε => ?_⟩
    set a : ℝ := Ct * (W * (4 / 3)) with ha
    have ha0 : 0 ≤ a := by positivity
    set cε : ℝ := a * Real.exp (lam * T) with hcε
    have hcε0 : 0 ≤ cε := by positivity
    set x₀ : ℝ := ε / (2 * ((1 + Cn) * (cε + 1))) with hx₀
    have hx₀0 : 0 < x₀ := by positivity
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx₀0 (by norm_num : (1 / 4 : ℝ) < 1)
    obtain ⟨δ, hδ, hSδ⟩ := (hS (N + 1) (by omega)).unif (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun σ hσ σ' hσ' hd => ?_⟩
    have hq : (1 / 4 : ℝ) ^ (N + 1) ≤ x₀ :=
      ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans hN.le)
    have hb : ∀ τ ∈ Icc 0 T, ulNormE k θ (fun x => ut τ x - S (N + 1) τ x) ≤
        ENNReal.ofReal (cε * x₀) := fun τ hτ => (hcN (N + 1) τ hτ).2.trans (ENNReal.ofReal_le_ofReal (by
      have h1 : Real.exp (lam * τ) ≤ Real.exp (lam * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hlam0)
      calc Ct * (W * (1 / 4) ^ (N + 1) * (4 / 3)) * Real.exp (lam * τ)
          = a * (1 / 4) ^ (N + 1) * Real.exp (lam * τ) := by rw [ha]; ring
        _ ≤ a * x₀ * Real.exp (lam * T) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq ha0) h1 (Real.exp_pos _).le (by positivity)
        _ = cε * x₀ := by rw [hcε]; ring))
    have e : (fun x => ut σ x - ut σ' x) = fun x => (S (N + 1) σ x - S (N + 1) σ' x) +
        ((ut σ x - S (N + 1) σ x) + (-(ut σ' x - S (N + 1) σ' x))) := by funext x; ring
    show ulNormE k θ (fun x => ut σ x - ut σ' x) ≤ _
    rw [e]
    refine (ul0_ulNormE_add k θ _ _).trans ?_
    have h2 : ulNormE k θ (fun x => (ut σ x - S (N + 1) σ x) + (-(ut σ' x - S (N + 1) σ' x))) ≤
        ENNReal.ofReal (ε / 2) := by
      refine (ul0_ulNormE_add k θ _ _).trans ?_
      calc _ ≤ ENNReal.ofReal (cε * x₀) + ENNReal.ofReal Cn * ENNReal.ofReal (cε * x₀) :=
            add_le_add (hb σ hσ) ((hneg _).trans (mul_le_mul' le_rfl (hb σ' hσ')))
        _ = ENNReal.ofReal ((1 + Cn) * (cε * x₀)) := by
            rw [← ENNReal.ofReal_mul hCn.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (ε / 2) := by
            apply ENNReal.ofReal_le_ofReal
            have : (1 + Cn) * (cε * x₀) ≤ ((1 + Cn) * (cε + 1)) * x₀ := by nlinarith [mul_nonneg hCn.le hcε0, mul_pos hx₀0 hCn, hx₀0.le]
            refine this.trans (le_of_eq ?_)
            rw [hx₀]; field_simp
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hSδ σ hσ σ' hσ' hd) h2
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hmem0 : ∀ σ ∈ Icc 0 T, UlClosure k θ (ut σ) ∧ ulNormE k θ (ut σ) ≤
      ENNReal.ofReal (Ct * (W * (4 / 3)) * Real.exp (lam * σ)) := fun σ hσ => by
    have := hcN 0 σ hσ
    simp only [hSdef, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one] at this
    exact this
  have hUD : ∀ w, UlUReg k θ T w → ∀ τ ∈ Icc 0 T,
      UlClosure k θ (fun y => ulD Q ν s M ρ c w τ τ y) := fun w hw τ hτ => (hAdm w hw).mem τ hτ
  have e1 : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Icc 0 T, ∀ x,
      S (N + 1) τ x = u 0 τ x + ulD Q ν s M ρ c (S N) τ τ x := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro τ hτ x
      have h1 : S 1 = u 0 := by funext σ y; simp [hSdef]
      rw [h1]
      simp only [hSdef, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rfl
    | succ N hN ih =>
      intro τ hτ x
      have hsub := ul4_D_sub hs0 hsd M ρ hρ hc Q hν hk hθ hτ.1 le_rfl
        (ul4_reg_mono hτ.2 (hS (N + 1) (by omega)).toReg) (ul4_reg_mono hτ.2 (hUR N).toReg) x
      have e : (fun σ y => S (N + 1) σ y - u N σ y) = S N := by
        funext σ y; simp only [hSdef, Finset.sum_range_succ]; ring
      rw [e] at hsub
      have h3 : S (N + 1 + 1) τ x = S (N + 1) τ x + u (N + 1) τ x := by
        simp only [hSdef, Finset.sum_range_succ]
      rw [h3, ih τ hτ x]
      have h2 : u (N + 1) τ x = ulD Q ν s M ρ c (u N) τ τ x := rfl
      rw [h2]; linarith
  have e2 : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Icc 0 T, ∀ x,
      ulD Q ν s M ρ c (fun σ y => ut σ y - S N σ y) τ τ x =
        ulD Q ν s M ρ c ut τ τ x - ulD Q ν s M ρ c (S N) τ τ x := fun N hN τ hτ x =>
    ul4_D_sub hs0 hsd M ρ hρ hc Q hν hk hθ hτ.1 le_rfl (ul4_reg_mono hτ.2 hutU.toReg)
      (ul4_reg_mono hτ.2 (hS N hN).toReg) x
  have hΘ0 := ul4_Th_nonneg (γ := ul4gam d s) hT lam
  have e3 : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Icc 0 T, ∀ x,
      |ulD Q ν s M ρ c (fun σ y => ut σ y - S N σ y) τ τ x| ≤
        Ccb * (KG * (Ct * (W * (1 / 4) ^ N * (4 / 3))) * Real.exp (lam * τ) * ul4Th (ul4gam d s) T lam) := by
    intro N hN τ hτ x
    have hcl := ul4_closure_sub hθ (hUD ut hutU τ hτ) (hUD (S N) (hS N hN) τ hτ)
    have hg : (fun y => ulD Q ν s M ρ c ut τ τ y - ulD Q ν s M ρ c (S N) τ τ y) =
        fun y => ulD Q ν s M ρ c (fun σ y => ut σ y - S N σ y) τ τ y :=
      funext fun y => (e2 N hN τ hτ y).symm
    rw [hg] at hcl
    obtain ⟨hmem, hnorm⟩ := hcb _ hcl
    have h1 := ul3_cb_apply hmem (Nat.zero_le 0) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    refine h1.trans (hnorm.trans (mul_le_mul_of_nonneg_left ?_ hCcb.le))
    have hpos : 0 ≤ KG * (Ct * (W * (1 / 4) ^ N * (4 / 3))) * Real.exp (lam * τ) * ul4Th (ul4gam d s) T lam := by
      positivity
    rcases hτ.1.eq_or_lt with h0 | hp
    · subst h0
      have : (fun y => ulD Q ν s M ρ c (fun σ y => ut σ y - S N σ y) 0 0 y) = fun _ => 0 := by
        funext y; simp [ulD]
      rw [this]
      have hz : ulNormE k θ (fun _ : Euc d => (0 : ℝ)) = 0 := by
        simp [ulNormE, HRS.MS.UlocCut.uc_zero]
      rw [hz]; simpa using hpos
    · have hRegw : UlReg k θ τ (fun σ y => ut σ y - S N σ y) :=
        ul4_reg_mono hτ.2 (ul4_reg_sub hθ hutU.toReg (hS N hN).toReg)
      have := hD hp le_rfl hτ.2 hRegw hlam0 (by positivity) (W := Ct * (W * (1 / 4) ^ N * (4 / 3)))
        (fun σ hσ => (hcN N σ ⟨hσ.1, hσ.2.trans hτ.2⟩).2)
      have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
      rwa [ENNReal.toReal_ofReal hpos] at h3
  have hEq : ∀ τ ∈ Icc 0 T, ∀ x, ut τ x = u 0 τ x + ulD Q ν s M ρ c ut τ τ x := by
    intro τ hτ x
    have hlim1 : Tendsto (fun N : ℕ => S (N + 1) τ x) atTop (𝓝 (ut τ x)) :=
      (hsumx τ hτ x).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hb : Tendsto (fun N : ℕ => Ccb * (KG * (Ct * (W * (1 / 4) ^ N * (4 / 3))) *
        Real.exp (lam * τ) * ul4Th (ul4gam d s) T lam)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul (Ccb * (KG * (Ct * (W * (4 / 3))) * Real.exp (lam * τ) *
          ul4Th (ul4gam d s) T lam))
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have hz : Tendsto (fun N : ℕ => ulD Q ν s M ρ c (fun σ y => ut σ y - S N σ y) τ τ x) atTop (𝓝 0) :=
      squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun N hN => by
        rw [Real.norm_eq_abs]; exact e3 N hN τ hτ x⟩) hb
    have hlim2 := (tendsto_const_nhds (x := u 0 τ x + ulD Q ν s M ρ c ut τ τ x)).sub hz
    rw [sub_zero] at hlim2
    refine tendsto_nhds_unique hlim1 (hlim2.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [e1 N hN τ hτ x, e2 N hN τ hτ x]; ring
  refine ⟨ut, fun τ hτ => ⟨(hmem0 τ hτ).1, (hmem0 τ hτ).2.trans ?_⟩, hutU.toReg.cont, fun τ hτ x => hEq τ hτ x⟩
  rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : Real.exp (lam * τ) ≤ Real.exp (lam * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hlam0)
  rw [hW]
  have h5 : 0 ≤ Ct * (4 / 3) * C0 * (ulNormE k θ f).toReal := by positivity
  calc Ct * (C0 * (ulNormE k θ f).toReal * (4 / 3)) * Real.exp (lam * τ)
      = (Ct * (4 / 3) * C0 * (ulNormE k θ f).toReal) * Real.exp (lam * τ) := by ring
    _ ≤ (Ct * (4 / 3) * C0 * (ulNormE k θ f).toReal) * Real.exp (lam * T) :=
        mul_le_mul_of_nonneg_left this h5
    _ = _ := by ring

end HRS.MS.Ul
