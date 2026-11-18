import HRS.MS.ThCorrRespAux2
import HRS.MS.ThCorrDefs

/-!
# TC-2 (response operator), part 3: assembly, `tc_response_zero`, `tc_response_pos`, `tc_response`

Namespace `HRS.MS.TcR`; helper lemmas carry the prefix `tc2_`.  No existing file is edited.

Interface (all `[new]`, infrastructure for the S4.4 chain `thermal_corrector`): constants `M₀ c S` (and `N`) are
quantified before `ρ`, then for every `ρ` with `TcRef d ρ M₀ c S N` (positive smooth probability density with
`ρ ≤ M₀ exp (-c ‖x‖²)`; only `prob` and `gauss` are used), every `γ > 0` and every `f ∈ L²_0(μ)`, `μ = withDensityReal ρ`,
there is `r₀ ∈ L²_0(μ)` with `r₀ + γ K_μ r₀ = f` `μ`-a.e. and `‖r₀‖_{L²(μ)} ≤ ‖f‖_{L²(μ)}`, where
`K_μ = Kop (rieszKernel d s) μ` (so `γ⁻¹ r₀ + K_μ r₀ = P_μ φ` for `f = γ • projMean μ φ`, see `tc_memL2Zero_smul_projMean`).

* `tc_response_pos` (`0 < s < d`): wrapper of `wr13c_resolvent_norm_le`;
* `tc_response_zero` (`s = 0`, `d ≥ 1`): `Kc0 = P T̃ P` with `T̃ f x = ∫ t67K d x y f y dμ(y)` (`ThCorrRespAux1/2`), then
  `HRS.Whole.Q34.resolvent_exists` on `Lp ℝ 2 μ` (copy of `Q34.partD`, abstracted in `tc2_response_of_op`);
* `tc_response` (`0 ≤ s < d`): the two cases.

Hypotheses: `0 < c` (needed for `l ∈ L²(μ)` at `s = 0`); `Kop` is a Bochner integral, but the statements are a.e. in `μ`
and the integrals are not junk for `μ`-a.e. `x` (`tc2_T_ae_integrable`, `tc2_kop_log`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.MS.TcR

open HRS.Whole HRS.Whole.Q34 HRS.MS.Thm

variable {d : ℕ}

section Abstract

variable {ν : Measure (Euc d)}

theorem tc2_kop_congr_ae {g : Euc d → ℝ} {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') :
    HRS.Whole.Kop g ν u = HRS.Whole.Kop g ν u' := by
  have e : (fun x => ∫ y, g (x - y) * u y ∂ν) = fun x => ∫ y, g (x - y) * u' y ∂ν := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  unfold HRS.Whole.Kop
  rw [e]

/-- Abstract form of `Q34.partD`: if a bounded, symmetric, nonnegative operator `K` on `L²(ν)` with range in the centered
classes represents `Kop g ν` on centered classes, then the response equation has an `L²_0`-solution of norm `≤ ‖f‖`. -/
theorem tc2_response_of_op [IsProbabilityMeasure ν] {g : Euc d → ℝ} {Mg : ℝ}
    (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hsymm : ∀ U V, inner ℝ (K U) V = inner ℝ U (K V))
    (hpos : ∀ U, 0 ≤ inner ℝ (K U) U) (hMg0 : 0 ≤ Mg) (hMg : ∀ U, ‖K U‖ ≤ Mg * ‖U‖)
    (hPK : ∀ U, Pc ν (K U) = K U)
    (hkop : ∀ U : Lp ℝ 2 ν, Pc ν U = U →
      HRS.Whole.Kop g ν (U : Euc d → ℝ) =ᵐ[ν] (K U : Euc d → ℝ))
    {β : ℝ} (hβ : 0 < β) {f : Euc d → ℝ} (hf : HRS.Whole.MemL2Zero ν f) :
    ∃ h : Euc d → ℝ, HRS.Whole.IsResponse g ν β f h ∧
      HRS.Whole.l2Norm ν h ≤ HRS.Whole.l2Norm ν f := by
  obtain ⟨F, hF, hPF⟩ := exists_class hf
  obtain ⟨Hh, hsol, -, -, -, hnorm⟩ := resolvent_exists K hsymm hpos hMg0 hMg hβ F
  have hPHh : Pc ν Hh = Hh := by
    have h1 := congrArg (Pc ν) hsol
    rw [map_add, map_smul, hPK, hPF] at h1
    have h2 : Pc ν Hh + β • K Hh = Hh + β • K Hh := h1.trans hsol.symm
    exact add_right_cancel h2
  have hpm : ∀ x, HRS.Whole.projMean ν f x = f x := by
    intro x
    simp only [HRS.Whole.projMean, HRS.Whole.pair, hf.2, sub_zero]
  have hresp : HRS.Whole.IsResponse g ν β f (Hh : Euc d → ℝ) := by
    refine ⟨⟨Lp.memLp Hh, ?_⟩, ?_⟩
    · rw [← inner_one2]
      calc inner ℝ (one2 ν) Hh = inner ℝ (one2 ν) (Pc ν Hh) := by rw [hPHh]
        _ = 0 := inner_one2_Pc Hh
    · have hsol' : ((Hh + β • K Hh : Lp ℝ 2 ν) : Euc d → ℝ) = (F : Euc d → ℝ) := by
        rw [hsol]
      filter_upwards [Lp.coeFn_add Hh (β • K Hh), Lp.coeFn_smul β (K Hh),
        hkop Hh hPHh, hF] with x h1 h2 h3 h4
      have e1 := congrFun hsol' x
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← h3] at e1
      rw [hpm, h4]
      exact e1
  refine ⟨_, hresp, ?_⟩
  rw [l2Norm_eq (Filter.EventuallyEq.refl _ _), l2Norm_eq hF]
  exact hnorm

end Abstract

section Zero

variable {ρ : Euc d → ℝ}

/-- On centered classes the operator `tc2_Kc` of the log kernel represents `Kop (rieszKernel d 0)`. -/
theorem tc2_kop_class_log [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (hρ : HRS.Whole.IsProbDensity ρ) {Mg : ℝ}
    (hk : TcKer (HRS.Whole.withDensityReal ρ) (t67K d) Mg)
    (hl2 : MemLp (t67l : Euc d → ℝ) 2 (HRS.Whole.withDensityReal ρ))
    (U : Lp ℝ 2 (HRS.Whole.withDensityReal ρ)) (hU : Pc (HRS.Whole.withDensityReal ρ) U = U) :
    HRS.Whole.Kop (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) (U : Euc d → ℝ)
      =ᵐ[HRS.Whole.withDensityReal ρ] (tc2_Kc hk U : Euc d → ℝ) := by
  have h0 : inner ℝ (one2 (HRS.Whole.withDensityReal ρ)) U = 0 := by
    have := inner_one2_Pc (ν := HRS.Whole.withDensityReal ρ) U
    rwa [hU] at this
  have hmean : ∫ x, mrep U x ∂(HRS.Whole.withDensityReal ρ) = 0 :=
    (integral_congr_ae (mrep_ae U)).symm.trans ((inner_one2 U).symm.trans h0)
  have h1 := tc2_kop_log hρ hk hl2 (mrep_measurable U) (mrep_memLp U) hmean
  rw [tc2_kop_congr_ae (mrep_ae U)]
  have e : tc2_T (HRS.Whole.withDensityReal ρ) (t67K d) (U : Euc d → ℝ) = tc2_T (HRS.Whole.withDensityReal ρ) (t67K d) (mrep U) :=
    tc2_T_congr_ae (mrep_ae U)
  filter_upwards [h1, tc2_Kc_ae hk U hU] with x hx hy
  rw [hx, hy, e]

/-- **Response operator at `s = 0`.** -/
theorem tc_response_zero (hd : 1 ≤ d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) :
    ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ →
      ∀ f : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ r₀ : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) r₀ x = f x) ∧
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) r₀ ≤
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
  intro ρ h γ hγ f hf
  have hρ := h.prob
  have hg := h.gauss
  have := isProbabilityMeasure_nu hρ
  obtain ⟨Mg, hk⟩ := tc2_tcker_log hd hρ hc hg
  have hl2 := tc2_l_memLp hρ hc hg
  have hp := tc2_pos_log hd hρ hk
  obtain ⟨r, hr, hnorm⟩ := tc2_response_of_op (tc2_Kc hk) (tc2_Kc_symm hk) (tc2_Kc_pos hk hp)
    hk.mg_nonneg (tc2_Kc_norm_le hk) (tc2_Pc_Kc hk) (tc2_kop_class_log hρ hk hl2) hγ hf
  have hpm : ∀ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) f x = f x := by
    intro x
    simp only [HRS.Whole.projMean, HRS.Whole.pair, hf.2, sub_zero]
  refine ⟨r, hr.1, ?_, hnorm⟩
  filter_upwards [hr.2] with x hx
  rw [hx, hpm]

end Zero

section Pos

variable {ρ : Euc d → ℝ}

/-- **Response operator for `0 < s < d`** (wrapper of `wr13c_resolvent_norm_le`). -/
theorem tc_response_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c)
    (N : ℕ) :
    ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ →
      ∀ f : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ r₀ : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x = f x) ∧
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) r₀ ≤
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
  intro ρ h γ hγ f hf
  have hρ := h.prob
  obtain ⟨hex, -, hnorm⟩ := HRS.MS.Wr.wr13c_resolvent_norm_le hd hs0 hsd hρ
    (tc2_le_M0 hρ hc h.gauss) hγ hf
  have hresp : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ f
      (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ f) := by
    unfold HRS.Whole.responseInverse
    split
    · next hh => exact hh.choose_spec
    · next hh => exact absurd hex hh
  have hpm : ∀ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) f x = f x := by
    intro x
    simp only [HRS.Whole.projMean, HRS.Whole.pair, hf.2, sub_zero]
  refine ⟨_, hresp.1, ?_, hnorm⟩
  filter_upwards [hresp.2] with x hx
  rw [hx, hpm]

end Pos

/-- **Response operator for `0 ≤ s < d`** (interface `tc_response` of the S4.4 plan, step 2). -/
theorem tc_response (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c)
    (N : ℕ) :
    ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ →
      ∀ f : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ r₀ : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x = f x) ∧
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) r₀ ≤
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    exact tc_response_zero hd M₀ c S hc N
  · exact tc_response_pos hd h hsd M₀ c S hc N

/-- The datum `f = γ • projMean μ φ` of the S4.4 response step lies in `L²_0(μ)` when `φ ∈ L²(μ)`. -/
theorem tc_memL2Zero_smul_projMean {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {φ : Euc d → ℝ}
    (hφ : MemLp φ 2 (HRS.Whole.withDensityReal ρ)) (γ : ℝ) :
    HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
      (γ • HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) := by
  have := isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hmem : MemLp (HRS.Whole.projMean ν φ) 2 ν := by
    unfold HRS.Whole.projMean
    exact hφ.sub (memLp_const _)
  refine ⟨hmem.const_smul γ, ?_⟩
  have hint : Integrable (HRS.Whole.projMean ν φ) ν := hmem.integrable (by norm_num)
  have h0 : ∫ x, HRS.Whole.projMean ν φ x ∂ν = 0 := by
    have hφ1 : Integrable φ ν := hφ.integrable (by norm_num)
    simp only [HRS.Whole.projMean, HRS.Whole.pair]
    rw [integral_sub hφ1 (integrable_const _), integral_const]
    simp
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h0, mul_zero]

end HRS.MS.TcR

end
