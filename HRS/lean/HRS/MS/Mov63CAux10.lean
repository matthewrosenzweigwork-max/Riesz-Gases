import HRS.MS.Mov63CAux9

/-!
# S6.3, uniqueness chain (N3b, part 5): the dilated Hermite test functions

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
`mnc_hα α = √(ℓ^d) h_α(ℓ ·)` (`ℓ = mov_dil β q`) is a Schwartz function with `S_0 h̃_α = q|α| h̃_α`; hence it is a good test
function (`mnc_Good`), and `mnc_Psi_good_zero` gives the coefficient identity
`⟨h̃_α,u_t⟩ - ⟨h̃_α,u_0⟩ = ∫_{[0,t]} (-q|α| ⟨h̃_α,u_x⟩ - ⟨h̃_α,R u_x⟩ + ⟨h̃_α,B(u_x,u_x)⟩) dx`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `h̃_α(x) = √(ℓ^d) h_α(ℓ x)`. -/
def mnc_hα (d : ℕ) (β q : ℝ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • x)

lemma mnc_hα_schwartz (hβ : 0 < β) (hq : 0 < q) (α : MultiIndex d) :
    ∃ φ : 𝓢R, (⇑φ : Euc d → ℝ) = mnc_hα d β q α := by
  obtain ⟨φ0, hφ0⟩ := mnb_hs_sch (d := d) (Finsupp.single α 1)
  have e0 : mov2d_hs d (Finsupp.single α 1) = hermiteFunD α := by
    funext z; simp [mov2d_hs, Finsupp.linearCombination_single]
  have hl := mov_dil_pos hβ hq
  set l := mov_dil β q with hldef
  let φ1 : 𝓢R := SchwartzMap.compCLM ℝ (g := fun x : Euc d => l • x) (by fun_prop)
    ⟨1, l⁻¹, fun x => by
      have : ‖x‖ = l⁻¹ * ‖l • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]
      rw [pow_one]
      nlinarith [norm_nonneg (l • x), inv_pos.2 hl]⟩ φ0
  refine ⟨Real.sqrt (l ^ d) • φ1, ?_⟩
  funext x
  simp only [SchwartzMap.smul_apply, smul_eq_mul, mnc_hα]
  congr 1
  show φ0 (l • x) = _
  rw [hφ0, e0]

lemma mnc_hα_smooth (hβ : 0 < β) (hq : 0 < q) (α : MultiIndex d) : ContDiff ℝ ∞ (mnc_hα d β q α) := by
  obtain ⟨φ, hφ⟩ := mnc_hα_schwartz (d := d) hβ hq α
  rw [← hφ]; exact φ.smooth ⊤

lemma mnc_S0_hα (hβ : 0 < β) (hq : 0 < q) (α : MultiIndex d) (x : Euc d) :
    mov_S0 d β q (mnc_hα d β q α) x = (q * (α.degree : ℝ)) * mnc_hα d β q α x := by
  have hc : ContDiff ℝ ∞ (fun y : Euc d => hermiteFunD α (mov_dil β q • y)) :=
    ((contDiff_hermiteFunD α).comp (contDiff_const_smul _)).of_le (by simp)
  have e : mnc_hα d β q α = fun y => Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • y) := rfl
  have h := InnerProductSpace.laplacian_smul (x := x) (Real.sqrt (mov_dil β q ^ d))
    (f := fun y : Euc d => hermiteFunD α (mov_dil β q • y)) (hc.contDiffAt.of_le (by simp))
  have e2 : Laplacian.laplacian (fun y => Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • y)) x =
      Real.sqrt (mov_dil β q ^ d) * Laplacian.laplacian (fun y => hermiteFunD α (mov_dil β q • y)) x := by
    simpa [Pi.smul_def] using h
  have h0 := mov_S0_hermite_dil hβ hq α x
  unfold mov_S0 at h0 ⊢
  rw [e, e2]
  simp only [mnc_hα]
  have := h0
  nlinarith [this, Real.sqrt_nonneg (mov_dil β q ^ d)]


lemma mnc_hα_good (hβ : 0 < β) (hq : 0 < q) (α : MultiIndex d) :
    mnc_Good d β q (mnc_hα d β q α) ∧ Integrable (fun x => ‖gradient (mnc_hα d β q α) x‖) := by
  obtain ⟨φ, hφ⟩ := mnc_hα_schwartz (d := d) hβ hq α
  have hS : mov_S0 d β q (mnc_hα d β q α) = fun x => (q * (α.degree : ℝ)) * mnc_hα d β q α x :=
    funext (mnc_S0_hα hβ hq α)
  have hl2 : MemLp (mnc_hα d β q α) 2 (volume : Measure (Euc d)) := by rw [← hφ]; exact φ.memLp 2
  have hl1 : Integrable (mnc_hα d β q α) := by rw [← hφ]; exact φ.integrable
  refine ⟨⟨mnc_hα_smooth hβ hq α, hl2, hl1, ?_, ?_⟩, ?_⟩
  · rw [hS]; exact hl2.const_mul _
  · rw [hS]; exact hl1.const_mul _
  · have := φ.integrable_pow_mul (volume : Measure (Euc d)) 0 |> fun _ => φ.integrable_pow_mul_iteratedFDeriv
      (volume : Measure (Euc d)) 0 1
    rw [← hφ]
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_one, mnc_norm_gradient]

lemma mnc_ipL_smul {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) (c : ℝ) {r : ℝ} (h0 : 0 ≤ r)
    (y : OscSpace d r) : mnc_ipL (fun x => c * g x) h0 y = c * mnc_ipL g h0 y := by
  have hgo : MemOsc 0 g := ⟨hg, by simpa using mov2b_coeff_sq_summable hg⟩
  simp only [mnc_ipL, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [mn_ofFun_smul 0 c hgo, inner_smul_left]
  simp

end HRS.MS.Mov63
