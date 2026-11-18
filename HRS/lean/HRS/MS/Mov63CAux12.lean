import HRS.MS.Mov63CAux11

/-!
# S6.3, uniqueness chain (N3b, part 7): the dilated coefficients determine an element of `Σ^m`; action of `e^{-τS_0}`

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
* `mnc_ae_eq_of_ip`: two `L²` functions with the same pairings against all `h̃_α` agree a.e.
* `mnc_ext_of_ip`: two elements of `Σ^m` with equal `⟨h̃_α, ·⟩` coincide.
* `mnc_ipL_Sm`: `⟨h̃_α, e^{-τS_0} y⟩ = e^{-τ q|α|} ⟨h̃_α, y⟩` for `y ∈ Σ^{m-a}`, `τ > 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mnc_ae_eq_of_ip (hβ : 0 < β) (hq : 0 < q) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 (volume : Measure (Euc d)))
    (h : ∀ α : MultiIndex d, ∫ x, mnc_hα d β q α x * f x = ∫ x, mnc_hα d β q α x * g x) :
    f =ᵐ[volume] g := by
  have hl := mov_dil_pos hβ hq
  set l := mov_dil β q with hldef
  have hpre : 0 < Real.sqrt (l ^ d) * (l ^ d)⁻¹ := by positivity
  have hcoef : ∀ α, hermiteCoeff (fun y => f (l⁻¹ • y)) α = hermiteCoeff (fun y => g (l⁻¹ • y)) α := by
    intro α
    have h1 : mov2b_dcoeff l f α = mov2b_dcoeff l g α := by
      have := h α
      unfold mov2b_dcoeff
      simpa [mnc_hα, mul_comm] using this
    rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl] at h1
    exact mul_left_cancel₀ hpre.ne' h1
  have hae := mov2b_ae_eq_of_coeff (mov2b_memLp_inv hl hf) (mov2b_memLp_inv hl hg) hcoef
  have := mov2b_ae_comp_smul hl hae
  filter_upwards [this] with x hx
  simp only [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hx
  exact hx

lemma mnc_ext_of_ip (hβ : 0 < β) (hq : 0 < q) {m : ℕ} {X Y : OscSpace d (m : ℝ)}
    (h : ∀ α : MultiIndex d, mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) X =
      mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) Y) : X = Y := by
  obtain ⟨f, hf, rfl⟩ := mn_exists_fun m X
  obtain ⟨g, hg, rfl⟩ := mn_exists_fun m Y
  have hα2 : ∀ α, MemLp (mnc_hα d β q α) 2 (volume : Measure (Euc d)) := fun α =>
    (mnc_hα_good hβ hq α).1.l2
  have := mnc_ae_eq_of_ip hβ hq hf.1 hg.1 (fun α => by
    have h1 := h α
    rwa [mnc_ipL_ofFun (hα2 α) _ hf, mnc_ipL_ofFun (hα2 α) _ hg] at h1)
  exact mov2d_ofFun_ae hf this

lemma mnc_exists_fun_real {r : ℝ} (hr : 0 ≤ r) (u : OscSpace d r) :
    ∃ f : Euc d → ℝ, MemOsc r f ∧ OscSpace.ofFun r f = u := by
  set F := OscSpace.toLp u with hF
  have hL : MemLp (⇑F) 2 (volume : Measure (Euc d)) := Lp.memLp F
  have e : hL.toLp ⇑F = F := Lp.toLp_coeFn F hL
  have hsum := (OscSpace.range_toLp hr F).1 ⟨u, rfl⟩
  have hcoeff : ∀ α, hermiteCoeff (⇑F) α = inner ℝ F (hermiteLpD α) := by
    intro α
    rw [real_inner_comm, ← OscSpace.inner_hermiteLpD_toLp _ hL α, e]
  have hmem : MemOsc r ⇑F := ⟨hL, hsum.congr fun α => by rw [hcoeff]⟩
  refine ⟨⇑F, hmem, ?_⟩
  exact OscSpace.toLp_injective hr (by rw [OscSpace.toLp_ofFun _ hmem, e])

lemma mnc_ipL_Sm (hβ : 0 < β) (hq : 0 < q) {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (hma : 0 ≤ (m : ℝ) - a)
    (α : MultiIndex d) {τ : ℝ} (hτ : 0 < τ) (y : OscSpace d ((m : ℝ) - a)) :
    mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mov2d_Sm β q (sub_le_self (m : ℝ) ha) τ y) =
      Real.exp (-(τ * q * (α.degree : ℝ))) * mnc_ipL (mnc_hα d β q α) hma y := by
  obtain ⟨f, hf, rfl⟩ := mnc_exists_fun_real hma y
  have hα2 : MemLp (mnc_hα d β q α) 2 (volume : Measure (Euc d)) := (mnc_hα_good hβ hq α).1.l2
  rw [mov2d_Sm_ofFun hβ hq (sub_le_self (m : ℝ) ha) (Or.inl hτ) hf, max_eq_left hτ.le]
  obtain ⟨K, -, hK⟩ := mov2d_expS0_bdd (d := d) hβ hq (sub_le_self (m : ℝ) ha) hτ.le (Or.inl hτ)
  have hmem := (hK f hf).1
  rw [mnc_ipL_ofFun hα2 _ hmem, mnc_ipL_ofFun hα2 _ hf]
  have hd := mov_expS0_dcoeff hβ hq hτ.le hf.1 α
  unfold mov2b_dcoeff at hd
  have e1 : ∫ x, mnc_hα d β q α x * mov_expS0 β q τ f x =
      ∫ x, mov_expS0 β q τ f x * (Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • x)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [mnc_hα]; ring)
  have e2 : ∫ x, mnc_hα d β q α x * f x =
      ∫ x, f x * (Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • x)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [mnc_hα]; ring)
  rw [e1, e2, hd]

end HRS.MS.Mov63
