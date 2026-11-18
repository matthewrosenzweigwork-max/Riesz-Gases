import HRS.MS.ThCorrRespAux3
import HRS.MS.MovForceAux3
import HRS.Whole.Round2

/-!
# S9.8 `r2_screened`, part 1: the continuous representative of the response

Namespace `HRS.MS.S98`; helper lemmas carry the prefix `s98_`.  No existing file is edited.

For a thermal density `ρ` with `TcRef` data (`0 ≤ s < d`, `0 < c`), `γ > 0`, a continuous test function `φ` and a continuous
bounded `r` representing (up to `μ`-null sets) an `L²_0(μ)` solution of `r₀ + γ K r₀ = γ P_μ φ`:

* `s98_resp_unique`: the `L²_0(μ)` solutions of the response equation are `μ`-a.e. unique (the operator `K` is
  nonnegative; `0 < s`: `wr13c_resolvent_norm_le`; `s = 0`: `Q34.resolvent_exists` for the log kernel operator);
* `s98_kop_continuous`: `x ↦ HRS.Whole.Kop g μ r x` is continuous for continuous bounded `r`;
* `s98_resp_rep`: `responseRepW g μ γ φ x = γ⁻¹ r x` for every `x`, and `IsResponse g μ γ φ (responseRepW ...)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.S98

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- `Kop` is homogeneous: `Kop g μ (c f) = c HRS.Whole.Kop g μ f` (no integrability needed). -/
theorem s98_kop_smul (g : Euc d → ℝ) (μ : Measure (Euc d)) (c : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.Kop g μ (fun y => c * f y) x = c * HRS.Whole.Kop g μ f x := by
  unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
  have e : ∀ z : Euc d, ∫ y, g (z - y) * (c * f y) ∂μ = c * ∫ y, g (z - y) * f y ∂μ := by
    intro z
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp only [e]
  rw [integral_const_mul]
  ring

/-- `Kop g ν f x` depends only on the `ν`-class of `f`. -/
theorem s98_kop_congr_ae {ν : Measure (Euc d)} {g : Euc d → ℝ} {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') :
    HRS.Whole.Kop g ν u = HRS.Whole.Kop g ν u' := by
  have e : (fun x => ∫ y, g (x - y) * u y ∂ν) = fun x => ∫ y, g (x - y) * u' y ∂ν := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  unfold HRS.Whole.Kop
  rw [e]

/-- `projMean` is the identity on centered functions. -/
theorem s98_projMean_of_zero {ν : Measure (Euc d)} {f : Euc d → ℝ} (hf : ∫ x, f x ∂ν = 0) (x : Euc d) :
    HRS.Whole.projMean ν f x = f x := by
  simp only [HRS.Whole.projMean, HRS.Whole.pair, hf, sub_zero]

/-- Uniqueness of the response from an abstract nonnegative operator (no integrability of the datum needed). -/
theorem s98_unique_of_op {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ} {Mg : ℝ}
    (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hsymm : ∀ U V, inner ℝ (K U) V = inner ℝ U (K V))
    (hpos : ∀ U, 0 ≤ inner ℝ (K U) U) (hMg0 : 0 ≤ Mg) (hMg : ∀ U, ‖K U‖ ≤ Mg * ‖U‖)
    (hkop : ∀ U : Lp ℝ 2 ν, Pc ν U = U →
      HRS.Whole.Kop g ν (U : Euc d → ℝ) =ᵐ[ν] (K U : Euc d → ℝ))
    {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ} {h1 h2 : Euc d → ℝ}
    (r1 : HRS.Whole.IsResponse g ν β ψ h1) (r2 : HRS.Whole.IsResponse g ν β ψ h2) : h1 =ᵐ[ν] h2 := by
  obtain ⟨H, -, huniq, -⟩ := resolvent_exists K hsymm hpos hMg0 hMg hβ 0
  have key : ∀ h, HRS.Whole.IsResponse g ν β ψ h → ∃ U : Lp ℝ 2 ν, h =ᵐ[ν] (U : Euc d → ℝ) ∧
      ((U + β • K U : Lp ℝ 2 ν) : Euc d → ℝ) =ᵐ[ν] HRS.Whole.projMean ν ψ := by
    intro h hr
    obtain ⟨U, hU, hPU⟩ := exists_class hr.1
    refine ⟨U, hU, ?_⟩
    filter_upwards [Lp.coeFn_add U (β • K U), Lp.coeFn_smul β (K U), hkop U hPU, hU, hr.2]
      with x h1 h2 h3 h4 h6
    have hkc : HRS.Whole.Kop g ν h x = HRS.Whole.Kop g ν (U : Euc d → ℝ) x :=
      congrFun (s98_kop_congr_ae hU) x
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← h3, ← hkc, ← h4]
    exact h6
  obtain ⟨U1, hu1, e1⟩ := key h1 r1
  obtain ⟨U2, hu2, e2⟩ := key h2 r2
  have e : U1 + β • K U1 = U2 + β • K U2 := Lp.ext (e1.trans e2.symm)
  have hD : (U1 - U2) + β • K (U1 - U2) = 0 := by
    have : (U1 - U2) + β • K (U1 - U2) = (U1 + β • K U1) - (U2 + β • K U2) := by
      simp only [map_sub, smul_sub]; abel
    rw [this, e, sub_self]
  have h0 : (0 : Lp ℝ 2 ν) + β • K 0 = 0 := by simp
  have : U1 - U2 = 0 := (huniq _ hD).trans (huniq _ h0).symm
  have hU : U1 = U2 := sub_eq_zero.1 this
  subst hU
  exact hu1.trans hu2.symm

/-- Uniqueness of the `L²_0` response solution for the Riesz kernel `0 ≤ s < d` and thermal data. -/
theorem s98_resp_unique (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M₀ c S : ℝ} (hc : 0 < c)
    {N : ℕ} {ρ : Euc d → ℝ} (h : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) {γ : ℝ} (hγ : 0 < γ)
    {ψ h1 h2 : Euc d → ℝ}
    (r1 : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ ψ h1)
    (r2 : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ ψ h2) :
    h1 =ᵐ[HRS.Whole.withDensityReal ρ] h2 := by
  have hρ := h.prob
  have := isProbabilityMeasure_nu hρ
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    obtain ⟨Mg, hk⟩ := HRS.MS.TcR.tc2_tcker_log hd hρ hc h.gauss
    have hl2 := HRS.MS.TcR.tc2_l_memLp hρ hc h.gauss
    have hp := HRS.MS.TcR.tc2_pos_log hd hρ hk
    exact s98_unique_of_op (HRS.MS.TcR.tc2_Kc hk) (HRS.MS.TcR.tc2_Kc_symm hk)
      (HRS.MS.TcR.tc2_Kc_pos hk hp) hk.mg_nonneg (HRS.MS.TcR.tc2_Kc_norm_le hk)
      (HRS.MS.TcR.tc2_kop_class_log hρ hk hl2) hγ r1 r2
  · have hQ : Q34Hyp d s ρ M₀ := ⟨hd, h0, hsd, hρ, HRS.MS.TcR.tc2_le_M0 hρ hc h.gauss⟩
    have hM0 : 0 ≤ M₀ := (hρ.nonneg 0).trans (hQ.hM 0)
    exact s98_unique_of_op (Kc hQ) (Kc_symm hQ) (Kc_pos hQ) (Mg_nonneg hQ.hd hQ.hsd hM0) (Kc_norm_le hQ)
      (fun U hU => kop_class hQ (Filter.EventuallyEq.refl _ _) hU) hγ r1 r2

/-- `∫ f dμ = ∫ ρ f` for `μ = ρ dx` with `ρ ≥ 0` measurable. -/
theorem s98_integral_wDR (ρ : Euc d → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : Euc d → ℝ) :
    ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y)]

/-- Continuity of `x ↦ ∫ g(x - y) r(y) dμ(y)` for continuous bounded `r`. -/
theorem s98_conv_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M₀ c S : ℝ} (hc : 0 < c)
    {N : ℕ} {ρ : Euc d → ℝ} (h : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) {r : Euc d → ℝ} (hr : Continuous r)
    {B : ℝ} (hB : ∀ x, |r x| ≤ B) :
    Continuous (fun x => ∫ y, rieszKernel d s (x - y) * r y ∂(HRS.Whole.withDensityReal ρ)) := by
  have hρc : Continuous ρ := h.smooth.continuous
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M₀ := by
    have := h.gauss 0
    have h1 := (h.pos 0).le
    simp at this
    linarith
  have e : (fun x => ∫ y, rieszKernel d s (x - y) * r y ∂(HRS.Whole.withDensityReal ρ)) =
      fun x => ∫ z, rieszKernel d s z * (ρ (x - z) * r (x - z)) := by
    funext x
    rw [s98_integral_wDR ρ hρc.measurable (fun y => (h.pos y).le)]
    have := integral_sub_left_eq_self (fun z => rieszKernel d s z * (ρ (x - z) * r (x - z)))
      (volume : Measure (Euc d)) x
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel]
    ring
  rw [e]
  obtain ⟨hk, hB', hBint⟩ := HRS.MS.MovForce.mv1_g_data (d := d) (s := s) hd hs0 hsd hc
  refine HRS.MS.MovForce.mv1_continuous_conv (ρ := fun y => ρ y * r y) hc hk hB' hBint
    (C := M₀ * B) (mul_nonneg hM0 hB0) (hρc.mul hr) (fun y => ?_)
  rw [abs_mul, abs_of_pos (h.pos y)]
  calc ρ y * |r y| ≤ (M₀ * Real.exp (-c * ‖y‖ ^ 2)) * B :=
        mul_le_mul (h.gauss y) (hB y) (abs_nonneg _) (mul_nonneg hM0 (Real.exp_pos _).le)
    _ = M₀ * B * Real.exp (-c * ‖y‖ ^ 2) := by ring

/-- **The continuous representative of the response.**  `r` continuous and bounded, `r =ᵐ r₀` with `r₀ ∈ L²_0(μ)` solving
`r₀ + γ K r₀ = γ P_μ φ`; then `responseRepW = γ⁻¹ r` everywhere and it is a response. -/
theorem s98_resp_rep (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M₀ c S : ℝ} (hc : 0 < c)
    {N : ℕ} {ρ : Euc d → ℝ} (h : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) {γ : ℝ} (hγ : 0 < γ)
    {φ : Euc d → ℝ} (hφ : Continuous φ) {r r₀ : Euc d → ℝ} (hr : Continuous r) {B : ℝ}
    (hB : ∀ x, |r x| ≤ B) (hr₀ : MemL2Zero (HRS.Whole.withDensityReal ρ) r₀)
    (hae : ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
        γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x)
    (hrr : r =ᵐ[HRS.Whole.withDensityReal ρ] r₀) :
    (∀ x, responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ x = γ⁻¹ * r x) ∧
      HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ
        (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) := by
  have hρ := h.prob
  have := isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set g := rieszKernel d s with hg
  have hKr : HRS.Whole.Kop g μ r = HRS.Whole.Kop g μ r₀ := s98_kop_congr_ae hrr
  have hL2 : MemL2Zero μ r := ⟨hr₀.1.ae_eq hrr.symm, (integral_congr_ae hrr).trans hr₀.2⟩
  have hL2' : MemL2Zero μ (fun x => γ⁻¹ * r x) :=
    ⟨hL2.1.const_mul γ⁻¹, by rw [integral_const_mul, hL2.2, mul_zero]⟩
  -- the a.e. identity for `γ⁻¹ r`
  have hae' : ∀ᵐ x ∂μ, γ⁻¹ * r x + HRS.Whole.Kop g μ r x = HRS.Whole.projMean μ φ x := by
    filter_upwards [hae, hrr] with x hx hx2
    rw [congrFun hKr x, hx2]
    have : γ⁻¹ * r₀ x + HRS.Whole.Kop g μ r₀ x = γ⁻¹ * (r₀ x + γ * HRS.Whole.Kop g μ r₀ x) := by
      field_simp
    rw [this, hx]
    field_simp
  have hresp0 : HRS.Whole.IsResponse g μ γ φ (fun x => γ⁻¹ * r x) := by
    refine ⟨hL2', ?_⟩
    filter_upwards [hae'] with x hx
    rw [s98_kop_smul g μ γ⁻¹ r x, ← hx]
    field_simp
  have hinv : HRS.Whole.IsResponse g μ γ φ (HRS.Whole.responseInverse g μ γ φ) := by
    unfold HRS.Whole.responseInverse
    rw [dif_pos ⟨_, hresp0⟩]
    exact (Classical.choose_spec (⟨_, hresp0⟩ : ∃ h, HRS.Whole.IsResponse g μ γ φ h))
  have hu : HRS.Whole.responseInverse g μ γ φ =ᵐ[μ] (fun x => γ⁻¹ * r x) :=
    s98_resp_unique hd hs0 hsd hc h hγ hinv hresp0
  have hKinv : ∀ x, HRS.Whole.Kop g μ (HRS.Whole.responseInverse g μ γ φ) x = γ⁻¹ * HRS.Whole.Kop g μ r x := fun x => by
    rw [congrFun (s98_kop_congr_ae hu) x, s98_kop_smul]
  have hrepx : ∀ x, responseRepW g μ γ φ x = HRS.Whole.projMean μ φ x - HRS.Whole.Kop g μ r x := fun x => by
    unfold responseRepW
    rw [hKinv x]
    field_simp
  -- continuity: both sides continuous, a.e. equal for the (full-support) measure
  have hKc : Continuous (HRS.Whole.Kop g μ r) := by
    have := s98_conv_continuous hd hs0 hsd hc h hr hB
    unfold HRS.Whole.Kop HRS.Whole.projMean
    exact this.sub continuous_const
  have hPc : Continuous (HRS.Whole.projMean μ φ) := by
    unfold HRS.Whole.projMean
    exact hφ.sub continuous_const
  have hvol : ∀ᵐ x ∂(volume : Measure (Euc d)), γ⁻¹ * r x + HRS.Whole.Kop g μ r x = HRS.Whole.projMean μ φ x := by
    have hmeas : Measurable fun x => ENNReal.ofReal (ρ x) :=
      ENNReal.measurable_ofReal.comp h.smooth.continuous.measurable
    have := (ae_withDensity_iff hmeas).1 hae'
    filter_upwards [this] with x hx
    exact hx (by simpa using h.pos x)
  have hall : ∀ x, γ⁻¹ * r x + HRS.Whole.Kop g μ r x = HRS.Whole.projMean μ φ x := by
    have hcont : Continuous fun x => γ⁻¹ * r x + HRS.Whole.Kop g μ r x := (continuous_const.mul hr).add hKc
    exact fun x => congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hcont hPc).1 hvol) x
  have hrep : ∀ x, responseRepW g μ γ φ x = γ⁻¹ * r x := fun x => by
    rw [hrepx x, ← hall x]; ring
  refine ⟨hrep, ?_⟩
  have : responseRepW g μ γ φ = fun x => γ⁻¹ * r x := funext hrep
  rw [this]
  exact hresp0

end HRS.MS.S98

end
