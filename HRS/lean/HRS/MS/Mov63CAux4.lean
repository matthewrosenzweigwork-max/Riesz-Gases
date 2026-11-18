import HRS.MS.Mov63CAux3

/-!
# S6.3, uniqueness chain (N2b/N3a, part 3): identification of the weak-form functionals

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.

On Schwartz inputs an integration by parts identifies `A_ψ`, `Q_ψ` with `-∫ P v φ` and `∫ B(v,v')φ`; the diffusion part
`D_φ = -S_0φ - ν V_1 φ` is pointwise algebra.  Density of the Hermite span in `OscSpace d m` and continuity of the
functionals (`Mov63CAux3`) then give the identities on all of `Σ^m`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `u ↦ ⟨f, u⟩_{L²}` on `Σ^r`, `r ≥ 0`. -/
def mnc_ipL (f : Euc d → ℝ) {r : ℝ} (hr : 0 ≤ r) : OscSpace d r →L[ℝ] ℝ :=
  (innerSL ℝ (OscSpace.ofFun 0 f)).comp (mov2d_j hr)

lemma mnc_ipL_ofFun {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) {r : ℝ} (hr : 0 ≤ r)
    (hg : MemOsc r g) : mnc_ipL f hr (OscSpace.ofFun r g) = ∫ x, f x * g x := by
  simp only [mnc_ipL, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [mov2d_j_ofFun hr hg, mov2d_inner_ofFun hf hg.1]

section Classical

lemma mnc_P_pair (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (w : 𝓢R) :
    ∫ x, movP d s ρ w x * φ x =
      -mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) (fun z => Real.sqrt (ρ z) * w z) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  have hψs := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport (fun z => φ z / Real.sqrt (ρ z)) := mnc_psi_cs hφc
  obtain ⟨hFc, -⟩ := mnb_force_bdd hd1 H.hs0 H.hsd (mnb_rhoData H) w
  set F : Euc d → Euc d := movForce d s (fun z => Real.sqrt (ρ z) * w z) with hF
  set ψ : Euc d → ℝ := fun z => φ z / Real.sqrt (ρ z) with hψ
  have hY : ContDiff ℝ 1 (fun y => ρ y • F y) := (hρsm.of_le (by exact_mod_cast le_top)).smul hFc
  have hYc : HasCompactSupport ψ ∨ HasCompactSupport (fun y => ρ y • F y) := Or.inl hψc
  have h1 := mnc_ibp_div hY (hψs.of_le (by exact_mod_cast le_top)) hYc
  have e1 : ∀ x, movP d s ρ w x * φ x = -(movDiv (fun y => ρ y • F y) x * ψ x) := by
    intro x
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    simp only [movP, hψ]
    field_simp
    try ring
  simp_rw [e1]
  rw [integral_neg, h1, neg_neg]
  unfold mnc_A
  rw [neg_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_smul_left, conj_trivial]
  rw [real_inner_comm]

lemma mnc_B_pair (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (v w : 𝓢R) :
    ∫ x, movB d s ρ v w x * φ x =
      mnc_Q d s (fun z => φ z / Real.sqrt (ρ z)) (fun z => Real.sqrt (ρ z) * v z)
        (fun z => Real.sqrt (ρ z) * w z) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  have hψs := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport (fun z => φ z / Real.sqrt (ρ z)) := mnc_psi_cs hφc
  obtain ⟨hFc, -⟩ := mnb_force_bdd hd1 H.hs0 H.hsd (mnb_rhoData H) w
  have hh := (mv1_h_gauss (mnb_rhoData H) v).1
  set F : Euc d → Euc d := movForce d s (fun z => Real.sqrt (ρ z) * w z) with hF
  set ψ : Euc d → ℝ := fun z => φ z / Real.sqrt (ρ z) with hψ
  have hY : ContDiff ℝ 1 (fun y => (Real.sqrt (ρ y) * v y) • F y) :=
    (hh.of_le (by exact_mod_cast le_top)).smul hFc
  have h1 := mnc_ibp_div hY (hψs.of_le (by exact_mod_cast le_top)) (Or.inl hψc)
  have e1 : ∀ x, movB d s ρ v w x * φ x = movDiv (fun y => (Real.sqrt (ρ y) * v y) • F y) x * ψ x := by
    intro x
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    simp only [movB, hψ]
    field_simp
    try ring
  simp_rw [e1]
  rw [h1]
  unfold mnc_Q
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_smul_left, conj_trivial]
  rw [real_inner_comm]


lemma mnc_S0_cont (hβ : 0 < β) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) : Continuous (mov_S0 d β q φ) := by
  unfold mov_S0
  refine Continuous.sub ?_ (continuous_const.mul hφ.continuous)
  exact continuous_const.mul ((mnc_lap_cont hφ).neg.add
    ((continuous_const.mul (continuous_norm.pow 2)).mul hφ.continuous))

lemma mnc_S0_cs {φ : Euc d → ℝ} (hφc : HasCompactSupport φ) : HasCompactSupport (mov_S0 d β q φ) := by
  unfold mov_S0
  refine HasCompactSupport.sub ?_ ?_
  · refine HasCompactSupport.mul_left (f := fun _ => β⁻¹) ?_
    refine HasCompactSupport.add (mnc_lap_cs hφc).neg ?_
    exact hφc.mul_left (f := fun x => (β * q / 2) ^ 2 * ‖x‖ ^ 2)
  · exact hφc.mul_left (f := fun _ => β⁻¹ * (β * q) * (d / 2))


lemma mnc_V1_cont (H : Mov2dTh d s β q ρ) : Continuous (mov2a_V1 d s β q ρ) := by
  have := (mov2a_V1_memCb H.hd H.hs0 H.hsd H.hβ H.hq H.hρ 0).1.1
  exact this.continuous

lemma mnc_pointwise_D (H : Mov2dTh d s β q ρ) (φ : Euc d → ℝ) (v : Euc d → ℝ) (x : Euc d) :
    v x * mnc_Dphi ρ β φ x = -(mov_S0 d β q φ x * v x) - φ x * (β⁻¹ * mov2a_V1 d s β q ρ x * v x) := by
  unfold mnc_Dphi mov_S0
  rw [mov2a_V_decomp H.hd H.hs0 H.hsd H.hβ H.hq H.hρ x]
  ring

/-- The linear identity on Schwartz inputs (`S = S_0 + νV_1 + P`, `P` handled by the integration by parts). -/
lemma mnc_lin_schwartz (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (w : 𝓢R) :
    (∫ x, w x * mnc_Dphi ρ β φ x) +
        mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) (fun z => Real.sqrt (ρ z) * w z) =
      -(∫ x, mov_S0 d β q φ x * w x) - ∫ x, φ x * mov2d_AR d s β q ρ w x := by
  have hP := mnc_P_pair H hφ hφc w
  have hφ2 : MemLp φ 2 (volume : Measure (Euc d)) := hφ.continuous.memLp_of_hasCompactSupport hφc
  obtain ⟨CP, -, hCP⟩ := mov_P_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ 0
  have hPint : Integrable (fun x => φ x * movP d s ρ w x) := (hφ2.integrable_mul (hCP w).1.1)
  have hV1 := mnc_V1_cont H
  have hwc : Continuous w := w.continuous
  have hVint : Integrable (fun x => φ x * (β⁻¹ * mov2a_V1 d s β q ρ x * w x)) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hφ.continuous.mul ((continuous_const.mul hV1).mul hwc)) (hφc.mul_right (f' := fun x => β⁻¹ * mov2a_V1 d s β q ρ x * w x))
  have hAR : ∫ x, φ x * mov2d_AR d s β q ρ w x =
      (∫ x, φ x * (β⁻¹ * mov2a_V1 d s β q ρ x * w x)) + ∫ x, φ x * movP d s ρ w x := by
    rw [← integral_add hVint hPint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mov2d_AR]
    ring
  have hD : ∫ x, w x * mnc_Dphi ρ β φ x =
      -(∫ x, mov_S0 d β q φ x * w x) - ∫ x, φ x * (β⁻¹ * mov2a_V1 d s β q ρ x * w x) := by
    have hS : Integrable (fun x => mov_S0 d β q φ x * w x) :=
      ((mnc_S0_cont H.hβ hφ).mul hwc).integrable_of_hasCompactSupport ((mnc_S0_cs hφc).mul_right)
    have hS' : Integrable (fun x => -(mov_S0 d β q φ x * w x)) := hS.neg
    rw [← integral_neg]
    have := integral_sub hS' hVint
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mnc_pointwise_D H φ w x)
  have hP' : ∫ x, φ x * movP d s ρ w x = -mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) (fun z => Real.sqrt (ρ z) * w z) := by
    rw [← hP]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hAR, hD, hP']
  ring

end Classical

/-! ### Density: the identities on all of `Σ^m` -/

section Density

lemma mnc_rep_hs {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) (c : MultiIndex d →₀ ℝ) (w : 𝓢R)
    (hw : (⇑w : Euc d → ℝ) = mov2d_hs d c) :
    mn_repFun 3 m hn (OscSpace.ofFun (m : ℝ) (mov2d_hs d c)) = ⇑w := by
  rw [← hw]
  exact mn_repFun_ofFun hn (hw ▸ mov2d_hs_memOsc (m : ℝ) c) ((w.smooth ⊤).of_le (by simp))

/-- **Linear part of the weak form on `Σ^m`**: `∫ rep(u) D_φ + A_ψ(h_u) = -⟨S_0φ,u⟩ - ⟨φ, R u⟩`. -/
theorem mnc_lin_osc (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m)
    (hm : (d : ℝ) / 2 + 3 < m) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u : OscSpace d (m : ℝ)) :
    (∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y) +
        mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) (mnc_hu ρ hn u) =
      -(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) u) -
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) u) := by
  have hψs := mnc_psi_smooth (mnc_rho_smooth H) (mnb_rhoData H).pos hφ
  have hψc : HasCompactSupport (fun z => φ z / Real.sqrt (ρ z)) := mnc_psi_cs hφc
  obtain ⟨L, hL⟩ := mnc_L_clm H hn hφ hφc
  obtain ⟨A, hA⟩ := mnc_A_clm H hn hψs hψc
  have hφ2 : MemLp φ 2 (volume : Measure (Euc d)) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hS2 : MemLp (mov_S0 d β q φ) 2 (volume : Measure (Euc d)) :=
    (mnc_S0_cont H.hβ hφ).memLp_of_hasCompactSupport (mnc_S0_cs hφc)
  let R2 : OscSpace d (m : ℝ) →L[ℝ] ℝ :=
    -(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m)) -
      (mnc_ipL φ (mnb_sub_a_nonneg H hm)).comp (mov2d_R d s β q ρ (m : ℝ))
  have key : L + A = R2 := by
    refine mnb_clm_ext (e := mov2d_e d (m : ℝ)) (mov2d_e_dense (m : ℝ)) fun c => ?_
    obtain ⟨w, hw⟩ := mnb_hs_sch (d := d) c
    have he : mov2d_e d (m : ℝ) c = OscSpace.ofFun (m : ℝ) (mov2d_hs d c) := mov2d_e_apply _ c
    have hrep := mnc_rep_hs hn c w hw
    have hhu : mnc_hu ρ hn (OscSpace.ofFun (m : ℝ) (mov2d_hs d c)) = fun z => Real.sqrt (ρ z) * w z := by
      funext z; simp only [mnc_hu, hrep]
    rw [he, ContinuousLinearMap.add_apply, hL, hA, hrep, hhu]
    have hmem := mov2d_hs_memOsc (m : ℝ) c
    obtain ⟨CR, -, hR⟩ := mov2d_AR_data H (m : ℝ)
    simp only [R2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
    rw [mov2d_R_ofFun H (m : ℝ) c, mnc_ipL_ofFun hS2 _ hmem, mnc_ipL_ofFun hφ2 _ (hR.1 c).1, ← hw]
    exact mnc_lin_schwartz H hφ hφc w
  have := congrArg (fun T => T u) key
  simpa [hL, hA, R2] using this

/-- **Quadratic part of the weak form on `Σ^m`**: `Q_ψ(h_u, h_{u'}) = ⟨φ, B(u,u')⟩`. -/
theorem mnc_quad_osc (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m)
    (hm : (d : ℝ) / 2 + 3 < m) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u u' : OscSpace d (m : ℝ)) :
    mnc_Q d s (fun z => φ z / Real.sqrt (ρ z)) (mnc_hu ρ hn u) (mnc_hu ρ hn u') =
      mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm u u') := by
  have hψs := mnc_psi_smooth (mnc_rho_smooth H) (mnb_rhoData H).pos hφ
  have hψc : HasCompactSupport (fun z => φ z / Real.sqrt (ρ z)) := mnc_psi_cs hφc
  obtain ⟨Qb, hQ⟩ := mnc_Q_clm H hn hψs hψc
  have hφ2 : MemLp φ 2 (volume : Measure (Euc d)) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have base : ∀ c c' : MultiIndex d →₀ ℝ, Qb (mov2d_e d (m : ℝ) c) (mov2d_e d (m : ℝ) c') =
      mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mov2d_e d (m : ℝ) c) (mov2d_e d (m : ℝ) c')) := by
    intro c c'
    obtain ⟨w, hw⟩ := mnb_hs_sch (d := d) c
    obtain ⟨w', hw'⟩ := mnb_hs_sch (d := d) c'
    have hrep := mnc_rep_hs hn c w hw
    have hrep' := mnc_rep_hs hn c' w' hw'
    have hhu : ∀ (c : MultiIndex d →₀ ℝ) (w : 𝓢R), (⇑w : Euc d → ℝ) = mov2d_hs d c →
        mnc_hu ρ hn (OscSpace.ofFun (m : ℝ) (mov2d_hs d c)) = fun z => Real.sqrt (ρ z) * w z := by
      intro c w hw
      have hr := mnc_rep_hs hn c w hw
      funext z; simp only [mnc_hu, hr]
    rw [mov2d_e_apply, mov2d_e_apply, hQ, hhu c w hw, hhu c' w' hw', mov_B_ext_hs H hm c c',
      mnc_ipL_ofFun hφ2 _ (mnb_memOsc_hs H hm c c').1, ← mnc_B_pair H hφ hφc w w', ← hw, ← hw']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have step1 : ∀ c' : MultiIndex d →₀ ℝ, ∀ u : OscSpace d (m : ℝ),
      Qb u (mov2d_e d (m : ℝ) c') =
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm u (mov2d_e d (m : ℝ) c')) := by
    intro c' u
    have := mnb_clm_ext (e := mov2d_e d (m : ℝ)) (mov2d_e_dense (m : ℝ))
      (E₁ := (ContinuousLinearMap.apply ℝ ℝ (mov2d_e d (m : ℝ) c')).comp Qb)
      (E₂ := (mnc_ipL φ (mnb_sub_a_nonneg H hm)).comp
        ((ContinuousLinearMap.apply ℝ _ (mov2d_e d (m : ℝ) c')).comp (mov_B_ext H hm)))
      (fun c => by simpa using base c c')
    simpa using congrArg (fun T => T u) this
  have step2 := mnb_clm_ext (e := mov2d_e d (m : ℝ)) (mov2d_e_dense (m : ℝ))
    (E₁ := Qb u) (E₂ := (mnc_ipL φ (mnb_sub_a_nonneg H hm)).comp (mov_B_ext H hm u))
    (fun c' => by simpa using step1 c' u)
  rw [← hQ]
  simpa using congrArg (fun T => T u') step2

end Density

end HRS.MS.Mov63
