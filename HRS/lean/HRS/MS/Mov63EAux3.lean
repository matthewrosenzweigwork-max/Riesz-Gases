import HRS.MS.Mov63EAux2

/-!
# S6.3, packet N6 (part 3): the flux `Y_u` and the identity `∫ ψ div Y_u = -⟨S₀φ,u⟩ + ⟨φ,-Ru + B(u,u)⟩`

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  For `u ∈ Σ^m` (`m ∈ ℕ`, `d/2 + 3 < m`): `V_u = mneV hm u` the `C³` representative,
`h_u = √ρ V_u`, `ρ_u = mneRho = ρ + h_u`, `F_u = ∇g*h_u = mneFo` (`C¹`, `mne_force_facts`), `Y_u = mneY = ν∇ρ_u + ρ_u (qx + ∇g*ρ_u)`.

* `mne_decomp_signed`: the signed version of `mnc_decomp` (no positivity, no `pair`): `∫ ρ_t f_ψ - ∫ ρ_t⟨∇ψ,∇g*ρ_t⟩ = ∫ (h/√ρ) D_φ + A_ψ(h) + Q_ψ(h,h)`.
* `mne_pair_e`: for `φ ∈ C_c^∞`, `ψ = φ/√ρ`: `∫ ψ div Y_u = -⟨S₀φ,u⟩ + ⟨φ, -Ru + B(u,u)⟩` (two integrations by parts, `mnc_lin_osc`, `mnc_quad_osc`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Signed

/-- The signed version of `mnc_decomp` (no positivity, no `pair`/`withDensityReal`): for `ρ_t = ρ + h`, `h ∈ RgW`,
`ψ = φ/√ρ`, `φ ∈ C_c^∞`: `∫ ρ_t f_ψ - ∫ ρ_t ⟨∇ψ, ∇g*ρ_t⟩ = ∫ (h/√ρ) D_φ + A_ψ(h) + Q_ψ(h,h)`. -/
theorem mne_decomp_signed (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {h : Euc d → ℝ} {ch : ℝ} (hch : 0 ≤ ch) (hhW : HRS.MP.RdGen.RgW (mnc_W d) 1 ch h) :
    (∫ x, (ρ x + h x) * ((quadraticGradientDyn d s q β).invβ *
          Laplacian.laplacian (fun z => φ z / Real.sqrt (ρ z)) x -
        inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient (fun z => φ z / Real.sqrt (ρ z)) x))) +
      ∫ x, -((ρ x + h x) * inner ℝ (gradient (fun z => φ z / Real.sqrt (ρ z)) x)
        (movForce d s (fun y => ρ y + h y) x)) =
    (∫ x, (h x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) +
      mnc_A d s ρ (fun z => φ z / Real.sqrt (ρ z)) h + mnc_Q d s (fun z => φ z / Real.sqrt (ρ z)) h h := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  set ψ : Euc d → ℝ := fun z => φ z / Real.sqrt (ρ z) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport ψ := mnc_psi_cs hφc
  have hψM : MemCb 2 ψ := mnc_memCb_of_cs hψs hψc 2
  obtain ⟨Kρ, hKρ, hρW⟩ := mnc_rgW_rho H
  have hρtW : HRS.MP.RdGen.RgW (mnc_W d) 1 (Kρ + ch) (fun y => ρ y + h y) := hρW.add hhW
  set ρt : Euc d → ℝ := fun y => ρ y + h y with hρt
  have hρtc : Continuous ρt := (dc1a_rgW_facts (add_nonneg hKρ hch) hρtW).2.1
  have hρc : Continuous ρ := hρsm.continuous
  have hhc : Continuous h := (dc1a_rgW_facts hch hhW).2.1
  set D := quadraticGradientDyn d s q β with hD
  have hM : ∀ y : Euc d, Torus.matVec D.M y = -y := fun y => by simp [hD, quadraticGradientDyn, Torus.matVec]
  have hforce : ∀ x, movForce d s ρt x = movForce d s ρ x + movForce d s h x :=
    fun x => mnc_force_add hd1 H.hs0 H.hsd hKρ hch hρW hhW x
  have hEuler : ∀ x, β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + movForce d s ρ x = 0 :=
    fun x => HRS.MS.Mov0.mv0_thermal_force H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x
  -- the continuous compactly supported factor E
  set E : Euc d → ℝ := fun x => Laplacian.laplacian ψ x +
    inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x) with hEdef
  have hgr := mnc_grad_contDiff hψs
  have hgcs := mnc_grad_cs hψc
  have hEc : Continuous E := (mnc_lap_cont hψs).add ((mnc_loggrad_cont hρsm hpos).inner hgr)
  have hEcs : HasCompactSupport E := by
    refine HasCompactSupport.add (mnc_lap_cs hψc) ?_
    refine hgcs.mono' ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp [h0]
  -- pointwise algebra
  have hrhoE : ∀ x, ρ x * E x = Real.sqrt (ρ x) * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) := by
    intro x
    rw [← mnc_div_rho_grad hρsm hpos hψs x, mnc_div_flux hρsm hpos hφ x]
  have hEW : ∀ x, E x = (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) / Real.sqrt (ρ x) := by
    intro x
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt (hpos x).le
    have h1 := hrhoE x
    have h2 : Real.sqrt (ρ x) * Real.sqrt (ρ x) * E x = Real.sqrt (ρ x) * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x) := by
      rw [hss]; exact h1
    rw [eq_div_iff hs.ne']
    refine mul_left_cancel₀ hs.ne' ?_
    linear_combination h2
  have hfx : ∀ x, gradient D.V x = q • x := fun x => movtr_gradient_confinement q x
  have hpt : ∀ x, ρt x * (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) +
      -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x)) =
      β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
        (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) + (-(h x * inner ℝ (gradient ψ x) (movForce d s h x))) := by
    intro x
    have he := congrArg (fun v => inner ℝ (gradient ψ x) v) (hEuler x)
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at he
    rw [hforce x, inner_add_right, hfx x, inner_smul_left, real_inner_comm (gradient ψ x) x]
    simp only [hD, quadraticGradientDyn, hEdef, hρt]
    have hc : inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient ψ x) =
        inner ℝ (gradient ψ x) (gradient (fun y => Real.log (ρ y)) x) := real_inner_comm _ _
    simp only [hc, conj_trivial] at *
    linear_combination (-(ρ x + h x)) * he
  -- the drift factor f
  set f : Euc d → ℝ := fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x) with hf
  have hfc : Continuous f := by
    refine ((continuous_const.mul (mnc_lap_cont hψs))).sub ?_
    have : (fun x => inner ℝ (gradient D.V x) (gradient ψ x)) = fun x => inner ℝ (q • x) (gradient ψ x) :=
      funext fun x => by rw [hfx x]
    rw [this]
    exact (continuous_id.const_smul q).inner hgr
  have hfcs : HasCompactSupport f := by
    refine HasCompactSupport.sub ((mnc_lap_cs hψc).mul_left (f := fun _ => D.invβ)) ?_
    refine hgcs.mono' ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp [h0]
  have hI1 : Integrable (fun x => ρt x * f x) :=
    (hρtc.mul hfc).integrable_of_hasCompactSupport (hfcs.mul_left (f := ρt))
  have hI2 : Integrable (fun x => -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc (add_nonneg hKρ hch) hρtW hρtc).neg
  -- integrability of the four pieces
  have hG1 : Integrable (fun x => ρ x * E x) :=
    (hρc.mul hEc).integrable_of_hasCompactSupport (hEcs.mul_left (f := ρ))
  have hG2 : Integrable (fun x => h x * E x) :=
    (hhc.mul hEc).integrable_of_hasCompactSupport (hEcs.mul_left (f := h))
  have hG3 : Integrable (fun x => -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc hch hhW hρc).neg
  have hG4 : Integrable (fun x => -(h x * inner ℝ (gradient ψ x) (movForce d s h x))) :=
    (mnc_int_mul_gradforce hd1 H.hs0 H.hsd hψs hψc hch hhW hhc).neg
  -- the divergence integral vanishes
  have hdiv0 : ∫ x, ρ x * E x = 0 := by
    have hY : ContDiff ℝ 1 (fun y => ρ y • gradient ψ y) :=
      (hρsm.of_le (by exact_mod_cast le_top)).smul (HRS.MS.Gap.gap1_contDiff_gradient hψs 1)
    have hYc : HasCompactSupport (fun y => ρ y • gradient ψ y) := hgcs.smul_left (f := ρ)
    have := mnc_ibp_div hY (contDiff_const (c := (1 : ℝ))) (Or.inr hYc)
    simp only [mul_one] at this
    have e : ∀ x, movDiv (fun y => ρ y • gradient ψ y) x = ρ x * E x := fun x =>
      mnc_div_rho_grad hρsm hpos hψs x
    simp_rw [e] at this
    rw [this]
    simp
  calc _ = ∫ x, (ρt x * f x + -(ρt x * inner ℝ (gradient ψ x) (movForce d s ρt x))) :=
        (integral_add hI1 hI2).symm
    _ = ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
        (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
          (-(h x * inner ℝ (gradient ψ x) (movForce d s h x)))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
    _ = β⁻¹ * (∫ x, ρ x * E x) + β⁻¹ * (∫ x, h x * E x) +
        (∫ x, -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
          (∫ x, -(h x * inner ℝ (gradient ψ x) (movForce d s h x))) := by
        have i12 : Integrable (fun x => β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x)) :=
          (hG1.const_mul _).add (hG2.const_mul _)
        have i123 : Integrable (fun x => β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)))) := i12.add hG3
        have e1 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))) +
            (-(h x * inner ℝ (gradient ψ x) (movForce d s h x)))) =
            (∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x))))) +
            ∫ x, -(h x * inner ℝ (gradient ψ x) (movForce d s h x)) := integral_add i123 hG4
        have e2 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x) +
            (-(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)))) =
            (∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x))) +
            ∫ x, -(ρ x * inner ℝ (gradient ψ x) (movForce d s h x)) := integral_add i12 hG3
        have e3 : ∫ x, (β⁻¹ * (ρ x * E x) + β⁻¹ * (h x * E x)) =
            (∫ x, β⁻¹ * (ρ x * E x)) + ∫ x, β⁻¹ * (h x * E x) := integral_add (hG1.const_mul _) (hG2.const_mul _)
        rw [e1, e2, e3, integral_const_mul, integral_const_mul]
    _ = _ := by
        rw [hdiv0, integral_neg, integral_neg]
        unfold mnc_A mnc_Q
        have e2 : β⁻¹ * ∫ x, h x * E x =
            ∫ x, (h x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hEW x]; ring
        rw [e2]
        ring

end Signed

section Cl

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma mne_cbVec_le {K : ℕ} {F : Euc d → Euc d} {X : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    (h : cbNormVecE K F + X ≤ ENNReal.ofReal B) (k : ℕ) (hk : k ≤ K) (x : Euc d) :
    ‖iteratedFDeriv ℝ k F x‖ ≤ B := by
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ k F x‖ ≤ cbNormVecE K F := by
    unfold cbNormVecE
    refine le_trans (le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ k F x‖) x) ?_
    exact Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j F x‖)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  have := h1.trans (le_trans le_self_add h)
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 this

lemma mne_hn {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) : ((3 : ℕ) : ℝ) + d / 2 < m := by push_cast; linarith

/-- The `C³` representative of `u ∈ Σ^m`. -/
abbrev mneV {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) : Euc d → ℝ :=
  mn_repFun 3 m (mne_hn hm) u

section Basic

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

lemma mneV_memOsc (u : OscSpace d (m : ℝ)) : MemOsc (m : ℝ) (mneV hm u) := by
  obtain ⟨-, f, hf, -, hfg⟩ := mn_repFun_spec 3 m (mne_hn hm) u
  exact mov2b_memOsc_congr hfg _ hf

lemma mneV_ofFun (u : OscSpace d (m : ℝ)) : OscSpace.ofFun (m : ℝ) (mneV hm u) = u := by
  obtain ⟨-, f, hf, hfu, hfg⟩ := mn_repFun_spec 3 m (mne_hn hm) u
  exact ((mov2d_ofFun_ae hf hfg).symm).trans hfu

lemma mneV_norm (u : OscSpace d (m : ℝ)) : oscNorm (m : ℝ) (mneV hm u) = ‖u‖ := by
  rw [← OscSpace.norm_ofFun _ (mneV_memOsc hm u), mneV_ofFun hm u]

lemma mneV_cd (u : OscSpace d (m : ℝ)) : ContDiff ℝ 3 (mneV hm u) := by
  have := mn_repFun_contDiff 3 m (mne_hn hm) u
  exact_mod_cast this

lemma mneV_sub (u u' : OscSpace d (m : ℝ)) : mneV hm (u - u') = fun x => mneV hm u x - mneV hm u' x := by
  have : u - u' = u + (-1 : ℝ) • u' := by rw [neg_one_smul]; rfl
  rw [this]
  show mn_repFun 3 m (mne_hn hm) (u + (-1 : ℝ) • u') = _
  rw [mn_repFun_add, mn_repFun_smul]
  funext x
  simp [sub_eq_add_neg]

/-- The force of `√ρ · V_u`. -/
abbrev mneFo (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) : Euc d → Euc d :=
  movForce d s (mnc_hu ρ (mne_hn hm) u)

lemma mne_force_facts (H : Mov2dTh d s β q ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : OscSpace d (m : ℝ), ContDiff ℝ 1 (mneFo d s ρ hm u) ∧
      (∀ x, ‖mneFo d s ρ hm u x‖ ≤ C * ‖u‖) ∧
      (∀ x, ‖fderiv ℝ (mneFo d s ρ hm u) x‖ ≤ C * ‖u‖) := by
  have hm0 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 2 < m := by push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ 0 m hm0
  refine ⟨C, hC0, fun u => ?_⟩
  have hv := mneV_cd hm u
  obtain ⟨-, -, h1, -, h5⟩ := hC (mneV hm u) hv.continuous (mneV_memOsc hm u)
  rw [mneV_norm hm u] at h5
  have hB : 0 ≤ C * ‖u‖ := mul_nonneg hC0 (norm_nonneg _)
  refine ⟨by exact_mod_cast h1, fun x => ?_, fun x => ?_⟩
  · have := mne_cbVec_le hB h5 0 (by omega) x
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · have := mne_cbVec_le hB h5 1 (by omega) x
    rw [norm_iteratedFDeriv_one] at this
    exact this

end Basic

end Cl

section Flux

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

/-- `ρ_u = ρ + √ρ · V_u`. -/
abbrev mneRho (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) : Euc d → ℝ :=
  fun y => ρ y + mnc_hu ρ (mne_hn hm) u y

/-- The flux `Y_u = β⁻¹ ∇ρ_u + ρ_u (q x + ∇g * ρ_u)`. -/
def mneY (d : ℕ) (s q β : ℝ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ))
    (x : Euc d) : Euc d :=
  β⁻¹ • gradient (mneRho ρ hm u) x + mneRho ρ hm u x • (q • x + movForce d s (mneRho ρ hm u) x)

lemma mne_grad_cd {n : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (n : WithTop ℕ∞) (gradient f) := by
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := n) (by rw [Nat.cast_succ])
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1

lemma mne_rho_cd (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) : ContDiff ℝ 3 (mneRho ρ hm u) := by
  obtain ⟨c, K0, hc, hK0, h⟩ := mnc_h_gauss H (mne_hn hm)
  have h3 : ContDiff ℝ 3 (mnc_hu ρ (mne_hn hm) u) := by exact_mod_cast (h u).1
  exact ((mnc_rho_smooth H).of_le (by simp)).add h3

/-- the force `∇g * ρ` of the thermal density, as the force of `V_{u₀}`, `u₀ = ofFun √ρ`. -/
lemma mne_sqrt_mem (H : Mov2dTh d s β q ρ) : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x)) := by
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  rw [← hψ0]
  exact memOsc_schwartz _ ψ0

/-- `u₀ ∈ Σ^m` with `V_{u₀} = √ρ`. -/
def mneU0 (m : ℕ) (ρ : Euc d → ℝ) : OscSpace d (m : ℝ) := OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x))

lemma mneU0_V (H : Mov2dTh d s β q ρ) : mneV hm (mneU0 m ρ) = fun x => Real.sqrt (ρ x) := by
  have hc : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x)) := by
    have := (mnb_rhoData H).sqrt_smooth
    exact this.of_le (by simp)
  exact mn_repFun_ofFun (mne_hn hm) (mne_sqrt_mem H) hc

lemma mneF0 (H : Mov2dTh d s β q ρ) : movForce d s ρ = mneFo d s ρ hm (mneU0 m ρ) := by
  funext x
  show movForce d s ρ x = movForce d s (mnc_hu ρ (mne_hn hm) (mneU0 m ρ)) x
  have : mnc_hu ρ (mne_hn hm) (mneU0 m ρ) = ρ := by
    funext y
    simp only [mnc_hu]
    rw [show mn_repFun 3 m (mne_hn hm) (mneU0 m ρ) y = Real.sqrt (ρ y) from congrFun (mneU0_V hm H) y]
    exact Real.mul_self_sqrt ((mnb_rhoData H).pos y).le
  rw [this]


lemma mne_force_split (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) (x : Euc d) :
    movForce d s (mneRho ρ hm u) x = movForce d s ρ x + mneFo d s ρ hm u x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨Kρ, hKρ, hρW⟩ := mnc_rgW_rho H
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H (mne_hn hm)
  exact mnc_force_add hd1 H.hs0 H.hsd hKρ (mul_nonneg hK1 (norm_nonneg u)) hρW (hW u) x

include hm in
lemma mne_F0_cd (H : Mov2dTh d s β q ρ) : ContDiff ℝ 1 (movForce d s ρ) := by
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  rw [mneF0 hm H]
  exact (hC (mneU0 m ρ)).1

lemma mne_Fr_cd (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) :
    ContDiff ℝ 1 (movForce d s (mneRho ρ hm u)) := by
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  have e : movForce d s (mneRho ρ hm u) = fun x => movForce d s ρ x + mneFo d s ρ hm u x :=
    funext (mne_force_split hm H u)
  rw [e]
  exact (mne_F0_cd hm H).add (hC u).1

lemma mne_Y_cd (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) :
    ContDiff ℝ 1 (mneY d s q β ρ hm u) := by
  have hR := mne_rho_cd hm H u
  have hF := mne_Fr_cd hm H u
  have hg : ContDiff ℝ 1 (gradient (mneRho ρ hm u)) := by
    have := mne_grad_cd (n := 2) (f := mneRho ρ hm u) (by exact_mod_cast hR.of_le (by norm_num))
    exact this.of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (fun x => β⁻¹ • gradient (mneRho ρ hm u) x) := hg.const_smul _
  have h2 : ContDiff ℝ 1 (fun x => mneRho ρ hm u x • ((q • x : Euc d) + movForce d s (mneRho ρ hm u) x)) :=
    (hR.of_le (by norm_num)).smul ((contDiff_id.const_smul q).add hF)
  exact h1.add h2

end Flux

section PairE

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

/-- **Step C identity**: for every `C_c^∞` test function `φ` and every `u ∈ Σ^m`, the weak form of the linear and
quadratic parts at `ρ_u` is the integral of the flux divergence against `ψ = φ/√ρ`:
`∫ ψ div Y_u = -⟨S₀φ,u⟩ + ⟨φ, -R u + B(u,u)⟩`. -/
theorem mne_pair_e (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (u : OscSpace d (m : ℝ)) :
    ∫ x, (φ x / Real.sqrt (ρ x)) * movDiv (mneY d s q β ρ hm u) x =
      -(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) u) +
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (-(mov2d_R d s β q ρ (m : ℝ) u) + mov_B_ext H hm u u) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hn := mne_hn hm
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  set ψ : Euc d → ℝ := fun z => φ z / Real.sqrt (ρ z) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport ψ := mnc_psi_cs hφc
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H hn
  obtain ⟨Kρ, hKρ, hρW⟩ := mnc_rgW_rho H
  have hch : 0 ≤ K1 * ‖u‖ := mul_nonneg hK1 (norm_nonneg _)
  have hhW := hW u
  have hRW : HRS.MP.RdGen.RgW (mnc_W d) 1 (Kρ + K1 * ‖u‖) (mneRho ρ hm u) := hρW.add hhW
  have hRc : Continuous (mneRho ρ hm u) := (dc1a_rgW_facts (add_nonneg hKρ hch) hRW).2.1
  have hRcd := mne_rho_cd hm H u
  have hYcd := mne_Y_cd hm H u
  have hgrψ : ContDiff ℝ 1 (gradient ψ) := HRS.MS.Gap.gap1_contDiff_gradient hψs 1
  have hgcs := mnc_grad_cs hψc
  have hgr := mnc_grad_contDiff hψs
  have hD : ∀ x, gradient (quadraticGradientDyn d s q β).V x = q • x := fun x => movtr_gradient_confinement q x
  -- Step a
  have hA := mnc_ibp_div hYcd (hψs.of_le (by simp)) (Or.inl hψc)
  -- Step c
  have hB := mnc_ibp_div hgrψ (hRcd.of_le (by norm_num)) (Or.inr hgcs)
  have hLap : ∀ x, movDiv (gradient ψ) x = Laplacian.laplacian ψ x := fun x => mov2a_movDiv_gradient hψs x
  -- integrability
  have hgR : Continuous (fun x => gradient (mneRho ρ hm u) x) :=
    ((mne_grad_cd (n := 2) (f := mneRho ρ hm u) (by exact_mod_cast hRcd.of_le (by norm_num))).continuous)
  have hFc : Continuous (movForce d s (mneRho ρ hm u)) := (mne_Fr_cd hm H u).continuous
  have hcs : ∀ f : Euc d → ℝ, (∀ x, gradient ψ x = 0 → f x = 0) → HasCompactSupport f := fun f hf =>
    hgcs.mono' (fun x hx => subset_tsupport _ (fun h0 => hx (hf x h0)))
  have i1 : Integrable (fun x => inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x)) :=
    (hgR.inner hgr).integrable_of_hasCompactSupport (hcs _ (fun x h0 => by simp only [Pi.mul_apply, h0, inner_zero_right, mul_zero]))
  have i2 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x)) :=
    (hRc.mul ((continuous_id.const_smul q).inner hgr)).integrable_of_hasCompactSupport
      (hcs _ (fun x h0 => by simp only [Pi.mul_apply, h0, inner_zero_right, mul_zero]))
  have i3 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) :=
    (hRc.mul (hFc.inner hgr)).integrable_of_hasCompactSupport (hcs _ (fun x h0 => by simp only [Pi.mul_apply, h0, inner_zero_right, mul_zero]))
  have i4 : Integrable (fun x => Laplacian.laplacian ψ x * mneRho ρ hm u x) :=
    ((mnc_lap_cont hψs).mul hRc).integrable_of_hasCompactSupport ((mnc_lap_cs hψc).mul_right)
  -- the expansion of the flux pairing
  have hpt : ∀ x, inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x) =
      β⁻¹ * inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x) +
        (mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) +
          mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := by
    intro x
    simp only [mneY, inner_add_left, inner_smul_left, conj_trivial]
    ring
  have hI : ∫ x, inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x) =
      β⁻¹ * (∫ x, inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x)) +
        ((∫ x, mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x)) +
          ∫ x, mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := by
    simp_rw [hpt]
    have i23 : Integrable (fun x => mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) +
        mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x)) := i2.add i3
    rw [integral_add (i1.const_mul _) i23, integral_add i2 i3, integral_const_mul]
  have hJ : ∫ x, Laplacian.laplacian ψ x * mneRho ρ hm u x =
      -∫ x, inner ℝ (gradient (mneRho ρ hm u) x) (gradient ψ x) := by
    have := hB
    simp_rw [hLap] at this
    rw [this]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
  have hlhs : ∫ x, (φ x / Real.sqrt (ρ x)) * movDiv (mneY d s q β ρ hm u) x =
      -∫ x, inner ℝ (mneY d s q β ρ hm u x) (gradient ψ x) := by
    rw [← hA]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  -- the signed decomposition
  have hdec := mne_decomp_signed H hφ hφc hch hhW
  have hdec' : (∫ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x -
        inner ℝ (q • x : Euc d) (gradient ψ x))) +
      ∫ x, -(mneRho ρ hm u x * inner ℝ (gradient ψ x) (movForce d s (mneRho ρ hm u) x)) =
      (∫ x, (mnc_hu ρ hn u x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) +
        mnc_A d s ρ ψ (mnc_hu ρ hn u) + mnc_Q d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u) := by
    have e : ∀ x, gradient (quadraticGradientDyn d s q β).V x = q • x := hD
    simp only [e] at hdec
    exact hdec
  have hT1 : ∫ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x)) =
      β⁻¹ * (∫ x, Laplacian.laplacian ψ x * mneRho ρ hm u x) -
        ∫ x, mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) := by
    have e : ∀ x, mneRho ρ hm u x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (q • x : Euc d) (gradient ψ x)) =
        β⁻¹ * (Laplacian.laplacian ψ x * mneRho ρ hm u x) -
          mneRho ρ hm u x * inner ℝ (q • x : Euc d) (gradient ψ x) := fun x => by ring
    simp_rw [e]
    rw [integral_sub (i4.const_mul _) i2, integral_const_mul]
  have hT2 : ∫ x, -(mneRho ρ hm u x * inner ℝ (gradient ψ x) (movForce d s (mneRho ρ hm u) x)) =
      -∫ x, mneRho ρ hm u x * inner ℝ (movForce d s (mneRho ρ hm u) x) (gradient ψ x) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [real_inner_comm])
  have hmain : ∫ x, (φ x / Real.sqrt (ρ x)) * movDiv (mneY d s q β ρ hm u) x =
      (∫ x, (mnc_hu ρ hn u x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) +
        mnc_A d s ρ ψ (mnc_hu ρ hn u) + mnc_Q d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u) := by
    rw [← hdec', hT1, hT2, hlhs, hI, hJ]
    ring
  rw [hmain]
  -- identification with the functionals on `Σ^m`
  have e1 : (∫ x, (mnc_hu ρ hn u x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) =
      ∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    simp only [mnc_hu, mnc_Dphi]
    field_simp
  have hlin := mnc_lin_osc H hn hm hφ hφc u
  have hquad := mnc_quad_osc H hn hm hφ hφc u u
  rw [e1]
  have hsum : (∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y) + mnc_A d s ρ ψ (mnc_hu ρ hn u) +
      mnc_Q d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u) =
      -(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) u) -
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) u) +
        mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm u u) := by
    rw [hquad]; linarith
  rw [hsum, map_add, map_neg]
  ring

end PairE

end HRS.MS.Mov63

end
