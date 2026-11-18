import HRS.MS.Mov63CAux2

/-!
# S6.3, uniqueness chain (N3a, part 2): the interaction functional `Phi` and its (bi)linearity

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.

`mnc_Phi d s ψ g h = -∫ g ⟨∇ψ, ∇g*h⟩` is linear in `g` and in `h` (on the class `RgW`) and bounded by
`d B_f c ∫ |g| |∇ψ|` (`c` the `RgW` constant of `h`); `mnc_A = mnc_Phi (ρ) ·`, `mnc_Q = mnc_Phi (h) ·`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s : ℝ}

def mnc_Phi (d : ℕ) (s : ℝ) (ψ g h : Euc d → ℝ) : ℝ :=
  -∫ x, g x * inner ℝ (gradient ψ x) (movForce d s h x)

lemma mnc_A_eq (ρ ψ h : Euc d → ℝ) : mnc_A d s ρ ψ h = mnc_Phi d s ψ ρ h := rfl
lemma mnc_Q_eq (ψ h h' : Euc d → ℝ) : mnc_Q d s ψ h h' = mnc_Phi d s ψ h h' := rfl

section Phi

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
  (hψc : HasCompactSupport ψ)
include hd hs0 hsd hψ hψc

lemma mnc_Phi_add_h {g : Euc d → ℝ} (hg : Continuous g) {h1 h2 : Euc d → ℝ} {c1 c2 : ℝ} (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hh1 : HRS.MP.RdGen.RgW (mnc_W d) 1 c1 h1) (hh2 : HRS.MP.RdGen.RgW (mnc_W d) 1 c2 h2) :
    mnc_Phi d s ψ g (fun y => h1 y + h2 y) = mnc_Phi d s ψ g h1 + mnc_Phi d s ψ g h2 := by
  unfold mnc_Phi
  have e : ∀ x, g x * inner ℝ (gradient ψ x) (movForce d s (fun y => h1 y + h2 y) x) =
      g x * inner ℝ (gradient ψ x) (movForce d s h1 x) + g x * inner ℝ (gradient ψ x) (movForce d s h2 x) := by
    intro x
    rw [mnc_force_add hd hs0 hsd hc1 hc2 hh1 hh2 x, inner_add_right, mul_add]
  simp_rw [e]
  rw [integral_add (mnc_int_mul_gradforce hd hs0 hsd hψ hψc hc1 hh1 hg)
    (mnc_int_mul_gradforce hd hs0 hsd hψ hψc hc2 hh2 hg)]
  ring

lemma mnc_Phi_smul_h {g : Euc d → ℝ} {h : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hh : HRS.MP.RdGen.RgW (mnc_W d) 1 c h) (a : ℝ) :
    mnc_Phi d s ψ g (fun y => a * h y) = a * mnc_Phi d s ψ g h := by
  unfold mnc_Phi
  have e : ∀ x, g x * inner ℝ (gradient ψ x) (movForce d s (fun y => a * h y) x) =
      a * (g x * inner ℝ (gradient ψ x) (movForce d s h x)) := by
    intro x
    rw [mnc_force_smul hd hs0 hsd hc hh a x, inner_smul_right]
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring

lemma mnc_Phi_add_g {g1 g2 : Euc d → ℝ} (hg1 : Continuous g1) (hg2 : Continuous g2) {h : Euc d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hh : HRS.MP.RdGen.RgW (mnc_W d) 1 c h) :
    mnc_Phi d s ψ (fun y => g1 y + g2 y) h = mnc_Phi d s ψ g1 h + mnc_Phi d s ψ g2 h := by
  unfold mnc_Phi
  have e : ∀ x, (g1 x + g2 x) * inner ℝ (gradient ψ x) (movForce d s h x) =
      g1 x * inner ℝ (gradient ψ x) (movForce d s h x) + g2 x * inner ℝ (gradient ψ x) (movForce d s h x) :=
    fun x => add_mul _ _ _
  simp_rw [e]
  rw [integral_add (mnc_int_mul_gradforce hd hs0 hsd hψ hψc hc hh hg1)
    (mnc_int_mul_gradforce hd hs0 hsd hψ hψc hc hh hg2)]
  ring

lemma mnc_Phi_smul_g (a : ℝ) {g : Euc d → ℝ} {h : Euc d → ℝ} :
    mnc_Phi d s ψ (fun y => a * g y) h = a * mnc_Phi d s ψ g h := by
  unfold mnc_Phi
  have e : ∀ x, a * g x * inner ℝ (gradient ψ x) (movForce d s h x) =
      a * (g x * inner ℝ (gradient ψ x) (movForce d s h x)) := fun x => mul_assoc _ _ _
  simp_rw [e]
  rw [integral_const_mul]
  ring

lemma mnc_Phi_bound {g : Euc d → ℝ} (hg : Continuous g) {h : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hh : HRS.MP.RdGen.RgW (mnc_W d) 1 c h) :
    |mnc_Phi d s ψ g h| ≤ d * (mnc_Bf d s * c) * ∫ x, |g x| * ‖gradient ψ x‖ := by
  have hgr := mnc_grad_contDiff hψ
  have hgcs := mnc_grad_cs hψc
  have hint : Integrable (fun x => |g x| * ‖gradient ψ x‖) :=
    (hg.abs.mul hgr.norm).integrable_of_hasCompactSupport (HasCompactSupport.mul_left (f := fun x => |g x|) hgcs.norm)
  unfold mnc_Phi
  rw [abs_neg]
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ x, |g x * inner ℝ (gradient ψ x) (movForce d s h x)| ≤
      ∫ x, (d * (mnc_Bf d s * c)) * (|g x| * ‖gradient ψ x‖) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hint.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [abs_mul]
    have h1 : |inner ℝ (gradient ψ x) (movForce d s h x)| ≤ ‖gradient ψ x‖ * (d * (mnc_Bf d s * c)) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (mnc_force_norm_bound hd hs0 hsd hc hh x) (norm_nonneg _))
    calc |g x| * |inner ℝ (gradient ψ x) (movForce d s h x)|
        ≤ |g x| * (‖gradient ψ x‖ * (d * (mnc_Bf d s * c))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := by ring
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]

end Phi


/-! ### The functionals on `OscSpace d m` -/

section Osc

variable {β q : ℝ} {ρ : Euc d → ℝ}

/-- `h_u = √ρ · rep(u)` for `u ∈ Σ^m`, `rep` the `C³` representative. -/
def mnc_hu (ρ : Euc d → ℝ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) (u : OscSpace d (m : ℝ)) : Euc d → ℝ :=
  fun y => Real.sqrt (ρ y) * mn_repFun 3 m hn u y

lemma mnc_hu_add (ρ : Euc d → ℝ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) (u v : OscSpace d (m : ℝ)) :
    mnc_hu ρ hn (u + v) = fun y => mnc_hu ρ hn u y + mnc_hu ρ hn v y := by
  funext y
  simp only [mnc_hu, mn_repFun_add, Pi.add_apply]
  ring

lemma mnc_hu_smul (ρ : Euc d → ℝ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) (a : ℝ) (u : OscSpace d (m : ℝ)) :
    mnc_hu ρ hn (a • u) = fun y => a * mnc_hu ρ hn u y := by
  funext y
  simp only [mnc_hu, mn_repFun_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma mnc_hu_cont (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) (u : OscSpace d (m : ℝ)) :
    Continuous (mnc_hu ρ hn u) := by
  have := (mnc_h_gauss H hn).choose_spec.choose_spec.2.2 u
  exact this.1.continuous

lemma mnc_hu_rgW (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ u : OscSpace d (m : ℝ),
      HRS.MP.RdGen.RgW (mnc_W d) 1 (K1 * ‖u‖) (mnc_hu ρ hn u) :=
  mnc_rgW_h H hn (by norm_num)

/-- The `A`-functional: `u ↦ A_ψ(h_u)` as a continuous linear form. -/
theorem mnc_A_clm (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ A : OscSpace d (m : ℝ) →L[ℝ] ℝ, ∀ u, A u = mnc_A d s ρ ψ (mnc_hu ρ hn u) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H hn
  have hρc : Continuous ρ := (mnc_rho_smooth H).continuous
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ((mnb_rhoData H).pos x).le
  set I : ℝ := ∫ x, |ρ x| * ‖gradient ψ x‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  let lm : OscSpace d (m : ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => mnc_A d s ρ ψ (mnc_hu ρ hn u)
      map_add' := fun u v => by
        simp only [mnc_A_eq]
        rw [mnc_hu_add, mnc_Phi_add_h hd1 H.hs0 H.hsd hψ hψc hρc (mul_nonneg hK1 (norm_nonneg u))
          (mul_nonneg hK1 (norm_nonneg v)) (hW u) (hW v)]
      map_smul' := fun a u => by
        simp only [mnc_A_eq, RingHom.id_apply, smul_eq_mul]
        rw [mnc_hu_smul, mnc_Phi_smul_h hd1 H.hs0 H.hsd hψ hψc (mul_nonneg hK1 (norm_nonneg u)) (hW u)] }
  refine ⟨LinearMap.mkContinuous lm (d * (mnc_Bf d s * K1) * I) (fun u => ?_), fun u => rfl⟩
  have := mnc_Phi_bound hd1 H.hs0 H.hsd hψ hψc hρc (mul_nonneg hK1 (norm_nonneg u)) (hW u)
  show |mnc_Phi d s ψ ρ (mnc_hu ρ hn u)| ≤ _
  refine this.trans (le_of_eq ?_)
  ring


/-- The bilinear `Q`-functional. -/
theorem mnc_Q_clm (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ Qb : OscSpace d (m : ℝ) →L[ℝ] OscSpace d (m : ℝ) →L[ℝ] ℝ,
      ∀ u u', Qb u u' = mnc_Q d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u') := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H hn
  have hgr := mnc_grad_contDiff hψ
  have hgcs := mnc_grad_cs hψc
  set J : ℝ := ∫ x, ‖gradient ψ x‖ with hJ
  have hJint : Integrable (fun x => ‖gradient ψ x‖) :=
    hgr.norm.integrable_of_hasCompactSupport hgcs.norm
  have hJ0 : 0 ≤ J := integral_nonneg fun x => norm_nonneg _
  let lm : OscSpace d (m : ℝ) →ₗ[ℝ] OscSpace d (m : ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u u' => mnc_Q d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u'))
      (fun u u'' u' => by
        simp only [mnc_Q_eq]
        rw [mnc_hu_add, mnc_Phi_add_g hd1 H.hs0 H.hsd hψ hψc (mnc_hu_cont H hn u) (mnc_hu_cont H hn u'')
          (mul_nonneg hK1 (norm_nonneg u')) (hW u')])
      (fun a u u' => by
        simp only [mnc_Q_eq, smul_eq_mul]
        rw [mnc_hu_smul, mnc_Phi_smul_g hd1 H.hs0 H.hsd hψ hψc])
      (fun u u' u'' => by
        simp only [mnc_Q_eq]
        rw [mnc_hu_add, mnc_Phi_add_h hd1 H.hs0 H.hsd hψ hψc (mnc_hu_cont H hn u)
          (mul_nonneg hK1 (norm_nonneg u')) (mul_nonneg hK1 (norm_nonneg u'')) (hW u') (hW u'')])
      (fun a u u' => by
        simp only [mnc_Q_eq, smul_eq_mul]
        rw [mnc_hu_smul, mnc_Phi_smul_h hd1 H.hs0 H.hsd hψ hψc (mul_nonneg hK1 (norm_nonneg u')) (hW u')])
  refine ⟨LinearMap.mkContinuous₂ lm (d * (mnc_Bf d s * K1) * (K1 * J)) (fun u u' => ?_), fun u u' => rfl⟩
  have h1 := mnc_Phi_bound hd1 H.hs0 H.hsd hψ hψc (mnc_hu_cont H hn u) (mul_nonneg hK1 (norm_nonneg u'))
    (hW u')
  have h2 : ∫ x, |mnc_hu ρ hn u x| * ‖gradient ψ x‖ ≤ K1 * ‖u‖ * J := by
    have hb : ∀ x, |mnc_hu ρ hn u x| ≤ K1 * ‖u‖ := fun x => by
      have := (dc1a_rgW_facts (mul_nonneg hK1 (norm_nonneg u)) (hW u)).2.2.2.2 x
      rwa [Real.norm_eq_abs] at this
    rw [hJ, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (hJint.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  show |mnc_Phi d s ψ (mnc_hu ρ hn u) (mnc_hu ρ hn u')| ≤ _
  have hc : 0 ≤ (d : ℝ) * (mnc_Bf d s * (K1 * ‖u'‖)) := by
    have : 0 ≤ mnc_Bf d s * (K1 * ‖u'‖) := by
      have := (abs_nonneg _).trans (mnc_force_bound hd1 H.hs0 H.hsd (mul_nonneg hK1 (norm_nonneg u')) (hW u')
        0 ⟨0, by omega⟩)
      exact this
    positivity
  refine h1.trans ?_
  calc (d : ℝ) * (mnc_Bf d s * (K1 * ‖u'‖)) * ∫ x, |mnc_hu ρ hn u x| * ‖gradient ψ x‖
      ≤ (d : ℝ) * (mnc_Bf d s * (K1 * ‖u'‖)) * (K1 * ‖u‖ * J) := mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

lemma mnc_V_cont (H : Mov2dTh d s β q ρ) : Continuous (mov2a_V ρ) := by
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (ρ y)) := hρsm.log fun x => (hpos x).ne'
  unfold mov2a_V
  exact ((continuous_const.mul ((mnc_loggrad_cont hρsm hpos).norm.pow 2))).add
    (continuous_const.mul (mnc_lap_cont hlog))

/-- The diffusion density `D_φ = β⁻¹ (Δφ - Vφ)`. -/
def mnc_Dphi (ρ : Euc d → ℝ) (β : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x)

lemma mnc_Dphi_cont (H : Mov2dTh d s β q ρ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (mnc_Dphi ρ β φ) := by
  unfold mnc_Dphi
  exact continuous_const.mul ((mnc_lap_cont hφ).sub ((mnc_V_cont H).mul hφ.continuous))

lemma mnc_Dphi_cs {φ : Euc d → ℝ} (hφc : HasCompactSupport φ) : HasCompactSupport (mnc_Dphi ρ β φ) := by
  unfold mnc_Dphi
  exact ((mnc_lap_cs hφc).sub (hφc.mul_left (f := mov2a_V ρ))).mul_left (f := fun _ => β⁻¹)

/-- The diffusion functional `u ↦ ∫ rep(u) D_φ`. -/
theorem mnc_L_clm (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ L : OscSpace d (m : ℝ) →L[ℝ] ℝ, ∀ u, L u = ∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y := by
  have hDc := mnc_Dphi_cont H hφ
  have hDcs := mnc_Dphi_cs (ρ := ρ) (β := β) hφc
  obtain ⟨Cs, hCs0, hCs⟩ := mn_repFun_bound 3 m hn
  have hint : ∀ u : OscSpace d (m : ℝ), Integrable (fun y => mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y) := fun u =>
    (((mn_repFun_contDiff 3 m hn u).continuous).mul hDc).integrable_of_hasCompactSupport (hDcs.mul_left)
  set N : ℝ := ∫ y, |mnc_Dphi ρ β φ y| with hN
  have hNint : Integrable (fun y => |mnc_Dphi ρ β φ y|) := hDc.abs.integrable_of_hasCompactSupport hDcs.abs
  have hN0 : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  let lm : OscSpace d (m : ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y
      map_add' := fun u v => by
        simp only [mn_repFun_add, Pi.add_apply, add_mul]
        exact integral_add (hint u) (hint v)
      map_smul' := fun a u => by
        simp only [mn_repFun_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine ⟨LinearMap.mkContinuous lm (Cs * N) (fun u => ?_), fun u => rfl⟩
  show |∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y| ≤ _
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ y, |mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y| ≤ ∫ y, (Cs * ‖u‖) * |mnc_Dphi ρ β φ y| := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hNint.const_mul _)
      (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [abs_mul]
    have := hCs u 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end Osc

end HRS.MS.Mov63
