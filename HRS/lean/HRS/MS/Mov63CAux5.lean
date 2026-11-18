import HRS.MS.Mov63CAux4

/-!
# S6.3, uniqueness chain (N3a, final): weak solutions satisfy the linear weak identity

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.

`mnc_weak_linear`: for a member `P` of `MovInSmallClass`, `u_r = ofFun m (movV ρ P r)` and `φ ∈ C_c^∞`,
`⟨φ,u_t⟩ - ⟨φ,u_0⟩ = ∫_{[0,t]} ( -⟨S_0φ, u_r⟩ - ⟨φ, R u_r⟩ + ⟨φ, B(u_r,u_r)⟩ ) dr`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- A continuous `Σ^n` function is `C^i` and equals its representative. -/
lemma mnc_rep_of_cont {i n : ℕ} (hn : (i : ℝ) + d / 2 < n) {f : Euc d → ℝ} (hc : Continuous f)
    (hf : MemOsc (n : ℝ) f) :
    ContDiff ℝ (i : WithTop ℕ∞) f ∧ mn_repFun i n hn (OscSpace.ofFun (n : ℝ) f) = f := by
  obtain ⟨hg, f', hf', hfu, hfg⟩ := mn_repFun_spec i n hn (OscSpace.ofFun (n : ℝ) f)
  have h1 : OscSpace.toLp (OscSpace.ofFun (n : ℝ) f') = OscSpace.toLp (OscSpace.ofFun (n : ℝ) f) := by
    rw [hfu]
  rw [OscSpace.toLp_ofFun _ hf', OscSpace.toLp_ofFun _ hf] at h1
  have h2 : f' =ᵐ[(volume : Measure (Euc d))] f := (MemLp.toLp_eq_toLp_iff hf'.1 hf.1).1 h1
  have h3 : f = mn_repFun i n hn (OscSpace.ofFun (n : ℝ) f) :=
    mn_ae_eq_cont hc hg.continuous (h2.symm.trans hfg)
  refine ⟨?_, h3.symm⟩
  rw [h3]
  exact hg

lemma mnc_gauss_mono {c c' : ℝ} (h : c ≤ c') (x : Euc d) : Real.exp (-c' * ‖x‖ ^ 2) ≤ Real.exp (-c * ‖x‖ ^ 2) :=
  Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖x‖])

/-- `RegSliceRd` of `ρ + h_u` when it is a probability density. -/
lemma mnc_regSlice_hu (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m)
    (u : OscSpace d (m : ℝ)) (hp : Whole.IsProbDensity (fun y => ρ y + mnc_hu ρ hn u y)) :
    RegSliceRd (fun y => ρ y + mnc_hu ρ hn u y) := by
  obtain ⟨c1, K1, hc1, hK1, hb1⟩ := mnc_rho_gauss H 3
  obtain ⟨c2, K0, hc2, hK0, h2⟩ := mnc_h_gauss H hn
  have hρ3 : ContDiff ℝ 3 ρ := (mnc_rho_smooth H).of_le (by simp)
  have hh3 : ContDiff ℝ 3 (mnc_hu ρ hn u) := by exact_mod_cast (h2 u).1
  refine mnc_regSlice_of_gauss (c := min c1 c2) (K := K1 + K0 * ‖u‖) (lt_min hc1 hc2)
    (by positivity) (hρ3.add hh3) (fun n hn3 x => ?_) hp
  have e : iteratedFDeriv ℝ n (fun y => ρ y + mnc_hu ρ hn u y) x =
      iteratedFDeriv ℝ n ρ x + iteratedFDeriv ℝ n (mnc_hu ρ hn u) x :=
    iteratedFDeriv_add_apply (hρ3.of_le (by exact_mod_cast hn3)).contDiffAt (hh3.of_le (by exact_mod_cast hn3)).contDiffAt
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have a1 := (hb1 n hn3 x).trans (mul_le_mul_of_nonneg_left (mnc_gauss_mono (min_le_left c1 c2) x) hK1)
  have a2 := ((h2 u).2 n hn3 x).trans (mul_le_mul_of_nonneg_left (mnc_gauss_mono (min_le_right c1 c2) x)
    (mul_nonneg hK0 (norm_nonneg u)))
  refine (add_le_add a1 a2).trans (le_of_eq ?_)
  ring


/-- The element `u_r = ofFun m (movV ρ P r)` of `Σ^m`. -/
def mnc_u (ρ : Euc d → ℝ) (P : ℝ → Euc d → ℝ) (m : ℕ) (r : ℝ) : OscSpace d (m : ℝ) :=
  OscSpace.ofFun (m : ℝ) (movV ρ P r)

section Weak

variable {P : ℝ → Euc d → ℝ} {m : ℕ} {r c₀ : ℝ} {f0 : Euc d → ℝ}

lemma mnc_movV_cont (H : Mov2dTh d s β q ρ) (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (movV ρ P t) := by
  have hpos := (mnb_rhoData H).pos
  unfold movV
  exact ((hcls.regular t ht).sub (mnc_rho_smooth H).continuous).div
    ((mnc_rho_smooth H).continuous.sqrt) (fun x => (Real.sqrt_pos.2 (hpos x)).ne')

/-- The weak-form integrand at time `r ≥ 0`, identified with the functionals on `Σ^m`. -/
theorem mnc_integrand (H : Mov2dTh d s β q ρ) {m : ℕ} (hn : ((3 : ℕ) : ℝ) + d / 2 < m)
    (hm : (d : ℝ) / 2 + 3 < m) (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    Whole.pair (Whole.withDensityReal (P t))
        (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian (fun z => φ z / Real.sqrt (ρ z)) x -
          inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient (fun z => φ z / Real.sqrt (ρ z)) x)) +
      interactionPairingW (quadraticGradientDyn d s q β) (fun z => φ z / Real.sqrt (ρ z))
        (Whole.withDensityReal (P t)) (Whole.withDensityReal (P t)) =
    -(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) (mnc_u ρ P m t)) -
      mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m t)) +
      mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m t) (mnc_u ρ P m t)) := by
  have hpos := (mnb_rhoData H).pos
  have hmem := (hcls.weighted t ht).1
  obtain ⟨-, hrep⟩ := mnc_rep_of_cont hn (mnc_movV_cont H hcls ht) hmem
  set u := mnc_u ρ P m t with hu
  have hrep' : mn_repFun 3 m hn u = movV ρ P t := hrep
  have hhu : mnc_hu ρ hn u = fun y => P t y - ρ y := by
    funext y
    have hs : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
    simp only [mnc_hu, hrep', movV]
    field_simp
  have hPr : (fun y => ρ y + mnc_hu ρ hn u y) = P t := by
    funext y; rw [hhu]; ring
  have hprob : Whole.IsProbDensity (fun y => ρ y + mnc_hu ρ hn u y) := by
    rw [hPr]; exact (hcls.solution t).density t ⟨ht, le_rfl⟩
  have hreg := mnc_regSlice_hu H hn u hprob
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H hn
  have hdec := mnc_decomp H hφ hφc (mul_nonneg hK1 (norm_nonneg u)) (hW u) hreg
  rw [hPr] at hdec
  rw [hdec]
  have e1 : (∫ x, (mnc_hu ρ hn u x / Real.sqrt (ρ x)) * (β⁻¹ * (Laplacian.laplacian φ x - mov2a_V ρ x * φ x))) =
      ∫ y, mn_repFun 3 m hn u y * mnc_Dphi ρ β φ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hpos x)
    simp only [mnc_hu, mnc_Dphi]
    field_simp
  rw [e1, mnc_Q_eq, ← mnc_Q_eq (s := s), mnc_quad_osc H hn hm hφ hφc u u]
  have := mnc_lin_osc H hn hm hφ hφc u
  linarith


/-- **N3a**: a member of the class satisfies the linear weak identity against `C_c^∞` test functions. -/
theorem mnc_weak_linear (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)
    (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    mnc_ipL φ (Nat.cast_nonneg m) (mnc_u ρ P m t) - mnc_ipL φ (Nat.cast_nonneg m) (mnc_u ρ P m 0) =
      ∫ x in Set.Icc (0 : ℝ) t,
        (-(mnc_ipL (mov_S0 d β q φ) (Nat.cast_nonneg m) (mnc_u ρ P m x)) -
          mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x)) +
          mnc_ipL φ (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x))) := by
  have hn : ((3 : ℕ) : ℝ) + d / 2 < m := by push_cast; linarith
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  have hψs := mnc_psi_smooth hρsm hpos hφ
  have hψc : HasCompactSupport (fun z => φ z / Real.sqrt (ρ z)) := mnc_psi_cs hφc
  have hψM : MemCb 2 (fun z => φ z / Real.sqrt (ρ z)) := mnc_memCb_of_cs hψs hψc 2
  have hweak := ((hcls.solution t).weak _ hψM t ⟨ht, le_rfl⟩)
  rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => mnc_integrand H hn hm hcls hφ hφc hx.1)] at hweak
  rw [← hweak]
  have hφ2 : MemLp φ 2 (volume : Measure (Euc d)) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hP : ∀ x, 0 ≤ x → Whole.IsProbDensity (P x) := fun x hx => (hcls.solution x).density x ⟨hx, le_rfl⟩
  -- expand both sides as integrals of continuous compactly supported functions
  have hPψ : ∀ x, 0 ≤ x → ∫ y, (P x y) * (φ y / Real.sqrt (ρ y)) =
      Whole.pair (Whole.withDensityReal (P x)) (fun y => φ y / Real.sqrt (ρ y)) := fun x hx => by
    rw [Whole.pair, dc1a_integral_withDensity (hP x hx).measurable (hP x hx).nonneg]
  have hPi : ∀ x, 0 ≤ x → Integrable (fun y => (P x y) * (φ y / Real.sqrt (ρ y))) := fun x hx =>
    ((hcls.regular x hx).mul hψs.continuous).integrable_of_hasCompactSupport (hψc.mul_left (f := P x))
  have hvφ : ∀ x, 0 ≤ x → Integrable (fun y => φ y * movV ρ P x y) := fun x hx =>
    (hφ.continuous.mul (mnc_movV_cont H hcls hx)).integrable_of_hasCompactSupport (hφc.mul_right)
  have hkey : ∀ x, 0 ≤ x → ∀ y, P x y = ρ y + Real.sqrt (ρ y) * movV ρ P x y := by
    intro x hx y
    have hs : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
    simp only [movV]
    field_simp
    ring
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have e1 : mnc_ipL φ (Nat.cast_nonneg m) (mnc_u ρ P m t) = ∫ y, φ y * movV ρ P t y :=
    mnc_ipL_ofFun hφ2 _ (hcls.weighted t ht).1
  have e0 : mnc_ipL φ (Nat.cast_nonneg m) (mnc_u ρ P m 0) = ∫ y, φ y * movV ρ P 0 y :=
    mnc_ipL_ofFun hφ2 _ (hcls.weighted 0 h0).1
  rw [e1, e0, ← hPψ t ht, ← hPψ 0 h0, ← integral_sub (hvφ t ht) (hvφ 0 h0), ← integral_sub (hPi t ht) (hPi 0 h0)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hs : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
  dsimp only
  rw [hkey t ht y, hkey 0 h0 y]
  field_simp
  ring

end Weak

end HRS.MS.Mov63
