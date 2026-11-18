import HRS.MS.Mov63FAux3

/-!
# S6.3, packet N7 (part 4): the master comparison for the `Q`-equation

Namespace `HRS.MS.Mov63`, prefix `mnf_`.  See `Mov63FAux1`.

For the N5/N6 mild solution `v` (`MneMild`), `Q_t = mneQ ρ hm (v t)` solves, classically, `∂_tQ = νΔQ + ⟨b_t,∇Q⟩ + A_t Q`
(`mne_Q_hasDerivAt`) with `ν = β⁻¹`, `b_t = ν∇log ρ + F_t` (`mnfb`), `A_t = div F_t + ⟨∇log ρ, F_t⟩` (`mnfA`).

**`mnf_master`**: for `P = γ(t) + α(t) Q` with `α, γ` differentiable, if `c P ≤ ∂_tP - νΔP - ⟨b,∇P⟩` for some `c ≤ 0`
(i.e. `c (γ + αQ) ≤ γ' + (α' + αA) Q`), `|P| ≤ K_p exp((5βq/16)‖x‖²)` on `[0,T]×ℝ^d` and `P(0,·) ≥ 0`, then `P ≥ 0` on `[0,T]×ℝ^d`.
The Lyapunov function is `exp(l t + (3βq/8)‖x‖²)` (`2ν κ < q` for `κ = 3βq/8`; `5βq/16 < κ`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoissonSpike

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Master

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) {v : ℝ → OscSpace d (m : ℝ)}

/-- The drift `b_u = ν ∇log ρ + F_u` of the `Q`-equation. -/
abbrev mnfb (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) (x : Euc d) : Euc d :=
  β⁻¹ • gradient (fun y => Real.log (ρ y)) x + mneFo d s ρ hm u x

/-- The zero-order coefficient `A_u = div F_u + ⟨∇log ρ, F_u⟩` of the `Q`-equation. -/
abbrev mnfA (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) (x : Euc d) : ℝ :=
  movDiv (mneFo d s ρ hm u) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (mneFo d s ρ hm u x)

lemma mnf_laplacian_const (γ : ℝ) (x : Euc d) : Laplacian.laplacian (fun _ : Euc d => γ) x = 0 := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun _ : Euc d => γ)) x]
  simp [iteratedFDeriv_const_of_ne]

lemma mnf_gradient_const (γ : ℝ) (x : Euc d) : gradient (fun _ : Euc d => γ) x = 0 := by
  simp [gradient]

lemma mnf_laplacian_aff {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (γ a : ℝ) (x : Euc d) :
    Laplacian.laplacian (fun z => γ + a * g z) x = a * Laplacian.laplacian g x := by
  rw [mnf_laplacian_add_smul (f := fun _ : Euc d => γ) contDiffAt_const hg.contDiffAt a, mnf_laplacian_const]
  ring

lemma mnf_gradient_aff {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (γ a : ℝ) (x : Euc d) :
    gradient (fun z => γ + a * g z) x = a • gradient g x := by
  rw [mnf_gradient_add_smul (f := fun _ : Euc d => γ) (differentiableAt_const γ)
    ((hg.differentiable (by norm_num)) x) a, mnf_gradient_const, zero_add]

include hm in
lemma mnf_Q_joint (H : Mov2dTh d s β q ρ) (hmild : MneMild H hm v) :
    ContinuousOn (fun p : ℝ × Euc d => mneQ ρ hm (v p.1) p.2) (Ici 0 ×ˢ univ) := by
  have h1 := (mne_joint hm H hmild.cont).1
  have hρc : Continuous ρ := (mnc_rho_smooth H).continuous
  have hρ' : Continuous (fun p : ℝ × Euc d => ρ p.2) := hρc.comp continuous_snd
  exact (hρ'.continuousOn.add h1).div hρ'.continuousOn (fun p _ => ((mnb_rhoData H).pos p.2).ne')

/-- **The master comparison** for `P = γ + αQ`. -/
theorem mnf_master (H : Mov2dTh d s β q ρ) (hmild : MneMild H hm v) {K : ℝ}
    (hvK : ∀ t, 0 ≤ t → ‖v t‖ ≤ K) {T : ℝ}
    {α γ α' γ' : ℝ → ℝ} (hα : ∀ t, HasDerivAt α (α' t) t) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    {c : ℝ → Euc d → ℝ} (hc : ∀ t ∈ Ioc 0 T, ∀ x, c t x ≤ 0)
    (hineq : ∀ t ∈ Ioc 0 T, ∀ x, c t x * (γ t + α t * mneQ ρ hm (v t) x) ≤
      γ' t + (α' t + α t * mnfA d s ρ hm (v t) x) * mneQ ρ hm (v t) x)
    {Kp : ℝ} (hKp : 0 ≤ Kp)
    (hPb : ∀ t ∈ Icc 0 T, ∀ x, |γ t + α t * mneQ ρ hm (v t) x| ≤
      Kp * Real.exp ((5 * β * q / 16) * ‖x‖ ^ 2))
    (h0 : ∀ x, 0 ≤ γ 0 + α 0 * mneQ ρ hm (v 0) x) :
    ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ γ t + α t * mneQ ρ hm (v t) x := by
  have hβ := H.hβ
  have hq := H.hq
  obtain ⟨M0, hM00, hM0⟩ := mnf_M0 hm H
  obtain ⟨CF, hCF0, hCF⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  set Mdr : ℝ := M0 + CF * K with hMdr
  set κ : ℝ := 3 * β * q / 8 with hκ
  have hκpos : 0 < κ := by positivity
  have hνpos : 0 < β⁻¹ := inv_pos.2 hβ
  have hνκ : 2 * β⁻¹ * κ < q := by
    rw [hκ]
    have : 2 * β⁻¹ * (3 * β * q / 8) = 3 * q / 4 := by field_simp; ring
    rw [this]; linarith
  set lam : ℝ := 2 * β⁻¹ * κ * d + κ ^ 2 * Mdr ^ 2 / (2 * κ * q - 4 * β⁻¹ * κ ^ 2) + 1 with hlam
  have hapos : 0 < 2 * κ * q - 4 * β⁻¹ * κ ^ 2 := by
    have : 0 < 2 * κ * (q - 2 * β⁻¹ * κ) := mul_pos (by positivity) (by linarith)
    nlinarith
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    have : 0 ≤ 2 * β⁻¹ * κ * d := by positivity
    have : 0 ≤ κ ^ 2 * Mdr ^ 2 / (2 * κ * q - 4 * β⁻¹ * κ ^ 2) := by positivity
    linarith
  have hκ0 : 5 * β * q / 16 < κ := by
    rw [hκ]; have := mul_pos hβ hq; nlinarith
  have hQcd : ∀ t, ContDiff ℝ 2 (mneQ ρ hm (v t)) := fun t => (mneQ_cd hm H (v t)).of_le (by norm_num)
  have hJ := mnf_Q_joint hm H hmild
  refine mnf_comparison (ν := β⁻¹) hνpos.le (T := T)
    (P := fun t x => γ t + α t * mneQ ρ hm (v t) x)
    (Pt := fun t x => γ' t + (α' t * mneQ ρ hm (v t) x + α t *
      (β⁻¹ * Laplacian.laplacian (mneQ ρ hm (v t)) x +
        inner ℝ (mnfb d s β ρ hm (v t) x) (gradient (mneQ ρ hm (v t)) x) +
        mnfA d s ρ hm (v t) x * mneQ ρ hm (v t) x)))
    (φ := mnf_lyap lam κ) (φt := fun t x => lam * mnf_lyap lam κ t x)
    (b := fun t x => mnfb d s β ρ hm (v t) x) (c := c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc ?_ ?_ ?_ h0
  · intro t ht
    exact contDiff_const.add (contDiff_const.mul (hQcd t))
  · intro t ht
    exact mnf_lyap_cd lam κ t
  · -- joint continuity of P
    have hαc : Continuous α := continuous_iff_continuousAt.2 fun t => (hα t).continuousAt
    have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
    have h1 : ContinuousOn (fun p : ℝ × Euc d => mneQ ρ hm (v p.1) p.2) (Icc 0 T ×ˢ univ) :=
      hJ.mono (prod_mono Icc_subset_Ici_self le_rfl)
    exact ((hγc.comp continuous_fst).continuousOn).add (((hαc.comp continuous_fst).continuousOn).mul h1)
  · exact (mnf_lyap_cont lam κ).continuousOn
  · intro t ht x
    have := (hγ t).add ((hα t).mul (mne_Q_hasDerivAt hm H hmild ht.1 x))
    exact this.hasDerivWithinAt
  · intro t ht x
    exact (mnf_lyap_hasDerivAt lam κ t x).hasDerivWithinAt
  · intro t ht x
    have e1 := mnf_laplacian_aff (hQcd t) (γ t) (α t) x
    have e2 := mnf_gradient_aff (hQcd t) (γ t) (α t) x
    have hh := hineq t ht x
    simp only [e1, e2, inner_smul_right]
    nlinarith
  · intro t ht x
    have hvt : ‖v t‖ ≤ K := hvK t ht.1.le
    have hb := mnf_drift_bound hm H hM0 (fun u x => (hCF u).2.1 x) (v t) x
    have hr : (M0 + CF * ‖v t‖) * ‖x‖ ≤ Mdr * ‖x‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [hMdr]; nlinarith
    exact mnf_lyap_super hνpos hκpos hνκ t x _ (hb.trans (by linarith))
  · intro t ht x
    exact mnf_lyap_pos _ _ _ _
  · exact mnf_hgrow hKp hκ0 hlam0 hPb

end Master

end HRS.MS.Mov63

end
