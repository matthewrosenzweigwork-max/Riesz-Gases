import HRS.MS.SA16SEn12

/-!
# S.A.16 (SA16S) En13: Gronwall and the energy bound for the Duhamel solution (packet P7, sub case)

`sa16sz_energy_solution`: for the mild solution `u ∈ C([0,T]; W^{m+2,p})` of `sa16r_fixedn_mild` with
`K_r = b_r·∇ - G_r ι` (`b_r` smooth, `‖D^i b_{r,l}‖ ≤ B` for `i ≤ m+1`, `G_r` bounded nonlocal operators compatible with
level `m`, `‖G_r‖_{W^{m,p}} ≤ CG`):  `jetEnergy_m(u(τ)) ≤ jetEnergy_m(φ) e^{cτ}`, `c = p(cTr + C_J CG)` independent of `ν`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En13
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- Gronwall for a function continuous on `[0,T]` with `e' ≤ c e` in the interior -/
lemma sa16sz_gronwall {e : ℝ → ℝ} {T c : ℝ} (hc : ContinuousOn e (Icc 0 T))
    (hd : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧ e' ≤ c * e τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, e τ ≤ e 0 * Real.exp (c * τ) := by
  set g : ℝ → ℝ := fun τ => e τ * Real.exp (-(c * τ)) with hg
  have hgc : ContinuousOn g (Icc 0 T) :=
    hc.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  have hgd : ∀ τ ∈ Ioo 0 T, ∃ g' : ℝ, HasDerivAt g g' τ ∧ g' ≤ 0 := by
    intro τ hτ
    obtain ⟨e', he', hle⟩ := hd τ hτ
    have h2 : HasDerivAt (fun τ => Real.exp (-(c * τ))) (Real.exp (-(c * τ)) * (-c)) τ := by
      have := ((hasDerivAt_id τ).const_mul c).neg.exp
      simpa using this
    refine ⟨e' * Real.exp (-(c * τ)) + e τ * (Real.exp (-(c * τ)) * (-c)), he'.mul h2, ?_⟩
    have hx := Real.exp_pos (-(c * τ))
    nlinarith [mul_le_mul_of_nonneg_right hle hx.le]
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgc ?_ ?_
    · rw [interior_Icc]
      intro τ hτ
      obtain ⟨g', hg', -⟩ := hgd τ hτ
      exact hg'.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro τ hτ
      obtain ⟨g', hg', hle⟩ := hgd τ hτ
      rw [hg'.deriv]; exact hle
  intro τ hτ
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [hτ.1, hτ.2]⟩
  have := hanti h0 hτ hτ.1
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  have hpos := Real.exp_pos (c * τ)
  calc e τ = e τ * Real.exp (-(c * τ)) * Real.exp (c * τ) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ e 0 * Real.exp (c * τ) := mul_le_mul_of_nonneg_right this hpos.le

set_option maxHeartbeats 1600000 in
/-- **Energy bound for the Duhamel solution** (packet P7, sub case). -/
theorem sa16sz_energy_solution {m : ℕ} {ν T B Bk CG : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B (bc r))
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ τ ∈ Icc (0 : ℝ) T,
      jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
        jetEnergy d m p (sa16sz_iota2 d m p φ) *
          Real.exp ((p * sa16sz_cTr d m p B + p * CJ * CG) * τ) := by
  obtain ⟨CJ, hCJ0, hgen⟩ := sa16sz_gen_energy (d := d) (p := p) m
  refine ⟨CJ, hCJ0, ?_⟩
  set c : ℝ := p * sa16sz_cTr d m p B + p * CJ * CG with hc
  set e : ℝ → ℝ := fun τ => jetEnergy d m p (sa16sz_iota2 d m p (u τ)) with he
  have hcont : ContinuousOn e (Icc 0 T) :=
    (sa16sz_jetEnergy_cont m).comp_continuousOn ((sa16sz_iota2 d m p).continuous.comp_continuousOn hu)
  have hderiv : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧ e' ≤ c * e τ := by
    intro τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
    have hdu := sa16sx_hasDerivAt hν hT K hKb hBk hKc φ hu hsol hτ
    have hE := (sa16v2_jetEnergy_hasFDerivAt d m p (sa16sz_iota2 d m p (u τ))).comp_hasDerivAt τ hdu
    refine ⟨sa16v2_Dj d m p (sa16r_iota d m p (sa16r_iota d (m + 1) p (u τ))) (sa16sx_f m ν K u τ), hE, ?_⟩
    have hf : sa16sx_f m ν K u τ = ν • sa16so_Lap d m p (u τ) +
        sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) - T0 τ (sa16sz_iota2 d m p (u τ)) := by
      unfold sa16sx_f
      rw [hK τ]
      have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p (u τ))) (hcomp τ hτI)
      simp only [ContinuousLinearMap.comp_apply] at h1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, h1]
      unfold sa16sz_iota2
      simp only [ContinuousLinearMap.comp_apply]
      abel
    have hder : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p (u τ)) =
        sa16v2_Dj d m p (sa16sz_iota2 d m p (u τ)) :=
      (sa16v2_jetEnergy_hasFDerivAt d m p _).fderiv
    have := hgen hν.le (hbc τ hτI) (T0 τ) (hT0 τ hτI) (u τ)
    rw [hder, ← hf] at this
    exact this
  have hmain := sa16sz_gronwall hcont hderiv
  have h0 : e 0 = jetEnergy d m p (sa16sz_iota2 d m p φ) := by
    have := sa16sx_strong hν hT K hKb hBk hKc φ hu hsol 0 ⟨le_rfl, hT.le⟩
    simp only [he, intervalIntegral.integral_same, add_zero] at this ⊢
    unfold sa16sz_iota2
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
  intro τ hτ
  have := hmain τ hτ
  rw [h0] at this
  exact this

end En13

end HRS.Whole.AppendixA.Phase2SA16R
