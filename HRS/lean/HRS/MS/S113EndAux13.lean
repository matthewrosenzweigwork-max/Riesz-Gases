import HRS.MS.S113EndAux12
import HRS.MS.MovSchTie

/-!
# S11.3 endpoint (worker S11X), part 13: the mild representation of the class members

`s113x_class_rep`: for the constants constructed in S6.3 (`mov63_decay_f0`, as in `s64_schwartz`), every member `ρ` of the small class is the mild
solution `ρ^t = mneRho ρ_* (v_t)` with `‖v_t‖ ≤ r`.  `s113x_rho_hasDerivAt`: from the representation, `∂_t ρ^t(x) = div(ρ^t u^t)(x)`, `u^t = movU (ρ^t)`
(right derivative at `0`, two-sided for `t > 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole HRS.MS.MovSch HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ}

theorem s113x_grad_eq_mul_log {f : Euc d → ℝ} {y : Euc d} (hf : DifferentiableAt ℝ f y) (hy : 0 < f y) :
    gradient f y = f y • gradient (fun z => Real.log (f z)) y := by
  refine ext_inner_left ℝ fun e => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, inner_smul_right, HRS.MS.PoisKolm.kl_inner_gradient]
  exact mv1_fderiv_rho hf hy e

/-- The flux of the mild representation is `ρ_u • movU ρ_u`, for a positive `C¹` density. -/
theorem s113x_Y_eq_rho_smul_movU {s q β : ℝ} {f : Euc d → ℝ} (hf : ∀ y, DifferentiableAt ℝ f y)
    (hpos : ∀ y, 0 < f y) :
    (fun y => β⁻¹ • gradient f y + f y • (q • y + movForce d s f y)) =
      fun y => f y • movU d s q β f y := by
  funext y
  unfold movU
  rw [s113x_grad_eq_mul_log (hf y) (hpos y)]
  simp only [smul_add, smul_smul]
  rw [mul_comm (f y) β⁻¹, ← smul_smul]
  abel



theorem s113x_class_rep (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (hm3 : (d : ℝ) / 2 + 3 < m) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
          ∃ v : ℝ → OscSpace d (m : ℝ),
            MneMild (⟨hd, hs0, hsd, hβ, hq, hρ⟩ : Mov2dTh d s β q ρ₀) hm3 v ∧
            (∀ t : ℝ, 0 ≤ t → ρ t = mneRho ρ₀ hm3 (v t)) ∧ (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ r) := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨c₁, hc₁, h⟩ := mov63_decay_f0 H hj
  obtain ⟨εstar, r, c, C₀, hε, hε4, hr, hc, hC₀, hf⟩ := h m hm
  have hC2 : (2 : ℝ) ≤ max C₀ 2 := le_max_right _ _
  refine ⟨εstar, r, c₁ / 2, c, max C₀ 2, hε, hr, by positivity, hc, by linarith, ?_, ?_⟩
  · intro f0 hf0
    have hcont := mnh_contDiff3 H hm3 hf0.cb hj hf0.osc
    have hmass := mnh_massZero H hm3 hf0.osc hf0.mean
    obtain ⟨v, hM, hv0, hcls, hrat, hDi, hDe, hI⟩ := hf hm3 f0 hcont hf0.cb hf0.osc hmass hf0.small
    have hRD := mnb_rhoData H
    have hCinv : (max C₀ 2)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hC2
    refine ⟨mneP d ρ₀ hm3 v, hcls, fun t ht => ⟨(hcls.solution t).density t ⟨ht, le_rfl⟩, fun x => ?_⟩,
      fun t ht x => ⟨?_, ?_⟩, mnh_decay_mono_C hε.le (le_max_left _ _) hDe,
      mnh_decay_mono_C (mnh_initialNorm_nonneg f0 ρ₀ j m) (le_max_left _ _) hDi, hI,
      mov_nl_unique_conjunct hd hs0 hsd hβ hq hρ hj hm hcls⟩
    · linarith [(hrat t ht x).1, hRD.pos x]
    · have h1 := (hrat t ht x).1
      have h2 : (max C₀ 2)⁻¹ * ρ₀ x ≤ 2⁻¹ * ρ₀ x := mul_le_mul_of_nonneg_right hCinv (hRD.pos x).le
      linarith
    · have h1 := (hrat t ht x).2
      have h2 : 2 * ρ₀ x ≤ max C₀ 2 * ρ₀ x := mul_le_mul_of_nonneg_right hC2 (hRD.pos x).le
      linarith
  · intro f0 hf0 ρ hρcls
    have hcont := mnh_contDiff3 H hm3 hf0.cb hj hf0.osc
    have hmass := mnh_massZero H hm3 hf0.osc hf0.mean
    obtain ⟨v, hmild, hv0, hcls, hrat, hDi, hDe, hI⟩ := hf hm3 f0 hcont hf0.cb hf0.osc hmass hf0.small
    have huniq := mov_nl_unique_conjunct hd hs0 hsd hβ hq hρ hj hm hcls ρ (hρcls.mono_rate (by positivity))
    refine ⟨v, hmild, fun t ht => by rw [huniq t ht, mneP_eq hm3 ht], fun t ht => ?_⟩
    have h1 := (hcls.weighted t ht).2
    rw [mne_movV hm3 H t ht, mneV_norm hm3] at h1
    refine h1.trans ?_
    have : Real.exp (-(c₁ / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith


/-- The flux `ρ^t u^t` of a member of the class, in terms of the mild representation. -/
theorem s113x_flux_eq {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} (H : Mov2dTh d s β q ρ₀)
    (hm3 : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) (hpos : ∀ y, 0 < mneRho ρ₀ hm3 u y) :
    (fun y => mneRho ρ₀ hm3 u y • movU d s q β (mneRho ρ₀ hm3 u) y) = mneY d s q β ρ₀ hm3 u := by
  have hdiff : ∀ y, DifferentiableAt ℝ (mneRho ρ₀ hm3 u) y := fun y =>
    ((mne_rho_cd hm3 H u).differentiable (by norm_num)) y
  exact (s113x_Y_eq_rho_smul_movU (s := s) (q := q) (β := β) hdiff hpos).symm

theorem s113x_rho_hasDerivAt {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} (H : Mov2dTh d s β q ρ₀)
    (hm3 : (d : ℝ) / 2 + 3 < m) {v : ℝ → OscSpace d (m : ℝ)} (hmild : MneMild H hm3 v)
    {ρ : ℝ → Euc d → ℝ} (hrep : ∀ t : ℝ, 0 ≤ t → ρ t = mneRho ρ₀ hm3 (v t))
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ y, 0 < ρ t y) :
    (∀ t : ℝ, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x)
        (movDiv (fun y => ρ t y • movU d s q β (ρ t) y) x) (Set.Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x, HasDerivAt (fun τ => ρ τ x)
        (movDiv (fun y => ρ t y • movU d s q β (ρ t) y) x) t) := by
  have hY : ∀ t : ℝ, 0 ≤ t → (fun y => ρ t y • movU d s q β (ρ t) y) = mneY d s q β ρ₀ hm3 (v t) := by
    intro t ht
    rw [hrep t ht]
    exact s113x_flux_eq H hm3 (v t) (fun y => by rw [← hrep t ht]; exact hpos t ht y)
  refine ⟨fun t ht x => ?_, fun t ht x => ?_⟩
  · have hder := mne_hasDeriv hm3 H hmild ht x
    rw [hY t ht]
    refine (hder.mono (Set.Ici_subset_Ici.2 ht)).congr (fun τ hτ => ?_) ?_
    · rw [hrep τ (ht.trans hτ)]
    · rw [hrep t ht]
  · have hder := mne_hasDerivAt hm3 H hmild ht x
    rw [hY t ht.le]
    refine hder.congr_of_eventuallyEq ?_
    filter_upwards [Ici_mem_nhds ht] with τ hτ
    rw [hrep τ hτ]

end HRS.MS.S113BD

end
