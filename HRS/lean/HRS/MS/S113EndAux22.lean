import HRS.MS.S113EndAux21

/-!
# S11.3 endpoint (worker S11X), part 22: Gaussian bounds, `S113XSlice` and the facts of a class member

* `s113x_rep_gauss`: the densities `ρ_* + √ρ_* rep(u)`, `‖u‖ ≤ r`, are `C³` with Gaussian-bounded derivatives up to order 3.
* `S113XFacts`: the uniform fixed-time data of a class member (slice at every time `t ≥ 0`, Gaussian derivative bounds, `∂_t ρ = div(ρ u)`).
* `s113x_class_facts`: the members of the S6.3 class (constructed constants) satisfy `S113XFacts`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole HRS.MS.Mov63 HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1 HRS.MS.MovForce HRS.MH.DualityRd

variable {d : ℕ}

theorem s113x_rep_gauss {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} (H : Mov2dTh d s β q ρ₀) (hm3 : (d : ℝ) / 2 + 3 < m)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ r →
      ContDiff ℝ 3 (mneRho ρ₀ hm3 u) ∧
        ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (mneRho ρ₀ hm3 u) x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨c1, K1, hc1, hK1, h1⟩ := mnc_rho_gauss H 3
  obtain ⟨c2, K0, hc2, hK0, h2⟩ := mnc_h_gauss H (mne_hn hm3)
  refine ⟨min c1 c2, K1 + K0 * r, lt_min hc1 hc2, by positivity, fun u hu => ⟨mne_rho_cd hm3 H u, fun n hn x => ?_⟩⟩
  obtain ⟨hcd, hb⟩ := h2 u
  have hρ3 : ContDiff ℝ 3 ρ₀ := (contDiff_infty.1 (mnc_rho_smooth H)) 3
  have hsum : mneRho ρ₀ hm3 u = ρ₀ + mnc_hu ρ₀ (mne_hn hm3) u := rfl
  have hcd' : ContDiff ℝ (3 : ℕ) (mnc_hu ρ₀ (mne_hn hm3) u) := by exact_mod_cast hcd
  have hρn : ContDiff ℝ (n : ℕ) ρ₀ := hρ3.of_le (by exact_mod_cast hn)
  have hhn : ContDiff ℝ (n : ℕ) (mnc_hu ρ₀ (mne_hn hm3) u) := hcd'.of_le (by exact_mod_cast hn)
  rw [hsum, iteratedFDeriv_add_apply hρn.contDiffAt hhn.contDiffAt]
  refine (norm_add_le _ _).trans ?_
  have e1 : Real.exp (-c1 * ‖x‖ ^ 2) ≤ Real.exp (-(min c1 c2) * ‖x‖ ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c1 c2, sq_nonneg ‖x‖])
  have e2 : Real.exp (-c2 * ‖x‖ ^ 2) ≤ Real.exp (-(min c1 c2) * ‖x‖ ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c1 c2, sq_nonneg ‖x‖])
  have a1 := h1 n hn x
  have a2 := hb n hn x
  have hE := Real.exp_pos (-(min c1 c2) * ‖x‖ ^ 2)
  calc ‖iteratedFDeriv ℝ n ρ₀ x‖ + ‖iteratedFDeriv ℝ n (mnc_hu ρ₀ (mne_hn hm3) u) x‖
      ≤ K1 * Real.exp (-c1 * ‖x‖ ^ 2) + (K0 * ‖u‖) * Real.exp (-c2 * ‖x‖ ^ 2) := add_le_add a1 a2
    _ ≤ K1 * Real.exp (-(min c1 c2) * ‖x‖ ^ 2) + (K0 * r) * Real.exp (-(min c1 c2) * ‖x‖ ^ 2) := by
        gcongr
    _ = _ := by ring


/-- The uniform data of a member of the class. -/
def S113XFacts (d : ℕ) (s q β : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∃ c B M : ℝ, 0 < c ∧ 0 ≤ B ∧ 0 ≤ M ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 3 (ρ t) ∧
      ∀ k ≤ 3, ∀ y, ‖iteratedFDeriv ℝ k (ρ t) y‖ ≤ B * Real.exp (-c * ‖y‖ ^ 2)) ∧
    (∀ t : ℝ, 0 ≤ t → S113XSlice (ρ t) (movU d s q β (ρ t)) c B M) ∧
    (∀ t : ℝ, 0 < t → ∀ x, HasDerivAt (fun τ => ρ τ x)
      (movDiv (fun y => ρ t y • movU d s q β (ρ t) y) x) t)

theorem s113x_class_facts (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (hm3 : (d : ℝ) / 2 + 3 < m) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → S113XFacts d s q β ρ := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨εstar, r, c₀, c, C, hε, hr, hc₀, hc, hC, hNL, hrep⟩ := s113x_class_rep hd hs0 hsd β q hβ hq j m hj hm hm3 ρ₀ hρ
  refine ⟨εstar, r, c₀, c, C, hε, hr, hc₀, hc, hC, hNL, fun f0 hf0 ρ hρ' => ?_⟩
  obtain ⟨v, hmild, hreq, hv⟩ := hrep f0 hf0 ρ hρ'
  obtain ⟨cg, Kg, hcg, hKg, hgauss⟩ := s113x_rep_gauss H hm3 r hr.le
  have hprops := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le
  have hG : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ 3 (ρ t) ∧
      ∀ k ≤ 3, ∀ y, ‖iteratedFDeriv ℝ k (ρ t) y‖ ≤ Kg * Real.exp (-cg * ‖y‖ ^ 2) := fun t ht => by
    rw [hreq t ht]; exact hgauss (v t) (hv t ht)
  have hM : 0 ≤ C * εstar := by positivity
  refine ⟨cg, Kg, C * εstar, hcg, hKg, hM, hG, fun t ht => ?_, ?_⟩
  · obtain ⟨-, hpos, -, hdec⟩ := hprops t ht
    obtain ⟨-, -, hcd, hcb⟩ := (hdec t ht)
    have hB0 : 0 ≤ C * εstar * Real.exp (-c * t) := by positivity
    have hcb' : cbNormVecE j (movU d s q β (ρ t)) + cbNormVecE j (fun x => gradient (fun y => Real.log (ρ t y / ρ₀ y)) x) ≤
        ENNReal.ofReal (C * εstar * Real.exp (-c * t)) := by rwa [add_comm]
    have hexp : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hle : C * εstar * Real.exp (-c * t) ≤ C * εstar := mul_le_of_le_one_right hM hexp
    refine ⟨hcg, hKg, hM, hpos, ((hG t ht).1.of_le (by norm_num)), fun x => ?_, fun x => ?_, hcd.of_le (by exact_mod_cast hj), fun x => ?_, fun x => ?_⟩
    · have := (hG t ht).2 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    · have := (hG t ht).2 1 (by norm_num) x
      rwa [norm_iteratedFDeriv_one] at this
    · have := mne_cbVec_le hB0 hcb' 0 (by omega) x
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans hle
    · have := mne_cbVec_le hB0 hcb' 1 hj x
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans hle
  · exact (s113x_rho_hasDerivAt H hm3 hmild hreq (fun t ht y => (hprops t ht).2.1 y)).2

end HRS.MS.S113BD

end
