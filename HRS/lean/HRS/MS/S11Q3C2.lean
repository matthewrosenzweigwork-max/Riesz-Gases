import HRS.MS.S11Q3C1
import HRS.MS.S113EndAux28

/-!
# S11.3 / S11.4 (worker S11Q3), C2: the constructed S6.3 tuple has regular class members

`s11q3_class_data`: for the constants constructed in S6.3 (as in `s113x_class_facts`), every member `ρ` of the small class satisfies `S113XFacts`
and `s11q3_Reg d ρ D c B` with `D t x = div(ρ_t u_t)(x)` (the pointwise time derivative).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.Mov63 HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1 HRS.MS.MovForce HRS.MH.DualityRd
open HRS.MS.S113BD

variable {d : ℕ}

theorem s11q3_class_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (hm3 : (d : ℝ) / 2 + 3 < m) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
          S113XFacts d s q β ρ ∧ ∃ (D : ℝ → Euc d → ℝ) (c B : ℝ), s11q3_Reg d ρ D c B := by
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
  have hSlice : ∀ t : ℝ, 0 ≤ t → S113XSlice (ρ t) (movU d s q β (ρ t)) cg Kg (C * εstar) := fun t ht => by
    obtain ⟨-, hpos, -, hdec⟩ := hprops t ht
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
  have hder : ∀ t : ℝ, 0 < t → ∀ x, HasDerivAt (fun τ => ρ τ x)
      (movDiv (fun y => ρ t y • movU d s q β (ρ t) y) x) t :=
    (s113x_rho_hasDerivAt H hm3 hmild hreq (fun t ht y => (hprops t ht).2.1 y)).2
  refine ⟨⟨cg, Kg, C * εstar, hcg, hKg, hM, hG, hSlice, hder⟩, fun t x => movDiv (fun y => ρ t y • movU d s q β (ρ t) y) x,
    cg, max Kg ((d : ℝ) * (2 * (Kg * (C * εstar)))), ?_⟩
  have hBn : 0 ≤ max Kg ((d : ℝ) * (2 * (Kg * (C * εstar)))) := le_trans hKg (le_max_left _ _)
  have hexp : ∀ x : Euc d, 0 ≤ Real.exp (-cg * ‖x‖ ^ 2) := fun x => (Real.exp_pos _).le
  have hKle : ∀ x : Euc d, Kg * Real.exp (-cg * ‖x‖ ^ 2) ≤
      max Kg ((d : ℝ) * (2 * (Kg * (C * εstar)))) * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hexp x)
  obtain ⟨hj0, hj1, hj2⟩ := s11q3_rho_joint hm3 H hmild.cont
  have hrepeq : ∀ p : ℝ × Euc d, p ∈ Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)) → ρ p.1 = mneRho ρ₀ hm3 (v p.1) :=
    fun p hp => funext fun y => by rw [hreq p.1 hp.1]
  exact
    { hc := hcg
      hB := hBn
      pos := fun t ht x => (hprops t ht).2.1 x
      cd := fun t ht => (hG t ht).1.of_le (by norm_num)
      g0 := fun t ht x => by
        have := (hG t ht).2 0 (by norm_num) x
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
        exact this.trans (hKle x)
      g1 := fun t ht x => by
        have := (hG t ht).2 1 (by norm_num) x
        rw [norm_iteratedFDeriv_one] at this
        exact this.trans (hKle x)
      g2 := fun t ht x => by
        have := (hG t ht).2 2 (by norm_num) x
        rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
        exact this.trans (hKle x)
      gD := fun t ht x => by
        have := (hSlice t ht).D_le x
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hexp x))
      j0 := hj0.congr fun p hp => by simp only [hrepeq p hp]
      j1 := hj1.congr fun p hp => by simp only [hrepeq p hp]
      j2 := hj2.congr fun p hp => by simp only [hrepeq p hp]
      jD := by
        have hc := (mne_Ec_cont hm3 H hmild).continuousOn (s := Ici (0 : ℝ) ×ˢ (univ : Set (Euc d)))
        refine hc.congr fun p hp => ?_
        obtain ⟨t, x⟩ := p
        have hp1 : 0 ≤ t := hp.1
        simp only
        rw [mneEc_eq hm3 hp1 x, hreq t hp1]
        have := s113x_flux_eq H hm3 (v t) (fun y => by rw [← hreq t hp1]; exact (hprops t hp1).2.1 y)
        rw [this]
      dA := fun t ht x => hder t ht x }

end HRS.MS.S11Q3

end
