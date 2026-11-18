import HRS.MS.MovSchAux4

/-!
# S64 (S6.4 `mov_schwartz`), part 5: the assembly `s64_schwartz`

Namespace `HRS.MS.MovSch`, prefix `s64_`.  The statement of `HRS.Whole.mov_schwartz`.  Constants as in `mnh_nonlinear`
(`mov63_decay_f0`: `εstar, r, c₀ = c₁/2, c, C = max C₀ 2`); `MovNonlinearConclusion` is the same assembly.  For the new conjunct:
a member `ρ` of `MovInSmallClass r c₀ f0` equals the constructed solution `mneP .. v` on `t ≥ 0` (exponent-0 uniqueness,
`mov_nl_unique_conjunct`, `MovInSmallClass.mono_rate`); `ρ' t x = div Y_t(x)` is its classical right derivative
(`mne_hasDeriv`), and the weighted bounds are `s64_out` with `‖v_t‖_{Σ^m} ≤ C εstar e^{-ct}` (`MovDecayBounds`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

theorem s64_schwartz {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (K j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (hmK : (K : ℝ) + d / 2 + 4 < m) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ L : ℕ, ∃ CKL : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
          ∃ ρ' : ℝ → Euc d → ℝ,
            (∀ t : ℝ, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t) ∧
            ∀ t : ℝ, 0 ≤ t → ContDiff ℝ K (ρ t) ∧ ContDiff ℝ K (ρ' t) ∧
              ∀ k : ℕ, k ≤ K → ∀ x : Euc d,
                movBracket x ^ L * (‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ +
                    ‖iteratedFDeriv ℝ k (ρ' t) x‖) ≤
                  CKL * εstar * Real.exp (-c * t) := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨c₁, hc₁, h⟩ := mov63_decay_f0 H hj
  obtain ⟨εstar, r, c, C₀, hε, hε4, hr, hc, hC₀, hf⟩ := h m hm
  have hm3 : (d : ℝ) / 2 + 3 < m := s64_hm3 hmK
  have hC2 : (2 : ℝ) ≤ max C₀ 2 := le_max_right _ _
  have hCinv : (max C₀ 2)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hC2
  refine ⟨εstar, r, c₁ / 2, c, max C₀ 2, hε, hr, by positivity, hc, by linarith, ?_, ?_⟩
  · intro f0 hf0
    have hcont := mnh_contDiff3 H hm3 hf0.cb hj hf0.osc
    have hmass := mnh_massZero H hm3 hf0.osc hf0.mean
    obtain ⟨v, hM, hv0, hcls, hrat, hDi, hDe, hI⟩ := hf hm3 f0 hcont hf0.cb hf0.osc hmass hf0.small
    have hRD := mnb_rhoData H
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
  · intro L
    obtain ⟨M, hM0, hMb⟩ := s64_out H hmK L hr.le
    refine ⟨M * max C₀ 2, fun f0 hf0 ρ hρcls => ?_⟩
    have hcont := mnh_contDiff3 H hm3 hf0.cb hj hf0.osc
    have hmass := mnh_massZero H hm3 hf0.osc hf0.mean
    obtain ⟨v, hmild, hv0, hcls, hrat, hDi, hDe, hI⟩ := hf hm3 f0 hcont hf0.cb hf0.osc hmass hf0.small
    have huniq := mov_nl_unique_conjunct hd hs0 hsd hβ hq hρ hj hm hcls ρ (hρcls.mono_rate (by positivity))
    have hDe' : MovDecayBounds d s q β ρ₀ j m c (max C₀ 2) εstar (mneP d ρ₀ hm3 v) :=
      mnh_decay_mono_C hε.le (le_max_left _ _) hDe
    refine ⟨fun τ x => movDiv (mneY d s q β ρ₀ hm3 (v τ)) x, fun t ht x => ?_, fun t ht => ?_⟩
    · have hder := mne_hasDeriv hm3 H hmild ht x
      refine (hder.mono (Set.Ici_subset_Ici.2 ht)).congr (fun τ hτ => ?_) ?_
      · rw [huniq τ (ht.trans hτ), mneP_eq hm3 (ht.trans hτ)]
      · rw [huniq t ht, mneP_eq hm3 ht]
    · have hrt : ρ t = mneRho ρ₀ hm3 (v t) := by rw [huniq t ht, mneP_eq hm3 ht]
      have hnorm : ‖v t‖ ≤ r := by
        have h1 := (hcls.weighted t ht).2
        rw [mne_movV hm3 H t ht, mneV_norm hm3] at h1
        refine h1.trans ?_
        have : Real.exp (-(c₁ / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith
      obtain ⟨o1, o2, o3⟩ := hMb (v t) hnorm
      refine ⟨by rw [hrt]; exact o1, o2, fun k hk x => ?_⟩
      have h3 := o3 k hk x
      have hdec := (hDe' t ht).1.2
      rw [mne_movV hm3 H t ht, mneV_norm hm3] at hdec
      rw [hrt]
      refine h3.trans ?_
      calc M * ‖v t‖ ≤ M * (max C₀ 2 * εstar * Real.exp (-c * t)) := mul_le_mul_of_nonneg_left hdec hM0
        _ = M * max C₀ 2 * εstar * Real.exp (-c * t) := by ring

end HRS.MS.MovSch

end
