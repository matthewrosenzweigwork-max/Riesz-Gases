import HRS.MS.S113EndAux4
import HRS.MS.S113PowerFatou
import HRS.MS.S113PowerAux1

/-!
# S11.3 endpoint (worker S113X), part 5: removal of the localization at a fixed time

From the localized bound `M_n(t) ≤ K` and the `L¹` convergence `r_n(t) → h^t` we get, along an a.e. convergent subsequence and by Fatou
(`s113_power_fatou`), the bound `∫(h^t)^{p(t)}dQ^t ≤ K`; and the assembly of the localized chain bound with the cores X1, X2 for one
particle setup and one exponent `p₀`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

section Limit

variable {α : Type*} [MeasurableSpace α]

theorem s113x_limit_bound (Q : Measure α) (rr : ℕ → α → ℝ) (h : α → ℝ)
    (hrm : ∀ n, Measurable (rr n)) (hr0 : ∀ n x, 0 ≤ rr n x) (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (p K : ℝ) (hp : 1 < p)
    (hL1 : Tendsto (fun n => ∫⁻ x, ‖rr n x - h x‖ₑ ∂Q) atTop (𝓝 0))
    (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (rr n x ^ p) ∂Q ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (h x ^ p) ∂Q ≤ ENNReal.ofReal K := by
  have hmeas : TendstoInMeasure Q rr atTop h := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    have : ∀ n, eLpNorm (rr n - h) 1 Q = ∫⁻ x, ‖rr n x - h x‖ₑ ∂Q := fun n => by
      rw [eLpNorm_one_eq_lintegral_enorm ((hrm n).sub hh).aestronglyMeasurable]; rfl
    simpa only [this] using hL1
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact s113_power_fatou Q (fun n => rr (ns n)) h (fun n => hrm _) hh (fun n => hr0 _) hh0 p K hp hae
    (fun n => hbound _)

theorem s113x_lintegral_eq_mass (Q : Measure α) [IsProbabilityMeasure Q] (r : α → ℝ) (hr : Measurable r)
    (hr0 : ∀ x, 0 ≤ r x) (p B : ℝ) (hp : 1 < p) (hB : ∀ x, r x ≤ B) :
    ∫⁻ x, ENNReal.ofReal (r x ^ p) ∂Q = ENNReal.ofReal (s113_powerMass Q r p) := by
  obtain ⟨hi, -, -⟩ := s113_power_integrable Q r hr hr0 p B hp hB
  unfold s113_powerMass
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hr0 x) p)]

end Limit

theorem s113x_mass_nonneg {α : Type*} [MeasurableSpace α] (Q : Measure α) (r : α → ℝ) (p : ℝ)
    (hr0 : ∀ x, 0 ≤ r x) : 0 ≤ s113_powerMass Q r p :=
  integral_nonneg fun x => Real.rpow_nonneg (hr0 x) p

section Bound

variable {d : ℕ}

/-- The power bound for one particle setup, from the cores X1 (specialized to the trajectory) and X2. -/
theorem s113x_power_bound {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ : ℝ}
    (hX2 : S113XLocalized d s q β ρ₀ j m εstar r c₀) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {cL C₀ : ℝ} (hcL : 0 < cL) (hC₀ : 0 ≤ C₀)
    (hLi : Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hsrc : ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        Measurable (s113x_source d s q β N ρ t) ∧
        (r2MovL d s q β ρ t = 0 → ∀ X, s113x_source d s q β N ρ t X = 0) ∧
        (0 < r2MovL d s q β ρ t →
          ∫⁻ X, ENNReal.ofReal (Real.exp ((cL / r2MovL d s q β ρ t) * |s113x_source d s q β N ρ t X|))
              ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal (Real.exp C₀)))
    {N : ℕ} (hN : 2 ≤ N) (hQ : ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (s113x_Q d s β ρ N t))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hsetup : MovParticleSetup P d s q β N X₀ W X)
    (hac0 : P.map X₀ ≪ s113x_Q d s β ρ N 0) {p₀ : ℝ} (hp₀ : 1 < p₀) {K₀ : ℝ}
    (hM0 : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K₀) (t : ℝ) (ht : 0 ≤ t) :
    P.map (X t.toNNReal) ≪ s113x_Q d s β ρ N t ∧
      r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
        (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤
        ENNReal.ofReal (max (max K₀ 0 + 1) (Real.exp C₀)) := by
  have hfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ < ⊤ :=
    lt_of_le_of_lt hM0 ENNReal.ofReal_lt_top
  obtain ⟨rr, hrm, hr0, hrB, hconv, hinit, hode⟩ :=
    hX2 f0 hf0 ρ hρ N hN P X₀ W X hsetup hac0 p₀ hp₀ hfin
  obtain ⟨hacT, hL1⟩ := hconv t ht
  refine ⟨hacT, ?_⟩
  set L : ℝ → ℝ := r2MovL d s q β ρ with hL
  have hL0 : ∀ u, 0 ≤ u → 0 ≤ L u := fun u _ => ENNReal.toReal_nonneg
  set p : ℝ → ℝ := r2MovExponent cL p₀ L with hp
  have hpb : ∀ u, 0 ≤ u → 1 < p u := fun u hu => (s113x_exponent_bounds hcL hp₀ hL0 hu).1
  have hpac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval p 0 T := fun T hT =>
    s113x_exponent_ac hcL hp₀ hL0 hLi hT
  set K : ℝ := max (max K₀ 0 + 1) (Real.exp C₀) with hK
  -- the bound for every localization
  have hbound : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (rr n t x ^ p t) ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal K := by
    intro n
    obtain ⟨hmass, hmain⟩ := hode p hpac hpb n
    have := hQ t ht
    obtain ⟨B, hBt⟩ := hrB n t
    rw [s113x_lintegral_eq_mass (s113x_Q d s β ρ N t) (rr n t) (hrm n t) (hr0 n t) (p t) B (hpb t ht) (hBt t ⟨ht, le_rfl⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hch := s113x_chain_bound (fun u => s113x_Q d s β ρ N u) hQ (fun u => rr n u)
      (fun u => s113x_source d s q β N ρ u) L cL C₀ p₀ hcL hC₀ hp₀ hL0 hLi (hrm n) (hr0 n) (hrB n)
      (fun u hu => (hsrc N hN u hu).1) (fun u hu => (hsrc N hN u hu).2.1)
      (fun u hu => (hsrc N hN u hu).2.2) hmass (fun T hT => (hmain T hT).1) (fun T hT => (hmain T hT).2)
      ht
    refine hch.trans (max_le_max ?_ le_rfl)
    -- initial mass
    have := hQ 0 le_rfl
    obtain ⟨B0, hB0⟩ := hrB n 0
    have h0 := hinit n
    have hl := s113x_lintegral_eq_mass (s113x_Q d s β ρ N 0) (rr n 0) (hrm n 0) (hr0 n 0) p₀ B0 hp₀ (hB0 0 ⟨le_rfl, le_rfl⟩)
    rw [hl] at h0
    have hMfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ + ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.ofReal_ne_top⟩
    have h1 := ENNReal.toReal_mono hMfin h0
    rw [ENNReal.toReal_ofReal (s113x_mass_nonneg _ _ _ (hr0 n 0))] at h1
    rw [ENNReal.toReal_add hfin.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 : (r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀).toReal ≤ max K₀ 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM0
      rwa [ENNReal.toReal_ofReal'] at this
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  -- Fatou along an a.e. subsequence
  have := hQ t ht
  have hhm : Measurable (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hh0 : ∀ x, 0 ≤ r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x := fun x => ENNReal.toReal_nonneg
  have := s113x_limit_bound (s113x_Q d s β ρ N t) (fun n => rr n t)
    (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) (fun n => hrm n t) (fun n => hr0 n t) hhm hh0
    (p t) K (hpb t ht) hL1 hbound
  exact this

end Bound

end HRS.MS.S113BD
