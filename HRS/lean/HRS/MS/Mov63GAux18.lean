import HRS.MS.Mov63GAux17

/-!
# S6.3, packet N8 (part 18): the decay clauses of `MovDecayBounds` (output for N9)

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mov63_decay_bounds`**: for the thermal data `H`, `j ≥ 1`, `m > d/2 + j + 6` and the constants `(C_v, c₁)` of the
N5/N7 solution there are `δ₁, c, C > 0` such that every mild solution `v` with `‖v_t‖ ≤ C_v K e^{-c₁ t}`, `0 ≤ K ≤ δ₁`, `ρ/2 ≤ ρ_t ≤ 2ρ` and initial datum
`Q_0 = 1 + f₀` with `‖f₀‖_{C_b^{j+1}} ≤ K` satisfies `MovDecayBounds d s q β ρ j m c C K (mneP d ρ hm v)` and `∫_0^∞ ‖u_t‖_{C_b^j} dt < ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Output

variable {m : ℕ} (H : Mov2dTh d s β q ρ)

lemma mng_init_of_f0 {j : ℕ} {f0 : Euc d → ℝ} {K : ℝ} (hcb : MemCb (j + 1) f0) (hK : cbNorm (j + 1) f0 ≤ K)
    {Q0 : Euc d → ℝ} (hQ0 : ∀ y, Q0 y = 1 + f0 y) :
    ∀ i, 1 ≤ i → i ≤ j + 1 → ∀ y, ‖iteratedFDeriv ℝ i Q0 y‖ ≤ K := by
  intro i hi1 hij y
  have e : Q0 = (fun _ : Euc d => (1 : ℝ)) + f0 := by funext z; simp [hQ0 z]
  rw [e, iteratedFDeriv_add_apply contDiffAt_const ((hcb.1.of_le (by exact_mod_cast hij)).contDiffAt),
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  exact (mnf_norm_le_cbNorm hcb hij y).trans hK

set_option maxHeartbeats 3200000 in
include H in
theorem mov63_decay_bounds {j : ℕ} (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m) (Cv c1 : ℝ) (hCv : 0 ≤ Cv) (hc1 : 0 < c1) :
    ∃ δ1 c C : ℝ, 0 < δ1 ∧ 0 < c ∧ c ≤ c1 ∧ 0 ≤ C ∧ ∀ (hm3 : (d : ℝ) / 2 + 3 < m) (v : ℝ → OscSpace d (m : ℝ)),
      MneMild H hm3 v → ∀ (K : ℝ) (f0 : Euc d → ℝ), 0 ≤ K → K ≤ δ1 →
        (∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K * Real.exp (-c1 * t)) →
        (∀ t, 0 ≤ t → ∀ y, ρ y / 2 ≤ mneP d ρ hm3 v t y ∧ mneP d ρ hm3 v t y ≤ 2 * ρ y) →
        (∀ y, mneQ ρ hm3 (v 0) y = 1 + f0 y) → MemCb (j + 1) f0 → cbNorm (j + 1) f0 ≤ K →
        MovDecayBounds d s q β ρ j m c C K (mneP d ρ hm3 v) ∧
          ∫⁻ t in Ioi (0 : ℝ), cbNormVecE j (movU d s q β (mneP d ρ hm3 v t)) < ⊤ := by
  have hm3 : (d : ℝ) / 2 + 3 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hN : (d : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) + 2 < m := by push_cast; linarith
  have hN1 : 1 ≤ j + 1 := by omega
  obtain ⟨δ0, c, Cc, hδ0, hc, hcc1, hCc0, hcore⟩ := mng_core H hm3 hN1 hN Cv c1 hCv hc1
  obtain ⟨C0, hC00, hU⟩ := mng_unif H hm3 hN
  set LB : ℝ := (((j + 1).factorial : ℝ) * (1 + ((j + 1).factorial : ℝ) * 2 ^ (j + 1))) with hLB
  have hβ := H.hβ
  set Cd : ℝ := ((j : ℝ) + 1) * (LB * Cc) + ((j : ℝ) + 1) * (β⁻¹ * (LB * Cc) + C0 * Cv) with hCd
  have hCd0 : 0 ≤ Cd := by rw [hCd, hLB]; positivity
  set δ1 : ℝ := min (min 1 (δ0 / (Cv + 1))) (1 / (Cc + 1)) with hδ1
  have hδ1pos : 0 < δ1 := by rw [hδ1]; positivity
  refine ⟨δ1, c, max Cv Cd, hδ1pos, hc, hcc1, le_trans hCv (le_max_left _ _), ?_⟩
  intro hm3' v hmild K f0 hK0 hKδ hvd hratio hQ0 hcb hcbK
  have hK1 : K ≤ 1 := hKδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hCvK : Cv * K ≤ δ0 := by
    have h1 : K ≤ δ0 / (Cv + 1) := hKδ.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hCcK : Cc * K ≤ 1 := by
    have h1 : K ≤ 1 / (Cc + 1) := hKδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- positivity / ratio of Q
  have hQ : ∀ t, 0 ≤ t → ∀ x, 1 / 2 ≤ mneQ ρ hm3 (v t) x ∧ mneQ ρ hm3 (v t) x ≤ 2 := by
    intro t ht x
    have hρx := (mnb_rhoData H).pos x
    have h := hratio t ht x
    rw [mneP_eq hm3 ht] at h
    show 1 / 2 ≤ mneRho ρ hm3 (v t) x / ρ x ∧ mneRho ρ hm3 (v t) x / ρ x ≤ 2
    rw [le_div_iff₀ hρx, div_le_iff₀ hρx]
    constructor <;> nlinarith [h.1, h.2]
  have hinit := mng_init_of_f0 hcb hcbK (Q0 := mneQ ρ hm3 (v 0)) hQ0
  have hcr := hcore v hmild K hK0 hK1 hCvK hvd hQ hinit
  have hcd : ∀ t, ContDiff ℝ ((j + 1 + 2 : ℕ) : WithTop ℕ∞) (mneQ ρ hm3 (v t)) := fun t => mng_Q_cd H hm3 hN (v t)
  -- the pointwise bound for the velocity part and the sum
  have hpt : ∀ t, 0 ≤ t →
      ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (fun y => Real.log (mneP d ρ hm3 v t y / ρ y)) x) ∧
      ContDiff ℝ (j : WithTop ℕ∞) (movU d s q β (mneP d ρ hm3 v t)) ∧
      cbNormVecE j (fun x => gradient (fun y => Real.log (mneP d ρ hm3 v t y / ρ y)) x) +
          cbNormVecE j (movU d s q β (mneP d ρ hm3 v t)) ≤ ENNReal.ofReal (Cd * K * Real.exp (-c * t)) := by
    intro t ht
    rw [mneP_eq hm3 ht]
    have hex : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
    have hε1 : Cc * K * Real.exp (-c * t) ≤ 1 := by
      have : Real.exp (-c * t) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
      have h2 : 0 ≤ Cc * K := by positivity
      nlinarith
    have hFD : ∀ k ≤ j, ∀ y, ‖iteratedFDeriv ℝ k (mneFo d s ρ hm3 (v t)) y‖ ≤ C0 * Cv * K * Real.exp (-c * t) := by
      intro k hk y
      have h1 := (hU (v t)).2.2.2.1 k (by omega) y
      have h2 : ‖v t‖ ≤ Cv * K * Real.exp (-c * t) := by
        refine (hvd t ht).trans ?_
        have : Real.exp (-c1 * t) ≤ Real.exp (-c * t) := Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_left this (by positivity)
      calc _ ≤ C0 * ‖v t‖ := h1
        _ ≤ C0 * (Cv * K * Real.exp (-c * t)) := mul_le_mul_of_nonneg_left h2 hC00
        _ = _ := by ring
    obtain ⟨h1, h2, h3⟩ := mng_decay_at H hm3 (u := v t) (j := j) hj (hQ t ht)
      ((hcd t).of_le (by exact_mod_cast (by omega : j + 1 ≤ j + 1 + 2))) (ε := Cc * K * Real.exp (-c * t))
      (Bf := C0 * Cv * K * Real.exp (-c * t)) (by positivity) hε1 (by positivity)
      (fun i hi1 hi2 y => hcr t ht i hi1 hi2 y)
      (((hU (v t)).2.2.1).of_le (by exact_mod_cast (by omega : j ≤ j + 1 + 1))) hFD
    refine ⟨h1, h2, h3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [hCd, ← hLB]
    nlinarith [mul_nonneg hex hK0, mul_nonneg (mul_nonneg hex hK0) hC00]
  have hmax : ∀ t, 0 ≤ t → ENNReal.ofReal (Cd * K * Real.exp (-c * t)) ≤
      ENNReal.ofReal (max Cv Cd * K * Real.exp (-c * t)) := fun t ht =>
    ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ K * Real.exp (-c * t) := by positivity
      nlinarith [le_max_right Cv Cd])
  refine ⟨fun t ht => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [mne_movV hm3 H t ht]; exact mneV_memOsc hm3 (v t)
  · rw [mne_movV hm3 H t ht, mneV_norm hm3 (v t)]
    refine (hvd t ht).trans ?_
    have : Real.exp (-c1 * t) ≤ Real.exp (-c * t) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : 0 ≤ K := hK0
    calc Cv * K * Real.exp (-c1 * t) ≤ Cv * K * Real.exp (-c * t) := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ max Cv Cd * K * Real.exp (-c * t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h2) (Real.exp_pos _).le
  · obtain ⟨h1, h2, h3⟩ := hpt t ht
    exact ⟨h1, h2, h3.trans (hmax t ht)⟩
  · -- integrability
    have hint : IntegrableOn (fun t : ℝ => max Cv Cd * K * Real.exp (-c * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc).const_mul (max Cv Cd * K)
    calc ∫⁻ t in Ioi (0 : ℝ), cbNormVecE j (movU d s q β (mneP d ρ hm3 v t)) ≤
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (max Cv Cd * K * Real.exp (-c * t)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have := (hpt t (le_of_lt ht)).2.2
          exact (le_trans le_add_self this).trans (hmax t (le_of_lt ht))
      _ < ⊤ := (hint : Integrable _ (volume.restrict (Ioi (0 : ℝ)))).lintegral_lt_top

end Output

end HRS.MS.Mov63

end
