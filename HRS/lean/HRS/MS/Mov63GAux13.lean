import HRS.MS.Mov63GAux12

/-!
# S6.3, packet N8 (part 13): Lipschitz decay of `Q_t` for the N5-N7 solution (stage A, instantiation of `mng_lip_decay`)

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mng_lip_conc`**: `|Q_t(x) - Q_t(y)| ≤ C_L K e^{-ct} ‖x-y‖`, `K` bounding `‖D Q_0‖` and `‖v_t‖ ≤ C_v K e^{-c₁ t}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm
  HRS.MS.PoisMax HRS.MS.PoisFlow

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section LipConc2

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

set_option maxHeartbeats 3200000 in
include H hm in
theorem mng_lip_conc {N : ℕ} (hN1 : 1 ≤ N) (hN : (d : ℝ) / 2 + N + 2 < m) (Cv c1 : ℝ) (hCv : 0 ≤ Cv) (hc1 : 0 < c1) :
    ∃ δ0 c CL : ℝ, 0 < δ0 ∧ 0 < c ∧ c ≤ c1 ∧ 0 ≤ CL ∧
      ∀ v : ℝ → OscSpace d (m : ℝ), MneMild H hm v → ∀ K : ℝ, 0 ≤ K → K ≤ 1 → Cv * K ≤ δ0 →
        (∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K * Real.exp (-c1 * t)) →
        (∀ t, 0 ≤ t → ∀ x, 1 / 2 ≤ mneQ ρ hm (v t) x ∧ mneQ ρ hm (v t) x ≤ 2) →
        (∀ x, ‖iteratedFDeriv ℝ 1 (mneQ ρ hm (v 0)) x‖ ≤ K) →
        ∀ t, 0 ≤ t → ∀ x y : Euc d, |mneQ ρ hm (v t) x - mneQ ρ hm (v t) y| ≤
          CL * K * Real.exp (-c * t) * ‖x - y‖ := by
  obtain ⟨C0, hC00, hU⟩ := mng_unif H hm hN
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Mb0, hMb0⟩ := hR.cb 1
  have hBb : ∀ z, ‖B z‖ ≤ Mb0 := fun z => by simpa using hMb0.2 0 (by norm_num) z
  have hMb0nn : 0 ≤ Mb0 := (norm_nonneg _).trans (hBb 0)
  have hBl := pf_lip_of_cb (le_refl 1) hMb0
  have hq' : 0 < β * q := mul_pos H.hβ H.hq
  have hMb' : 0 ≤ Mb0 + 1 := by linarith
  have hκ : 0 < pm_kappa (β * q) (Mb0 + 1) := Real.exp_pos _
  have hc0 : 0 < pm_c0 (β * q) (Mb0 + 1) := by
    unfold pm_c0
    exact mul_pos hκ (lt_min one_pos (by linarith))
  set κ : ℝ := pm_kappa (β * q) (Mb0 + 1) with hκdef
  set c0 : ℝ := pm_c0 (β * q) (Mb0 + 1) with hc0def
  have hν : 0 < β⁻¹ := inv_pos.2 H.hβ
  set c : ℝ := min c1 (β⁻¹ * c0 / 2) with hcdef
  have hcpos : 0 < c := lt_min hc1 (by positivity)
  have hcc1 : c ≤ c1 := min_le_left _ _
  have hcc0 : c ≤ β⁻¹ * c0 / 2 := min_le_right _ _
  set δ0 : ℝ := 1 / (β * C0 + 1) with hδ0
  have hδ0pos : 0 < δ0 := by rw [hδ0]; have := H.hβ; positivity
  set CΦ : ℝ := 4 * C0 * Cv / (κ * β⁻¹ * c0) + 1 / κ with hCΦ
  have hCΦ0 : 0 ≤ CΦ := by rw [hCΦ]; positivity
  refine ⟨δ0, c, Real.exp (C0 * Cv / c1) * CΦ, hδ0pos, hcpos, hcc1, by positivity, ?_⟩
  intro v hmild K hK0 hK1 hCvK hvd hQ hinit t0 ht0 x y
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hβne : β ≠ 0 := H.hβ.ne'
  set aa : ℝ := C0 * Cv * K with haa
  have haa0 : 0 ≤ aa := by positivity
  have hex : ∀ t, 0 ≤ t → ∀ c' : ℝ, 0 ≤ c' → Real.exp (-c' * t) ≤ 1 := fun t ht c' hc' => by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
  have hvb : ∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K := fun t ht => by
    refine (hvd t ht).trans ?_
    have := hex t ht c1 hc1.le
    have h2 : 0 ≤ Cv * K := by positivity
    nlinarith
  have hvK : ∀ t, 0 ≤ t → C0 * ‖v t‖ ≤ 1 / β := fun t ht => by
    have h1 : ‖v t‖ ≤ δ0 := (hvb t ht).trans hCvK
    have : C0 * ‖v t‖ ≤ C0 * δ0 := mul_le_mul_of_nonneg_left h1 hC00
    refine this.trans ?_
    have hb := H.hβ
    rw [hδ0, mul_one_div, div_le_div_iff₀ (by positivity) hb]
    nlinarith
  -- the data of `mng_lip_decay`
  set Qf : ℝ → Euc d → ℝ := fun t => mneQ ρ hm (v t) with hQf
  set Bt : ℝ → Euc d → Euc d := fun t z => B z + β • mneFo d s ρ hm (v t) z with hBt
  set Af : ℝ → Euc d → ℝ := fun t => mnfA d s ρ hm (v t) with hAf
  have hFb : ∀ t, 0 ≤ t → ∀ z, ‖mneFo d s ρ hm (v t) z‖ ≤ C0 * ‖v t‖ := fun t ht z => by
    have := (hU (v t)).2.2.2.1 0 (by omega) z
    rwa [norm_iteratedFDeriv_zero] at this
  have hFl : ∀ t, 0 ≤ t → ∀ x y, ‖mneFo d s ρ hm (v t) x - mneFo d s ρ hm (v t) y‖ ≤ C0 * ‖v t‖ * ‖x - y‖ :=
    fun t ht x y => by
      have hd := ((hU (v t)).2.2.1).differentiable (by simp)
      exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le (f := mneFo d s ρ hm (v t))
        (C := C0 * ‖v t‖) (fun z _ => hd z)
        (fun z _ => by
          have := (hU (v t)).2.2.2.1 1 (by omega) z
          rwa [norm_iteratedFDeriv_one] at this) (mem_univ y) (mem_univ x)
  have hBbd : ∀ t ∈ Icc (0 : ℝ) t0, ∀ z, ‖Bt t z‖ ≤ Mb0 + 1 := fun t ht z => by
    have h1 : ‖Bt t z‖ ≤ ‖B z‖ + β * ‖mneFo d s ρ hm (v t) z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos H.hβ]
    have h2 := hFb t ht.1 z
    have h3 := hvK t ht.1
    have hb := H.hβ
    have h4 : β * ‖mneFo d s ρ hm (v t) z‖ ≤ 1 := by
      calc β * ‖mneFo d s ρ hm (v t) z‖ ≤ β * (C0 * ‖v t‖) := mul_le_mul_of_nonneg_left h2 hb.le
        _ ≤ β * (1 / β) := mul_le_mul_of_nonneg_left h3 hb.le
        _ = 1 := by field_simp
    linarith [hBb z]
  have hBlip : ∀ t ∈ Icc (0 : ℝ) t0, ∀ x y, ‖Bt t x - Bt t y‖ ≤ (Mb0 + 1) * ‖x - y‖ := fun t ht x y => by
    have e : Bt t x - Bt t y = (B x - B y) + β • (mneFo d s ρ hm (v t) x - mneFo d s ρ hm (v t) y) := by
      simp only [hBt, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos H.hβ]
    have h1 := hBl x y
    have h2 := hFl t ht.1 x y
    have h3 := hvK t ht.1
    have hb := H.hβ
    have h4 : β * ‖mneFo d s ρ hm (v t) x - mneFo d s ρ hm (v t) y‖ ≤ 1 * ‖x - y‖ := by
      calc β * ‖mneFo d s ρ hm (v t) x - mneFo d s ρ hm (v t) y‖ ≤ β * (C0 * ‖v t‖ * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left h2 hb.le
        _ = (β * (C0 * ‖v t‖)) * ‖x - y‖ := by ring
        _ ≤ 1 * ‖x - y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc β * (C0 * ‖v t‖) ≤ β * (1 / β) := mul_le_mul_of_nonneg_left h3 hb.le
              _ = 1 := by field_simp
    linarith
  have hAbd : ∀ t, 0 ≤ t → ∀ z, |Af t z| ≤ aa * Real.exp (-c1 * t) := fun t ht z => by
    have := (hU (v t)).2.2.2.2.2 0 (by omega) z
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    calc C0 * ‖v t‖ ≤ C0 * (Cv * K * Real.exp (-c1 * t)) := mul_le_mul_of_nonneg_left (hvd t ht) hC00
      _ = aa * Real.exp (-c1 * t) := by rw [haa]; ring
  have hAlip : ∀ t, 0 ≤ t → ∀ x y, |Af t x - Af t y| ≤ aa * Real.exp (-c1 * t) * ‖x - y‖ := fun t ht x y => by
    refine mng_lip_of_fderiv (((hU (v t)).2.2.2.2.1).differentiable (by exact_mod_cast (by omega : N ≠ 0))) (fun z => ?_) x y
    have := (hU (v t)).2.2.2.2.2 1 hN1 z
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans ?_
    calc C0 * ‖v t‖ ≤ C0 * (Cv * K * Real.exp (-c1 * t)) := mul_le_mul_of_nonneg_left (hvd t ht) hC00
      _ = aa * Real.exp (-c1 * t) := by rw [haa]; ring
  have hL0 : ∀ x y, |Qf 0 x - Qf 0 y| ≤ K * ‖x - y‖ := fun x y => by
    refine mng_lip_of_fderiv (((mng_Q_cd H hm hN (v 0)).differentiable (by simp))) (fun z => ?_) x y
    have := hinit z
    rwa [norm_iteratedFDeriv_one] at this
  set Φ0 : ℝ := K * CΦ with hΦ0
  have hΦ00 : 0 ≤ Φ0 := by positivity
  set Λ : ℝ → ℝ := fun t => aa / c1 * (1 - Real.exp (-c1 * t)) with hΛ
  set Φ : ℝ → ℝ := fun t => Φ0 * Real.exp (-c * t) with hΦ
  set Φ' : ℝ → ℝ := fun t => -c * Φ0 * Real.exp (-c * t) with hΦ'
  have hΛd : ∀ t, HasDerivAt Λ (aa * Real.exp (-c1 * t)) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-c1 * t)) (Real.exp (-c1 * t) * (-c1)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c1)).exp
    have := (h1.const_sub 1).const_mul (aa / c1)
    refine this.congr_deriv ?_
    field_simp
  have hΦd : ∀ t, HasDerivAt Φ (Φ' t) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-c * t)) (Real.exp (-c * t) * (-c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c)).exp
    have := h1.const_mul Φ0
    refine this.congr_deriv ?_
    simp only [hΦ']; ring
  have hΦcond : ∀ t ∈ Icc (0 : ℝ) t0, -(β⁻¹ * c0 * Φ t) + (aa * Real.exp (-c1 * t)) * 2 / κ ≤ Φ' t := by
    intro t ht
    have hE : 0 < Real.exp (-c * t) := Real.exp_pos _
    have hE1 : Real.exp (-c1 * t) ≤ Real.exp (-c * t) :=
      Real.exp_le_exp.2 (by nlinarith [ht.1])
    have hβc0 : 0 < β⁻¹ * c0 := by positivity
    have h1 : 2 * aa / κ ≤ (β⁻¹ * c0 / 2) * Φ0 := by
      have e : (β⁻¹ * c0 / 2) * Φ0 = 2 * aa / κ + (β⁻¹ * c0 / 2) * (K / κ) := by
        rw [hΦ0, hCΦ, haa]; field_simp; ring
      rw [e]
      have : 0 ≤ (β⁻¹ * c0 / 2) * (K / κ) := by positivity
      linarith
    have h2 : (aa * Real.exp (-c1 * t)) * 2 / κ ≤ (β⁻¹ * c0 / 2) * Φ0 * Real.exp (-c * t) := by
      calc (aa * Real.exp (-c1 * t)) * 2 / κ = (2 * aa / κ) * Real.exp (-c1 * t) := by ring
        _ ≤ (2 * aa / κ) * Real.exp (-c * t) := mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 hE.le
    have h3 : c * Φ0 * Real.exp (-c * t) ≤ (β⁻¹ * c0 / 2) * Φ0 * Real.exp (-c * t) := by
      apply mul_le_mul_of_nonneg_right _ hE.le
      exact mul_le_mul_of_nonneg_right hcc0 hΦ00
    simp only [hΦ, hΦ']
    linarith
  have hΦinit : Real.exp (-Λ 0) * K ≤ Φ 0 * κ := by
    have : Λ 0 = 0 := by simp [hΛ]
    rw [this]
    simp only [hΦ, neg_zero, Real.exp_zero, one_mul, mul_zero]
    rw [hΦ0, hCΦ]
    have : K ≤ K * (4 * C0 * Cv / (κ * β⁻¹ * c0) + 1 / κ) * κ := by
      have h1 : 0 ≤ 4 * C0 * Cv / (κ * β⁻¹ * c0) := by positivity
      have e : K * (4 * C0 * Cv / (κ * β⁻¹ * c0) + 1 / κ) * κ =
          K * (4 * C0 * Cv / (κ * β⁻¹ * c0) * κ) + K := by field_simp
      rw [e]
      have : 0 ≤ K * (4 * C0 * Cv / (κ * β⁻¹ * c0) * κ) := by positivity
      linarith
    simpa using this
  have key := mng_lip_decay hd1 hq' hMb' hν (T := t0) (Q := Qf) (Bt := Bt) (A := Af) (Φ := Φ) (Φ' := Φ')
    (Λ := Λ) (α := fun t => aa * Real.exp (-c1 * t)) (α₁ := fun t => aa * Real.exp (-c1 * t)) (MQ := 2) (L0 := K)
    (fun t ht => (mng_Q_cd H hm hN (v t)).of_le (by exact_mod_cast (by omega : 2 ≤ N + 2)))
    ((mnf_Q_joint hm H hmild).mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl))
    (fun t ht x => by
      have h1 := (mne_Q_hasDeriv hm H hmild ht.1 x).mono (Set.Icc_subset_Ici_self : Icc (0:ℝ) t0 ⊆ Ici 0)
      refine h1.congr_deriv ?_
      exact mng_Qeq_form hm hR H.hβ (v t) x)
    hBbd hBlip
    (fun t ht x => abs_le.2 ⟨by linarith [(hQ t ht.1 x).1], (hQ t ht.1 x).2⟩)
    (fun t ht x => hAbd t ht.1 x) (fun t ht x y => hAlip t ht.1 x y) (fun t ht => by positivity)
    hL0 hΛd (fun t ht => by
      simp only [hΛ]
      have := hex t ht.1 c1 hc1.le
      have hh : 0 ≤ aa / c1 := by positivity
      apply mul_nonneg hh; linarith)
    hΦd (fun t ht => by positivity) hΦcond hΦinit (t := t0) ⟨ht0, le_rfl⟩ x y
  refine key.trans ?_
  have hΛle : Real.exp (Λ t0) ≤ Real.exp (C0 * Cv / c1) := by
    refine Real.exp_le_exp.2 ?_
    simp only [hΛ]
    have h1 : 0 ≤ Real.exp (-c1 * t0) := (Real.exp_pos _).le
    have h2 : aa / c1 ≤ C0 * Cv / c1 := by
      rw [haa]
      apply div_le_div_of_nonneg_right _ hc1.le
      have : 0 ≤ C0 * Cv := by positivity
      nlinarith
    have h3 : 0 ≤ aa / c1 := by positivity
    nlinarith
  have hnorm := norm_nonneg (x - y)
  calc Real.exp (Λ t0) * Φ t0 * ‖x - y‖ ≤ Real.exp (C0 * Cv / c1) * Φ t0 * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ hnorm
        exact mul_le_mul_of_nonneg_right hΛle (by positivity)
    _ = Real.exp (C0 * Cv / c1) * CΦ * K * Real.exp (-c * t0) * ‖x - y‖ := by
        simp only [hΦ, hΦ0]; ring

end LipConc2

end HRS.MS.Mov63

end
