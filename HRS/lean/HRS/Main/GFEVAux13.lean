import HRS.Main.GFEVAux12

/-!
# Packet GFEVG, part 13: `t ↦ A_t` is continuous in operator norm
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem GFPde.mean_mu (h : GFPde d s γ R VB Λ D T ρ) (t : ℝ) : Torus.mean (gfevMu T ρ t) = 1 :=
  (h.hρ _ (gfevClamp_mem h.hT.le t)).1.integral_one

theorem GFPde.weak_mu (h : GFPde d s γ R VB Λ D T ρ) (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    Continuous fun t => ∫ x, ψ x * gfevMu T ρ t x := by
  have hc : ContinuousOn ((fun r => ∫ x, ψ x * ρ r x) ∘ gfevClamp T) Set.univ :=
    ContinuousOn.comp (g := fun r => ∫ x, ψ x * ρ r x) (s := Set.univ) (h.hweak ψ hψ)
      (continuous_gfevClamp T).continuousOn (fun r _ => gfevClamp_mem h.hT.le r)
  exact continuousOn_univ.1 hc

theorem GFPde.cb_mu (h : GFPde d s γ R VB Λ D T ρ) (t₀ : ℝ) :
    Tendsto (fun t => Torus.cbNorm γ (fun x => gfevMu T ρ t x - gfevMu T ρ t₀ x)) (𝓝 t₀) (𝓝 0) :=
  gfev_cb_tendsto (f := gfevMu T ρ) (n := γ + 2 * d + 12) (j := γ) (Λ := Λ) (c₀ := 1) h.hd
    (by omega) (fun t => (h.hρ _ (gfevClamp_mem h.hT.le t)).2.1)
    (fun t => (h.hρ _ (gfevClamp_mem h.hT.le t)).2.2) h.mean_mu h.weak_mu t₀

theorem GFPde.generatorOp_cont (h : GFPde d s γ R VB Λ D T ρ)
    (A2 : ℝ → NegSobolev d ((γ : ℝ) - 2) →L[ℝ] NegSobolev d (γ : ℝ)) {M : ℝ}
    (hdual : ∀ t (z : NegSobolev d ((γ : ℝ) - 2)) (φ : Torus d → ℝ), Dom (γ + 2) φ →
        NegSobolev.eval (A2 t z) φ = NegSobolev.eval z (gfevL D (gfevMu T ρ t) φ))
    (hM : ∀ t, GfDualHyp (Dom (γ + 2)) (γ : ℝ) ((γ : ℝ) - 2) (gfevL D (gfevMu T ρ t)) M) :
    Continuous A2 := by
  have hγ2 : 2 ≤ γ := by have := h.hγ5; omega
  have hcast : (((γ - 2 : ℕ) : ℝ)) = (γ : ℝ) - 2 := by rw [Nat.cast_sub hγ2]; norm_num
  obtain ⟨Kd, hKd0, hKd⟩ := StabAux.forwardGen_diff_bound h.hd s h.hs0 h.hsd (γ - 2) 1 Λ
  have hm2 : γ - 2 + 2 = γ := by omega
  have hle : γ - 2 + 3 ≤ γ + 2 * d + 12 := by omega
  have hVH : VHyp (γ - 2) VB D.V := ⟨ET.isCk_mono' hle h.hV.1, (ET.cbNorm_mono' hle _).trans h.hV.2⟩
  have hdata := fun t : ℝ => coeff_memHs_zero_of_data (m := γ - 2) (VB := VB) D (gfevMu T ρ t)
    (ET.isCk_mono' hle (h.hρ _ (gfevClamp_mem h.hT.le t)).2.1) hVH
  -- the key estimate
  have hkey : ∀ t t₀ : ℝ, ‖A2 t - A2 t₀‖ ≤ Kd * Torus.cbNorm γ (fun x => gfevMu T ρ t x - gfevMu T ρ t₀ x) := by
    intro t t₀
    set δ := Torus.cbNorm γ (fun x => gfevMu T ρ t x - gfevMu T ρ t₀ x) with hδ
    have hδ0 : 0 ≤ δ := R2Aux.cbNorm_nonneg' γ _
    refine gfev_dual_diff (hM t) (hM t₀) (mul_nonneg hKd0 hδ0) ?_ (A2 t) (A2 t₀) (hdual t) (hdual t₀)
    intro φ hφ
    obtain ⟨Bμ, BV, hBμ, hBV, hG⟩ := h.genHyp
    have hK : (d : ℝ) + |(γ : ℝ) - 2| + 4 ≤ ((γ + 2 * d + 11 : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ γ := by exact_mod_cast hγ2
      rw [abs_of_nonneg (by linarith)]; push_cast; linarith
    obtain ⟨C, hC, hfacts⟩ := h.gen_facts (K := ((γ + 2 * d + 11 : ℕ) : ℝ)) (MB := 1) (Bμ := Bμ) (BV := BV)
      zero_le_one hBμ hBV hK
    obtain ⟨hc1, hn1⟩ := (hfacts _ (h.contMu t) (hG t) φ hφ).1, (hfacts _ (h.contMu t) (hG t) φ hφ).2
    have hfa := hfacts _ (h.contMu t) (hG t) φ hφ
    have hfb := hfacts _ (h.contMu t₀) (hG t₀) φ hφ
    have hγ1 : (1 : ℝ) ≤ γ := by have : (2 : ℝ) ≤ γ := by exact_mod_cast hγ2
                                 linarith
    have hψγ : MemSobolev (γ : ℝ) φ := memSobolev_of_dom (by push_cast; linarith) hφ
    obtain ⟨hcφ1, hcφ2⟩ := hsNormSq_coeffOf (γ : ℝ) φ hψγ
    have hcφ : MemHs (((γ - 2 : ℕ) : ℝ) + 2) (coeffOf φ) := by
      rw [hcast]; have e : (γ : ℝ) - 2 + 2 = γ := by ring
      rw [e]; exact hcφ1
    have hρ₁ := (h.hρ _ (gfevClamp_mem h.hT.le t))
    have hρ₂ := (h.hρ _ (gfevClamp_mem h.hT.le t₀))
    have hkd := hKd D D h.hDs h.hDs rfl h.matBound rfl (gfevMu T ρ t) (gfevMu T ρ t₀) hρ₁.1 hρ₂.1
      (ET.isCk_mono' hle hρ₁.2.1) (ET.isCk_mono' hle hρ₂.2.1)
      ((ET.cbNorm_mono' hle _).trans hρ₁.2.2) ((ET.cbNorm_mono' hle _).trans hρ₂.2.2)
      (hdata t).1 (hdata t₀).1 (hdata t).2 (hdata t₀).2 δ (by rw [hδ, ← hm2]; exact le_rfl) (coeffOf φ) hcφ
    obtain ⟨hmem, hnorm⟩ := hkd
    simp only [sub_self, abs_zero, zero_add] at hnorm
    have hdc : Continuous fun x => gfevL D (gfevMu T ρ t) φ x - gfevL D (gfevMu T ρ t₀) φ x :=
      hfa.2.1.sub hfb.2.1
    have hcoef : coeffOf (fun x => gfevL D (gfevMu T ρ t) φ x - gfevL D (gfevMu T ρ t₀) φ x) =
        forwardGen D (gfevMu T ρ t) (coeffOf φ) - forwardGen D (gfevMu T ρ t₀) (coeffOf φ) := by
      have e : (fun x => gfevL D (gfevMu T ρ t) φ x - gfevL D (gfevMu T ρ t₀) φ x) =
          fun x => 1 * gfevL D (gfevMu T ρ t) φ x + (-1) * gfevL D (gfevMu T ρ t₀) φ x := by
        funext x; ring
      rw [e, Q54.coeffOf_lin hfa.2.1 hfb.2.1 1 (-1), hfa.1, hfb.1]
      funext k; simp [sub_eq_add_neg]
    rw [hcast] at hmem hnorm
    have hmemS : MemSobolev ((γ : ℝ) - 2) (fun x => gfevL D (gfevMu T ρ t) φ x - gfevL D (gfevMu T ρ t₀) φ x) :=
      memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous hdc) (by rw [hcoef]; exact hmem)
    refine ⟨hmemS, ?_⟩
    have e1 := (hsNormSq_coeffOf ((γ : ℝ) - 2) _ hmemS).2
    rw [hcoef] at e1
    have e2 : ((γ : ℝ) - 2) + 2 = γ := by ring
    rw [e2, hcφ2] at hnorm
    have hs0 : 0 ≤ Kd * δ * sobolevNorm (γ : ℝ) φ := mul_nonneg (mul_nonneg hKd0 hδ0) (Real.sqrt_nonneg _)
    refine le_of_sq_le_sq ?_ hs0
    rw [← e1]
    calc hsNormSq ((γ : ℝ) - 2) (forwardGen D (gfevMu T ρ t) (coeffOf φ) - forwardGen D (gfevMu T ρ t₀) (coeffOf φ))
        ≤ (Kd * δ) ^ 2 * sobolevNorm (γ : ℝ) φ ^ 2 := hnorm
      _ = _ := by ring
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hz := (h.cb_mu t₀).const_mul Kd
  rw [mul_zero] at hz
  exact squeeze_zero (fun t => norm_nonneg _) (fun t => hkey t t₀) hz

end HRS.GF
