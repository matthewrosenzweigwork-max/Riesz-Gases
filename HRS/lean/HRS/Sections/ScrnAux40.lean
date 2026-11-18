import HRS.Sections.ScrnAux39

/-!
# Packet SCRN, part 40: the remainder bound for the transported mesoscopic tests

`scrn_rem_final`: `Integrable R` and `E‖R‖ ≤ p · (C_q C/(2 c₁)) · √N o_N ℓ^{-d/2-2-e}`, `e = max(q-2,0)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma scrn_max_q (q : ℝ) : max (q - 2) 0 + 2 = max q 2 := by
  rcases le_total q 2 with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

lemma scrn_min_q (q : ℝ) : q - max (q - 2) 0 = min q 2 := by
  rcases le_total q 2 with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

theorem scrn_rem_final (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {C₀ Cq : ℝ} (hC₀ : 0 ≤ C₀) (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq) {bp ℓ CG : ℝ} (hbp : 0 < bp)
    (hℓ : 0 < ℓ) (hCG : 0 ≤ CG) {p : ℕ} {ts : Fin p → ℝ} {ψ : Fin p → Torus d → ℝ}
    {f : Fin p → ℝ → Torus d → ℝ}
    (htr : ScrnTr d hs0 hsd hβ ℓ (scrnLamS d s bp ℓ) CG ts ψ f) :
    Integrable (scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X) P ∧
      ∫ ω, ‖scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X ω‖ ∂P ≤
        p * (Cq * CG / (2 * min (rieszConst d s) bp⁻¹)) *
          (Real.sqrt N * oN d s C₀ N *
            ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0)) := by
  obtain ⟨ℱ, W', hF⟩ := hfl.filt
  set lamS := scrnLamS d s bp ℓ with hlamS
  have hlam := scrnLamS_pos hd hs0 hsd hbp hℓ
  have hc1 : 0 < min (rieszConst d s) bp⁻¹ :=
    lt_min (rieszConst_pos hd hs0 hsd) (inv_pos.2 hbp)
  set ex : ℝ := -((d : ℝ) / 2) - 2 with hex
  set Kf : Fin p → ℝ → ℝ := fun a r => scrnTheta lamS (ts a) r * CG * ℓ ^ ex with hKf
  have hKc : ∀ a, Continuous (Kf a) := fun a => by
    have := scrnTheta_cont lamS (ts a)
    simp only [hKf]; fun_prop
  have hpex : 0 ≤ ℓ ^ ex := Real.rpow_nonneg hℓ.le _
  obtain ⟨hint, hbd⟩ := scrn_rem_bound hd hs0 hsd β hβ hN hfl hF hcom hCq (ts := ts) htr.ts0 ψ
    htr.ck2 f htr.cases htr.c12 htr.fcont Kf (fun a => (hKc a).measurable)
    (fun a => (hKc a).integrableOn_Icc)
    (fun a r _ => by
      have := scrnTheta_pos lamS (ts a) r
      simp only [hKf]; positivity)
    (fun a r hr => by
      rw [scrn_gfb2_v_mf hs0 hsd hβ]
      exact (htr.gb a r hr).tb)
  refine ⟨hint, hbd.trans ?_⟩
  have hbound : ∀ a, ∫ r in Set.Icc 0 (ts a), Kf a r ≤
      (min (rieszConst d s) bp⁻¹)⁻¹ * CG * ℓ ^ (ex - max ((d : ℝ) - s - 2) 0) := by
    intro a
    have h1 := scrn_K_int hlam (htr.ts0 a) (mul_nonneg hCG hpex)
    have e : ∀ r, Kf a r = scrnTheta lamS (ts a) r * (CG * ℓ ^ ex) := fun r => by
      simp only [hKf]; ring
    simp_rw [e]
    refine h1.trans (le_of_eq ?_)
    have h2 := scrnLamS_inv hd hs0 hsd hbp hℓ ex
    rw [← hlamS] at h2
    calc CG * ℓ ^ ex / lamS = CG * (ℓ ^ ex / lamS) := by ring
      _ = _ := by rw [h2]; ring
  have hoN : 0 ≤ oN d s C₀ N := scrn_oN_nonneg hC₀ (by omega)
  calc ∑ a, Real.sqrt N * ((1 / 2) * Cq * (∫ r in Set.Icc 0 (ts a), Kf a r) * oN d s C₀ N)
      ≤ ∑ _a : Fin p, Real.sqrt N * ((1 / 2) * Cq * ((min (rieszConst d s) bp⁻¹)⁻¹ * CG *
          ℓ ^ (ex - max ((d : ℝ) - s - 2) 0)) * oN d s C₀ N) := by
        refine Finset.sum_le_sum fun a _ => ?_
        gcongr
        exact hbound a
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [hex]
        field_simp

end HRS
