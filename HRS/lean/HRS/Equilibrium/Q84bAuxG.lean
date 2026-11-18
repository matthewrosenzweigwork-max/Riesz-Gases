/-
# HRS.Equilibrium.Q84bAuxG — packet Q84b: absolute integrability on the product (Tonelli/Fubini)
-/
import HRS.Equilibrium.Q84bAuxF

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_ae_ne (hd : 0 < d) (b : Torus d) : ∀ᵐ x : Torus d, x ≠ b := by
  have := (measure_eq_zero_iff_ae_notMem (μ := (volume : Measure (Torus d))) (s := {b})).1
    (volume_singleton_torus hd b)
  filter_upwards [this] with x hx using hx

theorem q84b_wEnv_symm0 (x : Torus d) : wEnv s x 0 = wEnv s 0 x := PairCorrAux.wEnv_symm s x 0

/-- `ω(u) = w(u, 0)` is integrable. -/
theorem q84b_omega_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    Integrable (fun u : Torus d => wEnv s u 0) := by
  have := q84b_w_integrable hd hcrit (0 : Torus d)
  simpa [q84b_wEnv_symm0] using this

theorem q84b_measurable_omega : Measurable (fun u : Torus d => wEnv s u 0) := by
  have := PairCorrAux.measurable_wEnv s (0 : Torus d)
  simpa [q84b_wEnv_symm0] using this

theorem q84b_measurable_w_left (b : Torus d) : Measurable (fun x : Torus d => wEnv s x b) := by
  have := PairCorrAux.measurable_wEnv s b
  simpa [PairCorrAux.wEnv_symm s _ b] using this

/-- The integrand of the double integral on the `ρ`-side. -/
def q84b_Psi (ρ : Torus d → ℝ) (s : ℝ) (ψ : Torus d → Torus d → ℝ) (b : Torus d)
    (p : Torus d × Torus d) : ℝ :=
  ρ p.1 * (ρ (p.1 - p.2) * inner ℝ (periodicRieszGrad d s p.2)
    (gradFst ψ (p.1 - p.2) b - gradFst ψ p.1 b))

theorem q84b_measurable_Psi (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρc : Continuous ρ) (ψ : Torus d → Torus d → ℝ) (b : Torus d) :
    Measurable (q84b_Psi ρ s ψ b) := by
  have hG : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    HRS.KernelGrad.measurable_periodicRieszGrad hsd
  have hD := q84b_measurable_gradFst ψ b
  unfold q84b_Psi
  refine (hρc.measurable.comp measurable_fst).mul ((hρc.measurable.comp (measurable_fst.sub measurable_snd)).mul ?_)
  exact Measurable.inner (hG.comp measurable_snd)
    ((hD.comp (measurable_fst.sub measurable_snd)).sub (hD.comp measurable_fst))

theorem q84b_Psi_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d) :
    Integrable (q84b_Psi ρ s ψ b) ((volume : Measure (Torus d)).prod volume) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  obtain ⟨Cg, hCg0, hCg⟩ := Q84a.q84a_gg_bound hd hs0 hsd
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  set C₁ : ℝ := 8 * Cg * (1 + d) * 2 ^ s * K with hC₁
  set BB : Torus d × Torus d → ℝ := fun p => Bρ * Bρ * (C₁ * (wEnv s p.2 0 * wEnv s p.1 b +
    wEnv s p.2 0 * wEnv s (p.1 - p.2) b)) with hBB
  have hωi := q84b_omega_integrable (s := s) hd hcrit
  have hwi := q84b_w_integrable hd hcrit b
  have hwi' : Integrable (fun x : Torus d => wEnv s x b) := by
    simpa [PairCorrAux.wEnv_symm s _ b] using hwi
  have hI1 : Integrable (fun p : Torus d × Torus d => wEnv s p.1 b * wEnv s p.2 0)
      ((volume : Measure (Torus d)).prod volume) := hwi'.mul_prod hωi
  have hI2 : Integrable (fun p : Torus d × Torus d => wEnv s (p.1 - p.2) b * wEnv s p.2 0)
      ((volume : Measure (Torus d)).prod volume) := by
    have hmp := measurePreserving_sub_prod (volume : Measure (Torus d)) (volume : Measure (Torus d))
    have := (hmp.integrable_comp (g := fun q : Torus d × Torus d => wEnv s q.1 b * wEnv s q.2 0)
      hI1.aestronglyMeasurable).2 hI1
    exact this
  have hBBi : Integrable BB ((volume : Measure (Torus d)).prod volume) := by
    have := ((hI1.add hI2).const_mul (Bρ * Bρ * C₁))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [hBB, Pi.add_apply]
    ring
  have hΨm := q84b_measurable_Psi hd hs0 hsd hρc ψ b
  have hBBm : Measurable BB := by
    have h1 := q84b_measurable_omega (s := s) (d := d)
    have h2 := q84b_measurable_w_left (s := s) b
    have e1 : Measurable (fun p : Torus d × Torus d => wEnv s p.2 0) := h1.comp measurable_snd
    have e2 : Measurable (fun p : Torus d × Torus d => wEnv s p.1 b) := h2.comp measurable_fst
    have e3 : Measurable (fun p : Torus d × Torus d => wEnv s (p.1 - p.2) b) :=
      h2.comp (measurable_fst.sub measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((e1.mul e2).add (e1.mul e3)))
  refine Integrable.mono' hBBi hΨm.aestronglyMeasurable ?_
  have hset : MeasurableSet {p : Torus d × Torus d | ‖q84b_Psi ρ s ψ b p‖ ≤ BB p} :=
    measurableSet_le hΨm.norm hBBm
  refine (Measure.ae_prod_iff_ae_ae hset).2 ?_
  filter_upwards [q84b_ae_ne hd0 b] with x hx
  have hu : ∀ᵐ u : Torus d, u ≠ 0 ∧ x - u ≠ b := by
    have h0 := q84b_ae_ne hd0 (0 : Torus d)
    have h1 := q84b_ae_ne hd0 (x - b)
    filter_upwards [h0, h1] with u hu0 hu1
    refine ⟨hu0, fun h => hu1 ?_⟩
    rw [← h]; abel
  filter_upwards [hu] with u hu'
  obtain ⟨hu0, hub⟩ := hu'
  have hxu : x ≠ x - u := by
    intro h
    apply hu0
    have : u = x - x + u := by abel
    rw [sub_self, zero_add] at this
    have h2 : x - u = x := h.symm
    have : u = x - (x - u) := by abel
    rw [h2, sub_self] at this
    exact this
  have hP := Q84a.q84a_Pq_bound hd hs1 hCg0 hCg hPs (a := x) (b := x - u) (c := b) hxu hx hub
  rw [sub_sub_cancel, q84b_wEnv_sub] at hP
  show ‖q84b_Psi ρ s ψ b (x, u)‖ ≤ BB (x, u)
  simp only [q84b_Psi, hBB, norm_mul, Real.norm_eq_abs]
  have hneg : inner ℝ (periodicRieszGrad d s u) (gradFst ψ (x - u) b - gradFst ψ x b) =
      -inner ℝ (periodicRieszGrad d s u) (gradFst ψ x b - gradFst ψ (x - u) b) := by
    rw [← inner_neg_right, neg_sub]
  rw [hneg, abs_neg]
  have h1 := hBρ x
  have h2 := hBρ (x - u)
  have h3 := abs_nonneg (ρ (x - u))
  have h4 := abs_nonneg (inner ℝ (periodicRieszGrad d s u) (gradFst ψ x b - gradFst ψ (x - u) b))
  calc |ρ x| * (|ρ (x - u)| * |inner ℝ (periodicRieszGrad d s u)
        (gradFst ψ x b - gradFst ψ (x - u) b)|)
      ≤ Bρ * (Bρ * (8 * Cg * (1 + d) * 2 ^ s * K * (wEnv s u 0 * wEnv s x b +
          wEnv s u 0 * wEnv s (x - u) b))) := by
        refine mul_le_mul h1 (mul_le_mul h2 hP h4 hBρ0) (mul_nonneg h3 h4) hBρ0
    _ = _ := by simp only [hC₁]; ring

end HRS.Q84b
