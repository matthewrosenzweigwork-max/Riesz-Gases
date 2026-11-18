import HRS.MC.E213U18h

/-!
# Packet e213u18 (part i): the drift term `E[ℓ_i(D_a) ℓ_j(Z_a) ℓ_k(Z_a)]`

`E[ℓ_i(D_a) ℓ_j(Z_a) ℓ_k(Z_a)] = ∫_0^{t_i} ∬ h_{∇ f_i^r}(x,y) χ_j^r(x) χ_k^r(y) dx dy dr` (Fubini over `(ω, v)` and the Wick pairing at a.e. fixed time).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U10 HRS.MC.E213U1 HRS.MC.E213U13

variable {d : ℕ}

section DTerm

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_B_prod_int (H : ℝ) (hH : 0 < H) {ζ : gd.Ω₀ → ℝ} (hζ : MemLp ζ 2 gd.P₀) :
    Integrable (fun p : gd.Ω₀ × ℝ => ‖gd.B p.2 p.1‖ * |ζ p.1|)
      (gd.P₀.prod (volume.restrict (Set.Ioc 0 H))) := by
  have hBm : Measurable (fun p : gd.Ω₀ × ℝ => ‖gd.B p.2 p.1‖) :=
    (gd.B_meas.comp measurable_swap).norm
  have hmeas : AEStronglyMeasurable (fun p : gd.Ω₀ × ℝ => ‖gd.B p.2 p.1‖ * |ζ p.1|)
      (gd.P₀.prod (volume.restrict (Set.Ioc 0 H))) :=
    hBm.aestronglyMeasurable.mul (hζ.aestronglyMeasurable.norm).comp_fst
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [gd_B_int gd H hH] with ω hω
    exact hω.mul_const _
  · have h1 : ∀ ω : gd.Ω₀, ∫ v in Set.Ioc 0 H, ‖‖gd.B v ω‖ * |ζ ω|‖ =
        (∫ v in Set.Ioc 0 H, ‖gd.B v ω‖) * |ζ ω| := by
      intro ω
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_abs, abs_norm]
    simp_rw [h1]
    exact (gd_B_L2 gd H hH).integrable_mul hζ.norm

theorem u18_joint_int (H : ℝ) (hH : 0 < H) {Λ : ℝ → NegSobolev d (rLvl d) →L[ℝ] ℝ} {K : ℝ}
    (hΛ : ∀ v, ‖Λ v‖ ≤ K) (hΛm : Measurable (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2))
    {ζ : gd.Ω₀ → ℝ} (hζ : MemLp ζ 2 gd.P₀) :
    Integrable (fun p : gd.Ω₀ × ℝ => Λ p.2 (gd.B p.2 p.1) * ζ p.1)
      (gd.P₀.prod (volume.restrict (Set.Ioc 0 H))) := by
  have hm : AEStronglyMeasurable (fun p : gd.Ω₀ × ℝ => Λ p.2 (gd.B p.2 p.1) * ζ p.1)
      (gd.P₀.prod (volume.restrict (Set.Ioc 0 H))) := by
    have : Measurable (fun p : gd.Ω₀ × ℝ => Λ p.2 (gd.B p.2 p.1)) :=
      hΛm.comp (measurable_snd.prodMk (gd.B_meas.comp measurable_swap))
    exact this.aestronglyMeasurable.mul hζ.aestronglyMeasurable.comp_fst
  refine ((u18_B_prod_int gd H hH hζ).const_mul K).mono' hm (Eventually.of_forall fun p => ?_)
  rw [norm_mul, ← mul_assoc]
  have h1 : ‖Λ p.2 (gd.B p.2 p.1)‖ ≤ K * ‖gd.B p.2 p.1‖ :=
    ((Λ p.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hΛ _) (norm_nonneg _))
  rw [Real.norm_eq_abs (ζ p.1)]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The observation variable `ζ_l = η^{t_l}(φ_l)`. -/
abbrev u18_zeta (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ) (l : Fin 3) (ω : gd.Ω₀) : ℝ :=
  NegSobolev.eval (gd.η (t l) ω) (φ l)

theorem u18_zeta_memLp {H : ℝ} {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ} {χ : Fin 3 → ℝ → Torus d → ℝ}
    (h : U18Cov gd H t φ χ) (l : Fin 3) : MemLp (u18_zeta gd t φ l) 4 gd.P₀ :=
  (u18_G4 gd H h.hH _ (u18_eta_mem gd H h.hH (h.ht l) (h.hφ l))).1

theorem u18_Dterm (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ}
    {χ : Fin 3 → ℝ → Torus d → ℝ} (h : U18Cov gd (a + T) t φ χ) (hta : ∀ i, t i ∈ Set.Icc a (a + T))
    (ℓ : Fin 3 → PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ i w, ℓ i w = NegSobolev.eval (pathEval w (t i - a)) (φ i)) (i j k : Fin 3) :
    ∫ ω, ℓ i (gd.Dwin T a ω) * ℓ j (gd.Zwin T a ω) * ℓ k (gd.Zwin T a ω) ∂gd.P₀ =
      ∫ r in Set.Icc 0 (t i), ∫ x, ∫ y, HRS.Main.hKernel d S.s
        (Torus.grad (propagator S.dyn S.ρ r (t i) (φ i))) x y * χ j r x * χ k r y := by
  have hH : 0 < a + T := h.hH
  obtain ⟨K, hK, Λ, hΛ, hΛm, hΛ0, hΛe, hΛrep⟩ := u18_D_data gd T hT a ha (hta i) (h.hφ i)
  have hζζ : MemLp (fun ω => u18_zeta gd t φ j ω * u18_zeta gd t φ k ω) 2 gd.P₀ :=
    HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (u18_zeta_memLp gd h j) (u18_zeta_memLp gd h k)
  have hZ : ∀ l, ∀ᵐ ω ∂gd.P₀, ℓ l (gd.Zwin T a ω) = u18_zeta gd t φ l ω := by
    intro l
    filter_upwards [u18_Zwin_eval gd T hT a ha (ψ := φ l)] with ω hω
    have hτ : t l - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [(hta l).1], by linarith [(hta l).2]⟩
    rw [hℓ, hω _ hτ]
    simp only [u18_zeta, add_sub_cancel]
  have step1 : ∫ ω, ℓ i (gd.Dwin T a ω) * ℓ j (gd.Zwin T a ω) * ℓ k (gd.Zwin T a ω) ∂gd.P₀ =
      ∫ ω, (∫ v in Set.Ioc 0 (a + T), Λ v (gd.B v ω) *
        (u18_zeta gd t φ j ω * u18_zeta gd t φ k ω)) ∂gd.P₀ := by
    refine integral_congr_ae ?_
    filter_upwards [hZ j, hZ k, hΛrep] with ω h1 h2 h3
    rw [integral_mul_const, hℓ i, h3, h1, h2]
    ring
  have hint := u18_joint_int gd (a + T) hH hΛ hΛm hζζ
  rw [step1, integral_integral_swap (f := fun ω v => Λ v (gd.B v ω) *
    (u18_zeta gd t φ j ω * u18_zeta gd t φ k ω)) hint]
  have hBw : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) (a + T))),
      IsWickQuadraticField S.s gd.P₀ (fun ω => gd.η v ω) (withDensityReal (S.ρ v)) (gd.B v) :=
    ae_restrict_of_ae_restrict_of_subset (fun v hv => (hv.1.le : v ∈ Set.Ici (0 : ℝ))) gd.B_wick
  have hintv : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) (a + T))),
      Integrable (fun ω => ‖gd.B v ω‖ *
        |u18_zeta gd t φ j ω * u18_zeta gd t φ k ω|) gd.P₀ :=
    (u18_B_prod_int gd (a + T) hH hζζ).prod_left_ae
  have step5 : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) (a + T))),
      ∫ ω, Λ v (gd.B v ω) * (u18_zeta gd t φ j ω * u18_zeta gd t φ k ω) ∂gd.P₀ =
        (Set.Iic (t i)).indicator (fun r => ∫ x, ∫ y, HRS.Main.hKernel d S.s
          (Torus.grad (propagator S.dyn S.ρ r (t i) (φ i))) x y * χ j r x * χ k r y) v := by
    filter_upwards [hBw, hintv, ae_restrict_mem measurableSet_Ioc] with v hW hi hv
    by_cases hvt : v ≤ t i
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hvt)]
      have hf : Torus.IsSmooth (propagator S.dyn S.ρ v (t i) (φ i)) := (HRS.MC.L2C0.l2c0_proof (regime S β₀ hE) (φ i) (h.hφ i) v (t i) hv.1.le hvt).1
      rw [← u18_D_pair h j k ⟨hv.1.le, hv.2⟩ hW hi hf]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      rw [hΛe v hv.1.le hvt]
    · rw [Set.indicator_of_notMem (show v ∉ Set.Iic (t i) from hvt), hΛ0 v (not_le.1 hvt)]
      simp
  rw [integral_congr_ae step5, setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioc (0 : ℝ) (a + T) ∩ Set.Iic (t i) = Set.Ioc 0 (t i) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans (hta i).2⟩, h3⟩
  rw [hset, integral_Icc_eq_integral_Ioc]


end DTerm

end HRS.MC.E213U18

end
