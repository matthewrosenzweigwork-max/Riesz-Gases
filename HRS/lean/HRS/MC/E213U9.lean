import HRS.MC.E213U5b
import HRS.MC.E213L
import HRS.MC.S7S7f
import HRS.MC.S7FCD3BLaw
import HRS.MC.SEdgeB1
import HRS.MC.S7PIS2Cb

/-!
# Packet e213u9 (Theorem 2.13, part): `init_term`

The initial-term bound: `static_field` applied to `Ψ_a/L = (Ucan 0 ∘ I_a)/L`, uniform in `a` and `Φ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U9

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- The susceptibility covariance is `∫ φ · responseRep ψ dμ` on smooth tests. -/
theorem u9_susc_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) γ φ ψ =
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  rw [← HRS.MC.Sec7.FCD3B.d3b_Cmat_eq hd hs0 hs hγ hρ hψ]
  obtain ⟨r, v, hrS, -, hr_ae, -, hmean, -⟩ := HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hγ hρ hψ
  have hφc : Continuous φ := HRS.Q66.q66_cont_of_smooth hφ
  have hrc : Continuous r := HRS.Q66.q66_cont_of_smooth hrS
  have hφi := HRS.MC.E213L.e213l_integrable (μ := withDensityReal ρ) hφc
  have hri := HRS.MC.E213L.e213l_integrable (μ := withDensityReal ρ) hrc
  have hφri : Integrable (fun x => φ x * r x) (withDensityReal ρ) :=
    HRS.MC.E213L.e213l_integrable (μ := withDensityReal ρ) (hφc.mul hrc)
  unfold susceptibilityCov l2Inner projMean
  have e1 : ∫ x, (φ x - pair (withDensityReal ρ) φ) *
      responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) =
      ∫ x, (φ x * r x - pair (withDensityReal ρ) φ * r x) ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [hr_ae] with x hx
    rw [← hx]; ring
  have e2 : ∫ x, φ x * responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) =
      ∫ x, φ x * r x ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [hr_ae] with x hx
    rw [← hx]
  rw [e1, e2, integral_sub hφri (hri.const_mul _), integral_const_mul, hmean]
  simp

/-- The scalar error functional of `static_field`. -/
def u9E {α ι B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [MeasurableSpace α] [MeasurableSpace ι] (n : ℝ) (Q : Measure α) (ζ : α → B) (G : Measure B)
    (μ : Measure ι) (ℓ : ι → B) (F : B → ℝ) : ℝ :=
  n * (∫ X, F (ζ X) ∂Q - ∫ z, F z ∂G) -
    (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z ![ℓ x, ℓ x, ℓ x] ∂μ ∂G

theorem u9_iter_const_mul {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ψ : B → ℝ} {j : ℕ} {z : B} (c : ℝ) (h : ContDiffAt ℝ j Ψ z) :
    iteratedFDeriv ℝ j (fun z => c * Ψ z) z = c • iteratedFDeriv ℝ j Ψ z :=
  iteratedFDeriv_const_smul_apply' (a := c) h

theorem u9E_const_mul {α ι B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [MeasurableSpace α] [MeasurableSpace ι] (n : ℝ) (Q : Measure α) (ζ : α → B) (G : Measure B)
    (μ : Measure ι) (ℓ : ι → B) {F : B → ℝ} (hF : ContDiff ℝ 3 F) (c : ℝ) :
    u9E n Q ζ G μ ℓ (fun z => c * F z) = c * u9E n Q ζ G μ ℓ F := by
  unfold u9E
  have h1 : ∫ X, c * F (ζ X) ∂Q = c * ∫ X, F (ζ X) ∂Q := integral_const_mul _ _
  have h2 : ∫ z, c * F z ∂G = c * ∫ z, F z ∂G := integral_const_mul _ _
  have h3 : ∫ z, ∫ x, iteratedFDeriv ℝ 3 (fun z => c * F z) z ![ℓ x, ℓ x, ℓ x] ∂μ ∂G =
      c * ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z ![ℓ x, ℓ x, ℓ x] ∂μ ∂G := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [u9_iter_const_mul c hF.contDiffAt, ← integral_const_mul]
    simp
  simp only [h1, h2, h3]
  ring

/-- Scaling a `C_b^5` function: membership and norm. -/
theorem u9_memCb_const_mul {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    {Ψ : B → ℝ} (h : MemCb 5 Ψ) {c : ℝ} (hc : 0 ≤ c) :
    MemCb 5 (fun z => c * Ψ z) ∧ cbNorm 5 (fun z => c * Ψ z) ≤ c * cbNorm 5 Ψ := by
  have hd : ∀ j ≤ 5, ∀ z, iteratedFDeriv ℝ j (fun z => c * Ψ z) z = c • iteratedFDeriv ℝ j Ψ z :=
    fun j hj z => u9_iter_const_mul c ((h.1.contDiffAt (x := z)).of_le (by exact_mod_cast hj))
  have hn : ∀ j ≤ 5, ∀ z, ‖iteratedFDeriv ℝ j (fun z => c * Ψ z) z‖ = c * ‖iteratedFDeriv ℝ j Ψ z‖ := by
    intro j hj z
    rw [hd j hj z, norm_smul, Real.norm_of_nonneg hc]
  refine ⟨⟨h.1.const_smul c, fun j hj => ?_⟩, ?_⟩
  · obtain ⟨M, hM⟩ := h.2 j hj
    refine ⟨c * M, ?_⟩
    rintro _ ⟨z, rfl⟩
    show ‖iteratedFDeriv ℝ j (fun z => c * Ψ z) z‖ ≤ c * M
    rw [hn j hj z]
    exact mul_le_mul_of_nonneg_left (hM ⟨z, rfl⟩) hc
  · unfold cbNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hjm => ?_
    have hj : j ≤ 5 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
    obtain ⟨M, hM⟩ := h.2 j hj
    refine ciSup_le fun z => ?_
    show ‖iteratedFDeriv ℝ j (fun z => c * Ψ z) z‖ ≤ _
    rw [hn j hj z]
    exact mul_le_mul_of_nonneg_left
      (le_ciSup (f := fun z => ‖iteratedFDeriv ℝ j Ψ z‖) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM ⟨y, rfl⟩⟩ z) hc

section Main

variable {S : PreparedData d} {β₀ m : ℝ}

theorem init_term_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a),
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      |Real.sqrt N *
          (∫ X, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a
              (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) X))
              ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) -
            ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0))) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F
            ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] ∂S.μ0 ∂(gd.P₀.map (gd.η 0))| ≤ ε := by
  intro ε hε
  -- uniform bound on `I_a`
  obtain ⟨C, c, hC, hc, hI⟩ := Classical.choose_spec (exists_Iwin S β₀ hE T)
  have hIw : ∀ a : ℝ, 0 ≤ a → ‖Iwin S β₀ hE T a‖ ≤ C := fun a ha =>
    ((hI a ha).2).trans (mul_le_of_le_one_right hC.le
      (Real.exp_le_one_iff.2 (by nlinarith)))
  -- the Gaussian side
  obtain ⟨Y₀, hY₀, hsol⟩ := gd.limit
  have hη0 : Measurable (gd.η 0) := (hsol 0).meas 0
  have hinit : ∀ᵐ ω ∂gd.P₀, gd.η 0 ω = Y₀ ω := (hsol 0).init
  have hGeq : gd.P₀.map (gd.η 0) = gd.P₀.map Y₀ := Measure.map_congr hinit
  have hG : IsCenteredGaussianWithCov (rLvl d) (gd.P₀.map (gd.η 0)) fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d S.s) (withDensityReal S.ρ0) β₀ ψ x ∂(withDensityReal S.ρ0) := by
    rw [hGeq]
    refine ⟨hY₀.1, fun φ ψ hφ hψ => ?_⟩
    rw [hY₀.2 φ ψ hφ hψ]
    exact u9_susc_eq S.hd S.hs0 hE.s_lt hE.β₀_nonneg S.hρ0 hφ hψ
  set L : ℝ := (1 + C) ^ 5 * 6 with hL
  have hLpos : 0 < L := by positivity
  obtain ⟨N₀, hN₀⟩ := HRS.MC.Sec7.S7f.static_field_proof S.hd S.hs0 hE.s_lt (rLvl d) rfl β₀ hE.β₀_nonneg
    S.ρ0 S.hρ0 (gd.P₀.map (gd.η 0)) hG (ε / L) (div_pos hε hLpos)
  refine ⟨N₀, fun N hN hN1 a ha Φ hΦ => ?_⟩
  have hΦcb : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  obtain ⟨hf1, hf2, -⟩ := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦcb
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨le_refl _, by linarith⟩
  have hfmem := hf1 0 h0mem
  have hfcb : cbNorm 5 (Ucan hE T a ha Φ 0) ≤ 6 := by
    unfold cbNorm
    calc _ ≤ ∑ j ∈ Finset.range (5 + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj : j ≤ 5 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
          exact ciSup_le fun y => (hf2 0 h0mem j hj y).trans hΦ.2.2
      _ = 6 := by simp
  obtain ⟨hΨ1, hΨ2, -⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Iwin S β₀ hE T a) hfmem
  have hΨn : cbNorm 5 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) ≤ L := by
    refine hΨ2.trans ?_
    have h1 : (1 + ‖Iwin S β₀ hE T a‖) ^ 5 ≤ (1 + C) ^ 5 :=
      pow_le_pow_left₀ (by positivity) (by linarith [hIw a ha]) 5
    have h2 : 0 ≤ cbNorm 5 (Ucan hE T a ha Φ 0) := by
      unfold cbNorm
      exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    calc _ ≤ (1 + C) ^ 5 * cbNorm 5 (Ucan hE T a ha Φ 0) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ (1 + C) ^ 5 * 6 := mul_le_mul_of_nonneg_left hfcb (by positivity)
  obtain ⟨hΨ'1, hΨ'2⟩ := u9_memCb_const_mul hΨ1 (inv_nonneg.2 hLpos.le)
  have hball : (fun z => L⁻¹ * Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) ∈ CbUnitBall (NegSobolev d (rLvl d)) 5 :=
    ⟨hΨ'1.1, hΨ'1.2, hΨ'2.trans (by
      calc L⁻¹ * cbNorm 5 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) ≤ L⁻¹ * L :=
            mul_le_mul_of_nonneg_left hΨn (inv_nonneg.2 hLpos.le)
        _ = 1 := inv_mul_cancel₀ hLpos.ne')⟩
  have hkey := hN₀ N hN hN1 _ hball
  have hscale := u9E_const_mul (Real.sqrt N) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) (gd.P₀.map (gd.η 0)) S.μ0
    (ellVec S β₀) (F := fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z))
    (hΨ1.1.of_le (by norm_num)) L⁻¹
  change |u9E (Real.sqrt N) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) (gd.P₀.map (gd.η 0)) S.μ0
    (ellVec S β₀) (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z))| ≤ ε
  change |u9E (Real.sqrt N) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) (gd.P₀.map (gd.η 0)) S.μ0
    (ellVec S β₀) (fun z => L⁻¹ * Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z))| ≤ ε / L at hkey
  rw [hscale, abs_mul, abs_of_pos (inv_pos.2 hLpos)] at hkey
  have := (mul_le_mul_of_nonneg_left hkey hLpos.le)
  rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at this
  calc _ ≤ _ := this
    _ = ε := by field_simp

end Main

end HRS.MC.E213U9

end
