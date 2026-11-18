import HRS.Commutator.Torus.NRSTAux31

/-!
# NRS-T, part 32: the `ℝ^d` bound for the ratio multiplier `(1+4π²|ξ|²)^{β/2}(2π|ξ|)^{-β}` on the lifts
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- A compactly supported smooth function agreeing with `ψ` (smooth off the origin) on an annulus. -/
lemma nrstr_theta_exists_gen (ψ : 𝔼 → ℂ) (hψ : ∀ η : 𝔼, η ≠ 0 → ContDiffAt ℝ ∞ ψ η) {R : ℝ} (hR : 1 ≤ R) :
    ∃ θ : 𝔼 → ℂ, θ.HasTemperateGrowth ∧ ∀ ξ : 𝔼, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ R → θ ξ = ψ ξ := by
  have hR0 : 0 < R := by linarith
  set b1 := nrstr_b1 d with hb1
  set b2 := nrstr_b2 R hR0 (d := d) with hb2
  set cut : 𝔼 → ℝ := fun ξ => (1 - b1 ξ) * b2 ξ with hcut
  set θ : 𝔼 → ℂ := fun ξ => ψ ξ * ((cut ξ : ℝ) : ℂ) with hθ
  have hcutsm : ContDiff ℝ ∞ cut := (contDiff_const.sub b1.contDiff).mul b2.contDiff
  have hsm : ContDiff ℝ ∞ θ := by
    refine HRS.Commutator.Whole.cmxMY_contDiff_of_away_real (r := 1 / 4) (by norm_num) (fun η hη => ?_) (fun η hη => ?_)
    · exact (hψ η hη).mul ((Complex.ofRealCLM.contDiff.comp hcutsm).contDiffAt)
    · have : b1 η = 1 := b1.one_of_mem_closedBall (by
        simpa [hb1, nrstr_b1, mem_closedBall_zero_iff] using hη.le)
      simp [hθ, hcut, this]
  have hcs : HasCompactSupport θ := by
    have : HasCompactSupport (fun ξ : 𝔼 => ((cut ξ : ℝ) : ℂ)) := by
      have h2 : HasCompactSupport (fun ξ : 𝔼 => b2 ξ) := b2.hasCompactSupport
      have h3 : HasCompactSupport cut := h2.mul_left
      exact h3.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
    exact this.mul_left
  refine ⟨θ, hcs.hasTemperateGrowth hsm, fun ξ h1 h2 => ?_⟩
  have e1 : b1 ξ = 0 := b1.zero_of_le_dist (by
    simpa [hb1, nrstr_b1, dist_zero_right] using h1)
  have e2 : b2 ξ = 1 := b2.one_of_mem_closedBall (by
    simpa [hb2, nrstr_b2, mem_closedBall_zero_iff] using h2)
  simp [hθ, hcut, e1, e2]

/-- `mulS θ W = nrstg_T θ W`. -/
lemma nrstr_mulS_eq_T (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (W : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    HRS.Commutator.Whole.XLI.mulS θ hθ W x = nrstg_T θ W x := by
  rw [HRS.Commutator.Whole.XLI.mulS_apply, Real.fourierInv_eq']
  unfold nrstg_T
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [leibt_e_comm x ξ]
  rfl

/-- The ratio symbol `(1+4π²|ξ|²)^{β/2}(2π|ξ|)^{-β}`. -/
def nrstr_mmB (β : ℝ) (ξ : 𝔼) : ℂ :=
  HRS.Commutator.Whole.XLI.bsymX β ξ * (((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ)

lemma nrstr_inv_contDiffAt (β : ℝ) (η : 𝔼) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (fun η : 𝔼 => ((((2 * Real.pi * ‖η‖) ^ (-β) : ℝ)) : ℂ)) η := by
  have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
  have h2 : ContDiffAt ℝ ∞ (fun η : 𝔼 => 2 * Real.pi * ‖η‖) η :=
    contDiffAt_const.mul (contDiffAt_norm ℝ hη)
  have h3 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (2 * Real.pi * ‖η‖) ^ (-β)) η :=
    h2.rpow_const_of_ne (by positivity)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp η h3

lemma nrstr_Rd_bessel (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : β < d) {p : ℝ} (hp : 1 < p) :
    ∃ Cx : ℝ≥0∞, Cx ≠ ⊤ ∧ ∀ f : NRST.TPA d, (∀ k ∈ f.coeff.support, 3 ≤ ‖Lattice.toEuc k‖) →
      ∃ θ : 𝔼 → ℂ, θ.HasTemperateGrowth ∧
        (∀ k ∈ f.coeff.support, θ (Lattice.toEuc k) = nrstr_mmB β (Lattice.toEuc k)) ∧
        ∀ (N : ℝ) (hN : 1 ≤ N), ∃ Rs : SchwartzMap 𝔼 ℂ,
          (∀ x, Rs x = nrstg_T θ (nrstr_W f N (by linarith)) x) ∧
          eLpNorm (⇑Rs) (ENNReal.ofReal p) volume ≤
            Cx * eLpNorm (⇑(nrstr_W f N (by linarith))) (ENNReal.ofReal p) volume := by
  obtain ⟨Cx, hCx, hB⟩ := HRS.Commutator.Whole.XBB.xbb_bessel_hom hd hβ hβd
  refine ⟨Cx, hCx, fun f hf => ?_⟩
  classical
  set R : ℝ := 1 + ∑ k ∈ f.coeff.support, ‖Lattice.toEuc k‖ + 1 / 8 with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ ∑ k ∈ f.coeff.support, ‖Lattice.toEuc k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [hR]; linarith
  obtain ⟨θ1, hθ1, hθ1R⟩ := nrstr_theta_exists_gen
    (fun ξ : 𝔼 => ((((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ)) : ℂ)) (nrstr_inv_contDiffAt β) hR1
  have hθ : (fun ξ => HRS.Commutator.Whole.XLI.bsymX β ξ * θ1 ξ).HasTemperateGrowth :=
    (HRS.Commutator.Whole.XLI.bsymX_temperate β).mul hθ1
  have hsupp : ∀ k ∈ f.coeff.support, 1 / 2 ≤ ‖Lattice.toEuc k‖ ∧ ‖Lattice.toEuc k‖ + 1 / 8 ≤ R := by
    intro k hk
    have h3 := hf k hk
    have := Finset.single_le_sum (f := fun k => ‖Lattice.toEuc k‖) (fun k _ => norm_nonneg _) hk
    rw [hR]; constructor <;> linarith
  refine ⟨fun ξ => HRS.Commutator.Whole.XLI.bsymX β ξ * θ1 ξ, hθ, fun k hk => ?_, fun N hN => ?_⟩
  · obtain ⟨h1, h2⟩ := hsupp k hk
    simp only [nrstr_mmB]
    rw [hθ1R _ h1 (by linarith)]
  · have hN0 : 0 < N := by linarith
    set W := nrstr_W f N hN0 with hW
    have hFW : ∀ ξ : 𝔼, (‖ξ‖ < 2 ∨ R < ‖ξ‖) → 𝓕 (⇑W) ξ = 0 := by
      intro ξ hξ
      refine nrstr_fourierW_zero f hN ξ fun k hk => ?_
      have h3 := hf k hk
      obtain ⟨_, h2⟩ := hsupp k hk
      rcases hξ with h | h
      · have : ‖Lattice.toEuc k‖ - ‖ξ‖ ≤ ‖ξ - Lattice.toEuc k‖ := by
          rw [norm_sub_rev]; exact norm_sub_norm_le _ _
        linarith
      · have : ‖ξ‖ - ‖Lattice.toEuc k‖ ≤ ‖ξ - Lattice.toEuc k‖ := norm_sub_norm_le _ _
        linarith
    set fS := HRS.Commutator.Whole.XLI.mulS θ1 hθ1 W with hfS
    have hfS1 : ∀ ξ, 𝓕 (⇑fS) ξ = θ1 ξ * 𝓕 (⇑W) ξ := fun ξ =>
      HRS.Commutator.Whole.XLI.fourier_mulS θ1 hθ1 W ξ
    refine ⟨HRS.Commutator.Whole.XLI.mulS _ hθ W, fun x => nrstr_mulS_eq_T _ hθ W x, ?_⟩
    have hRs : HRS.Commutator.Whole.XLI.mulS _ hθ W =
        HRS.Commutator.Whole.XLI.Fm β fS := by
      unfold HRS.Commutator.Whole.XLI.Fm
      rw [HRS.Commutator.Whole.XLI.mulS_mulS _ _ (HRS.Commutator.Whole.XLI.bsymX_temperate β) hθ1 hθ]
    rw [hRs]
    have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
    refine hB fS W (fun ξ => ?_) (fun ξ hξ => ?_) _ hP1
    · by_cases hξ : ‖ξ‖ < 2 ∨ R < ‖ξ‖
      · rw [hfS1, hFW ξ hξ]; simp
      · push Not at hξ
        rw [hfS1, hθ1R ξ (by linarith [hξ.1]) hξ.2, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add
          (by have := hξ.1; positivity)]
        simp
    · rw [hfS1, hFW ξ (Or.inl hξ), mul_zero]

end HRS.Commutator.TorusNote
