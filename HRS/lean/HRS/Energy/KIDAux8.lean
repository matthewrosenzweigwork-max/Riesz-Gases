import HRS.Energy.KIDAux7

/-!
# KID helper file 8: integrability of the full drift on `[0,t] × Ω` (Fubini step)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Fubini

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.integrable_Jc (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (hmicro : Integrable (fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2))
      ((volume.restrict (Set.Icc 0 t)).prod P)) :
    Integrable (fun p : ℝ × Ω => Jc D h ρ T X p.1 p.2) ((volume.restrict (Set.Icc 0 t)).prod P) := by
  have hN0 : 0 < N := by omega
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set μ : Measure (ℝ × Ω) := (volume.restrict (Set.Icc 0 t)).prod P with hμ
  have hXm := measurable_X_joint hF
  have hJm := c.measurable_Jc hF hsm hev
  have hmic : Measurable fun p : ℝ × Ω => microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2) := by
    have := (c.measurable_micro hsm hev).comp (measurable_fst.prodMk hXm)
    simpa only [Function.comp_def] using this
  have hr : ∀ᵐ p ∂μ, p.1 ∈ Set.Icc (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hmic_eq : (fun p : ℝ × Ω => microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2)) =ᵐ[μ]
      fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2) := by
    filter_upwards [hr] with p hp
    rw [clampT_of_mem ⟨hp.1, hp.2.trans htT⟩]
  have hmic_int : Integrable (fun p : ℝ × Ω =>
      microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2)) μ := hmicro.congr hmic_eq.symm
  obtain ⟨C₁, C₂, hCb⟩ := c.Cb_bound hsm hev hN0
  set C : ℝ := (1 / 2) * C₁ + D.invβ * C₂ with hC
  have hgood : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) t,
      |Jc D h ρ T X r ω - microTerm D h (ρ (clampT T r)) (X (Real.toNNReal r) ω)| ≤ C := by
    filter_upwards [hsol.no_collision] with ω hω r hrI
    have hrT : r ∈ Set.Icc 0 T := ⟨hrI.1, hrI.2.trans htT⟩
    have hX' : X (Real.toNNReal r) ω ∉ collisionSet d N :=
      hω _ (by rw [Real.coe_toNNReal _ hrI.1]; exact hrI.2.trans htT)
    have hmain := c.main_alg hsm hev hrT hN0 (X (Real.toNNReal r) ω) hX'
    have e : Jc D h ρ T X r ω - microTerm D h (ρ (clampT T r)) (X (Real.toNNReal r) ω) =
        (1 / 2) * commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r)) (X (Real.toNNReal r) ω)
            (withDensityReal (ρ r)) +
          D.invβ * offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) := by
      unfold Jc
      rw [clampT_of_mem hrT]
      unfold Jc at *
      linarith
    rw [e]
    obtain ⟨b1, b2⟩ := hCb r hrT _ hX'
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg D.hβ]
    have := mul_le_mul_of_nonneg_left b2 D.hβ
    linarith
  have hQm : Measurable fun p : ℝ × Ω => Jc D h ρ T X p.1 p.2 -
      microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2) := hJm.sub hmic
  have hS : MeasurableSet {p : ℝ × Ω | |Jc D h ρ T X p.1 p.2 -
      microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2)| ≤ C} :=
    measurableSet_le hQm.abs measurable_const
  have hQb : ∀ᵐ p ∂μ, |Jc D h ρ T X p.1 p.2 -
      microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2)| ≤ C := by
    refine (Measure.ae_prod_iff_ae_ae hS).2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hrI
    filter_upwards [hgood] with ω hω using hω r hrI
  have hQint : Integrable (fun p : ℝ × Ω => Jc D h ρ T X p.1 p.2 -
      microTerm D h (ρ (clampT T p.1)) (X (Real.toNNReal p.1) p.2)) μ :=
    Integrable.mono' (integrable_const C) hQm.aestronglyMeasurable
      (hQb.mono fun p hp => by simpa [Real.norm_eq_abs] using hp)
  have := hQint.add hmic_int
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp

end Fubini

end HRS.KID
