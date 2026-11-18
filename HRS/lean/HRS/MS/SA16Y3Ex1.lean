import HRS.MS.SA16Y3Mo1
import HRS.MS.SA16Y3Iw2

/-!
# S.A.16 (SA16Y3) Ex1: cut-off mollification of jets (SA16S item (iii), step (a))

`sa16y3_cutmol n f := ρ_n ⋆ (χ_{n+1} f)` with `χ_R = sa16j_chi d R` (cut-off, `R = n+1 ≥ 1`) and `ρ_n = sa16y_rho d n`.
`sa16y3_cutmol_cc`: smooth and compactly supported for `f ∈ C_c^∞`.
`sa16y3_cutmol_jet`: `‖J_m(cutmol n ψ)‖_{L^p} ≤ C ‖J_m ψ‖_{L^p}` with `C` independent of `n` and `ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

variable {d : ℕ}

/-- the cut-off used at mollification level `n` -/
def sa16y3_cut (d n : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ := sa16j_chi d ((n : ℝ) + 1)

/-- the cut-off mollification `ρ_n ⋆ (χ_{n+1} f)` -/
def sa16y3_cutmol (d n : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  sa16q_mol n (fun y => sa16y3_cut d n y * f y)

lemma sa16y3_cut_bound (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ i ≤ m, ∀ x : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ i (sa16y3_cut d n) x‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := sa16j_cut_bound d m
  exact ⟨B, hB0, fun n i hi x => hB ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) i hi x⟩

lemma sa16y3_cut_cc {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (n : ℕ) :
    IsCcInfty (fun y => sa16y3_cut d n y * ψ y) :=
  ⟨(sa16j_chi_contDiff d _).mul hψ.1, hψ.2.mul_left⟩

lemma sa16y3_cutmol_cc {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (n : ℕ) :
    IsCcInfty (sa16y3_cutmol d n ψ) := by
  have hc := sa16y3_cut_cc hψ n
  refine ⟨?_, ?_⟩
  · exact sa16y3_conv_contDiff (sa16y_rho_integrable n).locallyIntegrable hc
  · have h : HasCompactSupport (convolution (sa16y_rho d n) (fun y => sa16y3_cut d n y * ψ y)
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
      HasCompactSupport.convolution (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (ContinuousLinearMap.lsmul ℝ ℝ) (sa16y_rho_compact (d := d) n) hc.2
    rw [← sa16y3_conv_eq] at h
    exact h

lemma sa16y3_cut_pt (m : ℕ) {B : ℝ} (hB : ∀ n : ℕ, ∀ i ≤ m, ∀ x : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ i (sa16y3_cut d n) x‖ ≤ B) (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖wJet m (fun y => sa16y3_cut d n y * ψ y) x‖ ≤ B * ((d : ℝ) + 1) ^ m * ‖wJet m ψ x‖ :=
  sa16y_prod_jet_le (sa16j_chi_contDiff d _) hψ.1 m x (fun i hi => hB n i hi x)

lemma sa16y3_eLp_mul_const {q c : ℝ} (hc : 0 ≤ c) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    eLpNorm (fun x => c * f x) (ENNReal.ofReal q) volume =
      ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal q) volume := by
  have h : (fun x => c * f x) = c • f := by
    funext x
    simp [smul_eq_mul]
  rw [h, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]

theorem sa16y3_cutmol_jet {p : ℝ} (hp : 1 ≤ p) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty ψ →
      eLpNorm (fun x => ‖wJet m (sa16y3_cutmol d n ψ) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume := by
  obtain ⟨B, hB0, hB⟩ := sa16y3_cut_bound (d := d) m
  refine ⟨(Fintype.card (WIndex d m) : ℝ) * (B * ((d : ℝ) + 1) ^ m), by positivity, fun n ψ hψ => ?_⟩
  have hcm := sa16y3_cutmol_cc hψ n
  have hcont : Continuous (fun x => ‖wJet m (sa16y3_cutmol d n ψ) x‖) :=
    (sa16j_jet_cont hcm.1 m).norm
  -- pointwise: the vector norm is bounded by the sum of the coordinate absolute values
  have hA : ∀ x, ‖wJet m (sa16y3_cutmol d n ψ) x‖ ≤
      ∑ τ : WIndex d m, ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖ := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun τ => ?_
    exact Finset.single_le_sum (f := fun τ : WIndex d m => ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hh := sa16y3_cut_cc hψ n
  have hcoord : ∀ τ : WIndex d m,
      eLpNorm (fun x => ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m) * eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume := by
    intro τ
    have hτm : (τ.1 : ℕ) ≤ m := Nat.lt_succ_iff.mp τ.1.isLt
    have hmol := sa16y3_mol_jet_le hp n hh τ.2
    have hcτ : Continuous (partialDeriv τ.2 (sa16y3_cutmol d n ψ)) :=
      (sa16s_cc_partialDeriv hcm τ.2).1.continuous
    have hhτ : Continuous (partialDeriv τ.2 (fun y => sa16y3_cut d n y * ψ y)) :=
      (sa16s_cc_partialDeriv hh τ.2).1.continuous
    have e1 : eLpNorm (fun x => ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖) (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x => ‖partialDeriv τ.2 (fun y => sa16y3_cut d n y * ψ y) x‖) (ENNReal.ofReal p) volume := by
      rw [eLpNorm_norm _ hcτ.aestronglyMeasurable, eLpNorm_norm _ hhτ.aestronglyMeasurable]
      exact hmol
    have e2 : eLpNorm (fun x => ‖partialDeriv τ.2 (fun y => sa16y3_cut d n y * ψ y) x‖) (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x => ‖wJet m (fun y => sa16y3_cut d n y * ψ y) x‖) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_real hhτ.norm.aestronglyMeasurable (fun x => by
        have := sa16j_pd_le_jet m (fun y => sa16y3_cut d n y * ψ y) x hτm τ.2
        simpa [Real.norm_eq_abs] using this)
    have e3 : eLpNorm (fun x => ‖wJet m (fun y => sa16y3_cut d n y * ψ y) x‖) (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x => B * ((d : ℝ) + 1) ^ m * ‖wJet m ψ x‖) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_real ((sa16j_jet_cont hh.1 m).norm.aestronglyMeasurable) (fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact sa16y3_cut_pt m hB n hψ x)
    have e4 : eLpNorm (fun x => B * ((d : ℝ) + 1) ^ m * ‖wJet m ψ x‖) (ENNReal.ofReal p) volume =
        ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m) * eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume :=
      sa16y3_eLp_mul_const (q := p) (mul_nonneg hB0 (by positivity)) _
    exact e1.trans (e2.trans (e3.trans e4.le))
  have hcont' : Continuous (fun x => ∑ τ : WIndex d m, ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖) := by
    refine continuous_finset_sum _ fun τ _ => ?_
    exact (sa16s_cc_partialDeriv hcm τ.2).1.continuous.norm
  have hN : (0 : ℝ) ≤ (Fintype.card (WIndex d m) : ℝ) := Nat.cast_nonneg _
  calc eLpNorm (fun x => ‖wJet m (sa16y3_cutmol d n ψ) x‖) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ τ : WIndex d m, ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖)
          (ENNReal.ofReal p) volume :=
        eLpNorm_mono_real hcont.aestronglyMeasurable (fun x => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hA x)
    _ = eLpNorm (∑ τ : WIndex d m, fun x => ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖)
          (ENNReal.ofReal p) volume := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ τ : WIndex d m, eLpNorm (fun x => ‖partialDeriv τ.2 (sa16y3_cutmol d n ψ) x‖)
          (ENNReal.ofReal p) volume := eLpNorm_sum_le hp1
    _ ≤ ∑ τ : WIndex d m, ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m) *
          eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume :=
        Finset.sum_le_sum fun τ _ => hcoord τ
    _ = (Fintype.card (WIndex d m) : ENNReal) * (ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m) *
          eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ENNReal.ofReal ((Fintype.card (WIndex d m) : ℝ) * (B * ((d : ℝ) + 1) ^ m)) *
          eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_mul hN, ENNReal.ofReal_natCast, mul_assoc]

end HRS.Whole.AppendixA.Phase2SA16R
