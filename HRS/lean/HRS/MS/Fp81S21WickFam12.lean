import HRS.MS.Fp81S21WickFam11

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21

local instance fp81s21_wickFam12_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- Oscillator observations of a continuous supplied Gaussian extension
admit L⁴ classes that are continuous on the nonnegative half-line. -/
theorem fp81s21_wickFam_oscillator_L4_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    (hφLp : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ))
    (hJoint : ∀ u : ℝ, 0 ≤ u → ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω))
    (hag : ∀ u : ℝ, 0 ≤ u → (T u (hφLp.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
      fun ω => OscDual.eval (G.Z u ω) φ)
    (hcont : ContinuousOn (fun u => T u (hφLp.toLp φ)) (Ici (0 : ℝ))) :
    ∃ F : ℝ → Lp ℝ 4 G.P,
      ContinuousOn F (Ici (0 : ℝ)) ∧
      ∀ u : ℝ, 0 ≤ u → (F u : G.Ω → ℝ) =ᵐ[G.P]
        fun ω => OscDual.eval (G.Z u ω) φ := by
  classical
  let X : ℝ → G.Ω → ℝ := fun u ω => OscDual.eval (G.Z (max u 0) ω) φ
  have h4 : ∀ u, MemLp (X u) 4 G.P := by
    intro u
    let Y : G.Ω → Fin 1 → ℝ := fun ω _ => (T (max u 0) (hφLp.toLp φ)) ω
    have hYm : AEMeasurable Y G.P := aemeasurable_pi_iff.2 fun i =>
      (Lp.stronglyMeasurable (T (max u 0) (hφLp.toLp φ))).aestronglyMeasurable.aemeasurable
    have hYlaw : HasGaussianLaw Y G.P := ⟨hYm, (hJoint (max u 0) (le_max_right u 0)
      1 (fun _ => hφLp.toLp φ)).1⟩
    let π : (Fin 1 → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
    have hscalar : HasGaussianLaw (fun ω => (T (max u 0) (hφLp.toLp φ)) ω) G.P := by
      simpa [π, Y, ContinuousLinearMap.proj_apply] using hYlaw.map_fun π
    have hz4 : MemLp (fun ω => (T (max u 0) (hφLp.toLp φ)) ω) 4 G.P :=
      hscalar.memLp (by norm_num)
    exact (memLp_congr_ae (hag (max u 0) (le_max_right u 0))).1 hz4
  have ha : ∀ u ∈ Ici (0 : ℝ),
      (T u (hφLp.toLp φ) : G.Ω → ℝ) =ᵐ[G.P] X u := by
    intro u hu
    have hu0 : 0 ≤ u := Set.mem_Ici.mp hu
    simpa [X, max_eq_left hu0] using hag u hu0
  have hb : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      eLpNorm (X t - X s) 4 G.P ≤ HRS.Contr.gK ^ (1 / 4 : ℝ) *
        eLpNorm (X t - X s) 2 G.P := by
    intro s hs t ht
    have hs0 : 0 ≤ s := Set.mem_Ici.mp hs
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    change eLpNorm (fun ω => OscDual.eval (G.Z (max t 0) ω) φ -
        OscDual.eval (G.Z (max s 0) ω) φ) 4 G.P ≤
      HRS.Contr.gK ^ (1 / 4 : ℝ) * eLpNorm (fun ω =>
        OscDual.eval (G.Z (max t 0) ω) φ - OscDual.eval (G.Z (max s 0) ω) φ) 2 G.P
    simpa only [max_eq_left hs0, max_eq_left ht0] using
      (fp81s21_wickFam_increment_L4_bound p R G s t hs0 ht0 φ hφ).2
  refine ⟨fun u => (h4 u).toLp (X u), ?_, ?_⟩
  · exact fp81s21_wickFam_L4_continuous_of_increment G.P _ X h4
      (fun u => T u (hφLp.toLp φ)) ha _
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) HRS.Contr.gK_ne_top) hb hcont
  · intro u hu
    simpa [X, max_eq_left hu] using (h4 u).coeFn_toLp

#print axioms fp81s21_wickFam_oscillator_L4_continuous
end HRS.Fp81.S21
end
