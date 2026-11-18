import HRS.MS.GenPathAux37
import HRS.MS.ZeroTempAux5
import HRS.MS.GoMeasAux2
import HRS.MS.SA16Y4Wk2

/-!
# S.A.16 (SA16Y4) Tc1: pointwise time continuity of the densities and of the drift from `CoeffHypRd`

`sa16y4_mu_data`: from `CoeffHypRd` (weak continuity of `μ_r` against bounded continuous tests plus regularity) the maps
`r ↦ μ_r(y)` are continuous on `[0,T]` and `μ_r` has `RgDecay 2` with a constant independent of `r`
(`s56_rho_pointwise`, `sa11_regular_mono`).
`sa16y4_drift_pointwise`: `r ↦ meanFieldDriftW D (μ r) x j` is continuous on `[0,T]` (`s55m_conv_tendsto`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Tc1
variable {d : ℕ}

theorem sa16y4_mu_data (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {Λ T : ℝ} {μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : CoeffHypRd s m Λ T μ) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ r ∈ Icc (0 : ℝ) T, HRS.MP.RdGen.RgDecay 2 (fun _ => A) (μ r)) ∧
      ∀ y, ContinuousOn (fun r => μ r y) (Icc (0 : ℝ) T) := by
  have hreg3 := (HRS.MS.ZeroTemp.sa11_regular_mono h.regular (by omega : 3 ≤ m + 3)).1
  set A : ℝ := (d : ℝ) ^ 3 * max Λ 0 * 2 ^ ((d : ℝ) + 3) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A, hA0, fun r hr => ?_, ?_⟩
  · have hcb := hreg3 r hr
    have hcb0 : 0 ≤ HRS.cbNorm 3 (μ r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have hdec3 : HRS.MP.RdGen.RgDecay 3 (fun _ => A) (μ r) :=
      HRS.MP.RdGen.rg_rho_decay hd (r := 3) (Λ := max Λ 0) hcb.1 hcb.2.1
        (by linarith [hcb.2.2, le_max_left Λ 0])
    exact HRS.MP.RdGen.rg_decay_mono (by norm_num) hdec3
  · have hweak : ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Icc (0 : ℝ) T) := by
      intro ψ hψ hcs
      obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
      exact h.cont ψ hψ.continuous ⟨C, fun x => by simpa using hC x⟩
    exact (HRS.MS.GenPath.s56_rho_pointwise hd Λ hreg3 hweak).2

theorem sa16y4_drift_pointwise (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {A T : ℝ} (hA : 0 ≤ A)
    {μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (hdec : ∀ r ∈ Icc (0 : ℝ) T, HRS.MP.RdGen.RgDecay 2 (fun _ => A) (μ r))
    (hpt : ∀ y, ContinuousOn (fun r => μ r y) (Icc (0 : ℝ) T)) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ContinuousOn (fun r => meanFieldDriftW D (μ r) x j) (Icc (0 : ℝ) T) := by
  intro r0 hr0
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro τ hτ
  rw [tendsto_nhdsWithin_iff] at hτ
  obtain ⟨hτ1, hτ2⟩ := hτ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hτ2
  have hmem : ∀ n, τ (n + N) ∈ Icc (0 : ℝ) T := fun n => hN _ (Nat.le_add_left N n)
  have hτ1' : Tendsto (fun n => τ (n + N)) atTop (𝓝 r0) := hτ1.comp (tendsto_add_atTop_nat N)
  have hρt : ∀ y, Tendsto (fun n => μ (τ (n + N)) y) atTop (𝓝 (μ r0 y)) := fun y =>
    ((hpt y r0 hr0).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hτ1', Eventually.of_forall hmem⟩)
  have hconv : ∀ i, Tendsto (fun n => (convGradConvW (rieszKernelGrad d D.s) (μ (τ (n + N))) x) i) atTop
      (𝓝 ((convGradConvW (rieszKernelGrad d D.s) (μ r0) x) i)) := fun i =>
    HRS.MS.Go.s55m_conv_tendsto hd hs0 hsd hA (k := fun n => μ (τ (n + N))) (k₀ := μ r0)
      (fun n => hdec _ (hmem n)) (hdec _ hr0) hρt x i
  have hdr : Tendsto (fun n => meanFieldDriftW D (μ (τ (n + N))) x j) atTop
      (𝓝 (meanFieldDriftW D (μ r0) x j)) := by
    simp only [meanFieldDriftW, PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply]
    exact (tendsto_finsetSum _ fun i _ => (hconv i).const_mul _).sub tendsto_const_nhds
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n => meanFieldDriftW D (μ (τ n)) x j) N).1 hdr

end Tc1

end HRS.Whole.AppendixA.Phase2SA16R
