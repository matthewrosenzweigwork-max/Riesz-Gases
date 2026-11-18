import HRS.MS.Fp81S21GaussianQuadraticHilbert13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert14_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert14_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A bounded linear history-to-correction map transports the same finite
quadratic approximations and their L⁴ convergence. -/
theorem fp81s21_TimeL2Rep_clm_L4_polynomials
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j))
    (Λ : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) →L[ℝ] B) :
    MemLp (fun ω => Λ (U ω)) 4 P ∧
    ∃ (ι : Type) (b : HilbertBasis ι ℝ
        (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))))
      (S : ℕ → Finset ι) (N : ℕ → ι → ℕ) (c : ℕ → ι → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω =>
        (∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • Λ (b s)) - Λ (U ω)) 4 P)
        atTop (𝓝 0) := by
  obtain ⟨h4, _, ι, b, S, N, c, ht⟩ :=
    fp81s21_TimeL2Rep_L4_polynomials hξ q M a H ha hH U hq hrep hcoord
  let g : ℕ → Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) :=
    fun n ω => ∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • b s
  have hgm : ∀ n, AEStronglyMeasurable (g n) P := by
    intro n
    exact Finset.aestronglyMeasurable_fun_sum _ fun s _ =>
      (memLp_quadSum hξ (c n s) (N n s)).aestronglyMeasurable.smul_const _
  have hlin : Tendsto (fun n => ∫⁻ ω, ‖g n ω - U ω‖ₑ ^ (4 : ℝ) ∂P) atTop (𝓝 0) := by
    apply (tendsto_lintegral_iff_eLpNorm (fun n => (hgm n).sub hrep.2.1.aestronglyMeasurable) (by norm_num)).2
    change Tendsto (fun n => eLpNorm (fun ω => g n ω - U ω) (ENNReal.ofReal 4) P) atTop (𝓝 0)
    simpa only [ENNReal.ofReal_ofNat, g] using ht
  have hmap := tendsto_clm_lintegral (P := P) Λ (q := 4) (by norm_num) hlin
  have hmapmeas : ∀ n, AEStronglyMeasurable (fun ω => Λ (g n ω - U ω)) P := fun n =>
    Λ.continuous.comp_aestronglyMeasurable ((hgm n).sub hrep.2.1.aestronglyMeasurable)
  have hmapLp := (tendsto_lintegral_iff_eLpNorm hmapmeas (by norm_num : (0 : ℝ) < 4)).1 hmap
  have hmapLp' : Tendsto (fun n => eLpNorm (fun ω => Λ (g n ω - U ω)) 4 P) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_ofNat] using hmapLp
  refine ⟨h4.continuousLinearMap_comp Λ, ι, b, S, N, c, ?_⟩
  refine hmapLp'.congr fun n => ?_
  congr 1
  funext ω
  simp [g, map_sub, map_sum]

#print axioms fp81s21_TimeL2Rep_clm_L4_polynomials
end HRS.Fp81.S21
end
