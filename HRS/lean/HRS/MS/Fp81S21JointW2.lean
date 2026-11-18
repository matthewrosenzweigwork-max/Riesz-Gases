import HRS.MS.Fp81S21JointW
import HRS.MS.S111BDAux1
import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21JointT2
import HRS.MS.Fp81S21WickApprox33
import HRS.MS.Fp81S21WickApprox11

/-! The selected physical Gaussian Wick operator on finite-rank kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_jointW2_measurable (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointW2_borel (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The selected half-Wick operator is the raw polynomial centered under
its own Gaussian law, at every nonnegative time. -/
theorem fp81s21_physical31_rank_center
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (u : ℝ) (hu : 0 ≤ u)
    (D : fp81s21_RankKernel p.d) :
    (S.W G u (fp81s21_rankKernelLp R D) : G.Ω → ℝ) =ᵐ[G.P]
      fp81s21_center G.P (fun ω => fp81s21_polyAt D (G.Z u ω)) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (D.u i) :=
    fun i => fp81s21_isOscTest_of_r2 D.valid i
  have hφLp : ∀ i, MemLp (D.u i) 2 μ := fun i =>
    (D.valid.smooth i).continuous.memLp_of_hasCompactSupport (D.valid.compactSupport i)
  have hk : MemLp (fp81s21_wickG_finite_rank_kernel D.u D.c) 2 (μ.prod μ) :=
    HRS.MS.R2Chaos.s94_finiteRank_memLp
      (fun i => ⟨D.valid.smooth i, D.valid.compactSupport i⟩)
  obtain ⟨hL, hJ, hW⟩ := (S.payload G).1 u hu
  have hw := fp81s21_wickFam_oscillator_finite_rank R G (S.T G u) S.Kstar
    hL hJ D.u hφ D.c hk
  have hw' : (S.W G u (fp81s21_rankKernelLp R D) : G.Ω → ℝ) =ᵐ[G.P]
      fp81s21_wickG_finite_rank_polynomial (S.T G u) D.u hφLp D.c := by
    rw [hW]
    simpa [fp81s21_rankKernelLp, fp81s21_RankKernel.kernel, μ] using hw
  let X : Fin D.n → G.Ω → ℝ := fun i ω => S.T G u ((hφLp i).toLp (D.u i)) ω
  let Q : G.Ω → ℝ := fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j * X i ω * X j ω
  have hX : ∀ i, MemLp (X i) 2 G.P := fun i => Lp.memLp _
  have hXeq : ∀ᵐ ω ∂G.P, ∀ i, X i ω = OscDual.eval (G.Z u ω) (D.u i) :=
    ae_all_iff.mpr (fun i => (S.payload G).2.1 u hu (D.u i) (hφ i) (hφLp i))
  have hQ : Q =ᵐ[G.P] (fun ω => fp81s21_polyAt D (G.Z u ω)) := by
    filter_upwards [hXeq] with ω hω
    simp [Q, fp81s21_polyAt, hω]
  have hmean := integral_congr_ae hQ
  filter_upwards [hw', hQ] with ω hwω hQω
  calc
    (S.W G u (fp81s21_rankKernelLp R D) : G.Ω → ℝ) ω =
        fp81s21_wickG_finite_rank_polynomial (S.T G u) D.u hφLp D.c ω := hwω
    _ = fp81s21_center G.P Q ω := by
      simpa [Q, X, fp81s21_wickG_finite_rank_polynomial] using
        (fp81s21_center_finite_polynomial G.P D.c X hX ω).symm
    _ = fp81s21_center G.P (fun ω => fp81s21_polyAt D (G.Z u ω)) ω := by
      simp only [fp81s21_center]
      rw [hQω, hmean]

/-- Pointwise centering of jointly measurable coefficient sections commutes
with their random time-L² classes and the Bochner mean. -/
theorem fp81s21_time_center_of_sections
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q r : ℝ → Ω → r26t6_Coeff) (M N a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hr : Measurable (Function.uncurry r))
    (ha : 0 ≤ a)
    (hsec : ∀ u, 0 ≤ u → (fun ω => q u ω) =ᵐ[P] fp81s21_center P (r u))
    (hU : fp81s21_TimeL2Rep P q M a H U)
    (hV : fp81s21_TimeL2Rep P r N a H V) :
    U =ᵐ[P] fp81s21_center P V := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  let f : ℝ × Ω → r26t6_Coeff := fun z =>
    r (a + z.1) z.2 - ∫ ω, r (a + z.1) ω ∂P
  have hg : Measurable g := hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hbar : Measurable (fun u => ∫ ω, r u ω ∂P) :=
    hr.stronglyMeasurable.integral_prod_right.measurable
  have hf : Measurable f := by
    exact (hr.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)).sub
      (hbar.comp (measurable_const.add measurable_fst))
  have hsections : ∀ᵐ t ∂dt, (fun ω => g (t, ω)) =ᵐ[P] (fun ω => f (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hsec (a + t) (by linarith [ht.1])
  have hprod := fp81s21_product_ae_of_section_ae dt P g f hg hf hsections
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae hprod
  have hωt := Measure.ae_ae_of_ae_prod hswap
  have hmean := fp81s21_TimeL2Rep_mean_section P r N a H V hr hV
  filter_upwards [hU.2.2.2, hV.2.2.2, hωt] with ω hωU hωV heq
  change U ω = V ω - ∫ ω', V ω' ∂P
  apply Lp.ext
  filter_upwards [hωU.2, hωV.2, heq, hmean, Lp.coeFn_sub (V ω) (∫ ω', V ω' ∂P)]
    with t hUt hVt hqt hmt hsub
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hUt, hVt, hmt]
  exact hqt

/-- One common Gaussian event identifies the whole raw polynomial window
with the single-time polynomials at the shifted times. -/
theorem fp81s21_polyAt_gaussian_window
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (D : fp81s21_RankKernel p.d) :
    ∀ᵐ ω ∂G.P, ∀ t : Set.Icc (0 : ℝ) H,
      fp81s21_polyAt D (G.Z (a + t) ω) =
        fp81s21_quadPoly D.c D.u
          (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) t := by
  obtain ⟨_, heval⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas
    p.d G.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ H a (a + H)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G.Z (G.evolution (a + H)) hH ha le_rfl
  filter_upwards [heval] with ω hω t
  rw [← hω t, fp81s21_polyAt_path]

/-- At each window time the selected rank output is the centered raw
window polynomial, centered with respect to the Gaussian realization. -/
theorem fp81s21_physical31_rank_center_window
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (D : fp81s21_RankKernel p.d) (t : Set.Icc (0 : ℝ) H) :
    (S.W G (a + t) (fp81s21_rankKernelLp R D) : G.Ω → ℝ) =ᵐ[G.P]
      fp81s21_center G.P (fun ω => fp81s21_quadPoly D.c D.u
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) t) := by
  have htime : 0 ≤ a + (t : ℝ) := add_nonneg ha t.property.1
  have hpoly : (fun ω => fp81s21_polyAt D (G.Z (a + t) ω)) =ᵐ[G.P]
      (fun ω => fp81s21_quadPoly D.c D.u
        (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) t) := by
    filter_upwards [fp81s21_polyAt_gaussian_window p R G a H ha hH D] with ω hω
    exact hω t
  have hmean := integral_congr_ae hpoly
  filter_upwards [fp81s21_physical31_rank_center p R Es E ε S G (a + t) htime D,
    hpoly] with ω hw hp
  simpa only [fp81s21_center, hp, hmean] using hw

#print axioms fp81s21_physical31_rank_center_window
#print axioms fp81s21_polyAt_gaussian_window
#print axioms fp81s21_physical31_rank_center
#print axioms fp81s21_time_center_of_sections
end HRS.Fp81.S21
end
