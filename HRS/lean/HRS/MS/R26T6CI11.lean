import HRS.MS.R26T6CI11PathL3
import HRS.MS.R26T6CI11CoordFTC
import HRS.MS.R26T6CI11Initial
import HRS.MS.R26T6CI11Joint
import HRS.MS.R26T6CI11Section

/-!
# R26-T6C.I11: exact continuous random initial path and L³ estimate.

All original hypotheses are retained. We prove the proposed frozen statement,
using the explicit universal constant K(T) = 4(1+T³).
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_initial_path_L3 (d : ℕ) (m T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P],
      ∀ f g : MultiIndex d → ℝ → Omega → ℝ,
      ∀ b : MultiIndex d → ℝ, (∀ alpha, 0 ≤ b alpha) →
      Summable (fun alpha => b alpha ^ 2) → (∑' alpha, b alpha ^ 2) ≤ 1 →
      ∀ A : ℝ, 0 ≤ A →
      (∀ alpha, MemLp (f alpha 0) 3 P) →
      (∀ alpha, AEStronglyMeasurable (fun z : ℝ × Omega => g alpha z.1 z.2)
        ((volume.restrict (Set.Icc 0 T)).prod P)) →
      (∀ alpha, ∀ t ∈ Set.Icc 0 T, MemLp (g alpha t) 3 P) →
      (∀ alpha, (∫ w, |f alpha 0 w| ^ 3 ∂P) ≤ (A * b alpha) ^ 3) →
      (∀ alpha, ∀ t ∈ Set.Icc 0 T,
        (∫ w, |g alpha t w| ^ 3 ∂P) ≤ (A * b alpha) ^ 3) →
      (∀ᵐ w ∂P, ∀ alpha,
        IntegrableOn (fun t => g alpha t w) (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T, f alpha t w =
          f alpha 0 w + ∫ v in Set.Icc 0 t, g alpha v w) →
      ∃ L : Omega → OscPath d m T, MemLp L 3 P ∧
        (∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ alpha,
          OscDual.coord (OscPath.at' (L w) t) alpha = f alpha t w) ∧
        (∫ w, ‖L w‖ ^ 3 ∂P) ≤ K * A ^ 3 := by
  refine ⟨4 * (1 + T ^ 3), by positivity, ?_⟩
  intro Omega msOmega P instProb f g b hb0 hb hb1 A hA hf0 hgm hgLp hfm hgBound hFTC
  let I : Omega → OscDual d m :=
    fun w => ellVec (d := d) m (fun i => f i 0 w)
  let G : ℝ × Omega → OscDual d m :=
    fun z => ellVec (d := d) m (fun i => g i z.1 z.2)
  have hInit := r26t6c_initial_ellVec_L3 m P
    (fun i w => f i 0 w) b hb0 hb hb1 A hA hf0 hfm
  have hJoint := r26t6c_interval_oscillator_derivative_L3
    m T hT P g b hb0 hb hb1 A hA hgm hgLp hgBound
  have htime : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      t ∈ Set.Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  have hsec : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      MemLp (fun w => G (t,w)) 3 P ∧
      eLpNorm (fun w => G (t,w)) 3 P ≤ ENNReal.ofReal A := by
    filter_upwards [htime] with t ht
    have h := r26t6c_derivative_section_L3 m T hT P g b hb0 hb hb1
      A hA hgLp hgBound t ht
    exact ⟨h.1, h.2.2⟩
  obtain ⟨L, hL, hLae, hLBound⟩ :=
    r26t6c_measurable_primitive_L3 T hT P I hInit.1 G hJoint.1
      A hA hInit.2.2 hsec
  have hcoord : ∀ᵐ w ∂P,
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∀ i, OscDual.coord (G (t,w)) i = g i t w :=
    r26t6c_spacetime_coordinates_swapped m
      (volume.restrict (Set.Icc 0 T)) P
      (fun i z => g i z.1 z.2) hJoint.2
  have hcoordInt :=
    r26t6c_samplewise_coord_primitive m T hT P g G hJoint.1 hcoord
  refine ⟨L, hL, ?_, hLBound⟩
  filter_upwards [hLae, hInit.2.1, hcoordInt, hFTC]
    with w hLw hIw hIntw hFTCw
  intro t i
  rw [hLw t]
  have h0 : OscDual.coord (I w) i = f i 0 w := hIw i
  have h1 : OscDual.coord
      (∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
      ∫ v in Set.Icc (0 : ℝ) (t : ℝ), g i v w := hIntw t i
  change OscDual.coord
    (I w + ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
      f i (t : ℝ) w
  rw [show OscDual.coord
      (I w + ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
      OscDual.coord (I w) i +
        OscDual.coord (∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i by rfl]
  rw [h0,h1]
  exact ((hFTCw i).2 (t : ℝ) t.2).symm

end HRS.MS.R26T6C
