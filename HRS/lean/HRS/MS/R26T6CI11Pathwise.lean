import HRS.MS.R26T6CI11CoordFTC
import HRS.MS.R26T6CI11Joint
import HRS.MS.R26T6CI11Initial
import HRS.MS.R26T6CI11SamplePath

/-!
# I11: construct an exact continuous sample path with every original FTC coordinate.
# This is a pathwise existence theorem. The remaining I11 task is a jointly
# measurable selection and its L³ moment bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_pathwise_FTC_exists
    (m T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : MultiIndex d → ℝ → Omega → ℝ)
    (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb : Summable (fun i => b i ^ 2))
    (hb1 : (∑' i, b i ^ 2) ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hf0 : ∀ i, MemLp (f i 0) 3 P)
    (hfm : ∀ i, (∫ w, |f i 0 w| ^ 3 ∂P) ≤ (A * b i) ^ 3)
    (hgm : ∀ i, AEStronglyMeasurable
      (fun z : ℝ × Omega => g i z.1 z.2)
      ((volume.restrict (Set.Icc 0 T)).prod P))
    (hgLp : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (g i t) 3 P)
    (hgBound : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ w, |g i t w| ^ 3 ∂P) ≤ (A * b i) ^ 3)
    (hFTC : ∀ᵐ w ∂P, ∀ i,
      IntegrableOn (fun t => g i t w) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T,
        f i t w = f i 0 w + ∫ v in Set.Icc 0 t, g i v w) :
    ∀ᵐ w ∂P, ∃ Lw : OscPath d m T,
      ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
        OscDual.coord (OscPath.at' Lw t) i = f i (t : ℝ) w := by
  let G : ℝ × Omega → OscDual d m :=
    fun z => ellVec (d := d) m (fun i => g i z.1 z.2)
  have hInit := r26t6c_initial_ellVec_L3 m P
    (fun i w => f i 0 w) b hb0 hb hb1 A hA hf0 hfm
  have hJoint := r26t6c_interval_oscillator_derivative_L3
    m T hT P g b hb0 hb hb1 A hA hgm hgLp hgBound
  have hcont := r26t6c_samplewise_continuous_primitive T hT P G hJoint.1
  have hcoord : ∀ᵐ w ∂P,
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∀ i, OscDual.coord (G (t,w)) i = g i t w :=
    r26t6c_spacetime_coordinates_swapped m
      (volume.restrict (Set.Icc 0 T)) P
      (fun i z => g i z.1 z.2) hJoint.2
  have hcoordInt :=
    r26t6c_samplewise_coord_primitive m T hT P g G hJoint.1 hcoord
  filter_upwards [hInit.2.1, hcont, hcoordInt, hFTC]
    with w hIw hcw hIntw hFTCw
  let Lw : OscPath d m T :=
    ⟨fun t => (ellVec (d := d) m (fun i => f i 0 w)) +
        ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w), by
      have hc : ContinuousOn (fun t : ℝ =>
          ellVec (d := d) m (fun i => f i 0 w) +
            ∫ v in Set.Icc (0 : ℝ) t, G (v,w)) (Set.Icc 0 T) :=
        (continuousOn_const : ContinuousOn
          (fun _ : ℝ => ellVec (d := d) m (fun i => f i 0 w)) (Set.Icc 0 T)).add hcw
      exact continuousOn_iff_continuous_restrict.mp hc⟩
  refine ⟨Lw, fun t i => ?_⟩
  have h0 : OscDual.coord (ellVec (d := d) m (fun i => f i 0 w)) i =
      f i 0 w := hIw i
  have h1 : OscDual.coord
      (∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
      ∫ v in Set.Icc (0 : ℝ) (t : ℝ), g i v w := hIntw t i
  change OscDual.coord
    (ellVec (d := d) m (fun i => f i 0 w) +
      ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
        f i (t : ℝ) w
  rw [show OscDual.coord
      (ellVec (d := d) m (fun i => f i 0 w) +
        ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i =
      OscDual.coord (ellVec (d := d) m (fun i => f i 0 w)) i +
        OscDual.coord (∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) i by rfl]
  rw [h0, h1]
  exact (hFTCw i).2 (t : ℝ) t.2 |>.symm

end HRS.MS.R26T6C
