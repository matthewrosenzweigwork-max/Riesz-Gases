import HRS.MS.R26T6CI11MeasPath
import HRS.MS.R26T6CI11Pathwise

/-! I11: measurable continuous oscillator path with all original FTC coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_measurable_path_FTC
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
    ∃ L : Omega → OscPath d m T,
      AEMeasurable L P ∧
      (∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
        OscDual.coord (OscPath.at' (L w) t) i = f i (t : ℝ) w) := by
  let I : Omega → OscDual d m :=
    fun w => ellVec (d := d) m (fun i => f i 0 w)
  let G : ℝ × Omega → OscDual d m :=
    fun z => ellVec (d := d) m (fun i => g i z.1 z.2)
  have hInit := r26t6c_initial_ellVec_L3 m P
    (fun i w => f i 0 w) b hb0 hb hb1 A hA hf0 hfm
  have hJoint := r26t6c_interval_oscillator_derivative_L3
    m T hT P g b hb0 hb hb1 A hA hgm hgLp hgBound
  obtain ⟨L, hLm, hLae⟩ :=
    r26t6c_measurable_oscillator_primitive m T hT P I hInit.1
      G hJoint.1
  have hcoord : ∀ᵐ w ∂P,
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∀ i, OscDual.coord (G (t,w)) i = g i t w :=
    r26t6c_spacetime_coordinates_swapped m
      (volume.restrict (Set.Icc 0 T)) P
      (fun i z => g i z.1 z.2) hJoint.2
  have hcoordInt :=
    r26t6c_samplewise_coord_primitive m T hT P g G hJoint.1 hcoord
  refine ⟨L, hLm, ?_⟩
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
