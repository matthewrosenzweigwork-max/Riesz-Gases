import HRS.MS.R26T6CI11CoordSwap
import HRS.MS.R26T6CI11Sample
import HRS.MS.R26T6CI11CoordIntegral

/-!
# I11: samplewise coordinatewise Bochner FTC.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_samplewise_coord_primitive
    (m T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [SFinite P]
    (g : MultiIndex d → ℝ → Omega → ℝ)
    (G : ℝ × Omega → OscDual d m)
    (hG : MemLp G 3 ((volume.restrict (Set.Icc 0 T)).prod P))
    (hcoord : ∀ᵐ w ∂P,
      ∀ᵐ v ∂(volume.restrict (Set.Icc 0 T)),
      ∀ i, OscDual.coord (G (v,w)) i = g i v w) :
    ∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
      OscDual.coord (∫ v in Set.Icc 0 (t : ℝ), G (v,w)) i =
        ∫ v in Set.Icc 0 (t : ℝ), g i v w := by
  have hsample := r26t6c_samplewise_memLp_three
    (volume.restrict (Set.Icc 0 T)) P G hG
  filter_upwards [hsample, hcoord] with w hw hc
  intro t i
  have hsub : volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)) ≤
      volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right t.2.2) le_rfl
  have hfull : IntegrableOn (fun v => G (v,w)) (Set.Icc 0 T) :=
    hw.integrable (by norm_num)
  have hint : IntegrableOn (fun v => G (v,w)) (Set.Icc 0 (t : ℝ)) :=
    hfull.mono_set (Set.Icc_subset_Icc_right t.2.2)
  rw [r26t6c_oscCoord_integral (m := m) (t := (t : ℝ))
    (G := fun v => G (v,w)) hint i]
  have hc' : ∀ᵐ v ∂(volume.restrict (Set.Icc 0 (t : ℝ))),
      OscDual.coord (G (v,w)) i = g i v w :=
    (hc.mono (fun v hv => hv i)).filter_mono
      (Measure.absolutelyContinuous_of_le hsub).ae_le
  exact integral_congr_ae hc'

end HRS.MS.R26T6C
