import HRS.MS.Fp81S21B6iiAssembly2
import HRS.MS.Fp81S21RawIto5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Restrict the raw compact-test Itô equation from the moving-input horizon
`a + H + p.T` to the interval needed by the vector assembly. -/
theorem fp81s21_b6ii_raw_hU2
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (Fp : FilteredParticle A)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hphys : Fp81MovingPhysicalInputs R hN A (a + H + p.T)) :
    ∀ f : Euc p.d → ℝ, IsR2Test f →
      ∀ᵐ ω ∂A.P,
        IntegrableOn (fun v => fp81s21_b6ii_physicalDrift p R N A f v ω)
          (Icc 0 (a + H)) ∧
        ∀ u ∈ Icc 0 (a + H),
          fp81s21_particleEmpField R N A u ω f =
            fp81s21_particleEmpField R N A 0 ω f +
              (∫ v in Icc 0 u, fp81s21_b6ii_physicalDrift p R N A f v ω) +
              fp81s21_b6ii_scalarNoise p E A Fp f u ω -
              fp81s21_b6ii_scalarNoise p E A Fp f 0 ω := by
  have hT : 0 < a + H + p.T := by linarith [p.hT, ha, hH]
  have htop : a + H ≤ a + H + p.T := by linarith [p.hT]
  have hsubset : Icc (0 : ℝ) (a + H) ⊆ Icc 0 (a + H + p.T) :=
    Icc_subset_Icc le_rfl htop
  intro f hf
  have hraw := fp81s21_particle_raw_compact_ito p R hN A Fp hT hphys hf
  filter_upwards [hraw] with ω hω
  refine ⟨?_, ?_⟩
  · exact hω.1.mono_set hsubset
  · intro u hu
    have hu' : u ∈ Icc (0 : ℝ) (a + H + p.T) := hsubset hu
    have heq := hω.2 u hu'
    have hItoU (v : ℝ) :
        fp81s21_particle_raw_testIto p A Fp f v ω =
          fp81s21_b6ii_scalarNoise p E A Fp f v ω := rfl
    have hnoiseEq :
        fp81s21_particleEmpField R N A u ω f =
          fp81s21_particleEmpField R N A 0 ω f +
            (∫ v in Icc 0 u,
              fp81s21_particle_raw_physicalDrift p A f v ω) +
            (fp81s21_b6ii_scalarNoise p E A Fp f u ω -
              fp81s21_b6ii_scalarNoise p E A Fp f 0 ω) := by
      calc
        _ = fp81s21_particleEmpField R N A 0 ω f +
              (∫ v in Icc 0 u,
                fp81s21_particle_raw_physicalDrift p A f v ω) +
              (fp81s21_particle_raw_testIto p A Fp f u ω -
                fp81s21_particle_raw_testIto p A Fp f 0 ω) := heq
        _ = _ := by rw [hItoU u, hItoU 0]
    have hgroup :
        fp81s21_particleEmpField R N A u ω f =
          fp81s21_particleEmpField R N A 0 ω f +
            (∫ v in Icc 0 u,
              fp81s21_particle_raw_physicalDrift p A f v ω) +
            fp81s21_b6ii_scalarNoise p E A Fp f u ω -
            fp81s21_b6ii_scalarNoise p E A Fp f 0 ω := by
      calc
        _ = fp81s21_particleEmpField R N A 0 ω f +
              (∫ v in Icc 0 u,
                fp81s21_particle_raw_physicalDrift p A f v ω) +
              (fp81s21_b6ii_scalarNoise p E A Fp f u ω -
                fp81s21_b6ii_scalarNoise p E A Fp f 0 ω) := hnoiseEq
        _ = _ := by ring
    simpa [fp81s21_particle_raw_physicalDrift,
      fp81s21_particle_raw_cN,
      fp81s21_b6ii_physicalDrift] using hgroup

#print axioms fp81s21_b6ii_raw_hU2
end HRS.Fp81.S21
end
