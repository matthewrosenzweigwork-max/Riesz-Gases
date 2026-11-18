import HRS.MS.S21T4ProdA

/-! S2.1(iii): exact centering linearity, then the isonormal linearity of the product-Gaussian field. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_proj_linear (f g : HRS.Euc d → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (c : ℝ) :
    HRS.Whole.projMean μ (f + c • g) =
      HRS.Whole.projMean μ f + c • HRS.Whole.projMean μ g := by
  funext x
  unfold HRS.Whole.projMean HRS.Whole.pair
  have hfi : Integrable f μ := hf.integrable one_le_two
  have hgi : Integrable g μ := hg.integrable one_le_two
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    integral_add hfi (hgi.const_mul c), integral_const_mul]
  ring

/-- Six-term polarization identity, with all Bochner-integrability obligations explicit. -/
theorem s21t4_sq_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u v w : Ω → ℝ) (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hw : MemLp w 2 P) (c : ℝ) :
    (∫ ω, (u ω - v ω - c * w ω) ^ 2 ∂P) =
      (∫ ω, u ω * u ω ∂P) + (∫ ω, v ω * v ω ∂P) +
      c ^ 2 * (∫ ω, w ω * w ω ∂P) -
      2 * (∫ ω, u ω * v ω ∂P) -
      2 * c * (∫ ω, u ω * w ω ∂P) +
      2 * c * (∫ ω, v ω * w ω ∂P) := by
  have i1 : Integrable (fun ω => u ω * u ω) P := hu.integrable_mul hu
  have i2 : Integrable (fun ω => v ω * v ω) P := hv.integrable_mul hv
  have i3 : Integrable (fun ω => w ω * w ω) P := hw.integrable_mul hw
  have iuv : Integrable (fun ω => u ω * v ω) P := hu.integrable_mul hv
  have iuw : Integrable (fun ω => u ω * w ω) P := hu.integrable_mul hw
  have ivw : Integrable (fun ω => v ω * w ω) P := hv.integrable_mul hw
  have ia : Integrable (fun ω => u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω)) P :=
    (i1.add i2).add (i3.const_mul (c ^ 2))
  have ib : Integrable (fun ω => 2 * (u ω * v ω) + 2 * c * (u ω * w ω)) P :=
    (iuv.const_mul 2).add (iuw.const_mul (2 * c))
  have ie : Integrable (fun ω => 2 * c * (v ω * w ω)) P := ivw.const_mul (2 * c)
  calc
    (∫ ω, (u ω - v ω - c * w ω) ^ 2 ∂P) =
      ∫ ω, (u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω)) -
        (2 * (u ω * v ω) + 2 * c * (u ω * w ω)) + 2 * c * (v ω * w ω) ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by ring
    _ = _ := by
      have h1 : (∫ ω, (u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω)) -
         (2 * (u ω * v ω) + 2 * c * (u ω * w ω)) + 2 * c * (v ω * w ω) ∂P) =
          (∫ ω, (u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω)) -
           (2 * (u ω * v ω) + 2 * c * (u ω * w ω)) ∂P) +
          ∫ ω, 2 * c * (v ω * w ω) ∂P := by
        simpa only [Pi.add_apply, Pi.sub_apply] using integral_add (ia.sub ib) ie
      rw [h1]
      have h2 : (∫ ω, (u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω)) -
           (2 * (u ω * v ω) + 2 * c * (u ω * w ω)) ∂P) =
           (∫ ω, u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω) ∂P) -
           (∫ ω, 2 * (u ω * v ω) + 2 * c * (u ω * w ω) ∂P) := by
        simpa only [Pi.sub_apply] using integral_sub ia ib
      rw [h2]
      have h3 : (∫ ω, u ω * u ω + v ω * v ω + c ^ 2 * (w ω * w ω) ∂P) =
          (∫ ω, u ω * u ω ∂P) + (∫ ω, v ω * v ω ∂P) +
            c ^ 2 * (∫ ω, w ω * w ω ∂P) := by
        have h := integral_add (i1.add i2) (i3.const_mul (c ^ 2))
        have h' := integral_add i1 i2
        simp only [Pi.add_apply, integral_const_mul] at h
        rw [h, h']
      have h4 : (∫ ω, 2 * (u ω * v ω) + 2 * c * (u ω * w ω) ∂P) =
          2 * (∫ ω, u ω * v ω ∂P) + 2 * c * (∫ ω, u ω * w ω ∂P) := by
        simpa only [Pi.add_apply, integral_const_mul] using
          (integral_add (iuv.const_mul 2) (iuw.const_mul (2 * c)))
      rw [h3, h4, integral_const_mul]
      ring

end HRS.MS.R26T3
