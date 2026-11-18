import HRS.PDE.MovCAux1
import HRS.Equilibrium.Q84dAuxA

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_config_decomp (v : Fin N → Euc d) :
    v = ∑ k : Fin N × Fin d, v k.1 k.2 • configBasis d N k := by
  ext i j
  simp only [Finset.sum_apply, Pi.smul_apply, PiLp.smul_apply, configBasis, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply, EuclideanSpace.single_apply, Finset.sum_ite_eq]

theorem movc_measurable_clm_apply {α : Type*} [MeasurableSpace α]
    {f : α → (Fin N → Euc d) →L[ℝ] ℝ} {v : α → Fin N → Euc d} (hf : Measurable f)
    (hv : ∀ k : Fin N × Fin d, Measurable fun x => v x k.1 k.2) :
    Measurable fun x => f x (v x) := by
  have : (fun x => f x (v x)) = fun x => ∑ k : Fin N × Fin d, v x k.1 k.2 * f x (configBasis d N k) := by
    funext x
    conv_lhs => rw [movc_config_decomp (v x)]
    simp [map_sum, map_smul]
  rw [this]
  exact Finset.measurable_sum _ fun k _ => (hv k).mul (hf.apply_continuousLinearMap _)

theorem movc_convFun_measurable {g f : Torus d → ℝ} (hg : Measurable g) (hf : Measurable f) :
    Measurable (convFun g f) := by
  have : Measurable (fun p : Torus d × Torus d => g (p.1 - p.2) * f p.2) :=
    (hg.comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable


theorem movc_measurable_configRep : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
  measurable_pi_iff.2 fun i => (Q84d.q84d_measurable_rep d).comp (measurable_pi_apply i)

theorem movc_measurable_configDriftReg (D : DynData d) (M : ℝ) :
    Measurable (b15d_configDriftReg D M : Config d N → Fin N → Euc d) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold b15d_configDriftReg
  have hm : Continuous (Torus.matVec D.M) := by
    unfold Torus.matVec
    exact LinearMap.continuous_of_finiteDimensional _
  refine Measurable.sub ?_ ((Q84d.q84d_measurable_grad D.V).comp (measurable_pi_apply i))
  refine Measurable.const_smul (Finset.measurable_sum _ fun j _ => hm.measurable.comp ?_) (1 / (N : ℝ))
  exact (Q84d.q84d_measurable_grad _).comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem movc_srcReg_measurable {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (M : ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    Measurable (movT_srcReg D N M ρ ρt r) := by
  have hrep : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) := movc_measurable_configRep
  have hgc := movc_gReg_measurable (b15_one_le_d D) D.hs0 D.hsd M
  have hρc : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  have hρtc : Continuous (ρt r) := by
    have h1 := hρt.cont_time_deriv
    exact h1.comp (Continuous.prodMk (continuous_const (y := (⟨r, hr⟩ : Set.Icc (0:ℝ) T)))
      continuous_id)
  have hphit : Measurable (movT_phit D M ρ ρt r) := by
    unfold movT_phit
    exact ((movc_convFun_measurable hgc.measurable hρtc.measurable).const_mul _).add (hρtc.measurable.div hρc.measurable)
  have hpsit : Measurable (movT_psit D M ρ ρt r : Config d N → ℝ) := by
    unfold movT_psit
    exact Finset.measurable_sum _ fun i _ => hphit.comp (measurable_pi_apply i)
  unfold movT_srcReg d1_configGen
  refine ((Measurable.add ?_ ?_).add ?_).sub hpsit |>.add measurable_const
  · refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
    exact (((measurable_fderiv_apply_const ℝ (fderiv ℝ (configLift (fun _ => movT_psi D M ρ r) 0))
      (configBasis d N k)).apply_continuousLinearMap
      (configBasis d N k)).comp hrep)
  · exact movc_measurable_clm_apply ((measurable_fderiv ℝ _).comp hrep)
      (fun k => ((EuclideanSpace.proj k.2).continuous.measurable.comp
        ((measurable_pi_apply k.1).comp (movc_measurable_configDriftReg D M))))
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact (((measurable_norm).comp ((Q84d.q84d_measurable_grad _).comp (measurable_pi_apply i)))).pow_const 2

end HRS
