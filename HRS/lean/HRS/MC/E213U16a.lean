import HRS.MC.E213U10P
import HRS.MC.E213U13o

/-!
# Packet e213u16, part a: `gaussian_rs_exists`

Pathwise, for a.e. `ω`, the Riemann--Stieltjes sums of the Gaussian limit objects converge: the drift coefficient
`ℬ^v(ω)` is `L²` (hence `L¹`) on `[0,a+T]`, the field `η` is continuous on every `[0,N]`, and the existence results of
`E213U7` apply.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11

variable {d : ℕ}

section RS

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- A.s. the limit field is continuous on all of `[0,∞)`. -/
theorem u16_eta_cont_Ici : ∀ᵐ ω ∂gd.P₀, ContinuousOn (fun t => gd.η t ω) (Set.Ici 0) := by
  have h : ∀ᵐ ω ∂gd.P₀, ∀ N : ℕ, ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (N : ℝ)) :=
    ae_all_iff.2 fun N => u11_eta_cont gd (N : ℝ)
  filter_upwards [h] with ω hω
  intro x hx
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have h1 : ContinuousWithinAt (fun t => gd.η t ω) (Set.Icc 0 (N : ℝ)) x := hω N x ⟨hx, hN.le⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Set.Iio (N : ℝ), isOpen_Iio, hN, ?_⟩
  intro y hy
  exact ⟨hy.2, hy.1.le⟩

theorem u16_nearCoef0_measurable {r : ℝ} {f : ℝ → NegSobolev d r} (hf : ContinuousOn f (Set.Ici 0)) :
    Measurable (nearCoef 0 f) := by
  have hg : Continuous fun v : ℝ => f (max v 0) :=
    hf.comp_continuous (continuous_id.max continuous_const) (fun v => le_max_right v 0)
  have : nearCoef 0 f = fun v => if 0 ≤ v then f (max v 0) else 0 := by
    funext v
    unfold nearCoef
    by_cases h : 0 ≤ v
    · simp [h, max_eq_left h]
    · simp [h]
  rw [this]
  exact Measurable.ite measurableSet_Ici hg.measurable measurable_const

theorem gaussian_rs_exists_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    ∀ᵐ ω ∂gd.P₀,
      IsRS (a + T)
        (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
          (fun u u' => winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u u'))
        (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (fun v => NegSobolev.embed m (gd.B v ω))) ∧
      IsRS (a + T)
        (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
          (fun u u' => winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u')))
        (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (fun v => NegSobolev.embed m (gd.η v ω))) := by
  have hH : 0 < a + T := by linarith
  have hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  filter_upwards [u11_B_integrable gd (a + T) hH, u16_eta_cont_Ici gd, u11_eta_cont gd (a + T)] with ω hBi hηc hηc'
  set w := gd.Zwin (a + T) 0 ω with hw
  have hY := HRS.MC.E213U7.e213u7_Y_cont hE T hT a ha w
  refine ⟨?_, ?_⟩
  · have hA := HRS.MC.E213U7.e213u7_fderiv_cont hE T a ha Φ hreg
      (fun τ => winPred (regime S β₀ hE) m T a ha w τ) hY
    have hlp : MemLp (fun v => NegSobolev.embed m (gd.B v ω)) 1 (volume.restrict (Set.Icc (0 : ℝ) (a + T))) :=
      HRS.MC.E213U7.e213u7_memLp_embed hE (a + T) (u11_B_nearCoef_measurable gd ω) hBi (fun v => le_rfl)
    obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_drift_exists hE T hT a ha _ hA _ hlp
    have hr : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (gd.B v ω)) = I :=
      HRS.MC.E213U7.e213u7_rsLim_eq hH hI
    rw [hr]
    exact hI
  · have hM := HRS.MC.E213U7.e213u7_iFD_cont hE T a ha Φ hreg
      (fun τ => winPred (regime S β₀ hE) m T a ha w τ) hY 2 le_rfl
    have hcpt : IsCompact (Set.Icc (0 : ℝ) (a + T)) := isCompact_Icc
    obtain ⟨K, hK⟩ := hcpt.exists_bound_of_continuousOn hηc'
    obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_J_exists hE T hT a ha _ hM
      (fun v => NegSobolev.embed m (gd.η v ω)) (nearCoef 0 (fun v => gd.η v ω))
      (fun v hv => by rw [HRS.MC.E213U7.e213u7_nc0_apply _ hv])
      (u16_nearCoef0_measurable hηc) K
      (fun u hu => by rw [HRS.MC.E213U7.e213u7_nc0_apply _ hu.1]; exact hK u hu)
    have hr : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (gd.η v ω)) = I :=
      HRS.MC.E213U7.e213u7_rsLim_eq hH hI
    rw [hr]
    exact hI

end RS

end HRS.MC.E213U16

end
