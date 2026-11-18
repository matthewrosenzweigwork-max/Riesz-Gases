import HRS.PDE.D3PhiPAux7

/-!
# D3PHIP, helper 8: continuity in time of `Dir`, `S h^p`, `h^p log h` integrals, and measurability bridge
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

section cont

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ} {p : ℝ → ℝ}

theorem d3pp_p_cont_sub (hpc : ContinuousOn p (Set.Icc 0 T)) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => p q.1.1 :=
  hpc.comp_continuous (continuous_subtype_val.comp continuous_fst) (fun q => q.1.2)

theorem d3pp_A_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpc : ContinuousOn p (Set.Icc 0 T)) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_A κ U ψ w p q.1.1 q.2 :=
  ((d3pp_h_cont_sub hκ hU hw hψ).rpow (d3pp_p_cont_sub hpc)
    (fun q => Or.inl (d3pp_h_pos hκ hU hw hψ q).ne')).mul
    (Real.continuous_exp.comp (d3pp_m_cont_sub hκ hU hψ))

theorem d3pp_gradlogw_cont_sub (hw : D3Classical κ U T w) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => Torus.grad (fun y => Real.log (w q.1.1 y)) q.2 := by
  have e : (fun q : Set.Icc (0 : ℝ) T × Torus n => Torus.grad (fun y => Real.log (w q.1.1 y)) q.2) =
      fun q => (w q.1.1 q.2)⁻¹ • Torus.grad (w q.1.1) q.2 := funext fun q =>
    d3a_grad_log (d3a_ck2_ck1 (hw.c12.c2 q.1.1 q.1.2)) (hw.pos q.1.1 q.1.2) q.2
  rw [e]
  exact (hw.c12.continuous_f.inv₀ fun q => (hw.pos q.1.1 q.1.2 q.2).ne').smul (d3a_continuous_grad hw.c12)

theorem d3pp_Ylog_contOn (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpc : ContinuousOn p (Set.Icc 0 T)) :
    ContinuousOn (d3phi_Ylog κ U ψ w p) (Set.Icc 0 T) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  have hc := d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x)
    ((d3pp_A_cont_sub hκ hU hw hψ hpc).mul (d3pp_ell_cont_sub hκ hU hw hψ))
  exact hc.congr fun r hr => d3pp_Ylog_eq hκ hU hψ hr p

theorem d3pp_Sh_contOn (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpc : ContinuousOn p (Set.Icc 0 T)) :
    ContinuousOn (d3phi_Sh κ U ψ ψt w p) (Set.Icc 0 T) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  have hS : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n =>
      d1_gen κ (d1_gradDrift U) (ψ q.1.1) q.2 + κ * ‖Torus.grad (ψ q.1.1) q.2‖ ^ 2 - ψt q.1.1 q.2
        + d3pp_c κ U ψ ψt q.1.1 :=
    d3b_source_cont (κ := κ) hU hψ |>.add (d3pp_c_cont_sub hκ hU hT hψ)
  have hc := d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => d3pp_A κ U ψ w p r x *
      (d1_gen κ (d1_gradDrift U) (ψ r) x + κ * ‖Torus.grad (ψ r) x‖ ^ 2 - ψt r x + d3pp_c κ U ψ ψt r))
    ((d3pp_A_cont_sub hκ hU hw hψ hpc).mul hS)
  exact hc.congr fun r hr => d3pp_Sh_eq hκ hU hψ hr p

theorem d3pp_dir_contOn (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpc : ContinuousOn p (Set.Icc 0 T)) (hp1 : ∀ r ∈ Set.Icc 0 T, 1 < p r) :
    ContinuousOn (d3phi_dir κ U ψ w p) (Set.Icc 0 T) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  have hH : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n =>
      d3phi_h κ U ψ w q.1.1 q.2 ^ (p q.1.1 - 1) * w q.1.1 q.2 *
        ‖Torus.grad (fun y => Real.log (w q.1.1 y)) q.2 - Torus.grad (ψ q.1.1) q.2‖ ^ 2 :=
    (((d3pp_h_cont_sub hκ hU hw hψ).rpow ((d3pp_p_cont_sub hpc).sub continuous_const)
      (fun q => Or.inl (d3pp_h_pos hκ hU hw hψ q).ne')).mul hw.c12.continuous_f).mul
      (((d3pp_gradlogw_cont_sub hw).sub (d3a_continuous_grad hψ)).norm.pow 2)
  have hc := d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => d3phi_h κ U ψ w r x ^ (p r - 1) * w r x *
      ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2) hH
  have hpf : ContinuousOn (fun r => p r * (p r - 1) * κ) (Set.Icc 0 T) :=
    ((hpc.mul (hpc.sub continuousOn_const)).mul continuousOn_const)
  exact (hpf.mul hc).congr fun r hr =>
    d3pp_dir_eq hκ hU hw hψ hr p (by linarith [hp1 r hr])

/-- Measurability bridge: a function jointly continuous on `[0,T] × 𝕋ⁿ` is a.e.-strongly measurable for
`P ⊗ vol|_{[0,T]}`. -/
theorem d3pp_aesm {G : ℝ → Torus n → ℝ}
    (hG : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => G q.1 q.2) (P : Measure (Torus n))
    [SFinite P] :
    AEStronglyMeasurable (fun z : Torus n × ℝ => G z.2 z.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hφ : Continuous fun z : (Set.univ ×ˢ Set.Icc (0 : ℝ) T : Set (Torus n × ℝ)) =>
      ((⟨z.1.2, (z.2.2 : z.1.2 ∈ Set.Icc (0 : ℝ) T)⟩ : Set.Icc (0 : ℝ) T), z.1.1)  := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
    · exact continuous_fst.comp continuous_subtype_val
  have hco : ContinuousOn (fun z : Torus n × ℝ => G z.2 z.1) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hG.comp hφ
  have e : P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) =
      (P.prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e]
  exact hco.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Icc)

end cont

end HRS
