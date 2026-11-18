import HRS.MC.CepE6Aux1

/-!
# Packet CEPE6A, file 4: the extended force norm `‖∇Φ‖₁` (`+∞` off the open alcove) is lower semicontinuous
along sequences in the alcove

`e6a_ext z = ofReal ‖∇Φ(z)‖₁` on the open alcove and `∞` elsewhere.  If `z_j` lie in the alcove and `z_j → z`, then
`e6a_ext z ≤ liminf ofReal ‖∇Φ(z_j)‖₁` (continuity inside, blow-up of the pair forces, `cep_pair_cot_le`, at the boundary).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE6

variable {N : ℕ}

theorem e6a_continuousAt_sum {X M ι : Type*} [TopologicalSpace X] [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] (s : Finset ι) {f : ι → X → M} {x : X} (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x :=
  tendsto_finset_sum s h

/-- Extended `ℓ¹` norm of the singular force. -/
def e6a_ext (a : ℝ) (N : ℕ) (z : Ch N) : ℝ≥0∞ :=
  open Classical in
  if z ∈ cep_Alcove N then ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) z) i|) else ⊤

theorem e6a_alcove_open : IsOpen (cep_Alcove N) := by
  have h1 : IsOpen {z : Ch N | ∀ k l : Fin N, k < l → z k < z l} := by
    have : {z : Ch N | ∀ k l : Fin N, k < l → z k < z l} = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ _ : k < l, {z : Ch N | z k < z l} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun _ =>
      isOpen_lt ((EuclideanSpace.proj k).continuous) ((EuclideanSpace.proj l).continuous)
  have h2 : IsOpen {z : Ch N | ∀ k l : Fin N, z l < z k + 1} := by
    have : {z : Ch N | ∀ k l : Fin N, z l < z k + 1} = ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch N | z l < z k + 1} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l =>
      isOpen_lt ((EuclideanSpace.proj l).continuous) (((EuclideanSpace.proj k).continuous).add continuous_const)
  exact h1.inter h2

theorem e6a_measurable_ext (a : ℝ) : Measurable (e6a_ext a N) := by
  classical
  unfold e6a_ext
  refine Measurable.ite e6a_alcove_open.measurableSet ?_ measurable_const
  have hg : Measurable (gradient (cep_chamberPot a N)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Ch N)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
  refine ENNReal.measurable_ofReal.comp ?_
  exact Finset.measurable_sum _ fun i _ => ((EuclideanSpace.proj i).continuous.measurable.comp hg).abs

theorem e6a_norm_le_sum (x : Ch N) : ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => ‖x i‖) (fun _ _ => norm_nonneg _)

theorem e6a_ofReal_norm_le_ext (a : ℝ) (z : Ch N) :
    ENNReal.ofReal ‖gradient (cep_chamberPot a N) z‖ ≤ e6a_ext a N z := by
  classical
  unfold e6a_ext
  split_ifs with h
  · exact ENNReal.ofReal_le_ofReal (e6a_norm_le_sum _)
  · exact le_top

theorem e6a_hasGrad {a : ℝ} {z : Ch N} (hz : z ∈ cep_Alcove N) :
    gradient (cep_chamberPot a N) z = HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) z :=
  (e4_Phi_hasGradient fun k l hkl => ⟨by linarith [hz.1 k l hkl], by linarith [hz.2 k l]⟩).gradient

theorem e6a_pairGrad_cont {a : ℝ} {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ContinuousAt (fun w : Ch N => HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) w) z := by
  unfold HRS.MC.CepE1.cepe1_pairGrad
  refine e6a_continuousAt_sum _ fun k _ => e6a_continuousAt_sum _ fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    have hd0 : 0 < z l - z k := by linarith [hz.1 k l hkl]
    have hd1 : z l - z k < 1 := by linarith [hz.2 k l]
    have hsin : Real.sin (Real.pi * (z l - z k)) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
    have hh : ContinuousAt (HRS.MC.CepE1.cepe1_h1 a N) (z l - z k) := by
      unfold HRS.MC.CepE1.cepe1_h1
      refine continuousAt_const.mul (ContinuousAt.neg (continuousAt_const.mul ?_))
      refine ContinuousAt.div ?_ ?_ hsin
      · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    have hc2 : ContinuousAt (fun w : Ch N => HRS.MC.CepE1.cepe1_h1 a N (w l - w k)) z :=
      hh.comp (f := fun w : Ch N => w l - w k)
        (((EuclideanSpace.proj l).continuous.sub (EuclideanSpace.proj k).continuous).continuousAt)
    exact hc2.tendsto.smul_const _
  · simp only [hkl, ite_false]
    exact continuousAt_const

theorem e6a_gradnorm_cont {a : ℝ} {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ContinuousAt (fun w : Ch N => ∑ i, |(gradient (cep_chamberPot a N) w) i|) z := by
  have hev : (fun w : Ch N => ∑ i, |(gradient (cep_chamberPot a N) w) i|) =ᶠ[𝓝 z]
      fun w => ∑ i, |(HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) w) i| := by
    filter_upwards [e6a_alcove_open.mem_nhds hz] with w hw
    rw [e6a_hasGrad hw]
  refine ContinuousAt.congr ?_ hev.symm
  refine e6a_continuousAt_sum _ fun i _ => ?_
  exact ((EuclideanSpace.proj i).continuous.continuousAt.comp (e6a_pairGrad_cont hz)).abs

/-- Boundary points of the alcove have a degenerate pair. -/
theorem e6a_boundary {z : Ch N} (hc : z ∈ closure (cep_Alcove N)) (hz : z ∉ cep_Alcove N) :
    ∃ k l : Fin N, k < l ∧ (z l - z k = 0 ∨ z l - z k = 1) := by
  have hK : closure (cep_Alcove N) ⊆ {z : Ch N | (∀ k l : Fin N, k < l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1} := by
    refine closure_minimal (fun w hw => ⟨fun k l hkl => (hw.1 k l hkl).le, fun k l => (hw.2 k l).le⟩) ?_
    have h1 : IsClosed {z : Ch N | ∀ k l : Fin N, k < l → z k ≤ z l} := by
      have : {z : Ch N | ∀ k l : Fin N, k < l → z k ≤ z l} =
          ⋂ k : Fin N, ⋂ l : Fin N, ⋂ _ : k < l, {z : Ch N | z k ≤ z l} := by
        ext z; simp
      rw [this]
      exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ =>
        isClosed_le ((EuclideanSpace.proj k).continuous) ((EuclideanSpace.proj l).continuous)
    have h2 : IsClosed {z : Ch N | ∀ k l : Fin N, z l ≤ z k + 1} := by
      have : {z : Ch N | ∀ k l : Fin N, z l ≤ z k + 1} = ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch N | z l ≤ z k + 1} := by
        ext z; simp
      rw [this]
      exact isClosed_iInter fun k => isClosed_iInter fun l =>
        isClosed_le ((EuclideanSpace.proj l).continuous) (((EuclideanSpace.proj k).continuous).add continuous_const)
    exact h1.inter h2
  obtain ⟨h1, h2⟩ := hK hc
  by_contra hcon
  push_neg at hcon
  apply hz
  refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
  · refine lt_of_le_of_ne (h1 k l hkl) fun heq => ?_
    exact (hcon k l hkl).1 (by linarith)
  · refine lt_of_le_of_ne (h2 k l) fun heq => ?_
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact (hcon k l hkl).2 (by linarith)
    · linarith
    · have := h1 l k hlk
      linarith

theorem e6a_blowup {a : ℝ} (ha : 0 < a) {z : Ch N} {zs : ℕ → Ch N} (hzs : ∀ j, zs j ∈ cep_Alcove N)
    (hlim : Tendsto zs atTop (𝓝 z)) (hz : z ∉ cep_Alcove N) :
    Tendsto (fun j => ∑ i, |(gradient (cep_chamberPot a N) (zs j)) i|) atTop atTop := by
  have hc : z ∈ closure (cep_Alcove N) := mem_closure_of_tendsto hlim (Eventually.of_forall hzs)
  obtain ⟨k, l, hkl, hd⟩ := e6a_boundary hc hz
  obtain ⟨C, hC0, hC⟩ := cep_pair_cot_le ha N
  set d : ℕ → ℝ := fun j => zs j l - zs j k with hdj
  have hdlim : Tendsto d atTop (𝓝 (z l - z k)) :=
    ((EuclideanSpace.proj l).continuous.continuousAt.tendsto.comp hlim).sub
      ((EuclideanSpace.proj k).continuous.continuousAt.tendsto.comp hlim)
  have hd01 : ∀ j, 0 < d j ∧ d j < 1 := fun j =>
    ⟨by linarith [(hzs j).1 k l hkl], by linarith [(hzs j).2 k l]⟩
  -- the pair force blows up
  have hsin : Tendsto (fun j => Real.sin (Real.pi * d j)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => ?_⟩
    · have h1 : Tendsto (fun j => Real.sin (Real.pi * d j)) atTop (𝓝 (Real.sin (Real.pi * (z l - z k)))) :=
        (Real.continuous_sin.tendsto _).comp (hdlim.const_mul Real.pi)
      have h0 : Real.sin (Real.pi * (z l - z k)) = 0 := by
        rcases hd with h | h
        · rw [h]; simp
        · rw [h]; simp
      rwa [h0] at h1
    · exact Real.sin_pos_of_pos_of_lt_pi (by have := (hd01 j).1; positivity)
        (by nlinarith [Real.pi_pos, (hd01 j).2])
  have hcos : Tendsto (fun j => |Real.cos (Real.pi * d j)|) atTop (𝓝 1) := by
    have h1 : Tendsto (fun j => |Real.cos (Real.pi * d j)|) atTop (𝓝 |Real.cos (Real.pi * (z l - z k))|) :=
      ((Real.continuous_cos.tendsto _).comp (hdlim.const_mul Real.pi)).abs
    have h0 : |Real.cos (Real.pi * (z l - z k))| = 1 := by
      rcases hd with h | h
      · rw [h]; simp
      · rw [h]; simp
    rwa [h0] at h1
  have hinv : Tendsto (fun j => (Real.sin (Real.pi * d j))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hsin
  have hprod : Tendsto (fun j => (Real.sin (Real.pi * d j))⁻¹ * |Real.cos (Real.pi * d j)|) atTop atTop :=
    hinv.atTop_mul_pos one_pos hcos
  have hterm : Tendsto (fun j => |Real.pi * (Real.cos (Real.pi * (zs j l - zs j k)) /
      Real.sin (Real.pi * (zs j l - zs j k)))|) atTop atTop := by
    have := hprod.const_mul_atTop Real.pi_pos
    refine this.congr fun j => ?_
    have hs : 0 < Real.sin (Real.pi * d j) :=
      Real.sin_pos_of_pos_of_lt_pi (by have := (hd01 j).1; positivity) (by nlinarith [Real.pi_pos, (hd01 j).2])
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, abs_of_pos hs]
    simp only [hdj]
    field_simp
  rw [tendsto_atTop]
  intro M
  filter_upwards [tendsto_atTop.1 hterm (C * (M + 1) + 1)] with j hj
  have hb := (hC (zs j) (hzs j)).2 k l hkl
  by_contra hlt
  push_neg at hlt
  have hS0 : (∑ i, |(gradient (cep_chamberPot a N) (zs j)) i|) + 1 ≤ M + 1 := by linarith
  have := mul_le_mul_of_nonneg_left hS0 hC0
  linarith

theorem e6a_ext_le_liminf {a : ℝ} (ha : 0 < a) {z : Ch N} {zs : ℕ → Ch N} (hzs : ∀ j, zs j ∈ cep_Alcove N)
    (hlim : Tendsto zs atTop (𝓝 z)) :
    e6a_ext a N z ≤ liminf (fun j => ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (zs j)) i|)) atTop := by
  classical
  by_cases hz : z ∈ cep_Alcove N
  · have h1 : Tendsto (fun j => ∑ i, |(gradient (cep_chamberPot a N) (zs j)) i|) atTop
        (𝓝 (∑ i, |(gradient (cep_chamberPot a N) z) i|)) :=
      (e6a_gradnorm_cont hz).tendsto.comp hlim
    have h2 := (ENNReal.tendsto_ofReal h1).liminf_eq
    rw [h2]
    simp [e6a_ext, hz]
  · have h1 := e6a_blowup ha hzs hlim hz
    have h2 : Tendsto (fun j => ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (zs j)) i|)) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp h1
    rw [h2.liminf_eq]
    simp [e6a_ext, hz]

end HRS.MC.CepE6A
