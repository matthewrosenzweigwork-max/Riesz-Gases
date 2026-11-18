import HRS.MS.MfeConfAux56

/-!
# S.B.1, packet F6 (part 19): the source integral converges as the mollification is removed

For a source `S` with `|S_s| ≤ C_S(s)(1+q)` and the weighted Lipschitz bound `|S_s(x) - S_s(y)| ≤ D_S(s) ‖x-y‖ (1+‖x‖+‖y‖)`:
* `sb1_cut_tendsto`: `∫ χ_R u f → ∫ u f`;
* `sb1_Fv_aesm`: `s ↦ ∫ u_s S_s` is a.e. strongly measurable;
* `sb1_src_limit`: `∫_0^t ∫ u_{w_n,s} S_s dx ds → ∫_0^t ∫ S_s dμ_s ds` as `w_n → 0`;
* `sb1_G_aesm`, `sb1_G_bound`, `sb1_S_integrable`: measurability and bounds of `s ↦ ∫ S_s dμ_s`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_cut_tendsto (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {f : EucConfig d N → ℝ} (hfc : Continuous f) {A : ℝ} (hf : ∀ x, |f x| ≤ A * (1 + p4m_q x)) :
    Tendsto (fun n : ℕ => ∫ x, p4m_chi ((n : ℝ) + 1) x * (p4Mol v ν x * f x)) atTop
      (𝓝 (∫ x, p4Mol v ν x * f x)) := by
  have hcu := p4m_cont_u hv hm (ν := ν)
  refine tendsto_integral_of_dominated_convergence (fun x => |A| * ((1 + p4m_q x) * p4Mol v ν x)) ?_
    ((p4m_integrable_q_mol hv hm).const_mul _) ?_ ?_
  · intro n
    exact ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.mul (hcu.mul hfc)).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    have hu := p4m_mol_pos hv hm x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (p4m_chi_nonneg _ _), abs_of_pos hu]
    have h1 := hf x
    have h2 := p4m_chi_le_one ((n : ℝ) + 1) x
    have h3 := p4m_chi_nonneg ((n : ℝ) + 1) x
    have h4 : A * (1 + p4m_q x) ≤ |A| * (1 + p4m_q x) :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (by have := p4m_q_nonneg x; linarith)
    calc p4m_chi ((n : ℝ) + 1) x * (p4Mol v ν x * |f x|)
        ≤ 1 * (p4Mol v ν x * (|A| * (1 + p4m_q x))) := by gcongr; exact h1.trans h4
      _ = _ := by ring
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    have hq := p4m_q_nonneg x
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [p4m_chi_eq_one (R := (n : ℝ) + 1) (by positivity) (by nlinarith), one_mul]

end

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_Fv_aesm (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) :
    AEStronglyMeasurable (fun s => ∫ x, p4Mol v (μ s) x * sb1S θ b w Wψ s x) (volume.restrict (Set.Icc 0 T)) := by
  have hSc := sb1_S_cont hP hΨ θ
  have hcu := hP.cont_u hv
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun (n : ℕ) (s : ℝ) => ∫ x,
    p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) ?_ ?_
  · intro n
    have hc : Continuous (fun p : ℝ × EucConfig d N => p4m_chi ((n : ℝ) + 1) p.2 *
        (p4Mol v (μ p.1) p.2 * sb1S θ b w Wψ p.1 p.2)) :=
      ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.comp continuous_snd).mul (hcu.mul hSc)
    exact (p4m_cont_param_cs (f := fun s x => p4m_chi ((n : ℝ) + 1) x *
      (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) hc (p4m_hasCompactSupport_chi (R := (n : ℝ) + 1) (by positivity))
      (fun s x hx => by simp [hx])).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    haveI := hP.prob s
    exact sb1_cut_tendsto hv (hP.hm s) (hSc.comp (Continuous.prodMk continuous_const continuous_id))
      (hΨ.Sg s)

theorem sb1_S_integrable (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (s : ℝ) :
    Integrable (sb1S θ b w Wψ s) (μ s) := by
  haveI := hP.prob s
  have hSc := sb1_S_cont hP hΨ θ
  have hS_s : Continuous (fun x => sb1S θ b w Wψ s x) := hSc.comp (Continuous.prodMk continuous_const continuous_id)
  refine ((hP.hm s).const_mul (CS s) |>.add (integrable_const (CS s))).mono' hS_s.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (hΨ.Sg s x).trans (le_of_eq ?_)
  simp only [Pi.add_apply]; ring

theorem sb1_G_bound (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (s : ℝ) :
    ‖∫ y, sb1S θ b w Wψ s y ∂(μ s)‖ ≤ CS s * (1 + M) := by
  haveI := hP.prob s
  have hm := hP.hm s
  have hCS := (hΨ.nn s).2.2.2
  have hgi : Integrable (fun y => CS s * (1 + p4m_q y)) (μ s) :=
    (integrable_const (1 : ℝ) |>.add hm).const_mul _
  refine (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hΨ.Sg s y
  · rw [integral_const_mul, integral_add (integrable_const _) hm]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [hP.hM s]) hCS

end

end HRS.MS.MfeConf
