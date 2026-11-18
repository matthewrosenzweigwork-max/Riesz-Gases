import HRS.MS.MfeConfAux39

/-!
# S.B.1, packet F6 (part 2): the fixed-time cut-off inequality with a tilted reference

For a probability measure `ν` with finite second moment, `u = G_v * ν`, `Λ = log u + 1 + (H+Ψ)/θ`, a cut-off `χ`:
`∫ χ a Λ ≤ ∫ χ u (-div w - ⟨w,b⟩/θ + |w|²/θ) + N Kl² (N d v)/(4θ) - ∑_k ∫ u w_k ∂_kχ - ∑_k ∫ Λ ∂_kχ J_k`
(the Fisher information of `u` relative to the tilted reference is dropped; Young's inequality absorbs the commutator).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

/-- Integration by parts for the cross term `∫ χ u ⟨w, ℓ + w/θ⟩`. -/
theorem sb1_ibp_w [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ : ℝ} (hθ : 0 < θ)
    {b w : EucConfig d N → EucConfig d N} (hbc : Continuous b) (hw : ContDiff ℝ 1 w)
    {χ : EucConfig d N → ℝ} (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ) :
    ∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) =
      (∫ x, χ x * (p4Mol v ν x * (-(sb1div w x) - p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ))) -
        ∑ k : Fin N × Fin d, ∫ x, p4Mol v ν x * (w x k.1 k.2 * fderiv ℝ χ x (configBasis d N k)) := by
  have hu := p4m_contDiff_mol hv (ν := ν)
  have hupos := fun x => p4m_mol_pos hv hm x
  have hwc := hw.continuous
  have hwk := sb1_wcomp hw
  have hfk : ∀ k : Fin N × Fin d, ContDiff ℝ 1 (fun x => χ x * w x k.1 k.2) := fun k => hχ.mul (hwk k)
  have hsk : ∀ k : Fin N × Fin d, HasCompactSupport (fun x => χ x * w x k.1 k.2) := fun k => hχs.mul_right
  have hibp : ∀ k : Fin N × Fin d, ∫ x, χ x * w x k.1 k.2 * fderiv ℝ (p4Mol v ν) x (configBasis d N k) =
      -∫ x, fderiv ℝ (fun x => χ x * w x k.1 k.2) x (configBasis d N k) * p4Mol v ν x :=
    fun k => p4m_ibp_cs (hfk k) (hsk k) hu k
  have hder : ∀ (k : Fin N × Fin d) x, fderiv ℝ (fun x => χ x * w x k.1 k.2) x (configBasis d N k) =
      χ x * fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k) +
        w x k.1 k.2 * fderiv ℝ χ x (configBasis d N k) := by
    intro k x
    have h1 := (hχ.differentiable (by norm_num) x).hasFDerivAt
    have h2 := ((hwk k).differentiable (by norm_num) x).hasFDerivAt
    rw [(h1.fun_mul h2).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hdχ := fun k : Fin N × Fin d => p4m_cont_deriv_coord hχ k
  have hdχs := fun k : Fin N × Fin d => p4m_cs_deriv_coord hχs k
  have hdw := fun k : Fin N × Fin d => p4m_cont_deriv_coord (hwk k) k
  have hdu := fun k : Fin N × Fin d => p4m_cont_deriv_coord hu k
  have hwkc := fun k : Fin N × Fin d => (hwk k).continuous
  have huc := hu.continuous
  have hchc := hχ.continuous
  -- the pointwise decomposition
  have hpt : ∀ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
      (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) =
      ∑ k : Fin N × Fin d, (χ x * w x k.1 k.2) * fderiv ℝ (p4Mol v ν) x (configBasis d N k) +
        χ x * (p4Mol v ν x * (-p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ)) := by
    intro x
    have hu0 := (hupos x).ne'
    have e1 : ∀ k : Fin N × Fin d, p4Mol v ν x * (w x k.1 k.2 * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) =
        w x k.1 k.2 * fderiv ℝ (p4Mol v ν) x (configBasis d N k) +
          p4Mol v ν x * (-(w x k.1 k.2 * b x k.1 k.2) / θ + w x k.1 k.2 ^ 2 / θ) := by
      intro k
      rw [p4m_fderiv_mol_basis hv]
      unfold p4m_ell
      field_simp
      ring
    have hsumA : ∑ k : Fin N × Fin d, (-(w x k.1 k.2 * b x k.1 k.2) / θ + w x k.1 k.2 ^ 2 / θ) =
        -p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_neg_distrib, p4m_inner_eq,
        p4m_q_eq]
    have e2 : p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) =
        ∑ k : Fin N × Fin d, w x k.1 k.2 * fderiv ℝ (p4Mol v ν) x (configBasis d N k) +
          p4Mol v ν x * (-p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib, ← Finset.mul_sum,
        hsumA]
    rw [e2, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  -- integrability of the pieces
  have hi_a : ∀ k : Fin N × Fin d, Integrable (fun x => χ x * w x k.1 k.2 *
      fderiv ℝ (p4Mol v ν) x (configBasis d N k)) := fun k =>
    p4m_int_of_supp ((hchc.mul (hwkc k)).mul (hdu k)) hχs (fun x hx => by simp [hx])
  have hPc : Continuous (fun x => p4InnerL (w x) (b x)) := (p4m_continuous_innerL.comp hwc).clm_apply hbc
  have hQc : Continuous (fun x => p4m_q (w x)) := p4m_continuous_q.comp hwc
  have hi_b : Integrable (fun x => χ x * (p4Mol v ν x * (-p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ))) :=
    p4m_int_of_supp (hchc.mul (huc.mul (((hPc.neg).div_const θ).add (hQc.div_const θ)))) hχs
      (fun x hx => by simp [hx])
  have hi_c : ∀ k : Fin N × Fin d, Integrable (fun x => χ x * fderiv ℝ (fun y => w y k.1 k.2) x
      (configBasis d N k) * p4Mol v ν x) := fun k =>
    p4m_int_of_supp ((hchc.mul (hdw k)).mul huc) hχs (fun x hx => by simp [hx])
  have hi_d : ∀ k : Fin N × Fin d, Integrable (fun x => p4Mol v ν x * (w x k.1 k.2 *
      fderiv ℝ χ x (configBasis d N k))) := fun k =>
    p4m_int_of_supp (huc.mul ((hwkc k).mul (hdχ k))) (hdχs k) (fun x hx => by simp [hx])
  -- the integration by parts in each direction
  have hk : ∀ k : Fin N × Fin d, ∫ x, χ x * w x k.1 k.2 * fderiv ℝ (p4Mol v ν) x (configBasis d N k) =
      -(∫ x, χ x * fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k) * p4Mol v ν x) -
        ∫ x, p4Mol v ν x * (w x k.1 k.2 * fderiv ℝ χ x (configBasis d N k)) := by
    intro k
    rw [hibp k]
    have e : ∀ x, fderiv ℝ (fun x => χ x * w x k.1 k.2) x (configBasis d N k) * p4Mol v ν x =
        χ x * fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k) * p4Mol v ν x +
          p4Mol v ν x * (w x k.1 k.2 * fderiv ℝ χ x (configBasis d N k)) := by
      intro x
      rw [hder k x]
      ring
    simp_rw [e]
    rw [integral_add (hi_c k) (hi_d k)]
    ring
  -- the right-hand side
  have hdiv : ∀ x, χ x * (p4Mol v ν x * (-(sb1div w x) - p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ)) =
      -(∑ k : Fin N × Fin d, χ x * fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k) * p4Mol v ν x) +
        χ x * (p4Mol v ν x * (-p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ)) := by
    intro x
    have hs : ∑ k : Fin N × Fin d, χ x * fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k) * p4Mol v ν x =
        χ x * p4Mol v ν x * sb1div w x := by
      unfold sb1div
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hs]
    ring
  have hi_cn : Integrable (fun x => -(∑ k : Fin N × Fin d, χ x * fderiv ℝ (fun y => w y k.1 k.2) x
      (configBasis d N k) * p4Mol v ν x)) := (integrable_finset_sum _ fun k _ => hi_c k).neg
  simp_rw [hpt, hdiv]
  rw [integral_add (integrable_finset_sum _ fun k _ => hi_a k) hi_b, integral_finset_sum _ fun k _ => hi_a k,
    integral_add hi_cn hi_b, integral_neg, integral_finset_sum _ fun k _ => hi_c k]
  simp_rw [hk]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end

end HRS.MS.MfeConf
