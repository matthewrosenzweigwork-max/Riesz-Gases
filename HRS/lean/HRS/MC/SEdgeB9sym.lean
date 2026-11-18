import HRS.MC.SEdgeVocab
import HRS.PDE.MeanFieldAdjointFrozen

/-!
# Packet B9sym: integration by parts and symmetry of the response form (Prop 7.4 chain)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B9sym

open HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b9s_pair_sub_const {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {F : Torus d → ℝ}
    (hF : Continuous F) (c : ℝ) :
    pair (withDensityReal ρ) (fun x => F x - c) = pair (withDensityReal ρ) F - c := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have c1 : Continuous fun x => ρ x * F x := hρc.mul hF
  have c2 : Continuous fun x => ρ x * c := hρc.mul continuous_const
  rw [HRS.PDE.MFAdjoint.pair_mu hρ.density, HRS.PDE.MFAdjoint.pair_mu hρ.density]
  simp_rw [mul_sub]
  rw [integral_sub (HRS.PDE.MFAdjoint.integrable_of_cont c1)
    (HRS.PDE.MFAdjoint.integrable_of_cont c2), integral_mul_const,
    hρ.density.integral_one, one_mul]

theorem b9s_pair_projMean {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {F : Torus d → ℝ}
    (hF : Continuous F) : pair (withDensityReal ρ) (projMean (withDensityReal ρ) F) = 0 := by
  unfold projMean
  rw [b9s_pair_sub_const hρ hF]; ring

theorem b9s_pair_kop (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Continuous f) :
    pair (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) f) = 0 := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hρf : Continuous fun y => ρ y * f y := hρc.mul hf
  have hC := HRS.PDE.MFAdjoint.continuous_conv_kernel (by omega) s hs0 hsd hρf
  rw [HRS.PDE.MFAdjoint.kop_eq s hρ.density f]
  rw [b9s_pair_sub_const hρ hC]; ring

theorem b9s_pair_resp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w r : Torus d → ℝ} (hw : Continuous w)
    (hr : Continuous r)
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x) :
    pair (withDensityReal ρ) r = 0 := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hK := b9s_pair_kop hd hs0 hs hρ hr
  have hP := b9s_pair_projMean hρ hw
  have hcK : Continuous (Kop (periodicRiesz d s) (withDensityReal ρ) r) := by
    have hsd : s < d := by
      have : (0 : ℝ) ≤ d := by positivity
      linarith
    have hρr : Continuous fun y => ρ y * r y := hρc.mul hr
    have hC := HRS.PDE.MFAdjoint.continuous_conv_kernel (by omega) s hs0 hsd hρr
    rw [HRS.PDE.MFAdjoint.kop_eq s hρ.density r]
    exact hC.sub continuous_const
  have h1 : pair (withDensityReal ρ) (fun x => r x + β *
      Kop (periodicRiesz d s) (withDensityReal ρ) r x) = 0 := by
    have : (fun x => r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x) =
        projMean (withDensityReal ρ) w := funext hresp
    rw [this]; exact hP
  rw [HRS.PDE.MFAdjoint.pair_mu hρ.density] at h1 ⊢
  have c1 : Continuous fun x => ρ x * r x := hρc.mul hr
  have c2 : Continuous fun x => ρ x * (β * Kop (periodicRiesz d s) (withDensityReal ρ) r x) :=
    hρc.mul (continuous_const.mul hcK)
  simp_rw [mul_add] at h1
  rw [integral_add (HRS.PDE.MFAdjoint.integrable_of_cont c1)
    (HRS.PDE.MFAdjoint.integrable_of_cont c2)] at h1
  have h2 : ∫ x, ρ x * (β * Kop (periodicRiesz d s) (withDensityReal ρ) r x) =
      β * pair (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) r) := by
    rw [HRS.PDE.MFAdjoint.pair_mu hρ.density, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [h2, hK] at h1
  simpa using h1

theorem b9s_cont_kop (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : Torus d → ℝ} (hr : Continuous r) :
    Continuous (Kop (periodicRiesz d s) (withDensityReal ρ) r) := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hρr : Continuous fun y => ρ y * r y := hρc.mul hr
  have hC := HRS.PDE.MFAdjoint.continuous_conv_kernel (by omega) s hs0 hsd hρr
  rw [HRS.PDE.MFAdjoint.kop_eq s hρ.density r]
  exact hC.sub continuous_const

theorem b9s_l2_proj {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ r : Torus d → ℝ}
    (hφ : Continuous φ) (hr : Continuous r) (hr0 : pair (withDensityReal ρ) r = 0) :
    l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ) r =
      l2Inner (withDensityReal ρ) φ r := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  rw [HRS.PDE.MFAdjoint.pair_mu hρ.density] at hr0
  rw [HRS.PDE.MFAdjoint.l2Inner_mu hρ.density, HRS.PDE.MFAdjoint.l2Inner_mu hρ.density]
  unfold projMean
  have c1 : Continuous fun x => ρ x * (φ x * r x) := hρc.mul (hφ.mul hr)
  have c2 : Continuous fun x => ρ x * r x := hρc.mul hr
  have e : ∀ x, ρ x * ((φ x - pair (withDensityReal ρ) φ) * r x) =
      ρ x * (φ x * r x) - pair (withDensityReal ρ) φ * (ρ x * r x) := fun x => by ring
  simp_rw [e]
  rw [integral_sub (HRS.PDE.MFAdjoint.integrable_of_cont c1)
    ((HRS.PDE.MFAdjoint.integrable_of_cont c2).const_mul _), integral_const_mul, hr0]
  ring

theorem b9s_l2_resp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w r u : Torus d → ℝ} (hr : Continuous r)
    (hu : Continuous u)
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x) :
    l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) w) u =
      l2Inner (withDensityReal ρ) r u +
        β * l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) r) u := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hK := b9s_cont_kop hd hs0 hs hρ hr
  have : projMean (withDensityReal ρ) w =
      fun x => r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x := (funext hresp).symm
  rw [this, HRS.PDE.MFAdjoint.l2Inner_mu hρ.density, HRS.PDE.MFAdjoint.l2Inner_mu hρ.density,
    HRS.PDE.MFAdjoint.l2Inner_mu hρ.density]
  have c1 : Continuous fun x => ρ x * (r x * u x) := hρc.mul (hr.mul hu)
  have c2 : Continuous fun x => ρ x *
      (Kop (periodicRiesz d s) (withDensityReal ρ) r x * u x) := hρc.mul (hK.mul hu)
  have e : ∀ x, ρ x * ((r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x) * u x) =
      ρ x * (r x * u x) + β * (ρ x * (Kop (periodicRiesz d s) (withDensityReal ρ) r x * u x)) :=
    fun x => by ring
  simp_rw [e]
  rw [integral_add (HRS.PDE.MFAdjoint.integrable_of_cont c1)
    ((HRS.PDE.MFAdjoint.integrable_of_cont c2).const_mul _), integral_const_mul]

theorem b9s_part2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w φ rw rφ : Torus d → ℝ}
    (hw : Torus.IsSmooth w) (hφ : Torus.IsSmooth φ) (hrw : Torus.IsSmooth rw)
    (hrφ : Torus.IsSmooth rφ)
    (hrespw : ∀ x, rw x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rw x =
      projMean (withDensityReal ρ) w x)
    (hrespφ : ∀ x, rφ x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rφ x =
      projMean (withDensityReal ρ) φ x) :
    ∫ x, φ x * rw x ∂(withDensityReal ρ) = ∫ x, w x * rφ x ∂(withDensityReal ρ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have cw := Q66.q66_cont_of_smooth hw
  have cφ := Q66.q66_cont_of_smooth hφ
  have crw := Q66.q66_cont_of_smooth hrw
  have crφ := Q66.q66_cont_of_smooth hrφ
  have h0w := b9s_pair_resp hd hs0 hs hρ cw crw hrespw
  have h0φ := b9s_pair_resp hd hs0 hs hρ cφ crφ hrespφ
  have A := b9s_l2_resp hd hs0 hs hρ crφ crw hrespφ
  have B := b9s_l2_resp hd hs0 hs hρ crw crφ hrespw
  rw [b9s_l2_proj hρ cφ crw h0w] at A
  rw [b9s_l2_proj hρ cw crφ h0φ] at B
  have S := HRS.PDE.MFAdjoint.l2Inner_kop_symm' (by omega) s hs0 hsd ρ hρ.density hρc rφ rw crφ
    crw h0φ h0w
  have C1 := HRS.PDE.MFAdjoint.l2Inner_comm' (withDensityReal ρ) rφ rw
  have C2 := HRS.PDE.MFAdjoint.l2Inner_comm' (withDensityReal ρ)
    (Kop (periodicRiesz d s) (withDensityReal ρ) rw) rφ
  show l2Inner (withDensityReal ρ) φ rw = l2Inner (withDensityReal ρ) w rφ
  rw [A, B, C1, S, C2]

theorem b9s_part1 (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ rw : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hrw : Torus.IsSmooth rw) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * rw x)) :
    ∫ x, sed_drift v φ x ∂(withDensityReal ρ) = ∫ x, rw x * φ x ∂(withDensityReal ρ) := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hF : ∀ j, Torus.IsSmooth (fun y => ρ y * v j y) := fun j => Q66.q66_isSmooth_mul hρ.smooth (hv j)
  have hF1 : ∀ j, Torus.IsCk 1 (fun y => ρ y * v j y) := fun j => Q66.q66_isCk_of_smooth (hF j) 1
  have hφ1 : Torus.IsCk 1 φ := Q66.q66_isCk_of_smooth hφ 1
  have cφ := Q66.q66_cont_of_smooth hφ
  have crw := Q66.q66_cont_of_smooth hrw
  have cdφ : ∀ k, Continuous (Torus.partialDeriv k φ) := fun k => HRS.PDE.continuous_partialDeriv k φ hφ1
  have cdF : ∀ j, Continuous (Torus.partialDeriv j (fun y => ρ y * v j y)) :=
    fun j => HRS.PDE.continuous_partialDeriv j _ (hF1 j)
  have cF : ∀ j, Continuous (fun y => ρ y * v j y) := fun j => Q66.q66_cont_of_smooth (hF j)
  rw [integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg,
    integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg]
  have e1 : ∀ x, ρ x * sed_drift v φ x = ∑ k, (ρ x * v k x) * Torus.partialDeriv k φ x := fun x => by
    unfold sed_drift; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ x, ρ x * (rw x * φ x) =
      -(∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x * φ x) := fun x => by
    have := hdiv x
    rw [← Finset.sum_mul]; rw [this]; ring
  simp_rw [e1, e2]
  have i1 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun x => (ρ x * v k x) * Torus.partialDeriv k φ x) :=
    fun k _ => HRS.PDE.MFAdjoint.integrable_of_cont ((cF k).mul (cdφ k))
  have i2 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun x => Torus.partialDeriv k (fun y => ρ y * v k y) x * φ x) :=
    fun k _ => HRS.PDE.MFAdjoint.integrable_of_cont ((cdF k).mul cφ)
  rw [integral_finsetSum _ i1, integral_neg, integral_finsetSum _ i2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := HRS.PDE.integral_partialDeriv_mul k (fun y => ρ y * v k y) φ (hF1 k) hφ1
  linarith

theorem sed_B9sym_response_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w φ rw rφ : Torus d → ℝ}
    (hw : Torus.IsSmooth w) (hφ : Torus.IsSmooth φ) (hrw : Torus.IsSmooth rw)
    (hrφ : Torus.IsSmooth rφ) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * rw x))
    (hrespw : ∀ x, rw x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rw x =
      projMean (withDensityReal ρ) w x)
    (hrespφ : ∀ x, rφ x + β * Kop (periodicRiesz d s) (withDensityReal ρ) rφ x =
      projMean (withDensityReal ρ) φ x) :
    ∫ x, sed_drift v φ x ∂(withDensityReal ρ) = ∫ x, rw x * φ x ∂(withDensityReal ρ) ∧
      ∫ x, φ x * rw x ∂(withDensityReal ρ) = ∫ x, w x * rφ x ∂(withDensityReal ρ) :=
  ⟨b9s_part1 hd hρ hφ hrw hv hdiv, b9s_part2 hd hs0 hs hρ hw hφ hrw hrφ hrespw hrespφ⟩

end HRS.MC.SEdge.B9sym


end
