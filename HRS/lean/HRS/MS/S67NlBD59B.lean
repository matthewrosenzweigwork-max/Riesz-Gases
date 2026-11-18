import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD53
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD58
import HRS.MS.S67NlBD59A
import HRS.MS.S67NlBD59C
import HRS.MS.S67NlBD65

/-!
# S6.7 nonlinear, packet S6.7nl.59B: finite measurable gradient norm and singular OU gradient inequality

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4851, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
The finite `C^2` bound gives a finite order-zero gradient norm `Y_0` (measurable by packet 65,
nonnegative, bounded, dominating the pointwise gradient norms). For `t` the Duhamel remainder
`Phi = u_t - P_{nu t} u_0` is `C^1` (58), and for `v < t` the integrand `P_{nu (t-v)} F_v` is
`C^1` with gradient bound `C (1 + (t-v)^(-1/2)) (Mb Y_0(v) + MJ)` by `gradient_smoothing_cb`
(`k = 0`, zero drift); packet 53 at `K = 1` differentiates under the integral.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

lemma s67bd59b_cb0 (f : Euc d → ℝ) :
    cbNormVecE 0 (fun x => gradient f x) = ⨆ x : Euc d, ENNReal.ofReal ‖gradient f x‖ := by
  unfold cbNormVecE
  rw [Finset.sum_range_one]
  refine iSup_congr fun x => ?_
  rw [norm_iteratedFDeriv_zero]

lemma s67bd59b_Y_le (f : Euc d → ℝ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ x, ‖gradient f x‖ ≤ R) :
    cbNormVecE 0 (fun x => gradient f x) ≤ ENNReal.ofReal R := by
  rw [s67bd59b_cb0]
  exact iSup_le fun x => ENNReal.ofReal_le_ofReal (h x)

lemma s67bd59b_Y_toReal_le (f : Euc d → ℝ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ x, ‖gradient f x‖ ≤ R) :
    (cbNormVecE 0 (fun x => gradient f x)).toReal ≤ R := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (s67bd59b_Y_le f hR h)
  rwa [ENNReal.toReal_ofReal hR] at this

lemma s67bd59b_Y_ge (f : Euc d → ℝ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ x, ‖gradient f x‖ ≤ R)
    (x : Euc d) : ‖gradient f x‖ ≤ (cbNormVecE 0 (fun x => gradient f x)).toReal := by
  have hlt : cbNormVecE 0 (fun x => gradient f x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s67bd59b_Y_le f hR h)
  have h1 : ENNReal.ofReal ‖gradient f x‖ ≤ cbNormVecE 0 (fun x => gradient f x) := by
    rw [s67bd59b_cb0]; exact le_iSup (fun x => ENNReal.ofReal ‖gradient f x‖) x
  have := ENNReal.toReal_mono hlt h1
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at this

lemma s67bd59b_rpow_half (w : ℝ) (hw : 0 ≤ w) : w ^ ((-1 : ℝ) / 2) = (Real.sqrt w)⁻¹ := by
  have : (-1 : ℝ) / 2 = -(1 / 2) := by norm_num
  rw [this, Real.rpow_neg hw, ← Real.sqrt_eq_rpow]

universe u

set_option maxHeartbeats 3200000 in
theorem s67bd_slab_gradient_inequality {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : IsBrownianFiltration P ℱ W)
    (ν q : ℝ) (hν : 0 < ν) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T Mb MJ D : ℝ,
      0 ≤ T → 0 ≤ Mb → 0 ≤ MJ → 0 ≤ D →
      ∀ (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ),
      s67bd_ParabolicData ν q T u a B J → s67bd_OUDuhamel P W ν q T u B J →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖B t x‖ ≤ Mb) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, |J t x| ≤ MJ) →
      (∀ x, ‖gradient (u 0) x‖ ≤ D) →
      AEStronglyMeasurable (s67bd_Y 0 u) (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, cbNormVecE 0 (fun x => gradient (u t) x) < ⊤) ∧
      (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ s67bd_Y 0 u t) ∧
      (∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T, s67bd_Y 0 u t ≤ K) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖gradient (u t) x‖ ≤ s67bd_Y 0 u t) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun v => s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ))
          (Icc (0 : ℝ) t) volume ∧
        s67bd_Y 0 u t ≤ D + C * ∫ v in Icc (0 : ℝ) t,
          s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ) := by
  have hq' : 0 < q / ν := div_pos hq hν
  obtain ⟨Cg, cg, hCg0, hcg, hgs⟩ :=
    HRS.MS.GradSm.gradient_smoothing_cb.{u} (d := d) (q / ν) 0 hq' le_rfl 2 le_rfl 0 (by norm_num)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  refine ⟨Cg * (1 + (Real.sqrt ν)⁻¹), by positivity, ?_⟩
  intro T Mb MJ D hT hMb hMJ hD u a B J hPD hOU hB hJ hD0
  obtain ⟨K, hK⟩ := hPD.bdd_c2
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hgn : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖gradient (u t) y‖ ≤ K' := fun t ht y => by
    rw [s67bd59_gradient_norm, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (hK t ht 1 (by norm_num) y).trans (le_max_left _ _)
  have hfin : ∀ t ∈ Icc (0 : ℝ) T, cbNormVecE 0 (fun x => gradient (u t) x) < ⊤ := fun t ht =>
    lt_of_le_of_lt (s67bd59b_Y_le _ hK'0 (hgn t ht)) ENNReal.ofReal_lt_top
  have hY0 : ∀ t, 0 ≤ s67bd_Y 0 u t := fun t => ENNReal.toReal_nonneg
  have hYK : ∀ t ∈ Icc (0 : ℝ) T, s67bd_Y 0 u t ≤ K' := fun t ht =>
    s67bd59b_Y_toReal_le _ hK'0 (hgn t ht)
  have hYge : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖gradient (u t) x‖ ≤ s67bd_Y 0 u t := fun t ht x =>
    s67bd59b_Y_ge _ hK'0 (hgn t ht) x
  have hgc1 := hPD.cont_c2 1 (by norm_num)
  have hgrad : ContinuousOn (fun p : ℝ × Euc d => gradient (u p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := s67bd59_gradient_cont hgc1
  have hucont : ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := s67bd59_val_cont (hPD.cont_c2 0 (by norm_num))
  have hYmeas : AEStronglyMeasurable (s67bd_Y 0 u) (volume.restrict (Icc (0 : ℝ) T)) :=
    (s67bd_gradient_norm_measurable d 0 T hT u hucont
      (fun r hr => (hPD.c2 r hr).of_le (by norm_num)) hfin).2
  refine ⟨hYmeas, hfin, fun t _ => hY0 t, ⟨K', hYK⟩, hYge, ?_⟩
  intro t ht
  have htT : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  obtain ⟨hkint, _⟩ := s67bd59c_mass ht.1
  set Cc : ℝ := Cg * (1 + (Real.sqrt ν)⁻¹) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hYm_t : AEStronglyMeasurable (fun v => Mb * s67bd_Y 0 u v + MJ)
      (volume.restrict (Icc (0 : ℝ) t)) :=
    ((hYmeas.mono_measure (Measure.restrict_mono htT le_rfl)).const_mul Mb).add
      aestronglyMeasurable_const
  have hbd : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) t)), ‖Mb * s67bd_Y 0 u v + MJ‖ ≤ Mb * K' + MJ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hvT : v ∈ Icc (0 : ℝ) T := htT hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hY0 v; positivity)]
    have := hYK v hvT
    nlinarith
  have hI : IntegrableOn (fun v => s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ))
      (Icc (0 : ℝ) t) volume := Integrable.mul_bdd hkint hYm_t hbd
  refine ⟨hI, ?_⟩
  set Fv : ℝ → Euc d → ℝ := fun v y => inner ℝ (B v y) (gradient (u v) y) + J v y with hFv
  set G : ℝ → Euc d → ℝ := fun v x =>
    sg P W (q / ν) (fun _ => (0 : Euc d)) (ν * (t - v)) (Fv v) x with hG
  set g : ℝ → ℝ := fun v =>
    Cc * (s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ)) with hg
  have hgI : IntegrableOn g (Icc (0 : ℝ) t) volume := hI.const_mul Cc
  have hGI : ∀ x, IntegrableOn (fun v => G v x) (Icc (0 : ℝ) t) volume := by
    intro x
    have := (hOU t ht x).1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1] at this
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 this
  have hne : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) t)), v ≠ t := by
    have := (Set.countable_singleton t).ae_notMem (volume : Measure ℝ)
    exact ae_restrict_of_ae (this.mono fun v hv => by simpa using hv)
  have hae : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) t)),
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (G v) ∧ 0 ≤ g v ∧
      ∀ i, 1 ≤ i → i ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ i (G v) x‖ ≤ g v := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with v hv hvt
    have hvT : v ∈ Icc (0 : ℝ) T := htT hv
    have hτ : 0 < ν * (t - v) := mul_pos hν (sub_pos.2 (lt_of_le_of_ne hv.2 hvt))
    have hBc : Continuous fun y => B v y :=
      hPD.Bcont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hvT, mem_univ _⟩)
    have hJc : Continuous fun y => J v y :=
      hPD.Jcont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hvT, mem_univ _⟩)
    have hgc : Continuous fun y => gradient (u v) y :=
      hgrad.comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨hvT, mem_univ _⟩)
    have hFc : Continuous (Fv v) := (hBc.inner hgc).add hJc
    have hF0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (Fv v) := by
      rw [Nat.cast_zero]; exact contDiff_zero.2 hFc
    set M0 : ℝ := Mb * s67bd_Y 0 u v + MJ with hM0
    have hM00 : 0 ≤ M0 := by have := hY0 v; positivity
    have hFb : ∀ i ≤ 0, ∀ y, ‖iteratedFDeriv ℝ i (Fv v) y‖ ≤ (fun _ : ℕ => M0) i := by
      intro i hi y
      obtain rfl : i = 0 := by omega
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      have h1 : |inner ℝ (B v y) (gradient (u v) y)| ≤ Mb * s67bd_Y 0 u v :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hB v hvT y) (hYge v hvT y) (norm_nonneg _) hMb)
      have h2 := hJ v hvT y
      simp only [hM0]
      linarith
    obtain ⟨hcd, _, hbound, _⟩ := hgs P ℱ W hW (fun _ => 0) (s67bd59_zero_cb 2) (Fv v) hF0
      (fun _ => M0) hFb (ν * (t - v)) hτ
    have hsq : Real.sqrt (ν * (t - v)) = Real.sqrt ν * Real.sqrt (t - v) :=
      Real.sqrt_mul hν.le _
    have hker : s67bd_kernel 1 0 (t - v) = 1 + (Real.sqrt (t - v))⁻¹ := by
      rw [s67bd59c_ker, s67bd59b_rpow_half _ (sub_nonneg.2 hv.2)]
    have hker0 : 0 ≤ s67bd_kernel 1 0 (t - v) := s67bd_kernel_nonneg 1 0 (sub_nonneg.2 hv.2)
    refine ⟨hcd, ?_, ?_⟩
    · simp only [hg]; positivity
    · intro i hi1 hi2 x
      obtain rfl : i = 1 := le_antisymm hi2 hi1
      have hb0 := hbound 0 le_rfl x
      rw [norm_iteratedFDeriv_zero, Finset.sum_range_one] at hb0
      rw [norm_iteratedFDeriv_one, ← s67bd59_gradient_norm]
      refine hb0.trans ?_
      have ha : 0 ≤ (Real.sqrt ν)⁻¹ := inv_nonneg.2 hsν.le
      have hb : 0 ≤ (Real.sqrt (t - v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hexp : Real.exp (-cg * (ν * (t - v))) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [hτ])
      have hcomb : (1 + (Real.sqrt (ν * (t - v)))⁻¹) ≤
          (1 + (Real.sqrt ν)⁻¹) * (1 + (Real.sqrt (t - v))⁻¹) := by
        rw [hsq, mul_inv]; nlinarith [mul_nonneg ha hb]
      simp only [hg, hCc, hker]
      calc Cg * (1 + (Real.sqrt (ν * (t - v)))⁻¹) * Real.exp (-cg * (ν * (t - v))) * M0
          ≤ Cg * ((1 + (Real.sqrt ν)⁻¹) * (1 + (Real.sqrt (t - v))⁻¹)) * 1 * M0 := by
            gcongr
        _ = Cg * (1 + (Real.sqrt ν)⁻¹) * ((1 + (Real.sqrt (t - v))⁻¹) * M0) := by ring
  -- the Duhamel remainder
  have hu0 : MemCb 1 (u 0) :=
    ⟨(hPD.c2 0 hmem0).of_le (by norm_num), fun j hj =>
      ⟨K, by rintro _ ⟨y, rfl⟩; exact hK 0 hmem0 j (by omega) y⟩⟩
  obtain ⟨hS1, hSb⟩ := s67bd_ou_gradient P ℱ W hW ν q hν hq (u 0) hu0 D hD hD0 t ht.1
  set Sg : Euc d → ℝ := sg P W (q / ν) (fun _ => (0 : Euc d)) (ν * t) (u 0) with hSg
  set Φ : Euc d → ℝ := fun x => u t x - Sg x with hΦdef
  have hΦ : ∀ x, Φ x = ∫ v in Icc (0 : ℝ) t, G v x := by
    intro x
    have := (hOU t ht x).2
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
    simp only [hΦdef, hSg, hG, hFv]
    linarith
  have hΦK : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) Φ := by
    have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (u t) := (hPD.c2 t ht).of_le (by norm_num)
    have h2 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) Sg := by exact_mod_cast hS1
    exact h1.sub h2
  obtain ⟨_, h53⟩ := s67bd_param_deriv_ae d 1 le_rfl t ht.1 G g hGI hgI hae Φ hΦ hΦK
  have hint_nonneg : 0 ≤ ∫ v in Icc (0 : ℝ) t,
      s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ) := by
    refine setIntegral_nonneg measurableSet_Icc (fun v hv => ?_)
    exact mul_nonneg (s67bd_kernel_nonneg 1 0 (sub_nonneg.2 hv.2))
      (by have := hY0 v; positivity)
  have hRnn : 0 ≤ D + Cc * ∫ v in Icc (0 : ℝ) t,
      s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ) := by positivity
  refine s67bd59b_Y_toReal_le _ hRnn (fun x => ?_)
  have hdiffΦ : DifferentiableAt ℝ Φ x := (hΦK.differentiable (by norm_num)) x
  have hdiffS : DifferentiableAt ℝ Sg x := (hS1.differentiable (by norm_num)) x
  have hdec : (fun y => Φ y + Sg y) = u t := by
    funext y; simp only [hΦdef]; ring
  have hfd : fderiv ℝ (u t) x = fderiv ℝ Φ x + fderiv ℝ Sg x := by
    rw [← hdec]; exact fderiv_add hdiffΦ hdiffS
  rw [s67bd59_gradient_norm, hfd]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖fderiv ℝ Φ x‖ ≤ ∫ v in Icc (0 : ℝ) t, g v := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact h53 1 le_rfl le_rfl x
  have h2 : ‖fderiv ℝ Sg x‖ ≤ D := by
    rw [← s67bd59_gradient_norm]
    refine (hSb x).trans ?_
    exact mul_le_of_le_one_left hD (Real.exp_le_one_iff.2 (by nlinarith [ht.1]))
  have h3 : ∫ v in Icc (0 : ℝ) t, g v = Cc * ∫ v in Icc (0 : ℝ) t,
      s67bd_kernel 1 0 (t - v) * (Mb * s67bd_Y 0 u v + MJ) := integral_const_mul _ _
  linarith

end HRS.MS.BreakdownS67
