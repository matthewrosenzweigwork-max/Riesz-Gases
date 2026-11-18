import HRS.Uniform.Q45Lind2

/-!
# Q45: the partition step with an `ℱ₀`-measurable shift and a general pairing seminorm
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma partition_step_gen (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν)
    (ξ : Ω → ℝ^p) (hξ : StronglyMeasurable[ℱ 0] ξ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) (hadm : adm a b)
    (u : (ℝ^p) → ℝ) (hu : ContDiff ℝ 2 u) (H L Hp B0 G1 : ℝ) (hHp : 0 ≤ Hp)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤ L * ‖x - y‖)
    (hB0 : ∀ x, |u x| ≤ B0) (hG1 : ∀ x, ‖fderiv ℝ u x‖ ≤ G1)
    (hpair : ∀ x Q', |hessPair u x Q'| ≤ Hp * ν Q') :
    Integrable (fun ω => u (ξ ω + M b ω) -
      gaussSmooth u (covBlock sb a b) (ξ ω + M a ω)) P ∧
    |∫ ω, (u (ξ ω + M b ω) - gaussSmooth u (covBlock sb a b) (ξ ω + M a ω)) ∂P| ≤
      (1 / 2) * Hp * (∫ ω, (∫ σ in Set.Icc a b, ν (Sg σ ω - sb σ)) ∂P) +
      ∫ ω, taylorRem H L (M b ω - M a ω) ∂P +
      ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb a b)) := by
  classical
  set G := covBlock sb a b with hG
  set γ := multivariateGaussian (0 : ℝ^p) G with hγ
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hGpsd : G.PosSemidef := covBlock_psd hsbpsd hent ha hbt
  set v := gaussSmooth u G with hv
  obtain ⟨hv2, hvH, -⟩ := gaussSmooth_hessian G hGpsd u hu H hH
  have hvB : ∀ x, |v x| ≤ B0 := fun x => gs_abs_le hB0 G x
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hma : MemLp (M a) 2 P := hM.sq_int a ⟨ha, hab.trans hbt⟩
  have hmb : MemLp (M b) 2 P := hM.sq_int b ⟨ha.trans hab, hbt⟩
  have hca := memLp_coord P hma
  have hcb := memLp_coord P hmb
  set e : Fin p → ℝ^p := fun i => EuclideanSpace.single i (1 : ℝ) with he
  set X : Ω → ℝ^p := fun ω => ξ ω + M a ω with hX
  set Xb : Ω → ℝ^p := fun ω => ξ ω + M b ω with hXb
  have hξ0 : StronglyMeasurable[ℱ a] ξ := hξ.mono (ℱ.mono ha)
  have hξm : StronglyMeasurable ξ := hξ.mono (ℱ.le 0)
  have hmeasA : StronglyMeasurable[ℱ a] (M a) :=
    stronglyMeasurable_of_coord fun i => hM.adapted a ⟨ha, hab.trans hbt⟩ i
  have hmeasB : StronglyMeasurable[ℱ b] (M b) :=
    stronglyMeasurable_of_coord fun i => hM.adapted b ⟨ha.trans hab, hbt⟩ i
  have hmeasX : StronglyMeasurable[ℱ a] X := hξ0.add hmeasA
  have hmeasXb : StronglyMeasurable Xb := hξm.add (hmeasB.mono (ℱ.le b))
  set y : Ω → ℝ^p := fun ω => M b ω - M a ω with hy
  set Z : Fin p → Fin p → Ω → ℝ := fun i j ω => iteratedFDeriv ℝ 2 u (X ω) ![e i, e j] with hZ
  set w : Fin p → Ω → ℝ := fun i ω => fderiv ℝ u (X ω) (e i) with hw
  set T1 : Ω → ℝ := fun ω => ∑ i, w i ω * y ω i with hT1
  set T2 : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * (y ω i * y ω j) with hT2
  set T3 : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * G i j with hT3
  set T4 : Ω → ℝ := fun ω => v (X ω) - u (X ω) - (1 / 2) * T3 ω with hT4
  have hZmeas : ∀ i j, StronglyMeasurable[ℱ a] (Z i j) := by
    intro i j
    have hc : Continuous (fun x : ℝ^p => iteratedFDeriv ℝ 2 u x ![e i, e j]) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ^p) ℝ ![e i, e j]).continuous.comp
        (hu.continuous_iteratedFDeriv le_rfl)
    exact hc.comp_stronglyMeasurable hmeasX
  have hZK : ∀ i j ω, |Z i j ω| ≤ H := by
    intro i j ω
    have h1 := (iteratedFDeriv ℝ 2 u (X ω)).le_opNorm ![e i, e j]
    simp only [Fin.prod_univ_two, he, PiLp.norm_single, Matrix.cons_val_zero,
      Matrix.cons_val_one, norm_one, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hH _)
  have hwmeas : ∀ i, StronglyMeasurable[ℱ a] (w i) := by
    intro i
    have hc : Continuous (fun x : ℝ^p => fderiv ℝ u x (e i)) :=
      (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hc.comp_stronglyMeasurable hmeasX
  have hwK : ∀ i ω, |w i ω| ≤ G1 := by
    intro i ω
    have h1 := (fderiv ℝ u (X ω)).le_opNorm (e i)
    simp only [he, PiLp.norm_single, norm_one, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hG1 _)
  have hwL2 : ∀ i, MemLp (w i) 2 P := fun i =>
    MemLp.of_bound ((hwmeas i).mono (ℱ.le a)).aestronglyMeasurable G1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hwK i ω)
  have hyL2 : ∀ i, MemLp (fun ω => y ω i) 2 P := fun i => (hcb i).sub (hca i)
  have hcp := fun i j => hM.cov a b ha hab hbt hadm (Z i j) (hZmeas i j) H (hZK i j) i j
  have iT1 : Integrable T1 P := integrable_finsetSum _ fun i _ => (hwL2 i).integrable_mul (hyL2 i)
  have iT2 : Integrable T2 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).1
  have iT3 : Integrable T3 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_bdd_mul P ((hZmeas i j).mono (ℱ.le a)).aestronglyMeasurable (hZK i j)
        (integrable_const (G i j))
  have iub : Integrable (fun ω => u (Xb ω)) P :=
    Integrable.of_bound (hu.continuous.comp_aestronglyMeasurable hmeasXb.aestronglyMeasurable) B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB0 _)
  have iua : Integrable (fun ω => u (X ω)) P :=
    Integrable.of_bound (hu.continuous.comp_aestronglyMeasurable
      (hmeasX.mono (ℱ.le a)).aestronglyMeasurable) B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB0 _)
  have iva : Integrable (fun ω => v (X ω)) P :=
    Integrable.of_bound (hv2.continuous.comp_aestronglyMeasurable
      (hmeasX.mono (ℱ.le a)).aestronglyMeasurable) B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hvB _)
  have iT4 : Integrable T4 P := (iva.sub iua).sub (iT3.const_mul _)
  set c := ∫ y, taylorRem H L y ∂γ with hc
  have hT4b : ∀ ω, |T4 ω| ≤ c := fun ω => (gauss_taylor_step hu hH hL hGpsd (X ω)).2
  have hint_c : Integrable (taylorRem H L) γ := (gauss_taylor_step hu hH hL hGpsd 0).1
  set R1 : Ω → ℝ := fun ω => u (Xb ω) - u (X ω) - T1 ω - (1 / 2) * T2 ω with hR1
  have iR1 : Integrable R1 P := ((iub.sub iua).sub iT1).sub (iT2.const_mul _)
  have hR1b : ∀ ω, |R1 ω| ≤ taylorRem H L (y ω) := by
    intro ω
    have h := taylor_two_remainder u hu H L hH hL (X ω) (y ω)
    have e1 : X ω + y ω = Xb ω := by simp [hX, hXb, hy]
    have e2 : fderiv ℝ u (X ω) (y ω) = T1 ω := by
      rw [clm_expand (fderiv ℝ u (X ω)) (y ω)]
      simp only [hT1, hw, he]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e3 : iteratedFDeriv ℝ 2 u (X ω) ![y ω, y ω] = T2 ω := by
      rw [cmm_expand (iteratedFDeriv ℝ 2 u (X ω)) (y ω) (y ω)]
      simp only [hT2, hZ, he]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, e2, e3] at h
    exact h
  have hD : (fun ω => u (Xb ω) - v (X ω)) =
      fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω - (1 / 2) * T3 ω - T4 ω := by
    funext ω
    simp only [hR1, hT4]
    ring
  refine ⟨iub.sub iva, ?_⟩
  have e1 : ∫ ω, T1 ω ∂P = 0 := by
    have hi : ∀ i, ∫ ω, w i ω * y ω i ∂P = 0 := by
      intro i
      have h := (hM.orth a b ha hab hbt hadm (w i) (hwmeas i) (hwL2 i) i).symm
      have i1 : Integrable (fun ω => w i ω * M b ω i) P := (hwL2 i).integrable_mul (hcb i)
      have i0 : Integrable (fun ω => w i ω * M a ω i) P := (hwL2 i).integrable_mul (hca i)
      have hfe : (fun ω => w i ω * y ω i) = fun ω => w i ω * M b ω i - w i ω * M a ω i := by
        funext ω; simp [hy, mul_sub]
      rw [hfe, integral_sub i1 i0, h, sub_self]
    simp only [hT1]
    rw [integral_finsetSum (f := fun i ω => w i ω * y ω i) _
      (fun i _ => (hwL2 i).integrable_mul (hyL2 i))]
    exact Finset.sum_eq_zero fun i _ => hi i
  set TA : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * (∫ σ in Set.Icc a b, Sg σ ω i j) with hTA
  have iTA : Integrable TA P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).2.1
  have e2 : ∫ ω, T2 ω ∂P = ∫ ω, TA ω ∂P := by
    simp only [hT2, hTA]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).1),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).2.1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hcp i j).1),
      integral_finsetSum _ (fun j _ => (hcp i j).2.1)]
    exact Finset.sum_congr rfl fun j _ => (hcp i j).2.2
  set T : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω *
    ((∫ σ in Set.Icc a b, Sg σ ω i j) - G i j) with hT
  have hTe : T = fun ω => TA ω - T3 ω := by
    funext ω
    simp only [hT, hTA, hT3, mul_sub, Finset.sum_sub_distrib]
  have hTint : ∫ ω, T ω ∂P = (∫ ω, TA ω ∂P) - ∫ ω, T3 ω ∂P := by
    rw [hTe]; exact integral_sub iTA iT3
  have hTb : |∫ ω, T ω ∂P| ≤ Hp * ∫ ω, (∫ σ in Set.Icc a b, ν (Sg σ ω - sb σ)) ∂P := by
    have iI := Iblk_integrable_gen P ℱ hM hsbmeas hsbint hν ha hbt (c := a) (d := b)
    have hpw := pathwise_bound_gen P ℱ hM hsbmeas hsbint hsbpsd hν (c := a) (d := b) ha hbt hHp
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (iI.const_mul Hp) ?_
    filter_upwards [hpw] with ω hω
    rw [Real.norm_eq_abs]
    exact hω u hpair (X ω)
  have hintD : ∫ ω, (u (Xb ω) - v (X ω)) ∂P =
      ∫ ω, R1 ω ∂P + 0 + (1 / 2) * (∫ ω, T ω ∂P) - ∫ ω, T4 ω ∂P := by
    rw [hD]
    have j1 : Integrable (fun ω => R1 ω + T1 ω) P := iR1.add iT1
    have j2 : Integrable (fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω) P := j1.add (iT2.const_mul _)
    have j3 : Integrable (fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω - (1 / 2) * T3 ω) P :=
      j2.sub (iT3.const_mul _)
    rw [integral_sub j3 iT4, integral_sub j2 (iT3.const_mul _), integral_add j1 (iT2.const_mul _),
      integral_add iR1 iT1, integral_const_mul, integral_const_mul, e1, e2, hTint]
    ring
  have itr : Integrable (fun ω => taylorRem H L (y ω)) P := by
    refine Integrable.mono' ((((hmb.sub hma).norm.integrable_sq)).const_mul H)
      ((continuous_taylorRem H L).comp_aestronglyMeasurable
        (hmb.sub hma).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ taylorRem H L (y ω) := (abs_nonneg _).trans (hR1b ω)
    simp only [Real.norm_eq_abs, abs_of_nonneg h0]
    exact taylorRem_le_left H L _
  have b1 : |∫ ω, R1 ω ∂P| ≤ ∫ ω, taylorRem H L (y ω) ∂P := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le itr (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hR1b ω)
  have b4 : |∫ ω, T4 ω ∂P| ≤ c := by
    rw [← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := P) (C := c) (f := T4)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hT4b ω)
    simpa using this
  show |∫ ω, (u (Xb ω) - v (X ω)) ∂P| ≤ _
  rw [hintD]
  have b1' := abs_le.1 b1
  have b4' := abs_le.1 b4
  have bT := abs_le.1 hTb
  show _ ≤ _ + ∫ ω, taylorRem H L (y ω) ∂P + c
  rw [abs_le]
  constructor <;> nlinarith [b1'.1, b1'.2, b4'.1, b4'.2, bT.1, bT.2]

end HRS.Uniform.Q45
