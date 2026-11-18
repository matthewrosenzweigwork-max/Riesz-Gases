import HRS.MS.S113EndAux17

/-!
# S11.3 endpoint (worker S11X), part 18: the background energy identity `d/dt ∬ g dμ dμ = - ∬ h_u dμ dμ` at a fixed time

`s113x_A_identity`: for `A' = ∫ (D Γ + f Γ')`, `Γ = g * f`, `Γ' = g * D`, `D = div(f u)`: `A' = - ∬ h_u dμ dμ`.
Proof: the one-body identity integrated against `f`, and the integration by parts `∫ D Γ = - ∫ f ⟨u, ∇Γ⟩`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

section Slice

variable {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ}

theorem S113XSlice.D_le (S : S113XSlice f u c B M) (x : Euc d) :
    |movDiv (fun y => f y • u y) x| ≤ ((d : ℝ) * (2 * (B * M))) * Real.exp (-c * ‖x‖ ^ 2) := by
  rw [S.movDiv_flux]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k : Fin d, |fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ))|
      ≤ ∑ k : Fin d, (2 * (B * M)) * Real.exp (-c * ‖x‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
        rw [this, mul_one]
        exact S.Yk_g1 k x
    _ = ((d : ℝ) * (2 * (B * M))) * Real.exp (-c * ‖x‖ ^ 2) := by simp [mul_assoc]

theorem S113XSlice.D_cont (S : S113XSlice f u c B M) : Continuous (fun x => movDiv (fun y => f y • u y) x) := by
  have : (fun x => movDiv (fun y => f y • u y) x) = fun x =>
      ∑ k, fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ)) := funext S.movDiv_flux
  rw [this]
  exact continuous_finsetSum _ fun k _ => ((S.Yk_cd k).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem S113XSlice.nonneg_aux (S : S113XSlice f u c B M) : 0 ≤ B * M := mul_nonneg S.hB S.hM

end Slice

section Gamma

variable {s : ℝ} {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ}

theorem s113x_Gamma_hasFDerivAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (S : S113XSlice f u c B M) (x : Euc d) :
    HasFDerivAt (fun x => ∫ z, rieszKernel d s z * f (x - z)) (innerSL ℝ (movForce d s f x)) x := by
  obtain ⟨L, hL, -, -⟩ := HRS.MS.MovForce.mv1_hasFDerivAt_convFun hd hs0 hsd S.hc S.hB S.cd S.g0 S.g1 x
  have hgrad := HRS.MS.MovForce.mv1_force_eq_grad hd hs0 hsd S.hc S.hB S.cd S.g0 S.g1 x
  have hfun : (fun x => ∫ z, rieszKernel d s z * f (x - z)) = HRS.Whole.convFun (rieszKernel d s) f :=
    funext fun x => (HRS.MS.MovForce.mv1_convFun_eq _ _ x).symm
  rw [hfun]
  have : L = innerSL ℝ (movForce d s f x) := by
    rw [hL.fderiv.symm, hgrad.1]
    ext v
    rw [innerSL_apply_apply, real_inner_comm]
    exact (HRS.MS.PoisKolm.kl_inner_gradient _ x v).symm
  rw [← this]
  exact hL

theorem s113x_force_bdd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (S : S113XSlice f u c B M) :
    ∃ K : ℝ, ∀ x, ‖movForce d s f x‖ ≤ K := by
  have hB := S.hB
  have hc := S.hc
  have hΛf : ∀ y, ‖fderiv ℝ f y‖ ≤ B := fun y =>
    (S.g1 y).trans (mul_le_of_le_one_right hB (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])))
  obtain ⟨-, K, hK⟩ := HRS.MH.PairingRdP.integrable_conv_rd hd hs0 hsd (h := f) (Λ := B) (β := 1)
    S.cd.continuous.measurable (s113x_gauss_integrable hd S.hc S.cd.continuous.aestronglyMeasurable S.g0) hB
    (by linarith) (fun x z _ => by rw [Real.rpow_one]; exact s113x_lip_bound (S.cd.differentiable (by norm_num)) hΛf x z)
  exact ⟨K, hK⟩

theorem s113x_integrable_poly_gauss (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {φ : Euc d → ℝ}
    (hm : AEStronglyMeasurable φ volume) {K A0 A1 : ℝ}
    (h : ∀ x, |φ x| ≤ K * ((A0 + A1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2))) : Integrable φ := by
  refine ((s113x_poly_gauss_integrable hd hc A0 A1).const_mul K).mono' hm (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact h x

theorem s113x_ibp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (S : S113XSlice f u c B M) :
    Integrable (fun x => f x * inner ℝ (u x) (movForce d s f x)) ∧
    ∫ x, (∫ z, rieszKernel d s z * f (x - z)) * movDiv (fun y => f y • u y) x =
      -∫ x, f x * inner ℝ (u x) (movForce d s f x) := by
  have hB := S.hB
  have hM := S.hM
  have hc := S.hc
  have hBM := S.nonneg_aux
  obtain ⟨A0, A1, hA0, hA1, hbd⟩ := s113x_conv_bound hd hs0 hsd (s := s) hc
  obtain ⟨K, hK⟩ := s113x_force_bdd hd hs0 hsd S
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set Γ : Euc d → ℝ := fun x => ∫ z, rieszKernel d s z * f (x - z) with hΓ
  have hΓc : Continuous Γ := s113x_Gamma_continuous hd hs0 hsd hc hB S.cd.continuous S.g0
  have hΓb : ∀ x, |Γ x| ≤ B * (A0 + A1 * ‖x‖) := fun x => (hbd B f hB S.cd.continuous S.g0 x).2
  have hΓd : ∀ x, HasFDerivAt Γ (innerSL ℝ (movForce d s f x)) x := s113x_Gamma_hasFDerivAt hd hs0 hsd S
  have hexp : ∀ x : Euc d, 0 < Real.exp (-c * ‖x‖ ^ 2) := fun x => Real.exp_pos _
  have hnn : ∀ x : Euc d, 0 ≤ A0 + A1 * ‖x‖ := fun x => by positivity
  have hfd : ∀ k : Fin d, ∀ x, (fderiv ℝ Γ x) (EuclideanSpace.single k (1 : ℝ)) = (movForce d s f x) k := by
    intro k x
    rw [(hΓd x).fderiv, innerSL_apply_apply, s113x_inner_single]
  have hfg : ∀ k : Fin d, Integrable (fun x => Γ x * s113x_Yk f u k x) := by
    intro k
    refine s113x_integrable_poly_gauss hd hc (K := B * (B * M)) (A0 := A0) (A1 := A1)
      (hΓc.mul (S.Yk_cd k).continuous).aestronglyMeasurable fun x => ?_
    rw [abs_mul]
    calc |Γ x| * |s113x_Yk f u k x| ≤ (B * (A0 + A1 * ‖x‖)) * ((B * M) * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul (hΓb x) (S.Yk_g0 k x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hfg' : ∀ k : Fin d, Integrable (fun x => Γ x * fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ))) := by
    intro k
    refine s113x_integrable_poly_gauss hd hc (K := B * (2 * (B * M))) (A0 := A0) (A1 := A1)
      (hΓc.mul (((S.Yk_cd k).continuous_fderiv (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable fun x => ?_
    rw [abs_mul]
    have h2 : |fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ))| ≤ (2 * (B * M)) * Real.exp (-c * ‖x‖ ^ 2) := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
      rw [this, mul_one]
      exact S.Yk_g1 k x
    calc |Γ x| * |fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ))|
        ≤ (B * (A0 + A1 * ‖x‖)) * ((2 * (B * M)) * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul (hΓb x) h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hf'g : ∀ k : Fin d, Integrable (fun x => (movForce d s f x) k * s113x_Yk f u k x) := by
    intro k
    have hFm : AEStronglyMeasurable (fun x => (movForce d s f x) k) volume :=
      ((measurable_fderiv_apply_const ℝ Γ (EuclideanSpace.single k (1 : ℝ))).aestronglyMeasurable).congr
        (Filter.Eventually.of_forall (hfd k))
    refine s113x_gauss_integrable hd hc (B' := K * (B * M)) (hFm.mul (S.Yk_cd k).continuous.aestronglyMeasurable) fun x => ?_
    rw [abs_mul]
    calc |(movForce d s f x) k| * |s113x_Yk f u k x| ≤ K * ((B * M) * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul ((s113x_coord_norm_le _ k).trans (hK x)) (S.Yk_g0 k x) (abs_nonneg _) hK0
      _ = _ := by ring
  have hIk : ∀ k : Fin d, ∫ x, Γ x * fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ)) =
      -∫ x, (movForce d s f x) k * s113x_Yk f u k x := by
    intro k
    have hf'g' : Integrable (fun x => (fderiv ℝ Γ x) (EuclideanSpace.single k (1 : ℝ)) * s113x_Yk f u k x) := by
      simpa only [hfd k] using hf'g k
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := Γ) (g := s113x_Yk f u k)
      (v := EuclideanSpace.single k (1 : ℝ)) hf'g' (hfg' k) (hfg k) (fun x _ => (hΓd x).differentiableAt)
      (fun x _ => ((S.Yk_cd k).differentiable (by norm_num)) x)
    rw [this]
    simp only [hfd k]
  have hL : ∫ x, Γ x * movDiv (fun y => f y • u y) x =
      ∑ k, ∫ x, Γ x * fderiv ℝ (s113x_Yk f u k) x (EuclideanSpace.single k (1 : ℝ)) := by
    rw [← integral_finsetSum _ (fun k _ => hfg' k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [S.movDiv_flux, Finset.mul_sum]
  have hpt : ∀ x, f x * inner ℝ (u x) (movForce d s f x) = ∑ k, (movForce d s f x) k * s113x_Yk f u k x := by
    intro x
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [s113x_Yk]
    simp [mul_comm]
    ring
  have hsumint : Integrable (fun x => ∑ k, (movForce d s f x) k * s113x_Yk f u k x) :=
    integrable_finsetSum _ (fun k _ => hf'g k)
  have hR : ∫ x, f x * inner ℝ (u x) (movForce d s f x) = ∑ k, ∫ x, (movForce d s f x) k * s113x_Yk f u k x := by
    rw [← integral_finsetSum _ (fun k _ => hf'g k)]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  refine ⟨hsumint.congr (Filter.Eventually.of_forall fun x => (hpt x).symm), ?_⟩
  rw [hL, hR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => hIk k

end Gamma

section AIdentity

variable {s : ℝ} {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ}

theorem s113x_A_identity (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (S : S113XSlice f u c B M) :
    ∫ x, (movDiv (fun y => f y • u y) x * (∫ z, rieszKernel d s z * f (x - z)) +
      f x * ∫ z, rieszKernel d s z * movDiv (fun y => f y • u y) (x - z)) =
      -∫ x, ∫ y, commutatorKernel d s u x y ∂(HRS.Whole.withDensityReal f) ∂(HRS.Whole.withDensityReal f) := by
  have hB := S.hB
  have hM := S.hM
  have hc := S.hc
  have hBM := S.nonneg_aux
  obtain ⟨A0, A1, hA0, hA1, hbd⟩ := s113x_conv_bound hd hs0 hsd (s := s) hc
  obtain ⟨hFint, hibp⟩ := s113x_ibp hd hs0 hsd S
  set D : Euc d → ℝ := fun x => movDiv (fun y => f y • u y) x with hDdef
  set Γ : Euc d → ℝ := fun x => ∫ z, rieszKernel d s z * f (x - z) with hΓ
  set Γ' : Euc d → ℝ := fun x => ∫ z, rieszKernel d s z * D (x - z) with hΓ'
  have hΓc : Continuous Γ := s113x_Gamma_continuous hd hs0 hsd hc hB S.cd.continuous S.g0
  have hΓb : ∀ x, |Γ x| ≤ B * (A0 + A1 * ‖x‖) := fun x => (hbd B f hB S.cd.continuous S.g0 x).2
  have hDb : 0 ≤ (d : ℝ) * (2 * (B * M)) := by positivity
  have hΓ'c : Continuous Γ' := s113x_Gamma_continuous hd hs0 hsd hc hDb S.D_cont S.D_le
  have hΓ'b : ∀ x, |Γ' x| ≤ ((d : ℝ) * (2 * (B * M))) * (A0 + A1 * ‖x‖) := fun x =>
    (hbd _ D hDb S.D_cont S.D_le x).2
  have hnn : ∀ x : Euc d, 0 ≤ A0 + A1 * ‖x‖ := fun x => by positivity
  have hDΓ : Integrable (fun x => D x * Γ x) := by
    refine s113x_integrable_poly_gauss hd hc (K := ((d : ℝ) * (2 * (B * M))) * B) (A0 := A0) (A1 := A1)
      (S.D_cont.mul hΓc).aestronglyMeasurable fun x => ?_
    rw [abs_mul]
    calc |D x| * |Γ x| ≤ (((d : ℝ) * (2 * (B * M))) * Real.exp (-c * ‖x‖ ^ 2)) * (B * (A0 + A1 * ‖x‖)) :=
          mul_le_mul (S.D_le x) (hΓb x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hfΓ' : Integrable (fun x => f x * Γ' x) := by
    refine s113x_integrable_poly_gauss hd hc (K := B * ((d : ℝ) * (2 * (B * M)))) (A0 := A0) (A1 := A1)
      (S.cd.continuous.mul hΓ'c).aestronglyMeasurable fun x => ?_
    rw [abs_mul]
    calc |f x| * |Γ' x| ≤ (B * Real.exp (-c * ‖x‖ ^ 2)) * (((d : ℝ) * (2 * (B * M))) * (A0 + A1 * ‖x‖)) :=
          mul_le_mul (S.g0 x) (hΓ'b x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hfm : Measurable f := S.cd.continuous.measurable
  have hf0 : ∀ y, 0 ≤ f y := fun y => (S.pos y).le
  -- ∬ h
  have hinner : ∫ x, ∫ y, commutatorKernel d s u x y ∂(HRS.Whole.withDensityReal f) ∂(HRS.Whole.withDensityReal f) =
      (∫ x, f x * (inner ℝ (u x) (movForce d s f x))) - ∫ x, f x * Γ' x := by
    rw [HRS.MP.RdRem.mrr_integral_withDensityReal f hfm hf0]
    rw [← integral_sub hFint hfΓ']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * (∫ y, commutatorKernel d s u x y ∂(HRS.Whole.withDensityReal f)) = _
    rw [s113x_onebody hd hs0 hsd S x]
    ring
  rw [hinner, integral_add hDΓ hfΓ']
  have : ∫ x, D x * Γ x = -∫ x, f x * inner ℝ (u x) (movForce d s f x) := by
    rw [← hibp]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [this]
  ring

end AIdentity

end HRS.MS.S113BD

end
