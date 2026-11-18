import HRS.Commutator.Torus.TUNITAux2
import HRS.Commutator.Torus.Layer
import HRS.Commutator.Torus.TEN2Aux1

/-!
# T-UNIT-a helpers, part 3: `commAT = 𝒞`, the decomposition and the high identity

Prefix `tunit_`.  Torus analogues of `commA_eq_Ccomm`, `Ccomm_decomp`, `high_identity` of `Whole/Unit.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-- The kernel `commKernel ∇g_≤ (v_>)` is good (bounded). -/
theorem tunit_gloPgt_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (hη1 : η ≤ 1)
    {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) : TDecGood ρ (commKernel (gloForceT s η) (PgtT η v)) := by
  obtain ⟨C, hC, hvh⟩ := vhi_bounded_T (d := d) hd
  obtain ⟨hcont, hbdd⟩ := hvh η hη hη1 v L hL hv
  obtain ⟨Bg, hBg0, hG⟩ := tunit_glo_bound hd hs0 hsd hη
  have hCL : 0 ≤ C * η * L := mul_nonneg (mul_nonneg hC.le hη.le) hL
  have hbound : ∀ x y, ‖commKernel (gloForceT s η) (PgtT η v) x y‖ ≤ 2 * (C * η * L) * Bg := by
    intro x y
    unfold commKernel
    by_cases hxy : x = y
    · rw [if_pos hxy, norm_zero]
      exact mul_nonneg (mul_nonneg two_pos.le hCL) hBg0
    · rw [if_neg hxy]
      have h1 : ‖inner ℝ (PgtT η v x - PgtT η v y) (gloForceT s η (x - y))‖ ≤
          ‖PgtT η v x - PgtT η v y‖ * ‖gloForceT s η (x - y)‖ := norm_inner_le_norm _ _
      have h2 : ‖PgtT η v x - PgtT η v y‖ ≤ 2 * (C * η * L) :=
        (norm_sub_le _ _).trans (by linarith [hbdd x, hbdd y])
      exact h1.trans (mul_le_mul h2 (hG _) (norm_nonneg _) (mul_nonneg two_pos.le hCL))
  exact tunit_good_bdd hρ (tunit_commKer_meas (tunit_glo_measurable hd hs0 hsd hη) hcont.measurable)
    (tunit_commKer_symm (fun z => by rw [tunit_glo_odd hd hsd]) (PgtT η v)) hbound

theorem tunit_commKer_split_P (F : Torus d → Euc d) (v : Torus d → Euc d) (x y : Torus d) :
    commKernel F v x y = commKernel F (PleqT η v) x y + commKernel F (PgtT η v) x y := by
  unfold commKernel
  by_cases h : x = y
  · simp [h]
  · rw [if_neg h, if_neg h, if_neg h, ← inner_add_left]
    congr 1
    simp only [PgtT]
    abel

theorem tunit_commKer_split_gh (s η : ℝ) (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (periodicRieszGrad d s) v x y =
      commKernel (ghiForceT s η) v x y + commKernel (gloForceT s η) v x y := by
  have hk : ∀ z : Torus d, periodicRieszGrad d s z = ghiForceT s η z + gloForceT s η z := fun z => by
    unfold ghiForceT; abel
  unfold commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, if_neg hxy, hk (x - y), inner_add_right]

/-- The identification `𝖠₁[X, μ, v] = 𝒞_g(v, ν)`. -/
theorem tunit_commAT_eq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Torus d → ℝ)
    (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    commAT s X ρ v = CcommT (periodicRieszGrad d s) v (chargeT X ρ) := by
  have hG := tunit_full_good hd hs0 hsd hρ hL hv
  unfold commAT CcommT
  rw [tunit_pairT_formula X hG (fun x => tunit_commKer_diag _ _ x), tunit_pair2_formula hρ hN X hG]

/-- `(5.full-decomposition)` at scale `η`. -/
theorem tunit_decomp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    CcommT (periodicRieszGrad d s) v (chargeT X ρ) =
      CcommT (ghiForceT s η) v (chargeT X ρ) + CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ) +
        CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ) := by
  have hGfull := tunit_full_good hd hs0 hsd hρ hL hv
  have hGglo := tunit_glo_good hd hs0 hsd hη hρ hL hv
  have hGp := tunit_gloPgt_good hd hs0 hsd hη hη1 hρ hL hv
  have hGg : TDecGood ρ (commKernel (ghiForceT s η) v) :=
    (hGfull.sub hGglo).congr' (fun x y => by rw [tunit_commKer_split_gh s η v x y]; ring)
  have hGq : TDecGood ρ (commKernel (gloForceT s η) (PleqT η v)) :=
    (hGglo.sub hGp).congr' (fun x y => by rw [tunit_commKer_split_P (η := η) (gloForceT s η) v x y]; ring)
  have hfun : commKernel (periodicRieszGrad d s) v = fun x y => commKernel (ghiForceT s η) v x y +
      (commKernel (gloForceT s η) (PleqT η v) x y + commKernel (gloForceT s η) (PgtT η v) x y) := by
    funext x y
    rw [tunit_commKer_split_gh s η v x y, tunit_commKer_split_P (η := η) (gloForceT s η) v x y]
  have key : CcommT (periodicRieszGrad d s) v (chargeT X ρ) = (chargeT X ρ).pair2
      (fun x y => commKernel (ghiForceT s η) v x y +
        (commKernel (gloForceT s η) (PleqT η v) x y + commKernel (gloForceT s η) (PgtT η v) x y)) := by
    unfold CcommT
    rw [hfun]
  rw [key]
  unfold CcommT
  rw [tunit_pair2_add hρ hN X hGg (hGq.add hGp), tunit_pair2_add hρ hN X hGq hGp]
  ring

/-- `(5.highidentity)` on the torus, `u = ∇g_≤ * ν`. -/
theorem tunit_high_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ) =
      (2 / (N : ℝ)) * ∑ i, inner ℝ (PgtT η v (X i)) ((chargeT X ρ).convForce (gloForceT s η) (X i)) -
        2 * ∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x) := by
  have hfin := ten2_charge_finite hN X hρ
  haveI : IsFiniteMeasure (chargeT X ρ).pos := hfin.1
  haveI : IsFiniteMeasure (chargeT X ρ).neg := hfin.2
  obtain ⟨C, hC, hvh⟩ := vhi_bounded_T (d := d) hd
  obtain ⟨hcont, hbdd⟩ := hvh η hη hη1 v L hL hv
  obtain ⟨Bg, hBg0, hG⟩ := tunit_glo_bound hd hs0 hsd hη
  have hGm := tunit_glo_measurable hd hs0 hsd hη
  have hpair := tunit_pair2_odd (chargeT X ρ) hGm (fun z => by rw [tunit_glo_odd hd hsd]) Bg hG
    hcont.measurable (C * η * L) hbdd
  have hU : StronglyMeasurable (fun x => (chargeT X ρ).convForce (gloForceT s η) x) := by
    have hjoint : StronglyMeasurable (fun q : Torus d × Torus d => gloForceT s η (q.1 - q.2)) :=
      (hGm.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact (hjoint.integral_prod_right' (ν := (chargeT X ρ).pos)).sub
      (hjoint.integral_prod_right' (ν := (chargeT X ρ).neg))
  have hf : StronglyMeasurable
      (fun x => inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)) :=
    hcont.stronglyMeasurable.inner hU
  have hbf : ∀ x, ‖inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)‖ ≤
      (C * η * L) * (Bg * ((chargeT X ρ).pos.real Set.univ + (chargeT X ρ).neg.real Set.univ)) :=
    fun x => (norm_inner_le_norm _ _).trans (mul_le_mul (hbdd x)
      (tunit_convForce_bound (chargeT X ρ) hG x) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC.le hη.le) hL))
  obtain ⟨B, hB⟩ := hρ.bdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hfρ : Integrable (fun x => ρ x *
      inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)) := by
    refine ten_integrable_of_bdd (μ := volume) (hρ.measurable.mul hf.measurable)
      (B * ((C * η * L) * (Bg * ((chargeT X ρ).pos.real Set.univ + (chargeT X ρ).neg.real Set.univ))))
      (fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (by rw [Real.norm_eq_abs]; exact hB x) (hbf x) (norm_nonneg _) hB0
  have key : (chargeT X ρ).int (fun x => inner ℝ (PgtT η v x)
        ((chargeT X ρ).convForce (gloForceT s η) x)) =
      (1 / (N : ℝ)) * ∑ i, inner ℝ (PgtT η v (X i)) ((chargeT X ρ).convForce (gloForceT s η) (X i)) -
        ∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x) :=
    tunit_charge_int ρ hρ hN X _ hf.measurable hfρ
  unfold CcommT
  rw [hpair]
  show 2 * (chargeT X ρ).int (fun x => inner ℝ (PgtT η v x)
    ((chargeT X ρ).convForce (gloForceT s η) x)) = _
  rw [key]
  ring

end HRS.Commutator.TorusNote
