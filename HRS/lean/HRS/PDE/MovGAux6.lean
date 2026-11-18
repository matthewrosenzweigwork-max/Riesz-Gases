import HRS.PDE.MovGAux5

/-!
# MOVG Aux6: the time-slice identity `∫ q T = βN ∫ q C_N`

Pair algebra (oddness of `∇g`), the expansion of `C_N = movT_commAt` through `ob`, and the combination of the
Q-IBP identity (Aux3) with the one-body identity (Aux5).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `p(x,y) = ⟨u(x), ∇g(x-y)⟩`. -/
def movg_p (D : DynData d) (ρ : Torus d → ℝ) (x y : Torus d) : ℝ :=
  ∑ l, (mfeTransport D ρ x).ofLp l * (periodicRieszGrad d D.s (x - y)).ofLp l

theorem movg_commKernel_eq (D : DynData d) (ρ : Torus d → ℝ) {x y : Torus d} (hxy : x ≠ y) :
    commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) x y = movg_p D ρ x y + movg_p D ρ y x := by
  unfold commKernel movg_p
  rw [if_neg hxy, mova_inner_eq_sum]
  have hneg : periodicRieszGrad d D.s (y - x) = -periodicRieszGrad d D.s (x - y) := by
    rw [← neg_sub, PDE.periodicRieszGrad_neg D.hsd]
  rw [hneg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [PiLp.sub_apply, PiLp.neg_apply]
  ring

theorem movg_sum_erase_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    ∑ i, ∑ k ∈ Finset.univ.erase i, F i k = ∑ i, ∑ k ∈ Finset.univ.erase i, F k i := by
  refine Finset.sum_comm' ?_
  intro i k
  simp [Finset.mem_erase, eq_comm]

theorem movg_commAt_expand (D : DynData d) {ρ : Torus d → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (X : Config d N) :
    movT_commAt D N ρ X = (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) (X i) (X j) -
      (1 / (N : ℝ)) * ∑ i, movg_ob D ρ (X i) + (1 / 2) * ∫ x, ρ x * movg_ob D ρ x := by
  unfold movT_commAt modulatedEnergy
  simp_rw [PDE.MFPairing.integral_withDensityReal hρc.measurable hρ0]
  rfl

theorem movg_bracket (D : DynData d) {ρ : Torus d → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (β : ℝ) {n : ℕ} (X : Config d (n + 1)) (hX : ∀ i k, i ≠ k → X i ≠ X k)
    (G' : Torus d → ℝ)
    (hOB : ∀ x, G' x = ∑ j, (mfeTransport D ρ x).ofLp j *
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j - movg_ob D ρ x) :
    (∑ i, ∑ j, (mfeTransport D ρ (X i)).ofLp j * ((β / ((n + 1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        β * (convGradConv (periodicRieszGrad d D.s) ρ (X i)).ofLp j)) +
      (∑ i, β * G' (X i)) + (β * ((n + 1 : ℕ) : ℝ) / 2) * ∫ x, ρ x * movg_ob D ρ x =
    β * ((n + 1 : ℕ) : ℝ) * movT_commAt D (n + 1) ρ X := by
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hN0 : Nr ≠ 0 := by rw [hNr]; positivity
  rw [movg_commAt_expand D hρc hρ0 X]
  set P : ℝ := ∑ i, ∑ k ∈ Finset.univ.erase i, movg_p D ρ (X i) (X k) with hP
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i,
      commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) (X i) (X j) = 2 * P := by
    have : ∀ i, ∑ j ∈ Finset.univ.erase i,
        commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ) (X i) (X j) =
        ∑ j ∈ Finset.univ.erase i, (movg_p D ρ (X i) (X j) + movg_p D ρ (X j) (X i)) := by
      intro i
      refine Finset.sum_congr rfl fun j hj => ?_
      exact movg_commKernel_eq D ρ (hX i j (Ne.symm (Finset.ne_of_mem_erase hj)))
    simp_rw [this, Finset.sum_add_distrib]
    rw [← hP, movg_sum_erase_comm (fun i k => movg_p D ρ (X k) (X i))]
    ring
  have hper : ∀ i, ∑ j, (mfeTransport D ρ (X i)).ofLp j * ((β / Nr) *
        ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        β * (convGradConv (periodicRieszGrad d D.s) ρ (X i)).ofLp j) =
      (β / Nr) * ∑ k ∈ Finset.univ.erase i, movg_p D ρ (X i) (X k) -
        β * ∑ j, (mfeTransport D ρ (X i)).ofLp j * (convGradConv (periodicRieszGrad d D.s) ρ (X i)).ofLp j := by
    intro i
    unfold movg_p
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hper, hOB, h1]
  simp only [← hNr]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [← hP]
  field_simp
  ring

theorem movg_ae_noCollision (hd : 1 ≤ d) :
    ∀ᵐ X ∂(volume : Measure (Config d N)), ∀ i k, i ≠ k → X i ≠ X k := by
  filter_upwards [b15_ae_not_collision (d := d) (N := N) hd] with X hX i k hik h
  exact hX ⟨i, k, hik, h⟩

/-- The time-slice identity `∫ q T = βN ∫ q C_N` (unnormalised Gibbs density `q`). -/
theorem movg_time_identity (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) (n : ℕ) :
    ∫ X : Config d (n + 1), movg_q d D.s (D.invβ⁻¹ / ((n + 1 : ℕ) : ℝ))
        (fun x => ρ x * Real.exp (D.invβ⁻¹ * convFun (periodicRiesz d D.s) ρ x)) X *
      ((∑ i, (mova_pdeRHS D ρ (X i) / ρ (X i) +
          D.invβ⁻¹ * convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) (X i))) +
        (D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * ∫ x, ρ x * movg_ob D ρ x) =
    D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) * ∫ X : Config d (n + 1), movg_q d D.s (D.invβ⁻¹ / ((n + 1 : ℕ) : ℝ))
        (fun x => ρ x * Real.exp (D.invβ⁻¹ * convFun (periodicRiesz d D.s) ρ x)) X *
      movT_commAt D (n + 1) ρ X := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hρc := mova_continuous_of_isCk hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hG1 : Torus.IsCk 1 (convFun (periodicRiesz d D.s) ρ) := mova_isCk_one_convFun hgi hρ1
  set β : ℝ := D.invβ⁻¹ with hβdef
  have hβpos : 0 < β := inv_pos.2 hβ
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNpos : 0 < Nr := by rw [hNr]; positivity
  set a : ℝ := β / Nr with ha_def
  have ha : 0 < a := div_pos hβpos hNpos
  set b : Torus d → ℝ := fun x => β * convFun (periodicRiesz d D.s) ρ x with hbdef
  have hb : Torus.IsCk 1 b := mova_isCk_const_mul β hG1
  have hKj : ∀ j x, Torus.partialDeriv j (convFun (periodicRiesz d D.s) ρ) x =
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := fun j x => by
    rw [mova_partialDeriv_convFun hgi hρ1 j x, mova_convGradConv_eq hd D.hs0 D.hsd hρ1 j x]
  have hdb : ∀ j x, Torus.partialDeriv j b x = β * (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j := by
    intro j x
    rw [hbdef, mova_partialDeriv_const_mul j hG1 β x, hKj]
  set u : Fin d → Torus d → ℝ := fun j x => (mfeTransport D ρ x).ofLp j with hudef
  have hfj : ∀ j, Torus.IsCk 1 (mova_fj D ρ j) := fun j => mova_fj_isCk D hρ hV j
  have hu : ∀ j x, mova_fj D ρ j x = ρ x * u j x := fun j x => (movg_rho_u D hρ hpos j x).symm
  set π : Torus d → ℝ := fun x => ρ x * Real.exp (b x) with hπdef
  set q : Config d (n + 1) → ℝ := movg_q d D.s a π with hqdef
  -- bounds on `q`
  have hbc : Continuous b := mova_continuous_of_isCk hb
  have hπc : Continuous π := hρc.mul (Real.continuous_exp.comp hbc)
  have hπ0 : ∀ x, 0 ≤ π x := fun x => mul_nonneg (hpos x).le (Real.exp_pos _).le
  obtain ⟨Cπ, -, hCπ⟩ := mova_bound_of_continuous hπc
  have hπ : ∀ x, π x ≤ Cπ := fun x => (le_abs_self _).trans (hCπ x)
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd D.hs0 D.hsd
  have hGa : Measurable (movg_Ga d D.s (a / 2)) := (movg_Ga_continuous hd D.hs0 D.hsd (half_pos ha)).measurable
  have hqm : Measurable q := movg_q_measurable hGa hπc.measurable
  obtain ⟨Cq, hCq0, hCq⟩ := movg_q_le_const (N := n + 1) hB ha.le hπ0 hπ
  have hq0 : ∀ X, 0 ≤ q X := fun X => movg_q_nonneg hπ0 X
  -- the integrable pieces
  have hG'c : Continuous (convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ)) := movg_convpde_continuous D hρ hV
  set c : ℝ := (β * Nr / 2) * ∫ x, ρ x * movg_ob D ρ x with hcdef
  set W : Config d (n + 1) → ℝ := fun X => (∑ i, β * convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) (X i)) + c with hWdef
  have hWc : Continuous W := (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (hG'c.comp (continuous_apply i))).add continuous_const
  obtain ⟨CW, hCW⟩ : ∃ CW, ∀ X, |W X| ≤ CW := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hWc.continuousOn
    exact ⟨C, fun X => by simpa using hC X (Set.mem_univ X)⟩
  have hMint : Integrable (fun X => q X * W X) := by
    refine (integrable_const (Cq * CW)).mono' (hqm.mul hWc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 X)]
    exact mul_le_mul (hCq X) (hCW X) (abs_nonneg _) hCq0
  have hQ := fun i : Fin (n + 1) => movg_Q_ibp hd D.hs0 D.hsd ha i hρc hpos hb hfj hu
  have hL : ∀ i : Fin (n + 1), Integrable (fun X : Config d (n + 1) =>
      q X * (mova_pdeRHS D ρ (X i) / ρ (X i))) := fun i => (hQ i).1
  have hR : ∀ i : Fin (n + 1), Integrable (fun X : Config d (n + 1) => q X * ∑ j, u j (X i) *
      (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        Torus.partialDeriv j b (X i))) := fun i => (hQ i).2.1
  have hEq : ∀ i : Fin (n + 1), ∫ X : Config d (n + 1), q X * (mova_pdeRHS D ρ (X i) / ρ (X i)) =
      ∫ X : Config d (n + 1), q X * ∑ j, u j (X i) *
      (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        Torus.partialDeriv j b (X i)) := fun i => (hQ i).2.2
  have hF : (fun X : Config d (n + 1) => q X * ((∑ i, (mova_pdeRHS D ρ (X i) / ρ (X i) +
          β * convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) (X i))) + c)) =
      fun X => (∑ i, q X * (mova_pdeRHS D ρ (X i) / ρ (X i))) + q X * W X := by
    funext X
    simp only [hWdef, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hOB : ∀ x, convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ) x = ∑ j, (mfeTransport D ρ x).ofLp j *
      (convGradConv (periodicRieszGrad d D.s) ρ x).ofLp j - movg_ob D ρ x := fun x => movg_OB D hρ hpos hV x
  rw [hF, integral_add (integrable_finsetSum _ fun i _ => hL i) hMint, integral_finsetSum _ fun i _ => hL i,
    Finset.sum_congr rfl fun i _ => hEq i, ← integral_finsetSum _ fun i _ => hR i,
    ← integral_add (integrable_finsetSum _ fun i _ => hR i) hMint, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [movg_ae_noCollision (N := n + 1) hd] with X hX
  have hbr := movg_bracket D hρc (fun x => (hpos x).le) β X hX
    (convFun (periodicRiesz d D.s) (mova_pdeRHS D ρ)) hOB
  have e1 : ∑ i, q X * ∑ j, u j (X i) * (a * ∑ k ∈ Finset.univ.erase i,
      (periodicRieszGrad d D.s (X i - X k)).ofLp j - Torus.partialDeriv j b (X i)) =
      q X * ∑ i, ∑ j, (mfeTransport D ρ (X i)).ofLp j * ((β / ((n + 1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        β * (convGradConv (periodicRieszGrad d D.s) ρ (X i)).ofLp j) := by
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hdb, hudef, ha_def, hNr]
  rw [e1]
  have : q X * (∑ i, ∑ j, (mfeTransport D ρ (X i)).ofLp j * ((β / ((n + 1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d D.s (X i - X k)).ofLp j -
        β * (convGradConv (periodicRieszGrad d D.s) ρ (X i)).ofLp j)) + q X * W X =
      q X * (β * ((n + 1 : ℕ) : ℝ) * movT_commAt D (n + 1) ρ X) := by
    rw [← mul_add]
    congr 1
    simp only [hWdef, hcdef]
    rw [← add_assoc]
    exact hbr
  rw [this]
  ring

end HRS
