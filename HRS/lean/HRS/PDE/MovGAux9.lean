import HRS.PDE.MovGAux8

/-!
# MOVG Aux9: continuity on `[0,T]`, uniform bounds, and the logarithmic derivative of the normaliser

For `ρ` with `IsC12Test T ρ ρt`, `T > 0`: `Φ(r) = -(βN/2) c₃(r) + log J(r)` equals `log K_N(ρ^r)` on `[0,T]`, is continuous there,
`HasDerivAt Φ (βN E_{Q_r}[C_N]) r` on `(0,T)`, and the derivative is bounded.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

section Time

variable {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}

theorem movg_continuousOn_c3 (D : DynData d) (hρt : IsC12Test T ρ ρt) :
    ContinuousOn (fun r => movg_c3 D (ρ r)) (Set.Icc (0 : ℝ) T) := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  obtain ⟨Mρ, Mρt, hMρ0, hMρt0, hM⟩ := movg_traj_sup hρt
  set L1 := mova_L1 (periodicRiesz d D.s) with hL1
  have hGc := mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => ρ r.1 y) hgi (mova_cont_rho hρt)
  have hρx : ∀ y : Torus d, Continuous fun r : Set.Icc (0 : ℝ) T => ρ r.1 y := fun y =>
    Continuous.comp (g := fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1 p.2)
      (f := fun r : Set.Icc (0 : ℝ) T => (r, y)) (mova_cont_rho hρt) (continuous_id.prodMk continuous_const)
  have hGx : ∀ y : Torus d, Continuous fun r : Set.Icc (0 : ℝ) T => convFun (periodicRiesz d D.s) (ρ r.1) y :=
    fun y => Continuous.comp (g := fun q : Set.Icc (0 : ℝ) T × Torus d => convFun (periodicRiesz d D.s) (ρ q.1.1) q.2)
      (f := fun r : Set.Icc (0 : ℝ) T => (r, y)) hGc (continuous_id.prodMk continuous_const)
  have hc : Continuous fun r : Set.Icc (0 : ℝ) T => movg_c3 D (ρ r.1) := by
    unfold movg_c3
    have h1 : ∀ r : Set.Icc (0 : ℝ) T, AEStronglyMeasurable
        (fun x => ρ r.1 x * convFun (periodicRiesz d D.s) (ρ r.1) x) volume := fun r =>
      ((mova_cont_rho_slice hρt r.2).mul
        (PDE.MFAux.continuous_convFun hgi (mova_cont_rho_slice hρt r.2))).aestronglyMeasurable
    have h2 : ∀ r : Set.Icc (0 : ℝ) T, ∀ᵐ x ∂(volume : Measure (Torus d)),
        ‖ρ r.1 x * convFun (periodicRiesz d D.s) (ρ r.1) x‖ ≤ Mρ * (L1 * Mρ) := fun r =>
      Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hM r.1 r.2 x).1 (mova_abs_convFun_le hgi (mova_cont_rho_slice hρt r.2)
          (fun y => (hM r.1 r.2 y).1) x) (abs_nonneg _) hMρ0
    have h3 : ∀ᵐ x ∂(volume : Measure (Torus d)),
        Continuous fun r : Set.Icc (0 : ℝ) T => ρ r.1 x * convFun (periodicRiesz d D.s) (ρ r.1) x :=
      Filter.Eventually.of_forall fun x => (hρx x).mul (hGx x)
    exact continuous_of_dominated (μ := (volume : Measure (Torus d)))
      (F := fun (r : Set.Icc (0 : ℝ) T) x => ρ r.1 x * convFun (periodicRiesz d D.s) (ρ r.1) x)
      (bound := fun _ => Mρ * (L1 * Mρ)) h1 h2 (integrable_const _) h3
  exact continuousOn_iff_continuous_restrict.2 hc

theorem movg_continuousOn_J (D : DynData d) (hβ : 0 < D.invβ) (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (n : ℕ) :
    ContinuousOn (fun r => ∫ X : Config d (n + 1), movg_qn D (ρ r) n X) (Set.Icc (0 : ℝ) T) := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  obtain ⟨Mρ, Mρt, hMρ0, hMρt0, hM⟩ := movg_traj_sup hρt
  set L1 := mova_L1 (periodicRiesz d D.s) with hL1
  set β := D.invβ⁻¹ with hβdef
  have hβpos : 0 < β := inv_pos.2 hβ
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < β / ((n + 1 : ℕ) : ℝ) := div_pos hβpos hNpos
  have hGc := mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T)
    (f := fun r y => ρ r.1 y) hgi (mova_cont_rho hρt)
  have hπ0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ movg_pi D (ρ r) x := fun r hr x =>
    mul_nonneg (hpos r hr x).le (Real.exp_pos _).le
  set Cπ : ℝ := Mρ * Real.exp (β * (L1 * Mρ)) with hCπ
  have hπb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, movg_pi D (ρ r) x ≤ Cπ := by
    intro r hr x
    unfold movg_pi
    have h1 : ρ r x ≤ Mρ := (le_abs_self _).trans (hM r hr x).1
    have h2 : Real.exp (β * convFun (periodicRiesz d D.s) (ρ r) x) ≤ Real.exp (β * (L1 * Mρ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans
        (mova_abs_convFun_le hgi (mova_cont_rho_slice hρt hr) (fun y => (hM r hr y).1) x)) hβpos.le)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hMρ0
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd D.hs0 D.hsd
  obtain ⟨Cq, hCq0, hCq⟩ := movg_q_le_unif (N := n + 1) (s := D.s) hB ha.le Cπ
  have hρx : ∀ y : Torus d, Continuous fun r : Set.Icc (0 : ℝ) T => ρ r.1 y := fun y =>
    Continuous.comp (g := fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1 p.2)
      (f := fun r : Set.Icc (0 : ℝ) T => (r, y)) (mova_cont_rho hρt) (continuous_id.prodMk continuous_const)
  have hGx : ∀ y : Torus d, Continuous fun r : Set.Icc (0 : ℝ) T => convFun (periodicRiesz d D.s) (ρ r.1) y :=
    fun y => Continuous.comp (g := fun q : Set.Icc (0 : ℝ) T × Torus d => convFun (periodicRiesz d D.s) (ρ q.1.1) q.2)
      (f := fun r : Set.Icc (0 : ℝ) T => (r, y)) hGc (continuous_id.prodMk continuous_const)
  have hc : Continuous fun r : Set.Icc (0 : ℝ) T => ∫ X : Config d (n + 1), movg_qn D (ρ r.1) n X := by
    have h1 : ∀ r : Set.Icc (0 : ℝ) T, AEStronglyMeasurable (fun X : Config d (n + 1) => movg_qn D (ρ r.1) n X)
        volume := fun r =>
      (movg_qn_bounded hd D hβ (mova_cont_rho_slice hρt r.2) (fun x => (hpos r.1 r.2 x).le) n).1.aestronglyMeasurable
    have h2 : ∀ r : Set.Icc (0 : ℝ) T, ∀ᵐ X ∂(volume : Measure (Config d (n + 1))),
        ‖movg_qn D (ρ r.1) n X‖ ≤ Cq := fun r => Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        ((movg_qn_bounded hd D hβ (mova_cont_rho_slice hρt r.2) (fun x => (hpos r.1 r.2 x).le) n).2.1 X)]
      exact hCq _ (hπ0 r.1 r.2) (hπb r.1 r.2) X
    have h3 : ∀ᵐ X ∂(volume : Measure (Config d (n + 1))),
        Continuous fun r : Set.Icc (0 : ℝ) T => movg_qn D (ρ r.1) n X := Filter.Eventually.of_forall fun X => by
      unfold movg_qn movg_q
      refine continuous_const.mul (continuous_finsetProd _ fun i _ => ?_)
      unfold movg_pi
      exact (hρx (X i)).mul (Real.continuous_exp.comp (continuous_const.mul (hGx (X i))))
    exact continuous_of_dominated (μ := (volume : Measure (Config d (n + 1))))
      (F := fun (r : Set.Icc (0 : ℝ) T) (X : Config d (n + 1)) => movg_qn D (ρ r.1) n X)
      (bound := fun _ => Cq) h1 h2 (integrable_const _) h3
  exact continuousOn_iff_continuous_restrict.2 hc

theorem movg_abs_integral_le {α : Type*} [MeasureSpace α] [IsProbabilityMeasure (volume : Measure α)]
    (f : α → ℝ) {C : ℝ} (h : ∀ x, |f x| ≤ C) : |∫ x, f x| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure α)) (f := f) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa using h x)
  simpa using this

/-- `E_t = E_{Q_t}[C_N]`. -/
def movg_E (D : DynData d) (n : ℕ) (ρ : ℝ → Torus d → ℝ) (t : ℝ) : ℝ :=
  ∫ X, movT_comm D (n + 1) ρ t X ∂(movT_Q (periodicRiesz d D.s) D (n + 1) ρ t)

/-- `Φ(r) = -(βN/2) c₃(r) + log J(r)`, equal to `log K_N(ρ^r)`. -/
def movg_Phi (D : DynData d) (n : ℕ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) : ℝ :=
  -(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * movg_c3 D (ρ r) + Real.log (∫ X : Config d (n + 1), movg_qn D (ρ r) n X)

theorem movg_Phi_eq (D : DynData d) (hβ : 0 < D.invβ) {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    (n : ℕ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Real.log (gibbsNormalizer (periodicRiesz d D.s) (n + 1) D.invβ⁻¹ (withDensityReal (ρ r))) =
      movg_Phi D n ρ r := by
  have hd := b15_one_le_d D
  have hρc : Continuous (ρ r) := mova_continuous_of_isCk (h.ck r hr)
  rw [movg_K_eq hd D (h.mf.density r hr) hρc n]
  have hJ := movg_J_pos hd D hβ hρc (h.pos r hr) n
  rw [Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp]
  rfl

theorem movg_qn_mul_integrable (hd : 1 ≤ d) (D : DynData d) (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (n : ℕ) {S : Config d (n + 1) → ℝ} (hS : Continuous S) :
    Integrable (fun X => movg_qn D ρ n X * S X) := by
  obtain ⟨hm, hq0, C, hC0, hC⟩ := movg_qn_bounded hd D hβ hρc hρ0 n
  obtain ⟨CS, hCS⟩ := isCompact_univ.exists_bound_of_continuousOn hS.continuousOn
  refine (integrable_const (C * CS)).mono' (hm.mul hS.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 X)]
  have := hCS X (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul (hC X) this (abs_nonneg _) hC0

theorem movg_Psi_eq (D : DynData d) (hβ : 0 < D.invβ) {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    (hT : 0 < T) (hρt : IsC12Test T ρ ρt) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    -(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2) * ((∫ x, ρt t x * convFun (periodicRiesz d D.s) (ρ t) x) +
        ∫ x, ρ t x * convFun (periodicRiesz d D.s) (ρt t) x) +
      (∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ∑ i,
        (ρt t (X i) / ρ t (X i) + D.invβ⁻¹ * convFun (periodicRiesz d D.s) (ρt t) (X i))) /
        (∫ X : Config d (n + 1), movg_qn D (ρ t) n X) =
    D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) * movg_E D n ρ t := by
  have hd := b15_one_le_d D
  have htI : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hρck := h.ck t htI
  have hpos := h.pos t htI
  have hV := h.V_reg
  have hdens := h.mf.density t htI
  have hρc : Continuous (ρ t) := mova_continuous_of_isCk hρck
  have hpde : ρt t = mova_pdeRHS D (ρ t) :=
    funext (mova_pde_pointwise D h.gradient h.V_reg hT h.mf hρt t htI)
  rw [hpde]
  set β := D.invβ⁻¹ with hβdef
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hid := movg_time_identity D hρck hpos hV hβ n
  have hc3 := movg_c3_deriv D hρck hpos hV
  set J : ℝ := ∫ X : Config d (n + 1), movg_qn D (ρ t) n X with hJdef
  have hJ : 0 < J := movg_J_pos hd D hβ hρc hpos n
  set IOb : ℝ := ∫ x, ρ t x * movg_ob D (ρ t) x with hIOb
  set IC : ℝ := ∫ X : Config d (n + 1), movg_qn D (ρ t) n X * movT_commAt D (n + 1) (ρ t) X with hIC
  have hE : movg_E D n ρ t = IC / J := by
    unfold movg_E movT_Q movT_comm
    exact movg_expect_eq hd D hβ hdens hρc hpos n (fun X => movT_commAt D (n + 1) (ρ t) X)
  have hSc : Continuous fun X : Config d (n + 1) => ∑ i, (mova_pdeRHS D (ρ t) (X i) / ρ t (X i) +
      β * convFun (periodicRiesz d D.s) (mova_pdeRHS D (ρ t)) (X i)) :=
    continuous_finsetSum _ fun i _ =>
      (((movg_pde_continuous D hρck hV).div hρc (fun x => (hpos x).ne')).add
        (continuous_const.mul (movg_convpde_continuous D hρck hV))).comp (continuous_apply i)
  have hI1 := movg_qn_mul_integrable hd D hβ hρc (fun x => (hpos x).le) n hSc
  have hI2 := movg_qn_mul_integrable hd D hβ hρc (fun x => (hpos x).le) n
    (continuous_const (y := (β * Nr / 2) * IOb))
  have e1 : (∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ∑ i, (mova_pdeRHS D (ρ t) (X i) / ρ t (X i) +
      β * convFun (periodicRiesz d D.s) (mova_pdeRHS D (ρ t)) (X i))) =
      β * Nr * IC - (β * Nr / 2) * IOb * J := by
    have h1 : ∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ((∑ i, (mova_pdeRHS D (ρ t) (X i) / ρ t (X i) +
        β * convFun (periodicRiesz d D.s) (mova_pdeRHS D (ρ t)) (X i))) + (β * Nr / 2) * IOb) =
        β * Nr * IC := hid
    simp_rw [mul_add] at h1
    rw [integral_add hI1 hI2] at h1
    have h2 : ∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ((β * Nr / 2) * IOb) = (β * Nr / 2) * IOb * J := by
      calc ∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ((β * Nr / 2) * IOb)
          = ∫ X : Config d (n + 1), ((β * Nr / 2) * IOb) * movg_qn D (ρ t) n X :=
            integral_congr_ae (Filter.Eventually.of_forall fun X => mul_comm _ _)
        _ = (β * Nr / 2) * IOb * J := integral_const_mul _ _
    rw [h2] at h1
    linarith
  have e2 : (∫ x, mova_pdeRHS D (ρ t) x * convFun (periodicRiesz d D.s) (ρ t) x) +
      ∫ x, ρ t x * convFun (periodicRiesz d D.s) (mova_pdeRHS D (ρ t)) x = -IOb := by
    rw [← hc3]
    have : ∫ x, mova_pdeRHS D (ρ t) x * convFun (periodicRiesz d D.s) (ρ t) x =
        ∫ x, convFun (periodicRiesz d D.s) (ρ t) x * mova_pdeRHS D (ρ t) x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [this]; ring
  rw [e1, e2, hE]
  field_simp
  ring

theorem movg_hasDerivAt_Phi (D : DynData d) (hβ : 0 < D.invβ) {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hT : 0 < T) (hρt : IsC12Test T ρ ρt) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (movg_Phi D n ρ) (D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) * movg_E D n ρ t) t := by
  have hd := b15_one_le_d D
  have htI : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hρc : Continuous (ρ t) := mova_continuous_of_isCk (h.ck t htI)
  have hc3 := movg_hasDerivAt_c3 D hρt ht
  have hJ := movg_hasDerivAt_J D hβ hρt h.pos ht n
  have hJpos := movg_J_pos hd D hβ hρc (h.pos t htI) n
  have h1 := (hc3.const_mul (-(D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) / 2))).add (hJ.log hJpos.ne')
  rw [← movg_Psi_eq D hβ h hT hρt n ht]
  exact h1

theorem movg_Phi_deriv_bound (D : DynData d) (hβ : 0 < D.invβ) {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hT : 0 < T) (hρt : IsC12Test T ρ ρt) (n : ℕ) :
    ∃ B : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) T, |D.invβ⁻¹ * ((n + 1 : ℕ) : ℝ) * movg_E D n ρ t| ≤ B := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hIcc : ∀ t ∈ Set.Ioo (0 : ℝ) T, t ∈ Set.Icc (0 : ℝ) T := fun t ht => ⟨ht.1.le, ht.2.le⟩
  obtain ⟨Mρ, Mρt, hMρ0, hMρt0, hM⟩ := movg_traj_sup hρt
  obtain ⟨Cq, W0, hCq0, hW00, hqb, hwb⟩ := movg_unif_bounds D hβ hρt h.pos hT.le n
  set L1 := mova_L1 (periodicRiesz d D.s) with hL1
  have hL10 : 0 ≤ L1 := mova_L1_nonneg _
  set β := D.invβ⁻¹ with hβdef
  have hβpos : 0 < β := inv_pos.2 hβ
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNpos : 0 < Nr := by rw [hNr]; positivity
  -- lower bound of `J`
  have hJc := movg_continuousOn_J D hβ hρt h.pos n
  obtain ⟨r₀, hr₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.2 hT.le) hJc
  have hJpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < ∫ X : Config d (n + 1), movg_qn D (ρ r) n X := fun r hr =>
    movg_J_pos hd D hβ (mova_continuous_of_isCk (h.ck r hr)) (h.pos r hr) n
  set m : ℝ := ∫ X : Config d (n + 1), movg_qn D (ρ r₀) n X with hm
  have hm0 : 0 < m := hJpos r₀ hr₀
  refine ⟨(β * Nr / 2) * (Mρt * (L1 * Mρ) + Mρ * (L1 * Mρt)) + Cq * (Nr * W0) / m, fun t ht => ?_⟩
  have htI := hIcc t ht
  rw [← movg_Psi_eq D hβ h hT hρt n ht]
  have hJt : m ≤ ∫ X : Config d (n + 1), movg_qn D (ρ t) n X := isMinOn_iff.1 hmin t htI
  have hρc : Continuous (ρ t) := mova_continuous_of_isCk (h.ck t htI)
  have hc3a : |∫ x, ρt t x * convFun (periodicRiesz d D.s) (ρ t) x| ≤ Mρt * (L1 * Mρ) :=
    movg_abs_integral_le _ fun x => by
      rw [abs_mul]
      exact mul_le_mul (hM t htI x).2 (mova_abs_convFun_le hgi hρc (fun y => (hM t htI y).1) x)
        (abs_nonneg _) hMρt0
  have hc3b : |∫ x, ρ t x * convFun (periodicRiesz d D.s) (ρt t) x| ≤ Mρ * (L1 * Mρt) :=
    movg_abs_integral_le _ fun x => by
      rw [abs_mul]
      exact mul_le_mul (hM t htI x).1 (mova_abs_convFun_le hgi (mova_cont_ρt_slice hρt htI)
        (fun y => (hM t htI y).2) x) (abs_nonneg _) hMρ0
  have hJd : |∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ∑ i,
      (ρt t (X i) / ρ t (X i) + β * convFun (periodicRiesz d D.s) (ρt t) (X i))| ≤ Cq * (Nr * W0) :=
    movg_abs_integral_le _ fun X => by
      rw [abs_mul, abs_of_nonneg ((movg_qn_bounded hd D hβ hρc (fun x => (h.pos t htI x).le) n).2.1 X)]
      refine mul_le_mul (hqb t htI X) ?_ (abs_nonneg _) hCq0
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |ρt t (X i) / ρ t (X i) + β * convFun (periodicRiesz d D.s) (ρt t) (X i)|
          ≤ ∑ _i : Fin (n + 1), W0 := Finset.sum_le_sum fun i _ => hwb t htI (X i)
        _ = Nr * W0 := by simp [hNr]
  have hJtpos : 0 < ∫ X : Config d (n + 1), movg_qn D (ρ t) n X := hm0.trans_le hJt
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < β * Nr / 2)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hc3a hc3b)) (by positivity)
  · rw [abs_div, abs_of_pos hJtpos]
    calc _ ≤ Cq * (Nr * W0) / (∫ X : Config d (n + 1), movg_qn D (ρ t) n X) :=
          div_le_div_of_nonneg_right hJd hJtpos.le
      _ ≤ Cq * (Nr * W0) / m := div_le_div_of_nonneg_left (by positivity) hm0 hJt

end Time

end HRS
