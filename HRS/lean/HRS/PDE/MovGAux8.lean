import HRS.PDE.MovGAux7

/-!
# MOVG Aux8: differentiation in time of `G_r = g*ρ_r`, `c₃(r)`, `J(r) = ∫ q_r`

Dominated differentiation under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`); all `∂_r` are bounded by constants
on `[0,T]` since `ρ, ρt` are jointly continuous on the compact `[0,T] × 𝕋^d` and `ρ ≥ c₀ > 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movg_q_le_unif {s a B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a) (Cπ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Torus d → ℝ, (∀ x, 0 ≤ π x) → (∀ x, π x ≤ Cπ) →
      ∀ X : Config d N, movg_q d s a π X ≤ C := by
  set M := max (Real.exp (a / 2 * B)) 1 with hM
  set P := max Cπ 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  refine ⟨((M ^ N) ^ N) * P ^ N, by positivity, fun π hπ0 hπ X => ?_⟩
  have h1 : ∏ i, π (X i) ≤ P ^ N := by
    simpa using movg_prod_le Finset.univ (fun i => π (X i)) hP1 (fun i => hπ0 _)
      (fun i => (hπ _).trans (le_max_left _ _))
  unfold movg_q
  exact mul_le_mul (movg_pairW_le_pow hB ha X) h1 (Finset.prod_nonneg fun i _ => hπ0 _) (by positivity)

section Time

variable {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}

theorem movg_traj_sup (hρt : IsC12Test T ρ ρt) :
    ∃ Mρ Mρt : ℝ, 0 ≤ Mρ ∧ 0 ≤ Mρt ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ r x| ≤ Mρ ∧ |ρt r x| ≤ Mρt := by
  obtain ⟨B1, hB1⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
    (mova_cont_rho hρt).continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
    hρt.cont_time_deriv.continuousOn
  refine ⟨max B1 0, max B2 0, le_max_right _ _, le_max_right _ _, fun r hr x => ⟨?_, ?_⟩⟩
  · have := hB1 (⟨r, hr⟩, x) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have := hB2 (⟨r, hr⟩, x) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

theorem movg_hasDerivAt_pairL1 (hρt : IsC12Test T ρ ρt) {ψ : Torus d → ℝ} (hψ : Integrable ψ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => ∫ x, ψ x * ρ r x) (∫ x, ψ x * ρt t x) t := by
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  obtain ⟨Mρ, Mρt, -, -, hM⟩ := movg_traj_sup hρt
  have hmeasF : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x => ψ x * ρ r x) volume := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact hψ.aestronglyMeasurable.mul (mova_cont_rho_slice hρt (hIcc r hr)).aestronglyMeasurable
  have hintF : Integrable (fun x => ψ x * ρ t x) :=
    hψ.mul_bdd (mova_cont_rho_slice hρt (hIcc t ht)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using (hM t (hIcc t ht) x).1)
  have hmeasF' : AEStronglyMeasurable (fun x => ψ x * ρt t x) volume :=
    hψ.aestronglyMeasurable.mul (mova_cont_ρt_slice hρt (hIcc t ht)).aestronglyMeasurable
  have hbound : Integrable (fun x => |ψ x| * Mρt) := hψ.abs.mul_const _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun r x => ψ x * ρ r x)
    (F' := fun r x => ψ x * ρt r x) (bound := fun x => |ψ x| * Mρt) (s := Set.Ioo 0 T)
    (Ioo_mem_nhds ht.1 ht.2) hmeasF hintF hmeasF' ?_ hbound ?_).2
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM r (hIcc r hr) x).2 (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    exact (hρt.time_deriv x r hr).const_mul (ψ x)

theorem movg_hasDerivAt_G (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hρt : IsC12Test T ρ ρt)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : Torus d) :
    HasDerivAt (fun r => convFun (periodicRiesz d s) (ρ r) x) (convFun (periodicRiesz d s) (ρt t) x) t := by
  have hψ : Integrable (fun y : Torus d => periodicRiesz d s (x - y)) :=
    (mova_integrable_periodicRiesz hd hs0 hsd).comp_sub_left x
  exact movg_hasDerivAt_pairL1 hρt hψ ht

theorem movg_hasDerivAt_pi (D : DynData d) (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : Torus d) :
    HasDerivAt (fun r => movg_pi D (ρ r) x)
      (movg_pi D (ρ t) x * (ρt t x / ρ t x + D.invβ⁻¹ * convFun (periodicRiesz d D.s) (ρt t) x)) t := by
  have hd := b15_one_le_d D
  have h1 := hρt.time_deriv x t ht
  have h2 := movg_hasDerivAt_G hd D.hs0 D.hsd hρt ht x
  have h3 := (h2.const_mul D.invβ⁻¹).exp
  have h4 := h1.mul h3
  have hp := (hpos t ⟨ht.1.le, ht.2.le⟩ x).ne'
  unfold movg_pi
  convert h4 using 1
  field_simp

theorem movg_hasDerivAt_c3 (D : DynData d) (hρt : IsC12Test T ρ ρt) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => movg_c3 D (ρ r))
      ((∫ x, ρt t x * convFun (periodicRiesz d D.s) (ρ t) x) +
        ∫ x, ρ t x * convFun (periodicRiesz d D.s) (ρt t) x) t := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  obtain ⟨Mρ, Mρt, hMρ0, hMρt0, hM⟩ := movg_traj_sup hρt
  set L1 := mova_L1 (periodicRiesz d D.s) with hL1
  have hGb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |convFun (periodicRiesz d D.s) (ρ r) x| ≤ L1 * Mρ := fun r hr x =>
    mova_abs_convFun_le hgi (mova_cont_rho_slice hρt hr) (fun y => (hM r hr y).1) x
  have hG'b : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |convFun (periodicRiesz d D.s) (ρt r) x| ≤ L1 * Mρt := fun r hr x =>
    mova_abs_convFun_le hgi (mova_cont_ρt_slice hρt hr) (fun y => (hM r hr y).2) x
  have hGc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (convFun (periodicRiesz d D.s) (ρ r)) := fun r hr =>
    PDE.MFAux.continuous_convFun hgi (mova_cont_rho_slice hρt hr)
  have hG'c : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (convFun (periodicRiesz d D.s) (ρt r)) := fun r hr =>
    PDE.MFAux.continuous_convFun hgi (mova_cont_ρt_slice hρt hr)
  have htI := hIcc t ht
  unfold movg_c3
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x => ρ r x * convFun (periodicRiesz d D.s) (ρ r) x)
    (F' := fun r x => ρt r x * convFun (periodicRiesz d D.s) (ρ r) x + ρ r x * convFun (periodicRiesz d D.s) (ρt r) x)
    (bound := fun _ => Mρt * (L1 * Mρ) + Mρ * (L1 * Mρt)) (s := Set.Ioo 0 T)
    (Ioo_mem_nhds ht.1 ht.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2.congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact ((mova_cont_rho_slice hρt (hIcc r hr)).mul (hGc r (hIcc r hr))).aestronglyMeasurable
  · exact mova_int_cont ((mova_cont_rho_slice hρt htI).mul (hGc t htI))
  · exact (((mova_cont_ρt_slice hρt htI).mul (hGc t htI)).add
      ((mova_cont_rho_slice hρt htI).mul (hG'c t htI))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    have hr' := hIcc r hr
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hM r hr' x).2 (hGb r hr' x) (abs_nonneg _) hMρt0
    · rw [abs_mul]
      exact mul_le_mul (hM r hr' x).1 (hG'b r hr' x) (abs_nonneg _) hMρ0
  · refine Filter.Eventually.of_forall fun x r hr => ?_
    exact (hρt.time_deriv x r hr).mul (movg_hasDerivAt_G hd D.hs0 D.hsd hρt hr x)
  · have h1 : Integrable (fun x => ρt t x * convFun (periodicRiesz d D.s) (ρ t) x) :=
      mova_int_cont ((mova_cont_ρt_slice hρt htI).mul (hGc t htI))
    have h2 : Integrable (fun x => ρ t x * convFun (periodicRiesz d D.s) (ρt t) x) :=
      mova_int_cont ((mova_cont_rho_slice hρt htI).mul (hG'c t htI))
    exact integral_add h1 h2

theorem movg_unif_bounds (D : DynData d) (hβ : 0 < D.invβ) (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (hT : 0 ≤ T) (n : ℕ) :
    ∃ Cq W0 : ℝ, 0 ≤ Cq ∧ 0 ≤ W0 ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ X : Config d (n + 1), movg_qn D (ρ r) n X ≤ Cq) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρt r x / ρ r x +
        D.invβ⁻¹ * convFun (periodicRiesz d D.s) (ρt r) x| ≤ W0) := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  obtain ⟨c₀, hc₀, hc⟩ := mova_traj_c0 hT hρt hpos
  obtain ⟨Mρ, Mρt, hMρ0, hMρt0, hM⟩ := movg_traj_sup hρt
  set L1 := mova_L1 (periodicRiesz d D.s) with hL1
  have hL10 : 0 ≤ L1 := mova_L1_nonneg _
  set β := D.invβ⁻¹ with hβdef
  have hβpos : 0 < β := inv_pos.2 hβ
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < β / ((n + 1 : ℕ) : ℝ) := div_pos hβpos hNpos
  have hGb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |convFun (periodicRiesz d D.s) (ρ r) x| ≤ L1 * Mρ := fun r hr x =>
    mova_abs_convFun_le hgi (mova_cont_rho_slice hρt hr) (fun y => (hM r hr y).1) x
  have hG'b : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |convFun (periodicRiesz d D.s) (ρt r) x| ≤ L1 * Mρt := fun r hr x =>
    mova_abs_convFun_le hgi (mova_cont_ρt_slice hρt hr) (fun y => (hM r hr y).2) x
  have hπ0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ movg_pi D (ρ r) x := fun r hr x =>
    mul_nonneg (hpos r hr x).le (Real.exp_pos _).le
  set Cπ : ℝ := Mρ * Real.exp (β * (L1 * Mρ)) with hCπ
  have hπb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, movg_pi D (ρ r) x ≤ Cπ := by
    intro r hr x
    unfold movg_pi
    have h1 : ρ r x ≤ Mρ := (le_abs_self _).trans (hM r hr x).1
    have h2 : Real.exp (β * convFun (periodicRiesz d D.s) (ρ r) x) ≤ Real.exp (β * (L1 * Mρ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hGb r hr x)) hβpos.le)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hMρ0
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd D.hs0 D.hsd
  obtain ⟨Cq, hCq0, hCq⟩ := movg_q_le_unif (N := n + 1) (s := D.s) hB ha.le Cπ
  refine ⟨Cq, Mρt / c₀ + β * (L1 * Mρt), hCq0, by positivity, fun r hr X =>
    hCq _ (hπ0 r hr) (hπb r hr) X, ?_⟩
  intro r hr x
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos (hpos r hr x)]
    exact div_le_div₀ hMρt0 (hM r hr x).2 hc₀ (hc r hr x)
  · rw [abs_mul, abs_of_pos hβpos]
    exact mul_le_mul_of_nonneg_left (hG'b r hr x) hβpos.le

theorem movg_hasDerivAt_J (D : DynData d) (hβ : 0 < D.invβ) (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (n : ℕ) :
    HasDerivAt (fun r => ∫ X : Config d (n + 1), movg_qn D (ρ r) n X)
      (∫ X : Config d (n + 1), movg_qn D (ρ t) n X * ∑ i,
        (ρt t (X i) / ρ t (X i) + D.invβ⁻¹ * convFun (periodicRiesz d D.s) (ρt t) (X i))) t := by
  have hd := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  have hT : 0 ≤ T := ht.1.le.trans ht.2.le
  obtain ⟨Cq, W0, hCq0, hW00, hqb, hwb⟩ := movg_unif_bounds D hβ hρt hpos hT n
  set β := D.invβ⁻¹ with hβdef
  have hβpos : 0 < β := inv_pos.2 hβ
  have htI := hIcc t ht
  have hρc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ρ r) := fun r hr => mova_cont_rho_slice hρt hr
  have hmeasq : ∀ r ∈ Set.Icc (0 : ℝ) T, Measurable (movg_qn D (ρ r) n) := fun r hr =>
    (movg_qn_bounded hd D hβ (hρc r hr) (fun x => (hpos r hr x).le) n).1
  have hq0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ X, 0 ≤ movg_qn D (ρ r) n X := fun r hr X =>
    (movg_qn_bounded hd D hβ (hρc r hr) (fun x => (hpos r hr x).le) n).2.1 X
  have hWc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous fun X : Config d (n + 1) =>
      ∑ i, (ρt r (X i) / ρ r (X i) + β * convFun (periodicRiesz d D.s) (ρt r) (X i)) := fun r hr =>
    continuous_finsetSum _ fun i _ =>
      (((mova_cont_ρt_slice hρt hr).div (hρc r hr) (fun x => (hpos r hr x).ne')).add
        (continuous_const.mul (PDE.MFAux.continuous_convFun hgi (mova_cont_ρt_slice hρt hr)))).comp
        (continuous_apply i)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r X => movg_qn D (ρ r) n X)
    (F' := fun r X => movg_qn D (ρ r) n X * ∑ i,
      (ρt r (X i) / ρ r (X i) + β * convFun (periodicRiesz d D.s) (ρt r) (X i)))
    (bound := fun _ => Cq * (((n + 1 : ℕ) : ℝ) * W0)) (s := Set.Ioo 0 T)
    (Ioo_mem_nhds ht.1 ht.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hmeasq r (hIcc r hr)).aestronglyMeasurable
  · exact (integrable_const Cq).mono' (hmeasq t htI).aestronglyMeasurable (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 t htI X)]
      exact hqb t htI X)
  · exact ((hmeasq t htI).mul (hWc t htI).measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X r hr => ?_
    have hr' := hIcc r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 r hr' X)]
    refine mul_le_mul (hqb r hr' X) ?_ (abs_nonneg _) hCq0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |ρt r (X i) / ρ r (X i) + β * convFun (periodicRiesz d D.s) (ρt r) (X i)|
        ≤ ∑ _i : Fin (n + 1), W0 := Finset.sum_le_sum fun i _ => hwb r hr' (X i)
      _ = ((n + 1 : ℕ) : ℝ) * W0 := by simp
  · refine Filter.Eventually.of_forall fun X r hr => ?_
    have hr' := hIcc r hr
    unfold movg_qn movg_q
    have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun i r => movg_pi D (ρ r) (X i))
      (f' := fun i => movg_pi D (ρ r) (X i) * (ρt r (X i) / ρ r (X i) +
        β * convFun (periodicRiesz d D.s) (ρt r) (X i)))
      (fun i _ => movg_hasDerivAt_pi D hρt hpos hr (X i))
    refine (hprod.const_mul (movg_pairW d D.s (β / ((n + 1 : ℕ) : ℝ)) X)).congr_deriv ?_
    simp only [smul_eq_mul]
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, Finset.prod_erase_mul _ _ hi]

end Time

end HRS
