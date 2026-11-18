import HRS.MS.S111K3E1

/-!
# S11.1 continuation (S11K3), B03 part E2: the shifted covariance map `k3Jm` and its algebraic properties

`k3Jm z a b = Ψ(J(D̂_z)((φ a, φ b]))` (`Ψ` the push-forward by the shifted reconstruction) for admissible `z`, `0` otherwise.
Additivity and homogeneity in `z`, `J z a a = 0`, additivity in the interval, continuity of the cumulative map.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

/-- A.e. equalities on `[0,u+T]` pass to a.e. equalities of the transformed densities on `[0,2T]`. -/
lemma k3_hat_congr_ae (hT : 0 < T) (hu : 0 ≤ u) {F G : ℝ → K3Bil d m T}
    (h : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (u + T))), F v = G v) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) (2 * T))), k3Hat T u F s = k3Hat T u G s := by
  have h' := (ae_restrict_iff' measurableSet_Icc).1 h
  have hN : volume {v : ℝ | ¬ (v ∈ Icc (0 : ℝ) (u + T) → F v = G v)} = 0 := ae_iff.1 h'
  set N : Set ℝ := {v : ℝ | ¬ (v ∈ Icc (0 : ℝ) (u + T) → F v = G v)} with hNdef
  have hN2 : volume ((fun s : ℝ => s + (u - T)) ⁻¹' N) = 0 := by
    rw [measure_preimage_add_right]; exact hN
  have hN1 : u ≠ 0 → volume ((fun s : ℝ => (u / T) * s) ⁻¹' N) = 0 := by
    intro hu0
    have hc : u / T ≠ 0 := div_ne_zero hu0 hT.ne'
    rw [Real.volume_preimage_mul_left hc, hN, mul_zero]
  rw [ae_restrict_iff' measurableSet_Icc]
  refine measure_mono_null (t := (if u = 0 then ∅ else (fun s : ℝ => (u / T) * s) ⁻¹' N) ∪
    (fun s : ℝ => s + (u - T)) ⁻¹' N) ?_ ?_
  · intro s hs
    have hs' : ¬ (s ∈ Icc (0 : ℝ) (2 * T) → k3Hat T u F s = k3Hat T u G s) := hs
    rw [not_imp] at hs'
    obtain ⟨hs1, hs2⟩ := hs'
    by_cases hsT : s ≤ T
    · left
      by_cases hu0 : u = 0
      · exfalso
        apply hs2
        subst hu0
        simp [k3Hat, hsT]
      · simp only [hu0, if_false, mem_preimage, hNdef, mem_setOf_eq, not_imp]
        refine ⟨k3_pre hT hu hs1.1 hsT, ?_⟩
        intro hFG
        apply hs2
        simp only [k3Hat, hsT, if_true]
        rw [hFG]
    · right
      have hs' : T < s := not_le.1 hsT
      simp only [mem_preimage, hNdef, mem_setOf_eq, not_imp]
      have hv : s + (u - T) ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith, by linarith [hs1.2]⟩
      refine ⟨hv, ?_⟩
      intro hFG
      apply hs2
      simp only [k3Hat, hsT, if_false]
      have e : u + (s - T) = s + (u - T) := by ring
      rw [e, hFG]
  · refine measure_union_null ?_ hN2
    by_cases hu0 : u = 0
    · simp [hu0]
    · simp only [hu0, if_false]; exact hN1 hu0

lemma k3_hat_add (Dm₁ Dm₂ : ℝ → K3Bil d m T) (s : ℝ) :
    k3Hat T u (fun v => Dm₁ v + Dm₂ v) s = k3Hat T u Dm₁ s + k3Hat T u Dm₂ s := by
  unfold k3Hat; split_ifs <;> simp [smul_add]

lemma k3_hat_smul (c : ℝ) (Dm : ℝ → K3Bil d m T) (s : ℝ) :
    k3Hat T u (fun v => c • Dm v) s = c • k3Hat T u Dm s := by
  unfold k3Hat; split_ifs <;> simp [smul_comm c]

/-! ### Copies of the abstract tools at horizon `2T` -/

lemma k3_td_comb {H' : ℝ} {D₁ D₂ : ℝ → K3Bil d m T} (h₁ : IsTraceDensityL1 H' D₁)
    (h₂ : IsTraceDensityL1 H' D₂) (a b : ℝ) : IsTraceDensityL1 H' (fun r => a • D₁ r + b • D₂ r) := by
  obtain ⟨s1, b1, m1, i1⟩ := h₁
  obtain ⟨s2, b2, m2, i2⟩ := h₂
  have hent : ∀ r x y, (a • D₁ r + b • D₂ r) x y = a * D₁ r x y + b * D₂ r x y := by
    intro r x y; simp
  have hmeasE : ∀ x y, Measurable fun r => (a • D₁ r + b • D₂ r) x y := by
    intro x y
    have : (fun r => (a • D₁ r + b • D₂ r) x y) = fun r => a * D₁ r x y + b * D₂ r x y :=
      funext fun r => hent r x y
    rw [this]; exact ((m1 x y).const_mul a).add ((m2 x y).const_mul b)
  refine ⟨fun r x y => ?_, fun r hr => ?_, hmeasE, ?_⟩
  · rw [hent, hent, s1, s2]
  · obtain ⟨c1, hc1⟩ := s101_bdd_smul a (b1 r hr)
    obtain ⟨c2, hc2⟩ := s101_bdd_smul b (b2 r hr)
    refine ⟨c1 + c2, ?_⟩
    rintro _ ⟨p, rfl⟩
    have e1 : ∑ i, |(a • D₁ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 := hc1 ⟨p, rfl⟩
    have e2 : ∑ i, |(b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c2 := hc2 ⟨p, rfl⟩
    show ∑ i, |(a • D₁ r + b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 + c2
    calc ∑ i, |(a • D₁ r + b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)|
        ≤ ∑ i, (|(a • D₁ r) (p.1.2.1 i) (p.1.2.2 i)| + |(b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)|) :=
          Finset.sum_le_sum fun i _ => abs_add_le _ _
      _ ≤ c1 + c2 := by rw [Finset.sum_add_distrib]; exact add_le_add e1 e2
  · have hm : Measurable fun r => HRS.traceNormForm (a • D₁ r + b • D₂ r) :=
      HRS.measurable_traceNormForm _ hmeasE
    have hint : Integrable (fun r => |a| * HRS.traceNormForm (D₁ r) + |b| * HRS.traceNormForm (D₂ r))
        (volume.restrict (Icc (0 : ℝ) H')) := (i1.const_mul |a|).add (i2.const_mul |b|)
    refine hint.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (HRS.traceNormForm_nonneg _)]
    calc HRS.traceNormForm (a • D₁ r + b • D₂ r)
        ≤ HRS.traceNormForm (a • D₁ r) + HRS.traceNormForm (b • D₂ r) :=
          s101_tn_add_le (s101_bdd_smul a (b1 r hr)) (s101_bdd_smul b (b2 r hr))
      _ ≤ |a| * HRS.traceNormForm (D₁ r) + |b| * HRS.traceNormForm (D₂ r) :=
          add_le_add (s101_tn_smul_le a (b1 r hr)) (s101_tn_smul_le b (b2 r hr))

theorem k3_J_congr {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hJ : K3Jprops T C0 J) {D₁ D₂ : ℝ → K3Bil d m T} (h₁ : IsTraceDensityL1 (2 * T) D₁)
    (h₂ : IsTraceDensityL1 (2 * T) D₂)
    (hae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) (2 * T))), D₁ τ = D₂ τ) {I : Set ℝ} (hI : MeasurableSet I) :
    J D₁ I = J D₂ I := by
  set E : ℝ → K3Bil d m T := fun r => (1 : ℝ) • D₁ r + (-1 : ℝ) • D₂ r with hE
  have hEr : ∀ r x y, E r x y = D₁ r x y - D₂ r x y := by
    intro r x y; simp [hE, sub_eq_add_neg]
  have hEae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) (2 * T))), E τ = 0 := by
    filter_upwards [hae] with τ hτ
    show (1 : ℝ) • D₁ τ + (-1 : ℝ) • D₂ τ = 0
    rw [hτ]
    ext u v
    simp
  have hEtd : IsTraceDensityL1 (2 * T) E := k3_td_comb h₁ h₂ 1 (-1)
  have hvar : (J E).variation (Icc 0 (2 * T)) = 0 := by
    refine le_antisymm ?_ bot_le
    refine (hJ.tv E hEtd).trans ?_
    have : ∫⁻ r in Icc (0 : ℝ) (2 * T), ENNReal.ofReal (traceNormForm (E r)) = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hEae] with τ hτ
        rw [hτ, traceNormForm_zero_eq]; simp
    rw [this]; simp
  have hJE : J E I = 0 := by
    have h1 : ‖J E I‖ₑ ≤ (J E).variation (I ∩ Icc 0 (2 * T)) := by
      rw [hJ.supp E hEtd I hI]
      exact VectorMeasure.enorm_measure_le_variation _ _
    have h2 : (J E).variation (I ∩ Icc 0 (2 * T)) ≤ (J E).variation (Icc 0 (2 * T)) :=
      measure_mono inter_subset_right
    rw [hvar] at h2
    have : ‖J E I‖ₑ = 0 := le_antisymm (h1.trans h2) bot_le
    simpa using this
  have hlin : J E I = (1 : ℝ) • J D₁ I + (-1 : ℝ) • J D₂ I := hJ.lin D₁ D₂ h₁ h₂ 1 (-1) I hI
  have : J E I = J D₁ I - J D₂ I := by
    rw [hlin]; simp [sub_eq_add_neg]
  rw [this] at hJE
  exact sub_eq_zero.1 hJE

/-! ### The map `k3Jm` -/

/-- Weak admissibility. -/
def K3AdmP (C : WholeCoeff d) (m T u : ℝ) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  S101Lin r Pw (u + T) z ∧ R2JIntegrandMeas C m (u + T) z ∧ K3Tr C m T u z

def k3Jm (hT : 0 ≤ T)
    (J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T))))
    (C : WholeCoeff d) (u : ℝ) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (a a' : ℝ) :
    projTensor (OscPath d m T) 2 :=
  if h : K3AdmP C m T u r Pw z then
    ⟨k3Jx hT J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u a) (k3φ T u a')), k3Psi_mem hT _⟩ else 0

lemma k3Jm_coe {hT : 0 ≤ T}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (h : K3AdmP C m T u r Pw z) (a a' : ℝ) :
    ((k3Jm hT J C u r Pw z a a' : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
      k3Jx hT J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u a) (k3φ T u a')) := by
  unfold k3Jm; rw [dif_pos h]

lemma K3AdmP.adm (c : K3Ctx C m T u c0 r b Pw K1) (h : K3AdmP C m T u r Pw z) :
    K3Adm C m T u c0 r b Pw K1 z := c.adm h.1 h.2.1

lemma K3AdmP.add (c : K3Ctx C m T u c0 r b Pw K1) (h : K3AdmP C m T u r Pw z) (h' : K3AdmP C m T u r Pw z') :
    K3AdmP C m T u r Pw (z + z') :=
  ⟨h.1.add h'.1, s101_meas_add h.2.1 h'.2.1, K3Tr.add (h.adm c) (h'.adm c) h.2.2 h'.2.2⟩

lemma K3AdmP.smul (c : K3Ctx C m T u c0 r b Pw K1) (a : ℝ) (h : K3AdmP C m T u r Pw z) :
    K3AdmP C m T u r Pw (a • z) :=
  ⟨h.1.smul a, s101_meas_smul a h.2.1, K3Tr.smul a (h.adm c) h.2.2⟩

lemma k3_admP_of_L1F (c : K3Ctx C m T u c0 r b Pw K1) (hz : IsR2L1F r Pw (u + T) z)
    (hm : R2JIntegrandMeas C m (u + T) z) : K3AdmP C m T u r Pw z :=
  ⟨hz.1, hm, k3_Tr_of_L1F (c.adm hz.1 hm) hz⟩

lemma K3AdmP.hat_td (hT : 0 < T) (c : K3Ctx C m T u c0 r b Pw K1) (h : K3AdmP C m T u r Pw z) :
    IsTraceDensityL1 (2 * T) (k3Hat T u (k3Dm C m T u z)) :=
  k3_hat_td hT c.hu (k3_Dm_td (h.adm c) h.2.2)

section Algebra

variable (hT : 0 < T) (c : K3Ctx C m T u c0 r b Pw K1)
  {C0 : ℝ} {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
  (hJ : K3Jprops T C0 J)

include hT c hJ in
theorem k3Jm_add (h : K3AdmP C m T u r Pw z) (h' : K3AdmP C m T u r Pw z') (a a' : ℝ) :
    k3Jm hT.le J C u r Pw (z + z') a a' = k3Jm hT.le J C u r Pw z a a' + k3Jm hT.le J C u r Pw z' a a' := by
  have h3 := h.add c h'
  have A1 := h.adm c
  have A2 := h'.adm c
  apply Subtype.ext
  rw [Submodule.coe_add, k3Jm_coe h3, k3Jm_coe h, k3Jm_coe h']
  have TD1 := h.hat_td hT c
  have TD2 := h'.hat_td hT c
  have TD3 := h3.hat_td hT c
  have hJeq : J (k3Hat T u (k3Dm C m T u (z + z'))) (Ioc (k3φ T u a) (k3φ T u a')) =
      J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u a) (k3φ T u a')) +
        J (k3Hat T u (k3Dm C m T u z')) (Ioc (k3φ T u a) (k3φ T u a')) := by
    rw [k3_J_congr hJ TD3 (k3_td_comb TD1 TD2 1 1) (by
      filter_upwards [k3_hat_congr_ae hT c.hu (k3_Dm_ae_add A1 A2)] with s hs
      rw [hs, k3_hat_add]; simp) measurableSet_Ioc]
    have := hJ.lin _ _ TD1 TD2 1 1 (Ioc (k3φ T u a) (k3φ T u a')) measurableSet_Ioc
    simpa using this
  show k3Psi hT.le (J (k3Hat T u (k3Dm C m T u (z + z'))) (Ioc (k3φ T u a) (k3φ T u a'))) =
    k3Psi hT.le (J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u a) (k3φ T u a'))) +
      k3Psi hT.le (J (k3Hat T u (k3Dm C m T u z')) (Ioc (k3φ T u a) (k3φ T u a')))
  rw [hJeq, k3Psi_add]

include hT c hJ in
theorem k3Jm_smul (a : ℝ) (h : K3AdmP C m T u r Pw z) (s s' : ℝ) :
    k3Jm hT.le J C u r Pw (a • z) s s' = a • k3Jm hT.le J C u r Pw z s s' := by
  have h3 := h.smul c a
  have A1 := h.adm c
  apply Subtype.ext
  rw [Submodule.coe_smul, k3Jm_coe h3, k3Jm_coe h]
  have TD1 := h.hat_td hT c
  have TD3 := h3.hat_td hT c
  have hJeq : J (k3Hat T u (k3Dm C m T u (a • z))) (Ioc (k3φ T u s) (k3φ T u s')) =
      a • J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u s) (k3φ T u s')) := by
    rw [k3_J_congr hJ TD3 (k3_td_comb TD1 TD1 a 0) (by
      filter_upwards [k3_hat_congr_ae hT c.hu (k3_Dm_ae_smul a A1)] with t ht
      rw [ht, k3_hat_smul]; simp) measurableSet_Ioc]
    have := hJ.lin _ _ TD1 TD1 a 0 (Ioc (k3φ T u s) (k3φ T u s')) measurableSet_Ioc
    simpa using this
  show k3Psi hT.le (J (k3Hat T u (k3Dm C m T u (a • z))) (Ioc (k3φ T u s) (k3φ T u s'))) =
    a • k3Psi hT.le (J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u s) (k3φ T u s')))
  rw [hJeq, k3Psi_smul]

include hT c in
theorem k3Jm_self (h : K3AdmP C m T u r Pw z) (a : ℝ) : k3Jm hT.le J C u r Pw z a a = 0 := by
  apply Subtype.ext
  rw [k3Jm_coe h, Submodule.coe_zero]
  rw [Set.Ioc_self]
  exact k3Jx_empty hT.le J _

include hT c in
theorem k3Jm_add_interval (h : K3AdmP C m T u r Pw z) {a a' a'' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (haa' : a' ≤ a'') :
    k3Jm hT.le J C u r Pw z a a'' = k3Jm hT.le J C u r Pw z a a' + k3Jm hT.le J C u r Pw z a' a'' := by
  apply Subtype.ext
  rw [Submodule.coe_add, k3Jm_coe h, k3Jm_coe h, k3Jm_coe h]
  exact k3Jx_Ioc_add hT.le J _ (k3φ_mono hT c.hu ha haa) (k3φ_mono hT c.hu (ha.trans haa) haa')

end Algebra

end HRS.MS.S111K3
