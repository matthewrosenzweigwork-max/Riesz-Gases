import HRS.MS.S111K3E3

/-!
# S11.1 continuation (S11K3), B03 part E4: the value of the shifted covariance map on observation functionals

`k3Jm_value`: for `0 ≤ a ≤ a' ≤ u+T`, the tensor `J_z(a,a']` has on `ℓ_{ta,φ} ⊗ ℓ_{tb,ψ}` the value
`2ν ∫_{(a,a'] ∩ [0, u + min(ta,tb)]} z_v(∇U^{v,u+ta}φ · ∇U^{v,u+tb}ψ) dv`.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.FixEq HRS.MS.S52
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

/-- The shifted observation coordinates of the actual interval covariance (Pro `ShiftedJValue`). -/
def K3ShiftedJValue (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (a b : ℝ)
    (J : projTensor (OscPath d m T) 2) : Prop :=
  ∀ ta tb : Set.Icc (0 : ℝ) T, ∀ phi psi : Euc d → ℝ,
    ∀ l1 l2 : StrongDual ℝ (OscPath d m T),
      IsR2DualCombo m phi → IsR2DualCombo m psi →
      (∀ w, l1 w = OscDual.eval (OscPath.at' w ta) phi) →
      (∀ w, l2 w = OscDual.eval (OscPath.at' w tb) psi) →
      (J : TensorDual (OscPath d m T) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l1, l2]) =
        2 * C.ν * ∫ v in Set.Ioc a b ∩ Set.Icc 0 (min (u + ta) (u + tb)),
          z v (fun x => inner ℝ (gradient (propagatorW C v (u + ta) phi) x)
            (gradient (propagatorW C v (u + tb) psi) x))

/-- Observation vectors. -/
theorem k3_obs_eq (hT : 0 ≤ T) (S : Finset (MultiIndex d)) (cc : MultiIndex d → ℝ)
    (y : PathSp (2 * T) (KSpace d m T)) (t : Icc (0 : ℝ) T) :
    OscDual.eval (OscPath.at' (k3reconCLM hT y : OscPath d m T) t) (k3combo m S cc) =
      inner ℝ (pcm y (k3pt hT)) (k3y1c m T t S cc - k3y2c m T S cc) +
        inner ℝ (pcm y (k3sh hT t)) (k3y2c m T S cc) := by
  have e : k3combo m S cc = fun x => ∑ α ∈ S, cc α * oscTestFun m α x := rfl
  rw [e, s101_eval_combo]
  simp_rw [k3_recon_coord hT y t]
  unfold k3y1c k3y2c
  rw [inner_sub_right, inner_sum, inner_sum, inner_sum]
  simp only [inner_smul_right]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- Vanishing of the `P`-pairing beyond the observation time. -/
lemma k3_P_vanish (A : K3Adm C m T u c0 r b Pw K1 z) {v t : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    (ht : t ∈ Icc (0 : ℝ) T) (hvt : u + t < v) (S : Finset (MultiIndex d)) (cc : MultiIndex d → ℝ)
    (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (k3y1c m T t S cc - k3y2c m T S cc) = 0 := by
  have h1 := k3_pair_y1c A.hW A.hbS A.hc0 A.hu hv.1 hv.2 ht i x S cc
  have h2 := k3_pair_y2c (u := u) (T := T) A.hW A.hbS A.hc0 hv.1 i x S cc
  have h1' : inner ℝ (r2WindowFeature C m T (gradComp i) u v x) (k3y1c m T t S cc) =
      gradComp i (k3combo m S cc) x := by rw [h1, if_neg (not_le.2 hvt)]
  have h2' : inner ℝ (r2WindowFeature C m T (gradComp i) u v x) (k3y2c m T S cc) =
      gradComp i (k3combo m S cc) x := by
    rw [h2, if_pos (by linarith [ht.1])]
  show inner ℝ (r2WindowFeature C m T (gradComp i) u v x) (k3y1c m T t S cc - k3y2c m T S cc) = 0
  rw [inner_sub_right, h1', h2', sub_self]

lemma k3_Dm_zero_left (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    {h : KSpace d m T} (hh : ∀ i x, inner ℝ (k3G C m T u v i x) h = 0) (k : KSpace d m T) :
    k3Dm C m T u z v h k = 0 := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  rw [hDm]
  by_cases hvG : v ∈ G
  · simp only [hvG, if_true]; exact k3_D_zero_left A hv hh k
  · simp [hvG]

lemma k3_cut {F : ℝ → ℝ} {Hh : ℝ} (hF : IntegrableOn F (Icc 0 Hh)) {a a' X Y : ℝ} (hXY : X ≤ Y) (hX0 : 0 ≤ X)
    (hYH : Y ≤ Hh) (hz : ∀ v ∈ Ioc X Y, F v = 0) :
    ∫ v in Ioc a a' ∩ Icc 0 Y, F v = ∫ v in Ioc a a' ∩ Icc 0 X, F v := by
  have hU : Ioc a a' ∩ Icc 0 Y = (Ioc a a' ∩ Icc 0 X) ∪ (Ioc a a' ∩ Ioc X Y) := by
    ext v
    simp only [mem_inter_iff, mem_Ioc, mem_Icc, mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hv : v ≤ X
      · exact Or.inl ⟨h1, h2, hv⟩
      · exact Or.inr ⟨h1, not_le.1 hv, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, h3.trans hXY⟩
      · exact ⟨h1, by linarith [h2], h3⟩
  have hd : Disjoint (Ioc a a' ∩ Icc 0 X) (Ioc a a' ∩ Ioc X Y) := by
    rw [Set.disjoint_left]
    intro v h1 h2
    exact absurd h2.2.1 (not_lt.2 h1.2.2)
  have hI1 : IntegrableOn F (Ioc a a' ∩ Icc 0 X) :=
    hF.mono_set fun v hv => ⟨hv.2.1, hv.2.2.trans (hXY.trans hYH)⟩
  have hI2 : IntegrableOn F (Ioc a a' ∩ Ioc X Y) :=
    hF.mono_set fun v hv => ⟨by linarith [hv.2.1], hv.2.2.trans hYH⟩
  have hz0 : ∫ v in Ioc a a' ∩ Ioc X Y, F v = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun v hv => hz v hv.2)
  rw [hU, setIntegral_union hd (measurableSet_Ioc.inter measurableSet_Ioc) hI1 hI2, hz0, add_zero]

section Value

variable (hT : 0 < T) (c : K3Ctx C m T u c0 r b Pw K1)
  {C0 : ℝ} {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
  (hJ : K3Jprops T C0 J)

include hT c hJ in
theorem k3Jm_value (h : K3AdmP C m T u r Pw z) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (haH : a' ≤ u + T) :
    K3ShiftedJValue C m T u z a a' (k3Jm hT.le J C u r Pw z a a') := by
  intro ta tb phi psi l1 l2 hφ hψ hl1 hl2
  obtain ⟨Sa, ca, rfl⟩ := hφ
  obtain ⟨Sb, cb, rfl⟩ := hψ
  have A := h.adm c
  have TD := k3_Dm_td A h.2.2
  have hTD := h.hat_td hT c
  rw [k3Jm_coe h]
  set Dm := k3Dm C m T u z with hDm
  set Pa := k3y1c m T ta Sa ca - k3y2c m T Sa ca with hPa
  set Qa := k3y2c m T Sa ca with hQa
  set Pb := k3y1c m T tb Sb cb - k3y2c m T Sb cb with hPb
  set Qb := k3y2c m T Sb cb with hQb
  have h₁ : ∀ y : PathSp (2 * T) (KSpace d m T), l1 (k3reconCLM hT.le y) =
      inner ℝ (pcm y (k3pt hT.le)) Pa + inner ℝ (pcm y (k3sh hT.le ta)) Qa := fun y => by
    rw [hl1]; exact k3_obs_eq hT.le Sa ca y ta
  have h₂ : ∀ y : PathSp (2 * T) (KSpace d m T), l2 (k3reconCLM hT.le y) =
      inner ℝ (pcm y (k3pt hT.le)) Pb + inner ℝ (pcm y (k3sh hT.le tb)) Qb := fun y => by
    rw [hl2]; exact k3_obs_eq hT.le Sb cb y tb
  rw [k3_Jx_four hT hJ hTD measurableSet_Ioc Pa Qa Pb Qb l1 l2 h₁ h₂]
  -- transport each of the four integrals
  have hta := ta.2
  have hHT : u + T = u + T := rfl
  have e1 := k3_hat_int hT c.hu TD ha haa haH (M := 2 * T) (by linarith) le_rfl Pa Pb
  have e2 := k3_hat_int hT c.hu TD ha haa haH (M := T + tb) (by linarith [tb.2.1]) (by linarith [tb.2.2]) Pa Qb
  have e3 := k3_hat_int hT c.hu TD ha haa haH (M := T + ta) (by linarith [ta.2.1]) (by linarith [ta.2.2]) Qa Pb
  have e4 := k3_hat_int hT c.hu TD ha haa haH (M := min (T + ta) (T + tb))
    (le_min (by linarith [ta.2.1]) (by linarith [tb.2.1]))
    ((min_le_left _ _).trans (by linarith [ta.2.2])) Qa Qb
  have r1 : u + (2 * T - T) = u + T := by ring
  have r2 : u + (T + (tb : ℝ) - T) = u + tb := by ring
  have r3 : u + (T + (ta : ℝ) - T) = u + ta := by ring
  have r4 : u + (min (T + (ta : ℝ)) (T + tb) - T) = u + min (ta : ℝ) tb := by
    rw [min_add_add_left]; ring
  rw [r1] at e1; rw [r2] at e2; rw [r3] at e3; rw [r4] at e4
  rw [e1, e2, e3, e4]
  have hDmI : ∀ x y : KSpace d m T, IntegrableOn (fun v => Dm v x y) (Icc 0 (u + T)) :=
    fun x y => k3_entry_integrable TD x y
  have hX0 : 0 ≤ u + min (ta : ℝ) tb := by linarith [c.hu, le_min ta.2.1 tb.2.1]
  have hXa : u + min (ta : ℝ) tb ≤ u + ta := by linarith [min_le_left (ta : ℝ) tb]
  have hXb : u + min (ta : ℝ) tb ≤ u + tb := by linarith [min_le_right (ta : ℝ) tb]
  have hHa : u + (ta : ℝ) ≤ u + T := by linarith [ta.2.2]
  have hHb : u + (tb : ℝ) ≤ u + T := by linarith [tb.2.2]
  have hmemH : ∀ v, 0 ≤ v → v ≤ u + T → v ∈ Icc (0 : ℝ) (u + T) := fun v h1 h2 => ⟨h1, h2⟩
  -- the cuts
  have c1 : ∫ v in Ioc a a' ∩ Icc 0 (u + T), (Dm v) Pa Pb = ∫ v in Ioc a a' ∩ Icc 0 (u + min (ta : ℝ) tb), (Dm v) Pa Pb := by
    refine k3_cut (hDmI Pa Pb) (by linarith [ta.2.2, min_le_left (ta : ℝ) tb]) hX0 le_rfl ?_
    intro v hv
    have hvH := hmemH v (by linarith [hv.1]) hv.2
    rcases le_total (ta : ℝ) tb with hab | hab
    · rw [min_eq_left hab] at hv
      exact k3_Dm_zero_left A hvH (fun i x => k3_P_vanish A hvH ta.2 hv.1 Sa ca i x) Pb
    · rw [min_eq_right hab] at hv
      rw [k3_Dm_symm A]
      exact k3_Dm_zero_left A hvH (fun i x => k3_P_vanish A hvH tb.2 hv.1 Sb cb i x) Pa
  have c2 : ∫ v in Ioc a a' ∩ Icc 0 (u + tb), (Dm v) Pa Qb = ∫ v in Ioc a a' ∩ Icc 0 (u + min (ta : ℝ) tb), (Dm v) Pa Qb := by
    refine k3_cut (hDmI Pa Qb) hXb hX0 hHb ?_
    intro v hv
    have hvH := hmemH v (by linarith [hv.1]) (hv.2.trans hHb)
    rcases le_total (ta : ℝ) tb with hab | hab
    · rw [min_eq_left hab] at hv
      exact k3_Dm_zero_left A hvH (fun i x => k3_P_vanish A hvH ta.2 hv.1 Sa ca i x) Qb
    · rw [min_eq_right hab] at hv
      exact absurd hv.2 (not_le.2 hv.1)
  have c3 : ∫ v in Ioc a a' ∩ Icc 0 (u + ta), (Dm v) Qa Pb = ∫ v in Ioc a a' ∩ Icc 0 (u + min (ta : ℝ) tb), (Dm v) Qa Pb := by
    refine k3_cut (hDmI Qa Pb) hXa hX0 hHa ?_
    intro v hv
    have hvH := hmemH v (by linarith [hv.1]) (hv.2.trans hHa)
    rcases le_total (ta : ℝ) tb with hab | hab
    · rw [min_eq_left hab] at hv
      exact absurd hv.2 (not_le.2 hv.1)
    · rw [min_eq_right hab] at hv
      rw [k3_Dm_symm A]
      exact k3_Dm_zero_left A hvH (fun i x => k3_P_vanish A hvH tb.2 hv.1 Sb cb i x) Qa
  rw [c1, c2, c3]
  set S' : Set ℝ := Ioc a a' ∩ Icc 0 (u + min (ta : ℝ) tb) with hS'
  have hS'sub : S' ⊆ Icc 0 (u + T) := fun v hv =>
    ⟨hv.2.1, hv.2.2.trans (by linarith [ta.2.2, min_le_left (ta : ℝ) tb])⟩
  have hint : ∀ x y : KSpace d m T, IntegrableOn (fun v => Dm v x y) S' := fun x y =>
    (hDmI x y).mono_set hS'sub
  have hexp : ∀ v, (Dm v) (Pa + Qa) (Pb + Qb) =
      (((Dm v) Pa Pb + (Dm v) Pa Qb) + (Dm v) Qa Pb) + (Dm v) Qa Qb := by
    intro v
    simp only [map_add, ContinuousLinearMap.add_apply]
    ring
  have hsum : ∫ v in S', (Dm v) (Pa + Qa) (Pb + Qb) =
      (((∫ v in S', (Dm v) Pa Pb) + ∫ v in S', (Dm v) Pa Qb) + ∫ v in S', (Dm v) Qa Pb) +
        ∫ v in S', (Dm v) Qa Qb := by
    simp_rw [hexp]
    have i12 : IntegrableOn (fun v => (Dm v) Pa Pb + (Dm v) Pa Qb) S' := (hint Pa Pb).add (hint Pa Qb)
    have i123 : IntegrableOn (fun v => ((Dm v) Pa Pb + (Dm v) Pa Qb) + (Dm v) Qa Pb) S' :=
      i12.add (hint Qa Pb)
    rw [← integral_add (hint Pa Pb) (hint Pa Qb), ← integral_add i12 (hint Qa Pb),
      ← integral_add i123 (hint Qa Qb)]
  rw [← hsum]
  have hPQa : Pa + Qa = k3y1c m T ta Sa ca := by rw [hPa, hQa]; exact sub_add_cancel _ _
  have hPQb : Pb + Qb = k3y1c m T tb Sb cb := by rw [hPb, hQb]; exact sub_add_cancel _ _
  rw [hPQa, hPQb]
  have hmin : min (u + (ta : ℝ)) (u + tb) = u + min (ta : ℝ) tb := min_add_add_left _ _ _
  rw [hmin, ← integral_const_mul]
  have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Icc (0 : ℝ) (u + T) → Dm v = k3D C m T u z v :=
    (ae_restrict_iff' measurableSet_Icc).1 (k3_Dm_ae_eq A)
  refine setIntegral_congr_ae (measurableSet_Ioc.inter measurableSet_Icc) ?_
  filter_upwards [hae] with v hv hvS
  have hvH := hS'sub hvS
  have hvA : v ≤ u + (ta : ℝ) := hvS.2.2.trans hXa
  have hvB : v ≤ u + (tb : ℝ) := hvS.2.2.trans hXb
  rw [hv hvH]
  refine k3_D_pairs A hvH (f := propagatorW C v (u + ta) (k3combo m Sa ca))
    (g := propagatorW C v (u + tb) (k3combo m Sb cb)) (fun i x => ?_) (fun i x => ?_)
  · have := k3_pair_y1c A.hW A.hbS A.hc0 A.hu hvH.1 hvH.2 ta.2 i x Sa ca
    unfold k3G
    rw [this, if_pos hvA]
  · have := k3_pair_y1c A.hW A.hbS A.hc0 A.hu hvH.1 hvH.2 tb.2 i x Sb cb
    unfold k3G
    rw [this, if_pos hvB]

end Value

end HRS.MS.S111K3
