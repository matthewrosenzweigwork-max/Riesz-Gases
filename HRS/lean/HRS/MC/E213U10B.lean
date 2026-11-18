import HRS.MC.E213U10A
import HRS.MC.E213U7

/-!
# Packet e213u10, part B: congruences for the window drift / covariance tensor and the tag clamp for `IsRS`

* `u10_winDrift_congr`, `u10_winDrift_near_zero`: the window drift only depends on the coefficient a.e. on `(u,u']`,
  and the drift of the near part `nearCoef b f` over `(u,u']` with `u' ≤ b` vanishes.
* `u10_jTensor_congr_on`, `u10_jTensor_shrink`, `u10_winJ_*`: the same for the covariance tensor.
* `u10_isRS_clamp`: clamping the tag of a Riemann--Stieltjes summand to `[b, ·]` preserves `IsRS`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_ofSeq_zero (m : ℝ) : (NegSobolev.ofSeq m (fun _ : NonzeroLattice d => (0 : ℝ)) : NegSobolev d m) = 0 := by
  have h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (fun _ : NonzeroLattice d => (0 : ℝ)) k) 2 := by
    simp only [mul_zero]
    exact (0 : lp (fun _ : NonzeroLattice d => ℝ) 2).2
  have h2 := NegSobolev.ofSeq_of_mem (d := d) (m := m) (fun _ : NonzeroLattice d => (0 : ℝ)) h
  apply lp.ext
  funext k
  have h3 := congrArg (fun x : lp (fun _ : NonzeroLattice d => ℝ) 2 => (x : NonzeroLattice d → ℝ) k) h2
  refine (by simpa using h3 : _ = (0 : ℝ)).trans ?_
  rfl

theorem u10_vprop_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m t u : ℝ) :
    Vprop D ρ m t u (0 : NegSobolev d m) = 0 := by
  unfold Vprop
  simp only [HRS.MC.E213U2.e213u2_eval_zero]
  exact u10_ofSeq_zero m

theorem u10_driftInc_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {f g : ℝ → NegSobolev d m} {u u' : ℝ}
    (h : ∀ᵐ v ∂(volume.restrict (Set.Ioc u u')), f v = g v) :
    driftInc D ρ m T f u u' = driftInc D ρ m T g u u' := by
  unfold driftInc
  congr 1
  funext t
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
  filter_upwards [h'] with v hv hvm
  have : v ∈ Set.Ioc u u' := ⟨hvm.1, hvm.2.trans (min_le_left _ _)⟩
  rw [hv this]

theorem u10_pathOf_zero (m T : ℝ) : HRS.Sec7.pathOf m T (fun _ => (0 : NegSobolev d m)) = 0 := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => (fun _ : ℝ => (0 : NegSobolev d m)) t := continuous_const
  have hw : HRS.Sec7.pathOf m T (fun _ => (0 : NegSobolev d m)) =
      (⟨fun _ => 0, continuous_const⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold HRS.Sec7.pathOf
    exact dif_pos hc
  rw [hw]
  apply e213o_ext
  intro t
  rfl

theorem u10_driftInc_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T u u' : ℝ) :
    driftInc D ρ m T (fun _ => (0 : NegSobolev d m)) u u' = 0 := by
  have : (fun t : ℝ => ∫ v in Set.Ioc u (min u' t), Vprop D ρ m t v ((fun _ => (0 : NegSobolev d m)) v)) =
      fun _ => 0 := by
    funext t
    simp [u10_vprop_zero]
  unfold driftInc
  rw [this]
  exact u10_pathOf_zero m T

theorem u10_winDrift_congr (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) {f g : ℝ → NegSobolev d m} {u u' : ℝ}
    (h : ∀ᵐ v ∂(volume.restrict (Set.Ioc u u')), f v = g v) :
    winDrift R m T a ha f u u' = winDrift R m T a ha g u u' := by
  unfold winDrift
  rw [u10_driftInc_congr R.D R.ρ m (a + T) h]

theorem u10_nearCoef_ae_zero {E : Type*} [Zero E] (b : ℝ) (f : ℝ → E) {u u' : ℝ} (h : u' ≤ b) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioc u u')), nearCoef b f v = 0 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hne : ∀ᵐ v : ℝ ∂volume, v ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
  filter_upwards [hne] with v hv hvm
  have hvb : v ≠ b := fun e => hv (by simp [e])
  have : v < b := lt_of_le_of_ne (hvm.2.trans h) hvb
  simp [nearCoef, not_le.2 this]

theorem u10_winDrift_near_zero (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (b : ℝ) (f : ℝ → NegSobolev d m) {u u' : ℝ}
    (h : u' ≤ b) : winDrift R m T a ha (nearCoef b f) u u' = 0 := by
  have h0 : ∀ᵐ v ∂(volume.restrict (Set.Ioc u u')), nearCoef b f v = (fun _ => (0 : NegSobolev d m)) v :=
    u10_nearCoef_ae_zero b f h
  rw [u10_winDrift_congr R m T a ha h0]
  unfold winDrift
  rw [u10_driftInc_zero, map_zero]

/-! ### The covariance tensor -/

theorem u10_jTensor_congr_iff (R : Regime d) (m T : ℝ) {z z' : ℝ → NegSobolev d m} {I I' : Set ℝ}
    (hiff : ∀ J, IsJValue R.D R.ρ m T z I J ↔ IsJValue R.D R.ρ m T z' I' J) :
    jTensor R.D R.ρ m T z I = jTensor R.D R.ρ m T z' I' := by
  by_cases hex : ∃ J, IsJValue R.D R.ρ m T z I J
  · obtain ⟨J, hJ⟩ := hex
    rw [HRS.MC.E213U2.e213u2_jTensor_eq R m T z I J hJ, HRS.MC.E213U2.e213u2_jTensor_eq R m T z' I' J ((hiff J).1 hJ)]
  · have hex' : ¬ ∃ J, IsJValue R.D R.ρ m T z' I' J := fun ⟨J, hJ⟩ => hex ⟨J, (hiff J).2 hJ⟩
    unfold jTensor
    rw [dif_neg hex, dif_neg hex']

theorem u10_isJValue_congr_on (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {z z' : ℝ → NegSobolev d m}
    {I : Set ℝ} (hI : MeasurableSet I) (h : ∀ v ∈ I, 0 ≤ v → z v = z' v) (J : TensorDual (PathSpace d m T) 2)
    (hJ : IsJValue D ρ m T z I J) : IsJValue D ρ m T z' I J := by
  refine ⟨hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine setIntegral_congr_fun (hI.inter measurableSet_Icc) fun u hu => ?_
  rw [h u hu.1 hu.2.1]

theorem u10_winJ_congr_on (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) {z z' : ℝ → NegSobolev d m} {I : Set ℝ}
    (hI : MeasurableSet I) (h : ∀ v ∈ I, 0 ≤ v → z v = z' v) :
    winJ R m T a ha z I = winJ R m T a ha z' I := by
  unfold winJ
  rw [u10_jTensor_congr_iff R m (a + T) (z := z) (z' := z') (I := I) (I' := I)]
  exact fun J => ⟨u10_isJValue_congr_on R.D R.ρ m (a + T) hI h J,
    u10_isJValue_congr_on R.D R.ρ m (a + T) hI (fun v hv h0 => (h v hv h0).symm) J⟩

/-- Shrinking the set of integration is harmless if the coefficient vanishes a.e. on the removed part. -/
theorem u10_isJValue_shrink (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) {z : ℝ → NegSobolev d m}
    {I I' : Set ℝ} (hI : MeasurableSet I) (hsub : I' ⊆ I)
    (h : ∀ᵐ v ∂volume, v ∈ I → v ∉ I' → z v = 0) (J : TensorDual (PathSpace d m T) 2) :
    IsJValue D ρ m T z I J ↔ IsJValue D ρ m T z I' J := by
  have key : ∀ (ta tb : ℝ) (f : ℝ → ℝ), (∀ v, z v = 0 → f v = 0) →
      ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), f u = ∫ u in I' ∩ Set.Icc (0 : ℝ) (min ta tb), f u := by
    intro ta tb f hf
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hI.inter measurableSet_Icc).nullMeasurableSet
      (Set.inter_subset_inter_left _ hsub) ?_
    filter_upwards [h] with v hv hvm
    have h1 : v ∈ I := hvm.1.1
    have h2 : v ∉ I' := fun hh => hvm.2 ⟨hh, hvm.1.2⟩
    exact hf v (hv h1 h2)
  constructor
  · intro hJ
    refine ⟨hJ.1, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    rw [hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
    congr 1
    exact key ta tb _ (fun v hv => by simp [hv, HRS.MC.E213U2.e213u2_eval_zero])
  · intro hJ
    refine ⟨hJ.1, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    rw [hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
    congr 1
    exact (key ta tb _ (fun v hv => by simp [hv, HRS.MC.E213U2.e213u2_eval_zero])).symm

theorem u10_winJ_shrink (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) {z : ℝ → NegSobolev d m}
    {I I' : Set ℝ} (hI : MeasurableSet I) (hsub : I' ⊆ I)
    (h : ∀ᵐ v ∂volume, v ∈ I → v ∉ I' → z v = 0) :
    winJ R m T a ha z I = winJ R m T a ha z I' := by
  unfold winJ
  rw [u10_jTensor_congr_iff R m (a + T) (z := z) (z' := z) (I := I) (I' := I')]
  exact fun J => u10_isJValue_shrink R.D R.ρ m (a + T) hI hsub h J

/-! ### Clamping the tag -/

/-- Clamping the tag to `[b, u']` (and keeping it in `[u,u']`) preserves `IsRS`. -/
theorem u10_isRS_clamp {T : ℝ} (b : ℝ) {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I) :
    IsRS T (fun τ u u' => S (min (max τ b) u') u u') I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have := H n u (fun i => min (max (τ i) b) (u i.succ)) hu hu0 huT (fun i => ?_) hmesh
  · exact this
  · refine ⟨le_min ((htag i).1.trans (le_max_left _ _)) (hu.monotone (Fin.castSucc_lt_succ).le), min_le_right _ _⟩

end HRS.MC.E213U10

end
