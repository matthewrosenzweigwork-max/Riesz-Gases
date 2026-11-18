import HRS.MS.FixEqP2Aux5

/-!
# S5.7 `fixed_equation` (worker S57P), part 9: the Duhamel formula (assembly)
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

section Duhamel

variable {C : WholeCoeff d} {T : ℝ} {n : ℕ} {B : ℝ} {g : ℝ → Euc d → ℝ}

theorem s57p_gen_Z_contOn (hgc : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
    generatorW C p.1 (s57pZ C g T p.1) p.2) (x : Euc d) :
    ContinuousOn (fun τ => generatorW C τ (s57pZ C g T τ) x) (Set.Icc (0 : ℝ) T) := by
  have hmap : Continuous (fun τ : Set.Icc (0 : ℝ) T => ((τ, x) : Set.Icc (0 : ℝ) T × Euc d)) :=
    continuous_id.prodMk continuous_const
  have h := hgc.comp hmap
  intro τ hτ
  exact (continuousWithinAt_iff_continuousAt_restrict (fun τ => generatorW C τ (s57pZ C g T τ) x) hτ).2
    h.continuousAt

/-- `Z` solves the inhomogeneous equation in the classical sense -/
theorem s57p_Z_hasDeriv (G : S57pGen C T) (Lin : S57pLin C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) (hT : 0 ≤ T) {r : ℝ} (hr : r ∈ Set.Ioo 0 T) (x : Euc d) :
    HasDerivAt (fun r' => s57pZ C g T r' x) (-(g r x) - generatorW C r (s57pZ C g T r) x) r := by
  obtain ⟨L, hL0, hLip⟩ := s57p_Z_lip G huniq hn4 hB0 O
  have hgc := s57p_Z_gen_cont G huniq hn4 hB0 O hT
  set k : ℝ → ℝ := fun τ => g τ x + generatorW C τ (s57pZ C g T τ) x with hk
  have hkc : ContinuousOn k (Set.Icc (0 : ℝ) T) :=
    (O.cont x).add (s57p_gen_Z_contOn hgc x)
  have hZc : ContinuousOn (fun r' => s57pZ C g T r' x) (Set.Icc (0 : ℝ) T) := by
    rw [Metric.continuousOn_iff]
    intro a ha ε hε
    have hM : 0 < L * (1 + ‖x‖) + 1 := by positivity
    refine ⟨ε / (L * (1 + ‖x‖) + 1), by positivity, fun b hb hba => ?_⟩
    rw [Real.dist_eq] at hba ⊢
    have hlip : |s57pZ C g T b x - s57pZ C g T a x| ≤ L * (1 + ‖x‖) * |b - a| := by
      rcases le_total a b with h | h
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
        exact hLip a b ha hb h x
      · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
        exact hLip b a hb ha h x
    calc |s57pZ C g T b x - s57pZ C g T a x| ≤ L * (1 + ‖x‖) * |b - a| := hlip
      _ ≤ (L * (1 + ‖x‖) + 1) * |b - a| := by nlinarith [abs_nonneg (b - a)]
      _ < (L * (1 + ‖x‖) + 1) * (ε / (L * (1 + ‖x‖) + 1)) := mul_lt_mul_of_pos_left hba hM
      _ = ε := by field_simp
  have hZT : s57pZ C g T T x = 0 := by simp [s57pZ]
  have hint : ∀ r' ∈ Set.Icc (0 : ℝ) T, s57pZ C g T r' x = ∫ τ in r'..T, k τ := by
    intro r' hr'
    have h1 := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := r') (b := T)
      (f := fun r'' => s57pZ C g T r'' x) (f' := fun τ => -(k τ)) hr'.2 (hZc.mono (Set.Icc_subset_Icc hr'.1 le_rfl))
      (fun τ hτ => by
        have := s57p_Z_rderiv G Lin huniq hn4 hB0 O ⟨hr'.1.trans_lt hτ.1, hτ.2⟩ x
        refine (this.mono Set.Ioi_subset_Ici_self).congr_deriv ?_
        simp only [hk]; ring)
      ((hkc.mono (Set.Icc_subset_Icc hr'.1 le_rfl)).neg.intervalIntegrable_of_Icc hr'.2)
    rw [intervalIntegral.integral_neg, hZT] at h1
    linarith
  have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  have hd : HasDerivAt (fun u => ∫ τ in u..T, k τ) (-(k r)) r := by
    refine intervalIntegral.integral_hasDerivAt_left (hkc.mono (Set.Icc_subset_Icc hr.1.le le_rfl) |>.intervalIntegrable_of_Icc hr.2.le) ?_ ?_
    · exact (hkc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
    · exact (hkc.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hr.1 hr.2)
  refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Icc_mem_nhds hr.1 hr.2] with r' hr'
    exact hint r' hr'
  · simp only [hk]; ring

/-- **Inhomogeneous Duhamel formula** (see the module docstring of `FixEqP2Aux5`). -/
theorem s57p_duhamel (G : S57pGen C T) (Lin : S57pLin C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) (hT : 0 ≤ T) {h : ℝ → Euc d → ℝ} {Bh : ℝ}
    (hc3 : ∀ r ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 3 (h r) ∧ ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (h r) x‖ ≤ Bh)
    (hcont : ∀ i ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ i (h p.1) p.2)
    (hterm : h T = 0)
    (hode : ∀ x, ∀ r ∈ Set.Ioo 0 T,
      HasDerivAt (fun r' => h r' x) (-(generatorW C r (h r) x) - g r x) r)
    (hgc : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 (h p.1) p.2)
    (hgb : ∃ Bg : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |generatorW C r (h r) x| ≤ Bg * (1 + ‖x‖)) :
    ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ i ≤ n, ∀ x,
      iteratedFDeriv ℝ i (h r) x = ∫ u in r..T, iteratedFDeriv ℝ i (propagatorW C r u (g u)) x := by
  obtain ⟨K, hK0, hgen⟩ := G.bound
  obtain ⟨Bg, hBg⟩ := hgb
  have hBZ : 0 ≤ B * T := mul_nonneg hB0 hT
  have hZ3 : ∀ r ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 3 (s57pZ C g T r) ∧
      ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (s57pZ C g T r) x‖ ≤ B * T := fun r hr =>
    ⟨((s57p_Z_jets G huniq hn4 hB0 O hr).1).of_le (by exact_mod_cast (by omega : 3 ≤ n)),
      fun i hi x => s57p_Z_bound G huniq hn4 hB0 O hr (by omega) x⟩
  have hZ4 : ∀ r ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 4 (s57pZ C g T r) := fun r hr =>
    ((s57p_Z_jets G huniq hn4 hB0 O hr).1).of_le (by exact_mod_cast hn4)
  have hsub : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, generatorW C r (fun y => h r y - s57pZ C g T r y) x =
      generatorW C r (h r) x - generatorW C r (s57pZ C g T r) x := fun r hr x =>
    Lin.sub r hr (max Bh (B * T)) (h r) (s57pZ C g T r) (hc3 r hr).1 (hZ3 r hr).1
      (fun i hi y => ((hc3 r hr).2 i hi y).trans (le_max_left _ _))
      (fun i hi y => ((hZ3 r hr).2 i hi y).trans (le_max_right _ _)) x
  have hjsub : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ i ≤ 3, ∀ x,
      iteratedFDeriv ℝ i (fun y => h r y - s57pZ C g T r y) x =
        iteratedFDeriv ℝ i (h r) x - iteratedFDeriv ℝ i (s57pZ C g T r) x := fun r hr i hi x =>
    iteratedFDeriv_sub_apply (((hc3 r hr).1.of_le (by exact_mod_cast hi)).contDiffAt)
      (((hZ3 r hr).1.of_le (by exact_mod_cast hi)).contDiffAt)
  -- the difference is a classical solution with datum `0`
  have hcl : IsClassicalAdjointW C T (0 : Euc d → ℝ) (fun r x => h r x - s57pZ C g T r x) := by
    refine ⟨fun r hr => ((hc3 r hr).1.of_le (by norm_num)).sub ((hZ3 r hr).1.of_le (by norm_num)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      refine ⟨Bh + B * T, fun r hr x => ?_⟩
      rw [hjsub r hr j (by omega) x]
      exact (norm_sub_le _ _).trans (add_le_add ((hc3 r hr).2 j (by omega) x) ((hZ3 r hr).2 j (by omega) x))
    · intro j hj
      have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ j (fun y => h p.1 y - s57pZ C g T p.1 y) p.2) =
          fun p => iteratedFDeriv ℝ j (h p.1) p.2 - iteratedFDeriv ℝ j (s57pZ C g T p.1) p.2 := by
        funext p; exact hjsub p.1 p.1.2 j (by omega) p.2
      rw [e]
      exact (hcont j hj).sub (s57p_Z_jet_cont G huniq hn4 hB0 O hj)
    · funext x
      simp [congrFun hterm x, s57pZ]
    · intro x r hr
      have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
      have := (hode x r hr).sub (s57p_Z_hasDeriv G Lin huniq hn4 hB0 O hT hr x)
      refine this.congr_deriv ?_
      rw [hsub r hrI x]
      ring
    · have e : (fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 (fun y => h p.1 y - s57pZ C g T p.1 y) p.2) =
          fun p => generatorW C p.1 (h p.1) p.2 - generatorW C p.1 (s57pZ C g T p.1) p.2 := by
        funext p; exact hsub p.1 p.1.2 p.2
      rw [e]
      exact hgc.sub (s57p_Z_gen_cont G huniq hn4 hB0 O hT)
    · refine ⟨Bg + (B * T) * K, fun r hr x => ?_⟩
      rw [hsub r hr x]
      have h1 := hBg r hr x
      have h2 := (hgen r hr (B * T) (s57pZ C g T r) hBZ (hZ4 r hr)
        (fun j hj y => s57p_Z_bound G huniq hn4 hB0 O hr (by omega) y)).2 0 (by norm_num) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
      calc |generatorW C r (h r) x - generatorW C r (s57pZ C g T r) x|
          ≤ |generatorW C r (h r) x| + |generatorW C r (s57pZ C g T r) x| := abs_sub _ _
        _ ≤ Bg * (1 + ‖x‖) + B * T * K * (1 + ‖x‖) := add_le_add h1 h2
        _ = (Bg + B * T * K) * (1 + ‖x‖) := by ring
  have hzero : IsClassicalAdjointW C T (0 : Euc d → ℝ) (fun _ _ => (0 : ℝ)) := by
    have hg0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, generatorW C r (fun _ : Euc d => (0 : ℝ)) x = 0 := by
      intro r hr x
      have := Lin.sub r hr 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) contDiff_const contDiff_const
        (fun i hi y => by simp) (fun i hi y => by simp) x
      simpa using this
    refine ⟨fun r hr => contDiff_const, fun j hj => ⟨0, fun r hr x => by simp⟩, fun j hj => ?_, rfl, ?_, ?_, ?_⟩
    · simp only [iteratedFDeriv_zero_fun]; exact continuous_const
    · intro x r hr
      simp only [hg0 r ⟨hr.1.le, hr.2.le⟩ x, neg_zero]
      exact hasDerivAt_const r 0
    · simp only [hg0 _ (Subtype.mem _)]
      exact continuous_const
    · exact ⟨0, fun r hr x => by simp [hg0 r hr x]⟩
  have hfin := huniq T ⟨hT, le_rfl⟩ 0 _ _ hcl hzero
  intro r hr i hi x
  have hrZ : h r = s57pZ C g T r := by
    funext y
    have := congrFun (hfin r hr) y
    simp only [sub_eq_zero] at this
    exact this
  rw [hrZ]
  exact (s57p_Z_jets G huniq hn4 hB0 O hr).2 i hi x

end Duhamel
