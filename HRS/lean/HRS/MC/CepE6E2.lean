import HRS.MC.CepE6E1

/-!
# Packet CEPE6E, file 2: S4 (local convergence of the force away from the boundary)

The deterministic setting `Det`: resolvents `J n`, indices `nn i → ∞`, continuous approximants `Zs i → Zl` uniformly on
`[0,T]`, `Zl` in the closed alcove, `∇Φ(Zl)` integrable, boundary time set null.  With `b_i(s) = nn_i (Zs_i s - J_{nn_i}(Zs_i s))
= ∇Φ(J_{nn_i} Zs_i s)` we show: on the part of time where `Zl` stays at distance `≥ r` from the boundary
`b_i → ∇Φ(Zl)` uniformly, hence the weak limit `Λ` of `b_i ds` agrees with `∇Φ(Zl) ds` on test functions supported there.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {N : ℕ}

/-- The force along the approximants. -/
def bF (J : ℝ → Ch N → Ch N) (nn : ℕ → ℝ) (Zs : ℕ → ℝ → Ch N) (i : ℕ) (s : ℝ) : Ch N :=
  nn i • (Zs i s - J (nn i) (Zs i s))

open Classical in
/-- Distance to the complement of the open alcove (`1` if the complement is empty). -/
def dd (N : ℕ) (z : Ch N) : ℝ :=
  if ((cep_Alcove N)ᶜ).Nonempty then Metric.infDist z (cep_Alcove N)ᶜ else 1

theorem dd_continuous : Continuous (dd N) := by
  unfold dd
  split_ifs
  · exact Metric.continuous_infDist_pt _
  · exact continuous_const

theorem dd_nonneg (z : Ch N) : 0 ≤ dd N z := by
  unfold dd
  split_ifs
  · exact Metric.infDist_nonneg
  · exact zero_le_one

theorem dd_pos_of_mem {z : Ch N} (hz : z ∈ cep_Alcove N) : 0 < dd N z := by
  unfold dd
  split_ifs with h
  · have hc : IsClosed (cep_Alcove N)ᶜ := (HRS.MC.CepE6A.e6a_alcove_open).isClosed_compl
    exact (hc.notMem_iff_infDist_pos h).1 (by simpa using hz)
  · exact one_pos

theorem dd_eq_zero_of_not_mem {z : Ch N} (hz : z ∉ cep_Alcove N) : dd N z = 0 := by
  unfold dd
  rw [if_pos ⟨z, hz⟩]
  exact Metric.infDist_zero_of_mem hz

theorem mem_of_dd_pos {z : Ch N} (h : 0 < dd N z) : z ∈ cep_Alcove N := by
  by_contra hz
  rw [dd_eq_zero_of_not_mem hz] at h
  exact lt_irrefl _ h

/-- The deterministic setting. -/
structure Det (a : ℝ) (J : ℝ → Ch N → Ch N) (T : ℝ) (nn : ℕ → ℝ) (Zs : ℕ → ℝ → Ch N)
    (Zl : ℝ → Ch N) : Prop where
  ha : 0 < a
  hJ : cep_Yosida a N J
  hT : 0 ≤ T
  hnn : ∀ i, 0 < nn i
  hnn_top : Tendsto nn atTop atTop
  hZs : ∀ i, Continuous (Zs i)
  hZl : Continuous Zl
  hcl : ∀ s ∈ Icc (0 : ℝ) T, Zl s ∈ closure (cep_Alcove N)
  hnull : volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ∉ cep_Alcove N} = 0
  hint : IntegrableOn (fun s => ‖gradient (cep_chamberPot a N) (Zl s)‖) (Icc 0 T)
  hunif : TendstoUniformlyOn Zs Zl atTop (Icc 0 T)

/-- `Λ` is the weak limit of `b_i ds` on `C([0,T]; ℝ^N)`: the property (3) of `cepe6d_weak_limit`. -/
def IsWL (J : ℝ → Ch N → Ch N) (nn : ℕ → ℝ) (Zs : ℕ → ℝ → Ch N) (T : ℝ)
    (Λ : C(Icc (0 : ℝ) T, Ch N) →L[ℝ] ℝ) : Prop :=
  ∀ (fn : ℕ → ℝ → Ch N) (f : ℝ → Ch N) (_ : ∀ n, ContinuousOn (fn n) (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)), TendstoUniformlyOn fn f atTop (Icc 0 T) →
    Tendsto (fun n => ∫ s in (0 : ℝ)..T, ⟪fn n s, bF J nn Zs n s⟫) atTop (𝓝 (Λ (ofFun f hf)))

variable {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N} {Zl : ℝ → Ch N}

theorem Det.bF_cont (D : Det a J T nn Zs Zl) (i : ℕ) : Continuous (bF J nn Zs i) := by
  have h := (D.hJ.lip (nn i) (D.hnn i)).continuous
  exact h.comp (D.hZs i)

theorem Det.bF_eq (D : Det a J T nn Zs Zl) (i : ℕ) (s : ℝ) :
    bF J nn Zs i s = gradient (cep_chamberPot a N) (J (nn i) (Zs i s)) :=
  D.hJ.force _ _ (D.hnn i)

/-- The Gradient of `Φ` along `Zl` is measurable. -/
theorem Det.grZl_meas (D : Det a J T nn Zs Zl) :
    Measurable fun s => gradient (cep_chamberPot a N) (Zl s) :=
  (HRS.MC.CepE6A.e6a_gradient_measurable a).comp D.hZl.measurable

theorem Det.grZl_integrable (D : Det a J T nn Zs Zl) :
    IntegrableOn (fun s => gradient (cep_chamberPot a N) (Zl s)) (Icc 0 T) :=
  (integrable_norm_iff D.grZl_meas.aestronglyMeasurable).1 D.hint

/-- `⟨g, ∇Φ(Zl)⟩` is integrable on `[0,T]` for `g` bounded measurable. -/
theorem Det.integrableOn_inner (D : Det a J T nn Zs Zl) {g : ℝ → Ch N} (hg : ContinuousOn g (Icc 0 T)) :
    IntegrableOn (fun s => ⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫) (Icc 0 T) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hm : AEStronglyMeasurable (fun s => ⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫)
      (volume.restrict (Icc 0 T)) := by
    refine (ContinuousOn.aestronglyMeasurable hg measurableSet_Icc).inner ?_
    exact D.grZl_meas.aestronglyMeasurable
  refine Integrable.mono' (D.hint.const_mul M) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs]
  calc |⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫|
      ≤ ‖g s‖ * ‖gradient (cep_chamberPot a N) (Zl s)‖ := abs_real_inner_le_norm _ _
    _ ≤ M * ‖gradient (cep_chamberPot a N) (Zl s)‖ :=
        mul_le_mul_of_nonneg_right (hM s hs) (norm_nonneg _)

/-- **S4a.**  Away from the boundary the force converges uniformly: for `r > 0` and `ε' > 0`, eventually
`‖b_i(s) - ∇Φ(Zl s)‖ < ε'` for all `s ∈ [0,T]` with `dd (Zl s) ≥ r`. -/
theorem cepe6e_force_close (D : Det a J T nn Zs Zl) {r : ℝ} (hr : 0 < r) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) T, r ≤ dd N (Zl s) →
      ‖bF J nn Zs i s - gradient (cep_chamberPot a N) (Zl s)‖ < ε' := by
  set S : Set ℝ := Icc 0 T ∩ {s | r ≤ dd N (Zl s)} with hS
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (dd_continuous.comp D.hZl))
  set KS : Set (Ch N) := Zl '' S with hKS
  have hKSc : IsCompact KS := hSc.image D.hZl
  have hKSA : KS ⊆ cep_Alcove N := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_of_dd_pos (lt_of_lt_of_le hr hs.2)
  obtain ⟨δ, hδ, hsub⟩ := hKSc.exists_cthickening_subset_open HRS.MC.CepE6A.e6a_alcove_open hKSA
  set K2 : Set (Ch N) := Metric.cthickening δ KS with hK2
  have hK2c : IsCompact K2 := hKSc.cthickening
  have huc : UniformContinuousOn (gradient (cep_chamberPot a N)) K2 :=
    hK2c.uniformContinuousOn_of_continuous ((cepe6e_gr_continuousOn a).mono hsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨τ, hτ, hτ'⟩ := huc ε' hε'
  obtain ⟨M, hM⟩ := hKSc.exists_bound_of_continuousOn ((cepe6e_gr_continuousOn a).mono hKSA)
  set τ' : ℝ := min τ δ with hτ'def
  have hτ'pos : 0 < τ' := lt_min hτ hδ
  have h1 := Metric.tendstoUniformlyOn_iff.1 D.hunif (τ' / 2) (by positivity)
  have h2 : ∀ᶠ i in atTop, |M| / nn i < τ' / 2 := by
    have := (D.hnn_top.eventually_gt_atTop (|M| / (τ' / 2)))
    filter_upwards [this] with i hi
    have hpos := D.hnn i
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ (by positivity)] at hi
    linarith
  filter_upwards [h1, h2] with i hi1 hi2 s hs hrs
  have hsS : s ∈ S := ⟨hs, hrs⟩
  have hZs : Zl s ∈ KS := ⟨s, hsS, rfl⟩
  have hzA : Zl s ∈ cep_Alcove N := hKSA hZs
  have hnpos := D.hnn i
  -- closeness of the resolvent value
  have hw : ‖J (nn i) (Zs i s) - Zl s‖ < τ' := by
    have e1 : ‖J (nn i) (Zs i s) - J (nn i) (Zl s)‖ ≤ ‖Zs i s - Zl s‖ :=
      cepe6e_J_nonexp D.ha D.hJ hnpos _ _
    have e2 : ‖Zl s - J (nn i) (Zl s)‖ ≤ ‖gradient (cep_chamberPot a N) (Zl s)‖ / nn i :=
      cepe6e_J_close D.ha D.hJ hnpos hzA
    have e3 : ‖gradient (cep_chamberPot a N) (Zl s)‖ / nn i ≤ |M| / nn i :=
      div_le_div_of_nonneg_right ((hM _ hZs).trans (le_abs_self M)) hnpos.le
    have e4 : ‖Zs i s - Zl s‖ < τ' / 2 := by
      have := hi1 s hs
      rwa [dist_comm, dist_eq_norm] at this
    calc ‖J (nn i) (Zs i s) - Zl s‖
        = ‖(J (nn i) (Zs i s) - J (nn i) (Zl s)) - (Zl s - J (nn i) (Zl s))‖ := by
          congr 1; abel
      _ ≤ ‖J (nn i) (Zs i s) - J (nn i) (Zl s)‖ + ‖Zl s - J (nn i) (Zl s)‖ := norm_sub_le _ _
      _ < τ' := by linarith
  have hwK : J (nn i) (Zs i s) ∈ K2 := by
    refine Metric.mem_cthickening_of_dist_le _ (Zl s) δ _ hZs ?_
    rw [dist_eq_norm]
    exact (hw.trans_le (min_le_right _ _)).le
  have hzK : Zl s ∈ K2 := Metric.self_subset_cthickening _ hZs
  have := hτ' _ hwK _ hzK (by rw [dist_eq_norm]; exact hw.trans_le (min_le_left _ _))
  rw [D.bF_eq i s, ← dist_eq_norm]
  exact this

/-- **S4b.**  For a test function supported where `dd (Zl s) ≥ r`, the weak limit of `b_i ds` is `∇Φ(Zl) ds`. -/
theorem cepe6e_local_identity (D : Det a J T nn Zs Zl) (Λ : C(Icc (0 : ℝ) T, Ch N) →L[ℝ] ℝ)
    (hP2 : IsWL J nn Zs T Λ)
    {r : ℝ} (hr : 0 < r) {g : ℝ → Ch N} (hg : ContinuousOn g (Icc 0 T))
    (hsupp : ∀ s ∈ Icc (0 : ℝ) T, g s ≠ 0 → r ≤ dd N (Zl s)) :
    Λ (ofFun g hg) = ∫ s in (0 : ℝ)..T, ⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫ := by
  have hT := D.hT
  have h1 := hP2 (fun _ => g) g (fun _ => hg) hg
    (Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n x hx => by simpa using hε)
  refine tendsto_nhds_unique h1 ?_
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / ((|Mg| + 1) * (T + 1)) := by positivity
  filter_upwards [cepe6e_force_close D hr hε'] with i hi
  have hbi : Continuous (bF J nn Zs i) := D.bF_cont i
  have hI1 : IntervalIntegrable (fun s => ⟪g s, bF J nn Zs i s⟫) volume 0 T :=
    ((hg.inner hbi.continuousOn).intervalIntegrable_of_Icc hT)
  have hI2 : IntervalIntegrable (fun s => ⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact D.integrableOn_inner hg
  rw [dist_eq_norm, ← intervalIntegral.integral_sub hI1 hI2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (f := fun s => ⟪g s, bF J nn Zs i s⟫ - ⟪g s, gradient (cep_chamberPot a N) (Zl s)⟫)
    (C := (|Mg| + 1) * (ε / ((|Mg| + 1) * (T + 1)))) (fun s hs => by
      rw [uIoc_of_le hT] at hs
      have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
      by_cases hg0 : g s = 0
      · simp [hg0]
        positivity
      · have := hi s hsI (hsupp s hsI hg0)
        rw [← inner_sub_right]
        calc ‖⟪g s, bF J nn Zs i s - gradient (cep_chamberPot a N) (Zl s)⟫‖
            ≤ ‖g s‖ * ‖bF J nn Zs i s - gradient (cep_chamberPot a N) (Zl s)‖ :=
              norm_inner_le_norm _ _
          _ ≤ (|Mg| + 1) * (ε / ((|Mg| + 1) * (T + 1))) := by
              refine mul_le_mul ?_ this.le (norm_nonneg _) (by positivity)
              linarith [hMg s hsI, le_abs_self Mg])
  refine lt_of_le_of_lt this ?_
  rw [sub_zero, abs_of_nonneg hT]
  have e : (|Mg| + 1) * (ε / ((|Mg| + 1) * (T + 1))) * T = ε * (T / (T + 1)) := by
    field_simp
  rw [e]
  have : T / (T + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

end HRS.MC.CepE6E
