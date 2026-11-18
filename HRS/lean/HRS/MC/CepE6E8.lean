import HRS.MC.CepE6E7

/-!
# Packet CEPE6E, file 8: near-contact sets and the Itô-isometry term

* `nearI r z`: indicator that some gap `min(d_p, 1-d_p)` of `z` is `< r`;
* `‖v_ε(z)‖² ≤ N⁴ · nearI (ε/2) z`, stability of `nearI` under small perturbations;
* `cepe6e_near_tendsto`: if the contact set of `Zl` is a.s. Lebesgue null, then `E ∫ nearI (r_l)(Zl) → 0`;
* `cepe6e_limsup_near`: `limsup_j E ∫ σ'² ‖v_ε(Zs_j)‖² ≤ σ'² N⁴ E ∫ nearI ε (Zl)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

open Classical in
/-- Indicator of the `r`-near-contact set. -/
def nearI (r : ℝ) (z : Ch N) : ℝ≥0∞ :=
  if (∃ k l : Fin N, k < l ∧ min (z l - z k) (1 - (z l - z k)) < r) then 1 else 0

theorem nearI_le_one (r : ℝ) (z : Ch N) : nearI r z ≤ 1 := by
  unfold nearI; split_ifs <;> simp

theorem nearI_measurable (r : ℝ) : Measurable (nearI (N := N) r) := by
  unfold nearI
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {z : Ch N | ∃ k l : Fin N, k < l ∧ min (z l - z k) (1 - (z l - z k)) < r} =
      ⋃ k : Fin N, ⋃ l : Fin N, {z | k < l ∧ min (z l - z k) (1 - (z l - z k)) < r} := by
    ext z; simp
  rw [this]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => ?_
  by_cases hkl : k < l
  · simp only [hkl, true_and]
    have hc : Continuous fun z : Ch N => min (z l - z k) (1 - (z l - z k)) := by fun_prop
    exact measurableSet_lt hc.measurable measurable_const
  · simp [hkl]

theorem norm_vv_sq_le_nearI (ε : ℝ) (hε : 0 < ε) (z : Ch N) :
    ENNReal.ofReal (‖vv ε z‖ ^ 2) ≤ ENNReal.ofReal ((N : ℝ) ^ 4) * nearI (ε / 2) z := by
  have h := norm_vv_le_indicator ε hε z
  unfold nearI
  split_ifs at h ⊢ with h1
  · rw [mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := norm_nonneg (vv ε z)
    calc ‖vv ε z‖ ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = (N : ℝ) ^ 4 := by ring
  · rw [mul_zero]
    have : ‖vv ε z‖ = 0 := le_antisymm h (norm_nonneg _)
    simp [this]

theorem nearI_le_of_close {ε : ℝ} {z z' : Ch N} (h : ‖z' - z‖ ≤ ε / 4) :
    nearI (ε / 2) z' ≤ nearI ε z := by
  have hco : ∀ i : Fin N, |z' i - z i| ≤ ε / 4 := fun i => by
    have := PiLp.norm_apply_le (z' - z) i
    rw [PiLp.sub_apply, Real.norm_eq_abs] at this
    exact this.trans h
  by_cases h1 : ∃ k l : Fin N, k < l ∧ min (z' l - z' k) (1 - (z' l - z' k)) < ε / 2
  · obtain ⟨k, l, hkl, hlt⟩ := h1
    have h2 : ∃ k l : Fin N, k < l ∧ min (z l - z k) (1 - (z l - z k)) < ε := by
      refine ⟨k, l, hkl, ?_⟩
      have a1 := abs_le.1 (hco k)
      have a2 := abs_le.1 (hco l)
      rcases min_lt_iff.1 hlt with h3 | h3
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have e1 : nearI (ε / 2) z' = 1 := by unfold nearI; exact if_pos ⟨k, l, hkl, hlt⟩
    have e2 : nearI ε z = 1 := by unfold nearI; exact if_pos h2
    rw [e1, e2]
  · have e1 : nearI (ε / 2) z' = 0 := by unfold nearI; exact if_neg h1
    rw [e1]; exact bot_le

/-- A uniform lower bound on the gaps of an alcove point. -/
theorem cepe6e_gap_lower {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ∃ m : ℝ, 0 < m ∧ ∀ k l : Fin N, k < l → m ≤ min (z l - z k) (1 - (z l - z k)) := by
  classical
  have hd : ∀ k l : Fin N, k < l → 0 < min (z l - z k) (1 - (z l - z k)) := by
    intro k l hkl
    exact lt_min (by linarith [hz.1 k l hkl]) (by linarith [hz.2 k l])
  let f : Fin N × Fin N → ℝ := fun p =>
    if p.1 < p.2 then min (z p.2 - z p.1) (1 - (z p.2 - z p.1)) else 1
  have hfpos : ∀ p, 0 < f p := by
    intro p; by_cases h : p.1 < p.2
    · simp only [f, h, if_true]; exact hd _ _ h
    · simp only [f, h, if_false]; exact one_pos
  by_cases hne : (Finset.univ : Finset (Fin N × Fin N)).Nonempty
  · refine ⟨(Finset.univ : Finset (Fin N × Fin N)).inf' hne f, ?_, ?_⟩
    · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' hne f
      rw [hp]; exact hfpos p
    · intro k l hkl
      have h1 := Finset.inf'_le f (Finset.mem_univ (k, l))
      have h2 : f (k, l) = min (z l - z k) (1 - (z l - z k)) := by simp [f, hkl]
      rw [← h2]; exact h1
  · refine ⟨1, one_pos, fun k l _ => ?_⟩
    exact absurd ⟨(k, l), Finset.mem_univ _⟩ hne

theorem nearI_eventually_zero {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, r ≤ r₀ → nearI r z = 0 := by
  obtain ⟨m, hm0, hm⟩ := cepe6e_gap_lower hz
  refine ⟨m, hm0, fun r hr => ?_⟩
  unfold nearI
  rw [if_neg]
  rintro ⟨k, l, hkl, hlt⟩
  linarith [hm k l hkl]

/-- If the contact set is a.s. null, the expected near-contact time tends to `0`. -/
theorem cepe6e_near_tendsto [IsProbabilityMeasure P] {Zl : ℝ → Ω → Ch N} {T : ℝ} (hT : 0 ≤ T)
    (hZc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlj : Measurable fun p : Ω × ℝ => Zl (max p.2 0) p.1)
    (hnull : ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun l => ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl s ω)) ∂P) atTop (𝓝 0) := by
  have hFG : ∀ l ω, ∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl s ω) =
      ∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl (max s 0) ω) := fun l ω =>
    setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [max_eq_left hs.1])
  have hmeas : ∀ l, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl s ω) := by
    intro l
    have h1 : Measurable fun p : Ω × ℝ => nearI (N := N) (r l) (Zl (max p.2 0) p.1) :=
      (nearI_measurable (r l)).comp hZlj
    have h2 := h1.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) T))
    simp_rw [hFG]
    exact h2
  have key := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun l ω => ∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl s ω)) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal T) hmeas ?_ ?_ ?_
  · simpa using key
  · intro l
    refine Eventually.of_forall fun ω => ?_
    calc ∫⁻ s in Icc (0 : ℝ) T, nearI (r l) (Zl s ω) ≤ ∫⁻ s in Icc (0 : ℝ) T, 1 :=
          lintegral_mono fun s => nearI_le_one _ _
      _ = ENNReal.ofReal T := by simp
  · simp
  · filter_upwards [hnull] with ω hω
    have hae : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), Zl s ω ∈ cep_Alcove N := by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hω] with s hs hsI
      by_contra hz; exact hs ⟨hsI, hz⟩
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Icc (0 : ℝ) T))
      (F := fun l s => nearI (r l) (Zl s ω)) (f := fun _ => 0) (fun _ => 1)
      (fun l => (nearI_measurable _).comp (hZc ω).measurable)
      (fun l => Eventually.of_forall fun s => nearI_le_one _ _) (by simp) (by
        filter_upwards [hae] with s hs
        obtain ⟨r0, hr0, h⟩ := nearI_eventually_zero hs
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hr.eventually (ge_mem_nhds hr0)] with l hl
        exact (h _ hl).symm)
    simpa using this

theorem cepe6e_near_choose [IsProbabilityMeasure P] {Zl : ℝ → Ω → Ch N} {T : ℝ} (hT : 0 ≤ T)
    (hZc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlj : Measurable fun p : Ω × ℝ => Zl (max p.2 0) p.1)
    (hnull : ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    {η : ℕ → ℝ} (hη : ∀ k, 0 < η k) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k ∧ ε k ≤ 1 / 8) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ k, ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, nearI (ε k) (Zl s ω)) ∂P ≤ ENNReal.ofReal (η k) := by
  set e : ℕ → ℝ := fun n => (1 / 8) / ((n : ℝ) + 1) with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have het : Tendsto e atTop (𝓝 0) := by
    have := h1n.const_mul (1 / 8 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [he]; ring
  have hH := cepe6e_near_tendsto hT hZc hZlj hnull het
  have h : ∀ k : ℕ, ∃ n : ℕ, e n ≤ 1 / ((k : ℝ) + 1) ∧
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, nearI (e n) (Zl s ω)) ∂P ≤ ENNReal.ofReal (η k) := by
    intro k
    have a1 : ∀ᶠ n in atTop, e n ≤ 1 / ((k : ℝ) + 1) := het.eventually (ge_mem_nhds (by positivity))
    have a2 : ∀ᶠ n in atTop, ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, nearI (e n) (Zl s ω)) ∂P < ENNReal.ofReal (η k) :=
      hH.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (hη k)))
    exact (a1.and a2).exists.imp fun n hn => ⟨hn.1, hn.2.le⟩
  choose nk hnk using h
  refine ⟨fun k => e (nk k), fun k => ⟨he0 _, ?_⟩, ?_, fun k => (hnk k).2⟩
  · simp only [he]
    exact div_le_self (by norm_num) (by linarith [(Nat.cast_nonneg (nk k) : (0 : ℝ) ≤ nk k)])
  · exact squeeze_zero (fun k => (he0 _).le) (fun k => (hnk k).1) h1n

theorem cepe6e_limsup_near [IsProbabilityMeasure P] {Zs : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N} {T : ℝ}
    (hT : 0 ≤ T) (hZsj : ∀ j, Measurable fun p : Ω × ℝ => Zs j (max p.2 0) p.1)
    (hunif : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun j t => Zs j t ω) (fun t => Zl t ω) atTop (Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    limsup (fun j => ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (‖vv ε (Zs j s ω)‖ ^ 2)) ∂P) atTop ≤
      ENNReal.ofReal ((N : ℝ) ^ 4) * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, nearI ε (Zl s ω)) ∂P := by
  set f : ℕ → Ω → ℝ≥0∞ := fun j ω => ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (‖vv ε (Zs j s ω)‖ ^ 2) with hf
  have hfm : ∀ j, Measurable (f j) := by
    intro j
    have h1 : Measurable fun p : Ω × ℝ => ENNReal.ofReal (‖vv ε (Zs j (max p.2 0) p.1)‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp (((vv_continuous ε).measurable.comp (hZsj j)).norm.pow_const 2)
    have h2 := h1.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) T))
    have : f j = fun ω => ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (‖vv ε (Zs j (max s 0) ω)‖ ^ 2) := by
      funext ω
      exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [max_eq_left hs.1])
    rw [this]
    exact h2
  have hbound : ∀ j, f j ≤ᵐ[P] fun _ => ENNReal.ofReal ((N : ℝ) ^ 4) * ENNReal.ofReal T := by
    intro j
    refine Eventually.of_forall fun ω => ?_
    calc f j ω ≤ ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal ((N : ℝ) ^ 4) := by
          refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
          have h0 := norm_nonneg (vv ε (Zs j s ω))
          calc ‖vv ε (Zs j s ω)‖ ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 :=
                pow_le_pow_left₀ h0 (norm_vv_le _ _) 2
            _ = (N : ℝ) ^ 4 := by ring
      _ = ENNReal.ofReal ((N : ℝ) ^ 4) * ENNReal.ofReal T := by simp
  have hfin : ∫⁻ ω, ENNReal.ofReal ((N : ℝ) ^ 4) * ENNReal.ofReal T ∂P ≠ ∞ := by
    simp [ENNReal.mul_eq_top]
  refine (limsup_lintegral_le _ hfm hbound hfin).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hunif] with ω hω
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  have hev : ∀ᶠ j in atTop, ∀ t ∈ Icc (0 : ℝ) T, dist (Zl t ω) (Zs j t ω) < ε / 4 :=
    Metric.tendstoUniformlyOn_iff.1 hω (ε / 4) (by positivity)
  filter_upwards [hev] with j hj
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  have h1 := norm_vv_sq_le_nearI ε hε (Zs j s ω)
  have h2 : nearI (ε / 2) (Zs j s ω) ≤ nearI ε (Zl s ω) := by
    refine nearI_le_of_close ?_
    have := hj s hs
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  exact h1.trans (by gcongr)

end HRS.MC.CepE6E
