import HRS.MS.R2ChaosAux31

/-!
# HRS.MS.R2ChaosAux32 -- a jointly measurable `L²(P')`-limit of an `L²`-Cauchy family indexed by time

Packet S94 (R4, part 1), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_measurable_L2_limit`: if `Φ_m` are jointly measurable on `ℝ × Ω'` and for every `t ∈ S` the sequence `Φ_m(t,·)` is
Cauchy in `L²(P')`, there is a jointly measurable `F` with `Φ_m(t,·) → F(t,·)` in `L²(P')` for EVERY `t ∈ S`.
(The index `M_j(t)` of the `j`-th fast subsequence is Borel in `t` by `measurable_find`.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

theorem s94_measurable_L2_limit {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {S : Set ℝ} (hS : MeasurableSet S) {Φ : ℕ → ℝ × Ω' → ℝ}
    (hΦ : ∀ m, Measurable (Φ m)) (hΦ2 : ∀ m, ∀ t ∈ S, MemLp (fun ζ => Φ m (t, ζ)) 2 P')
    (hcau : ∀ t ∈ S, ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m → ∀ m', M ≤ m' →
      eLpNorm (fun ζ => Φ m (t, ζ) - Φ m' (t, ζ)) 2 P' < ε) :
    ∃ F : ℝ × Ω' → ℝ, Measurable F ∧ ∀ t ∈ S, MemLp (fun ζ => F (t, ζ)) 2 P' ∧
      Tendsto (fun m => eLpNorm (fun ζ => Φ m (t, ζ) - F (t, ζ)) 2 P') atTop (𝓝 0) := by
  classical
  let dd : ℕ → ℕ → ℝ → ℝ≥0∞ := fun m m' t => eLpNorm (fun ζ => Φ m (t, ζ) - Φ m' (t, ζ)) 2 P'
  have hdd : ∀ m m', Measurable (dd m m') := fun m m' =>
    s94_measurable_eLpNorm (F := fun t ζ => Φ m (t, ζ) - Φ m' (t, ζ)) ((hΦ m).sub (hΦ m'))
  let p : ℕ → ℝ → ℕ → Prop := fun j t M =>
    t ∈ S → ∀ m, M ≤ m → ∀ m', M ≤ m' → dd m m' t < (2⁻¹ : ℝ≥0∞) ^ j
  have hex : ∀ j t, ∃ M, p j t M := by
    intro j t
    by_cases ht : t ∈ S
    · obtain ⟨M, hM⟩ := hcau t ht ((2⁻¹ : ℝ≥0∞) ^ j) (ENNReal.pow_pos (by norm_num) j)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h ht⟩
  let Mj : ℕ → ℝ → ℕ := fun j t => Nat.find (hex j t)
  have hMj_spec : ∀ j t, t ∈ S → ∀ m, Mj j t ≤ m → ∀ m', Mj j t ≤ m' → dd m m' t < (2⁻¹ : ℝ≥0∞) ^ j :=
    fun j t ht => Nat.find_spec (hex j t) ht
  have hMj_meas : ∀ j, Measurable (Mj j) := by
    intro j
    refine measurable_find (hex j) fun k => ?_
    have : {t | p j t k} = Sᶜ ∪ ⋂ m, ⋂ (_ : k ≤ m), ⋂ m', ⋂ (_ : k ≤ m'), {t | dd m m' t < (2⁻¹ : ℝ≥0∞) ^ j} := by
      ext t
      simp [p, imp_iff_not_or]
    rw [this]
    exact hS.compl.union (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun m' => MeasurableSet.iInter fun _ => measurableSet_lt (hdd m m') measurable_const)
  let Mmon : ℕ → ℝ → ℕ := fun j => Nat.rec (motive := fun _ => ℝ → ℕ) (Mj 0)
    (fun j f t => max (f t) (Mj (j + 1) t)) j
  have hMmon_succ : ∀ j t, Mmon (j + 1) t = max (Mmon j t) (Mj (j + 1) t) := fun j t => rfl
  have hMmon_meas : ∀ j, Measurable (Mmon j) := by
    intro j
    induction j with
    | zero => exact hMj_meas 0
    | succ j ih => exact (ih.max (hMj_meas (j + 1)))
  have hMmon_ge : ∀ j t, Mj j t ≤ Mmon j t := by
    intro j t
    cases j with
    | zero => exact le_rfl
    | succ j => rw [hMmon_succ]; exact le_max_right _ _
  have hMmon_mono : ∀ j t, Mmon j t ≤ Mmon (j + 1) t := fun j t => by
    rw [hMmon_succ]; exact le_max_left _ _
  have hMmon_mono' : ∀ j t n, j ≤ n → Mmon j t ≤ Mmon n t := fun j t n hjn =>
    monotone_nat_of_le_succ (fun i => hMmon_mono i t) hjn
  let G : ℕ → ℝ × Ω' → ℝ := fun j q => Φ (Mmon j q.1) q
  have hG : ∀ j, Measurable (G j) := fun j =>
    (measurable_from_prod_countable_right (f := fun r : ℕ × (ℝ × Ω') => Φ r.1 r.2) (fun m => hΦ m)).comp
      (((hMmon_meas j).comp measurable_fst).prodMk measurable_id)
  have hGdist : ∀ t ∈ S, ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (fun ζ => G n (t, ζ) - G m (t, ζ)) 2 P' < (2⁻¹ : ℝ≥0∞) ^ N := by
    intro t ht N n m hn hm
    exact hMj_spec N t ht _ ((hMmon_ge N t).trans (hMmon_mono' N t n hn)) _
      ((hMmon_ge N t).trans (hMmon_mono' N t m hm))
  let C : Set (ℝ × Ω') := {q | ∃ c, Tendsto (fun j => G j q) atTop (𝓝 c)}
  have hCm : MeasurableSet C := measurableSet_exists_tendsto (fun j => hG j)
  let Gh : ℕ → ℝ × Ω' → ℝ := fun j q => if q ∈ C then G j q else 0
  have hGh : ∀ j, Measurable (Gh j) := fun j => Measurable.ite hCm (hG j) measurable_const
  let F : ℝ × Ω' → ℝ := fun q => limUnder atTop (fun j => Gh j q)
  have hlim : ∀ q, Tendsto (fun j => Gh j q) atTop (𝓝 (F q)) := by
    intro q
    by_cases hq : q ∈ C
    · obtain ⟨c, hc⟩ := hq
      have hex2 : ∃ a, Tendsto (fun j => Gh j q) atTop (𝓝 a) := by
        refine ⟨c, hc.congr fun j => ?_⟩
        simp only [Gh]
        rw [if_pos ⟨c, hc⟩]
      exact tendsto_nhds_limUnder hex2
    · have hex2 : ∃ a, Tendsto (fun j => Gh j q) atTop (𝓝 a) := by
        refine ⟨0, ?_⟩
        have : (fun j => Gh j q) = fun _ => 0 := by funext j; simp only [Gh]; rw [if_neg hq]
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_limUnder hex2
  have hFm : Measurable F := measurable_of_tendsto_metrizable hGh (tendsto_pi_nhds.2 hlim)
  refine ⟨F, hFm, fun t ht => ?_⟩
  have hae : ∀ᵐ ζ ∂P', (t, ζ) ∈ C := by
    have := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (μ := P') (p := 2) (f := fun j ζ => G j (t, ζ))
      (fun j => (hG j).comp (measurable_prodMk_left (x := t)) |>.aestronglyMeasurable) (by norm_num)
      (B := fun N => (2⁻¹ : ℝ≥0∞) ^ N)
      (by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]; exact ENNReal.ofNat_ne_top)
      (fun N n m hn hm => hGdist t ht N n m hn hm)
    exact this
  have hlimt : ∀ m, ∀ᵐ ζ ∂P', Tendsto (fun j => Φ m (t, ζ) - G j (t, ζ)) atTop (𝓝 (Φ m (t, ζ) - F (t, ζ))) := by
    intro m
    filter_upwards [hae] with ζ hζ
    have h1 := hlim (t, ζ)
    have h2 : (fun j => Gh j (t, ζ)) = fun j => G j (t, ζ) := by
      funext j; simp [Gh, hζ]
    rw [h2] at h1
    exact tendsto_const_nhds.sub h1
  have hbound : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m →
      eLpNorm (fun ζ => Φ m (t, ζ) - F (t, ζ)) 2 P' ≤ ε := by
    intro ε hε
    obtain ⟨M0, hM0⟩ := hcau t ht ε hε
    obtain ⟨j0, hj0⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨M0, fun m hm => ?_⟩
    have hfin : ∀ j, j0 ≤ j → eLpNorm (fun ζ => Φ m (t, ζ) - G j (t, ζ)) 2 P' ≤ ε := by
      intro j hj
      show dd m (Mmon j t) t ≤ ε
      rcases le_or_gt M0 (Mmon j t) with hc | hc
      · exact (hM0 m hm _ hc).le
      · have h1 := hMj_spec j t ht m ((hMmon_ge j t).trans (hc.le.trans hm)) _ (hMmon_ge j t)
        exact (h1.trans_le ((pow_le_pow_right_of_le_one' (by norm_num) hj).trans hj0.le)).le
    have hFat := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := P') (p := 2)
      (f := fun j ζ => Φ m (t, ζ) - G j (t, ζ))
      (fun j => (((hΦ m).comp (measurable_prodMk_left (x := t))).sub
        ((hG j).comp (measurable_prodMk_left (x := t)))).aestronglyMeasurable)
      (fun ζ => Φ m (t, ζ) - F (t, ζ))
      ((((hΦ m).comp (measurable_prodMk_left (x := t))).sub
        (hFm.comp (measurable_prodMk_left (x := t)))).aestronglyMeasurable) (hlimt m)
    exact hFat.trans (Filter.liminf_le_of_frequently_le'
      (Filter.eventually_atTop.2 ⟨j0, hfin⟩).frequently)
  have hF2 : MemLp (fun ζ => F (t, ζ)) 2 P' := by
    obtain ⟨M, hM⟩ := hbound 1 one_pos
    have h1 : MemLp (fun ζ => Φ M (t, ζ) - F (t, ζ)) 2 P' := lt_of_le_of_lt (hM M le_rfl) ENNReal.one_lt_top
    have := (hΦ2 M t ht).sub h1
    refine (memLp_congr_ae (Filter.EventuallyEq.of_eq ?_)).1 this
    funext ζ; simp
  refine ⟨hF2, ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ := hbound ε hε
  exact Filter.eventually_atTop.2 ⟨M, hM⟩

end HRS.MS.R2Chaos
