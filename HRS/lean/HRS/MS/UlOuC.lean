import HRS.MS.UlOuCAux1

/-!
# UL-3 (d): the OU semigroup on `UlClosure` (strong continuity and invariance)

Not a manuscript row.  Statements, with `ouSg Q ν τ` the OU semigroup (`UlOuAux1`), `θ` an `IsUlCutoff`
and `UlClosure k θ` the closure of `C_c^∞ + const` in `ulNormE k θ`:

* (d1) `ouSg_smooth_decay`: `h ∈ C_c^∞` gives `ouSg τ h ∈ C^∞` with every derivative tending to `0` at infinity.
* (d2) `ouSg_cb_tendsto`: `‖ouSg τ h - h‖_{C_b^k} → 0` as `τ → 0+` for `h ∈ C_c^∞`; and
  `ouSg_strongCont`: `ulNormE k θ (ouSg τ f - f) → 0` for `f ∈ UlClosure k θ` (`d/2 < k`).
* (d4) `ouSg_contDiff_two`: `f ∈ UlClosure k θ` (`2 + d/2 < k`) gives `ContDiff ℝ 2 (ouSg τ f)`.
* (d3) `ouSg_mem_ulClosure`: `ouSg τ` maps `UlClosure k θ` into itself (`2 + d/2 < k`, `ν > 0`).

`ν > 0` and constants as in `UlOuS`; helper lemmas carry the prefix `ul3C_`.  The proofs avoid the merged
`ulClosure_of_op` (its linearity hypothesis is for all functions, false for `ouSg` because of Bochner junk
values) and redo its two-line density argument with linearity only on bounded continuous functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}

/-- **UL-3 (d1)**: for `h ∈ C_c^∞`, `ouSg τ h` is `C^∞` and all its derivatives tend to `0` at infinity. -/
theorem ouSg_smooth_decay (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (ouSg Q ν τ h) ∧ ∀ (i : ℕ) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ i (ouSg Q ν τ h) x‖ ≤ ε := by
  refine ⟨contDiff_infty.2 fun n => ?_, fun i ε hε => ?_⟩
  · obtain ⟨M, hM⟩ := ul3C_bdd_upto hh hc n
    exact (ul3C_smooth Q ν τ n (hh.of_le (by exact_mod_cast le_top)) hM).1
  · obtain ⟨M, hM⟩ := ul3C_bdd_upto hh hc i
    set E := ouExp Q τ with hE
    set T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ :=
      ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin i => E) with hT
    set ψ := iteratedFDeriv ℝ i h with hψ
    have hψc : Continuous ψ := hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨R, hR⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) i).isCompact.isBounded.subset_closedBall (0 : Euc d)
    have hRs : ∀ z, max R 0 < ‖z‖ → ψ z = 0 := by
      intro z hz
      by_contra h0
      have := hR (subset_tsupport _ h0)
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R 0]
    have hM' : ∀ z, ‖ψ z‖ ≤ max M 0 := fun z => (hM i le_rfl z).trans (le_max_left _ _)
    set m1 : ℝ := ∫ y, ‖y‖ ∂(ouLaw Q ν τ) with hm1
    have hm10 : 0 ≤ m1 := integral_nonneg fun _ => norm_nonneg _
    set s : ℝ := ‖T‖ * max M 0 * m1 / ε + 1 with hs
    have hs0 : 0 < s := by positivity
    set K : ℝ := ‖ouExp Q (-τ)‖ + 1 with hK
    have hK0 : 0 < K := by positivity
    refine ⟨K * (max R 0 + s), fun x hx => ?_⟩
    have hEx : ‖x‖ ≤ K * ‖E x‖ := by
      have h1 : x = ouExp Q (-τ) (E x) := by
        have := congrArg (fun A : Euc d →L[ℝ] Euc d => A x) (ul2_exp_mul_neg Q (-τ))
        simpa [hE] using this.symm
      calc ‖x‖ = ‖ouExp Q (-τ) (E x)‖ := by rw [← h1]
        _ ≤ ‖ouExp Q (-τ)‖ * ‖E x‖ := (ouExp Q (-τ)).le_opNorm _
        _ ≤ K * ‖E x‖ := by gcongr; linarith
    have hxs : max R 0 + s ≤ ‖E x‖ := by
      rw [← mul_le_mul_iff_of_pos_left hK0]; linarith
    have hint : Integrable (fun y => ψ (E x + y)) (ouLaw Q ν τ) :=
      Integrable.of_bound (hψc.comp (continuous_const.add continuous_id)).aestronglyMeasurable (max M 0)
        (Filter.Eventually.of_forall fun y => hM' _)
    have hder := (ul3C_smooth Q ν τ i (hh.of_le (by exact_mod_cast le_top)) (M := M)
      (fun j hj y => hM j hj y)).2 i le_rfl x
    have e : iteratedFDeriv ℝ i (ouSg Q ν τ h) x = T (∫ y, ψ (E x + y) ∂(ouLaw Q ν τ)) := by
      rw [hder, ← ContinuousLinearMap.integral_comp_comm T hint]; rfl
    rw [e]
    refine (T.le_opNorm _).trans ?_
    have h2 := ul3C_decay_int ψ hψc (R := max R 0) hRs hM' (ouLaw Q ν τ)
      (IsGaussian.integrable_id (μ := ouLaw Q ν τ)).norm E x hs0 hxs
    calc ‖T‖ * ‖∫ y, ψ (E x + y) ∂(ouLaw Q ν τ)‖ ≤ ‖T‖ * (max M 0 / s * m1) := by gcongr
      _ = ‖T‖ * max M 0 * m1 / s := by ring
      _ ≤ ε := by
        rw [div_le_iff₀ hs0, hs]
        have : ‖T‖ * max M 0 * m1 = ‖T‖ * max M 0 * m1 / ε * ε := by field_simp
        nlinarith [mul_pos hε hε]


/-- **UL-3 (d2), `C_b^k` form**: `‖ouSg τ h - h‖_{C_b^k} → 0` as `τ → 0+` for `h ∈ C_c^∞`. -/
theorem ouSg_cb_tendsto (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (k : ℕ) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝[≥] (0 : ℝ), HRS.MemCb k (fun x => ouSg Q ν τ h x - h x) ∧
      HRS.cbNorm k (fun x => ouSg Q ν τ h x - h x) ≤ ε := by
  set ε' : ℝ := ε / (k + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hev : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), ∀ j ∈ Finset.range (k + 1), ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (ouSg Q ν τ h) x - iteratedFDeriv ℝ j h x‖ ≤ ε' :=
    (Filter.eventually_all_finset _).2 fun j _ => ul3C_deriv_close Q hν hh hc j hε'0
  filter_upwards [hev] with τ hτ
  have hsm : ContDiff ℝ k (fun x => ouSg Q ν τ h x - h x) :=
    ((ouSg_smooth_decay Q ν τ hh hc).1.of_le (by exact_mod_cast le_top)).sub
      (hh.of_le (by exact_mod_cast le_top))
  have hD : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ouSg Q ν τ h x - h x) x‖ ≤ ε' := by
    intro j hj x
    have h1 : ContDiff ℝ (j : WithTop ℕ∞) (ouSg Q ν τ h) :=
      (ouSg_smooth_decay Q ν τ hh hc).1.of_le (by exact_mod_cast le_top)
    have h2 : ContDiff ℝ (j : WithTop ℕ∞) h := hh.of_le (by exact_mod_cast le_top)
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x) h1.contDiffAt h2.contDiffAt
    have e : (fun x => ouSg Q ν τ h x - h x) = ouSg Q ν τ h - h := rfl
    rw [e, this]
    exact hτ j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) x
  refine ⟨⟨hsm, fun j hj => ⟨ε', ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact hD j hj x
  · refine le_trans (le_of_eq (rfl : HRS.cbNorm k (fun x => ouSg Q ν τ h x - h x) =
      ∑ j ∈ Finset.range (k + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => ouSg Q ν τ h x - h x) z‖)) ?_
    calc _ ≤ ∑ j ∈ Finset.range (k + 1), ε' :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x => hD j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hε']; push_cast; field_simp


/-- **UL-3 (d4)**: `ouSg τ f` is `C²` for `f ∈ UlClosure k θ`, `2 + d/2 < k`. -/
theorem ouSg_contDiff_two (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (k : ℕ) (θ : Euc d → ℝ)
    (hθ : IsUlCutoff θ) (hk : (2 : ℝ) + (d : ℝ) / 2 < k) {f : Euc d → ℝ} (hf : UlClosure k θ f) :
    ContDiff ℝ 2 (ouSg Q ν τ f) := by
  obtain ⟨C, -, hC⟩ := ulClosure_cb k 2 (by exact_mod_cast hk) θ hθ
  have hcb := (hC f hf).1
  have := (ul3C_smooth Q ν τ 2 (h := f) (by exact_mod_cast hcb.1)
    (M := HRS.cbNorm 2 f) (fun i hi y => ul3_cb_apply hcb hi y)).1
  exact_mod_cast this

/-- **UL-3 (d2)**: strong continuity at `τ = 0` on `UlClosure`. -/
theorem ouSg_strongCont (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (k : ℕ) (θ : Euc d → ℝ)
    (hθ : IsUlCutoff θ) (hk : (d : ℝ) / 2 < k) {f : Euc d → ℝ} (hf : UlClosure k θ f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ ∈ Set.Icc (0 : ℝ) τ0,
      ulNormE k θ (fun x => ouSg Q ν τ f x - f x) ≤ ENNReal.ofReal ε := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Ca, hCa, ha⟩ := ouSg_ulocNormE_le k χ hχ Q ν 1
  obtain ⟨Cs, hCs, hs⟩ := ul3_scalar k χ
  obtain ⟨Ccb, hCcb, hcb⟩ := ulocNormE_le_cb k χ hχ
  set Kc : ℝ := Ca * Ce + Cs * Ce + Ccb with hKc
  have hKc0 : 0 < Kc := by positivity
  set δ : ℝ := ε / (Ce * Kc + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, ⟨h, c, hh, hhc, hg⟩, hle⟩ := hf.2 δ hδ0
  have hgc : IsCcInftyPlusConst g := ⟨h, c, hh, hhc, hg⟩
  have hu : UlClosure k θ (fun x => f x - g x) := ul0_closure_sub_ccc k θ hf hgc
  have hev := ouSg_cb_tendsto Q hν k hh hhc hδ0
  obtain ⟨τ0, hτ0, hsub⟩ := (mem_nhdsGE_iff_exists_Icc_subset).1
    (Filter.inter_mem hev (Icc_mem_nhdsGE one_pos))
  refine ⟨τ0, hτ0, fun τ hτ => ?_⟩
  obtain ⟨⟨hcb1, hcb2⟩, hτ1⟩ := hsub hτ
  subst hg
  set u : Euc d → ℝ := fun x => f x - (h x + c) with hudef
  obtain ⟨hfc, Bf, hBf⟩ := ul3C_closure_bdd k θ hθ hk hf
  obtain ⟨huc, Bu, hBu⟩ := ul3C_closure_bdd k θ hθ hk hu
  have hhb : ∃ Bh, ∀ x, |h x| ≤ Bh := ul3C_bdd_of_cb (m := 0) (ul3_memCb_of_cs 0 hh hhc)
  obtain ⟨Bh, hBh⟩ := hhb
  have hhm : Measurable h := hh.continuous.measurable
  have hgm : Measurable (fun x => h x + c) := hhm.add measurable_const
  have hBg : ∀ x, |h x + c| ≤ Bh + |c| := fun x => (abs_add_le _ _).trans (by linarith [hBh x])
  have hsum : ouSg Q ν τ u = fun x => ouSg Q ν τ f x - (ouSg Q ν τ h x + c) := by
    have e1 : u = fun x => f x - (fun x => h x + c) x := rfl
    rw [e1, ul3C_sub_lin Q ν τ hfc.measurable hgm hBf hBg, ul3C_add_const Q ν τ hhm hBh c]
  have hF : (fun x => ouSg Q ν τ f x - f x) =
      fun x => (ouSg Q ν τ u x + (-1 : ℝ) * u x) + (ouSg Q ν τ h x - h x) := by
    funext x
    have := congrFun hsum x
    simp only [hudef] at this ⊢
    rw [this]; ring
  have hub : ulocNormE k χ u ≤ ENNReal.ofReal (Ce * δ) := by
    refine (hequ u).2.trans ?_
    rw [ENNReal.ofReal_mul hCe.le]
    exact mul_le_mul' le_rfl hle
  have hPu : ulocNormE k χ (ouSg Q ν τ u) ≤ ENNReal.ofReal (Ca * (Ce * δ)) := by
    refine (ha τ ⟨hτ.1, hτ1.2⟩ u huc.measurable ⟨Bu, hBu⟩).trans ?_
    rw [ENNReal.ofReal_mul hCa.le]
    exact mul_le_mul' le_rfl hub
  have hneg : ulocNormE k χ (fun x => (-1 : ℝ) * u x) ≤ ENNReal.ofReal (Cs * (Ce * δ)) := by
    refine (hs (-1) u).trans ?_
    rw [abs_neg, abs_one, mul_one, ENNReal.ofReal_mul hCs.le]
    exact mul_le_mul' le_rfl hub
  have hPh : ulocNormE k χ (fun x => ouSg Q ν τ h x - h x) ≤ ENNReal.ofReal (Ccb * δ) :=
    (hcb _ hcb1).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcb2 hCcb.le))
  have hF2 : ulocNormE k χ (fun x => ouSg Q ν τ f x - f x) ≤ ENNReal.ofReal (Kc * δ) := by
    rw [hF]
    refine (ul0_ulocNormE_add k χ _ _).trans ?_
    refine (add_le_add (ul0_ulocNormE_add k χ _ _) hPh).trans ?_
    refine (add_le_add (add_le_add hPu hneg) le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hKc]; nlinarith
  calc ulNormE k θ (fun x => ouSg Q ν τ f x - f x)
      ≤ ENNReal.ofReal Ce * ulocNormE k χ (fun x => ouSg Q ν τ f x - f x) := (hequ _).1
    _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Kc * δ) := mul_le_mul' le_rfl hF2
    _ = ENNReal.ofReal (Ce * (Kc * δ)) := (ENNReal.ofReal_mul hCe.le).symm
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [hδ]
        have : Ce * (Kc * (ε / (Ce * Kc + 1))) = (Ce * Kc) / (Ce * Kc + 1) * ε := by
          field_simp
        rw [this]
        have h1 : (Ce * Kc) / (Ce * Kc + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith


/-- **UL-3 (d3)**: `ouSg τ` maps `UlClosure k θ` into itself (`τ ≥ 0`, `ν > 0`, `2 + d/2 < k`). -/
theorem ouSg_mem_ulClosure (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {τ : ℝ} (hτ : 0 ≤ τ)
    (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (hk : (2 : ℝ) + (d : ℝ) / 2 < k)
    {f : Euc d → ℝ} (hf : UlClosure k θ f) : UlClosure k θ (ouSg Q ν τ f) := by
  have hk0 : (d : ℝ) / 2 < k := by linarith
  refine ⟨ouSg_contDiff_two Q ν τ k θ hθ hk hf, fun ε hε => ?_⟩
  obtain ⟨C, hC, hbd⟩ := ul3C_ulNorm_bdd Q ν τ k θ hθ hk0
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, ⟨h, c, hh, hhc, hg⟩, hle⟩ := hf.2 δ hδ0
  have hgc : IsCcInftyPlusConst g := ⟨h, c, hh, hhc, hg⟩
  have hu : UlClosure k θ (fun x => f x - g x) := ul0_closure_sub_ccc k θ hf hgc
  -- `ouSg τ g = ouSg τ h + c` lies in the closure
  have hhm : Measurable h := hh.continuous.measurable
  obtain ⟨Bh, hBh⟩ := ul3C_bdd_of_cb (m := 0) (ul3_memCb_of_cs 0 hh hhc)
  have hPg : UlClosure k θ (fun x => ouSg Q ν τ h x + c) := by
    obtain ⟨hsm, hdec⟩ := ouSg_smooth_decay Q ν τ hh hhc
    refine ulClosure_of_decay k θ hθ _ c (hsm.add contDiff_const) (fun ε hε => ?_) (fun j hj _ ε hε => ?_)
    · obtain ⟨R, hR⟩ := hdec 0 ε hε
      refine ⟨R, fun x hx => ?_⟩
      have := hR x hx
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      rwa [add_sub_cancel_right]
    · obtain ⟨R, hR⟩ := hdec j ε hε
      refine ⟨R, fun x hx => ?_⟩
      have e : iteratedFDeriv ℝ j (fun x => ouSg Q ν τ h x + c) x =
          iteratedFDeriv ℝ j (ouSg Q ν τ h) x := by
        have := ul0_iteratedFDeriv_sub_const (ouSg Q ν τ h) hsm (-c) j (by omega) x
        simpa [sub_neg_eq_add] using this
      rw [e]; exact hR x hx
  obtain ⟨g', hg', hle'⟩ := hPg.2 (ε / 2) (by positivity)
  refine ⟨g', hg', ?_⟩
  obtain ⟨hfc, Bf, hBf⟩ := ul3C_closure_bdd k θ hθ hk0 hf
  have hgm : Measurable (fun x => h x + c) := hhm.add measurable_const
  have hBg : ∀ x, |h x + c| ≤ Bh + |c| := fun x => (abs_add_le _ _).trans (by linarith [hBh x])
  subst hg
  have hsum : (fun x => ouSg Q ν τ f x - g' x) = fun x =>
      ouSg Q ν τ (fun x => f x - (h x + c)) x + (ouSg Q ν τ h x + c - g' x) := by
    rw [ul3C_sub_lin Q ν τ hfc.measurable hgm hBf hBg, ul3C_add_const Q ν τ hhm hBh c]
    funext x; ring
  rw [hsum]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  have h1 : ulNormE k θ (ouSg Q ν τ (fun x => f x - (h x + c))) ≤ ENNReal.ofReal (ε / 2) := by
    refine (hbd τ ⟨hτ, le_rfl⟩ _ hu).trans ?_
    calc ENNReal.ofReal C * ulNormE k θ (fun x => f x - (h x + c)) ≤ ENNReal.ofReal C * ENNReal.ofReal δ :=
          mul_le_mul' le_rfl hle
      _ = ENNReal.ofReal (C * δ) := (ENNReal.ofReal_mul hC.le).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hδ]
          have : C * (ε / (2 * (C + 1))) = (C / (C + 1)) * (ε / 2) := by field_simp
          rw [this]
          have : C / (C + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith [div_nonneg hC.le (by positivity : (0 : ℝ) ≤ C + 1)]
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 hle'
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end HRS.MS.Ul
