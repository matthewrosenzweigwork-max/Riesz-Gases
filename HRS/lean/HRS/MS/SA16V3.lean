import HRS.MS.SA16V2
import HRS.MS.SA16StrongSL4
import HRS.MS.SA16StrongSL5
import HRS.MS.SA16StrongLeib
import HRS.MS.SA16JetConvDiff
import HRS.MS.SA16EvolDefs

/-!
# S.A.16 A2, part 3: `W^{m,p} ⊂ H^1_uloc`

`sa16v_uloc_of_wmp`: for `m ≥ 1`, `p ≥ 2` and a uniformly local cutoff `χ` there is `K` such that every
`u` which is the zeroth component of `G ∈ W^{m,p}` has `‖u‖_{H^1_uloc} ≤ K (‖G‖ + 1)`.  Smooth jets: pointwise
Leibniz for `χ(·-z) u` plus the ball estimate of part 2; general `G`: smooth approximation and the lower
semicontinuity `local_norm_lower_semicontinuity` of S.A.12.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16V
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section Part3
variable {d : ℕ}

lemma sa16v_cut_deriv_bound {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Euc d, ∀ i ≤ 1, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ B := by
  have hs : ∀ i : ℕ, ∃ Bi : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ Bi := fun i =>
    (hχ.2.1.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      (hχ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  obtain ⟨B0, h0⟩ := hs 0
  obtain ⟨B1, h1⟩ := hs 1
  refine ⟨max (max B0 B1) 0, le_max_right _ _, fun z i hi x => ?_⟩
  have e : (fun y => χ (y - z)) = fun y => χ (y + -z) := by funext y; rw [sub_eq_add_neg]
  rw [e, iteratedFDeriv_comp_add_right]
  interval_cases i
  · exact (h0 _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 _).trans ((le_max_right _ _).trans (le_max_left _ _))

lemma sa16v_cut_support {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (z : Euc d) :
    tsupport (fun y => χ (y - z)) ⊆ Metric.ball z 2 := by
  have hcl : IsClosed {y : Euc d | y - z ∈ tsupport χ} :=
    (isClosed_tsupport χ).preimage (continuous_id.sub continuous_const)
  have h1 : tsupport (fun y => χ (y - z)) ⊆ {y : Euc d | y - z ∈ tsupport χ} := by
    refine closure_minimal (fun y hy => ?_) hcl
    exact subset_tsupport χ hy
  refine h1.trans fun y hy => ?_
  have := hχ.2.2.1 hy
  simpa [Metric.mem_ball, dist_eq_norm] using this

lemma sa16v_smooth_uloc (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] {χ : Euc d → ℝ}
    (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Euc d → ℝ, ContDiff ℝ ∞ u → ∀ b : ℝ, 0 ≤ b →
      eLpNorm (fun x => ‖wJet m u x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal b →
      ulocNormE 1 χ u ≤ ENNReal.ofReal (K * b) := by
  obtain ⟨B, hB0, hB⟩ := sa16v_cut_deriv_bound hχ
  set c : ℝ := B * ((d : ℝ) + 1) ^ 1 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Real.sqrt (1 + (d : ℝ) ^ 3) * sa16v_K1 d p * c, by
    have := sa16v_K1_nonneg d p
    positivity, fun u hu b hb hF => ?_⟩
  unfold ulocNormE
  refine iSup_le fun z => ?_
  have ha : ContDiff ℝ ∞ (fun y => χ (y - z)) := hχ.1.comp (contDiff_id.sub contDiff_const)
  have hv : ContDiff ℝ ∞ (fun x => χ (x - z) * u x) := ha.mul hu
  have hsupp : tsupport (fun x => χ (x - z) * u x) ⊆ Metric.ball z 2 :=
    (tsupport_mul_subset_left).trans (sa16v_cut_support hχ z)
  have hpt : ∀ x, ‖(fun x => ‖wJet 1 (fun x => χ (x - z) * u x) x‖) x‖ ≤ c * ‖wJet m u x‖ := by
    intro x
    have h1 := sa16y_prod_jet_le ha hu 1 x (B := B) (fun i hi => hB z i hi x)
    have h2 := sa16y_jet_mono hm u x
    simp only [norm_norm]
    calc ‖wJet 1 (fun x => χ (x - z) * u x) x‖ ≤ B * ((d : ℝ) + 1) ^ 1 * ‖wJet 1 u x‖ := h1
      _ ≤ c * ‖wJet m u x‖ := mul_le_mul_of_nonneg_left h2 hc0
  have hF1 : eLpNorm (fun x => ‖wJet 1 (fun x => χ (x - z) * u x) x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (c * b) := by
    refine (eLpNorm_mono_real (sa16j_jet_cont hv 1).norm.aestronglyMeasurable hpt).trans ?_
    have e : (fun x => c * ‖wJet m u x‖) = c • (fun x => ‖wJet m u x‖) := by
      funext x; simp
    rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hc0, ENNReal.ofReal_mul hc0]
    exact mul_le_mul' le_rfl hF
  have := sa16v_sob_bound p hv hsupp (mul_nonneg hc0 hb) hF1
  rw [Nat.cast_one]
  refine this.trans (le_of_eq ?_)
  congr 1
  ring

lemma sa16v_eLpNorm_eq (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : WmpSpace d m p) :
    eLpNorm (fun x => ‖((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖) (ENNReal.ofReal p) volume =
      ENNReal.ofReal ‖G‖ := by
  rw [eLpNorm_norm _ (Lp.aestronglyMeasurable (G : WLp d m p))]
  have hfin : eLpNorm (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) (ENNReal.ofReal p) volume < ⊤ :=
    Lp.eLpNorm_lt_top _
  have : ‖G‖ = ‖(G : WLp d m p)‖ := rfl
  rw [this, Lp.norm_def, ENNReal.ofReal_toReal hfin.ne]

theorem sa16v_uloc_of_wmp (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] {χ : Euc d → ℝ}
    (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : WmpSpace d m p) (u : Euc d → ℝ), wrep d m p G =ᵐ[volume] u →
      ulocNormE 1 χ u ≤ ENNReal.ofReal (K * (‖G‖ + 1)) := by
  obtain ⟨K, hK0, hK⟩ := sa16v_smooth_uloc m hm p hχ
  refine ⟨K, hK0, fun G u hGu => ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  -- smooth approximants
  obtain ⟨Gs, hGs, hGlim⟩ := mem_closure_iff_seq_limit.1 (wmp_smooth_dense d m p G)
  choose uu hcc hjet using hGs
  have hnorm_ev : ∀ᶠ i in atTop, ‖Gs i‖ < ‖G‖ + 1 :=
    hGlim.norm.eventually (gt_mem_nhds (by linarith : ‖G‖ < ‖G‖ + 1))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hnorm_ev
  set Gt : ℕ → WmpSpace d m p := fun i => Gs (i + N0) with hGt
  set ut : ℕ → Euc d → ℝ := fun i => uu (i + N0) with hut
  have hGtlim : Tendsto Gt atTop (𝓝 G) := hGlim.comp (tendsto_add_atTop_nat N0)
  -- bound for the approximants
  have hB : ∀ n, ulocNormE 1 χ (ut n) ≤ ENNReal.ofReal (K * (‖G‖ + 1)) := by
    intro n
    have hnn : ‖Gt n‖ < ‖G‖ + 1 := hN0 _ (by omega)
    have hF : eLpNorm (fun x => ‖wJet m (ut n) x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖Gt n‖ := by
      rw [← sa16v_eLpNorm_eq m p (Gt n)]
      refine le_of_eq (eLpNorm_congr_ae ?_)
      filter_upwards [hjet (n + N0)] with x hx
      show ‖wJet m (uu (n + N0)) x‖ = ‖((Gs (n + N0) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖
      rw [hx]
    refine (hK (ut n) (hcc (n + N0)).1 ‖Gt n‖ (norm_nonneg _) hF).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnn.le hK0)
  -- local square integrability of the limit
  have hP : MemLp (wrep d m p G) (ENNReal.ofReal p) (volume : Measure (Euc d)) := by
    have hG' := Lp.memLp (G : WLp d m p)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).comp_memLp' hG'
  have huloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball (0 : Euc d) R)) := by
    intro R hR
    set ν : Measure (Euc d) := volume.restrict (Metric.ball (0 : Euc d) R) with hν
    have hae : wrep d m p G =ᵐ[ν] u := ae_restrict_of_ae hGu
    have hPν : MemLp (wrep d m p G) (ENNReal.ofReal p) ν := hP.restrict _
    have hle : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal (Fact.out : (2 : ℝ) ≤ p)
    have hfin : volume (Metric.ball (0 : Euc d) R) < ⊤ := measure_ball_lt_top
    have h2 : eLpNorm (wrep d m p G) 2 ν < ⊤ := by
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (p := 2) (q := ENNReal.ofReal p) hle
        hPν.aestronglyMeasurable
      refine lt_of_le_of_lt h (ENNReal.mul_lt_top hPν.eLpNorm_lt_top ?_)
      have hν1 : ν Set.univ < ⊤ := by
        rw [hν, Measure.restrict_apply_univ]; exact hfin
      refine ENNReal.rpow_lt_top_of_nonneg ?_ hν1.ne
      rw [ENNReal.toReal_ofReal (by linarith)]
      simp only [ENNReal.toReal_ofNat]
      have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (Fact.out : (2 : ℝ) ≤ p)
      linarith
    exact MemLp.ae_eq hae h2
  -- weak convergence against test functions
  have hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, ut n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x)) := by
    intro ψ hψ
    have hpair := sa16s_pair d m p (wZero d m) hψ.1.continuous hψ.2
    have hT : Tendsto (fun n => sa16s_pair d m p (wZero d m) hψ.1.continuous hψ.2 (Gt n : WLp d m p))
        atTop (𝓝 (sa16s_pair d m p (wZero d m) hψ.1.continuous hψ.2 (G : WLp d m p))) :=
      ((sa16s_pair d m p (wZero d m) hψ.1.continuous hψ.2).continuous.tendsto _).comp
        ((continuous_subtype_val.tendsto G).comp hGtlim)
    simp only [sa16s_pair_apply] at hT
    have e1 : ∀ n, ∫ x, ((Gt n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) * ψ x =
        ∫ x, ut n x * ψ x := by
      intro n
      refine integral_congr_ae ?_
      filter_upwards [hjet (n + N0)] with x hx
      show ((Gs (n + N0) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) * ψ x = _
      rw [hx]
      simp only [wJet, wZero]
      rw [sa16j_pd_zero]
    have e2 : ∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) * ψ x =
        ∫ x, u x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hGu] with x hx
      show wrep d m p G x * ψ x = _
      rw [hx]
    simp_rw [e1] at hT
    rwa [e2] at hT
  exact (HRS.MH.AdjointRd.Phase2SA12Limit.local_norm_lower_semicontinuity hd 1 χ hχ _ ut u huloc hconv hB).1

end Part3

end HRS.Whole.AppendixA.Phase2SA16V
