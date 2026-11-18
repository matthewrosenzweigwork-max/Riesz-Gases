import HRS.MS.UlocMWAux1
import HRS.MS.UlocMWAux3
import HRS.Whole.AppendixALemmas

/-!
# MS-ULOC-MW (B): Lemma S.A.31(iv), `H^m_uloc ⊂ H^m(ϖ)`

Route (S L11006-11007): cover `ℝ^d` by the unit cells `Q_z = z + [0,1]^d`; each cell is covered by `N(d)` balls
`B(z + y_j, 1)` on which `χ(· - (z + y_j)) ≡ 1`, so `∂^α u = ∂^α (χ_w u)` there and
`∫_{B} |∂^α u|² ≤ ‖χ_w u‖²_{H^m} ≤ ‖u‖²_{H^m_uloc}` (Plancherel, `UlocMWAux1.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.UlocWeighted
open HRS.MS.UlocMW

variable {d : ℕ}

theorem uw_pd_eq {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (u : Euc d → ℝ) {n : ℕ} (i : Fin n → Fin d)
    (w x : Euc d) (hx : x ∈ Metric.ball w 1) :
    partialDeriv i (fun y => χ (y - w) * u y) x = partialDeriv i u x := by
  have h : (fun y => χ (y - w) * u y) =ᶠ[𝓝 x] u := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have : χ (y - w) = 1 := hχ.2.2.2.2 _ (by
      rw [mem_closedBall_zero_iff, ← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
    rw [this, one_mul]
  unfold partialDeriv
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]

theorem uw_ball_le {m : ℕ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ}
    (hu : ContDiff ℝ m u) {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (w : Euc d) :
    ∫⁻ x in Metric.ball w 1, ENNReal.ofReal ((partialDeriv i u x) ^ 2) ≤ ulocNormE m χ u ^ 2 := by
  set f : Euc d → ℝ := fun x => χ (x - w) * u x with hf
  have hχm : ContDiff ℝ m χ := hχ.1.of_le (by exact_mod_cast le_top)
  have hfd : ContDiff ℝ m f := (hχm.comp (contDiff_id.sub contDiff_const)).mul hu
  have hχc : HasCompactSupport (fun x => χ (x - w)) :=
    hχ.2.1.comp_homeomorph (Homeomorph.subRight w)
  have hfc : HasCompactSupport f := hχc.mul_right
  calc ∫⁻ x in Metric.ball w 1, ENNReal.ofReal ((partialDeriv i u x) ^ 2)
      = ∫⁻ x in Metric.ball w 1, ENNReal.ofReal ((partialDeriv i f x) ^ 2) := by
        refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x hx => ?_
        rw [hf, uw_pd_eq hχ u i w x hx]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((partialDeriv i f x) ^ 2) := setLIntegral_le_lintegral _ _
    _ ≤ HRS.Whole.sobolevNormE (m : ℝ) f ^ 2 := um_deriv_le hfd hfc hn i
    _ ≤ ulocNormE m χ u ^ 2 := by
        apply pow_le_pow_left' _ 2
        exact le_iSup (fun z : Euc d => HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) w

theorem uw_net (d : ℕ) : ∃ Y : Finset (Euc d), ∀ p : Euc d, ‖p‖ ≤ Real.sqrt d →
    ∃ y ∈ Y, ‖p - y‖ < 1 := by
  obtain ⟨t, hts, htf, hcov⟩ := (isCompact_closedBall (0 : Euc d) (Real.sqrt d)).finite_cover_balls one_pos
  refine ⟨htf.toFinset, fun p hp => ?_⟩
  have := hcov (mem_closedBall_zero_iff.2 hp)
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
  obtain ⟨y, hy, hpy⟩ := this
  exact ⟨y, htf.mem_toFinset.2 hy, by rwa [← dist_eq_norm]⟩

theorem uw_cell_le {m : ℕ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ}
    (hu : ContDiff ℝ m u) {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (Y : Finset (Euc d))
    (hY : ∀ p : Euc d, ‖p‖ ≤ Real.sqrt d → ∃ y ∈ Y, ‖p - y‖ < 1) (z : Fin d → ℤ) :
    ∫⁻ x in uw_cell z, ENNReal.ofReal ((partialDeriv i u x) ^ 2) ≤
      (Y.card : ℝ≥0∞) * ulocNormE m χ u ^ 2 := by
  have hsub : uw_cell z ⊆ ⋃ y : Y, Metric.ball (latticePt z + (y : Euc d)) 1 := by
    intro x hx
    have h1 : ‖x - latticePt z‖ ≤ Real.sqrt d :=
      Real.le_sqrt_of_sq_le (uw_cell_norm hx)
    obtain ⟨y, hy, hxy⟩ := hY _ h1
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have : x - (latticePt z + y) = x - latticePt z - y := by abel
    rw [this]; exact hxy
  calc ∫⁻ x in uw_cell z, ENNReal.ofReal ((partialDeriv i u x) ^ 2)
      ≤ ∫⁻ x in ⋃ y : Y, Metric.ball (latticePt z + (y : Euc d)) 1,
          ENNReal.ofReal ((partialDeriv i u x) ^ 2) := lintegral_mono_set hsub
    _ ≤ ∑' y : Y, ∫⁻ x in Metric.ball (latticePt z + (y : Euc d)) 1,
          ENNReal.ofReal ((partialDeriv i u x) ^ 2) := lintegral_iUnion_le _ _
    _ ≤ ∑' _y : Y, ulocNormE m χ u ^ 2 :=
        ENNReal.tsum_le_tsum fun y => uw_ball_le hχ hu hn i _
    _ = (Y.card : ℝ≥0∞) * ulocNormE m χ u ^ 2 := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

theorem uw_pd_cont {m : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ m u) {n : ℕ} (hn : n ≤ m)
    (i : Fin n → Fin d) : Continuous (partialDeriv i u) := by
  have h1 : Continuous (iteratedFDeriv ℝ n u) := hu.continuous_iteratedFDeriv (by exact_mod_cast hn)
  exact (continuous_eval_const (fun t : Fin n => (EuclideanSpace.single (i t) (1 : ℝ) : Euc d))).comp h1

theorem uw_tuple_le {m : ℕ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ}
    (hu : ContDiff ℝ m u) {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (Y : Finset (Euc d))
    (hY : ∀ p : Euc d, ‖p‖ ≤ Real.sqrt d → ∃ y ∈ Y, ‖p - y‖ < 1) (ϖ : Euc d → ℝ)
    (hϖ : ∀ x, 0 ≤ ϖ x) :
    ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2) ≤
      cellSupSum ϖ * ((Y.card : ℝ≥0∞) * ulocNormE m χ u ^ 2) := by
  have hpc := uw_pd_cont hu hn i
  calc ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2)
      = ∫⁻ x in ⋃ z : Fin d → ℤ, uw_cell z, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2) := by
        rw [uw_cell_cover, Measure.restrict_univ]
    _ ≤ ∑' z : Fin d → ℤ, ∫⁻ x in uw_cell z, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' z : Fin d → ℤ, (⨆ x ∈ uw_cell z, ENNReal.ofReal (ϖ x)) *
          ((Y.card : ℝ≥0∞) * ulocNormE m χ u ^ 2) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        calc ∫⁻ x in uw_cell z, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2)
            ≤ ∫⁻ x in uw_cell z, (⨆ x ∈ uw_cell z, ENNReal.ofReal (ϖ x)) *
                ENNReal.ofReal ((partialDeriv i u x) ^ 2) := by
              refine setLIntegral_mono' (uw_cell_closed z).measurableSet fun x hx => ?_
              rw [ENNReal.ofReal_mul (hϖ x)]
              have := le_iSup₂ (f := fun x (_ : x ∈ uw_cell z) => ENNReal.ofReal (ϖ x)) x hx
              gcongr
          _ = (⨆ x ∈ uw_cell z, ENNReal.ofReal (ϖ x)) *
                ∫⁻ x in uw_cell z, ENNReal.ofReal ((partialDeriv i u x) ^ 2) :=
              lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hpc.pow 2).measurable)
          _ ≤ _ := by
              have := uw_cell_le hχ hu hn i Y hY z
              gcongr
    _ = cellSupSum ϖ * ((Y.card : ℝ≥0∞) * ulocNormE m χ u ^ 2) := by
        rw [ENNReal.tsum_mul_right]
        rfl

theorem uw_part1 (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ ϖ : Euc d → ℝ, (∀ x, 0 ≤ ϖ x) → ∀ u : Euc d → ℝ, ContDiff ℝ m u →
      weightedHE m ϖ u ≤ ENNReal.ofReal C * (cellSupSum ϖ) ^ (1 / 2 : ℝ) * ulocNormE m χ u := by
  obtain ⟨Y, hY⟩ := uw_net d
  set M : ℕ := ∑ j ∈ Finset.range (m + 1), d ^ j with hM
  refine ⟨Real.sqrt ((M : ℝ) * (Y.card : ℝ)), fun ϖ hϖ u hu => ?_⟩
  set U := ulocNormE m χ u with hU
  set S := cellSupSum ϖ with hS
  set c : ℝ≥0∞ := S * ((Y.card : ℝ≥0∞) * U ^ 2) with hc
  have hsum : ∑ j ∈ Finset.range (m + 1), ∑ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2) ≤ (M : ℝ≥0∞) * c := by
    calc _ ≤ ∑ j ∈ Finset.range (m + 1), ∑ _i : Fin j → Fin d, c := by
          refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ => ?_
          exact uw_tuple_le hχ hu (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i Y hY ϖ hϖ
      _ = (M : ℝ≥0∞) * c := by
          have hcount : ∀ j : ℕ, ∑ _i : Fin j → Fin d, c = (d ^ j : ℕ) • c := by
            intro j
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin]
          simp_rw [hcount, nsmul_eq_mul]
          rw [← Finset.sum_mul, hM]
          push_cast
          rfl
  unfold weightedHE
  calc (∑ j ∈ Finset.range (m + 1), ∑ i : Fin j → Fin d,
          ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ((M : ℝ≥0∞) * c) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt ((M : ℝ) * (Y.card : ℝ))) * S ^ (1 / 2 : ℝ) * U := by
        have e1 : (M : ℝ≥0∞) * c = (ENNReal.ofReal ((M : ℝ) * (Y.card : ℝ)) * S) * U ^ 2 := by
          rw [hc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
          ring
        rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_natCast U 2, ← ENNReal.rpow_mul]
        have e2 : ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
        rw [e2, ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (by norm_num), Real.sqrt_eq_rpow]

theorem uw_part2 :
    cellSupSum (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) < ⊤ := by
  have h : cellSupSum (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) ≤
      ∑' z : Fin d → ℤ, ENNReal.ofReal (Real.sqrt (2 * (1 + d)) ^ ((d : ℝ) + 3)) *
        ENNReal.ofReal (jbracket (latticePt z) ^ (-((d : ℝ) + 3))) :=
    ENNReal.tsum_le_tsum fun z => uw_cellsup_le z
  rw [ENNReal.tsum_mul_left] at h
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top uw_S_lt_top)

theorem uw_jb_smul_ge {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : Euc d) :
    c * jbracket x ≤ jbracket (c • x) := by
  unfold jbracket
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, mul_pow]
  calc c * Real.sqrt (1 + ‖x‖ ^ 2) = Real.sqrt (c ^ 2 * (1 + ‖x‖ ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0]
    _ ≤ Real.sqrt (1 + c ^ 2 * ‖x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) (sq_nonneg ‖x‖)]

theorem uw_Sfine_lt_top :
    (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)))) < ⊤ := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    haveI : Unique (Fin 0 → ℤ) := inferInstance
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top
  · set k : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hk
    have hk1 : 1 ≤ k := by
      have h1 : (1 : ℝ) ≤ Real.sqrt d := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
      have h2 : (1 : ℤ) ≤ ⌈Real.sqrt d⌉ := by
        rw [Int.one_le_ceil_iff]; linarith
      rw [hk]; exact_mod_cast h2
    have hkpos : 0 < k := by linarith
    have hp : 0 ≤ (d : ℝ) + 3 := by positivity
    have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) ≤
        ENNReal.ofReal (k ^ ((d : ℝ) + 3)) *
          ENNReal.ofReal (jbracket (latticePt z) ^ (-((d : ℝ) + 3))) := by
      intro z
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hkpos.le _)]
      apply ENNReal.ofReal_le_ofReal
      have hc : cellPt d z = k⁻¹ • latticePt z := rfl
      have hge := uw_jb_smul_ge (inv_nonneg.2 hkpos.le) (inv_le_one_of_one_le₀ hk1) (latticePt z)
      have hjpos : 0 < jbracket (latticePt z) := Real.sqrt_pos.2 (by positivity)
      have hcpos : 0 < k⁻¹ * jbracket (latticePt z) := mul_pos (inv_pos.2 hkpos) hjpos
      rw [hc]
      calc jbracket (k⁻¹ • latticePt z) ^ (-((d : ℝ) + 3))
          ≤ (k⁻¹ * jbracket (latticePt z)) ^ (-((d : ℝ) + 3)) :=
            Real.rpow_le_rpow_of_nonpos hcpos hge (by linarith)
        _ = k ^ ((d : ℝ) + 3) * jbracket (latticePt z) ^ (-((d : ℝ) + 3)) := by
            rw [Real.mul_rpow (inv_nonneg.2 hkpos.le) hjpos.le, Real.inv_rpow hkpos.le,
              Real.rpow_neg hkpos.le, inv_inv]
    calc (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))))
        ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal (k ^ ((d : ℝ) + 3)) *
            ENNReal.ofReal (jbracket (latticePt z) ^ (-((d : ℝ) + 3))) :=
          ENNReal.tsum_le_tsum hpt
      _ < ⊤ := by
          rw [ENNReal.tsum_mul_left]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top uw_S_lt_top

theorem uw_part3 (m : ℕ) (χ : Euc d → ℝ) :
    ∃ C : ℝ, ∀ u : Euc d → ℝ, varpiNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ u := by
  set S : ℝ≥0∞ := ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)))
    with hS
  have hSt : S ≠ ⊤ := uw_Sfine_lt_top.ne
  refine ⟨Real.sqrt S.toReal, fun u => ?_⟩
  unfold varpiNormE
  set U := ulocNormE m χ u with hU
  calc (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * u x) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * U ^ 2) ^
          (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        refine ENNReal.tsum_le_tsum fun z => ?_
        have : HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * u x) ≤ U :=
          le_iSup (fun w : Euc d => HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - w) * u x)
            (cellPt d z)
        gcongr
    _ = ENNReal.ofReal (Real.sqrt S.toReal) * U := by
        rw [ENNReal.tsum_mul_right, ← hS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_natCast U 2, ← ENNReal.rpow_mul]
        have e2 : ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
        rw [e2, ENNReal.rpow_one, Real.sqrt_eq_rpow,
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
        rw [ENNReal.ofReal_toReal hSt]

/-- Lemma S.A.31(iv) -/
theorem uloc_embedding_weighted_proof (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    (∃ C : ℝ, ∀ ϖ : Euc d → ℝ, (∀ x, 0 ≤ ϖ x) → ∀ u : Euc d → ℝ, ContDiff ℝ m u →
      weightedHE m ϖ u ≤ ENNReal.ofReal C * (cellSupSum ϖ) ^ (1 / 2 : ℝ) * ulocNormE m χ u) ∧
    cellSupSum (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) < ⊤ ∧
    (∃ C : ℝ, ∀ u : Euc d → ℝ, varpiNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ u) :=
  ⟨uw_part1 m χ hχ, uw_part2, uw_part3 m χ⟩

example := (@uloc_embedding_weighted_proof : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_weighted)

end HRS.MS.UlocWeighted
