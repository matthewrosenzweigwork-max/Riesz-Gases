import HRS.Main.ThermLin2Ba1
import HRS.Main.ThermLinAux4

/-!
# THERMLIN2, packet Ba, part 2: A2 (`tl2_canonical`)

Refactor of the body of `HRS.ThermLin.thermlin_preparedLinear_exists` (ThermLinAux4): the Gaussian martingale, the dual
evolution and the stochastic convolution are built once, independently of the initial law `ν`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

/-- A2 proof. -/
theorem tl2_canonical_proof (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T' : ℝ) (hT' : 0 < T') :
    ∃ (Ωg : Type) (_ : MeasurableSpace Ωg) (Pg : Measure Ωg) (_ : IsProbabilityMeasure Pg)
      (ℱ : Filtration ℝ ‹MeasurableSpace Ωg›) (G Zs : ℝ → Ωg → NegSobolev d m)
      (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      IsDualEvolution S.dyn S.ρ m Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) ∧
      IsHilbertMartingaleWithCovariation Pg ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) ∧
      (∀ ω, Continuous fun s => G s ω) ∧ (∀ ω, G 0 ω = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T',
        IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) ∧
      (∀ t, Measurable (Zs t)) ∧ (∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 T')) ∧
      ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν],
        HRS.Main.IsPreparedLinear S m T' ν (ν.prod Pg) (fun p => p.1) (fun t p => Vev t 0 p.1 + Zs t p.2) := by
  have hd : 2 ≤ d := S.hd
  have hm2 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory hd htr m
  obtain ⟨Vev, hdual, hplain, hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  obtain ⟨C, hC0, hC⟩ := hB1 T' hT'
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
    intro u t hu hut
    rw [t25p_dual_unique hdual hdualA hu hut]
    exact hdecA u t hu hut
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hdec r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  -- Gaussian martingale with the covariation density of the noise
  obtain ⟨Ωg, mΩg, Pg, hPg, ℱ, G, hGc, hGz, hG⟩ := Q45.exists_gaussian_martingale T' hT'.le
    (covDensT m S.β⁻¹ T' S.ρ) (thermlin_detCov hd htr hm2 hT')
  -- its stochastic convolution
  have hG' : IsHilbertMartingaleWithCovariation Pg ℱ (0 + T') G
      (fun r _ => if r ≤ T' then covDensT m S.β⁻¹ T' S.ρ r else 0) := by
    rwa [zero_add]
  obtain ⟨Zs, hZS, hZc, hZm, -⟩ := hC Ωg Pg ℱ 0 T' le_rfl hT' le_rfl G _ hG'
  simp only [zero_add] at hZS hZc hZm
  obtain ⟨Zm, hZmm, hZmc, hZmae⟩ := thermlin_measurable_version (P := Pg) hT'.le Zs hZm hZc
  have hZb : ∀ t ∈ Set.Icc (0 : ℝ) T',
      IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zm t) :=
    fun t ht => thermlin_isStochConv_congr (hZS t ht) (hZmae t ht)
  have hCr0 : 0 ≤ Cr := hCr.le
  have hdual' : IsDualEvolution S.dyn S.ρ m Vev := hdual
  have hq : (0 : ℝ) ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  have hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} := (hplain T' hT'.le).2.2
  have hV00 : Vev 0 0 = 1 := (hplain T' hT'.le).1 0 ⟨le_rfl, hT'.le⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T' := ⟨le_rfl, hT'.le⟩
  have hZ0 : Zm 0 =ᵐ[Pg] fun _ => 0 := thermlin_stochConv_zero (hZb 0 h0) (hZmm 0)
  have hVcont : ∀ x : NegSobolev d m, ContinuousOn (fun t => Vev t 0 x) (Set.Icc 0 T') := fun x => by
    have := (hVc x).comp (f := fun t : ℝ => ((t, 0) : ℝ × ℝ)) (by fun_prop) (s := Set.Icc 0 T')
      (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
    exact this
  have hGstmt : IsHilbertMartingaleWithCovariation Pg ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) := by
    have e : (fun (r : ℝ) (_ : Ωg) => if r ≤ T' then covDensT m S.β⁻¹ T' S.ρ r else 0) =
        fun r _ => covDensT m S.β⁻¹ T' S.ρ r := by
      funext r ω
      by_cases hr : r ≤ T'
      · simp [hr]
      · have : covDensT m S.β⁻¹ T' S.ρ r = 0 := by
          unfold covDensT
          rw [if_neg]
          intro hh; exact hr hh.2
        simp [hr, this]
    rwa [e] at hG
  refine ⟨Ωg, mΩg, Pg, hPg, ℱ, G, Zm, Vev, hdual', hplain, ⟨Cr, cr, hCr0, hcr, hdec⟩, hGstmt, hGc, hGz, hZb,
    hZmm, hZmc, ?_⟩
  intro ν _
  refine ⟨measurable_fst, ?_, ?_, ?_, ?_, ?_⟩
  · -- law of the initial field
    show (ν.prod Pg).map Prod.fst = ν
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  · -- init
    have h1 : ∀ᵐ p ∂(ν.prod Pg), Zm 0 p.2 = 0 := (Measure.quasiMeasurePreserving_snd).ae hZ0
    filter_upwards [h1] with p hp
    show Vev 0 0 p.1 + Zm 0 p.2 = p.1
    rw [hV00, hp]; simp
  · -- continuity
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := Pg)).ae hZmc
    filter_upwards [h2] with p hp
    exact (hVcont p.1).add hp
  · -- measurability
    intro t
    exact (((Vev t 0).continuous.measurable).comp measurable_fst).add ((hZmm t).comp measurable_snd)
  · -- Gaussian part
    intro p ts φ hts hφ Gv
    have hmemφ : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
    set Gz : Ωg → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Zm (ts a) ω) (φ a) with hGz_def
    have hGzm : Measurable Gz :=
      HRS.Uniform.Q54c.measurable_toLp_eval fun a => (HRS.Uniform.Q54c.continuous_eval_const (hmemφ a)).measurable.comp (hZmm _)
    have hGeq : Gv = fun q => Gz q.2 := by
      funext q
      ext a
      show NegSobolev.eval (Vev (ts a) 0 q.1 + Zm (ts a) q.2) (φ a) -
        NegSobolev.eval q.1 (propagator S.dyn S.ρ 0 (ts a) (φ a)) = NegSobolev.eval (Zm (ts a) q.2) (φ a)
      rw [HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth m (hφ a)),
        hdual' 0 (ts a) le_rfl (hts a).1 q.1 (φ a) (hφ a)]
      ring
    refine ⟨?_, ?_⟩
    · rw [hGeq]
      exact (indepFun_prod (μ := ν) (ν := Pg) (X := (id : NegSobolev d m → NegSobolev d m)) (Y := Gz)
        measurable_id hGzm).symm
    · have hlaw : law (ν.prod Pg) Gv = Pg.map Gz := by
        rw [hGeq]
        show (ν.prod Pg).map (Gz ∘ Prod.snd) = Pg.map Gz
        rw [← Measure.map_map hGzm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
      rw [hlaw]
      have hmain := t25p_Zb_gaussian hCr0 hT' Vev hVc hKb Pg G
        (fun r => if r ≤ T' then covDensT m S.β⁻¹ T' S.ρ r else 0) hG hGc hGz Zm hZb hZmm ts hts φ hmemφ
      rw [hmain]
      congr 1
      ext a b
      simp only [Matrix.of_apply]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
      have hσT : σ ≤ T' := hσ.2.trans ((min_le_left _ _).trans (hts a).2)
      simp only [if_pos hσT]
      exact t25p_cov_eq hd htr hm2 hT' hdual hCr0 hKb hq (hts a) (hts b) hσ (hφ a) (hφ b)

example := (@tl2_canonical_proof : type_of% @tl2_canonical)

end HRS.ThermLin.Plan2
