import HRS.MS.R26T8AB03b

/-!
# S8.2 T8A B03: `r26t8a_old_noise` (Pro contract, verbatim)
`S05` (`r26t8a_fixed_interval_ito_parameter`) applied to `H t r = noiseAge 0 (a0+t) r`, `Hd t r = noiseAge 1 (a0+t) r`
on `[l,h]`; the gradient age FTC is B03b, joint measurability is O04c, progressive `L²` is O04 + B03a, and the energies
are bounded by B03a.  The constant is `B = √(2+2T²) √(2/β) C Cf`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 25600000 in
theorem r26t8a_old_noise (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C) (hCf : 0≤Cf) (hc : 0<c)
    (T : ℝ) (hT : 0<T) :
    ∃ B : ℝ, 0≤B ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
      r26t8a_NormalFormFamily d a beta M C rho Psi →
      r26t8a_FeatureOrbits d a beta m Cf c rho →
      ∀ N : ℕ, 2≤N → ∀ {Omega : Type} [mOmega : MeasurableSpace Omega],
      ∀ P : Measure Omega, ∀ [IsProbabilityMeasure P],
      ∀ X0 : Omega → EucConfig d N, ∀ W : ℝ≥0 → Omega → Fin N → Euc d,
      ∀ X : ℝ≥0 → Omega → EucConfig d N,
      IsCanonicalRealization d (criticalS d) a beta N P X0 W X →
      ∀ a0 : ℝ, 0≤a0 → ∀ alpha : MultiIndex d,
      ∀ F : Filtration ℝ mOmega, ∀ W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ,
      IsWholeFilteredSolution P F W' W X →
      ∀ j : ℕ, ∀ l h : ℝ, 0≤l → l≤h → h≤a0-(j:ℝ) → h-l≤1 →
      ∃ G : ℝ → Omega → ℝ, Measurable (Function.uncurry G) ∧
        (∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T)) ∧
        (∀ t∈Set.Icc 0 T, G t =ᵐ[P] itoIntegral P F W'
          (r26t8a_clipIntegrand l h (r26t8a_noiseAge a beta m rho Psi alpha X 0 (a0+t))) h) ∧
        (r26t8a_scalarSupSq P T G)^(1/2:ℝ)≤ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))*Real.exp (-c*(j:ℝ))) := by
  classical
  refine ⟨Real.sqrt (2 + 2 * T ^ 2) * Real.sqrt (2 / beta) * C * Cf, by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha F W' hfilt j l h hl hlh hha hhl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set E : ℝ := Real.exp (-2 * c * (j : ℝ)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set K : ℝ := (2 / beta) * (C * Cf * w0) ^ 2 / (N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hh0 : 0 ≤ h := hl.trans hlh
  -- the integrands
  set H : ℝ → ℝ → Omega → Fin N × Fin d → ℝ := fun t r w i => r26t8a_noiseAge a beta m rho Psi alpha X 0 (a0 + t) r w i
    with hH
  set Hd : ℝ → ℝ → Omega → Fin N × Fin d → ℝ := fun t r w i => r26t8a_noiseAge a beta m rho Psi alpha X 1 (a0 + t) r w i
    with hHd
  have hsub : ∀ t : ℝ, 0 ≤ t → ∀ jj : ℕ, jj ≤ 1 →
      r26t8a_clipIntegrand l h (r26t8a_noiseAge a beta m rho Psi alpha X jj (a0 + t)) =
        r26t8a_clipIntegrand l h (r26t8a_clipIntegrand 0 (a0 + t) (r26t8a_noiseAge a beta m rho Psi alpha X jj (a0 + t))) := by
    intro t ht jj hjj
    funext r w i
    unfold r26t8a_clipIntegrand
    by_cases hr : r ∈ Set.Icc l h
    · have : r ∈ Set.Icc (0 : ℝ) (a0 + t) := ⟨hl.trans hr.1, by linarith [hr.2, hha, ht]⟩
      rw [if_pos hr, if_pos hr, if_pos this]
    · rw [if_neg hr, if_neg hr]
  have hprog : ∀ jj : ℕ, jj ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsProgressiveL2 P F (r26t8a_clipIntegrand l h (r26t8a_noiseAge a beta m rho Psi alpha X jj (a0 + t))) := by
    intro jj hjj t ht
    rw [hsub t ht.1 jj hjj]
    obtain ⟨-, hL2, -⟩ := r26t8a_noise_regular d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
      P X0 W X hX F W' hfilt alpha jj hjj
    exact r26t8a_b03_clip_L2 (hL2 (a0 + t) (by linarith [ht.1])) l h
  have hXm : Measurable (fun q : ℝ × Omega => X q.1.toNNReal q.2) := r26t8a_o04_X_meas hfilt.progressive
  have hmeasHd : Measurable (fun p : (ℝ × ℝ) × Omega => Hd p.1.1 p.1.2 p.2) := by
    refine measurable_pi_iff.2 fun i => ?_
    have hG := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1 le_rfl i
    have hcomp : Measurable (fun p : (ℝ × ℝ) × Omega => (a0 + p.1.1, p.1.2, X p.1.2.toNNReal p.2)) :=
      (measurable_const.add (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk
          (hXm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    exact hG.comp hcomp
  -- energies
  have hEn : ∀ jj : ℕ, jj ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
      r26t8a_itoEnergy P (r26t8a_noiseAge a beta m rho Psi alpha X jj (a0 + t)) l h ≤
        ENNReal.ofReal (K * E * (h - l)) := by
    intro jj hjj t ht
    refine r26t8a_b03_energy_interval d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX
      F W' hfilt alpha jj hjj l h (a0 + t) E hl hlh (by linarith [ht.1]) ?_
    intro r hr
    refine Real.exp_le_exp.2 ?_
    have : (j : ℝ) ≤ a0 + t - r := by linarith [hr.2, ht.1]
    nlinarith
  have hHdE : (∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) l h) ≤
      ENNReal.ofReal (K * E * (h - l)) * ENNReal.ofReal T := by
    calc (∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) l h) ≤ ∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (K * E * (h - l)) :=
          setLIntegral_mono' measurableSet_Icc fun t ht => hEn 1 le_rfl t ht
      _ = _ := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
          simp [hT.le]
  have he : (∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) l h) < ⊤ :=
    lt_of_le_of_lt hHdE (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- the pathwise FTC
  have hgood : ∀ᵐ w ∂P, ∀ r ∈ Set.Icc l h, X r.toNNReal w ∉ eucCollisionSet d N := by
    filter_upwards [(hX.solution h).no_collision] with w hw r hr
    exact hw r.toNNReal (by rw [Real.coe_toNNReal r (hl.trans hr.1)]; exact hr.2)
  have hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, H t p.1 p.2 i = H 0 p.1 p.2 i + ∫ v in Set.Icc 0 t, Hd v p.1 p.2 i := by
    have h1 : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P), p.1 ∈ Set.Icc l h :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have h2 : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P), ∀ r ∈ Set.Icc l h, X r.toNNReal p.2 ∉ eucCollisionSet d N :=
      Measure.quasiMeasurePreserving_snd.ae hgood
    filter_upwards [h1, h2] with p hp1 hp2
    intro i
    obtain ⟨r, w⟩ := p
    simp only at hp1 hp2 ⊢
    have hx := hp2 r hp1
    have hr0 : 0 ≤ r := hl.trans hp1.1
    have hra : r ≤ a0 := by linarith [hp1.2, hha, hj0]
    obtain ⟨hc1, hftc⟩ := r26t8a_b03_cg_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
      (X r.toNNReal w) hx (a0 - r) T (by linarith) i.1 i.2
    have hrw : ∀ t : ℝ, a0 + t - r = (a0 - r) + t := fun t => by ring
    have hform : ∀ (jj : ℕ) (t : ℝ), 0 ≤ t → r26t8a_noiseAge a beta m rho Psi alpha X jj (a0 + t) r w i =
        Real.sqrt (2 / beta) * Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha jj ((a0 - r) + t))
          (X r.toNNReal w) i.1 i.2 := by
      intro jj t ht
      unfold r26t8a_noiseAge
      rw [if_pos ⟨hr0, by linarith, hx⟩, hrw]
    refine ⟨?_, fun t ht => ?_⟩
    · have hc2 : ContinuousOn (fun t => Hd t r w i) (Set.Icc 0 T) := by
        have := hc1.const_smul (Real.sqrt (2 / beta))
        refine (this.congr (fun t ht => ?_))
        simp only [hHd, smul_eq_mul]
        exact hform 1 t ht.1
      exact hc2.integrableOn_Icc
    · have e1 : H t r w i = Real.sqrt (2 / beta) *
          Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 ((a0 - r) + t)) (X r.toNNReal w) i.1 i.2 :=
        hform 0 t ht.1
      have e0 : H 0 r w i = Real.sqrt (2 / beta) *
          Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 ((a0 - r) + 0)) (X r.toNNReal w) i.1 i.2 :=
        hform 0 0 le_rfl
      have e2 : ∫ v in Set.Icc 0 t, Hd v r w i = Real.sqrt (2 / beta) *
          ∫ s in Set.Icc 0 t, Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 ((a0 - r) + s))
            (X r.toNNReal w) i.1 i.2 := by
        rw [← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Icc fun s hs => hform 1 s hs.1
      rw [e1, e0, e2, hftc t ht]
      ring
  obtain ⟨G, Gd, hGm, hGdm, hGc, hGeq, hGdeq, hGFTC, hsup⟩ := r26t8a_fixed_interval_ito_parameter P F W' hfilt.brownian
    l h T hl hlh hT H Hd (fun t ht => hprog 0 (by norm_num) t ht) (fun t ht => hprog 1 le_rfl t ht)
    hmeasHd.aestronglyMeasurable he hFTC
  refine ⟨G, hGm, hGc, hGeq, ?_⟩
  have hH0 := hEn 0 (by norm_num) 0 ⟨le_rfl, hT.le⟩
  have hsup' : r26t8a_scalarSupSq P T G ≤ ENNReal.ofReal ((2 + 2 * T ^ 2) * (K * E)) := by
    refine hsup.trans ?_
    have hKE : 0 ≤ K * E := mul_nonneg hK0 hE0
    have hle1 : K * E * (h - l) ≤ K * E := by nlinarith [hhl, hKE, hlh]
    calc 2 * r26t8a_itoEnergy P (H 0) l h + ENNReal.ofReal (2 * T) * ∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) l h
        ≤ 2 * ENNReal.ofReal (K * E) + ENNReal.ofReal (2 * T) * (ENNReal.ofReal (K * E) * ENNReal.ofReal T) :=
          add_le_add (mul_le_mul_of_nonneg_left (hH0.trans (ENNReal.ofReal_le_ofReal hle1)) (zero_le))
            (mul_le_mul_of_nonneg_left (hHdE.trans (mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal hle1) (zero_le))) (zero_le))
      _ = ENNReal.ofReal ((2 + 2 * T ^ 2) * (K * E)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  set Yv : ℝ := Real.sqrt (2 + 2 * T ^ 2) * Real.sqrt (2 / beta) * C * Cf * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-c * (j : ℝ)) with hYv
  have hYv0 : 0 ≤ Yv := by positivity
  have hNrt : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  have hexp : Real.exp (-c * (j : ℝ)) ^ 2 = E := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hYsq : Yv ^ 2 = (2 + 2 * T ^ 2) * (K * E) := by
    have h2 : Real.sqrt (2 + 2 * T ^ 2) ^ 2 = 2 + 2 * T ^ 2 := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (2 / beta) ^ 2 = 2 / beta := Real.sq_sqrt (by positivity)
    have : Yv ^ 2 = Real.sqrt (2 + 2 * T ^ 2) ^ 2 * Real.sqrt (2 / beta) ^ 2 * (C * Cf * w0) ^ 2 *
        ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-c * (j : ℝ)) ^ 2 := by rw [hYv]; ring
    rw [this, h2, h3, hNrt, hexp, hK]
    field_simp
  calc (r26t8a_scalarSupSq P T G) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal ((2 + 2 * T ^ 2) * (K * E))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsup' (by norm_num)
    _ = ENNReal.ofReal Yv := by
        rw [← hYsq, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hYv0]
    _ = _ := rfl

end HRS.MS.R26T8A

end
