import HRS.MS.R26T8AB06b
import HRS.MS.R26T8AS07

/-!
# S8.2 T8A B06: `r26t8a_recent_noise` (Pro contract, verbatim)
`S07` (`r26t8a_recent_ito_fubini`) applied to `H b r = noiseAge 0 b r`, `Hd b r = noiseAge 1 b r` on `a0 ≤ r ≤ b ≤ a0+T`.
The diagonal is progressive `L²` with energy `≤ K T` (B06a), the triangular FTC is B06b, the energies are B03a.
The constant is `B = √(T(8+2T²)) √(2/β) C Cf`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 25600000 in
theorem r26t8a_recent_noise (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
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
      ∃ G : ℝ → Omega → ℝ, Measurable (Function.uncurry G) ∧
        (∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T)) ∧
        (∀ t∈Set.Icc 0 T, G t =ᵐ[P] itoIntegral P F W'
          (r26t8a_clipIntegrand a0 (a0+t) (r26t8a_noiseAge a beta m rho Psi alpha X 0 (a0+t))) (a0+t)) ∧
        (r26t8a_scalarSupSq P T G)^(1/2:ℝ)≤ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))) := by
  classical
  refine ⟨Real.sqrt (T * (8 + 2 * T ^ 2)) * Real.sqrt (2 / beta) * C * Cf, by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha F W' hfilt
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set K : ℝ := (2 / beta) * (C * Cf * w0) ^ 2 / (N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set H : ℝ → ℝ → Omega → Fin N × Fin d → ℝ := fun b r w i => r26t8a_noiseAge a beta m rho Psi alpha X 0 b r w i
    with hH
  set Hd : ℝ → ℝ → Omega → Fin N × Fin d → ℝ := fun b r w i => r26t8a_noiseAge a beta m rho Psi alpha X 1 b r w i
    with hHd
  have hXm : Measurable (fun q : ℝ × Omega => X q.1.toNNReal q.2) := r26t8a_o04_X_meas hfilt.progressive
  -- progressive `L²` of the clipped slices
  have hsl : ∀ jj : ℕ, jj ≤ 1 → ∀ t ∈ Set.Icc a0 (a0 + T),
      IsProgressiveL2 P F (r26t8a_clipIntegrand a0 t (r26t8a_noiseAge a beta m rho Psi alpha X jj t)) := by
    intro jj hjj t ht
    have hsub : r26t8a_clipIntegrand a0 t (r26t8a_noiseAge a beta m rho Psi alpha X jj t) =
        r26t8a_clipIntegrand a0 t (r26t8a_clipIntegrand 0 t (r26t8a_noiseAge a beta m rho Psi alpha X jj t)) := by
      funext r w i
      unfold r26t8a_clipIntegrand
      by_cases hr : r ∈ Set.Icc a0 t
      · rw [if_pos hr, if_pos hr, if_pos ⟨ha0.trans hr.1, hr.2⟩]
      · rw [if_neg hr, if_neg hr]
    rw [hsub]
    obtain ⟨-, hL2, -⟩ := r26t8a_noise_regular d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
      P X0 W X hX F W' hfilt alpha jj hjj
    exact r26t8a_b03_clip_L2 (hL2 t (ha0.trans ht.1)) a0 t
  -- the diagonal
  have hdiagE := r26t8a_b06_diag_energy d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX
    F W' hfilt alpha a0 T ha0 hT.le
  have hdiag : IsProgressiveL2 P F (r26t8a_clipIntegrand a0 (a0 + T) (fun r w i => H r r w i)) := by
    refine ⟨?_, fun T' => ?_⟩
    · have hg : Measurable (fun q : ℝ × EucConfig d N => fun i : Fin N × Fin d =>
          if q.1 ∈ Set.Icc a0 (a0 + T) then r26t8a_o04_G d N a beta m rho Psi alpha 0 q.1 q.1 q.2 i else 0) := by
        refine measurable_pi_iff.2 fun i => ?_
        refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
        have hG := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
          (by norm_num) i
        exact hG.comp (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))
      exact r26t8a_o04_prog_time hfilt.progressive hg
    · have hle : sqIntegralOn P (r26t8a_clipIntegrand a0 (a0 + T) (fun r w i => H r r w i)) T' ≤
          r26t8a_itoEnergy P (fun r w i => r26t8a_noiseAge a beta m rho Psi alpha X 0 r r w i) a0 (a0 + T) := by
        unfold sqIntegralOn r26t8a_itoEnergy
        refine lintegral_mono fun w => ?_
        have hpt : ∀ s : ℝ, ∑ i, ‖r26t8a_clipIntegrand a0 (a0 + T) (fun r w i => H r r w i) s w i‖ₑ ^ 2 =
            (Set.Icc a0 (a0 + T)).indicator
              (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 s s w i‖ₑ ^ 2) s := by
          intro s
          by_cases hs : s ∈ Set.Icc a0 (a0 + T)
          · simp [r26t8a_clipIntegrand, hs, hH]
          · simp [r26t8a_clipIntegrand, hs]
        simp_rw [hpt]
        calc ∫⁻ s in Set.Icc (0 : ℝ) T', (Set.Icc a0 (a0 + T)).indicator
              (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 s s w i‖ₑ ^ 2) s
            ≤ ∫⁻ s, (Set.Icc a0 (a0 + T)).indicator
              (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 s s w i‖ₑ ^ 2) s :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ s in Set.Icc a0 (a0 + T), ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 s s w i‖ₑ ^ 2 :=
              lintegral_indicator measurableSet_Icc _
      exact lt_of_le_of_lt hle (lt_of_le_of_lt hdiagE ENNReal.ofReal_lt_top)
  -- measurability of `Hd`
  have hmeas : Measurable (fun p : (ℝ × ℝ) × Omega => if p.1.2 ≤ p.1.1 then Hd p.1.1 p.1.2 p.2 else 0) := by
    refine Measurable.ite (measurableSet_le (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_fst))
      ?_ measurable_const
    refine measurable_pi_iff.2 fun i => ?_
    have hG := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1 le_rfl i
    have hcomp : Measurable (fun p : (ℝ × ℝ) × Omega => (p.1.1, p.1.2, X p.1.2.toNNReal p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk
          (hXm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    exact hG.comp hcomp
  -- energy of the derivative field
  have hEn : ∀ v ∈ Set.Icc a0 (a0 + T), r26t8a_itoEnergy P (Hd v) a0 v ≤ ENNReal.ofReal (K * T) := by
    intro v hv
    have h1 := r26t8a_b03_energy_interval d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X
      hX F W' hfilt alpha 1 le_rfl a0 v v 1 ha0 hv.1 le_rfl (fun r hr => by
        have : Real.exp (-2 * c * (v - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.2])
        exact this)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hv.2, hK0]
  have hHdE : (∫⁻ v in Set.Icc a0 (a0 + T), r26t8a_itoEnergy P (Hd v) a0 v) ≤
      ENNReal.ofReal (K * T) * ENNReal.ofReal T := by
    calc (∫⁻ v in Set.Icc a0 (a0 + T), r26t8a_itoEnergy P (Hd v) a0 v) ≤
          ∫⁻ v in Set.Icc a0 (a0 + T), ENNReal.ofReal (K * T) :=
          setLIntegral_mono' measurableSet_Icc fun v hv => hEn v hv
      _ = _ := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
          simp [hT.le]
  have he : (∫⁻ v in Set.Icc a0 (a0 + T), r26t8a_itoEnergy P (Hd v) a0 v) < ⊤ :=
    lt_of_le_of_lt hHdE (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- pathwise FTC
  have hgood : ∀ᵐ w ∂P, ∀ r ∈ Set.Icc a0 (a0 + T), X r.toNNReal w ∉ eucCollisionSet d N := by
    filter_upwards [(hX.solution (a0 + T)).no_collision] with w hw r hr
    exact hw r.toNNReal (by rw [Real.coe_toNNReal r (ha0.trans hr.1)]; exact hr.2)
  have hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc a0 (a0 + T))).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc p.1 (a0 + T)) ∧
      ∀ t ∈ Set.Icc p.1 (a0 + T), H t p.1 p.2 i = H p.1 p.1 p.2 i + ∫ v in Set.Icc p.1 t, Hd v p.1 p.2 i := by
    have h1 : ∀ᵐ p ∂((volume.restrict (Set.Icc a0 (a0 + T))).prod P), p.1 ∈ Set.Icc a0 (a0 + T) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have h2 : ∀ᵐ p ∂((volume.restrict (Set.Icc a0 (a0 + T))).prod P),
        ∀ r ∈ Set.Icc a0 (a0 + T), X r.toNNReal p.2 ∉ eucCollisionSet d N :=
      Measure.quasiMeasurePreserving_snd.ae hgood
    filter_upwards [h1, h2] with p hp1 hp2
    intro i
    exact r26t8a_b06_tri_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha X p.2 p.1
      (a0 + T) (ha0.trans hp1.1) (hp2 p.1 hp1) i
  obtain ⟨G, J, hGm, hJm, hGc, hGeq, hJeq, hGFTC, hsup⟩ := r26t8a_recent_ito_fubini P F W' hfilt.brownian a0 T ha0 hT
    H Hd hdiag (fun t ht => hsl 0 (by norm_num) t ht) (fun t ht => hsl 1 le_rfl t ht) hmeas.aestronglyMeasurable he hFTC
  refine ⟨G, hGm, hGc, hGeq, ?_⟩
  have hsup' : r26t8a_scalarSupSq P T G ≤ ENNReal.ofReal (K * T * (8 + 2 * T ^ 2)) := by
    refine hsup.trans ?_
    calc 8 * r26t8a_itoEnergy P (fun r w i => H r r w i) a0 (a0 + T) +
          ENNReal.ofReal (2 * T) * ∫⁻ v in Set.Icc a0 (a0 + T), r26t8a_itoEnergy P (Hd v) a0 v
        ≤ 8 * ENNReal.ofReal (K * T) + ENNReal.ofReal (2 * T) * (ENNReal.ofReal (K * T) * ENNReal.ofReal T) :=
          add_le_add (mul_le_mul_of_nonneg_left hdiagE (zero_le)) (mul_le_mul_of_nonneg_left hHdE (zero_le))
      _ = ENNReal.ofReal (K * T * (8 + 2 * T ^ 2)) := by
          rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  set Yv : ℝ := Real.sqrt (T * (8 + 2 * T ^ 2)) * Real.sqrt (2 / beta) * C * Cf * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ))
    with hYv
  have hYv0 : 0 ≤ Yv := by positivity
  have hNrt : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  have hYsq : Yv ^ 2 = K * T * (8 + 2 * T ^ 2) := by
    have h2 : Real.sqrt (T * (8 + 2 * T ^ 2)) ^ 2 = T * (8 + 2 * T ^ 2) := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (2 / beta) ^ 2 = 2 / beta := Real.sq_sqrt (by positivity)
    have : Yv ^ 2 = Real.sqrt (T * (8 + 2 * T ^ 2)) ^ 2 * Real.sqrt (2 / beta) ^ 2 * (C * Cf * w0) ^ 2 *
        ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by rw [hYv]; ring
    rw [this, h2, h3, hNrt, hK]
    field_simp
  calc (r26t8a_scalarSupSq P T G) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (K * T * (8 + 2 * T ^ 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsup' (by norm_num)
    _ = ENNReal.ofReal Yv := by
        rw [← hYsq, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hYv0]
    _ = _ := rfl

end HRS.MS.R26T8A

end
