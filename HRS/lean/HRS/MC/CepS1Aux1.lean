import HRS.MC.CepC0

/-!
# Packet CEPS1 (auxiliary 1): barrier chain under a `C^{1,1}` potential

Mechanical copy-adaptation of theorems of `HRS/Stochastic/Particle.lean` (line ranges L1766-1983, L3167-3313) with
`Torus.IsCk 2 D.V` replaced by `cep_IsC11 D.V`; the hypothesis enters only through the Lipschitz
constant of `∇V` and the local Lipschitz continuity of the drift (`HRS.MC.CepC0.cepc0_locLipschitz`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS1

open HRS HRS.ClusterBarrier HRS.MC.CepC0

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem clusterRemainder_bound (D : DynData d) (hK : KernelLocal d D.s) (hV : cep_IsC11 D.V)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q C : ℝ, 0 < q ∧ q < clusterRadius I ∧ 0 ≤ C ∧
      ∀ Y : Fin N → Euc d, Y ∈ liftedFree d N → clusterDispersionLift I Y < q →
        (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Y) →
        -C * clusterDispersionLift I Y ≤ clusterRemainder D I Y := by
  have hIne : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨r, δK, hδK, hrs, hr0, hloc⟩ := hK.local_sing
  obtain ⟨Lr, hLr0, hLr⟩ := rem_exists_norm_le_of_smooth_zero r hrs hr0
  set k : ℝ := (I.card : ℝ) with hk
  have hk2 : (2 : ℝ) ≤ k := by
    have : (2 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI
    exact this
  have hkpos : 0 < k := by linarith
  set ε₀ : ℝ := min (1 / 16) (Real.sqrt δ / 4) with hε₀
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  have hε₀1 : ε₀ ≤ 1 / 16 := min_le_left _ _
  have hε₀δ : 4 * ε₀ ^ 2 ≤ δ / 4 := by
    have h1 : ε₀ ≤ Real.sqrt δ / 4 := min_le_right _ _
    have h2 : ε₀ ^ 2 ≤ (Real.sqrt δ / 4) ^ 2 := pow_le_pow_left₀ hε₀pos.le h1 2
    have h3 : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ.le
    have h4 : (Real.sqrt δ / 4) ^ 2 = δ / 16 := by rw [div_pow, h3]; norm_num
    linarith
  obtain ⟨Lg, hLg0, hLg⟩ := rem_kernel_lipschitz_off_zero hK.smoothOffZero hε₀pos
  obtain ⟨LV, hLV⟩ := hV.2
  set cm := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M) with hcm
  have hradpos : 0 < clusterRadius I := by unfold clusterRadius; positivity
  set q : ℝ := min (min (clusterRadius I / 2) (δK ^ 2 / (2 * k))) (min (ε₀ ^ 2 / (2 * k)) (δ / 4))
    with hq
  have hqpos : 0 < q :=
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hq1 : q ≤ clusterRadius I / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hq2 : q ≤ δK ^ 2 / (2 * k) := (min_le_left _ _).trans (min_le_right _ _)
  have hq3 : q ≤ ε₀ ^ 2 / (2 * k) := (min_le_right _ _).trans (min_le_left _ _)
  have hq4 : q ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q, (3 * k * ‖cm‖ * Lr) / N + 2 * ‖cm‖ * Lg + 2 * (LV : ℝ), hqpos, by linarith, ?_, ?_⟩
  · positivity
  intro Y hY hQ hsep
  set Q := clusterDispersionLift I Y with hQdef
  have hQrad : Q < clusterRadius I := by linarith
  obtain ⟨hsmall, hQ1', hQ2'⟩ := clusterDispersionLift_eq_euclid I Y hQrad
  have hQ1 : Q = (1 / (2 * k)) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 := hQ1'
  have hQ2 : Q = ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 := hQ2'
  have hQnn : 0 ≤ Q := clusterDispersion_nonneg I (fun i => Torus.mk (Y i))
  have h2k : 0 < 2 * k := by positivity
  have hS : ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 = 2 * k * Q := by
    rw [hQ1]; field_simp
  have hxsq : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 ≤ 2 * k * Q := by
    intro i hi j hj
    rw [← hS]
    refine le_trans (Finset.single_le_sum (f := fun j => ‖geoRep (Y i - Y j)‖ ^ 2)
      (fun j _ => by positivity) hj) ?_
    exact Finset.single_le_sum (f := fun i => ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) hi
  have hcsq : ∀ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 ≤ Q := by
    intro i hi
    rw [hQ2]
    exact Finset.single_le_sum (f := fun i => ‖clusterCentered I Y i‖ ^ 2)
      (fun i _ => by positivity) hi
  have e1 : 2 * k * q ≤ δK ^ 2 := by
    have := (le_div_iff₀ h2k).1 hq2; linarith
  have e2 : 2 * k * q ≤ ε₀ ^ 2 := by
    have := (le_div_iff₀ h2k).1 hq3; linarith
  have hxlt : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < δK ∧ ‖geoRep (Y i - Y j)‖ < ε₀ := by
    intro i hi j hj
    have h := hxsq i hi j hj
    have h3 : 2 * k * Q < 2 * k * q := mul_lt_mul_of_pos_left hQ h2k
    constructor
    · by_contra hc
      push Not at hc
      linarith [pow_le_pow_left₀ hδK.le hc 2]
    · by_contra hc
      push Not at hc
      linarith [pow_le_pow_left₀ hε₀pos.le hc 2]
  have hclt : ∀ i ∈ I, ‖clusterCentered I Y i‖ ≤ ε₀ / 2 := by
    intro i hi
    have h := hcsq i hi
    by_contra hc
    push Not at hc
    have h4 : q ≤ ε₀ ^ 2 / 4 := by
      refine hq3.trans ?_
      rw [div_le_div_iff₀ h2k (by norm_num)]
      exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg ε₀)
    linarith [pow_le_pow_left₀ (by positivity : 0 ≤ ε₀ / 2) hc.le 2]
  have hIne' : I.Nonempty := hIne
  obtain ⟨hneg, hcomp⟩ := rem_cluster_compat hsmall
  have hsumc := rem_clusterCentered_sum (I := I) (Y := Y) hneg
  have hlocI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      periodicRieszGrad d D.s (Torus.mk (Y i - Y j)) =
        eucRieszGrad D.s (geoRep (Y i - Y j)) + r (Torus.mk (Y i - Y j)) := by
    intro i hi j hj hij
    have hne : geoRep (Y i - Y j) ≠ 0 := by
      intro h0
      apply mk_sub_ne_zero_of_mem_liftedFree hY hij
      rw [← rem_mk_geoRep_eq, h0]
      funext a; simp [Torus.mk]
    have := hloc _ (hxlt i hi j hj).1 hne
    rwa [rem_mk_geoRep_eq] at this
  have hdec := rem_decomp D hIne' hQrad r hsmall hlocI
  rw [hdec]
  -- compatible lifts
  obtain ⟨i₀, hi₀⟩ := hIne
  set ytil : Fin N → Euc d := fun i => Y i₀ - geoRep (Y i₀ - Y i) with hytil
  have hytil_mk : ∀ i, Torus.mk (ytil i) = Torus.mk (Y i) := by
    intro i
    simp only [hytil]
    rw [mk_sub', rem_mk_geoRep_eq, mk_sub']
    abel
  have hytil_sub : ∀ i ∈ I, ∀ l ∈ I, ytil i - ytil l = geoRep (Y i - Y l) := by
    intro i hi l hl
    have := hcomp i₀ hi₀ i hi l hl
    simp only [hytil]
    rw [this]
    abel
  set ybar : Euc d := (1 / k) • ∑ l ∈ I, ytil l with hybar
  have hyc : ∀ i ∈ I, ytil i - ybar = clusterCentered I Y i := by
    intro i hi
    rw [rem_clusterCentered_of_mem hi]
    have h1 : ∑ l ∈ I, geoRep (Y i - Y l) = ∑ l ∈ I, (ytil i - ytil l) :=
      Finset.sum_congr rfl fun l hl => (hytil_sub i hi l hl).symm
    rw [h1, Finset.sum_sub_distrib, Finset.sum_const, hybar, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, one_div, inv_mul_cancel₀ hkpos.ne', one_smul]
  have hc_norm : ∀ i ∈ I, ‖ybar - ytil i‖ = ‖clusterCentered I Y i‖ := by
    intro i hi; rw [norm_sub_rev, hyc i hi]
  have hNk : k ≤ (N : ℝ) := by
    have h : I.card ≤ N := by simpa using Finset.card_le_univ I
    have h' : (I.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    exact h'
  have hNpos : 0 < (N : ℝ) := by linarith
  -- (1) the smooth part of the internal force
  have hAr := rem_bound_internal_remainder D r hLr0 hLr hsmall hQ1' hQ2' hIne'
  -- (2) the exterior forces
  have hB : ∀ j ∈ Finset.univ \ I, |∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))| ≤
      2 * ‖cm‖ * Lg * Q := by
    intro j hj
    have hjI : j ∉ I := (Finset.mem_sdiff.1 hj).2
    have hsepj := rem_exterior_separation hIne' hjI hδ hε₀1 hε₀δ
      (fun a ha b hb => (hxlt a ha b hb).2) (by linarith) (hsep j hjI)
    have hF : ∀ i ∈ I, ‖Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j) -
        Torus.lift (periodicRieszGrad d D.s) (ybar - Y j)‖ ≤ Lg * ‖clusterCentered I Y i‖ := by
      intro i hi
      have hu : ε₀ ≤ Torus.tdist (Torus.mk (ytil i)) (Torus.mk (Y j)) := by
        rw [hytil_mk]; exact hsepj i hi
      have hv : ‖ybar - ytil i‖ ≤ ε₀ / 2 := by rw [hc_norm i hi]; exact hclt i hi
      have := hLg (ytil i) ybar (Y j) hu hv
      rw [norm_sub_rev, hc_norm i hi] at this
      exact this
    have key := rem_abs_sum_inner_le I (clusterCentered I Y) hsumc
      (fun i => Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j))
      (Torus.lift (periodicRieszGrad d D.s) (ybar - Y j)) cm Lg hF
    have hF_eq : ∀ i, Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j) =
        periodicRieszGrad d D.s (Torus.mk (Y i - Y j)) := by
      intro i
      show periodicRieszGrad d D.s (Torus.mk (ytil i - Y j)) = _
      rw [mk_sub', hytil_mk, ← mk_sub']
    simp only [hF_eq] at key
    rw [← hQ2] at key
    exact key
  have hBtot : |(1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ Finset.univ \ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))| ≤
      2 * ‖cm‖ * Lg * Q := by
    rw [Finset.sum_comm, abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
    have h1 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hB)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : ((Finset.univ \ I).card : ℝ) ≤ N := by
      have : (Finset.univ \ I).card ≤ N := by simpa using Finset.card_le_univ (Finset.univ \ I)
      exact_mod_cast this
    have h2 : 0 ≤ 2 * ‖cm‖ * Lg * Q := by positivity
    calc 1 / (N : ℝ) * |∑ j ∈ Finset.univ \ I, ∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))|
        ≤ 1 / (N : ℝ) * (((Finset.univ \ I).card : ℝ) * (2 * ‖cm‖ * Lg * Q)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / (N : ℝ) * ((N : ℝ) * (2 * ‖cm‖ * Lg * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard h2) (by positivity)
      _ = 2 * ‖cm‖ * Lg * Q := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hNpos.ne', one_mul]
  -- (3) the confinement
  have hVF : ∀ i ∈ I, ‖gradient (Torus.lift D.V) (ytil i) - gradient (Torus.lift D.V) ybar‖ ≤
      (LV : ℝ) * ‖clusterCentered I Y i‖ := by
    intro i hi
    have := hLV.dist_le_mul (ytil i) ybar
    rw [dist_eq_norm, dist_eq_norm, hyc i hi] at this
    exact this
  have hVkey := rem_abs_sum_inner_le I (clusterCentered I Y) hsumc
    (fun i => gradient (Torus.lift D.V) (ytil i)) (gradient (Torus.lift D.V) ybar)
    (ContinuousLinearMap.id ℝ (Euc d)) (LV : ℝ) hVF
  have hVeq : ∀ i, gradient (Torus.lift D.V) (ytil i) = gradient (Torus.lift D.V) (Y i) := by
    intro i
    rw [← Torus.grad_mk_aux, hytil_mk, Torus.grad_mk_aux]
  simp only [hVeq, ContinuousLinearMap.id_apply] at hVkey
  rw [← hQ2] at hVkey
  have hidn : ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hVkey' : |∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (gradient (Torus.lift D.V) (Y i))| ≤ 2 * (LV : ℝ) * Q := by
    refine hVkey.trans ?_
    have h0 : 0 ≤ 2 * (LV : ℝ) * Q := by positivity
    have e : 2 * ‖ContinuousLinearMap.id ℝ (Euc d)‖ * (LV : ℝ) * Q =
        ‖ContinuousLinearMap.id ℝ (Euc d)‖ * (2 * (LV : ℝ) * Q) := by ring
    rw [e]
    calc _ ≤ 1 * (2 * (LV : ℝ) * Q) := mul_le_mul_of_nonneg_right hidn h0
      _ = _ := one_mul _
  -- assemble
  have hArN : |(1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (r (Torus.mk (Y i - Y j))))| ≤ (3 * k * ‖cm‖ * Lr) / N * Q := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (3 * k * ‖cm‖ * Lr * Q) :=
          mul_le_mul_of_nonneg_left hAr (by positivity)
      _ = (3 * k * ‖cm‖ * Lr) / N * Q := by ring
  have h1 := abs_le.1 hArN
  have h2 := abs_le.1 hBtot
  have h3 := abs_le.1 hVkey'
  have e : -((3 * k * ‖cm‖ * Lr) / N + 2 * ‖cm‖ * Lg + 2 * (LV : ℝ)) * Q =
      -((3 * k * ‖cm‖ * Lr) / N * Q) - 2 * ‖cm‖ * Lg * Q - 2 * (LV : ℝ) * Q := by ring
  rw [e]
  linarith [h1.1, h2.1, h3.2]


theorem ito_along_solution [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {T : ℝ} (hT : 0 ≤ T)
    (ρ : Ω → WithTop ℝ) (hρ : IsStoppingTime ℱ ρ) (hρτ : ∀ ω, ρ ω < τ ω)
    {U : Set (Fin N → Euc d)} (hU : IsOpen U) (Kc : Set (Fin N → Euc d)) (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) (hKfree : Kc ⊆ liftedFree d N) {g : (Fin N → Euc d) → ℝ}
    (hg : ContDiffOn ℝ 2 g U)
    (hYK : ∀ ω, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω → Y t ω ∈ Kc) :
    ∃ Ψ : ℝ → Ω → (Fin N × Fin d) → ℝ, IsProgressiveL2 P ℱ Ψ ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → s ≤ T → (s : WithTop ℝ) ≤ ρ ω → ∀ k,
        Ψ s ω k = fderiv ℝ g (Y s ω) (liftedNoise D k)) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω →
        IntegrableOn (fun s => diffGen D g (Y s ω)) (Set.Icc 0 t) ∧
        g (Y t ω) = g (Y₀ ω) + (∫ s in Set.Icc 0 t, diffGen D g (Y s ω)) +
          localItoIntegral P ℱ W' (stopIntegrand Ψ ρ) t ω := by
  classical
  have hY0 : ∀ t : ℝ, Measurable[ℱ t] (Y 0) := by
    have : Y 0 = Y₀ := funext hsol.sol.init
    rw [this]; exact hsol.init_meas
  have hcont : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) ≤ ρ ω →
      ContinuousOn (fun s => Y s ω) (Set.Icc 0 t) := fun ω t ht h =>
    hsol.sol.cont ω t ht (lt_of_le_of_lt h (hρτ ω))
  have hVprog := isProgressive_stoppedPath ℱ Y hsol.sol.adapted hY0 hρ hcont
  have hlip := cepc0_locLipschitz (N := N) D hK.smoothOffZero hV
  have hFc : ContinuousOn (liftedDrift D) (liftedFree d N) := by
    have h1 : ContinuousOn (Function.uncurry fun (_ : ℝ) (Z : Fin N → Euc d) => liftedDrift D Z)
        (Set.Ici 0 ×ˢ liftedFree d N) := hlip.cont
    have h2 : ContinuousOn (fun z : Fin N → Euc d => ((0 : ℝ), z)) (liftedFree d N) :=
      (continuousOn_const.prodMk continuousOn_id)
    have h3 : Set.MapsTo (fun z : Fin N → Euc d => ((0 : ℝ), z)) (liftedFree d N)
        (Set.Ici 0 ×ˢ liftedFree d N) := fun z hz => ⟨Set.mem_Ici.2 le_rfl, hz⟩
    have h4 := ContinuousOn.comp h1 h2 h3
    exact h4
  have hFKm : Measurable (Kc.piecewise (liftedDrift D) (fun _ => (0 : Fin N → Euc d))) :=
    ContinuousOn.measurable_piecewise (hFc.mono hKfree) continuousOn_const
      hKc.isClosed.measurableSet
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hFc.mono hKfree)
  set b := stoppedDrift D Kc T ρ Y with hbdef
  have hb_apply : ∀ ω s, 0 ≤ s → s ≤ T → (s : WithTop ℝ) ≤ ρ ω →
      b s ω = liftedDrift D (Y s ω) := by
    intro ω s hs0 hsT hsρ
    have hmem : Y s ω ∈ Kc := hYK ω s ⟨hs0, hsT⟩ hsρ
    simp only [hbdef, stoppedDrift, hs0, hsT, hsρ, and_self, ite_true]
    rw [Set.indicator_of_mem (show ω ∈ {ω | (s : WithTop ℝ) ≤ ρ ω} from hsρ), max_eq_left hs0,
      Set.piecewise_eq_of_mem _ _ _ hmem]
  have hb_bound : ∀ ω s, ‖b s ω‖ ≤ max B 0 := by
    intro ω s
    simp only [hbdef, stoppedDrift]
    split_ifs with hc
    · by_cases hmem : Set.indicator {ω | (s : WithTop ℝ) ≤ ρ ω} (fun ω => Y (max s 0) ω) ω ∈ Kc
      · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
        exact (hB _ hmem).trans (le_max_left _ _)
      · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
        simp
    · simp
  have hb_prog : IsProgressive ℱ b := by
    intro i
    let M : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have hS : MeasurableSet[M] {p : Set.Iic i × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} :=
      measurableSet_le_stoppingTime ℱ hρ i
    have hc : MeasurableSet[M] {p : Set.Iic i × Ω |
        0 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ T ∧ ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} := by
      have h1 : MeasurableSet[M] {p : Set.Iic i × Ω | 0 ≤ (p.1 : ℝ)} :=
        measurableSet_le measurable_const (measurable_subtype_coe.comp measurable_fst)
      have h2 : MeasurableSet[M] {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ T} :=
        measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const
      exact h1.inter (h2.inter hS)
    have hm : Measurable[M] (fun p : Set.Iic i × Ω =>
        Kc.piecewise (liftedDrift D) (fun _ => (0 : Fin N → Euc d))
          (Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω} (fun ω => Y (max (p.1 : ℝ) 0) ω) p.2)) :=
      hFKm.comp (hVprog i)
    exact Measurable.ite hc hm measurable_const
  have hb_L1 : IsProgressiveLocL1 P ℱ b := by
    refine ⟨hb_prog, fun T' => Eventually.of_forall fun ω => ?_⟩
    exact Integrable.of_bound (C := max B 0) (progressive_aestronglyMeasurable_Icc hb_prog T' ω)
      (Eventually.of_forall fun s => hb_bound ω s)
  -- the constant noise integrand
  have hΦ : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) := by
    refine ⟨isProgressive_const ℱ (liftedNoise (N := N) D), fun T' => Eventually.of_forall fun ω => ?_⟩
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    refine ENNReal.mul_lt_top ?_ (by simp)
    exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top (enorm_lt_top)
  set X := itoProcess P ℱ W' Y₀ b (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) with hXdef
  have hXY : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ ω → X t ω = Y t ω := by
    filter_upwards [localItoIntegralE_const hW' (liftedNoise (N := N) D), hsol.sol.eq] with ω h1 h2 t ht htρ
    have htτ : (t : WithTop ℝ) < τ ω := lt_of_le_of_lt htρ (hρτ ω)
    have h3 := (h2 t ht.1 htτ).2
    have h4 : (∫ s in Set.Icc (0 : ℝ) t, b s ω) = ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (Y s ω) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs =>
        hb_apply ω s hs.1 (hs.2.trans ht.2) (le_trans (by exact_mod_cast hs.2) htρ)
    simp only [hXdef, itoProcess]
    rw [h1 t, h4, h3]
  have hXK : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ ω → X t ω ∈ Kc := by
    filter_upwards [hXY] with ω h t ht htρ
    rw [h t ht htρ]; exact hYK ω t ht htρ
  have hf := isC12On_of_contDiffOn T hU hg
  have hmain := ito_formula_localized hW' hT U hU Kc hKc hKU (fun _ x => g x) hf Y₀
    hsol.init_meas b hb_L1 (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) hΦ ρ hρ hXK
  have hXad : Adapted ℱ X := adapted_itoProcess Y₀ hsol.init_meas b hb_prog _
  have hXc : ∀ᵐ ω ∂P, Continuous fun t => X t ω := continuous_itoProcess Y₀ b hb_L1 _
  have hprogLoc := isProgressiveLocL2_itoIntegrand Kc hKc.isClosed U hKU
    (fun _ x => g x) hf X (isProgressive_itoProcess Y₀ hsol.init_meas b hb_prog _) hXc _ hΦ
  -- boundedness of the martingale integrand
  have hdg : ContinuousOn (fderiv ℝ g) Kc :=
    (hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hdg
  set C₂ : ℝ := ∑ k, ‖liftedNoise (N := N) D k‖ with hC₂
  have hΨbdd : ∀ s ω k, |itoIntegrand T Kc (fun _ x => g x) X (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) s ω k|
      ≤ max C₁ 0 * C₂ := by
    intro s ω k
    simp only [itoIntegrand, Set.indicator]
    split_ifs with h1 h2
    · rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ g (X s ω) (liftedNoise D k)‖
          ≤ ‖fderiv ℝ g (X s ω)‖ * ‖liftedNoise D k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C₁ 0 * C₂ := by
          apply mul_le_mul ((hC₁ _ h2).trans (le_max_left _ _))
            (Finset.single_le_sum (f := fun k => ‖liftedNoise (N := N) D k‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ k)) (norm_nonneg _) (le_max_right _ _)
    · simp [hC₂]; positivity
    · simp [hC₂]; positivity
  have hΨ2 : IsProgressiveL2 P ℱ
      (itoIntegrand T Kc (fun _ x => g x) X (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D)) :=
    IsProgressiveL2.of_bounded P hprogLoc.prog _ hΨbdd
  refine ⟨_, hΨ2, ?_, ?_⟩
  · filter_upwards [hXY] with ω h s hs0 hsT hsρ k
    have hXs := h s ⟨hs0, hsT⟩ hsρ
    simp only [itoIntegrand, Set.indicator, Set.mem_Icc, Set.mem_ofPred_eq, hs0, hsT, and_self,
      ite_true, hXs, hYK ω s ⟨hs0, hsT⟩ hsρ]
  · filter_upwards [hmain, hXY] with ω h1 h2 t ht htρ
    obtain ⟨hint, heq⟩ := h1 t ht htρ
    have hdrift : ∀ s ∈ Set.Icc (0 : ℝ) t,
        itoDrift T (fun _ x => g x) X b (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) s ω =
          diffGen D g (Y s ω) := by
      intro s hs
      have hsT : s ≤ T := hs.2.trans ht.2
      have hsρ : (s : WithTop ℝ) ≤ ρ ω := le_trans (by exact_mod_cast hs.2) htρ
      have hXs := h2 s ⟨hs.1, hsT⟩ hsρ
      simp only [itoDrift, diffGen, hXs, hb_apply ω s hs.1 hsT hsρ]
      simp
    refine ⟨hint.congr_fun hdrift measurableSet_Icc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Icc hdrift] at heq
    have hX0 : X 0 ω = Y₀ ω := by
      simp [hXdef, itoProcess_zero]
    rw [← h2 t ht htρ]
    simpa [hX0] using heq

end HRS.MC.CepS1
