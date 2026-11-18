import HRS.MC.CepN6Aux11
import HRS.MC.CepN6Aux1
import HRS.MC.CepN5
import HRS.MC.CepN5b
import HRS.MC.CepN3
import HRS.MC.CepN4

/-!
# Packet CEPN6 (aux 12): the core contradiction
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem n6_core [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0)
    (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (hπ0 : ∀ ω, cep_StrictlyOrdered (π ω) (Y₀ ω))
    {T : ℝ} (hT : 0 < T) (htop : ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) < τ ω)
    (hbelow : a < N * D.invβ) : False := by
  classical
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (8 * (N : ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr16 : r ≤ 1 / 16 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = r / 2 := ⟨_, rfl⟩
  have hr20 : 0 < r2 := by rw [hr2]; positivity
  -- bounded drifts, gap dynamics
  obtain ⟨Bd, hBd0, hBd1, hBd2'⟩ := n6_drift_bounds hs ha hM hV hr20 hNpos
  obtain ⟨C, c, hC0, hc, hcad, hN4⟩ :=
    HRS.MC.CepN4.cep_N4_gap_dynamics_proof hN hs ha hM hV hW' hsol hπ hr20
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * a / N := ⟨_, rfl⟩
  obtain ⟨σ5, hσ5def⟩ : ∃ σ5 : ℝ, σ5 = 2 * Real.sqrt D.invβ := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = Real.sqrt (2 * D.invβ) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hσ5 : 0 < σ5 := by rw [hσ5def]; have := Real.sqrt_pos.2 hβ; positivity
  have hν : 0 < ν := by rw [hνdef]; exact Real.sqrt_pos.2 (by positivity)
  have hκσ : κ < σ5 ^ 2 / 2 := by
    rw [hκdef, hσ5def, mul_pow, Real.sq_sqrt hβ.le, div_lt_iff₀ hNr]
    nlinarith
  have hσ52 : 0 < σ5 ^ 2 := by positivity
  have hθ : 2 * κ / σ5 ^ 2 < 1 := by
    rw [div_lt_one hσ52]; linarith
  have hlam : 0 ≤ 2 * C / σ5 ^ 2 := by positivity
  obtain ⟨ε₀, q, hε₀, hq, hN5b⟩ := HRS.MC.CepN5b.cep_N5b_scale_ratio_proof hθ hlam
  obtain ⟨η, dur, ε, hη0, hdur0, hε0, hdurT, hMcond, hcond, hbad, hεε₀, hε18, hεL, hCε, hεdur⟩ :=
    n6_params hNpos hBd0 hC0 hκ hν hσ5 hT hq hε₀ hr0
  -- N3 steering
  have hT2 : 0 < T / 2 := by linarith
  obtain ⟨t₁, ht₁0, ht₁T, A, hAm, hAP, hA⟩ :=
    HRS.MC.CepN3.cep_N3_steering_proof hN hs hβ ha hM hV hW' hsol hπ hπ0 hT2 hε0 hε18
  have ht₁T' : t₁ + dur ≤ T := by linarith
  -- fix a permutation
  obtain ⟨σ, hσP⟩ : ∃ σ : Equiv.Perm (Fin N), 0 < P (A ∩ {ω | π ω = σ}) := by
    by_contra h
    push Not at h
    have h0 : P A = 0 := by
      refine measure_mono_null (t := ⋃ σ : Equiv.Perm (Fin N), A ∩ {ω | π ω = σ}) ?_ ?_
      · intro ω hω
        exact Set.mem_iUnion.2 ⟨π ω, hω, rfl⟩
      · exact measure_iUnion_null fun σ => nonpos_iff_eq_zero.1 (h σ)
    exact hAP.ne' h0
  set p0 := σ (cep_i0 hN) with hp0
  set p1 := σ (cep_i1 hN) with hp1
  have hp01 : p0 ≠ p1 := σ.injective.ne (cepn4_i0_ne_i1 hN)
  have hlt01 : cep_i0 hN < cep_i1 hN := by
    show (⟨0, _⟩ : Fin N) < ⟨1, _⟩
    exact Fin.mk_lt_mk.2 one_pos
  -- the good event E
  obtain ⟨E, hE⟩ : ∃ E : Set Ω, E = {ω | π ω = σ} ∩ {ω | ((T : ℝ) : WithTop ℝ) < τ ω} := ⟨_, rfl⟩
  have hEmem : ∀ ω, ω ∈ E ↔ π ω = σ ∧ ((T : ℝ) : WithTop ℝ) < τ ω := fun ω => by rw [hE]; rfl
  have hEm : MeasurableSet[ℱ 0] E := by
    have hS : MeasurableSet {ω | τ ω ≤ ((T : ℝ) : WithTop ℝ)} := ℱ.le T _ (hsol.stopping T)
    have hS0 : P {ω | τ ω ≤ ((T : ℝ) : WithTop ℝ)} = 0 := by
      have := ae_iff.1 htop
      simpa [not_lt] using this
    have hS' := hW'.complete 0 _ hS hS0
    rw [hE]
    refine (hπ σ).inter ?_
    have : {ω | ((T : ℝ) : WithTop ℝ) < τ ω} = {ω | τ ω ≤ ((T : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω; simp
    rw [this]
    exact hS'.compl
  have hordE : ∀ ω ∈ E, ∀ v ∈ Set.Icc (0 : ℝ) T, cep_StrictlyOrdered σ (Y v ω) := by
    intro ω hω v hv
    obtain ⟨hπσ, hτ⟩ := (hEmem ω).1 hω
    have hlt : ∀ u : ℝ, u ≤ T → ((u : ℝ) : WithTop ℝ) < τ ω := fun u hu =>
      lt_of_le_of_lt (by exact_mod_cast hu) hτ
    have hfree : ∀ v ∈ Set.Icc (0 : ℝ) T, Y v ω ∈ liftedFree 1 N := fun v hv =>
      hsol.mem ω v hv.1 (hlt v hv.2)
    have hcont := hsol.sol.cont ω T hT.le hτ
    have h0 : cep_StrictlyOrdered σ (Y 0 ω) := by
      rw [hsol.sol.init ω, ← hπσ]
      exact hπ0 ω
    exact n6_persist hT.le hcont hfree h0 v hv
  have hcontE : ∀ ω ∈ E, ContinuousOn (fun s => Y s ω) (Set.Icc 0 T) := fun ω hω =>
    hsol.sol.cont ω T hT.le ((hEmem ω).1 hω).2
  -- the bad configuration
  obtain ⟨yb, hyb⟩ : ∃ yb : Fin N → Euc 1,
      yb = fun k => EuclideanSpace.single (0 : Fin 1) (if k = p1 then (1 / 2 : ℝ) else 0) := ⟨_, rfl⟩
  have hyb1 : yb p1 0 = 1 / 2 := by rw [hyb]; simp
  have hyb0 : yb p0 0 = 0 := by rw [hyb]; simp [hp01]
  obtain ⟨Ypp, hYpp⟩ : ∃ f : ℝ → Ω → Fin N → Euc 1, f = n6_Ypp E Y T yb := ⟨_, rfl⟩
  have hYppE : ∀ ω ∈ E, ∀ u ∈ Set.Icc (0 : ℝ) T, Ypp u ω = Y u ω := fun ω hω u hu => by
    rw [hYpp]; exact n6_Ypp_eq hω hu
  have hYppoff : ∀ ω, ω ∉ E → ∀ u, Ypp u ω = yb := fun ω hω u => by
    rw [hYpp]; exact n6_Ypp_off hω u
  have hYc : ∀ ω, Continuous fun u => Ypp u ω := by
    intro ω; rw [hYpp]; exact n6_Ypp_cont hT.le hcontE ω
  have hYad : Adapted (n6_clampFilt ℱ) Ypp := by
    rw [hYpp]; exact n6_Ypp_adapted hT.le hEm hsol.sol.adapted
  obtain ⟨U, hU⟩ : ∃ U : Set (Fin N → Euc 1), U = n6_Uo p0 p1 r2 (1 / 8) := ⟨_, rfl⟩
  have hUopen : IsOpen U := by rw [hU]; exact n6_isOpen_Uo _ _ _ _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Ω → WithTop ℝ, ρ = exitTime Ypp U t₁ := ⟨_, rfl⟩
  have hρst : IsStoppingTime ℱ ρ := by
    rw [hρ]
    refine n6_stopping_transfer
      (isStoppingTime_exitTime (n6_clampFilt ℱ) Ypp hYad hYc hUopen t₁) (fun ω => ?_)
    exact (show ((0 : ℝ) : WithTop ℝ) ≤ ((t₁ : ℝ) : WithTop ℝ) by exact_mod_cast ht₁0.le).trans
      (le_hittingAfter ω)
  obtain ⟨G, hG⟩ : ∃ G : ℝ → Ω → ℝ, ∀ u ω, G u ω = Ypp u ω p1 0 - Ypp u ω p0 0 :=
    ⟨fun u ω => Ypp u ω p1 0 - Ypp u ω p0 0, fun _ _ => rfl⟩
  have hGc : ∀ ω, Continuous fun u => G u ω := fun ω => by
    simp only [hG]
    exact ((n6_coord_cont p1).comp (hYc ω)).sub ((n6_coord_cont p0).comp (hYc ω))
  have hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t) := by
    intro t ht
    have h : Measurable[ℱ (max t 0)] (Ypp t) := hYad t
    rw [max_eq_left ht] at h
    have : G t = fun ω => Ypp t ω p1 0 - Ypp t ω p0 0 := funext fun ω => hG t ω
    rw [this]
    exact ((n6_coord_cont p1).measurable.comp h).sub ((n6_coord_cont p0).measurable.comp h)
  have hGposE : ∀ ω ∈ E, ∀ u ∈ Set.Icc (0 : ℝ) T, 0 < G u ω := by
    intro ω hω u hu
    rw [hG, hYppE ω hω u hu]
    have := (hordE ω hω u hu).1 _ _ hlt01
    linarith
  have hGposall : ∀ ω, ∀ u ∈ Set.Icc (0 : ℝ) T, 0 < G u ω := by
    intro ω u hu
    by_cases hω : ω ∈ E
    · exact hGposE ω hω u hu
    · rw [hG, hYppoff ω hω, hyb1, hyb0]; norm_num
  -- the Brownian motion of the pair
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0 → Ω → ℝ, ∀ t ω, B t ω = (W' t ω (p1, 0) - W' t ω (p0, 0)) / Real.sqrt 2 :=
    ⟨fun t ω => (W' t ω (p1, 0) - W' t ω (p0, 0)) / Real.sqrt 2, fun _ _ => rfl⟩
  have hB : IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => B t ω) := by
    have hij : ((p1, (0 : Fin 1)) : Fin N × Fin 1) ≠ (p0, 0) := fun h => hp01.symm (congrArg Prod.fst h)
    have := n6_isBrownianFiltration_diff hW' hij
    have hfun : (fun t ω (_ : Fin 1) => B t ω) =
        fun t ω (_ : Fin 1) => (W' t ω (p1, 0) - W' t ω (p0, 0)) / Real.sqrt 2 := by
      funext t ω _; exact hBdef t ω
    rw [hfun]; exact this
  have hPath := n6_pathOK_ae hN hsol hπ0 hT hN4 htop σ
  have hpos : ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω → 0 < G u ω :=
    Eventually.of_forall fun ω u hu _ =>
      hGposall ω u ⟨ht₁0.le.trans hu.1, hu.2.trans ht₁T'⟩
  have hdyn : ∀ᵐ ω ∂P, ∀ s t : ℝ, t₁ ≤ s → s ≤ t → t ≤ t₁ + dur → ((t : ℝ) : WithTop ℝ) ≤ ρ ω →
      G t ω - G s ω = (∫ u in s..t, (κ / G u ω + c u ω)) +
        σ5 * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω) := by
    filter_upwards [hPath] with ω hPω
    intro s t hs hst hdt htρ
    by_cases htt : t = t₁
    · have hst' : s = t := le_antisymm hst (by linarith)
      subst hst'
      simp
    · have hlt : t₁ < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm htt)
      have hUmem : ∀ v ∈ Set.Ico t₁ t, Ypp v ω ∈ U := fun v hv => by
        rw [hρ] at htρ
        exact mem_of_lt_exitTime Ypp U t₁ ω v hv.1 (lt_of_lt_of_le (by exact_mod_cast hv.2) htρ)
      have hωE : ω ∈ E := by
        by_contra hωE
        have h1 := hUmem t₁ ⟨le_rfl, hlt⟩
        rw [hYppoff ω hωE, hU] at h1
        have := h1.1
        rw [hyb1, hyb0] at this
        norm_num at this
      have hπσ := ((hEmem ω).1 hωE).1
      have hP := hPω hπσ
      have htT : t ≤ T := by linarith
      have hU' : ∀ v ∈ Set.Ico t₁ t, Y v ω ∈ n6_Uo p0 p1 r2 (1 / 8) := fun v hv => by
        have := hUmem v hv
        rw [hYppE ω hωE v ⟨ht₁0.le.trans hv.1, hv.2.le.trans htT⟩, hU] at this
        exact this
      have key := n6_dyn_of_pathOK hN hP ht₁0.le hlt htT hU' hs hst
      have hs0 : s ∈ Set.Icc (0 : ℝ) T := ⟨ht₁0.le.trans hs, hst.trans htT⟩
      have ht0 : t ∈ Set.Icc (0 : ℝ) T := ⟨ht₁0.le.trans (hs.trans hst), htT⟩
      have hint : ∫ u in s..t, (κ / G u ω + c u ω) =
          ∫ u in s..t, ((2 * a / N) / (Y u ω p1 0 - Y u ω p0 0) + c u ω) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hst] at hu
        simp only
        rw [hG, hYppE ω hωE u ⟨(ht₁0.le.trans hs).trans hu.1, hu.2.trans htT⟩, hκdef]
      have hBt : σ5 * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω) =
          2 * Real.sqrt D.invβ * (((W' (Real.toNNReal t) ω (p1, 0) - W' (Real.toNNReal t) ω (p0, 0)) -
            (W' (Real.toNNReal s) ω (p1, 0) - W' (Real.toNNReal s) ω (p0, 0))) / Real.sqrt 2) := by
        rw [hBdef, hBdef, hσ5def]
        ring
      rw [hint, hBt, hG, hG, hYppE ω hωE t ht0, hYppE ω hωE s hs0]
      exact key
  -- the event A₁
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Set Ω, A₁ = A ∩ E := ⟨_, rfl⟩
  have hA₁m : MeasurableSet[ℱ t₁] A₁ := by
    rw [hA₁]; exact hAm.inter (ℱ.mono ht₁0.le _ hEm)
  have hA₁m' : MeasurableSet A₁ := ℱ.le t₁ _ hA₁m
  have hA₁P : 0 < (P A₁).toReal := by
    have h1 : P A₁ = P (A ∩ {ω | π ω = σ}) := by
      rw [hA₁, hE, ← Set.inter_assoc]
      apply measure_inter_conull
      exact ae_iff.1 htop
    exact ENNReal.toReal_pos (by rw [h1]; exact hσP.ne') (measure_ne_top _ _)
  have hA₀ : ∀ ω ∈ A₁, 0 < G t₁ ω ∧ G t₁ ω ≤ ε / 2 := by
    intro ω hω
    rw [hA₁] at hω
    obtain ⟨hωA, hωE⟩ := hω
    obtain ⟨hπσ, -⟩ := (hEmem ω).1 hωE
    obtain ⟨-, -, h3, h4, -, -⟩ := hA ω hωA
    rw [hπσ] at h3 h4
    rw [hG, hYppE ω hωE t₁ ⟨ht₁0.le, by linarith⟩]
    exact ⟨h3, h4⟩
  have hBd2 : ∀ z ∈ liftedFree 1 N,
      (∀ j, j ≠ p0 → j ≠ p1 → r2 ≤ n6_dc (z p0 0 - z j 0) ∧ r2 ≤ n6_dc (z p1 0 - z j 0)) →
      |(liftedDrift D z p0) 0 + (liftedDrift D z p1) 0| ≤ Bd :=
    fun z hz h => hBd2' z hz p0 p1 hp01 h
  have hN5 : ∀ δ : ℝ, 0 < δ → δ < ε / 2 →
      (1 - HRS.MC.CepN5b.cep_scale (2 * κ / σ5 ^ 2) (2 * C / σ5 ^ 2) (ε / 2) /
          HRS.MC.CepN5b.cep_scale (2 * κ / σ5 ^ 2) (2 * C / σ5 ^ 2) ε - ε ^ 2 / (σ5 ^ 2 * dur)) *
            (P A₁).toReal -
        (P (A₁ ∩ {ω | ρ ω < ((t₁ + dur : ℝ) : WithTop ℝ)})).toReal ≤
      (P (A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ})).toReal :=
    fun δ hδ hδε => HRS.MC.CepN5.cep_N5_bessel_hitting_proof hB hκ hσ5 hκσ hC0 hρst ht₁0.le hdur0
      hGc hGad hc hcad hpos hdyn hε0 hCε hδ hδε hA₁m hA₀
  have h2L : 2 * (r / 16) ≤ 1 / 8 := by linarith
  have hρbound : (P (A₁ ∩ {ω | ρ ω < ((t₁ + dur : ℝ) : WithTop ℝ)})).toReal ≤
      q / 4 * (P A₁).toReal := by
    have h1 : P (A₁ ∩ {ω | ρ ω < ((t₁ + dur : ℝ) : WithTop ℝ)}) ≤
        P (A₁ ∩ {ω | ∃ k : Fin N, ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|}) := by
      refine measure_mono_ae ?_
      filter_upwards [hPath] with ω hPω
      rintro ⟨hωA₁, hρlt⟩
      refine ⟨hωA₁, ?_⟩
      by_contra hnot
      have hρlt' : exitTime Ypp U t₁ ω < ((t₁ + dur : ℝ) : WithTop ℝ) := by
        rw [← hρ]; exact hρlt
      have hMcond' : r2 + 2 * (Bd * dur + 2 * Real.sqrt (2 * D.invβ) * η + r / 16) < r := by
        rw [hr2, ← hνdef]; exact hMcond
      have hcond' : ((2 * a / N) / (r / 16) + C) * dur + 4 * Real.sqrt (2 * D.invβ) * η < r / 16 := by
        rw [← hκdef, ← hνdef]; exact hcond
      have hωE : ω ∈ E := by rw [hA₁] at hωA₁; exact hωA₁.2
      have hωA : ω ∈ A := by rw [hA₁] at hωA₁; exact hωA₁.1
      have hπσ := ((hEmem ω).1 hωE).1
      have hP := hPω hπσ
      obtain ⟨-, -, -, hG0le, hiso, hsep2⟩ := hA ω hωA
      rw [hπσ] at hiso hG0le hsep2
      rw [← hr] at hiso hsep2
      have hnoise : ∀ k : Fin N, ∀ v ∈ Set.Icc t₁ (t₁ + dur),
          |W' (Real.toNNReal v) ω (k, 0) - W' (Real.toNNReal t₁) ω (k, 0)| ≤ η := fun k v hv =>
        not_lt.1 (fun h => hnot ⟨k, v, hv, h⟩)
      have hexit := n6_exit hN σ (a := a) (Bd := Bd) (C := C) (r := r) (r2 := r2) (η := η)
        (L := r / 16) (ε := ε) (T := T) (t₁ := t₁) (dur := dur) ha hβ hη0.le hBd0 hC0 ht₁0.le hdur0
        ht₁T' hBd1 hBd2 (y := fun v => Y v ω) (c := fun u => c u ω)
        (w := fun v k => W' (Real.toNNReal v) ω (k, 0)) (fun u => hc u ω) hP.free hP.cont hP.ord
        hP.coord hP.gap hnoise (n6_hinit_of_N3 hN hiso hsep2) hG0le hεL h2L hMcond' hcond'
      obtain ⟨x, hx⟩ : ∃ x : ℝ, exitTime Ypp U t₁ ω = (x : WithTop ℝ) := by
        rcases h : exitTime Ypp U t₁ ω with _ | x
        · rw [h] at hρlt'; exact absurd hρlt' (not_lt.2 le_top)
        · exact ⟨x, rfl⟩
      have hx1 : t₁ ≤ x := by
        have : ((t₁ : ℝ) : WithTop ℝ) ≤ exitTime Ypp U t₁ ω := le_hittingAfter ω
        rw [hx] at this; exact_mod_cast this
      have hx2 : x < t₁ + dur := by
        rw [hx] at hρlt'; exact_mod_cast hρlt'
      have hxT : x ≤ T := by linarith
      have hxnot : Ypp x ω ∉ U := notMem_of_exitTime_eq Ypp U hUopen t₁ ω (hYc ω) x hx
      have hbefore : ∀ v ∈ Set.Ico t₁ x, Y v ω ∈ n6_Uo p0 p1 r2 (1 / 8) := fun v hv => by
        have h1 : Ypp v ω ∈ U :=
          mem_of_lt_exitTime Ypp U t₁ ω v hv.1 (by rw [hx]; exact_mod_cast hv.2)
        rw [hYppE ω hωE v ⟨ht₁0.le.trans hv.1, hv.2.le.trans hxT⟩, hU] at h1
        exact h1
      have hfin := hexit x hx1 hx2.le hbefore
      apply hxnot
      rw [hYppE ω hωE x ⟨ht₁0.le.trans hx1, hxT⟩, hU]
      exact hfin
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    have h3 := n6_bad_bound hW' ht₁0.le hdur0.le hη0 hA₁m
    calc _ ≤ _ := h2
      _ ≤ N * dur / η ^ 2 * P.real A₁ := h3
      _ ≤ q / 4 * (P A₁).toReal := mul_le_mul_of_nonneg_right hbad measureReal_nonneg
  have hlow : ∀ δ : ℝ, 0 < δ → δ < ε / 2 → q / 4 * (P A₁).toReal ≤
      (P (A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), G u ω ≤ δ})).toReal := by
    intro δ hδ hδε
    have h1 := hN5 δ hδ hδε
    have h2 := hN5b ε hε0 hεε₀
    have hpnn : 0 ≤ (P A₁).toReal := ENNReal.toReal_nonneg
    have h3 : (P (A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ})).toReal ≤
        (P (A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), G u ω ≤ δ})).toReal := by
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      rintro ω ⟨hω, u, hu, -, hle⟩
      exact ⟨hω, u, hu, hle⟩
    have hfac : q / 2 ≤ 1 - HRS.MC.CepN5b.cep_scale (2 * κ / σ5 ^ 2) (2 * C / σ5 ^ 2) (ε / 2) /
          HRS.MC.CepN5b.cep_scale (2 * κ / σ5 ^ 2) (2 * C / σ5 ^ 2) ε - ε ^ 2 / (σ5 ^ 2 * dur) := by
      linarith
    have h4 := mul_le_mul_of_nonneg_right hfac hpnn
    linarith
  exact n6_core_final (P := P) hA₁m' (G := G) (t₁ := t₁) (dur := dur) (ε := ε)
    (c0 := q / 4 * (P A₁).toReal) hdur0.le hGc
    (fun u hu => (hGad u (ht₁0.le.trans hu.1)).mono (ℱ.le u) le_rfl)
    (fun ω _ u hu => hGposall ω u ⟨ht₁0.le.trans hu.1, hu.2.trans ht₁T'⟩) hε0
    (mul_pos (by linarith) hA₁P) hlow

end HRS.MC.CepN6
