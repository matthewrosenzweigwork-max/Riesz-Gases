import HRS.PDE.MovSpec2b
import HRS.PDE.MovSXFinal
import HRS.PDE.MovAFinal
import HRS.PDE.MovBFinal
import HRS.PDE.MovCFinal
import HRS.PDE.MovDFinal
import HRS.PDE.MovEFinal
import HRS.PDE.D3PhiPChain2
import HRS.PDE.MovRepairTie

/-!
# MOV-FINAL (part 1): the entropy glue re-run with the relocated packet proofs

Verbatim copies of `movT_entropy_gronwall`, `mov_ent_ineq_bdd`, `movT_traj_exp` (renamed `movfin_movT_traj_exp`),
`mov_ent_ineq`, `movT_entropy_bound` (`HRS/PDE/MovSpec2b.lean`) with every frozen sorried packet replaced by its `_proof`
(`MovSXFinal`, `MovAFinal`-`MovEFinal`, `D3PhiPChain2`, `MovRepairTie`).  Each `_proof` is tied by `type_of%` to the frozen
statement.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The physical reference `ℚ_{N,β}(μ^r)` is a probability measure for a positive `C²` background
(`0 < K < ∞`: `gibbs_facts` with `rowOK_g_h`, and `movT_pressure_two_sided_C2_proof` at `θ = 0`, `h = 0`).  PROVED from the
`C²` pressure packet.  Implicit in the TeX (H:eq:modulated-gibbs, M L446-452). -/
theorem movfin_movT_Q_isProb (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (h.mf.density r hr)
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hcont.continuousOn
  have hc₀ : 0 < ρ r x₀ := h.pos r hr x₀
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2_proof hd D.s D.hs0 D.hsd (Bg + 1) hw D.invβ⁻¹
    D.invβ⁻¹ hβ (ρ r x₀) hc₀ Λ₂ 0
  have hP0 := hP (ρ r) (h.mf.density r hr) (h.ck r hr) (fun x => hx₀ (Set.mem_univ x))
    (hΛ₂ r hr) (fun _ _ => 0) measurable_const (fun _ _ => rfl) (fun x y => by simp) N hN
    D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ 0 (by simp [hθ₀.le])
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlow, hup⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ 0 := by
    intro h0
    rw [h0] at hlow
    simp at hlow
    exact absurd hlow (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  exact (gibbs_facts hgR hK0 hKt).2

/-- **Lower semicontinuity of the relative entropy along the regularisation** (the entropy part of B.15 Step 4,
M L12195-12204, for the moving reference): `H(f_t | Q_t) ≤ liminf_n H(f^n_t | Q^{M_n}_t)`.  PROVED from
`b15b_klDiv_liminf_le` (joint narrow lsc of `klDiv`, from Donsker-Varadhan), `b15c_marginal_tendsto` (narrow convergence of
the marginals) and `movT_Q_tendsto_weak_proof`. -/
theorem movfin_movT_entropy_lsc {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} {T : ℝ}
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hS : IsStrongSolution P D T X₀ W X)
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
      liminf (fun n => relEntropy (selectedLaw P (b15c_regProcess (Y n)) t)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop := by
  haveI hQ : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movfin_movT_Q_isProb hN htr ht
  haveI hQn : ∀ n, IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) :=
    fun n => movT_QReg_isProb D htr (M n) ht
  haveI hf : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    inferInstance
  haveI hfn : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (seq.sol n) s) t
  exact b15b_klDiv_liminf_le
    (fun φ hφ => b15c_marginal_tendsto hS seq.sol seq.eventually_eq ht.1 ht.2 hφ)
    (fun φ hφ => movT_Q_tendsto_weak_proof hN htr seq.levels seq.levels_nonneg ht hφ)

/-- **Gronwall step** (M L6456-6458): any system satisfying the integrated entropy inequality obeys
`H(f_t|Q_t) ≤ C(1 + H(f_0|Q_0) + Nδ_N)`, `C` depending only on the trajectory and `T` (not on `N`, the system, the initial
law).  PROVED from `movT_source_exp_proof`, `movT_traj_bounds_proof`, `movspec_int_le`, `movspec_gronwall_exp`. -/
theorem movT_entropy_gronwall_proof {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (htr : MovTraj D T ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (X : ℝ≥0 → Ω → Config d N),
      (∀ s : ℝ≥0, Measurable (X s)) → MovEntConcl D N T ρ P X₀ X →
      ∀ t ∈ Set.Icc 0 T,
        relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≠ ⊤ ∧
        (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal ≤
          C * (1 + (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal +
            N * deltaN d D.s N) := by
  obtain ⟨c₀, Lu, hc₀, hLu, hρlow, hLip⟩ := movT_traj_bounds_proof htr
  obtain ⟨Λ₂, hΛ⟩ := htr.bounds
  obtain ⟨l, C₁, hl, hexp⟩ := movT_source_exp_proof (b15_one_le_d D) D.hs0 D.hsd D.invβ⁻¹ D.invβ⁻¹
    (inv_pos.2 htr.pos_temp) c₀ hc₀ Λ₂
  set C1p : ℝ := max C₁ 0 with hC1p
  set A : ℝ := Lu / l with hA
  set Bc : ℝ := Lu * C1p / l with hBc
  have hA0 : 0 ≤ A := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  refine ⟨Real.exp (A * T) * max 1 (Bc * T), by positivity, ?_⟩
  intro N hN Ω _ P _ X₀ X hXm hmov t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hNδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN D.hs0 N (by omega)
  set f : ℝ → Measure (Config d N) := fun r => P.map (X r.toNNReal) with hf
  set Q : ℝ → Measure (Config d N) := fun r => movT_Q (periodicRiesz d D.s) D N ρ r with hQ
  set u : ℝ → ℝ := fun r => (relEntropy (f r) (Q r)).toReal with hu
  set G : ℝ → ℝ := fun r => ∫ Z, movT_source D N ρ r Z ∂(f r) with hG
  set a : ℝ := (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal with ha
  have hGint : IntegrableOn G (Set.Icc 0 T) := (hmov T ⟨hT, le_rfl⟩).2.2.1
  have hbd : ∀ t ∈ Set.Icc 0 T, u t ≤ a + ∫ r in Set.Icc 0 t, G r := fun t ht => (hmov t ht).2.2.2
  have hGu : ∀ r ∈ Set.Icc 0 T, G r ≤ A * u r + Bc * (N * deltaN d D.s N) := by
    intro r hr
    haveI : IsProbabilityMeasure (f r) :=
      inferInstance
    haveI : IsProbabilityMeasure (Q r) := movfin_movT_Q_isProb hN htr hr
    obtain ⟨hcomm, hex⟩ := hexp D rfl ⟨le_rfl, le_rfl⟩ (ρ r) (htr.mf.density r hr) (htr.ck r hr)
      (hρlow r hr) (hΛ r hr) Lu hLu (hLip r hr) N hN
    have hSi : Integrable (movT_source D N ρ r) (f r) := (hmov r hr).2.1 r ⟨hr.1, le_rfl⟩
    have hSQ : AEMeasurable (movT_source D N ρ r) (Q r) := by
      have h1 := hcomm.aemeasurable
      unfold movT_source movT_sourceAt
      exact (h1.sub aemeasurable_const).const_mul _
    have hex' : ∫⁻ Z, ENNReal.ofReal (Real.exp ((l / Lu) * |movT_source D N ρ r Z|)) ∂(Q r) ≤
        ENNReal.ofReal (Real.exp (C1p * (N * deltaN d D.s N))) := by
      refine hex.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have : C₁ ≤ C1p := le_max_left _ _
      nlinarith
    have key := movspec_int_le (f r) (Q r) hSi.aemeasurable hSQ (by positivity : 0 < l / Lu) hex'
      (hmov r hr).1
    have h1 : G r ≤ ∫ Z, |movT_source D N ρ r Z| ∂(f r) :=
      integral_mono hSi hSi.abs fun Z => le_abs_self _
    refine h1.trans (key.2.trans ?_)
    simp only [hu, hA, hBc, relEntropy]
    rw [div_le_iff₀ (by positivity : 0 < l / Lu)]
    field_simp
    nlinarith
  have hgr := movspec_gronwall_exp (A := A) (B := Bc * (N * deltaN d D.s N)) (H0 := a) hA0
    (mul_nonneg hBc0 (by linarith)) hGint hbd hGu t ht
  refine ⟨(hmov t ht).1, hgr.trans ?_⟩
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hE : Real.exp (A * t) ≤ Real.exp (A * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hA0)
  have hmx : Bc * t * (N * deltaN d D.s N) ≤ max 1 (Bc * T) * (N * deltaN d D.s N) :=
    mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left ht.2 hBc0).trans (le_max_right _ _))
      (by linarith)
  have h1 : a + Bc * (N * deltaN d D.s N) * t ≤ max 1 (Bc * T) * (1 + a + N * deltaN d D.s N) := by
    have hm1 : 1 ≤ max 1 (Bc * T) := le_max_left _ _
    nlinarith [mul_nonneg ha0 (sub_nonneg.2 hm1), le_max_right 1 (Bc * T)]
  calc (a + Bc * (N * deltaN d D.s N) * t) * Real.exp (A * t) ≤
        (max 1 (Bc * T) * (1 + a + N * deltaN d D.s N)) * Real.exp (A * T) :=
        mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
    _ = Real.exp (A * T) * max 1 (Bc * T) * (1 + a + N * deltaN d D.s N) := by ring



/-- **Step 1** of the constructive route: `mov_ent_ineq_proof` for a bounded initial density `dν₀/dQ₀ ≤ k`.  PROVED from
`movT_regSeq_exists_proof`, `movT_reg_ineq_proof`, `movT_init_tendsto_proof`, `movT_lp_init_limsup_proof`, `movT_lp_reg_bound_proof` (with `L ≡ 1`,
`p₀ = 2`, `c = l`, `Cs = C` from `movT_source_exp_uniform_proof'`), `movT_source_limit_bdd_proof`, `movfin_movT_entropy_lsc`,
`movspec_ent_assembly`. -/
theorem mov_ent_ineq_bdd_proof (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X)
    (hbdd : P.map X₀ ≪ movT_Q (periodicRiesz d D.s) D N ρ 0 ∧ ∃ k : ℝ,
      ∀ᵐ x ∂(movT_Q (periodicRiesz d D.s) D N ρ 0),
        (P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0) x ≤ ENNReal.ofReal k)
    (hfin : relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤) :
    MovEntConcl D N T ρ P X₀ X := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hS := h.sol
  obtain ⟨ℱ, W', M, Y₀, Y, seq⟩ := movT_regSeq_exists_proof h
  obtain ⟨ρt, hρt⟩ := h.traj.classical
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  haveI hQ0 : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ 0) :=
    movfin_movT_Q_isProb hN h.traj ⟨le_rfl, hT⟩
  obtain ⟨hfin_n, hH0⟩ := movT_init_tendsto_proof hN hT h.traj seq.levels seq.levels_nonneg hfin
  obtain ⟨l, C, M₀, hl, hexpM⟩ := movT_source_exp_uniform_proof' hN h.traj hρt
  have hMev : ∀ᶠ n in atTop, M₀ ≤ M n := seq.levels.eventually_ge_atTop M₀
  have hexp : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt r Z|))
        ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) :=
    ⟨l, C, hl, hMev.mono fun n hn r hr => hexpM (M n) hn r hr⟩
  -- the uniform `L^q` bound
  obtain ⟨kk, hkk⟩ := hbdd.2
  have hfin2 : eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0))
      (ENNReal.ofReal 2) (movT_Q (periodicRiesz d D.s) D N ρ 0) < ⊤ := by
    have := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal 2)
      (μ := movT_Q (periodicRiesz d D.s) D N ρ 0) (f := (P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0))
      (C := ENNReal.ofReal kk) (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
      (hkk.mono fun x hx => by simpa using hx)
    refine lt_of_le_of_lt this ?_
    simp [measure_univ]
  obtain ⟨hac_n, hlim0⟩ := movT_lp_init_limsup_proof hN hT h.traj seq.levels seq.levels_nonneg
    (p₀ := 2) (by norm_num) hbdd.1 hfin2
  set a := eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal 2)
    (movT_Q (periodicRiesz d D.s) D N ρ 0) with ha
  have haTop : a ≠ ⊤ := hfin2.ne
  have hlt : a < ENNReal.ofReal (a.toReal + 1) := by
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal haTop).symm
      _ < ENNReal.ofReal (a.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  have hAev : ∀ᶠ n in atTop, eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
      (ENNReal.ofReal 2) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) < ENNReal.ofReal (a.toReal + 1) :=
    hlim0.eventually (gt_mem_nhds hlt)
  have hLi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 T) := integrableOn_const (by simp)
  have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ (fun _ : ℝ => (1 : ℝ)) r := fun _ _ => zero_le_one
  have hint1 : ∫ r in Set.Icc 0 T, (fun _ : ℝ => (1 : ℝ)) r ≤ T := by simp [hT]
  set q0 : ℝ := 1 - 1 / 2 with hq0
  set eT : ℝ := Real.exp (-(1 / l) * T) with heT
  have heT0 : 0 < eT := Real.exp_pos _
  have heT1 : eT ≤ 1 := by
    rw [heT]; apply Real.exp_le_one_iff.2
    have : 0 < 1 / l := by positivity
    nlinarith
  set qT : ℝ := 1 / (1 - (1 - 1 / 2) * eT) with hqT
  have hden0 : 0 < 1 - (1 - 1 / 2 : ℝ) * eT := by nlinarith
  have hqT1 : 1 < qT := by
    rw [hqT, lt_div_iff₀ hden0]; nlinarith
  have hLq : ∃ q C : ℝ, 1 < q ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess (Y n)) r ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ r ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal q)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal C := by
    refine ⟨qT, (a.toReal + 1) * Real.exp (max C 0), hqT1, ?_⟩
    filter_upwards [hMev, hAev] with n hn hnA r hr
    have hnfin : eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
        (ENNReal.ofReal 2) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) < ⊤ :=
      lt_of_lt_of_le hnA le_top |>.trans_le le_rfl |> fun h => lt_of_lt_of_le hnA (by simp)
    have hexpS : ∀ r' ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
        ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt r' X| / (fun _ : ℝ => (1 : ℝ)) r'))
          ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r') ≤ ENNReal.ofReal (Real.exp C) := by
      intro r' hr'
      simpa using hexpM (M n) hn r' hr'
    have key := movT_lp_reg_bound_proof hN seq.brownian h.traj hρt (M n) (seq.levels_nonneg n)
      seq.init_adapted (seq.sol n) (c := l) (Cs := C) (ℓ := 1) hl one_pos
      (L := fun _ => 1) (fun r' _ => le_rfl) hLi hexpS (p₀ := 2) (by norm_num)
      (by rw [movT_reg_init_law seq n]; exact hac_n n)
      (by rw [movT_reg_init_law seq n]; exact hnfin) r hr
    rw [movT_reg_init_law seq n] at key
    haveI : IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) :=
      movT_QReg_isProb D h.traj (M n) hr
    have hpge : qT ≤ movT_pPath l 2 (fun _ => 1) r := by
      have := movT_pPath_ge (c := l) (p₀ := 2) (T := T) (Λ₁ := T) hl (by norm_num) hL0 hLi hr hint1
      simpa [hqT, heT] using this
    have hm : AEStronglyMeasurable ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) :=
      (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
    have hmono : eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal qT)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal (movT_pPath l 2 (fun _ => 1) r))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) :=
      eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpge)
    have hgain : movT_lpGain l C 2 (fun _ => 1) r ≤ max C 0 := by
      unfold movT_lpGain
      have hA : 0 ≤ (1 / l) * ∫ r' in (0 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) r' :=
        mul_nonneg (by positivity) (movT_intL_nonneg hL0 hr)
      have hE0 := Real.exp_pos (-(1 / l) * ∫ r' in (0 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) r')
      have hE1 : Real.exp (-(1 / l) * ∫ r' in (0 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) r') ≤ 1 := by
        apply Real.exp_le_one_iff.2; nlinarith
      set κ := (1 - 1 / 2 : ℝ) * (1 - Real.exp (-(1 / l) * ∫ r' in (0 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) r'))
        with hκ
      have hκ0 : 0 ≤ κ := mul_nonneg (by norm_num) (by linarith)
      have hκ1 : κ ≤ 1 := by rw [hκ]; nlinarith
      have : C * (1 - 1 / 2) * (1 - Real.exp (-(1 / l) * ∫ r' in (0 : ℝ)..r, (fun _ : ℝ => (1 : ℝ)) r')) = C * κ := by
        rw [hκ]; ring
      rw [this]
      rcases le_total 0 C with hc | hc
      · calc C * κ ≤ C * 1 := mul_le_mul_of_nonneg_left hκ1 hc
          _ ≤ max C 0 := by simpa using le_max_left C 0
      · have : C * κ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hκ0
        exact this.trans (le_max_right _ _)
    refine ⟨key.1, hmono.trans (key.2.trans ?_)⟩
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' hnA.le (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hgain))
  obtain ⟨hint, hintOn, hlim⟩ := movT_source_limit_bdd_proof hN h.traj hρt hS seq hexp hLq
  have hreg := fun n => movT_reg_ineq_proof hN seq.brownian h.traj hρt (M n) (seq.levels_nonneg n)
    seq.init_adapted (seq.sol n) (by rw [movT_reg_init_law seq n]; exact hfin_n n)
  have hpart := movspec_ent_assembly
    (H := fun n => relEntropy (selectedLaw P (b15c_regProcess (Y n)) t)
      (movT_Q (b15c_gReg d D.s (M n)) D N ρ t))
    (H0 := fun n => relEntropy (P.map X₀) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
    (I := fun n => ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N (M n) ρ ρt r Z
      ∂(selectedLaw P (b15c_regProcess (Y n)) r))
    (Hlim := relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t))
    (hlsc := movfin_movT_entropy_lsc hN h.traj hS seq ht)
    (hreg := fun n => by
      have := hreg n t ht
      rw [movT_reg_init_law seq n] at this
      exact ⟨this.1, this.2.2.2⟩)
    hH0 (hlim t ht)
  refine ⟨hpart.1, fun r hr => hint r ⟨hr.1, hr.2.trans ht.2⟩, ?_, hpart.2⟩
  exact hintOn.mono_set (Set.Icc_subset_Icc le_rfl ht.2)


/-- The exponential moment of the exact source and the integrability of `C_N` under `Q_N^r`, for fixed `N`, along the
trajectory (from `movT_source_exp_proof` and `movT_traj_bounds_proof`). -/
theorem movfin_movT_traj_exp (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (htr : MovTraj D T ρ) :
    ∃ l C : ℝ, 0 < l ∧ ∀ r ∈ Set.Icc 0 T,
      Integrable (movT_comm D N ρ r) (movT_Q (periodicRiesz d D.s) D N ρ r) ∧
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_source D N ρ r Z|))
        ∂(movT_Q (periodicRiesz d D.s) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) := by
  obtain ⟨c₀, Lu, hc₀, hLu, hρlow, hLip⟩ := movT_traj_bounds_proof htr
  obtain ⟨Λ₂, hΛ⟩ := htr.bounds
  obtain ⟨l, C₁, hl, hexp⟩ := movT_source_exp_proof (b15_one_le_d D) D.hs0 D.hsd D.invβ⁻¹ D.invβ⁻¹
    (inv_pos.2 htr.pos_temp) c₀ hc₀ Λ₂
  refine ⟨l / Lu, C₁ * N * deltaN d D.s N, by positivity, fun r hr => ?_⟩
  exact hexp D rfl ⟨le_rfl, le_rfl⟩ (ρ r) (htr.mf.density r hr) (htr.ck r hr) (hρlow r hr) (hΛ r hr)
    Lu hLu (hLip r hr) N hN

/-- **`mov_ent_ineq_proof` (moving-reference entropy inequality, Fisher term dropped).**  Theorem-level statement of
`N:eq:entropy-differential` (M L6452-6457) for the *unregularised* particle system, in the integrated form with the
nonpositive Fisher term discarded (ISSUES MOV item 4): for all `t ∈ [0,T]`, `H(f_N^t | Q_N^t) < ∞` and
`H(f_N^t|Q_N^t) ≤ H(f_N^0|Q_N^0) + ∫_0^t ∫ R_N^r f_N^r dr`, `R_N^r` the exact source `N:eq:source`
(`movT_source`), `f_N^r = Law(X_N^r)`, `Q_N^r = ℚ_{N,β}(μ^r)`; integrability of `R_N^r` under `f_N^r` and of
`r ↦ ∫R_N^r df_N^r` is part of the conclusion, as is the `Q_N^r`-integrability of `C_N(u^r;μ^r)` (non-junk
`E_{Q_N}[C_N]` in `movT_source`).  Standing assumptions: `MovHyp`; `H(f_N^0|Q_N^0) < ∞` (M L6078).
Proof: truncation of the initial density (`movT_cond_entropy_limit_proof`), conditioning (`movT_cond_hyp_proof`),
`mov_ent_ineq_bdd_proof` for each conditioned system, `movT_entropy_gronwall_proof` (uniform entropy bound),
`movT_source_limit_cond_proof`, lower semicontinuity (`b15b_klDiv_liminf_le`, `movT_cond_narrow_proof`),
`movspec_ent_assembly`.  Discharges the justification sentence of M L6466-6467 for `dynamic_entropy`/`dynamic_comparison`. -/
theorem mov_ent_ineq_proof (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X)
    (hfin : relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤) :
    (∀ t ∈ Set.Icc 0 T,
      relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≠ ⊤ ∧
      (∀ r ∈ Set.Icc 0 t, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
      IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 t) ∧
      (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal ≤
        (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) ∧
    ∀ r ∈ Set.Icc 0 T, Integrable (movT_comm D N ρ r) (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  obtain ⟨lR, CR, hlR, hRexp⟩ := movfin_movT_traj_exp hN h.traj
  refine ⟨?_, fun r hr => (hRexp r hr).1⟩
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hS := h.sol
  have hXm : ∀ s : ℝ≥0, Measurable (X s) := hS.adapted
  have hX0 : Measurable (X 0) := hXm 0
  haveI hQ0 : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ 0) :=
    movfin_movT_Q_isProb hN h.traj ⟨le_rfl, hT⟩
  haveI hQt : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movfin_movT_Q_isProb hN h.traj ht
  -- initial law
  have hν₀ : P.map X₀ = P.map (X 0) := (Measure.map_congr (by
    filter_upwards [hS.init] with ω hω using hω.symm))
  set ν₀ : Measure (Config d N) := P.map (X 0) with hν₀def
  rw [hν₀] at hfin
  obtain ⟨K₀, hν1, hk, hH0lim⟩ := movT_cond_entropy_limit_proof ν₀ (movT_Q (periodicRiesz d D.s) D N ρ 0) hfin
  obtain ⟨Cg, hCg0, hgron⟩ := movT_entropy_gronwall_proof h.traj
  -- the conditioning events
  set B : ℕ → Set (Config d N) := fun n => movT_truncSet ν₀ (movT_Q (periodicRiesz d D.s) D N ρ 0) (n + K₀)
    with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n => movT_truncSet_meas _ _ _
  set A : ℕ → Set Ω := fun n => (X 0) ⁻¹' (B n) with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => hX0 (hBm n)
  have hPA : ∀ n, P (A n) = ν₀ (B n) := fun n => (Measure.map_apply hX0 (hBm n)).symm
  have hPA1 : Tendsto (fun n => P (A n)) atTop (𝓝 1) := by
    have := hν1.comp (tendsto_add_atTop_nat K₀)
    simpa [hPA, hB, Function.comp_def] using this
  have hk2 := fun n : ℕ => hk (n + K₀) (by omega)
  have hPAne : ∀ n, P (A n) ≠ 0 := fun n => by rw [hPA]; exact (hk2 n).1
  have hPAtop : ∀ n, P (A n) ≠ ⊤ := fun n => measure_ne_top _ _
  haveI hPk : ∀ n, IsProbabilityMeasure (movT_cond P (A n)) := fun n =>
    movT_cond_isProb P (hPAne n) (hPAtop n)
  have hHk : ∀ n, MovHyp (movT_cond P (A n)) D N T ρ X₀ W X := fun n =>
    movT_cond_hyp_proof h (hBm n) (hPAne n)
  -- the initial law of the conditioned systems
  have hmap : ∀ n, (movT_cond P (A n)).map X₀ =
      movT_truncLaw ν₀ (movT_Q (periodicRiesz d D.s) D N ρ 0) (n + K₀) := by
    intro n
    have h1 : (movT_cond P (A n)).map X₀ = (movT_cond P (A n)).map (X 0) := by
      refine Measure.map_congr ?_
      have hac : movT_cond P (A n) ≪ P := by
        unfold movT_cond
        exact (Measure.smul_absolutelyContinuous).trans Measure.restrict_le_self.absolutelyContinuous
      exact hac.ae_le (by filter_upwards [hS.init] with ω hω using hω.symm)
    rw [h1, movT_cond_map P hX0 (hBm n)]
    rfl
  have hconcl : ∀ n, MovEntConcl D N T ρ (movT_cond P (A n)) X₀ X := fun n =>
    mov_ent_ineq_bdd_proof hN (movT_cond P (A n)) (hHk n)
      ⟨by rw [hmap n]; exact (hk2 n).2.1, by rw [hmap n]; exact (hk2 n).2.2.1⟩
      (by rw [hmap n]; exact (hk2 n).2.2.2)
  -- the initial entropies converge
  have hH0lim' : Tendsto (fun n => (relEntropy ((movT_cond P (A n)).map X₀)
      (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal) atTop
      (𝓝 (relEntropy ν₀ (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal) := by
    have := hH0lim.comp (tendsto_add_atTop_nat K₀)
    simpa [hmap, Function.comp_def] using this
  obtain ⟨Bd, hBd⟩ := hH0lim'.bddAbove_range
  -- uniform entropy bound for the conditioned marginals
  have hUnif : ∃ C : ℝ, ∀ n, ∀ r ∈ Set.Icc 0 T,
      relEntropy ((movT_cond P (A n)).map (X r.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ r) ≤
        ENNReal.ofReal C := by
    refine ⟨Cg * (1 + Bd + N * deltaN d D.s N), fun n r hr => ?_⟩
    obtain ⟨hne, hle⟩ := hgron N hN (movT_cond P (A n)) X₀ X hXm (hconcl n) r hr
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
    have : (relEntropy ((movT_cond P (A n)).map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal ≤ Bd :=
      hBd ⟨n, rfl⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hCg0
  obtain ⟨hint, hintOn, hlim⟩ := movT_source_limit_cond_proof hN h.traj hS hAm hPA1
    ⟨lR, CR, hlR, fun r hr => (hRexp r hr).2⟩ hUnif
  -- lower semicontinuity of the entropy at time `t`
  have hlsc : relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
      liminf (fun n => relEntropy ((movT_cond P (A n)).map (X t.toNNReal))
        (movT_Q (periodicRiesz d D.s) D N ρ t)) atTop := by
    have hP : ∀ φ : Config d N → ℝ, Continuous φ →
        Tendsto (fun n => ∫ x, φ x ∂((movT_cond P (A n)).map (X t.toNNReal))) atTop
          (𝓝 (∫ x, φ x ∂(P.map (X t.toNNReal)))) := by
      intro φ hφ
      obtain ⟨Cφ, hCφ⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hφ.continuousOn
      haveI : BorelSpace (Torus d) := Pi.borelSpace
      haveI : BorelSpace (Config d N) := Pi.borelSpace
      exact movT_cond_narrow_proof P (hXm _) hAm hPA1 hφ ⟨Cφ, fun x => by
        simpa using hCφ x (Set.mem_univ x)⟩
    exact b15b_klDiv_liminf_le hP (fun φ _ => tendsto_const_nhds)
  have hpart := movspec_ent_assembly
    (H := fun n => relEntropy ((movT_cond P (A n)).map (X t.toNNReal))
      (movT_Q (periodicRiesz d D.s) D N ρ t))
    (H0 := fun n => relEntropy ((movT_cond P (A n)).map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0))
    (I := fun n => ∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z
      ∂((movT_cond P (A n)).map (X r.toNNReal)))
    (Hlim := relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t))
    hlsc (fun n => by
      have := hconcl n t ht
      exact ⟨this.1, this.2.2.2⟩) hH0lim' (hlim t ht)
  rw [hν₀]
  exact ⟨hpart.1, fun r hr => hint r ⟨hr.1, hr.2.trans ht.2⟩,
    hintOn.mono_set (Set.Icc_subset_Icc le_rfl ht.2), hpart.2⟩


/-- **`movT_entropy_bound_proof`: `sup_{t≤T} H(f_N^t|Q_N^t) ≤ C_T B_N`** (M L6456-6458), `B_N = 1 + H(f_N^0|Q_N^0) + Nδ_N`
(`entropyScale`).  The constant depends only on the trajectory (`MovTraj`) and `T`, not on `N`, the system or the initial law
(M L6558).  PROVED from `mov_ent_ineq_proof` and `movT_entropy_gronwall_proof`.  The product-entropy half of `dynamic_entropy`
(`N:eq:product-entropy`, M L6460-6464) is `movT_relEntropy_split_proof` plus the last conclusion of `perturbed_pressure` (resp.
its `C²` version) with `h = g`, in the consumer. -/
theorem movT_entropy_bound_proof {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (htr : MovTraj D T ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N), MovHyp P D N T ρ X₀ W X →
      relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤ →
      ∀ t ∈ Set.Icc 0 T,
        relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≠ ⊤ ∧
        (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal ≤
          C * (1 + (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal +
            N * deltaN d D.s N) := by
  obtain ⟨C, hC0, hg⟩ := movT_entropy_gronwall_proof htr
  exact ⟨C, hC0, fun N hN Ω _ P _ X₀ W X hH hfin =>
    hg N hN P X₀ X hH.sol.adapted (mov_ent_ineq_proof hN P hH hfin).1⟩

example := (@movfin_movT_Q_isProb : type_of% @HRS.movT_Q_isProb)
example := (@movfin_movT_entropy_lsc : type_of% @HRS.movT_entropy_lsc)
example := (@movT_entropy_gronwall_proof : type_of% @HRS.movT_entropy_gronwall)
example := (@mov_ent_ineq_bdd_proof : type_of% @HRS.mov_ent_ineq_bdd)
example := (@mov_ent_ineq_proof : type_of% @HRS.mov_ent_ineq)
example := (@movT_entropy_bound_proof : type_of% @HRS.movT_entropy_bound)

end HRS

end
