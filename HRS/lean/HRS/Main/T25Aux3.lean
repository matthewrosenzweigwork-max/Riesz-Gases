import HRS.Main.T25Aux2

/-!
# T25-IN, part 3 (ENT-UNI): horizon-uniform entropy input `P:eq:entropy-input`

TeX M L6558-6560: `sup_{t ≥ 0} (H(f_N^t | Q_N^t) + H(f_N^t | (μ^t)^{⊗N})) ≤ C B_N`, the constant uniform over the smooth positive
trajectory.  The proved `dynamic_entropy_proof'` has a constant depending on the horizon `T` (`movT_entropy_gronwall_proof` uses the
sup of the Lipschitz bound, `e^{A T}`).  Here:

* `t25_product_bound` is a single-time copy of `dynent_product_bound` (its constant depends only on `(D, c₀, Λ₂)`, which the
  statement of the original, quantified over a horizon `T`, hides);
* `t25_entropy_Q`: `H(f^t | Q^t) ≤ C (1 + H(f^0|Q^0) + Nδ_N)` for all `t ≤ T` with `C` independent of `T`, by the weighted Gronwall
  `t25_gronwall_unif` (T25Aux2) with `G(r) ≤ L(r)(u(r)/l + C₁Nδ_N/l)` (the per-time exponential source bound `movT_source_exp_proof`
  with `Lu = L(r)`, the entropy inequality `movspec_int_le`) and the all-time Lipschitz bound `L` of `MovLog.movlog_L`
  (`∫_0^T L ≤ Λ₁` for all `T`);
* `t25_entropy_uniform`: both entropies, `≤ C B_N` with `C` independent of `N`, `T`, `t`, the system and the initial law.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

variable {d : ℕ}

/-- Single-time copy of `dynent_product_bound` (`N:eq:product-entropy`, M L6460-6464): for a `C²` density `ρt` with
`c₀ ≤ ρt`, `‖ρt‖_{C²} ≤ Λ₂`, and a probability law `ν` with `H(ν|Q) < ∞`: `H(ν|μ^{⊗N}) < ∞` and
`H(ν|μ^{⊗N}) ≤ H(ν|Q) + C (Nδ_N + H(ν|Q))`, `C = C(D, c₀, Λ₂)`. -/
theorem t25_product_bound (hd : 1 ≤ d) {D : DynData d} (hpt : 0 < D.invβ) {c₀ Λ₂ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ ρt : Torus d → ℝ, IsProbDensity ρt → Torus.IsCk 2 ρt →
      (∀ x, 0 < ρt x) → (∀ x, c₀ ≤ ρt x) → Torus.cbNorm 2 ρt ≤ Λ₂ →
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt)) ≠ ⊤ →
        relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρt) ≠ ⊤ ∧
        (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρt)).toReal ≤
          (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt))).toReal +
            C * (N * deltaN d D.s N + (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹
              (withDensityReal ρt))).toReal) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hpt
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  set cs : ℝ := 2 * |Bg| + 1 with hcs
  have hBa := le_abs_self Bg
  have hBn := neg_abs_le Bg
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + cs := fun z _ => by
    have := hBg z; have := abs_nonneg Bg; linarith
  have hdom : ∀ x y : Torus d, |periodicRiesz d D.s (x - y)| ≤
      1 * (periodicRiesz d D.s (x - y) + cs) := by
    intro x y
    have := hBg (x - y)
    have := abs_nonneg Bg
    rw [abs_le]; constructor <;> linarith
  have hgm : Measurable (periodicRiesz d D.s) := CoercAux.measurable_periodicRiesz_one hd D.hs0 D.hsd
  have hhm : Measurable (Function.uncurry fun x y : Torus d => periodicRiesz d D.s (x - y)) :=
    hgm.comp (measurable_fst.sub measurable_snd)
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2_proof hd D.s D.hs0 D.hsd cs hw D.invβ⁻¹
    D.invβ⁻¹ hβ c₀ hc₀ Λ₂ 1
  set Cp : ℝ := (D.invβ⁻¹ * θ₀)⁻¹ * (2 * C + 1) with hCp
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  refine ⟨D.invβ⁻¹ * Cp + C, by positivity, ?_⟩
  intro N hN ρt hρ hck hpos hlow hΛ ν hν hHfin
  haveI := isProb_withDensityReal hρ
  have hcont : Continuous ρt := b15_continuous_of_isCk hck
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρt x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd D.s D.hs0 D.hsd cs hw 1 hMρ0 hρΛ
    (h := fun x y => periodicRiesz d D.s (x - y)) hhm hdom
  have hPt : ∀ θ : ℝ, |θ| ≤ θ₀ →
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d D.s N))) ≤
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) - θ * periodicRiesz d D.s (x - y)) X
              (withDensityReal ρt))) ∂(Measure.pi fun _ : Fin N => withDensityReal ρt) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) - θ * periodicRiesz d D.s (x - y)) X
              (withDensityReal ρt))) ∂(Measure.pi fun _ : Fin N => withDensityReal ρt) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := fun θ hθ =>
    hP ρt hρ hck hlow hΛ (fun x y => periodicRiesz d D.s (x - y)) hhm
      (fun x y => by rw [← neg_sub, periodicRiesz_neg]) hdom N hN D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ θ hθ
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN D.hs0 N (by omega)
  have hmom := moments_of_pressure (N := N) hgR hhR hδ hC hθ₀ hβ (le_refl _) hPt
  have hsplit := movT_relEntropy_split_proof hN hpt hρ hck hpos (ν := ν)
  have hMFE := hsplit.1.1 hHfin
  have hid := hsplit.2 hMFE
  -- lower bound on the normaliser
  have hP0 := (hPt 0 (by simp [hθ₀.le]))
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlowK, hupK⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal ρt)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρt) ≠ 0 := by
    intro h0
    rw [h0] at hlowK
    simp at hlowK
    exact absurd hlowK (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal ρt)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρt) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupK
  have hKeq := (gibbs_facts hgR hK0 hKt).1
  have hKnn : 0 ≤ gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt) :=
    integral_nonneg fun X => (Real.exp_pos _).le
  have hKge : Real.exp (-(C * N * deltaN d D.s N)) ≤
      gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt) := by
    rw [← hKeq] at hlowK
    exact (ENNReal.ofReal_le_ofReal_iff hKnn).1 hlowK
  have hlogK : -(C * N * deltaN d D.s N) ≤
      Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt)) := by
    have := Real.log_le_log (Real.exp_pos _) hKge
    rwa [Real.log_exp] at this
  -- moment bound
  have hm := hmom.2 ν hν (lt_top_iff_ne_top.2 hHfin)
  set Fm : Config d N → ℝ := fun X => modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X
    (withDensityReal ρt) with hFm
  have hFmeas : Measurable Fm := measurable_modulatedEnergy hhR
  have hJ : ∫ X, (N : ℝ) * |Fm X| ∂ν ≤ Cp * ((relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N
      D.invβ⁻¹ (withDensityReal ρt))).toReal + N * deltaN d D.s N) := by
    have hnn : 0 ≤ᵐ[ν] fun X => (N : ℝ) * |Fm X| := Eventually.of_forall fun X => by positivity
    have hae : AEStronglyMeasurable (fun X => (N : ℝ) * |Fm X|) ν :=
      (measurable_const.mul (hFmeas.norm)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hnn hae]
    have hle := ENNReal.toReal_mono (by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hHfin, ENNReal.ofReal_ne_top⟩))
      hm
    refine hle.trans (le_of_eq ?_)
    have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCp0, ENNReal.toReal_add hHfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hNδ]
  have hFint : Integrable Fm ν := hMFE.2
  have hE : -((N : ℝ) * ∫ X, Fm X ∂ν) ≤ ∫ X, (N : ℝ) * |Fm X| ∂ν := by
    rw [integral_const_mul]
    have h1 : |∫ X, Fm X ∂ν| ≤ ∫ X, |Fm X| ∂ν := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) Fm
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [neg_abs_le (∫ X, Fm X ∂ν), mul_le_mul_of_nonneg_left h1 hN0]
  refine ⟨hMFE.1, ?_⟩
  have hH0 := ENNReal.toReal_nonneg (a := relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N
      D.invβ⁻¹ (withDensityReal ρt)))
  have hid' : (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρt)).toReal =
      (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt))).toReal
        - D.invβ⁻¹ * ((N : ℝ) * ∫ X, Fm X ∂ν) -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt)) := by
    have : ∫ X, rieszEnergy d D.s X (withDensityReal ρt) ∂ν = ∫ X, Fm X ∂ν := rfl
    rw [this] at hid
    linarith
  rw [hid']
  have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
  have hb1 : -(D.invβ⁻¹ * ((N : ℝ) * ∫ X, Fm X ∂ν)) ≤ D.invβ⁻¹ * (Cp * ((relEntropy ν
      (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρt))).toReal +
      N * deltaN d D.s N)) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (hE.trans hJ) hβ.le
  have hCH := mul_nonneg hC hH0
  have hbCp : 0 ≤ D.invβ⁻¹ * Cp := mul_nonneg hβ.le hCp0
  nlinarith [hlogK, hb1, hCH, mul_nonneg hbCp hH0, mul_nonneg hbCp hNδ]


theorem t25_setInt_eq {G : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in Set.Icc 0 r, G x = ∫ x in (0 : ℝ)..r, G x := by
  rw [intervalIntegral.integral_of_le hr, integral_Icc_eq_integral_Ioc]

/-- **Horizon-uniform `Q`-entropy bound** (the `Q`-half of `P:eq:entropy-input`, M L6558): for every horizon `T`, a `MovHyp` system
and `t ≤ T`: `H(f^t | Q^t) < ∞` and `H(f^t|Q^t) ≤ C (1 + H(f^0|Q^0) + Nδ_N)`, with `C` independent of `T`, `N`, the system. -/
theorem t25_entropy_Q (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        MovHyp P htr.dyn N T ρ X₀ W X →
        relEntropy (P.map X₀) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0) ≠ ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ t) ≠ ⊤ ∧
          (relEntropy (P.map (X t.toNNReal))
              (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ t)).toReal ≤
            C * (1 + (relEntropy (P.map X₀)
              (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0)).toReal +
                N * deltaN d htr.dyn.s N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ := movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ
    htr.V_smooth htr.init htr.global
  obtain ⟨Λ₁, hΛ₁, L, hLl, hLi, hLlip, hLint⟩ := MovLog.movlog_L hd htr
  have hinv : 0 < htr.dyn.invβ := inv_pos.2 htr.hβ
  obtain ⟨l, C₁, hl, hexp⟩ := movT_source_exp_proof (s := htr.dyn.s) hd1 htr.hs0 htr.hsd htr.dyn.invβ⁻¹
    htr.dyn.invβ⁻¹ (inv_pos.2 hinv) c₀ hc₀ Λ₂
  set C1p : ℝ := max C₁ 0 with hC1p
  have hC1p0 : 0 ≤ C1p := le_max_right _ _
  refine ⟨2 ^ (⌈2 * (1 / l) * Λ₁⌉₊ + 1) * max 1 C1p, by positivity, ?_⟩
  intro N hN T hT Ω _ P _ X₀ W X hMov hfin t ht
  have htrT : MovTraj htr.dyn T ρ := hMov.traj
  obtain ⟨hmov, -⟩ := mov_ent_ineq_proof hN P hMov hfin
  have hNδ : 1 ≤ (N : ℝ) * deltaN d htr.dyn.s N := one_le_mul_deltaN htr.dyn.hs0 N (by omega)
  set f : ℝ → Measure (Config d N) := fun r => P.map (X r.toNNReal) with hf
  set Q : ℝ → Measure (Config d N) := fun r => movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r
    with hQ
  set u : ℝ → ℝ := fun r => (relEntropy (f r) (Q r)).toReal with hu
  set G : ℝ → ℝ := fun r => ∫ Z, movT_source htr.dyn N ρ r Z ∂(f r) with hG
  set a : ℝ := (relEntropy (P.map X₀) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0)).toReal
    with ha
  have hGint : IntegrableOn G (Set.Icc 0 T) := (hmov T ⟨hT, le_rfl⟩).2.2.1
  have hbd : ∀ t ∈ Set.Icc 0 T, u t ≤ a + ∫ r in Set.Icc 0 t, G r := fun t ht => (hmov t ht).2.2.2
  have hu0 : ∀ r, 0 ≤ u r := fun r => ENNReal.toReal_nonneg
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLl T
  have hLpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < L r := fun r hr => lt_of_lt_of_le hℓ (hLℓ r hr)
  have hGu : ∀ r ∈ Set.Icc 0 T,
      G r ≤ L r * ((1 / l) * u r + C1p / l * ((N : ℝ) * deltaN d htr.dyn.s N)) := by
    intro r hr
    haveI : IsProbabilityMeasure (f r) :=
      ((Measure.isProbabilityMeasure_map_iff (hMov.sol.adapted _).aemeasurable).2 inferInstance)
    haveI : IsProbabilityMeasure (Q r) := movfin_movT_Q_isProb hN htrT hr
    obtain ⟨hcomm, hex⟩ := hexp htr.dyn rfl ⟨le_rfl, le_rfl⟩ (ρ r) (htrT.mf.density r hr)
      (htrT.ck r hr) (hb r hr.1).1 (hb r hr.1).2 (L r) (hLpos r hr) (hLlip T r hr) N hN
    have hSi : Integrable (movT_source htr.dyn N ρ r) (f r) := (hmov r hr).2.1 r ⟨hr.1, le_rfl⟩
    have hSQ : AEMeasurable (movT_source htr.dyn N ρ r) (Q r) := by
      have h1 := hcomm.aemeasurable
      unfold movT_source movT_sourceAt
      exact (h1.sub aemeasurable_const).const_mul _
    have hex' : ∫⁻ Z, ENNReal.ofReal (Real.exp ((l / L r) * |movT_source htr.dyn N ρ r Z|)) ∂(Q r) ≤
        ENNReal.ofReal (Real.exp (C1p * ((N : ℝ) * deltaN d htr.dyn.s N))) := by
      refine hex.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have : C₁ ≤ C1p := le_max_left _ _
      nlinarith
    have key := movspec_int_le (f r) (Q r) hSi.aemeasurable hSQ
      (by have := hLpos r hr; positivity : 0 < l / L r) hex' (hmov r hr).1
    have h1 : G r ≤ ∫ Z, |movT_source htr.dyn N ρ r Z| ∂(f r) :=
      integral_mono hSi hSi.abs fun Z => le_abs_self _
    refine h1.trans (key.2.trans (le_of_eq ?_))
    have hLr := (hLpos r hr).ne'
    simp only [hu, relEntropy]
    field_simp
  have hvu : ∀ r ∈ Set.Icc (0 : ℝ) T, u r ≤ t25V a G r := by
    intro r hr
    have := hbd r hr
    rw [t25_setInt_eq hr.1] at this
    exact this
  have hv0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ t25V a G r := fun r hr => (hu0 r).trans (hvu r hr)
  have hGv : ∀ r ∈ Set.Icc 0 T, G r ≤ L r *
      ((1 / l) * t25V a G r + C1p / l * ((N : ℝ) * deltaN d htr.dyn.s N)) := by
    intro r hr
    refine (hGu r hr).trans ?_
    exact mul_le_mul_of_nonneg_left (by have := hvu r hr; have : 0 < 1 / l := by positivity
                                        nlinarith) (hLpos r hr).le
  have hΛ : ∫ x in (0 : ℝ)..T, L x ≤ Λ₁ := by
    rw [← t25_setInt_eq hT]; exact hLint T
  have hgr := t25_gronwall_unif (A := 1 / l) (B := C1p / l * ((N : ℝ) * deltaN d htr.dyn.s N))
    (H0 := a) hGint (hLi T) (fun r hr => (hLpos r hr).le) (by positivity) (by positivity) hv0 hGv hΛ
    hT t ht
  refine ⟨(hmov t ht).1, ?_⟩
  have hBA : C1p / l * ((N : ℝ) * deltaN d htr.dyn.s N) / (1 / l) = C1p * ((N : ℝ) * deltaN d htr.dyn.s N) := by
    field_simp
  rw [hBA] at hgr
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hm1 : (1 : ℝ) ≤ max 1 C1p := le_max_left _ _
  have hmC : C1p ≤ max 1 C1p := le_max_right _ _
  have hp : (0 : ℝ) ≤ 2 ^ (⌈2 * (1 / l) * Λ₁⌉₊ + 1) := by positivity
  have hfin2 : a + C1p * ((N : ℝ) * deltaN d htr.dyn.s N) ≤
      max 1 C1p * (1 + a + (N : ℝ) * deltaN d htr.dyn.s N) := by
    nlinarith [mul_le_mul_of_nonneg_right hmC (by linarith : 0 ≤ (N : ℝ) * deltaN d htr.dyn.s N),
      mul_le_mul_of_nonneg_right hm1 ha0]
  calc u t ≤ t25V a G t := hvu t ht
    _ ≤ 2 ^ (⌈2 * (1 / l) * Λ₁⌉₊ + 1) * (a + C1p * ((N : ℝ) * deltaN d htr.dyn.s N)) := hgr
    _ ≤ 2 ^ (⌈2 * (1 / l) * Λ₁⌉₊ + 1) * (max 1 C1p *
          (1 + a + (N : ℝ) * deltaN d htr.dyn.s N)) := mul_le_mul_of_nonneg_left hfin2 hp
    _ = _ := by ring

/-- **`P:eq:entropy-input`, horizon-uniform** (TeX M L6558-6560): `H(f_N^t | Q_N^t) + H(f_N^t | (μ^t)^{⊗N}) ≤ C B_N`
for every horizon `T ≥ t ≥ 0`, with `C` independent of `N`, `T`, `t`, the system and the initial law (contrast
`dynamic_entropy_proof'`, whose constant depends on `T`). -/
theorem t25_entropy_uniform (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          relEntropy (P.map (X t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) +
            relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ := movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ
    htr.V_smooth htr.init htr.global
  obtain ⟨C₁, hC₁0, hC₁⟩ := t25_entropy_Q hd htr
  have hpt : 0 < htr.dyn.invβ := inv_pos.2 htr.hβ
  obtain ⟨C₂, hC₂0, hC₂⟩ := t25_product_bound hd1 hpt hc₀ (Λ₂ := Λ₂)
  refine ⟨2 * C₁ + C₂ * (1 + C₁), by positivity, ?_⟩
  intro N hN T hT Ω _ P _ X₀ W X hP hfilt hfin t ht
  have e : ∀ r, movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) := fun r =>
    movT_Q_eq_beta (g := periodicRiesz d s) rfl N ρ r
  have htrT : MovTraj htr.dyn T ρ := MovLog.movlog_traj htr T
  have hMov : MovHyp P htr.dyn N T ρ X₀ W X :=
    movT_hyp_of_parts htrT hP.brownian hP.indep hP.sol hfilt
  have hfin' : relEntropy (P.map X₀) (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ 0) ≠ ⊤ := by
    rw [e]; exact hfin
  obtain ⟨hfinT, hbd⟩ := hC₁ N hN T hT P X₀ W X hMov hfin' t ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    ((Measure.isProbabilityMeasure_map_iff (hP.sol.adapted _).aemeasurable).2 inferInstance)
  have hρt := htrT.mf.density t ht
  have hinvs : htr.dyn.invβ⁻¹ = β := by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]
  rw [e] at hfinT hbd
  have hfinT' : relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d htr.dyn.s) N htr.dyn.invβ⁻¹ (withDensityReal (ρ t))) ≠ ⊤ := by
    rw [hinvs]; exact hfinT
  obtain ⟨hprodfin, hprodle⟩ := hC₂ N hN (ρ t) hρt (htrT.ck t ht) (htrT.pos t ht)
    (hb t ht.1).1 (hb t ht.1).2 (P.map (X t.toNNReal)) inferInstance hfinT'
  rw [hinvs] at hprodle
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hbd' : (relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal ≤ C₁ * B := by
    rw [e 0] at hbd; exact hbd
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal :=
    ENNReal.toReal_nonneg
  have hBge : (N : ℝ) * deltaN d s N ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hHq0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
  have hp0 := ENNReal.toReal_nonneg (a := relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t)))
  have hprodfin' : relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≠ ⊤ := hprodfin
  rw [← ENNReal.ofReal_toReal hfinT, ← ENNReal.ofReal_toReal hprodfin',
    ← ENNReal.ofReal_add hHq0 hp0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpr : (relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal ≤
      (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal +
      C₂ * ((N : ℝ) * deltaN d s N + (relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal) := by
    have := hprodle
    simpa [IsSmoothPositiveTrajectory.dyn, PDE.mfData] using this
  nlinarith [mul_le_mul_of_nonneg_left hBge hC₂0, mul_le_mul_of_nonneg_left hbd' hC₂0, hC₁0]

end T25

end HRS

end
