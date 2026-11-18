import HRS.MC.CepE7A4

/-!
# Packet CEPE7 (`cep_E7_existence`): PLAN (assembly of E0, E1, E2, E3, E5c/E6, K1, `cep_pair_cot_le`)

Namespace `HRS.MC.CepE7`, helpers prefixed `cepE7_`.  Assembly, in order:
1. Canonical Brownian filtration `ℱc, W'c` and `X₀` measurable for all `t : ℝ`
   (`exists_isBrownianFiltration_of_isVectorBrownian`, `Bridge.lean:75`); `W'c = W` a.s.
2. Labelling `π ω = π₀ (X₀ ω)` with `π₀` from `cep_E0_sort_proof` (fibres measurable).  E0 and `hdist` hold only a.s., while
   E4-E6 need `hz₀A`, `hz₀b` for ALL `ω`: `z₀ ω = cep_toCh (π ω) (rep ∘ X₀ ω)` if `X₀ ω ∉ collisionSet`, else the fixed alcove
   point `ρ_k = k/N` (collisionSet is closed, so `z₀` stays `ℱ₀`-measurable).  `‖z₀‖ ≤ N` since `rep ∈ [0,1)`.
3. `cep_E1_chamber_drift_proof` (`a > 0`): `Ψ ∈ C¹`, `∇Ψ` `L`-Lipschitz, and on every strictly ordered lift the drift is
   `-∇Φ - ∇Ψ`; put `F = -∇Ψ` (Lipschitz).  `cep_E2_moreau_yosida_proof` gives `J` with `cep_Yosida a N J` (Tie repackaging).
4. `cep_E3_regularised_sde_proof` for `B_n = -n(· - J_n ·) + F` (Lipschitz, `n + L`), `n ≥ 1`: `Z n`, adapted to `ℱc`.
5. `cep_E6_limit_solution_proof` (uses E4, E5a, E5b, E5c, hz₀A, hz₀b): `Zl`, continuous, `ℱc`-adapted, in `closure(alcove)`,
   contact set null, `‖∇Φ(Zl)‖` locally integrable, integral equation with the principal force `σ' = √(2 invβ)`.
6. `X t ω = mk ∘ unrank_{π ω} (Zl t ω)`, lift `Y t ω = cep_unrank (π ω) (Zl t ω)`.  Pathwise: on the full-measure set of times
   with `Zl s ∈ alcove` the lift is strictly ordered, so E1 turns the particle drift into `-∇Φ(Zl)-∇Ψ(Zl)` read at the rank
   `π⁻¹ i`; the E6 equation read coordinatewise is exactly the lift equation (integrability from E6 + continuity of `∇Ψ`).
   `ordered`: `Zl ∈ closure(alcove)` is `CyclicallyOrdered`; `occupation`: a collision forces a lattice difference of two
   alcove coordinates, impossible inside the open alcove.  `X 0 = X₀` a.s. since `W' 0 = 0`.
7. Pair forces: `periodicRieszGrad 1 0 (mk y) = ι (cepk1_F (y 0))`, `cepk1_F = cepk1_ρ - π cot(π ·)` (K1, `ρ` continuous), and
   `|π cot π(z_l - z_k)| ≤ C (‖∇Φ‖₁ + 1)` on the alcove (`cep_pair_cot_le`, CepE6Aux1), hence locally integrable.
8. Adaptedness to an arbitrary Brownian filtration `(ℱ, W')`: E3 for `ℱ` gives `Z^{n,ℱ}`; both `Z^n` and `Z^{n,ℱ}` solve the
   same pathwise Lipschitz equation, so they agree a.s. (Gronwall, `eq_zero_of_integral_bound`); completeness of `ℱ` makes `Z^n_t`
   `ℱ_t`-measurable and the hypotheses of E6 hold for `ℱ` with the same sequence.  E6 for `ℱ` gives `Zl^ℱ`; `Zl` and `Zl^ℱ` are both
   limits in measure of `Z^n_t`, hence a.e. equal (`tendstoInMeasure_ae_unique`), so `Zl_t` is `ℱ_t`-measurable.  Then
   `adapted`; `progressive` from continuity (`StronglyAdapted.isStronglyProgressive_of_continuous`).

STATEMENT DEFECT (third conjunct, found while planning; also in the frozen `HRS.cepa_log_flow`): `IsFilteredSolution.progressive`
is `IsProgressive ℱ (ofNNRealTime X)` with `ℱ : Filtration ℝ _`, which contains `Adapted ℱ (ofNNRealTime X)`, in particular
`Measurable[ℱ t] (X 0)` for every NEGATIVE `t`.  The hypothesis `Measurable[ℱ 0] X₀` does not give this: a Brownian filtration
that is the null-set algebra at negative times and `σ(X₀, W_{≤t})` for `t ≥ 0` satisfies all hypotheses, while `X 0 = X₀` a.s.
is not a.e. constant for a nondegenerate initial law.  Minimal repair: hypothesis `∀ t : ℝ, Measurable[ℱ t] X₀` (what
`exists_isBrownianFiltration_of_isVectorBrownian` delivers).  The proof below is carried out under that repair
(`cep_E7_existence_repaired_proof`); everything else is verbatim.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE7

open HRS HRS.MC.Cepa HRS.MC.CepK1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

set_option maxHeartbeats 800000 in
/-- **E7 under the repair `∀ t : ℝ, Measurable[ℱ t] X₀`** (see the statement defect above); otherwise the statement of
`cep_E7_existence`. -/
theorem cep_E7_existence_repaired_proof [IsProbabilityMeasure P]
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    ∃ X : ℝ≥0 → Ω → Config 1 N,
      (∀ T : ℝ, 0 ≤ T → IsCepaLepingleFlow P D T X₀ W X) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j →
        IntegrableOn (fun r : ℝ => periodicRieszGrad 1 D.s
          (X (Real.toNNReal r) ω i - X (Real.toNNReal r) ω j)) (Set.Icc 0 T)) ∧
      (∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ),
        IsBrownianFiltration P ℱ W' → (∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) →
        (∀ t : ℝ, Measurable[ℱ t] X₀) → IsFilteredSolution P ℱ W' W X) := by
  classical
  obtain ⟨W'c, hW'cm, hWae, hBFc, hinitc⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  set ℱc := generatedFiltration P X₀ hX₀ W'c hW'cm with hℱc
  obtain ⟨π0, hπ0m, hπ0⟩ := cepE7_E0 N
  obtain ⟨Ψ, LΨ, hΨ1, hΨL, -, hΨdr, -⟩ := cepE7_E1 hs ha.le hM hV N
  have hE1 : cepE7_E1drift D a N Ψ := hΨdr
  obtain ⟨J, Φn, hJ, -, -, -⟩ := cepE7_E2 a ha N
  set σ' : ℝ := Real.sqrt (2 * D.invβ) with hσ'
  set F : Ch N → Ch N := fun z => -(gradient Ψ z) with hFdef
  have hF : LipschitzWith LΨ F := cepE7_lip_neg hΨL
  have hΨc : Continuous (gradient Ψ) := hΨL.continuous
  set π : Ω → Equiv.Perm (Fin N) := fun ω => π0 (X₀ ω) with hπdef
  set z₀ : Ω → Ch N := fun ω => cepE7_z0 π0 (X₀ ω) with hz₀def
  have hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N := fun ω => cepE7_z0_mem π0 hπ0 (X₀ ω)
  have hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R := ⟨Real.sqrt N, fun ω => cepE7_z0_norm π0 (X₀ ω)⟩
  have hπm : ∀ {m : MeasurableSpace Ω}, Measurable[m] X₀ → ∀ σ, MeasurableSet[m] {ω | π ω = σ} :=
    fun hX σ => hX (hπ0m σ)
  have hz₀m : ∀ {m : MeasurableSpace Ω}, Measurable[m] X₀ → Measurable[m] z₀ :=
    fun hX => (cepE7_z0_meas π0 hπ0m).comp hX
  have hB : ∀ n : ℕ, 1 ≤ n → LipschitzWith (Real.toNNReal n + LΨ)
      (fun z => -((n : ℝ) • (z - J n z)) + F z) := fun n hn =>
    (cepE7_lip_neg (hJ.lip (n : ℝ) (Nat.cast_pos.mpr (by omega)))).add hF
  have hex : ∀ n : ℕ, 1 ≤ n → ∃ Zn : ℝ → Ω → Ch N, cep_IsChamberSolution P ℱc W'c π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ Zn := fun n hn =>
    cepE7_E3 hBFc (hπm (hinitc 0)) (hB n hn) σ' (hz₀m (hinitc 0))
  choose Zs hZs using hex
  set Z : ℕ → ℝ → Ω → Ch N := fun n => if h : 1 ≤ n then Zs n h else Zs 1 le_rfl with hZdef
  have hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱc W'c π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n) := by
    intro n hn
    simp only [hZdef, dif_pos hn]
    exact hZs n hn
  have hZc : ∀ n ω, Continuous fun t => Z n t ω := by
    intro n ω
    by_cases hn : 1 ≤ n
    · exact (hZ n hn).1 ω
    · simp only [hZdef, dif_neg hn]
      exact (hZs 1 le_rfl).1 ω
  obtain ⟨Zl, hZlc, hZlm, hZlconv, hZlcl, hZlnull, hZlint, hZleq⟩ :=
    cepE7_E6 hBFc (hπm (hinitc 0)) ha hJ hF σ' (hz₀m (hinitc 0)) hz₀A hz₀b hZ
  set Y : ℝ≥0 → Ω → Fin N → Euc 1 := fun t ω => cep_unrank (π ω) (Zl (t : ℝ) ω) with hYdef
  have hAE : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ T : ℝ, volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Icc 0 T)) ∧
      (∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
        (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (Zl s ω)) + -(gradient Ψ (Zl s ω)))) +
          σ' • cep_noise π W'c t ω) ∧
      (∀ t i j, W'c t ω (i, j) = W t ω i j) ∧ X₀ ω ∉ collisionSet 1 N := by
    filter_upwards [hZlcl, hZlnull, hZlint, hZleq, hWae, hdist] with ω h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hproj : ∀ ω, ∀ s : ℝ, 0 ≤ s → projectPath Y (Real.toNNReal s) ω =
      fun j => Torus.mk (cep_unrank (π ω) (Zl s ω) j) := by
    intro ω s hs0
    funext j
    simp only [projectPath, hYdef, Real.coe_toNNReal s hs0]
  have hinit : ∀ᵐ ω ∂P, projectPath Y 0 ω = X₀ ω := by
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hcoll⟩
    have h0 := heq 0 le_rfl
    have hnz : cep_noise π W'c 0 ω = 0 := by
      ext k
      simp [cep_noise, hBFc.zero ω]
    simp only [intervalIntegral.integral_same, add_zero, hnz, smul_zero] at h0
    funext i
    show Torus.mk (cep_unrank (π ω) (Zl ((0 : ℝ≥0) : ℝ) ω) i) = X₀ ω i
    rw [NNReal.coe_zero, h0]
    have hz : z₀ ω = cep_toCh (π ω) (fun i => Torus.rep (X₀ ω i)) := by
      simp only [hz₀def, cepE7_z0, if_neg hcoll]
      rfl
    rw [hz, cepE7_unrank_apply]
    have : cepk1_ι ((cep_toCh (π ω) fun i => Torus.rep (X₀ ω i)) ((π ω).symm i)) =
        Torus.rep (X₀ ω i) := by
      ext c
      have hc : c = 0 := Subsingleton.elim _ _
      subst hc
      simp [cep_toCh, cep_rank, cepk1_ι]
    rw [this, Torus.mk_rep]
  have hadX : ∀ {m : MeasurableSpace Ω} (t : ℝ≥0), Measurable[m] X₀ →
      Measurable[m] (Zl (t : ℝ)) → Measurable[m] (projectPath Y t) :=
    fun t hX hz => cepE7_X_measurable (hπm hX) hz
  refine ⟨projectPath Y, ?_, ?_, ?_⟩
  · intro T hT
    have hlift : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
        (∀ i, IntegrableOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
          (Icc 0 (t : ℝ))) ∧
        ∀ i, Y t ω i = Y 0 ω i +
          (∫ s in Icc (0 : ℝ) t, particleDrift D (projectPath Y (Real.toNNReal s) ω) i) +
            Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i) := by
      filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hcoll⟩ t _
      have hEqOn : ∀ i, EqOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
          (fun s : ℝ => particleDrift D (fun j => Torus.mk (cep_unrank (π ω) (Zl s ω) j)) i)
          (Icc 0 (t : ℝ)) := by
        intro i s hs0
        simp only [hproj ω s hs0.1]
      have hP := fun i => cepE7_lift_path hE1 hΨc (hZlc ω) (π ω) (z₀ ω)
        (fun t => cep_noise π W'c t ω) σ' heq hint hnull (t.2 : (0 : ℝ) ≤ t) i
      refine ⟨fun i => ((hP i).1).congr_fun (fun s hs0 => (hEqOn i hs0).symm) measurableSet_Icc, fun i => ?_⟩
      rw [setIntegral_congr_fun measurableSet_Icc (hEqOn i)]
      have hn : ∀ s : ℝ≥0, cep_noise π W'c (s : ℝ) ω ((π ω).symm i) = W s ω i 0 := by
        intro s
        simp only [cep_noise, Real.toNNReal_coe, Equiv.apply_symm_apply]
        exact hWW s i 0
      have hn0 : cep_noise π W'c 0 ω ((π ω).symm i) = W 0 ω i 0 := by
        simpa using hn 0
      have hE := (hP i).2
      have hnt := hn t
      erw [hnt] at hE
      rw [hn0] at hE
      show cep_unrank (π ω) (Zl (t : ℝ) ω) i = cep_unrank (π ω) (Zl ((0 : ℝ≥0) : ℝ) ω) i + _ + _
      rw [NNReal.coe_zero]
      refine hE.trans ?_
      congr 1
      ext c
      have hc : c = 0 := Subsingleton.elim _ _
      subst hc
      simp [cepk1_ι]
      left
      rw [hσ']
      exact Real.sqrt_mul (by norm_num) _
    have hord : ∀ᵐ ω ∂P, ∃ Y' : ℝ≥0 → Fin N → Euc 1,
        (∀ t : ℝ≥0, (t : ℝ) ≤ T → projectPath Y t ω = fun i => Torus.mk (Y' t i)) ∧ Continuous Y' ∧
        ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered (π ω) (Y' t) := by
      filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hcoll⟩
      refine ⟨fun t => cep_unrank (π ω) (Zl (t : ℝ) ω), fun t _ => rfl, ?_, fun t _ => ?_⟩
      · exact continuous_pi fun i => cepk1_contDiff_ι.continuous.comp
          ((EuclideanSpace.proj ((π ω).symm i)).continuous.comp ((hZlc ω).comp NNReal.continuous_coe))
      · exact cepE7_unrank_cyc (hcl t t.2) (π ω)
    have hocc : ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Icc 0 T ∧
        projectPath Y (Real.toNNReal s) ω ∈ collisionSet 1 N} = 0 := by
      filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hcoll⟩
      refine measure_mono_null (fun s hs => ?_) (hnull T)
      refine ⟨hs.1, fun hz => ?_⟩
      have := hs.2
      rw [hproj ω s hs.1.1] at this
      exact cepE7_not_collision hz (π ω) this
    refine ⟨⟨⟨Y, ?_, rfl⟩, hinit, ?_, ?_⟩, ⟨π, hπm hX₀, hord⟩, hocc⟩
    · filter_upwards [hlift] with ω h t ht
      exact h t ht
    · exact Filter.Eventually.of_forall fun ω i =>
        (continuous_apply i).comp (cepE7_X_continuous (π ω) (hZlc ω))
    · intro t
      exact hadX t hX₀ ((hZlm t t.2).mono (ℱc.le _) le_rfl)
  · intro T hT
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hcoll⟩ i j hij
    have h := cepE7_pair_integrable hs ha (hZlc ω) (hint T) (cepE7_hal (hnull T)) (π ω) hij
    refine h.congr_fun (fun r hr => ?_) measurableSet_Icc
    simp only [hproj ω r hr.1]
  · intro ℱ W' hBF hWW' hXm
    have hX0m : Measurable[ℱ 0] X₀ := hXm 0
    have hπℱ := hπm hX0m
    have hz₀ℱ := hz₀m hX0m
    have hWWc : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W'c t ω (i, j) := by
      filter_upwards [hWW', hWae] with ω h1 h2 t i j
      rw [h1 t i j, h2 t i j]
    have hZℱ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
        (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n) :=
      fun n hn => cepE7_transfer hBFc hBF hWWc hπℱ (hB n hn) σ' hz₀ℱ (hZ n hn)
    obtain ⟨Zl', hZlc', hZlm', hZlconv', -, -, -, -⟩ :=
      cepE7_E6 hBF hπℱ ha hJ hF σ' hz₀ℱ hz₀A hz₀b hZℱ
    have hZlℱ : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ t] (Zl t) :=
      cepE7_Zl_measurable hBF.complete hZc hZlc hZlc' hZlm hZlm' hZlconv hZlconv'
    have hXt : ∀ s : ℝ≥0, Measurable[ℱ s] (projectPath Y s) := fun s =>
      hadX s (hXm s) (hZlℱ s s.2)
    have hXad : ∀ t : ℝ, Measurable[ℱ t] (ofNNRealTime (projectPath Y) t) := by
      intro t
      rcases le_or_gt 0 t with ht | ht
      · have h := hXt (Real.toNNReal t)
        rw [Real.coe_toNNReal t ht] at h
        exact h
      · have h0 : Real.toNNReal t = 0 := Real.toNNReal_of_nonpos ht.le
        show Measurable[ℱ t] (projectPath Y (Real.toNNReal t))
        rw [h0]
        refine hBF.complete.measurable_of_ae_eq t (hXm t) ?_ (hinit.mono fun ω h => h.symm)
        exact hadX 0 hX₀ ((hZlm _ (NNReal.coe_nonneg 0)).mono (ℱc.le _) le_rfl)
    have hXc : ∀ ω, Continuous fun t : ℝ => ofNNRealTime (projectPath Y) t ω := fun ω =>
      (cepE7_X_continuous (π ω) (hZlc ω)).comp continuous_real_toNNReal
    exact ⟨hBF, hWW', hXt, (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hXad t).stronglyMeasurable) hXc).isProgressive⟩

end HRS.MC.CepE7
