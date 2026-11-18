import HRS.MC.CepE6E10

/-!
# Packet CEPE6E, file 11: the singular part vanishes at a fixed time (probabilistic assembly)

For fixed `T ≥ 0`: a.s. `A(T) = ∫_0^T ∇Φ(Zl)` where `A(T) = z₀ + ∫_0^T F(Zl) + σ' N_T - Zl_T`.

Route: a.s. subsequence `m` with `Z^{m i} → Zl` uniformly on `[0,T]`; near-contact levels `ε_k ↓ 0`;
Itô martingales `M k i` for `g_{ε_k}(Z^{m i})`; `Y k i = 4^{-k} V_i + M_{k,i}²` with Fatou/Markov/Borel–Cantelli
selection of subsequences with `V ≲ 2^k`, `|M| ≲ 2^{-k/2}`; deterministic glue.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE5b HRS.MC.CepE6D HRS.MC.CepE6A

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepe6e_R_zero [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N} (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlm : ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t))
    (hprob : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hcl : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hgi : ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn
      (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T))
    (hinv : ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ∑ k : Fin N, ∑ l : Fin N,
      (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else 0)) (Set.Icc 0 T))
    (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, z₀ ω + (∫ s in (0 : ℝ)..T, F (Zl s ω)) + σ' • cep_noise π W' T ω - Zl T ω =
      ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s ω) := by
  classical
  -- Step 1: a.s. uniformly convergent subsequence
  obtain ⟨m, hm, hm1, hunif⟩ := cepe6e_subseq (Zn := fun n => Z (n + 1)) (Zl := Zl) (T := T)
    (fun n ω => (hZ (n + 1) (by omega)).1 ω) hZlc
    (fun ε hε => (hprob T ε hε).comp (tendsto_add_atTop_nat 1))
  set nnN : ℕ → ℕ := fun i => m i + 1 with hnnN
  have hnn1 : ∀ i, 1 ≤ nnN i := fun i => by simp [hnnN]
  have hnntop : Tendsto nnN atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ _) hm.tendsto_atTop
  have hposi : ∀ i, (0 : ℝ) < ((nnN i : ℕ) : ℝ) := fun i => Nat.cast_pos.2 (hnn1 i)
  -- joint measurability
  have hZlj : Measurable fun p : Ω × ℝ => Zl (max p.2 0) p.1 :=
    (e6a_joint hZlc hZlm).comp measurable_swap
  have hZsj : ∀ i, Measurable fun p : Ω × ℝ => Z (nnN i) (max p.2 0) p.1 := fun i =>
    (e6a_joint (hZ _ (hnn1 i)).1 (hZ _ (hnn1 i)).2.1).comp measurable_swap
  -- the E4 constant
  obtain ⟨C, hC⟩ := e6a_E4_lint hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ T hT
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  -- near-contact levels
  set σc : ℝ := σ' ^ 2 * (N : ℝ) ^ 4 with hσc
  have hσc0 : 0 ≤ σc := by positivity
  set η : ℕ → ℝ := fun k => (1 / 4) ^ k / (1 + σc) with hη
  have hη0 : ∀ k, 0 < η k := fun k => by simp only [hη]; positivity
  obtain ⟨ε, hε01, hεlim, hεH⟩ := cepe6e_near_choose hT hZlc hZlj (hnull.mono fun ω h => h T) hη0
  have hε0 : ∀ k, 0 < ε k := fun k => (hε01 k).1
  have hε1 : ∀ k, ε k ≤ 1 / 8 := fun k => (hε01 k).2
  -- the Itô martingales
  choose M hM2 hMeq hMiso using fun (k i : ℕ) =>
    cepe6e_ito_gg hW' hπ hJ hF σ' hz₀ hz₀b hZ (n := nnN i) (hnn1 i) hT (hε0 k) (hε1 k)
  -- total variation of the force
  set V : ℕ → Ω → ℝ≥0∞ := fun i ω => ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal
    (∑ k : Fin N, |(((nnN i : ℕ) : ℝ) • (Z (nnN i) s ω - J (nnN i) (Z (nnN i) s ω))) k|) with hV
  have hGc : ∀ i, Continuous fun x : Ch N => (((nnN i : ℕ) : ℝ) • (x - J (nnN i) x)) :=
    fun i => (hJ.lip _ (hposi i)).continuous
  have hVm : ∀ i, Measurable (V i) := fun i =>
    cepe6e_meas_lint (Y := fun s ω => Z (nnN i) s ω) (hZsj i)
      (G := fun x => ENNReal.ofReal (∑ k : Fin N, |(((nnN i : ℕ) : ℝ) • (x - J (nnN i) x)) k|))
      (ENNReal.measurable_ofReal.comp (continuous_finset_sum _ fun k _ =>
        (continuous_abs.comp ((EuclideanSpace.proj k).continuous.comp (hGc i)))).measurable) T
  have hVint : ∀ i, ∫⁻ ω, V i ω ∂P ≤ ENNReal.ofReal C' := fun i =>
    (hC (nnN i) (hnn1 i)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the weighted sums
  set Y : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ENNReal.ofReal ((1 / 4) ^ k) * V i ω + ‖M k i ω‖ₑ ^ 2 with hY
  have hYm : ∀ k i, AEMeasurable (Y k i) P := fun k i =>
    ((hVm i).const_mul _).aemeasurable.add ((hM2 k i).aestronglyMeasurable.enorm.pow_const 2)
  have hint' : ∀ k, liminf (fun i => ∫⁻ ω, Y k i ω ∂P) atTop ≤
      ENNReal.ofReal ((C' + 1) * (1 / 4) ^ k) := by
    intro k
    set X : ℕ → ℝ≥0∞ := fun i => ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (‖vv (ε k) (Z (nnN i) s ω)‖ ^ 2)) ∂P with hX
    have hXlim : limsup X atTop ≤ ENNReal.ofReal ((N : ℝ) ^ 4) * ENNReal.ofReal (η k) := by
      refine (cepe6e_limsup_near (Zs := fun i => Z (nnN i)) hT hZsj hunif (hε0 k)).trans ?_
      gcongr
      exact hεH k
    have hu : ∀ i, ∫⁻ ω, Y k i ω ∂P ≤
        ENNReal.ofReal ((1 / 4) ^ k) * ENNReal.ofReal C' + ENNReal.ofReal (σ' ^ 2) * X i := by
      intro i
      have e1 : ∫⁻ ω, Y k i ω ∂P = ENNReal.ofReal ((1 / 4) ^ k) * ∫⁻ ω, V i ω ∂P +
          ∫⁻ ω, ‖M k i ω‖ₑ ^ 2 ∂P := by
        simp only [hY]
        rw [lintegral_add_left ((hVm i).const_mul _), lintegral_const_mul _ (hVm i)]
      have e2 : ∫⁻ ω, ‖M k i ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (σ' ^ 2) * X i := by
        rw [hMiso k i]
        simp only [hX]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_mul (sq_nonneg σ')]
      rw [e1, e2]
      gcongr
      exact hVint i
    refine (cepe6e_liminf_bound (ENNReal.ofReal_ne_top) hXlim hu).trans ?_
    have h4 : (0 : ℝ) ≤ (1 / 4) ^ k := by positivity
    have hNn : (0 : ℝ) ≤ (N : ℝ) ^ 4 := by positivity
    have hs2 : (0 : ℝ) ≤ σ' ^ 2 := sq_nonneg _
    have hkey : ENNReal.ofReal ((1 / 4) ^ k) * ENNReal.ofReal C' +
        ENNReal.ofReal (σ' ^ 2) * (ENNReal.ofReal ((N : ℝ) ^ 4) * ENNReal.ofReal (η k)) =
        ENNReal.ofReal ((1 / 4) ^ k * C' + σ' ^ 2 * ((N : ℝ) ^ 4 * η k)) := by
      rw [← ENNReal.ofReal_mul hNn, ← ENNReal.ofReal_mul hs2, ← ENNReal.ofReal_mul h4,
        ← ENNReal.ofReal_add (mul_nonneg h4 hC'0) (mul_nonneg hs2 (mul_nonneg hNn (hη0 k).le))]
    rw [hkey]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : σc * η k ≤ (1 / 4) ^ k := by
      have hp : 0 < 1 + σc := by linarith
      simp only [hη]
      rw [← mul_div_assoc, div_le_iff₀ hp]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) k]
    have h2 : σ' ^ 2 * ((N : ℝ) ^ 4 * η k) = σc * η k := by simp only [hσc]; ring
    rw [h2]
    nlinarith
  have hsel := cepe6e_select hYm (c := C' + 1) (by linarith) hint'
  -- a.s. facts
  have hsolall : ∀ᵐ ω ∂P, ∀ i, ∀ t : ℝ, 0 ≤ t → Z (nnN i) t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-(bF J (fun i => ((nnN i : ℕ) : ℝ)) (fun i t => Z (nnN i) t ω) i s) +
        F (Z (nnN i) s ω))) + σ' • cep_noise π W' t ω := by
    rw [ae_all_iff]; intro i; exact (hZ (nnN i) (hnn1 i)).2.2
  have hIall : ∀ᵐ ω ∂P, ∀ k i, ∫ s in (0 : ℝ)..T, ⟪vv (ε k) (Z (nnN i) s ω),
      bF J (fun i => ((nnN i : ℕ) : ℝ)) (fun i t => Z (nnN i) t ω) i s⟫ =
      gg (ε k) (z₀ ω) - gg (ε k) (Z (nnN i) T ω) +
        (∫ s in (0 : ℝ)..T, ⟪vv (ε k) (Z (nnN i) s ω), F (Z (nnN i) s ω)⟫) +
        σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 (ε k) (Z (nnN i) s ω)) + M k i ω := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro i; exact hMeq k i
  have hBlim : Tendsto (fun k : ℕ => Real.sqrt (2 * (1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
    have h' := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at h'
    exact h'
  filter_upwards [hunif, hsel, hcl, hnull, hgi, hinv, hsolall, hIall] with ω hu hs hc hn hg hv hsol hI
  have Dω : Det a J T (fun i => ((nnN i : ℕ) : ℝ)) (fun i t => Z (nnN i) t ω) (fun t => Zl t ω) :=
    ⟨ha, hJ, hT, hposi, tendsto_natCast_atTop_atTop.comp hnntop,
      fun i => (hZ _ (hnn1 i)).1 ω, hZlc ω, fun s hs => hc s hs.1, hn T, hg T, hu⟩
  have hA := cepe6e_hA (nn := fun i => ((nnN i : ℕ) : ℝ)) (Zs := fun i t => Z (nnN i) t ω)
    (Zl := fun t => Zl t ω) hT (fun i => (hZ _ (hnn1 i)).1 ω) (hZlc ω) hJ hposi hF
    (z0 := z₀ ω) (nz := fun t => cep_noise π W' t ω) (σ' := σ') hsol hu
  have hselω : ∀ᶠ k in atTop, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
      (∫ s in (0 : ℝ)..T, ‖bF J (fun i => ((nnN i : ℕ) : ℝ)) (fun i t => Z (nnN i) t ω) (φ j) s‖ ≤
        2 * 2 ^ k) ∧ |M k (φ j) ω| ≤ Real.sqrt (2 * (1 / 2 : ℝ) ^ k) := by
    filter_upwards [hs] with k hk
    obtain ⟨φ, hφ, hφY⟩ := hk
    refine ⟨φ, hφ, fun j => ⟨?_, ?_⟩⟩
    · have hy : ENNReal.ofReal ((1 / 4) ^ k) * V (φ j) ω + ‖M k (φ j) ω‖ₑ ^ 2 <
          ENNReal.ofReal (2 * (1 / 2) ^ k) := hφY j
      have h1 : ENNReal.ofReal ((1 / 4) ^ k) * V (φ j) ω ≤ ENNReal.ofReal (2 * (1 / 2) ^ k) :=
        le_trans le_self_add hy.le
      have hpow : ((1 : ℝ) / 4) ^ k * 2 ^ k = (1 / 2) ^ k := by
        rw [← mul_pow]; norm_num
      have h2 : V (φ j) ω ≤ ENNReal.ofReal (2 * 2 ^ k) :=
        cepe6e_ennreal_div (c := (1 / 4) ^ k) (by positivity) (by positivity)
          (by calc (1 / 4 : ℝ) ^ k * (2 * 2 ^ k) = 2 * ((1 / 4) ^ k * 2 ^ k) := by ring
                _ = 2 * (1 / 2) ^ k := by rw [hpow]) h1
      have hbc : Continuous (bF J (fun i => ((nnN i : ℕ) : ℝ)) (fun i t => Z (nnN i) t ω) (φ j)) :=
        (hJ.lip _ (hposi (φ j))).continuous.comp ((hZ _ (hnn1 _)).1 ω)
      have h3 := cepe6e_normint_le hbc hT
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h3.trans h2)
    · have hy : ENNReal.ofReal ((1 / 4) ^ k) * V (φ j) ω + ‖M k (φ j) ω‖ₑ ^ 2 <
          ENNReal.ofReal (2 * (1 / 2) ^ k) := hφY j
      exact cepe6e_enorm_sq_le (by positivity) (le_add_self.trans_lt hy)
  exact cepe6e_glue Dω hN hA (hz₀A ω) hF.continuous (hv T) hε0 hε1 hεlim (M := fun k i => M k i ω) hI
    (K := fun k => 2 * 2 ^ k) (B := fun k => Real.sqrt (2 * (1 / 2 : ℝ) ^ k)) hBlim hselω

end HRS.MC.CepE6E
