import HRS.MS.R2WinErrAux13

/-!
# S10.4 packet E3c: part (b) of `r2_window_errors` as a conditional statement

`s104_partB`: the forcing remainder `D_b(u)_α = -(√N/2) ∫_0^{b+u} r2CommForcingMov(α, b+u, r) dr` satisfies
`E sup_{u≤T} ‖D_b(u)‖_{ℓ²} ≤ C_c Cs (√N/2) δ_N (1/c + T + T/c) Σ_α b_α` under
* the orbit bounds of S10.3 (`R2OrbitGrad` for `φ_α` and `L_tφ_α`, amplitude `Cs b_α`, rate `c`, order `k ≥ 1`),
* the entropy bound `H(P∘X_r^{-1} | Q_{N,β}(μ^r)) ≤ H₀ N δ_N` (first clause of `MovParticleBounds`) and a uniform density bound for `μ^r`,
* the integrated evolution inequality `|Fm(t,r)| ≤ |Fm(t₀,r)| + ∫_{(t₀,t]} |F2(s,r)| ds` (`∂_tU(r,t)φ = U(r,t)L_tφ` for the pair functional),
* joint a.e.-measurability of the three families in `(ζ, r)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal

namespace HRS.MS.R2WinErr

open HRS.Whole

variable {d : ℕ}

lemma s104_ae_slice {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    {P : Measure Ω} {μ : Measure β} [SFinite P] [SFinite μ] {f : Ω × β → γ}
    (hf : AEMeasurable f (P.prod μ)) : ∀ᵐ ζ ∂P, AEMeasurable (fun r => f (ζ, r)) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  filter_upwards [Measure.ae_ae_of_ae_prod hfg] with ζ hζ
  exact ⟨fun r => g (ζ, r), hg.comp measurable_prodMk_left, hζ⟩

/-- The time derivative of the forcing family: `F2(s,r) = D_{μ^r}(h_{U(r,s)L_sφ_α})(X_r)` for `r ≤ s`, `0` otherwise. -/
def s104_F2 {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (s m : ℝ) (ρ : ℝ → Euc d → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (α : MultiIndex d) (p : ℝ × ℝ) (ζ : Ω) : ℝ :=
  open Classical in
  if p.2 ≤ p.1 then centeredPairFunctional
    (commutatorKernel d s (fun x => gradient (propagatorW C p.2 p.1 (generatorW C p.1 (oscTestFun m α))) x))
    (X p.2.toNNReal ζ) (HRS.Whole.withDensityReal (ρ p.2)) else 0

theorem s104_partB_core {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : WholeCoeff d) (ρ : ℝ → Euc d → ℝ) (m T b cdec Cs κ0 : ℝ) (k : ℕ) (hc : 0 < cdec) (hCs : 0 ≤ Cs)
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hκ0 : 0 ≤ κ0) (bα : MultiIndex d → ℝ) (hb0 : ∀ α, 0 ≤ bα α)
    (hbS : Summable bα)
    (hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * bα α) cdec)
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * bα α) cdec)
    (N : ℕ) (s : ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hexp : ∀ (t : ℝ) (ψ : Euc d → ℝ) (A : ℝ), 0 ≤ A → R2OrbitGrad C k t ψ A cdec →
      ∀ r ∈ Set.Icc (0 : ℝ) (b + T), r ∈ Set.Icc (0 : ℝ) t →
      ∫⁻ ζ, ENNReal.ofReal |centeredPairFunctional
        (commutatorKernel d s (fun x => gradient (propagatorW C r t ψ) x)) (X r.toNNReal ζ)
        (HRS.Whole.withDensityReal (ρ r))| ∂P ≤
        ENNReal.ofReal (κ0 * (A * Real.exp (-cdec * (t - r)))))
    (hevol : ∀ ζ : Ω, ∀ α : MultiIndex d, ∀ r t0 t : ℝ, 0 ≤ r → r ≤ t0 → t0 ≤ t → t ≤ b + T →
        ENNReal.ofReal |r2CommForcingMov C s m ρ X α t r ζ| ≤
          ENNReal.ofReal |r2CommForcingMov C s m ρ X α t0 r ζ| +
            ∫⁻ s' in Set.Ioc t0 t, ENNReal.ofReal |s104_F2 C s m ρ X α (s', r) ζ|)
    (M0 : ∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α b p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) b))))
    (M1 : ∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α p.2 p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc b (b + T)))))
    (M2 : ∀ α, AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2 C s m ρ X α p.2 p.1|)
        (P.prod (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)))))) :
    ∫⁻ ζ, (⨆ u ∈ Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
            r2CommForcingMov C s m ρ X α (b + u) r ζ)) ∂P ≤
        ENNReal.ofReal ((Real.sqrt N / 2) * (κ0 * Cs) *
          (1 / cdec + T + T * (1 / cdec)) * ∑' α, bα α) := by
  have hκ : 0 ≤ κ0 * Cs := by positivity
  have hw : ∀ α, 0 ≤ bα α := hb0
  have hcoef : 0 ≤ Real.sqrt N / 2 := by positivity
  have hAα : ∀ α, 0 ≤ Cs * bα α := fun α => mul_nonneg hCs (hb0 α)
  -- the three expectation bounds
  have E0 : ∀ α, ∀ r ∈ Set.Icc (0 : ℝ) b, ∫⁻ ζ, ENNReal.ofReal |r2CommForcingMov C s m ρ X α b r ζ| ∂P ≤
      ENNReal.ofReal ((κ0 * Cs) * bα α * Real.exp (-cdec * (b - r))) := by
    intro α r hr
    refine (hexp b (oscTestFun m α) (Cs * bα α) (hAα α) (hG α b hb) r ⟨hr.1, hr.2.trans (by linarith)⟩
      ⟨hr.1, hr.2⟩).trans (le_of_eq ?_)
    congr 1; ring
  have E1 : ∀ α, ∀ r ∈ Set.Icc b (b + T), ∫⁻ ζ, ENNReal.ofReal |r2CommForcingMov C s m ρ X α r r ζ| ∂P ≤
      ENNReal.ofReal ((κ0 * Cs) * bα α) := by
    intro α r hr
    refine (hexp r (oscTestFun m α) (Cs * bα α) (hAα α) (hG α r (hb.trans hr.1)) r
      ⟨hb.trans hr.1, hr.2⟩ ⟨hb.trans hr.1, le_rfl⟩).trans (le_of_eq ?_)
    congr 1; simp; ring
  have E2 : ∀ α, ∀ p ∈ (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)),
      ∫⁻ ζ, ENNReal.ofReal |s104_F2 C s m ρ X α p ζ| ∂P ≤
        ENNReal.ofReal ((κ0 * Cs) * bα α * s104_psi cdec p) := by
    intro α p hp
    by_cases hle : p.2 ≤ p.1
    · have := hexp p.1 (generatorW C p.1 (oscTestFun m α)) (Cs * bα α) (hAα α)
        (hG' α p.1 (hb.trans hp.1.1)) p.2 hp.2 ⟨hp.2.1, hle⟩
      have e2 : ∀ ζ, s104_F2 C s m ρ X α p ζ = centeredPairFunctional
          (commutatorKernel d s (fun x => gradient (propagatorW C p.2 p.1
            (generatorW C p.1 (oscTestFun m α))) x)) (X p.2.toNNReal ζ)
          (HRS.Whole.withDensityReal (ρ p.2)) := fun ζ => by
        unfold s104_F2; rw [if_pos hle]
      have key : ∫⁻ ζ, ENNReal.ofReal |s104_F2 C s m ρ X α p ζ| ∂P = ∫⁻ ζ, ENNReal.ofReal |centeredPairFunctional
          (commutatorKernel d s (fun x => gradient (propagatorW C p.2 p.1
            (generatorW C p.1 (oscTestFun m α))) x)) (X p.2.toNNReal ζ)
          (HRS.Whole.withDensityReal (ρ p.2))| ∂P := lintegral_congr fun ζ => by rw [e2]
      rw [key]
      refine this.trans (le_of_eq ?_)
      have e : s104_psi cdec p = Real.exp (-cdec * (p.1 - p.2)) := by
        unfold s104_psi; rw [if_pos hle]
      rw [e]; congr 1; ring
    · have h0 : ∀ ζ, s104_F2 C s m ρ X α p ζ = 0 := fun ζ => by
        unfold s104_F2; rw [if_neg hle]
      simp [h0]
  -- the pathwise Duhamel bound
  have hslice0 := fun α => s104_ae_slice (M0 α)
  have hslice1 := fun α => s104_ae_slice (M1 α)
  have hslice2 := fun α => s104_ae_slice (M2 α)
  have hall : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d,
      AEMeasurable (fun r => ENNReal.ofReal |r2CommForcingMov C s m ρ X α b r ζ|)
        (volume.restrict (Set.Icc (0 : ℝ) b)) ∧
      AEMeasurable (fun r => ENNReal.ofReal |r2CommForcingMov C s m ρ X α r r ζ|)
        (volume.restrict (Set.Icc b (b + T))) ∧
      AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal |s104_F2 C s m ρ X α q ζ|)
        (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)))) := by
    rw [ae_all_iff]
    intro α
    filter_upwards [hslice0 α, hslice1 α, hslice2 α] with ζ h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hH' : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal |-(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
          r2CommForcingMov C s m ρ X α (b + u) r ζ| ≤ ENNReal.ofReal (Real.sqrt N / 2) *
        ((∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |r2CommForcingMov C s m ρ X α b r ζ|) +
          (∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal |r2CommForcingMov C s m ρ X α r r ζ|) +
          (∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)),
            ENNReal.ofReal |s104_F2 C s m ρ X α p ζ|)) := by
    filter_upwards [hall] with ζ hζ α u hu
    obtain ⟨h0, h1, h2⟩ := hζ α
    have hd := s104_duhamel_path hb hT (fun t r => r2CommForcingMov C s m ρ X α t r ζ)
      (fun p => s104_F2 C s m ρ X α p ζ) (fun r t0 t hr0 hrt0 ht0t htT => hevol ζ α r t0 t hr0 hrt0 ht0t htT)
      h0 h1 h2 hu
    rw [abs_mul, abs_neg, abs_of_nonneg hcoef, ENNReal.ofReal_mul hcoef]
    exact mul_le_mul' le_rfl hd
  have hcore := s104_part_b_core P (ι := MultiIndex d) (b := b) (T := T) (c := cdec)
    (κ := κ0 * Cs) (coef := Real.sqrt N / 2) hc hb hT hκ hcoef bα hb0 hbS
    (fun α u ζ => -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
      r2CommForcingMov C s m ρ X α (b + u) r ζ)
    (fun α r ζ => r2CommForcingMov C s m ρ X α b r ζ)
    (fun α r ζ => r2CommForcingMov C s m ρ X α r r ζ)
    (fun α p ζ => s104_F2 C s m ρ X α p ζ) hH' M0 M1 M2 E0 E1 E2
  exact hcore


theorem s104_partB (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) (H₀ : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (C : WholeCoeff d) (ρ : ℝ → Euc d → ℝ) (m T b cdec Cs : ℝ) (k : ℕ), 1 ≤ k →
      0 < cdec → 0 ≤ Cs → 0 ≤ T → 0 ≤ b → ∀ bα : MultiIndex d → ℝ, (∀ α, 0 ≤ bα α) → Summable bα →
      (∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * bα α) cdec) →
      (∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * bα α) cdec) →
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ M) ∧
        (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ r)) L)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), Measurable (X r.toNNReal)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.relEntropy (P.map (X r.toNNReal))
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ r))) ≤
          ENNReal.ofReal (H₀ * N * deltaN d s N)) →
      (∀ ζ : Ω, ∀ α : MultiIndex d, ∀ r t0 t : ℝ, 0 ≤ r → r ≤ t0 → t0 ≤ t → t ≤ b + T →
        ENNReal.ofReal |r2CommForcingMov C s m ρ X α t r ζ| ≤
          ENNReal.ofReal |r2CommForcingMov C s m ρ X α t0 r ζ| +
            ∫⁻ s' in Set.Ioc t0 t, ENNReal.ofReal |s104_F2 C s m ρ X α (s', r) ζ|) →
      (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α b p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) b)))) →
      (∀ α, AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov C s m ρ X α p.2 p.2 p.1|)
        (P.prod (volume.restrict (Set.Icc b (b + T))))) →
      (∀ α, AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2 C s m ρ X α p.2 p.1|)
        (P.prod (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)))))) →
      ∫⁻ ζ, (⨆ u ∈ Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + u),
            r2CommForcingMov C s m ρ X α (b + u) r ζ)) ∂P ≤
        ENNReal.ofReal ((Real.sqrt N / 2) * (Cc * Cs * deltaN d s N) *
          (1 / cdec + T + T * (1 / cdec)) * ∑' α, bα α) := by
  obtain ⟨Cc, hCc0, hCc⟩ := s104_forcing_expect hd s hs0 hsd M L β hβ H₀
  refine ⟨Cc, hCc0, fun C ρ m T b cdec Cs k hk hc hCs hT hb bα hb0 hbS hG hG' N hN Ω _ P _ X
    hρ hXm hH hevol M0 M1 M2 => ?_⟩
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  -- the generic expectation bound
  have hexp : ∀ (t : ℝ) (ψ : Euc d → ℝ) (A : ℝ), 0 ≤ A → R2OrbitGrad C k t ψ A cdec →
      ∀ r ∈ Set.Icc (0 : ℝ) (b + T), r ∈ Set.Icc (0 : ℝ) t →
      ∫⁻ ζ, ENNReal.ofReal |centeredPairFunctional
        (commutatorKernel d s (fun x => gradient (propagatorW C r t ψ) x)) (X r.toNNReal ζ)
        (HRS.Whole.withDensityReal (ρ r))| ∂P ≤
        ENNReal.ofReal (Cc * (A * Real.exp (-cdec * (t - r))) * deltaN d s N) := by
    intro t ψ A hA hR r hr hrt
    obtain ⟨hprob, hM, hlog⟩ := hρ r hr
    exact hCc (ρ r) hprob hM hlog N hN P (X r.toNNReal) (hXm r hr) (hH r hr) _ _
      (s104_grad_lip C hk hA hR hrt)
  have hκ0 : 0 ≤ Cc * deltaN d s N := by positivity
  refine (s104_partB_core P C ρ m T b cdec Cs (Cc * deltaN d s N) k hc hCs hT hb hκ0 bα hb0 hbS hG hG' N s X
    ?_ hevol M0 M1 M2).trans (le_of_eq ?_)
  · intro t ψ A hA hR r hr hrt
    exact (hexp t ψ A hA hR r hr hrt).trans (le_of_eq (by congr 1; ring))
  · congr 1; ring

end HRS.MS.R2WinErr
