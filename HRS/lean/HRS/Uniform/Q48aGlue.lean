import HRS.Uniform.Q48aAux6

/-!
# Q48a: the infinite-horizon adapted coupling (infrastructure for Lemma 3.31 `stationary_noise`)

**Statement proved** (`HRS.Uniform.Q48a.relative_covariance_coupling_top`):
for `M`, `Sg` with `∀ T ≥ 0, IsHilbertMartingaleWithCovariation P ℱ T M Sg` (exactly the hypothesis form of
`stationary_noise`, `HRS/Uniform/Evolution.lean`) and a deterministic covariance density `Db` with
`∀ T ≥ 0, IsDetCovDensity T Db`,
`AdaptedGaussianCoupling P ℱ ⊤ 𝒢 M Sg Db (· = ·) (fun r ω => bures2 (Sg r ω) (Db r))`
(one enlargement `Ω'` for the whole half-line; horizon `⊤`, so the conclusions hold on every `[0,S]`:
`M∘π` is a Hilbert martingale with covariation `Sg∘π` on every window, the Gaussian martingale has covariation
density `Db` on every window and is independent of `𝒢`, the difference stopped at each `S` has covariation
density `Sd` on `[0,S]` and `‖Sd_r‖_{𝔖₁} = 𝔟(Sg_r∘π, Db_r)²` for all `r ≥ 0` almost surely).

Route (ISSUES §I, PROOF_QUEUE Q48a, route (i)): the finite-horizon proof `relative_covariance_coupling_proof`
(`HRS/Uniform/RelativeCoupling.lean`, Q07c) is not usable as a black box because its enlargement is existentially
built for one horizon; its ingredients are horizon-local only through the cut-off `r ≤ T`, so the construction is
rerun once on `[0,∞)`: `Q48aAux1`–`3` (martingale representation, `⊤`-copy of MREP `MRepAux5-9,12,14`),
`Q48aAux4`–`6` (the deterministic square root, the Gaussian integral and the coupling core, `⊤`-copy of
`PCDetData`, `pc_exists_G`, `pc_Z_isItoC`, `Q07c.coupling_core`), and the assembly below (`⊤`-copy of
`relative_covariance_coupling_proof`).  The cut-offs disappear and the global integrability `E∫_0^T ‖Σ‖₁ < ∞`
becomes local integrability on every window (all supplied by the hypotheses `∀ T ≥ 0`).
-/

noncomputable section

open HRS HRS.MRep HRS.Uniform.Q07c
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

namespace Q48a

universe u

section Top

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma 3.29 on the whole half-line: one adapted coupling of the entire martingales, horizon `⊤`. -/
theorem relative_covariance_coupling_top {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : ∀ T : ℝ, 0 ≤ T → IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hDb : ∀ T : ℝ, 0 ≤ T → IsDetCovDensity T Db) :
    AdaptedGaussianCoupling P ℱ ⊤ 𝒢 M Sg Db (· = ·)
      (fun r ω => bures2 (Sg r ω) (Db r)) := by
  classical
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', κ, hκ, B, Φ, M', hfilt, hB, -, hΦ, hMimm, hM'I,
    hM'eq, -, hΦSgF⟩ := martingale_representation_top P ℱ 𝒢 M Sg hM
  haveI := hP'
  haveI := hκ
  obtain ⟨ιe, hι, Gb, Z, hGc, hG0, hGHM, hZhs, hNHM, hcost⟩ :=
    coupling_coreT P' ℱ' B hB Φ hΦ M' hM'I Db hDb
  haveI := hι
  obtain ⟨ι₀, hι₀, e0, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι₀
  have hM0 := hM 0 le_rfl
  have hπp : MeasurePreserving (Prod.fst : Ω' × (ιe → WienerSeq) → Ω')
      (P'.prod (wMeasure ιe)) P' := measurePreserving_fst
  have hπ''p : MeasurePreserving (fun p : Ω' × (ιe → WienerSeq) => π p.1)
      (P'.prod (wMeasure ιe)) P := hπ.comp hπp
  have hfst : ∀ s, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s, ℱ' s]
      (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have hfilt'' : ∀ s, (ℱ s).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) ≤
      prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s := fun s => by
    have h1 : (ℱ s).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) =
        ((ℱ s).comap π).comap (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [h1]
    exact (MeasurableSpace.comap_mono (hfilt s)).trans (le_sup_of_le_left le_sup_left)
  have hπ''m : ∀ s, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s, ℱ s]
      (fun p : Ω' × (ιe → WienerSeq) => π p.1) := fun s => Measurable.of_comap_le (hfilt'' s)
  have hcomplete : IsCompleteFiltration (P'.prod (wMeasure ιe))
      (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) := HRS.MRep.prodFiltration_complete P' ℱ'
  -- the difference density
  have hZtc : ∀ r p, IsTraceClassCov (hsCovForm (Z r p)) := fun r p =>
    isTraceClassCov_hsCovForm ((hZhs 0).summable r p)
  -- joint measurability and adaptedness of the ingredients of `Sd`
  have hCm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      hsCovForm (Φ a.1 a.2.1) x y := fun x y => by
    have h : Measurable fun p : ℝ × Ω' => hsCovForm (Φ p.1 p.2) x y :=
      HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hΦ x y)
    have hf : Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, a.2.1) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    exact Measurable.comp (g := fun p : ℝ × Ω' => hsCovForm (Φ p.1 p.2) x y)
      (f := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, a.2.1)) h hf
  have hZm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      hsCovForm (Z a.1 a.2) x y := fun x y =>
    HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hZhs x y)
  have hSm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      Sg a.1 (π a.2.1) x y := fun x y => by
    have h : Measurable (Function.uncurry fun σ ω => Sg σ ω x y) := hM0.sigma_meas x y
    have hf : Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, π a.2.1) :=
      measurable_fst.prodMk (hπ.measurable.comp (measurable_fst.comp measurable_snd))
    exact Measurable.comp (g := Function.uncurry fun σ ω => Sg σ ω x y)
      (f := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, π a.2.1)) h hf
  have hDm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1 x y := fun x y =>
    ((hDb 0 le_rfl).meas x y).comp measurable_fst
  -- the difference covariation density
  obtain ⟨Sd, hSdDef⟩ : ∃ Sd : ℝ → Ω' × (ιe → WienerSeq) → (H →L[ℝ] H →L[ℝ] ℝ), ∀ r p,
      Sd r p = SdDef e0 (fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
        (fun a => hsCovForm (Φ a.1 a.2.1)) (fun a => hsCovForm (Z a.1 a.2))
        (fun a => Sg a.1 (π a.2.1)) (r, p) := ⟨_, fun _ _ => rfl⟩
  have hSdm : ∀ x y : H, Measurable (Function.uncurry fun r p => Sd r p x y) := fun x y => by
    have h := measurable_SdDef e0 hCm hZm hSm hDm x y
    have e : (Function.uncurry fun r p => Sd r p x y) = fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
        SdDef e0 (fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
          (fun a => hsCovForm (Φ a.1 a.2.1)) (fun a => hsCovForm (Z a.1 a.2))
          (fun a => Sg a.1 (π a.2.1)) a x y := by
      funext ⟨r, p⟩; simp only [Function.uncurry_apply_pair, hSdDef]
    rw [e]; exact h
  have hSda : ∀ σ (x y : H), Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
      (fun p => Sd σ p x y) := by
    intro σ x y
    have h1 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1) x y := fun x y =>
      (adapted_hsCov hΦ σ x y).comp (hfst σ)
    have h2 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Z σ p) x y := fun x y =>
      adapted_hsCov hZhs σ x y
    have h3 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => Sg σ (π p.1) x y := fun x y =>
      (hM0.sigma_adapted σ x y).comp (hπ''m σ)
    have := measurable_SdDef (mα := prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ) e0
      (D := fun _ => Db σ) (C := fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1))
      (Z := fun p => hsCovForm (Z σ p)) (S := fun p => Sg σ (π p.1)) h1 h2 h3
      (fun x y => measurable_const) x y
    have e : (fun p : Ω' × (ιe → WienerSeq) => Sd σ p x y) = fun p =>
        SdDef e0 (fun _ => Db σ) (fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1))
          (fun p => hsCovForm (Z σ p)) (fun p => Sg σ (π p.1)) p x y := by
      funext p; rw [hSdDef]; rfl
    rw [e]; exact this
  have hSdtc : ∀ σ p, IsTraceClassCov (Sd σ p) := fun σ p => by
    rw [hSdDef]; exact SdDef_tc e0 (fun a => hZtc _ _) _
  have hgoodae : ∀ᵐ p ∂(P'.prod (wMeasure ιe)), ∀ᵐ σ ∂(volume.restrict (Set.Ici (0 : ℝ))),
      hsCovForm (Φ σ p.1) = Sg σ (π p.1) :=
    hπp.quasiMeasurePreserving.ae hΦSgF
  have hMM' : ∀ τ' : ℝ, ∀ᵐ p ∂(P'.prod (wMeasure ιe)), M τ' (π p.1) = M' τ' p.1 := by
    intro τ'
    have hz' : ∀ᵐ ω ∂P', M τ' (π ω) = M' τ' ω := by
      by_cases h0 : 0 ≤ τ'
      · exact hM'eq.mono fun ω h => (h τ' h0).symm
      · have hz := isHM_ae_zero_nonpos (hMimm 0 le_rfl) (not_le.1 h0).le
        exact hz.mono fun ω h => by
          have h1 : M τ' (π ω) = 0 := h
          rw [h1, hM'I.zero τ' (not_le.1 h0).le ω]
    exact hπp.quasiMeasurePreserving.ae hz'
  refine ⟨Ω' × (ιe → WienerSeq), inferInstance, ⟨P'.prod (wMeasure ιe), inferInstance⟩,
    fun p => π p.1, prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe), Gb, Sd, ?_⟩
  refine ⟨hπ''p, hfilt'', ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS _
    exact (hMimm S hS).comp_fst
  · intro S hS _
    have e : (fun (r : ℝ) (_ : Ω' × (ιe → WienerSeq)) =>
        if ENNReal.ofReal r ≤ ⊤ then Db r else 0) = fun r _ => Db r := by
      funext r _; simp
    rw [e]
    exact hGHM S hS
  · intro S hS _
    have hae : ∀ᵐ p ∂(P'.prod (wMeasure ιe)), ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) S)),
        Sd σ p = hsCovForm (Z σ p) := by
      filter_upwards [hgoodae] with p hp
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self hp]
        with σ hσ
      rw [hSdDef]
      unfold SdDef
      simp only [hσ, if_true]
    have hst := (hNHM S).stop_congr hcomplete hS le_rfl hSdm hSda hSdtc hae
    refine hst.congr_process hcomplete (fun τ => ?_) (fun τ => ?_) ?_
    · exact ((measurable_of_isHM hM0 (min τ S)).comp hπ''p.measurable).sub
        (measurable_of_isHM (hGHM 0 le_rfl) (min τ S))
    · filter_upwards [hMM' (min τ S)] with p hp
      show M (min τ S) (π p.1) - Gb (min τ S) p = M' (min τ S) p.1 - Gb (min τ S) p
      rw [hp]
    · filter_upwards [hπp.quasiMeasurePreserving.ae (hMimm S hS).cont] with p hp
      have h1 : ContinuousOn (fun τ => M τ (π p.1) - Gb τ p) (Set.Icc 0 S) :=
        hp.sub (hGc p).continuousOn
      refine h1.congr fun τ hτ => ?_
      simp [min_eq_left hτ.2]
  · have hle : (𝒢.1).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) ≤
        prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) 0 :=
      (MeasurableSpace.comap_mono 𝒢.2).trans (hfilt'' 0)
    set 𝒢' : InitialSigma (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) :=
      ⟨(𝒢.1).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1), hle⟩ with h𝒢'
    set m : ℕ → MeasurableSpace (Ω' × (ιe → WienerSeq)) := fun n =>
      ⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ (n : ℝ)}, MeasurableSpace.comap (Gb τ) inferInstance with hm
    have hn : ∀ n : ℕ, Indep 𝒢'.1 (m n) (P'.prod (wMeasure ιe)) := fun n =>
      indep_path (hGHM n (Nat.cast_nonneg n)) (Nat.cast_nonneg n) hGc hG0 𝒢'
    have hmle : ∀ n, m n ≤ (inferInstance : MeasurableSpace (Ω' × (ιe → WienerSeq))) := fun n =>
      iSup₂_le fun τ _ => (measurable_of_isHM (hGHM 0 le_rfl) τ).comap_le
    have hdir : Directed (· ≤ ·) m := by
      refine Monotone.directed_le fun a b hab => ?_
      refine iSup₂_le fun τ hτ => le_iSup₂_of_le τ ⟨hτ.1, hτ.2.trans (Nat.cast_le.2 hab)⟩ le_rfl
    have hbig := indep_iSup_of_directed_le (fun n => (hn n).symm) hmle
      (𝒢'.2.trans ((prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)).le 0)) hdir
    refine indep_of_indep_of_le_right hbig.symm ?_
    refine iSup₂_le fun τ hτ => ?_
    obtain ⟨n, hn'⟩ := exists_nat_ge τ
    exact le_iSup_of_le n (le_iSup₂_of_le τ ⟨hτ.1, hn'⟩ le_rfl)
  · have hSgtc := allwin_traceClass hM
    filter_upwards [hπ''p.quasiMeasurePreserving.ae hSgtc] with p hp r hr0 _
    rw [hSdDef]
    exact traceNormForm_SdDef e0 (D := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
      (C := fun a => hsCovForm (Φ a.1 a.2.1)) (Z := fun a => hsCovForm (Z a.1 a.2))
      (S := fun a => Sg a.1 (π a.2.1)) (r, p) (hp r hr0)
      ((hDb r hr0).traceClass r ⟨hr0, le_rfl⟩)
      (fun h => by
        show traceNormForm (hsCovForm (Z r p)) = bures2 (Sg r (π p.1)) (Db r)
        rw [hcost r hr0 p]
        exact congrArg (fun F => bures2 F (Db r)) h)

end Top

end Q48a

end Uniform

end HRS
