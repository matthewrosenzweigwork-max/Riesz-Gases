import HRS.MS.FinNoiseAux10

/-!
# S8.6 `finite_noise`, packet P6c (S86): `hilbert_polar_coupling` with the Hilbert-Schmidt integrability exposed

`s86_polar_ext` is the proof of `HRS.hilbert_polar_coupling` (copied verbatim) with two extra conclusions: the empirical
integrand `1_{r≤t} S_r(π ·)` and the Gaussian integrand `1_{r≤t} Sb_r` are `IsHSIntegrand` on every horizon (the
original statement discards this; it is needed to see `M∘π - G` as a Hilbert martingale, and to avoid the junk values
of `Sb r` at `r < 0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

open HilbertCLTAux HRS.MS.FinNoise

universe uΩ

variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s86_polar_ext (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (𝒢 : InitialSigma ℱ)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → H) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    ∃ (Ω' : Type uΩ) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type uΩ) (_ : Countable ι) (e : HilbertBasis ι ℝ H) (B : ℝ≥0 → Ω' → ι → ℝ)
      (S : ℝ → Ω → (H →L[ℝ] H)) (Sb : ℝ → (H →L[ℝ] H)) (G : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ r ω, IsSqrtOfForm (S r ω) (hsCovForm (Φ r ω))) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r ω' j => if r ≤ t then S r (π ω') (e j) else 0)
        (fun τ ω' => M (min τ t) (π ω')) ∧
      (∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r)) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r _ j => if r ≤ t then Sb r (e j) else 0) G ∧
      AEMeasurable (G t) P' ∧
      Indep (𝒢.1.comap π) (MeasurableSpace.comap (G t) inferInstance) P' ∧
      IsCenteredGaussian (law P' (G t)) ∧
      (∀ x y, covarianceBilin (law P' (G t)) x y = ∫ σ in Set.Icc 0 t, sb σ x y) ∧
      ∫⁻ ω', ‖M t (π ω') - G t ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) ∧
      (∀ T : ℝ, IsHSIntegrand P' ℱ' T (fun r ω' (j : ι) => if r ≤ t then S r (π ω') (e j) else 0)) ∧
      (∀ T : ℝ, IsHSIntegrand P' ℱ' T (fun r (_ : Ω') (j : ι) => if r ≤ t then Sb r (e j) else 0)) ∧
      (∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)) ∧
      (∀ x y, Measurable fun r => inner ℝ (Sb r x) y) := by
  classical
  obtain ⟨ι, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, uΩ} (H := H)
  obtain ⟨S, ψ, hSsq, hSprog, hψprog, hψo, hψe, hψn, hψt⟩ := exists_polar_family e Φ
    (fun k => (hΦ 0).prog k) (fun r ω => (hΦ 0).summable r ω)
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_density e t sb hsb
  obtain ⟨T, hD⟩ := pc_detData e t sb hsb hSbm hSb0 hSb
  have hW₂ : IsCylindricalBrownian (wMeasure ι) (wFiltration ι)
      (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  have h𝔚 : IsCylindricalBrownian (P.prod (wMeasure ι))
      (prodFiltration P (wMeasure ι) ℱ (wFiltration ι))
      (sumFam W (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i))) :=
    isCylindricalBrownian_prod hW hW₂
  set P' : Measure (Ω × (ι → WienerSeq)) := P.prod (wMeasure ι) with hP'
  set ℱ' := prodFiltration P (wMeasure ι) ℱ (wFiltration ι) with hℱ'
  set 𝔚 := sumFam W (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) with h𝔚def
  have hπp : MeasurePreserving (Prod.fst : Ω × (ι → WienerSeq) → Ω) P' P := measurePreserving_fst
  have hπm : ∀ s, Measurable[ℱ' s, ℱ s] (Prod.fst : Ω × (ι → WienerSeq) → Ω) := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have h𝔚l : ∀ s (ω' : Ω × (ι → WienerSeq)) k, 𝔚 s ω' (Sum.inl k) = W s ω'.1 k :=
    fun _ _ _ => rfl
  set ψ' : ι → ℝ → Ω × (ι → WienerSeq) → κ ⊕ ι → ℝ := fun j r ω' a => ψ j r ω'.1 a with hψ'
  have hψctbl : ∀ j, IsCtbl P' ℱ' (ψ' j) := fun j =>
    pc_isCtbl_comp hπm hπp (pc_isCtbl_of_hasSum_one (hψprog j)
      (fun r ω => by simpa [sq] using hψo r ω j j))
  have hex : ∀ j, ∃ I, IsItoC P' ℱ' 𝔚 (ψ' j) I := fun j => exists_isItoC h𝔚 (hψctbl j)
  choose Bj hBj using hex
  have hortho' : ∀ r (ω' : Ω × (ι → WienerSeq)) i j, HasSum (fun a => ψ' i r ω' a * ψ' j r ω' a)
      (if i = j then (1 : ℝ) else 0) := fun r ω' i j => hψo r ω'.1 i j
  have hB : IsCylindricalBrownian P' ℱ' (fun t ω' j => Bj j (t : ℝ) ω') :=
    isCylindricalBrownian_of_itoC h𝔚 hψctbl hBj hortho'
  -- S side
  have hfS : ∀ x, IsCtbl P' ℱ' (fun r ω' (j : ι) => if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) :=
    fun x => pc_isCtbl_comp hπm hπp (pc_ctbl_S hΦ e hSsq hSprog t x (fun r ω x => hψn x r ω))
  have hZ : ∀ x, IsItoC P' ℱ' 𝔚 (fun r ω' => pcXi t Φ x ι r ω'.1)
      (fun τ ω' => inner ℝ (M (min τ t) ω'.1) x) :=
    fun x => pc_Z_isItoC hW hΦ hM ht hπm hπp h𝔚 h𝔚l x
  have hΞ : ∀ x, IsCtbl P' ℱ' (fun r ω' => pcXi t Φ x ι r ω'.1) :=
    fun x => pc_isCtbl_comp hπm hπp (pc_ctbl_pcXi hΦ x t)
  have hsum : ∀ x r (ω' : Ω × (ι → WienerSeq)), Summable fun j : ι =>
      (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) ^ 2 := fun x r ω' => by
    by_cases hr : r ≤ t
    · simpa [hr] using (hψn x r ω'.1).summable
    · simp [hr]
  have hE2 : ∀ x (s : Finset ι) r (ω' : Ω × (ι → WienerSeq)), HasSum
      (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s, (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) *
        ψ' j r ω' a) ^ 2)
      (∑' j, if j ∈ s then 0 else (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) ^ 2) := by
    intro x s r ω'
    by_cases hr : r ≤ t
    · have h := hψt s x r ω'.1
      have e1 : (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s,
          (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) * ψ' j r ω' a) ^ 2) =
          fun a => (Sum.elim (fun k => inner ℝ (Φ r ω'.1 k) x) (fun _ => (0 : ℝ)) a -
            ∑ j ∈ s, inner ℝ (S r ω'.1 (e j)) x * ψ j r ω'.1 a) ^ 2 := by
        funext a; simp [pcXi, hr, hψ']
      rw [e1]
      simpa [hr] using h
    · have e1 : (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s,
          (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) * ψ' j r ω' a) ^ 2) = fun _ => 0 := by
        funext a; rcases a with k | l <;> simp [pcXi, hr]
      rw [e1]
      simpa [hr] using hasSum_zero
  have hbridge : ∀ x τ, 0 ≤ τ → Tendsto (fun s : Finset ι => ∫⁻ ω', ‖itoIntegral P' ℱ'
      (fun t ω' (k : s) => (fun t ω' j => Bj j (t : ℝ) ω') t ω' k)
      (fun r ω' (k : s) => (if r ≤ t then inner ℝ (S r ω'.1 (e k)) x else 0)) τ ω' -
        inner ℝ (M (min τ t) ω'.1) x‖ₑ ^ 2 ∂P') atTop (𝓝 0) := fun x τ hτ =>
    pc_bridge h𝔚 hψctbl hBj hB hortho' (hfS x) (hΞ x) (hZ x) (hsum x) (hE2 x) τ hτ
  have hZB : ∀ x, IsItoC P' ℱ' (fun t ω' j => Bj j (t : ℝ) ω')
      (fun r ω' (j : ι) => if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0)
      (fun τ ω' => inner ℝ (M (min τ t) ω'.1) x) := fun x =>
    ⟨(hZ x).cont, (hZ x).adapted, (hZ x).zero, fun τ hτ => hbridge x τ hτ⟩
  -- the Gaussian part
  have hBp : ∀ ω' : Ω × (ι → WienerSeq), True := fun _ => trivial
  obtain ⟨G, hGI, hGJ⟩ := pc_exists_G hD (P := P') (ℱ := ℱ') hB
  have hGmeas : Measurable (G t) := (hGI.adapted t).mono (ℱ'.le t) le_rfl
  have hle0 : (𝒢.1.comap (Prod.fst : Ω × (ι → WienerSeq) → Ω)) ≤ ℱ' 0 :=
    (MeasurableSpace.comap_mono (𝒢.2)).trans (le_sup_of_le_left le_sup_left)
  have hGauss := pc_G_gaussian hD hB hGJ ht hGmeas ⟨_, hle0⟩
  refine ⟨Ω × (ι → WienerSeq), inferInstance, P', inferInstance, Prod.fst, hπp, ℱ', ι, hι, e,
    fun t ω' j => Bj j (t : ℝ) ω', S, Sb, G, ?_, hB, ?_, hSsq, ?_, hSb, hGI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    exact le_sup_of_le_left le_sup_left
  · exact indep_of_indep_of_le_left (indep_zero_cylPath hB) hle0
  · refine ⟨fun ω' => (hM.cont ω'.1).comp (continuous_id.min continuous_const), fun τ => ?_,
      fun τ hτ ω' => ?_, fun τ hτ x => ?_⟩
    · exact ((hM.adapted (min τ t)).mono (ℱ.mono (min_le_left τ t)) le_rfl).comp (hπm τ)
    · simp [hM.zero (min τ t) ((min_le_left τ t).trans hτ) ω'.1]
    · have h1 := hbridge x τ hτ
      refine h1.congr (fun s => ?_)
      have e1 : (fun r (ω' : Ω × (ι → WienerSeq)) (k : s) =>
          if r ≤ t then inner ℝ (S r ω'.1 (e k)) x else 0) =
          fun r ω' (k : s) => inner ℝ (if r ≤ t then S r ω'.1 (e k) else 0) x := by
        funext r ω' k; by_cases hr : r ≤ t <;> simp [hr]
      rw [e1]
  · exact hGmeas.aemeasurable
  · exact hGauss.1
  · exact hGauss.2.1
  · intro x y
    rw [hGauss.2.2 x y]
    exact setIntegral_congr_fun measurableSet_Icc (fun σ hσ => (hSb σ hσ).sq x y)
  · have hMm : Measurable (fun ω' : Ω × (ι → WienerSeq) => M t ω'.1) :=
      ((hM.adapted t).mono (ℱ.le t) le_rfl).comp measurable_fst
    have h1 := pc_L2_bound hD (P := P') (ℱ := ℱ') hB ht (fun r ω' => S r ω'.1)
      (fun x y => isProgressive_comp_π hπm (hSprog x y)) hfS
      (Z := fun x τ ω' => inner ℝ (M (min τ t) ω'.1) x) hZB hGJ hGmeas hMm
      (fun x => Eventually.of_forall fun ω' => by simp)
      (fun r ω' => traceNormForm (hsCovForm (Φ r ω'.1) - sb r)) (fun r hr ω' => by
        have hC := isTraceClassCov_hsCovForm ((hΦ 0).summable r ω'.1)
        have hC' := hsb.traceClass r hr
        obtain ⟨T1, hT1, -⟩ := hC.hasSum_basis e
        obtain ⟨T2, hT2, -⟩ := hC'.hasSum_basis e
        exact powers_stormer e (hSsq r ω'.1) (hSb r hr) hC hC' hT1.summable hT2.summable)
    refine h1.trans (le_of_eq ?_)
    rw [hπp.lintegral_comp (pc_meas_Lr hΦ t sb hsb), pc_lintegral_covDisc hΦ ht sb hsb]
  · exact fun T => s86_hs_S P P' Prod.fst hπp hπm e Φ hΦ S hSsq hSprog t T
  · exact fun T' => s86_hs_Sb P' e t Sb T hD T'
  · exact hSprog
  · exact fun x y => (hD.meas x).inner measurable_const

end HRS
