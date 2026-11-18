import HRS.Uniform.Q07cAux9

/-!
# Q07c, part 10: the coupling core on the product enlargement
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Core

universe u

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The `x`-coordinate of the Gaussian integrand `Sb Ψ̃`. -/
def XiG {ιe κ : Type*} {Ω : Type*} (e : HilbertBasis ιe ℝ H) (Sb : ℝ → H →L[ℝ] H)
    (ψ : ιe → ℝ → Ω → κ ⊕ ιe → ℝ) (x : H) : ℝ → Ω → κ ⊕ ιe → ℝ :=
  fun r ω a => inner ℝ (Sb r (PsiVec e (fun j => ψ j r ω) a)) x

lemma XiG_hasSum {ιe κ Ω : Type*} (e : HilbertBasis ιe ℝ H) {Sb : ℝ → H →L[ℝ] H}
    (hSbsymm : ∀ r x y, inner ℝ (Sb r x) y = inner ℝ x (Sb r y))
    {ψ : ιe → ℝ → Ω → κ ⊕ ιe → ℝ}
    (hrow : ∀ r ω a, Summable fun j => ψ j r ω a ^ 2) (x : H) (r : ℝ) (ω : Ω) (a : κ ⊕ ιe) :
    HasSum (fun j => ψ j r ω a * inner ℝ (Sb r (e j)) x) (XiG e Sb ψ x r ω a) := by
  have h := pcVec_hasSum_inner e (hrow r ω a) (Sb r x)
  have e1 : XiG e Sb ψ x r ω a = inner ℝ (pcVec e fun j => ψ j r ω a) (Sb r x) := by
    unfold XiG PsiVec; rw [hSbsymm]
  rw [e1]
  convert h using 2 with j
  rw [hSbsymm]

lemma tail_hasSum {ιe α : Type*} [Countable ιe] {ψ : ιe → α → ℝ} {f : ιe → ℝ} {Ξ : α → ℝ}
    (ho : ∀ i j, HasSum (fun a => ψ i a * ψ j a) (if i = j then (1 : ℝ) else 0))
    (hX : ∀ a, HasSum (fun j => ψ j a * f j) (Ξ a)) (hf : Summable fun j => f j ^ 2)
    (s : Finset ιe) :
    HasSum (fun a => (Ξ a - ∑ j ∈ s, f j * ψ j a) ^ 2) (∑' j, if j ∈ s then 0 else f j ^ 2) := by
  set c : ιe → ℝ := fun j => if j ∈ s then 0 else f j with hc
  have hcs : Summable fun j => c j ^ 2 := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hf
    by_cases h : j ∈ s
    · simp only [hc, h, ite_true, zero_pow two_ne_zero]; positivity
    · simp [hc, h]
  obtain ⟨-, h2⟩ := frame_identity ψ ho hcs
  have hcoord : ∀ a, Ξ a - ∑ j ∈ s, f j * ψ j a = ∑' j, ψ j a * c j := by
    intro a
    have h1 : HasSum (fun j => ψ j a * c j) (Ξ a - ∑ j ∈ s, f j * ψ j a) := by
      have h3 : HasSum (fun j => if j ∈ s then ψ j a * f j else 0)
          (∑ j ∈ s, if j ∈ s then ψ j a * f j else 0) :=
        hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hj])
      have h4 := (hX a).sub h3
      have e3 : (∑ j ∈ s, if j ∈ s then ψ j a * f j else 0) = ∑ j ∈ s, f j * ψ j a :=
        Finset.sum_congr rfl fun j hj => by simp [hj, mul_comm]
      rw [e3] at h4
      convert h4 using 1
      funext j
      by_cases h : j ∈ s <;> simp [hc, h]
    exact h1.tsum_eq.symm
  have e1 : (fun a => (Ξ a - ∑ j ∈ s, f j * ψ j a) ^ 2) = fun a => (∑' j, ψ j a * c j) ^ 2 := by
    funext a; rw [hcoord a]
  have e2 : ∑' j, c j ^ 2 = ∑' j, if j ∈ s then 0 else f j ^ 2 := by
    refine tsum_congr fun j => ?_
    by_cases h : j ∈ s <;> simp [hc, h]
  rw [e1, ← e2]
  exact h2

omit [BorelSpace H] [SecondCountableTopology H] in
lemma _root_.HRS.PCDetData.symm_of {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H} {T : ℝ}
    {Sb : ℝ → H →L[ℝ] H} {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ}
    (hSb : ∀ r ∈ Set.Icc 0 T, IsSqrtOfForm (Sb r) (Db r))
    (hSb0 : ∀ r, r ∉ Set.Icc 0 T → Sb r = 0) (r : ℝ) (x y : H) :
    inner ℝ (Sb r x) y = inner ℝ x (Sb r y) := by
  by_cases hr : r ∈ Set.Icc 0 T
  · exact (hSb r hr).symm x y
  · simp [hSb0 r hr]

lemma _root_.HRS.PCDetData.summable_of {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H} {T : ℝ}
    {Sb : ℝ → H →L[ℝ] H} {Tf : ℝ → ℝ} (hD : PCDetData e T Sb Tf) (r : ℝ) :
    Summable fun i => ‖Sb r (e i)‖ ^ 2 := by
  by_cases hr : r ∈ Set.Icc 0 T
  · exact (hD.trace r hr).summable
  · simp [hD.zero r hr]

lemma _root_.HRS.PCDetData.tr_lt_top {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H} {T : ℝ}
    {Sb : ℝ → H →L[ℝ] H} {Tf : ℝ → ℝ} (hD : PCDetData e T Sb Tf) (S : ℝ) :
    ∫⁻ r in Set.Icc 0 S, ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) < ⊤ := by
  have hle : ∀ r, ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) ≤
      (Set.Icc 0 T).indicator (fun r => ENNReal.ofReal (Tf r)) r := by
    intro r
    by_cases hr : r ∈ Set.Icc 0 T
    · simp only [hr, Set.indicator_of_mem]
      rw [(hD.trace r hr).tsum_eq]
    · simp [hD.zero r hr, hr]
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  refine lt_of_le_of_lt (lintegral_mono_set (Set.subset_univ _)) ?_
  rw [lintegral_indicator measurableSet_Icc, Measure.restrict_univ]
  exact hD.Tint.lintegral_lt_top

theorem coupling_core {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] (ℱ' : Filtration ℝ mΩ') {κ : Type u} [Countable κ]
    (B : ℝ≥0 → Ω' → κ → ℝ) (hB : IsCylindricalBrownian P' ℱ' B) (Φ : ℝ → Ω' → κ → H)
    (hΦ : ∀ S, IsHSIntegrand P' ℱ' S Φ) (M' : ℝ → Ω' → H)
    (hM' : IsHilbertItoIntegral P' ℱ' B Φ M') (T : ℝ) (hT : 0 ≤ T)
    (hΦ0 : ∀ r ω, T < r → Φ r ω = 0) (Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (hDb : IsDetCovDensity T Db) :
    ∃ (ιe : Type u) (_ : Countable ιe) (Gb : ℝ → Ω' × (ιe → WienerSeq) → H)
      (Z : ℝ → Ω' × (ιe → WienerSeq) → κ ⊕ ιe → H),
      (∀ ω, Continuous fun τ => Gb τ ω) ∧ (∀ ω, Gb 0 ω = 0) ∧
      IsHilbertMartingaleWithCovariation (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) T Gb
        (fun r _ => if r ≤ T then Db r else 0) ∧
      (∀ S, IsHSIntegrand (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) S Z) ∧
      (∀ S, IsHilbertMartingaleWithCovariation (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) S
        (fun τ p => M' (min τ T) p.1 - Gb τ p) (fun r p => hsCovForm (Z r p))) ∧
      (∀ r ∈ Set.Icc 0 T, ∀ p, traceNormForm (hsCovForm (Z r p)) =
        Uniform.bures2 (hsCovForm (Φ r p.1)) (Db r)) := by
  classical
  obtain ⟨ιe, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, u} (H := H)
  haveI := hι
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_density e T Db hDb
  obtain ⟨Tf, hD⟩ := pc_detData e T Db hDb hSbm hSb0 hSb
  have hSbsymm := PCDetData.symm_of (e := e) hSb hSb0
  have hSbHS := hD.summable_of
  -- the polar family of `Θ = Sb Φ`
  have hΘp : ∀ k, IsProgressive ℱ' (fun r ω => Sb r (Φ r ω k)) := by
    intro k i
    letI : MeasurableSpace (Set.Iic i × Ω') := Subtype.instMeasurableSpace.prod (ℱ' i)
    have hSbz : OpMeas fun z : Set.Iic i × Ω' => Sb z.1.1 := fun x =>
      (hSbm x).comp (measurable_subtype_coe.comp measurable_fst)
    exact hSbz.apply ((hΦ 0).prog k i)
  have hΘs : ∀ r ω, Summable fun k => ‖Sb r (Φ r ω k)‖ ^ 2 := fun r ω =>
    summable_norm_sq_comp (Sb := Sb r) ((hΦ 0).summable r ω)
  obtain ⟨Sθ, ψ, hSθ, -, hψprog, hψo, hψe, -, -⟩ := exists_polar_family (ℱ := ℱ') e
    (fun r ω k => Sb r (Φ r ω k)) hΘp hΘs
  -- the product enlargement
  have hW₂ : IsCylindricalBrownian (wMeasure ιe) (wFiltration ιe)
      (fun t (ω : ιe → WienerSeq) (i : ιe) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  have h𝔚 : IsCylindricalBrownian (P'.prod (wMeasure ιe))
      (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe))
      (sumFam B (fun t (ω : ιe → WienerSeq) (i : ιe) => wienerPath t (ω i))) :=
    isCylindricalBrownian_prod hB hW₂
  set P'' : Measure (Ω' × (ιe → WienerSeq)) := P'.prod (wMeasure ιe) with hP''
  set ℱ'' := prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) with hℱ''
  set 𝔚 := sumFam B (fun t (ω : ιe → WienerSeq) (i : ιe) => wienerPath t (ω i)) with h𝔚def
  have hπp : MeasurePreserving (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') P'' P' :=
    measurePreserving_fst
  have hπm : ∀ s, Measurable[ℱ'' s, ℱ' s] (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have h𝔚l : ∀ s (ω' : Ω' × (ιe → WienerSeq)) k, 𝔚 s ω' (Sum.inl k) = B s ω'.1 k :=
    fun _ _ _ => rfl
  set ψ' : ιe → ℝ → Ω' × (ιe → WienerSeq) → κ ⊕ ιe → ℝ := fun j r ω' a => ψ j r ω'.1 a with hψ'
  have hψctbl : ∀ j, IsCtbl P'' ℱ'' (ψ' j) := fun j =>
    pc_isCtbl_comp hπm hπp (pc_isCtbl_of_hasSum_one (hψprog j)
      (fun r ω => by simpa [sq] using hψo r ω j j))
  have hex : ∀ j, ∃ I, IsItoC P'' ℱ'' 𝔚 (ψ' j) I := fun j => exists_isItoC h𝔚 (hψctbl j)
  choose Bj hBj using hex
  have hortho' : ∀ r (ω' : Ω' × (ιe → WienerSeq)) i j, HasSum (fun a => ψ' i r ω' a * ψ' j r ω' a)
      (if i = j then (1 : ℝ) else 0) := fun r ω' i j => hψo r ω'.1 i j
  have hBt : IsCylindricalBrownian P'' ℱ'' (fun t ω' j => Bj j (t : ℝ) ω') :=
    isCylindricalBrownian_of_itoC h𝔚 hψctbl hBj hortho'
  obtain ⟨Gb, hGI, hGJ⟩ := pc_exists_G hD hBt
  -- the difference integrand
  set Z : ℝ → Ω' × (ιe → WienerSeq) → κ ⊕ ιe → H := fun r ω a =>
    ZVec (e := e) (Sb r) (Φ r ω.1) (fun j => ψ j r ω.1) a with hZdef
  have hZhsBase : ∀ S, IsHSIntegrand P' ℱ' S
      (fun r ω a => ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a) := fun S =>
    Zint_hsInt e hSbm hSbsymm hSbHS (hΦ S) hψo hψprog (hD.tr_lt_top S)
  have hZhs : ∀ S, IsHSIntegrand P'' ℱ'' S Z := fun S => hsInt_comp_fst (hZhsBase S)
  -- the Gaussian martingale
  have hZG : ∀ S, IsHSIntegrand P'' ℱ'' S
      (fun r (_ : Ω' × (ιe → WienerSeq)) (j : ιe) => if r ≤ T then Sb r (e j) else 0) :=
    fun S => hD.hsInt P'' ℱ'' S
  have hNJG : ∀ x : H, ∃ J : ℝ → Ω' × (ιe → WienerSeq) → ℝ,
      IsItoC P'' ℱ'' (fun t ω j => Bj j (t : ℝ) ω)
        (fun r (_ : Ω' × (ιe → WienerSeq)) (j : ιe) => inner ℝ (if r ≤ T then Sb r (e j) else 0) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Gb τ ω) x) =ᵐ[P''] J τ := by
    intro x
    obtain ⟨J, hJ, hae⟩ := hGJ x
    refine ⟨J, ?_, hae⟩
    have : (fun r (_ : Ω' × (ιe → WienerSeq)) (j : ιe) =>
        inner ℝ (if r ≤ T then Sb r (e j) else (0 : H)) x) = fSb e T Sb x := by
      funext r ω j; by_cases h : r ≤ T <;> simp [fSb, h]
    rw [this]; exact hJ
  have hGHM := isHM_of_ito hBt hZG hGI.cont hGI.adapted hGI.zero hNJG T
  have hcovG : ∀ r : ℝ, 0 ≤ r → hsCovForm (fun j => if r ≤ T then Sb r (e j) else (0 : H)) =
      if r ≤ T then Db r else 0 := by
    intro r hr0
    by_cases hr : r ≤ T
    · simp only [hr, ite_true]
      exact hsCovForm_sqrt_cols e (hSb r ⟨hr0, hr⟩) (hSbHS r)
    · have h0 : Sb r = 0 := hSb0 r (fun h => hr h.2)
      simp only [hr, ite_false]
      refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
      rw [hsCovForm_apply (by simpa using (summable_zero : Summable fun _ : ιe => (0 : ℝ)))]
      simp
  have hGfinal : IsHilbertMartingaleWithCovariation P'' ℱ'' T Gb
      (fun r _ => if r ≤ T then Db r else 0) := by
    refine hGHM.mono_congr hT le_rfl (fun x y => ?_) (fun σ x y => measurable_const) ?_
    · have : (Function.uncurry fun σ (ω : Ω' × (ιe → WienerSeq)) =>
          (fun r (_ : Ω' × (ιe → WienerSeq)) => if r ≤ T then Db r else 0) σ ω x y) =
          fun p => if p.1 ≤ T then Db p.1 x y else 0 := by
        funext p; by_cases h : p.1 ≤ T <;> simp [Function.uncurry, h]
      rw [this]
      exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
        ((hDb.meas x y).comp measurable_fst) measurable_const
    · intro r hr ω
      exact (hcovG r hr).symm
  -- the difference process
  set Nproc : ℝ → Ω' × (ιe → WienerSeq) → H := fun τ p => M' (min τ T) p.1 - Gb τ p with hNproc
  have hNc : ∀ ω, Continuous fun τ => Nproc τ ω := fun ω =>
    ((hM'.cont ω.1).comp (continuous_id.min continuous_const)).sub (hGI.cont ω)
  have hNa : ∀ τ, Measurable[ℱ'' τ] (Nproc τ) := fun τ => by
    have h1 : Measurable[ℱ' τ] (M' (min τ T)) :=
      (hM'.adapted (min τ T)).mono (ℱ'.mono (min_le_left τ T)) le_rfl
    exact (h1.comp (hπm τ)).sub (hGI.adapted τ)
  have hN0 : ∀ τ, τ ≤ 0 → ∀ ω, Nproc τ ω = 0 := fun τ hτ ω => by
    simp only [hNproc]
    rw [min_eq_left (hτ.trans hT), hM'.zero τ hτ ω.1, hGI.zero τ hτ ω]; simp
  have hrow : ∀ r (ω : Ω') a, Summable fun j => ψ j r ω a ^ 2 := fun r ω a =>
    rowsum_le_one (fun j => ψ j r ω) (hψo r ω) a
  have hzx : ∀ x r (ω : Ω' × (ιe → WienerSeq)) a, inner ℝ (Z r ω a) x =
      pcXi T Φ x ιe r ω.1 a - XiG e Sb ψ' x r ω a := by
    intro x r ω a
    show inner ℝ (ZVec (e := e) (Sb r) (Φ r ω.1) (fun j => ψ j r ω.1) a) x = _
    unfold ZVec XiG
    rw [inner_sub_left]
    congr 1
    rcases a with k | l
    · simp only [Sum.elim_inl, pcXi]
      by_cases h : r ≤ T
      · simp [h]
      · simp [h, hΦ0 r ω.1 (not_le.1 h)]
    · simp [pcXi]
  have hNJ : ∀ x : H, ∃ J : ℝ → Ω' × (ιe → WienerSeq) → ℝ,
      IsItoC P'' ℱ'' 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Nproc τ ω) x) =ᵐ[P''] J τ := by
    intro x
    have hJM := pc_Z_isItoC hB hΦ hM' hT hπm hπp h𝔚 h𝔚l x
    have hcM : IsCtbl P'' ℱ'' (fun r (ω' : Ω' × (ιe → WienerSeq)) => pcXi T Φ x ιe r ω'.1) :=
      pc_isCtbl_comp hπm hπp (pc_ctbl_pcXi hΦ x T)
    have hcZ : IsCtbl P'' ℱ'' (fun r ω a => inner ℝ (Z r ω a) x) := ctbl_coord hZhs x
    have hcG : IsCtbl P'' ℱ'' (XiG e Sb ψ' x) := by
      have := pc_isCtbl_sub hcM hcZ
      convert this using 1
      funext r ω a
      rw [hzx]; ring
    obtain ⟨IG, hIG⟩ := exists_isItoC h𝔚 hcG
    have hsum : ∀ r (ω : Ω' × (ιe → WienerSeq)), Summable fun j => (fSb e T Sb x r ω j) ^ 2 := by
      intro r ω
      by_cases hr : r ≤ T
      · simpa [fSb, hr] using (hD.parseval r x).summable
      · simp [fSb, hr]
    have hE2 : ∀ (s : Finset ιe) r (ω : Ω' × (ιe → WienerSeq)), HasSum
        (fun a => (XiG e Sb ψ' x r ω a - ∑ j ∈ s, fSb e T Sb x r ω j * ψ' j r ω a) ^ 2)
        (∑' j, if j ∈ s then 0 else fSb e T Sb x r ω j ^ 2) := by
      intro s r ω
      refine tail_hasSum (ψ := fun j a => ψ j r ω.1 a) (f := fun j => fSb e T Sb x r ω j)
        (Ξ := fun a => XiG e Sb ψ' x r ω a) (hψo r ω.1) (fun a => ?_) (hsum r ω) s
      by_cases hr : r ≤ T
      · have := XiG_hasSum e hSbsymm hrow x r ω.1 a (ψ := ψ)
        simpa [fSb, hr, ψ', XiG] using this
      · have h0 : Sb r = 0 := hSb0 r (fun h => hr h.2)
        simp only [fSb, hr, ite_false, mul_zero]
        have : XiG e Sb ψ' x r ω a = 0 := by simp [XiG, h0]
        rw [this]
        exact hasSum_zero
    have hbridge := fun τ hτ => pc_bridge h𝔚 hψctbl hBj hBt hortho' (f := fSb e T Sb x)
      (hD.ctbl x) hcG hIG hsum hE2 τ hτ
    have hIGB : IsItoC P'' ℱ'' (fun t ω j => Bj j (t : ℝ) ω) (fSb e T Sb x) IG :=
      ⟨hIG.cont, hIG.adapted, hIG.zero, fun τ hτ => hbridge τ hτ⟩
    obtain ⟨J0, hJ0, hae0⟩ := hGJ x
    have huniq := hJ0.ae_eq_forall hIGB
    refine ⟨fun τ ω => inner ℝ (M' (min τ T) ω.1) x - IG τ ω, ?_, ?_⟩
    · have := IsItoC.sub h𝔚 hcM hcG hJM hIG
      have hfun : (fun r (ω : Ω' × (ιe → WienerSeq)) a => inner ℝ (Z r ω a) x) =
          (fun r ω a => pcXi T Φ x ιe r ω.1 a - XiG e Sb ψ' x r ω a) := by
        funext r ω a; exact hzx x r ω a
      rw [hfun]; exact this
    · intro τ hτ
      filter_upwards [hae0 τ hτ, huniq] with ω h1 h2
      show inner ℝ (M' (min τ T) ω.1 - Gb τ ω) x = _
      rw [inner_sub_left, h1, h2 τ]
  have hcost : ∀ r ∈ Set.Icc 0 T, ∀ p : Ω' × (ιe → WienerSeq),
      traceNormForm (hsCovForm (Z r p)) = Uniform.bures2 (hsCovForm (Φ r p.1)) (Db r) := by
    intro r hr p
    have hs := Zint_summable e hSbsymm hSbHS (fun r ω => (hΦ 0).summable r ω) hψo r p.1
    rw [traceNormForm_hsCovForm_eq (by exact hs)]
    exact (sum_norm_ZVec_eq_bures2 (e := e) (Sb := Sb r) (Φ := Φ r p.1)
      (ψ := fun j => ψ j r p.1) (hDb.traceClass r hr) (hSb r hr) ((hΦ 0).summable r p.1)
      (hSθ r p.1) (hψo r p.1) (fun x a => hψe x r p.1 a)).tsum_eq
  refine ⟨ιe, hι, Gb, Z, hGI.cont, fun ω => hGI.zero 0 le_rfl ω, hGfinal, hZhs,
    fun S => isHM_of_ito h𝔚 hZhs hNc hNa hN0 hNJ S, hcost⟩

end Core

end HRS.Uniform.Q07c
