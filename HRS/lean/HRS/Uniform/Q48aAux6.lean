import HRS.Uniform.Q48aAux5

/-!
# Q48a, part 6: the coupling core on the whole half-line

`⊤`-copy of `HRS.Uniform.Q07c.coupling_core` (`HRS/Uniform/Q07cAux10.lean`): given a cylindrical Brownian motion `B`,
a Hilbert-Schmidt integrand `Φ` (Hilbert-Schmidt on every window) with `M' = ∫ Φ dB`, and a deterministic covariance
density `Db` (`IsDetCovDensity t Db` for every `t ≥ 0`), the product enlargement carries a Gaussian martingale `Gb` with
covariation `Db` on every window and a difference integrand `Z` with `M' - Gb = ∫ Z d𝔚` and
`‖ZZ*‖₁ = 𝔟(ΦΦ*, Db)²` pointwise.
-/

noncomputable section

open HRS HRS.MRep HRS.Uniform.Q07c
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section Core

universe u

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma PCDetTop.tr_lt_top {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H}
    {Sb : ℝ → H →L[ℝ] H} {Tf : ℝ → ℝ} (hD : PCDetTop e Sb Tf) (S : ℝ) :
    ∫⁻ r in Set.Icc 0 S, ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) < ⊤ := by
  have hle : ∀ r, ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) ≤
      ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator Tf r) := by
    intro r
    by_cases hr : r ∈ Set.Ici (0 : ℝ)
    · simp only [hr, Set.indicator_of_mem]
      rw [(hD.trace r hr).tsum_eq]
    · simp [hD.zero r hr, hr]
  exact lt_of_le_of_lt (lintegral_mono hle) (hD.lintegral_T_lt S)

/-- The coupling core on the whole half-line. -/
theorem coupling_coreT {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] (ℱ' : Filtration ℝ mΩ') {κ : Type u} [Countable κ]
    (B : ℝ≥0 → Ω' → κ → ℝ) (hB : IsCylindricalBrownian P' ℱ' B) (Φ : ℝ → Ω' → κ → H)
    (hΦ : ∀ S, IsHSIntegrand P' ℱ' S Φ) (M' : ℝ → Ω' → H)
    (hM' : IsHilbertItoIntegral P' ℱ' B Φ M') (Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hDb : ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t Db) :
    ∃ (ιe : Type u) (_ : Countable ιe) (Gb : ℝ → Ω' × (ιe → WienerSeq) → H)
      (Z : ℝ → Ω' × (ιe → WienerSeq) → κ ⊕ ιe → H),
      (∀ ω, Continuous fun τ => Gb τ ω) ∧ (∀ ω, Gb 0 ω = 0) ∧
      (∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) S Gb (fun r _ => Db r)) ∧
      (∀ S, IsHSIntegrand (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) S Z) ∧
      (∀ S, IsHilbertMartingaleWithCovariation (P'.prod (wMeasure ιe))
        (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) S
        (fun τ p => M' τ p.1 - Gb τ p) (fun r p => hsCovForm (Z r p))) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ p, traceNormForm (hsCovForm (Z r p)) =
        Uniform.bures2 (hsCovForm (Φ r p.1)) (Db r)) := by
  classical
  obtain ⟨ιe, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, u} (H := H)
  haveI := hι
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_densityT e Db hDb
  obtain ⟨Tf, hD⟩ := pc_detDataT e Db hDb hSbm hSb0 hSb
  have hSbsymm : ∀ r x y, inner ℝ (Sb r x) y = inner ℝ x (Sb r y) := by
    intro r x y
    by_cases hr : 0 ≤ r
    · exact (hSb r hr).symm x y
    · simp [hSb0 r hr]
  have hSbHS := hD.summable_sb
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
  obtain ⟨Gb, hGI, hGJ⟩ := pc_exists_GT hD hBt
  -- the difference integrand
  set Z : ℝ → Ω' × (ιe → WienerSeq) → κ ⊕ ιe → H := fun r ω a =>
    ZVec (e := e) (Sb r) (Φ r ω.1) (fun j => ψ j r ω.1) a with hZdef
  have hZhsBase : ∀ S, IsHSIntegrand P' ℱ' S
      (fun r ω a => ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a) := fun S =>
    Zint_hsInt e hSbm hSbsymm hSbHS (hΦ S) hψo hψprog (hD.tr_lt_top S)
  have hZhs : ∀ S, IsHSIntegrand P'' ℱ'' S Z := fun S => hsInt_comp_fst (hZhsBase S)
  -- the Gaussian martingale
  have hZG : ∀ S, IsHSIntegrand P'' ℱ'' S
      (fun r (_ : Ω' × (ιe → WienerSeq)) (j : ιe) => Sb r (e j)) :=
    fun S => hD.hsInt P'' ℱ'' S
  have hNJG : ∀ x : H, ∃ J : ℝ → Ω' × (ιe → WienerSeq) → ℝ,
      IsItoC P'' ℱ'' (fun t ω j => Bj j (t : ℝ) ω)
        (fun r (_ : Ω' × (ιe → WienerSeq)) (j : ιe) => inner ℝ (Sb r (e j)) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Gb τ ω) x) =ᵐ[P''] J τ := by
    intro x
    obtain ⟨J, hJ, hae⟩ := hGJ x
    exact ⟨J, hJ, hae⟩
  have hGHM := fun S => isHM_of_ito hBt hZG hGI.cont hGI.adapted hGI.zero hNJG S
  have hcovG : ∀ r : ℝ, 0 ≤ r → hsCovForm (fun j => Sb r (e j)) = Db r :=
    fun r hr => hsCovForm_sqrt_cols e (hSb r hr) (hSbHS r)
  have hGfinal : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P'' ℱ'' S Gb
      (fun r _ => Db r) := by
    intro S hS
    refine (hGHM S).mono_congr hS le_rfl (fun x y => ?_) (fun σ x y => measurable_const) ?_
    · exact ((hDb 0 le_rfl).meas x y).comp measurable_fst
    · intro r hr ω
      exact (hcovG r hr).symm
  -- the difference process
  set Nproc : ℝ → Ω' × (ιe → WienerSeq) → H := fun τ p => M' τ p.1 - Gb τ p with hNproc
  have hNc : ∀ ω, Continuous fun τ => Nproc τ ω := fun ω =>
    (hM'.cont ω.1).sub (hGI.cont ω)
  have hNa : ∀ τ, Measurable[ℱ'' τ] (Nproc τ) := fun τ => by
    have h1 : Measurable[ℱ' τ] (M' τ) := hM'.adapted τ
    exact (h1.comp (hπm τ)).sub (hGI.adapted τ)
  have hN0 : ∀ τ, τ ≤ 0 → ∀ ω, Nproc τ ω = 0 := fun τ hτ ω => by
    simp only [hNproc]
    rw [hM'.zero τ hτ ω.1, hGI.zero τ hτ ω]; simp
  have hrow : ∀ r (ω : Ω') a, Summable fun j => ψ j r ω a ^ 2 := fun r ω a =>
    rowsum_le_one (fun j => ψ j r ω) (hψo r ω) a
  have hzx : ∀ x r (ω : Ω' × (ιe → WienerSeq)) a, inner ℝ (Z r ω a) x =
      pcXiT Φ x ιe r ω.1 a - XiG e Sb ψ' x r ω a := by
    intro x r ω a
    show inner ℝ (ZVec (e := e) (Sb r) (Φ r ω.1) (fun j => ψ j r ω.1) a) x = _
    unfold ZVec XiG
    rw [inner_sub_left]
    congr 1
    rcases a with k | l
    · simp only [Sum.elim_inl, pcXiT]
    · simp [pcXiT]
  have hNJ : ∀ x : H, ∃ J : ℝ → Ω' × (ιe → WienerSeq) → ℝ,
      IsItoC P'' ℱ'' 𝔚 (fun r ω a => inner ℝ (Z r ω a) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Nproc τ ω) x) =ᵐ[P''] J τ := by
    intro x
    have hJM := pc_Z_isItoCT hB hΦ hM' hπm hπp h𝔚 h𝔚l x
    have hcM : IsCtbl P'' ℱ'' (fun r (ω' : Ω' × (ιe → WienerSeq)) => pcXiT Φ x ιe r ω'.1) :=
      pc_isCtbl_comp hπm hπp (pc_ctbl_pcXiT hΦ x)
    have hcZ : IsCtbl P'' ℱ'' (fun r ω a => inner ℝ (Z r ω a) x) := ctbl_coord hZhs x
    have hcG : IsCtbl P'' ℱ'' (XiG e Sb ψ' x) := by
      have := pc_isCtbl_sub hcM hcZ
      convert this using 1
      funext r ω a
      rw [hzx]; ring
    obtain ⟨IG, hIG⟩ := exists_isItoC h𝔚 hcG
    have hsum : ∀ r (ω : Ω' × (ιe → WienerSeq)), Summable fun j => (fSbT e Sb x r ω j) ^ 2 := by
      intro r ω
      exact (hD.parseval r x).summable
    have hE2 : ∀ (s : Finset ιe) r (ω : Ω' × (ιe → WienerSeq)), HasSum
        (fun a => (XiG e Sb ψ' x r ω a - ∑ j ∈ s, fSbT e Sb x r ω j * ψ' j r ω a) ^ 2)
        (∑' j, if j ∈ s then 0 else fSbT e Sb x r ω j ^ 2) := by
      intro s r ω
      refine tail_hasSum (ψ := fun j a => ψ j r ω.1 a) (f := fun j => fSbT e Sb x r ω j)
        (Ξ := fun a => XiG e Sb ψ' x r ω a) (hψo r ω.1) (fun a => ?_) (hsum r ω) s
      have := XiG_hasSum e hSbsymm hrow x r ω.1 a (ψ := ψ)
      simpa [fSbT, ψ', XiG] using this
    have hbridge := fun τ hτ => pc_bridge h𝔚 hψctbl hBj hBt hortho' (f := fSbT e Sb x)
      (hD.ctbl x) hcG hIG hsum hE2 τ hτ
    have hIGB : IsItoC P'' ℱ'' (fun t ω j => Bj j (t : ℝ) ω) (fSbT e Sb x) IG :=
      ⟨hIG.cont, hIG.adapted, hIG.zero, fun τ hτ => hbridge τ hτ⟩
    obtain ⟨J0, hJ0, hae0⟩ := hGJ x
    have huniq := hJ0.ae_eq_forall hIGB
    refine ⟨fun τ ω => inner ℝ (M' τ ω.1) x - IG τ ω, ?_, ?_⟩
    · have := IsItoC.sub h𝔚 hcM hcG hJM hIG
      have hfun : (fun r (ω : Ω' × (ιe → WienerSeq)) a => inner ℝ (Z r ω a) x) =
          (fun r ω a => pcXiT Φ x ιe r ω.1 a - XiG e Sb ψ' x r ω a) := by
        funext r ω a; exact hzx x r ω a
      rw [hfun]; exact this
    · intro τ hτ
      filter_upwards [hae0 τ hτ, huniq] with ω h1 h2
      show inner ℝ (M' τ ω.1 - Gb τ ω) x = _
      rw [inner_sub_left, h1, h2 τ]
  have hcost : ∀ r : ℝ, 0 ≤ r → ∀ p : Ω' × (ιe → WienerSeq),
      traceNormForm (hsCovForm (Z r p)) = Uniform.bures2 (hsCovForm (Φ r p.1)) (Db r) := by
    intro r hr p
    have hs := Zint_summable e hSbsymm hSbHS (fun r ω => (hΦ 0).summable r ω) hψo r p.1
    rw [traceNormForm_hsCovForm_eq (by exact hs)]
    exact (sum_norm_ZVec_eq_bures2 (e := e) (Sb := Sb r) (Φ := Φ r p.1)
      (ψ := fun j => ψ j r p.1) ((hDb r hr).traceClass r ⟨hr, le_rfl⟩) (hSb r hr)
      ((hΦ 0).summable r p.1) (hSθ r p.1) (hψo r p.1) (fun x a => hψe x r p.1 a)).tsum_eq
  refine ⟨ιe, hι, Gb, Z, hGI.cont, fun ω => hGI.zero 0 le_rfl ω, hGfinal, hZhs,
    fun S => isHM_of_ito h𝔚 hZhs hNc hNa hN0 hNJ S, hcost⟩

end Core

end HRS.Uniform.Q48a
