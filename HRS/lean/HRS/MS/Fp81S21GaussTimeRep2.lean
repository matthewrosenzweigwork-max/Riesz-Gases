import HRS.MS.Fp81S21GaussTimeRep
import HRS.MS.Fp81S21GaussModification
import HRS.MS.Fp81S21EmbedIdent

/-! The Gaussian compact-test agreement has a product-a.e. version. The
physical weighted-test premise remains separate from this compact bridge. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

universe u v w

private theorem fp81s21_gaussian_transport_projection
    {α : Sort u} {P : α → Sort v} {Q : α → Sort w}
    (f : ∀ a, P a → Q a) {a b : α} (h : a = b) (x : P a) :
    f b (h ▸ x) = h ▸ f a x := by
  cases h
  rfl

private def fp81s21_gaussian_compactAgreementSet
    {d r : ℕ} {Pw m : ℝ}
    (E : r26t6_WeightedChart d r Pw) :
    Set (OscDual d m × r26t6_Coeff) :=
  {x | ∀ f : {f : Euc d → ℝ // IsR2Test f},
    fp81s21_chartAction E x.2 f.1 = OscDual.eval x.1 f.1}

private theorem fp81s21_gaussian_compactAgreementSet_closed
    {d r : ℕ} {Pw m : ℝ}
    (E : r26t6_WeightedChart d r Pw) :
    IsClosed (fp81s21_gaussian_compactAgreementSet (m := m) E) := by
  classical
  have hset : fp81s21_gaussian_compactAgreementSet (m := m) E =
      ⋂ f : {f : Euc d → ℝ // IsR2Test f},
        {x : OscDual d m × r26t6_Coeff |
          fp81s21_chartAction E x.2 f.1 = OscDual.eval x.1 f.1} := by
    ext x
    simp [fp81s21_gaussian_compactAgreementSet]
  rw [hset]
  refine isClosed_iInter fun f => ?_
  let φ : HRS.MS.S111X1.oscSub d m :=
    ⟨f.1, r2Test_isOscTest m f.2⟩
  have heval : Continuous (fun z : OscDual d m => OscDual.eval z f.1) := by
    have hEq : (fun z : OscDual d m => OscDual.eval z f.1) =
        fun z => gaussianOscEval φ z := by
      funext z
      exact (gaussianOscEval_apply φ z).symm
    rw [hEq]
    exact (gaussianOscEval φ).continuous
  have hchart : Continuous (fun x : OscDual d m × r26t6_Coeff =>
      fp81s21_chartAction E x.2 f.1) := by
    simpa [fp81s21_chartAction] using
      (continuous_snd.inner continuous_const :
        Continuous (fun x : OscDual d m × r26t6_Coeff =>
          inner ℝ x.2 (E.encode f.1)))
  exact isClosed_eq hchart (heval.comp continuous_fst)

/-- The normalized and G2 embedded strong representatives agree almost
surely at each fixed nonnegative time, and their compact-test identity lifts
to the time-sample product. This exports `hcompact_prod_ae`; it does not
assert weighted-test `S102Z` compatibility. -/
theorem fp81s21_gaussian_compact_product_bridge (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ G : GaussianRealization R,
            ∃ qs : ℝ → G.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f) qs M ∧
              (let q := fp81s21_gaussian_embedFamily p Es E qs
               let q₀ := fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)
               fp81s21_MomentRep E G.P
                 (fun u ω f => OscDual.eval (G.Z u ω) f) q M ∧
               fp81s21_MomentRep E G.P
                 (fun u ω f => OscDual.eval (G.Z u ω) f) q₀ M ∧
               Measurable (Function.uncurry q) ∧
               (∀ u : ℝ, 0 ≤ u →
                 (fun ω => q u ω) =ᵐ[G.P] (fun ω => q₀ u ω)) ∧
               ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                 ∃ U : G.Ω → Lp r26t6_Coeff 2
                     (volume.restrict (Set.Icc (0 : ℝ) H)),
                   fp81s21_TimeL2Rep G.P q M a H U ∧
                   ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod G.P),
                     ∀ f, IsR2Test f →
                       fp81s21_chartAction E (q (a + z.1) z.2) f =
                         OscDual.eval (G.Z (a + z.1) z.2) f) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by
    nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  obtain ⟨δ₀, hδ₀, hhalf, hgauss⟩ :=
    fp81s21_gaussian_momentRep_embedded p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hrealizations⟩ := hgauss δ hδ hδle R Es E
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨qs, hstrong, hGweak⟩ := hrealizations G
  refine ⟨qs, hstrong, ?_⟩
  let Pkg : ℝ → Type := fun w =>
    PSigma fun Eη : r26t6_WeightedChart p.d (2 * p.d + 6) w =>
      fp81s21_MomentRep Eη G.P
        (fun u ω f => OscDual.eval (G.Z u ω) f) qs M
  let hPkg : Pkg ((p.d : ℝ) + 4) := ⟨Es, hstrong⟩
  let hPkg' : Pkg (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ hPkg
  have hstrong' : fp81s21_MomentRep Es' G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qs M := by
    have hcast := fp81s21_gaussian_transport_projection
      (fun w (x : Pkg w) => x.1) hExp.symm hPkg
    have hchart : hPkg'.1 = Es' := by
      simpa [hPkg', hPkg, Pkg, Es'] using hcast
    rw [← hchart]
    exact hPkg'.2
  let Q : ℝ → G.Ω → (Euc p.d → ℝ) → ℝ :=
    fun u ω f => OscDual.eval (G.Z u ω) f
  let q : ℝ → G.Ω → r26t6_Coeff := fp81s21_gaussian_embedFamily p Es E qs
  let q₀ : ℝ → G.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)
  have hweak : fp81s21_MomentRep E G.P Q q M := by
    have hEmbed := fp81s21_MomentRep_embedField hP hPs Es' E G.P Q qs M hstrong'
    change fp81s21_MomentRep E G.P Q
      (fun u ω => fp81s21_embedField hP hPs Es' E (qs u ω)) M
    exact hEmbed
  have hweak₀ : fp81s21_MomentRep E G.P Q q₀ M := by
    simpa [Q, q₀] using hGweak
  have hsame : ∀ u : ℝ, 0 ≤ u →
      (fun ω => q u ω) =ᵐ[G.P] (fun ω => q₀ u ω) := by
    intro u hu
    exact fp81s21_MomentRep_eq_ae hP E G.P Q q q₀ M M hweak hweak₀ u hu
  refine ⟨hweak, hweak₀, hweak.1, hsame, ?_⟩
  have hmod := fp81s21_gauss_modification p R G
  obtain ⟨Zbar, hZbar, _, hZbarEq⟩ := hmod
  let Cset := fp81s21_gaussian_compactAgreementSet (m := (wholeSpaceIndex p.d : ℝ)) E
  have hCclosed : IsClosed Cset := fp81s21_gaussian_compactAgreementSet_closed E
  have hCmeas : MeasurableSet Cset := hCclosed.measurableSet
  have hgoodWeak : ∀ u : ℝ, 0 ≤ u → ∀ᵐ ω ∂G.P,
      (Zbar u ω, q u ω) ∈ Cset := by
    intro u hu
    have hact := (hweak.2 u hu).2.2
    filter_upwards [hact, hZbarEq] with ω hω hz
    change ∀ f : {f : Euc p.d → ℝ // IsR2Test f},
      fp81s21_chartAction E (q u ω) f.1 = OscDual.eval (Zbar u ω) f.1
    intro f
    rw [hz u hu]
    exact hω.1 f.1 f.2
  intro a ha H hH
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let timeSampleShift : ℝ × G.Ω → ℝ × G.Ω := fun z => (a + z.1, z.2)
  let X : ℝ × G.Ω → OscDual p.d (wholeSpaceIndex p.d) × r26t6_Coeff :=
    fun z => (Zbar (a + z.1) z.2, q (a + z.1) z.2)
  have hshift : Measurable timeSampleShift := by
    change Measurable (fun z : ℝ × G.Ω => (a + z.1, z.2))
    fun_prop
  have hX : Measurable X := by
    change Measurable (fun z =>
      (Function.uncurry Zbar (timeSampleShift z),
        Function.uncurry q (timeSampleShift z)))
    exact (hZbar.prodMk hweak.1).comp hshift
  have hCprodSet : MeasurableSet {z : ℝ × G.Ω | X z ∈ Cset} :=
    hCmeas.preimage hX
  have hCprod : ∀ᵐ z ∂(dt.prod G.P), X z ∈ Cset := by
    apply (Measure.ae_prod_iff_ae_ae hCprodSet).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hat : 0 ≤ a + t := by linarith [ha, ht.1]
    have hsec := hgoodWeak (a + t) hat
    simpa [X, timeSampleShift] using hsec
  obtain ⟨Bad, hBadSub, hBadMeas, hBadZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hZbarEq)
  have hnotBad : ∀ᵐ ω ∂G.P, ω ∉ Bad := by
    rw [ae_iff]
    simpa using hBadZero
  have hgood : ∀ ω, ω ∉ Bad → ∀ u : ℝ, 0 ≤ u →
      Zbar u ω = G.Z u ω := by
    intro ω hω u hu
    by_contra h
    apply hω
    apply hBadSub
    intro hall
    exact h (hall u hu)
  have hnotBadProd : ∀ᵐ z ∂(dt.prod G.P), z.2 ∉ Bad := by
    apply (Measure.ae_prod_iff_ae_ae
      (hBadMeas.compl.preimage measurable_snd)).2
    exact Filter.Eventually.of_forall fun _ => hnotBad
  have hIccProd : ∀ᵐ z ∂(dt.prod G.P), z.1 ∈ Set.Icc (0 : ℝ) H := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_preimage measurable_fst measurableSet_Icc)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall fun _ => ht
  have hcompactProd : ∀ᵐ z ∂(dt.prod G.P),
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (q (a + z.1) z.2) f =
          OscDual.eval (G.Z (a + z.1) z.2) f := by
    filter_upwards [hCprod, hnotBadProd, hIccProd] with z hz hbad ht
    have hmodAt := hgood z.2 hbad (a + z.1) (by linarith [ha, ht.1])
    have hz' : ∀ f : {f : Euc p.d → ℝ // IsR2Test f},
        fp81s21_chartAction E (q (a + z.1) z.2) f.1 =
          OscDual.eval (Zbar (a + z.1) z.2) f.1 := by
      simpa [X, Cset, fp81s21_gaussian_compactAgreementSet] using hz
    intro f hf
    rw [← hmodAt]
    exact hz' ⟨f, hf⟩
  obtain ⟨U, hcore⟩ := fp81s21_MomentRep_time_section E G.P Q q M a H hweak ha
    (le_of_lt hH)
  refine ⟨U, hcore, ?_⟩
  simpa [dt] using hcompactProd

#print axioms fp81s21_gaussian_compactAgreementSet_closed
#print axioms fp81s21_gaussian_compact_product_bridge

end HRS.Fp81.S21
