import HRS.MS.R26T8AA01b

/-!
# S8.2 T8A A01 (part c): continuity of the gradient slices of a `PairCorrector` off the diagonal
`z ↦ pairGradX Q z y` is continuous on `{y}ᶜ` and `z ↦ pairGradX Q x z` is continuous on `{x}ᶜ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_gradX_cont_fst {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2}) (y : Euc d) :
    ContinuousOn (fun z => pairGradX Q z y) {y}ᶜ := by
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    have hg : ContDiff ℝ 2 (fun v : Euc d => (v, y)) := contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    exact hQ.comp hg.contDiffOn hmaps
  have h1 : ContinuousOn (fderiv ℝ (fun v => Q v y)) {y}ᶜ :=
    hf2.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have e : (fun z => pairGradX Q z y) = fun z => r26t8a_Rz d (fderiv ℝ (fun v => Q v y) z) := by
    funext z; exact congrFun (r26t8a_gradient_eq_Rz (fun v => Q v y)) z
  rw [e]
  exact (r26t8a_Rz d).continuous.comp_continuousOn h1

theorem r26t8a_a01_gradX_cont_snd {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2}) (x : Euc d) :
    ContinuousOn (fun z => pairGradX Q x z) {x}ᶜ := by
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hD : ContinuousOn (fderiv ℝ (Function.uncurry Q)) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set L : Euc d →L[ℝ] Euc d × Euc d := ContinuousLinearMap.inl ℝ (Euc d) (Euc d) with hL
  have hmaps : Set.MapsTo (fun z : Euc d => (x, z)) {x}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
    fun z hz => by simpa [eq_comm] using hz
  have h1 : ContinuousOn (fun z : Euc d => fderiv ℝ (Function.uncurry Q) (x, z)) {x}ᶜ :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn hmaps
  have hprec : Continuous (fun T : (Euc d × Euc d) →L[ℝ] ℝ => T.comp L) :=
    ((ContinuousLinearMap.compL ℝ (Euc d) (Euc d × Euc d) ℝ).flip L).continuous
  have h2 : ContinuousOn (fun z : Euc d => (fderiv ℝ (Function.uncurry Q) (x, z)).comp L) {x}ᶜ :=
    hprec.comp_continuousOn h1
  have e : ∀ z : Euc d, z ≠ x → pairGradX Q x z = r26t8a_Rz d ((fderiv ℝ (Function.uncurry Q) (x, z)).comp L) := by
    intro z hz
    have hdiff : DifferentiableAt ℝ (Function.uncurry Q) (x, z) :=
      ((hQ.contDiffAt (hU.mem_nhds (by simpa [eq_comm] using hz))).differentiableAt (by norm_num))
    have hι : HasFDerivAt (fun v : Euc d => (v, z)) L x := by
      have : HasFDerivAt (fun v : Euc d => (v, z)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x)
      exact this
    have hcomp := (hdiff.hasFDerivAt.comp x hι)
    have : fderiv ℝ (fun x' => Q x' z) x = (fderiv ℝ (Function.uncurry Q) (x, z)).comp L := hcomp.fderiv
    unfold pairGradX
    rw [r26t8a_gradient_eq_Rz]
    show r26t8a_Rz d (fderiv ℝ (fun x' => Q x' z) x) = _
    rw [this]
  have h3 : ContinuousOn (fun z : Euc d => r26t8a_Rz d ((fderiv ℝ (Function.uncurry Q) (x, z)).comp L)) {x}ᶜ :=
    (r26t8a_Rz d).continuous.comp_continuousOn h2
  exact h3.congr (fun z hz => e z hz)

end HRS.MS.R26T8A
