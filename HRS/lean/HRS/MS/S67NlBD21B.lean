import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.UniqM2
import HRS.MS.UniqM2Loc
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD21A

/-!
# S6.7nl.21B: Sobolev membership and norm of the actual weak derivative
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.

Route (Fourier side, no density sequence): for `h ∈ H^r ⊆ H^1` the `L²` function `V = F⁻¹(2πiξ_i ĥ)`
is real (Hermitian symmetry of `ĥ`), and its real part satisfies the compact-test weak identity
(`pairing_identity`).  Compact-test uniqueness (`ae_eq_of_weak_eq` on the whole space) identifies it
with the continuous `v`; so `v ∈ L²` with `v̂ = 2πiξ_i ĥ`, and `|2πiξ_i|² ≤ 1 + 4π²|ξ|²` gives the
`H^(r-1)` bound with constant `1`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqM2 in
/-- The actual continuous weak derivative of an `H¹` function is `L²` with Fourier transform
`2πiξ_i ĥ`. -/
theorem s67bd_wd_identify (i : Fin d) {h v : Euc d → ℝ}
    (hh : HRS.PDE.ToolboxRd.MemSobolev 1 h) (hv : Continuous v) (hw : s67bd_WeakDerivative i h v) :
    MemLp v 2 volume ∧
      HRS.PDE.ToolboxRd.fourierL2 v =ᵐ[volume] HRS.MS.UniqM2.gfun h i := by
  set G := (memLp_gfun hh i).toLp (gfun h i) with hG
  set V : Lp (α := Euc d) ℂ 2 := (FT d).symm G with hV
  have hFV : FT d V = G := (FT d).apply_symm_apply G
  have hGae : (G : Euc d → ℂ) =ᵐ[volume] gfun h i := MemLp.coeFn_toLp (memLp_gfun hh i)
  -- `V` is real: `conj V = V`
  have hVc : conjLp V = V := by
    refine (FT d).injective ?_
    rw [fourier_conjLp, hFV]
    apply Lp.ext
    have hq := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
    have h5 := negLp_coe (conjLp G)
    have h6 := hq.ae_eq_comp (conjLp_coe G)
    have h7 := hq.ae_eq_comp hGae
    have h8 := fourierL2_neg hh.1
    filter_upwards [h5, h6, h7, h8, hGae] with ξ a b c e g
    simp only [Function.comp_apply] at b c
    rw [a, b, c]
    simp only [gfun] at e g ⊢
    rw [e, g]
    unfold mult
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.conj_conj,
      PiLp.neg_apply, Complex.ofReal_neg, map_neg]
    ring
  have hVr : ∀ᵐ x ∂(volume : Measure (Euc d)), (((V x).re : ℝ) : ℂ) = V x := by
    filter_upwards [conjLp_coe V] with x hx
    rw [hVc] at hx
    exact Complex.conj_eq_iff_re.1 hx.symm
  have hmem : MemLp (fun x => (V x).re) 2 volume := (Lp.memLp V).re
  -- identification with `v`
  have hae := ae_eq_of_weak_eq (U := Set.univ) isOpen_univ (a := v) (b := fun x => (V x).re)
    hv.locallyIntegrable (hmem.locallyIntegrable (by norm_num)) (fun ψ hψ hc _ => by
      have h1 := (hw ψ hψ hc).2.2
      have h2 := pairing_identity hh i V hFV hψ hc
      have h3 : (∫ x, h x * s67bd_D i ψ x) =
          ∫ x, h x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := rfl
      linarith)
  have hvV : v =ᵐ[volume] fun x => (V x).re := by
    filter_upwards [hae] with x hx using hx (Set.mem_univ x)
  have hvL : MemLp v 2 volume := hmem.ae_eq hvV.symm
  refine ⟨hvL, ?_⟩
  have hoV : ofRealLp hvL = V := by
    apply Lp.ext
    filter_upwards [ofRealLp_coe hvL, hvV, hVr] with x a b c
    rw [a, b, c]
  rw [fourierL2_eq hvL, hoV, hFV]
  exact hGae

/-- S6.7nl.21B: the continuous weak derivative of an `H^r` function, `r ≥ 1`, lies in `H^(r-1)`
with norm at most `‖h‖_{H^r}`. -/
theorem s67bd_weak_derivative_sobolev (d : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h v : Euc d → ℝ) (i : Fin d),
      HRS.PDE.ToolboxRd.MemSobolev r h → Continuous v → s67bd_WeakDerivative i h v →
      HRS.PDE.ToolboxRd.MemSobolev (r - 1) v ∧
      s67bd_Hnorm (r - 1) v ≤ C * s67bd_Hnorm r h := by
  refine ⟨1, zero_le_one, fun h v i hS hv hw => ?_⟩
  have hS1 : HRS.PDE.ToolboxRd.MemSobolev 1 h := HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hr hS
  obtain ⟨hvL, hF⟩ := s67bd_wd_identify i hS1 hv hw
  have hm : AEStronglyMeasurable (HRS.PDE.ToolboxRd.fourierL2 v) volume :=
    HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hvL
  have hI : Integrable (fun ξ : Euc d => HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ r *
      ‖HRS.PDE.ToolboxRd.fourierL2 h ξ‖ ^ 2) volume := hS.2
  -- pointwise bound on the Fourier side
  have hpt : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) * ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2 ≤
        HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ r * ‖HRS.PDE.ToolboxRd.fourierL2 h ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    have hW : 0 < HRS.PDE.ToolboxRd.FourierAux.wt (d := d) ξ :=
      HRS.PDE.ToolboxRd.FourierAux.wt_pos ξ
    have hrw : HRS.PDE.ToolboxRd.FourierAux.wt (d := d) ξ ^ r =
        HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) * HRS.PDE.ToolboxRd.FourierAux.wt ξ := by
      have := Real.rpow_add_one hW.ne' (r - 1)
      rwa [sub_add_cancel] at this
    rw [hξ, hrw]
    unfold HRS.MS.UniqM2.gfun
    rw [norm_mul, mul_pow]
    have h1 := HRS.MS.UniqM2.norm_mult_sq_le i ξ
    have h0 : 0 ≤ HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) := Real.rpow_nonneg hW.le _
    calc HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) *
          (‖HRS.MS.UniqM2.mult i ξ‖ ^ 2 * ‖HRS.PDE.ToolboxRd.fourierL2 h ξ‖ ^ 2)
        ≤ HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) *
          (HRS.PDE.ToolboxRd.FourierAux.wt ξ * ‖HRS.PDE.ToolboxRd.fourierL2 h ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) h0
      _ = _ := by ring
  have hint : Integrable (fun ξ : Euc d => HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ (r - 1) *
      ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2) volume := by
    refine Integrable.mono' hI (HRS.PDE.ToolboxRd.FourierAux.aesm_wt_mul hm (r - 1)) ?_
    filter_upwards [hpt] with ξ hξ
    have hW : 0 < HRS.PDE.ToolboxRd.FourierAux.wt (d := d) ξ :=
      HRS.PDE.ToolboxRd.FourierAux.wt_pos ξ
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hW.le _) (sq_nonneg _))]
    exact hξ
  refine ⟨⟨hvL, hint⟩, ?_⟩
  rw [one_mul]
  unfold s67bd_Hnorm
  refine Real.sqrt_le_sqrt ?_
  rw [HRS.PDE.ToolboxRd.FourierAux.sobolevNormSq_eq, HRS.PDE.ToolboxRd.FourierAux.sobolevNormSq_eq]
  exact integral_mono_ae hint hI hpt

end HRS.MS.BreakdownS67
