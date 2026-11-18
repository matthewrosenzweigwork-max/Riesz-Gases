import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.LOWVAux11
import HRS.Commutator.Whole.INHOMAux30

/-!
# Sub-Coulomb commutator on `ℝ^d`: the two auxiliary commutator estimates (Section 4)

Source `[N]`: Section 4 (L514-636).  Lemma 4.1 `lem:lowvelocity` (L523-562) and Lemma 4.2
`lem:inhomogeneous` (L565-636).  Packets `CMX-LOWV` and `CMX-INHOM`.  Both are reductions to the
external inputs `nrs_commutator` (`External.lean`), `Local.vhi_Lp`, `Local.potentialSobolev`,
`Local.product_estimate`, `Local.kernel_remainder_Lp`, `External.bernstein_Lq`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Lemma 4.1 `lem:lowvelocity` (`[N] L523-529`, proof L531-562): for a compactly supported finite real
measure or a real Schwartz density `σ` (of mass zero when `s = 0`),
`|𝒞_{g_{≤1}}(v_{≤1}, σ)| ≲ C(v) ‖P_{≤4}σ‖²_{Ḣ^{-α}}`.
Proof: `𝒞_{g_{≤1}}(v_{≤1},σ) = 2⟨σ, v_{≤1}·u⟩` (oddness of `∇g_{≤1}`, `(4.low-pairing)`), Fourier
support in `B(0,4)` gives `= 𝒞_{g_{≤1}}(v_{≤1}, a)`, `a = P_{≤4}σ`, `= 𝒞_g(v_{≤1},a) - 𝒞_{g_{>1}}(v_{≤1},a)`
(`(4.lowexact)`); the first term by `nrs_commutator` and `vlo_bound`, the second by
`‖∇v_{≤1}‖_∞ ‖|x|∇h‖_{L¹} ‖a‖²_{L²}` with `h = P_{≤8}g_{>1}` Schwartz (`(4.low-schwartz-remainder)`).
Here `C(v) ≤ K` is `SubTransport d s v K`. -/
theorem low_velocity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ σ : SMeas d, IsAdmissible σ → (s = 0 → σ.mass = 0) →
        ENNReal.ofReal |Ccomm (gloForce s) (Pleq 1 v) σ| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (lowFreq 4 σ.fourier) := by
  obtain ⟨C, hC, hmain⟩ := lowv_perLam hd hs0 hsd
  refine ⟨C, hC, fun v K hv σ hσ hmass => ?_⟩
  have ht : -alphaE d s ≤ 0 := by
    unfold alphaE
    linarith
  exact lowv_limit (by omega) (-alphaE d s) ht σ hσ _ (C * K)
    (fun Λ h4 h5 => hmain v K hv σ hσ hmass Λ h4 h5)

/-- Lemma 4.2 `lem:inhomogeneous` (`[N] L565-571`, proof L573-636): for every real `a ∈ L²(ℝ^d)`,
`|𝒞_{g_{>1}}(v,a)| ≲ C(v) ‖a‖²_{H^{-α}}`; no mass-zero assumption, also for `s = 0`.
Proof: split `a = a_0 + a_1` (`P_{≤1/8}`, `P_{>1/8}`, `(4.inhom-split)`); `a_1` by
`𝒞_{g_{>1}} = 𝒞_g - 𝒞_{g_{≤1}}(v_{≤1}) - 𝒞_{g_{≤1}}(v_{>1})` with `nrs_commutator`, `low_velocity`
and `(3.product)`/`(3.potentialSobolev)` (`(4.inhom-high-product)`); the cross term `a_0`: exact identity
`(4.crosslow)`, Fourier support separation, `L²` boundedness of `⟨∇⟩^α ∇g_{>1} *`, Hölder `(p₂,p₁)`
and `(3.zhigh)` at scale `1/8`; finally density of Schwartz functions via the `L²×L²` continuity
`(4.L2-continuity)` with `|x||∇g_{>1}| ∈ L¹` (Lemma 3.1).  `𝒞` is the iterated integral
`∬ (v(x)-v(y))·∇g_{>1}(x-y) a(x)a(y)`, absolutely convergent by `(4.L2-continuity)`. -/
theorem inhomogeneous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, MemLp a 2 volume →
        ENNReal.ofReal |CcommFun (ghiForce s) v a| ≤
          ENNReal.ofReal (C * K) * sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) :=
  inhom_main hd hs0 hsd

end HRS.Commutator.Whole
