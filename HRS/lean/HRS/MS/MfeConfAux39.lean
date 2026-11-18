import HRS.MS.MfeConfAux38
import HRS.MP.SelfSimP4Mol

/-!
# S.B.1, packet F6 (part 1): definitions and basic lemmas for the mollified entropy inequality with a tilted reference

Generalisation of the P4 mollified dissipation inequality (`HRS/MP/SelfSimP4Mol*`) to a reference
`Q_s ∝ exp(-(H + Ψ_s)/θ)` with a static Hamiltonian `H` (`∇H = -b`, the drift of the flow) and a tilt `Ψ_s` with
`∇Ψ_s = w_s`.  Writing `u = G_v * μ_s`, the free energy `∫ u log u + u (H+Ψ_s)/θ` satisfies (Fisher term dropped)
`d/ds ≤ ∫ u S_s` with the exact source `S = -div w - ⟨w,b⟩/θ + |w|²/θ + ∂_sΨ/θ` (up to the commutator error `O(v)`).

* `sb1div`, `sb1S`: divergence and source;
* `sb1_fderiv_Lam_gen`: `∂_k Λ = ℓ_k + w_k/θ` for `Λ = log u + 1 + (H+Ψ)/θ`;
* `sb1_young_gen`: the pointwise Young inequality for the commutator with an arbitrary vector.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The divergence `∑_k ∂_k w_k` of a vector field on configuration space. -/
def sb1div (w : EucConfig d N → EucConfig d N) (x : EucConfig d N) : ℝ :=
  ∑ k : Fin N × Fin d, fderiv ℝ (fun y => w y k.1 k.2) x (configBasis d N k)

/-- The exact source `S = -div w - ⟨w,b⟩/θ + |w|²/θ + ∂_sΨ/θ`. -/
def sb1S (θ : ℝ) (b w : ℝ → EucConfig d N → EucConfig d N) (Wψ : ℝ → EucConfig d N → ℝ) (r : ℝ)
    (x : EucConfig d N) : ℝ :=
  -sb1div (w r) x - p4InnerL (w r x) (b r x) / θ + p4m_q (w r x) / θ + Wψ r x / θ

theorem sb1_innerL_sub (a c : EucConfig d N) : p4InnerL (a - c) = p4InnerL a - p4InnerL c := by
  ext h
  simp only [ContinuousLinearMap.sub_apply, p4m_inner_eq, Pi.sub_apply, PiLp.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem sb1_contDiff_of_grad {Ψ : EucConfig d N → ℝ} {w : EucConfig d N → EucConfig d N}
    (hwc : Continuous w) (h : ∀ x, HasFDerivAt Ψ (p4InnerL (w x)) x) : ContDiff ℝ 1 Ψ := by
  refine contDiff_one_iff_fderiv.2 ⟨fun x => (h x).differentiableAt, ?_⟩
  have : fderiv ℝ Ψ = fun x => p4InnerL (w x) := funext fun x => (h x).fderiv
  rw [this]
  exact p4m_continuous_innerL.comp hwc

theorem sb1_wcomp {w : EucConfig d N → EucConfig d N} (hw : ContDiff ℝ 1 w) (k : Fin N × Fin d) :
    ContDiff ℝ 1 (fun x => w x k.1 k.2) :=
  contDiff_euclidean.1 (contDiff_pi.1 hw k.1) k.2

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_fderiv_Lam_gen (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (θ : ℝ)
    {b w : EucConfig d N → EucConfig d N} {H Ψ : EucConfig d N → ℝ}
    (hH : ∀ x, HasFDerivAt H (-(p4InnerL (b x))) x) (hΨ : ∀ x, HasFDerivAt Ψ (p4InnerL (w x)) x)
    (k : Fin N × Fin d) (x : EucConfig d N) :
    fderiv ℝ (p4m_Lam v θ ν (fun x => H x + Ψ x)) x (configBasis d N k) =
      p4m_ell v θ ν b k x + w x k.1 k.2 / θ := by
  have hV : ∀ x, HasFDerivAt (fun x => H x + Ψ x) (-(p4InnerL ((fun x => b x - w x) x))) x := by
    intro x
    have h := (hH x).add (hΨ x)
    simp only [sb1_innerL_sub]
    convert h using 1
    abel
  rw [p4m_fderiv_Lam_basis hv hm θ hV k x]
  unfold p4m_ell
  simp only [PiLp.sub_apply, Pi.sub_apply]
  ring

/-- The pointwise Young inequality for the commutator term against an arbitrary vector `ℓ`. -/
theorem sb1_young_gen [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ δ : ℝ} (hθ : 0 < θ)
    (hδ : 0 < δ) {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (ℓ : Fin N × Fin d → ℝ)
    (x : EucConfig d N) :
    ∑ k : Fin N × Fin d, (p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) * ℓ k ≤
      θ * δ * (p4Mol v ν x * ∑ k : Fin N × Fin d, ℓ k ^ 2) + p4m_T v ν b x / (4 * θ * δ) := by
  have hbc : Continuous b := hbl.continuous
  have hG := p4m_integrable_gauss_sub hv ν x (d := d) (N := N)
  have hc : ∀ k : Fin N × Fin d, Integrable (fun y => p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2)) ν := by
    intro k
    have h1 := p4m_integrable_hB hv hm hbc hB hK hbg k x
    have h2 : Integrable (fun y => p4Gauss d N v (x - y) * b x k.1 k.2) ν := hG.mul_const _
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  have e1 : ∑ k : Fin N × Fin d, (p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) * ℓ k =
      ∫ y, ∑ k : Fin N × Fin d, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) * ℓ k ∂ν := by
    rw [integral_finset_sum _ fun k _ => (hc k).mul_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← p4m_rk_eq hv hm hbc hB hK hbg k x, ← integral_mul_const]
  have hT := p4m_Tint_integrable hv hbl x (ν := ν)
  have e2 : θ * δ * (p4Mol v ν x * ∑ k : Fin N × Fin d, ℓ k ^ 2) + p4m_T v ν b x / (4 * θ * δ) =
      ∫ y, (p4Gauss d N v (x - y) * (θ * δ * ∑ k : Fin N × Fin d, ℓ k ^ 2) +
        (p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) / (4 * θ * δ)) ∂ν := by
    rw [integral_add (hG.mul_const _) (hT.div_const _), integral_mul_const, integral_div]
    unfold p4m_T p4Mol
    ring
  rw [e1, e2]
  refine integral_mono ?_ ?_ ?_
  · exact integrable_finset_sum _ fun k _ => (hc k).mul_const _
  · exact (hG.mul_const _).add (hT.div_const _)
  · intro y
    simp only
    have hGy := (p4m_gauss_pos (d := d) (N := N) hv (x - y)).le
    have hpt : ∀ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) * ℓ k ≤
        θ * δ * ℓ k ^ 2 + (b y k.1 k.2 - b x k.1 k.2) ^ 2 / (4 * θ * δ) := by
      intro k
      have hp : 0 < θ * δ := mul_pos hθ hδ
      have h4 : 0 < 4 * θ * δ := by positivity
      have : θ * δ * ℓ k ^ 2 + (b y k.1 k.2 - b x k.1 k.2) ^ 2 / (4 * θ * δ) -
          (b y k.1 k.2 - b x k.1 k.2) * ℓ k =
          θ * δ * (ℓ k - (b y k.1 k.2 - b x k.1 k.2) / (2 * θ * δ)) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg hp.le (sq_nonneg (ℓ k - (b y k.1 k.2 - b x k.1 k.2) / (2 * θ * δ)))]
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
    have h2 := mul_le_mul_of_nonneg_left hsum hGy
    have e3 : ∑ k : Fin N × Fin d, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) * ℓ k =
        p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) * ℓ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e3]
    refine h2.trans (le_of_eq ?_)
    ring

end

end HRS.MS.MfeConf
