import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.DECAux3
import HRS.Commutator.Whole.UREMAux1
import HRS.Commutator.Whole.ULOWAux1
import HRS.Commutator.Whole.UHIGHAux2
import HRS.Commutator.Whole.UHIGHAux4

/-!
# Sub-Coulomb commutator on `ℝ^d`: the estimate at unit scale (Section 5.1 of the note)

Source `[N]`: Section 5.1 (L640-728), `(5.unitestimate)` (L642-643).  Packets `CMX-DEC` (decomposition),
`CMX-REM` (Fourier remainder), `CMX-LOW` (low-frequency transport), `CMX-HIGH` (high-frequency transport).
The theorems `high_bound` and `unit_estimate` are *proved* from the statements of the pieces (they only
need the triangle inequality), which checks that the decomposition composes.

`Ec = F_N + C_p(1/N + ‖μ‖_{L^p})` is `unitE`; constants as in `Energy.lean` (`C` depends only on `d, s`,
chosen before `p`; `C_{p,0}` threshold after `p`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- `Ec = F_N(X_N, μ) + C_p(1/N + ‖μ‖_{L^p})` (`[N] (1.intro-control)` L182). -/
def unitE (s Cp : ℝ) (p : ℝ≥0∞) {N : ℕ} (X : Fin N → Euc d) (ρ : Euc d → ℝ) : ℝ :=
  modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)

/-- The identification `𝖠₁[X_N, μ, v] = 𝒞_g(v, ν)` (`[N] L233`: "in particular `𝒞_g(v,ν) = 𝖠₁`"):
the deleted-diagonal formula `(1.comm)` equals the iterated integral over the signed measure
`ν = μ_N - μ` (`∇g` is odd, so `commKer` is symmetric; the diagonal is null).  `v` Lipschitz,
`μ` bounded and compactly supported. -/
theorem commA_eq_Ccomm (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X)
    (v : Euc d → Euc d) (L : ℝ≥0) (hv : LipschitzWith L v) :
    commA s X ρ v = Ccomm (kernGrad s) v (chargeOf X ρ) := by
  have hG := DEC.full_good hd hs0 hsd hρ hv
  unfold commA Ccomm
  rw [DEC.pairGen_formula hρ hN X hG (fun x => DEC.dec_commKer_diag (kernGrad s) v x),
    DEC.pair2_formula hρ hN X hG]

/-- `(5.full-decomposition)` (`[N] L646-651`): `𝒞_g(v,ν) = 𝒞_{g_{>1}}(v,ν) + 𝒞_{g_{≤1}}(v_{≤1},ν) +
𝒞_{g_{≤1}}(v_{>1},ν)` (linearity in the force `∇g = ∇g_{≤1} + ∇g_{>1}` and in `v = v_{≤1} + v_{>1}`;
all terms absolutely convergent: Lemma 3.1 for `g_{>1}`, boundedness of `∇g_{≤1}` and `v_{>1}`). -/
theorem Ccomm_decomp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X)
    (v : Euc d → Euc d) (L : ℝ≥0) (hv : LipschitzWith L v) :
    Ccomm (kernGrad s) v (chargeOf X ρ) =
      Ccomm (ghiForce s) v (chargeOf X ρ) + Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ) +
        Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ) := by
  have hGg := DEC.ghi_good hd hs0 hsd hρ hv
  have hGq := DEC.glo_Pleq_good hd hs0 hsd hρ hv
  have hGp := DEC.gloPgt_good hd hs0 hsd hρ hv
  have hfun : commKer (kernGrad s) v = fun x y => commKer (ghiForce s) v x y +
      (commKer (gloForce s) (Pleq 1 v) x y + commKer (gloForce s) (Pgt 1 v) x y) := by
    funext x y
    rw [DEC.kernGrad_split v x y, DEC.dec_commKer_split (gloForce s) v x y]
  have key : Ccomm (kernGrad s) v (chargeOf X ρ) = (chargeOf X ρ).pair2
      (fun x y => commKer (ghiForce s) v x y +
        (commKer (gloForce s) (Pleq 1 v) x y + commKer (gloForce s) (Pgt 1 v) x y)) := by
    unfold Ccomm
    rw [hfun]
  rw [key]
  unfold Ccomm
  rw [DEC.pair2_add hρ hN X hGg (hGq.add hGp), DEC.pair2_add hρ hN X hGq hGp]
  ring

/-- The Fourier remainder `(5.remainderbound)` (`[N] L655-677`): `|𝒞_{g_{>1}}(v,ν)| ≲ C(v) Ec`.
Particle–particle `(5.remainder-particles)` by `|x||∇g_{>1}| ≲ f_1` (Lemma 3.1) and
`(2.energy-control)`; mixed `(5.remainder-mixed)` by Hölder with `‖f_1‖_{L^{p'}}‖μ‖_{L^p} ≤ Ec`
(`(2.Ecoercive)`); density–density `(5.remainder-density)` by Lemma 4.2 and `(2.backgroundH)`. -/
theorem remainder_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |Ccomm (ghiForce s) v (chargeOf X ρ)| ≤ C * K * unitE s Cp p X ρ :=
  UREM.urem_main hd hs0 hsd

/-- The low-frequency transport `(5.lowpartbound)` (`[N] L680-687`): `|𝒞_{g_{≤1}}(v_{≤1},ν)| ≲ C(v) Ec`,
from Lemma 4.1, `(3.Scoercive)` for `σ = ν` and `(2.energy-control)` (`= (1.intro-control)`). -/
theorem low_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)| ≤ C * K * unitE s Cp p X ρ :=
  ULOW.ulow_main hd hs0 hsd

/-- `(5.highidentity)` (`[N] L691-697`): with `u = ∇g_{≤1} * ν`,
`𝒞_{g_{≤1}}(v_{>1},ν) = (2/N) ∑_i v_{>1}(x_i)·u(x_i) - 2 ∫ μ v_{>1}·u`
(oddness and smoothness of the kernel; no self-interaction term as `∇g_{≤1}(0) = 0`). -/
theorem high_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X)
    (v : Euc d → Euc d) (L : ℝ≥0) (hv : LipschitzWith L v) :
    Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ) =
      (2 / (N : ℝ)) * ∑ i, inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i)) -
        2 * ∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x) := by
  have hfin := chargeOf_admissible ρ hρ hN X
  haveI : IsFiniteMeasure (chargeOf X ρ).pos := hfin.1.1
  haveI : IsFiniteMeasure (chargeOf X ρ).neg := hfin.1.2
  obtain ⟨C, hC, hvh⟩ := vhi_bounded (d := d) hd
  obtain ⟨hcont, -, hbdd⟩ := hvh v L hv
  obtain ⟨Bg, hBg⟩ := (gloForce_props hd hs0 hsd).2.2.2 0
  have hG : ∀ z, ‖gloForce s z‖ ≤ Bg := fun z => by
    have h := hBg z
    rwa [norm_iteratedFDeriv_zero] at h
  have hGm : Measurable (gloForce s : Euc d → Euc d) :=
    (gloForce_props hd hs0 hsd).1.continuous.measurable
  have hpair := DEC.pair2_odd (chargeOf X ρ) hGm (DEC.glo_odd hd hs0 hsd) Bg hG hcont.measurable
    (C * (L : ℝ)) hbdd
  have hU : StronglyMeasurable (fun x => (chargeOf X ρ).convForce (gloForce s) x) := by
    have hjoint : StronglyMeasurable (fun q : Euc d × Euc d => gloForce s (q.1 - q.2)) :=
      (hGm.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact (hjoint.integral_prod_right' (ν := (chargeOf X ρ).pos)).sub
      (hjoint.integral_prod_right' (ν := (chargeOf X ρ).neg))
  have hf : StronglyMeasurable (fun x => inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)) :=
    hcont.stronglyMeasurable.inner hU
  have hbf : ∀ x, ‖inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)‖ ≤
      (C * (L : ℝ)) * (Bg * ((chargeOf X ρ).pos.real Set.univ + (chargeOf X ρ).neg.real Set.univ)) :=
    fun x => (norm_inner_le_norm _ _).trans (mul_le_mul (hbdd x)
      (DEC.convForce_bound (chargeOf X ρ) hG x) (norm_nonneg _) (mul_nonneg hC.le L.coe_nonneg))
  have hfρ : Integrable (fun x => ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)) := by
    have h1 := (energyAux_bddCpt_integrable ρ hρ).1.bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ hbf)
    exact h1.congr (ae_of_all _ fun x => mul_comm _ _)
  have key : (chargeOf X ρ).int (fun x => inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)) =
      (1 / (N : ℝ)) * ∑ i, inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i)) -
        ∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x) :=
    energyAux_charge_int ρ hρ hN X _ hf hfρ
  unfold Ccomm
  rw [hpair]
  show 2 * (chargeOf X ρ).int (fun x => inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)) = _
  rw [key]
  ring

/-- The particle contribution `(5.atomicclosing)` (`[N] L699-714`): Hölder for sequences with
`1/2 + 1/p₁ + 1/p₂ = 1`:
`N⁻¹ ∑_i |v_{>1}(x_i)||u(x_i)| ≤ ∑_j n_j sup_{Q_j}|v_{>1}| sup_{Q_j}|u| ≤ (∑ n_j²)^{1/2}
(∑ sup|v_{>1}|^{p₁})^{1/p₁} (∑ sup|u|^{p₂})^{1/p₂} ≲ Ec^{1/2} ‖|∇|^α v‖_{p₁} ‖P_{≤4}ν‖_{Ḣ^{-α}} ≲ C(v) Ec`
by `(2.occupancy)`, `(3.zsample)`, `(3.usample)`, `(3.potentialSobolev)`, `(3.Scoercive)`. -/
theorem high_particles (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        (1 / (N : ℝ)) * ∑ i, |inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i))| ≤
          C * K * unitE s Cp p X ρ :=
  UHIGH.uhigh_particles_main hd hs0 hsd

/-- The background contribution `(5.backgroundclosing)` (`[N] L716-728`): Sobolev duality and
`(3.product)`: `|∫ μ v_{>1}·u| ≤ ‖μ‖_{H^{-α}} ‖v_{>1}·u‖_{H^α} ≲ ‖|∇|^α v‖_{p₁} ‖μ‖_{f_1} ‖ν‖_{g_1} ≲ C(v) Ec`
(`μ ∈ L²`, `v_{>1}·u ∈ H^α ⊂ L²`, so the duality pairing is the displayed integral). -/
theorem high_background (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)| ≤
          C * K * unitE s Cp p X ρ :=
  UHIGH.uhigh_background_main hd hs0 hsd

/-- The high-frequency transport: `|𝒞_{g_{≤1}}(v_{>1},ν)| ≲ C(v) Ec`, from `high_identity`,
`high_particles` and `high_background` (`[N] L690-728`). -/
theorem high_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ)| ≤ C * K * unitE s Cp p X ρ := by
  obtain ⟨C₁, hC₁, H₁⟩ := high_particles hd hs0 hsd
  obtain ⟨C₂, hC₂, H₂⟩ := high_background hd hs0 hsd
  refine ⟨2 * C₁ + 2 * C₂, by positivity, fun p q hp hpq => ?_⟩
  obtain ⟨c₁, hc₁, G₁⟩ := H₁ p q hp hpq
  obtain ⟨c₂, hc₂, G₂⟩ := H₂ p q hp hpq
  refine ⟨max c₁ c₂, lt_max_of_lt_left hc₁, fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  have hLip : ∃ L : ℝ≥0, LipschitzWith L v := by
    obtain ⟨L, F, -, hL, -, -⟩ := hv
    exact ⟨L, hL⟩
  obtain ⟨L, hL⟩ := hLip
  have e1 := G₁ Cp (le_trans (le_max_left _ _) hCp) ρ hρ N X hN hX v K hv
  have e2 := G₂ Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX v K hv
  rw [high_identity hd hs0 hsd ρ hρ hN X hX v L hL]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set A := ∑ i, inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i)) with hA
  set B := ∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x) with hB
  have hA' : |A| ≤ ∑ i, |inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i))| :=
    Finset.abs_sum_le_sum_abs _ _
  have h1 : |(2 / (N : ℝ)) * A| ≤ 2 * (C₁ * K * unitE s Cp p X ρ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / N)]
    calc 2 / (N : ℝ) * |A|
        ≤ 2 / (N : ℝ) * ∑ i, |inner ℝ (Pgt 1 v (X i))
            ((chargeOf X ρ).convForce (gloForce s) (X i))| :=
          mul_le_mul_of_nonneg_left hA' (by positivity)
      _ = 2 * ((1 / (N : ℝ)) * ∑ i, |inner ℝ (Pgt 1 v (X i))
            ((chargeOf X ρ).convForce (gloForce s) (X i))|) := by ring
      _ ≤ 2 * (C₁ * K * unitE s Cp p X ρ) := by gcongr
  have h2 : |2 * B| ≤ 2 * (C₂ * K * unitE s Cp p X ρ) := by
    rw [abs_mul, abs_two]
    linarith
  calc |(2 / (N : ℝ)) * A - 2 * B|
      ≤ |(2 / (N : ℝ)) * A| + |2 * B| := abs_sub _ _
    _ ≤ 2 * (C₁ * K * unitE s Cp p X ρ) + 2 * (C₂ * K * unitE s Cp p X ρ) := add_le_add h1 h2
    _ = (2 * C₁ + 2 * C₂) * K * unitE s Cp p X ρ := by ring

/-- The unit-scale estimate `(5.unitestimate)` (`[N] L641-643`): for `μ` bounded and compactly
supported, `|𝖠₁[X_N, μ, v]| ≲ C(v) Ec`, `C` depending only on `d, s`; `C_p` sufficiently large.
Proved from the decomposition and the three bounds `(5.remainderbound)`, `(5.lowpartbound)`,
`(5.highidentity)`-`(5.backgroundclosing)` (`[N] L728`: "Combining … proves `(5.unitestimate)`"). -/
theorem unit_estimate (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |commA s X ρ v| ≤ C * K * unitE s Cp p X ρ := by
  obtain ⟨C₁, hC₁, H₁⟩ := remainder_bound hd hs0 hsd
  obtain ⟨C₂, hC₂, H₂⟩ := low_bound hd hs0 hsd
  obtain ⟨C₃, hC₃, H₃⟩ := high_bound hd hs0 hsd
  refine ⟨C₁ + C₂ + C₃, by positivity, fun p q hp hpq => ?_⟩
  obtain ⟨c₁, hc₁, G₁⟩ := H₁ p q hp hpq
  obtain ⟨c₂, hc₂, G₂⟩ := H₂ p q hp hpq
  obtain ⟨c₃, hc₃, G₃⟩ := H₃ p q hp hpq
  refine ⟨max (max c₁ c₂) c₃, lt_max_of_lt_left (lt_max_of_lt_left hc₁), fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzWith L v := by
    obtain ⟨L, F, -, hL, -, -⟩ := hv
    exact ⟨L, hL⟩
  have e1 := G₁ Cp (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCp) ρ hρ N X hN hX v K hv
  have e2 := G₂ Cp (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCp) ρ hρ N X hN hX v K hv
  have e3 := G₃ Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX v K hv
  rw [commA_eq_Ccomm hd hs0 hsd ρ hρ hN X hX v L hL, Ccomm_decomp hd hs0 hsd ρ hρ hN X hX v L hL]
  calc |Ccomm (ghiForce s) v (chargeOf X ρ) + Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ) +
          Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ)|
      ≤ |Ccomm (ghiForce s) v (chargeOf X ρ) + Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)| +
          |Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ)| := abs_add_le _ _
    _ ≤ |Ccomm (ghiForce s) v (chargeOf X ρ)| + |Ccomm (gloForce s) (Pleq 1 v) (chargeOf X ρ)| +
          |Ccomm (gloForce s) (Pgt 1 v) (chargeOf X ρ)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ C₁ * K * unitE s Cp p X ρ + C₂ * K * unitE s Cp p X ρ + C₃ * K * unitE s Cp p X ρ := by
        gcongr
    _ = (C₁ + C₂ + C₃) * K * unitE s Cp p X ρ := by ring

end HRS.Commutator.Whole
