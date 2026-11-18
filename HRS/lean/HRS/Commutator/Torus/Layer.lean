import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.TPOSAux16
import HRS.Commutator.Torus.TENAux2
import HRS.Commutator.Torus.TENAux4
import HRS.Commutator.Torus.TEN2Aux11
import HRS.Commutator.Torus.TKRAux13
import HRS.Commutator.Torus.TSAMPAux7
import HRS.Commutator.Torus.TSAMPAux10
import HRS.Commutator.Torus.TSAMPAux16
import HRS.Commutator.Torus.TSAMPAux30
import HRS.Commutator.Torus.TSAMPAux34
import HRS.Commutator.Torus.TPRODAux4

/-!
# Torus sub-Coulomb commutator: the lemma layer (torus versions of Sections 2-4 of the note)

Each statement is the torus analogue of an `ℝ^d` statement of `HRS/Commutator/Whole/*` (cited in the docstring),
written in the original variables of `𝕋^d` (period 1) at scale `η`, via the dictionary of `Defs.lean`
(`x̃ = x/η`, `ξ = ηk`).  Standing assumptions: `d ≥ 3`, `0 ≤ s < d-2`; exponents `α = Whole.alphaE d s`,
`p₁ = Whole.p1E d s`, `p₂ = Whole.p2E d s`.  Constants depend only on `d, s` (and `p`).  Packets `T-POS`, `T-EN`,
`T-KR`, `T-SAMP`, `T-PROD`, `T-LOWV`, `T-INHOM`.

Torus-specific features: the zero mode (`g_η^𝕋`, `f_η^𝕋` are mean-free, `ρ̂(0) = 1` enters `H^{-α}`; absorbed
because `‖μ‖_p ≥ 1`), periodisation of the kernels, finitely many cells, and the restriction `η ≤ η₀(d,s)` where the
periodised truncation separates scales (`η^d ≪ 1`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s : ℝ}

/-- Data of Lemma 3.2 on the torus: `v` is `L`-Lipschitz (`IsLipschitzVF`), `w` represents `|∇|^α v`
(`IsFracDeriv`, zero mode removed) and `‖|w|‖_{L^{p₁}(𝕋^d)} ≤ F`. -/
structure HasFracDataT (d : ℕ) (s : ℝ) (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d) (F : ℝ) :
    Prop where
  nonneg : 0 ≤ L ∧ 0 ≤ F
  lip : IsLipschitzVF L v
  rep : IsFracDeriv (Whole.alphaE d s) v w
  norm : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ ENNReal.ofReal F

/-! ### T-POS: the periodised positive truncation (Lemma 2.1) -/

/-- Fourier coefficients of the truncations (Poisson summation: the `k`-th coefficient of the periodisation of
`f_η ∈ L¹` is `f̂_η(k)`; `periodicRiesz` has coefficient `rieszCoeff`; both mean-free): `fcoef f_η^𝕋 (k) =
tScale·f̂_η(k)` (`k ≠ 0`), `fcoef g_η^𝕋 (k) = gTcoef k`; `gTorus0 = g_η^𝕋(0)` is the (absolutely
convergent) sum of the coefficients and `g_η^𝕋` is continuous.  Torus analogue of `[N] (2.fourierpositive)`. -/
theorem tr_coef_formula (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) :
    (∀ k : Lattice d, Torus.fcoef (fTorus s η : Torus d → ℝ) k =
        (((if k = 0 then 0 else tScale s * fHatEta d s η (Lattice.toEuc k) : ℝ)) : ℂ)) ∧
      (∀ k : Lattice d, Torus.fcoef (gTorus s η : Torus d → ℝ) k = ((gTcoef d s η k : ℝ) : ℂ)) ∧
      Summable (fun k : Lattice d => |gTcoef d s η k|) ∧ Continuous (Torus.lift (gTorus s η : Torus d → ℝ)) := by
  exact tpos_coef_formula hd hs0 hsd η hη

/-- Coefficient bounds (torus analogue of `(2.lowcoercive)`, `(2.shortcoercive)`, `g1Hat ≥ 0`; scaling
`ĝ_η(k) = η^{d-s}ĝ_1(ηk)`): for `0 < η ≤ 1`, `k ≠ 0`:
`gTcoef ≥ 0`; `η|k| ≤ 8 ⇒ gTcoef ≥ c (2π|k|)^{-(d-s)}`; `tScale·f̂_η(k) ≥ c η^{d-s}(1+4π²η²|k|²)^{-α}`. -/
theorem tr_coef_bounds (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ k : Lattice d, k ≠ 0 →
      0 ≤ gTcoef d s η k ∧
      (η * Lattice.enorm k ≤ 8 → c * (2 * Real.pi * Lattice.enorm k) ^ (-((d : ℝ) - s)) ≤ gTcoef d s η k) ∧
      c * η ^ ((d : ℝ) - s) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) ≤
        tScale s * fHatEta d s η (Lattice.toEuc k) := by
  exact tpos_coef_bounds hd hs0 hsd

/-- Value of the kernel at the origin, `g_η^𝕋(0) = η^{-s} g̃_1^R(0)`: `|g_η^𝕋(0)| ≤ Cη^{-s}` for `s > 0`,
`|g_η^𝕋(0) + log η| ≤ C` for `s = 0` (the `log R` of the lattice sum `R^{-d}∑ĝ_1(ξ)`). -/
theorem tr_g_zero (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      (0 < s → |gTorus0 d s η| ≤ C * η ^ (-s)) ∧ (s = 0 → |gTorus0 d s η + Real.log η| ≤ C) := by
  exact tpos_g_zero hd hs0 hsd

/-- Near-diagonal lower bound of `f_η^𝕋` (torus analogue of `(2.fcomparison)`/`fTrunc_lower_near`; the mean
correction costs `Cη^{d-s}`, absorbed for `η ≤ η₀`): `c η^{-s} ≤ f_η^𝕋(x)` for `0 < |x| ≤ 2η√d` (the diameter of a cell of side `<2η`). -/
theorem tr_f_lower_near (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ c : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < c ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * η * Real.sqrt d → c * η ^ (-s) ≤ fTorus s η x := by
  exact tpos_f_lower_near hd hs0 hsd

/-! ### T-EN: energy control (Lemma 2.2) -/

/-- The energy identity `(2.energyidentity)` on the torus (exact, any `η > 0`):
`‖ν‖²_{g_η} + N⁻²∑_{i≠j}f_η(x_i-x_j) + ‖μ‖²_{f_η} = 2F_N + g_η(0)/N + (2/N)∑_i (f_η*μ)(x_i)`. -/
theorem energy_identity_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (hX : X ∉ collisionSet d N) :
    kerEnergyT (gTorus s η) (chargeT X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
        ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y =
      2 * modEnergyT s X ρ + gTorus0 d s η / (N : ℝ) +
        (2 / (N : ℝ)) * ∑ i, ∫ y, fTorus s η (X i - y) * ρ y := by
  exact ten2_energy_identity hd hs0 hsd η hη ρ hρ hN X hX

/-- Lemma 2.2 on the torus, in original variables (`Ẽ = η^s Q_η`): for `C_p ≥ C_{p,0}(p)` and `η ≤ η₀`,
`Q_η = scaleQT s C_p p η X ρ` satisfies
(a) `(2.Ecoercive)`: `η^{-s}/N + ‖μ‖_p η^{d(1-1/p)-s} ≤ Q_η` (so `Q_η ≥ 0`);
(b) `(2.energy-control)`: `‖ν‖²_{g_η} + N⁻²∑f_η + ‖μ‖²_{f_η} ≤ 2Q_η`;
(c) `(2.backgroundH)`: `η^{-s}·η^d∑_k(1+4π²η²|k|²)^{-α}|ρ̂(k)|² ≤ C_b Q_η` (zero mode absorbed by (a), `‖μ‖_p ≥ 1`);
(d) `(2.occupancy)`: `∑_j n_j² ≤ C_b η^s Q_η` (cells of side `≈ η`, `n_j = μ_N(Q_j)`). -/
theorem energy_control_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cb η₀ : ℝ, 0 < Cb ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
        η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤
            scaleQT s Cp p η X ρ ∧
        kerEnergyT (gTorus s η) (chargeT X ρ) +
            (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
            ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y ≤ 2 * scaleQT s Cp p η X ρ ∧
        ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef ρ k) ≤
          ENNReal.ofReal (Cb * scaleQT s Cp p η X ρ) ∧
        ∑ j : Fin d → Fin (nCells η), occT η X j ^ 2 ≤ Cb * η ^ s * scaleQT s Cp p η X ρ := by
  exact ten2_energy_control hd hs0 hsd

/-- `(3.Scoercive)` on the torus (`‖P_{≤4}σ‖²_{Ḣ^{-α}} + ‖P_{≤4}σ‖²_{L²} ≲ ‖σ‖²_{g_η}`, from `tr_coef_bounds`;
unit norms are `η^s·` resp. `η^d·` the sums below): for a finite signed measure `σ` of mass zero. -/
theorem scoercive_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ σ : SMT d, σ.IsFinite → σ.mass = 0 →
      homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) +
          ENNReal.ofReal (η ^ ((d : ℝ) - s)) * ∑' k : Lattice d, ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 ≤
        ENNReal.ofReal (C * kerEnergyT (gTorus s η) σ) := by
  obtain ⟨c0, hc0, hcb⟩ := tr_coef_bounds hd hs0 hsd
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hds : 0 < (d : ℝ) - s := by linarith
  refine ⟨(1 + (16 * Real.pi) ^ ((d : ℝ) - s)) / c0, ?_, fun η hη hη1 σ hσ hm => ?_⟩
  · have : 0 < (16 * Real.pi) ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  obtain ⟨-, hcoef, hsumm, hlift⟩ := tr_coef_formula hd hs0 hsd η hη hη1
  have hg : Continuous (gTorus s η) := HRS.Torus.continuous_of_continuous_lift hlift
  have hcnn : ∀ k, 0 ≤ gTcoef d s η k := fun k => by
    by_cases hk : k = 0
    · simp [gTcoef, hk]
    · exact (hcb η hη hη1 k hk).1
  have hcb' : ∀ k : Lattice d, k ≠ 0 → η * Lattice.enorm k ≤ 8 →
      c0 * (2 * Real.pi * Lattice.enorm k) ^ (-((d : ℝ) - s)) ≤ gTcoef d s η k :=
    fun k hk h8 => (hcb η hη hη1 k hk).2.1 h8
  exact ten_scoercive_core hds hη hη1 σ hσ hm hg hsumm hcoef hcnn c0 hc0 hcb'

/-! ### T-KR: Lemma 3.1 -/

/-- Lemma 3.1 on the torus (`|x||∇g_{>1}| ≲ f_1`, scale `η`): `|x|_𝕋 |∇g_η^{>}(x)| ≤ C·tScale·perio(f_η)(x)` (positive
periodised truncation, no mean correction), `0 < |x| `. -/
theorem kernel_remainder_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ ≤ C * tScale s * perio (Whole.fTrunc s η) x := by
  exact tkr_kernel_remainder hd hs0 hsd

/-- Lemma 3.1, "Consequently": `W = |x||∇g_{>}|` is in `L^q(𝕋^d)`, `p⁻¹+q⁻¹=1`, `p > d/(d-s)`, with
`‖W‖_q ≤ C η^{d/q - s}` (unit norm `≲ 1`). -/
theorem kernel_remainder_Lq_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      MemLp (fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖) q volume ∧
        eLpNorm (fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖) q volume ≤
          ENNReal.ofReal (C * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) := by
  exact tkr_kernel_remainder_Lq hd hs0 hsd p q hp hpq

/-! ### T-SAMP: Lemma 3.2 -/

/-- `(3.zhigh)` first estimate: `C(P^η_≤ v) ≲ C(v)` (`TorusSubTransport`), uniformly in `η ∈ (0,1]`. -/
theorem vlo_bound_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → TorusSubTransport d s (PleqT η v) (C * K) := by
  exact tsamp_vlo_core hd hs0 hsd

/-- `(3.zhigh)` second estimate at scale `η` (unit: `‖⟨∇⟩^α ṽ_{>1}‖_{p₁} + ‖ṽ_{>1}‖_{p₁} ≲ ‖|∇|^α v‖_{p₁}`,
`ṽ_{>1} = η^{-1}v_{>}(η·)`, `α = 1 + d/p₁`): `‖⟨∇⟩_η^α v_{>}‖_{p₁} + ‖v_{>}‖_{p₁} ≲ η^α F`. -/
theorem vhi_Lp_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d)
      (F : ℝ), HasFracDataT d s v L w F →
      ∃ W : Torus d → Euc d,
        (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => PgtT η v x i) (fun x => W x i)) ∧
        eLpNorm (fun x => ‖W x‖) (ENNReal.ofReal (Whole.p1E d s)) volume +
            eLpNorm (fun x => ‖PgtT η v x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤
          ENNReal.ofReal (C * η ^ (Whole.alphaE d s) * F) := by
  obtain ⟨C, hC, h⟩ := tsamp_vhi_Lp_core hd hs0 hsd
  refine ⟨C, hC, fun η hη hη1 v L w F hF => ?_⟩
  obtain ⟨⟨hL, hF0⟩, hlip, hrep, hnorm⟩ := hF
  exact h η hη hη1 v L w F hF0 hL hlip hrep hnorm

/-- `(3.high-continuous)` on the torus: `v_{>}` is continuous with `‖v_{>}‖_∞ ≲ η L` (unit: `≲ ‖∇v‖_∞`). -/
theorem vhi_bounded_T (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L →
      IsLipschitzVF L v → Continuous (PgtT η v) ∧ ∀ x, ‖PgtT η v x‖ ≤ C * η * L := by
  exact tsamp_vhi_bounded_core (by omega)

/-- `(3.zsample)` at scale `η` (unit: `(∑_j sup_{Q_j}|ṽ_{>1}|^{p₁})^{1/p₁} ≲ ‖|∇|^αv‖_{p₁}`, `ṽ_{>1} = η^{-1}v_>(η·)`):
`(∑_j sup_{Q_j}|v_>|^{p₁})^{1/p₁} ≲ η F` over the `≈ η^{-d}` cells. -/
theorem vhi_cell_sampling_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d)
      (F : ℝ), HasFracDataT d s v L w F →
        cellSupNorm η (Whole.p1E d s) (PgtT η v) ≤ ENNReal.ofReal (C * η * F) := by
  obtain ⟨C, hC, h⟩ := tsamp_vhi_cell_core hd hs0 hsd
  refine ⟨C, hC, fun η hη hη1 v L w F hF => ?_⟩
  obtain ⟨⟨hL, hF0⟩, hlip, hrep, hnorm⟩ := hF
  exact h η hη hη1 v L w F hF0 hL hlip hrep hnorm

/-- `(3.usample)` at scale `η` (unit-scale `u` with `supp û ⊂ B(0,2)` is `η|k| ≤ 2`; `u` continuous): `‖⟨∇⟩_η^αu‖_{p₂} ≲
‖u‖_{p₂}` and `(∑_j sup_{Q_j}|u|^{p₂})^{1/p₂} ≲ η^{-d/p₂}‖u‖_{p₂}`. -/
theorem usample_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : Torus d → Euc d, Continuous u →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume →
      (∀ i (k : Lattice d), 2 < η * Lattice.enorm k → Torus.fcoef (fun x => u x i) k = 0) →
      ∃ U : Torus d → Euc d,
        (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => u x i) (fun x => U x i)) ∧
        eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
          ENNReal.ofReal C * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ∧
        cellSupNorm η (Whole.p2E d s) u ≤
          ENNReal.ofReal (C * η ^ (-(d : ℝ) / Whole.p2E d s)) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
  exact tsamp_usample_core hd hs0 hsd

/-- `(3.potentialSobolev)` on the torus (unit: `‖∇̃g̃_{≤1}*ν̃‖_{p₂} ≲ ‖P_{≤4}ν̃‖_{Ḣ^{-α}}`; the powers of `η` cancel):
`‖∇g^𝕋_{≤} * σ‖_{L^{p₂}(𝕋^d)} ≲ (∑_{k≠0}(2π|k|)^{-2α}χ(ηk/4)²|σ̂(k)|²)^{1/2}` (torus Sobolev embedding for mean-free
functions, uniform in the scale). -/
theorem potential_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ σ : SMT d, σ.IsFinite →
      eLpNorm (fun x => ‖σ.convForce (gloForceT s η) x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
        ENNReal.ofReal C * (homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)) ^ ((1 : ℝ) / 2) := by
  exact tsamp_potential_core hd hs0 hsd

/-! ### T-PROD -/

/-- `(3.product)` on the torus (unit: `‖ṽ_{>1}·ũ‖_{H^α(𝕋_R)} ≲ ‖|∇|^αv‖_{p₁}‖ũ‖_{p₂}`; `h̃ = η^{-1}h(η·)` is a *function*, so its coefficients are
`η^{-1-d}ĥ(k)` and `‖h̃‖²_{H^α(𝕋_R)} = η^{-2-2d}·sobSqT η α ĥ` (for densities the factor would be `η^d`);
`‖ũ‖_{p₂(𝕋_R)} = η^{-d/p₂}‖u‖_{p₂}`, `1+d-d/p₂ = d-s/2`): for `u` continuous, `L^{p₂}`, `η|k| ≤ 2`,
`MemLp h 2` and `(η^{s-2d}·sobSqT η α ĥ)^{1/2} ≤ C F ‖u‖_{p₂}`, `h = ⟨v_>, u⟩`. -/
theorem product_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d)
      (F : ℝ), HasFracDataT d s v L w F → ∀ u : Torus d → Euc d, Continuous u →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume →
      (∀ i (k : Lattice d), 2 < η * Lattice.enorm k → Torus.fcoef (fun x => u x i) k = 0) →
        MemLp (fun x => inner ℝ (PgtT η v x) (u x)) 2 volume ∧
        (ENNReal.ofReal (η ^ (s - 2 * (d : ℝ))) *
            sobSqT η (Whole.alphaE d s) (fun k => Torus.fcoef (fun x => inner ℝ (PgtT η v x) (u x)) k)) ^
            ((1 : ℝ) / 2) ≤
          ENNReal.ofReal (C * F) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
  obtain ⟨CL, hCL, hcore⟩ := tprod_core hd hs0 hsd
  obtain ⟨CV, hCV, hV⟩ := vhi_Lp_T hd hs0 hsd
  obtain ⟨Cb, hCb, hb⟩ := vhi_bounded_T hd
  obtain ⟨Cu, hCu, hu⟩ := usample_T hd hs0 hsd
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨d * CL * (1 + Cu) * CV, by positivity, ?_⟩
  intro η hη hη1 v L w F hF u huc hmem hsupp
  obtain ⟨W, hWrep, hWnorm⟩ := hV η hη hη1 v L w F hF
  obtain ⟨U, hUrep, hUnorm, -⟩ := hu η hη hη1 u huc hmem hsupp
  have hF0 : 0 ≤ F := hF.nonneg.2
  have hPc : Continuous (PgtT η v) := (hb η hη hη1 v L hF.nonneg.1 hF.lip).1
  obtain ⟨hm2, hbound⟩ := hcore η hη hη1 Cu hCu.le (PgtT η v) W u U
    (ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F))
    (eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume) hPc huc hWrep hUrep hsupp
    (le_trans le_self_add hWnorm) (le_trans le_add_self hWnorm) ENNReal.ofReal_ne_top le_rfl
    hmem.eLpNorm_lt_top.ne hUnorm
  refine ⟨hm2, ?_⟩
  set Nu := eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume with hNu
  set S := sobSqT η (Whole.alphaE d s)
    (fun k => Torus.fcoef (fun x => inner ℝ (PgtT η v x) (u x)) k) with hS
  have hα : Whole.alphaE d s = ((d : ℝ) - s) / 2 := rfl
  have hexp : η ^ ((s - 2 * (d : ℝ)) / 2) * η ^ ((d : ℝ) / 2) * η ^ (Whole.alphaE d s) = 1 := by
    rw [← Real.rpow_add hη, ← Real.rpow_add hη, hα]
    have : (s - 2 * (d : ℝ)) / 2 + (d : ℝ) / 2 + ((d : ℝ) - s) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  have hηa : 0 ≤ η ^ (Whole.alphaE d s) := Real.rpow_nonneg hη.le _
  have hηb : 0 ≤ η ^ ((d : ℝ) / 2) := Real.rpow_nonneg hη.le _
  have hηc : 0 ≤ η ^ ((s - 2 * (d : ℝ)) / 2) := Real.rpow_nonneg hη.le _
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hη.le _) (by norm_num),
    ← Real.rpow_mul hη.le]
  calc ENNReal.ofReal (η ^ ((s - 2 * (d : ℝ)) * (1 / 2))) * S ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (η ^ ((s - 2 * (d : ℝ)) * (1 / 2))) *
          (ENNReal.ofReal (η ^ ((d : ℝ) / 2)) *
            ((d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) *
              ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F) * Nu))) := by
        gcongr
    _ = ENNReal.ofReal (η ^ ((s - 2 * (d : ℝ)) / 2) * η ^ ((d : ℝ) / 2) * η ^ (Whole.alphaE d s)) *
          (ENNReal.ofReal (d * CL * (1 + Cu) * CV * F) * Nu) := by
        have e1 : (s - 2 * (d : ℝ)) * (1 / 2) = (s - 2 * (d : ℝ)) / 2 := by ring
        rw [e1]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_add (by norm_num) hCu.le, ENNReal.ofReal_one]
        ring
    _ = ENNReal.ofReal (d * CL * (1 + Cu) * CV * F) * Nu := by
        rw [hexp, ENNReal.ofReal_one, one_mul]

/-! ### T-LOWV, T-INHOM: Lemmas 4.1, 4.2 -/

/-- Lemma 4.1 on the torus (`𝒞̃ = η^s𝒞`, unit RHS `η^s·hom`): for a finite signed measure `σ`,
`|𝒞_{g_≤}(P^η_≤v, σ)| ≲ C(v)·∑_{k≠0}(2π|k|)^{-2α}χ(ηk/4)²|σ̂(k)|²`.  The mass-zero hypothesis is needed on the torus
(the zero mode is isolated: `v = sin(2πx₁)e₁`, `σ = (1+ε cos 2πx₁)dx` gives `-2πε ĝ(e₁)` against `O(ε²)`); all uses have `mass ν = 0`. -/
theorem low_velocity_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ σ : SMT d, σ.IsFinite → σ.mass = 0 →
        ENNReal.ofReal |CcommT (gloForceT s η) (PleqT η v) σ| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) := by
  sorry

/-- Lemma 4.2 on the torus (unit: `|𝒞̃_{g̃_{>1}}(ṽ,ã)| ≲ C(v)‖ã‖²_{H^{-α}(𝕋_R)}`; `‖ã‖² = η^d∑(1+4π²η²|k|²)^{-α}|â|²`,
`𝒞̃ = η^s𝒞`): `|𝒞_{g_>}(v,a)| ≲ C(v)·η^{-s}·sobSqT η (-α) â`, `a ∈ L²(𝕋^d)` real, no mass condition. -/
theorem inhomogeneous_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ a : Torus d → ℝ, MemLp a 2 volume →
        ENNReal.ofReal |CcommFunT (ghiForceT s η) v a| ≤
          ENNReal.ofReal (C * K) *
            (ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef a k)) := by
  sorry

end HRS.Commutator.TorusNote
