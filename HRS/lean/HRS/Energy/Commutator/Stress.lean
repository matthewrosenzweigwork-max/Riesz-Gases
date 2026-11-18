import HRS.Energy.Commutator.Smear
import HRS.Energy.Commutator.StressAux
import HRS.Energy.Commutator.EnergyAux
import HRS.Energy.Commutator.EnergyCoulomb
import HRS.Energy.Commutator.RoughFinal

/-!
# Route S, packet S3: Lipschitz-only commutator inequality for one slice (stress-energy tensor)

The mathematical core of the Lipschitz-only estimate: for `h` smooth on `T^d`, `l ≥ 0`,
`f = l h - Δh` and a Lipschitz field `v` with constant `L`,
```
∫ f v·∇h = -(l/2) ∫ div v h² + ∫ ∂_i v_j ∂_i h ∂_j h - ½ ∫ div v |∇h|²      (stress tensor)
```
so `|∫ f v·∇h| ≤ C_d L ∫ (l h² + |∇h|²)` = `C_d L ⟨f, G_l f⟩`.  This is `[RS] Prop. 3.2 / (3.25)` with
the weight `|z|^γ` replaced by the slice parameter `l`; for the Coulomb slice `l = 0` it is the
classical `[LS18]`/`[Ser20]` identity.  It requires no integration by parts on singular sets: `h` is
smooth, `v` Lipschitz is handled by mollifying `v` (`‖∇(v*ψ_ε)‖_∞ ≤ L`, uniform convergence) or by
Rademacher.  `stress_rough` then passes to the rough charges `σ_{l,η}` by mollification of the charges
(`∇h_ε → ∇h` in `L²`; the pairing converges by dominated convergence, `|k_l(x,y)| ≲ L G_l(x-y)`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d N : ℕ}

/-- The Hoeffding-type quadratic form `∬ K d(ν-μ)^{⊗2}` written with its three terms. -/
def quadForm (K : Torus d → Torus d → ℝ) (ν μ : Measure (Torus d)) : ℝ :=
  ∫ x, ∫ y, K x y ∂ν ∂ν - 2 * ∫ x, ∫ y, K x y ∂μ ∂ν + ∫ x, ∫ y, K x y ∂μ ∂μ

/-- The charge `N⁻¹ ∑_i σ(η_i)(· - x_i)` of smeared particles (`σ` is a family of charges centred
at the origin: `smearT d l` for the slice `l > 0`, `sphereT d` for the Coulomb slice). -/
def chargeMeasure (σ : ℝ → Measure (Torus d)) (η : Fin N → ℝ) (X : Config d N) : Measure (Torus d) :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, (σ (η i)).map (fun y => y + X i)

/-- **S3.1 (regular stress inequality).**  `C = C(d)` independent of `l ≥ 0`, `h`, `v`, `L`.
Quantified over *all* `C²` functions `h` on the torus (no mean condition: for `l > 0` the zero
mode contributes `l ∫ h² / ...` consistently, for `l = 0` it drops from both sides). -/
theorem stress_regular (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, 0 ≤ l → ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ h : Torus d → ℝ, Torus.IsCk 2 h →
        |∫ x, (l * h x - Torus.laplacian h x) * inner ℝ (v x) (Torus.grad h x)| ≤
          C * L * ∫ x, (l * h x ^ 2 + ‖Torus.grad h x‖ ^ 2) := by
  refine ⟨2 * d + 1, by positivity, fun l hl L v hL hv h hh => ?_⟩
  exact StressAux.stress_bound d hl hL hv hh

/-- **S3.2 (stress inequality for rough charges).**  For finite measures `ν, μ` such that the
`G_l`-energy of `ν + μ` is finite (so that the commutator kernel `|k_l| ≲ L G_l + L` is integrable
for `(ν+μ)^{⊗2}`; for `l = 0` the charges must be neutral, `ν(1) = μ(1)`):
`|∬ k_l d(ν-μ)^{⊗2}| ≤ C L ∬ G_l d(ν-μ)^{⊗2}`, with the force `k_l(x,y) = (v(x)-v(y))·∇𝒢_l(x-y)`
(`0` on the diagonal).  Same `C` as in S3.1 up to a dimensional factor.
**No atoms for `d ≥ 2`** (hypothesis `2 ≤ d → ν, μ` atomless): `sliceG d l 0` is a non-integrable Bochner
integral, i.e. the junk value `0`, so `sliceGfull d l 0 = 1/l`; with `ν = δ_a`, `μ = δ_b` the diagonal junk
would make the statement false.  Atomless charges make the diagonal `ν⊗ν`-, `μ⊗μ`-, `ν⊗μ`-null; the charges of
S4 (`smearT`, `sphereT` for `d ≥ 2`, `withDensityReal ρ`, convex combinations) are atomless. -/
theorem stress_rough (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, 0 ≤ l → ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ ν μ : Measure (Torus d), IsFiniteMeasure ν → IsFiniteMeasure μ →
        (l = 0 → ν Set.univ = μ Set.univ) →
        (2 ≤ d → (∀ x, ν {x} = 0) ∧ ∀ x, μ {x} = 0) →
        Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2))
          ((ν + μ).prod (ν + μ)) →
        |quadForm (fun x y => commKernel (sliceGrad d l) v x y) ν μ| ≤
          C * L * quadForm (fun x y => sliceGfull d l (x - y)) ν μ := by
  refine ⟨2 * (2 * d + 1), by positivity, fun l hl L v hL hv ν μ hν hμ hneut hatom hint => ?_⟩
  haveI := hν
  haveI := hμ
  unfold quadForm
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨h1, h2⟩ := RoughFinal.d0_case hl v ν μ
    rw [h1, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hL) h2
  · exact RoughFinal.core_pos hd hl hL hv ν μ hneut hatom hint

/-- **S3.3 (exact energy identity for smeared particles, slice `l > 0`).**  If the balls
`B(x_i,η_i)` are pairwise disjoint (`η_i + η_j < tdist(x_i,x_j)`), `0 < η_i < 1/2`, then
```
E_l(ν,μ) := quadForm G_l ν μ
 = N⁻² ∑_{i≠j} G_l(x_i-x_j) + N⁻² ∑_i S_l(η_i) - 2N⁻¹ ∑_i ∫ (G_l(x_i - y) - f_{l,η_i}(x_i - y)) dμ(y)
   + ∬ G_l dμ dμ ,       S_l(η) := ∬ G_l(x-y) dσ_{l,η}(x) dσ_{l,η}(y),
```
(`ν = chargeMeasure (smearT d l) η X`).  Pair terms are *exactly* the point interactions (S2.2 and
`fTrunc_support`), the self term is the energy of one charge, the cross term uses S2.2 once more.
This is `[RS] Prop. 2.1 / (2.19)` slice by slice. -/
theorem energy_identity_slice (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] (hμ0 : ∀ x, μ {x} = 0)
    (hμ1 : ∀ x, Integrable (fun y => sliceGfull d l (x - y)) μ)
    (hμ2 : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (μ.prod μ))
    (X : Config d N) (η : Fin N → ℝ) (hη : ∀ i, 0 < η i ∧ η i < 1 / 2)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) :
    quadForm (fun x y => sliceGfull d l (x - y)) (chargeMeasure (smearT d l) η X) μ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, sliceGfull d l (X i - X j)
      + (1 / (N : ℝ) ^ 2) * ∑ i, ∫ x, ∫ y, sliceGfull d l (x - y) ∂(smearT d l (η i)) ∂(smearT d l (η i))
      - (2 / (N : ℝ)) * ∑ i, ∫ y, (sliceGfull d l (X i - y) - fTrunc d l (η i) (X i - y)) ∂μ
      + ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂μ := by
  unfold quadForm chargeMeasure
  exact EnergyAux.energy_identity_slice_aux hd hl μ hμ0 hμ1 X η hη hdisj _ rfl

/-- **S3.3' (the same for the Coulomb slice `l = 0`, `d ≥ 2`; neutral charges).**  Each pair
carries the additive constant `κ_i + κ_j`, `κ = η²/(2d)` (S2.4), and each cross term the constant
`κ_i`; all are `O(η²) = O(Λ λ^{2})` for `η ≤ λ`. -/
theorem energy_identity_coulomb (hd : 2 ≤ d) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (hμ0 : ∀ x, μ {x} = 0) (hμ1 : ∀ x, Integrable (fun y => sliceG d 0 (x - y)) μ)
    (hμ2 : Integrable (fun p : Torus d × Torus d => sliceG d 0 (p.1 - p.2)) (μ.prod μ))
    (X : Config d N) (η : Fin N → ℝ) (hη : ∀ i, 0 < η i ∧ η i < 1 / 2)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) :
    quadForm (fun x y => sliceG d 0 (x - y)) (chargeMeasure (sphereT d) η X) μ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (sliceG d 0 (X i - X j) + η i ^ 2 / (2 * d) + η j ^ 2 / (2 * d))
      + (1 / (N : ℝ) ^ 2) * ∑ i, ∫ x, ∫ y, sliceG d 0 (x - y) ∂(sphereT d (η i)) ∂(sphereT d (η i))
      - (2 / (N : ℝ)) * ∑ i, ∫ y, (sliceG d 0 (X i - y) - fTrunc0 d (η i) (X i - y) + η i ^ 2 / (2 * d)) ∂μ
      + ∫ x, ∫ y, sliceG d 0 (x - y) ∂μ ∂μ := by
  unfold quadForm chargeMeasure
  exact EnergyAux.energy_identity_coulomb_aux hd μ hμ0 hμ1 X η hη hdisj _ rfl

end HRS.Commutator
