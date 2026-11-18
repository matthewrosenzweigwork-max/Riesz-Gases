import HRS.Equilibrium.Parametrix.Defs
import HRS.Equilibrium.Parametrix.PX1AuxTop
import HRS.Equilibrium.Parametrix.PX1AuxChart
import HRS.Equilibrium.Parametrix.PX1AuxMul
import HRS.Equilibrium.Parametrix.PX1AuxPartial
import HRS.Equilibrium.Parametrix.PX1AuxExtApply
import HRS.Equilibrium.Parametrix.PX2Aux
import HRS.Equilibrium.Parametrix.PX2AuxB
import HRS.Equilibrium.Parametrix.PX2AuxE
import HRS.Equilibrium.Parametrix.PX3bAux
import HRS.Equilibrium.Parametrix.PX7AuxE
import HRS.Equilibrium.Parametrix.PX3aAuxAA
import HRS.Equilibrium.Parametrix.PX4bAuxD
import HRS.Equilibrium.Parametrix.PX4bAuxI
import HRS.Equilibrium.Parametrix.PX4aAuxU
import HRS.Equilibrium.Parametrix.PX4bAuxK
import HRS.Equilibrium.Parametrix.PX4bAuxM

/-!
# Prop 4.13 (`pair_poisson`): the parametrix packets (statements) -- packet PARX-PLAN

Each theorem below is one proof packet of `docs/external/parametrix-plan.md`; all are `sorry`
except `ConormalL.mono` and `parxR_conormal` (which is a proved induction from two packets).
The statements are mathematically true as written (Lean junk values are controlled by
conormal membership: rows integrable, slices `C^m` off the diagonal).

Packets: PX1 calculus, PX2 kernel classes and the source `H_f`, PX3 Newton potential, PX4 defect
map / nonlocal estimates, PX5 iteration, PX6 the gap lemma (`parx_gap`) and the smoothness
bootstrap (`parx_psi_smooth`), PX7 the pair inverse at small differentiability.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-! ## PX1: calculus of conormal classes -/

/-- Monotonicity of the classes in `σ`, `b`, `m`, `B` (the weight is `≥ 1` and `r < r₀ < 1`). -/
theorem ConormalL.mono {σ σ' : ℝ} {b b' : ℕ → ℕ} {m m' : ℕ} {B B' : ℝ}
    {F : Torus d → Torus d → ℝ} (h : ConormalL σ b m B F) (hB0 : 0 ≤ B) (hσ : σ ≤ σ')
    (hb : ∀ c, b c ≤ b' c) (hm : m' ≤ m) (hB : B ≤ B') : ConormalL σ' b' m' B' F where
  smooth := h.smooth.of_le (by exact_mod_cast hm)
  near := by
    intro a c hac X z hz hzr
    refine (h.near a c (hac.trans hm) X z hz hzr).trans ?_
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hr1 : ‖z‖ ≤ 1 := by unfold r0 at hzr; linarith
    have h1 : ‖z‖ ^ (-(σ + c)) ≤ ‖z‖ ^ (-(σ' + c)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    have h2 : (1 + |Real.log ‖z‖|) ^ b c ≤ (1 + |Real.log ‖z‖|) ^ b' c :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log ‖z‖)]) (hb c)
    have hw : 0 ≤ 1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c := by positivity
    calc B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c)
        ≤ B' * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c) :=
          mul_le_mul_of_nonneg_right hB hw
      _ ≤ B' * (1 + ‖z‖ ^ (-(σ' + c)) * (1 + |Real.log ‖z‖|) ^ b' c) := by
          refine mul_le_mul_of_nonneg_left ?_ (hB0.trans hB)
          have h3 : 0 ≤ ‖z‖ ^ (-(σ + c)) := by positivity
          have h4 : 0 ≤ (1 + |Real.log ‖z‖|) ^ b c := by positivity
          have h5 := mul_le_mul h1 h2 h4 (by positivity)
          linarith
  far := fun k hk p hp hr => (h.far k (hk.trans hm) p hp hr).trans hB

/-- Sums (Lean: `mixedDeriv` is additive because both summands are `C^m` off the diagonal). -/
theorem ConormalL.add {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B B' : ℝ} {F G : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (hG : ConormalL σ b m B' G) :
    ConormalL σ b m (B + B') (fun x y => F x y + G x y) :=
  conormalL_add hF hG

/-- Real multiples. -/
theorem ConormalL.smul {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (a : ℝ) : ConormalL σ b m (|a| * B) (fun x y => a * F x y) :=
  conormalL_smul hF a

/-- Multiplication by a smooth kernel `a ∈ C^m(𝕋^d × 𝕋^d)` (coefficients `ρ`, `∇V`, `F_μ`, the
relative drift `b(X+z/2) - b(X-z/2)` of `Q:eq:relative-drift`, ...): the class is preserved with
the constant multiplied by `Cm * cbNorm2 m a` (Leibniz; the log index of the product at order `c` is `max_{c' ≤ c} b c'`, since the term `D^i a · D^{c-i} F` carries `b (c-i)`; `Cm` depends on `(σ, b)`; the chart `(X,z) ↦ (X+z/2, X-z/2)` has
norm `≤ 2`; `r^{-(σ+c-i)} ≤ r^{-(σ+c)}` for `r < 1`).  Multiplication by a smooth function
vanishing at `z = 0` (order lowering `σ ↦ σ - 1`) is part of `hsource_conormal`. -/
theorem conormal_mul_smooth (m : ℕ) (σ : ℝ) (b : ℕ → ℕ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (B : ℝ) (F a : Torus d → Torus d → ℝ),
      ConormalL σ b m B F → PDE.IsCk2 m a →
        ConormalL σ (fun c => (Finset.range (c + 1)).sup b) m (Cm * PDE.cbNorm2 m a * B)
          (fun x y => a x y * F x y) :=
  conormal_mul_smooth_aux m σ b

/-- Chart derivatives and torus derivatives: `∂_x = ½∂_X + ∂_z`, `∂_y = ½∂_X - ∂_z`.  If `F`
is in the class of order `σ`, then `x ↦ F(x, y)` (resp. `y ↦ F(x, y)`), differentiated `k` times,
is in the class of order `σ + k` with `m - k`; the log index at order `c` is `max (b c) (b (c+1))`, because
`∂_x = ½∂_X + ∂_z` moves one derivative from `(a,c)` to `(a+1,c)` or `(a,c+1)` (with a non-constant `b` the index is
not preserved: counterexample `d = 2`, `σ = -1`, `b 0 = 0`, `b 1 = 1`, `F = φ(z) z₁ log|z|`); stated for the first and second slice generator
`∇_x`, `∇_y` components (used for `∇_xψ`, `Q:eq:Vpair`, and the drift terms of `ℰ`). -/
theorem conormal_partial_fst {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (hm : 1 ≤ m) (j : Fin d) :
    ConormalL (σ + 1) (fun c => max (b c) (b (c + 1))) (m - 1) (2 * B)
      (fun x y => Torus.partialDeriv j (fun z => F z y) x) :=
  conormal_partial_fst_aux hF hm j

/-- Extension across the diagonal (`Q:eq:parametrix-telescope` and the sentence after it, source
line 4848: "derivatives through order eight extend continuously ... integration on short paths
avoiding zero"): if `σ + J + 1 < 0` and the class has `J + 1` derivatives, the kernel extends
(by `diagExt`) to a `C^J` kernel on `𝕋^d × 𝕋^d` with `cbNorm2 J ≤ C B`.  Needs `d ≥ 2` (the
diagonal has codimension `≥ 2`). -/
theorem conormal_extend (hd : 2 ≤ d) (J : ℕ) (σ : ℝ) (b : ℕ) (hσ : σ + ((J : ℝ) + 1) < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
      Conormal σ b (J + 1) B F →
        PDE.IsCk2 J (diagExt F) ∧ PDE.cbNorm2 J (diagExt F) ≤ C * B ∧
        ∀ x y, x ≠ y → diagExt F x y = F x y :=
  conormal_extend_aux hd J σ b hσ

/-! ## PX2: the kernel `g`, `∇g`, the source `H_f` -/

/-- `g(x - y)` is conormal of order `s` (`g = |z|^{-s} + smooth` near `0`,
`periodicRiesz_local_singularity`; `g` smooth off `0`). -/
theorem riesz_conormal (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ Conormal s 0 m C (fun x y => periodicRiesz d s (x - y)) := by
  have hs0 : 0 < s := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
    rw [H.crit]; linarith
  exact conormal_of_kerBound (kerBound_periodicRiesz H.two_le hs0 H.s_lt m)

/-- `∂_j g(x - y)` is conormal of order `s + 1` (`periodicRieszGrad_local_singularity`,
`periodicRieszGrad_smoothOffZero`). -/
theorem rieszGrad_conormal (H : ParxHyp d s V β ρ) (m : ℕ) (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ Conormal (s + 1) 0 m C (fun x y => periodicRieszGrad d s (x - y) j) := by
  have hs0 : 0 < s := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
    rw [H.crit]; linarith
  exact conormal_of_kerBound (kerBound_periodicRieszGrad H.two_le hs0 H.s_lt m j)

/-- `H_f` (`Q:eq:H-source`, `Q:eq:leading-diagonal`): the source is conormal of order `s` with
`m` conormal derivatives from `m + 2` derivatives of `f` (Taylor: `∇f(X+z/2) - ∇f(X-z/2) =
∫₀¹ D²f(X+(t-½)z) z dt`, times `∇g` of order `s+1`; the projections `P_xP_y` add smooth rows),
symmetric and doubly centred. -/
theorem hsource_conormal (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal s 0 m (C * posSeminorm (m + 2) f) (offZero (Hsource d s ρ f)) ∧
      IsSymmPair (Hsource d s ρ f) ∧
      PDE.DoublyCentered (withDensityReal ρ) (offZero (Hsource d s ρ f)) :=
  hsource_conormal_aux (fun σ b m B B' F G hF hG => ConormalL.add hF hG)
    (fun σ b m B F hF a => ConormalL.smul hF a) H m

/-- Rows of conormal kernels of order `< d` are smooth (differentiation under the integral after
`y' = x - z`; tangential derivatives are free): `x ↦ ∫ F(x, y') ρ(y') dy'` is `C^m` with norm
`≤ C B`.  Used by `hsource_conormal`, `newton_map` (canonical projection), `defect_map`. -/
theorem conormal_row_smooth (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, F x y ∂(withDensityReal ρ)) ≤ C * B :=
  conormal_row_smooth_aux H.two_le H.rho_smooth hσ b m

/-! ## PX3: the Newton potential `𝒩` (`Q:eq:Newton-map`, source lines 4811-4817) -/

/-- The mapping estimate.  For a symmetric kernel of class `(σ, b, m)` with `σ < d`, `𝒩F` has
class `σ - 2` with `m` derivatives; the logarithm power increases by one exactly at the resonant
`z`-derivative orders `c` with `σ - 2 + c = 0` (shell sum `∑_{R ∈ {2^n r} ∩ [r, r₀]} R^{2-σ-c}`),
except `c = 1` for a symmetric (= `z`-even) kernel: there `∇Γ(z - ·)` is odd, which kills the
leading term of the shell expansion (this replaces the spherical-harmonic computation of
`Q:eq:spherical-inverse`, source lines 4852-4862, and gives `|∇ψ| ≤ C` at `d = 2, s = 1`).
Proof: split `|z'| < r/2`, `|z - z'| < r/2`, dyadic shells; derivatives in `X` commute with the
integral; for `c ≥ 2` write `∂^c Γ * F = ∂²Γ * ∂^{c-2} F` with Taylor subtraction. -/
theorem newton_map (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F →
      Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) :=
  px3a_newton_map H.two_le H.rho_smooth H.beta_pos hσ b m

/-- The same without symmetry (log power `b + 1` at every resonance). -/
theorem newton_map_general (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
        (newtonOp d β ρ F) :=
  px3a_newton_map_general H.two_le H.rho_smooth H.beta_pos hσ b m

/-- `𝒩` is symmetric on symmetric kernels. -/
theorem newton_symm (F : Torus d → Torus d → ℝ) (hF : IsSymmPair F) :
    IsSymmPair (newtonOp d β ρ F) :=
  px3a_newton_symm F hF

/-- `𝒩F` is doubly centred (rows integrable by conormality, `σ < d`). -/
theorem newton_doublyCentered (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) :
    PDE.DoublyCentered (withDensityReal ρ) (newtonOp d β ρ F) :=
  px3a_newton_doublyCentered H.two_le H.rho_smooth H.beta_pos hσ hF

/-- `𝒩` is linear on a conormal class of order `< d` (integrals of integrable functions). -/
theorem newton_linear (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {B B' : ℝ}
    {F G : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) (hG : Conormal σ b m B' G)
    (a c : ℝ) :
    newtonOp d β ρ (fun x y => a * F x y + c * G x y) =
      fun x y => a * newtonOp d β ρ F x y + c * newtonOp d β ρ G x y :=
  px3a_newton_linear H.two_le H.rho_smooth H.beta_pos hσ hF hG a c

/-- Poisson equation for the local inverse (the cancellation "near zero, the normal Laplacian
cancels `F` in the defect", source line 4819): off the diagonal and for `|z| < 1/32`,
`-2ν Δ_z` of the chart function `newtonChart F` equals `F` (classical Newton-potential fact for a
source that is `C¹` near `z`; no such theory is in Mathlib: proof via Green's identity on
annuli or the mean-value characterisation of `Δ`). -/
theorem newtonChart_poisson (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ < d) {b : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hF : Conormal σ b 2 B F) (X z : Euc d) (hz0 : z ≠ 0)
    (hz : ‖z‖ < 1 / 32) :
    -(2 * β⁻¹) * Laplacian.laplacian (fun z' => newtonChart d β⁻¹ (toChart F) (X, z')) z =
      toChart F (X, z) :=
  newtonChart_poisson_aux H.two_le (inv_pos.mpr H.beta_pos) hσ hF X z hz0 hz

/-! ## PX4: the nonlocal estimate and the defect map -/

/-- The nonlocal term `J_x 𝒩 F` (`Q:eq:nonlocal-divergence`, `Q:eq:nonlocal-power`, source
lines 4822-4840): for a class of order `σ ≤ s`, the kernel `(x, y) ↦ J_x[𝒩F(·, y)](x)` has class
`σ - s` (the two singular powers `|x-u|^{-s}|u-y|^{-σ}`, `s + σ - d = σ - s`) with two fewer
derivatives and up to two extra logarithms.  Route: (i) `Jop` as the divergence form
`∫ g(x-u){ρ Δ_uΨ + ∇ρ·∇_uΨ}(u, y) du` (flux through `∂B_ε(y)` is `O(ε^{d-σ})`); (ii) two near
balls and dyadic shells with Taylor subtraction on shells larger than `|x - y|`
(`MFSchauder.KB` gives the torus convolution bounds). -/
theorem jop_map (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
      Conormal σ b m B F →
        Conormal (σ - s) (b + 2) (m - 2) (C * B)
          (offZero fun x y => Jop d s ρ (fun z => newtonOp d β ρ F z y) x) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  have hs0 : 0 < s := by rw [H.crit]; positivity
  have hσd : σ < d := lt_of_le_of_lt hσ H.s_lt
  obtain ⟨C1, hC10, hC1⟩ := newton_map_general H σ hσd b m
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C2, hC20, hC2⟩ := jop_engine (s := s) (ρ := ρ) H.two_le hs0 H.s_lt H.rho_smooth.smooth
    (τ := σ - 2) (by linarith) (b + 1) m'
  refine ⟨C2 * C1, mul_nonneg hC20 hC10, fun B F hB hF => ?_⟩
  have h1 := hC1 B F hB hF
  have h1' : ConormalL (σ - 2) (fun _ => b + 1) (m' + 2) (C1 * B)
      (newtonOp d β ρ F) :=
    ConormalL.mono h1 (mul_nonneg hC10 hB) le_rfl
      (fun c => by split_ifs <;> omega) le_rfl le_rfl
  have h2 := hC2 (C1 * B) (newtonOp d β ρ F) (mul_nonneg hC10 hB) h1'
  have e1 : σ - 2 + 2 + s - d = σ - s := by rw [H.crit] at *; ring
  have e2 : m' + 2 - 2 = m' := by omega
  rw [e1] at h2
  rw [e2]
  exact ConormalL.mono h2 (mul_nonneg hC20 (mul_nonneg hC10 hB)) le_rfl (fun c => by omega) le_rfl
    (le_of_eq (by ring))

/-- `ℰ` preserves symmetry (`𝒜_x + 𝒜_y` is swap-symmetric). -/
theorem defect_symm (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) {b m : ℕ} (hm : 2 ≤ m) {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hsym : IsSymmPair F) (hF : Conormal σ b m B F) :
    IsSymmPair (defectOp d s V β ρ F) := by
  have hN : IsSymmPair (newtonOp d β ρ F) := newton_symm F hsym
  intro x y
  by_cases hxy : x = y
  · subst hxy; rfl
  · have hyx : y ≠ x := fun h => hxy h.symm
    simp only [defectOp, if_neg hxy, if_neg hyx, genFst, genSnd]
    have h1 : (fun z => newtonOp d β ρ F z y) = fun z => newtonOp d β ρ F y z :=
      funext fun z => hN z y
    have h2 : (fun z => newtonOp d β ρ F x z) = fun z => newtonOp d β ρ F z x :=
      funext fun z => (hN z x).symm
    rw [hsym x y, h1, h2]
    ring

/-- Hidden obligation of `gen_add_smooth`/`gen_linear`/`Jpair`: the `J`-estimate for a *general* conormal
kernel (not only `𝒩F`).  For `σ + 2 < d`, `x ↦ Jop(F(·, y))(x)` is conormal of order `σ + 2 - s`
(divergence form `∫ g(x-u){ρΔ_uF + ∇ρ·∇_uF}(u,y)du`, source of order `σ + 2`, `s + σ + 2 - d`), so that
`projMean` in `Jpair` and in `projGen` integrates an `L¹` function (`σ + 2 - s < d`); log index `b + 2`.
Proof as `jop_map` (PX4a). -/
theorem jop_general (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ + 2 < d) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Conormal (σ + 2 - s) (b + 2) (m - 2) (C * B)
        (offZero fun x y => Jop d s ρ (fun z => F z y) x) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  have hs0 : 0 < s := by rw [H.crit]; positivity
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C2, hC20, hC2⟩ := jop_engine (s := s) (ρ := ρ) H.two_le hs0 H.s_lt H.rho_smooth.smooth
    (τ := σ) hσ b m'
  refine ⟨C2, hC20, fun B F hB hF => ?_⟩
  have h2 := hC2 B F hB hF
  have e1 : σ + 2 + s - d = σ + 2 - s := by rw [H.crit] at *; ring
  have e2 : m' + 2 - 2 = m' := by omega
  rw [e1] at h2
  rw [e2]
  exact ConormalL.mono h2 (mul_nonneg hC20 hB) le_rfl (fun c => by omega) le_rfl le_rfl

/-- Measurability: a kernel that is `C^m` on the open set `offDiag` and set to `0` on the closed diagonal
is jointly measurable (used for `ParxGapAt.measurable` and for every Bochner integral over kernels). -/
theorem conormal_measurable {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) : Measurable (Function.uncurry (offZero F)) :=
  measurable_offZero_of_contDiffOn hF.smooth

/-- (PX4b helper) Slices of conormal kernels are good for the generator (`Nice`, `Bop`, `Jop`
integrable); the `Jop` integrability is `jop_general`. -/
theorem px4b_good_conormal (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b m : ℕ}
    (hm : 2 ≤ m) {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) (y : Torus d) :
    Good d s V β ρ y (fun x => F x y) := by
  refine ⟨px4b_slice_nice H.two_le H.rho_smooth hσ hm hF y, px4b_Bop_int H hσ hm hF y, ?_⟩
  obtain ⟨C, hC0, hC⟩ := jop_general H σ hσ b m hm
  have hB := conormalL_B_nonneg H.two_le hF
  have hJ := hC B F hB hF
  have hlt : σ + 2 - s < d := by linarith [H.s_nonneg]
  have := px4b_slice_int H.two_le H.rho_smooth hlt hJ y
  refine this.congr ?_
  filter_upwards [px4b_ae_ne_mu (by have := H.two_le; omega) ρ y] with x hx
  simp [offZero, hx]

/-- The generators are additive on the sum of a conormal kernel and a `C²` kernel.  The hypothesis
`σ + 2 < d` is exactly what makes `Δ_x F` (order `σ + 2`), `∇F·F_μ` and `Jop F` (integrand of order
`σ + 1`) integrable, so that no Bochner junk enters `projMean`; slices are `C²` at `x ≠ y`. -/
theorem gen_add_smooth (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b m : ℕ} (hm : 2 ≤ m)
    {B : ℝ} {F Ψ : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) (hΨ : PDE.IsCk2 2 Ψ)
    (x y : Torus d) (hxy : x ≠ y) :
    genFst d s V β ρ (fun x y => F x y + Ψ x y) x y =
        genFst d s V β ρ F x y + genFst d s V β ρ Ψ x y ∧
      genSnd d s V β ρ (fun x y => F x y + Ψ x y) x y =
        genSnd d s V β ρ F x y + genSnd d s V β ρ Ψ x y ∧
      Jpair d s ρ (fun x y => F x y + Ψ x y) x y = Jpair d s ρ F x y + Jpair d s ρ Ψ x y := by
  have hF1 : Good d s V β ρ y (fun z => F z y) := px4b_good_conormal H hσ hm hF y
  have hF2 : Good d s V β ρ x (fun z => F x z) := px4b_good_conormal H hσ hm (conormalL_swap hF) x
  have hΨ1 : Good d s V β ρ y (fun z => Ψ z y) :=
    Good.of_smooth H (by exact_mod_cast PDE.MFPair.isCk_slice 2 Ψ hΨ y) y
  have hΨ2 : Good d s V β ρ x (fun z => Ψ x z) :=
    Good.of_smooth H (by exact_mod_cast PDE.MFPair.isCk_slice2 2 Ψ hΨ x) x
  have e1 := Good.projGen_lin H hxy hF1 hΨ1 1 1
  have e2 := Good.projGen_lin H hxy.symm hF2 hΨ2 1 1
  have e3 := Good.projJ_lin H hxy hF1 hΨ1 1 1
  have e4 := Good.projJ_lin H hxy.symm hF2 hΨ2 1 1
  simp only [one_mul] at e1 e2 e3 e4
  refine ⟨e1, e2, ?_⟩
  unfold Jpair
  rw [e3, e4]
  ring

/-- The same for a finite sum of conormal kernels (telescoping `Q:eq:parametrix-telescope`). -/
theorem gen_sum (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b m : ℕ} (hm : 2 ≤ m)
    (n : ℕ) (F : ℕ → Torus d → Torus d → ℝ) (hF : ∀ j < n, ∃ B : ℝ, Conormal σ b m B (F j))
    (x y : Torus d) (hxy : x ≠ y) :
    genFst d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y =
        ∑ j ∈ Finset.range n, genFst d s V β ρ (F j) x y ∧
      genSnd d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y =
        ∑ j ∈ Finset.range n, genSnd d s V β ρ (F j) x y := by
  have hzero : ∀ z : Torus d, Good d s V β ρ z (fun _ => (0 : ℝ)) := fun z =>
    Good.of_smooth H (show ContDiff ℝ 2 (Torus.lift fun _ : Torus d => (0 : ℝ)) from contDiff_const) z
  have key : ∀ n : ℕ, (∀ j < n, ∃ B : ℝ, Conormal σ b m B (F j)) →
      Good d s V β ρ y (fun z => ∑ j ∈ Finset.range n, F j z y) ∧
      Good d s V β ρ x (fun z => ∑ j ∈ Finset.range n, F j x z) ∧
      genFst d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y =
        ∑ j ∈ Finset.range n, genFst d s V β ρ (F j) x y ∧
      genSnd d s V β ρ (fun x y => ∑ j ∈ Finset.range n, F j x y) x y =
        ∑ j ∈ Finset.range n, genSnd d s V β ρ (F j) x y := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty]
      refine ⟨hzero y, hzero x, ?_, ?_⟩
      · have := Good.projGen_lin H hxy (hzero y) (hzero y) 1 (-1)
        simp at this
        simpa [genFst] using this
      · have := Good.projGen_lin H hxy.symm (hzero x) (hzero x) 1 (-1)
        simp at this
        simpa [genSnd] using this
    | succ n ih =>
      intro hFn
      obtain ⟨G1, G2, E1, E2⟩ := ih fun j hj => hFn j (Nat.lt_succ_of_lt hj)
      obtain ⟨B, hB⟩ := hFn n (Nat.lt_succ_self n)
      have hF1 : Good d s V β ρ y (fun z => F n z y) := px4b_good_conormal H hσ hm hB y
      have hF2 : Good d s V β ρ x (fun z => F n x z) :=
        px4b_good_conormal H hσ hm (conormalL_swap hB) x
      have eq1 : (fun z => ∑ j ∈ Finset.range (n + 1), F j z y) =
          fun w => 1 * (∑ j ∈ Finset.range n, F j w y) + 1 * F n w y := by
        funext w; rw [Finset.sum_range_succ]; ring
      have eq2 : (fun z => ∑ j ∈ Finset.range (n + 1), F j x z) =
          fun w => 1 * (∑ j ∈ Finset.range n, F j x w) + 1 * F n x w := by
        funext w; rw [Finset.sum_range_succ]; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eq1]; exact Good.lin H G1 hF1 1 1
      · rw [eq2]; exact Good.lin H G2 hF2 1 1
      · have := Good.projGen_lin H hxy G1 hF1 1 1
        simp only [genFst] at E1 ⊢
        rw [Finset.sum_range_succ, ← E1, eq1]
        simpa using this
      · have := Good.projGen_lin H hxy.symm G2 hF2 1 1
        simp only [genSnd] at E2 ⊢
        rw [Finset.sum_range_succ, ← E2, eq2]
        simpa using this
  obtain ⟨-, -, E1, E2⟩ := key n hF
  exact ⟨E1, E2⟩

/-- Linearity of the generators on conormal kernels (`σ + 2 < d`): `genFst`, `genSnd`, `Jpair` of
`a F + c G` at `x ≠ y` (all integrals converge absolutely, so no Bochner junk). -/
theorem gen_linear (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b m : ℕ} (hm : 2 ≤ m)
    {B B' : ℝ} {F G : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) (hG : Conormal σ b m B' G)
    (a c : ℝ) (x y : Torus d) (hxy : x ≠ y) :
    genFst d s V β ρ (fun x y => a * F x y + c * G x y) x y =
        a * genFst d s V β ρ F x y + c * genFst d s V β ρ G x y ∧
      genSnd d s V β ρ (fun x y => a * F x y + c * G x y) x y =
        a * genSnd d s V β ρ F x y + c * genSnd d s V β ρ G x y ∧
      Jpair d s ρ (fun x y => a * F x y + c * G x y) x y =
        a * Jpair d s ρ F x y + c * Jpair d s ρ G x y := by
  have hF1 : Good d s V β ρ y (fun z => F z y) := px4b_good_conormal H hσ hm hF y
  have hF2 : Good d s V β ρ x (fun z => F x z) := px4b_good_conormal H hσ hm (conormalL_swap hF) x
  have hG1 : Good d s V β ρ y (fun z => G z y) := px4b_good_conormal H hσ hm hG y
  have hG2 : Good d s V β ρ x (fun z => G x z) := px4b_good_conormal H hσ hm (conormalL_swap hG) x
  refine ⟨Good.projGen_lin H hxy hF1 hG1 a c, Good.projGen_lin H hxy.symm hF2 hG2 a c, ?_⟩
  unfold Jpair
  rw [Good.projJ_lin H hxy hF1 hG1 a c, Good.projJ_lin H hxy.symm hF2 hG2 a c]
  ring


/-- Commutation of `∫ · μ(dy)` with `𝒜_x` (no diagonal measure: `μ{x} = 0`, the slice `y ↦ F(x,y)` is
integrable by conormality, differentiation under the integral after `y = x - z`): if the rows of a
conormal kernel `F` (`σ + 2 < d`) have `μ`-mean zero, so do the rows of `𝒜_xF` and `𝒜_yF`; used in
`defect_doublyCentered`, `ParxGapAt.canonical`, `jpair_canonical`. -/
theorem gen_integral_comm (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b m : ℕ} (hm : 2 ≤ m)
    {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F)
    (hc : IsCanonicalPair (withDensityReal ρ) F) (x : Torus d) :
    Integrable (genFst d s V β ρ F x) (withDensityReal ρ) ∧
      ∫ y, genFst d s V β ρ F x y ∂(withDensityReal ρ) = 0 ∧
    Integrable (genSnd d s V β ρ F x) (withDensityReal ρ) ∧
      ∫ y, genSnd d s V β ρ F x y ∂(withDensityReal ρ) = 0 := by
  have hd := H.two_le
  have hρ := H.rho_smooth
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0 := fun x => (hc x).2
  -- joint integrability of the nonlocal kernel (`jop_general`)
  obtain ⟨C, hC0, hC⟩ := jop_general H σ hσ b m hm
  have hB := conormalL_B_nonneg hd hF
  have hJcl := hC B F hB hF
  have hJ0 := px4b_prod_int hd hρ (σ := σ + 2 - s) (by linarith [H.s_nonneg]) hJcl
  have hJ : Integrable (fun p : Torus d × Torus d =>
      offZero (fun u y => Jop d s ρ (fun z => F z y) u) p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    hJ0.congr (Eventually.of_forall fun p => by
      by_cases h : p.1 = p.2 <;> simp [offZero, h])
  obtain ⟨h1, h2⟩ := px4b_genFst_row H hσ hm hF hrow hJ x
  refine ⟨h1, h2, ?_⟩
  -- the second variable: `P_μ` of an integrable function
  have hG : Good d s V β ρ x (fun z => F x z) := px4b_good_conormal H hσ hm (conormalL_swap hF) x
  have hGi : Integrable (fun u => Bop d s V β ρ (fun z => F x z) u + Jop d s ρ (fun z => F x z) u)
      (withDensityReal ρ) := hG.bop.add hG.jop
  have hdef : (fun y => genSnd d s V β ρ F x y) = fun y =>
      (Bop d s V β ρ (fun z => F x z) y + Jop d s ρ (fun z => F x z) y) -
        ∫ u, (Bop d s V β ρ (fun z => F x z) u + Jop d s ρ (fun z => F x z) u) ∂(withDensityReal ρ) := by
    funext y
    unfold genSnd projGen projMean pair
    rfl
  rw [hdef]
  refine ⟨hGi.sub (integrable_const _), ?_⟩
  rw [integral_sub hGi (integrable_const _), integral_const]
  simp

/-- `ℰ` preserves double centring (`𝒜1 = 0`, `μ(𝒜f) = 0` and commutation of `𝒜_x` with `∫ · μ(dy)`
by differentiation under the integral; source line 4837, last sentence). -/
theorem defect_doublyCentered (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) {b m : ℕ} (hm : 2 ≤ m)
    {B : ℝ} {F : Torus d → Torus d → ℝ} (hsym : IsSymmPair F) (hF : Conormal σ b m B F)
    (hc : PDE.DoublyCentered (withDensityReal ρ) F) :
    PDE.DoublyCentered (withDensityReal ρ) (defectOp d s V β ρ F) := by
  have hd := H.two_le
  have hρ := H.rho_smooth
  have hσd : σ < d := lt_of_le_of_lt hσ H.s_lt
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hsymD := defect_symm H hσ hm hsym hF
  have hrow : ∀ x, ∫ y, defectOp d s V β ρ F x y ∂(withDensityReal ρ) = 0 := by
    intro x
    obtain ⟨C, hC0, hC⟩ := newton_map_general H σ hσd b m
    have hB := conormalL_B_nonneg hd hF
    have hN0 := hC B F hB hF
    have hN : Conormal (σ - 2) (b + 1) m (C * B) (newtonOp d β ρ F) :=
      conormalL_mono_b (mul_nonneg hC0 hB) (fun c => by split_ifs <;> omega) hN0
    have hNc : IsCanonicalPair (withDensityReal ρ) (newtonOp d β ρ F) := fun x' =>
      ⟨((px4b_row_bound hd hρ (σ := σ - 2) (by linarith) hN).choose_spec x').1,
        (newton_doublyCentered H hσd hF).2 x'⟩
    obtain ⟨g1, g2, g3, g4⟩ := gen_integral_comm H (σ := σ - 2) (by linarith [H.s_lt]) hm hN hNc x
    have hFi : Integrable (fun y => F x y) (withDensityReal ρ) :=
      ((px4b_row_bound hd hρ hσd hF).choose_spec x).1
    have hae : (fun y => defectOp d s V β ρ F x y) =ᵐ[withDensityReal ρ] fun y =>
        F x y + genFst d s V β ρ (newtonOp d β ρ F) x y + genSnd d s V β ρ (newtonOp d β ρ F) x y := by
      filter_upwards [px4b_ae_ne_mu (by omega) ρ x] with y hy
      simp [defectOp, Ne.symm hy]
    have hF0 : ∫ y, F x y ∂(withDensityReal ρ) = 0 := hc.2 x
    have h12 : Integrable (fun y => F x y + genFst d s V β ρ (newtonOp d β ρ F) x y)
        (withDensityReal ρ) := hFi.add g1
    rw [integral_congr_ae hae, integral_add h12 g3, integral_add hFi g1, hF0, g2, g4]
    simp
  refine ⟨fun y => ?_, fun x => hrow x⟩
  show ∫ x, defectOp d s V β ρ F x y ∂(withDensityReal ρ) = 0
  simp_rw [hsymD _ y]
  exact hrow y

theorem px4b_N_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun _ => b + 1) m (C * B) (newtonOp d β ρ F) := by
  obtain ⟨C, hC0, hC⟩ := newton_map_general H σ (lt_of_le_of_lt hσ H.s_lt) b m
  refine ⟨C, hC0, fun B F hB hF => ?_⟩
  exact conormalL_mono_b (mul_nonneg hC0 hB) (fun c => by split_ifs <;> omega) (hC B F hB hF)

theorem px4b_G_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun _ => b + 1) m (C * B)
        (ofChart (newtonChart d β⁻¹ (toChart F))) := by
  obtain ⟨C, hC0, hC⟩ := newton_ofChart_general H.two_le (inv_pos.mpr H.beta_pos)
    (lt_of_le_of_lt hσ H.s_lt) b m
  refine ⟨C, hC0, fun B F hB hF => ?_⟩
  exact conormalL_mono_b (mul_nonneg hC0 hB) (fun c => by split_ifs <;> omega) (hC B F hB hF)

/-- The row means `a`, `a'` of `G` are `C^m`, with norms `≲ B`. -/
theorem px4b_aa_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) x y
          ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) x y
          ∂(withDensityReal ρ)) ≤ C * B ∧
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) y x
          ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) y x
          ∂(withDensityReal ρ)) ≤ C * B := by
  obtain ⟨CG, hCG0, hCG⟩ := px4b_G_class H hσ b m
  have hσ2 : σ - 2 < d := by linarith [H.s_lt]
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth H (σ - 2) hσ2 (b + 1) m
  refine ⟨Cr * CG, mul_nonneg hCr0 hCG0, fun B F hB hF => ?_⟩
  have hG := hCG B F hB hF
  have hGB : 0 ≤ CG * B := mul_nonneg hCG0 hB
  have h1 := hCr (CG * B) _ hGB hG
  have h2 := hCr (CG * B) _ hGB (conormalL_swap hG)
  refine ⟨h1.1, ?_, h2.1, ?_⟩
  · calc _ ≤ Cr * (CG * B) := h1.2
      _ = _ := by ring
  · calc _ ≤ Cr * (CG * B) := h2.2
      _ = _ := by ring


theorem px4b_hAdd : ConormalAdd d := fun _ _ _ _ _ _ _ hF hG => conormalL_add hF hG

/-- The `∂_X²` piece. -/
theorem px4b_Y1_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => (β⁻¹ / 2) * ∑ i : Fin d, px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b m
  refine ⟨|β⁻¹ / 2| * ((d : ℝ) * C1), by positivity, fun B F hB hF => ?_⟩
  have hN := hC1 B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have h2 : ∀ i : Fin d, ConormalL (σ - 2) (fun _ => b + 1) (m - 1 - 1) (C1 * B)
      (px4b_dX i (px4b_dX i (newtonOp d β ρ F))) := fun i =>
    px4b_dX_conormal (by omega) (px4b_dX_conormal (by omega) hN i) i
  have h3 := conormal_finset_sum px4b_hAdd (σ - 2) (fun _ => b + 1) (m - 1 - 1) Finset.univ
    (fun i => px4b_dX i (px4b_dX i (newtonOp d β ρ F))) (fun _ => C1 * B) (fun i _ => h2 i)
  have h4 := ConormalL.smul h3 (β⁻¹ / 2)
  refine ConormalL.mono h4 (by positivity) (by linarith) (fun c => by omega) (by omega) ?_
  simp [Finset.sum_const]
  ring_nf
  exact le_refl _


theorem px4b_q_smooth (hρ : SmoothPosDensity ρ) (j : Fin d) :
    Torus.IsSmooth (fun u => Torus.partialDeriv j ρ u / ρ u) := by
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := hρ.smooth
  have e : Torus.lift (fun u => Torus.partialDeriv j ρ u / ρ u) =
      fun v => (fderiv ℝ (Torus.lift ρ) v (EuclideanSpace.single j 1)) / Torus.lift ρ v := by
    funext v
    have h := px4b_lift_partialDeriv ρ j v
    show Torus.partialDeriv j ρ (Torus.mk v) / ρ (Torus.mk v) = _ / Torus.lift ρ v
    rw [← h]
    rfl
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift fun u => Torus.partialDeriv j ρ u / ρ u)
  rw [e]
  refine ContDiff.div ?_ hρs (fun v => (hρ.pos _).ne')
  exact (hρs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply contDiff_const


/-- The first-order (drift) piece. -/
theorem px4b_T1_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => β⁻¹ * ∑ j : Fin d, ((Torus.partialDeriv j ρ x / ρ x) *
          px4b_K1 j (newtonOp d β ρ F) x y +
          (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y)) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b m
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth (d := d) (m - 1) (σ - 2 + 1) (fun _ => b + 1)
  have hq : ∀ j : Fin d, Torus.IsCk ((m - 1 : ℕ) : WithTop ℕ∞) (fun u => Torus.partialDeriv j ρ u / ρ u) :=
    fun j => PDE.MFPair.isCk_of_smooth_ps (px4b_q_smooth H.rho_smooth j) _
  set M : ℝ := ∑ j : Fin d, (PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) +
    PDE.cbNorm2 (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y)) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => add_nonneg (PDE.MFPair.cbNorm2_nonneg _ _)
    (PDE.MFPair.cbNorm2_nonneg _ _)
  refine ⟨|β⁻¹| * ((d : ℝ) * (Cm * M * (2 * C1))), by positivity, fun B F hB hF => ?_⟩
  have hN := hC1 B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have hK1 : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1) (2 * (C1 * B))
      (px4b_K1 j (newtonOp d β ρ F)) := fun j =>
    conormalL_mono_b (by positivity) (fun c => by simp) (px4b_K1_conormal (by omega) hN j)
  have hKy : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1) (2 * (C1 * B))
      (px4b_dy j (newtonOp d β ρ F)) := fun j =>
    conormalL_mono_b (by positivity) (fun c => by simp) (px4b_dy_conormal (by omega) hN j)
  have hterm : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1)
      (Cm * M * (2 * (C1 * B)))
      (fun x y => (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j (newtonOp d β ρ F) x y +
        (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y) := by
    intro j
    have a1 := hCm (2 * (C1 * B)) _ (fun x _ => Torus.partialDeriv j ρ x / ρ x) (hK1 j)
      (px4b_isCk2_fst (hq j))
    have a2 := hCm (2 * (C1 * B)) _ (fun _ y => Torus.partialDeriv j ρ y / ρ y) (hKy j)
      (px4b_isCk2_snd (hq j))
    have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => b + 1)) = fun _ => b + 1 :=
      funext fun c => Finset.sup_const (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero c)) _
    rw [hsup] at a1 a2
    have a3 := conormalL_add a1 a2
    have c1 := PDE.MFPair.cbNorm2_nonneg (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x)
    have c2 := PDE.MFPair.cbNorm2_nonneg (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y)
    have h2C : 0 ≤ 2 * (C1 * B) := by positivity
    refine conormalL_mono_B a3 (add_nonneg (mul_nonneg (mul_nonneg hCm0 c1) h2C)
      (mul_nonneg (mul_nonneg hCm0 c2) h2C)) ?_
    have hj : PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) +
        PDE.cbNorm2 (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y) ≤ M :=
      Finset.single_le_sum (f := fun j : Fin d => (PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) +
        PDE.cbNorm2 (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y))) (fun j _ => add_nonneg
          (PDE.MFPair.cbNorm2_nonneg _ _) (PDE.MFPair.cbNorm2_nonneg _ _)) (Finset.mem_univ j)
    have : 0 ≤ Cm * (2 * (C1 * B)) := by positivity
    nlinarith
  have hsum := conormal_finset_sum px4b_hAdd (σ - 2 + 1) (fun _ => b + 1) (m - 1) Finset.univ
    (fun j x y => (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j (newtonOp d β ρ F) x y +
        (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y)
    (fun _ => Cm * M * (2 * (C1 * B))) (fun j _ => hterm j)
  have hs2 := ConormalL.smul hsum β⁻¹
  refine ConormalL.mono hs2 (by positivity) (by linarith) (fun c => by omega) (by omega) ?_
  simp [Finset.sum_const]
  ring_nf
  exact le_refl _


lemma px4b_s_ge_one (H : ParxHyp d s V β ρ) : 1 ≤ s := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  rw [H.crit]; linarith

/-- The nonlocal pieces. -/
theorem px4b_J_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => offZero (fun x y => Jop d s ρ (fun z => newtonOp d β ρ F z y) x) x y +
          swapK (offZero (fun x y => Jop d s ρ (fun z => swapK (newtonOp d β ρ F) z y) x)) x y) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b m
  have hσd : σ - 2 + 2 < d := by linarith [H.s_lt]
  obtain ⟨C2, hC20, hC2⟩ := jop_general H (σ - 2) hσd (b + 1) m hm
  refine ⟨C2 * C1 + C2 * C1, by positivity, fun B F hB hF => ?_⟩
  have hN := hC1 B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have h1 := hC2 (C1 * B) _ hB1 hN
  have h2 := conormalL_swap (hC2 (C1 * B) _ hB1 (conormalL_swap hN))
  have hs := px4b_s_ge_one H
  have h1' : ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C2 * (C1 * B))
      (offZero fun x y => Jop d s ρ (fun z => newtonOp d β ρ F z y) x) :=
    ConormalL.mono h1 (by positivity) (by linarith) (fun c => by omega) le_rfl le_rfl
  have h2' : ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C2 * (C1 * B))
      (swapK (offZero fun x y => Jop d s ρ (fun z => swapK (newtonOp d β ρ F) z y) x)) :=
    ConormalL.mono h2 (by positivity) (by linarith) (fun c => by omega) le_rfl le_rfl
  have h3 := conormalL_add h1' h2'
  refine conormalL_mono_B h3 (by positivity) ?_
  nlinarith


/-- The `μ`-mean of `Bop + Jop` of the slices of `N` (the constant removed by `projGen`). -/
def px4b_cN (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (N : Torus d → Torus d → ℝ) (y : Torus d) : ℝ :=
  ∫ u, (Bop d s V β ρ (fun z => N z y) u + Jop d s ρ (fun z => N z y) u) ∂(withDensityReal ρ)

/-- The explicit kernel representing `Bop + Jop` of the slices. -/
def px4b_Kc (d : ℕ) (s : ℝ) (β : ℝ) (ρ : Torus d → ℝ) (N : Torus d → Torus d → ℝ) :
    Torus d → Torus d → ℝ := fun u y =>
  (β⁻¹ * ∑ i : Fin d, offZero (px4b_K2 i N) u y +
    β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ u / ρ u) * offZero (px4b_K1 j N) u y) +
  offZero (fun u y => Jop d s ρ (fun z => N z y) u) u y

theorem px4b_Kc_eq (H : ParxHyp d s V β ρ) {τ : ℝ} {b' m : ℕ} {B' : ℝ} {N : Torus d → Torus d → ℝ}
    (hm : 2 ≤ m) (hN : ConormalL τ b' m B' N) {u y : Torus d} (hu : u ≠ y) :
    Bop d s V β ρ (fun z => N z y) u + Jop d s ρ (fun z => N z y) u = px4b_Kc d s β ρ N u y := by
  have hc2 : ContDiffAt ℝ 2 (Torus.lift (fun z => N z y)) (Torus.rep u) :=
    px4b_slice_c2 hm hN y _ (by rw [Torus.mk_rep]; exact hu)
  rw [px4b_Bop_eq H hc2]
  simp only [px4b_Kc, offZero, if_neg hu]
  rfl

theorem px4b_Kc_class (H : ParxHyp d s V β ρ) {τ : ℝ} (hτ : τ + 2 < d) (b' m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B' : ℝ) (N : Torus d → Torus d → ℝ), 0 ≤ B' → Conormal τ b' m B' N →
      ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (C * B') (px4b_Kc d s β ρ N) := by
  obtain ⟨Cj, hCj0, hCj⟩ := jop_general H τ hτ b' m hm
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth (d := d) (m - 1) (τ + 1) (fun _ => b')
  have hq : ∀ j : Fin d, Torus.IsCk ((m - 1 : ℕ) : WithTop ℕ∞) (fun u => Torus.partialDeriv j ρ u / ρ u) :=
    fun j => PDE.MFPair.isCk_of_smooth_ps (px4b_q_smooth H.rho_smooth j) _
  set M : ℝ := ∑ j : Fin d, PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => PDE.MFPair.cbNorm2_nonneg _ _
  refine ⟨|β⁻¹| * ((d : ℝ) * 4) + |β⁻¹| * (Cm * M * 2) + Cj, by positivity, fun B' N hB' hN => ?_⟩
  have hB4 : 0 ≤ 4 * B' := by positivity
  -- the second-derivative terms
  have hK2 : ∀ i : Fin d, ConormalL (τ + 2) (fun _ => b') (m - 2) (4 * B') (offZero (px4b_K2 i N)) := by
    intro i
    have h'' : ConormalL (τ + 2) (fun _ => b') (m - 2) (4 * B') (px4b_K2 i N) :=
      ConormalL.mono (px4b_K2_conormal hm hN i) (by positivity) (by linarith) (fun c => by simp)
        (by omega) (by linarith)
    exact conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) h''
  have sumK2 := conormal_finset_sum px4b_hAdd (τ + 2) (fun _ => b') (m - 2) Finset.univ
    (fun i => offZero (px4b_K2 i N)) (fun _ => 4 * B') (fun i _ => hK2 i)
  have sK2 := ConormalL.smul sumK2 β⁻¹
  -- the first-derivative terms
  have hK1 : ∀ j : Fin d, ConormalL (τ + 1) (fun _ => b') (m - 1) (2 * B') (offZero (px4b_K1 j N)) := by
    intro j
    have h'' : ConormalL (τ + 1) (fun _ => b') (m - 1) (2 * B') (px4b_K1 j N) :=
      ConormalL.mono (px4b_K1_conormal (by omega) hN j) (by positivity) le_rfl (fun c => by simp)
        le_rfl le_rfl
    exact conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) h''
  have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => b')) = fun _ => b' :=
    funext fun c => Finset.sup_const (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero c)) _
  have hterm : ∀ j : Fin d, ConormalL (τ + 1) (fun _ => b') (m - 1)
      (Cm * PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) * (2 * B'))
      (fun x y => (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j N) x y) := by
    intro j
    have a1 := hCm (2 * B') _ (fun x _ => Torus.partialDeriv j ρ x / ρ x) (hK1 j)
      (px4b_isCk2_fst (hq j))
    rw [hsup] at a1
    exact a1
  have sumK1 := conormal_finset_sum px4b_hAdd (τ + 1) (fun _ => b') (m - 1) Finset.univ
    (fun j x y => (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j N) x y)
    (fun j => Cm * PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) * (2 * B'))
    (fun j _ => hterm j)
  have sK1 := ConormalL.smul sumK1 β⁻¹
  -- the nonlocal term
  have hJ := hCj B' N hB' hN
  -- bring everything to `(τ + 2, b' + 2, m - 2)`
  have e1 : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (|β⁻¹| * ∑ _i : Fin d, 4 * B')
      (fun x y => β⁻¹ * ∑ i : Fin d, offZero (px4b_K2 i N) x y) :=
    ConormalL.mono sK2 (by positivity) le_rfl (fun c => by omega) le_rfl le_rfl
  have e2 : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2)
      (|β⁻¹| * ∑ j : Fin d, Cm * PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) * (2 * B'))
      (fun x y => β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ x / ρ x) * offZero (px4b_K1 j N) x y) := by
    refine ConormalL.mono sK1 ?_ (by linarith) (fun c => by omega) (by omega) le_rfl
    refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
    exact mul_nonneg (mul_nonneg hCm0 (PDE.MFPair.cbNorm2_nonneg _ _)) (by positivity)
  have hs := px4b_s_ge_one H
  have e3 : ConormalL (τ + 2) (fun _ => b' + 2) (m - 2) (Cj * B')
      (offZero fun x y => Jop d s ρ (fun z => N z y) x) :=
    ConormalL.mono hJ (by positivity) (by linarith) (fun c => le_rfl) le_rfl le_rfl
  have e12 := conormalL_add e1 e2
  have e123 := conormalL_add e12 e3
  refine conormalL_mono_B e123 (add_nonneg (add_nonneg
    (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => hB4))
    (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg hCm0 (PDE.MFPair.cbNorm2_nonneg _ _)) (by positivity))))
    (mul_nonneg hCj0 hB')) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs1 : ∑ j : Fin d, Cm * PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) * (2 * B') =
      Cm * M * (2 * B') := by
    rw [hM, Finset.mul_sum, Finset.sum_mul]
  rw [hs1]
  apply le_of_eq
  ring


theorem px4b_cN_eq (H : ParxHyp d s V β ρ) {τ : ℝ} {b' m : ℕ} {B' : ℝ} {N : Torus d → Torus d → ℝ}
    (hm : 2 ≤ m) (hN : ConormalL τ b' m B' N) :
    px4b_cN d s V β ρ N = fun y => ∫ u, swapK (px4b_Kc d s β ρ N) y u ∂(withDensityReal ρ) := by
  funext y
  unfold px4b_cN
  refine integral_congr_ae ?_
  filter_upwards [px4b_ae_ne_mu (by have := H.two_le; omega) ρ y] with u hu
  exact px4b_Kc_eq H hm hN hu

theorem px4b_cN_class (H : ParxHyp d s V β ρ) {τ : ℝ} (hτ : τ + 2 < d) (b' m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B' : ℝ) (N : Torus d → Torus d → ℝ), 0 ≤ B' → Conormal τ b' m B' N →
      Torus.IsCk ((m - 2 : ℕ) : WithTop ℕ∞) (px4b_cN d s V β ρ N) ∧
        Torus.cbNorm (m - 2) (px4b_cN d s V β ρ N) ≤ C * B' := by
  obtain ⟨Ck, hCk0, hCk⟩ := px4b_Kc_class H hτ b' m hm
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth H (τ + 2) hτ (b' + 2) (m - 2)
  refine ⟨Cr * Ck, mul_nonneg hCr0 hCk0, fun B' N hB' hN => ?_⟩
  have hKc := hCk B' N hB' hN
  have h := hCr (Ck * B') (swapK (px4b_Kc d s β ρ N)) (mul_nonneg hCk0 hB') (conormalL_swap hKc)
  rw [px4b_cN_eq H hm hN]
  refine ⟨h.1, ?_⟩
  calc _ ≤ Cr * (Ck * B') := h.2
    _ = _ := by ring


/-- `∂_i ∂_i a`. -/
def px4b_Lam (i : Fin d) (a : Torus d → ℝ) : Torus d → ℝ :=
  fun x => Torus.partialDeriv i (fun u => Torus.partialDeriv i a u) x

theorem px4b_Lam_class {n : ℕ} {a : Torus d → ℝ} (ha : Torus.IsCk ((n + 2 : ℕ) : WithTop ℕ∞) a) (i : Fin d) :
    Torus.IsCk ((n : ℕ) : WithTop ℕ∞) (px4b_Lam i a) ∧ Torus.cbNorm n (px4b_Lam i a) ≤ Torus.cbNorm (n + 2) a := by
  have h1 : Torus.IsCk ((n + 1 : ℕ) : WithTop ℕ∞) (Torus.partialDeriv i a) :=
    PDE.ProdAux.isCk_partialDeriv (n := n + 1) (by exact_mod_cast ha) i
  have h2 : Torus.IsCk ((n : ℕ) : WithTop ℕ∞) (Torus.partialDeriv i (fun u => Torus.partialDeriv i a u)) :=
    PDE.ProdAux.isCk_partialDeriv (n := n) (by exact_mod_cast h1) i
  refine ⟨h2, ?_⟩
  calc Torus.cbNorm n (px4b_Lam i a) ≤ Torus.cbNorm (n + 1) (Torus.partialDeriv i a) :=
        PDE.ProdAux.cbNorm_partialDeriv_le (n := n) (by exact_mod_cast h1) i
    _ ≤ Torus.cbNorm (n + 2) a := PDE.ProdAux.cbNorm_partialDeriv_le (n := n + 1) (by exact_mod_cast ha) i

/-- The smooth kernel `-(ν/2)(Δa(x) + Δa'(y))`. -/
def px4b_Sm (ν : ℝ) (a a' : Torus d → ℝ) : Torus d → Torus d → ℝ := fun x y =>
  -(ν / 2) * (∑ i : Fin d, px4b_Lam i a x + ∑ i : Fin d, px4b_Lam i a' y)

theorem px4b_Sm_class (ν σ : ℝ) (b : ℕ → ℕ) {n : ℕ} {a a' : Torus d → ℝ}
    (ha : Torus.IsCk ((n + 2 : ℕ) : WithTop ℕ∞) a) (ha' : Torus.IsCk ((n + 2 : ℕ) : WithTop ℕ∞) a') :
    ConormalL σ b n (|ν / 2| * ((d : ℝ) * Torus.cbNorm (n + 2) a + (d : ℝ) * Torus.cbNorm (n + 2) a'))
      (px4b_Sm ν a a') := by
  have f1 : ∀ i : Fin d, ConormalL σ b n (Torus.cbNorm (n + 2) a) (fun x _ => px4b_Lam i a x) := fun i =>
    conormalL_mono_B (px4b_conormal_fst σ b (px4b_Lam_class ha i).1) (PDE.cbNorm_nonneg'C _ _)
      (px4b_Lam_class ha i).2
  have f2 : ∀ i : Fin d, ConormalL σ b n (Torus.cbNorm (n + 2) a') (fun _ y => px4b_Lam i a' y) := fun i =>
    conormalL_mono_B (px4b_conormal_snd σ b (px4b_Lam_class ha' i).1) (PDE.cbNorm_nonneg'C _ _)
      (px4b_Lam_class ha' i).2
  have s1 := conormal_finset_sum px4b_hAdd σ b n Finset.univ (fun i x y => px4b_Lam i a x)
    (fun _ => Torus.cbNorm (n + 2) a) (fun i _ => f1 i)
  have s2 := conormal_finset_sum px4b_hAdd σ b n Finset.univ (fun i x y => px4b_Lam i a' y)
    (fun _ => Torus.cbNorm (n + 2) a') (fun i _ => f2 i)
  have s3 := conormalL_add s1 s2
  have s4 := ConormalL.smul s3 (-(ν / 2))
  have c1 := PDE.cbNorm_nonneg'C (n + 2) a
  have c2 := PDE.cbNorm_nonneg'C (n + 2) a'
  refine ConormalL.mono s4 (mul_nonneg (abs_nonneg _) (add_nonneg (Finset.sum_nonneg fun _ _ => c1)
    (Finset.sum_nonneg fun _ _ => c2))) le_rfl (fun c => le_rfl) le_rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg]
  exact le_refl _


/-- `G = ofChart (newtonChart ..)` and its row means. -/
def px4b_G (d : ℕ) (β : ℝ) (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  ofChart (newtonChart d β⁻¹ (toChart F))

def px4b_aF (d : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (F : Torus d → Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, px4b_G d β F x y ∂(withDensityReal ρ)

def px4b_a'F (d : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (F : Torus d → Torus d → ℝ) (y : Torus d) : ℝ :=
  ∫ x, px4b_G d β F x y ∂(withDensityReal ρ)

def px4b_c0F (d : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (F : Torus d → Torus d → ℝ) : ℝ :=
  ∫ x, ∫ y, px4b_G d β F x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)

lemma px4b_hNeq (F : Torus d → Torus d → ℝ) {x y : Torus d} (hxy : x ≠ y) :
    newtonOp d β ρ F x y = px4b_G d β F x y - px4b_aF d β ρ F x - px4b_a'F d β ρ F y +
      px4b_c0F d β ρ F := by
  simp only [newtonOp, if_neg hxy, canonicalCenter, px4b_G, px4b_aF, px4b_a'F, px4b_c0F]

theorem px4b_hP (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) {b m : ℕ} (hm : 2 ≤ m) {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hF : Conormal σ b m B F) (X z : Euc d) (hz : z ≠ 0)
    (hzr : ‖z‖ < 1 / 32) :
    toChart F (X, z) + 2 * β⁻¹ * Laplacian.laplacian (fun z' => toChart (px4b_G d β F) (X, z')) z = 0 := by
  have hσd : σ < d := lt_of_le_of_lt hσ H.s_lt
  have h := newtonChart_poisson_aux H.two_le (inv_pos.mpr H.beta_pos) hσd
    (conormalL_mono_m hm hF) X z hz hzr
  have hzr' : ‖z‖ < r0 := by unfold r0; linarith
  have hev : (fun z' : Euc d => toChart (px4b_G d β F) (X, z')) =ᶠ[𝓝 z]
      fun z' => newtonChart d β⁻¹ (toChart F) (X, z') := by
    have hU : {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < r0} ∈ 𝓝 z :=
      (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hz, hzr'⟩
    filter_upwards [hU] with z' hz'
    exact toChart_ofChart (fun X z k hk => px3a_newtonChart_periodic F β⁻¹ X z k hk) hz'.1 hz'.2
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  linarith


/-- Crude class (order `σ`) of the kernel `Z0`. -/
theorem px4b_Z0_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL σ (fun _ => b + 1) (m - 2) (C * B) (px4b_Z0 β⁻¹ F (newtonOp d β ρ F)) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b m
  refine ⟨1 + |β⁻¹| * ((d : ℝ) * (4 * C1 + 4 * C1 + C1 / 2)), by positivity, fun B F hB hF => ?_⟩
  have hN := hC1 B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have hF' : ConormalL σ (fun _ => b + 1) (m - 2) B F :=
    ConormalL.mono hF hB le_rfl (fun c => by omega) (by omega) le_rfl
  have hA : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (4 * (C1 * B))
      (px4b_K1 i (px4b_K1 i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_K1_conormal (by omega) (px4b_K1_conormal (by omega) hN i) i)
      (by positivity) (by linarith) (fun c => by simp) (by omega) (by linarith)
  have hBy : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (4 * (C1 * B))
      (px4b_dy i (px4b_dy i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_dy_conormal (by omega) (px4b_dy_conormal (by omega) hN i) i)
      (by positivity) (by linarith) (fun c => by simp) (by omega) (by linarith)
  have hX : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (C1 * B)
      (px4b_dX i (px4b_dX i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_dX_conormal (by omega) (px4b_dX_conormal (by omega) hN i) i)
      hB1 (by linarith) (fun c => le_rfl) (by omega) le_rfl
  have hterm : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2)
      (4 * (C1 * B) + 4 * (C1 * B) + |(-(1 / 2 : ℝ))| * (C1 * B))
      (fun x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) := by
    intro i
    have e : (fun x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) =
        fun x y => (px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
          px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y) +
          (-(1 / 2 : ℝ)) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y := by
      funext x y; ring
    rw [e]
    exact conormalL_add (conormalL_add (hA i) (hBy i)) (ConormalL.smul (hX i) (-(1 / 2 : ℝ)))
  have hsum := conormal_finset_sum px4b_hAdd σ (fun _ => b + 1) (m - 2) Finset.univ
    (fun i x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y)
    (fun _ => 4 * (C1 * B) + 4 * (C1 * B) + |(-(1 / 2 : ℝ))| * (C1 * B)) (fun i _ => hterm i)
  have hs2 := ConormalL.smul hsum β⁻¹
  have hall := conormalL_add hF' hs2
  refine conormalL_mono_B hall (by positivity) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : |(-(1 / 2 : ℝ))| = 1 / 2 := by norm_num
  rw [this]
  nlinarith


theorem px4b_laplacian_sum {a : Torus d → ℝ} {n : ℕ} (ha : Torus.IsCk ((n + 2 : ℕ) : WithTop ℕ∞) a)
    (x : Torus d) : Torus.laplacian a x = ∑ i : Fin d, px4b_Lam i a x := by
  have hc : ContDiffAt ℝ 2 (Torus.lift a) (Torus.rep x) :=
    (show ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift a) from ha).contDiffAt.of_le
      (by exact_mod_cast Nat.le_add_left 2 n)
  exact px4b_laplacian_eq hc

theorem px4b_Zv_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
          px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨CZ, hCZ0, hCZ⟩ := px4b_Z0_class H hσ b (n + 2) hm
  obtain ⟨CA, hCA0, hCA⟩ := px4b_aa_class H hσ b (n + 2)
  obtain ⟨CG, hCG0, hCG⟩ := px4b_G_class H hσ b (n + 2)
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b (n + 2)
  have hν : 0 ≤ |β⁻¹ / 2| := abs_nonneg _
  refine ⟨px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
    (CZ + |β⁻¹ / 2| * ((d : ℝ) * CA + (d : ℝ) * CA)), ?_, fun B F hB hF => ?_⟩
  · have := px4b_Cvan_ge_one σ (fun _ => b + 1) n (by norm_num : (0 : ℝ) < 1 / 32)
    positivity
  have hZ := hCZ B F hB hF
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hCA B F hB hF
  have hAn : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_aF d β ρ F) := hA1
  have hA'n : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_a'F d β ρ F) := hA3
  have hSm := px4b_Sm_class β⁻¹ σ (fun _ => b + 1) hAn hA'n
  have c1 := PDE.cbNorm_nonneg'C (n + 2) (px4b_aF d β ρ F)
  have c2 := PDE.cbNorm_nonneg'C (n + 2) (px4b_a'F d β ρ F)
  have hSm' : ConormalL σ (fun _ => b + 1) n (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))
      (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F)) :=
    conormalL_mono_B hSm (mul_nonneg hν (add_nonneg (mul_nonneg (Nat.cast_nonneg _) c1)
      (mul_nonneg (Nat.cast_nonneg _) c2)))
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hA4 (Nat.cast_nonneg _))) hν)
  have hdiff : ConormalL σ (fun _ => b + 1) n
      (CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))))
      (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) := by
    have e : (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) =
        fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y +
          (-1 : ℝ) * px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y := by
      funext x y; ring
    rw [e]
    exact conormalL_add hZ (ConormalL.smul hSm' (-1))
  have hBnn : 0 ≤ CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))) := by
    positivity
  have hvan : ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 1 / 32 →
      toChart (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) (X, z) = 0 := by
    intro X z hz hzr
    have hN := (hC1 B F hB hF).smooth
    have hG : ContDiffOn ℝ (2 : ℕ) (lift2 (px4b_G d β F)) (offDiag d) :=
      ((hCG B F hB hF).smooth).of_le (by exact_mod_cast Nat.le_add_left 2 n)
    have ha : ContDiff ℝ 2 (Torus.lift (px4b_aF d β ρ F)) :=
      (show ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift (px4b_aF d β ρ F)) from hAn).of_le
        (by exact_mod_cast Nat.le_add_left 2 n)
    have ha' : ContDiff ℝ 2 (Torus.lift (px4b_a'F d β ρ F)) :=
      (show ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift (px4b_a'F d β ρ F)) from hA'n).of_le
        (by exact_mod_cast Nat.le_add_left 2 n)
    have hpo := px4b_Z0_poisson (ν := β⁻¹) (F := F) (N := newtonOp d β ρ F) (G := px4b_G d β F)
      (a := px4b_aF d β ρ F) (a' := px4b_a'F d β ρ F) (c0 := px4b_c0F d β ρ F) (m := n + 2) (X := X) (z := z) hN hm
      (fun x y hxy => px4b_hNeq F hxy) hG ha ha' (fun X z hz hzr => px4b_hP H hσ hm hF X z hz hzr)
      hz hzr
    show px4b_Z0 β⁻¹ F (newtonOp d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) -
      px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z))
        (Torus.mk (X - (1 / 2 : ℝ) • z)) = 0
    have hz0 : px4b_Z0 β⁻¹ F (newtonOp d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) =
        toChart (px4b_Z0 β⁻¹ F (newtonOp d β ρ F)) (X, z) := rfl
    rw [hz0, hpo]
    simp only [px4b_Sm]
    rw [← px4b_laplacian_sum hAn, ← px4b_laplacian_sum hA'n]
    ring
  have hv := px4b_conormal_vanish (σ' := σ - 1) (by norm_num : (0 : ℝ) < 1 / 32) hBnn hdiff hvan
  have hC1' := px4b_Cvan_ge_one σ (fun _ => b + 1) n (by norm_num : (0 : ℝ) < 1 / 32)
  have hvn : 0 ≤ px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
      (CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))) :=
    mul_nonneg (by linarith) hBnn
  refine conormalL_mono_B (ConormalL.mono hv hvn le_rfl (fun c => by omega) le_rfl le_rfl)
    hvn ?_
  have e : CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))) =
      (CZ + |β⁻¹ / 2| * ((d : ℝ) * CA + (d : ℝ) * CA)) * B := by
    rw [abs_neg, abs_one]; ring
  rw [e]
  apply le_of_eq
  ring


theorem px4b_Ps_class (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y -
          px4b_cN d s V β ρ (newtonOp d β ρ F) y -
          px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨CA, hCA0, hCA⟩ := px4b_aa_class H hσ b (n + 2)
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b (n + 2)
  have hτ : σ - 2 + 2 < d := by linarith [H.s_lt]
  obtain ⟨Cc, hCc0, hCc⟩ := px4b_cN_class H hτ (b + 1) (n + 2) hm
  refine ⟨|β⁻¹ / 2| * ((d : ℝ) * CA + (d : ℝ) * CA) + Cc * C1 + Cc * C1, by positivity, fun B F hB hF => ?_⟩
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hCA B F hB hF
  have hAn : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_aF d β ρ F) := hA1
  have hA'n : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_a'F d β ρ F) := hA3
  have hN := hC1 B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have c1 := PDE.cbNorm_nonneg'C (n + 2) (px4b_aF d β ρ F)
  have c2 := PDE.cbNorm_nonneg'C (n + 2) (px4b_a'F d β ρ F)
  have hν : 0 ≤ |β⁻¹ / 2| := abs_nonneg _
  have hSm := px4b_Sm_class β⁻¹ (σ - 1) (fun _ => b + 3) hAn hA'n
  have hSm' : ConormalL (σ - 1) (fun _ => b + 3) n
      (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))
      (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F)) :=
    conormalL_mono_B hSm (mul_nonneg hν (add_nonneg (mul_nonneg (Nat.cast_nonneg _) c1)
      (mul_nonneg (Nat.cast_nonneg _) c2)))
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hA4 (Nat.cast_nonneg _))) hν)
  obtain ⟨hc1, hc2⟩ := hCc (C1 * B) _ hB1 hN
  obtain ⟨hc3, hc4⟩ := hCc (C1 * B) _ hB1 (conormalL_swap hN)
  have k1 : ConormalL (σ - 1) (fun _ => b + 3) n (Cc * (C1 * B))
      (fun _ y => px4b_cN d s V β ρ (newtonOp d β ρ F) y) :=
    conormalL_mono_B (px4b_conormal_snd (σ - 1) (fun _ => b + 3) hc1)
      (PDE.cbNorm_nonneg'C _ _) hc2
  have k2 : ConormalL (σ - 1) (fun _ => b + 3) n (Cc * (C1 * B))
      (fun x _ => px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) :=
    conormalL_mono_B (px4b_conormal_fst (σ - 1) (fun _ => b + 3) hc3)
      (PDE.cbNorm_nonneg'C _ _) hc4
  have e : (fun x y => px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y -
          px4b_cN d s V β ρ (newtonOp d β ρ F) y -
          px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) =
      fun x y => (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y +
          (-1 : ℝ) * px4b_cN d s V β ρ (newtonOp d β ρ F) y) +
          (-1 : ℝ) * px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x := by
    funext x y; ring
  rw [e]
  have h3 := conormalL_add (conormalL_add hSm' (ConormalL.smul k1 (-1))) (ConormalL.smul k2 (-1))
  refine conormalL_mono_B h3 (by positivity) ?_
  rw [abs_neg, abs_one]
  apply le_of_eq
  ring


theorem px4b_defect_decomp (H : ParxHyp d s V β ρ) {τ : ℝ} {b' m : ℕ} {B1 : ℝ}
    {N : Torus d → Torus d → ℝ} (F : Torus d → Torus d → ℝ) (hm : 2 ≤ m)
    (hN : ConormalL τ b' m B1 N) {x y : Torus d} (hxy : x ≠ y) :
    F x y + genFst d s V β ρ N x y + genSnd d s V β ρ N x y =
      px4b_Z0 β⁻¹ F N x y + (β⁻¹ / 2) * ∑ i : Fin d, px4b_dX i (px4b_dX i N) x y +
        β⁻¹ * ∑ j : Fin d, ((Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j N x y +
          (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j N x y) +
        offZero (fun x y => Jop d s ρ (fun z => N z y) x) x y +
        swapK (offZero (fun x y => Jop d s ρ (fun z => swapK N z y) x)) x y -
        px4b_cN d s V β ρ N y - px4b_cN d s V β ρ (swapK N) x := by
  have hyx : y ≠ x := Ne.symm hxy
  have hc2x : ContDiffAt ℝ 2 (Torus.lift (fun z => N z y)) (Torus.rep x) :=
    px4b_slice_c2 hm hN y _ (by rw [Torus.mk_rep]; exact hxy)
  have hc2y : ContDiffAt ℝ 2 (Torus.lift (fun z => swapK N z x)) (Torus.rep y) :=
    px4b_slice_c2 hm (conormalL_swap hN) x _ (by rw [Torus.mk_rep]; exact hyx)
  have g1 : genFst d s V β ρ N x y = (Bop d s V β ρ (fun z => N z y) x + Jop d s ρ (fun z => N z y) x) -
      px4b_cN d s V β ρ N y := rfl
  have g2 : genSnd d s V β ρ N x y = (Bop d s V β ρ (fun z => swapK N z x) y +
      Jop d s ρ (fun z => swapK N z x) y) - px4b_cN d s V β ρ (swapK N) x := rfl
  have b1 := px4b_Bop_eq H hc2x
  have b2 := px4b_Bop_eq H hc2y
  have j1 : offZero (fun x y => Jop d s ρ (fun z => N z y) x) x y = Jop d s ρ (fun z => N z y) x := by
    simp [offZero, hxy]
  have j2 : swapK (offZero (fun x y => Jop d s ρ (fun z => swapK N z y) x)) x y =
      Jop d s ρ (fun z => swapK N z x) y := by
    simp [swapK, offZero, hyx]
  rw [g1, g2, b1, b2, j1, j2]
  have hZ : px4b_Z0 β⁻¹ F N x y = F x y + β⁻¹ * ∑ i : Fin d,
      (px4b_K1 i (px4b_K1 i N) x y + px4b_dy i (px4b_dy i N) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i N) x y) := rfl
  rw [hZ]
  have hsum1 : β⁻¹ * ∑ i : Fin d, (px4b_K1 i (px4b_K1 i N) x y + px4b_dy i (px4b_dy i N) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i N) x y) + β⁻¹ / 2 * ∑ i : Fin d, px4b_dX i (px4b_dX i N) x y =
      β⁻¹ * ∑ i : Fin d, (px4b_K1 i (px4b_K1 i N) x y + px4b_dy i (px4b_dy i N) x y) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum2 : β⁻¹ * ∑ j : Fin d, ((Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j N x y +
          (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j N x y) =
      β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => N z y) x +
      β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ y / ρ y) *
        Torus.partialDeriv j (fun z => swapK N z x) y := by
    rw [Finset.sum_add_distrib, mul_add]
    rfl
  have hsum3 : β⁻¹ * ∑ i : Fin d, (px4b_K1 i (px4b_K1 i N) x y + px4b_dy i (px4b_dy i N) x y) =
      β⁻¹ * ∑ i : Fin d, Torus.partialDeriv i (fun u => Torus.partialDeriv i (fun z => N z y) u) x +
      β⁻¹ * ∑ i : Fin d, Torus.partialDeriv i (fun u => Torus.partialDeriv i (fun z => swapK N z x) u) y := by
    rw [Finset.sum_add_distrib, mul_add]
    rfl
  linarith [hsum1, hsum2, hsum3]

/-- The defect map `ℰ = I + (𝒜_x + 𝒜_y)𝒩` lowers the order by `1/2` and costs two derivatives
(`Q:eq:defect-map`, source lines 4807-4809, 4837): the `Δ_z` part cancels `F` (`newtonChart_poisson`)
up to commutators with `χ` supported where `1/32 ≤ |z|` (bounded); `½Δ_X𝒩F` and the central drift
have order `σ - 2`; the relative drift `b(X+z/2) - b(X-z/2) = O(r)` against `∇_z𝒩F` has order
`σ - 2`; the nonlocal term has order `σ - s ≤ σ - 1` (`jop_map`, `s ≥ 1`); the projections add
smooth rows.  All logarithms are absorbed by the margin `1 - 1/2`. -/
theorem defect_map (H : ParxHyp d s V β ρ) (σ : ℝ) (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
      Conormal σ b m B F →
        Conormal (σ - 1 / 2) b (m - 2) (C * B) (defectOp d s V β ρ F) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class H hσ b m
  obtain ⟨C2, hC20, hC2⟩ := px4b_Zv_class H hσ b m hm
  obtain ⟨C3, hC30, hC3⟩ := px4b_Y1_class H hσ b m hm
  obtain ⟨C4, hC40, hC4⟩ := px4b_T1_class H hσ b m hm
  obtain ⟨C5, hC50, hC5⟩ := px4b_J_class H hσ b m hm
  obtain ⟨C6, hC60, hC6⟩ := px4b_Ps_class H hσ b m hm
  obtain ⟨Cr, hCr1, hCr⟩ := px4b_conormal_relax (d := d) (fun _ => b + 3) (fun _ => b) (m - 2)
    (show σ - 1 < σ - 1 / 2 by linarith)
  refine ⟨Cr * (C2 + C3 + C4 + C5 + C6), by positivity, fun B F hB hF => ?_⟩
  have e2 := hC2 B F hB hF
  have e3 := hC3 B F hB hF
  have e4 := hC4 B F hB hF
  have e5 := hC5 B F hB hF
  have e6 := hC6 B F hB hF
  have hsum := conormalL_add (conormalL_add (conormalL_add (conormalL_add e2 e3) e4) e5) e6
  have hB' : C2 * B + C3 * B + C4 * B + C5 * B + C6 * B = (C2 + C3 + C4 + C5 + C6) * B := by ring
  rw [hB'] at hsum
  have hcongr := conormalL_congr_offDiag
    (F' := defectOp d s V β ρ F) (fun x y hxy => ?_) hsum
  · have := hCr _ _ (by positivity) hcongr
    rw [← mul_assoc] at this
    exact this
  · have hN := hC1 B F hB hF
    have hd := px4b_defect_decomp H F hm (b' := b + 1) hN hxy
    simp only [defectOp, if_neg hxy]
    rw [hd]
    have hZ : px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y =
        (px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y - px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) +
          px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y := by ring
    linarith

/-! ## PX5: the iteration -/

theorem posSeminorm_nonneg' (K : ℕ) (f : Torus d → ℝ) : 0 ≤ posSeminorm K f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- `R_j` stays conormal of order `s - j/2` with `m - 2j` derivatives (`Q:eq:parametrix-iteration`):
induction from `hsource_conormal` and `defect_map`, with `R_j` symmetric
(`defect_symm`) and doubly centred (`defect_doublyCentered`). -/
theorem parxR_conormal (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∀ j : ℕ, 2 * j ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - (j : ℝ) / 2) 0 (m - 2 * j) (C * posSeminorm (m + 2) f) (parxR d s V β ρ f j) ∧
      IsSymmPair (parxR d s V β ρ f j) ∧
      PDE.DoublyCentered (withDensityReal ρ) (parxR d s V β ρ f j) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨C, hC0, hC⟩ := hsource_conormal H m
    refine ⟨C, hC0, fun f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hC f hf
    refine ⟨?_, ?_, ?_⟩
    · simpa [parxR] using h1
    · intro x y
      simp only [parxR, offZero]
      by_cases hxy : x = y
      · subst hxy; rfl
      · simp only [hxy, Ne.symm hxy, ite_false]; exact h2 x y
    · simpa [parxR] using h3
  | succ j ih =>
    intro hj
    obtain ⟨C, hC0, hC⟩ := ih (by omega)
    have hσ : s - (j : ℝ) / 2 ≤ s := by
      have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
      linarith
    obtain ⟨CE, hCE0, hCE⟩ := defect_map H (s - (j : ℝ) / 2) hσ 0 (m - 2 * j) (by omega)
    refine ⟨CE * C, mul_nonneg hCE0 hC0, fun f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hC f hf
    have hB0 : 0 ≤ C * posSeminorm (m + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
    have hE := hCE _ (parxR d s V β ρ f j) hB0 h1
    have e1 : s - (j : ℝ) / 2 - 1 / 2 = s - ((j + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    have e2 : m - 2 * j - 2 = m - 2 * (j + 1) := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, e2] at hE
      simpa [parxR, mul_assoc] using hE
    · exact defect_symm H hσ (by omega) h2 h1
    · exact defect_doublyCentered H hσ (by omega) h2 h1 h3

/-- The conormal classes of `𝒩R_j` (`j ≥ 0`) after the Newton map. -/
theorem parxN_conormal (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∀ j : ℕ, 2 * j ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ConormalL (s - (j : ℝ) / 2 - 2)
        (fun c => 0 + if s - (j : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
        (m - 2 * j) (C * posSeminorm (m + 2) f) (newtonOp d β ρ (parxR d s V β ρ f j)) := by
  intro j hj
  obtain ⟨C, hC0, hC⟩ := parxR_conormal H m j hj
  have hσ : s - (j : ℝ) / 2 < d := by
    have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
    linarith [H.s_lt]
  obtain ⟨CN, hCN0, hCN⟩ := newton_map H (s - (j : ℝ) / 2) hσ 0 (m - 2 * j)
  refine ⟨CN * C, mul_nonneg hCN0 hC0, fun f hf => ?_⟩
  obtain ⟨h1, h2, _⟩ := hC f hf
  have hB0 : 0 ≤ C * posSeminorm (m + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  simpa [mul_assoc] using hCN _ _ hB0 h2 h1

/-- `ψ^loc_L` is `C^∞` off the diagonal (`f` smooth): `parxN_conormal` at every `m` (`ConormalL.smooth`),
finite sum.  Used for `ParxGapAt.size` (field `PsiSize.smooth`) and as input of `parx_psi_smooth`. -/
theorem parxPsi_smooth_offDiag (H : ParxHyp d s V β ρ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (L : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 (parxPsi d s V β ρ f L)) (offDiag d) := by
  rw [contDiffOn_infty]
  intro n
  have key : ∀ j ∈ Finset.range L, ContDiffOn ℝ (n : WithTop ℕ∞)
      (lift2 (newtonOp d β ρ (parxR d s V β ρ f j))) (offDiag d) := by
    intro j hj
    have hjL : j < L := Finset.mem_range.mp hj
    obtain ⟨C, -, hC⟩ := parxN_conormal H (2 * L + n) j (by omega)
    have h := (hC f hf).smooth
    refine h.of_le ?_
    have : n ≤ 2 * L + n - 2 * j := by omega
    exact_mod_cast this
  have hsum : lift2 (parxPsi d s V β ρ f L) =
      fun p => ∑ j ∈ Finset.range L, lift2 (newtonOp d β ρ (parxR d s V β ρ f j)) p := by
    funext p; simp [lift2, parxPsi]
  rw [hsum]
  exact ContDiffOn.sum key

/-! ## PX6: the gap lemma -/

/-- The conclusions of the gap lemma at differentiability `J` (`L = parxL d J` defect steps,
`K = parxK d J` derivatives of `f`), with constant `C`.  `Φ_f = parxPsi f L = ψ^loc`,
`R_f = diagExt (parxR f L) = R_L`. -/
structure ParxGapAt (H : ParxHyp d s V β ρ) (J : ℕ) (C : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  linear_psi : ∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
    parxPsi d s V β ρ (a • f + b • f') (parxL d J) =
      fun x y => a * parxPsi d s V β ρ f (parxL d J) x y + b * parxPsi d s V β ρ f' (parxL d J) x y
  linear_R : ∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
    diagExt (parxR d s V β ρ (a • f + b • f') (parxL d J)) =
      fun x y => a * diagExt (parxR d s V β ρ f (parxL d J)) x y +
        b * diagExt (parxR d s V β ρ f' (parxL d J)) x y
  measurable : ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    Measurable (Function.uncurry (parxPsi d s V β ρ f (parxL d J)))
  symm : ∀ f : Torus d → ℝ, Torus.IsSmooth f → IsSymmPair (parxPsi d s V β ρ f (parxL d J))
  canonical : ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    IsCanonicalPair (withDensityReal ρ) (parxPsi d s V β ρ f (parxL d J))
  size : ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    PsiSize s (C * posSeminorm (parxK d J) f) (parxPsi d s V β ρ f (parxL d J))
  jpair_canonical : ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)))
  jpair_bound : ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ x y, x ≠ y →
    |Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)) x y| ≤
      C * posSeminorm (parxK d J) f * wEnv s x y
  remainder_ck : ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    PDE.IsCk2 J (diagExt (parxR d s V β ρ f (parxL d J))) ∧
    PDE.DoublyCentered (withDensityReal ρ) (diagExt (parxR d s V β ρ f (parxL d J))) ∧
    PDE.cbNorm2 J (diagExt (parxR d s V β ρ f (parxL d J))) ≤ C * posSeminorm (parxK d J) f ∧
    (∀ x y, diagExt (parxR d s V β ρ f (parxL d J)) x y =
      diagExt (parxR d s V β ρ f (parxL d J)) y x)
  telescope : ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ x y, x ≠ y →
    parxR d s V β ρ f (parxL d J) x y =
      Hsource d s ρ f x y + genFst d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y +
        genSnd d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y
  add_smooth : ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ Ψ : Torus d → Torus d → ℝ,
    PDE.IsCk2 2 Ψ → ∀ x y, x ≠ y →
      genFst d s V β ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
          genFst d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y + genFst d s V β ρ Ψ x y ∧
        genSnd d s V β ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
          genSnd d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y + genSnd d s V β ρ Ψ x y ∧
        Jpair d s ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
          Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)) x y + Jpair d s ρ Ψ x y

/-- **The gap lemma** (Prop 4.13 without the global step): for every `J` there is `C` with
`ParxGapAt H J C`.  Derivation from the packets: `parxR_conormal` (+ `parxN_conormal`) at
`m = (J+1) + 2L`, `L = 2J + d + 6`, `σ_L = s - L/2`, `σ_L + J + 1 = -2 < 0`, then `conormal_extend`
for `remainder_ck`; `gen_sum` + the definition of `defectOp` for `telescope`; `gen_add_smooth` for
`add_smooth`; `newton_linear`, `defect` linearity for `linear_*`; `size` from `newton_map` at `j = 0`
(log only at `s = 2`, none for `c = 1` by evenness) and the coarse classes of `𝒩R_j`, `j ≥ 1`
(order `≤ s - 2 - 1/2` absorbs all logarithms); `jpair_*` from `jop_map` (order `σ_j - s ≤ 0`,
i.e. `≤ C(1+|log r|) ≤ C w`) and `conormal_row_smooth` for the projections; `measurable` from continuity
off the closed null diagonal and `0` on it; `canonical` from `newton_doublyCentered`. -/
theorem parx_gap (H : ParxHyp d s V β ρ) (J : ℕ) : ∃ C : ℝ, ParxGapAt H J C := by
  sorry

/-- **Smoothness bootstrap**: `ψ_f = ψ^loc_L + Ψ_{R_L}` is `C^∞` off the diagonal (needed for
`PsiSize.smooth`; the source asserts "smooth off the diagonal" without proof).  Route: for any
`M` take `L₁ ≥ L` so large that `R_{L₁}` is `C^{J(M)}` (`parxR_conormal`, `conormal_extend`, `f`
smooth; `J(M)` from the existing qualitative `periodic_pair_inverse`), so `ψ_{L₁} = ψ^loc_{L₁} +
Ψ_{R_{L₁}}` is `C^M` off the diagonal; `Δ := ψ^loc_{L₁} - ψ^loc_L = ∑_{L ≤ j < L₁} 𝒩R_j` is a doubly
centred `C^{J+2}` kernel (`𝒩R_j` has order `s - j/2 - 2`; `conormal_extend` at `J+2`, `j ≥ L`) with `(𝒜_x+𝒜_y)Δ = R_{L₁} - R_L` (`gen_sum`, telescoping), hence by the
left-inverse clause of `PairInverseSpec` `Ψ_{R_{L₁}} - Ψ_{R_L} = Ψ_{R_{L₁}-R_L} = -Δ`, i.e.
`ψ_{L₁} = ψ_L`. -/
theorem parx_psi_smooth (H : ParxHyp d s V β ρ) (J : ℕ) (hspec : PairInverseSpec H J)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (lift2 (fun x y => parxPsi d s V β ρ f (parxL d J) x y +
        PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f (parxL d J))) x y)) (offDiag d) := by
  sorry

/-! ## PX7: the pair inverse at small differentiability -/

/-- Lemma 4.14 in the quantitative form `PairInverseSpec` with `J = d + 12`.  The existing proof
(`exists_pairSemigroup_decay`) needs `J = 2L + 3 m_* + 2d + 9`, `L = j + m_* + 4`, i.e. `J ≈ 4.5 d + 36`
for `j = 2`, which exceeds the derivative budget of `K = 8d + 80` (needs `K ≈ 25 d + 200`).
Route for `J = d + 12`: the tensor/mixed-Sobolev form of the same argument: `U_t^xU_t^y` acts on
`H^{j₀} ⊗ H^{j₀}` (`j₀` the least even integer `> d/2 + 4`; `adjoint_decay_comparison` with
`C e^{-ct}` on each factor, Hilbert tensor product), `C^{2j₀}(𝕋^{2d}) ⊂ H^{j₀}⊗H^{j₀}`,
`H^{j₀}⊗H^{j₀} ⊂ C²(𝕋^{2d})` as `j₀ > d/2 + 2`; `2 j₀ ≤ d + 12`.  Left-inverse: `d/dt U_tU_tΔ =
U_tU_t(𝒜_x+𝒜_y)Δ` (`hasDerivAt_pairSemigroup` at this `J`) and decay. -/
theorem pair_inverse_small (H : ParxHyp d s V β ρ) : PairInverseSpec H (parxJ d) := by
  have hρ := H.rho_smooth
  exact PDE.PX7.px7_spec H.two_le s H.s_nonneg H.s_lt β H.beta_pos V H.V_smooth ρ H.thermal hρ.smooth
    hρ.pos (parxJ d) (by unfold parxJ; exact PDE.PX7.px7_m_le d)

end HRS.Parx

end
