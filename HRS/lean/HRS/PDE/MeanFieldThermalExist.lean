import HRS.PDE.MeanFieldFejer
import HRS.PDE.MeanFieldThermalUnique

/-!
# Existence of the thermal equilibrium from the Fejér-truncated problems (package MF-01, packet P2b2)

Given solutions `ρ_N` of the Fejér-truncated thermal equation
`ρ_N = exp(-β(V + g_N ⋆ ρ_N))/Z_N` (`g_N = F_N ⋆ g`), we prove uniform two-sided bounds,
equicontinuity (via `g_N ⋆ ρ_N = g ⋆ (F_N ⋆ ρ_N)` and the `L¹`-modulus of `g`), extract a uniformly
convergent subsequence (Arzelà–Ascoli) and pass to the limit.  Plan: `HRS/PDE/MeanFieldPlan.md`,
§3.1 ("Uniform bounds", "Equicontinuity", "Limit").
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate BoundedContinuousFunction

namespace HRS.PDE.MFThermalExist

variable {d : ℕ}

/-- Fejér-smoothed kernel `g_N = F_N ⋆ g`. -/
noncomputable def truncKernel (d : ℕ) (s : ℝ) (N : ℕ) : Torus d → ℝ :=
  convFun (fejer N) (periodicRiesz d s)

/-! ### Convolution algebra -/

/-- Commutativity of the convolution on the torus. -/
theorem convFun_comm (a b : Torus d → ℝ) (x : Torus d) : convFun a b x = convFun b a x := by
  unfold convFun
  rw [← integral_sub_left_eq_self (fun y => a (x - y) * b y) volume x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- Associativity `(F ⋆ g) ⋆ h = g ⋆ (F ⋆ h)` for `F, h` continuous, `g` integrable. -/
theorem convFun_assoc {g F h : Torus d → ℝ} (hg : Integrable g) (hF : Continuous F)
    (hh : Continuous h) :
    convFun (convFun F g) h = convFun g (convFun F h) := by
  have hFi : Integrable F := integrable_of_continuous' hF
  have e1 : convFun F g = convFun g F := funext (convFun_comm F g)
  have hG : Continuous (convFun g F) := MFAux.continuous_convFun hg hF
  have hGi : Integrable (convFun g F) := integrable_of_continuous' hG
  have hFh : Continuous (convFun F h) := MFAux.continuous_convFun hFi hh
  refine MFAux.eq_of_funFourierCoeff_eq ?_ ?_ ?_
  · rw [e1]; exact MFAux.continuous_convFun hGi hh
  · exact MFAux.continuous_convFun hg hFh
  · intro k
    rw [e1, MFAux.funFourierCoeff_convFun hGi hh, MFAux.funFourierCoeff_convFun hg hF,
      MFAux.funFourierCoeff_convFun hg hFh, MFAux.funFourierCoeff_convFun hFi hh]
    ring

theorem truncKernel_eq_comm (s : ℝ) (N : ℕ) :
    truncKernel d s N = convFun (periodicRiesz d s) (fejer N) :=
  funext (convFun_comm _ _)

theorem truncKernel_continuous {s : ℝ} (hg : Integrable (periodicRiesz d s)) (N : ℕ) :
    Continuous (truncKernel d s N) := by
  rw [truncKernel_eq_comm]
  exact MFAux.continuous_convFun hg (fejer_continuous N)

theorem convFun_trunc_eq {s : ℝ} (hg : Integrable (periodicRiesz d s)) (N : ℕ)
    {h : Torus d → ℝ} (hh : Continuous h) :
    convFun (truncKernel d s N) h = convFun (periodicRiesz d s) (convFun (fejer N) h) :=
  convFun_assoc hg (fejer_continuous N) hh


/-- The zero-mass property of the kernel: `∫ g ⋆ σ = 0` for continuous `σ`. -/
theorem integral_convFun_riesz {s : ℝ} (F : MFInputs.MFKernelFacts d s) {σ : Torus d → ℝ}
    (hσ : Continuous σ) : ∫ x, convFun (periodicRiesz d s) σ x = 0 := by
  have h := MFAux.funFourierCoeff_convFun F.integrable hσ 0
  rw [F.fourierCoeff 0] at h
  have h0 : (rieszCoeff d s 0 : ℂ) = 0 := by simp [rieszCoeff]
  rw [h0, zero_mul, funFourierCoeff_eq_int] at h
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- Jensen for `exp` against the probability measure `volume`, via `x + 1 ≤ exp x`. -/
theorem exp_integral_le {Φ : Torus d → ℝ} (hΦ : Continuous Φ) :
    Real.exp (∫ x, Φ x) ≤ ∫ x, Real.exp (Φ x) := by
  set c := ∫ x, Φ x with hc
  have hi1 : Integrable Φ := integrable_of_continuous' hΦ
  have hi2 : Integrable fun x => Real.exp (Φ x) :=
    integrable_of_continuous' (Real.continuous_exp.comp hΦ)
  have hpt : ∀ x, Real.exp c * (Φ x - c + 1) ≤ Real.exp (Φ x) := by
    intro x
    have h1 := Real.add_one_le_exp (Φ x - c)
    have e : Real.exp (Φ x) = Real.exp c * Real.exp (Φ x - c) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos c).le
  have hi3 : Integrable fun x => Real.exp c * (Φ x - c + 1) :=
    ((hi1.sub (integrable_const c)).add (integrable_const 1)).const_mul _
  have h := integral_mono hi3 hi2 hpt
  have hI : ∫ x, (Φ x - c + 1) = 1 := by
    rw [integral_add (f := fun x => Φ x - c) (g := fun _ => (1 : ℝ))
      (hi1.sub (integrable_const c)) (integrable_const 1),
      integral_sub hi1 (integrable_const c)]
    simp [hc]
  rw [integral_const_mul, hI, mul_one] at h
  exact h

/-! ### Solutions of the truncated equation -/

/-- A positive continuous probability density solving the Fejér-truncated thermal equation. -/
structure TruncSol (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (N : ℕ) (ρ : Torus d → ℝ) : Prop where
  cont : Continuous ρ
  pos : ∀ x, 0 < ρ x
  int_one : ∫ x, ρ x = 1
  eq : ∀ x, ρ x = Real.exp (-β * (V x + convFun (truncKernel d s N) ρ x)) /
    ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y))

section Bounds

variable {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {N : ℕ} {ρ : Torus d → ℝ}

theorem TruncSol.sigma_cont (S : TruncSol s V β N ρ) :
    Continuous (convFun (fejer N) ρ) :=
  MFAux.continuous_convFun (integrable_of_continuous' (fejer_continuous N)) S.cont

theorem TruncSol.u_eq (F : MFInputs.MFKernelFacts d s) (S : TruncSol s V β N ρ) :
    convFun (truncKernel d s N) ρ = convFun (periodicRiesz d s) (convFun (fejer N) ρ) :=
  convFun_trunc_eq F.integrable N S.cont

theorem TruncSol.u_cont (F : MFInputs.MFKernelFacts d s) (S : TruncSol s V β N ρ) :
    Continuous (convFun (truncKernel d s N) ρ) := by
  rw [S.u_eq F]; exact MFAux.continuous_convFun F.integrable S.sigma_cont

theorem TruncSol.sigma_nonneg (hN : 0 < N) (S : TruncSol s V β N ρ) (x : Torus d) :
    0 ≤ convFun (fejer N) ρ x :=
  convFun_fejer_ge hN (integrable_of_continuous' S.cont) (fun y => (S.pos y).le) x

theorem TruncSol.u_ge {B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hB : ∀ x, -B ≤ periodicRiesz d s x) (S : TruncSol s V β N ρ) (x : Torus d) :
    -B ≤ convFun (truncKernel d s N) ρ x := by
  have hgN : ∀ y, -B ≤ truncKernel d s N y := fun y => convFun_fejer_ge hN F.integrable hB y
  have hc : Continuous fun y => truncKernel d s N (x - y) * ρ y :=
    ((truncKernel_continuous F.integrable N).comp (continuous_const.sub continuous_id)).mul S.cont
  have hi1 : Integrable fun y => -B * ρ y :=
    (integrable_of_continuous' S.cont).const_mul _
  have := integral_mono hi1 (integrable_of_continuous' hc)
    (fun y => mul_le_mul_of_nonneg_right (hgN (x - y)) (S.pos y).le)
  rw [integral_const_mul, S.int_one] at this
  simpa [convFun] using this

theorem TruncSol.u_int (F : MFInputs.MFKernelFacts d s) (S : TruncSol s V β N ρ) :
    ∫ x, convFun (truncKernel d s N) ρ x = 0 := by
  rw [S.u_eq F]; exact integral_convFun_riesz F S.sigma_cont


/-- The partition function of the truncated equation. -/
theorem TruncSol.Z_ge {Mv : ℝ} (F : MFInputs.MFKernelFacts d s) (hVc : Continuous V)
    (hMv : ∀ x, |V x| ≤ Mv) (hβ : 0 < β) (S : TruncSol s V β N ρ) :
    Real.exp (-β * Mv) ≤ ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) := by
  have huc := S.u_cont F
  have hΦ : Continuous fun y => -β * (V y + convFun (truncKernel d s N) ρ y) :=
    continuous_const.mul (hVc.add huc)
  refine le_trans ?_ (exp_integral_le hΦ)
  refine Real.exp_le_exp.mpr ?_
  have hVi : Integrable V := integrable_of_continuous' hVc
  have hui : Integrable (convFun (truncKernel d s N) ρ) := integrable_of_continuous' huc
  rw [integral_const_mul, integral_add hVi hui, S.u_int F]
  have : ∫ y, V y ≤ Mv := by
    have := integral_mono hVi (integrable_const Mv) (fun y => (abs_le.mp (hMv y)).2)
    simpa using this
  nlinarith

theorem TruncSol.Z_pos {Mv : ℝ} (F : MFInputs.MFKernelFacts d s) (hVc : Continuous V)
    (hMv : ∀ x, |V x| ≤ Mv) (hβ : 0 < β) (S : TruncSol s V β N ρ) :
    0 < ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) :=
  lt_of_lt_of_le (Real.exp_pos _) (S.Z_ge F hVc hMv hβ)

theorem TruncSol.rho_le {Mv B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hVc : Continuous V) (hMv : ∀ x, |V x| ≤ Mv) (hB : ∀ x, -B ≤ periodicRiesz d s x)
    (hβ : 0 < β) (S : TruncSol s V β N ρ) (x : Torus d) :
    ρ x ≤ Real.exp (β * (2 * Mv + B)) := by
  have hZ := S.Z_ge F hVc hMv hβ
  have hZp := S.Z_pos F hVc hMv hβ
  rw [S.eq x, div_le_iff₀ hZp]
  have h1 : -β * (V x + convFun (truncKernel d s N) ρ x) ≤ β * (Mv + B) := by
    have := (abs_le.mp (hMv x)).1
    have := S.u_ge F hN hB x
    nlinarith
  calc Real.exp (-β * (V x + convFun (truncKernel d s N) ρ x))
      ≤ Real.exp (β * (Mv + B)) := Real.exp_le_exp.mpr h1
    _ = Real.exp (β * (2 * Mv + B)) * Real.exp (-β * Mv) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le

theorem TruncSol.sigma_le {Mv B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hVc : Continuous V) (hMv : ∀ x, |V x| ≤ Mv) (hB : ∀ x, -B ≤ periodicRiesz d s x)
    (hβ : 0 < β) (S : TruncSol s V β N ρ) (x : Torus d) :
    convFun (fejer N) ρ x ≤ Real.exp (β * (2 * Mv + B)) :=
  convFun_fejer_le hN (integrable_of_continuous' S.cont) (fun y => S.rho_le F hN hVc hMv hB hβ y) x

theorem TruncSol.u_abs {Mv B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hVc : Continuous V) (hMv : ∀ x, |V x| ≤ Mv) (hB : ∀ x, -B ≤ periodicRiesz d s x)
    (hβ : 0 < β) (S : TruncSol s V β N ρ) (x : Torus d) :
    |convFun (truncKernel d s N) ρ x| ≤ (∫ y, |periodicRiesz d s y|) * Real.exp (β * (2 * Mv + B)) := by
  rw [S.u_eq F]
  refine convFun_bound_of_le F.integrable (fun y => ?_) x
  rw [abs_of_nonneg (S.sigma_nonneg hN y)]
  exact S.sigma_le F hN hVc hMv hB hβ y

theorem TruncSol.rho_ge {Mv B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hVc : Continuous V) (hMv : ∀ x, |V x| ≤ Mv) (hB : ∀ x, -B ≤ periodicRiesz d s x)
    (hβ : 0 < β) (S : TruncSol s V β N ρ) (x : Torus d) :
    Real.exp (-2 * β * (Mv + (∫ y, |periodicRiesz d s y|) * Real.exp (β * (2 * Mv + B)))) ≤ ρ x := by
  set C := Mv + (∫ y, |periodicRiesz d s y|) * Real.exp (β * (2 * Mv + B)) with hC
  have hZp := S.Z_pos F hVc hMv hβ
  have hpt : ∀ y, |V y + convFun (truncKernel d s N) ρ y| ≤ C := fun y =>
    (abs_add_le _ _).trans (add_le_add (hMv y) (S.u_abs F hN hVc hMv hB hβ y))
  have hZ : ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) ≤ Real.exp (β * C) := by
    have hΦ : Continuous fun y => Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) :=
      Real.continuous_exp.comp (continuous_const.mul (hVc.add (S.u_cont F)))
    have := integral_mono (integrable_of_continuous' hΦ) (integrable_const (Real.exp (β * C)))
      (fun y => Real.exp_le_exp.mpr (by
        have := (abs_le.mp (hpt y)).1
        nlinarith))
    simpa using this
  rw [S.eq x, le_div_iff₀ hZp]
  have h1 : -β * C ≤ -β * (V x + convFun (truncKernel d s N) ρ x) := by
    have := (abs_le.mp (hpt x)).2
    nlinarith
  calc Real.exp (-2 * β * C) * ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y))
      ≤ Real.exp (-2 * β * C) * Real.exp (β * C) := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
    _ = Real.exp (-β * C) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr h1


/-! ### Equicontinuity -/

theorem abs_exp_sub_exp_le {a b m : ℝ} (ha : a ≤ m) (hb : b ≤ m) :
    |Real.exp a - Real.exp b| ≤ Real.exp m * |a - b| := by
  have key : ∀ a b : ℝ, a ≤ m → Real.exp a - Real.exp b ≤ Real.exp m * |a - b| := by
    intro a b ha
    have h1 := Real.add_one_le_exp (b - a)
    have e : Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp a * (b - a + 1) ≤ Real.exp b := by
      rw [e]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    have h3 : Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by nlinarith
    calc Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := h3
      _ ≤ Real.exp a * |a - b| := mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos a).le
      _ ≤ Real.exp m * |a - b| :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (abs_nonneg _)
  rw [abs_le]
  constructor
  · have := key b a hb
    rw [abs_sub_comm b a] at this
    linarith
  · exact key a b ha

/-- Oscillation of `g ⋆ σ` through the `L¹`-modulus of translations of `g`. -/
theorem convFun_diff_le {g σ : Torus d → ℝ} (hg : Integrable g) (hσ : Continuous σ) {Λ : ℝ}
    (hΛ : ∀ y, |σ y| ≤ Λ) (x x' : Torus d) :
    |convFun g σ x - convFun g σ x'| ≤ Λ * ∫ z, |g (z - (x' - x)) - g z| := by
  have hi : ∀ x : Torus d, Integrable fun y => g (x - y) * σ y := fun x =>
    (hg.comp_sub_left x).mul_bdd hσ.aestronglyMeasurable (c := Λ)
      (Filter.Eventually.of_forall fun y => by simpa using hΛ y)
  have hsub : convFun g σ x - convFun g σ x' = ∫ y, (g (x - y) - g (x' - y)) * σ y := by
    unfold convFun
    rw [← integral_sub (hi x) (hi x')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_mul]
  have hint : Integrable fun y => |g (x - y) - g (x' - y)| * Λ :=
    (((hg.comp_sub_left x).sub (hg.comp_sub_left x')).abs).mul_const Λ
  have hsubst : ∫ y, |g (x - y) - g (x' - y)| = ∫ z, |g (z - (x' - x)) - g z| := by
    rw [← integral_sub_left_eq_self (fun z => |g (z - (x' - x)) - g z|) volume x']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have : x' - y - (x' - x) = x - y := by abel
    simp only [this]
  rw [hsub, ← Real.norm_eq_abs]
  calc ‖∫ y, (g (x - y) - g (x' - y)) * σ y‖ ≤ ∫ y, |g (x - y) - g (x' - y)| * Λ :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hΛ y) (abs_nonneg _))
    _ = Λ * ∫ z, |g (z - (x' - x)) - g z| := by
        rw [integral_mul_const, hsubst, mul_comm]

theorem TruncSol.dist_le {Mv B : ℝ} (F : MFInputs.MFKernelFacts d s) (hN : 0 < N)
    (hVc : Continuous V) (hMv : ∀ x, |V x| ≤ Mv) (hB : ∀ x, -B ≤ periodicRiesz d s x)
    (hβ : 0 < β) (S : TruncSol s V β N ρ) (x x' : Torus d) :
    |ρ x - ρ x'| ≤ (β * Real.exp (β * (Mv + B)) * Real.exp (β * Mv)) *
      (|V x - V x'| + Real.exp (β * (2 * Mv + B)) *
        ∫ z, |periodicRiesz d s (z - (x' - x)) - periodicRiesz d s z|) := by
  have hZ := S.Z_ge F hVc hMv hβ
  have hZp := S.Z_pos F hVc hMv hβ
  set Z := ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) with hZdef
  set u := convFun (truncKernel d s N) ρ with hu
  have hamax : ∀ y, -β * (V y + u y) ≤ β * (Mv + B) := fun y => by
    have := (abs_le.mp (hMv y)).1
    have := S.u_ge F hN hB y
    nlinarith
  have hexp : |Real.exp (-β * (V x + u x)) - Real.exp (-β * (V x' + u x'))| ≤
      Real.exp (β * (Mv + B)) * (β * (|V x - V x'| + |u x - u x'|)) := by
    refine (abs_exp_sub_exp_le (hamax x) (hamax x')).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have : -β * (V x + u x) - -β * (V x' + u x') = -β * ((V x - V x') + (u x - u x')) := by ring
    rw [this, abs_mul, abs_neg, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _)) hβ.le
  have hu' : |u x - u x'| ≤ Real.exp (β * (2 * Mv + B)) *
      ∫ z, |periodicRiesz d s (z - (x' - x)) - periodicRiesz d s z| := by
    have hu1 : u = convFun (periodicRiesz d s) (convFun (fejer N) ρ) := S.u_eq F
    rw [hu1]
    exact convFun_diff_le F.integrable S.sigma_cont (fun y => by
      rw [abs_of_nonneg (S.sigma_nonneg hN y)]
      exact S.sigma_le F hN hVc hMv hB hβ y) x x'
  have hinvZ : 1 / Z ≤ Real.exp (β * Mv) := by
    rw [div_le_iff₀ hZp]
    have : Real.exp (β * Mv) * Real.exp (-β * Mv) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (β * Mv)]
  have e1 : ρ x - ρ x' = (Real.exp (-β * (V x + u x)) - Real.exp (-β * (V x' + u x'))) / Z := by
    rw [S.eq x, S.eq x']; ring
  rw [e1, abs_div, abs_of_pos hZp, div_eq_mul_one_div]
  have hnn : 0 ≤ |V x - V x'| + |u x - u x'| := by positivity
  calc |Real.exp (-β * (V x + u x)) - Real.exp (-β * (V x' + u x'))| * (1 / Z)
      ≤ (Real.exp (β * (Mv + B)) * (β * (|V x - V x'| + |u x - u x'|))) * Real.exp (β * Mv) :=
        mul_le_mul hexp hinvZ (by positivity) (by positivity)
    _ = (β * Real.exp (β * (Mv + B)) * Real.exp (β * Mv)) * (|V x - V x'| + |u x - u x'|) := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

end Bounds

/-! ### Arzelà–Ascoli -/

/-- A uniformly bounded, equicontinuous sequence of continuous functions on the torus has a
uniformly convergent subsequence. -/
theorem arzela_subseq (ρs : ℕ → Torus d → ℝ) (hc : ∀ n, Continuous (ρs n)) {lo hi : ℝ}
    (hb : ∀ n x, ρs n x ∈ Set.Icc lo hi)
    (heq : ∀ x₀, ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ n, |ρs n x₀ - ρs n x| < ε) :
    ∃ ρ : Torus d → ℝ, Continuous ρ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∀ᶠ j in atTop, ∀ y, |ρs (φ j) y - ρ y| < ε := by
  let f : ℕ → (Torus d →ᵇ ℝ) := fun n => BoundedContinuousFunction.mkOfCompact ⟨ρs n, hc n⟩
  have hf : ∀ n y, f n y = ρs n y := fun n y => rfl
  set A : Set (Torus d →ᵇ ℝ) := Set.range f with hA
  have hequi : Equicontinuous ((↑) : A → Torus d → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [heq x₀ ε hε] with x hx
    rintro ⟨_, ⟨n, rfl⟩⟩
    simpa [Real.dist_eq, hf] using hx n
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc lo hi) isCompact_Icc A
      (by rintro _ x ⟨n, rfl⟩; exact hb n x) hequi
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨a, a.continuous, φ, hφ, fun ε hε => ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hlim ε hε] with j hj y
  have := BoundedContinuousFunction.dist_coe_le_dist (f := f (φ j)) (g := a) y
  rw [Real.dist_eq] at this
  exact lt_of_le_of_lt this hj


/-! ### The limit at fixed `β` -/

/-- Fixed-`β` limit: from truncated solutions `ρ_n` (of order `N = n + 1`) to a thermal density with
the same uniform bounds. -/
theorem thermal_exists_fixed {s : ℝ} (F : MFInputs.MFKernelFacts d s) {V : Torus d → ℝ}
    (hV : Continuous V) {Mv B β : ℝ} (hMv : ∀ x, |V x| ≤ Mv)
    (hB : ∀ x, -B ≤ periodicRiesz d s x) (hβ : 0 < β)
    (ρs : ℕ → Torus d → ℝ) (hρs : ∀ n, TruncSol s V β (n + 1) (ρs n)) :
    ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρ ∧ Continuous ρ ∧
      ∀ x, Real.exp (-2 * β * (Mv + (∫ y, |periodicRiesz d s y|) *
          Real.exp (β * (2 * Mv + B)))) ≤ ρ x ∧ ρ x ≤ Real.exp (β * (2 * Mv + B)) := by
  have hg := F.integrable
  set L1 := ∫ y, |periodicRiesz d s y| with hL1def
  have hL1 : 0 ≤ L1 := integral_nonneg fun y => abs_nonneg _
  set Lb := Real.exp (β * (2 * Mv + B)) with hLb
  set lb := Real.exp (-2 * β * (Mv + L1 * Lb)) with hlbdef
  have hN : ∀ n : ℕ, 0 < n + 1 := fun n => Nat.succ_pos n
  have hup : ∀ n x, ρs n x ≤ Lb := fun n x => (hρs n).rho_le F (hN n) hV hMv hB hβ x
  have hlo : ∀ n x, lb ≤ ρs n x := fun n x => (hρs n).rho_ge F (hN n) hV hMv hB hβ x
  set K := β * Real.exp (β * (Mv + B)) * Real.exp (β * Mv) with hK
  -- equicontinuity
  have heq : ∀ x₀, ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ n, |ρs n x₀ - ρs n x| < ε := by
    intro x₀ ε hε
    have h1 : Tendsto (fun x => |V x₀ - V x|) (𝓝 x₀) (𝓝 0) := by
      have := ((tendsto_const_nhds (x := V x₀)).sub (hV.tendsto x₀)).abs
      simpa using this
    have h2 : Tendsto (fun x : Torus d => ∫ z, |periodicRiesz d s (z - (x - x₀)) -
        periodicRiesz d s z|) (𝓝 x₀) (𝓝 0) := by
      refine (l1_modulus hg).comp ?_
      have := (continuous_sub_right x₀).tendsto x₀
      simpa using this
    have h3 : Tendsto (fun x : Torus d => K * (|V x₀ - V x| + Lb * ∫ z,
        |periodicRiesz d s (z - (x - x₀)) - periodicRiesz d s z|)) (𝓝 x₀) (𝓝 0) := by
      have := (tendsto_const_nhds (x := K)).mul (h1.add (h2.const_mul Lb))
      simpa using this
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with x hx n
    exact lt_of_le_of_lt ((hρs n).dist_le F (hN n) hV hMv hB hβ x₀ x) hx
  obtain ⟨ρ, hρc, φ, hφ, huni⟩ := arzela_subseq ρs (fun n => (hρs n).cont)
    (fun n x => ⟨hlo n x, hup n x⟩) heq
  have hφN : Tendsto (fun j => φ j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_succ _) hφ.tendsto_atTop
  have hpt : ∀ x, Tendsto (fun j => ρs (φ j) x) atTop (𝓝 (ρ x)) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [huni ε hε] with j hj
    rw [Real.dist_eq]; exact hj x
  -- `F_N ⋆ ρ_N → ρ` uniformly
  have hσ : ∀ ε > 0, ∀ᶠ j in atTop, ∀ y,
      |convFun (fejer (φ j + 1)) (ρs (φ j)) y - ρ y| ≤ ε := by
    intro ε hε
    have h1 := huni (ε / 2) (by positivity)
    have h2 := Metric.tendstoUniformly_iff.mp (fejer_tendsto_uniformly ρ hρc) (ε / 2)
      (by positivity)
    filter_upwards [h1, hφN.eventually h2] with j hj1 hj2 y
    have hlin := MFThermal.convFun_sub (integrable_of_continuous' (fejer_continuous (d := d)
      (φ j + 1))) (hρs (φ j)).cont hρc y
    have hb := convFun_fejer_bound (hN (φ j))
      (h := fun y => ρs (φ j) y - ρ y)
      (integrable_of_continuous' ((hρs (φ j)).cont.sub hρc)) (m := -(ε / 2)) (M := ε / 2)
      (fun y => by have := abs_lt.mp (hj1 y); linarith)
      (fun y => by have := abs_lt.mp (hj1 y); linarith) y
    have h2y := hj2 y
    rw [Real.dist_eq] at h2y
    have h3 := abs_lt.mp h2y
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  -- `g_N ⋆ ρ_N → g ⋆ ρ` pointwise
  have hu : ∀ x, Tendsto (fun j => convFun (truncKernel d s (φ j + 1)) (ρs (φ j)) x) atTop
      (𝓝 (convFun (periodicRiesz d s) ρ x)) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (L1 + 1) := by positivity
    filter_upwards [hσ _ hε'] with j hj
    have e1 := (hρs (φ j)).u_eq F
    have hlin := MFThermal.convFun_sub hg (hρs (φ j)).sigma_cont hρc x
    have hbd := convFun_bound_of_le hg
      (h := fun y => convFun (fejer (φ j + 1)) (ρs (φ j)) y - ρ y) hj x
    rw [Real.dist_eq, congrFun e1 x, ← hlin]
    have : (L1 + 1) * (ε / (L1 + 1)) = ε := by field_simp
    have h5 : L1 * (ε / (L1 + 1)) < ε := by nlinarith
    exact lt_of_le_of_lt hbd h5
  -- partition functions
  set Φ : Torus d → ℝ := fun y => -β * (V y + convFun (periodicRiesz d s) ρ y) with hΦdef
  have hZ : Tendsto (fun j => ∫ y, Real.exp (-β * (V y +
      convFun (truncKernel d s (φ j + 1)) (ρs (φ j)) y))) atTop
      (𝓝 (∫ y, Real.exp (Φ y))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (β * (Mv + B)))
      (fun j => ?_) (integrable_const _) (fun j => ?_) (Filter.Eventually.of_forall fun y => ?_)
    · exact (Real.continuous_exp.comp (continuous_const.mul
        (hV.add ((hρs (φ j)).u_cont F)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      have := (abs_le.mp (hMv y)).1
      have := (hρs (φ j)).u_ge F (hN _) hB y
      nlinarith
    · exact ((tendsto_const_nhds (x := -β)).mul
        ((tendsto_const_nhds (x := V y)).add (hu y))).rexp
  set Z := ∫ y, Real.exp (Φ y) with hZdef
  have hZge : Real.exp (-β * Mv) ≤ Z :=
    ge_of_tendsto hZ (Filter.Eventually.of_forall fun j => (hρs (φ j)).Z_ge F hV hMv hβ)
  have hZp : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZge
  have hlimρ : ∀ x, ρ x = Real.exp (Φ x) / Z := by
    intro x
    have h1 : Tendsto (fun j => ρs (φ j) x) atTop (𝓝 (Real.exp (Φ x) / Z)) := by
      have := (((tendsto_const_nhds (x := -β)).mul
        ((tendsto_const_nhds (x := V x)).add (hu x))).rexp).div hZ hZp.ne'
      exact this.congr (fun j => ((hρs (φ j)).eq x).symm)
    exact tendsto_nhds_unique (hpt x) h1
  have hint : ∫ x, ρ x = 1 := by
    have h1 := tendsto_integral_of_dominated_convergence (μ := volume) (fun _ => Lb)
      (F := fun j x => ρs (φ j) x) (f := ρ)
      (fun j => (hρs (φ j)).cont.aestronglyMeasurable) (integrable_const _)
      (fun j => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos ((hρs _).pos x)]; exact hup _ x)
      (Filter.Eventually.of_forall hpt)
    exact tendsto_nhds_unique h1
      (tendsto_const_nhds.congr (fun j => ((hρs (φ j)).int_one).symm))
  have hlb0 : 0 < lb := Real.exp_pos _
  have hlo' : ∀ x, lb ≤ ρ x := fun x =>
    ge_of_tendsto (hpt x) (Filter.Eventually.of_forall fun j => hlo _ x)
  have hup' : ∀ x, ρ x ≤ Lb := fun x =>
    le_of_tendsto (hpt x) (Filter.Eventually.of_forall fun j => hup _ x)
  exact ⟨ρ, ⟨⟨fun x => (hlb0.trans_le (hlo' x)).le, hρc.measurable, hint⟩, fun x => hlimρ x⟩, hρc,
    fun x => ⟨hlo' x, hup' x⟩⟩


/-! ### Existence of the thermal equilibrium from the truncated problems -/

/-- **Thermal existence from the Fejér-truncated problems** (plan §3.1: uniform bounds,
equicontinuity, Arzelà–Ascoli, limit).  The two-sided bounds `lam ≤ ρ ≤ Lam` are uniform in
`β ∈ [βm, βp]`. -/
theorem thermal_exists_of_truncated (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (V : Torus d → ℝ) (hV : Continuous V) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp)
    (htrunc : ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 0 < N → ∃ ρ : Torus d → ℝ, Continuous ρ ∧
      (∀ x, 0 < ρ x) ∧ ∫ x, ρ x = 1 ∧ ∀ x, ρ x =
        Real.exp (-β * (V x + convFun (truncKernel d s N) ρ x)) /
        ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y))) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ β ∈ Set.Icc βm βp, ∃ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρ ∧ Continuous ρ ∧
        ∀ x, lam ≤ ρ x ∧ ρ x ≤ Lam := by
  obtain ⟨M0, hM0⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨B0, hB0⟩ := F.bddBelow
  have hMv : ∀ x, |V x| ≤ |M0| := fun x => by
    have := hM0 x (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hB : ∀ x, -|B0| ≤ periodicRiesz d s x := fun x =>
    le_trans (neg_le_neg (le_abs_self B0)) (hB0 x)
  set Mv := |M0| with hMvdef
  set B := |B0| with hBdef
  have hMv0 : 0 ≤ Mv := abs_nonneg _
  have hB0' : 0 ≤ B := abs_nonneg _
  set L1 := ∫ y, |periodicRiesz d s y| with hL1def
  have hL1 : 0 ≤ L1 := integral_nonneg fun y => abs_nonneg _
  set Lp := Real.exp (βp * (2 * Mv + B)) with hLp
  refine ⟨Real.exp (-2 * βp * (Mv + L1 * Lp)), Lp, Real.exp_pos _, fun β hβ => ?_⟩
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have H : ∀ n : ℕ, ∃ ρ, TruncSol s V β (n + 1) ρ := fun n => by
    obtain ⟨ρ, hc, hp, hi, he⟩ := htrunc β hβ (n + 1) (Nat.succ_pos n)
    exact ⟨ρ, ⟨hc, hp, hi, he⟩⟩
  choose ρs hρs using H
  obtain ⟨ρ, hth, hc, hbd⟩ := thermal_exists_fixed F hV hMv hB hβpos ρs hρs
  have h1 : Real.exp (β * (2 * Mv + B)) ≤ Lp :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.2 (by positivity))
  have h2 : Mv + L1 * Real.exp (β * (2 * Mv + B)) ≤ Mv + L1 * Lp := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hL1]
  have h3 : β * (Mv + L1 * Real.exp (β * (2 * Mv + B))) ≤ βp * (Mv + L1 * Lp) :=
    mul_le_mul hβ.2 h2 (by positivity) (hβpos.le.trans hβ.2)
  refine ⟨ρ, hth, hc, fun x => ⟨?_, (hbd x).2.trans h1⟩⟩
  refine le_trans (Real.exp_le_exp.mpr ?_) (hbd x).1
  linarith

/-- Single-`β` version: a continuous thermal density with explicit two-sided bounds. -/
theorem thermal_exists_continuous_of_truncated (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (V : Torus d → ℝ) (hV : Continuous V) (β : ℝ) (hβ : 0 < β)
    (htrunc : ∀ N : ℕ, 0 < N → ∃ ρ : Torus d → ℝ, Continuous ρ ∧
      (∀ x, 0 < ρ x) ∧ ∫ x, ρ x = 1 ∧ ∀ x, ρ x =
        Real.exp (-β * (V x + convFun (truncKernel d s N) ρ x)) /
        ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y))) :
    ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρ ∧ Continuous ρ ∧
      ∃ lam Lam : ℝ, 0 < lam ∧ ∀ x, lam ≤ ρ x ∧ ρ x ≤ Lam := by
  obtain ⟨lam, Lam, hlam, h⟩ := thermal_exists_of_truncated hd s hs0 hsd F V hV β β hβ le_rfl
    (fun β' hβ' N hN => by
      have : β' = β := le_antisymm hβ'.2 hβ'.1
      subst this
      exact htrunc N hN)
  obtain ⟨ρ, hth, hc, hb⟩ := h β ⟨le_rfl, le_rfl⟩
  exact ⟨ρ, hth, hc, lam, Lam, hlam, hb⟩

end HRS.PDE.MFThermalExist
