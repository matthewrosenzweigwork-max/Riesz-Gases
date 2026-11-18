import HRS.MD.EQTraceLin
import HRS.MD.EQTraceMink
import HRS.Uniform.Q48cCov

/-!
# EQ-TRACE: `eq_trace_bound` and `eq_trace_bound_L2`

`‖C_N - C̄_β‖_{𝔖₁(E_M)} ≤ ∑_{kl} |(C_N - C̄_β)(e_k,e_l)|` (`eqtrace_traceNorm_le`), the entries are
`2β⁻¹ w_k w_l (μ_N(F_{kl}) - μ(F_{kl}))` with `F_{kl} = ∇e_k·∇e_l`, `|F_{kl}| ≤ 2d⟨k⟩⟨l⟩` (`Q48c.entry_eq`, `abs_Fkl_le`);
`E(μ_N(F) - μ(F))² ≤ K‖F‖²_∞ b_N²` (`eqtrace_test_L2`) and Minkowski (`eqtrace_mink`) give the `L²` bound; the `L¹` bound follows
from Cauchy-Schwarz.  Needs `M > d+1` (`∑_k w_k⟨k⟩ < ∞`, `Q48c.summable_s`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQTrace

open HRS.Uniform.Q48c (wt Fkl continuous_Fkl abs_Fkl_le entry_eq sum_s_le summable_s wt_pos)
open HRS.MD.EQ29 (bracketBias)
open HRS.Uniform HRS.Main

variable {d : ℕ}

theorem basis_eq_eb (γ : ℝ) (k : NonzeroLattice d) :
    (HRS.Uniform.Q48c.basis d γ k : NegSobolev d γ) = eb γ k := by
  classical
  have := HilbertBasis.repr_symm_single (HRS.Uniform.Q48c.basis d γ) k
  exact this.symm.trans rfl

/-- The trace-norm majorant `S(X) = ∑_{kl} |Q_X(e_k,e_l)|` in `ℝ≥0∞`. -/
def traceMaj (M q : ℝ) (ρβ : Torus d → ℝ) {N : ℕ} (X : Config d N) : ℝ≥0∞ :=
  ∑' p : NonzeroLattice d × NonzeroLattice d,
    ‖(covForm M q (empirical X) - covForm M q (withDensityReal ρβ)) (eb M p.1) (eb M p.2)‖ₑ

theorem entry_eq' {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N) (k l : NonzeroLattice d) :
    (covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l) =
      2 * q * (wt M k * wt M l) * (pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) := by
  have := entry_eq hM hq hρ hN X k l
  rw [basis_eq_eb, basis_eq_eb] at this
  rw [this, pair_empirical (by omega) X (Fkl k l)]
  rfl

theorem abs_entry_le {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) (hρp : IsProbDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (k l : NonzeroLattice d) :
    |(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l)| ≤
      8 * q * d * ((wt M k * Lattice.jp k.1) * (wt M l * Lattice.jp l.1)) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρp
  rw [entry_eq' hM hq hρ hN X k l]
  set B : ℝ := 2 * d * (Lattice.jp k.1 * Lattice.jp l.1) with hB
  have hFB := abs_Fkl_le k l
  have hB0 : 0 ≤ B := by
    have := Torus.jp_pos k.1; have := Torus.jp_pos l.1; positivity
  have h1 : |pair (empirical X) (Fkl k l)| ≤ B := by
    rw [pair_empirical (by omega) X (Fkl k l), abs_mul, abs_of_pos (inv_pos.2 (by exact_mod_cast (by omega : 0 < N)))]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : |∑ i, Fkl k l (X i)| ≤ N * B := by
      calc |∑ i, Fkl k l (X i)| ≤ ∑ i, |Fkl k l (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hFB _
        _ = N * B := by simp
    calc (N : ℝ)⁻¹ * |∑ i, Fkl k l (X i)| ≤ (N : ℝ)⁻¹ * (N * B) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hN0.le)
      _ = B := by field_simp
  have h2 : |pair (withDensityReal ρ) (Fkl k l)| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ) (f := Fkl k l) (C := B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFB x)
    simpa [pair, Measure.real] using this
  have h3 : |pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith)
  have hw : 0 ≤ 2 * q * (wt M k * wt M l) := by
    have := wt_pos (m := M) k; have := wt_pos (m := M) l; positivity
  rw [abs_mul, abs_of_nonneg hw]
  calc 2 * q * (wt M k * wt M l) * |pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)|
      ≤ 2 * q * (wt M k * wt M l) * (2 * B) := mul_le_mul_of_nonneg_left h3 hw
    _ = _ := by rw [hB]; ring

theorem measurable_pair_empirical {g : Torus d → ℝ} (hg : Measurable g) {N : ℕ} (hN : 1 ≤ N) :
    Measurable fun X : Config d N => pair (empirical X) g := by
  have : (fun X : Config d N => pair (empirical X) g) = fun X => (N : ℝ)⁻¹ * ∑ i, g (X i) :=
    funext fun X => pair_empirical (by omega) X g
  rw [this]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i))

theorem measurable_entry' {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (k l : NonzeroLattice d) :
    Measurable fun X : Config d N =>
      (covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l) := by
  have : (fun X : Config d N =>
      (covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l)) =
      fun X => 2 * q * (wt M k * wt M l) *
        (pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) :=
    funext fun X => entry_eq' hM hq hρ hN X k l
  rw [this]
  exact measurable_const.mul
    ((measurable_pair_empirical (continuous_Fkl k l).measurable hN).sub measurable_const)

theorem eqtrace_b_nonneg {s : ℝ} (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ EQ29.bracketBias d s N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ0 : 0 ≤ deltaN d s N :=
    (inv_nonneg.2 hN0.le).trans (MarginalAux.inv_le_deltaN (d := d) hs0 N hN)
  unfold EQ29.bracketBias
  have := Real.rpow_nonneg hN0.le (-(1 : ℝ) / 2)
  linarith

theorem traceNorm_le_maj (hd : 2 ≤ d) {M : ℝ} (hM : (d : ℝ) + 1 < M) {q : ℝ} (hq : 0 ≤ q)
    {ρ : Torus d → ℝ} (hρ : Continuous ρ) (hρp : IsProbDensity ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Config d N) :
    ENNReal.ofReal (traceNormForm (covForm M q (empirical X) - covForm M q (withDensityReal ρ))) ≤
      traceMaj M q ρ X := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < M := by linarith
  have hs0 := summable_s (d := d) hM
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt M k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hprod : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      (wt M p.1 * Lattice.jp p.1.1) * (wt M p.2 * Lattice.jp p.2.1) := hs0.mul_of_nonneg hs0 hnn hnn
  have hsum : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      |(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M p.1) (eb M p.2)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun p => abs_entry_le hM2 hq hρ hρp hN X p.1 p.2) (hprod.mul_left (8 * q * d))
  have h1 := eqtrace_traceNorm_le (covForm M q (empirical X) - covForm M q (withDensityReal ρ)) hsum
  calc ENNReal.ofReal (traceNormForm (covForm M q (empirical X) - covForm M q (withDensityReal ρ)))
      ≤ ENNReal.ofReal (∑' p : NonzeroLattice d × NonzeroLattice d,
          |(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M p.1) (eb M p.2)|) :=
        ENNReal.ofReal_le_ofReal h1
    _ = traceMaj M q ρ X := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hsum]
        unfold traceMaj
        refine tsum_congr fun p => ?_
        rw [Real.enorm_eq_ofReal_abs]

theorem measurable_traceMaj {M : ℝ} (hM2 : (d : ℝ) / 2 + 2 < M) {q : ℝ} (hq : 0 ≤ q)
    {ρ : Torus d → ℝ} (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) :
    Measurable fun X : Config d N => traceMaj M q ρ X :=
  Measurable.tsum fun p => (measurable_entry' hM2 hq hρ hN p.1 p.2).enorm

theorem eqtrace_setup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      Continuous ρβ ∧ IsProbDensity ρβ ∧
        IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨Lam, hLam⟩ := MD.EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  intro β hβ ρβ hρ N hN
  obtain ⟨hρs, hΛ, hP⟩ := hLam β hβ ρβ hρ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hPm : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := hP N
  refine ⟨PoleCavityAux.continuous_of_smoothPos hρs, hρs.density, ?_⟩
  rw [hPm]
  exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ0 (Λ := max Lam 1) (le_max_right _ _) hρs.density
    (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)

theorem eqtrace_real_id (q d K b wk wl jk jl : ℝ) (hK : 0 ≤ K) :
    (2 * q * (wk * wl)) ^ 2 * (K * (2 * d * (jk * jl)) ^ 2 * b ^ 2) =
      ((4 * q * d * Real.sqrt K * b) * ((wk * jk) * (wl * jl))) ^ 2 := by
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
  linear_combination (-(16 * q ^ 2 * d ^ 2 * b ^ 2 * ((wk * jk) * (wl * jl)) ^ 2)) * hsq

theorem eqtrace_term {M : ℝ} (hM2 : (d : ℝ) / 2 + 2 < M) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) {N : ℕ} (hN : 1 ≤ N) (P : Measure (Config d N)) (K b : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (k l : NonzeroLattice d)
    (h1 : ∫⁻ X, ENNReal.ofReal ((pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) ^ 2) ∂P ≤
      ENNReal.ofReal (K * (2 * (d : ℝ) * (Lattice.jp k.1 * Lattice.jp l.1)) ^ 2 * b ^ 2)) :
    ∫⁻ X, ‖(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((4 * q * d * Real.sqrt K * b) * ((wt M k * Lattice.jp k.1) * (wt M l * Lattice.jp l.1))) ^ 2 := by
  have hc0 : 0 ≤ (2 * q * (wt M k * wt M l)) ^ 2 := sq_nonneg _
  have e1 : ∀ X : Config d N,
      ‖(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l)‖ₑ ^ 2 =
        ENNReal.ofReal ((2 * q * (wt M k * wt M l)) ^ 2) *
          ENNReal.ofReal ((pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) ^ 2) := by
    intro X
    rw [entry_eq' hM2 hq hρ hN X k l, eqtrace_enorm_sq, ← ENNReal.ofReal_mul hc0]
    congr 1; ring
  have hmeas : Measurable fun X : Config d N =>
      ENNReal.ofReal ((pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_pair_empirical (continuous_Fkl k l).measurable hN).sub measurable_const).pow_const 2)
  have hwk := wt_pos (m := M) k
  have hwl := wt_pos (m := M) l
  have hjk := Torus.jp_pos k.1
  have hjl := Torus.jp_pos l.1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hpow : 0 ≤ (4 * q * d * Real.sqrt K * b) * ((wt M k * Lattice.jp k.1) * (wt M l * Lattice.jp l.1)) := by
    positivity
  calc ∫⁻ X, ‖(covForm M q (empirical X) - covForm M q (withDensityReal ρ)) (eb M k) (eb M l)‖ₑ ^ 2 ∂P
      = ∫⁻ X, ENNReal.ofReal ((2 * q * (wt M k * wt M l)) ^ 2) *
          ENNReal.ofReal ((pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) ^ 2) ∂P :=
        lintegral_congr e1
    _ = ENNReal.ofReal ((2 * q * (wt M k * wt M l)) ^ 2) *
          ∫⁻ X, ENNReal.ofReal ((pair (empirical X) (Fkl k l) - pair (withDensityReal ρ) (Fkl k l)) ^ 2) ∂P :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal ((2 * q * (wt M k * wt M l)) ^ 2) *
          ENNReal.ofReal (K * (2 * (d : ℝ) * (Lattice.jp k.1 * Lattice.jp l.1)) ^ 2 * b ^ 2) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal ((2 * q * (wt M k * wt M l)) ^ 2 *
          (K * (2 * (d : ℝ) * (Lattice.jp k.1 * Lattice.jp l.1)) ^ 2 * b ^ 2)) :=
        (ENNReal.ofReal_mul hc0).symm
    _ = ENNReal.ofReal ((4 * q * d * Real.sqrt K * b) * ((wt M k * Lattice.jp k.1) * (wt M l * Lattice.jp l.1))) ^ 2 := by
        rw [eqtrace_real_id q d K b (wt M k) (wt M l) (Lattice.jp k.1) (Lattice.jp l.1) hK,
          ENNReal.ofReal_pow hpow]

theorem eqtrace_key (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) + 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, traceMaj M β⁻¹ ρβ X ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * EQ29.bracketBias d s N) ^ 2) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < M := by linarith
  obtain ⟨K, hK, hT⟩ := eqtrace_test_L2 hd hs0 hsd V hV βm βp hβm hββ
  have hsetup := eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt M k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑' k : NonzeroLattice d, wt M k * Lattice.jp k.1 := ⟨_, rfl⟩
  have hS : 0 ≤ S := hSdef ▸ tsum_nonneg hnn
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  refine ⟨4 * βm⁻¹ * d * Real.sqrt K * S ^ 2 + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ N hN
  obtain ⟨hρc, hρp, hPr⟩ := hsetup β hβ ρβ hρ N hN
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ0.le
  have hqle : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = 4 * β⁻¹ * d * Real.sqrt K * EQ29.bracketBias d s N := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hterm : ∀ p : NonzeroLattice d × NonzeroLattice d,
      ∫⁻ X, ‖(covForm M β⁻¹ (empirical X) - covForm M β⁻¹ (withDensityReal ρβ))
          (eb M p.1) (eb M p.2)‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (K' * ((wt M p.1 * Lattice.jp p.1.1) * (wt M p.2 * Lattice.jp p.2.1))) ^ 2 := by
    intro p
    rw [hK']
    exact eqtrace_term hM2 hq hρc hN1 _ K (EQ29.bracketBias d s N) hK.le hb0 p.1 p.2
      (hT β hβ ρβ hρ N hN (Fkl p.1 p.2) _ (continuous_Fkl p.1 p.2) (abs_Fkl_le p.1 p.2))
  have hmain : ∫⁻ X, traceMaj M β⁻¹ ρβ X ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
      (∑' p : NonzeroLattice d × NonzeroLattice d,
        ENNReal.ofReal (K' * ((wt M p.1 * Lattice.jp p.1.1) * (wt M p.2 * Lattice.jp p.2.1)))) ^ 2 :=
    eqtrace_mink _ (fun (p : NonzeroLattice d × NonzeroLattice d) (X : Config d N) => ‖(covForm M β⁻¹ (empirical X) - covForm M β⁻¹ (withDensityReal ρβ))
        (eb M p.1) (eb M p.2)‖ₑ)
      (fun p => (measurable_entry' hM2 hq hρc hN1 p.1 p.2).enorm) _ hterm
  rw [sum_s_le hM K' hK'0, ← hSdef] at hmain
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_pow (by rw [hK']; positivity)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by rw [hK']; positivity) ?_ 2)
  have h4 : 0 ≤ 4 * (d : ℝ) * Real.sqrt K * S ^ 2 * EQ29.bracketBias d s N := by positivity
  calc K' * S ^ 2 = β⁻¹ * (4 * (d : ℝ) * Real.sqrt K * S ^ 2 * EQ29.bracketBias d s N) := by
        rw [hK']; ring
    _ ≤ βm⁻¹ * (4 * (d : ℝ) * Real.sqrt K * S ^ 2 * EQ29.bracketBias d s N) :=
        mul_le_mul_of_nonneg_right hqle h4
    _ ≤ _ := by nlinarith

theorem eq_trace_bound_L2_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) + 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ENNReal.ofReal (traceNormForm
            (covForm M β⁻¹ (empirical X) - covForm M β⁻¹ (withDensityReal ρβ))) ^ 2
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * bracketBias d s N) ^ 2) := by
  obtain ⟨C, hC, hk⟩ := eqtrace_key hd hs0 hsd V hV βm βp hβm hββ M hM
  have hsetup := eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ
  refine ⟨C, hC, fun β hβ ρβ hρ N hN => ?_⟩
  obtain ⟨hρc, hρp, hPr⟩ := hsetup β hβ ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 (lt_of_lt_of_le hβm hβ.1).le
  refine le_trans (lintegral_mono fun X => ?_) (hk β hβ ρβ hρ N hN)
  exact pow_le_pow_left' (traceNorm_le_maj hd hM hq hρc hρp (by omega) X) 2

theorem eq_trace_bound_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) + 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ENNReal.ofReal (traceNormForm
            (covForm M β⁻¹ (empirical X) - covForm M β⁻¹ (withDensityReal ρβ)))
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * bracketBias d s N) := by
  obtain ⟨C, hC, hk⟩ := eqtrace_key hd hs0 hsd V hV βm βp hβm hββ M hM
  have hsetup := eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ
  refine ⟨C, hC, fun β hβ ρβ hρ N hN => ?_⟩
  obtain ⟨hρc, hρp, hPr⟩ := hsetup β hβ ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 (lt_of_lt_of_le hβm hβ.1).le
  have hN1 : 1 ≤ N := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < M := by linarith
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  have hCb : 0 ≤ C * bracketBias d s N := mul_nonneg hC.le hb0
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  set f : Config d N → ℝ≥0∞ := fun X => traceMaj M β⁻¹ ρβ X with hf
  have hfm : Measurable f := measurable_traceMaj hM2 hq hρc hN1
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    hfm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h2 : ∫⁻ X, f X ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal ((C * bracketBias d s N) ^ 2) := by
    simpa [ENNReal.rpow_two, hf] using hk β hβ ρβ hρ N hN
  calc ∫⁻ X, ENNReal.ofReal (traceNormForm
            (covForm M β⁻¹ (empirical X) - covForm M β⁻¹ (withDensityReal ρβ))) ∂P
      ≤ ∫⁻ X, f X ∂P := lintegral_mono fun X => traceNorm_le_maj hd hM hq hρc hρp hN1 X
    _ ≤ (∫⁻ X, f X ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by simpa using hH
    _ ≤ (ENNReal.ofReal ((C * bracketBias d s N) ^ 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (C * bracketBias d s N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hCb]

end HRS.MD.EQTrace
