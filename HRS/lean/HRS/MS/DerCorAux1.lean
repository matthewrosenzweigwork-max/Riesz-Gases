import HRS.MS.ThCorr
import HRS.MS.R2ScrAux2
import HRS.MS.PoisFinal
import HRS.MS.GapRefAux2

/-!
# S4.8 `derivative_corrector`, part 1: the derivative-only resolvent representative

Namespace `HRS.MS.S48`; helper lemmas carry the prefix `s48_`.  No existing file is edited.

Route (S lines 2842-2918): for `φ ∈ C_b^J` the response `r₀ = γ (I+γK)⁻¹ P_μ φ` is written, by the finite resolvent
identity `r₀ = γ ∑_{j<M} (-γ)^j K^j P_μ φ + (-γ)^M K^M r₀`, as `γ P_μ φ` (whose positive-order derivatives are those of `φ`)
plus terms `K^j P_μ φ`, `j ≥ 1`, and `K^M r₀`, which are bounded in `C_b^m` by the weighted Sobolev machinery of S4.4
(`HRS.MS.Tc5`).

* `s48_rho_deriv`: `‖D^jρ‖ ≤ K ρ (1+|x|)^j` from the drift structure `∇ρ = ρ(-q x + B)`, `B ∈ C_b^J`.
* `s48_P_data`: the weighted product estimate `‖ρ P_μ φ‖_{H^J(dx)} ≤ K (‖P_μ φ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞)`
  (`W:eq:r2-derivative-weighted-product`), for `φ ∈ C_b^J` (only positive-order derivatives of `φ` enter).
* `s48_terms`, `s48_resolvent`: the terms `K^j P_μ φ` (`1 ≤ j < M`), and the `C^m` representative `r` of `r₀`
  with `‖D^i r‖_∞ ≤ C (‖P_μ φ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞)` for `1 ≤ i ≤ m`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.MS.S48

open HRS HRS.Whole

local notation "MemSob" => HRS.PDE.ToolboxRd.MemSobolev
local notation "SobSq" => HRS.PDE.ToolboxRd.sobolevNormSq

variable {d : ℕ}

/-! ### Derivatives of the drift `b = -q x + B` -/

/-- the first derivative of the dilation `y ↦ c • y` is bounded by `|c|`, the higher ones vanish. -/
theorem s48_lin_deriv (c : ℝ) (l : ℕ) (hl : 1 ≤ l) (x : Euc d) :
    ‖iteratedFDeriv ℝ l (fun y : Euc d => c • y) x‖ ≤ |c| := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hf : fderiv ℝ (fun y : Euc d => c • y) = fun _ => c • ContinuousLinearMap.id ℝ (Euc d) := by
    funext y
    exact ((hasFDerivAt_id y).const_smul c).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf]
  rcases n with _ | n
  · rw [norm_iteratedFDeriv_zero]
    calc ‖c • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = |c| := by simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp

theorem s48_b_deriv (q Mb : ℝ) (J : ℕ) {B : Euc d → Euc d} (hB : HasCbBound J Mb B) :
    ∀ l ≤ J, ∀ x, ‖iteratedFDeriv ℝ l (fun y => -q • y + B y) x‖ ≤ (|q| + Mb) * (1 + ‖x‖) := by
  intro l hl x
  have hM : 0 ≤ Mb := (norm_nonneg _).trans (hB.2 0 (Nat.zero_le _) 0)
  have hq : 0 ≤ |q| := abs_nonneg _
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · rw [norm_iteratedFDeriv_zero]
    have h1 := hB.2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h1
    calc ‖-q • x + B x‖ ≤ ‖-q • x‖ + ‖B x‖ := norm_add_le _ _
      _ ≤ |q| * ‖x‖ + Mb := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg]; exact add_le_add le_rfl h1
      _ ≤ _ := by nlinarith [norm_nonneg x]
  · have e : (fun y => -q • y + B y) = (fun y => -q • y) + B := rfl
    have hA : ContDiffAt ℝ l (fun y : Euc d => -q • y) x := (contDiff_const_smul (-q)).contDiffAt
    have hB' : ContDiffAt ℝ l B x := (hB.1.of_le (by exact_mod_cast hl)).contDiffAt
    rw [e, iteratedFDeriv_add_apply hA hB']
    refine (norm_add_le _ _).trans ?_
    have h1 := s48_lin_deriv (-q) l hl1 x
    rw [abs_neg] at h1
    have h2 := hB.2 l hl x
    nlinarith [norm_nonneg x]

/-! ### The density: `‖D^j ρ‖ ≤ K ρ (1+|x|)^j` -/

theorem s48_fderiv_rho {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    fderiv ℝ ρ = fun y => ρ y • InnerProductSpace.toDual ℝ (Euc d) (-q • y + B y) := by
  funext y
  ext v
  rw [HRS.MS.Gap.gap1_fderiv_rho (b := fun y => -q • y + B y) hR.grad y v]
  simp only [smul_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [real_inner_comm]

/-- the real-linear isometry `toDual`. -/
def s48_T (d : ℕ) : Euc d ≃ₗᵢ[ℝ] (Euc d →L[ℝ] ℝ) := InnerProductSpace.toDual ℝ (Euc d)

theorem s48_fderiv_rho' {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    fderiv ℝ ρ = fun y => ρ y • s48_T d (-q • y + B y) := s48_fderiv_rho hR

theorem s48_rho_deriv (qb Mb : ℝ) (J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| ≤ qb → ∀ (B : Euc d → Euc d) (ρ : Euc d → ℝ),
      HRS.MS.Gap.GapRef d ρ q B →
      HasCbBound J Mb B → ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ K * ρ x * (1 + ‖x‖) ^ j := by
  have key : ∀ n : ℕ, n ≤ J → ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| ≤ qb → ∀ (B : Euc d → Euc d) (ρ : Euc d → ℝ),
      HRS.MS.Gap.GapRef d ρ q B → HasCbBound J Mb B → ∀ j ≤ n, ∀ x,
        ‖iteratedFDeriv ℝ j ρ x‖ ≤ K * ρ x * (1 + ‖x‖) ^ j := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨1, zero_le_one, fun q hq B ρ hR hB j hj x => ?_⟩
      obtain rfl : j = 0 := by omega
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hR.pos x)]
      simp
    | succ n ih =>
      intro hn
      obtain ⟨K, hK0, hK⟩ := ih (by omega)
      refine ⟨K + K * ((|qb| + |Mb|) * 2 ^ n), by positivity, fun q hq B ρ hR hB j hj x => ?_⟩
      have hρ0 : 0 < ρ x := hR.pos x
      have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · have := hK q hq B ρ hR hB j (by omega) x
        refine this.trans ?_
        have h1 : 0 ≤ K * ρ x * (1 + ‖x‖) ^ j := by positivity
        have h2 : 0 ≤ K * ((|qb| + |Mb|) * 2 ^ n) * ρ x * (1 + ‖x‖) ^ j := by positivity
        nlinarith
      · obtain rfl : j = n + 1 := by omega
        have hρs : ContDiff ℝ n ρ := hR.smooth.of_le (by exact_mod_cast le_top)
        have hbs : ContDiff ℝ n (fun y => -q • y + B y) :=
          ((contDiff_const_smul (-q)).add (hB.1.of_le (by exact_mod_cast (by omega : n ≤ J))))
        have hTs : ContDiff ℝ n (fun y => s48_T d (-q • y + B y)) := (s48_T d).contDiff.comp hbs
        rw [← norm_iteratedFDeriv_fderiv, s48_fderiv_rho' hR]
        refine (norm_iteratedFDeriv_smul_le hρs hTs x (le_refl _)).trans ?_
        have hb := s48_b_deriv q Mb J hB
        have hterm : ∀ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ρ x‖ *
              ‖iteratedFDeriv ℝ (n - i) (fun y => s48_T d (-q • y + B y)) x‖ ≤
            (n.choose i : ℝ) * (K * ρ x * (1 + ‖x‖) ^ n * ((|qb| + |Mb|) * (1 + ‖x‖))) := by
          intro i hi
          have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 := hK q hq B ρ hR hB i (by omega) x
          have h2 : ‖iteratedFDeriv ℝ (n - i) (fun y => s48_T d (-q • y + B y)) x‖ ≤
              (|qb| + |Mb|) * (1 + ‖x‖) := by
            have e := (s48_T d).norm_iteratedFDeriv_comp_left (fun y => -q • y + B y) x (i := n - i)
            have e' : iteratedFDeriv ℝ (n - i) (fun y => s48_T d (-q • y + B y)) x =
                iteratedFDeriv ℝ (n - i) (s48_T d ∘ fun y => -q • y + B y) x := rfl
            rw [e', e]
            refine (hb (n - i) (by omega) x).trans ?_
            exact mul_le_mul_of_nonneg_right
              (add_le_add (hq.trans (le_abs_self _)) (le_abs_self _)) (by linarith)
          have h3 : (1 + ‖x‖) ^ i ≤ (1 + ‖x‖) ^ n := pow_le_pow_right₀ hx1 hi'
          have h4 : 0 ≤ ‖iteratedFDeriv ℝ i ρ x‖ := norm_nonneg _
          have h5 : 0 ≤ K * ρ x := by positivity
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) _)
          calc ‖iteratedFDeriv ℝ i ρ x‖ * ‖iteratedFDeriv ℝ (n - i) (fun y => s48_T d (-q • y + B y)) x‖
              ≤ (K * ρ x * (1 + ‖x‖) ^ i) * ((|qb| + |Mb|) * (1 + ‖x‖)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ ≤ (K * ρ x * (1 + ‖x‖) ^ n) * ((|qb| + |Mb|) * (1 + ‖x‖)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h5) (by positivity)
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.sum_mul, show (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n by
          exact_mod_cast Nat.sum_range_choose n]
        have h6 : 0 ≤ K * ρ x * (1 + ‖x‖) ^ (n + 1) := by positivity
        calc 2 ^ n * (K * ρ x * (1 + ‖x‖) ^ n * ((|qb| + |Mb|) * (1 + ‖x‖)))
            = K * ((|qb| + |Mb|) * 2 ^ n) * ρ x * (1 + ‖x‖) ^ (n + 1) := by ring
          _ ≤ (K + K * ((|qb| + |Mb|) * 2 ^ n)) * ρ x * (1 + ‖x‖) ^ (n + 1) := by
              have : 0 ≤ ρ x * (1 + ‖x‖) ^ (n + 1) := by positivity
              nlinarith
  obtain ⟨K, hK0, hK⟩ := key J le_rfl
  exact ⟨K, hK0, fun q hq B ρ hR hB j hj x => hK q hq B ρ hR hB j hj x⟩

/-! ### The derivative-only norm and the weighted product estimate -/

/-- `∑_{j=1}^J ‖D^jφ‖_∞`. -/
def s48_Dn (J : ℕ) (φ : Euc d → ℝ) : ℝ := ∑ j ∈ Finset.range J, ⨆ y, ‖iteratedFDeriv ℝ (j + 1) φ y‖

/-- `‖P_μ φ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞`. -/
def s48_Q (μ : Measure (Euc d)) (J : ℕ) (φ : Euc d → ℝ) : ℝ :=
  HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) + s48_Dn J φ

theorem s48_Dn_nonneg (J : ℕ) (φ : Euc d → ℝ) : 0 ≤ s48_Dn J φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem s48_Q_nonneg (μ : Measure (Euc d)) (J : ℕ) (φ : Euc d → ℝ) : 0 ≤ s48_Q μ J φ :=
  add_nonneg (Real.sqrt_nonneg _) (s48_Dn_nonneg J φ)

theorem s48_Dn_ge {J : ℕ} {φ : Euc d → ℝ} (hφ : MemCb J φ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ J)
    (y : Euc d) : ‖iteratedFDeriv ℝ i φ y‖ ≤ s48_Dn J φ := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  calc ‖iteratedFDeriv ℝ (n + 1) φ y‖ ≤ ⨆ y, ‖iteratedFDeriv ℝ (n + 1) φ y‖ := le_ciSup (hφ.2 _ h2) y
    _ ≤ s48_Dn J φ := Finset.single_le_sum (f := fun j => ⨆ y, ‖iteratedFDeriv ℝ (j + 1) φ y‖)
        (fun j _ => Real.iSup_nonneg fun y => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem s48_psi_deriv {φ : Euc d → ℝ} {J : ℕ} (hφ : ContDiff ℝ J φ) (p : ℝ) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ J) (y : Euc d) :
    iteratedFDeriv ℝ i (fun x => φ x - p) y = iteratedFDeriv ℝ i φ y := by
  have e : (fun x => φ x - p) = φ - fun _ => p := rfl
  rw [e, iteratedFDeriv_sub_apply (hφ.of_le (by exact_mod_cast h2)).contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]

theorem s48_cb_bound {J : ℕ} {φ : Euc d → ℝ} (hφ : MemCb J φ) : ∃ B0 : ℝ, ∀ y, ‖φ y‖ ≤ B0 := by
  obtain ⟨B0, hB0⟩ := hφ.2 0 (Nat.zero_le _)
  exact ⟨B0, fun y => by simpa using hB0 ⟨y, rfl⟩⟩

/-- **The weighted product estimate** `W:eq:r2-derivative-weighted-product`:
`‖ρ P_μφ‖_{H^J(dx)} ≤ K (‖P_μφ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞)` for `φ ∈ C_b^J`, using only the drift structure
`∇ρ = ρ(-q x + B)` (`B ∈ C_b^J`) and a Gaussian bound on `ρ`. -/
theorem s48_P_data (qb Mb M₀ c : ℝ) (J : ℕ) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ, |q| ≤ qb → ∀ (B : Euc d → Euc d) (ρ : Euc d → ℝ), HRS.MS.Gap.GapRef d ρ q B →
      HasCbBound J Mb B → (∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) → ∀ φ : Euc d → ℝ, MemCb J φ →
        HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) ∧
        MemSob (J : ℝ) (fun y => ρ y * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ y) ∧
        Real.sqrt (SobSq (J : ℝ) (fun y => ρ y * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ y)) ≤
          K * s48_Q (HRS.Whole.withDensityReal ρ) J φ := by
  obtain ⟨K0, hK0, hK⟩ := s48_rho_deriv (d := d) qb Mb J
  obtain ⟨Cs, hCs0, hCs⟩ := HRS.MS.TcS.tcs_sobolev_of_hsmooth d J
  set A : ℝ := K0 * 2 ^ J with hA
  have hA0 : 0 ≤ A := by positivity
  set P : ℝ := |M₀| * ∑ j ∈ Finset.range (J + 1), HRS.MS.Tc5.tc5_Kp c (2 * j) with hP
  have hP0 : 0 ≤ P := mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => HRS.MS.Tc5.tc5_Kp_nonneg c _)
  set L : ℝ := Real.sqrt (2 * A ^ 2 * P) with hL
  refine ⟨Real.sqrt Cs * (((J : ℝ) + 1) * L), by positivity, fun q hq B ρ hR hB hg φ hφ => ?_⟩
  have hprob := HRS.MS.Gap.gap1_isProb hR
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hm : Measurable ρ := hR.smooth.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hR.pos x).le
  set p0 := HRS.Whole.pair μ φ with hp0
  set ψ : Euc d → ℝ := HRS.Whole.projMean μ φ with hψ
  have hψe : ψ = fun x => φ x - p0 := rfl
  obtain ⟨B0, hB0⟩ := s48_cb_bound hφ
  have hψs : ContDiff ℝ J ψ := by rw [hψe]; exact hφ.1.sub contDiff_const
  have hψb : ∀ x, |ψ x| ≤ B0 + |p0| := fun x => by
    rw [hψe]
    have := hB0 x
    rw [Real.norm_eq_abs] at this
    calc |φ x - p0| ≤ |φ x| + |p0| := abs_sub _ _
      _ ≤ _ := by linarith
  have hφ2 : MemLp φ 2 μ := HRS.MS.Tc5.tc5_memLp_of_cb hφ
  have hP0' : HRS.Whole.MemL2Zero μ ψ := by
    have := HRS.MS.TcR.tc_memL2Zero_smul_projMean (ρ := ρ)
      ⟨hρ0, hm, hR.integral_one⟩ hφ2 1
    simpa using this
  set Dn := s48_Dn J φ with hDn
  have hDn0 : 0 ≤ Dn := s48_Dn_nonneg J φ
  set u : Euc d → ℝ := fun y => ρ y * ψ y with hu
  have hus : ContDiff ℝ J u := (hR.smooth.of_le (by exact_mod_cast le_top)).mul hψs
  -- pointwise bound
  have hpt : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ A * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|) := by
    intro j hj x
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ρ) (g := ψ) (N := (J : ℕ∞ω))
      (hR.smooth.of_le (by exact_mod_cast le_top)) hψs x (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ρ x‖ * ‖iteratedFDeriv ℝ (j - i) ψ x‖ ≤
          (j.choose i : ℝ) * (K0 * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|)) := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have e1 := hK q hq B ρ hR hB i (by omega) x
      have e2 : ‖iteratedFDeriv ℝ (j - i) ψ x‖ ≤ Dn + |ψ x| := by
        rcases Nat.eq_zero_or_pos (j - i) with h0 | h0
        · rw [h0, norm_iteratedFDeriv_zero]
          have : ‖ψ x‖ = |ψ x| := Real.norm_eq_abs _
          linarith
        · have e := s48_psi_deriv hφ.1 p0 h0 (by omega) x
          rw [show iteratedFDeriv ℝ (j - i) ψ x = iteratedFDeriv ℝ (j - i) φ x from e]
          have := s48_Dn_ge hφ h0 (by omega) x
          linarith [abs_nonneg (ψ x)]
      have e3 : (1 + ‖x‖) ^ i ≤ (1 + ‖x‖) ^ j := pow_le_pow_right₀ hx1 hi'
      have hT : 0 ≤ Dn + |ψ x| := by positivity
      have h5 : 0 ≤ K0 * ρ x := mul_nonneg hK0 (hρ0 x)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) _)
      calc ‖iteratedFDeriv ℝ i ρ x‖ * ‖iteratedFDeriv ℝ (j - i) ψ x‖
          ≤ (K0 * ρ x * (1 + ‖x‖) ^ i) * (Dn + |ψ x|) :=
            mul_le_mul e1 e2 (norm_nonneg _) (by have := hρ0 x; positivity)
        _ = (K0 * ρ x) * (1 + ‖x‖) ^ i * (Dn + |ψ x|) := by ring
        _ ≤ (K0 * ρ x) * (1 + ‖x‖) ^ j * (Dn + |ψ x|) := by gcongr
        _ = K0 * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, show (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j by
      exact_mod_cast Nat.sum_range_choose j]
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
    have h3 : 0 ≤ K0 * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|) := by
      have := hρ0 x; positivity
    calc 2 ^ j * (K0 * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|))
        ≤ 2 ^ J * (K0 * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|)) := mul_le_mul_of_nonneg_right h2 h3
      _ = A * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|) := by rw [hA]; ring
  -- square bound
  have hsq : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ^ 2 ≤ 2 * A ^ 2 * P * (ρ x * (Dn ^ 2 + ψ x ^ 2)) := by
    intro j hj x
    have h1 := hpt j hj x
    have hρx := hρ0 x
    have hR0 : 0 ≤ ρ x * (1 + ‖x‖) ^ j := by positivity
    have h2 : ‖iteratedFDeriv ℝ j u x‖ ^ 2 ≤ (A * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ρ x * (1 + ‖x‖) ^ (2 * j) ≤ P := by
      have e1 := HRS.MS.Tc5.tc5_poly hc (2 * j) (norm_nonneg x)
      have e2 : ρ x * (1 + ‖x‖) ^ (2 * j) ≤ |M₀| * ((1 + ‖x‖) ^ (2 * j) * Real.exp (-c * ‖x‖ ^ 2)) := by
        have := hg x
        have hx0 : 0 ≤ (1 + ‖x‖) ^ (2 * j) := by positivity
        calc ρ x * (1 + ‖x‖) ^ (2 * j) ≤ (M₀ * Real.exp (-c * ‖x‖ ^ 2)) * (1 + ‖x‖) ^ (2 * j) :=
              mul_le_mul_of_nonneg_right this hx0
          _ ≤ (|M₀| * Real.exp (-c * ‖x‖ ^ 2)) * (1 + ‖x‖) ^ (2 * j) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
                (Real.exp_pos _).le) hx0
          _ = _ := by ring
      refine e2.trans ?_
      refine (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)).trans ?_
      rw [hP]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Finset.single_le_sum (f := fun j => HRS.MS.Tc5.tc5_Kp c (2 * j))
        (fun j _ => HRS.MS.Tc5.tc5_Kp_nonneg c _) (Finset.mem_range.2 (by omega))
    have h4 : (ρ x * (1 + ‖x‖) ^ j) ^ 2 ≤ P * ρ x := by
      have : (ρ x * (1 + ‖x‖) ^ j) ^ 2 = ρ x * (ρ x * (1 + ‖x‖) ^ (2 * j)) := by
        rw [pow_mul']; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left h3 hρx]
    have h5 : (Dn + |ψ x|) ^ 2 ≤ 2 * (Dn ^ 2 + ψ x ^ 2) := by
      nlinarith [sq_nonneg (Dn - |ψ x|), sq_abs (ψ x)]
    calc ‖iteratedFDeriv ℝ j u x‖ ^ 2 ≤ (A * (ρ x * (1 + ‖x‖) ^ j) * (Dn + |ψ x|)) ^ 2 := h2
      _ = A ^ 2 * (ρ x * (1 + ‖x‖) ^ j) ^ 2 * (Dn + |ψ x|) ^ 2 := by ring
      _ ≤ A ^ 2 * (P * ρ x) * (2 * (Dn ^ 2 + ψ x ^ 2)) := by
          gcongr
      _ = 2 * A ^ 2 * P * (ρ x * (Dn ^ 2 + ψ x ^ 2)) := by ring
  -- integrability and the integral of the majorant
  set g : Euc d → ℝ := fun x => ρ x * (Dn ^ 2 + ψ x ^ 2) with hgdef
  have hψc : Continuous ψ := hψs.continuous
  have hρψ : Integrable (fun x => ρ x * ψ x ^ 2) := by
    refine (hR.integrable.const_mul ((B0 + |p0|) ^ 2)).mono'
      (hR.smooth.continuous.mul (hψc.pow 2)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x), abs_of_nonneg (sq_nonneg _)]
    have : ψ x ^ 2 ≤ (B0 + |p0|) ^ 2 := by
      rw [← sq_abs (ψ x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hψb x) 2
    nlinarith [hρ0 x, mul_le_mul_of_nonneg_left this (hρ0 x)]
  have hgeq : g = fun x => Dn ^ 2 * ρ x + ρ x * ψ x ^ 2 := by funext x; simp only [hgdef]; ring
  have hgi : Integrable g := by
    rw [hgeq]
    exact (hR.integrable.const_mul _).add hρψ
  have hl2 : HRS.Whole.l2Norm μ ψ ^ 2 = ∫ x, ρ x * ψ x ^ 2 := by
    unfold HRS.Whole.l2Norm
    rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    exact HRS.MS.TcF.tc4_integral_wd hm hρ0 (fun y => ψ y ^ 2)
  have hgint : ∫ x, g x = Dn ^ 2 + HRS.Whole.l2Norm μ ψ ^ 2 := by
    rw [hgeq, integral_add (hR.integrable.const_mul _) hρψ, integral_const_mul, hR.integral_one, hl2]
    ring
  -- the Sobolev data
  have hmem : HRS.Whole.MemHSmooth J u := by
    refine ⟨hus, fun j hj => ?_⟩
    have hmeas : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ j u x) volume :=
      (hus.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine (hgi.const_mul (2 * A ^ 2 * P)).mono' (hmeas.norm.pow 2) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq j hj x
  have hint : ∀ j ≤ J, ∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ (2 : ℝ) ≤
      2 * A ^ 2 * P * (Dn ^ 2 + HRS.Whole.l2Norm μ ψ ^ 2) := by
    intro j hj
    have hmeas : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ j u x) volume :=
      (hus.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).aestronglyMeasurable
    simp only [Real.rpow_two]
    calc ∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ 2 ≤ ∫ x, 2 * A ^ 2 * P * g x :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (hgi.const_mul _)
            (Eventually.of_forall fun x => hsq j hj x)
      _ = _ := by rw [integral_const_mul, hgint]
  have hW : HRS.Whole.sobolevWNorm J 2 u ≤ ((J : ℝ) + 1) * (L * s48_Q μ J φ) := by
    unfold HRS.Whole.sobolevWNorm
    have hterm : ∀ j ∈ Finset.range (J + 1),
        (∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ L * s48_Q μ J φ := by
      intro j hj
      have hj' : j ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hnn : 0 ≤ ∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ (2 : ℝ) :=
        integral_nonneg fun x => by positivity
      calc (∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
          ≤ (2 * A ^ 2 * P * (Dn ^ 2 + HRS.Whole.l2Norm μ ψ ^ 2)) ^ (1 / (2 : ℝ)) :=
            Real.rpow_le_rpow hnn (hint j hj') (by norm_num)
        _ = Real.sqrt (2 * A ^ 2 * P) * Real.sqrt (Dn ^ 2 + HRS.Whole.l2Norm μ ψ ^ 2) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]
        _ ≤ L * s48_Q μ J φ := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            have hl0 : 0 ≤ HRS.Whole.l2Norm μ ψ := Real.sqrt_nonneg _
            calc Real.sqrt (Dn ^ 2 + HRS.Whole.l2Norm μ ψ ^ 2)
                ≤ Real.sqrt ((HRS.Whole.l2Norm μ ψ + Dn) ^ 2) :=
                  Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hl0 hDn0])
              _ = HRS.Whole.l2Norm μ ψ + Dn := Real.sqrt_sq (by positivity)
              _ = s48_Q μ J φ := rfl
    calc ∑ j ∈ Finset.range (J + 1), (∫ x, ‖iteratedFDeriv ℝ j u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        ≤ ∑ j ∈ Finset.range (J + 1), L * s48_Q μ J φ := Finset.sum_le_sum hterm
      _ = ((J : ℝ) + 1) * (L * s48_Q μ J φ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  obtain ⟨hs1, hs2⟩ := hCs u hmem
  refine ⟨hP0', hs1, ?_⟩
  have hW0 : 0 ≤ HRS.Whole.sobolevWNorm J 2 u := by
    unfold HRS.Whole.sobolevWNorm
    exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  calc Real.sqrt (SobSq (J : ℝ) u) ≤ Real.sqrt (Cs * HRS.Whole.sobolevWNorm J 2 u ^ 2) :=
        Real.sqrt_le_sqrt hs2
    _ = Real.sqrt Cs * HRS.Whole.sobolevWNorm J 2 u := by
        rw [Real.sqrt_mul hCs0, Real.sqrt_sq hW0]
    _ ≤ Real.sqrt Cs * (((J : ℝ) + 1) * (L * s48_Q μ J φ)) :=
        mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ### The terms `K^j P_μ φ`, `j ≥ 1`, and the resolvent representative -/

section Resolvent

open HRS.MS.Tc5 HRS.MS.TcDefs

theorem s48_l2_le_Q (μ : Measure (Euc d)) (J : ℕ) (φ : Euc d → ℝ) :
    HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ s48_Q μ J φ := by
  unfold s48_Q; linarith [s48_Dn_nonneg J φ]

theorem s48_Dn_le_Q (μ : Measure (Euc d)) (J : ℕ) (φ : Euc d → ℝ) : s48_Dn J φ ≤ s48_Q μ J φ := by
  have : 0 ≤ HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) := Real.sqrt_nonneg _
  unfold s48_Q; linarith

/-- The terms `K^j P_μ φ`, `1 ≤ j < M`, have `C_b^m` representatives bounded by the derivative-only norm. -/
theorem s48_terms {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J M : ℕ) (hJ : (m : ℝ) + d / 2 < J)
    (qb Mb M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) (hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N) :
    ∀ j : ℕ, 1 ≤ j → j < M → ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, |q| ≤ qb → ∀ (ρ : Euc d → ℝ) (B : Euc d → Euc d),
      TcRef d ρ M₀ c S N → HRS.MS.Gap.GapRef d ρ q B → HasCbBound J Mb B →
      ∀ φ : Euc d → ℝ, MemCb J φ →
      ∃ R : Euc d → ℝ, MemCb m R ∧ cbNorm m R ≤ C * s48_Q (HRS.Whole.withDensityReal ρ) J φ ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) := by
  have hα : 0 < (d : ℝ) - s := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by
    have : (0 : ℝ) ≤ (m : ℝ) + d / 2 := by positivity
    linarith
  intro j hj1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < M := by omega
  have hiα : (i : ℝ) * ((d : ℝ) - s) ≤ M * ((d : ℝ) - s) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hα.le
  obtain ⟨K, hK0, hK⟩ := s48_P_data (d := d) qb Mb M₀ c J hc
  obtain ⟨Ci, hCi0, hCi⟩ := tc5_iter_from (d := d) hs0 hsd (J : ℝ) hJ0 M₀ c S hc N i (by linarith)
  obtain ⟨Cr, hCr0, hCr⟩ := tc5_rep_step (d := d) hs0 hsd m ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s))
    (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hα.le; linarith) (by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hα.le; linarith) M₀ c S hc N
  refine ⟨Cr * (2 * Ci * (K + 1)), by positivity, fun q hq ρ B hρ hR hB φ hφ => ?_⟩
  have hprob := HRS.MS.TcF.tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hPm, hPs, hPn⟩ := hK q hq B ρ hR hB hρ.gauss φ hφ
  have hQ0 := s48_Q_nonneg μ J φ
  have hPl := s48_l2_le_Q μ J φ
  obtain ⟨hhm, hhl, hhs, hhn⟩ := hCi ρ hρ _ hPm hPs
  set h := (HRS.Whole.Kop (rieszKernel d s) μ)^[i] (HRS.Whole.projMean μ φ) with hh
  obtain ⟨R, hRcb, hRn, hRae⟩ := hCr ρ hρ h hhm hhs
  refine ⟨R, hRcb, ?_, ?_⟩
  · set Q := s48_Q μ J φ with hQ
    have hQ' : Real.sqrt (SobSq (J : ℝ) (fun y => ρ y * HRS.Whole.projMean μ φ y)) +
        HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ (K + 1) * Q := by nlinarith
    have h1 : Real.sqrt (SobSq ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
        HRS.Whole.l2Norm μ h ≤ 2 * Ci * ((K + 1) * Q) := by
      have := mul_le_mul_of_nonneg_left hQ' hCi0
      linarith
    calc cbNorm m R ≤ Cr * (Real.sqrt (SobSq ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
          HRS.Whole.l2Norm μ h) := hRn
      _ ≤ Cr * (2 * Ci * ((K + 1) * Q)) := mul_le_mul_of_nonneg_left h1 hCr0
      _ = _ := by ring
  · rw [Function.iterate_succ_apply']
    exact hRae

end Resolvent

section Resolvent2

open HRS.MS.Tc5 HRS.MS.TcDefs

/-- **The derivative-only resolvent representative.** For `m ≤ J`, `m + d/2 < M (d - s)`: the response `r₀` of
`r₀ + γ K r₀ = γ P_μ φ` has a `C^m` representative `r` with `‖D^i r‖_∞ ≤ C (‖P_μ φ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞)`
for `1 ≤ i ≤ m`, `C` independent of `ρ`, `γ ∈ (0, γp]`. -/
theorem s48_resolvent {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J M : ℕ) (hmJ : m ≤ J)
    (hJ : (m : ℝ) + d / 2 < J) (hM : (m : ℝ) + d / 2 < M * ((d : ℝ) - s)) (γp qb Mb M₀ c S : ℝ)
    (hc : 0 < c) (N : ℕ) (hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, |q| ≤ qb → ∀ (ρ : Euc d → ℝ) (B : Euc d → Euc d), TcRef d ρ M₀ c S N →
      HRS.MS.Gap.GapRef d ρ q B → HasCbBound J Mb B → ∀ γ : ℝ, 0 < γ → γ ≤ γp →
      ∀ φ : Euc d → ℝ, MemCb J φ →
        ∃ r₀ r : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
              γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
          ContDiff ℝ m r ∧
          (∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ x, ‖iteratedFDeriv ℝ i r x‖ ≤
            C * s48_Q (HRS.Whole.withDensityReal ρ) J φ) ∧
          r =ᵐ[HRS.Whole.withDensityReal ρ] r₀ := by
  have hα : 0 < (d : ℝ) - s := by linarith
  have hd1 : 1 ≤ d := by
    have : 0 < d := by exact_mod_cast (lt_of_le_of_lt hs0 hsd)
    exact this
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := by
    rcases M with _ | M'
    · exfalso
      have : (0 : ℝ) ≤ (m : ℝ) + d / 2 := by positivity
      simp at hM; linarith
    · exact ⟨M', rfl⟩
  obtain ⟨Cs, hCs0, hCs⟩ := tc5_smoothing (d := d) hs0 hsd m (M' + 1) hM M₀ c S hc N (by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith)
  have hterm := s48_terms hs0 hsd m J (M' + 1) hJ qb Mb M₀ c S hc N hN
  have hterm' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → j < M' + 1 → ∀ q : ℝ, |q| ≤ qb → ∀ (ρ : Euc d → ℝ) (B : Euc d → Euc d),
      TcRef d ρ M₀ c S N → HRS.MS.Gap.GapRef d ρ q B → HasCbBound J Mb B →
      ∀ φ : Euc d → ℝ, MemCb J φ →
      ∃ R : Euc d → ℝ, MemCb m R ∧ cbNorm m R ≤ C * s48_Q (HRS.Whole.withDensityReal ρ) J φ ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ)) := by
    intro j
    by_cases h : 1 ≤ j ∧ j < M' + 1
    · obtain ⟨C, hC0, hC⟩ := hterm j h.1 h.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Cj hCj0 hCj using hterm'
  set Sg : ℝ := ∑ j ∈ Finset.range M', |γp| ^ (j + 1) * Cj (j + 1) with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hCj0 _)
  refine ⟨|γp| + |γp| * Sg + |γp| ^ (M' + 1) * (Cs * |γp|), by positivity,
    fun q hq ρ B hρ hR hB γ hγ hγp φ hφ => ?_⟩
  have hprob := HRS.MS.TcF.tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set Q := s48_Q μ J φ with hQ
  have hQ0 : 0 ≤ Q := s48_Q_nonneg μ J φ
  have hφ2 : MemLp φ 2 μ := tc5_memLp_of_cb hφ
  have hP := HRS.MS.TcR.tc_memL2Zero_smul_projMean hρ.prob hφ2 γ
  obtain ⟨r₀, hr0, hreq, hrn⟩ := HRS.MS.TcR.tc_response hd1 hs0 hsd M₀ c S hc N ρ hρ γ hγ _ hP
  have hγ0 : γ ≤ |γp| := hγp.trans (le_abs_self _)
  have hγa : |γ| = γ := abs_of_pos hγ
  have hRex : ∀ j : ℕ, ∃ R : Euc d → ℝ, (1 ≤ j → j < M' + 1 → (MemCb m R ∧ cbNorm m R ≤ Cj j * Q ∧
      R =ᵐ[μ] (HRS.Whole.Kop (rieszKernel d s) μ)^[j] (HRS.Whole.projMean μ φ))) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j < M' + 1
    · obtain ⟨R, h1, h2, h3⟩ := hCj j hj.1 hj.2 q hq ρ B hρ hR hB φ hφ
      exact ⟨R, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose Rj hRj using hRex
  obtain ⟨R, hRcb, hRn, hRae⟩ := hCs ρ hρ r₀ hr0
  have hPn : HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ Q := s48_l2_le_Q μ J φ
  have hr0n : HRS.Whole.l2Norm μ r₀ ≤ γ * Q := by
    refine hrn.trans ?_
    have : HRS.Whole.l2Norm μ (γ • HRS.Whole.projMean μ φ) = γ * HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) := by
      have := tc5_l2_smul μ γ (HRS.Whole.projMean μ φ)
      rw [hγa] at this; exact this
    rw [this]
    exact mul_le_mul_of_nonneg_left hPn hγ.le
  set p0 := HRS.Whole.pair μ φ with hp0
  set r₁ : Euc d → ℝ := fun x => γ * ∑ j ∈ Finset.range M', (-γ) ^ (j + 1) * Rj (j + 1) x +
    (-γ) ^ (M' + 1) * R x with hr₁
  obtain ⟨hS1, hS2⟩ := tc5_cb_sum (fun j x => (-γ) ^ (j + 1) * Rj (j + 1) x) M'
    (fun j hj => (tc5_cb_smul ((-γ) ^ (j + 1)) (hRj (j + 1) (by omega) (by omega)).1).1)
  obtain ⟨hS3, hS4⟩ := tc5_cb_smul γ hS1
  obtain ⟨hS5, hS6⟩ := tc5_cb_smul ((-γ) ^ (M' + 1)) hRcb
  obtain ⟨hr1, hr2⟩ := tc5_cb_add hS3 hS5
  have hsum : ∑ j ∈ Finset.range M', cbNorm m (fun x => (-γ) ^ (j + 1) * Rj (j + 1) x) ≤ Sg * Q := by
    rw [hSg, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hjm => ?_
    have hj' := Finset.mem_range.1 hjm
    obtain ⟨hm1, hm2, -⟩ := hRj (j + 1) (by omega) (by omega)
    refine (tc5_cb_smul ((-γ) ^ (j + 1)) hm1).2.trans ?_
    rw [abs_pow, abs_neg, hγa]
    calc γ ^ (j + 1) * cbNorm m (Rj (j + 1)) ≤ |γp| ^ (j + 1) * (Cj (j + 1) * Q) :=
          mul_le_mul (pow_le_pow_left₀ hγ.le hγ0 _) hm2 (tc5_cb_nonneg _ _) (by positivity)
      _ = _ := by ring
  have hcb : cbNorm m r₁ ≤ γ * (Sg * Q) + γ ^ (M' + 1) * (Cs * (γ * Q)) := by
    have e1 : cbNorm m R ≤ Cs * (γ * Q) := hRn.trans (mul_le_mul_of_nonneg_left hr0n hCs0)
    have h1 : cbNorm m (fun x => γ * ∑ j ∈ Finset.range M', (-γ) ^ (j + 1) * Rj (j + 1) x) ≤
        γ * (Sg * Q) := by
      refine hS4.trans ?_
      rw [hγa]
      exact mul_le_mul_of_nonneg_left (hS2.trans hsum) hγ.le
    have h2 : cbNorm m (fun x => (-γ) ^ (M' + 1) * R x) ≤ γ ^ (M' + 1) * (Cs * (γ * Q)) := by
      refine hS6.trans ?_
      rw [abs_pow, abs_neg, hγa]
      exact mul_le_mul_of_nonneg_left e1 (by positivity)
    exact hr2.trans (add_le_add h1 h2)
  have hcb' : cbNorm m r₁ ≤ (|γp| * Sg + |γp| ^ (M' + 1) * (Cs * |γp|)) * Q := by
    have hp1 : γ * (Sg * Q) ≤ |γp| * (Sg * Q) := mul_le_mul_of_nonneg_right hγ0 (mul_nonneg hSg0 hQ0)
    have hp2 : γ ^ (M' + 1) * (Cs * (γ * Q)) ≤ |γp| ^ (M' + 1) * (Cs * (|γp| * Q)) := by
      refine mul_le_mul (pow_le_pow_left₀ hγ.le hγ0 _) ?_ (mul_nonneg hCs0 (mul_nonneg hγ.le hQ0))
        (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hγ0 hQ0) hCs0
    nlinarith [hp1, hp2]
  set r : Euc d → ℝ := fun x => γ * (φ x - p0) + r₁ x with hr
  have hmJ' : (m : ℕ∞ω) ≤ (J : ℕ∞ω) := by exact_mod_cast hmJ
  have hφm : ContDiff ℝ m φ := hφ.1.of_le hmJ'
  refine ⟨r₀, r, hr0, hreq, (contDiff_const.mul (hφm.sub contDiff_const)).add hr1.1, ?_, ?_⟩
  · intro i h1 h2 x
    have hid : ContDiffAt ℝ i (fun x => γ * (φ x - p0)) x :=
      (contDiff_const.mul ((hφ.1.of_le (by exact_mod_cast (h2.trans hmJ))).sub contDiff_const)).contDiffAt
    have hid2 : ContDiffAt ℝ i r₁ x := (hr1.1.of_le (by exact_mod_cast h2)).contDiffAt
    have e : iteratedFDeriv ℝ i r x = iteratedFDeriv ℝ i (fun x => γ * (φ x - p0)) x +
        iteratedFDeriv ℝ i r₁ x := iteratedFDeriv_add_apply hid hid2
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have e2 : iteratedFDeriv ℝ i (fun x => γ * (φ x - p0)) x =
        γ • iteratedFDeriv ℝ i (fun x => φ x - p0) x := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := γ) (f := fun x => φ x - p0) (i := i) (x := x)
        ((hφ.1.of_le (by exact_mod_cast (h2.trans hmJ))).sub contDiff_const).contDiffAt
      simpa [smul_eq_mul] using this
    have h3 : ‖iteratedFDeriv ℝ i (fun x => γ * (φ x - p0)) x‖ ≤ γ * s48_Dn J φ := by
      rw [e2, norm_smul, Real.norm_eq_abs, hγa, s48_psi_deriv hφ.1 p0 h1 (h2.trans hmJ)]
      exact mul_le_mul_of_nonneg_left (s48_Dn_ge hφ h1 (h2.trans hmJ) x) hγ.le
    have h4 : ‖iteratedFDeriv ℝ i r₁ x‖ ≤ cbNorm m r₁ := HRS.MS.PoisFinal.rf_cb_le hr1 h2 x
    have h5 : s48_Dn J φ ≤ Q := s48_Dn_le_Q μ J φ
    have h6 : γ * s48_Dn J φ ≤ |γp| * Q := by
      calc γ * s48_Dn J φ ≤ |γp| * s48_Dn J φ := mul_le_mul_of_nonneg_right hγ0 (s48_Dn_nonneg J φ)
        _ ≤ |γp| * Q := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
    nlinarith [h3, h4, hcb', h6]
  · -- a.e. identity
    have hfin := tc5_finite_id hs0 hsd M₀ c S hc N hρ γ hφ2 hr0 hreq (M' + 1)
    have hall : ∀ᵐ x ∂μ, ∀ j : ℕ, 1 ≤ j → j < M' + 1 → Rj j x =
        (HRS.Whole.Kop (rieszKernel d s) μ)^[j] (HRS.Whole.projMean μ φ) x :=
      ae_all_iff.2 fun j => by
        by_cases hj : 1 ≤ j ∧ j < M' + 1
        · filter_upwards [(hRj j hj.1 hj.2).2.2] with x hx _ _ using hx
        · exact Filter.Eventually.of_forall fun x h1 h2 => absurd ⟨h1, h2⟩ hj
    filter_upwards [hfin, hall, hRae] with x h1 h2 h3
    rw [h1]
    simp only [hr, hr₁]
    rw [h3, Finset.sum_range_succ']
    have e0 : (HRS.Whole.Kop (rieszKernel d s) μ)^[0] (HRS.Whole.projMean μ φ) x = φ x - p0 := rfl
    rw [pow_zero, e0]
    have e1 : ∑ j ∈ Finset.range M', (-γ) ^ (j + 1) * Rj (j + 1) x =
        ∑ j ∈ Finset.range M', (-γ) ^ (j + 1) *
          (HRS.Whole.Kop (rieszKernel d s) μ)^[j + 1] (HRS.Whole.projMean μ φ) x :=
      Finset.sum_congr rfl fun j hj => by rw [h2 (j + 1) (by omega) (by have := Finset.mem_range.1 hj; omega)]
    rw [e1]
    ring

end Resolvent2

end HRS.MS.S48
