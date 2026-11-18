import HRS.MS.ThCorrSmAux1

/-!
# TC-5, part 2: `K` on `L²_0(μ)`, the Sobolev step (S4.4 step 7), smoothing and finite resolvent identity (step 8)

Namespace `HRS.MS.Tc5`.  Constants are quantified before `ρ`; `TcRef d ρ M₀ c S N` with `c > 0`.

Main declarations (all for `0 ≤ s < d`, `TcRef d ρ M₀ c S N`, `c > 0`, `μ = ρ dx`, `K = Kop (rieszKernel d s) μ`):
* `tc5_kop_l2`: `K` maps `L²_0(μ)` boundedly into itself.
* `tc5_step` (step 7): `‖ρ K f‖²_{H^{t+α}} ≤ C² (‖ρ f‖²_{H^t} + ‖f‖²_{L²(μ)})`, `α = d - s`, `N > t + α + d`.
* `tc5_smoothing` (step 8): `m + d/2 < M α`, `Mα + d < N`: `K^M f` has a `C_b^m` representative, norm `≤ C ‖f‖_{L²(μ)}`.
* `tc5_finite_id` (step 8): `r₀ + γ K r₀ = γ P_μ φ` a.e. gives `r₀ = γ ∑_{j<M} (-γ)^j K^j P_μ φ + (-γ)^M K^M r₀` a.e.
  (`K` is linear on `L²_0(μ)` only a.e.: `tc5_kop_sub_ae`).
* `tc5_resolvent_rep` (`φ ∈ C_b^J`) and `tc5_resolvent_rep_sob` (`φ ∈ H^J`, `m + d/2 < J`): the response `r₀` (from
  `tc_response`) has a representative `r ∈ C_b^m` with `‖r‖ ≤ C ‖φ‖`, `C` independent of `ρ` and `γ ∈ (0, γp]`;
  `tc5_M_spec`: `M = ⌈(m + d/2)/(d-s)⌉ + 1` works.  `tc5_assemble` is the abstract form.
Adjustments w.r.t. the plan sketch: statements are for a fixed internal cutoff `θ`; `N` (derivative order of `TcRef`)
must exceed the Sobolev orders involved (hypotheses `hN`); the data `φ` of the `H^J` version is `MemSobolev J φ`
(`MemHSmooth` is converted by `tcs_sobolev_of_hsmooth`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.Tc5

open HRS.Whole HRS.MS.TcDefs HRS.MS.TcF
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

local notation "MemSob" => HRS.PDE.ToolboxRd.MemSobolev
local notation "SobSq" => HRS.PDE.ToolboxRd.sobolevNormSq

variable {d : ℕ}

/-- `K_μ` maps `L²_0(μ)` to itself, boundedly (constants before `ρ`). -/
theorem tc5_kop_l2 {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ f : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f) ∧
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f) ≤
            C * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
  obtain ⟨θ, hθ⟩ := tc5_cutoff (d := d)
  obtain ⟨Cl, hCl, hgain⟩ :=
    HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ.smooth hθ.hasCompactSupport hs0 hsd
  obtain ⟨Cf, hCf0, hCf⟩ := tc4_far hθ hs0 0 M₀ c hc
  set K : ℝ := 9 * (M₀ ^ 2 * Cl ^ 2 + Cf ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun ρ hρ f hf => ?_⟩
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hu0, hu0n⟩ := tc5_rho_f_sob0 hρ hc hf.1
  obtain ⟨hLm, hLn⟩ := hgain 0 _ hu0
  set L := locK d s θ ρ f with hL
  set F := farK d s θ μ f with hF
  have hLL2 : MemLp L 2 volume := hLm.1
  have hIL : ∫ x, L x ^ 2 ≤ Cl ^ 2 * (M₀ * ∫ y, f y ^ 2 ∂μ) :=
    (tc5_sob_l2 (by linarith [show (0:ℝ) ≤ (d:ℝ) - s by linarith]) hLm).trans
      (hLn.trans (mul_le_mul_of_nonneg_left hu0n (sq_nonneg _)))
  obtain ⟨hFcb, hFn⟩ := hCf ρ S (tc5_ref_mono hρ (Nat.zero_le _)) f hf
  have hFc : Continuous F := hFcb.1.continuous
  set BF := HRS.cbNorm 0 F with hBF
  have hFb : ∀ x, |F x| ≤ BF := fun x => by
    simpa [Real.norm_eq_abs] using tc5_cb_sup_le hFcb x
  have hBF2 : BF ^ 2 ≤ Cf ^ 2 * ∫ y, f y ^ 2 ∂μ := by
    have h0 : 0 ≤ BF := tc5_cb_nonneg _ _
    have hq : 0 ≤ ∫ y, f y ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    calc BF ^ 2 ≤ (Cf * HRS.Whole.l2Norm μ f) ^ 2 := pow_le_pow_left₀ h0 hFn 2
      _ = Cf ^ 2 * ∫ y, f y ^ 2 ∂μ := by
          rw [mul_pow]; unfold HRS.Whole.l2Norm; rw [Real.sq_sqrt hq]
  have hc0 := tc5_pair_bound hρ hc hLL2 hFc hFb
  set c0 := HRS.Whole.pair μ (fun x => L x + F x) with hc0def
  obtain ⟨hLμ, hLμn⟩ := tc5_L_mu hρ hc hLL2
  have hFμ : MemLp F 2 μ := MemLp.of_bound hFc.aestronglyMeasurable BF
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x)
  have hmemh : MemLp (fun x => L x + F x - c0) 2 μ := (hLμ.add hFμ).sub (memLp_const c0)
  have hae := tc4_split_mu hρ hc hθ hs0 hsd hf.1
  have hae' : HRS.Whole.Kop (rieszKernel d s) μ f =ᵐ[μ] fun x => L x + F x - c0 := hae
  have hq0 : 0 ≤ ∫ y, f y ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  refine ⟨⟨hmemh.ae_eq hae'.symm, ?_⟩, ?_⟩
  · rw [integral_congr_ae hae']
    have h1 : Integrable (fun x => L x + F x) μ :=
      (hLμ.integrable (by norm_num)).add (hFμ.integrable (by norm_num))
    rw [integral_sub h1 (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_eq_zero.2 rfl
  · unfold HRS.Whole.l2Norm
    rw [integral_congr_ae (hae'.mono fun x hx => by rw [hx])]
    have hFi : ∫ x, F x ^ 2 ∂μ ≤ BF ^ 2 := by
      calc ∫ x, F x ^ 2 ∂μ ≤ ∫ x, BF ^ 2 ∂μ :=
            integral_mono (hFμ.integrable_sq) (integrable_const _) fun x => by
              have := hFb x
              rw [← sq_abs (F x)]
              exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = BF ^ 2 := by simp
    have hpt : ∀ x, (L x + F x - c0) ^ 2 ≤ 3 * L x ^ 2 + 3 * F x ^ 2 + 3 * c0 ^ 2 := fun x => by
      nlinarith [sq_nonneg (L x - F x), sq_nonneg (L x + F x - 2 * c0), sq_nonneg (L x - c0),
        sq_nonneg (F x + c0), sq_nonneg (F x - c0), sq_nonneg (L x + c0)]
    have hint1 : Integrable (fun x => (L x + F x - c0) ^ 2) μ := hmemh.integrable_sq
    have hint2 : Integrable (fun x => 3 * L x ^ 2 + 3 * F x ^ 2 + 3 * c0 ^ 2) μ :=
      ((hLμ.integrable_sq.const_mul 3).add (hFμ.integrable_sq.const_mul 3)).add (integrable_const _)
    have hmain : ∫ x, (L x + F x - c0) ^ 2 ∂μ ≤ K * ∫ y, f y ^ 2 ∂μ := by
      calc ∫ x, (L x + F x - c0) ^ 2 ∂μ
          ≤ ∫ x, (3 * L x ^ 2 + 3 * F x ^ 2 + 3 * c0 ^ 2) ∂μ := integral_mono hint1 hint2 hpt
        _ = 3 * ∫ x, L x ^ 2 ∂μ + 3 * ∫ x, F x ^ 2 ∂μ + 3 * c0 ^ 2 := by
            have iL : Integrable (fun x => 3 * L x ^ 2) μ := hLμ.integrable_sq.const_mul 3
            have iF : Integrable (fun x => 3 * F x ^ 2) μ := hFμ.integrable_sq.const_mul 3
            have iLF : Integrable (fun x => 3 * L x ^ 2 + 3 * F x ^ 2) μ := iL.add iF
            rw [integral_add iLF (integrable_const _), integral_add iL iF, integral_const_mul,
              integral_const_mul]
            simp
        _ ≤ K * ∫ y, f y ^ 2 ∂μ := by
            have hc0' : c0 ^ 2 ≤ 2 * M₀ * (∫ x, L x ^ 2) + 2 * BF ^ 2 := hc0
            have hM0 := tc5_M0_nonneg hρ
            have h1 : M₀ * ∫ x, L x ^ 2 ≤ M₀ * (Cl ^ 2 * (M₀ * ∫ y, f y ^ 2 ∂μ)) :=
              mul_le_mul_of_nonneg_left hIL hM0
            have h2 : ∫ x, L x ^ 2 ∂μ ≤ M₀ * (Cl ^ 2 * (M₀ * ∫ y, f y ^ 2 ∂μ)) := hLμn.trans h1
            rw [hK]
            nlinarith [h1, h2, hFi, hBF2, hc0']
    calc Real.sqrt (∫ x, (L x + F x - c0) ^ 2 ∂μ)
        ≤ Real.sqrt (K * ∫ y, f y ^ 2 ∂μ) := Real.sqrt_le_sqrt hmain
      _ = Real.sqrt K * Real.sqrt (∫ y, f y ^ 2 ∂μ) := Real.sqrt_mul hK0 _

set_option maxHeartbeats 1600000 in
/-- **Step 7 (Sobolev step).**  `ρ K f ∈ H^{t+α}`, `α = d - s`, with
`‖ρ K f‖²_{H^{t+α}} ≤ C² (‖ρ f‖²_{H^t} + ‖f‖²_{L²(μ)})`; constants before `ρ`, `N > t + α + d`. -/
theorem tc5_step {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (t : ℝ) (ht : 0 ≤ t) (M₀ c S : ℝ) (hc : 0 < c)
    (N : ℕ) (hN : t + ((d : ℝ) - s) + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ f : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f → MemSob t (fun y => ρ y * f y) →
        MemSob (t + ((d : ℝ) - s)) (fun x => ρ x * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f x) ∧
          SobSq (t + ((d : ℝ) - s)) (fun x => ρ x * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f x) ≤
            C ^ 2 * (SobSq t (fun y => ρ y * f y) + HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ^ 2) := by
  obtain ⟨θ, hθ⟩ := tc5_cutoff (d := d)
  have hα : 0 < (d : ℝ) - s := by linarith
  have hd1 : (1 : ℝ) ≤ d := by
    have : 0 < d := by exact_mod_cast (lt_of_le_of_lt hs0 hsd)
    exact_mod_cast this
  set τ : ℝ := t + ((d : ℝ) - s) with hτdef
  have hτ0 : 0 ≤ τ := by linarith
  set J : ℕ := ⌈τ⌉₊ with hJdef
  have hτJ : τ ≤ J := Nat.le_ceil τ
  have hJN : J ≤ N := by
    have h1 : (J : ℝ) < τ + 1 := Nat.ceil_lt_add_one hτ0
    have : (J : ℝ) < N := by linarith
    exact_mod_cast this.le
  obtain ⟨Cl, hCl, hgain⟩ :=
    HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ.smooth hθ.hasCompactSupport hs0 hsd
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MS.TcS.tcs_mul_schwartz d N τ hτ0 (by linarith)
  obtain ⟨Cf, hCf0, hCf⟩ := tc4_far hθ hs0 J M₀ c hc
  obtain ⟨Ccb, hCcb, hcb⟩ := HRS.MS.TcS.tcs_cb_mul (d := d) J
  obtain ⟨B, hB0, hB⟩ := tc5_rho_sob (d := d) J hc
  set W : ℝ := tc5_W d c N with hW
  have hW0 : 0 ≤ W := tc5_W_nonneg d c N
  have hS0 : ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → 0 ≤ S := fun ρ hρ => tc5_S_nonneg hρ
  set A : ℝ := 4 * (Cm * W * |S|) ^ 2 * Cl ^ 2 + 4 * B * S ^ 2 * M₀ * Cl ^ 2 with hA
  set B' : ℝ := 4 * (Ccb * Cf) ^ 2 * B * S ^ 2 + 4 * B * S ^ 2 * Cf ^ 2 with hB'
  have hM0 : ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → 0 ≤ M₀ := fun ρ hρ => tc5_M0_nonneg hρ
  by_cases hex : ∃ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N
  swap
  · refine ⟨0, le_rfl, fun ρ hρ => (hex ⟨ρ, hρ⟩).elim⟩
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hM00 : 0 ≤ M₀ := tc5_M0_nonneg hρ₀
  have hA0 : 0 ≤ A := by positivity
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨Real.sqrt (A + B'), Real.sqrt_nonneg _, fun ρ hρ f hf hu => ?_⟩
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hSn := tc5_S_nonneg hρ
  rw [abs_of_nonneg hSn] at hA
  obtain ⟨hLm, hLn⟩ := hgain t _ hu
  set L := locK d s θ ρ f with hL
  set F := farK d s θ μ f with hF
  have hLL2 : MemLp L 2 volume := hLm.1
  obtain ⟨hFcb, hFn⟩ := hCf ρ S (tc5_ref_mono hρ (Nat.zero_le _)) f hf
  have hFc : Continuous F := hFcb.1.continuous
  set BF := HRS.cbNorm J F with hBF
  have hBF0 : 0 ≤ BF := tc5_cb_nonneg _ _
  have hFb : ∀ x, |F x| ≤ BF := fun x => by
    simpa [Real.norm_eq_abs] using tc5_cb_sup_le hFcb x
  have hl0 : 0 ≤ HRS.Whole.l2Norm μ f := Real.sqrt_nonneg _
  have hBFn : BF ≤ Cf * HRS.Whole.l2Norm μ f := hFn
  have hc0 := tc5_pair_bound hρ hc hLL2 hFc hFb
  set c0 := HRS.Whole.pair μ (fun x => L x + F x) with hc0def
  set nt := SobSq t (fun y => ρ y * f y) with hnt
  have hnt0 : 0 ≤ nt := tc5_sob_nonneg _ _
  have hIL : ∫ x, L x ^ 2 ≤ Cl ^ 2 * nt :=
    (tc5_sob_l2 hτ0 hLm).trans hLn
  have hc0b : c0 ^ 2 ≤ 2 * M₀ * (Cl ^ 2 * nt) + 2 * (Cf * HRS.Whole.l2Norm μ f) ^ 2 := by
    refine hc0.trans ?_
    have h1 : 2 * M₀ * ∫ x, L x ^ 2 ≤ 2 * M₀ * (Cl ^ 2 * nt) :=
      mul_le_mul_of_nonneg_left hIL (by positivity)
    have h2 : BF ^ 2 ≤ (Cf * HRS.Whole.l2Norm μ f) ^ 2 := pow_le_pow_left₀ hBF0 hBFn 2
    linarith
  -- the three terms
  obtain ⟨hT1m, hT1n⟩ := hCm ρ hρ.smooth (fun j hj => (tc5_rho_W hρ hc).1 j hj) L hLm
  have hsum := (tc5_rho_W hρ hc).2
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _
  have hN1 : SobSq τ (fun x => ρ x * L x) ≤ (Cm * W * S) ^ 2 * (Cl ^ 2 * nt) := by
    refine hT1n.trans ?_
    have h1 : (Cm * ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖) ^ 2 ≤ (Cm * W * S) ^ 2 := by
      refine pow_le_pow_left₀ (mul_nonneg hCm0 hsum0) ?_ 2
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hsum hCm0
    exact mul_le_mul h1 hLn (tc5_sob_nonneg _ _) (sq_nonneg _)
  have hρJ := (hB ρ M₀ S (tc5_ref_mono hρ hJN))
  obtain ⟨hT2m, hT2n⟩ := hcb F hFcb ρ hρJ.1
  have e2 : (fun x => ρ x * F x) = fun x => F x * ρ x := by funext x; ring
  obtain ⟨hT2m', hT2n'⟩ := tc5_sob_mono hτJ (e2 ▸ hT2m : MemSob (J : ℝ) (fun x => ρ x * F x))
  have hN2 : SobSq τ (fun x => ρ x * F x) ≤ (Ccb * Cf * HRS.Whole.l2Norm μ f) ^ 2 * (B * S ^ 2) := by
    refine hT2n'.trans ?_
    rw [e2]
    refine hT2n.trans ?_
    have h1 : (Ccb * BF) ^ 2 ≤ (Ccb * Cf * HRS.Whole.l2Norm μ f) ^ 2 := by
      rw [mul_assoc]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hBFn hCcb.le) 2
    exact mul_le_mul h1 hρJ.2 (tc5_sob_nonneg _ _) (sq_nonneg _)
  obtain ⟨hρτ, hρτn⟩ := tc5_sob_mono hτJ hρJ.1
  obtain ⟨hT3m, hT3n⟩ := tc5_sob_smul (-c0) hρτ
  have hN3 : SobSq τ (fun x => (-c0) * ρ x) ≤
      (2 * M₀ * (Cl ^ 2 * nt) + 2 * (Cf * HRS.Whole.l2Norm μ f) ^ 2) * (B * S ^ 2) := by
    rw [hT3n, neg_sq]
    exact mul_le_mul hc0b (hρτn.trans hρJ.2) (tc5_sob_nonneg _ _) (by positivity)
  obtain ⟨h12m, h12n⟩ := tc5_sob_add hT1m hT2m'
  obtain ⟨h123m, h123n⟩ := tc5_sob_add h12m hT3m
  -- a.e. identification
  have hae := tc4_split hρ hc hθ hs0 hsd hf.1
  have hid : (fun x => (ρ x * L x + ρ x * F x) + (-c0) * ρ x) =ᵐ[volume]
      fun x => ρ x * HRS.Whole.Kop (rieszKernel d s) μ f x := by
    filter_upwards [hae] with x hx
    rw [hx]; ring
  obtain ⟨hfm, hfn⟩ := tc5_sob_congr hid h123m
  refine ⟨hfm, ?_⟩
  rw [hfn]
  have hl2 : HRS.Whole.l2Norm μ f ^ 2 = ∫ y, f y ^ 2 ∂μ := by
    unfold HRS.Whole.l2Norm; exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hsq : Real.sqrt (A + B') ^ 2 = A + B' := Real.sq_sqrt (by positivity)
  rw [hsq]
  have hl20 : 0 ≤ HRS.Whole.l2Norm μ f ^ 2 := sq_nonneg _
  calc SobSq τ (fun x => (ρ x * L x + ρ x * F x) + (-c0) * ρ x)
      ≤ 2 * SobSq τ (fun x => ρ x * L x + ρ x * F x) + 2 * SobSq τ (fun x => (-c0) * ρ x) := h123n
    _ ≤ 2 * (2 * SobSq τ (fun x => ρ x * L x) + 2 * SobSq τ (fun x => ρ x * F x)) +
          2 * SobSq τ (fun x => (-c0) * ρ x) := by linarith
    _ ≤ A * nt + B' * HRS.Whole.l2Norm μ f ^ 2 := by
        rw [hA, hB']
        nlinarith [hN1, hN2, hN3]
    _ ≤ (A + B') * (nt + HRS.Whole.l2Norm μ f ^ 2) := by nlinarith [mul_nonneg hA0 hl20, mul_nonneg hB'0 hnt0]

/-- One application of `K` lands in `C_b^m` (representative) when the output Sobolev order `t + α > m + d/2`. -/
theorem tc5_rep_step {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hq : (m : ℝ) + d / 2 < t + ((d : ℝ) - s)) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ h : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) h → MemSob t (fun y => ρ y * h y) →
        ∃ R : Euc d → ℝ, HRS.MemCb m R ∧
          HRS.cbNorm m R ≤ C * (Real.sqrt (SobSq t (fun y => ρ y * h y)) +
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h) ∧
          R =ᵐ[HRS.Whole.withDensityReal ρ] HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) h := by
  obtain ⟨θ, hθ⟩ := tc5_cutoff (d := d)
  have hα : 0 < (d : ℝ) - s := by linarith
  obtain ⟨Cl, hCl, hgain⟩ :=
    HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ.smooth hθ.hasCompactSupport hs0 hsd
  obtain ⟨Cr, hCr0, hCr⟩ := HRS.MS.TcS.tcs_rep (d := d) m hq
  obtain ⟨Cf, hCf0, hCf⟩ := tc4_far hθ hs0 m M₀ c hc
  refine ⟨(Cr * Cl + Real.sqrt (2 * M₀) * Cl) + Cf * (1 + Real.sqrt 2), by positivity,
    fun ρ hρ h hh hu => ?_⟩
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hLm, hLn⟩ := hgain t _ hu
  set L := locK d s θ ρ h with hL
  set F := farK d s θ μ h with hF
  set nt := SobSq t (fun y => ρ y * h y) with hnt
  have hnt0 : 0 ≤ nt := tc5_sob_nonneg _ _
  obtain ⟨R₁, hR1cb, hR1ae, hR1n⟩ := hCr L hLm
  obtain ⟨hFcb, hFn⟩ := hCf ρ S (tc5_ref_mono hρ (Nat.zero_le _)) h hh
  have hFc : Continuous F := hFcb.1.continuous
  set BF := HRS.cbNorm m F with hBF
  have hBF0 : 0 ≤ BF := tc5_cb_nonneg _ _
  have hFb : ∀ x, |F x| ≤ BF := fun x => by
    simpa [Real.norm_eq_abs] using tc5_cb_sup_le hFcb x
  have hc0 := tc5_pair_bound hρ hc hLm.1 hFc hFb
  set c0 := HRS.Whole.pair μ (fun x => L x + F x) with hc0def
  have hM0 := tc5_M0_nonneg hρ
  have hIL : ∫ x, L x ^ 2 ≤ Cl ^ 2 * nt :=
    (tc5_sob_l2 (by linarith) hLm).trans hLn
  set a : ℝ := Real.sqrt (2 * M₀) * Cl * Real.sqrt nt with ha
  set b : ℝ := Real.sqrt 2 * BF with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hc0abs : |c0| ≤ a + b := by
    have h1 : c0 ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have e1 : a ^ 2 = 2 * M₀ * (Cl ^ 2 * nt) := by
        rw [ha, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnt0]; ring
      have e2 : b ^ 2 = 2 * BF ^ 2 := by
        rw [hb, mul_pow, Real.sq_sqrt (by norm_num)]
      rw [e1, e2]
      have hc0' : c0 ^ 2 ≤ 2 * M₀ * (∫ x, L x ^ 2) + 2 * BF ^ 2 := hc0
      have : 2 * M₀ * ∫ x, L x ^ 2 ≤ 2 * M₀ * (Cl ^ 2 * nt) :=
        mul_le_mul_of_nonneg_left hIL (by positivity)
      linarith
    have h2 : c0 ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha0 hb0]
    calc |c0| = Real.sqrt (c0 ^ 2) := (Real.sqrt_sq_eq_abs c0).symm
      _ ≤ Real.sqrt ((a + b) ^ 2) := Real.sqrt_le_sqrt h2
      _ = a + b := Real.sqrt_sq (by positivity)
  obtain ⟨hAcb, hAn⟩ := tc5_cb_add hR1cb hFcb
  obtain ⟨hKcb, hKn⟩ := tc5_cb_add hAcb (tc5_cb_const (d := d) m (-c0)).1
  refine ⟨fun x => (R₁ x + F x) + (-c0), hKcb, ?_, ?_⟩
  · have hc1 := (tc5_cb_const (d := d) m (-c0)).2
    rw [abs_neg] at hc1
    have hsq : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (t + ((d : ℝ) - s)) L) ≤ Cl * Real.sqrt nt := by
      calc _ ≤ Real.sqrt (Cl ^ 2 * nt) := Real.sqrt_le_sqrt hLn
        _ = Cl * Real.sqrt nt := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCl.le]
    have hl0 : 0 ≤ HRS.Whole.l2Norm μ h := Real.sqrt_nonneg _
    have hR1 : HRS.cbNorm m R₁ ≤ Cr * (Cl * Real.sqrt nt) :=
      hR1n.trans (mul_le_mul_of_nonneg_left hsq hCr0)
    have hbb : b ≤ Real.sqrt 2 * (Cf * HRS.Whole.l2Norm μ h) :=
      mul_le_mul_of_nonneg_left hFn (Real.sqrt_nonneg _)
    have hs2 : Real.sqrt 2 * (Cf * HRS.Whole.l2Norm μ h) =
        (Cf * Real.sqrt 2) * HRS.Whole.l2Norm μ h := by ring
    have hsn : 0 ≤ Real.sqrt nt := Real.sqrt_nonneg _
    have hCl' : 0 ≤ Cl * Real.sqrt nt := by positivity
    have : HRS.cbNorm m (fun x => (R₁ x + F x) + (-c0)) ≤
        Cr * (Cl * Real.sqrt nt) + Cf * HRS.Whole.l2Norm μ h +
          (Real.sqrt (2 * M₀) * (Cl * Real.sqrt nt) + (Cf * Real.sqrt 2) * HRS.Whole.l2Norm μ h) := by
      have e : a = Real.sqrt (2 * M₀) * (Cl * Real.sqrt nt) := by rw [ha]; ring
      linarith
    refine this.trans ?_
    have h1 : 0 ≤ Cr * Cl := by positivity
    nlinarith [mul_nonneg hsn hl0, mul_nonneg (mul_nonneg hCf0 (Real.sqrt_nonneg 2)) hsn,
      mul_nonneg hCf0 hsn, mul_nonneg h1 hl0, mul_nonneg (mul_nonneg (Real.sqrt_nonneg (2 * M₀)) hCl.le) hl0,
      mul_nonneg hCf0 hl0, mul_nonneg (mul_nonneg hCf0 (Real.sqrt_nonneg 2)) hl0]
  · have hae := tc4_split_mu hρ hc hθ hs0 hsd hh.1
    have hvol : R₁ =ᵐ[volume] L := hR1ae
    have hacv : μ ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
    filter_upwards [hacv.ae_le hvol, hae] with x h1 h2
    rw [h2, h1]
    change L x + F x + -c0 = (L x + F x) - c0
    ring

/-- Iterated Sobolev regularity: `ρ K^n f ∈ H^{nα}`, `K^n f ∈ L²_0`, all with constants `C_n ‖f‖`. -/
theorem tc5_iter {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) :
    ∀ n : ℕ, ((n : ℝ) * ((d : ℝ) - s) + d < N) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ f : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
          ((HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f) ∧
        HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ)
          ((HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f) ≤
            C * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ∧
        MemSob ((n : ℝ) * ((d : ℝ) - s))
          (fun y => ρ y * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f y) ∧
        SobSq ((n : ℝ) * ((d : ℝ) - s))
          (fun y => ρ y * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f y) ≤
            C ^ 2 * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ^ 2 := by
  have hα : 0 < (d : ℝ) - s := by linarith
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨1 + Real.sqrt M₀, by positivity, fun ρ hρ f hf => ?_⟩
    have hprob := tc4_isProb hρ.prob
    obtain ⟨h0, h0n⟩ := tc5_rho_f_sob0 hρ hc hf.1
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul]
    refine ⟨hf, ?_, h0, ?_⟩
    · have : 0 ≤ HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := Real.sqrt_nonneg _
      nlinarith [Real.sqrt_nonneg M₀]
    · have hl2 : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ^ 2 =
          ∫ y, f y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
        unfold HRS.Whole.l2Norm; exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
      rw [hl2]
      have hM0 := tc5_M0_nonneg hρ
      have hq : 0 ≤ ∫ y, f y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun _ => sq_nonneg _
      refine h0n.trans ?_
      have : M₀ ≤ (1 + Real.sqrt M₀) ^ 2 := by
        nlinarith [Real.sq_sqrt hM0, Real.sqrt_nonneg M₀]
      exact mul_le_mul_of_nonneg_right this hq
  | succ n ih =>
    intro hN
    have hn : (n : ℝ) * ((d : ℝ) - s) + d < N := by
      have : ((n + 1 : ℕ) : ℝ) * ((d : ℝ) - s) = n * ((d : ℝ) - s) + ((d : ℝ) - s) := by push_cast; ring
      rw [this] at hN; linarith
    obtain ⟨Cn, hCn0, hCn⟩ := ih hn
    obtain ⟨Ck, hCk0, hCk⟩ := tc5_kop_l2 (d := d) hs0 hsd M₀ c S hc N
    obtain ⟨Cs, hCs0, hCs⟩ := tc5_step (d := d) hs0 hsd ((n : ℝ) * ((d : ℝ) - s))
      (by positivity) M₀ c S hc N (by
        have : ((n + 1 : ℕ) : ℝ) * ((d : ℝ) - s) = n * ((d : ℝ) - s) + ((d : ℝ) - s) := by push_cast; ring
        rw [this] at hN; linarith)
    refine ⟨Ck * Cn + Real.sqrt 2 * Cs * Cn, by positivity, fun ρ hρ f hf => ?_⟩
    obtain ⟨hm, hl, hsm, hsn⟩ := hCn ρ hρ f hf
    set h := (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f with hh
    have hit : (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n + 1] f =
        HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) h := by
      rw [Function.iterate_succ_apply']
    rw [hit]
    obtain ⟨hKm, hKl⟩ := hCk ρ hρ h hm
    obtain ⟨hSm, hSn⟩ := hCs ρ hρ h hm hsm
    have e : ((n + 1 : ℕ) : ℝ) * ((d : ℝ) - s) = n * ((d : ℝ) - s) + ((d : ℝ) - s) := by push_cast; ring
    rw [e]
    have hl0 : 0 ≤ HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := Real.sqrt_nonneg _
    refine ⟨hKm, ?_, hSm, ?_⟩
    · calc _ ≤ Ck * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h := hKl
        _ ≤ Ck * (Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) :=
            mul_le_mul_of_nonneg_left hl hCk0
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hCs0) (mul_nonneg hCn0 hl0)]
    · have hl2 : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h ^ 2 ≤
          (Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hl 2
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc _ ≤ Cs ^ 2 * (SobSq ((n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y) +
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h ^ 2) := hSn
        _ ≤ Cs ^ 2 * (Cn ^ 2 * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ^ 2 +
            (Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) ^ 2) := by
            gcongr
        _ = (Real.sqrt 2 * Cs * Cn) ^ 2 * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ^ 2 := by
            simp only [mul_pow, hsq]; ring
        _ ≤ _ := by
            have h1 : 0 ≤ Ck * Cn := by positivity
            have h2 : 0 ≤ Real.sqrt 2 * Cs * Cn := by positivity
            have h3 : (Real.sqrt 2 * Cs * Cn) ^ 2 ≤ (Ck * Cn + Real.sqrt 2 * Cs * Cn) ^ 2 :=
              pow_le_pow_left₀ h2 (by linarith) 2
            exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

/-- **Step 8 (smoothing).**  `m + d/2 < M α`: `K^M f` has a `C_b^m` representative with norm `≤ C ‖f‖_{L²(μ)}`. -/
theorem tc5_smoothing {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m M : ℕ)
    (hM : (m : ℝ) + d / 2 < M * ((d : ℝ) - s)) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    (hN : (M : ℝ) * ((d : ℝ) - s) + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ f : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ R : Euc d → ℝ, HRS.MemCb m R ∧
          HRS.cbNorm m R ≤ C * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f ∧
          R =ᵐ[HRS.Whole.withDensityReal ρ]
            (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[M] f := by
  have hα : 0 < (d : ℝ) - s := by linarith
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := by
    rcases M with _ | n
    · exfalso
      have : (0 : ℝ) ≤ (m : ℝ) + d / 2 := by positivity
      simp at hM; linarith
    · exact ⟨n, rfl⟩
  have e : ((n + 1 : ℕ) : ℝ) * ((d : ℝ) - s) = n * ((d : ℝ) - s) + ((d : ℝ) - s) := by push_cast; ring
  rw [e] at hM hN
  have hn : (n : ℝ) * ((d : ℝ) - s) + d < N := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := tc5_iter (d := d) hs0 hsd M₀ c S hc N n hn
  obtain ⟨Cr, hCr0, hCr⟩ := tc5_rep_step (d := d) hs0 hsd m ((n : ℝ) * ((d : ℝ) - s))
    (by positivity) hM M₀ c S hc N
  refine ⟨Cr * (Cn + Cn), by positivity, fun ρ hρ f hf => ?_⟩
  obtain ⟨hm, hl, hsm, hsn⟩ := hCn ρ hρ f hf
  set h := (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f with hh
  obtain ⟨R, hRcb, hRn, hRae⟩ := hCr ρ hρ h hm hsm
  refine ⟨R, hRcb, ?_, ?_⟩
  · have hs1 : Real.sqrt (SobSq ((n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) ≤
        Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
      calc _ ≤ Real.sqrt ((Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) ^ 2) := by
            refine Real.sqrt_le_sqrt (hsn.trans (le_of_eq ?_))
            ring
        _ = _ := Real.sqrt_sq (mul_nonneg hCn0 (Real.sqrt_nonneg _))
    calc HRS.cbNorm m R ≤ Cr * (Real.sqrt (SobSq ((n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h) := hRn
      _ ≤ Cr * (Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f +
          Cn * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) := by
          gcongr
      _ = _ := by ring
  · rw [Function.iterate_succ_apply']
    exact hRae

/-! ### Linearity of `K` on `L²_0(μ)` and the finite resolvent identity -/

theorem tc5_kop_smul (g : Euc d → ℝ) (ν : Measure (Euc d)) (a : ℝ) (u : Euc d → ℝ) :
    HRS.Whole.Kop g ν (fun x => a * u x) = fun x => a * HRS.Whole.Kop g ν u x := by
  funext x
  unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
  have e1 : ∀ z, ∫ y, g (z - y) * (a * u y) ∂ν = a * ∫ y, g (z - y) * u y ∂ν := fun z => by
    rw [← integral_const_mul]; congr 1; ext y; ring
  simp only [e1]
  rw [integral_const_mul]; ring

theorem tc5_iter_smul (g : Euc d → ℝ) (ν : Measure (Euc d)) (a : ℝ) (u : Euc d → ℝ) :
    ∀ n : ℕ, (HRS.Whole.Kop g ν)^[n] (fun x => a * u x) = fun x => a * (HRS.Whole.Kop g ν)^[n] u x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, tc5_kop_smul]

theorem tc5_iter_congr (g : Euc d → ℝ) (ν : Measure (Euc d)) {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') :
    ∀ n : ℕ, (HRS.Whole.Kop g ν)^[n] u =ᵐ[ν] (HRS.Whole.Kop g ν)^[n] u' := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have := HRS.MS.TcR.tc2_kop_congr_ae (g := g) ih
    rw [this]

theorem tc5_L2Zero_smul {ν : Measure (Euc d)} (a : ℝ) {u : Euc d → ℝ} (hu : HRS.Whole.MemL2Zero ν u) :
    HRS.Whole.MemL2Zero ν (fun x => a * u x) :=
  ⟨hu.1.const_mul a, by simp only [integral_const_mul, hu.2, mul_zero]⟩

theorem tc5_L2Zero_sub {ν : Measure (Euc d)} [IsFiniteMeasure ν] {u v : Euc d → ℝ}
    (hu : HRS.Whole.MemL2Zero ν u) (hv : HRS.Whole.MemL2Zero ν v) :
    HRS.Whole.MemL2Zero ν (fun x => u x - v x) :=
  ⟨hu.1.sub hv.1, by
    rw [integral_sub (hu.1.integrable (by norm_num)) (hv.1.integrable (by norm_num)), hu.2, hv.2]; simp⟩

/-- `K^[n]` preserves `L²_0(μ)`. -/
theorem tc5_iter_L2Zero {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    {ρ : Euc d → ℝ} (hρ : TcRef d ρ M₀ c S N) {f : Euc d → ℝ}
    (hf : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f) (n : ℕ) :
    HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
      ((HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f) := by
  obtain ⟨C, -, hC⟩ := tc5_kop_l2 (d := d) hs0 hsd M₀ c S hc N
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hC ρ hρ _ ih).1

/-- Additivity of `K` on `L²_0(μ)` (a.e.). -/
theorem tc5_kop_sub_ae {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    {ρ : Euc d → ℝ} (hρ : TcRef d ρ M₀ c S N) {u v : Euc d → ℝ}
    (hu : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) u)
    (hv : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) v) :
    HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) (fun x => u x - v x) =ᵐ[HRS.Whole.withDensityReal ρ]
      fun x => HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) u x -
        HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) v x := by
  obtain ⟨θ, hθ⟩ := tc5_cutoff (d := d)
  obtain ⟨C, -, hC⟩ := tc5_kop_l2 (d := d) hs0 hsd M₀ c S hc N
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set g := rieszKernel d s with hg
  -- integrability of `K̃ u`
  have hKt : ∀ w : Euc d → ℝ, HRS.Whole.MemL2Zero μ w →
      Integrable (fun x => ∫ y, g (x - y) * w y ∂μ) μ := by
    intro w hw
    have h1 := (hC ρ hρ w hw).1.1.integrable (by norm_num)
    have : (fun x => ∫ y, g (x - y) * w y ∂μ) =
        fun x => HRS.Whole.Kop g μ w x + HRS.Whole.pair μ (fun x => ∫ y, g (x - y) * w y ∂μ) := by
      funext x; unfold HRS.Whole.Kop HRS.Whole.projMean; ring
    rw [this]
    exact h1.add (integrable_const _)
  have hacv : μ ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ x ∂μ, Integrable (fun y => g (x - y) * u y) μ ∧ Integrable (fun y => g (x - y) * v y) μ :=
    hacv.ae_le (by
      filter_upwards [tc4_ae_integrable hρ hc hθ hs0 hsd hu.1, tc4_ae_integrable hρ hc hθ hs0 hsd hv.1]
        with x h1 h2 using ⟨h1, h2⟩)
  have hsubK : ∀ᵐ x ∂μ, ∫ y, g (x - y) * (u y - v y) ∂μ =
      (∫ y, g (x - y) * u y ∂μ) - ∫ y, g (x - y) * v y ∂μ := by
    filter_upwards [hae] with x hx
    rw [← integral_sub hx.1 hx.2]
    congr 1; ext y; ring
  have hpair : HRS.Whole.pair μ (fun x => ∫ y, g (x - y) * (u y - v y) ∂μ) =
      HRS.Whole.pair μ (fun x => ∫ y, g (x - y) * u y ∂μ) -
        HRS.Whole.pair μ (fun x => ∫ y, g (x - y) * v y ∂μ) := by
    unfold HRS.Whole.pair
    rw [← integral_sub (hKt u hu) (hKt v hv)]
    exact integral_congr_ae hsubK
  filter_upwards [hsubK] with x hx
  unfold HRS.Whole.Kop HRS.Whole.projMean
  simp only
  rw [hx, hpair]; ring

/-- Iterated additivity. -/
theorem tc5_iter_sub {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    {ρ : Euc d → ℝ} (hρ : TcRef d ρ M₀ c S N) {u v : Euc d → ℝ}
    (hu : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) u)
    (hv : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) v) (n : ℕ) :
    (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] (fun x => u x - v x)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun x =>
        (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] u x -
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] v x := by
  have hprob := tc4_isProb hρ.prob
  induction n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := HRS.MS.TcR.tc2_kop_congr_ae (g := rieszKernel d s) ih
    rw [h1]
    exact tc5_kop_sub_ae hs0 hsd M₀ c S hc N hρ (tc5_iter_L2Zero hs0 hsd M₀ c S hc N hρ hu n)
      (tc5_iter_L2Zero hs0 hsd M₀ c S hc N hρ hv n)

/-- **Step 8, finite resolvent identity (general form).** From `r₀ + γ K r₀ = f` a.e. (`f, r₀ ∈ L²_0(μ)`):
`r₀ = ∑_{j<M} (-γ)^j K^j f + (-γ)^M K^M r₀` a.e. -/
theorem tc5_finite_id_gen {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    {ρ : Euc d → ℝ} (hρ : TcRef d ρ M₀ c S N) (γ : ℝ) {f r₀ : Euc d → ℝ}
    (hf : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f)
    (hr : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀)
    (heq : ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x = f x) (M : ℕ) :
    r₀ =ᵐ[HRS.Whole.withDensityReal ρ] fun x =>
      ∑ j ∈ Finset.range M, (-γ) ^ j * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j] f x +
        (-γ) ^ M * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[M] r₀ x := by
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set K := HRS.Whole.Kop (rieszKernel d s) μ with hK
  obtain ⟨C, -, hC⟩ := tc5_kop_l2 (d := d) hs0 hsd M₀ c S hc N
  have hKr : HRS.Whole.MemL2Zero μ (K r₀) := (hC ρ hρ r₀ hr).1
  have hrf : r₀ =ᵐ[μ] fun x => f x - γ * K r₀ x := by
    filter_upwards [heq] with x hx; linarith
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, Function.iterate_zero, id_eq, zero_add]
    exact Filter.EventuallyEq.rfl
  | succ M ih =>
    have h1 := tc5_iter_congr (rieszKernel d s) μ hrf M
    have h2 := tc5_iter_sub hs0 hsd M₀ c S hc N hρ hf (tc5_L2Zero_smul γ hKr) M
    have h3 := tc5_iter_smul (rieszKernel d s) μ γ (K r₀) M
    have h4 : K^[M + 1] r₀ = K^[M] (K r₀) := Function.iterate_succ_apply K M r₀
    filter_upwards [ih, h1, h2] with x hx1 hx2 hx3
    have hx4 : K^[M] (fun x => γ * K r₀ x) x = γ * K^[M] (K r₀) x := by
      rw [h3]
    rw [Finset.sum_range_succ]
    rw [hx2, hx3, hx4] at hx1
    rw [← h4] at hx1
    rw [pow_succ]
    linarith [hx1]

/-- **Step 8, finite resolvent identity** for the response `r₀ + γ K r₀ = γ P_μ φ`. -/
theorem tc5_finite_id {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    {ρ : Euc d → ℝ} (hρ : TcRef d ρ M₀ c S N) (γ : ℝ) {φ r₀ : Euc d → ℝ}
    (hφ : MemLp φ 2 (HRS.Whole.withDensityReal ρ))
    (hr : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀)
    (heq : ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
        γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) (M : ℕ) :
    r₀ =ᵐ[HRS.Whole.withDensityReal ρ] fun x =>
      γ * ∑ j ∈ Finset.range M, (-γ) ^ j *
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) x +
        (-γ) ^ M * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[M] r₀ x := by
  have hP : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
      (fun x => γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) :=
    HRS.MS.TcR.tc_memL2Zero_smul_projMean hρ.prob hφ γ
  have h := tc5_finite_id_gen hs0 hsd M₀ c S hc N hρ γ hP hr heq M
  filter_upwards [h] with x hx
  rw [hx]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (tc5_iter_smul (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
    (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) j) x
  rw [this]; ring

/-! ### `C_b` data -/

theorem tc5_cb_mono {m J : ℕ} (h : m ≤ J) {u : Euc d → ℝ} (hu : HRS.MemCb J u) :
    HRS.MemCb m u ∧ HRS.cbNorm m u ≤ HRS.cbNorm J u := by
  refine ⟨⟨hu.1.of_le (by exact_mod_cast h), fun j hj => hu.2 j (hj.trans h)⟩, ?_⟩
  unfold HRS.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

theorem tc5_memLp_of_cb {ν : Measure (Euc d)} [IsFiniteMeasure ν] {m : ℕ} {u : Euc d → ℝ}
    (hu : HRS.MemCb m u) : MemLp u 2 ν :=
  MemLp.of_bound hu.1.continuous.aestronglyMeasurable (HRS.cbNorm m u)
    (Filter.Eventually.of_forall fun x => tc5_cb_sup_le hu x)

theorem tc5_pair_le {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {u : Euc d → ℝ} {B : ℝ}
    (hB : ∀ x, ‖u x‖ ≤ B) : |HRS.Whole.pair ν u| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := u) (C := B) (Filter.Eventually.of_forall hB)
  simpa [HRS.Whole.pair] using this

theorem tc5_l2_le_cb {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {m : ℕ} {u : Euc d → ℝ}
    (hu : HRS.MemCb m u) : HRS.Whole.l2Norm ν u ≤ HRS.cbNorm m u := by
  unfold HRS.Whole.l2Norm
  have hB := tc5_cb_nonneg m u
  calc Real.sqrt (∫ x, u x ^ 2 ∂ν) ≤ Real.sqrt (HRS.cbNorm m u ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => u x ^ 2) (C := HRS.cbNorm m u ^ 2)
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using tc5_cb_sup_le hu x) 2)
        simpa using (le_abs_self _).trans this
    _ = _ := Real.sqrt_sq hB

/-- One application of `K` preserves `C_b^m ∩ L²_0` (representative), boundedly. -/
theorem tc5_cb_step {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    (hmN : m ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ R : Euc d → ℝ, HRS.MemCb m R →
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) R →
        ∃ R' : Euc d → ℝ, HRS.MemCb m R' ∧ HRS.cbNorm m R' ≤ A * HRS.cbNorm m R ∧
          R' =ᵐ[HRS.Whole.withDensityReal ρ] HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) R := by
  obtain ⟨θ, hθ⟩ := tc5_cutoff (d := d)
  obtain ⟨Cl, hCl0, hCl⟩ := tc4_loc_cb_rho (d := d) (θ := θ) (s := s) m hθ hs0 hsd c hc
  obtain ⟨Cf, hCf0, hCf⟩ := tc4_far hθ hs0 m M₀ c hc
  set I : ℝ := ∫ z, ‖θ z * rieszKernel d s z‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  refine ⟨2 * (Cl * |S| * I + Cf), by positivity, fun ρ hρ R hR hR0 => ?_⟩
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hSn := tc5_S_nonneg hρ
  obtain ⟨hLcb, hLn⟩ := hCl ρ M₀ S (tc5_ref_mono hρ hmN) R hR
  obtain ⟨hFcb, hFn⟩ := hCf ρ S (tc5_ref_mono hρ (Nat.zero_le _)) R hR0
  set L := locK d s θ ρ R with hL
  set F := farK d s θ μ R with hF
  have hbR := tc5_cb_nonneg m R
  have hFn' : HRS.cbNorm m F ≤ Cf * HRS.cbNorm m R :=
    hFn.trans (mul_le_mul_of_nonneg_left (tc5_l2_le_cb hR) hCf0)
  have hLn' : HRS.cbNorm m L ≤ Cl * S * I * HRS.cbNorm m R := hLn
  obtain ⟨hAcb, hAn⟩ := tc5_cb_add hLcb hFcb
  set c0 := HRS.Whole.pair μ (fun x => L x + F x) with hc0def
  have hc0 : |c0| ≤ HRS.cbNorm m L + HRS.cbNorm m F := by
    refine tc5_pair_le (fun x => ?_)
    exact (norm_add_le _ _).trans (add_le_add (tc5_cb_sup_le hLcb x) (tc5_cb_sup_le hFcb x))
  obtain ⟨hKcb, hKn⟩ := tc5_cb_add hAcb (tc5_cb_const (d := d) m (-c0)).1
  have hc1 := (tc5_cb_const (d := d) m (-c0)).2
  rw [abs_neg] at hc1
  refine ⟨fun x => (L x + F x) + (-c0), hKcb, ?_, ?_⟩
  · rw [abs_of_nonneg hSn]
    have h1 := tc5_cb_nonneg m L
    have h2 := tc5_cb_nonneg m F
    nlinarith [hLn', hFn', hAn, hKn, hc0, hc1]
  · have hae := tc4_split_mu hρ hc hθ hs0 hsd (tc5_memLp_of_cb hR)
    filter_upwards [hae] with x h2
    rw [h2]
    change L x + F x + -c0 = (L x + F x) - c0
    ring

theorem tc5_cb_smul {m : ℕ} (a : ℝ) {u : Euc d → ℝ} (hu : HRS.MemCb m u) :
    HRS.MemCb m (fun x => a * u x) ∧ HRS.cbNorm m (fun x => a * u x) ≤ |a| * HRS.cbNorm m u := by
  set b : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j u z‖ with hb
  have hble : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j u z‖ ≤ b j := fun j hj z => le_ciSup (hu.2 j hj) z
  have key : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j (fun x => a * u x) z‖ ≤ |a| * b j := by
    intro j hj z
    have hu' : ContDiff ℝ j u := hu.1.of_le (by exact_mod_cast hj)
    have e : iteratedFDeriv ℝ j (fun x => a * u x) z = a • iteratedFDeriv ℝ j u z :=
      iteratedFDeriv_const_smul_apply' (a := a) hu'.contDiffAt
    rw [e, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hble j hj z) (abs_nonneg _)
  refine ⟨⟨contDiff_const.mul hu.1, fun j hj => ⟨|a| * b j, ?_⟩⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact key j hj z
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (m + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => a * u x) z‖
        ≤ ∑ j ∈ Finset.range (m + 1), |a| * b j :=
          Finset.sum_le_sum fun j hj => ciSup_le fun z => key j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) z
      _ = _ := by rw [← Finset.mul_sum]

theorem tc5_cb_sum {m : ℕ} (u : ℕ → Euc d → ℝ) (n : ℕ) (hu : ∀ j < n, HRS.MemCb m (u j)) :
    HRS.MemCb m (fun x => ∑ j ∈ Finset.range n, u j x) ∧
      HRS.cbNorm m (fun x => ∑ j ∈ Finset.range n, u j x) ≤ ∑ j ∈ Finset.range n, HRS.cbNorm m (u j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact ⟨(tc5_cb_const m 0).1, by simpa using (tc5_cb_const (d := d) m 0).2⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hu j (by omega))
    obtain ⟨h3, h4⟩ := tc5_cb_add h1 (hu n (by omega))
    simp only [Finset.sum_range_succ]
    exact ⟨h3, h4.trans (by linarith)⟩

/-- The terms `K^j (P_μ φ)`, `φ ∈ C_b^J`, are in `C_b^m` (representative), `‖·‖ ≤ C ‖φ‖_{C_b^J}`. -/
theorem tc5_terms_cb {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J : ℕ) (hmJ : m ≤ J) (M₀ c S : ℝ)
    (hc : 0 < c) (N : ℕ) (hmN : m ≤ N) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ : Euc d → ℝ, HRS.MemCb J φ →
      ∃ R : Euc d → ℝ, HRS.MemCb m R ∧ HRS.cbNorm m R ≤ C * HRS.cbNorm J φ ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) := by
  obtain ⟨A, hA0, hA⟩ := tc5_cb_step (d := d) hs0 hsd m M₀ c S hc N hmN
  intro j
  induction j with
  | zero =>
    refine ⟨2, by norm_num, fun ρ hρ φ hφ => ?_⟩
    have hprob := tc4_isProb hρ.prob
    obtain ⟨hφm, hφn⟩ := tc5_cb_mono hmJ hφ
    have hp : |HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ| ≤ HRS.cbNorm J φ :=
      tc5_pair_le fun x => tc5_cb_sup_le hφ x
    obtain ⟨h1, h2⟩ := tc5_cb_add hφm (tc5_cb_const (d := d) m (-HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ)).1
    have h3 := (tc5_cb_const (d := d) m (-HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ)).2
    rw [abs_neg] at h3
    refine ⟨_, h1, by linarith, Filter.Eventually.of_forall fun x => ?_⟩
    simp only [Function.iterate_zero, id_eq, HRS.Whole.projMean]
    ring
  | succ j ih =>
    obtain ⟨Cj, hCj0, hCj⟩ := ih
    refine ⟨A * Cj, by positivity, fun ρ hρ φ hφ => ?_⟩
    have hprob := tc4_isProb hρ.prob
    obtain ⟨Rj, hRjcb, hRjn, hRjae⟩ := hCj ρ hρ φ hφ
    have hP : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
        (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) := by
      have := HRS.MS.TcR.tc_memL2Zero_smul_projMean hρ.prob (tc5_memLp_of_cb hφ) 1
      simpa using this
    have hK := tc5_iter_L2Zero hs0 hsd M₀ c S hc N hρ hP j
    have hR0 : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) Rj :=
      ⟨hK.1.ae_eq hRjae.symm, by rw [integral_congr_ae hRjae]; exact hK.2⟩
    obtain ⟨R', hR'cb, hR'n, hR'ae⟩ := hA ρ hρ Rj hRjcb hR0
    refine ⟨R', hR'cb, ?_, ?_⟩
    · calc HRS.cbNorm m R' ≤ A * HRS.cbNorm m Rj := hR'n
        _ ≤ A * (Cj * HRS.cbNorm J φ) := mul_le_mul_of_nonneg_left hRjn hA0
        _ = _ := by ring
    · rw [Function.iterate_succ_apply']
      have := HRS.MS.TcR.tc2_kop_congr_ae (g := rieszKernel d s) hRjae
      rw [← this]
      exact hR'ae

theorem tc5_l2_smul (ν : Measure (Euc d)) (a : ℝ) (u : Euc d → ℝ) :
    HRS.Whole.l2Norm ν (fun x => a * u x) = |a| * HRS.Whole.l2Norm ν u := by
  unfold HRS.Whole.l2Norm
  have : (fun x => (a * u x) ^ 2) = fun x => a ^ 2 * u x ^ 2 := by funext x; ring
  rw [this, integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- `M = ⌈(m + d/2)/(d-s)⌉ + 1` satisfies `m + d/2 < M (d - s)`. -/
theorem tc5_M_spec {s : ℝ} (hsd : s < d) (m : ℕ) :
    (m : ℝ) + d / 2 < ((⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 : ℕ) : ℝ) * ((d : ℝ) - s) := by
  have hα : 0 < (d : ℝ) - s := by linarith
  have h1 : ((m : ℝ) + d / 2) / ((d : ℝ) - s) ≤ ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ := Nat.le_ceil _
  have h2 : (m : ℝ) + d / 2 ≤ ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ * ((d : ℝ) - s) := by
    have := mul_le_mul_of_nonneg_right h1 hα.le
    rwa [div_mul_cancel₀ _ hα.ne'] at this
  push_cast
  nlinarith

/-- **Step 8, abstract assembly.**  `X` is a class of data `φ` with norm `nrm`; hypotheses: the terms
`K^j P_μ φ` (`j < M`) have `C_b^m` representatives bounded by `C_j nrm φ`, `φ ∈ L²(μ)`, and
`‖P_μ φ‖_{L²(μ)} ≤ Cp nrm φ`.  Conclusion: the response `r₀` has a `C_b^m` representative `r` with
`‖r‖ ≤ C nrm φ`, `C` independent of `ρ` and of `γ ∈ (0, γp]`. -/
theorem tc5_assemble {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m M : ℕ)
    (hM : (m : ℝ) + d / 2 < M * ((d : ℝ) - s)) (γp M₀ c S : ℝ) (hc : 0 < c) (N : ℕ)
    (hN : (M : ℝ) * ((d : ℝ) - s) + d < N)
    (X : (Euc d → ℝ) → Prop) (nrm : (Euc d → ℝ) → ℝ) (hnrm : ∀ φ, 0 ≤ nrm φ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hmem : ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ, X φ →
      MemLp φ 2 (HRS.Whole.withDensityReal ρ))
    (hl2 : ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ, X φ →
      HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) ≤
        Cp * nrm φ)
    (hterm : ∀ j : ℕ, j < M → ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ, X φ →
      ∃ R : Euc d → ℝ, HRS.MemCb m R ∧ HRS.cbNorm m R ≤ C * nrm φ ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ → γ ≤ γp →
      ∀ φ : Euc d → ℝ, X φ →
        ∃ r₀ r : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
              γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
          HRS.MemCb m r ∧ HRS.cbNorm m r ≤ C * nrm φ ∧
          r =ᵐ[HRS.Whole.withDensityReal ρ] r₀ := by
  have hd1 : 1 ≤ d := by
    have : 0 < d := by exact_mod_cast (lt_of_le_of_lt hs0 hsd)
    exact this
  obtain ⟨Cs, hCs0, hCs⟩ := tc5_smoothing (d := d) hs0 hsd m M hM M₀ c S hc N hN
  have hterm' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j < M → ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ, X φ →
      ∃ R : Euc d → ℝ, HRS.MemCb m R ∧ HRS.cbNorm m R ≤ C * nrm φ ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ)) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨C, hC0, hC⟩ := hterm j hj
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose Cj hCj0 hCj using hterm'
  set Sg : ℝ := ∑ j ∈ Finset.range M, |γp| ^ j * Cj j with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hCj0 j)
  refine ⟨|γp| * Sg + |γp| ^ M * (Cs * (|γp| * Cp)), by positivity, fun ρ hρ γ hγ hγp φ hφ => ?_⟩
  have hnφ := hnrm φ
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hφ2 : MemLp φ 2 μ := hmem ρ hρ φ hφ
  have hP := HRS.MS.TcR.tc_memL2Zero_smul_projMean hρ.prob hφ2 γ
  obtain ⟨r₀, hr0, hreq, hrn⟩ := HRS.MS.TcR.tc_response hd1 hs0 hsd M₀ c S hc N ρ hρ γ hγ _ hP
  have hγ0 : γ ≤ |γp| := hγp.trans (le_abs_self _)
  have hγa : |γ| = γ := abs_of_pos hγ
  -- the terms
  have hRex : ∀ j : ℕ, ∃ R : Euc d → ℝ, j < M → (HRS.MemCb m R ∧ HRS.cbNorm m R ≤ Cj j * nrm φ ∧
      R =ᵐ[μ] (HRS.Whole.Kop (rieszKernel d s) μ)^[j] (HRS.Whole.projMean μ φ)) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨R, h1, h2, h3⟩ := hCj j hj ρ hρ φ hφ
      exact ⟨R, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose Rj hRj using hRex
  -- the remainder
  obtain ⟨R, hRcb, hRn, hRae⟩ := hCs ρ hρ r₀ hr0
  have hPn : HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ Cp * nrm φ := hl2 ρ hρ φ hφ
  have hr0n : HRS.Whole.l2Norm μ r₀ ≤ γ * (Cp * nrm φ) := by
    refine hrn.trans ?_
    have : HRS.Whole.l2Norm μ (γ • HRS.Whole.projMean μ φ) = γ * HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) := by
      have := tc5_l2_smul μ γ (HRS.Whole.projMean μ φ)
      rw [hγa] at this; exact this
    rw [this]
    exact mul_le_mul_of_nonneg_left hPn hγ.le
  set r : Euc d → ℝ := fun x => γ * ∑ j ∈ Finset.range M, (-γ) ^ j * Rj j x + (-γ) ^ M * R x with hr
  obtain ⟨hS1, hS2⟩ := tc5_cb_sum (fun j x => (-γ) ^ j * Rj j x) M
    (fun j hj => (tc5_cb_smul ((-γ) ^ j) (hRj j hj).1).1)
  obtain ⟨hS3, hS4⟩ := tc5_cb_smul γ hS1
  obtain ⟨hS5, hS6⟩ := tc5_cb_smul ((-γ) ^ M) hRcb
  obtain ⟨hr1, hr2⟩ := tc5_cb_add hS3 hS5
  refine ⟨r₀, r, hr0, hreq, hr1, ?_, ?_⟩
  · have hsum : ∑ j ∈ Finset.range M, HRS.cbNorm m (fun x => (-γ) ^ j * Rj j x) ≤
        Sg * nrm φ := by
      rw [hSg, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hjm => ?_
      have hj' := Finset.mem_range.1 hjm
      refine (tc5_cb_smul ((-γ) ^ j) (hRj j hj').1).2.trans ?_
      rw [abs_pow, abs_neg, hγa]
      calc γ ^ j * HRS.cbNorm m (Rj j) ≤ |γp| ^ j * (Cj j * nrm φ) := by
            exact mul_le_mul (pow_le_pow_left₀ hγ.le hγ0 j) (hRj j hj').2.1 (tc5_cb_nonneg _ _) (by positivity)
        _ = _ := by ring
    have hcb : HRS.cbNorm m r ≤ γ * (Sg * nrm φ) + γ ^ M * (Cs * (γ * (Cp * nrm φ))) := by
      have e1 : HRS.cbNorm m R ≤ Cs * (γ * (Cp * nrm φ)) :=
        hRn.trans (mul_le_mul_of_nonneg_left hr0n hCs0)
      have h1 : HRS.cbNorm m (fun x => γ * ∑ j ∈ Finset.range M, (-γ) ^ j * Rj j x) ≤
          γ * (Sg * nrm φ) := by
        refine hS4.trans ?_
        rw [hγa]
        exact mul_le_mul_of_nonneg_left (hS2.trans hsum) hγ.le
      have h2 : HRS.cbNorm m (fun x => (-γ) ^ M * R x) ≤ γ ^ M * (Cs * (γ * (Cp * nrm φ))) := by
        refine hS6.trans ?_
        rw [abs_pow, abs_neg, hγa]
        exact mul_le_mul_of_nonneg_left e1 (by positivity)
      exact hr2.trans (add_le_add h1 h2)
    refine hcb.trans ?_
    have hCn : 0 ≤ Cp * nrm φ := mul_nonneg hCp hnφ
    have hp1 : γ * (Sg * nrm φ) ≤ |γp| * (Sg * nrm φ) :=
      mul_le_mul_of_nonneg_right hγ0 (mul_nonneg hSg0 hnφ)
    have hp2 : γ ^ M * (Cs * (γ * (Cp * nrm φ))) ≤
        |γp| ^ M * (Cs * (|γp| * (Cp * nrm φ))) := by
      refine mul_le_mul (pow_le_pow_left₀ hγ.le hγ0 M) ?_ (mul_nonneg hCs0 (mul_nonneg hγ.le hCn))
        (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hγ0 hCn) hCs0
    nlinarith [hp1, hp2]
  · -- a.e. identity
    have hfin := tc5_finite_id hs0 hsd M₀ c S hc N hρ γ hφ2 hr0 hreq M
    have hall : ∀ᵐ x ∂μ, ∀ j : ℕ, j < M → Rj j x =
        (HRS.Whole.Kop (rieszKernel d s) μ)^[j] (HRS.Whole.projMean μ φ) x :=
      ae_all_iff.2 fun j => by
        by_cases hj : j < M
        · filter_upwards [(hRj j hj).2.2] with x hx _ using hx
        · exact Filter.Eventually.of_forall fun x h => absurd h hj
    filter_upwards [hfin, hall, hRae] with x h1 h2 h3
    rw [h1]
    simp only [hr]
    rw [h3]
    congr 2
    exact Finset.sum_congr rfl fun j hj => by rw [h2 j (Finset.mem_range.1 hj)]

/-- **Step 8, assembly for `C_b^J` data.**  For `m + d/2 < M (d - s)`, `m ≤ J`, `m ≤ N`, `M α + d < N`,
`γ ∈ (0, γp]`, `φ ∈ C_b^J`: the response `r₀` of `r₀ + γ K r₀ = γ P_μ φ` has a representative `r ∈ C_b^m`
with `‖r‖_{C_b^m} ≤ C ‖φ‖_{C_b^J}`, `C` independent of `ρ`, `γ`. -/
theorem tc5_resolvent_rep {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J M : ℕ) (hmJ : m ≤ J)
    (hM : (m : ℝ) + d / 2 < M * ((d : ℝ) - s)) (γp M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) (hmN : m ≤ N)
    (hN : (M : ℝ) * ((d : ℝ) - s) + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ → γ ≤ γp →
      ∀ φ : Euc d → ℝ, HRS.MemCb J φ →
        ∃ r₀ r : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
              γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
          HRS.MemCb m r ∧ HRS.cbNorm m r ≤ C * HRS.cbNorm J φ ∧
          r =ᵐ[HRS.Whole.withDensityReal ρ] r₀ := by
  refine tc5_assemble hs0 hsd m M hM γp M₀ c S hc N hN (HRS.MemCb J) (HRS.cbNorm J)
    (fun φ => tc5_cb_nonneg J φ) 2 (by norm_num) (fun ρ hρ φ hφ => ?_) (fun ρ hρ φ hφ => ?_)
    (fun j _ => tc5_terms_cb (d := d) hs0 hsd m J hmJ M₀ c S hc N hmN j)
  · have := tc4_isProb hρ.prob
    exact tc5_memLp_of_cb hφ
  · have hprob := tc4_isProb hρ.prob
    set μ := HRS.Whole.withDensityReal ρ with hμ
    obtain ⟨hφm, hφn⟩ := tc5_cb_mono hmJ hφ
    have hp : |HRS.Whole.pair μ φ| ≤ HRS.cbNorm J φ := tc5_pair_le fun x => tc5_cb_sup_le hφ x
    obtain ⟨h1, h2⟩ := tc5_cb_add hφm (tc5_cb_const (d := d) m (-HRS.Whole.pair μ φ)).1
    have h3 := (tc5_cb_const (d := d) m (-HRS.Whole.pair μ φ)).2
    rw [abs_neg] at h3
    have := tc5_l2_le_cb (ν := μ) h1
    have e : (fun x => φ x + -HRS.Whole.pair μ φ) = HRS.Whole.projMean μ φ := by
      funext x; simp [HRS.Whole.projMean, sub_eq_add_neg]
    rw [e] at this h2
    linarith

/-! ### Sobolev data `φ ∈ H^J` -/

theorem tc5_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    _ = _ := Real.sqrt_sq (by positivity)

/-- Iterated Sobolev regularity starting at order `t₀` (norm form). -/
theorem tc5_iter_from {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (M₀ c S : ℝ)
    (hc : 0 < c) (N : ℕ) :
    ∀ n : ℕ, (t₀ + (n : ℝ) * ((d : ℝ) - s) + d < N) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ f : Euc d → ℝ,
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f → MemSob t₀ (fun y => ρ y * f y) →
        HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ)
          ((HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f) ∧
        HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ)
          ((HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f) ≤
            C * (Real.sqrt (SobSq t₀ (fun y => ρ y * f y)) + HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) ∧
        MemSob (t₀ + (n : ℝ) * ((d : ℝ) - s))
          (fun y => ρ y * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f y) ∧
        Real.sqrt (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s))
          (fun y => ρ y * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f y)) ≤
            C * (Real.sqrt (SobSq t₀ (fun y => ρ y * f y)) + HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f) := by
  have hα : 0 < (d : ℝ) - s := by linarith
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨1, zero_le_one, fun ρ hρ f hf hu => ?_⟩
    have hl0 : 0 ≤ HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := Real.sqrt_nonneg _
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul, add_zero]
    refine ⟨hf, ?_, hu, ?_⟩ <;> nlinarith [Real.sqrt_nonneg (SobSq t₀ (fun y => ρ y * f y))]
  | succ n ih =>
    intro hN
    have e : ((n + 1 : ℕ) : ℝ) * ((d : ℝ) - s) = n * ((d : ℝ) - s) + ((d : ℝ) - s) := by push_cast; ring
    rw [e, ← add_assoc] at hN
    obtain ⟨Cn, hCn0, hCn⟩ := ih (by linarith)
    obtain ⟨Ck, hCk0, hCk⟩ := tc5_kop_l2 (d := d) hs0 hsd M₀ c S hc N
    obtain ⟨Cs, hCs0, hCs⟩ := tc5_step (d := d) hs0 hsd (t₀ + (n : ℝ) * ((d : ℝ) - s))
      (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hα.le; linarith) M₀ c S hc N hN
    refine ⟨Ck * Cn + 2 * Cs * Cn, by positivity, fun ρ hρ f hf hu => ?_⟩
    obtain ⟨hm, hl, hsm, hsn⟩ := hCn ρ hρ f hf hu
    set h := (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n] f with hh
    set Q := Real.sqrt (SobSq t₀ (fun y => ρ y * f y)) + HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f with hQ
    have hQ0 : 0 ≤ Q := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hit : (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[n + 1] f =
        HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) h := by
      rw [Function.iterate_succ_apply']
    rw [hit, e, ← add_assoc]
    obtain ⟨hKm, hKl⟩ := hCk ρ hρ h hm
    obtain ⟨hSm, hSn⟩ := hCs ρ hρ h hm hsm
    refine ⟨hKm, ?_, hSm, ?_⟩
    · calc _ ≤ Ck * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h := hKl
        _ ≤ Ck * (Cn * Q) := mul_le_mul_of_nonneg_left hl hCk0
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hCs0 hCn0) hQ0]
    · have h1 : Real.sqrt (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s) + ((d : ℝ) - s)) (fun y => ρ y * (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) h) y)) ≤
          Cs * Real.sqrt (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y) +
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h ^ 2) := by
        calc _ ≤ Real.sqrt (Cs ^ 2 * (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y) +
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h ^ 2)) := Real.sqrt_le_sqrt hSn
          _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCs0]
      have h2 := tc5_sqrt_add_le (tc5_sob_nonneg (t₀ + (n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y))
        (sq_nonneg (HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h))
      have hl0 : 0 ≤ HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h := Real.sqrt_nonneg _
      rw [Real.sqrt_sq hl0] at h2
      have h3 : Real.sqrt (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h ≤ Cn * Q + Cn * Q := add_le_add hsn hl
      calc _ ≤ Cs * (Real.sqrt (SobSq (t₀ + (n : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
            HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) h) := h1.trans (mul_le_mul_of_nonneg_left h2 hCs0)
        _ ≤ Cs * (Cn * Q + Cn * Q) := mul_le_mul_of_nonneg_left h3 hCs0
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hCk0 hCn0) hQ0]

/-- Data `φ ∈ H^J`: `P_μ φ ∈ L²_0(μ)`, `‖P_μ φ‖_{L²(μ)}` and `‖ρ P_μ φ‖_{H^J}` are `≤ K ‖φ‖_{H^J}`;
also `|pair μ φ|² ≤ 2 M₀ ‖φ‖²_{H^J}`. -/
theorem tc5_P_data (J : ℕ) (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) (hN : (J : ℝ) + d < N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ : Euc d → ℝ, MemSob (J : ℝ) φ →
      HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) ∧
      HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) ≤
        K * Real.sqrt (SobSq (J : ℝ) φ) ∧
      (HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ) ^ 2 ≤ 2 * M₀ * SobSq (J : ℝ) φ ∧
      MemSob (J : ℝ) (fun y => ρ y * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ y) ∧
      Real.sqrt (SobSq (J : ℝ) (fun y => ρ y * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ y)) ≤
        K * Real.sqrt (SobSq (J : ℝ) φ) := by
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MS.TcS.tcs_mul_schwartz d N (J : ℝ) hJ0 (by linarith)
  obtain ⟨B, hB0, hB⟩ := tc5_rho_sob (d := d) J hc
  set W : ℝ := tc5_W d c N with hW
  have hW0 : 0 ≤ W := tc5_W_nonneg d c N
  by_cases hex : ∃ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N
  swap
  · exact ⟨0, le_rfl, fun ρ hρ => (hex ⟨ρ, hρ⟩).elim⟩
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hM00 := tc5_M0_nonneg hρ₀
  have hS00 := tc5_S_nonneg hρ₀
  set K1 : ℝ := 2 * (Cm * W * S) ^ 2 + 2 * (2 * M₀ * (B * S ^ 2)) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine ⟨Real.sqrt (K1 + M₀) + 1, by positivity, fun ρ hρ φ hφ => ?_⟩
  have hprob := tc4_isProb hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hSn := tc5_S_nonneg hρ
  set nφ := SobSq (J : ℝ) φ with hnφ
  have hn0 : 0 ≤ nφ := tc5_sob_nonneg _ _
  have hφ2 : MemLp φ 2 μ := (tc5_L_mu hρ hc hφ.1).1
  have hφI : ∫ x, φ x ^ 2 ≤ nφ := tc5_sob_l2 hJ0 hφ
  have hφμ : ∫ x, φ x ^ 2 ∂μ ≤ M₀ * nφ :=
    (tc5_L_mu hρ hc hφ.1).2.trans (mul_le_mul_of_nonneg_left hφI hM00)
  -- the mean
  set p0 := HRS.Whole.pair μ φ with hp0
  have hp0b : p0 ^ 2 ≤ 2 * M₀ * nφ := by
    have := tc5_pair_bound hρ hc hφ.1 (F := fun _ => (0 : ℝ)) continuous_const (B := 0) (fun x => by simp)
    simp only [add_zero] at this
    have h2 : p0 ^ 2 ≤ 2 * M₀ * (∫ x, φ x ^ 2) + 2 * 0 ^ 2 := this
    have := mul_le_mul_of_nonneg_left hφI (by positivity : (0 : ℝ) ≤ 2 * M₀)
    linarith
  have hP : HRS.Whole.MemL2Zero μ (HRS.Whole.projMean μ φ) := by
    have := HRS.MS.TcR.tc_memL2Zero_smul_projMean hρ.prob hφ2 1
    simpa using this
  -- the variance bound
  have hvar : ∫ x, (φ x - p0) ^ 2 ∂μ ≤ ∫ x, φ x ^ 2 ∂μ := by
    have i1 : Integrable (fun x => φ x ^ 2) μ := hφ2.integrable_sq
    have i2 : Integrable φ μ := hφ2.integrable (by norm_num)
    have e : (fun x => (φ x - p0) ^ 2) = fun x => (φ x ^ 2 - 2 * p0 * φ x) + p0 ^ 2 := by
      funext x; ring
    have i3 : Integrable (fun x => 2 * p0 * φ x) μ := i2.const_mul _
    have i4 : Integrable (fun x => φ x ^ 2 - 2 * p0 * φ x) μ := i1.sub i3
    rw [e, integral_add i4 (integrable_const _), integral_sub i1 i3,
      integral_const_mul, integral_const]
    have : ∫ x, φ x ∂μ = p0 := rfl
    rw [this]
    simp only [probReal_univ, one_smul]
    nlinarith [sq_nonneg p0]
  have hl2 : HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ Real.sqrt (M₀ * nφ) := by
    unfold HRS.Whole.l2Norm
    refine Real.sqrt_le_sqrt ?_
    exact hvar.trans hφμ
  -- `ρ P φ`
  obtain ⟨hρφm, hρφn⟩ := hCm ρ hρ.smooth (fun j hj => (tc5_rho_W hρ hc).1 j hj) φ hφ
  have hsum := (tc5_rho_W hρ hc).2
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _
  have hN1 : SobSq (J : ℝ) (fun x => ρ x * φ x) ≤ (Cm * W * S) ^ 2 * nφ := by
    refine hρφn.trans (mul_le_mul_of_nonneg_right ?_ hn0)
    refine pow_le_pow_left₀ (mul_nonneg hCm0 hsum0) ?_ 2
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum hCm0
  have hJN : J ≤ N := by
    have : (J : ℝ) ≤ N := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    exact_mod_cast this
  have hρJ := hB ρ M₀ S (tc5_ref_mono hρ hJN)
  obtain ⟨hT3m, hT3n⟩ := tc5_sob_smul (-p0) hρJ.1
  obtain ⟨hAm, hAn⟩ := tc5_sob_add hρφm hT3m
  have e : (fun y => ρ y * HRS.Whole.projMean μ φ y) = fun x => ρ x * φ x + (-p0) * ρ x := by
    funext x; simp only [HRS.Whole.projMean]; ring
  rw [e]
  have hN3 : SobSq (J : ℝ) (fun x => (-p0) * ρ x) ≤ 2 * M₀ * (B * S ^ 2) * nφ := by
    rw [hT3n, neg_sq]
    calc p0 ^ 2 * SobSq (J : ℝ) ρ ≤ (2 * M₀ * nφ) * (B * S ^ 2) :=
          mul_le_mul hp0b hρJ.2 (tc5_sob_nonneg _ _) (by positivity)
      _ = _ := by ring
  have hbound : SobSq (J : ℝ) (fun x => ρ x * φ x + (-p0) * ρ x) ≤ K1 * nφ := by
    refine hAn.trans ?_
    rw [hK1]; nlinarith [hN1, hN3]
  refine ⟨hP, ?_, hp0b, hAm, ?_⟩
  · refine hl2.trans ?_
    calc Real.sqrt (M₀ * nφ) = Real.sqrt M₀ * Real.sqrt nφ := Real.sqrt_mul hM00 _
      _ ≤ _ := by
          have : Real.sqrt M₀ ≤ Real.sqrt (K1 + M₀) + 1 := by
            have := Real.sqrt_le_sqrt (show M₀ ≤ K1 + M₀ by linarith)
            linarith
          exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  · calc Real.sqrt (SobSq (J : ℝ) (fun x => ρ x * φ x + (-p0) * ρ x)) ≤ Real.sqrt (K1 * nφ) :=
          Real.sqrt_le_sqrt hbound
      _ = Real.sqrt K1 * Real.sqrt nφ := Real.sqrt_mul hK10 _
      _ ≤ _ := by
          have : Real.sqrt K1 ≤ Real.sqrt (K1 + M₀) + 1 := by
            have := Real.sqrt_le_sqrt (show K1 ≤ K1 + M₀ by linarith)
            linarith
          exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

/-- The terms `K^j (P_μ φ)`, `φ ∈ H^J`, `m + d/2 < J`, are in `C_b^m` (representative), `‖·‖ ≤ C ‖φ‖_{H^J}`. -/
theorem tc5_terms_sob {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J M : ℕ) (hJ : (m : ℝ) + d / 2 < J)
    (M₀ c S : ℝ) (hc : 0 < c) (N : ℕ) (hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N) :
    ∀ j : ℕ, j < M → ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ φ : Euc d → ℝ,
      MemSob (J : ℝ) φ → ∃ R : Euc d → ℝ, HRS.MemCb m R ∧
        HRS.cbNorm m R ≤ C * Real.sqrt (SobSq (J : ℝ) φ) ∧
        R =ᵐ[HRS.Whole.withDensityReal ρ]
          (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ))^[j]
            (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ) := by
  have hα : 0 < (d : ℝ) - s := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by
    have : (0 : ℝ) ≤ (m : ℝ) + d / 2 := by positivity
    linarith
  intro j hj
  have hMα : (0 : ℝ) ≤ M * ((d : ℝ) - s) := by positivity
  have hN0 : (J : ℝ) + d < N := by linarith
  obtain ⟨K, hK0, hK⟩ := tc5_P_data (d := d) J M₀ c S hc N hN0
  cases j with
  | zero =>
    obtain ⟨Cr, hCr0, hCr⟩ := HRS.MS.TcS.tcs_rep (d := d) m hJ
    refine ⟨Cr + Real.sqrt (2 * M₀), by positivity, fun ρ hρ φ hφ => ?_⟩
    have hprob := tc4_isProb hρ.prob
    set μ := HRS.Whole.withDensityReal ρ with hμ
    obtain ⟨-, -, hp0b, -, -⟩ := hK ρ hρ φ hφ
    obtain ⟨R, hRcb, hRae, hRn⟩ := hCr φ hφ
    set p0 := HRS.Whole.pair μ φ with hp0
    have hp0a : |p0| ≤ Real.sqrt (2 * M₀) * Real.sqrt (SobSq (J : ℝ) φ) := by
      rw [← Real.sqrt_mul (by have := tc5_M0_nonneg hρ; positivity)]
      exact Real.abs_le_sqrt hp0b |> fun h => by
        calc |p0| ≤ Real.sqrt (2 * M₀ * SobSq (J : ℝ) φ) := Real.abs_le_sqrt (by linarith)
          _ = _ := rfl
    obtain ⟨h1, h2⟩ := tc5_cb_add hRcb (tc5_cb_const (d := d) m (-p0)).1
    have h3 := (tc5_cb_const (d := d) m (-p0)).2
    rw [abs_neg] at h3
    refine ⟨_, h1, ?_, ?_⟩
    · have := tc5_sob_nonneg (J : ℝ) φ
      have hs := Real.sqrt_nonneg (SobSq (J : ℝ) φ)
      nlinarith [hRn, hp0a, h2, h3]
    · have hacv : μ ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
      filter_upwards [hacv.ae_le hRae] with x hx
      simp only [Function.iterate_zero, id_eq, HRS.Whole.projMean]
      rw [hx]; ring
  | succ i =>
    have hi : i < M := by omega
    have hiα : (i : ℝ) * ((d : ℝ) - s) ≤ M * ((d : ℝ) - s) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hα.le
    obtain ⟨Ci, hCi0, hCi⟩ := tc5_iter_from (d := d) hs0 hsd (J : ℝ) hJ0 M₀ c S hc N i (by linarith)
    obtain ⟨Cr, hCr0, hCr⟩ := tc5_rep_step (d := d) hs0 hsd m ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s))
      (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hα.le; linarith) (by
        have := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hα.le; linarith) M₀ c S hc N
    refine ⟨Cr * (2 * Ci * (2 * K)), by positivity, fun ρ hρ φ hφ => ?_⟩
    have hprob := tc4_isProb hρ.prob
    set μ := HRS.Whole.withDensityReal ρ with hμ
    obtain ⟨hPm, hPl, -, hPs, hPn⟩ := hK ρ hρ φ hφ
    obtain ⟨hhm, hhl, hhs, hhn⟩ := hCi ρ hρ _ hPm hPs
    set h := (HRS.Whole.Kop (rieszKernel d s) μ)^[i] (HRS.Whole.projMean μ φ) with hh
    obtain ⟨R, hRcb, hRn, hRae⟩ := hCr ρ hρ h hhm hhs
    refine ⟨R, hRcb, ?_, ?_⟩
    · set q := Real.sqrt (SobSq (J : ℝ) φ) with hq
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hQ : Real.sqrt (SobSq (J : ℝ) (fun y => ρ y * HRS.Whole.projMean μ φ y)) +
          HRS.Whole.l2Norm μ (HRS.Whole.projMean μ φ) ≤ 2 * K * q := by linarith
      have h1 : Real.sqrt (SobSq ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
          HRS.Whole.l2Norm μ h ≤ 2 * Ci * (2 * K * q) := by
        have := mul_le_mul_of_nonneg_left hQ hCi0
        linarith
      calc HRS.cbNorm m R ≤ Cr * (Real.sqrt (SobSq ((J : ℝ) + (i : ℝ) * ((d : ℝ) - s)) (fun y => ρ y * h y)) +
            HRS.Whole.l2Norm μ h) := hRn
        _ ≤ Cr * (2 * Ci * (2 * K * q)) := mul_le_mul_of_nonneg_left h1 hCr0
        _ = _ := by ring
    · rw [Function.iterate_succ_apply']
      exact hRae

/-- **Step 8, assembly for `H^J` data** (`m + d/2 < J`). -/
theorem tc5_resolvent_rep_sob {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m J M : ℕ)
    (hJ : (m : ℝ) + d / 2 < J) (hM : (m : ℝ) + d / 2 < M * ((d : ℝ) - s)) (γp M₀ c S : ℝ) (hc : 0 < c)
    (N : ℕ) (hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, TcRef d ρ M₀ c S N → ∀ γ : ℝ, 0 < γ → γ ≤ γp →
      ∀ φ : Euc d → ℝ, MemSob (J : ℝ) φ →
        ∃ r₀ r : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
          (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
            r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
              γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
          HRS.MemCb m r ∧ HRS.cbNorm m r ≤ C * Real.sqrt (SobSq (J : ℝ) φ) ∧
          r =ᵐ[HRS.Whole.withDensityReal ρ] r₀ := by
  have hα : 0 < (d : ℝ) - s := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by
    have : (0 : ℝ) ≤ (m : ℝ) + d / 2 := by positivity
    linarith
  have hMα : (0 : ℝ) ≤ M * ((d : ℝ) - s) := by positivity
  obtain ⟨K, hK0, hK⟩ := tc5_P_data (d := d) J M₀ c S hc N (by linarith)
  exact tc5_assemble hs0 hsd m M hM γp M₀ c S hc N (by linarith) (MemSob (J : ℝ))
    (fun φ => Real.sqrt (SobSq (J : ℝ) φ)) (fun φ => Real.sqrt_nonneg _) K hK0
    (fun ρ hρ φ hφ => (tc5_L_mu hρ hc hφ.1).1)
    (fun ρ hρ φ hφ => (hK ρ hρ φ hφ).2.1)
    (fun j hj => tc5_terms_sob hs0 hsd m J M hJ M₀ c S hc N hN j hj)

end HRS.MS.Tc5

end
