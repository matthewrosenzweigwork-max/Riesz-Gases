import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Assembly
import HRS.Commutator.Whole.External
import HRS.Commutator.Whole.BridgeAux

/-!
# Theorem 1.1 of the note implies `HRS.Whole.whole_commutator_sub_sharp` (S.B.5(ii))

Source: whole-space supplement `S:prop:whole-commutators`, item (ii) `B:item:comm-rd-sub-sharp`
(S L11382-11389; `HRS/Whole/AppendixBEnergy.lean`), versus Theorem 1.1 of `[N]`.  Packet `CMX-BRIDGE`.

Differences, all handled below (checked exactly):

1. *Normalisation of the kernel.*  The repository's `rieszKernel d s = |x|^{-s}` (`s > 0`), `-log|x|`
   (`s = 0`) equals `rieszScale s • kern s` with `rieszScale s = s` (`s > 0`), `1` (`s = 0`);
   hence `rieszModulatedEnergy = rieszScale s · F_N`, `commN = rieszScale s · 𝖠₁`
   (`rieszEnergy_eq`, `commN_eq`).  The additive constant is `C₀' = rieszScale s · C₀`.
2. *Transport norm.*  S.B.5(ii) has `a ∈ (d, d+2)` and `‖|∇|^{a/2}v‖_{L^{2d/(a-2)}}`;
   `[N] (1.regularity-embedding)` (`sobolev_embedding_frac`) bounds `C(v) ≲_{d,s,a} ‖∇v‖_∞ +
   ‖|∇|^{a/2}v‖`, so `C_a = C · C_emb(a)` (quantified before `Λ, N, ρ, X, v`, as in S.B.5(ii)).
3. *Error term.*  S.B.5(ii) uses `o_N = oNΛ d s C₀ Λ N` with `Λ ≥ ‖ρ‖_∞` arbitrary, `Λ ≥ 1`,
   `N ≥ 2`; the note uses `λ = (N‖ρ‖_∞)^{-1/d}`.  Since `‖ρ‖_∞ ≤ Λ`:
   `-log λ/(2N) = log(N‖ρ‖_∞)/(2dN) ≤ log(NΛ)/(2dN)` and
   `‖ρ‖_∞ λ^{d-s} = ‖ρ‖_∞^{s/d} N^{s/d-1} ≤ Λ^{s/d} N^{s/d-1}`, so `[N]`'s bracket is `≤ F_N + o_N`
   after multiplication by `rieszScale s`.
4. *Log hypothesis.*  S.B.5(ii) assumes the log moment `∫ log(2+|x|) dμ ≤ L` (constants quantified after
   `L`); `[N]` assumes `(1.loghyp)`, which follows (`logIntegrable_of_logMoment`), and its constants do
   *not* depend on `L`.  So `[N]` is stronger.
5. *Representation.*  `μ = withDensityReal ρ` (a measure) versus the function `ρ`; `IsProbDensity`
   implies `Integrable ρ`, `MemLp ρ ∞`, `∫ρ = 1`; absolute convergence (`CommIntegrableW`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

variable {d : ℕ} {s : ℝ}

/-- The factor between the repository's kernel and the note's: `s` for `s > 0`, `1` for `s = 0`. -/
def rieszScale (s : ℝ) : ℝ := if s = 0 then 1 else s

theorem rieszScale_pos (hs0 : 0 ≤ s) : 0 < rieszScale s := by
  unfold rieszScale
  split_ifs with h
  · exact one_pos
  · exact lt_of_le_of_ne hs0 (Ne.symm h)

/-- `rieszModulatedEnergy d s X (ρ dx) = rieszScale s · F_N(X, ρ)` for a probability density
(`rieszKernel = rieszScale s • kern s`; `∫ f d(withDensityReal ρ) = ∫ ρ f dx` for `ρ ≥ 0`;
unconditional, Bochner integrals on both sides). -/
theorem rieszEnergy_eq (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) {N : ℕ}
    (X : Fin N → Euc d) :
    HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) =
      rieszScale s * modEnergy s X ρ := by
  have h := cmxFB_cpf_eq hρ (rieszScale s) (fun x y => kern s (x - y))
    (fun x y => HRS.Whole.rieszKernel d s (x - y)) (fun x y => cmxFB_rk_eq _) X
  have e : HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) =
      (1 / 2) * HRS.Whole.centeredPairFunctional (fun x y => HRS.Whole.rieszKernel d s (x - y)) X
        (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.rieszModulatedEnergy HRS.Whole.modulatedEnergy
      HRS.Whole.centeredPairFunctional HRS.Whole.convMeasure HRS.Whole.energyPairing
    ring
  rw [e, h]
  unfold modEnergy
  ring

/-- `commN d s v X (ρ dx) = rieszScale s · 𝖠₁[X, ρ, v]` (`∇(|x|^{-s}) = s ∇g`; off the diagonal
`rieszKernelGrad d s z = rieszScale s • kernGrad s z` for `z ≠ 0` via `HasGradientAt`; both kernels vanish
on the diagonal since `v x - v x = 0`; the particle diagonal is deleted on both sides). -/
theorem commN_eq (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) {N : ℕ} (X : Fin N → Euc d)
    (hX : Function.Injective X) (v : Euc d → Euc d) :
    HRS.Whole.commN d s v X (HRS.Whole.withDensityReal ρ) = rieszScale s * commA s X ρ v := by
  unfold HRS.Whole.commN commA
  exact cmxFB_cpf_eq hρ (rieszScale s) (commKer (kernGrad s) v) (HRS.Whole.commutatorKernel d s v)
    (cmxFB_commKernel_eq v) X

/-- Absolute convergence: `CommIntegrableW d s v X (ρ dx) ↔ CommIntegrable s X ρ v` (`s ≥ 0`;
`integrable_withDensity_iff_integrable_smul`, `prod_withDensity`, and the factor `rieszScale s ≠ 0`). -/
theorem commIntegrableW_iff (hs0 : 0 ≤ s) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ)
    {N : ℕ} (X : Fin N → Euc d) (hX : Function.Injective X) (v : Euc d → Euc d) :
    HRS.Whole.CommIntegrableW d s v X (HRS.Whole.withDensityReal ρ) ↔ CommIntegrable s X ρ v := by
  have hc : rieszScale s ≠ 0 := (rieszScale_pos hs0).ne'
  unfold HRS.Whole.CommIntegrableW CommIntegrable PairIntegrable
  have key := cmxFB_commKernel_eq (d := d) (s := s) v
  have h1 : ∀ a : Euc d, Integrable (fun y => HRS.Whole.commutatorKernel d s v a y)
      (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun y => commKer (kernGrad s) v a y * ρ y) := by
    intro a
    rw [cmxFB_integrable_wd hρ]
    refine cmxFB_integrable_scale (c := rieszScale s) hc fun y => ?_
    simp only [smul_eq_mul, key]
    unfold rieszScale
    ring
  have h2 : Integrable (fun p : Euc d × Euc d => HRS.Whole.commutatorKernel d s v p.1 p.2)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ↔
      Integrable (fun p : Euc d × Euc d => commKer (kernGrad s) v p.1 p.2 * ρ p.1 * ρ p.2)
        (volume.prod volume) := by
    rw [cmxFB_integrable_wd2 hρ]
    refine cmxFB_integrable_scale (c := rieszScale s) hc fun p => ?_
    simp only [key]
    unfold rieszScale
    ring
  rw [h2]
  exact and_congr (forall_congr' fun i => h1 (X i)) Iff.rfl

/-- The log moment `∫ log(2+|x|) dμ ≤ L` with a bounded density `ρ ≤ Λ` implies `(1.loghyp)`
(`[N] L794-799` for the reverse direction; here: local part `‖ρ‖_∞∫_{B_1}|log|`, far part by
`log|x-y| ≤ log(2+|x|) + log(2+|y|)`). -/
theorem logIntegrable_of_logMoment (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (L : ℝ) (hlog : HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal ρ) L) :
    LogIntegrable ρ :=
  cmxFB_logIntegrable ρ hρ Λ hΛ L hlog

/-- `‖ρ‖_{L^∞} ≤ Λ` for `0 ≤ ρ ≤ Λ`. -/
theorem normE_top_le (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) : normE ⊤ ρ ≤ Λ := by
  have h : eLpNorm ρ ⊤ volume ≤ ENNReal.ofReal Λ := by
    rw [eLpNorm_exponent_top hρ.measurable.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]; exact hΛ x)
  have hΛ0 : 0 ≤ Λ := le_trans (hρ.nonneg 0) (hΛ 0)
  exact ENNReal.toReal_le_of_le_ofReal hΛ0 h

/-- The common core of the two bridges: Theorem 1.1 of the note, translated to the repository's
whole-space conventions (`rieszModulatedEnergy`, `commN`, `oNΛ`, `withDensityReal`), for a transport with
`C(v) ≤ K` (`SubTransport`, the exponent `(d-s)/2` of Theorem 1.1) and the hypothesis `(1.loghyp)`
instead of the log moment (so the constants are independent of any `L`). -/
theorem bridge_core (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → LogIntegrable ρ) →
      ∀ X : HRS.Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        HRS.Whole.CommIntegrableW d s v X (HRS.Whole.withDensityReal ρ) ∧
        |HRS.Whole.commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          C * K * (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
            HRS.oNΛ d s C₀ Λ N) := by
  obtain ⟨C, C₀, hC, hC₀, H⟩ := subcoulomb_commutator hd hs0 hsd
  have hsc := rieszScale_pos hs0
  refine ⟨rieszScale s * C₀, C, by positivity, hC, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ hlog' X hX v K hv'
  have hK : 0 ≤ K := by
    obtain ⟨L', F, hF, -, -, hLK⟩ := hv'
    have h0 : (0 : ℝ) ≤ (L' : ℝ) := L'.coe_nonneg
    linarith
  have h1 : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hinf : MemLp ρ ⊤ volume :=
    memLp_top_of_bound h1.aestronglyMeasurable |Λ| (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact le_trans (hΛρ x) (le_abs_self Λ))
  obtain ⟨-, hCI, hQ, hA⟩ := H ρ h1 hinf hρ.integral_one hlog' v K hv' N X (by omega) hX
  refine ⟨(commIntegrableW_iff hs0 ρ hρ X hX v).2 hCI, ?_⟩
  rw [commN_eq ρ hρ X hX v, rieszEnergy_eq ρ hρ X, abs_mul, abs_of_pos hsc]
  -- `λ`-bookkeeping
  have hM := normE_top_pos ρ h1 hinf hρ.integral_one
  have hMΛ := normE_top_le ρ hρ Λ hΛρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNM : 0 < (N : ℝ) * normE ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamN d N ρ := Real.rpow_pos_of_pos hNM _
  have hlamd : lamN d N ρ ^ (d : ℝ) = ((N : ℝ) * normE ⊤ ρ)⁻¹ := by
    unfold lamN
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hlams : lamN d N ρ ^ (-s) = ((N : ℝ) * normE ⊤ ρ) ^ (s / d) := by
    unfold lamN
    rw [← Real.rpow_mul hNM.le]
    congr 1
    field_simp
  have hMl : normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s) ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd, hlams, Real.mul_rpow hNpos.le hM.le]
    have e : normE ⊤ ρ * (((N : ℝ) * normE ⊤ ρ)⁻¹ * ((N : ℝ) ^ (s / d) * normE ⊤ ρ ^ (s / d))) =
        (N : ℝ) ^ (s / d - 1) * normE ⊤ ρ ^ (s / d) := by
      rw [Real.rpow_sub_one hNpos.ne']
      field_simp
    rw [e, mul_comm]
    gcongr
  have hlogterm : (if s = 0 then -(Real.log (lamN d N ρ) / (2 * (N : ℝ))) else 0) ≤
      (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
    split_ifs with h0
    · have h2 : Real.log (lamN d N ρ) = (-(1 : ℝ) / d) * Real.log ((N : ℝ) * normE ⊤ ρ) := by
        unfold lamN; rw [Real.log_rpow hNM]
      rw [h2]
      have h3 : Real.log ((N : ℝ) * normE ⊤ ρ) ≤ Real.log ((N : ℝ) * Λ) :=
        Real.log_le_log hNM (mul_le_mul_of_nonneg_left hMΛ hNpos.le)
      have : -((-(1 : ℝ) / d * Real.log ((N : ℝ) * normE ⊤ ρ)) / (2 * (N : ℝ))) =
          Real.log ((N : ℝ) * normE ⊤ ρ) / (2 * d * N) := by field_simp
      rw [this]
      gcongr
    · exact le_rfl
  -- assemble
  have hfin : rieszScale s * (modEnergy s X ρ -
        (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
        C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) ≤
      rieszScale s * modEnergy s X ρ + HRS.oNΛ d s (rieszScale s * C₀) Λ N := by
    unfold HRS.oNΛ
    have hs1 : rieszScale s * (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) =
        (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) := by
      unfold rieszScale; split_ifs <;> simp
    have h5 : rieszScale s * (C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) ≤
        rieszScale s * C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
      calc rieszScale s * (C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s))
          = rieszScale s * C₀ * (normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) := by ring
        _ ≤ rieszScale s * C₀ * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by gcongr
        _ = _ := by ring
    have h6 : rieszScale s * (modEnergy s X ρ -
          (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
          C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) =
        rieszScale s * modEnergy s X ρ - (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
          rieszScale s * (C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) := by
      rw [mul_add, mul_sub, hs1]
    rw [h6]
    have h7 : -(if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) ≤
        (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
      split_ifs at hlogterm ⊢ with h0
      · simpa [neg_div] using hlogterm
      · simp
    linarith
  calc rieszScale s * |commA s X ρ v|
      ≤ rieszScale s * (C * K * (modEnergy s X ρ -
          (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
          C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s))) := by gcongr
    _ = C * K * (rieszScale s * (modEnergy s X ρ -
          (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
          C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s))) := by ring
    _ ≤ C * K * (rieszScale s * modEnergy s X ρ + HRS.oNΛ d s (rieszScale s * C₀) Λ N) := by
        gcongr
    

/-- `e_N^{lr} ≥ 0` for `N ≥ 1`. -/
theorem commLowRateError_nonneg (s : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ HRS.Whole.commLowRateError s N := by
  unfold HRS.Whole.commLowRateError
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ (if s = 0 then Real.log N else 0) := by
    split_ifs
    · exact Real.log_nonneg hN'
    · exact le_rfl
  have : 0 ≤ (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2)))) := Real.rpow_nonneg (by positivity) _
  positivity

/-- **Theorem 1.1 of the note implies `HRS.Whole.whole_commutator_sub_sharp`** (S.B.5(ii); the statement
is copied verbatim from `HRS/Whole/AppendixBEnergy.lean`; `C₀, C` are quantified after `a` and `L`
and before `Λ, N, ρ, X, v`).  Proof: `bridge_core` + `sobolev_embedding_frac` (`C_a = C·C_emb(a)`) +
`logIntegrable_of_logMoment`. -/
theorem whole_commutator_sub_sharp_of_subcoulomb {s : ℝ} (hs0 : 0 ≤ s)
    (hsd : s < (d : ℝ) - 2) (a : ℝ) (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (L : ℝ) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal ρ) L) →
      ∀ X : HRS.Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ),
        HRS.Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K →
        HRS.Whole.CommIntegrableW d s v X (HRS.Whole.withDensityReal ρ) ∧
        |HRS.Whole.commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          C * K * (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
            HRS.oNΛ d s C₀ Λ N) := by
  have hd : 3 ≤ d := by
    have h2 : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast h2
    omega
  obtain ⟨C₀, C, hC₀, hC, H⟩ := bridge_core hd hs0 hsd
  obtain ⟨Ce, hCe, E⟩ := sobolev_embedding_frac hd hs0 hsd a ha
  refine ⟨C₀, C * Ce, hC₀, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
  obtain ⟨hci, hb⟩ := H Λ hΛ N hN ρ hρ hΛρ
    (fun h0 => logIntegrable_of_logMoment ρ hρ Λ hΛρ L (hlog h0)) X hX v (Ce * K) (E v K hv)
  refine ⟨hci, ?_⟩
  have e : C * (Ce * K) = C * Ce * K := by ring
  rwa [e] at hb

/-- **Theorem 1.1 of the note implies `HRS.Whole.whole_commutator_sub_lower`** (S.B.5(iii), the
strict sub-Coulomb specialization of NRS Prop. 4.1; statement copied verbatim): the transport norm is
literally that of Theorem 1.1, and the error `o_N + C e_N^{lr}` of S.B.5(iii) is *larger* than `o_N`
(`e_N^{lr} ≥ 0`), so (iii) is a corollary of `bridge_core` (and is strictly weaker). -/
theorem whole_commutator_sub_lower_of_subcoulomb {s : ℝ} (hs0 : 0 ≤ s)
    (hsd : s < (d : ℝ) - 2) (L : ℝ) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal ρ) L) →
      ∀ X : HRS.Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ),
        HRS.Whole.HasFracTransportBound (((d : ℝ) - s) / 2) (2 * d / ((d : ℝ) - s - 2)) v K →
        HRS.Whole.CommIntegrableW d s v X (HRS.Whole.withDensityReal ρ) ∧
        |HRS.Whole.commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          C * K * (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
            HRS.oNΛ d s C₀ Λ N + C * HRS.Whole.commLowRateError s N) := by
  have hd : 3 ≤ d := by
    have h2 : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast h2
    omega
  obtain ⟨C₀, C, hC₀, hC, H⟩ := bridge_core hd hs0 hsd
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
  obtain ⟨hci, hb⟩ := H Λ hΛ N hN ρ hρ hΛρ
    (fun h0 => logIntegrable_of_logMoment ρ hρ Λ hΛρ L (hlog h0)) X hX v K hv
  refine ⟨hci, hb.trans ?_⟩
  have hK : 0 ≤ K := by
    obtain ⟨L', F, hF, -, -, hLK⟩ := hv
    have h0 : (0 : ℝ) ≤ (L' : ℝ) := L'.coe_nonneg
    linarith
  have he := commLowRateError_nonneg s (N := N) (by omega)
  have hCK : 0 ≤ C * K := by positivity
  have hce : 0 ≤ C * HRS.Whole.commLowRateError s N := by positivity
  have := mul_le_mul_of_nonneg_left
    (show HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀ Λ N ≤
      HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀ Λ N +
        C * HRS.Whole.commLowRateError s N by linarith) hCK
  exact this

/-- The two statements are the same propositions as the repository's (checked by `rfl` up to proof
irrelevance): the note proves exactly the repository's `S.B.5(ii)` and `S.B.5(iii)` externals. -/
example : @whole_commutator_sub_sharp_of_subcoulomb = @HRS.Whole.whole_commutator_sub_sharp := rfl

example : @whole_commutator_sub_lower_of_subcoulomb = @HRS.Whole.whole_commutator_sub_lower := rfl

end HRS.Commutator.Whole
