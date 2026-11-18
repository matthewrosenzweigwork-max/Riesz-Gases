import HRS.MS.S88BDA02
import HRS.MS.S88BDA04
import HRS.MS.S88BDE02

/-!
# S8.8.A05: summable centered base and increment envelopes, uniform in `ρ`

`s88_orbit_envelopes`: there are `c > 0` and a nonnegative summable `b` (before `ρ`) such that for every thermal
equilibrium `ρ` the actual orbits are regular (`S88OrbitRegular`) and satisfy the two centered `L²(μ)` envelopes
`‖P_μ f_α(u)‖² ≤ b_α e^{-2cu}`, `‖P_μ(f_α(u+s) - f_α(u+t))‖² ≤ b_α e^{-2cu}(s-t)²` for `u ≥ 1`.

Route: by E02 the dual coefficients of the centered orbit are `e^{-tω_l} a_{αl}`, so by A04 the centered orbit is
`S (semiDiag om t z_α)` a.e. with `z_α = (a_{αl})_l ∈ ℓ²`, `‖z_α‖² ≤ B_α` (Bessel).  A02 gives the exponential decay
and the derivative bound of `semiDiag`, hence (mean value inequality) the Lipschitz estimate; `‖S‖² ≤ K` (A03/A04).
All thermal equilibria coincide (`mv0_rho_eq`), so `c, b` are chosen once.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

/-- The envelopes for one fixed thermal equilibrium. -/
theorem s88_envelope_single {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ (c : ℝ) (b : MultiIndex d → ℝ), 0 < c ∧ (∀ α, 0 ≤ b α) ∧ Summable b ∧
      S88OrbitEnvelope (critCoeff d a β ρ) (HRS.Whole.withDensityReal ρ) m c b := by
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hprob : HRS.Whole.IsProbDensity ρ := hρ.1.1
  haveI := Q34.isProbabilityMeasure_nu hprob
  have hreg := s88_regular_orbit hd a β ha hβ m hm ρ hρ
  obtain ⟨e, om, hdata, hcoef⟩ := s88_classical_spectral_coefficients hd a β ha hβ m hm ρ hρ
  obtain ⟨K, hK0, hfin⟩ := s88_finite_synthesis_bound hd a β ha hβ ρ hρ e om hdata
  obtain ⟨S, hSn, hScent, hScoef, hSrec⟩ :=
    s88_synthesis_reconstruction hd a β ha hβ ρ hρ e om hdata K hK0 hfin
  obtain ⟨B, hBsum, hB0, hBes⟩ := u11_coef_bessel hd ha hβ hρ hdata.centered hdata.orth hm
  have hom0 : 0 < om 0 := hdata.pos 0
  have hgap : ∀ l, om 0 ≤ om l := fun l => hdata.mono (Nat.zero_le l)
  obtain ⟨D, hD0, hDder⟩ := s88_diagonal_derivative om (om 0) hom0 hgap
  refine ⟨om 0 / 2, fun α => K * D * B α, by positivity,
    fun α => by have := hB0 α; positivity, hBsum.mul_left _, ?_⟩
  -- regularity of the orbits
  have horb : ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t →
      Continuous (s88Orbit (critCoeff d a β ρ) m t α) ∧
        ∃ B' : ℝ, ∀ x, |s88Orbit (critCoeff d a β ρ) m t α x| ≤ B' := by
    intro α t ht
    refine ⟨(hreg.memCb α t ht).1.continuous, ?_⟩
    obtain ⟨B', -, hB'⟩ := hreg.local_bdd α t ht
    exact ⟨B', fun x => hB' t ⟨ht, le_rfl⟩ x⟩
  have hint : ∀ g : Euc d → ℝ, Continuous g → (∃ B' : ℝ, ∀ x, |g x| ≤ B') → Integrable g ν := by
    rintro g hc ⟨B', hB'⟩
    exact (MemLp.of_bound hc.aestronglyMeasurable B'
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB' x)).integrable
        one_le_two
  have hmem0 : ∀ g : Euc d → ℝ, Continuous g → (∃ B' : ℝ, ∀ x, |g x| ≤ B') →
      MemL2Zero ν (HRS.Whole.projMean ν g) := by
    rintro g hc ⟨B', hB'⟩
    exact (u11_projMean_bound ν hc hB').1
  -- the centered orbit as a synthesized diagonal evolution
  have hz0 : ∀ α : MultiIndex d, ∃ z0 : SeqL2, ‖z0‖ ^ 2 ≤ B α ∧
      ∀ l, SeqL2.coord z0 l = u11Coef d β ρ e m α l := by
    intro α
    have hmemℓ : Memℓp (fun l => u11Coef d β ρ e m α l) 2 :=
      memℓp_two_iff.2 (summable_of_sum_le (fun l => sq_nonneg _) (fun T => hBes α T))
    refine ⟨SeqL2.ofSeq (fun l => u11Coef d β ρ e m α l), ?_, fun l => u11_coord_ofSeq hmemℓ l⟩
    have e1 : ∑' l, SeqL2.coord (SeqL2.ofSeq (fun l => u11Coef d β ρ e m α l)) l ^ 2 =
        ∑' l, u11Coef d β ρ e m α l ^ 2 := tsum_congr fun l => by rw [u11_coord_ofSeq hmemℓ l]
    rw [← u11_norm_sq, e1]
    exact Real.tsum_le_of_sum_le (fun l => sq_nonneg _) (hBes α)
  have hsemi : ∀ (z0 : SeqL2) (t : ℝ), 0 ≤ t → ∀ l,
      SeqL2.coord (semiDiag om t z0) l = Real.exp (-t * om l) * SeqL2.coord z0 l := by
    intro z0 t ht l
    unfold semiDiag
    exact u11_coord_ofSeq (u11_diag_memℓp om hdata.pos ht z0) l
  have hrepr : ∀ (α : MultiIndex d) (z0 : SeqL2),
      (∀ l, SeqL2.coord z0 l = u11Coef d β ρ e m α l) → ∀ t : ℝ, 0 ≤ t →
      (fun x => S (semiDiag om t z0) x) =ᵐ[ν]
        HRS.Whole.projMean ν (s88Orbit (critCoeff d a β ρ) m t α) := by
    intro α z0 hz t ht
    obtain ⟨hcont, B', hB'⟩ := horb α t ht
    have hF := hmem0 _ hcont ⟨B', hB'⟩
    obtain ⟨z, hzc, -, hSz⟩ := hSrec _ hF
    have hzeq : z = semiDiag om t z0 := by
      refine s88_seq_ext _ _ fun l => ?_
      rw [hzc l, hsemi z0 t ht l, hz l, ← hcoef α t ht l]
    rw [← hzeq]
    exact hSz
  have hSsq : ∀ w : SeqL2, ‖S w‖ ^ 2 ≤ K * ‖w‖ ^ 2 := by
    intro w
    calc ‖S w‖ ^ 2 ≤ (Real.sqrt K * ‖w‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          exact (S.le_opNorm w).trans (mul_le_mul_of_nonneg_right hSn (norm_nonneg _))
      _ = K * ‖w‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hK0]
  refine ⟨fun α u hu => ?_, fun α u s t hu hs ht => ?_⟩
  · -- base
    have hu0 : 0 ≤ u := by linarith
    obtain ⟨z0, hzB, hzc⟩ := hz0 α
    obtain ⟨hcont, B', hB'⟩ := horb α u hu0
    refine ⟨(hmem0 _ hcont ⟨B', hB'⟩).1, ?_⟩
    have hae := hrepr α z0 hzc u hu0
    have hI := Q34.integral_sq_eq (ν := ν) hae.symm
    rw [hI]
    obtain ⟨v, -, hv2⟩ := hDder z0
    have h1 := hv2 u hu
    have h2 : ‖semiDiag om u z0‖ ^ 2 ≤ D * Real.exp (-om 0 * u) * B α := by
      have : ‖semiDiag om u z0‖ ^ 2 ≤ D * Real.exp (-om 0 * u) * ‖z0‖ ^ 2 := by
        nlinarith [sq_nonneg ‖v u‖]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_left hzB (by positivity)
    calc ‖S (semiDiag om u z0)‖ ^ 2 ≤ K * ‖semiDiag om u z0‖ ^ 2 := hSsq _
      _ ≤ K * (D * Real.exp (-om 0 * u) * B α) := mul_le_mul_of_nonneg_left h2 hK0
      _ = K * D * B α * Real.exp (-2 * (om 0 / 2) * u) := by
          rw [show -2 * (om 0 / 2) * u = -om 0 * u by ring]; ring
  · -- increment
    have hu0 : 0 ≤ u := by linarith
    have hus : 0 ≤ u + s := by linarith
    have hut : 0 ≤ u + t := by linarith
    obtain ⟨z0, hzB, hzc⟩ := hz0 α
    obtain ⟨hc1, B1, hB1⟩ := horb α (u + s) hus
    obtain ⟨hc2, B2, hB2⟩ := horb α (u + t) hut
    have hcg : Continuous (fun x => s88Orbit (critCoeff d a β ρ) m (u + s) α x -
        s88Orbit (critCoeff d a β ρ) m (u + t) α x) := hc1.sub hc2
    have hbg : ∃ B' : ℝ, ∀ x, |s88Orbit (critCoeff d a β ρ) m (u + s) α x -
        s88Orbit (critCoeff d a β ρ) m (u + t) α x| ≤ B' :=
      ⟨B1 + B2, fun x => (abs_sub _ _).trans (add_le_add (hB1 x) (hB2 x))⟩
    refine ⟨(hmem0 _ hcg hbg).1, ?_⟩
    -- the difference is the synthesis of the difference
    have hI1 := hint _ hc1 ⟨B1, hB1⟩
    have hI2 := hint _ hc2 ⟨B2, hB2⟩
    have hpm : ∀ x, HRS.Whole.projMean ν (fun y => s88Orbit (critCoeff d a β ρ) m (u + s) α y -
        s88Orbit (critCoeff d a β ρ) m (u + t) α y) x =
        HRS.Whole.projMean ν (s88Orbit (critCoeff d a β ρ) m (u + s) α) x -
          HRS.Whole.projMean ν (s88Orbit (critCoeff d a β ρ) m (u + t) α) x := by
      intro x
      unfold HRS.Whole.projMean HRS.Whole.pair
      rw [integral_sub hI1 hI2]
      ring
    have hae : (fun x => S (semiDiag om (u + s) z0 - semiDiag om (u + t) z0) x) =ᵐ[ν]
        HRS.Whole.projMean ν (fun y => s88Orbit (critCoeff d a β ρ) m (u + s) α y -
          s88Orbit (critCoeff d a β ρ) m (u + t) α y) := by
      filter_upwards [hrepr α z0 hzc (u + s) hus, hrepr α z0 hzc (u + t) hut,
        Lp.coeFn_sub (S (semiDiag om (u + s) z0)) (S (semiDiag om (u + t) z0))] with x h1 h2 h3
      rw [hpm x, ← h1, ← h2, map_sub]
      exact h3
    have hI := Q34.integral_sq_eq (ν := ν) hae.symm
    rw [hI]
    -- mean value inequality for the diagonal evolution
    obtain ⟨v, hv1, hv2⟩ := hDder z0
    set M : ℝ := Real.sqrt (D * Real.exp (-om 0 * u) * ‖z0‖ ^ 2) with hM
    have hvM : ∀ r ∈ Set.Ici u, ‖v r‖ ≤ M := by
      intro r hr
      have hr' : u ≤ r := hr
      have h1 := hv2 r (hu.trans hr')
      have hsq : ‖v r‖ ^ 2 ≤ D * Real.exp (-om 0 * u) * ‖z0‖ ^ 2 := by
        have h3 : ‖v r‖ ^ 2 ≤ D * Real.exp (-om 0 * r) * ‖z0‖ ^ 2 := by
          nlinarith [sq_nonneg ‖semiDiag om r z0‖]
        refine h3.trans ?_
        have : Real.exp (-om 0 * r) ≤ Real.exp (-om 0 * u) :=
          Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hD0) (sq_nonneg _)
      calc ‖v r‖ = Real.sqrt (‖v r‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ M := Real.sqrt_le_sqrt hsq
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r : ℝ => semiDiag om r z0) (f' := v) (s := Set.Ici u)
      (fun r hr => (hv1 r (lt_of_lt_of_le one_pos (hu.trans hr))).1.hasDerivWithinAt) hvM
      (convex_Ici u) (x := u + t) (y := u + s) (by show u ≤ u + t; linarith)
      (by show u ≤ u + s; linarith)
    have hw : ‖semiDiag om (u + s) z0 - semiDiag om (u + t) z0‖ ^ 2 ≤
        D * Real.exp (-om 0 * u) * B α * (s - t) ^ 2 := by
      have h1 : ‖semiDiag om (u + s) z0 - semiDiag om (u + t) z0‖ ≤ M * |s - t| := by
        have := hmv
        rwa [Real.norm_eq_abs, show u + s - (u + t) = s - t by ring] at this
      have h2 : ‖semiDiag om (u + s) z0 - semiDiag om (u + t) z0‖ ^ 2 ≤ (M * |s - t|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      refine h2.trans ?_
      rw [mul_pow, sq_abs, hM, Real.sq_sqrt (by positivity)]
      have : D * Real.exp (-om 0 * u) * ‖z0‖ ^ 2 ≤ D * Real.exp (-om 0 * u) * B α :=
        mul_le_mul_of_nonneg_left hzB (by positivity)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    calc ‖S (semiDiag om (u + s) z0 - semiDiag om (u + t) z0)‖ ^ 2
        ≤ K * ‖semiDiag om (u + s) z0 - semiDiag om (u + t) z0‖ ^ 2 := hSsq _
      _ ≤ K * (D * Real.exp (-om 0 * u) * B α * (s - t) ^ 2) :=
          mul_le_mul_of_nonneg_left hw hK0
      _ = K * D * B α * Real.exp (-2 * (om 0 / 2) * u) * (s - t) ^ 2 := by
          rw [show -2 * (om 0 / 2) * u = -om 0 * u by ring]; ring

theorem s88_orbit_envelopes {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m) :
    ∃ (c : ℝ) (b : MultiIndex d → ℝ), 0 < c ∧ (∀ α, 0 ≤ b α) ∧ Summable b ∧
      ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ →
        S88OrbitRegular (critCoeff d a β ρ) m ∧
        S88OrbitEnvelope (critCoeff d a β ρ) (HRS.Whole.withDensityReal ρ) m c b := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  by_cases hex : ∃ ρ₀ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ₀
  · obtain ⟨ρ₀, h₀⟩ := hex
    obtain ⟨c, b, hc, hb0, hbs, henv⟩ := s88_envelope_single hd a β ha hβ m hm ρ₀ h₀
    refine ⟨c, b, hc, hb0, hbs, fun ρ hρ => ?_⟩
    have : ρ = ρ₀ :=
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans
        (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₀).symm
    subst this
    exact ⟨s88_regular_orbit hd a β ha hβ m hm ρ hρ, henv⟩
  · exact ⟨1, fun _ => 0, one_pos, fun _ => le_rfl, summable_zero,
      fun ρ hρ => absurd ⟨ρ, hρ⟩ hex⟩

end HRS.MS.S88Breakdown
