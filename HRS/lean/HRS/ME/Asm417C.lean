import HRS.ME.Asm417A
import HRS.ME.Asm417B
import HRS.ME.Fourier417B
import HRS.ME.Stat417

/-!
# Chunk E, row 4.17: assembly packet C (proof of B5, `forcing_intervalIntegrable`)

Proofs of `forcing_intervalIntegrable_proof` (B5) and of the auxiliary lemma `ae_lintegral_envelope_finite_proof`
(almost sure finiteness of `∫_0^H B(X^r) dr`).  The statements of `HRS/ME/Spec417Asm.lean` are copied verbatim;
`HRS/ME/Spec417Asm.lean` is not imported.  Helpers carry the prefix `asmC_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- Measurability of the forcing statistic `X ↦ forcingStat f X` (for every test `f`). -/
theorem asmC_fs_meas {s : ℝ} (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    (f : Torus d → ℝ) : Measurable (forcingStat s V β ρβ f : Config d N → ℝ) := by
  have hTm : Measurable (Function.uncurry (hTransport d s f)) :=
    HRS.Parx.PXFID.measurable_hTransport hsd f
  haveI : SFinite (withDensityReal ρβ) := by unfold withDensityReal; infer_instance
  have hQm := me_flow_quadStat_meas (N := N) (h := hTransport d s f) hTm (ν := withDensityReal ρβ)
  unfold forcingStat centeredUnder
  exact measurable_const.mul (hQm.sub measurable_const)

/-- A real estimate: the product of a coefficient and a bounded value is dominated by the weighted sum. -/
theorem asmC_norm_bound {c g fs jp C₁ W : ℝ} (hC₁ : 0 ≤ C₁) (hW : 0 ≤ W)
    (h : |fs| ≤ C₁ * jp ^ 2 * W) :
    ‖c * fs‖ ≤ C₁ * W * (jp ^ 2 * (|c| + |g|)) := by
  rw [Real.norm_eq_abs, abs_mul]
  have h2 : |c| * |fs| ≤ |c| * (C₁ * jp ^ 2 * W) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h3 : 0 ≤ C₁ * W * (jp ^ 2 * |g|) :=
    mul_nonneg (mul_nonneg hC₁ hW) (mul_nonneg (sq_nonneg _) (abs_nonneg _))
  have e : C₁ * W * (jp ^ 2 * (|c| + |g|)) = |c| * (C₁ * jp ^ 2 * W) + C₁ * W * (jp ^ 2 * |g|) := by
    ring
  rw [e]
  linarith

/-- Almost surely, `∫_0^H B(X^r) dr < ∞` (Tonelli and stationarity of the one-time marginals). -/
theorem ae_lintegral_envelope_finite_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (B : Config d N → ℝ) (hBm : Measurable B) (hB0 : ∀ X, 0 ≤ B X)
    (hB : MemLp B 2 (canonicalGibbs (periodicRiesz d s) V N β)) :
    ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (B (X r.toNNReal ω)) < ∞ := by
  classical
  by_cases hH : 0 ≤ H
  swap
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Set.Icc_eq_empty hH]
    simp
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = canonicalGibbs (periodicRiesz d s) V N β :=
    HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  have hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.cont
    · omega
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.adapted
    · omega
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hcont_bad : ∀ ω, ω ∉ Nn → ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    intro ω hω
    by_contra hne
    exact hω (hNsub hne)
  have hNae : ∀ᵐ ω ∂P, ω ∉ Nn := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => not_not.mp hω) hN0
  -- a jointly measurable modification of the path, equal to `X` off `Nn`
  obtain ⟨Xs, hXs_good, hXs_meas⟩ : ∃ Xs : ℝ → Ω → Config d N,
      (∀ ω, ω ∉ Nn → ∀ r : ℝ, Xs r ω = X r.toNNReal ω) ∧
        Measurable (fun p : ℝ × Ω => Xs p.1 p.2) := by
    refine ⟨fun r ω => if ω ∈ Nn then X 0 ω else X r.toNNReal ω, fun ω hω r => if_neg hω, ?_⟩
    refine measurable_uncurry_of_continuous_of_measurable (u := fun (r : ℝ) (ω : Ω) =>
      if ω ∈ Nn then X 0 ω else X r.toNNReal ω) (fun ω => ?_) (fun r => ?_)
    · by_cases hω : ω ∈ Nn
      · simp only [if_pos hω]
        exact continuous_const
      · simp only [if_neg hω]
        exact continuous_pi fun i => (hcont_bad ω hω i).comp continuous_real_toNNReal
    · exact Measurable.ite hNm (hadapt 0) (hadapt r.toNNReal)
  have hXsw : Measurable (fun p : Ω × ℝ => Xs p.2 p.1) := hXs_meas.comp measurable_swap
  have hBXs : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (B (Xs p.2 p.1))) :=
    (hBm.comp hXsw).ennreal_ofReal
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ≥0∞,
      M = ∫⁻ Y, ENNReal.ofReal (B Y) ∂(canonicalGibbs (periodicRiesz d s) V N β) := ⟨_, rfl⟩
  -- one-time identity on `[0, H]`
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) H, ∫⁻ ω, ENNReal.ofReal (B (Xs r ω)) ∂P = M := by
    intro r hr
    have hrH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by
      rw [Real.coe_toNNReal r hr.1]
      exact hr.2
    rw [hMdef]
    calc ∫⁻ ω, ENNReal.ofReal (B (Xs r ω)) ∂P
        = ∫⁻ ω, ENNReal.ofReal (B (X r.toNNReal ω)) ∂P :=
          lintegral_congr_ae (hNae.mono fun ω hω => by simp only [hXs_good ω hω r])
      _ = ∫⁻ Y, ENNReal.ofReal (B Y) ∂(P.map (X r.toNNReal)) :=
          (lintegral_map hBm.ennreal_ofReal (hadapt _)).symm
      _ = ∫⁻ Y, ENNReal.ofReal (B Y) ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
          rw [hstat r.toNNReal hrH]
  haveI : IsFiniteMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simpa using hH)]
    infer_instance
  have hMfin : M < ∞ := by
    have h := (hB.integrable one_le_two).2
    have heq : ∫⁻ Y, ENNReal.ofReal (B Y) ∂(canonicalGibbs (periodicRiesz d s) V N β) =
        ∫⁻ Y, ‖B Y‖ₑ ∂(canonicalGibbs (periodicRiesz d s) V N β) :=
      lintegral_congr fun Y => (Real.enorm_eq_ofReal (hB0 Y)).symm
    rw [hMdef, heq]
    exact h
  have hFmeas : Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (B (Xs r ω))) :=
    hBXs.lintegral_prod_right'
  -- Tonelli
  have hTon : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (B (Xs r ω))) ∂P
      = ∫⁻ r in Set.Icc (0 : ℝ) H, (∫⁻ ω, ENNReal.ofReal (B (Xs r ω)) ∂P) :=
    lintegral_lintegral_swap (f := fun ω r => ENNReal.ofReal (B (Xs r ω)))
      (μ := P) (ν := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) H)) hBXs.aemeasurable
  have hTonfin : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (B (Xs r ω))) ∂P ≠ ∞ := by
    rw [hTon, setLIntegral_congr_fun measurableSet_Icc (fun r hr => hinner r hr), setLIntegral_const]
    exact ENNReal.mul_ne_top hMfin.ne measure_Icc_lt_top.ne
  have hfin_ae : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) H, ENNReal.ofReal (B (Xs r ω)) < ∞ :=
    ae_lt_top hFmeas hTonfin
  filter_upwards [hfin_ae, hNae] with ω hω1 hω2
  simpa only [hXs_good ω hω2] using hω1

/-- B5.  Conjunct 2 of `integrated_forcing`: almost sure interval integrability of the time integrands, simultaneously
for all `t ∈ [0,T]` and all features.  Proof: for every `b ≤ a + T`, `R(U_{b-r} φ_k)(X^r) = ∑_l γ_l(b-r) R_{e_l}(X^r)`
(A1, A2, `fourier_coeff_decay`) is measurable in `r` and bounded by `C e^{-c(b-r)} (B(X^r) + C₀)`, and
`∫_0^{a+T} B(X^r) dr < ∞` almost surely because `E ∫_0^{a+T} B(X^r) dr = (a+T) ∫ B dμ`. -/
theorem forcing_intervalIntegrable_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r =>
        centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (a + t - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)
        volume 0 (a + t) := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hd1 : 1 ≤ d := by omega
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) (a + T) X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  obtain ⟨B, hBm, hB0, hBL, C₀, C₁, hC₀, hC₁, -, hbd⟩ :=
    forcingStat_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  obtain ⟨C_D, c_D, hCD, hcD, hdec⟩ :=
    fourier_coeff_decay_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos 2
  -- the pointwise statement, for a path with the good properties
  have pt : ∀ ω : Ω, (∀ i, Continuous fun t : ℝ≥0 => X t ω i) →
      (∀ t : ℝ≥0, (t : ℝ) ≤ a + T → X t ω ∉ collisionSet d N) →
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (B (X r.toNNReal ω)) < ∞ →
      ∀ b : ℝ, 0 ≤ b → b ≤ a + T → ∀ k : NonzeroLattice d,
        IntervalIntegrable (fun r =>
          centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
            (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
              (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)
          volume 0 b := by
    intro ω hc hcl hfin b hb0 hbH k
    have hpath : Continuous fun r : ℝ => X r.toNNReal ω :=
      continuous_pi fun i => (hc i).comp continuous_real_toNNReal
    have hnc : ∀ r : ℝ, 0 ≤ r → r ≤ a + T → X r.toNNReal ω ∉ collisionSet d N := by
      intro r hr0 hrH
      apply hcl
      rw [Real.coe_toNNReal r hr0]
      exact hrH
    have hψ : Torus.IsSmooth (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x) :=
      asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode k) _
    have hsm : ∀ v : ℝ, 0 ≤ v →
        Torus.IsSmooth (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) :=
      fun v hv => (fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ k).1 v hv
    have hcoefc : ∀ (l : NonzeroLattice d) (v : ℝ), 0 ≤ v →
        ContinuousWithinAt (fun u => Torus.funRealCoeff (PDE.equilibriumSemigroup
          (PDE.mfData d s hs0 hsd V β hβ) ρβ u (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l)
          (Set.Ici 0) v :=
      fun l v hv =>
        ((fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ l).2.1 v hv).continuousWithinAt
    have hcoefCont : ∀ l : NonzeroLattice d, ContinuousOn (fun r : ℝ => Torus.funRealCoeff
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l) (Set.Icc 0 b) := by
      intro l r hr
      exact (hcoefc l (b - r) (by linarith [hr.2])).comp (f := fun r : ℝ => b - r)
        (continuous_const.sub continuous_id).continuousWithinAt
        (fun x hx => by simp only [Set.mem_Ici]; linarith [hx.2])
    have hfm : ∀ l : NonzeroLattice d, Measurable
        (fun r : ℝ => forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) :=
      fun l => (asmC_fs_meas (N := N) hsd V β ρβ (Torus.realMode l)).comp hpath.measurable
    have hterm : ∀ l : NonzeroLattice d, AEStronglyMeasurable (fun r : ℝ =>
        Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)) := by
      intro l
      have h1 : AEStronglyMeasurable (fun r : ℝ => Torus.funRealCoeff
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) b)) :=
        (hcoefCont l).aestronglyMeasurable measurableSet_Icc
      exact (h1.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)).mul
        (hfm l).aestronglyMeasurable
    have hfS : ∀ S : Finset (NonzeroLattice d), AEStronglyMeasurable (fun r : ℝ =>
        ∑ l ∈ S, Torus.funRealCoeff
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)) := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simp only [Finset.sum_empty]
        exact aestronglyMeasurable_const
      · intro l0 S hl0 ih
        simp only [Finset.sum_insert hl0]
        exact (hterm l0).add ih
    -- the pointwise identity `forcing = forcingStat` (A1) and the mode expansion (A2)
    have hF : ∀ r ∈ Set.Icc (0 : ℝ) b,
        centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω =
        forcingStat s V β ρβ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) (X r.toNNReal ω) := by
      intro r hr
      exact forcing_eq_forcingStat_proof hd hs0 hsd V hV β hβ ρβ hN P X₀ W X (a + T) hflow _
        (hsm (b - r) (by linarith [hr.2])) r hr.1 (by linarith [hr.2, hbH]) ω
    have hHS : ∀ r ∈ Set.Icc (0 : ℝ) b, HasSum (fun l : NonzeroLattice d =>
        Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω))
        (forcingStat s V β ρβ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) (X r.toNNReal ω)) := by
      intro r hr
      have hv : 0 ≤ b - r := by linarith [hr.2]
      have hsumd := (hdec m k (b - r) hv).1
      have hsumsub : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ 2 *
          |Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l|) :=
        Summable.of_nonneg_of_le (fun l => by positivity)
          (fun l => mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) (sq_nonneg _)) hsumd
      exact forcingStat_hasSum_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN _
        (hsm (b - r) hv) hsumsub (X r.toNNReal ω) (hnc r hr.1 (by linarith [hr.2, hbH]))
    have hlim : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)),
        Tendsto (fun S : Finset (NonzeroLattice d) => ∑ l ∈ S, Torus.funRealCoeff
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) l *
            forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) atTop
          (𝓝 (centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
            (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
              (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_)
      rw [hF r ⟨hr.1.le, by linarith [hr.2, hbH]⟩]
      exact hHS r ⟨hr.1.le, by linarith [hr.2]⟩
    have hmeasF : AEStronglyMeasurable (fun r : ℝ => centeredCommutatorForcing d s P
        (fun _ => withDensityReal ρβ) X
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
          (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)) :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun S => hfS S) hlim
    -- the domination
    have hdom : ∀ r ∈ Set.Icc (0 : ℝ) b, ‖centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (b - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω‖ ≤
        C₁ * (C_D * Lattice.jp k.1 ^ (-m + ((2 + d + 3 : ℕ) : ℝ))) * (B (X r.toNNReal ω) + C₀) := by
      intro r hr
      have hv : 0 ≤ b - r := by linarith [hr.2]
      have hrH : r ≤ a + T := by linarith [hr.2, hbH]
      have hW : 0 ≤ B (X r.toNNReal ω) + C₀ := add_nonneg (hB0 _) hC₀
      obtain ⟨hsumd, hle⟩ := hdec m k (b - r) hv
      have hJ : 0 ≤ C_D * Lattice.jp k.1 ^ (-m + ((2 + d + 3 : ℕ) : ℝ)) :=
        mul_nonneg hCD.le (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      have hexp : Real.exp (-c_D * (b - r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [mul_nonneg hcD.le hv])
      have hsum_le := hle.trans (mul_le_of_le_one_right hJ hexp)
      have hG := hsumd.hasSum.mul_left (C₁ * (B (X r.toNNReal ω) + C₀))
      have hnorm := HasSum.norm_le_of_bounded (hHS r hr) hG
        (fun l => asmC_norm_bound hC₁ hW (hbd l (X r.toNNReal ω) (hnc r hr.1 hrH)))
      rw [hF r hr]
      exact hnorm.trans ((mul_le_mul_of_nonneg_left hsum_le (mul_nonneg hC₁ hW)).trans
        (le_of_eq (by ring)))
    -- integrability of the envelope `B(X^r) + C₀` on `(0, b]`
    have hBint : Integrable (fun r : ℝ => B (X r.toNNReal ω))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)) := by
      refine ⟨(hBm.comp hpath.measurable).aestronglyMeasurable, ?_⟩
      have e : ∀ r : ℝ, ‖B (X r.toNNReal ω)‖ₑ = ENNReal.ofReal (B (X r.toNNReal ω)) :=
        fun r => Real.enorm_eq_ofReal (hB0 _)
      show ∫⁻ r in Set.Ioc (0 : ℝ) b, ‖B (X r.toNNReal ω)‖ₑ < ∞
      simp only [e]
      exact lt_of_le_of_lt (lintegral_mono_set (Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc le_rfl hbH))) hfin
    have hg : Integrable (fun r : ℝ => C₁ * (C_D * Lattice.jp k.1 ^ (-m + ((2 + d + 3 : ℕ) : ℝ))) *
        (B (X r.toNNReal ω) + C₀)) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) b)) :=
      (hBint.add (integrable_const C₀)).const_mul _
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).2 ?_
    exact Integrable.mono' hg hmeasF
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => hdom r ⟨hr.1.le, hr.2⟩))
  have hgood := ae_lintegral_envelope_finite_proof hd hs0 hsd V hV β hβ hN P X₀ W X (a + T) hflow B hBm hB0 hBL
  filter_upwards [hgood, hsol.cont, hsol.no_collision] with ω hfin hc hcl
  intro t ht k
  exact pt ω hc hcl hfin (a + t) (by linarith [ht.1]) (by linarith [ht.2]) k

end HRS.ME

end
