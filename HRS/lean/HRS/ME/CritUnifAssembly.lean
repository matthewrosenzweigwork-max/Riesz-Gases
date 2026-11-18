import HRS.ME.CritUnifDefs
import HRS.ME.Asm417E

/-!
# Chunk E, row 2.10 path clauses: proof of the uniform-in-`β` Proposition 4.17 (U2)

* `unif_single_j`: the proof of `HRS.ME.single_j_bound_proof` with the decay constants `(C_D, c_D)` and the mode constant `C_B1`
  taken from the hypotheses `hdec`, `hmode` (chosen before `β ∈ [βm,βp]`), and specialised at each `β`.
* `uniform417_of_unif`: the proof of `HRS.ME.integrated_forcing_type_proof` with the constant of the single-mode bound taken
  from `unif_single_j`, the flow given directly, and the sum over the lattice (`lintegral_tsum`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Crit

open HRS HRS.LZ HRS.Uniform HRS.Main
open HRS.ME

variable {d : ℕ}

/-- The uniform single-feature bound: `single_j_bound_proof` with the constants chosen before `β ∈ [βm, βp]`.  The statement is
written for a general `s` with `s = d/2` (`hcrit`), so that the body of `single_j_bound_proof` is used verbatim. -/
theorem unif_single_j (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (T : ℝ) (hT : 0 ≤ T)
    (hdec : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
        Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (9 * d + 82) *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
        ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (9 * d + 82) *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
          C * Lattice.jp j.1 ^ (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v))
    (hmode : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
        (hflow : IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X)
        (l : NonzeroLattice d) (Γ : ℝ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ)
        (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) (hγ' : ContinuousOn γ' (Set.Ici 0))
        (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
            ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
                forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P ≤
          ENNReal.ofReal (C * Γ ^ 2 * Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (m : ℝ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
        (hflow : IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X) (j : NonzeroLattice d),
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
            (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ P X m j (a + t) ω ^ 2) ∂P ≤
          ENNReal.ofReal (C * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_D, c_D, hCD, hcD, hdecU⟩ := hdec
  obtain ⟨C_B1, hC_B1, hmodeU⟩ := hmode c_D hcD
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (-((d : ℝ) + 2)) :=
    ⟨_, rfl⟩
  have hsumSig : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (-((d : ℝ) + 2))) :=
    asmD_summable_rpow (d := d) ((d : ℝ) + 2) (by linarith)
  refine ⟨C_B1 * C_D ^ 2 * Sg ^ 2, mul_nonneg (mul_nonneg hC_B1 (sq_nonneg _)) (sq_nonneg _), ?_⟩
  intro β hβI ρβ hρβ hρS hρpos
  have hβ : 0 < β := hβm.trans_le hβI.1
  have hdec := hdecU β hβI ρβ hρβ hρS hρpos
  intro m N hN Ω _ P _ X₀ W X a ha hflow j
  have hN0 : (0 : ℝ) < N := by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Lattice.jp j.1 ^ (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hE2 : E ^ 2 = Lattice.jp j.1 ^ (2 * (-m + ((9 * d + 82 + d + 3 : ℕ) : ℝ))) := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos j.1).le]
    congr 1
    push_cast
    ring
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = Real.sqrt (C_B1 / N) := ⟨_, rfl⟩
  have hc0nn : 0 ≤ c0 := by rw [hc0]; exact Real.sqrt_nonneg _
  have hc0sq : c0 ^ 2 = C_B1 / N := by
    rw [hc0, Real.sq_sqrt (div_nonneg hC_B1 hN0.le)]
  have hy : ∀ l : NonzeroLattice d, C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Lattice.jp l.1 ^ (8 * d + 80)
      = C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)) := by
    intro l
    have hx := Torus.jp_pos l.1
    rw [show (-((d : ℝ) + 2)) = -(((9 * d + 82 : ℕ) : ℝ) - ((8 * d + 80 : ℕ) : ℝ)) by push_cast; ring,
      asmD_rpow_neg_sub _ hx]
    ring
  have hXnn : ∀ l : NonzeroLattice d, 0 ≤ c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2))) := fun l =>
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) (Real.rpow_nonneg (Torus.jp_pos _).le _))
  have hSgnn : 0 ≤ Sg := by
    rw [hSg]
    exact tsum_nonneg fun l => Real.rpow_nonneg (Torus.jp_pos l.1).le _
  -- the Minkowski integrands `S_l(ω) = sup_t |J_l(a+t)(ω)|`
  obtain ⟨S, hS⟩ : ∃ S : NonzeroLattice d → Ω → ℝ≥0∞, ∀ l ω, S l ω = ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
    ⟨fun l ω => ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖,
      fun _ _ => rfl⟩
  have hSmeas : ∀ l, AEMeasurable (S l) P := by
    intro l
    have e : S l = fun ω => ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := funext (hS l)
    rw [e]
    refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    exact ((asmD_J_aemeas hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j l
      (a + t) hb0 hbH).norm).ennreal_ofReal
  -- per-mode bound
  have hperl : ∀ l : NonzeroLattice d, ∫⁻ ω, (S l ω) ^ 2 ∂P ≤
      ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2) := by
    intro l
    have hψ : Torus.IsSmooth (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x) :=
      asmB_sm_const_mul (HRS.FieldSingAux.isSmooth_realMode j) _
    have hreg := fourier_coeff_regular_proof hd1 s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos _ hψ l
    have hγ : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt (asmD_gam s hs0 hsd V β hβ ρβ m j l)
        (asmD_gam' s hs0 hsd V β hβ ρβ m j l x) (Set.Ici 0) x :=
      fun x hx => hreg.2.1 x hx
    have hγ' : ContinuousOn (asmD_gam' s hs0 hsd V β hβ ρβ m j l) (Set.Ici 0) := hreg.2.2
    have hbdl : ∀ v, 0 ≤ v → |asmD_gam s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) ∧
        |asmD_gam' s hs0 hsd V β hβ ρβ m j l v| ≤
          C_D * E / Lattice.jp l.1 ^ (9 * d + 82) * Real.exp (-c_D * v) := by
      intro v hv
      have hdj := hdec m j v hv
      rw [← hE] at hdj
      exact asmD_coef_bound (d := d) (9 * d + 82) C_D c_D E hE0.le hCD.le
        (fun k => asmD_gam s hs0 hsd V β hβ ρβ m j k v) (fun k => asmD_gam' s hs0 hsd V β hβ ρβ m j k v)
        v hdj.1 hdj.2 l
    have hΓnn : 0 ≤ C_D * E / Lattice.jp l.1 ^ (9 * d + 82) :=
      div_nonneg (mul_nonneg hCD.le hE0.le) (pow_nonneg (Torus.jp_pos _).le _)
    have hmodel := hmodeU β hβI ρβ hρβ hρS hρpos hN P X₀ W X a ha hflow l (C_D * E / Lattice.jp l.1 ^ (9 * d + 82)) hΓnn
      (asmD_gam s hs0 hsd V β hβ ρβ m j l) (asmD_gam' s hs0 hsd V β hβ ρβ m j l) hγ hγ'
      (fun v hv => ⟨(hbdl v hv).1, (hbdl v hv).2⟩)
    have hpt : ∀ ω, (S l ω) ^ 2 ≤ ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal ((asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω) ^ 2) := by
      intro ω
      rw [hS l ω]
      refine (asmD_biSup_sq _ _).trans (iSup₂_mono fun t _ => le_of_eq ?_)
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    refine (lintegral_mono hpt).trans (hmodel.trans (le_of_eq ?_))
    congr 1
    rw [mul_pow, hc0sq, ← hy l]
    ring
  -- the `1/2`-power of each mode
  have hterm : ∀ l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
    intro l
    calc (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hperl l) (by norm_num)
      _ = ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (hXnn l)]
  have hsumX : Summable (fun l : NonzeroLattice d =>
      c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
    (hsumSig.mul_left (C_D * E)).mul_left c0
  have hsumterm : ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
    calc ∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ ∑' l : NonzeroLattice d, ENNReal.ofReal (c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' l : NonzeroLattice d, c0 * (C_D * E * Lattice.jp l.1 ^ (-((d : ℝ) + 2)))) :=
          (ENNReal.ofReal_tsum_of_nonneg hXnn hsumX).symm
      _ = ENNReal.ofReal (c0 * (C_D * E * Sg)) := by
          rw [tsum_mul_left, tsum_mul_left, hSg]
  -- the good event: the pointwise bound of the supremum over `t`
  have hgoodpw := asmD_pathwise hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P X₀ W X (a + T) hflow j
  have hpt' : ∀ᵐ ω ∂P, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
      (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2)) ≤
      (∑' l : NonzeroLattice d, S l ω) ^ 2 := by
    filter_upwards [hgoodpw] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hmem := ht
    obtain ⟨⟨ht0, htT⟩, -⟩ := hmem
    have hb0 : 0 ≤ a + t := by linarith
    have hbH : a + t ≤ a + T := by linarith
    obtain ⟨hI, hsum⟩ := hω (a + t) hb0 hbH
    set I := integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω with hIdef
    have h1 : ENNReal.ofReal (I ^ 2) = (ENNReal.ofReal ‖I‖) ^ 2 := by
      rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    have h2 : ENNReal.ofReal ‖I‖ ≤ ∑' l : NonzeroLattice d, S l ω := by
      calc ENNReal.ofReal ‖I‖
          = ENNReal.ofReal ‖∑' l : NonzeroLattice d, asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ := by
            rw [hI.tsum_eq]
        _ ≤ ENNReal.ofReal (∑' l : NonzeroLattice d, ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) :=
            ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
        _ = ∑' l : NonzeroLattice d, ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun l => norm_nonneg _) hsum
        _ ≤ ∑' l : NonzeroLattice d, S l ω := by
            refine ENNReal.tsum_le_tsum fun l => ?_
            rw [hS l ω]
            exact le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
              ENNReal.ofReal ‖asmD_J s hs0 hsd V β hβ ρβ m j l X (a + t) ω‖) t ht
    rw [h1]
    exact pow_le_pow_left₀ zero_le h2 2
  have hreal : (c0 * (C_D * E * Sg)) ^ 2 =
      C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N := by
    rw [← hE2, mul_pow, hc0sq]
    ring
  have hGsnn : 0 ≤ c0 * (C_D * E * Sg) :=
    mul_nonneg hc0nn (mul_nonneg (mul_nonneg hCD.le hE0.le) hSgnn)
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m j (a + t) ω ^ 2) ∂P
      ≤ ∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P := lintegral_mono_ae hpt'
    _ = ((∫⁻ ω, (∑' l : NonzeroLattice d, S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          (asmD_rpow_half_sq _).symm
    _ ≤ (∑' l : NonzeroLattice d, (∫⁻ ω, (S l ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ zero_le (lintegral_sq_tsum_le P S hSmeas) 2
    _ ≤ (ENNReal.ofReal (c0 * (C_D * E * Sg))) ^ 2 := pow_le_pow_left₀ (zero_le) hsumterm 2
    _ = ENNReal.ofReal ((c0 * (C_D * E * Sg)) ^ 2) := (ENNReal.ofReal_pow hGsnn 2).symm
    _ ≤ ENNReal.ofReal (C_B1 * C_D ^ 2 * Sg ^ 2 * Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
          ENNReal.ofReal_le_ofReal (le_of_eq hreal)

/-- U2.  `UnifDecay` and `UnifModeForcing` (for every `c > 0`) give `Uniform417`: the proof of
`HRS.ME.integrated_forcing_type_proof` with the single-mode constant `C₂` taken from `unif_single_j`. -/
theorem uniform417_of_unif (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T)
    (hdec : UnifDecay d hs0 hsd V βm βp hβm)
    (hmode : ∀ c : ℝ, 0 < c → UnifModeForcing d hs0 hsd V βm βp hβm c T) :
    Uniform417 d hs0 hsd V βm βp hβm m T := by
  classical
  obtain ⟨C₂, hC₂, hsingle⟩ := unif_single_j hd hs0 hsd rfl V hV βm βp hβm T hT.le hdec hmode
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the exponent `2 * (-m + p + d + 3)` is `-q` with `q = 2 (m - (p + d + 3)) > d`
  have hqd : (d : ℝ) < 2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)) := by
    push_cast
    linarith
  have hexp : ∀ j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)))
        = Lattice.jp j.1 ^ (-(2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)))) := fun j => by
    congr 1
    ring
  have hs1 : Summable fun j : NonzeroLattice d =>
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    (asmD_summable_rpow _ hqd).congr fun j => (hexp j).symm
  have hnn : ∀ j : NonzeroLattice d,
      0 ≤ Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    fun j => Real.rpow_nonneg (Torus.jp_pos j.1).le _
  obtain ⟨Ssum, hSsum⟩ : ∃ Ssum : ℝ, Ssum = ∑' j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hSnn : 0 ≤ Ssum := by
    rw [hSsum]
    exact tsum_nonneg hnn
  refine ⟨Real.sqrt (C₂ * Ssum), Real.sqrt_nonneg _, ?_⟩
  intro β hβ ρβ hρβ hρS hρpos N hN Ω _ P _ X₀ W X a ha hflow
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hCsq : Real.sqrt (C₂ * Ssum) ^ 2 = C₂ * Ssum := Real.sq_sqrt (mul_nonneg hC₂ hSnn)
  have hA : ∀ (k : NonzeroLattice d) (b : ℝ), 0 ≤ b → b ≤ a + T →
      AEMeasurable (fun ω => integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k b ω) P :=
    fun k b hb hbH => integratedCenteredForcing_aemeasurable hd hs0 hsd rfl V hV β hβ0 ρβ hρβ hρS hρpos m hN P
      X₀ W X (a + T) hflow k b hb hbH
  have hmeas : ∀ k : NonzeroLattice d, AEMeasurable (fun ω => ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2)) P := by
    intro k
    refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
    obtain ⟨⟨ht0, htT⟩, -⟩ := ht
    exact ((hA k (a + t) (by linarith) (by linarith)).pow_const 2).ennreal_ofReal
  have hpt : ∀ ω, (⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2))
        ≤ ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    exact ENNReal.tsum_le_tsum fun k => le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2)) t ht
  have hnnk : ∀ k : NonzeroLattice d,
      0 ≤ C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
    fun k => div_nonneg (mul_nonneg hC₂ (hnn k)) (Nat.cast_nonneg N)
  have hsumc : Summable fun k : NonzeroLattice d =>
      C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
    (hs1.mul_left C₂).div_const (N : ℝ)
  have hfin : ENNReal.ofReal (Real.sqrt (C₂ * Ssum) ^ 2 / N) = ∑' k : NonzeroLattice d,
      ENNReal.ofReal (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnnk hsumc, hCsq, tsum_div_const, tsum_mul_left, ← hSsum]
  rw [hfin]
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
        ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P
      ≤ ∫⁻ ω, ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P :=
        lintegral_mono fun ω => hpt ω
    _ = ∑' k : NonzeroLattice d, ∫⁻ ω, ⨆ t ∈ ratTimes 0 T,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + t) ω ^ 2) ∂P :=
        lintegral_tsum fun k => hmeas k
    _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal
          (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
        ENNReal.tsum_le_tsum fun k => hsingle β hβ ρβ hρβ hρS hρpos m hN P X₀ W X a ha hflow k

end HRS.ME.Crit

end
