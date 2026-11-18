import HRS.ME.Defs417
import HRS.ME.Mode417
import HRS.ME.DynkinClosed417
import HRS.ME.Mode417W
import HRS.ME.Fourier417A
import HRS.MD.EQLZFinal

/-!
# Row 4.17, packet B1: proof of `mode_forcing_bound`

Statement copied verbatim from `HRS/ME/Spec417Asm.lean`.  Helper lemmas carry the prefix `mode417B`.

Route: the mode package (`mode_package_proof`) supplies `F, G, E` with the pointwise identity off collisions;
`dynkin_closedGenerator_proof` gives the a.s. integrability, continuity and maximal inequality of the
martingale part; the scalar Lyons-Zheng bound (`lz_scalar_proof`, the family version specialised to
`F_0 = F`, `F_j = 0`) gives the sup bound for `F`; `mode_window_bound_proof` then bounds the window integral.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- Scalar Lyons-Zheng bound, replayed from the family version
`HRS.MD.EQLZFinal.lyonsZheng_maximal_family_proof` (the proof of `HRS.LZ.lyonsZheng_maximal`, with
`F_0 = F` and `F_j = 0` for `j ≥ 1`). -/
theorem lz_scalar_proof :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T a : ℝ), 0 ≤ T → 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ F : Config d N → ℝ, IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) F →
          ∫⁻ ω, ⨆ t ∈ ratTimes a T,
              ENNReal.ofReal
                ((F (X t.toNNReal ω) - ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2) ∂P ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (∫ Y, (F Y -
                  ∫ Y', F Y' ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)) +
                ENNReal.ofReal (β⁻¹ * T) *
                  ENNReal.ofReal (∫ Y, configGradSq F Y
                    ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  obtain ⟨C, hC, h⟩ := HRS.MD.EQLZFinal.lyonsZheng_maximal_family_proof
  refine ⟨C, hC, fun d N hd hN s hs0 hsd V hV β hβ T a hT ha Ω _ P _ X₀ W X hX F hF => ?_⟩
  classical
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hz : IsLZTest μ (fun _ : Config d N => (0 : ℝ)) := by
    refine ⟨measurable_const, MemLp.zero, ?_, ?_⟩
    · exact contDiffOn_const
    · rw [configGradSq_zero]; exact integrable_zero _ _ _
  set F' : ℕ → Config d N → ℝ := fun j => if j = 0 then F else fun _ => (0 : ℝ) with hF'
  have h0 : F' 0 = F := by simp [hF']
  have hne : ∀ j, j ≠ 0 → F' j = fun _ => (0 : ℝ) := fun j hj => by simp [hF', hj]
  have key := h d N hd hN s hs0 hsd V hV β hβ T a hT ha P X₀ W X hX F' (fun j => by
      by_cases hj : j = 0
      · subst hj; rw [h0]; exact hF
      · rw [hne j hj]; exact hz)
  have e1 : ∀ (G : ℕ → ℝ≥0∞), (∀ j, j ≠ 0 → G j = 0) → ∑' j, G j = G 0 :=
    fun G hG => tsum_eq_single 0 hG
  have hL : ∀ (ω : Ω) (t : ℝ), (∑' j, ENNReal.ofReal
      ((F' j (X t.toNNReal ω) - ∫ Y, F' j Y ∂μ) ^ 2)) =
      ENNReal.ofReal ((F (X t.toNNReal ω) - ∫ Y, F Y ∂μ) ^ 2) := by
    intro ω t
    rw [e1 _ (fun j hj => by simp [hne j hj]), h0]
  have hV' : (∑' j, ENNReal.ofReal (∫ Y, (F' j Y - ∫ Y', F' j Y' ∂μ) ^ 2 ∂μ)) =
      ENNReal.ofReal (∫ Y, (F Y - ∫ Y', F Y' ∂μ) ^ 2 ∂μ) := by
    rw [e1 _ (fun j hj => by simp [hne j hj]), h0]
  have hE : (∑' j, ENNReal.ofReal (∫ Y, configGradSq (F' j) Y ∂μ)) =
      ENNReal.ofReal (∫ Y, configGradSq F Y ∂μ) := by
    rw [e1 _ (fun j hj => by simp [hne j hj, configGradSq_zero]), h0]
  rw [← hμ] at key
  simp only [hL, hV', hE] at key
  exact key

/-- A single mode is smooth on the torus (from the `C^L` bounds of `fourierTailA_mul_realMode_isCk`). -/
theorem mode417B_isSmooth (l : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode l) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_infty]
  intro n
  have h := fourierTailA_mul_realMode_isCk 1 l n
  simp only [one_mul] at h
  exact h

/-- The pair seminorm of a single mode is bounded by its `cbNorm`, hence by `(K+1)√2 ⟨l⟩^K`. -/
theorem mode417B_ps_le (K : ℕ) (l : NonzeroLattice d) :
    0 ≤ posSeminorm K (Torus.realMode l) ∧
      posSeminorm K (Torus.realMode l) ≤ ((K : ℝ) + 1) * (Real.sqrt 2 * Lattice.jp l.1 ^ K) := by
  refine ⟨?_, ?_⟩
  · unfold posSeminorm
    exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun x => norm_nonneg _
  · have hcb := fourierTailA_mul_realMode_cbNorm 1 l K
    simp only [one_mul, abs_one, mul_one] at hcb
    refine le_trans ?_ hcb
    unfold posSeminorm Torus.cbNorm
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => Real.iSup_nonneg fun x => norm_nonneg _)
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega

theorem mode_forcing_bound_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
      (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X)
      (l : NonzeroLattice d) (Γ : ℝ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ)
      (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) (hγ' : ContinuousOn γ' (Set.Ici 0))
      (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
              forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (C * Γ ^ 2 * Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N) := by
  classical
  obtain ⟨C₈, hC₈0, hpkg⟩ := mode_package_proof hd hcrit V hV β hβ ρβ hρβ hρS hρpos
  obtain ⟨C₄, hC₄0, hwin⟩ := mode_window_bound_proof c hc T hT
  obtain ⟨CLZ, hCLZ0, hlzS⟩ := lz_scalar_proof
  obtain ⟨Cmax, hCmax⟩ : ∃ z : ℝ, z = max 1 (max (CLZ * (1 + β⁻¹ * T)) (8 * β⁻¹)) := ⟨_, rfl⟩
  have hCmax1 : 1 ≤ Cmax := by rw [hCmax]; exact le_max_left _ _
  have hCmaxLZ : CLZ * (1 + β⁻¹ * T) ≤ Cmax := by
    rw [hCmax]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCmax8 : 8 * β⁻¹ ≤ Cmax := by
    rw [hCmax]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCmax0 : 0 ≤ Cmax := by linarith
  have hβinv : 0 ≤ β⁻¹ * T := mul_nonneg (inv_nonneg.2 hβ.le) hT
  refine ⟨C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ (((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₄0 hCmax0) (sq_nonneg _)) h2
  intro N hN Ω _ P _ X₀ W X a ha hflow l Γ hΓ γ γ' hγ hγ' hbd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the single-mode data: mode package
  obtain ⟨F, G, E, hFm, hGm, hEm, hFlz, hFc, hFG, hFmean, hid, hFb, hEb, hGb, hcgs⟩ :=
    hpkg N hN (Torus.realMode l) (mode417B_isSmooth l)
  -- the seminorm constant `ς₀`
  obtain ⟨hps0, hps⟩ := mode417B_ps_le (8 * d + 80) l
  obtain ⟨ς₀, hς₀⟩ : ∃ z : ℝ, z = C₈ * ((((8 * d + 80 : ℕ) : ℝ) + 1) *
      (Real.sqrt 2 * Lattice.jp l.1 ^ (8 * d + 80))) := ⟨_, rfl⟩
  have hς₀0 : 0 ≤ ς₀ := by rw [hς₀]; exact mul_nonneg hC₈0 (le_trans hps0 hps)
  have hps' : C₈ * posSeminorm (8 * d + 80) (Torus.realMode l) ≤ ς₀ := by
    rw [hς₀]; exact mul_le_mul_of_nonneg_left hps hC₈0
  have hps'0 : 0 ≤ C₈ * posSeminorm (8 * d + 80) (Torus.realMode l) := mul_nonneg hC₈0 hps0
  have hq0 : 0 ≤ ς₀ ^ 2 / N := by positivity
  have hqsq : ∀ x : ℝ, 0 ≤ x → x ≤ ς₀ → x ^ 2 / N ≤ ς₀ ^ 2 / N := fun x hx0 hxle =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hxle 2) hN0.le
  -- the constant `ς`
  obtain ⟨ς, hς⟩ : ∃ z : ℝ, z = Real.sqrt (Cmax * (ς₀ ^ 2 / N)) := ⟨_, rfl⟩
  have hς0 : 0 ≤ ς := by rw [hς]; exact Real.sqrt_nonneg _
  have hς2 : ς ^ 2 = Cmax * (ς₀ ^ 2 / N) := by
    rw [hς]; exact Real.sq_sqrt (mul_nonneg hCmax0 hq0)
  have hqς : ς₀ ^ 2 / N ≤ ς ^ 2 := by
    rw [hς2]; exact le_mul_of_one_le_left hq0 hCmax1
  have hF : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
      ENNReal.ofReal (ς ^ 2) :=
    hFb.trans (ENNReal.ofReal_le_ofReal ((hqsq _ hps'0 hps').trans hqς))
  have hE : ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
      ENNReal.ofReal (ς ^ 2) :=
    hEb.trans (ENNReal.ofReal_le_ofReal ((hqsq _ hps'0 hps').trans hqς))
  -- the martingale part: Dynkin formula for the closed generator
  obtain ⟨hint, hcont, hmax0⟩ :=
    dynkin_closedGenerator_proof hd hs0 hsd V hV β hβ hN P X₀ W X (a + T) hflow F G hFm hGm hFc hFG
  have hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + T →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (ς ^ 2 * (t - u)) := by
    intro u t hu hut htH
    have ht0 : 0 ≤ t - u := by linarith
    have hmul0 : 0 ≤ 8 * β⁻¹ * (t - u) := mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hβ.le)) ht0
    have hx : (C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N ≤ ς₀ ^ 2 / N :=
      hqsq _ hps'0 hps'
    have hreal : 8 * β⁻¹ * (t - u) * ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N) ≤
        ς ^ 2 * (t - u) := by
      have s1 := mul_le_mul_of_nonneg_left hx hmul0
      have s2 : 8 * β⁻¹ * (t - u) * (ς₀ ^ 2 / N) ≤ Cmax * (t - u) * (ς₀ ^ 2 / N) := by
        apply mul_le_mul_of_nonneg_right _ hq0
        exact mul_le_mul_of_nonneg_right hCmax8 ht0
      rw [hς2]
      nlinarith
    refine (hmax0 u t hu hut htH).trans ?_
    calc ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2
          ∂(canonicalGibbs (periodicRiesz d s) V N β)
        ≤ ENNReal.ofReal (8 * β⁻¹ * (t - u)) *
            ENNReal.ofReal ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N) :=
          by gcongr
      _ = ENNReal.ofReal (8 * β⁻¹ * (t - u) *
            ((C₈ * posSeminorm (8 * d + 80) (Torus.realMode l)) ^ 2 / N)) :=
          (ENNReal.ofReal_mul hmul0).symm
      _ ≤ ENNReal.ofReal (ς ^ 2 * (t - u)) := ENNReal.ofReal_le_ofReal hreal
  -- the Lyons-Zheng bound for `F`
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hFsq_int : Integrable (fun Y => F Y ^ 2) μ := hFlz.memLp.integrable_sq
  have hFsq_nn : 0 ≤ᵐ[μ] (fun Y => F Y ^ 2) :=
    Filter.Eventually.of_forall fun Y => by show (0 : ℝ) ≤ F Y ^ 2; exact sq_nonneg _
  have hA : ∫ Y, F Y ^ 2 ∂μ ≤ ς₀ ^ 2 / N := by
    refine (ENNReal.ofReal_le_ofReal_iff hq0).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hFsq_int hFsq_nn]
    exact hFb.trans (ENNReal.ofReal_le_ofReal (hqsq _ hps'0 hps'))
  have hB_nn : 0 ≤ᵐ[μ] (fun Y => configGradSq F Y) :=
    Filter.Eventually.of_forall fun Y => by
      show (0 : ℝ) ≤ configGradSq F Y
      unfold configGradSq
      exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hB : ∫ Y, configGradSq F Y ∂μ ≤ ς₀ ^ 2 / N := by
    refine (ENNReal.ofReal_le_ofReal_iff hq0).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hFlz.energy hB_nn]
    exact hcgs.trans (ENNReal.ofReal_le_ofReal (hqsq _ hps'0 hps'))
  have hA0 : 0 ≤ ∫ Y, F Y ^ 2 ∂μ := integral_nonneg fun Y => sq_nonneg _
  have hB0 : 0 ≤ ∫ Y, configGradSq F Y ∂μ := integral_nonneg fun Y => by
    show (0 : ℝ) ≤ configGradSq F Y
    unfold configGradSq
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hlz0 := hlzS d N hd hN s hs0 hsd V hV β hβ T a hT ha P X₀ W X hflow F hFlz
  rw [← hμ] at hlz0
  rw [hFmean] at hlz0
  simp only [sub_zero] at hlz0
  have hLZ : ∫⁻ ω, ⨆ t ∈ ratTimes a T, ENNReal.ofReal (F (X t.toNNReal ω) ^ 2) ∂P ≤
      ENNReal.ofReal (ς ^ 2) := by
    refine hlz0.trans ?_
    have hreal : CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ) ≤ ς ^ 2 := by
      have h1 : ∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ ≤
          (1 + β⁻¹ * T) * (ς₀ ^ 2 / N) := by
        have m1 := mul_le_mul_of_nonneg_left hB hβinv
        have e1 : (1 + β⁻¹ * T) * (ς₀ ^ 2 / N) = ς₀ ^ 2 / N + β⁻¹ * T * (ς₀ ^ 2 / N) := by ring
        rw [e1]
        linarith
      have h2 : CLZ * ((1 + β⁻¹ * T) * (ς₀ ^ 2 / N)) ≤ Cmax * (ς₀ ^ 2 / N) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCmaxLZ hq0
      calc CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ)
          ≤ CLZ * ((1 + β⁻¹ * T) * (ς₀ ^ 2 / N)) := mul_le_mul_of_nonneg_left h1 hCLZ0.le
        _ ≤ Cmax * (ς₀ ^ 2 / N) := h2
        _ = ς ^ 2 := hς2.symm
    calc ENNReal.ofReal CLZ * (ENNReal.ofReal (∫ Y, F Y ^ 2 ∂μ) +
            ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal (∫ Y, configGradSq F Y ∂μ))
        = ENNReal.ofReal (CLZ * (∫ Y, F Y ^ 2 ∂μ + β⁻¹ * T * ∫ Y, configGradSq F Y ∂μ)) := by
          rw [ENNReal.ofReal_mul hCLZ0.le, ENNReal.ofReal_add hA0 (mul_nonneg hβinv hB0),
            ENNReal.ofReal_mul hβinv]
      _ ≤ ENNReal.ofReal (ς ^ 2) := ENNReal.ofReal_le_ofReal hreal
  -- the integrand identification: the forcing statistic equals `-G + E` along the flow
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) (a + T) X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  have hgood : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ a + T →
      forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω) =
        -G (X r.toNNReal ω) + E (X r.toNNReal ω) := by
    filter_upwards [hsol.no_collision] with ω hω r hr0 hrH
    have hcol : X r.toNNReal ω ∉ collisionSet d N := hω _ (by rw [Real.coe_toNNReal _ hr0]; exact hrH)
    exact hid _ hcol
  have hEqInt : ∀ᵐ ω ∂P,
      ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) =
      ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2) := by
    filter_upwards [hgood] with ω hω
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    have ht0 : 0 ≤ a + t := by linarith [ht.1.1]
    have htH : a + t ≤ a + T := by linarith [ht.1.2]
    have hEq : ∫ r in (0 : ℝ)..(a + t), γ (a + t - r) * forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)
        = ∫ r in (0 : ℝ)..(a + t), γ (a + t - r) * (-G (X r.toNNReal ω) + E (X r.toNNReal ω)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le ht0] at hr
      dsimp only
      rw [hω r hr.1 (hr.2.trans htH)]
    rw [hEq]
  have hwinb := hwin hd hs0 hsd V hV β hβ hN P X₀ W X (a + T) hflow F G E hFm hGm hEm ς Γ hς0 hΓ
    hint hcont hmax a ha le_rfl hLZ hF hE γ γ' hγ hγ' hbd
  -- the final constant
  have hς0sq : ς₀ ^ 2 = C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) *
      Lattice.jp l.1 ^ (2 * (8 * d + 80)) := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hς₀, mul_pow, mul_pow, mul_pow, h2, ← pow_mul]
    ring
  have hfinal : C₄ * Γ ^ 2 * ς ^ 2 =
      C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) * Γ ^ 2 *
        Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N := by
    rw [hς2, hς0sq]
    ring
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          forcingStat s V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P
      = ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
          (-G (X r.toNNReal ω) + E (X r.toNNReal ω))) ^ 2) ∂P := lintegral_congr_ae hEqInt
    _ ≤ ENNReal.ofReal (C₄ * Γ ^ 2 * ς ^ 2) := hwinb
    _ ≤ ENNReal.ofReal (C₄ * Cmax * C₈ ^ 2 * ((((8 * d + 80 : ℕ) : ℝ) + 1) ^ 2 * 2) * Γ ^ 2 *
          Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N) :=
        ENNReal.ofReal_le_ofReal (le_of_eq hfinal)

end HRS.ME

end
