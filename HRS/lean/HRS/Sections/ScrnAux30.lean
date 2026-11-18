import HRS.Sections.ScrnAux29

/-!
# Packet SCRN, part 30: `E ∫ ‖Σ - Σ̄‖_{S₁} ≤ ∑ 2β⁻¹ C_q (∫ L N^{-1/d} + ∫ H √o_N)`

Entry by entry, `Σ^{ab}_r - Σ̄^{ab}_r = 2β⁻¹ (μ_N^r(χ_{ab}) - ∫χ_{ab})`; the coercivity test clause of
`A8CommSpec` bounds this by the Lipschitz constant `L_{ab}(r)` and the `Ḣ^{(d-s)/2}` bound `H_{ab}(r)` of
`χ_{ab} = ⟨∇f_a^r, ∇f_b^r⟩`, then Jensen (`E √G_r ≤ √o_N`) and Tonelli in `(r, ω)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

open HRS.Main.A8P HRS.Uniform

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_cov_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {ℱ : MeasureTheory.Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {C₀ Cq : ℝ} (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq)
    {Tm : ℝ} (hTm0 : 0 < Tm) {p : ℕ} (ts : Fin p → ℝ) (htsT : ∀ a, ts a ∈ Set.Icc 0 Tm)
    (f : Fin p → ℝ → Torus d → ℝ)
    (Lf Hf : Fin p → Fin p → ℝ → ℝ) (hLm : ∀ a b, Measurable (Lf a b))
    (hHm : ∀ a b, Measurable (Hf a b))
    (hL0 : ∀ a b, ∀ r ∈ Set.Ico 0 (min (ts a) (ts b)), 0 ≤ Lf a b r)
    (hH0 : ∀ a b, ∀ r ∈ Set.Ico 0 (min (ts a) (ts b)), 0 ≤ Hf a b r)
    (hLint : ∀ a b, IntegrableOn (Lf a b) (Set.Ico 0 (min (ts a) (ts b))))
    (hHint : ∀ a b, IntegrableOn (Hf a b) (Set.Ico 0 (min (ts a) (ts b))))
    (hχ : ∀ a b, ∀ r ∈ Set.Ico 0 (min (ts a) (ts b)),
      KernelGrad.IsLipschitz (Lf a b r)
        (fun x => inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) ∧
      HasFiniteHomSobolev (((d : ℝ) - s) / 2)
        (fun x => inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) ∧
      homSobolev (((d : ℝ) - s) / 2)
        (fun x => inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) ≤ Hf a b r) :
    covDiscrepancyMatrix P Tm
        (killedCovMatrix (fun a => scrnPhi (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (Real.sqrt N)
          (ts a) (f a) X) ts)
        (scrnSig ts (scrnGc ts f) (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ)) ≤
      ∑ i : Fin p, ∑ j : Fin p, (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ * Cq *
        ((∫ r in Set.Ico 0 (min (ts j) (ts i)), Lf j i r) * (N : ℝ) ^ (-(1 : ℝ) / d) +
          (∫ r in Set.Ico 0 (min (ts j) (ts i)), Hf j i r) * Real.sqrt (oN d s C₀ N))) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  set o : ℝ := oN d s C₀ N with ho
  set c : ℝ := 2 * D.invβ with hc
  have hc0 : 0 ≤ c := by have := D.hβ; positivity
  obtain ⟨G, hGm, hG0, hGint, hGmom, hGfacts⟩ := scrn_G_facts hd hs0 hsd β hβ hN hfl hF hcom hTm0
  have hsolT := hfl.sol Tm hTm0.le
  have hnoc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ Tm → X t ω ∉ collisionSet d N := hsolT.no_collision
  have hρ := scrn_isProbDensity_one (d := d)
  have ho0 : 0 ≤ o := (integral_nonneg (hG0 0)).trans (hGmom 0 ⟨le_rfl, hTm0.le⟩)
  set Nn : ℝ := (N : ℝ) ^ (-(1 : ℝ) / d) with hNn
  have hNn0 : 0 ≤ Nn := Real.rpow_nonneg (Nat.cast_nonneg N) _
  -- the weights
  set gL : Fin p → Fin p → ℝ → ℝ := fun a b r => c * Cq * Lf a b r * Nn with hgL
  set gH : Fin p → Fin p → ℝ → ℝ := fun a b r => c * Cq * Hf a b r with hgH
  set wL : Fin p → Fin p → ℝ → ℝ := fun a b =>
    (Set.Ico 0 (min (ts a) (ts b))).indicator (gL a b) with hwL
  set wH : Fin p → Fin p → ℝ → ℝ := fun a b =>
    (Set.Ico 0 (min (ts a) (ts b))).indicator (gH a b) with hwH
  have hgL0 : ∀ a b, ∀ r ∈ Set.Ico 0 (min (ts a) (ts b)), 0 ≤ gL a b r := by
    intro a b r hr; have := hL0 a b r hr; simp only [hgL]; positivity
  have hgH0 : ∀ a b, ∀ r ∈ Set.Ico 0 (min (ts a) (ts b)), 0 ≤ gH a b r := by
    intro a b r hr; have := hH0 a b r hr; simp only [hgH]; positivity
  have hwL0 : ∀ a b r, 0 ≤ wL a b r := by
    intro a b r; simp only [hwL]
    by_cases h : r ∈ Set.Ico 0 (min (ts a) (ts b))
    · rw [Set.indicator_of_mem h]; exact hgL0 a b r h
    · rw [Set.indicator_of_notMem h]
  have hwH0 : ∀ a b r, 0 ≤ wH a b r := by
    intro a b r; simp only [hwH]
    by_cases h : r ∈ Set.Ico 0 (min (ts a) (ts b))
    · rw [Set.indicator_of_mem h]; exact hgH0 a b r h
    · rw [Set.indicator_of_notMem h]
  have hgLm : ∀ a b, Measurable (gL a b) := fun a b => ((hLm a b).const_mul _).mul_const _
  have hgHm : ∀ a b, Measurable (gH a b) := fun a b => (hHm a b).const_mul _
  have hwLm : ∀ a b, Measurable (wL a b) := fun a b => (hgLm a b).indicator measurableSet_Ico
  have hwHm : ∀ a b, Measurable (wH a b) := fun a b => (hgHm a b).indicator measurableSet_Ico
  have hmT : ∀ a b, min (ts a) (ts b) ≤ Tm := fun a b => (min_le_left _ _).trans (htsT a).2
  have hgLint : ∀ a b, IntegrableOn (gL a b) (Set.Ico 0 (min (ts a) (ts b))) := fun a b =>
    ((hLint a b).const_mul (c * Cq)).mul_const Nn
  have hgHint : ∀ a b, IntegrableOn (gH a b) (Set.Ico 0 (min (ts a) (ts b))) := fun a b =>
    (hHint a b).const_mul (c * Cq)
  have hwLint : ∀ a b, IntegrableOn (wL a b) (Set.Icc 0 Tm) := fun a b =>
    ((hgLint a b).integrable_indicator measurableSet_Ico).integrableOn
  have hwHint : ∀ a b, IntegrableOn (wH a b) (Set.Icc 0 Tm) := fun a b =>
    ((hgHint a b).integrable_indicator measurableSet_Ico).integrableOn
  have hIcoIcc : ∀ a b, Set.Icc 0 Tm ∩ Set.Ico 0 (min (ts a) (ts b)) = Set.Ico 0 (min (ts a) (ts b)) :=
    fun a b => Set.inter_eq_right.2 (fun r hr => ⟨hr.1, hr.2.le.trans (hmT a b)⟩)
  have hwLI : ∀ a b, ∫ r in Set.Icc 0 Tm, wL a b r = c * Cq * (∫ r in Set.Ico 0 (min (ts a) (ts b)), Lf a b r) * Nn := by
    intro a b
    simp only [hwL]
    rw [setIntegral_indicator measurableSet_Ico, hIcoIcc]
    simp only [hgL]
    rw [integral_mul_const, integral_const_mul]
  have hwHI : ∀ a b, ∫ r in Set.Icc 0 Tm, wH a b r = c * Cq * (∫ r in Set.Ico 0 (min (ts a) (ts b)), Hf a b r) := by
    intro a b
    simp only [hwH]
    rw [setIntegral_indicator measurableSet_Ico, hIcoIcc]
    simp only [hgH]
    rw [integral_const_mul]
  -- entrywise bound
  have hentry : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) Tm, ∀ a b : Fin p,
      |killedCovMatrix (fun a => scrnPhi D (Real.sqrt N) (ts a) (f a) X) ts r ω a b -
        scrnSig ts (scrnGc ts f) c r a b| ≤ wL a b r + wH a b r * Real.sqrt (G r ω) := by
    filter_upwards [hnoc, hGfacts] with ω hno hGf r hr a b
    rw [scrn_cov_entry (by omega) D ts f X r ω a b]
    by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
    · rw [if_pos h]
      have hmem : r ∈ Set.Ico 0 (min (ts a) (ts b)) := ⟨h.1, h.2⟩
      obtain ⟨hLip, hfin, hhom⟩ := hχ a b r hmem
      have hcoll : X (Real.toNNReal r) ω ∉ collisionSet d N := hno _ (by
        rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
      have htest := (hcom 1 le_rfl N hN (fun _ => (1 : ℝ)) hρ (fun _ => le_rfl) _ hcoll).2.2
        (fun x => inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) (Lf a b r)
        (hL0 a b r hmem) hLip hfin
      rw [scrn_withDensityReal_one, scrn_oNΛ_one] at htest
      have hsm : smearScale d N 1 = Nn := by unfold smearScale; rw [mul_one]
      rw [hsm] at htest
      have hGG := (hGf r hr).2
      have hsq : Real.sqrt (rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + o) ≤
          Real.sqrt (G r ω) := Real.sqrt_le_sqrt hGG
      have hH' : homSobolev (((d : ℝ) - s) / 2)
          (fun x => inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)) *
          Real.sqrt (rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + o) ≤
          Hf a b r * Real.sqrt (G r ω) :=
        mul_le_mul hhom hsq (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hhom)
      rw [abs_mul, abs_of_nonneg hc0]
      simp only [hwL, hwH, Set.indicator_of_mem hmem, hgL, hgH]
      have h2 : |∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)
            ∂(empirical (X (Real.toNNReal r) ω)) -
          ∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x)| ≤
          Cq * Lf a b r * Nn + Cq * (Hf a b r * Real.sqrt (G r ω)) := by
        refine htest.trans ?_
        have := mul_le_mul_of_nonneg_left hH' hCq
        linarith
      calc c * |_| ≤ c * (Cq * Lf a b r * Nn + Cq * (Hf a b r * Real.sqrt (G r ω))) :=
            mul_le_mul_of_nonneg_left h2 hc0
        _ = _ := by ring
    · rw [if_neg h, abs_zero]
      have hmem : r ∉ Set.Ico 0 (min (ts a) (ts b)) := fun h' => h ⟨h'.1, h'.2⟩
      exact add_nonneg (hwL0 a b r) (mul_nonneg (hwH0 a b r) (Real.sqrt_nonneg _))
  -- Fubini for the random part
  have hGrm : ∀ r, Measurable (G r) := fun r => hGm.comp measurable_prodMk_left
  have hjen : ∀ r ∈ Set.Icc (0 : ℝ) Tm, Integrable (fun ω => Real.sqrt (G r ω)) P ∧
      ∫ ω, Real.sqrt (G r ω) ∂P ≤ Real.sqrt o := by
    intro r hr
    obtain ⟨h1, h2⟩ := scrn_jensen_sqrt P (G r) (hGrm r) (Filter.Eventually.of_forall fun ω => hG0 r ω)
      (hGint r hr)
    exact ⟨h1, h2.trans (Real.sqrt_le_sqrt (hGmom r hr))⟩
  have hFub : ∀ a b : Fin p,
      (∀ᵐ ω ∂P, IntegrableOn (fun r => wH a b r * Real.sqrt (G r ω)) (Set.Icc (0 : ℝ) Tm)) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)) ∂P ≤
        ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt o) ∧
      AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)) P := by
    intro a b
    exact scrn_time_integral_w P hTm0.le (fun r ω => wH a b r * Real.sqrt (G r ω))
      (((hwHm a b).comp measurable_fst).mul (hGm.sqrt))
      (Filter.Eventually.of_forall fun ω r _ => mul_nonneg (hwH0 a b r) (Real.sqrt_nonneg _))
      (fun r hr => ((hjen r hr).1).const_mul _) (fun r => wH a b r * Real.sqrt o)
      ((hwHint a b).mul_const _) (fun r hr => by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hjen r hr).2 (hwH0 a b r))
  have hint_ae : ∀ᵐ ω ∂P, ∀ a b : Fin p,
      IntegrableOn (fun r => wH a b r * Real.sqrt (G r ω)) (Set.Icc (0 : ℝ) Tm) := by
    rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b; exact (hFub a b).1
  -- pointwise in ω
  have hω : ∀ᵐ ω ∂P, ∫ r in Set.Icc (0 : ℝ) Tm, s1Norm (killedCovMatrix
        (fun a => scrnPhi D (Real.sqrt N) (ts a) (f a) X) ts r ω - scrnSig ts (scrnGc ts f) c r) ≤
      ∑ i : Fin p, ∑ j : Fin p, ((∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
        ∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt (G r ω)) := by
    filter_upwards [hentry, hint_ae] with ω hent hint
    have hterm : ∀ i j : Fin p, IntegrableOn (fun r => wL j i r + wH j i r * Real.sqrt (G r ω))
        (Set.Icc (0 : ℝ) Tm) := fun i j => (hwLint j i).add (hint j i)
    have hsumint : IntegrableOn (fun r => ∑ i : Fin p, ∑ j : Fin p, (wL j i r +
        wH j i r * Real.sqrt (G r ω))) (Set.Icc (0 : ℝ) Tm) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j
    have hle := integral_mono_of_nonneg (μ := volume.restrict (Set.Icc (0 : ℝ) Tm))
      (f := fun r => s1Norm (killedCovMatrix (fun a => scrnPhi D (Real.sqrt N) (ts a) (f a) X) ts r ω -
        scrnSig ts (scrnGc ts f) c r))
      (Filter.Eventually.of_forall fun r => traceNormMatrix_nonneg _) hsumint
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr =>
        (LindebergAux.s1Norm_le_sum _).trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hent r hr j i)))
    refine hle.trans (le_of_eq ?_)
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_add (hwLint j i) (hint j i)
  -- integrability of the right-hand side and its integral
  have hgint : ∀ a b : Fin p, Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)) P ∧
      ∫ ω, (∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)) ∂P ≤
        ∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt o := by
    intro a b
    obtain ⟨-, h2, h3⟩ := hFub a b
    have hB0 : 0 ≤ ∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt o :=
      setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (hwH0 a b r) (Real.sqrt_nonneg _)
    have hnn : ∀ᵐ ω ∂P, 0 ≤ ∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω) :=
      Filter.Eventually.of_forall fun ω =>
        setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (hwH0 a b r) (Real.sqrt_nonneg _)
    obtain ⟨hi, hb⟩ := a8p_abs_integral_le h3 hB0 (by
      refine le_trans (le_of_eq ?_) h2
      refine lintegral_congr fun ω => ?_
      rw [abs_of_nonneg (setIntegral_nonneg measurableSet_Icc fun r _ =>
        mul_nonneg (hwH0 a b r) (Real.sqrt_nonneg _))])
    refine ⟨hi, ?_⟩
    have : ∫ ω, |∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)| ∂P =
        ∫ ω, (∫ r in Set.Icc (0 : ℝ) Tm, wH a b r * Real.sqrt (G r ω)) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hnn] with ω hω using abs_of_nonneg hω
    rw [← this]; exact hb
  have hterm2 : ∀ i j : Fin p, Integrable (fun ω => (∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
      ∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt (G r ω)) P := fun i j =>
    (integrable_const _).add (hgint j i).1
  have hRHSint : Integrable (fun ω => ∑ i : Fin p, ∑ j : Fin p, ((∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
      ∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt (G r ω))) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm2 i j
  unfold covDiscrepancyMatrix
  calc ∫ ω, (∫ σ in Set.Icc (0 : ℝ) Tm, s1Norm (killedCovMatrix
        (fun a => scrnPhi D (Real.sqrt N) (ts a) (f a) X) ts σ ω - scrnSig ts (scrnGc ts f) c σ)) ∂P
      ≤ ∫ ω, ∑ i : Fin p, ∑ j : Fin p, ((∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
          ∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt (G r ω)) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
          setIntegral_nonneg measurableSet_Icc fun r _ => traceNormMatrix_nonneg _) hRHSint hω
    _ = ∑ i : Fin p, ∑ j : Fin p, ((∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
          ∫ ω, (∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt (G r ω)) ∂P) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm2 i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hterm2 i j]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_add (integrable_const _) (hgint j i).1]
        simp
    _ ≤ ∑ i : Fin p, ∑ j : Fin p, ((∫ r in Set.Icc (0 : ℝ) Tm, wL j i r) +
          ∫ r in Set.Icc (0 : ℝ) Tm, wH j i r * Real.sqrt o) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add le_rfl (hgint j i).2
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hwLI, integral_mul_const, hwHI]
        ring

end HRS
