import HRS.MS.MovAdjAux7

/-!
# S6.7 (packet P2, part 3): the bridge from classical solutions to the adjoint semigroup

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_bridge`: for a classical adjoint solution `f` (stationary coefficient, terminal datum `φ` at `t`), `0 ≤ r ≤ t`, and `v₀ ∈ L²_0`
in the Schwartz core,
`∫ f_r √ρ v₀ = ∫ φ √ρ (T(t-r) v₀)`.
Proof: `g(σ) = ⟨f_{r+σ}√ρ, T(σ)v₀⟩` is continuous on `[0,t-r]` with right derivative `0` on `(0,t-r)`
(`s67_hasDeriv_pairing`, the duality identity `s67_duality`, `s67_T_deriv`), so it is constant.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The time clamp. -/
def s67clamp (r t τ : ℝ) : ℝ := max 0 (min (r + τ) t)

theorem s67clamp_mem {r t : ℝ} (ht : 0 ≤ t) (τ : ℝ) : s67clamp r t τ ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem s67clamp_eq {r t τ : ℝ} (h0 : 0 ≤ r + τ) (h1 : r + τ ≤ t) : s67clamp r t τ = r + τ := by
  unfold s67clamp
  rw [min_eq_left h1, max_eq_right h0]

theorem s67clamp_cont (r t : ℝ) : Continuous (s67clamp r t) := by
  unfold s67clamp
  fun_prop

/-- Bounds of the classical solution. -/
theorem s67_f_bdd {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |f r x| ≤ B := by
  obtain ⟨B, hB⟩ := hf.bdd 0 (by norm_num)
  refine ⟨max B 0, le_max_right _ _, fun r hr x => ?_⟩
  have := hB r hr x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem s67_gen_cont {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    Continuous fun x => generatorW C r (f r) x := by
  have h := hf.cont_time_deriv
  have h2 : Continuous fun x : Euc d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) t), x) :=
    Continuous.prodMk continuous_const continuous_id
  have h3 := Continuous.comp (g := fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW C p.1 (f p.1) p.2) h h2
  exact h3

/-- The family `a_τ = f_{clamp(r+τ)} √ρ`. -/
def s67a (f : ℝ → Euc d → ℝ) (ρ : Euc d → ℝ) (r t : ℝ) (τ : ℝ) (x : Euc d) : ℝ :=
  f (s67clamp r t τ) x * Real.sqrt (ρ x)

theorem s67a_memLp {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (ht : 0 ≤ t) (r : ℝ)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) (τ : ℝ) :
    MemLp (s67a f ρ r t τ) 2 (volume : Measure (Euc d)) := by
  obtain ⟨B0, hB00, hB0⟩ := s67_f_bdd hf
  have hfc : Continuous (f (s67clamp r t τ)) := (hf.c2 _ (s67clamp_mem ht τ)).continuous
  exact s67_memLp_mul_bdd hgL hfc.aestronglyMeasurable (B := B0) (fun x => hB0 _ (s67clamp_mem ht τ) x)

theorem s67a_cont {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (ht : 0 ≤ t) (r : ℝ)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) (hρ : Continuous ρ) :
    ContinuousOn (fun τ => (s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ)) Set.univ := by
  obtain ⟨B0, hB00, hB0⟩ := s67_f_bdd hf
  intro σ _
  refine s67_cont_toLp (H := fun x => B0 * Real.sqrt (ρ x)) (s67a_memLp hf ht r hgL) (hgL.const_mul B0) ?_
    (Set.mem_univ σ) ?_
  · intro τ _ x
    unfold s67a
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hB0 _ (s67clamp_mem ht τ) x) (Real.sqrt_nonneg _)
  · intro x
    have h1 : Continuous fun τ => f (s67clamp r t τ) x :=
      (s67_cont_time hf x).comp_continuous (s67clamp_cont r t) (fun τ => s67clamp_mem ht τ)
    exact (h1.mul continuous_const).continuousWithinAt

theorem s67a_hasDeriv (H : Mov2dTh d s β q ρ) {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (t - r)) :
    ∃ (a' : Euc d → ℝ) (ha' : MemLp a' 2 (volume : Measure (Euc d))),
      (∀ x, a' x = (-(generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) (r + σ) (f (r + σ)) x)) *
        Real.sqrt (ρ x)) ∧
      HasDerivWithinAt (fun τ => (s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
        (ha'.toLp a') (Set.Ici σ) σ := by
  set C := (quadraticGradientDyn d s q β).coeff (fun _ => ρ) with hC
  have hρ := mnb_rhoData H
  obtain ⟨Bf, hBf0, hBgen, hlip⟩ := s67_time_lip hf
  have hr1 : 0 < r + σ := by linarith [hr.1, hσ.1]
  have hr2 : r + σ < t := by linarith [hσ.2]
  set r' := r + σ with hr'
  have hr'mem : r' ∈ Set.Icc (0 : ℝ) t := ⟨hr1.le, hr2.le⟩
  have hclσ : s67clamp r t σ = r' := s67clamp_eq hr1.le hr2.le
  set a' : Euc d → ℝ := fun x => (-(generatorW C r' (f r') x)) * Real.sqrt (ρ x) with ha'def
  set G : Euc d → ℝ := fun x => Bf * ((1 + ‖x‖) * Real.sqrt (ρ x)) with hGdef
  have hGL : MemLp G 2 (volume : Measure (Euc d)) := (s67_memLp_G H).const_mul Bf
  have ha'meas : AEStronglyMeasurable a' (volume : Measure (Euc d)) := by
    have h1 : Continuous fun x => generatorW C r' (f r') x := s67_gen_cont hf hr'mem
    exact ((h1.neg).mul hρ.smooth.continuous.sqrt).aestronglyMeasurable
  have hbG : ∀ x, |a' x| ≤ G x := by
    intro x
    rw [ha'def]
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |generatorW C r' (f r') x| * Real.sqrt (ρ x) ≤ (Bf * (1 + ‖x‖)) * Real.sqrt (ρ x) :=
          mul_le_mul_of_nonneg_right (hBgen r' hr'mem x) (Real.sqrt_nonneg _)
      _ = G x := by rw [hGdef]; ring
  have ha'L : MemLp a' 2 (volume : Measure (Euc d)) :=
    MemLp.of_le_mul (c := 1) hGL ha'meas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg
        (mul_nonneg hBf0 (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))]
      exact hbG x)
  have hdom : ∀ τ ∈ Set.Ioo σ (σ + (t - r - σ)), ∀ x,
      |s67a f ρ r t τ x - s67a f ρ r t σ x| ≤ (τ - σ) * G x := by
    intro τ hτ x
    have hτ1 : r + τ < t := by linarith [hτ.2]
    have hτ0 : 0 ≤ r + τ := by linarith [hτ.1]
    have e1 : s67clamp r t τ = r + τ := s67clamp_eq hτ0 hτ1.le
    unfold s67a
    rw [e1, hclσ, ← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := hlip r' (r + τ) hr1 (by linarith [hτ.1]) hτ1.le x
    calc |f (r + τ) x - f r' x| * Real.sqrt (ρ x) ≤ (Bf * (1 + ‖x‖) * (r + τ - r')) * Real.sqrt (ρ x) :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ = (τ - σ) * G x := by rw [hGdef, hr']; ring
  have hpt : ∀ x, Tendsto (fun τ => (τ - σ)⁻¹ * (s67a f ρ r t τ x - s67a f ρ r t σ x)) (𝓝[>] σ)
      (𝓝 (a' x)) := by
    intro x
    have hd1 : HasDerivAt (fun τ => f (r + τ) x) (-(generatorW C r' (f r') x)) σ := by
      have := hf.time_deriv x r' ⟨hr1, hr2⟩
      exact this.comp_const_add r σ
    have hsl := (hasDerivAt_iff_tendsto_slope.1 hd1).mono_left (nhdsGT_le_nhdsNE σ)
    have hsl' := hsl.mul_const (Real.sqrt (ρ x))
    refine hsl'.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show σ < σ + (t - r - σ) by linarith)] with τ hτ
    have hτ1 : r + τ < t := by linarith [hτ.2]
    have hτ0 : 0 ≤ r + τ := by linarith [hτ.1]
    have e1 : s67clamp r t τ = r + τ := s67clamp_eq hτ0 hτ1.le
    unfold s67a
    rw [e1, hclσ, slope_def_field, ← sub_mul]
    simp only [← hr']
    field_simp
  refine ⟨a', ha'L, fun x => rfl, ?_⟩
  exact s67_hasDeriv_toLp (a := s67a f ρ r t) (a' := a') (G := G) (σ := σ) (δ := t - r - σ)
    (by linarith [hσ.2]) (s67a_memLp hf ht r hgL) hGL ha'L hdom hpt hbG

end HRS.MS.MovAdj
