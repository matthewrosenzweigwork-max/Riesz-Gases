import HRS.MS.R2ChaosAux32

/-!
# HRS.MS.R2ChaosAux33 -- bridges for the assembly of (i): membership in `L²(dt)` and norms in `R2L2 T × V`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_Flim_memLp` : the Gaussian-side finite-rank integrand lies in `L²(dt)` for every `ζ'`.
* `s94_quad_ae_memLp` : the quadratic process lies in `L²(dt)` for `P_N`-a.e. `ζ` (`N ≥ 2`).
* `s94_pair_enorm_sq` : `‖(L²path f, c) - (L²path g, c)‖ₑ² = ∫⁻_{[0,T]} ‖f - g‖ₑ²` for `f, g ∈ L²(dt)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Bridges

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_Flim_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 ≤ T) {n : ℕ}
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) {C : ℝ → Fin n → Fin n → ℝ}
    (hCm : ∀ a b, Measurable fun t => C t a b) {K0 : ℝ} (hK0 : 0 ≤ K0) (hCb : ∀ t a b, |C t a b| ≤ K0)
    (ζ : Ω') : MemLp (fun t => s94Flim ξ P' C u t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨K1, hK1, -, hbL⟩ := s94mN_bdd hd hs0 hs hb hp hρ hset (coef := s94coef C) hK0
    (s94coef_abs_le hK0 hCb) (ua := fun q => u q.1) (ub := fun q => u q.2) (fun q => hu q.1) (fun q => hu q.2)
  have hmL : MemLp (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    s94_memLp_of_bdd (s94mL_measurable ξ hset.measξ P' (s94coef_measurable hCm) _ _) hbL
  have hI : MemLp (s94Intg (s94coef C) Prod.fst Prod.snd (fun a => ξ (u a) ζ)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    s94Intg_memLp hT (s94coef_measurable hCm) (s94coef_abs_le hK0 hCb) Prod.fst Prod.snd _
  have e : (fun t => s94Flim ξ P' C u t ζ) = fun t => s94Intg (s94coef C) Prod.fst Prod.snd
      (fun a => ξ (u a) ζ) t - s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2) t := by
    funext t
    unfold s94Intg s94mL s94Flim s94coef
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e]
  exact hI.sub hmL

theorem s94_quad_ae_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B' : ℝ}
    {kf : ℝ → Euc d → Euc d → ℝ} (hkm : Measurable fun q : ℝ × Euc d × Euc d => kf q.1 q.2.1 q.2.2)
    (hk : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B' (kf t)) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_time_bounds hd hs0 hs hb hp hρ hset B' (r := 2) (by norm_num)
  have hQ := s94_quad_measurable (μ := Whole.withDensityReal ρ) (P := P N) hkm (X N) (hset.measX N)
  let I : Ω N → ℝ≥0∞ := fun ζ => ∫⁻ t in Set.Icc (0 : ℝ) T,
    ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2 ∂volume
  have hQ2 : Measurable fun q : ℝ × Ω N =>
      ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) q.1 q.2‖ₑ ^ 2 := hQ.enorm.pow_const 2
  have hIm : Measurable I := (hQ2.comp measurable_swap).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hswap : ∫⁻ ζ, I ζ ∂(P N) = ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ζ,
      ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2 ∂(P N) :=
    lintegral_lintegral_swap (hQ2.comp measurable_swap).aemeasurable
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ‖ₑ ^ 2
      ∂(P N) ≤ ENNReal.ofReal C ^ 2 := by
    intro t ht
    have hsm_t : AEStronglyMeasurable (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) (P N) :=
      (hQ.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
    rw [s94_lintegral_sq_eq hsm_t]
    have hb2 := (hC t ht N hN (kf t) (hk t ht)).2
    have e2 : ENNReal.ofReal 2 = 2 := by norm_num
    rw [e2] at hb2
    exact pow_le_pow_left' hb2 2
  have hfin : ∫⁻ ζ, I ζ ∂(P N) < ⊤ := by
    rw [hswap]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hbd) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)
  filter_upwards [ae_lt_top hIm hfin.ne] with ζ hζ
  have hsm : AEStronglyMeasurable (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (hQ.comp (measurable_prodMk_right (y := ζ))).aestronglyMeasurable
  have := s94_lintegral_sq_eq hsm
  have h2 : eLpNorm (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) ^ 2 < ⊤ := by rw [← this]; exact hζ
  by_contra hne
  have htop : eLpNorm (fun t => r2QuadFluct (Whole.withDensityReal ρ) kf (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) = ⊤ := by
    by_contra h'
    exact hne (lt_top_iff_ne_top.2 h')
  rw [htop] at h2
  simp at h2

theorem s94_pair_enorm_sq {V : Type*} [NormedAddCommGroup V] {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (c : V) :
    ‖((r2L2Path T f, c) : R2L2 T × V) - (r2L2Path T g, c)‖ₑ ^ 2 = ∫⁻ t in Set.Icc (0 : ℝ) T, ‖f t - g t‖ₑ ^ 2 := by
  have hfg : MemLp (fun t => f t - g t) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := hf.sub hg
  have h1 : ‖((r2L2Path T f, c) : R2L2 T × V) - (r2L2Path T g, c)‖ = ‖r2L2Path T (fun t => f t - g t)‖ := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, ← s94_r2L2Path_sub hf hg, norm_zero]
    exact max_eq_left (norm_nonneg _)
  have h2 : ‖r2L2Path T (fun t => f t - g t)‖ = (eLpNorm (fun t => f t - g t) 2
      (volume.restrict (Set.Icc (0 : ℝ) T))).toReal := by
    rw [s94_r2L2Path_eq hfg]
    exact Lp.norm_toLp _ _
  rw [← ofReal_norm_eq_enorm, h1, h2, ENNReal.ofReal_toReal hfg.eLpNorm_ne_top,
    ← s94_lintegral_sq_eq hfg.aestronglyMeasurable]

end Bridges

end HRS.MS.R2Chaos
