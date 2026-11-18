import HRS.MS.R2ChaosAux23

/-!
# HRS.MS.R2ChaosAux24 -- convergence in law for finite-rank kernels (assembly)

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
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

section FlatTid

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_measurable_FRfamily {n : ℕ} {C : ℝ → Fin n → Fin n → ℝ} (hCm : ∀ a b, Measurable fun t => C t a b)
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    Measurable fun q : ℝ × Euc d × Euc d => r2FiniteRankKernel (C q.1) u q.2.1 q.2.2 := by
  unfold r2FiniteRankKernel
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((((hCm a b).comp measurable_fst).mul
    ((s94_test_continuous (hu a)).measurable.comp (measurable_fst.comp measurable_snd))).mul
    ((s94_test_continuous (hu b)).measurable.comp (measurable_snd.comp measurable_snd)))

theorem s94_flat_tid (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 ≤ T) {n : ℕ}
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) {C : ℝ → Fin n → Fin n → ℝ}
    (hCm : ∀ a b, Measurable fun t => C t a b) {K0 : ℝ} (hK0 : 0 ≤ K0) (hCb : ∀ t a b, |C t a b| ≤ K0)
    (hCs : ∀ t a b, C t a b = C t b a) {k' : ℕ} {aa : Fin k' → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) :
    TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
          (P N) (X N) t ζ), fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
      atTop (fun ζ => (r2L2Path T (fun t => s94Flim ξ P' C u t ζ), fun i => ξ (aa i) ζ)) P P' := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨ε, hε0, hεb⟩ := s94_flat_approx hd hs0 hs hb hp hρ hset hT hu hCm hK0 hCb hCs
  obtain ⟨K1, hK1, -, hbL⟩ := s94mN_bdd hd hs0 hs hb hp hρ hset (coef := s94coef C) hK0
    (s94coef_abs_le hK0 hCb) (ua := fun q => u q.1) (ub := fun q => u q.2) (fun q => hu q.1) (fun q => hu q.2)
  have hΨc : Continuous (s94Psi (T := T) C) :=
    s94_Psi_continuous hT (s94coef_measurable hCm) hK0 (s94coef_abs_le hK0 hCb) Prod.fst Prod.snd
  have hmL : MemLp (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    s94_memLp_of_bdd (s94mL_measurable ξ hset.measξ P' (s94coef_measurable hCm) _ _) hbL
  set mfix := r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) with hmfix
  set G : (Fin (n + k') → C(Set.Icc (0 : ℝ) T, ℝ)) → R2L2 T × (Fin k' → C(Set.Icc (0 : ℝ) T, ℝ)) :=
    fun w => (s94Psi C (fun a => w (Fin.castAdd k' a)) - mfix, fun i => w (Fin.natAdd n i)) with hG
  have hGc : Continuous G := by
    refine Continuous.prodMk ?_ ?_
    · have hcomp : Continuous fun w : Fin (n + k') → C(Set.Icc (0 : ℝ) T, ℝ) => fun a : Fin n => w (Fin.castAdd k' a) :=
        continuous_pi fun a => continuous_apply (Fin.castAdd k' a)
      exact (hΨc.comp hcomp).sub continuous_const
    · exact continuous_pi fun i => continuous_apply (Fin.natAdd n i)
  have haaa : ∀ j, IsR2Test (Fin.append u aa j) := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun i => ?_) j
    · simpa using hu a
    · simpa using haa i
  have hconv := hset.conv (n + k') (Fin.append u aa) haaa
  have hconv' := hconv.continuous_comp hGc
  have hZeq : ∀ ζ, G (fun j => ξ (Fin.append u aa j) ζ) =
      (r2L2Path T (fun t => s94Flim ξ P' C u t ζ), fun i => ξ (aa i) ζ) := by
    intro ζ
    refine Prod.ext ?_ ?_
    · show s94Psi C (fun a => ξ (Fin.append u aa (Fin.castAdd k' a)) ζ) - mfix = _
      simp only [Fin.append_left]
      have hI : MemLp (s94Intg (s94coef C) Prod.fst Prod.snd (fun a => ξ (u a) ζ)) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        s94Intg_memLp hT (s94coef_measurable hCm) (s94coef_abs_le hK0 hCb) Prod.fst Prod.snd _
      unfold s94Psi
      rw [hmfix, s94_r2L2Path_sub hI hmL]
      refine s94_r2L2Path_congr fun t _ => ?_
      unfold s94Intg s94mL s94Flim s94coef
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    · funext i
      simp [hG, Fin.append_right]
  have hYm : ∀ N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ)
      (fun t => r2FiniteRankKernel (C t) u) (P N) (X N) t ζ) := fun N =>
    s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) (s94_measurable_FRfamily hCm hu) (X N) (hset.measX N))
  have hZm : Measurable fun ζ => r2L2Path T (fun t => s94Flim ξ P' C u t ζ) :=
    s94_measurable_r2L2Path T (fun q : ℝ × Ω' => s94Flim ξ P' C u q.1 q.2) (s94Flim_measurable hset.measξ P' hCm u)
  have hcaa := hset.conv k' aa haa
  refine s94_tid_of_approx (E := R2L2 T × (Fin k' → C(Set.Icc (0 : ℝ) T, ℝ)))
    (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
          (P N) (X N) t ζ), fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
    (fun ζ => (r2L2Path T (fun t => s94Flim ξ P' C u t ζ), fun i => ξ (aa i) ζ))
    (fun _ N ζ => G (fun j => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (Fin.append u aa j) (X N) ζ)))
    (fun _ ζ => (r2L2Path T (fun t => s94Flim ξ P' C u t ζ), fun i => ξ (aa i) ζ))
    (fun N => (hYm N).aemeasurable.prodMk (hcaa.forall_aemeasurable N))
    (hZm.aemeasurable.prodMk (measurable_pi_iff.2 fun i => hset.measξ _).aemeasurable)
    (fun j N => hconv'.forall_aemeasurable N)
    (fun j => (hZm.aemeasurable.prodMk (measurable_pi_iff.2 fun i => hset.measξ _).aemeasurable))
    (fun j => hconv'.congr (fun N => Filter.EventuallyEq.rfl) (ae_of_all _ hZeq))
    (fun j => 1 / ((j : ℝ) + 1)) (fun j => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun j => by simp [← ofReal_norm_eq_enorm]) ?_
  intro j
  have hev : ∀ᶠ N in atTop, ε N ≤ 1 / ((j : ℝ) + 1) :=
    (hε0.eventually (ge_mem_nhds (by positivity)))
  filter_upwards [hev, eventually_ge_atTop 2] with N hN hN2
  refine le_trans (le_of_eq ?_) ((hεb N hN2).trans (ENNReal.ofReal_le_ofReal hN))
  refine lintegral_congr fun ζ => ?_
  congr 1
  have e1 : (G fun j => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (Fin.append u aa j) (X N) ζ)).2 -
      (fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)) = 0 := by
    funext i; simp [hG, Fin.append_right]
  have e0 : (G fun j => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (Fin.append u aa j) (X N) ζ)) -
      (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u) (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)) =
      ((s94Psi C fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) - mfix -
        r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u) (P N) (X N) t ζ),
        (0 : Fin k' → C(Set.Icc (0 : ℝ) T, ℝ))) := by
    refine Prod.ext ?_ e1
    simp only [hG, Fin.append_left, Prod.fst_sub]
  rw [e0, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Prod.norm_def]
  simp

end FlatTid

end HRS.MS.R2Chaos
