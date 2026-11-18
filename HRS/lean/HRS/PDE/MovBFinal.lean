import HRS.PDE.MovBAux5

/-!
# MOVB: relocated proof of `movT_reg_ineq` (MovSpec1.lean:486)

Statement verbatim; tied to the original by `type_of%`.  Route: `MovBAux1`-`MovBAux5` (see the plan in `MovBAux1`):
the tilt `ψ^r = ∑_i movT_phi` is `C^{1,2}` (`movb_isC12Test_*`), `q^r = Q^M_r` (`movb_Q_eq_gibbs`), D2 + D3 give the level-`k`
inequality for the smooth `V_k` (`movb_reg_ineq_smooth`), and `k → ∞` is `movb_reg_ineq_pos`; the case `t = 0` is trivial and
the integrability conclusions follow from the joint continuity of `movT_srcReg` (`movb_srcReg_cont`).  No defect found in the
statement (the `T = 0` case is harmless: `ρt 0` is continuous by `cont_time_deriv`, and `Icc 0 0` is null).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movT_reg_ineq_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (M : ℝ) (hM : 0 ≤ M) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    (hfin : relEntropy (selectedLaw P (b15c_regProcess Y) 0)
      (movT_Q (b15c_gReg d D.s M) D N ρ 0) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ ∧
      (∀ r ∈ Set.Icc 0 t, Integrable (movT_srcReg D N M ρ ρt r) (selectedLaw P (b15c_regProcess Y) r)) ∧
      IntegrableOn (fun r => ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r))
        (Set.Icc 0 t) ∧
      (relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t)).toReal ≤
        (relEntropy (selectedLaw P (b15c_regProcess Y) 0) (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r) := by
  intro t ht
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hN0 : 0 < N := by omega
  have hNd : 1 ≤ N * d := Nat.mul_pos hN0 (b15_one_le_d D)
  have hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r) := fun r hr => htr.mf.density r hr
  have hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x := htr.pos
  have hSc : Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => movT_srcReg D N M ρ ρt p.1 p.2 :=
    movb_srcReg_cont hN0 D htr.gradient htr.pos_temp htr.V_reg M hρt hdens hpos
  have hprob : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hint : ∀ r ∈ Set.Icc 0 t, Integrable (movT_srcReg D N M ρ ρt r) (selectedLaw P (b15c_regProcess Y) r) := by
    intro r hr
    haveI := hprob r
    exact (movb_slice_of_joint (S := movT_srcReg D N M ρ ρt) hSc ⟨hr.1, hr.2.trans ht.2⟩).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFc : ContinuousOn (fun r => ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r))
      (Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact movb_cont_integral hY hT0 hSc
  have hFint : IntegrableOn (fun r => ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r))
      (Set.Icc 0 t) :=
    (hFc.mono (Set.Icc_subset_Icc_right ht.2)).integrableOn_Icc
  rcases ht.1.eq_or_lt with h0 | hpos0
  · subst h0
    have hz : ∫ r in Set.Icc (0 : ℝ) 0, ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r) = 0 := by
      rw [Set.Icc_self]
      exact setIntegral_measure_zero _ (by simp)
    refine ⟨hfin, hint, hFint, ?_⟩
    rw [hz, add_zero]
  · have hTpos : 0 < T := hpos0.trans_le ht.2
    obtain ⟨h1, h4⟩ := movb_reg_ineq_pos hN0 hNd hW' D htr.gradient htr.pos_temp htr.V_reg hTpos hρt hdens
      hpos M hY₀ hY hfin ht
    exact ⟨h1, hint, hFint, h4⟩

example := (@movT_reg_ineq_proof : type_of% @HRS.movT_reg_ineq)

end HRS
