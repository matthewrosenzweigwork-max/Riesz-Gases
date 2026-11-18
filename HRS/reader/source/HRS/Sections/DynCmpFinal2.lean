import HRS.Sections.DynCmpFinal
import HRS.PDE.MovFinalConsumers

/-! `dynamic_comparison_proof'`: the proof of `DynCmpFinal` re-run with the sorry-free `dynamic_entropy_proof'` (MOV-FINAL). -/

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison` (final, statement verbatim)

Chain plan: header of `DynCmpAux1.lean`.  The proof uses `dynamic_entropy_proof` (conditional on the sorried MOV statements, see
`DynEntFinal.lean`) for the entropy bounds `H(f^r|Q^r), H(f^r|(μ^r)^{⊗N}) ≤ C₁ B_N`, then `dyncmp_master` (duality identity,
remainder `L¹` bound `C B_N/√N`, Gaussian comparison on the enlargement, bracket error `C √(B_N/N)`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

theorem dynamic_comparison_proof' (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
        ∀ G : Ω → EuclideanSpace ℝ (Fin p),
          law P G = ProbabilityTheory.multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) →
          AEMeasurable G P →
          ProbabilityTheory.IndepFun X₀ G P →
          smoothDist 2
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) :
                  EuclideanSpace ℝ (Fin p)))
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X₀ ω) + G ω a :
                  EuclideanSpace ℝ (Fin p))) ≤
            C * (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N +
                Real.sqrt (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
  have hd1 : 1 ≤ d := by omega
  have htr' : MovTraj htr.dyn T ρ :=
    movT_traj_of_global_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global T
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ :=
    movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global
  obtain ⟨C₁, hC₁0, hC₁⟩ := dynamic_entropy_proof' hd htr T hT
  obtain ⟨Λ, hreg, hjc, hpack⟩ := dyncmp_adjoint_package hd htr T
  choose Cφ hCφ using fun a => hpack (φ a) (hφ a)
  set Cmax : ℝ := ∑ a, |Cφ a| with hCmax
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun a _ => abs_nonneg _
  set L : ℝ := d * Cmax with hLdef
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨Cf, hCf0, hCf⟩ := dyncmp_pair_moment hd1 htr' hc₀ (fun r hr x => (hb r hr.1).1 x)
    (fun r hr => (hb r hr.1).2) hL0
  set K₂ : ℝ := ∑ a : Fin p, ∑ b : Fin p, 2 * β⁻¹ * (L * Real.exp T) * (L * Real.exp T) / (2 * 1) with hK₂
  have hK₂0 : 0 ≤ K₂ := by
    have := htr.hβ
    positivity
  refine ⟨T * p * Cf * (C₁ + 1) + (1 / 2) * K₂ * Real.sqrt (2 * (C₁ + 1)), by positivity, ?_⟩
  intro N hN Ω _ P _ X₀ W X hP hfilt hfin t ht G hG hGm hind
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ℱ, W', hF⟩ := hfilt
  have e : ∀ r, movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) := fun r =>
    movT_Q_eq_beta (g := periodicRiesz d s) rfl N ρ r
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal := ENNReal.toReal_nonneg
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hBge : (N : ℝ) * deltaN d s N ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hentboth := fun r (hr : r ∈ Set.Icc (0 : ℝ) T) => hC₁ N hN P X₀ W X hP ⟨ℱ, W', hF⟩ hfin r hr
  have hentQ : ∀ r ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X r.toNNReal))
      (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r) ≤ ENNReal.ofReal (C₁ * B) := by
    intro r hr
    rw [e]
    exact le_trans le_self_add (hentboth r hr)
  have hentP : ∀ r ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X r.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≤ ENNReal.ofReal (C₁ * B) := fun r hr =>
    le_trans le_add_self (hentboth r hr)
  have hH₁ : 0 ≤ C₁ * B := by positivity
  have hBge' : (N : ℝ) * deltaN d htr.dyn.s N ≤ B := hBge
  have hδ' : 1 ≤ (N : ℝ) * deltaN d htr.dyn.s N := hδ
  have hcl : ∀ a, IsClassicalAdjointSolution htr.dyn ρ (t a) (φ a)
      (fun r => propagator htr.dyn ρ r (t a) (φ a)) := fun a => (hCφ a (t a) (ht a)).1
  have hgrad : ∀ a, ∀ r ∈ Set.Icc 0 (t a), ∀ x,
      ‖Torus.grad (propagator htr.dyn ρ r (t a) (φ a)) x‖ ≤ L := by
    intro a r hr x
    have hck : Torus.IsCk 2 (propagator htr.dyn ρ r (t a) (φ a)) := (hcl a).c2 r hr
    refine (dyncmp_norm_grad_le hck x).trans ?_
    have h1 := (hCφ a (t a) (ht a)).2 r hr
    have h2 : |Cφ a| ≤ Cmax := Finset.single_le_sum (f := fun a => |Cφ a|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc (d : ℝ) * Torus.cbNorm 2 (propagator htr.dyn ρ r (t a) (φ a)) ≤ d * Cmax :=
          mul_le_mul_of_nonneg_left (h1.trans ((le_abs_self _).trans h2)) hd0
      _ = L := rfl
  have hLip : ∀ a, ∀ r ∈ Set.Icc 0 (t a), IsLipschitzVF L
      (Torus.grad (propagator htr.dyn ρ r (t a) (φ a))) := by
    intro a r hr
    have hck : Torus.IsCk 2 (propagator htr.dyn ρ r (t a) (φ a)) := (hcl a).c2 r hr
    refine mova_isLipschitzVF_mono ?_ (dyncmp_lip_grad hck)
    have h1 := (hCφ a (t a) (ht a)).2 r hr
    have h2 : |Cφ a| ≤ Cmax := Finset.single_le_sum (f := fun a => |Cφ a|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    exact mul_le_mul_of_nonneg_left (h1.trans ((le_abs_self _).trans h2)) hd0
  have hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω := hP.sol.init
  have hind' : IndepFun (X 0) G P := hind.congr (hX0.mono fun ω h => h.symm) Filter.EventuallyEq.rfl
  have hmaster := dyncmp_master hd htr hT htr' hN hP.sol hF hH₁ hentQ hentP hCf0
    (fun r hr v hv => ⟨(hCf N hN r hr v hv).1, fun ν hν hH => ((hCf N hN r hr v hv).2 ν hν hH).1⟩) t ht φ hφ (fun _ => L) (fun _ => hL0) hcl hgrad hLip G hGm hG hind'
  have hlawX : (law P fun ω => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X 0 ω) + G ω a :
        EuclideanSpace ℝ (Fin p))) =
      law P fun ω => (WithLp.toLp 2 fun a =>
        linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X₀ ω) + G ω a :
          EuclideanSpace ℝ (Fin p)) :=
    Measure.map_congr (hX0.mono fun ω h => by simp only [h])
  rw [hlawX] at hmaster
  refine hmaster.trans ?_
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hBnn : 0 ≤ B := by linarith
  have hx : 0 ≤ B / Real.sqrt N := by positivity
  have hy : 0 ≤ Real.sqrt (B / N) := Real.sqrt_nonneg _
  have hHN : C₁ * B + N * deltaN d htr.dyn.s N ≤ (C₁ + 1) * B := by nlinarith [hBge']
  have h1 : ∑ a, t a * (Cf * (C₁ * B + N * deltaN d htr.dyn.s N)) / Real.sqrt N ≤
      (T * p * Cf * (C₁ + 1)) * (B / Real.sqrt N) := by
    calc ∑ a, t a * (Cf * (C₁ * B + N * deltaN d htr.dyn.s N)) / Real.sqrt N
        ≤ ∑ _a : Fin p, T * (Cf * ((C₁ + 1) * B)) / Real.sqrt N := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hta0 : 0 ≤ t a := (ht a).1
          have htaT : t a ≤ T := (ht a).2
          have hin : 0 ≤ Cf * (C₁ * B + N * deltaN d htr.dyn.s N) := by
            have : 0 ≤ C₁ * B + N * deltaN d htr.dyn.s N := by linarith [hH₁, hδ']
            positivity
          have h2 : Cf * (C₁ * B + N * deltaN d htr.dyn.s N) ≤ Cf * ((C₁ + 1) * B) :=
            mul_le_mul_of_nonneg_left hHN hCf0
          have h3 : t a * (Cf * (C₁ * B + N * deltaN d htr.dyn.s N)) ≤ T * (Cf * ((C₁ + 1) * B)) :=
            mul_le_mul htaT h2 hin hT
          exact div_le_div_of_nonneg_right h3 hsq.le
      _ = (T * p * Cf * (C₁ + 1)) * (B / Real.sqrt N) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hlog : Real.log 2 ≤ B := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h2 : Real.sqrt (2 * (C₁ * B + Real.log 2) / N) ≤ Real.sqrt (2 * (C₁ + 1)) * Real.sqrt (B / N) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : 2 * (C₁ + 1) * (B / N) = 2 * ((C₁ + 1) * B) / N := by ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ hNr.le
    nlinarith
  have h3 : (1 / 2 : ℝ) * (K₂ * Real.sqrt (2 * (C₁ * B + Real.log 2) / N)) ≤
      ((1 / 2) * K₂ * Real.sqrt (2 * (C₁ + 1))) * Real.sqrt (B / N) := by
    calc (1 / 2 : ℝ) * (K₂ * Real.sqrt (2 * (C₁ * B + Real.log 2) / N))
        ≤ (1 / 2 : ℝ) * (K₂ * (Real.sqrt (2 * (C₁ + 1)) * Real.sqrt (B / N))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK₂0) (by norm_num)
      _ = _ := by ring
  have hA1 : 0 ≤ T * p * Cf * (C₁ + 1) := by positivity
  have hA2 : 0 ≤ (1 / 2) * K₂ * Real.sqrt (2 * (C₁ + 1)) := by positivity
  calc _ ≤ (T * p * Cf * (C₁ + 1)) * (B / Real.sqrt N) +
        ((1 / 2) * K₂ * Real.sqrt (2 * (C₁ + 1))) * Real.sqrt (B / N) := add_le_add h1 h3
    _ ≤ (T * p * Cf * (C₁ + 1) + (1 / 2) * K₂ * Real.sqrt (2 * (C₁ + 1))) *
        (B / Real.sqrt N + Real.sqrt (B / N)) := by
        nlinarith [mul_nonneg hA1 hy, mul_nonneg hA2 hx]

example := (@dynamic_comparison_proof' : type_of% @HRS.dynamic_comparison)

end HRS

end
