import HRS.MC.S7FCF5Defs
import HRS.MC.S7FCF5A1
import HRS.MC.S7FCW7Aux

/-!
# Block A4 of packet `fcf5`: joint measurability of the mode statistic and of the commutator term

Proofs of `fcf5_A4a_eta_meas` and `fcf5_A4b_comm_meas` (`S7FCF5Plan.lean`), with the statements copied verbatim.

* A4a: `(u,ω) ↦ η_N^{max u 0}(G_{max u 0})(ω)`.  The empirical part is a finite sum of `G(max u 0)(X_i(u,ω))`, jointly
  measurable by `measurable_of_progressive` (`hF.progressive` of the filtered solution) and the joint measurability of
  `G`; the mean-field part is `∫ G(max u 0,y) ρ^{max u 0}(y) dy`, a parametric integral (`A1` gives joint continuity of
  `(u,y) ↦ ρ^{max u 0}(y)`).
* A4b: `(u,ω) ↦ N F_N^{h_f}(X_{max u 0}, μ^{max u 0})` written out as `(2N²)⁻¹ ∑_{i≠j} h_f(X_i,X_j)`,
  `N⁻¹ ∑_i ∫ h_f(X_i,y) ρ^{max u 0}(y) dy` and `½ ∬ h_f dμ dμ`, each jointly measurable by the same parametric
  integration lemma.

Namespace `HRS.MC.Sec7.S7FCF5D`, theorems `<name>_proof`, helpers prefixed `S7FCF5D_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5D

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW7
  HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- Parametric integration: the integral over the torus of a jointly measurable integrand is measurable in the
outer variable. -/
theorem S7FCF5D_meas_int {α : Type} [MeasurableSpace α] {F : α × Torus d → ℝ} (hF : Measurable F) :
    Measurable (fun a : α => ∫ y, F (a, y)) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- `(u,y) ↦ ρ^{max u 0}(y)` is jointly measurable (`A1`). -/
theorem S7FCF5D_rho_meas (R : Regime d) :
    Measurable (fun p : ℝ × Torus d => R.ρ (max p.1 0) p.2) := by
  have hmap : Continuous (fun q : ℝ × Torus d => (max q.1 0, q.2)) :=
    (continuous_fst.max continuous_const).prodMk continuous_snd
  have hc : Continuous (fun q : ℝ × Torus d => R.ρ (max q.1 0) q.2) :=
    (HRS.MC.Sec7.S7FCF5A.fcf5_A1_rho_cont_proof R).comp_continuous hmap
      (fun q => ⟨Set.mem_Ici.2 (le_max_right _ _), Set.mem_univ _⟩)
  exact hc.measurable

/-- The densities `ρ^{max u 0}` are nonnegative. -/
theorem S7FCF5D_rho_nonneg (R : Regime d) : ∀ u y, 0 ≤ R.ρ (max u 0) y := by
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  exact fun u y => hm₀.le.trans (hb (max u 0) (le_max_right _ _) y).1

/-- Integral against the mean-field measure `ρ^{max u 0} dx` as a Lebesgue integral with weight. -/
theorem S7FCF5D_int_dens (R : Regime d) (u : ℝ) (f : Torus d → ℝ) :
    ∫ y, f y ∂(withDensityReal (R.ρ (max u 0))) = ∫ y, R.ρ (max u 0) y * f y :=
  HRS.PDE.MFPairing.integral_withDensityReal
    (HRS.MC.Sec7.S7FCF5A.S7FCF5A_rho_cont_x R (le_max_right u 0)).measurable
    (S7FCF5D_rho_nonneg R u) f

/-- The Borel structure of the configuration space (as in `KIDAux7`). -/
instance S7FCF5D_borelConfig {N : ℕ} : BorelSpace (Fin N → Torus d) := Pi.borelSpace

/-- Composition of the jointly measurable `h_f` with two measurable maps (syntactic unification only). -/
theorem S7FCF5D_hT_comp {α : Type} [MeasurableSpace α] {s : ℝ} {f : Torus d → ℝ}
    (hT : Measurable (fun q : Torus d × Torus d => hTransport d s f q.1 q.2))
    {a b : α → Torus d} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p => hTransport d s f (a p) (b p)) :=
  Measurable.comp (g := fun q : Torus d × Torus d => hTransport d s f q.1 q.2)
    (f := fun p => (a p, b p)) hT (ha.prodMk hb)

/-- The configuration `(u,ω) ↦ X_{max u 0}(ω)` is jointly measurable (progressive measurability of the filtered
solution). -/
theorem S7FCF5D_Y_meas {N : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hF : ∃ (ℱ : MeasureTheory.Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution P ℱ W' W X) :
    Measurable (fun p : ℝ × Ω => X (max p.1 0).toNNReal p.2) := by
  obtain ⟨ℱ, W', h⟩ := hF
  exact (HRS.measurable_of_progressive h.progressive).comp
    ((measurable_fst.max measurable_const).prodMk measurable_snd)

/-- The double integral against `μ^{max u 0}` written with the Lebesgue weight. -/
theorem S7FCF5D_double (R : Regime d) (u : ℝ) (h : Torus d → Torus d → ℝ) :
    ∫ x, ∫ y, h x y ∂(withDensityReal (R.ρ (max u 0))) ∂(withDensityReal (R.ρ (max u 0))) =
      ∫ x, R.ρ (max u 0) x * ∫ y, R.ρ (max u 0) y * h x y := by
  rw [S7FCF5D_int_dens R u]
  congr 1
  funext x
  rw [S7FCF5D_int_dens R u (h x)]

/-- Measurability of the mode statistic `η^u(G_u)` in `(u,ω)` (proof of `fcf5_A4a_eta_meas`). -/
theorem fcf5_A4a_eta_meas_proof (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) (G : ℝ → Torus d → ℝ) (hG : Measurable (Function.uncurry G))
    (B : ℝ) (hB : ∀ u x, |G u x| ≤ B) :
    Measurable (fun p : ℝ × Ω => fcf5Eta R X (G (max p.1 0)) (max p.1 0) p.2) := by
  have hY : Measurable (fun p : ℝ × Ω => X (max p.1 0).toNNReal p.2) :=
    S7FCF5D_Y_meas hreal.filtered
  have hGm : ∀ u : ℝ, Measurable (G u) := fun u =>
    hG.comp (measurable_const.prodMk measurable_id)
  have hE1 : Measurable (fun p : ℝ × Ω =>
      (N : ℝ)⁻¹ * ∑ i, G (max p.1 0) (X (max p.1 0).toNNReal p.2 i)) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact hG.comp ((measurable_fst.max measurable_const).prodMk ((measurable_pi_apply i).comp hY))
  have hJ : Measurable (fun u : ℝ => ∫ y, R.ρ (max u 0) y * G (max u 0) y) := by
    have hF : Measurable (fun z : ℝ × Torus d => R.ρ (max z.1 0) z.2 * G (max z.1 0) z.2) :=
      (S7FCF5D_rho_meas R).mul (hG.comp ((measurable_fst.max measurable_const).prodMk measurable_snd))
    exact S7FCF5D_meas_int hF
  have hEq : ∀ p : ℝ × Ω, fcf5Eta R X (G (max p.1 0)) (max p.1 0) p.2 =
      Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, G (max p.1 0) (X (max p.1 0).toNNReal p.2 i)
        - ∫ y, R.ρ (max p.1 0) y * G (max p.1 0) y) := by
    intro p
    unfold fcf5Eta pair
    rw [s7fcw7_int_emp (X (max p.1 0).toNNReal p.2) (hGm (max p.1 0)),
      S7FCF5D_int_dens R p.1 (G (max p.1 0))]
  have hfun : (fun p : ℝ × Ω => fcf5Eta R X (G (max p.1 0)) (max p.1 0) p.2) =
      fun p : ℝ × Ω => Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, G (max p.1 0) (X (max p.1 0).toNNReal p.2 i)
        - (fun u : ℝ => ∫ y, R.ρ (max u 0) y * G (max u 0) y) p.1) :=
    funext hEq
  rw [hfun]
  exact measurable_const.mul (hE1.sub (hJ.comp measurable_fst))


/-- Measurability of the commutator term `N F_N^{h_f}(X_{max u 0}, μ^{max u 0})` in `(u,ω)`
(proof of `fcf5_A4b_comm_meas`). -/
theorem fcf5_A4b_comm_meas_proof (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Measurable (fun p : ℝ × Ω => fcf5Comm R X f (max p.1 0) p.2) := by
  have hY : Measurable (fun p : ℝ × Ω => X (max p.1 0).toNNReal p.2) :=
    S7FCF5D_Y_meas hreal.filtered
  have hT2 : Measurable (fun q : Torus d × Torus d => hTransport d R.D.s f q.1 q.2) :=
    s7fcw7_hT_meas (s7fcw7_sd R.hd R.hs) hf
  -- first term: the pair sum over `i ≠ j`
  have hT1 : Measurable (fun p : ℝ × Ω => ∑ i, ∑ j ∈ Finset.univ.erase i,
      hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) (X (max p.1 0).toNNReal p.2 j)) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact S7FCF5D_hT_comp hT2 ((measurable_pi_apply i).comp hY) ((measurable_pi_apply j).comp hY)
  -- second term: the mean-field interaction of each particle
  have hF2 : ∀ i : Fin N, Measurable (fun z : (ℝ × Ω) × Torus d =>
      R.ρ (max z.1.1 0) z.2 * hTransport d R.D.s f (X (max z.1.1 0).toNNReal z.1.2 i) z.2) := fun i =>
    ((S7FCF5D_rho_meas R).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (S7FCF5D_hT_comp hT2 ((measurable_pi_apply i).comp (hY.comp measurable_fst)) measurable_snd)
  have hT2eq : ∀ p : ℝ × Ω, ∑ i, ∫ y, hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) y
      ∂(withDensityReal (R.ρ (max p.1 0))) =
        ∑ i, ∫ y, R.ρ (max p.1 0) y * hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) y :=
    fun p => Finset.sum_congr rfl fun i _ => S7FCF5D_int_dens R p.1 _
  have hT2m : Measurable (fun p : ℝ × Ω => ∑ i, ∫ y, R.ρ (max p.1 0) y *
      hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) y) :=
    Finset.measurable_sum _ fun i _ => S7FCF5D_meas_int (hF2 i)
  -- third term: the double integral against `μ^u`, as a function of the time `u`
  have hK2 : Measurable (fun z : (ℝ × Torus d) × Torus d =>
      R.ρ (max z.1.1 0) z.2 * hTransport d R.D.s f z.1.2 z.2) :=
    ((S7FCF5D_rho_meas R).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (S7FCF5D_hT_comp hT2 (measurable_snd.comp measurable_fst) measurable_snd)
  have hF3 : Measurable (fun z : ℝ × Torus d =>
      R.ρ (max z.1 0) z.2 * ∫ y, R.ρ (max z.1 0) y * hTransport d R.D.s f z.2 y) :=
    (S7FCF5D_rho_meas R).mul (S7FCF5D_meas_int hK2)
  have hJm : Measurable (fun u : ℝ => ∫ x, R.ρ (max u 0) x *
      ∫ y, R.ρ (max u 0) y * hTransport d R.D.s f x y) :=
    S7FCF5D_meas_int hF3
  have hfun : (fun p : ℝ × Ω => fcf5Comm R X f (max p.1 0) p.2) = fun p : ℝ × Ω =>
      (N : ℝ) * ((1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) (X (max p.1 0).toNNReal p.2 j))
        - (1 / (N : ℝ)) * (∑ i, ∫ y, R.ρ (max p.1 0) y *
          hTransport d R.D.s f (X (max p.1 0).toNNReal p.2 i) y)
        + (1 / 2) * ∫ x, R.ρ (max p.1 0) x * ∫ y, R.ρ (max p.1 0) y * hTransport d R.D.s f x y) := by
    funext p
    unfold fcf5Comm modulatedEnergy
    rw [S7FCF5D_double R p.1 (hTransport d R.D.s f), hT2eq p]
  rw [hfun]
  exact measurable_const.mul (((measurable_const.mul hT1).sub (measurable_const.mul hT2m)).add
    (measurable_const.mul (hJm.comp measurable_fst)))

end HRS.MC.Sec7.S7FCF5D
