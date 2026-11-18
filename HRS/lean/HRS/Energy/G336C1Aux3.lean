import HRS.Energy.G336C1Aux2
import HRS.Stochastic.Particle
import HRS.Duality.PairingExpansion

/-!
# G336C1, helper file 3: self-forces and the microscopic term along a `GoodKernel` family

Convergence and bounds for `convGradConv G_n h x`, `selfForce G_n ρ X i` and
`microTerm D h_n ρ X` (with `∇h_n = G_n → G = ∇g`), uniformly in the collision-free configuration `X`
(through a lower bound `a` of `‖X i - X j‖`), and the sign `micro_g ≤ 0` for `SymNonpos`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

section SelfForce

variable {s C Lh B : ℝ} {Gn : ℕ → Torus d → Euc d} {G : Torus d → Euc d} {h : Torus d → ℝ}

theorem g336c1_convGradConv_tendsto (hGn : ∀ n, KernelGrad.GoodKernel d s C (Gn n))
    (hG : KernelGrad.GoodKernel d s C G)
    (hlim : ∀ z : Torus d, z ≠ 0 → Tendsto (fun n => Gn n z) atTop (𝓝 (G z)))
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hL : KernelGrad.IsLipschitz Lh h) (hL0 : 0 ≤ Lh)
    (hB0 : 0 ≤ B) (x : Torus d) :
    Tendsto (fun n => convGradConv (Gn n) h x) atTop (𝓝 (convGradConv G h x)) := by
  simp_rw [KernelGrad.convGradConv_eq_integral_kern]
  refine tendsto_integral_of_dominated_convergence (KernelGrad.dom s C Lh B d)
    (fun n => (KernelGrad.measurable_kern (hGn n) hh x).aestronglyMeasurable)
    (KernelGrad.integrable_dom hG Lh B) (fun n => KernelGrad.kern_bound_ae (hGn n) hB hL hL0 hB0 x) ?_
  filter_upwards [KernelGrad.torus_ae_ne' hG.pos] with z hz
  unfold KernelGrad.kern
  split_ifs
  · exact tendsto_const_nhds.smul (hlim z hz)
  · exact tendsto_const_nhds.smul (hlim z hz)

theorem g336c1_selfForce_tendsto (hGn : ∀ n, KernelGrad.GoodKernel d s C (Gn n))
    (hG : KernelGrad.GoodKernel d s C G)
    (hlim : ∀ z : Torus d, z ≠ 0 → Tendsto (fun n => Gn n z) atTop (𝓝 (G z)))
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hL : KernelGrad.IsLipschitz Lh h) (hL0 : 0 ≤ Lh)
    (hB0 : 0 ≤ B) (X : Config d N) (hX : X ∉ collisionSet d N) (i : Fin N) :
    Tendsto (fun n => selfForce (Gn n) h X i) atTop (𝓝 (selfForce G h X i)) := by
  unfold selfForce
  refine Tendsto.sub (Tendsto.const_smul (tendsto_finset_sum _ fun j hj => ?_) _)
    (g336c1_convGradConv_tendsto hGn hG hlim hh hB hL hL0 hB0 (X i))
  have hij : X i ≠ X j := fun h' => hX ⟨i, j, (Finset.mem_erase.mp hj).1.symm, h'⟩
  exact hlim (X i - X j) (sub_ne_zero.mpr hij)

/-- The bound for the self-force. -/
def g336c1_sfB (d : ℕ) (s C Lh B a : ℝ) : ℝ :=
  C * (a ^ (-s - 1) + 1) + (Lh * KernelGrad.opM1 d s C + B * KernelGrad.opM2 s C)

theorem g336c1_selfForce_bound (hG : KernelGrad.GoodKernel d s C G)
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hL : KernelGrad.IsLipschitz Lh h) (hL0 : 0 ≤ Lh)
    (hB0 : 0 ≤ B) {a : ℝ} (ha : 0 < a) (hN : 0 < N) (X : Config d N)
    (hXa : ∀ i j, i ≠ j → a ≤ ‖X i - X j‖) (i : Fin N) :
    ‖selfForce G h X i‖ ≤ g336c1_sfB d s C Lh B a := by
  unfold selfForce g336c1_sfB
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hG.bound_op h B Lh hh hB hL hL0 hB0 (X i)))
  have hs0 := hG.hs0
  have hC0 := hG.hC0
  have hk : ∀ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖ ≤ C * (a ^ (-s - 1) + 1) := by
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hz : X i - X j ≠ 0 := by
      intro h0
      have := hXa i j hij
      rw [h0, norm_zero] at this
      linarith
    refine (hG.bound_norm _ hz).trans ?_
    have : ‖X i - X j‖ ^ (-s - 1) ≤ a ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos ha (hXa i j hij) (by linarith)
    gcongr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖∑ j ∈ Finset.univ.erase i, G (X i - X j)‖ ≤
      ((Finset.univ.erase i).card : ℝ) * (C * (a ^ (-s - 1) + 1)) :=
    (norm_sum_le _ _).trans (by
      calc ∑ j ∈ Finset.univ.erase i, ‖G (X i - X j)‖
          ≤ ∑ _j ∈ Finset.univ.erase i, C * (a ^ (-s - 1) + 1) := Finset.sum_le_sum hk
        _ = _ := by simp)
  have hcard : ((Finset.univ.erase i).card : ℝ) ≤ N := by
    have : (Finset.univ.erase i).card ≤ N := by
      simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
    exact_mod_cast this
  have hpos : 0 ≤ C * (a ^ (-s - 1) + 1) := by
    have := Real.rpow_nonneg ha.le (-s - 1)
    positivity
  calc 1 / (N : ℝ) * ‖∑ j ∈ Finset.univ.erase i, G (X i - X j)‖
      ≤ 1 / (N : ℝ) * ((N : ℝ) * (C * (a ^ (-s - 1) + 1))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right hcard hpos
    _ = C * (a ^ (-s - 1) + 1) := by field_simp

end SelfForce

section Micro

variable {s C Lh B : ℝ} {hn : ℕ → Torus d → ℝ} {ρ : Torus d → ℝ}

/-- The limit microscopic term `N⁻¹ ∑_i a_iᵀ M a_i` (`a_i` the self-force of `∇g`). -/
def g336c1_microG (D : DynData d) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce (periodicRieszGrad d D.s) ρ X i)
    (Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) ρ X i))

theorem g336c1_microG_nonpos {D : DynData d} (hS : Torus.SymNonpos D.M) (ρ : Torus d → ℝ)
    (X : Config d N) : g336c1_microG D ρ X ≤ 0 := by
  unfold g336c1_microG
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun i _ => ?_)
  exact inner_matVec_nonpos hS _

theorem g336c1_micro_tendsto (D : DynData d) (hGn : ∀ n, KernelGrad.GoodKernel d D.s C (Torus.grad (hn n)))
    (hG : KernelGrad.GoodKernel d D.s C (periodicRieszGrad d D.s))
    (hlim : ∀ z : Torus d, z ≠ 0 →
      Tendsto (fun n => Torus.grad (hn n) z) atTop (𝓝 (periodicRieszGrad d D.s z)))
    (hh : Measurable ρ) (hB : ∀ x, |ρ x| ≤ B) (hL : KernelGrad.IsLipschitz Lh ρ) (hL0 : 0 ≤ Lh)
    (hB0 : 0 ≤ B) (X : Config d N) (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => microTerm D (hn n) ρ X) atTop (𝓝 (g336c1_microG D ρ X)) := by
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  unfold microTerm g336c1_microG
  refine Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => ?_)
  have h1 := g336c1_selfForce_tendsto hGn hG hlim hh hB hL hL0 hB0 X hX i
  have h2 : Tendsto (fun _ : ℕ => selfForce (periodicRieszGrad d D.s) ρ X i) atTop
      (𝓝 (selfForce (periodicRieszGrad d D.s) ρ X i)) := tendsto_const_nhds
  exact h1.inner ((hmat.tendsto _).comp h2)

/-- Bound for the microscopic term. -/
def g336c1_microB (d : ℕ) (cM s C Lh B a : ℝ) : ℝ := cM * g336c1_sfB d s C Lh B a * g336c1_sfB d s C Lh B a

theorem g336c1_micro_bound (D : DynData d) {cM : ℝ} (hcM0 : 0 ≤ cM)
    (hcM : ∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ cM * ‖v‖) {G1 G2 : Torus d → Euc d}
    (hG1 : KernelGrad.GoodKernel d D.s C G1) (hG2 : KernelGrad.GoodKernel d D.s C G2)
    (hh : Measurable ρ) (hB : ∀ x, |ρ x| ≤ B) (hL : KernelGrad.IsLipschitz Lh ρ) (hL0 : 0 ≤ Lh)
    (hB0 : 0 ≤ B) {a : ℝ} (ha : 0 < a) (hN : 0 < N) (X : Config d N)
    (hXa : ∀ i j, i ≠ j → a ≤ ‖X i - X j‖) :
    |(1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce G1 ρ X i) (Torus.matVec D.M (selfForce G2 ρ X i))|
      ≤ g336c1_microB d cM D.s C Lh B a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S := g336c1_sfB d D.s C Lh B a with hS
  have hS0 : 0 ≤ S := by
    have h1 := g336c1_selfForce_bound hG1 hh hB hL hL0 hB0 ha hN X hXa ⟨0, hN⟩
    exact (norm_nonneg _).trans h1
  have hk : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      |inner ℝ (selfForce G1 ρ X i) (Torus.matVec D.M (selfForce G2 ρ X i))| ≤ cM * S * S := by
    intro i _
    have h1 := g336c1_selfForce_bound hG1 hh hB hL hL0 hB0 ha hN X hXa i
    have h2 := g336c1_selfForce_bound hG2 hh hB hL hL0 hB0 ha hN X hXa i
    calc |inner ℝ (selfForce G1 ρ X i) (Torus.matVec D.M (selfForce G2 ρ X i))|
        ≤ ‖selfForce G1 ρ X i‖ * ‖Torus.matVec D.M (selfForce G2 ρ X i)‖ := abs_real_inner_le_norm _ _
      _ ≤ S * (cM * S) := by
          refine mul_le_mul h1 ((hcM _).trans (mul_le_mul_of_nonneg_left h2 hcM0)) (norm_nonneg _) hS0
      _ = cM * S * S := by ring
  have hs := g336c1_abs_sum_le (Finset.univ : Finset (Fin N)) _ (cM * S * S) hk
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  unfold g336c1_microB
  rw [abs_mul, abs_of_pos (by positivity)]
  calc 1 / (N : ℝ) * |∑ i, inner ℝ (selfForce G1 ρ X i) (Torus.matVec D.M (selfForce G2 ρ X i))|
      ≤ 1 / (N : ℝ) * ((N : ℝ) * (cM * S * S)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = cM * S * S := by field_simp

end Micro

end HRS
