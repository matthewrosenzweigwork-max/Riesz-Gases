import HRS.MC.CepaDefs
import HRS.MC.CepE0
import HRS.MC.CepE1
import HRS.MC.CepK1

/-!
# Packet CEPE7, file A1: initial point, chamber coordinates, collisions, closure of the alcove

Deterministic and measurability helpers for the assembly of `cep_E7_existence`:
* `cepE7_rho0`, `cepE7_z0` (the initial chamber point, reset to the fixed alcove point on the collision set);
* `cep_unrank` / `cep_toCh` algebra, non-collision of lifts of alcove points, cyclic order from `closure(alcove)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE7

open HRS HRS.MC.Cepa HRS.MC.CepK1

variable {N : ℕ}

/-- The fixed alcove point `ρ_k = k / N`. -/
def cepE7_rho0 (N : ℕ) : Ch N := WithLp.toLp 2 fun k : Fin N => ((k : ℕ) : ℝ) / N

theorem cepE7_rho0_coord (k : Fin N) : 0 ≤ cepE7_rho0 N k ∧ cepE7_rho0 N k < 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast k.pos
  refine ⟨?_, ?_⟩
  · show 0 ≤ ((k : ℕ) : ℝ) / N
    positivity
  · show ((k : ℕ) : ℝ) / N < 1
    rw [div_lt_one hN]
    exact_mod_cast k.2

theorem cepE7_rho0_mem (N : ℕ) : cepE7_rho0 N ∈ cep_Alcove N := by
  refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
  · have hN : (0 : ℝ) < N := by exact_mod_cast k.pos
    show ((k : ℕ) : ℝ) / N < ((l : ℕ) : ℝ) / N
    have : ((k : ℕ) : ℝ) < ((l : ℕ) : ℝ) := by exact_mod_cast hkl
    exact div_lt_div_of_pos_right this hN
  · obtain ⟨h0, _⟩ := cepE7_rho0_coord k
    obtain ⟨_, h1⟩ := cepE7_rho0_coord l
    linarith

open Classical in
/-- The initial chamber point: the sorted representatives off the collision set, `ρ` on it. -/
def cepE7_z0 (π0 : Config 1 N → Equiv.Perm (Fin N)) (x : Config 1 N) : Ch N :=
  if x ∈ collisionSet 1 N then cepE7_rho0 N else cep_toCh (π0 x) (fun i => Torus.rep (x i))

theorem cepE7_rep_coord (x : Torus 1) : 0 ≤ Torus.rep x 0 ∧ Torus.rep x 0 < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (x 0)).2
  simp only [zero_add] at h
  exact h

theorem cepE7_z0_coord (π0 : Config 1 N → Equiv.Perm (Fin N)) (x : Config 1 N) (k : Fin N) :
    0 ≤ cepE7_z0 π0 x k ∧ cepE7_z0 π0 x k < 1 := by
  unfold cepE7_z0
  split_ifs with h
  · exact cepE7_rho0_coord k
  · exact cepE7_rep_coord (x (π0 x k))

theorem cepE7_norm_le {z : Ch N} (hz : ∀ k, 0 ≤ z k ∧ z k < 1) : ‖z‖ ≤ Real.sqrt N := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        obtain ⟨h0, h1⟩ := hz i
        nlinarith
    _ = N := by simp

theorem cepE7_z0_norm (π0 : Config 1 N → Equiv.Perm (Fin N)) (x : Config 1 N) :
    ‖cepE7_z0 π0 x‖ ≤ Real.sqrt N :=
  cepE7_norm_le (cepE7_z0_coord π0 x)

theorem cepE7_alcove_iff (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) :
    cep_toCh π y ∈ cep_Alcove N ↔ cep_StrictlyOrdered π y := Iff.rfl

theorem cepE7_z0_mem (π0 : Config 1 N → Equiv.Perm (Fin N))
    (hπ0 : ∀ x : Config 1 N, x ∉ collisionSet 1 N → cep_StrictlyOrdered (π0 x) (fun i => Torus.rep (x i)))
    (x : Config 1 N) : cepE7_z0 π0 x ∈ cep_Alcove N := by
  unfold cepE7_z0
  split_ifs with h
  · exact cepE7_rho0_mem N
  · exact (cepE7_alcove_iff _ _).2 (hπ0 x h)

/-- Gluing finitely many measurable maps along a measurable labelling. -/
theorem cepE7_glue {α γ : Type*} {m : MeasurableSpace α} [MeasurableSpace γ]
    (π : α → Equiv.Perm (Fin N)) (F : Equiv.Perm (Fin N) → α → γ)
    (hF : ∀ σ, Measurable[m] (F σ)) (hπ : ∀ σ, MeasurableSet[m] {a | π a = σ}) :
    Measurable[m] (fun a => F (π a) a) := by
  intro S hS
  have : (fun a => F (π a) a) ⁻¹' S = ⋃ σ, {a | π a = σ} ∩ F σ ⁻¹' S := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨π a, rfl, h⟩, fun ⟨σ, h1, h2⟩ => by rw [h1]; exact h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hπ σ).inter (hF σ hS)

theorem cepE7_measurable_toCh (σ : Equiv.Perm (Fin N)) :
    Measurable (fun x : Config 1 N => cep_toCh σ (fun i => Torus.rep (x i))) := by
  have h := HRS.MC.CepE0.cepe0_measurable_repVec N
  have h2 : Measurable (fun x : Config 1 N => fun k : Fin N => Torus.rep (x (σ k)) 0) :=
    measurable_pi_iff.2 fun k => (measurable_pi_iff.1 h (σ k))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp h2

theorem cepE7_z0_meas (π0 : Config 1 N → Equiv.Perm (Fin N))
    (hπ0 : ∀ σ, MeasurableSet {x : Config 1 N | π0 x = σ}) : Measurable (cepE7_z0 π0) := by
  classical
  unfold cepE7_z0
  refine Measurable.ite (isClosed_collisionSet 1 N).measurableSet measurable_const ?_
  exact cepE7_glue (m := inferInstance) π0 (fun σ x => cep_toCh σ (fun i => Torus.rep (x i)))
    cepE7_measurable_toCh hπ0

theorem cepE7_toCh_unrank (π : Equiv.Perm (Fin N)) (z : Ch N) : cep_toCh π (cep_unrank π z) = z := by
  ext k
  show (cep_unrank π z (π k)) 0 = z k
  simp [cep_unrank]

theorem cepE7_unrank_apply (π : Equiv.Perm (Fin N)) (z : Ch N) (i : Fin N) :
    cep_unrank π z i = cepk1_ι (z (π.symm i)) := rfl

theorem cepE7_unrank_strict {z : Ch N} (hz : z ∈ cep_Alcove N) (π : Equiv.Perm (Fin N)) :
    cep_StrictlyOrdered π (cep_unrank π z) := by
  rw [← cepE7_alcove_iff, cepE7_toCh_unrank]
  exact hz

theorem cepE7_alcove_diff {z : Ch N} (hz : z ∈ cep_Alcove N) {k l : Fin N} (hkl : k ≠ l) :
    0 < |z k - z l| ∧ |z k - z l| < 1 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have h1 := hz.1 k l h
    have h2 := hz.2 k l
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 h1)]
    constructor <;> linarith
  · have h1 := hz.1 l k h
    have h2 := hz.2 l k
    rw [abs_of_pos (sub_pos.2 h1)]
    constructor <;> linarith

theorem cepE7_not_collision {z : Ch N} (hz : z ∈ cep_Alcove N) (π : Equiv.Perm (Fin N)) :
    (fun i => Torus.mk (cep_unrank π z i)) ∉ collisionSet 1 N := by
  rintro ⟨i, j, hij, h⟩
  have hkl : π.symm i ≠ π.symm j := fun h' => hij (π.symm.injective h')
  have h0 : Torus.mk (cep_unrank π z i - cep_unrank π z j) = 0 := by
    have h' : Torus.mk (cep_unrank π z i) = Torus.mk (cep_unrank π z j) := h
    rw [← HRS.MC.CepE1.cepe1_sub_mk, h', sub_self]
  have hd : (cep_unrank π z i - cep_unrank π z j) = cepk1_ι (z (π.symm i) - z (π.symm j)) := by
    ext a
    simp [cep_unrank, cepk1_ι]
  rw [hd] at h0
  obtain ⟨hb0, hb1⟩ := cepE7_alcove_diff hz hkl
  exact cepk1_mk_ne_zero (HRS.MC.CepE1.cepe1_noint hb0 hb1) h0

theorem cepE7_isClosed_cyc :
    IsClosed {z : Ch N | (∀ k l : Fin N, k ≤ l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1} := by
  have hp : ∀ k : Fin N, Continuous fun z : Ch N => z k := fun k => (EuclideanSpace.proj k).continuous
  have e : {z : Ch N | (∀ k l : Fin N, k ≤ l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1} =
      (⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k ≤ l), {z : Ch N | z k ≤ z l}) ∩
        ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch N | z l ≤ z k + 1} := by
    ext z; simp
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_le (hp k) (hp l)) (isClosed_iInter fun k => isClosed_iInter fun l =>
    isClosed_le (hp l) ((hp k).add continuous_const))

theorem cepE7_closure_sub :
    closure (cep_Alcove N) ⊆ {z : Ch N | (∀ k l : Fin N, k ≤ l → z k ≤ z l) ∧ ∀ k l : Fin N, z l ≤ z k + 1} := by
  refine closure_minimal (fun z hz => ⟨fun k l hkl => ?_, fun k l => (hz.2 k l).le⟩) cepE7_isClosed_cyc
  rcases eq_or_lt_of_le hkl with h | h
  · rw [h]
  · exact (hz.1 k l h).le

theorem cepE7_unrank_cyc {z : Ch N} (hz : z ∈ closure (cep_Alcove N)) (π : Equiv.Perm (Fin N)) :
    CyclicallyOrdered π (cep_unrank π z) := by
  intro j
  have h := cepE7_closure_sub hz
  refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
  · simpa [cep_unrank] using h.1 k k' hkk'
  · simpa [cep_unrank] using h.2 k k'

end HRS.MC.CepE7
