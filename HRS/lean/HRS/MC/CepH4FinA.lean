import HRS.MC.CepE7
import HRS.PDE.EnergyR2Fn

/-!
# Packet CEPH4FIN, file A: deterministic helpers

* `ch4f_isC11`: `Torus.IsCk 2 V` gives `cep_IsC11 V`.
* `ch4f_z0`: a Borel map `Config 1 N → Ch N` with values in the alcove and norm `≤ 2 √N`, which reads off a `σ₀`-ordered lift.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4Fin

open HRS HRS.MC.Cepa HRS.MC.CepK1 HRS.MC.CepE7

theorem ch4f_isC11 {V : Torus 1 → ℝ} (hV : Torus.IsCk 2 V) : cep_IsC11 V := by
  refine ⟨hV.of_le (by norm_num), ?_⟩
  obtain ⟨h1, h2⟩ := HRS.PDE.R2Aux.isC11_of_cbNorm hV
  refine ⟨Real.toNNReal (Torus.cbNorm 2 V), ?_⟩
  have : gradient (Torus.lift V) = fun x => (InnerProductSpace.toDual ℝ (Euc 1)).symm (fderiv ℝ (Torus.lift V) x) := by
    funext x; rfl
  rw [this]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [LinearIsometryEquiv.dist_map]
  exact h2.dist_le_mul x y

/-! ### The initial chamber point -/

section Z0

variable {N : ℕ} [NeZero N]

/-- The rank-`σ₀` lift of `x` anchored at the representative of `x (σ₀ 0)`. -/
def ch4f_yhat (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) : Fin N → Euc 1 := fun i =>
  cepk1_ι (Torus.rep (x (σ₀ 0)) 0 + Int.fract (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0))

open Classical in
def ch4f_z0 (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) : Ch N :=
  if cep_StrictlyOrdered σ₀ (ch4f_yhat σ₀ x) then cep_toCh σ₀ (ch4f_yhat σ₀ x) else cepE7_rho0 N

theorem ch4f_yhat_coord (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) (i : Fin N) :
    0 ≤ ch4f_yhat σ₀ x i 0 ∧ ch4f_yhat σ₀ x i 0 < 2 := by
  have h1 := cepE7_rep_coord (x (σ₀ 0))
  have h2 := Int.fract_nonneg (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0)
  have h3 := Int.fract_lt_one (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0)
  simp only [ch4f_yhat, cepk1_ι]
  constructor <;> linarith [h1.1, h1.2]

theorem ch4f_norm_le {z : Ch N} (hz : ∀ k, 0 ≤ z k ∧ z k < 2) : ‖z‖ ≤ 2 * Real.sqrt N := by
  have h : ‖z‖ ≤ Real.sqrt (4 * N) := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin N, (4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          obtain ⟨h0, h1⟩ := hz i
          nlinarith
      _ = 4 * N := by simp [mul_comm]
  have e : Real.sqrt (4 * N) = 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e] at h; exact h

theorem ch4f_z0_norm (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) : ‖ch4f_z0 σ₀ x‖ ≤ 2 * Real.sqrt N := by
  unfold ch4f_z0
  split_ifs with h
  · refine ch4f_norm_le fun k => ?_
    exact ch4f_yhat_coord σ₀ x (σ₀ k)
  · have := cepE7_norm_le (z := cepE7_rho0 N) cepE7_rho0_coord
    have h0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    linarith

theorem ch4f_z0_mem (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) : ch4f_z0 σ₀ x ∈ cep_Alcove N := by
  unfold ch4f_z0
  split_ifs with h
  · exact (cepE7_alcove_iff _ _).2 h
  · exact cepE7_rho0_mem N

theorem ch4f_yhat_meas (σ₀ : Equiv.Perm (Fin N)) (i : Fin N) :
    Measurable fun x : Config 1 N => ch4f_yhat σ₀ x i 0 := by
  have h := HRS.MC.CepE0.cepe0_measurable_repVec N
  have hi : ∀ j, Measurable fun x : Config 1 N => Torus.rep (x j) 0 := fun j => measurable_pi_iff.1 h j
  have : Measurable fun x : Config 1 N =>
      Torus.rep (x (σ₀ 0)) 0 + Int.fract (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0) :=
    (hi _).add (measurable_fract.comp ((hi i).sub (hi _)))
  simpa [ch4f_yhat, cepk1_ι] using this

theorem ch4f_ordered_meas (σ₀ : Equiv.Perm (Fin N)) :
    MeasurableSet {x : Config 1 N | cep_StrictlyOrdered σ₀ (ch4f_yhat σ₀ x)} := by
  have e : {x : Config 1 N | cep_StrictlyOrdered σ₀ (ch4f_yhat σ₀ x)} =
      (⋂ k : Fin N, ⋂ k' : Fin N, ⋂ (_ : k < k'),
        {x | ch4f_yhat σ₀ x (σ₀ k) 0 < ch4f_yhat σ₀ x (σ₀ k') 0}) ∩
      ⋂ k : Fin N, ⋂ k' : Fin N, {x | ch4f_yhat σ₀ x (σ₀ k') 0 < ch4f_yhat σ₀ x (σ₀ k) 0 + 1} := by
    ext x; simp [cep_StrictlyOrdered]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun k' =>
    MeasurableSet.iInter fun _ => measurableSet_lt (ch4f_yhat_meas σ₀ _) (ch4f_yhat_meas σ₀ _))
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun k' =>
      measurableSet_lt (ch4f_yhat_meas σ₀ _) ((ch4f_yhat_meas σ₀ _).add_const 1))

theorem ch4f_z0_meas (σ₀ : Equiv.Perm (Fin N)) : Measurable (ch4f_z0 σ₀) := by
  classical
  unfold ch4f_z0
  refine Measurable.ite (ch4f_ordered_meas σ₀) ?_ measurable_const
  refine (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun k => ?_
  simpa [cep_rank] using ch4f_yhat_meas σ₀ (σ₀ k)

theorem ch4f_mk_yhat (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) (i : Fin N) :
    Torus.mk (ch4f_yhat σ₀ x i) = x i := by
  funext c
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  have hr : ((Torus.rep (x i) 0 : ℝ) : UnitAddCircle) = x i 0 := by
    have := congrFun (Torus.mk_rep (x i)) 0
    simpa [Torus.mk] using this
  have hr' : ((Torus.rep (x (σ₀ 0)) 0 : ℝ) : UnitAddCircle) = x (σ₀ 0) 0 := by
    have := congrFun (Torus.mk_rep (x (σ₀ 0))) 0
    simpa [Torus.mk] using this
  have hfr : ((Int.fract (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0) : ℝ) : UnitAddCircle) =
      ((Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0 : ℝ) : UnitAddCircle) := by
    rw [Int.fract, AddCircle.coe_sub]
    have : (((⌊Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨⌊Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0⌋, by simp⟩
    rw [this, sub_zero]
  simp only [Torus.mk, ch4f_yhat, cepk1_ι]
  show ((Torus.rep (x (σ₀ 0)) 0 + Int.fract (Torus.rep (x i) 0 - Torus.rep (x (σ₀ 0)) 0) : ℝ) : UnitAddCircle) = x i 0
  rw [AddCircle.coe_add, hfr, AddCircle.coe_sub, hr, hr']
  abel

theorem ch4f_yhat_ordered (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) (y : Fin N → Euc 1)
    (hy : (fun i => Torus.mk (y i)) = x) (ho : cep_StrictlyOrdered σ₀ y) :
    cep_StrictlyOrdered σ₀ (ch4f_yhat σ₀ x) := by
  -- the integer offsets
  have hoff : ∀ i, ∃ n : ℤ, y i 0 = Torus.rep (x i) 0 + n := by
    intro i
    have h1 : ((y i 0 : ℝ) : UnitAddCircle) = x i 0 := by
      have := congrFun (congrFun hy i) 0
      simpa [Torus.mk] using this
    have h2 : ((Torus.rep (x i) 0 : ℝ) : UnitAddCircle) = x i 0 := by
      have := congrFun (Torus.mk_rep (x i)) 0
      simpa [Torus.mk] using this
    have h3 : (((y i 0 - Torus.rep (x i) 0 : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, h2, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
    exact ⟨n, by simp at hn; linarith⟩
  choose n hn using hoff
  set a := σ₀ 0 with ha
  have hfr : ∀ i, Int.fract (Torus.rep (x i) 0 - Torus.rep (x a) 0) = y i 0 - y a 0 := by
    intro i
    have hlt : 0 ≤ y i 0 - y a 0 ∧ y i 0 - y a 0 < 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, σ₀ k = i := ⟨σ₀.symm i, by simp⟩
      constructor
      · rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
        · have : k = 0 := Fin.ext h
          subst this; simp [ha]
        · have : (0 : Fin N) < k := Fin.pos_iff_ne_zero.2 (fun h' => by simp [h'] at h)
          have := ho.1 0 k this
          rw [ha]; linarith
      · have := ho.2 0 k
        rw [ha]; linarith
    have : Torus.rep (x i) 0 - Torus.rep (x a) 0 = (y i 0 - y a 0) + ((n a : ℤ) - n i : ℤ) := by
      rw [hn i, hn a]; push_cast; ring
    rw [this, Int.fract_add_intCast, Int.fract_eq_iff.2 ⟨hlt.1, hlt.2, 0, by simp⟩]
  have hyh : ∀ i, ch4f_yhat σ₀ x i 0 = y i 0 + (Torus.rep (x a) 0 - y a 0) := by
    intro i
    simp only [ch4f_yhat, cepk1_ι]
    show Torus.rep (x a) 0 + Int.fract (Torus.rep (x i) 0 - Torus.rep (x a) 0) = _
    rw [hfr i]; ring
  refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
  · rw [hyh, hyh]; linarith [ho.1 k k' hkk']
  · rw [hyh, hyh]; linarith [ho.2 k k']

theorem ch4f_unrank_toCh (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) (i : Fin N) :
    cep_unrank π (cep_toCh π y) i = y i := by
  ext c
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  simp [cep_unrank, cep_toCh, cep_rank]

theorem ch4f_z0_X (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N)
    (hx : ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = x ∧ cep_StrictlyOrdered σ₀ y) :
    (fun i => Torus.mk (cep_unrank σ₀ (ch4f_z0 σ₀ x) i)) = x := by
  obtain ⟨y, hy, ho⟩ := hx
  have hord := ch4f_yhat_ordered σ₀ x y hy ho
  funext i
  unfold ch4f_z0
  rw [if_pos hord, ch4f_unrank_toCh, ch4f_mk_yhat]

end Z0

end HRS.MC.CepH4Fin
