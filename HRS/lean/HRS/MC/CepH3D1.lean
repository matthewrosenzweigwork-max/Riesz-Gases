import HRS.MC.CepH3C3

/-!
# Packet CEPH3, part D1: the covering map `Q σ₀ = mk ∘ unrank σ₀ : Ch N → Config 1 N`

Periodicity, the integer-difference criterion, injectivity on `cell ∩ alcove`, continuity and a
measurable left inverse on `cell ∩ alcove`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- The covering map `mk ∘ unrank σ₀`. -/
def h3d_Q (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) : Config 1 N :=
  fun i => Torus.mk (cep_unrank σ₀ z i)

lemma h3d_Q_apply (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) (i : Fin N) (j : Fin 1) :
    h3d_Q σ₀ z i j = ((z (σ₀.symm i) : ℝ) : UnitAddCircle) := rfl

lemma h3d_coe_eq_iff (x y : ℝ) :
    ((x : ℝ) : UnitAddCircle) = (y : UnitAddCircle) ↔ ∃ n : ℤ, x - y = n := by
  show (QuotientAddGroup.mk x : ℝ ⧸ AddSubgroup.zmultiples (1:ℝ)) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]
  exact ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩

lemma h3d_Q_eq_iff (σ₀ : Equiv.Perm (Fin N)) (z z' : Ch N) :
    h3d_Q σ₀ z = h3d_Q σ₀ z' ↔ ∀ k, ∃ n : ℤ, z k - z' k = n := by
  constructor
  · intro h k
    have := congrFun (congrFun h (σ₀ k)) 0
    rw [h3d_Q_apply, h3d_Q_apply, Equiv.symm_apply_apply] at this
    exact (h3d_coe_eq_iff _ _).mp this
  · intro h
    funext i j
    rw [h3d_Q_apply, h3d_Q_apply]
    exact (h3d_coe_eq_iff _ _).mpr (h _)

/-- Integer translation of `z`. -/
def h3d_shift (m : Fin N → ℤ) : Ch N := WithLp.toLp 2 fun k => (m k : ℝ)

lemma h3d_Q_add_int (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) (m : Fin N → ℤ) :
    h3d_Q σ₀ (z + h3d_shift m) = h3d_Q σ₀ z := by
  rw [h3d_Q_eq_iff]
  intro k
  exact ⟨m k, by simp [h3d_shift]⟩

lemma h3d_Q_reduce [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) :
    h3d_Q σ₀ (cep_reduce z) = h3d_Q σ₀ z := by
  rw [h3d_Q_eq_iff]
  intro k
  exact ⟨-⌊z 0⌋, by simp [cep_reduce, cep_diag]⟩

lemma h3d_Q_injOn [NeZero N] (σ₀ : Equiv.Perm (Fin N)) :
    InjOn (h3d_Q σ₀) (cep_cell N ∩ cep_Alcove N) := by
  rintro z ⟨hzc, hzA⟩ z' ⟨hzc', hzA'⟩ h
  have hk := (h3d_Q_eq_iff σ₀ z z').mp h
  obtain ⟨n0, hn0⟩ := hk 0
  have h0 : n0 = 0 := by
    have h1 : (n0 : ℝ) < 1 := by
      have := hzc.2; have := hzc'.1; linarith
    have h2 : (-1 : ℝ) < n0 := by
      have := hzc.1; have := hzc'.2; linarith
    have : n0 < 1 := by exact_mod_cast h1
    have : -1 < n0 := by exact_mod_cast h2
    omega
  subst h0
  simp only [Int.cast_zero] at hn0
  ext k
  obtain ⟨nk, hnk⟩ := hk k
  have hz0 : z 0 = z' 0 := by linarith
  have hlt : ∀ y : Ch N, y ∈ cep_Alcove N → y 0 ≤ y k ∧ y k < y 0 + 1 := fun y hy =>
    ⟨by
      by_cases hk0 : (0 : Fin N) = k
      · rw [hk0]
      · exact (hy.1 0 k (lt_of_le_of_ne (Fin.zero_le _) hk0)).le,
     hy.2 0 k⟩
  have a1 := hlt z hzA
  have a2 := hlt z' hzA'
  have h1 : (nk : ℝ) < 1 := by linarith [a1.2, a2.1]
  have h2 : (-1 : ℝ) < nk := by linarith [a1.1, a2.2]
  have : nk < 1 := by exact_mod_cast h1
  have : -1 < nk := by exact_mod_cast h2
  have : nk = 0 := by omega
  subst this
  simp at hnk
  linarith

lemma h3d_Q_continuous (σ₀ : Equiv.Perm (Fin N)) : Continuous (h3d_Q σ₀) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [h3d_Q_apply]
  exact (AddCircle.continuous_mk' 1).comp (by fun_prop)

lemma h3d_Q_measurable (σ₀ : Equiv.Perm (Fin N)) : Measurable (h3d_Q σ₀) :=
  (h3d_Q_continuous σ₀).measurable

/-- fractional coordinate of the `i`-th particle. -/
def h3d_y (x : Config 1 N) (i : Fin N) : ℝ := Torus.rep (x i) 0

lemma h3d_y_mk (a : ℝ) : (AddCircle.equivIco (1:ℝ) 0 ((a : ℝ) : UnitAddCircle) : ℝ) = Int.fract a := by
  have h : ((a : ℝ) : UnitAddCircle) = ((Int.fract a : ℝ) : UnitAddCircle) :=
    (h3d_coe_eq_iff _ _).mpr ⟨⌊a⌋, by rw [← Int.self_sub_floor]; ring⟩
  rw [h, AddCircle.equivIco_coe_eq (by simp [Int.fract_nonneg, Int.fract_lt_one] : Int.fract a ∈ Ico (0:ℝ) (0+1))]

lemma h3d_y_Q (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) (k : Fin N) :
    h3d_y (h3d_Q σ₀ z) (σ₀ k) = Int.fract (z k) := by
  unfold h3d_y Torus.rep
  simp only [h3d_Q, cep_unrank, Torus.mk, Equiv.symm_apply_apply]
  exact h3d_y_mk _

lemma h3d_y_measurable (i : Fin N) : Measurable (fun x : Config 1 N => h3d_y x i) := by
  unfold h3d_y Torus.rep
  have : Measurable (fun a : UnitAddCircle => (AddCircle.equivIco (1:ℝ) 0 a : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact this.comp ((measurable_pi_apply 0).comp (measurable_pi_apply i))

def h3d_g [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (x : Config 1 N) : Ch N :=
  WithLp.toLp 2 fun k => if h3d_y x (σ₀ k) < h3d_y x (σ₀ 0) then h3d_y x (σ₀ k) + 1 else h3d_y x (σ₀ k)

lemma h3d_g_measurable [NeZero N] (σ₀ : Equiv.Perm (Fin N)) : Measurable (h3d_g σ₀) := by
  unfold h3d_g
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun k => ?_)
  refine Measurable.ite (measurableSet_lt (h3d_y_measurable _) (h3d_y_measurable _)) ?_ (h3d_y_measurable _)
  exact (h3d_y_measurable _).add_const _

lemma h3d_g_Q [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {z : Ch N} (hz : z ∈ cep_cell N ∩ cep_Alcove N) :
    h3d_g σ₀ (h3d_Q σ₀ z) = z := by
  obtain ⟨hc, hA⟩ := hz
  ext k
  unfold h3d_g
  simp only [h3d_y_Q]
  have h0 : Int.fract (z 0) = z 0 := Int.fract_eq_self.mpr ⟨hc.1, hc.2⟩
  have hk1 : z 0 ≤ z k := by
    by_cases hk0 : (0 : Fin N) = k
    · rw [hk0]
    · exact (hA.1 0 k (lt_of_le_of_ne (Fin.zero_le _) hk0)).le
  have hk2 : z k < z 0 + 1 := hA.2 0 k
  rw [h0]
  by_cases h : z k < 1
  · have : Int.fract (z k) = z k := Int.fract_eq_self.mpr ⟨by linarith [hc.1], h⟩
    rw [this]; simp [not_lt.mpr hk1]
  · have hfl : ⌊z k⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [hc.2]
    have : Int.fract (z k) = z k - 1 := by rw [← Int.self_sub_floor, hfl]; simp
    rw [this]
    have : z k - 1 < z 0 := by linarith
    simp [this]

end HRS.MC.CepH3
