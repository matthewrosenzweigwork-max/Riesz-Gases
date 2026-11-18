import HRS.MC.CepH3I1

/-!
# Packet CEPH3, part J1: separation constant of a test field, linear lifts, periodic lifts
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3j_norm_coe_le (a : ℝ) : ‖((a : ℝ) : UnitAddCircle)‖ ≤ |a| := by
  rw [AddCircle.norm_eq (1:ℝ)]
  have := round_le a 0
  simpa using this

lemma h3j_pair {K : Set (Config 1 N)} (hK : IsCompact K) (hKc : Disjoint K (collisionSet 1 N))
    {i j : Fin N} (hij : i ≠ j) : ∃ δ > 0, ∀ X ∈ K, δ ≤ dist (X i 0) (X j 0) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  have hcont : Continuous fun X : Config 1 N => dist (X i 0) (X j 0) := by fun_prop
  obtain ⟨X₀, hX₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨dist (X₀ i 0) (X₀ j 0), ?_, fun X hX => hmin hX⟩
  refine dist_pos.mpr fun h => ?_
  apply (disjoint_left.mp hKc) hX₀
  refine ⟨i, j, hij, ?_⟩
  funext t
  have : t = 0 := Subsingleton.elim _ _
  subst this
  exact h

lemma h3j_delta [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {K : Set (Config 1 N)} (hK : IsCompact K)
    (hKc : Disjoint K (collisionSet 1 N)) :
    ∃ δ > 0, ∀ z ∈ cep_Alcove N, h3d_Q σ₀ z ∈ K → ∀ k l : Fin N, k < l →
      δ ≤ z l - z k ∧ z l - z k ≤ 1 - δ := by
  classical
  have hp : ∀ p : Fin N × Fin N, ∃ δp : ℝ, 0 < δp ∧ (p.1 ≠ p.2 → ∀ X ∈ K, δp ≤ dist (X p.1 0) (X p.2 0)) := by
    intro p
    by_cases h : p.1 = p.2
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · obtain ⟨δ, hδ, hδ'⟩ := h3j_pair hK hKc h
      exact ⟨δ, hδ, fun _ => hδ'⟩
  choose δp hδp hδp' using hp
  let δ : ℝ := Finset.univ.inf' ⟨(0, 0), Finset.mem_univ _⟩ δp
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).mpr fun p _ => hδp p
  refine ⟨δ, hδpos, fun z hz hzK k l hkl => ?_⟩
  have hne : σ₀ k ≠ σ₀ l := fun h => (ne_of_lt hkl) (σ₀.injective h)
  have h1 : δ ≤ dist (h3d_Q σ₀ z (σ₀ k) 0) (h3d_Q σ₀ z (σ₀ l) 0) :=
    (Finset.inf'_le _ (Finset.mem_univ (σ₀ k, σ₀ l))).trans (hδp' (σ₀ k, σ₀ l) hne _ hzK)
  rw [h3d_Q_apply, h3d_Q_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, dist_eq_norm, ← AddCircle.coe_sub] at h1
  have hd0 : 0 < z l - z k := by linarith [hz.1 k l hkl]
  have hd1 : z l - z k < 1 := by linarith [hz.2 k l]
  have e1 := h3j_norm_coe_le (z k - z l)
  have e2 := h3j_norm_coe_le (z k - z l + 1)
  have e2' : ((z k - z l : ℝ) : UnitAddCircle) = ((z k - z l + 1 : ℝ) : UnitAddCircle) := by
    rw [h3d_coe_eq_iff]; exact ⟨-1, by simp⟩
  have h1b := h1
  rw [e2'] at h1b
  rw [abs_of_neg (by linarith)] at e1
  rw [abs_of_nonneg (by linarith)] at e2
  constructor <;> linarith

/-- Linear map `Λ : z ↦ unrank σ₀ z`. -/
def h3j_LamL (σ₀ : Equiv.Perm (Fin N)) : Ch N →L[ℝ] (Fin N → Euc 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := cep_unrank σ₀
      map_add' := fun x y => by ext i j; simp [cep_unrank]
      map_smul' := fun c x => by ext i j; simp [cep_unrank] }

lemma h3j_LamL_apply (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) : h3j_LamL σ₀ z = cep_unrank σ₀ z := rfl

/-- Linear map `y ↦ toCh σ₀ y`. -/
def h3j_ChL (σ₀ : Equiv.Perm (Fin N)) : (Fin N → Euc 1) →L[ℝ] Ch N :=
  LinearMap.toContinuousLinearMap
    { toFun := cep_toCh σ₀
      map_add' := fun x y => by ext k; simp [cep_toCh, cep_rank]
      map_smul' := fun c x => by ext k; simp [cep_toCh, cep_rank] }

lemma h3j_ChL_apply (σ₀ : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : h3j_ChL σ₀ y = cep_toCh σ₀ y := rfl

/-- Integer translation of a lift. -/
def h3j_ishift (n : Fin N → ℤ) : Fin N → Euc 1 := fun i => WithLp.toLp 2 fun _ => (n i : ℝ)

lemma h3j_mk_add_ishift (Y : Fin N → Euc 1) (n : Fin N → ℤ) :
    (fun i => Torus.mk (Y i + h3j_ishift n i)) = fun i => Torus.mk (Y i) := by
  funext i j
  simp only [Torus.mk, h3j_ishift, PiLp.add_apply]
  exact (h3d_coe_eq_iff _ _).mpr ⟨n i, by ring⟩

lemma h3j_fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : (Fin N → Euc 1) → E}
    (hg : ∀ Y n, g (Y + h3j_ishift n) = g Y) (Y : Fin N → Euc 1) (n : Fin N → ℤ) :
    fderiv ℝ g (Y + h3j_ishift n) = fderiv ℝ g Y := by
  have : (fun y => g (y + h3j_ishift n)) = g := funext fun y => hg y n
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (h3j_ishift n) (x := Y)
  rw [this] at h2
  exact h2.symm

lemma h3j_rep_Q (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) :
    (fun i => Torus.rep (h3d_Q σ₀ z i)) = cep_unrank σ₀ z + h3j_ishift (fun i => -⌊z (σ₀.symm i)⌋) := by
  funext i
  ext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  have h := h3d_y_Q σ₀ z (σ₀.symm i)
  rw [Equiv.apply_symm_apply] at h
  have h' : (Torus.rep (h3d_Q σ₀ z i)) 0 = Int.fract (z (σ₀.symm i)) := h
  have e1 : (cep_unrank σ₀ z i) 0 = z (σ₀.symm i) := rfl
  have e2 : (h3j_ishift (fun i => -⌊z (σ₀.symm i)⌋) i) 0 = ((-⌊z (σ₀.symm i)⌋ : ℤ) : ℝ) := rfl
  rw [Pi.add_apply, PiLp.add_apply, h', e1, e2, ← Int.self_sub_floor]
  push_cast
  ring
end
end HRS.MC.CepH3
