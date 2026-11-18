import HRS.MC.CepH3D1

/-!
# Packet CEPH3, part D2: change of variables for the covering map `Q σ₀` on sets of injectivity
-/

open MeasureTheory Set
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

/-- The half-open unit box with lower corner `m`. -/
def h3d_box (m : Fin N → ℤ) : Set (Ch N) := {z | ∀ k, z k ∈ Ioc (m k : ℝ) (m k + 1)}

lemma h3d_box_measurable (m : Fin N → ℤ) : MeasurableSet (h3d_box m) := by
  have : h3d_box m = ⋂ k, (fun z : Ch N => z k) ⁻¹' Ioc (m k : ℝ) (m k + 1) := by
    ext z; simp [h3d_box]
  rw [this]
  exact MeasurableSet.iInter fun k => (by fun_prop : Measurable fun z : Ch N => z k) measurableSet_Ioc

theorem h3d_box_mp (σ₀ : Equiv.Perm (Fin N)) (m : Fin N → ℤ) :
    MeasurePreserving (h3d_Q σ₀) (volume.restrict (h3d_box m)) volume := by
  set f1 : Ch N → (Fin N → ℝ) := WithLp.ofLp with hf1d
  set f2 : (Fin N → ℝ) → (Fin N → ℝ) := ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ₀) with hf2d
  set f3 : (Fin N → ℝ) → (Fin N → UnitAddCircle) := fun x i => ((x i : ℝ) : UnitAddCircle) with hf3d
  set f4 : (Fin N → UnitAddCircle) → Config 1 N := fun t i _ => t i with hf4d
  have h1 : MeasurePreserving f1 volume volume := PiLp.volume_preserving_ofLp (Fin N)
  have h2 : MeasurePreserving f2 volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ₀
  have h4 : MeasurePreserving f4 volume volume := by
    have := measurePreserving_pi (fun _ : Fin N => (volume : Measure UnitAddCircle))
      (fun _ : Fin N => (volume : Measure (Torus 1))) (f := fun _ a => fun (_ : Fin 1) => a) (fun i => ?_)
    · exact this
    · exact (volume_preserving_funUnique (Fin 1) UnitAddCircle).symm
  set s : Set (Fin N → ℝ) := Set.pi univ (fun i => Ioc ((m (σ₀.symm i) : ℤ) : ℝ) (m (σ₀.symm i) + 1)) with hs
  have hsm : MeasurableSet s := MeasurableSet.univ_pi fun i => measurableSet_Ioc
  have h3 : MeasurePreserving f3 (volume.restrict s) volume := by
    have e : (volume : Measure (Fin N → ℝ)).restrict s =
        Measure.pi (fun i => (volume : Measure ℝ).restrict (Ioc ((m (σ₀.symm i) : ℤ) : ℝ) (m (σ₀.symm i) + 1))) :=
      Measure.restrict_pi_pi (fun _ : Fin N => (volume : Measure ℝ)) _
    rw [e]
    exact measurePreserving_pi _ _ (fun i => AddCircle.measurePreserving_mk 1 _)
  have h12 : MeasurePreserving (f2 ∘ f1) volume volume := h2.comp h1
  have hpre : (f2 ∘ f1) ⁻¹' s = h3d_box m := by
    ext z
    simp only [hs, mem_preimage, Function.comp_apply, mem_pi, mem_univ, forall_true_left, h3d_box,
      mem_setOf_eq, hf2d]
    constructor
    · intro h k
      have := h (σ₀ k)
      simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using this
    · intro h i
      simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using h (σ₀.symm i)
  have h12' := h12.restrict_preimage hsm
  rw [hpre] at h12'
  have hQ : h3d_Q σ₀ = f4 ∘ f3 ∘ (f2 ∘ f1) := by
    funext z i j
    simp [h3d_Q_apply, hf4d, hf3d, hf2d, hf1d, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hQ]
  exact h4.comp (h3.comp h12')

lemma h3d_box_disjoint {m m' : Fin N → ℤ} {z : Ch N} (h : z ∈ h3d_box m) (h' : z ∈ h3d_box m') : m = m' := by
  funext k
  have a := h k; have b := h' k
  have h1 : (m k : ℝ) < m' k + 1 := by linarith [a.1, b.2]
  have h2 : (m' k : ℝ) < m k + 1 := by linarith [a.2, b.1]
  have : m k < m' k + 1 := by exact_mod_cast h1
  have : m' k < m k + 1 := by exact_mod_cast h2
  omega

lemma h3d_box_cover (z : Ch N) : z ∈ h3d_box (fun k => ⌈z k⌉ - 1) := by
  intro k
  constructor
  · have := Int.ceil_lt_add_one (z k)
    push_cast; linarith
  · have := Int.le_ceil (z k)
    push_cast; linarith

lemma h3d_Q_injOn_box (σ₀ : Equiv.Perm (Fin N)) (m : Fin N → ℤ) : InjOn (h3d_Q σ₀) (h3d_box m) := by
  intro z hz z' hz' h
  ext k
  obtain ⟨n, hn⟩ := (h3d_Q_eq_iff σ₀ z z').mp h k
  have a := hz k; have b := hz' k
  have h1 : (n : ℝ) < 1 := by linarith [a.2, b.1]
  have h2 : (-1 : ℝ) < n := by linarith [a.1, b.2]
  have : n < 1 := by exact_mod_cast h1
  have : -1 < n := by exact_mod_cast h2
  have : n = 0 := by omega
  subst this
  simp at hn
  linarith

/-- Change of variables for the covering map on a set where it is injective. -/
theorem h3d_pushforward (σ₀ : Equiv.Perm (Fin N)) {S : Set (Ch N)} (hS : MeasurableSet S)
    (hinj : InjOn (h3d_Q σ₀) S) :
    (volume.restrict S).map (h3d_Q σ₀) = volume.restrict (h3d_Q σ₀ '' S) := by
  have hQc := h3d_Q_continuous σ₀
  have hQm := h3d_Q_measurable σ₀
  have hSm : ∀ m, MeasurableSet (S ∩ h3d_box m) := fun m => hS.inter (h3d_box_measurable m)
  have himg : ∀ m, MeasurableSet (h3d_Q σ₀ '' (S ∩ h3d_box m)) := fun m =>
    (hSm m).image_of_continuousOn_injOn hQc.continuousOn (hinj.mono inter_subset_left)
  have hSU : S = ⋃ m, S ∩ h3d_box m := by
    ext z; simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨_, h, h3d_box_cover z⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun m => S ∩ h3d_box m) := by
    intro m m' hne
    refine disjoint_left.mpr fun z hz hz' => hne (h3d_box_disjoint hz.2 hz'.2)
  have himgS : h3d_Q σ₀ '' S = ⋃ m, h3d_Q σ₀ '' (S ∩ h3d_box m) := by
    rw [hSU, image_iUnion]; simp only [← hSU]
  ext T hT
  have hdisj' : Pairwise (Function.onFun Disjoint fun m => h3d_Q σ₀ '' (S ∩ h3d_box m)) := by
    intro m m' hne
    refine disjoint_left.mpr fun y hy hy' => hne ?_
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨s', hs', h⟩ := hy'
    have : s' = s := hinj hs'.1 hs.1 h
    subst this
    exact h3d_box_disjoint hs.2 hs'.2
  rw [Measure.map_apply hQm hT, Measure.restrict_apply (hQm hT), Measure.restrict_apply hT]
  have e1 : h3d_Q σ₀ ⁻¹' T ∩ S = ⋃ m, h3d_Q σ₀ ⁻¹' T ∩ (S ∩ h3d_box m) := by
    rw [← inter_iUnion, ← hSU]
  have e2 : T ∩ h3d_Q σ₀ '' S = ⋃ m, T ∩ h3d_Q σ₀ '' (S ∩ h3d_box m) := by
    rw [← inter_iUnion, ← himgS]
  rw [e1, e2, measure_iUnion, measure_iUnion]
  · refine tsum_congr fun m => ?_
    have hU : MeasurableSet (T ∩ h3d_Q σ₀ '' (S ∩ h3d_box m)) := hT.inter (himg m)
    have := (h3d_box_mp σ₀ m).measure_preimage hU.nullMeasurableSet
    rw [Measure.restrict_apply (hQm hU)] at this
    rw [← this]
    congr 1
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨hzT, hzS, hzb⟩
      exact ⟨⟨hzT, z, ⟨hzS, hzb⟩, rfl⟩, hzb⟩
    · rintro ⟨⟨hzT, s, ⟨hsS, hsb⟩, hs⟩, hzb⟩
      have : s = z := h3d_Q_injOn_box σ₀ m hsb hzb hs
      subst this
      exact ⟨hzT, hsS, hsb⟩
  · intro m m' hne
    exact (hdisj' hne).mono inter_subset_right inter_subset_right
  · exact fun m => hT.inter (himg m)
  · intro m m' hne
    exact (hdisj hne).mono inter_subset_right inter_subset_right
  · exact fun m => (hQm hT).inter (hSm m)
end
end HRS.MC.CepH3
