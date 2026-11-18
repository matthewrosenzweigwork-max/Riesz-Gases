import HRS.MC.S7PIS1Path1

/-!
# Packet S1, `s7_PIS_path_facts`: the predicted path and the initial propagation are genuine paths

Proof of `HRS.MC.Sec7.PIPlan.s7_PIS_path_facts` (statement copied verbatim).  The function
`G(u,t) = 1_{t ≤ u} w(t) + 1_{t > u} V^{t,u} w(u)` on `[0,T]²` is jointly continuous (`S7PIS1_G_cont`), by the joint strong
continuity `S7PIS1_V_joint` and `V^{t,t} = id`; its slices are the predicted paths (`pathOf` is not junk) and
`u ↦ G(u,·)` is the curried map, hence continuous into the sup-norm space.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- the standing data: an integer level `k` and the adjoint hypotheses at `J = k + 2` -/
lemma S7PIS1_data (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ J k : ℕ, 1 ≤ k ∧ k + 2 ≤ J ∧ (k : ℝ) + 1 < m ∧ m ≤ (k : ℝ) + 2 ∧ PIEHyp J R.D R.ρ T := by
  obtain ⟨k, hk1, hk2, hk3, -, H⟩ := S7PIDV_hyp R m hm T hT
  refine ⟨k + 3, k + 1, by omega, by omega, ?_, ?_, H⟩
  · push_cast; linarith
  · push_cast; linarith

lemma S7PIS1_pathAt_coe {m T : ℝ} (w : PathSpace d m T) (x : Set.Icc (0 : ℝ) T) :
    pathAt w x.1 = PathSpace.at' w x := by
  unfold pathAt
  rw [dif_pos x.2]

lemma S7PIS1_pathOf_eq {m T : ℝ} (g : ℝ → NegSobolev d m)
    (hg : Continuous fun t : Set.Icc (0 : ℝ) T => g t) :
    pathOf m T g = (⟨fun t : Set.Icc (0 : ℝ) T => g t, hg⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
  unfold pathOf
  exact dif_pos hg

lemma S7PIS1_pathAt_pathOf {m T : ℝ} (g : ℝ → NegSobolev d m)
    (hg : Continuous fun t : Set.Icc (0 : ℝ) T => g t) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (pathOf m T g) t = g t := by
  unfold pathAt
  rw [dif_pos ht, S7PIS1_pathOf_eq g hg]
  rfl

lemma S7PIS1_cont_pathAt {m T : ℝ} (w : PathSpace d m T) :
    Continuous fun x : Set.Icc (0 : ℝ) T => pathAt w x.1 := by
  have : (fun x : Set.Icc (0 : ℝ) T => pathAt w x.1) = fun x => PathSpace.at' w x := by
    funext x; exact S7PIS1_pathAt_coe w x
  rw [this]
  exact (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous

/-- the joint function `G(u,t)` -/
def S7PIS1_G (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (w : PathSpace d m T)
    (p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T) : NegSobolev d m :=
  if p.2.1 ≤ p.1.1 then pathAt w p.2.1 else Vprop D ρ m (max p.2.1 p.1.1) p.1.1 (pathAt w p.1.1)

/-- the clamped `V`-branch is jointly continuous -/
lemma S7PIS1_f2_cont {J k : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} (H : PIEHyp J D μ T)
    (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2) (w : PathSpace d m T) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T =>
      Vprop D μ m (max p.2.1 p.1.1) p.1.1 (pathAt w p.1.1) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  have hu : Tendsto (fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => p.1.1) (𝓝 p₀) (𝓝 p₀.1.1) :=
    (continuous_subtype_val.comp continuous_fst).tendsto p₀
  have hv : Tendsto (fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => p.2.1) (𝓝 p₀) (𝓝 p₀.2.1) :=
    (continuous_subtype_val.comp continuous_snd).tendsto p₀
  have ht : Tendsto (fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => max p.2.1 p.1.1) (𝓝 p₀)
      (𝓝 (max p₀.2.1 p₀.1.1)) := hv.max hu
  have hF : Tendsto (fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => pathAt w p.1.1) (𝓝 p₀)
      (𝓝 (pathAt w p₀.1.1)) :=
    ((S7PIS1_cont_pathAt w).comp continuous_fst).tendsto p₀
  exact S7PIS1_V_joint H m k hk hJ hm0 hm1 (𝓝 p₀) (fun p => max p.2.1 p.1.1) (fun p => p.1.1)
    (Eventually.of_forall fun p => ⟨p.1.2.1, le_max_right _ _, max_le p.2.2.2 p.1.2.2⟩)
    ⟨p₀.1.2.1, le_max_right _ _, max_le p₀.2.2.2 p₀.1.2.2⟩ hu ht (fun p => pathAt w p.1.1) hF

/-- joint continuity of `G` -/
lemma S7PIS1_G_cont {J k : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} (H : PIEHyp J D μ T)
    (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2) (w : PathSpace d m T) :
    Continuous (S7PIS1_G D μ m T w) := by
  have hf2 := S7PIS1_f2_cont H hk hJ hm0 hm1 w
  have hf1 : Continuous fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => pathAt w p.2.1 :=
    (S7PIS1_cont_pathAt w).comp continuous_snd
  rw [continuous_iff_continuousAt]
  intro p₀
  have hu : Continuous fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => p.2.1 :=
    continuous_subtype_val.comp continuous_snd
  rcases lt_trichotomy p₀.2.1 p₀.1.1 with hlt | heq | hgt
  · have hev : ∀ᶠ p in 𝓝 p₀, p.2.1 < p.1.1 := (isOpen_lt hv hu).mem_nhds hlt
    refine (hf1.continuousAt (x := p₀)).congr ?_
    filter_upwards [hev] with p hp
    simp [S7PIS1_G, hp.le]
  · have hv0 : Vprop D μ m (max p₀.2.1 p₀.1.1) p₀.1.1 (pathAt w p₀.1.1) = pathAt w p₀.2.1 := by
      rw [heq, max_self]
      exact S7PIS1_Vdiag H m k hk hJ hm0 hm1 p₀.1.2.1 p₀.1.2.2 _
    have h1 := hf1.tendsto p₀
    have h2 := hf2.tendsto p₀
    rw [hv0] at h2
    have h3 := h1.if' (p := fun p : Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T => p.2.1 ≤ p.1.1) h2
    have hG : S7PIS1_G D μ m T w p₀ = pathAt w p₀.2.1 := by
      simp [S7PIS1_G, heq.le]
    show Tendsto (S7PIS1_G D μ m T w) (𝓝 p₀) (𝓝 (S7PIS1_G D μ m T w p₀))
    rw [hG]
    exact h3
  · have hev : ∀ᶠ p in 𝓝 p₀, p.1.1 < p.2.1 := (isOpen_lt hu hv).mem_nhds hgt
    refine (hf2.continuousAt (x := p₀)).congr ?_
    filter_upwards [hev] with p hp
    simp [S7PIS1_G, not_le.2 hp]

/-- the slice `t ↦ G(u,t)` is the function defining the predicted path -/
lemma S7PIS1_G_slice (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m T : ℝ} (w : PathSpace d m T)
    (x y : Set.Icc (0 : ℝ) T) :
    S7PIS1_G D ρ m T w (x, y) =
      if y.1 ≤ x.1 then pathAt w y.1 else Vprop D ρ m y.1 x.1 (pathAt w x.1) := by
  unfold S7PIS1_G
  by_cases h : y.1 ≤ x.1
  · simp [h]
  · simp only [h, if_false]
    rw [max_eq_left (not_le.1 h).le]

lemma S7PIS1_slice_cont {J k : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} (H : PIEHyp J D μ T)
    (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2) (w : PathSpace d m T)
    (x : Set.Icc (0 : ℝ) T) :
    Continuous fun y : Set.Icc (0 : ℝ) T =>
      (if y.1 ≤ x.1 then pathAt w y.1 else Vprop D μ m y.1 x.1 (pathAt w x.1)) := by
  have := (S7PIS1_G_cont H hk hJ hm0 hm1 w).comp (Continuous.prodMk (continuous_const (y := x)) continuous_id)
  refine this.congr fun y => ?_
  exact S7PIS1_G_slice D μ w x y

/-- **S2 (the predicted path and the initial propagation are genuine paths, depending continuously on the time)**. -/
theorem s7_PIS_path_facts_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    (∀ (w : PathSpace d m T) (u t : ℝ), u ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T →
      pathAt (predicted R.D R.ρ w u) t =
        if t ≤ u then pathAt w t else Vprop R.D R.ρ m t u (pathAt w u)) ∧
    (∀ (z : NegSobolev d m) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      pathAt (initProp R.D R.ρ m T z) t = Vprop R.D R.ρ m t 0 z) ∧
    (∀ w : PathSpace d m T, Continuous fun u : Set.Icc (0 : ℝ) T => predicted R.D R.ρ w u) := by
  obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  refine ⟨?_, ?_, ?_⟩
  · intro w u t hu ht
    have hc := S7PIS1_slice_cont H hk hJ hm0 hm1 w ⟨u, hu⟩
    exact S7PIS1_pathAt_pathOf (fun t => if t ≤ u then pathAt w t else Vprop R.D R.ρ m t u (pathAt w u)) hc ht
  · intro z t ht
    have hc : Continuous fun y : Set.Icc (0 : ℝ) T => Vprop R.D R.ρ m y.1 0 z := by
      rw [continuous_iff_continuousAt]
      intro y₀
      exact S7PIS1_V_joint H m k hk hJ hm0 hm1 (𝓝 y₀) (fun y => y.1) (fun _ => (0 : ℝ))
        (Eventually.of_forall fun y => ⟨le_rfl, y.2.1, y.2.2⟩) ⟨le_rfl, y₀.2.1, y₀.2.2⟩ tendsto_const_nhds
        (continuous_subtype_val.tendsto y₀) (fun _ => z) tendsto_const_nhds
    exact S7PIS1_pathAt_pathOf (fun t => Vprop R.D R.ρ m t 0 z) hc ht
  · intro w
    have hG := S7PIS1_G_cont H hk hJ hm0 hm1 w
    have hcur := (ContinuousMap.curry (⟨S7PIS1_G R.D R.ρ m T w, hG⟩ :
      C(Set.Icc (0 : ℝ) T × Set.Icc (0 : ℝ) T, NegSobolev d m))).continuous
    refine hcur.congr fun x => ?_
    have hc := S7PIS1_slice_cont H hk hJ hm0 hm1 w x
    unfold predicted
    rw [S7PIS1_pathOf_eq _ hc]
    ext y
    exact S7PIS1_G_slice R.D R.ρ w x y

end HRS.MC.Sec7.S7PIS1

end
