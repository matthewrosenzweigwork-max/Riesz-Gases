import HRS.MC.CepN6Aux3

/-!
# Packet CEPN6 (aux 4): pathwise lemmas (gap upper bound, displacement bounds, order persistence,
coordinate form of the integrated equation)
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {N : ℕ}

/-- If the gap `G` can rise by at most `K (t - s) + Nz` along any interval on which it stays `≥ L`, and
`K (t₂ - t₁) + Nz < L`, then a gap starting `≤ L` stays `< 2 L`. -/
theorem n6_gap_bound {G : ℝ → ℝ} {t₁ t₂ L K Nz : ℝ} (hG : ContinuousOn G (Set.Icc t₁ t₂))
    (hK : 0 ≤ K) (h0 : G t₁ ≤ L) (ht : t₁ ≤ t₂)
    (hrise : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ t₂ → (∀ u ∈ Set.Ioc s t, L ≤ G u) →
      G t - G s ≤ K * (t - s) + Nz)
    (hcond : K * (t₂ - t₁) + Nz < L) :
    ∀ t ∈ Set.Icc t₁ t₂, G t < 2 * L := by
  intro t' ht'
  by_contra hcon
  push_neg at hcon
  set S : Set ℝ := Set.Icc t₁ t' ∩ G ⁻¹' Set.Iic L with hS
  have hSc : IsClosed S :=
    ContinuousOn.preimage_isClosed_of_isClosed (hG.mono (Set.Icc_subset_Icc_right ht'.2))
      isClosed_Icc isClosed_Iic
  have hSk : IsCompact S := isCompact_Icc.of_isClosed_subset hSc Set.inter_subset_left
  have hne : S.Nonempty := ⟨t₁, ⟨le_rfl, ht'.1⟩, h0⟩
  have hsmem : sSup S ∈ S := hSk.sSup_mem hne
  set s' := sSup S with hs'
  have hbdd : BddAbove S := hSk.bddAbove
  have hGs : G s' ≤ L := hsmem.2
  have hs1 : t₁ ≤ s' := hsmem.1.1
  have hs2 : s' ≤ t' := hsmem.1.2
  have hIoc : ∀ u ∈ Set.Ioc s' t', L ≤ G u := by
    intro u hu
    by_contra hlt
    push_neg at hlt
    have : u ∈ S := ⟨⟨hs1.trans hu.1.le, hu.2⟩, le_of_lt hlt⟩
    have := le_csSup hbdd this
    linarith [hu.1]
  have h := hrise s' t' hs1 hs2 ht'.2 hIoc
  have h2 : K * (t' - s') ≤ K * (t₂ - t₁) :=
    mul_le_mul_of_nonneg_left (by linarith [ht'.2]) hK
  linarith

theorem n6_disp {f yk : ℝ → ℝ} {t₁ u B ν η n : ℝ} (hu : t₁ ≤ u) (hν : 0 ≤ ν)
    (heq : yk u - yk t₁ = (∫ s in t₁..u, f s) + ν * n) (hf : ∀ s ∈ Set.Icc t₁ u, |f s| ≤ B)
    (hn : |n| ≤ η) : |yk u - yk t₁| ≤ B * (u - t₁) + ν * η := by
  have h1 : ‖∫ s in t₁..u, f s‖ ≤ B * |u - t₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
      rw [Set.uIoc_of_le hu] at hs
      rw [Real.norm_eq_abs]
      exact hf s ⟨hs.1.le, hs.2⟩)
  rw [abs_of_nonneg (sub_nonneg.2 hu), Real.norm_eq_abs] at h1
  rw [heq]
  calc |(∫ s in t₁..u, f s) + ν * n| ≤ |∫ s in t₁..u, f s| + |ν * n| := abs_add_le _ _
    _ ≤ B * (u - t₁) + ν * η := by
      rw [abs_mul, abs_of_nonneg hν]
      have : ν * |n| ≤ ν * η := mul_le_mul_of_nonneg_left hn hν
      linarith

theorem n6_disp2 {f g yp yq : ℝ → ℝ} {t₁ u B ν η n m : ℝ} (hu : t₁ ≤ u) (hν : 0 ≤ ν)
    (hfi : IntervalIntegrable f volume t₁ u) (hgi : IntervalIntegrable g volume t₁ u)
    (hp : yp u - yp t₁ = (∫ s in t₁..u, f s) + ν * n)
    (hq : yq u - yq t₁ = (∫ s in t₁..u, g s) + ν * m)
    (hfg : ∀ s ∈ Set.Icc t₁ u, |f s + g s| ≤ B) (hn : |n| ≤ η) (hm : |m| ≤ η) :
    |(yp u + yq u) - (yp t₁ + yq t₁)| ≤ B * (u - t₁) + 2 * ν * η := by
  have h := n6_disp (f := fun s => f s + g s) (yk := fun s => yp s + yq s) (n := n + m) (η := 2 * η)
    hu hν (by
      rw [intervalIntegral.integral_add hfi hgi]
      linarith) hfg (by
      calc |n + m| ≤ |n| + |m| := abs_add_le _ _
        _ ≤ 2 * η := by linarith)
  calc _ ≤ B * (u - t₁) + ν * (2 * η) := h
    _ = _ := by ring

/-! ### Order persistence -/

theorem n6_persist {σ : Equiv.Perm (Fin N)} {y : ℝ → Fin N → Euc 1} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn y (Set.Icc 0 T)) (hfree : ∀ t ∈ Set.Icc (0 : ℝ) T, y t ∈ liftedFree 1 N)
    (h0 : cep_StrictlyOrdered σ (y 0)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, cep_StrictlyOrdered σ (y t) := by
  have : PreconnectedSpace (Set.Icc (0 : ℝ) T) :=
    Subtype.preconnectedSpace (isConnected_Icc hT).isPreconnected
  let f : Set.Icc (0 : ℝ) T → (Fin N → Euc 1) := fun t => y t
  have hf : Continuous f := hc.domRestrict
  have hfc : ∀ i : Fin N, Continuous fun t : Set.Icc (0 : ℝ) T => f t i 0 := fun i =>
    (n6_coord_cont i).comp hf
  let S : Set (Set.Icc (0 : ℝ) T) := {t | cep_StrictlyOrdered σ (f t)}
  let S₀ : Set (Set.Icc (0 : ℝ) T) :=
    {t | (∀ k k' : Fin N, k < k' → f t (σ k) 0 ≤ f t (σ k') 0) ∧
      ∀ k k' : Fin N, f t (σ k') 0 ≤ f t (σ k) 0 + 1}
  have hSo : IsOpen S := by
    have e : S = (⋂ k, ⋂ k', {t | k < k' → f t (σ k) 0 < f t (σ k') 0}) ∩
        (⋂ k, ⋂ k', {t | f t (σ k') 0 < f t (σ k) 0 + 1}) := by
      ext t; simp [S, cep_StrictlyOrdered]
    rw [e]
    refine IsOpen.inter (isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun k' => ?_)
      (isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun k' => ?_)
    · by_cases h : k < k'
      · simp only [h, true_imp_iff]
        exact isOpen_lt (hfc _) (hfc _)
      · simp [h]
    · exact isOpen_lt (hfc _) ((hfc _).add continuous_const)
  have hS₀c : IsClosed S₀ := by
    have e : S₀ = (⋂ k, ⋂ k', {t | k < k' → f t (σ k) 0 ≤ f t (σ k') 0}) ∩
        (⋂ k, ⋂ k', {t | f t (σ k') 0 ≤ f t (σ k) 0 + 1}) := by
      ext t; simp [S₀]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun k' => ?_)
      (isClosed_iInter fun k => isClosed_iInter fun k' => ?_)
    · by_cases h : k < k'
      · simp only [h, true_imp_iff]
        exact isClosed_le (hfc _) (hfc _)
      · simp [h]
    · exact isClosed_le (hfc _) ((hfc _).add continuous_const)
  have hSS₀ : S = S₀ := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k k' h => (h1 k k' h).le, fun k k' => (h2 k k').le⟩
    · rintro ⟨h1, h2⟩
      have hfr : f t ∈ liftedFree 1 N := hfree t t.2
      refine ⟨fun k k' h => ?_, fun k k' => ?_⟩
      · refine lt_of_le_of_ne (h1 k k' h) fun heq => ?_
        have hne : σ k ≠ σ k' := fun h' => absurd (σ.injective h') (ne_of_lt h)
        exact cepn4_ne_int hfr hne 0 (by simpa using sub_eq_zero.2 heq)
      · by_cases hkk : k = k'
        · subst hkk; linarith
        · refine lt_of_le_of_ne (h2 k k') fun heq => ?_
          have hne : σ k' ≠ σ k := fun h' => hkk (σ.injective h').symm
          exact cepn4_ne_int hfr hne 1 (by simp; linarith)
  have hSc : IsClosed S := hSS₀ ▸ hS₀c
  have hne : S.Nonempty := ⟨⟨0, le_rfl, hT⟩, h0⟩
  have hall := (show IsClopen S from ⟨hSc, hSo⟩).eq_univ hne
  intro t ht
  have : (⟨t, ht⟩ : Set.Icc (0 : ℝ) T) ∈ S := by rw [hall]; trivial
  exact this

/-! ### Coordinate form of the integrated equation -/

theorem n6_coord_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {D : DynData 1} {Y₀ : Ω → Fin N → Euc 1}
    {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s ≤ t → ((t : ℝ) : WithTop ℝ) < τ ω → ∀ k : Fin N,
      IntervalIntegrable (fun u => (liftedDrift D (Y u ω) k) 0) volume s t ∧
      Y t ω k 0 - Y s ω k 0 = (∫ u in s..t, (liftedDrift D (Y u ω) k) 0) +
        Real.sqrt (2 * D.invβ) * (W' (Real.toNNReal t) ω (k, 0) - W' (Real.toNNReal s) ω (k, 0)) := by
  filter_upwards [hsol.sol.eq] with ω hω
  intro s t hs0 hst htτ k
  have ht0 : 0 ≤ t := le_trans hs0 hst
  have hsτ : ((s : ℝ) : WithTop ℝ) < τ ω := lt_of_le_of_lt (by exact_mod_cast hst) htτ
  obtain ⟨hIt, hEt⟩ := hω t ht0 htτ
  obtain ⟨hIs, hEs⟩ := hω s hs0 hsτ
  let Λ : (Fin N → Euc 1) →L[ℝ] ℝ :=
    EuclideanSpace.proj (0 : Fin 1) ∘L ContinuousLinearMap.proj k
  have hΛ : ∀ y : Fin N → Euc 1, Λ y = y k 0 := fun y => rfl
  set g : ℝ → ℝ := fun u => Λ (liftedDrift D (Y u ω)) with hg
  have hgI : IntegrableOn g (Set.Icc 0 t) := Λ.integrable_comp hIt
  have hEt' : Y t ω = Y₀ ω + (∫ u in Set.Icc 0 t, liftedDrift D (Y u ω)) +
      ∑ ij, W' (Real.toNNReal t) ω ij • liftedNoise D ij := hEt
  have hEs' : Y s ω = Y₀ ω + (∫ u in Set.Icc 0 s, liftedDrift D (Y u ω)) +
      ∑ ij, W' (Real.toNNReal s) ω ij • liftedNoise D ij := hEs
  rw [sum_liftedNoise] at hEt' hEs'
  have hlt : Λ (Y t ω) = Λ (Y₀ ω) + (∫ u in Set.Icc 0 t, g u) +
      Real.sqrt (2 * D.invβ) * W' (Real.toNNReal t) ω (k, 0) := by
    rw [hEt', map_add, map_add, ← Λ.integral_comp_comm hIt]
    simp [hΛ, ofCoords, hg]
  have hls : Λ (Y s ω) = Λ (Y₀ ω) + (∫ u in Set.Icc 0 s, g u) +
      Real.sqrt (2 * D.invβ) * W' (Real.toNNReal s) ω (k, 0) := by
    rw [hEs', map_add, map_add, ← Λ.integral_comp_comm hIs]
    simp [hΛ, ofCoords, hg]
  have hIcc : ∀ x : ℝ, 0 ≤ x → ∫ u in Set.Icc 0 x, g u = ∫ u in (0 : ℝ)..x, g u := fun x hx => by
    rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]
  have hII_t : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hgI
  have hII_s : IntervalIntegrable g volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs0]
    exact hgI.mono_set (Set.Icc_subset_Icc_right hst)
  have hsub : ∫ u in s..t, g u = (∫ u in Set.Icc 0 t, g u) - ∫ u in Set.Icc 0 s, g u := by
    rw [hIcc t ht0, hIcc s hs0, intervalIntegral.integral_interval_sub_left hII_t hII_s]
  refine ⟨hII_s.symm.trans hII_t, ?_⟩
  · show Λ (Y t ω) - Λ (Y s ω) = (∫ u in s..t, g u) + _
    rw [hlt, hls, hsub]
    ring

end HRS.MC.CepN6
