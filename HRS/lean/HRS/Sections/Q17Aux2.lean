import HRS.Sections.Q17Aux1

/-!
# Q17 auxiliary 2: Fin partitions as cell lists; existence of Riemann--Stieltjes integrals

Bridges the `Fin`-indexed `IsRS` sums with the cell-list machinery of `Q17Aux1`, and proves
existence of the RS integral of a continuous integrand against an integrator with a superadditive
budget `W` (uniform partitions form a Cauchy family).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Sec7

section Q17Exists

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cell list of a `Fin`-indexed tagged partition. -/
def q17_cells {n : ℕ} (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ) : List (ℝ × ℝ × ℝ) :=
  List.ofFn fun i : Fin n => (u i.castSucc, u i.succ, τ i)

theorem q17_sum_ofFn (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) :
    ∀ (n : ℕ) (f : Fin n → ℝ × ℝ × ℝ),
      q17_sum B G (List.ofFn f) = ∑ i, B (f i).2.2 (G (f i).2.1 - G (f i).1)
  | 0, f => by simp [q17_sum]
  | n + 1, f => by
    rw [List.ofFn_succ]
    simp only [q17_sum]
    rw [q17_sum_ofFn B G n (fun i => f i.succ), Fin.sum_univ_succ]

theorem q17_sum_cells (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) {n : ℕ} (u : Fin (n + 1) → ℝ)
    (τ : Fin n → ℝ) :
    q17_sum B G (q17_cells u τ) = ∑ i, B (τ i) (G (u i.succ) - G (u i.castSucc)) := by
  unfold q17_cells
  rw [q17_sum_ofFn]

theorem q17_cells_succ {n : ℕ} (u : Fin (n + 2) → ℝ) (τ : Fin (n + 1) → ℝ) :
    q17_cells u τ = (u (0 : Fin (n + 1)).castSucc, u (0 : Fin (n + 1)).succ, τ 0) ::
      q17_cells (fun i => u i.succ) (fun i => τ i.succ) := by
  unfold q17_cells
  rw [List.ofFn_succ]
  simp only [Fin.succ_castSucc]

theorem q17_P_ofFn (T δ : ℝ) : ∀ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ),
    Monotone u → (∀ i : Fin n, u i.succ - u i.castSucc ≤ δ) →
    (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) →
    0 ≤ u 0 → u (Fin.last n) ≤ T → q17_P T δ (q17_cells u τ) (u 0) (u (Fin.last n))
  | 0, u, τ, _, _, _, _, _ => by
    have hc : q17_cells u τ = [] := by simp [q17_cells]
    rw [hc]
    exact (q17_P_nil T δ _ _).2 rfl
  | n + 1, u, τ, hmono, hmesh, htag, h0, hT => by
    rw [q17_cells_succ]
    have hu' : Monotone (fun i : Fin (n + 1) => u i.succ) :=
      fun i j hij => hmono (Fin.succ_le_succ_iff.2 hij)
    have hmesh' : ∀ i : Fin n, (fun i : Fin (n + 1) => u i.succ) i.succ
        - (fun i : Fin (n + 1) => u i.succ) i.castSucc ≤ δ := fun i => by
      show u i.succ.succ - u i.castSucc.succ ≤ δ
      rw [Fin.succ_castSucc i]
      exact hmesh i.succ
    have htag' : ∀ i : Fin n, (fun i : Fin (n + 1) => u i.succ) i.castSucc ≤ (fun i => τ i.succ) i
        ∧ (fun i => τ i.succ) i ≤ (fun i : Fin (n + 1) => u i.succ) i.succ := fun i => by
      show u i.castSucc.succ ≤ τ i.succ ∧ τ i.succ ≤ u i.succ.succ
      rw [Fin.succ_castSucc i]
      exact htag i.succ
    have h0' : 0 ≤ (fun i : Fin (n + 1) => u i.succ) 0 := le_trans h0 (hmono (Fin.zero_le _))
    have hT' : (fun i : Fin (n + 1) => u i.succ) (Fin.last n) ≤ T := by
      show u (Fin.last n).succ ≤ T
      rw [Fin.succ_last]
      exact hT
    have htail := q17_P_ofFn T δ n (fun i : Fin (n + 1) => u i.succ) (fun i => τ i.succ)
      hu' hmesh' htag' h0' hT'
    rw [Fin.succ_last] at htail
    obtain ⟨hτ, hτ'⟩ := htag 0
    refine (q17_P_cons T δ _ _ _ _ _ _).2 ⟨?_, ?_, ?_, ?_, ?_, ?_, htail⟩
    · exact congrArg u Fin.castSucc_zero
    · exact hmono (Fin.zero_le _)
    · exact hmesh 0
    · exact le_trans h0 (le_trans (hmono (Fin.zero_le _)) hτ)
    · exact le_trans hτ' (le_trans (hmono (Fin.le_last _)) hT)
    · intro z hz1 hz2
      exact abs_sub_le_iff.2 ⟨by linarith [hmesh 0], by linarith [hmesh 0]⟩

/-- Comparison of two `Fin` partitions of `[0,T]` (in `IsRS` form). -/
theorem q17_fin_rl (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (W : ℝ → ℝ → ℝ) (T δ c : ℝ)
    (hW0 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖G y - G x‖ ≤ W x y)
    (hWadd : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T → W x u + W u y ≤ W x y)
    (hc : 0 ≤ c)
    (hB : ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| ≤ 2 * δ → ‖B s - B t‖ ≤ c)
    (n m : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ) (v : Fin (m + 1) → ℝ) (σ : Fin m → ℝ)
    (hu : Monotone u) (hv : Monotone v)
    (hmu : ∀ i : Fin n, u i.succ - u i.castSucc ≤ δ) (hmv : ∀ j : Fin m, v j.succ - v j.castSucc ≤ δ)
    (htu : ∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ)
    (htv : ∀ j : Fin m, v j.castSucc ≤ σ j ∧ σ j ≤ v j.succ)
    (hu0 : u 0 = 0) (huT : u (Fin.last n) = T) (hv0 : v 0 = 0) (hvT : v (Fin.last m) = T) :
    ‖∑ i, B (τ i) (G (u i.succ) - G (u i.castSucc))
        - ∑ j, B (σ j) (G (v j.succ) - G (v j.castSucc))‖ ≤ c * W 0 T := by
  have hP := q17_P_ofFn T δ n u τ hu hmu htu (by rw [hu0]) (by rw [huT])
  have hQ := q17_P_ofFn T δ m v σ hv hmv htv (by rw [hv0]) (by rw [hvT])
  rw [hu0, huT] at hP
  rw [hv0, hvT] at hQ
  have hlen : (q17_cells u τ).length + (q17_cells v σ).length ≤ n + m := by
    simp [q17_cells]
  have h := q17_rl B G W T δ c hW0 hWadd hc hB (n + m) (q17_cells u τ) (q17_cells v σ) 0 T
    hlen le_rfl le_rfl hP hQ
  rw [q17_sum_cells, q17_sum_cells] at h
  exact h

/-- Uniform partition with `N` cells: points `i T / N`. -/
def q17_uf (T : ℝ) (N : ℕ) : Fin (N + 1) → ℝ := fun i => (i.val : ℝ) * (T / N)

/-- Left-endpoint tags of the uniform partition. -/
def q17_ut (T : ℝ) (N : ℕ) : Fin N → ℝ := fun i => q17_uf T N i.castSucc

/-- RS sum of the uniform partition with `N` cells. -/
def q17_S (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (T : ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin N, B (q17_ut T N i) (G (q17_uf T N i.succ) - G (q17_uf T N i.castSucc))

theorem q17_uf_mono (T : ℝ) (hT : 0 ≤ T) (N : ℕ) : Monotone (q17_uf T N) := by
  intro i j hij
  unfold q17_uf
  have : (i.val : ℝ) ≤ j.val := Nat.cast_le.2 hij
  exact mul_le_mul_of_nonneg_right this (div_nonneg hT (Nat.cast_nonneg _))

theorem q17_uf_zero (T : ℝ) (N : ℕ) : q17_uf T N 0 = 0 := by
  simp [q17_uf]

theorem q17_uf_last (T : ℝ) (N : ℕ) (hN : 1 ≤ N) : q17_uf T N (Fin.last N) = T := by
  unfold q17_uf
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Fin.val_last]
  field_simp

theorem q17_uf_mesh (T : ℝ) (N : ℕ) (i : Fin N) :
    q17_uf T N i.succ - q17_uf T N i.castSucc = T / N := by
  unfold q17_uf
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- Modulus of continuity of a continuous integrand on `[0,T]`. -/
theorem q17_modulus (T : ℝ) (B : ℝ → (E →L[ℝ] ℝ)) (hBc : ContinuousOn B (Set.Icc 0 T))
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ s t : ℝ, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| < δ → ‖B s - B t‖ < η := by
  have hu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous hBc
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu η hη
  refine ⟨δ, hδ, fun s t hs hsT ht htT hst => ?_⟩
  have := h s ⟨hs, hsT⟩ t ⟨ht, htT⟩ (by rw [Real.dist_eq]; exact hst)
  rwa [dist_eq_norm] at this

theorem q17_uf_valid (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    Monotone (q17_uf T (m + 1)) ∧
    (∀ i : Fin (m + 1), q17_uf T (m + 1) i.succ - q17_uf T (m + 1) i.castSucc
        = T / ((m + 1 : ℕ) : ℝ)) ∧
    (∀ i : Fin (m + 1), q17_uf T (m + 1) i.castSucc ≤ q17_ut T (m + 1) i ∧
        q17_ut T (m + 1) i ≤ q17_uf T (m + 1) i.succ) ∧
    q17_uf T (m + 1) 0 = 0 ∧ q17_uf T (m + 1) (Fin.last (m + 1)) = T :=
  ⟨q17_uf_mono T hT (m + 1), fun i => q17_uf_mesh T (m + 1) i,
    fun i => ⟨le_rfl, q17_uf_mono T hT (m + 1) (Fin.castSucc_lt_succ (i := i)).le⟩,
    q17_uf_zero T (m + 1), q17_uf_last T (m + 1) (by omega)⟩

theorem q17_small (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (K : ℕ) (hK : T / δ < K) (N : ℕ)
    (hN : K ≤ N) : T / (N : ℝ) ≤ δ := by
  have hK0 : (0 : ℝ) < K := lt_trans (div_pos hT hδ) hK
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hK0 (by exact_mod_cast hN)
  rw [div_le_iff₀ hN0]
  have h1 : T < K * δ := (div_lt_iff₀ hδ).1 hK
  have h2 : (K : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- Key estimate: an arbitrary admissible `Fin` partition of `[0,T]` with mesh `≤ δ` is within
`η W(0,T)` of every uniform partition with mesh `≤ δ`. -/
theorem q17_key (T : ℝ) (hT : 0 < T) (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (W : ℝ → ℝ → ℝ)
    (hW0 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖G y - G x‖ ≤ W x y)
    (hWadd : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T → W x u + W u y ≤ W x y)
    (hBc : ContinuousOn B (Set.Icc 0 T)) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), Monotone u →
      (∀ i : Fin n, u i.succ - u i.castSucc ≤ δ) →
      (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) →
      u 0 = 0 → u (Fin.last n) = T →
      ∀ m : ℕ, T / ((m + 1 : ℕ) : ℝ) ≤ δ →
        ‖∑ i, B (τ i) (G (u i.succ) - G (u i.castSucc)) - q17_S B G T (m + 1)‖ ≤ η * W 0 T := by
  obtain ⟨δm, hδm, hmod⟩ := q17_modulus T B hBc η hη
  refine ⟨δm / 4, by positivity, fun n u τ hu hmu htu hu0 huT m hTm => ?_⟩
  have hB : ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| ≤ 2 * (δm / 4) → ‖B s - B t‖ ≤ η :=
    fun s t hs hsT ht htT hst => (hmod s t hs hsT ht htT (by linarith)).le
  obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := q17_uf_valid T hT.le m
  have h := q17_fin_rl B G W T (δm / 4) η hW0 hWadd hη.le hB n (m + 1) u τ
    (q17_uf T (m + 1)) (q17_ut T (m + 1)) hu hv1 hmu
    (fun j => by rw [hv2 j]; exact hTm) htu hv3 hu0 huT hv4 hv5
  unfold q17_S
  exact h

theorem q17_exists (T : ℝ) (hT : 0 < T) (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (W : ℝ → ℝ → ℝ)
    (hW0 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖G y - G x‖ ≤ W x y)
    (hWadd : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T → W x u + W u y ≤ W x y)
    (hBc : ContinuousOn B (Set.Icc 0 T)) :
    ∃ I : ℝ, IsRS T (fun τ a b => B τ (G b - G a)) I := by
  have hW00 : 0 ≤ W 0 T := le_trans (norm_nonneg _) (hW0 0 T le_rfl hT.le le_rfl)
  -- the uniform partitions form a Cauchy family
  have hcauchy : CauchySeq (fun n : ℕ => q17_S B G T (n + 1)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hη : 0 < ε / (2 * (W 0 T + 1)) := by positivity
    have hηW : (ε / (2 * (W 0 T + 1))) * (W 0 T + 1) = ε / 2 := by
      field_simp
    obtain ⟨δ, hδ, hk⟩ := q17_key T hT B G W hW0 hWadd hBc _ hη
    obtain ⟨K, hK⟩ : ∃ K : ℕ, T / δ < K := exists_nat_gt _
    refine ⟨K, fun n hn => ?_⟩
    rw [Real.dist_eq]
    show |q17_S B G T (n + 1) - q17_S B G T (K + 1)| < ε
    obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := q17_uf_valid T hT.le n
    have h : ‖q17_S B G T (n + 1) - q17_S B G T (K + 1)‖ ≤
        (ε / (2 * (W 0 T + 1))) * W 0 T :=
      hk (n + 1) (q17_uf T (n + 1)) (q17_ut T (n + 1)) hv1
        (fun i => by rw [hv2 i]; exact q17_small T δ hT hδ K hK (n + 1) (by omega))
        hv3 hv4 hv5 K (q17_small T δ hT hδ K hK (K + 1) (by omega))
    rw [Real.norm_eq_abs] at h
    have h5 : (ε / (2 * (W 0 T + 1))) * (W 0 T + 1)
        = (ε / (2 * (W 0 T + 1))) * W 0 T + ε / (2 * (W 0 T + 1)) := by ring
    linarith
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I, fun ε hε => ?_⟩
  have hη : 0 < ε / (2 * (W 0 T + 1)) := by positivity
  have hηW : (ε / (2 * (W 0 T + 1))) * (W 0 T + 1) = ε / 2 := by
    field_simp
  obtain ⟨δ, hδ, hk⟩ := q17_key T hT B G W hW0 hWadd hBc _ hη
  obtain ⟨K, hK⟩ : ∃ K : ℕ, T / δ < K := exists_nat_gt _
  obtain ⟨k0, hk0⟩ := Metric.tendsto_atTop.1 hI (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun n u τ hsm hu0 huT htag hmesh => ?_⟩
  set m : ℕ := max K k0 with hmdef
  have hmono : Monotone u := hsm.monotone
  have hmesh' : ∀ i : Fin n, u i.succ - u i.castSucc ≤ δ := fun i => (hmesh i).le
  have h1 := hk n u τ hmono hmesh' htag hu0 huT m
    (q17_small T δ hT hδ K hK (m + 1) (by omega))
  have h2 : dist (q17_S B G T (m + 1)) I < ε / 2 := hk0 m (le_max_right K k0)
  rw [Real.dist_eq] at h2
  rw [Real.norm_eq_abs] at h1
  have h3 := abs_sub_le (∑ i, B (τ i) (G (u i.succ) - G (u i.castSucc)))
    (q17_S B G T (m + 1)) I
  show |∑ i, B (τ i) (G (u i.succ) - G (u i.castSucc)) - I| < ε
  have h5 : (ε / (2 * (W 0 T + 1))) * (W 0 T + 1)
      = (ε / (2 * (W 0 T + 1))) * W 0 T + ε / (2 * (W 0 T + 1)) := by ring
  linarith

end Q17Exists

end HRS.Sec7
