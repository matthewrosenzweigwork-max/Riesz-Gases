import HRS.PDE.MovGAux2

/-!
# MOVG Aux3: configuration slicing and the Q-IBP identity

`q(X) = ∏_{i≠j} Ga(a/2)(x_i - x_j) · ∏_i π(x_i)`; `Fin.insertNth` decomposition of `q`, Fubini over the `i`-th particle,
bounds and integrability on `Config d N`, and `movg_Q_ibp`:
`∫ q R(x_i) = ∫ q ⟨V(x_i), a ∑_{k≠i} ∇g(x_i-x_k) - ∇b(x_i)⟩/ρ(x_i)` for `R = div V / ρ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movg_prod_erase {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → M) :
    ∏ c ∈ Finset.univ.erase i, f c = ∏ k : Fin n, f (i.succAbove k) := by
  have : (Finset.univ : Finset (Fin (n + 1))).erase i = Finset.univ.map (Fin.succAboveEmb i) := by
    conv_lhs => rw [Fin.univ_succAbove n i]
    exact Finset.erase_cons _
  rw [this, Finset.prod_map]
  rfl

theorem movg_sum_erase {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    ∑ c ∈ Finset.univ.erase i, f c = ∑ k : Fin n, f (i.succAbove k) := by
  have : (Finset.univ : Finset (Fin (n + 1))).erase i = Finset.univ.map (Fin.succAboveEmb i) := by
    conv_lhs => rw [Fin.univ_succAbove n i]
    exact Finset.erase_cons _
  rw [this, Finset.sum_map]
  rfl

variable {s a : ℝ}

/-- The pair weight `∏_{i≠j} Ga(a/2)(x_i - x_j)` (vanishing exactly on collisions). -/
def movg_pairW (d : ℕ) (s a : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  ∏ i, ∏ j, (if i = j then 1 else movg_Ga d s (a / 2) (X i - X j))

theorem movg_pairW_insertNth {n : ℕ} (i : Fin (n + 1)) (x : Torus d) (Y : Config d n) :
    movg_pairW d s a (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) =
      (∏ k, movg_Ga d s a (x - Y k)) * movg_pairW d s a Y := by
  unfold movg_pairW
  simp only [Fin.prod_univ_succAbove _ i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    if_true, Fin.succAbove_ne, (Fin.succAbove_ne i _).symm, if_false, Fin.succAbove_right_inj, one_mul,
    Finset.prod_mul_distrib]
  have hG : ∀ z : Torus d, movg_Ga d s (a / 2) z * movg_Ga d s (a / 2) (-z) = movg_Ga d s a z := fun z => by
    rw [movg_Ga_mul_neg]; congr 1; ring
  have h1 : (∏ l, movg_Ga d s (a / 2) (x - Y l)) * ∏ k, movg_Ga d s (a / 2) (Y k - x) =
      ∏ k, movg_Ga d s a (x - Y k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have := hG (x - Y k)
    rwa [neg_sub] at this
  rw [← h1]
  ring

/-- Fubini over the `i`-th particle. -/
theorem movg_integral_slice {n : ℕ} (i : Fin (n + 1)) (F : Config d (n + 1) → ℝ) (hF : Integrable F) :
    ∫ X, F X = ∫ Y : Config d n, ∫ x : Torus d, F (Fin.insertNth (α := fun _ => Torus d) i x Y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Torus d) i with he
  have hmp : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Torus d) i
  have hsymm : MeasurePreserving e.symm (volume : Measure (Torus d × Config d n)) volume :=
    MeasurePreserving.symm e hmp
  have h1 : ∫ X, F X = ∫ p : Torus d × Config d n, F (e.symm p) := (hsymm.integral_comp' F).symm
  have hint : Integrable (fun p : Torus d × Config d n => F (e.symm p)) :=
    (hsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  rfl

/-! ### Bounds on the pair weight -/

theorem movg_prod_le {ι : Type*} [Fintype ι] (t : Finset ι) (f : ι → ℝ) {M : ℝ} (hM : 1 ≤ M)
    (h0 : ∀ c, 0 ≤ f c) (h1 : ∀ c, f c ≤ M) : ∏ c ∈ t, f c ≤ M ^ Fintype.card ι :=
  calc ∏ c ∈ t, f c ≤ ∏ c ∈ t, M := Finset.prod_le_prod₀ (fun c _ => h0 c) (fun c _ => h1 c)
    _ = M ^ t.card := Finset.prod_const _
    _ ≤ M ^ Fintype.card ι := pow_le_pow_right₀ hM (Finset.card_le_univ t)

/-- The pair-weight factor `h p c`. -/
def movg_hf (d : ℕ) (s a : ℝ) {N : ℕ} (X : Config d N) (p c : Fin N) : ℝ :=
  if p = c then 1 else movg_Ga d s (a / 2) (X p - X c)

theorem movg_pairW_eq (X : Config d N) : movg_pairW d s a X = ∏ p, ∏ c, movg_hf d s a X p c := rfl

theorem movg_hf_nonneg (X : Config d N) (p c : Fin N) : 0 ≤ movg_hf d s a X p c := by
  unfold movg_hf; split_ifs
  · exact zero_le_one
  · exact movg_Ga_nonneg _ _ _

theorem movg_hf_le {B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a) (X : Config d N)
    (p c : Fin N) : movg_hf d s a X p c ≤ max (Real.exp (a / 2 * B)) 1 := by
  unfold movg_hf; split_ifs
  · exact le_max_right _ _
  · exact (movg_Ga_le (by linarith) hB _).trans (le_max_left _ _)

theorem movg_pairW_nonneg (X : Config d N) : 0 ≤ movg_pairW d s a X :=
  Finset.prod_nonneg fun p _ => Finset.prod_nonneg fun c _ => movg_hf_nonneg X p c

theorem movg_pairW_le_pow {B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a)
    (X : Config d N) : movg_pairW d s a X ≤ ((max (Real.exp (a / 2 * B)) 1) ^ N) ^ N := by
  set M := max (Real.exp (a / 2 * B)) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have h1 : ∀ p, ∏ c, movg_hf d s a X p c ≤ M ^ N := fun p => by
    simpa using movg_prod_le Finset.univ (fun c => movg_hf d s a X p c) hM1 (fun c => movg_hf_nonneg X p c)
      (fun c => movg_hf_le hB ha X p c)
  have h2 : 1 ≤ M ^ N := one_le_pow₀ hM1
  rw [movg_pairW_eq]
  simpa using movg_prod_le Finset.univ (fun p => ∏ c, movg_hf d s a X p c) h2
    (fun p => Finset.prod_nonneg fun c _ => movg_hf_nonneg X p c) h1

theorem movg_pairW_le_Ga {B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a)
    {i k : Fin N} (hik : i ≠ k) (X : Config d N) :
    movg_pairW d s a X ≤ (((max (Real.exp (a / 2 * B)) 1) ^ N) * (((max (Real.exp (a / 2 * B)) 1) ^ N) *
      ((max (Real.exp (a / 2 * B)) 1) ^ N) ^ N)) * movg_Ga d s a (X i - X k) := by
  classical
  set M := max (Real.exp (a / 2 * B)) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have h2 : 1 ≤ M ^ N := one_le_pow₀ hM1
  have hF0 : ∀ p, 0 ≤ ∏ c, movg_hf d s a X p c := fun p => Finset.prod_nonneg fun c _ => movg_hf_nonneg X p c
  have hF1 : ∀ p, ∏ c, movg_hf d s a X p c ≤ M ^ N := fun p => by
    simpa using movg_prod_le Finset.univ (fun c => movg_hf d s a X p c) hM1 (fun c => movg_hf_nonneg X p c)
      (fun c => movg_hf_le hB ha X p c)
  have hki : k ≠ i := hik.symm
  have hkmem : k ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩
  have e1 : movg_pairW d s a X = (∏ c, movg_hf d s a X i c) *
      ((∏ c, movg_hf d s a X k c) * ∏ p ∈ (Finset.univ.erase i).erase k, ∏ c, movg_hf d s a X p c) := by
    rw [movg_pairW_eq, ← Finset.mul_prod_erase Finset.univ (fun p => ∏ c, movg_hf d s a X p c) (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun p => ∏ c, movg_hf d s a X p c) hkmem]
  have e2 : ∏ c, movg_hf d s a X i c = movg_hf d s a X i k * ∏ c ∈ Finset.univ.erase k, movg_hf d s a X i c :=
    (Finset.mul_prod_erase Finset.univ (fun c => movg_hf d s a X i c) (Finset.mem_univ k)).symm
  have e3 : ∏ c, movg_hf d s a X k c = movg_hf d s a X k i * ∏ c ∈ Finset.univ.erase i, movg_hf d s a X k c :=
    (Finset.mul_prod_erase Finset.univ (fun c => movg_hf d s a X k c) (Finset.mem_univ i)).symm
  have hRi : ∏ c ∈ Finset.univ.erase k, movg_hf d s a X i c ≤ M ^ N := by
    simpa using movg_prod_le (Finset.univ.erase k) (fun c => movg_hf d s a X i c) hM1
      (fun c => movg_hf_nonneg X i c) (fun c => movg_hf_le hB ha X i c)
  have hRk : ∏ c ∈ Finset.univ.erase i, movg_hf d s a X k c ≤ M ^ N := by
    simpa using movg_prod_le (Finset.univ.erase i) (fun c => movg_hf d s a X k c) hM1
      (fun c => movg_hf_nonneg X k c) (fun c => movg_hf_le hB ha X k c)
  have hrest : ∏ p ∈ (Finset.univ.erase i).erase k, ∏ c, movg_hf d s a X p c ≤ (M ^ N) ^ N := by
    simpa using movg_prod_le ((Finset.univ.erase i).erase k) (fun p => ∏ c, movg_hf d s a X p c) h2 hF0 hF1
  have hRi0 : 0 ≤ ∏ c ∈ Finset.univ.erase k, movg_hf d s a X i c := Finset.prod_nonneg fun c _ => movg_hf_nonneg X i c
  have hRk0 : 0 ≤ ∏ c ∈ Finset.univ.erase i, movg_hf d s a X k c := Finset.prod_nonneg fun c _ => movg_hf_nonneg X k c
  have hrest0 : 0 ≤ ∏ p ∈ (Finset.univ.erase i).erase k, ∏ c, movg_hf d s a X p c :=
    Finset.prod_nonneg fun p _ => hF0 p
  have hGG : movg_hf d s a X i k * movg_hf d s a X k i = movg_Ga d s a (X i - X k) := by
    unfold movg_hf
    rw [if_neg hik, if_neg hki, show X k - X i = -(X i - X k) from (neg_sub _ _).symm, movg_Ga_mul_neg]
    congr 1; ring
  rw [e1, e2, e3]
  set Ri := ∏ c ∈ Finset.univ.erase k, movg_hf d s a X i c
  set Rk := ∏ c ∈ Finset.univ.erase i, movg_hf d s a X k c
  set Rr := ∏ p ∈ (Finset.univ.erase i).erase k, ∏ c, movg_hf d s a X p c
  have : movg_hf d s a X i k * Ri * (movg_hf d s a X k i * Rk * Rr) =
      (movg_hf d s a X i k * movg_hf d s a X k i) * (Ri * (Rk * Rr)) := by ring
  rw [this, hGG]
  have h3 : Ri * (Rk * Rr) ≤ M ^ N * (M ^ N * (M ^ N) ^ N) := by
    gcongr
  have := movg_Ga_nonneg s a (X i - X k)
  nlinarith

/-! ### The unnormalised Gibbs density `q` -/

/-- `q(X) = ∏_{i≠j} Ga(a/2)(x_i - x_j) · ∏_i π(x_i)`. -/
def movg_q (d : ℕ) (s a : ℝ) (π : Torus d → ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  movg_pairW d s a X * ∏ i, π (X i)

theorem movg_q_insertNth {n : ℕ} (π : Torus d → ℝ) (i : Fin (n + 1)) (x : Torus d) (Y : Config d n) :
    movg_q d s a π (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) =
      movg_q d s a π Y * ((∏ k, movg_Ga d s a (x - Y k)) * π x) := by
  unfold movg_q
  rw [movg_pairW_insertNth, Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

theorem movg_q_measurable (hGa : Measurable (movg_Ga d s (a / 2))) {π : Torus d → ℝ} (hπ : Measurable π) :
    Measurable (movg_q d s a π : Config d N → ℝ) := by
  unfold movg_q movg_pairW
  refine (Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_).mul
    (Finset.measurable_prod _ fun i _ => hπ.comp (measurable_pi_apply i))
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false]
    exact hGa.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem movg_q_nonneg {π : Torus d → ℝ} (hπ : ∀ x, 0 ≤ π x) (X : Config d N) : 0 ≤ movg_q d s a π X :=
  mul_nonneg (movg_pairW_nonneg X) (Finset.prod_nonneg fun i _ => hπ _)

theorem movg_q_le_const {B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a)
    {π : Torus d → ℝ} (hπ0 : ∀ x, 0 ≤ π x) {Cπ : ℝ} (hπ : ∀ x, π x ≤ Cπ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Config d N, movg_q d s a π X ≤ C := by
  set M := max (Real.exp (a / 2 * B)) 1 with hM
  set P := max Cπ 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  have h1 : ∀ X : Config d N, ∏ i, π (X i) ≤ P ^ N := fun X => by
    simpa using movg_prod_le Finset.univ (fun i => π (X i)) hP1 (fun i => hπ0 _)
      (fun i => (hπ _).trans (le_max_left _ _))
  refine ⟨((M ^ N) ^ N) * P ^ N, by positivity, fun X => ?_⟩
  unfold movg_q
  exact mul_le_mul (movg_pairW_le_pow hB ha X) (h1 X) (Finset.prod_nonneg fun i _ => hπ0 _) (by positivity)

theorem movg_q_le_Ga {B : ℝ} (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (ha : 0 ≤ a)
    {π : Torus d → ℝ} (hπ0 : ∀ x, 0 ≤ π x) {Cπ : ℝ} (hπ : ∀ x, π x ≤ Cπ) {i k : Fin N} (hik : i ≠ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Config d N, movg_q d s a π X ≤ C * movg_Ga d s a (X i - X k) := by
  set M := max (Real.exp (a / 2 * B)) 1 with hM
  set P := max Cπ 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  have h1 : ∀ X : Config d N, ∏ i, π (X i) ≤ P ^ N := fun X => by
    simpa using movg_prod_le Finset.univ (fun i => π (X i)) hP1 (fun i => hπ0 _)
      (fun i => (hπ _).trans (le_max_left _ _))
  refine ⟨((M ^ N) * ((M ^ N) * ((M ^ N) ^ N))) * P ^ N, by positivity, fun X => ?_⟩
  unfold movg_q
  have h2 := movg_pairW_le_Ga hB ha hik X
  have h3 := h1 X
  have h4 : 0 ≤ ∏ i, π (X i) := Finset.prod_nonneg fun i _ => hπ0 _
  have h5 := movg_Ga_nonneg s a (X i - X k)
  calc movg_pairW d s a X * ∏ i, π (X i)
      ≤ ((M ^ N) * ((M ^ N) * ((M ^ N) ^ N)) * movg_Ga d s a (X i - X k)) * P ^ N :=
        mul_le_mul h2 h3 h4 (by positivity)
    _ = _ := by ring

theorem movg_E_integrable_config (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) {i k : Fin N}
    (hik : i ≠ k) :
    Integrable (fun X : Config d N => movg_Ga d s a (X i - X k) * ‖periodicRieszGrad d s (X i - X k)‖) := by
  have hmp := measurePreserving_sub_coord (d := d) (N := N) hik
  have hint := movg_Ga_grad_integrable hd hs0 hsd ha
  have hm : AEStronglyMeasurable (fun z : Torus d => movg_Ga d s a z * ‖periodicRieszGrad d s z‖) volume :=
    ((movg_Ga_continuous hd hs0 hsd ha).measurable.mul
      (KernelGrad.measurable_periodicRieszGrad hsd).norm).aestronglyMeasurable
  exact (hmp.integrable_comp hm).2 hint

/-! ### The Q-IBP identity -/

theorem movg_Q_ibp_inner (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) {n : ℕ} (i : Fin (n + 1))
    {ρ : Torus d → ℝ} (hρp : ∀ x, 0 < ρ x) {b : Torus d → ℝ} (hb : Torus.IsCk 1 b)
    {V u : Fin d → Torus d → ℝ} (hV : ∀ j, Torus.IsCk 1 (V j)) (hu : ∀ j x, V j x = ρ x * u j x)
    (Y : Config d n) :
    ∫ x : Torus d, movg_q d s a (fun x => ρ x * Real.exp (b x))
        (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) *
        ((∑ j, Torus.partialDeriv j (V j) x) / ρ x) =
    ∫ x : Torus d, movg_q d s a (fun x => ρ x * Real.exp (b x))
        (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) *
        ∑ j, u j x * (a * ∑ k ∈ Finset.univ.erase i,
          (periodicRieszGrad d s (x - (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) k)).ofLp j -
          Torus.partialDeriv j b x) := by
  have h1 := movg_slice_ibp' (Y := Y) hd hs0 hsd ha hb hV
  have e1 : ∀ x : Torus d, movg_q d s a (fun x => ρ x * Real.exp (b x))
        (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) *
        ((∑ j, Torus.partialDeriv j (V j) x) / ρ x) =
      movg_q d s a (fun x => ρ x * Real.exp (b x)) Y *
        ((∑ j, Torus.partialDeriv j (V j) x) * movg_wt d s a Y b x) := by
    intro x
    rw [movg_q_insertNth]
    have := (hρp x).ne'
    unfold movg_wt
    field_simp
  have e2 : ∀ x : Torus d, movg_q d s a (fun x => ρ x * Real.exp (b x))
        (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) *
        ∑ j, u j x * (a * ∑ k ∈ Finset.univ.erase i,
          (periodicRieszGrad d s (x - (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) k)).ofLp j -
          Torus.partialDeriv j b x) =
      movg_q d s a (fun x => ρ x * Real.exp (b x)) Y *
        (movg_wt d s a Y b x * ∑ j, V j x * (a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j -
          Torus.partialDeriv j b x)) := by
    intro x
    rw [movg_q_insertNth]
    have hsum : ∀ j, ∑ k ∈ Finset.univ.erase i,
        (periodicRieszGrad d s (x - (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) k)).ofLp j =
        ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j := by
      intro j
      rw [movg_sum_erase i (fun k => (periodicRieszGrad d s
        (x - (Fin.insertNth (α := fun _ => Torus d) i x Y : Config d (n + 1)) k)).ofLp j)]
      simp only [Fin.insertNth_apply_succAbove]
    simp only [hsum, hu]
    unfold movg_wt
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e1, e2, integral_const_mul]
  rw [h1]

theorem movg_decomp_aux (q a ub db : ℝ) {ι : Type*} (G : ι → ℝ) (t : Finset ι) :
    q * (ub * (a * ∑ k ∈ t, G k - db)) = ∑ k ∈ t, a * (q * (ub * G k)) - q * (ub * db) := by
  have : ∑ k ∈ t, a * (q * (ub * G k)) = q * (ub * (a * ∑ k ∈ t, G k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]; ring

theorem movg_Q_ibp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) {n : ℕ} (i : Fin (n + 1))
    {ρ : Torus d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x) {b : Torus d → ℝ} (hb : Torus.IsCk 1 b)
    {V u : Fin d → Torus d → ℝ} (hV : ∀ j, Torus.IsCk 1 (V j)) (hu : ∀ j x, V j x = ρ x * u j x) :
    Integrable (fun X : Config d (n + 1) => movg_q d s a (fun x => ρ x * Real.exp (b x)) X *
        ((∑ j, Torus.partialDeriv j (V j) (X i)) / ρ (X i))) ∧
    Integrable (fun X : Config d (n + 1) => movg_q d s a (fun x => ρ x * Real.exp (b x)) X *
        ∑ j, u j (X i) * (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X k)).ofLp j -
          Torus.partialDeriv j b (X i))) ∧
    ∫ X : Config d (n + 1), movg_q d s a (fun x => ρ x * Real.exp (b x)) X *
        ((∑ j, Torus.partialDeriv j (V j) (X i)) / ρ (X i)) =
    ∫ X : Config d (n + 1), movg_q d s a (fun x => ρ x * Real.exp (b x)) X *
        ∑ j, u j (X i) * (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X k)).ofLp j -
          Torus.partialDeriv j b (X i)) := by
  have hbc : Continuous b := mova_continuous_of_isCk hb
  set π : Torus d → ℝ := fun x => ρ x * Real.exp (b x) with hπdef
  have hπc : Continuous π := hρc.mul (Real.continuous_exp.comp hbc)
  have hπ0 : ∀ x, 0 ≤ π x := fun x => mul_nonneg (hρp x).le (Real.exp_pos _).le
  obtain ⟨Cπ, -, hCπ⟩ := mova_bound_of_continuous hπc
  have hπ : ∀ x, π x ≤ Cπ := fun x => (le_abs_self _).trans (hCπ x)
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  have hGa : Measurable (movg_Ga d s (a / 2)) :=
    (movg_Ga_continuous hd hs0 hsd (half_pos ha)).measurable
  have hqm : Measurable (movg_q d s a π : Config d (n + 1) → ℝ) := movg_q_measurable hGa hπc.measurable
  obtain ⟨Cq, hCq0, hCq⟩ := movg_q_le_const (N := n + 1) hB ha.le hπ0 hπ
  have hq0 := fun X : Config d (n + 1) => movg_q_nonneg (s := s) (a := a) hπ0 X
  have huc : ∀ j, Continuous (u j) := fun j => by
    have : u j = fun x => V j x / ρ x := funext fun x => by rw [hu j x]; field_simp [(hρp x).ne']
    rw [this]; exact (mova_continuous_of_isCk (hV j)).div hρc (fun x => (hρp x).ne')
  have hr : Continuous (fun x => (∑ j, Torus.partialDeriv j (V j) x) / ρ x) :=
    (continuous_finsetSum _ fun j _ => mova_continuous_partialDeriv (hV j) j).div hρc (fun x => (hρp x).ne')
  obtain ⟨Cr, -, hCr⟩ := mova_bound_of_continuous hr
  have hLint : Integrable (fun X : Config d (n + 1) => movg_q d s a π X *
      ((∑ j, Torus.partialDeriv j (V j) (X i)) / ρ (X i))) := by
    refine (integrable_const (Cq * Cr)).mono' ?_ (Filter.Eventually.of_forall fun X => ?_)
    · exact (hqm.mul (hr.measurable.comp (measurable_pi_apply i))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 X)]
      exact mul_le_mul (hCq X) (hCr _) (abs_nonneg _) hCq0
  have hGm : Measurable (periodicRieszGrad d s : Torus d → Euc d) := KernelGrad.measurable_periodicRieszGrad hsd
  have hGj : ∀ j : Fin d, Measurable (fun z : Torus d => (periodicRieszGrad d s z).ofLp j) := fun j =>
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp (p := 2) (X := Fin d → ℝ) |>.comp hGm)
  have hRint : Integrable (fun X : Config d (n + 1) => movg_q d s a π X *
      ∑ j, u j (X i) * (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X k)).ofLp j -
        Torus.partialDeriv j b (X i))) := by
    have e : (fun X : Config d (n + 1) => movg_q d s a π X *
      ∑ j, u j (X i) * (a * ∑ k ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X k)).ofLp j -
        Torus.partialDeriv j b (X i))) = fun X => ∑ j, (∑ k ∈ Finset.univ.erase i,
          a * (movg_q d s a π X * (u j (X i) * (periodicRieszGrad d s (X i - X k)).ofLp j)) -
          movg_q d s a π X * (u j (X i) * Torus.partialDeriv j b (X i))) := by
      funext X
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => movg_decomp_aux _ _ _ _ _ _
    rw [e]
    refine integrable_finsetSum _ fun j _ => ?_
    obtain ⟨Cu, hCu0, hCu⟩ := mova_bound_of_continuous (huc j)
    refine (integrable_finsetSum _ fun k hk => ?_).sub ?_
    · have hki : i ≠ k := (Finset.ne_of_mem_erase hk).symm
      obtain ⟨Ck, hCk0, hCk⟩ := movg_q_le_Ga hB ha.le hπ0 hπ hki
      refine ((movg_E_integrable_config hd hs0 hsd ha hki).const_mul (a * Ck * Cu)).mono' ?_
        (Filter.Eventually.of_forall fun X => ?_)
      · exact (measurable_const.mul (hqm.mul (((huc j).measurable.comp (measurable_pi_apply i)).mul
          ((hGj j).comp ((measurable_pi_apply i).sub (measurable_pi_apply k)))))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg (hq0 X)]
        have h1 := hCk X
        have h2 := hCu (X i)
        have h3 : |(periodicRieszGrad d s (X i - X k)).ofLp j| ≤ ‖periodicRieszGrad d s (X i - X k)‖ := by
          simpa using PiLp.norm_apply_le (periodicRieszGrad d s (X i - X k)) j
        have h4 := movg_Ga_nonneg s a (X i - X k)
        calc a * (movg_q d s a π X * (|u j (X i)| * |(periodicRieszGrad d s (X i - X k)).ofLp j|))
            ≤ a * ((Ck * movg_Ga d s a (X i - X k)) * (Cu * ‖periodicRieszGrad d s (X i - X k)‖)) := by
              gcongr
          _ = _ := by ring
    · obtain ⟨Cdb, -, hCdb⟩ := mova_bound_of_continuous (mova_continuous_partialDeriv hb j)
      refine (integrable_const (Cq * (Cu * Cdb))).mono' ?_ (Filter.Eventually.of_forall fun X => ?_)
      · exact (hqm.mul (((huc j).measurable.comp (measurable_pi_apply i)).mul
          ((mova_continuous_partialDeriv hb j).measurable.comp (measurable_pi_apply i)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 X), abs_mul]
        exact mul_le_mul (hCq X) (mul_le_mul (hCu _) (hCdb _) (abs_nonneg _)
          ((abs_nonneg _).trans (hCu (X i)))) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCq0
  refine ⟨hLint, hRint, ?_⟩
  rw [movg_integral_slice i _ hLint, movg_integral_slice i _ hRint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  simp only [Fin.insertNth_apply_same]
  exact movg_Q_ibp_inner hd hs0 hsd ha i hρp hb hV hu Y

end HRS
