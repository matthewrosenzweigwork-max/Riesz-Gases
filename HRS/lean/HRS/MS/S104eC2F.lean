import HRS.MS.S104eC2E

/-!
# S104E route C, packet C2, part F: `c2_Q_bd` and `c2_Q_van`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  `s103bQ d s ρ f = -∑_i F_i ∂_i f + ∑_i movForce (ρ ∂_i f) · i` with `F_i = movForce ρ · i`.

* `s104c2_Q_bd_sharp`: `Bd j (C A B) (s103bQ d s ρ f)` for `ρ ∈ U2Dec (j+1) L A`, `f ∈ HolB j η B`, every `η ∈ (max 0 (s-d+1), 1)`;
* `c2_Q_bd`: the skeleton form (`C (1+A) B`, hypothesis `U2Dec (j+3)`);
* `c2_Q_van`: `VanB j (s103bQ d s ρ f)` (the hypothesis `VanB (j+1) f` is not needed).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem s104c2_Q_bd_sharp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (ρ : Euc d → ℝ), 0 ≤ A → U2Dec (j + 1) L A ρ →
      ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → Bd j (C * A * B) (s103bQ d s ρ f) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd j (L := L) (by linarith)
  choose Ci hCi0 hCi using fun i : Fin d =>
    s104c2_force_term hd hs0 hsd j hη0 hη1 hL (EuclideanSpace.single i (1 : ℝ)) i (by simp)
  refine ⟨d * (2 ^ j * Cf) + ∑ i, Ci i, by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hCi0 i
    positivity, fun A ρ hA hρ B f hf => ?_⟩
  have hB0 : 0 ≤ B := hf.bd.nonneg
  have hFS : ∀ i : Fin d, Sy j (Cf * A) (fun x => movForce d s ρ x i) := fun i => hCf A ρ hA hρ i
  have hDg : ∀ i : Fin d, Bd j B (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) := fun i => by
    have := hf.bd.deriv (N := j) (EuclideanSpace.single i (1 : ℝ))
    simpa using this
  have T1 : Bd j (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ j * (Cf * A) * B))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ x i *
        fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => ((hFS i).bd.mul (hDg i)).smul (-1))
  have T2 : Bd j (∑ i : Fin d, Ci i * A * B)
      (fun x => ∑ i : Fin d, movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i) :=
    Bd.sum Finset.univ _ _ (fun i _ => by
      obtain ⟨h1, h2, _⟩ := hCi i A ρ hA hρ B f hf
      exact ⟨h1, h2⟩)
  have hsum := T1.add T2
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one, one_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have : 0 ≤ A * B := mul_nonneg hA hB0
  nlinarith [mul_nonneg this hCf0]

theorem c2_Q_bd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (ρ : Euc d → ℝ), 0 ≤ A → U2Dec (j + 3) L A ρ →
      ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → Bd j (C * (1 + A) * B) (s103bQ d s ρ f) := by
  obtain ⟨C, hC0, hC⟩ := s104c2_Q_bd_sharp hd hs0 hsd j hη0 hη1 hL
  refine ⟨C, hC0, fun A ρ hA hρ B f hf => ?_⟩
  have hρ' : U2Dec (j + 1) L A ρ := ⟨hρ.1.of_le (by exact_mod_cast (by omega : j + 1 ≤ j + 3)),
    fun m hm => hρ.2 m (by omega)⟩
  refine (hC A ρ hA hρ' B f hf).mono_A ?_
  have hB0 : 0 ≤ B := hf.bd.nonneg
  nlinarith [mul_nonneg hC0 hB0]

/-! ### Vanishing at infinity -/

lemma s104c2_vanC_zero (j : ℕ) : ContDiff ℝ j (fun _ : Euc d => (0 : ℝ)) ∧ VanB j (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun i hi => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using tendsto_const_nhds
  · simpa [iteratedFDeriv_const_of_ne hi0.ne'] using tendsto_const_nhds

lemma s104c2_vanC_add {j : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ j f ∧ VanB j f)
    (hg : ContDiff ℝ j g ∧ VanB j g) :
    ContDiff ℝ j (fun x => f x + g x) ∧ VanB j (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun i hi => ?_⟩
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) (by simpa using (hf.2 i hi).add (hg.2 i hi))
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hi)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hi)).contDiffAt]
  exact norm_add_le _ _

lemma s104c2_vanC_neg {j : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ j f ∧ VanB j f) :
    ContDiff ℝ j (fun x => (-1 : ℝ) * f x) ∧ VanB j (fun x => (-1 : ℝ) * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun i hi => ?_⟩
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) (by simpa using (hf.2 i hi))
  have e : (fun x => (-1 : ℝ) * f x) = (-1 : ℝ) • f := by funext x; simp
  rw [e, iteratedFDeriv_const_smul_apply (hf.1.of_le (by exact_mod_cast hi)).contDiffAt, norm_smul]
  simp

lemma s104c2_vanC_sum {j : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ)
    (h : ∀ i ∈ S, ContDiff ℝ j (f i) ∧ VanB j (f i)) :
    ContDiff ℝ j (fun x => ∑ i ∈ S, f i x) ∧ VanB j (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using s104c2_vanC_zero (d := d) j
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := s104c2_vanC_add h1 h2
    simpa only [Finset.sum_insert ha] using this

lemma s104c2_sy_van {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : Sy N A f) : VanB N f := by
  intro i hi
  have h1 : Tendsto (fun x : Euc d => (1 + ‖x‖)⁻¹) (cocompact (Euc d)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_norm_cocompact_atTop)
  exact squeeze_zero (fun x => norm_nonneg _) (fun x => h.2 i hi x) (by simpa using h1.const_mul A)

theorem c2_Q_van (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) {A : ℝ} {ρ : Euc d → ℝ}
    (hρ : U2Dec (j + 3) L A ρ) {B : ℝ} {f : Euc d → ℝ} (hf : HolB j η B f) (hv : VanB (j + 1) f) :
    VanB j (s103bQ d s ρ f) := by
  have hρ' : U2Dec (j + 1) L A ρ := ⟨hρ.1.of_le (by exact_mod_cast (by omega : j + 1 ≤ j + 3)),
    fun m hm => hρ.2 m (by omega)⟩
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hρ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd j (L := L) (by linarith)
  choose Ci hCi0 hCi using fun i : Fin d =>
    s104c2_force_term hd hs0 hsd j hη0 hη1 hL (EuclideanSpace.single i (1 : ℝ)) i (by simp)
  have hFS : ∀ i : Fin d, Sy j (Cf * A) (fun x => movForce d s ρ x i) := fun i => hCf A ρ hA hρ' i
  have hDg : ∀ i : Fin d, Bd j B (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) := fun i => by
    have := hf.bd.deriv (N := j) (EuclideanSpace.single i (1 : ℝ))
    simpa using this
  have T1 := s104c2_vanC_sum (j := j) Finset.univ
    (fun i x => (-1 : ℝ) * (movForce d s ρ x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))))
    (fun i _ => s104c2_vanC_neg (j := j) ⟨((hFS i).mul_bd (hDg i)).1, s104c2_sy_van ((hFS i).mul_bd (hDg i))⟩)
  have T2 := s104c2_vanC_sum (j := j) Finset.univ
    (fun i x => movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i)
    (fun i _ => by
      obtain ⟨h1, _, h3⟩ := hCi i A ρ hA hρ' B f hf
      exact ⟨h1, h3⟩)
  exact (s104c2_vanC_add T1 T2).2

end HRS.MS.S104e.C

end
