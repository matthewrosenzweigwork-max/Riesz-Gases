import HRS.Stochastic.Simple

/-!
# EQ-LZ packet DL: the discrete Lyons-Zheng lemma (`eqlz_dl`), proof

Part 1 (this section): a maximal `L²` inequality for martingale differences on an abstract probability space (via
`doob_L2_discrete`).  Part 2: the discrete Lyons-Zheng lemma on a chain law `Λ` on `Fin (m+1) → E`.
All helper names carry the prefix `eqlzdl_`.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace HRS.MD.EQLZDl

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Orthogonality of an `L²` function measurable for `𝒢` to an `L²` function with vanishing `𝒢`-conditional mean. -/
theorem eqlzdl_orth [IsProbabilityMeasure P] {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {h ξ : Ω → ℝ}
    (hh : Measurable[𝒢] h) (hhL : MemLp h 2 P) (hξ : MemLp ξ 2 P) (hc : P[ξ | 𝒢] =ᵐ[P] 0) :
    ∫ ω, h ω * ξ ω ∂P = 0 := by
  have hint : Integrable (h * ξ) P := hhL.integrable_mul hξ
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := 𝒢) hh.stronglyMeasurable hint (hξ.integrable one_le_two)
  calc ∫ ω, h ω * ξ ω ∂P = ∫ ω, (P[h * ξ | 𝒢]) ω ∂P := (integral_condExp h𝒢).symm
    _ = ∫ ω, (h * P[ξ | 𝒢]) ω ∂P := integral_congr_ae h1
    _ = 0 := by
      have : (fun ω => (h * P[ξ | 𝒢]) ω) =ᵐ[P] fun _ => (0 : ℝ) := by
        filter_upwards [hc] with ω hω
        simp [hω]
      rw [integral_congr_ae this]; simp

/-- Maximal `L²` inequality for martingale differences. -/
theorem eqlzdl_maximal [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ) (n : ℕ)
    (hm : ∀ k < n, Measurable[ℱ (k + 1)] (ξ k)) (hL : ∀ k < n, MemLp (ξ k) 2 P)
    (hc : ∀ k < n, P[ξ k | ℱ k] =ᵐ[P] 0) :
    ∫⁻ ω, ⨆ j : Fin (n + 1), ENNReal.ofReal ((∑ i ∈ Finset.range j, ξ i ω) ^ 2) ∂P ≤
      ENNReal.ofReal (4 * ∑ k ∈ Finset.range n, ∫ ω, ξ k ω ^ 2 ∂P) := by
  classical
  set ξ' : ℕ → Ω → ℝ := fun k ω => if k < n then ξ k ω else 0 with hξ'
  set S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, ξ' i ω with hS
  have hξ'm : ∀ k, Measurable[ℱ (k + 1)] (ξ' k) := by
    intro k
    by_cases hk : k < n
    · simpa [hξ', hk] using hm k hk
    · simp [hξ', hk]
  have hξ'L : ∀ k, MemLp (ξ' k) 2 P := by
    intro k
    by_cases hk : k < n
    · simpa [hξ', hk] using hL k hk
    · simpa [hξ', hk] using (MemLp.zero : MemLp (fun _ : Ω => (0:ℝ)) 2 P)
  have hξ'c : ∀ k, P[ξ' k | ℱ k] =ᵐ[P] 0 := by
    intro k
    by_cases hk : k < n
    · simpa [hξ', hk] using hc k hk
    · have : ξ' k = fun _ => (0:ℝ) := by funext ω; simp [hξ', hk]
      rw [this, condExp_const (μ := P) (ℱ.le k)]; exact EventuallyEq.rfl
  have hSm : ∀ k, Measurable[ℱ k] (S k) := by
    intro k
    refine Finset.measurable_sum _ fun i hi => ?_
    exact (hξ'm i).mono (ℱ.mono (Finset.mem_range.1 hi)) le_rfl
  have hSL : ∀ k, MemLp (S k) 2 P := fun k => by
    have := memLp_finsetSum' (Finset.range k) (fun i _ => hξ'L i)
    convert this using 1
    funext ω; simp [hS]
  have hmart : Martingale S ℱ P := by
    refine martingale_of_condExp_sub_eq_zero_nat (μ := P) (𝒢 := ℱ) (f := S) (fun k => (hSm k).stronglyMeasurable)
      (fun k => (hSL k).integrable one_le_two) fun k => ?_
    have : S (k + 1) - S k = ξ' k := by
      funext ω; simp [hS, Finset.sum_range_succ]
    rw [this]; exact hξ'c k
  -- submartingale |S|
  have hsub : Submartingale (fun k ω => |S k ω|) ℱ P := by
    refine submartingale_nat (fun k => by simpa [Real.norm_eq_abs] using (hSm k).stronglyMeasurable.norm) (fun k =>
      ((hSL k).abs).integrable one_le_two) fun k => ?_
    have h1 := hmart.condExp_ae_eq (Nat.le_succ k)
    have hi1 : Integrable (S (k + 1)) P := (hSL _).integrable one_le_two
    have hi2 : Integrable (fun ω => |S (k + 1) ω|) P := ((hSL _).abs).integrable one_le_two
    have e1 := condExp_mono (m := ℱ k) hi1 hi2 (ae_of_all _ fun ω => le_abs_self (S (k + 1) ω))
    have e2 := condExp_mono (m := ℱ k) hi1.neg hi2 (ae_of_all _ fun ω => neg_le_abs (S (k + 1) ω))
    have e3 := condExp_neg (μ := P) (S (k + 1)) (ℱ k)
    filter_upwards [h1, e1, e2, e3] with ω h1 e1 e2 e3
    simp only [Pi.neg_apply] at e3
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdoob := HRS.SimpleIntegrand.doob_L2_discrete hsub (fun k ω => abs_nonneg _) (fun k => (hSL k).abs) n
  have hvar : ∀ m, ∫ ω, S m ω ^ 2 ∂P = ∑ k ∈ Finset.range m, ∫ ω, ξ' k ω ^ 2 ∂P := by
    intro m
    induction m with
    | zero => simp [hS]
    | succ m ih =>
      have hfun : (fun ω => S (m + 1) ω ^ 2) =
          fun ω => (S m ω ^ 2 + 2 * (S m ω * ξ' m ω)) + ξ' m ω ^ 2 := by
        funext ω; simp [hS, Finset.sum_range_succ]; ring
      have i1 : Integrable (fun ω => S m ω ^ 2) P := (hSL m).integrable_sq
      have i2 : Integrable (fun ω => S m ω * ξ' m ω) P := (hSL m).integrable_mul (hξ'L m)
      have i3 : Integrable (fun ω => ξ' m ω ^ 2) P := (hξ'L m).integrable_sq
      have i12 : Integrable (fun ω => S m ω ^ 2 + 2 * (S m ω * ξ' m ω)) P := i1.add (i2.const_mul 2)
      have i2' : Integrable (fun ω => 2 * (S m ω * ξ' m ω)) P := i2.const_mul 2
      rw [hfun, integral_add i12 i3, integral_add i1 i2',
        integral_const_mul, eqlzdl_orth (ℱ.le m) (hSm m) (hSL m) (hξ'L m) (hξ'c m), ih,
        Finset.sum_range_succ]
      ring
  have hsum : ∑ k ∈ Finset.range n, ∫ ω, ξ' k ω ^ 2 ∂P = ∑ k ∈ Finset.range n, ∫ ω, ξ k ω ^ 2 ∂P := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    simp [hξ', hk']
  calc ∫⁻ ω, ⨆ j : Fin (n + 1), ENNReal.ofReal ((∑ i ∈ Finset.range j, ξ i ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |S k ω|) ^ 2) ∂P := by
        refine lintegral_mono fun ω => iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
        have hj : (∑ i ∈ Finset.range j, ξ i ω) = S j ω := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.lt_succ_iff.1 j.2)
          simp [hξ', this]
        rw [hj, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (Finset.le_sup' (fun k => |S k ω|) (Finset.mem_range.2 (by omega))) 2
    _ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (|S n ω| ^ 2) ∂P := hdoob
    _ = ENNReal.ofReal (4 * ∑ k ∈ Finset.range n, ∫ ω, ξ k ω ^ 2 ∂P) := by
        have hint : Integrable (fun ω => S n ω ^ 2) P := (hSL n).integrable_sq
        have : ∫⁻ ω, ENNReal.ofReal (|S n ω| ^ 2) ∂P = ENNReal.ofReal (∫ ω, S n ω ^ 2 ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
          simp only [sq_abs]
        rw [this, hvar, hsum, ENNReal.ofReal_mul (by norm_num)]
        simp

/-- Pythagoras: `E ξ² ≤ E (ξ + h)²` when `h` is `𝒢`-measurable and `ξ` has vanishing `𝒢`-conditional mean. -/
theorem eqlzdl_pyth [IsProbabilityMeasure P] {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {h ξ : Ω → ℝ}
    (hh : Measurable[𝒢] h) (hhL : MemLp h 2 P) (hξ : MemLp ξ 2 P) (hc : P[ξ | 𝒢] =ᵐ[P] 0) :
    ∫ ω, ξ ω ^ 2 ∂P ≤ ∫ ω, (ξ ω + h ω) ^ 2 ∂P := by
  have hfun : (fun ω => (ξ ω + h ω) ^ 2) =
      fun ω => (ξ ω ^ 2 + 2 * (h ω * ξ ω)) + h ω ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => ξ ω ^ 2) P := hξ.integrable_sq
  have i2 : Integrable (fun ω => 2 * (h ω * ξ ω)) P := (hhL.integrable_mul hξ).const_mul 2
  have i3 : Integrable (fun ω => h ω ^ 2) P := hhL.integrable_sq
  have i12 : Integrable (fun ω => ξ ω ^ 2 + 2 * (h ω * ξ ω)) P := i1.add i2
  rw [hfun, integral_add i12 i3, integral_add i1 i2, integral_const_mul, eqlzdl_orth h𝒢 hh hhL hξ hc]
  have : 0 ≤ ∫ ω, h ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  linarith

end Abstract

section Chain

variable {E : Type} [MeasurableSpace E]

/-- The chain extended constantly beyond the last index. -/
def eqlzdl_c (m : ℕ) (z : Fin (m + 1) → E) (k : ℕ) : E :=
  z ⟨min k m, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem eqlzdl_c_of_le (m : ℕ) (z : Fin (m + 1) → E) (k : ℕ) (hk : k < m + 1) :
    eqlzdl_c m z k = z ⟨k, hk⟩ := by
  unfold eqlzdl_c
  congr 1
  exact Fin.ext (min_eq_left (by omega))

theorem eqlzdl_c_rev (m : ℕ) (z : Fin (m + 1) → E) (l : ℕ) :
    eqlzdl_c m (fun i => z (Fin.rev i)) l = eqlzdl_c m z (m - l) := by
  unfold eqlzdl_c
  refine congrArg z (Fin.ext ?_)
  simp only [Fin.val_rev]
  omega

/-- The partial sums `S_j = ∑_{i<j} (F(u_{i+1}) - g(u_i))`. -/
def eqlzdl_S (F g : E → ℝ) (u : ℕ → E) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (F (u (i + 1)) - g (u i))

/-- The algebraic Lyons-Zheng identity `G(u_j) - G(u_0) = S_j - R_0 + R_j`, `R_i = S'_{m-i}`. -/
theorem eqlzdl_ident (F g : E → ℝ) (u : ℕ → E) (m : ℕ) :
    ∀ j, j ≤ m →
      eqlzdl_S F g u j - eqlzdl_S F g (fun i => u (m - i)) m +
          eqlzdl_S F g (fun i => u (m - i)) (m - j) =
        (F (u j) + g (u j)) - (F (u 0) + g (u 0)) := by
  intro j
  induction j with
  | zero => intro _; simp [eqlzdl_S]
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hl : m - j = (m - (j + 1)) + 1 := by omega
    rw [hl] at ih'
    have e1 : m - (m - (j + 1) + 1) = j := by omega
    have e2 : m - (m - (j + 1)) = j + 1 := by omega
    unfold eqlzdl_S at ih' ⊢
    rw [Finset.sum_range_succ (fun i => F (u (i + 1)) - g (u i)) j]
    rw [Finset.sum_range_succ] at ih'
    simp only [e1, e2] at ih' ⊢
    linarith

/-- The prefix filtration of the coordinate process on `Fin (m+1) → E`. -/
def eqlzdl_fil (m : ℕ) (E : Type) [MeasurableSpace E] :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin (m + 1) → E)) where
  seq k := ⨆ (i : Fin (m + 1)) (_ : (i : ℕ) ≤ k),
    MeasurableSpace.comap (fun z : Fin (m + 1) → E => z i) inferInstance
  mono' := fun a b hab => iSup₂_le fun i hi => le_iSup₂_of_le i (hi.trans hab) le_rfl
  le' := fun k => iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

theorem eqlzdl_meas (m : ℕ) (j : Fin (m + 1)) (k : ℕ) (hjk : (j : ℕ) ≤ k) :
    Measurable[eqlzdl_fil m E k] (fun z : Fin (m + 1) → E => z j) :=
  (comap_measurable (fun z : Fin (m + 1) → E => z j)).mono
    (le_iSup₂_of_le j hjk le_rfl) le_rfl

theorem eqlzdl_fil_eq (m : ℕ) (k : ℕ) (hk : k < m) :
    (eqlzdl_fil m E k : MeasurableSpace (Fin (m + 1) → E)) =
      MeasurableSpace.comap (fun (z : Fin (m + 1) → E) (i : Fin (k + 1)) => z ⟨i, by omega⟩) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    have : Measurable[MeasurableSpace.comap (fun (z : Fin (m + 1) → E) (i : Fin (k + 1)) => z ⟨i, by omega⟩)
        (inferInstance : MeasurableSpace (Fin (k + 1) → E))] (fun z : Fin (m + 1) → E => z i) :=
      (measurable_pi_apply (⟨i, by omega⟩ : Fin (k + 1))).comp
        (comap_measurable (fun (z : Fin (m + 1) → E) (i : Fin (k + 1)) => (z ⟨i, by omega⟩ : E)))
    exact this.comap_le
  · refine Measurable.comap_le ?_
    refine @Measurable.of_eval _ _ _ (eqlzdl_fil m E k) _ _ fun i => ?_
    exact eqlzdl_meas m ⟨i, by omega⟩ k (by simpa using Nat.lt_succ_iff.1 i.2)

theorem eqlzdl_real (x1 x2 x3 d1 d0 f : ℝ) (h : 2 * f = x1 - x2 + x3 + d1 - d0) :
    f ^ 2 ≤ 3 / 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (d1 ^ 2 + d0 ^ 2) := by
  have hf : f = (x1 - x2 + x3 + d1 - d0) / 2 := by linarith
  subst hf
  nlinarith [sq_nonneg (x1 + x2), sq_nonneg (x1 - x3), sq_nonneg (x2 + x3), sq_nonneg (d1 + d0),
    sq_nonneg (x1 - x2 + x3 - (d1 - d0))]

end Chain

/-- (DL, `eqlz_dl`.)  Discrete Lyons-Zheng lemma; the statement is copied verbatim from `HRS.MD.EQLZ.eqlz_dl`.
Note on the edge case: `g(z_m) ∈ L²` is not a hypothesis (the martingale hypothesis only constrains `k < m`); it
follows from reversal invariance (`z_m` has the law of `z_0`), so `hB` at `j = m` is not a Bochner junk value. -/
theorem eqlz_dl_proof {E : Type} [MeasurableSpace E] (m : ℕ) (Λ : Measure (Fin (m + 1) → E))
    [IsProbabilityMeasure Λ] (F g : E → ℝ) (hF : Measurable F) (hg : Measurable g)
    (hFL2 : ∀ j : Fin (m + 1), MemLp (fun z : Fin (m + 1) → E => F (z j)) 2 Λ)
    (hrev : Λ.map (fun z i => z (Fin.rev i)) = Λ)
    (hmart : ∀ (k : ℕ) (hk : k < m),
      Λ[fun z => F (z ⟨k + 1, by omega⟩) |
          MeasurableSpace.comap (fun z (i : Fin (k + 1)) => z ⟨i, by omega⟩) inferInstance]
        =ᵐ[Λ] fun z => g (z ⟨k, by omega⟩))
    (A B : ℝ) (hA : ∑ k : Fin m, ∫ z, (F (z k.succ) - F (z k.castSucc)) ^ 2 ∂Λ ≤ A)
    (hB : ∀ j : Fin (m + 1), ∫ z, (F (z j) - g (z j)) ^ 2 ∂Λ ≤ B) :
    ∫⁻ z, ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) ∂Λ ≤
      ENNReal.ofReal (18 * A + 2 * ((m : ℝ) + 1) * B) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have h0 : ∀ z : Fin (0 + 1) → E,
        (⨆ j : Fin (0 + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2)) = 0 := by
      intro z
      refine le_antisymm (iSup_le fun j => ?_) bot_le
      have hj : j = 0 := Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)
      rw [hj]; simp
    calc _ = ∫⁻ z : Fin (0 + 1) → E, (0 : ℝ≥0∞) ∂Λ := lintegral_congr h0
      _ = 0 := by simp
      _ ≤ _ := zero_le
  -- the filtration and the coordinate facts
  set ℱ := eqlzdl_fil m E with hℱ
  have hmart' : ∀ (k : ℕ) (hk : k < m),
      Λ[fun z : Fin (m + 1) → E => F (z ⟨k + 1, by omega⟩) | ℱ k] =ᵐ[Λ]
        fun z => g (z ⟨k, by omega⟩) := by
    intro k hk
    have h := hmart k hk
    rwa [← eqlzdl_fil_eq m k hk] at h
  have gL : ∀ (k : ℕ) (hk : k < m),
      MemLp (fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩)) 2 Λ := fun k hk =>
    (MemLp.condExp (m := ℱ k) one_le_two (hFL2 ⟨k + 1, by omega⟩)).ae_eq (hmart' k hk)
  have hrvm : Measurable (fun (z : Fin (m + 1) → E) (i : Fin (m + 1)) => z (Fin.rev i)) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hmp : MeasurePreserving (fun (z : Fin (m + 1) → E) (i : Fin (m + 1)) => z (Fin.rev i)) Λ Λ :=
    ⟨hrvm, hrev⟩
  have hgj : ∀ j : Fin (m + 1), MemLp (fun z : Fin (m + 1) → E => g (z j)) 2 Λ := by
    intro j
    by_cases hj : (j : ℕ) < m
    · exact gL j hj
    · have h0 := (gL 0 hm0).comp_measurePreserving hmp
      have hj' : j = Fin.rev ⟨0, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
      have e : (fun z : Fin (m + 1) → E => g (z j)) =
          (fun z : Fin (m + 1) → E => g (z ⟨0, by omega⟩)) ∘
            (fun (z : Fin (m + 1) → E) (i : Fin (m + 1)) => z (Fin.rev i)) := by
        funext z
        exact congrArg (fun i => g (z i)) hj'
      rw [e]
      exact h0
  have hDL : ∀ j : Fin (m + 1), MemLp (fun z : Fin (m + 1) → E => F (z j) - g (z j)) 2 Λ :=
    fun j => (hFL2 j).sub (hgj j)
  -- martingale differences
  set ξ : ℕ → (Fin (m + 1) → E) → ℝ :=
    fun k z => F (eqlzdl_c m z (k + 1)) - g (eqlzdl_c m z k) with hξdef
  have hξk : ∀ (k : ℕ) (hk : k < m), ξ k =
      fun z => F (z ⟨k + 1, by omega⟩) - g (z ⟨k, by omega⟩) := by
    intro k hk
    funext z
    simp only [hξdef]
    rw [eqlzdl_c_of_le m z (k + 1) (by omega), eqlzdl_c_of_le m z k (by omega)]
  have hξm : ∀ k < m, Measurable[ℱ (k + 1)] (ξ k) := by
    intro k hk
    rw [hξk k hk]
    exact (hF.comp (eqlzdl_meas m ⟨k + 1, by omega⟩ (k + 1) le_rfl)).sub
      (hg.comp (eqlzdl_meas m ⟨k, by omega⟩ (k + 1) (Nat.le_succ k)))
  have hξL : ∀ k < m, MemLp (ξ k) 2 Λ := by
    intro k hk
    rw [hξk k hk]
    exact (hFL2 ⟨k + 1, by omega⟩).sub (gL k hk)
  have hξc : ∀ k < m, Λ[ξ k | ℱ k] =ᵐ[Λ] 0 := by
    intro k hk
    have hi1 : Integrable (fun z : Fin (m + 1) → E => F (z ⟨k + 1, by omega⟩)) Λ :=
      (hFL2 ⟨k + 1, by omega⟩).integrable one_le_two
    have hi2 : Integrable (fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩)) Λ :=
      (gL k hk).integrable one_le_two
    have hsm2 : StronglyMeasurable[ℱ k] (fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩)) :=
      (hg.comp (eqlzdl_meas m ⟨k, by omega⟩ k le_rfl)).stronglyMeasurable
    have h1 := condExp_sub (m := ℱ k) hi1 hi2
    have h2 : Λ[fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩) | ℱ k] =
        fun z => g (z ⟨k, by omega⟩) := condExp_of_stronglyMeasurable (ℱ.le k) hsm2 hi2
    filter_upwards [h1, hmart' k hk] with z e1 e2
    have e1' : (Λ[ξ k | ℱ k]) z =
        (Λ[fun z : Fin (m + 1) → E => F (z ⟨k + 1, by omega⟩) | ℱ k]) z -
          (Λ[fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩) | ℱ k]) z := by
      rw [hξk k hk]; exact e1
    rw [e1', e2, h2]
    simp
  have hmax := eqlzdl_maximal (P := Λ) ℱ ξ m hξm hξL hξc
  have hA0 : 0 ≤ A :=
    le_trans (Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _) hA
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun z => sq_nonneg _) (hB 0)
  have hA' : ∑ k ∈ Finset.range m, ∫ z, ξ k z ^ 2 ∂Λ ≤ A := by
    refine le_trans ?_ hA
    rw [Finset.sum_range (fun k => ∫ z, ξ k z ^ 2 ∂Λ)]
    refine Finset.sum_le_sum fun k _ => ?_
    have hk : (k : ℕ) < m := k.2
    have hhm : Measurable[ℱ k] (fun z : Fin (m + 1) → E =>
        g (z ⟨k, by omega⟩) - F (z ⟨k, by omega⟩)) :=
      (hg.comp (eqlzdl_meas m ⟨k, by omega⟩ k le_rfl)).sub
        (hF.comp (eqlzdl_meas m ⟨k, by omega⟩ k le_rfl))
    have hhL : MemLp (fun z : Fin (m + 1) → E => g (z ⟨k, by omega⟩) - F (z ⟨k, by omega⟩)) 2 Λ :=
      (gL k hk).sub (hFL2 ⟨k, by omega⟩)
    have key := eqlzdl_pyth (P := Λ) (ℱ.le k) hhm hhL (hξL k hk) (hξc k hk)
    refine key.trans (le_of_eq (integral_congr_ae (ae_of_all _ fun z => ?_)))
    simp only [hξk k hk]
    show (F (z ⟨k + 1, _⟩) - g (z ⟨k, _⟩) + (g (z ⟨k, _⟩) - F (z ⟨k, _⟩))) ^ 2 =
      (F (z ⟨k + 1, _⟩) - F (z ⟨k, _⟩)) ^ 2
    ring
  -- the three maximal functions
  set rv : (Fin (m + 1) → E) → (Fin (m + 1) → E) := fun z i => z (Fin.rev i) with hrv
  set MS : (Fin (m + 1) → E) → ℝ≥0∞ := fun z =>
    ⨆ j : Fin (m + 1), ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m z) j ^ 2) with hMS
  set MD : (Fin (m + 1) → E) → ℝ≥0∞ := fun z =>
    ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - g (z j)) ^ 2) with hMD
  have hcm : ∀ k : ℕ, Measurable (fun z : Fin (m + 1) → E => eqlzdl_c m z k) :=
    fun k => measurable_pi_apply _
  have hSm : ∀ j : ℕ, Measurable (fun z : Fin (m + 1) → E => eqlzdl_S F g (eqlzdl_c m z) j) := by
    intro j
    unfold eqlzdl_S
    exact Finset.measurable_sum _ fun i _ => (hF.comp (hcm (i + 1))).sub (hg.comp (hcm i))
  have hMSm : Measurable MS :=
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp ((hSm j).pow_const 2)
  have hMDm : Measurable MD :=
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (((hF.comp (measurable_pi_apply j)).sub (hg.comp (measurable_pi_apply j))).pow_const 2)
  have hint1 : ∫⁻ z, MS z ∂Λ ≤ ENNReal.ofReal (4 * A) :=
    hmax.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hint2 : ∫⁻ z, MS (rv z) ∂Λ ≤ ENNReal.ofReal (4 * A) := by
    have : ∫⁻ z, MS (rv z) ∂Λ = ∫⁻ z, MS z ∂Λ := by
      conv_rhs => rw [← hrev]
      exact (lintegral_map hMSm hrvm).symm
    rw [this]; exact hint1
  have hint3 : ∫⁻ z, MD z ∂Λ ≤ ENNReal.ofReal (((m : ℝ) + 1) * B) := by
    calc ∫⁻ z, MD z ∂Λ
        ≤ ∫⁻ z, ∑ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - g (z j)) ^ 2) ∂Λ :=
          lintegral_mono fun z => iSup_le fun j =>
            Finset.single_le_sum (f := fun j : Fin (m + 1) => ENNReal.ofReal ((F (z j) - g (z j)) ^ 2))
              (fun _ _ => zero_le) (Finset.mem_univ j)
      _ = ∑ j : Fin (m + 1), ∫⁻ z, ENNReal.ofReal ((F (z j) - g (z j)) ^ 2) ∂Λ :=
          lintegral_finset_sum _ fun j _ => ENNReal.measurable_ofReal.comp
            (((hF.comp (measurable_pi_apply j)).sub (hg.comp (measurable_pi_apply j))).pow_const 2)
      _ = ∑ j : Fin (m + 1), ENNReal.ofReal (∫ z, (F (z j) - g (z j)) ^ 2 ∂Λ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ofReal_integral_eq_lintegral_ofReal (hDL j).integrable_sq
            (ae_of_all _ fun z => sq_nonneg _)]
      _ ≤ ∑ j : Fin (m + 1), ENNReal.ofReal B :=
          Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal (hB j)
      _ = ENNReal.ofReal (((m : ℝ) + 1) * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [ENNReal.ofReal_add (Nat.cast_nonneg m) zero_le_one]
          simp
  have hMRm : Measurable (fun z => MS (rv z)) := hMSm.comp hrvm
  -- pointwise bound
  have hpt : ∀ (z : Fin (m + 1) → E) (j : Fin (m + 1)),
      ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) ≤
        ENNReal.ofReal (3 / 2) * (MS z + MS (rv z) + MS (rv z)) + MD z + MD z := by
    intro z j
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.2
    have hid := eqlzdl_ident F g (eqlzdl_c m z) m j hj
    have hu : eqlzdl_c m (rv z) = fun i => eqlzdl_c m z (m - i) := funext (eqlzdl_c_rev m z)
    have hcj : eqlzdl_c m z j = z j := eqlzdl_c_of_le m z j j.2
    have hc0 : eqlzdl_c m z 0 = z 0 := by
      rw [eqlzdl_c_of_le m z 0 (by omega)]; rfl
    rw [← hu, hcj, hc0] at hid
    have hreal := eqlzdl_real (eqlzdl_S F g (eqlzdl_c m z) j)
      (eqlzdl_S F g (eqlzdl_c m (rv z)) m) (eqlzdl_S F g (eqlzdl_c m (rv z)) (m - j))
      (F (z j) - g (z j)) (F (z 0) - g (z 0)) (F (z j) - F (z 0)) (by linarith [hid])
    have b1 : ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m z) j ^ 2) ≤ MS z :=
      le_iSup (fun j : Fin (m + 1) => ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m z) j ^ 2)) j
    have b2 : ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) m ^ 2) ≤ MS (rv z) :=
      le_iSup (fun j : Fin (m + 1) => ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) j ^ 2))
        ⟨m, by omega⟩
    have b3 : ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) (m - j) ^ 2) ≤ MS (rv z) :=
      le_iSup (fun j : Fin (m + 1) => ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) j ^ 2))
        ⟨m - j, by omega⟩
    have b4 : ENNReal.ofReal ((F (z j) - g (z j)) ^ 2) ≤ MD z :=
      le_iSup (fun j : Fin (m + 1) => ENNReal.ofReal ((F (z j) - g (z j)) ^ 2)) j
    have b5 : ENNReal.ofReal ((F (z 0) - g (z 0)) ^ 2) ≤ MD z :=
      le_iSup (fun j : Fin (m + 1) => ENNReal.ofReal ((F (z j) - g (z j)) ^ 2)) 0
    calc ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2)
        ≤ ENNReal.ofReal (3 / 2 * (eqlzdl_S F g (eqlzdl_c m z) j ^ 2 +
            eqlzdl_S F g (eqlzdl_c m (rv z)) m ^ 2 +
            eqlzdl_S F g (eqlzdl_c m (rv z)) (m - j) ^ 2) +
            ((F (z j) - g (z j)) ^ 2 + (F (z 0) - g (z 0)) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (3 / 2) * (ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m z) j ^ 2) +
            ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) m ^ 2) +
            ENNReal.ofReal (eqlzdl_S F g (eqlzdl_c m (rv z)) (m - j) ^ 2)) +
            (ENNReal.ofReal ((F (z j) - g (z j)) ^ 2) + ENNReal.ofReal ((F (z 0) - g (z 0)) ^ 2)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (3 / 2) * (MS z + MS (rv z) + MS (rv z)) + (MD z + MD z) := by
          gcongr
      _ = _ := (add_assoc _ _ _).symm
  have m3 : Measurable (fun z => MS z + MS (rv z)) := hMSm.add hMRm
  have m4 : Measurable (fun z => MS z + MS (rv z) + MS (rv z)) := m3.add hMRm
  have m1 : Measurable (fun z => ENNReal.ofReal (3 / 2) * (MS z + MS (rv z) + MS (rv z))) :=
    m4.const_mul _
  have m2 : Measurable (fun z => ENNReal.ofReal (3 / 2) * (MS z + MS (rv z) + MS (rv z)) + MD z) :=
    m1.add hMDm
  calc ∫⁻ z, ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) ∂Λ
      ≤ ∫⁻ z, (ENNReal.ofReal (3 / 2) * (MS z + MS (rv z) + MS (rv z)) + MD z + MD z) ∂Λ :=
        lintegral_mono fun z => iSup_le fun j => hpt z j
    _ = ENNReal.ofReal (3 / 2) * (∫⁻ z, MS z ∂Λ + ∫⁻ z, MS (rv z) ∂Λ + ∫⁻ z, MS (rv z) ∂Λ)
          + ∫⁻ z, MD z ∂Λ + ∫⁻ z, MD z ∂Λ := by
        rw [lintegral_add_left m2, lintegral_add_left m1, lintegral_const_mul _ m4,
          lintegral_add_left m3, lintegral_add_left hMSm]
    _ ≤ ENNReal.ofReal (3 / 2) * (ENNReal.ofReal (4 * A) + ENNReal.ofReal (4 * A) +
          ENNReal.ofReal (4 * A)) + ENNReal.ofReal (((m : ℝ) + 1) * B) +
          ENNReal.ofReal (((m : ℝ) + 1) * B) := by
        gcongr
    _ = ENNReal.ofReal (18 * A + 2 * ((m : ℝ) + 1) * B) := by
        have hmB : 0 ≤ ((m : ℝ) + 1) * B := by positivity
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) hmB,
          ← ENNReal.ofReal_add (by positivity) hmB]
        congr 1
        ring

end HRS.MD.EQLZDl
