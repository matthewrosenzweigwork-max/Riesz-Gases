import HRS.MS.WadAux172

/-!
# S8.3, packet S8H-4: the semigroup on pair kernels at order zero

Real-valued forms of the semigroup bounds (`s8h_U0`, `s8h_Ujet`), the weighted gap lemma (`s8h_gap`: slices of a decaying continuous pair kernel
vary continuously in the weighted sup norm) and the order-zero theory of `tensorU`: for a continuous kernel `F` with `|F| ≤ N w` and weighted
decay at infinity, the sections `x' ↦ U_t(F x')(y)` lie in `C_M` and `|tensorU U t F| ≤ K₀² N w` (`s8h_sec0`); `tensorU` is additive (`s8h_tensor_sub`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Pair kernels in `C^j` with weighted decay of all jets of order `≤ j`. -/
def S8hPair (M : ℝ) (j : ℕ) (F : Euc d × Euc d → ℝ) : Prop :=
  ContDiff ℝ j F ∧ ∀ i ≤ j, Tendsto (fun z => ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0)

theorem s8h_pair_iff {M : ℝ} {j : ℕ} {R : Euc d → Euc d → ℝ} :
    MemCMpair M j R ↔ S8hPair M j (Function.uncurry R) := by
  unfold MemCMpair S8hPair
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun hi => ?_)
  have : (fun z : Euc d × Euc d => jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
      ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖) =
      fun z => ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖ / s8h_w M z := by
    funext z
    unfold s8h_w
    rw [Real.rpow_neg (s83_jb_pos _).le, Real.rpow_neg (s83_jb_pos _).le]
    field_simp
  rw [this]

theorem s8h_cc_memCMj (M : ℝ) {φ : Euc d → ℝ} (hφ : S85Cc φ) (j : ℕ) : MemCMj M j φ := by
  refine ⟨hφ.1.of_le (by exact_mod_cast le_top), fun i hi idx => ?_⟩
  have hev : ∀ᶠ x in cocompact (Euc d), partialDeriv idx φ x / jbracket x ^ M = 0 := by
    filter_upwards [(hφ.2.iteratedFDeriv (𝕜 := ℝ) i).compl_mem_cocompact] with x hx
    unfold partialDeriv
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h_U0 (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) {T : ℝ}
    (hT : 0 ≤ T) : ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ t ∈ Set.Icc 0 T, ∀ f, MemCM M f → ∀ {C : ℝ}, 0 ≤ C →
      Wt M C f → Wt M (K0 * C) (U t f) := by
  obtain ⟨K, hK⟩ := hU.bdd T hT
  refine ⟨max K 0, le_max_right _ _, fun t ht f hf C hC hW => ?_⟩
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h1 := hK t ht f hf
  have h2 : weightedSupE 0 (-M) f ≤ ENNReal.ofReal C := (s83_wsup0_le_iff hC f).2 hW
  have h3 : weightedSupE 0 (-M) (U t f) ≤ ENNReal.ofReal (max K 0 * C) := by
    calc weightedSupE 0 (-M) (U t f) ≤ ENNReal.ofReal K * weightedSupE 0 (-M) f := h1
      _ ≤ ENNReal.ofReal (max K 0) * ENNReal.ofReal C :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) h2
      _ = ENNReal.ofReal (max K 0 * C) := (ENNReal.ofReal_mul hK0).symm
  exact (s83_wsup0_le_iff (mul_nonneg hK0 hC) _).1 h3

theorem s8h_Ujet (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, ∀ f, MemCMj M j f → ∀ {N : ℝ}, 0 ≤ N →
      (∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ N * jbracket y ^ M) →
      MemCMj M j (U t f) ∧ ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i (U t f) y‖ ≤ K * N * jbracket y ^ M := by
  obtain ⟨K', hK'⟩ := h3 j T hT
  set K'' : ℝ := max K' 0 with hK''
  have hK''0 : 0 ≤ K'' := le_max_right _ _
  refine ⟨((d : ℝ) + 1) ^ j * K'', by positivity, fun t ht f hf N hN hb => ?_⟩
  obtain ⟨hmem, hsup⟩ := hK' t ht f hf
  refine ⟨hmem, ?_⟩
  have hfN : weightedSupE j (-M) f ≤ ENNReal.ofReal N := by
    rw [s83_wsup_le_iff hN]
    intro i hi idx x
    unfold partialDeriv
    have h1 := (iteratedFDeriv ℝ i f x).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
    have h2 : ∏ l : Fin i, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [h2, mul_one] at h1
    exact (Real.norm_eq_abs _ ▸ h1).trans (hb i hi x)
  have hUN : weightedSupE j (-M) (U t f) ≤ ENNReal.ofReal (K'' * N) := by
    calc weightedSupE j (-M) (U t f) ≤ ENNReal.ofReal K' * weightedSupE j (-M) f := hsup
      _ ≤ ENNReal.ofReal K'' * ENNReal.ofReal N :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hfN
      _ = ENNReal.ofReal (K'' * N) := (ENNReal.ofReal_mul hK''0).symm
  obtain ⟨-, hjet⟩ := s8f_jet_data hM hmem
  intro i hi y
  have := hjet (mul_nonneg hK''0 hN) hUN i hi y
  calc ‖iteratedFDeriv ℝ i (U t f) y‖ ≤ ((d : ℝ) + 1) ^ j * (K'' * N) * jbracket y ^ M := this
    _ = ((d : ℝ) + 1) ^ j * K'' * N * jbracket y ^ M := by ring

theorem s8h_U_sub (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {t : ℝ} (ht : 0 ≤ t) {f g : Euc d → ℝ} (hf : MemCM M f) (hg : MemCM M g) :
    U t (fun x => f x - g x) = fun x => U t f x - U t g x := by
  have hgm : MemCM M ((-1 : ℝ) • g) := by
    refine ⟨hg.1.const_smul _, ?_⟩
    have := hg.2.const_mul (-1 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun x => ?_
    simp [Pi.smul_apply, neg_div]
  have e1 : (fun x => f x - g x) = f + (-1 : ℝ) • g := by funext x; simp [sub_eq_add_neg]
  rw [e1, hU.add t ht f _ hf hgm, hU.smul t ht (-1) g hg]
  funext x
  simp [sub_eq_add_neg]

end Interface

end HRS.MS.Wad
