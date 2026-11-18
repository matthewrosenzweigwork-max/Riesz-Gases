import HRS.MS.CovMeasAux3

/-!
# S10.1 (worker S101B), part 4: the `𝒦`-valued feature `Γ_τ` and its smoothness in `x`

`Γ_τ(x) = (B_τ(x), A'_τ(·,x), B_τ(x)) ∈ 𝒦 = KSpace d m T` with `B_τ(x) = (U^{τ,τ}φ_α(x))_α`,
`A'_τ(s,x) = (1_{τ<s≤T} ∂_sU^{τ,s}φ_α(x))_α` (the `𝒦`-feature of S5.2 with the time derivative given by the orbit assumption).
`s101_gamma_smooth`: `x ↦ Γ_τ(x)` is `C^{r+1}` with `‖D^jΓ_τ‖ ≤ B`, `B` independent of `τ ∈ [0,T]` (`s101_ell2_contDiff` for the
`ℓ²`-valued slices, `s55f_L2_contDiff` for the `L²_s(ℓ²)`-valued part, the embeddings `s55fΦ₁`, `s55fΦ₂`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

lemma s101_aesm_ellVec {μ : Measure ℝ} {m : ℝ} (v : MultiIndex d → ℝ → ℝ)
    (hv : ∀ α, AEStronglyMeasurable (v α) μ) (hmem : ∀ t, Memℓp (fun α => v α t) 2) :
    AEStronglyMeasurable (fun t => ellVec (d := d) m (fun α => v α t)) μ := by
  set ι : ∀ α : MultiIndex d, ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α with hι
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (t : ℝ) => ∑ α ∈ s, ι α (v α t)) ?_ ?_
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s fun α _ =>
      (ι α).continuous.comp_aestronglyMeasurable (hv α)
  · refine Eventually.of_forall fun t => ?_
    have h := hmem t
    have := s55f_ellVec_eq (d := d) (m := m) h
    show HasSum (fun α => (lp.single 2 α (v α t) : lp (fun _ : MultiIndex d => ℝ) 2))
      (ellVec (d := d) m (fun α => v α t) : lp (fun _ : MultiIndex d => ℝ) 2)
    rw [this]
    exact lp.hasSum_single (by norm_num) ⟨_, h⟩

/-- The `A'`-coordinates `s ↦ (1_{τ<s≤T} ∂_sU^{τ,s}φ_α(x))_α ∈ ℓ²`. -/
def s101Fl (C : WholeCoeff d) (m T τ : ℝ) (s : ℝ) (x : Euc d) : OscDual d m :=
  ellVec m (fun α => s101Th C m T τ s α x)

/-- The base value `(U^{τ,τ}φ_α(x))_α ∈ ℓ²`. -/
def s101Bv (C : WholeCoeff d) (m τ : ℝ) (x : Euc d) : OscDual d m :=
  ellVec m (fun α => propagatorW C τ τ (oscTestFun m α) x)

open Classical in
/-- The `L²([0,T];ℓ²)` component of the feature. -/
def s101Av (C : WholeCoeff d) (m T τ : ℝ) (x : Euc d) : L2Path d m T :=
  if h : MemLp (fun s => s101Fl C m T τ s x) 2 (volume.restrict (Icc (0 : ℝ) T)) then h.toLp _ else 0

/-- The feature `Γ_τ(x) ∈ 𝒦`. -/
def s101Gamma (C : WholeCoeff d) (m T τ : ℝ) (x : Euc d) : KSpace d m T :=
  KSpace.mk (s101Bv C m τ x) (s101Av C m T τ x) (s101Bv C m τ x)

lemma s101_th_slice {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (s : ℝ) (α : MultiIndex d) :
    ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun x => s101Th C m T τ s α x) ∧
    ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => s101Th C m T τ s α x) x‖ ≤ c α := by
  by_cases h : τ < s ∧ s ≤ T
  · have e : (fun x => s101Th C m T τ s α x) = fun x => s101Dt C m T τ s α x := by
      funext x; simp [s101Th, h]
    rw [e]
    exact ⟨hD.smoothD α τ hτ s ⟨h.1.le, h.2⟩, fun j hj x => hD.bddD α τ hτ s ⟨h.1.le, h.2⟩ j hj x⟩
  · have e : (fun x => s101Th C m T τ s α x) = fun _ => (0 : ℝ) := by
      funext x; simp [s101Th, h]
    rw [e]
    exact ⟨contDiff_const, fun j hj x => by rw [s55f_iter_zero]; exact hD.nonneg α⟩

theorem s101_gamma_smooth (hd : 1 ≤ d) {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Icc (0 : ℝ) T,
      ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun x => s101Gamma C m T τ x) ∧
      ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun y => s101Gamma C m T τ y) x‖ ≤ B := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set Bs : ℝ := Real.sqrt (∑' α, c α ^ 2) with hBs
  have hBs0 : 0 ≤ Bs := Real.sqrt_nonneg _
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  refine ⟨2 * Bs + (d : ℝ) ^ (r + 1) * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)), by positivity,
    fun τ hτ => ?_⟩
  -- the base part
  have hbase := s101_ell2_contDiff (d := d) (m := m) (r + 1)
    (fun α x => propagatorW C τ τ (oscTestFun m α) x) c hD.summable
    (fun α => hD.smoothU α τ hτ τ ⟨le_rfl, hτ.2⟩)
    (fun α j hj x => hD.bddU α τ hτ τ ⟨le_rfl, hτ.2⟩ j hj x)
  -- the orbit part
  set Fv : ℝ → Euc d → OscDual d m := fun s x => s101Fl C m T τ s x with hFv
  have hFsm : ∀ s, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (Fv s) ∧
      ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (Fv s) x‖ ≤ Bs := fun s =>
    s101_ell2_contDiff (d := d) (m := m) (r + 1) (fun α x => s101Th C m T τ s α x) c hD.summable
      (fun α => (s101_th_slice hD hτ s α).1) (fun α j hj x => (s101_th_slice hD hτ s α).2 j hj x)
  have hthmem : ∀ s x, Memℓp (fun α => s101Th C m T τ s α x) 2 := fun s x =>
    s101_memℓp_of_bound hD.summable fun α => s101_th_bound hD hτ s α x
  have hmeasF : ∀ x, AEStronglyMeasurable (fun s => Fv s x) μ := fun x =>
    s101_aesm_ellVec (m := m) (fun α s => s101Th C m T τ s α x)
      (fun α => (s101_th_aesm hD hτ α x).mono_measure Measure.restrict_le_self) (fun s => hthmem s x)
  have hFb0 : ∀ s x, ‖Fv s x‖ ≤ Bs := fun s x => by
    have := (hFsm s).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun s => Fv s x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun s => hFb0 s x)
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd (r + 1) Fv Bs (fun s => (hFsm s).1)
    (fun s j hj x => (hFsm s).2 j hj x) hmeasF hmem
  have hid : ∀ x, s101Gamma C m T τ x =
      s55fΦ₁ m T (ellVec (d := d) m (fun α => propagatorW C τ τ (oscTestFun m α) x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun s => Fv s x)) := by
    intro x
    rw [← s55f_mk_eq]
    unfold s101Gamma s101Av s101Bv
    rw [dif_pos (hmem x)]
  have hfun : (fun x => s101Gamma C m T τ x) = fun x =>
      s55fΦ₁ m T (ellVec (d := d) m (fun α => propagatorW C τ τ (oscTestFun m α) x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun s => Fv s x)) := funext hid
  rw [hfun]
  refine ⟨((s55fΦ₁ m T).contDiff.comp hbase.1).add ((s55fΦ₂ m T).contDiff.comp hWc), ?_⟩
  intro j hj x
  have hjk : (j : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    (((s55fΦ₁ m T).contDiff.comp hbase.1).of_le hjk).contDiffAt
    (((s55fΦ₂ m T).contDiff.comp hWc).of_le hjk).contDiffAt (x := x)
  have e1 := (s55fΦ₁ m T).norm_iteratedFDeriv_comp_left hbase.1.contDiffAt (x := x) (n := j) hjk
  have e2 := (s55fΦ₂ m T).norm_iteratedFDeriv_comp_left hWc.contDiffAt (x := x) (n := j) hjk
  show ‖iteratedFDeriv ℝ j ((s55fΦ₁ m T ∘ _) + (s55fΦ₂ m T ∘ _)) x‖ ≤ _
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hb1 := hbase.2 j hj x
  have hb2 := hWb j hj x
  have hn1 := s55fΦ₁_norm (d := d) m T
  have hn2 := s55fΦ₂_norm (d := d) m T
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ (r + 1) := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  calc _ ≤ ‖s55fΦ₁ m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m
          (fun α => propagatorW C τ τ (oscTestFun m α) x)) x‖ +
        ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun s => Fv s x)) x‖ :=
        add_le_add e1 e2
    _ ≤ 2 * Bs + (d : ℝ) ^ (r + 1) * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        have h1 : ‖s55fΦ₁ m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m
            (fun α => propagatorW C τ τ (oscTestFun m α) x)) x‖ ≤ 2 * Bs :=
          mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
        have h2 : ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun s => Fv s x)) x‖ ≤
            (d : ℝ) ^ (r + 1) * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
          calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
                mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
            _ ≤ (d : ℝ) ^ (r + 1) * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
        linarith

end HRS.MS.CovMeas
