import HRS.Uniform.Q48aAux3

/-!
# Q48a, part 4: the deterministic Gaussian integrand on the whole half-line

`⊤`-copy of `exists_sqrt_density`, `PCDetData`, `pc_exists_G`, `pc_detData` (`HRS/Prob/HilbertMartingale.lean`) and of
`PCDetData.hsInt` (`HRS/Uniform/Q07cAux9.lean`): the deterministic square-root density `Sb` of `Db` on `[0,∞)`,
locally trace-integrable, and the Itô integral `G = ∫ Sb dB` against any cylindrical Brownian motion.
-/

noncomputable section

open HRS HRS.MRep HRS.HilbertCLTAux
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section Sqrt

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma exists_sqrt_densityT {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t sb) :
    ∃ Sb : ℝ → H →L[ℝ] H, OpMeas Sb ∧ (∀ r, r ∉ Set.Ici (0 : ℝ) → Sb r = 0) ∧
      ∀ r, 0 ≤ r → IsSqrtOfForm (Sb r) (sb r) := by
  classical
  have hstc : ∀ r : ℝ, 0 ≤ r → IsTraceClassCov (sb r) := fun r hr =>
    (hsb r hr).traceClass r ⟨hr, le_rfl⟩
  have hsm : ∀ x y : H, Measurable fun σ => sb σ x y := (hsb 0 le_rfl).meas
  set A : ℝ → H →L[ℝ] H := fun r => if r ∈ Set.Ici (0 : ℝ) then formOp (sb r) else 0 with hA
  have hAp : ∀ r, IsPSDOp (A r) := by
    intro r
    by_cases hr : r ∈ Set.Ici (0 : ℝ)
    · simp only [hA, hr, ite_true]
      exact ⟨fun x y => by
        rw [inner_formOp, real_inner_comm, inner_formOp, (hstc r hr).symm],
        fun x => by rw [inner_formOp]; exact (hstc r hr).nonneg x⟩
    · simp only [hA, hr, ite_false]
      exact ⟨fun x y => by simp, fun x => by simp⟩
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun i => ?_)
    have : (fun r => inner ℝ (e i) (A r x)) =
        fun r => (Set.Ici (0 : ℝ)).indicator (fun r => sb r x (e i)) r := by
      funext r
      by_cases hr : r ∈ Set.Ici (0 : ℝ)
      · simp only [hA, hr, ite_true, Set.indicator_of_mem]
        rw [real_inner_comm, inner_formOp]
      · have h0 : A r = 0 := by simp only [hA, hr, ite_false]
        rw [h0, Set.indicator_of_notMem hr]
        simp
    rw [this]
    exact (hsm x (e i)).indicator measurableSet_Ici
  set c : ℝ → ℝ := fun r => 1 + (Set.Ici (0 : ℝ)).indicator (fun r => ∑' i, sb r (e i) (e i)) r with hc
  have hcm : Measurable c :=
    measurable_const.add ((Measurable.tsum fun i => hsm (e i) (e i)).indicator measurableSet_Ici)
  have hcpos : ∀ r, 0 < c r := by
    intro r
    by_cases hr : r ∈ Set.Ici (0 : ℝ)
    · have : 0 ≤ ∑' i, sb r (e i) (e i) := tsum_nonneg fun i => (hstc r hr).nonneg _
      simp only [hc, hr, Set.indicator_of_mem]
      linarith
    · simp [hc, hr]
  have hAc : ∀ r x, inner ℝ (A r x) x ≤ c r * ‖x‖ ^ 2 := by
    intro r x
    by_cases hr : r ∈ Set.Ici (0 : ℝ)
    · obtain ⟨T, hT, hb⟩ := (hstc r hr).hasSum_basis e
      simp only [hA, hr, ite_true, inner_formOp, hc, Set.indicator_of_mem, hT.tsum_eq]
      have := hb x
      nlinarith [sq_nonneg ‖x‖]
    · simp only [hA, hr, ite_false]
      simp only [zero_apply, inner_zero_left]
      have := hcpos r
      positivity
  set S0 : ℝ → H →L[ℝ] H := fun r => sqrtOp (c r) (A r) with hS0
  have hS0m : OpMeas S0 := OpMeas.sqrtOp hAm hcm hAp hcpos hAc
  refine ⟨fun r => if r ∈ Set.Ici (0 : ℝ) then S0 r else 0, ?_, fun r hr => by simp [hr],
    fun r hr' => ?_⟩
  · intro x
    have : (fun r => (if r ∈ Set.Ici (0 : ℝ) then S0 r else 0) x) =
        (Set.Ici (0 : ℝ)).indicator (fun r => S0 r x) := by
      funext r
      by_cases hr : r ∈ Set.Ici (0 : ℝ) <;> simp [hr]
    rw [this]
    exact (hS0m x).indicator measurableSet_Ici
  have hr : r ∈ Set.Ici (0 : ℝ) := hr'
  simp only [hr, ite_true]
  have hspec := sqrtOp_spec (hAp r) (hcpos r) (hAc r)
  refine ⟨hspec.1.symm, hspec.1.nonneg, fun x y => ?_⟩
  rw [hspec.1.symm x (sqrtOp (c r) (A r) y)]
  have : sqrtOp (c r) (A r) (sqrtOp (c r) (A r) y) = A r y := by
    have := congrArg (fun T : H →L[ℝ] H => T y) hspec.2
    simpa using this
  rw [this]
  simp only [hA, hr, ite_true]
  rw [real_inner_comm, inner_formOp, (hstc r hr).symm]

end Sqrt

section PC7

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- Data for a deterministic operator-valued integrand `Sb` on `[0,∞)` against `B`. -/
structure PCDetTop (e : HilbertBasis ι ℝ H) (Sb : ℝ → H →L[ℝ] H) (T : ℝ → ℝ) : Prop where
  meas : OpMeas Sb
  zero : ∀ r, r ∉ Set.Ici (0 : ℝ) → Sb r = 0
  parseval : ∀ r x, HasSum (fun j => inner ℝ (Sb r (e j)) x ^ 2) (‖Sb r x‖ ^ 2)
  bound : ∀ r ∈ Set.Ici (0 : ℝ), ∀ x, ‖Sb r x‖ ^ 2 ≤ T r * ‖x‖ ^ 2
  trace : ∀ r ∈ Set.Ici (0 : ℝ), HasSum (fun i => ‖Sb r (e i)‖ ^ 2) (T r)
  Tmeas : Measurable T
  Tnonneg : ∀ r ∈ Set.Ici (0 : ℝ), 0 ≤ T r
  Tint : ∀ t : ℝ, IntegrableOn T (Set.Icc 0 t)

/-- The deterministic integrand `⟨Sb_r e_j, x⟩`. -/
def fSbT (e : HilbertBasis ι ℝ H) (Sb : ℝ → H →L[ℝ] H) (x : H) :
    ℝ → Ω → ι → ℝ := fun r _ j => inner ℝ (Sb r (e j)) x

variable {e : HilbertBasis ι ℝ H} {Sb : ℝ → H →L[ℝ] H} {T : ℝ → ℝ}

lemma PCDetTop.prog (hD : PCDetTop e Sb T) (x : H) (j : ι) :
    IsProgressive ℱ (fun r ω => fSbT (Ω := Ω) e Sb x r ω j) :=
  pc_isProgressive_det (g := fun r => inner ℝ (Sb r (e j)) x)
    ((hD.meas (e j)).inner measurable_const)

lemma PCDetTop.tsum_eq (hD : PCDetTop e Sb T) (x : H) (r : ℝ) (ω : Ω) :
    ∑' j, ‖fSbT e Sb x r ω j‖ₑ ^ 2 = ENNReal.ofReal (‖Sb r x‖ ^ 2) :=
  enorm_tsum_sq_of_hasSum (hD.parseval r x)

lemma PCDetTop.tsum_le (hD : PCDetTop e Sb T) (x : H) (r : ℝ) (ω : Ω) :
    ∑' j, ‖fSbT e Sb x r ω j‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator (fun r => T r * ‖x‖ ^ 2) r) := by
  rw [hD.tsum_eq x r ω]
  by_cases hr : r ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hr]
    exact ENNReal.ofReal_le_ofReal (hD.bound r hr x)
  · rw [Set.indicator_of_notMem hr, hD.zero r hr]
    simp

lemma PCDetTop.lintegral_bound_lt (hD : PCDetTop e Sb T) (x : H) (N : ℝ) :
    ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator (fun r => T r * ‖x‖ ^ 2) r) < ⊤ := by
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun r => ENNReal.ofReal (T r * ‖x‖ ^ 2))
    (fun r hr => by rw [Set.indicator_of_mem (Set.mem_Ici.2 hr.1)])]
  exact ((hD.Tint N).mul_const _).lintegral_lt_top

lemma PCDetTop.ctbl (hD : PCDetTop e Sb T) (x : H) :
    IsCtbl P ℱ (fSbT (Ω := Ω) e Sb x) :=
  pc_isCtbl_of_le (hD.prog x)
    (g := fun r _ => ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator (fun r => T r * ‖x‖ ^ 2) r))
    (fun r ω => hD.tsum_le x r ω) (fun N => by
      rw [lintegral_const, measure_univ, mul_one]
      exact (hD.lintegral_bound_lt x N).ne)

lemma PCDetTop.lintegral_T_lt (hD : PCDetTop e Sb T) (N : ℝ) :
    ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r) < ⊤ := by
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun r => ENNReal.ofReal (T r))
    (fun r hr => by rw [Set.indicator_of_mem (Set.mem_Ici.2 hr.1)])]
  exact (hD.Tint N).lintegral_lt_top

lemma PCDetTop.tsum_cT_eq (ℱ' : Filtration ℝ mΩ) (hD : PCDetTop e Sb T) (x : H) (N : ℝ) :
    ∑' j, cT P (fSbT (Ω := Ω) e Sb x) j N =
      ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal (‖Sb r x‖ ^ 2) := by
  rw [pc_tsum_cT (ℱ := ℱ') (hD.prog x) N]
  simp_rw [hD.tsum_eq x]
  rw [lintegral_const, measure_univ, mul_one]

lemma PCDetTop.sum_trace_le (hD : PCDetTop e Sb T) (r : ℝ) :
    ∑' i, ENNReal.ofReal (‖Sb r (e i)‖ ^ 2) ≤
      ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r) := by
  by_cases hr : r ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hr]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (hD.trace r hr).summable,
      (hD.trace r hr).tsum_eq]
  · rw [Set.indicator_of_notMem hr]
    simp [hD.zero r hr]

lemma PCDetTop.doob_sum (hD : PCDetTop e Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {I : ι → ℝ → Ω → ℝ}
    (hI : ∀ i, IsItoC P ℱ B (fSbT e Sb (e i)) (I i)) (N : ℕ) :
    ∑' i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P ≠ ⊤ := by
  have hterm : ∀ i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P ≤
      4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ENNReal.ofReal (‖Sb r (e i)‖ ^ 2) := by
    intro i
    have hM : Martingale (I i) ℱ P := (hI i).martingale (hD.ctbl _) hB
    have hL2 : ∀ τ, MemLp (I i τ) 2 P := fun τ => by
      by_cases hτ : 0 ≤ τ
      · exact (hI i).memLp (hD.ctbl _) hB hτ
      · have : I i τ = fun _ => 0 := funext fun ω => (hI i).zero τ (not_le.1 hτ).le ω
        rw [this]; exact MemLp.zero
    have h1 := SimpleIntegrand.doob_L2_continuous hM (hI i).cont hL2 (N : ℝ)
    have h2 := (hI i).lintegral_sq_le (hD.ctbl _) hB (Nat.cast_nonneg N)
    rw [hD.tsum_cT_eq ℱ] at h2
    exact h1.trans (by gcongr)
  refine ne_top_of_le_ne_top (b := 4 * ∫⁻ r in Set.Icc 0 (N : ℝ),
    ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r)) ?_ ?_
  · exact ENNReal.mul_ne_top (by norm_num) (hD.lintegral_T_lt N).ne
  calc ∑' i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P
      ≤ ∑' i, 4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ENNReal.ofReal (‖Sb r (e i)‖ ^ 2) :=
        ENNReal.tsum_le_tsum hterm
    _ = 4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ∑' i, ENNReal.ofReal (‖Sb r (e i)‖ ^ 2) := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum]
        intro i
        refine (Measurable.ennreal_ofReal ?_).aemeasurable
        exact ((hD.meas (e i)).norm).pow_const 2
    _ ≤ _ := by
        gcongr with r
        exact hD.sum_trace_le r

lemma PCDetTop.scalar_le (hD : PCDetTop e Sb T) (z : H) (r : ℝ) :
    ENNReal.ofReal (‖Sb r z‖ ^ 2) ≤
      ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r) := by
  by_cases hr : r ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hr, ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖Sb r z‖ ^ 2 ≤ T r * ‖z‖ ^ 2 := hD.bound r hr z
      _ = ‖z‖ ^ 2 * T r := mul_comm _ _
  · rw [Set.indicator_of_notMem hr, hD.zero r hr]
    simp

lemma fSbT_comb (e : HilbertBasis ι ℝ H) (Sb : ℝ → H →L[ℝ] H) (c : ι → ℝ) (F : Finset ι)
    (x : H) (r : ℝ) (ω : Ω) (j : ι) :
    ∑ i ∈ F, c i * fSbT e Sb (e i) r ω j - fSbT e Sb x r ω j =
      fSbT e Sb (∑ i ∈ F, c i • e i - x) r ω j := by
  simp [fSbT, inner_sub_right, inner_sum, inner_smul_right]

lemma PCDetTop.comb_tendsto (hD : PCDetTop e Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {I : ι → ℝ → Ω → ℝ}
    (hI : ∀ i, IsItoC P ℱ B (fSbT e Sb (e i)) (I i)) {J : ℝ → Ω → ℝ} (x : H)
    (hJ : IsItoC P ℱ B (fSbT e Sb x) J) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun F : Finset ι => ∫⁻ ω, ‖(∑ i ∈ F, inner ℝ (e i) x * I i τ ω) - J τ ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
  set c : ι → ℝ := fun i => inner ℝ (e i) x with hc
  have hcomb : ∀ F : Finset ι, ∫⁻ ω, ‖(∑ i ∈ F, c i * I i τ ω) - J τ ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2) *
        ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r) := by
    intro F
    obtain ⟨hξF, hIF⟩ := IsItoC.finset_sum hB F (fun i => fun r ω j => c i * fSbT e Sb (e i) r ω j)
      (fun i => fun τ ω => c i * I i τ ω)
      (fun i _ => (hD.ctbl (Ω := Ω) (ℱ := ℱ) (e i)).mul_bdd (w := fun _ _ => c i)
        (isProgressive_const ℱ _) (C := |c i|) (fun r ω => le_rfl))
      (fun i _ => (hI i).smul hB (hD.ctbl (e i)) (c i))
    have hdiff := IsItoC.sub hB hξF (hD.ctbl x) hIF hJ
    have hΞd := pc_isCtbl_sub hξF (hD.ctbl (Ω := Ω) (ℱ := ℱ) x)
    have h1 := hdiff.lintegral_sq_le hΞd hB hτ
    have hfun : (fun r (ω : Ω) j => ∑ i ∈ F, c i * fSbT e Sb (e i) r ω j - fSbT e Sb x r ω j) =
        fSbT e Sb (∑ i ∈ F, c i • e i - x) := by
      funext r ω j; exact fSbT_comb e Sb c F x r ω j
    rw [hfun, hD.tsum_cT_eq ℱ] at h1
    refine h1.trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun r => hD.scalar_le _ r
  have hlim : Tendsto (fun F : Finset ι => ‖∑ i ∈ F, c i • e i - x‖) atTop (𝓝 0) := by
    have h2 : HasSum (fun i => c i • e i) x := by
      have := e.hasSum_repr x
      convert this using 2 with i
      simp [hc, HilbertBasis.repr_apply_apply]
    exact tendsto_iff_norm_sub_tendsto_zero.1 (show Tendsto (fun F : Finset ι => ∑ i ∈ F, c i • e i)
      atTop (𝓝 x) from h2)
  have hK : ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r) ≠ ⊤ :=
    (hD.lintegral_T_lt τ).ne
  have hlim2 : Tendsto (fun F : Finset ι => ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2) *
      ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Ici (0 : ℝ)).indicator T r)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun F : Finset ι => ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2)) atTop
        (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto (0 ^ 2 : ℝ)).comp (hlim.pow 2)
      have e0 : ENNReal.ofReal ((0 : ℝ) ^ 2) = 0 := by simp
      rw [e0] at this
      exact this
    have := ENNReal.Tendsto.mul_const h3 (Or.inr hK)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2 (fun F => bot_le) hcomb

theorem pc_exists_GT (hD : PCDetTop e Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) :
    ∃ G : ℝ → Ω → H,
      IsHilbertItoIntegral P ℱ B (fun r (_ : Ω) j => Sb r (e j)) G ∧
      ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSbT e Sb x) J ∧
        ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ := by
  classical
  have hex : ∀ i, ∃ J, IsItoC P ℱ B (fSbT e Sb (e i)) J := fun i => exists_isItoC hB (hD.ctbl _)
  choose I hI using hex
  obtain ⟨G, hGc, hGa, hG0, hGae⟩ := pc_hvalued (hB ∅).complete e I (fun i ω => (hI i).cont ω)
    (fun i τ => (hI i).adapted τ) (fun i τ hτ ω => (hI i).zero τ hτ ω) (hD.doob_sum hB hI)
  have hJex : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSbT e Sb x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ := by
    intro x
    obtain ⟨J, hJ⟩ := exists_isItoC hB (hD.ctbl (Ω := Ω) (ℱ := ℱ) x)
    refine ⟨J, hJ, fun τ hτ => ?_⟩
    obtain ⟨F, hF⟩ := exists_finset_seq (A := ι)
    have hImeas : ∀ i, Measurable (I i τ) := fun i => ((hI i).adapted τ).mono (ℱ.le τ) le_rfl
    refine pc_ae_eq_of_limits (X := fun n ω => ∑ i ∈ F n, inner ℝ (e i) x * I i τ ω)
      (fun n => (Finset.measurable_sum _ fun i _ => (hImeas i).const_mul _).aemeasurable)
      (((hJ.adapted τ).mono (ℱ.le τ) le_rfl).aemeasurable) ?_ ?_
    · filter_upwards [hGae τ] with ω hω
      obtain ⟨hsum, hGω⟩ := hω
      have := pcVec_hasSum_inner e hsum x
      rw [← hGω] at this
      have h2 : Tendsto (fun s : Finset ι => ∑ i ∈ s, I i τ ω * inner ℝ (e i) x) atTop
          (𝓝 (inner ℝ (G τ ω) x)) := this
      simp only [mul_comm (inner ℝ (e _) x)]
      exact h2.comp hF
    · exact (hD.comb_tendsto hB hI x hJ hτ).comp hF
  choose J hJ using hJex
  refine ⟨G, ⟨hGc, hGa, hG0, fun τ hτ x => ?_⟩, fun x => ⟨J x, (hJ x).1, (hJ x).2⟩⟩
  have hlim := (hJ x).1.approx τ hτ
  refine hlim.congr (fun F => lintegral_congr_ae ?_)
  filter_upwards [(hJ x).2 τ hτ] with ω h
  have hItoF : ItoF P ℱ B (fSbT e Sb x) F =
      itoIntegral P ℱ (fun t ω (k : F) => B t ω k)
        (fun r ω (k : F) => inner ℝ ((fun r (_ : Ω) j => Sb r (e j)) r ω k) x) := by
    unfold ItoF WF ξF
    congr 1
  rw [hItoF]
  show ‖itoIntegral P ℱ (fun t ω (k : F) => B t ω k)
        (fun r ω (k : F) => inner ℝ ((fun r (_ : Ω) j => Sb r (e j)) r ω k) x) τ ω
      - J x τ ω‖ₑ ^ 2 = _
  rw [← h]

end PC7

section DetHS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H} {Sb : ℝ → H →L[ℝ] H}
  {Tf : ℝ → ℝ}

lemma PCDetTop.summable_sb (hD : PCDetTop e Sb Tf) (r : ℝ) :
    Summable fun j => ‖Sb r (e j)‖ ^ 2 := by
  by_cases hr : r ∈ Set.Ici (0 : ℝ)
  · exact (hD.trace r hr).summable
  · have : Sb r = 0 := hD.zero r hr
    simp [this]

lemma PCDetTop.tsum_sb_le (hD : PCDetTop e Sb Tf) (r : ℝ) :
    ∑' j, ‖(Sb r (e j) : H)‖ₑ ^ 2 ≤ (Set.Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal (Tf r)) r := by
  by_cases hr : r ∈ Set.Ici (0 : ℝ)
  · simp only [hr, Set.indicator_of_mem]
    have h1 : ∀ j, ‖Sb r (e j)‖ₑ ^ 2 = ENNReal.ofReal (‖Sb r (e j)‖ ^ 2) := fun j => by
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [h1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (hD.trace r hr).summable,
      (hD.trace r hr).tsum_eq]
  · have : Sb r = 0 := hD.zero r hr
    simp [this, hr]

theorem PCDetTop.hsInt (hD : PCDetTop e Sb Tf) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (S : ℝ) :
    IsHSIntegrand P ℱ S (fun r (_ : Ω) (j : ιe) => Sb r (e j)) := by
  refine ⟨fun j => ?_, fun r ω => hD.summable_sb r, ?_⟩
  · exact pc_isProgressive_det (ℱ := ℱ) (Ω := Ω) (g := fun r => Sb r (e j)) (hD.meas (e j))
  · unfold hsSqIntegralOn
    simp only [lintegral_const, measure_univ, mul_one]
    refine lt_of_le_of_lt (lintegral_mono' le_rfl (fun r => hD.tsum_sb_le r)) ?_
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun r => ENNReal.ofReal (Tf r))
      (fun r hr => by rw [Set.indicator_of_mem (Set.mem_Ici.2 hr.1)])]
    exact (hD.Tint S).lintegral_lt_top

end DetHS

section DetData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

lemma pc_detDataT (e : HilbertBasis ι ℝ H) (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (hsb : ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t sb) {Sb : ℝ → H →L[ℝ] H} (hSbm : OpMeas Sb)
    (hSb0 : ∀ r, r ∉ Set.Ici (0 : ℝ) → Sb r = 0) (hSb : ∀ r, 0 ≤ r → IsSqrtOfForm (Sb r) (sb r)) :
    ∃ T : ℝ → ℝ, PCDetTop e Sb T := by
  have hstc : ∀ r : ℝ, 0 ≤ r → IsTraceClassCov (sb r) := fun r hr =>
    (hsb r hr).traceClass r ⟨hr, le_rfl⟩
  have hsm : ∀ x y : H, Measurable fun σ => sb σ x y := (hsb 0 le_rfl).meas
  set T : ℝ → ℝ := (Set.Ici (0 : ℝ)).indicator (fun r => ∑' i, sb r (e i) (e i)) with hT
  have hTm : Measurable T :=
    (Measurable.tsum fun i => hsm (e i) (e i)).indicator measurableSet_Ici
  refine ⟨T, ⟨hSbm, hSb0, ?_, ?_, ?_, hTm, ?_, ?_⟩⟩
  · intro r x
    by_cases hr : r ∈ Set.Ici (0 : ℝ)
    · have := hasSum_inner_sq e (Sb r x)
      convert this using 2 with j
      rw [(hSb r hr).symm (e j) x, real_inner_comm]
    · simp [hSb0 r hr]
  · intro r hr x
    obtain ⟨T0, hT0, hb⟩ := (hstc r hr).hasSum_basis e
    have h1 : ‖Sb r x‖ ^ 2 = sb r x x := by
      rw [← real_inner_self_eq_norm_sq, (hSb r hr).sq]
    simp only [hT, Set.indicator_of_mem hr, hT0.tsum_eq]
    rw [h1]; exact hb x
  · intro r hr
    obtain ⟨T0, hT0, hb⟩ := (hstc r hr).hasSum_basis e
    simp only [hT, Set.indicator_of_mem hr, hT0.tsum_eq]
    convert hT0 using 2 with i
    rw [← real_inner_self_eq_norm_sq, (hSb r hr).sq]
  · intro r hr
    simp only [hT, Set.indicator_of_mem hr]
    exact tsum_nonneg fun i => (hstc r hr).nonneg _
  · intro t
    by_cases ht : 0 ≤ t
    · refine (hsb t ht).int.mono' hTm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      have hr' : r ∈ Set.Ici (0 : ℝ) := hr.1
      have h0 : 0 ≤ T r := by
        simp only [hT, Set.indicator_of_mem hr']
        exact tsum_nonneg fun i => (hstc r hr.1).nonneg _
      rw [Real.norm_of_nonneg h0]
      simp only [hT, Set.indicator_of_mem hr']
      exact (hstc r hr.1).tsum_basis_le e
    · push Not at ht
      simp [Set.Icc_eq_empty (not_le.2 ht)]

end DetData

end HRS.Uniform.Q48a
