import HRS.Whole.AppendixA

/-!
# SA11, packet A1: jets of `C_c^∞` functions as elements of `W^{m,p}`; plan of S.A.11 and S.A.4

Worker SA11 (2026-10-24).  Frozen rows: S.A.11 `HRS.Whole.AppendixA.zero_temp_decaying_field`
(`HRS/Whole/AppendixA.lean`) and S.A.4 `main_rd_dec_stat`.  TeX: supplement L10028-10046, proof L10655-10658; L9893-9905.
The full plan, with the junk-value audit, is `SA11_PLAN.md` (scratch directory); its content is summarised here.

## Verdict on the frozen statements

* **S.A.11 is TRUE as stated and non-vacuous.**  `invβ = 0` gives `σ_N = κ_N`, `A_N = 1`, `q_N = 0`; the martingale
  term of the duality identity vanishes.  The existence clauses are true because (a) `φ ↦ U^{0,t}φ` induces a bounded linear
  `T : W^{m,p} → W^{m,p}` on jets (bounded by `AdjointInputRd`; LINEAR by uniqueness of classical adjoint solutions, which
  holds in the three cases `decSub` (regime `R1`, `s < d-2`), `decSuperIso/Hilb` (`UlocStarRegime`)), and the weak jet is
  unique; (b) `x ↦ δ_x ∈ W^{-m,p'}` is Lipschitz (`W^{m,p} ↪ C_b^1` in the jet norm, `m ≥ m_* + ⌊d/p⌋ + 1`).
  The proof takes the adjoint input as the stated hypothesis `AdjointInputRd (wClass m p) (wWeakClass m p) m_* (S.coeff N) T Kad`.
  Honest size 4-5.5k lines (the plan estimate 1.2-2k covers only the last two packets).
* **S.A.4 `main_rd_dec_stat`** is the S.A.2 engine for the test class `wClass` and the extra rate term `e_N^𝔠`; it cannot be
  proved without the S.A.2 engine (worker SA2).  Only engine-independent conditional pieces are provided (if at all).

## Packets (files `HRS/MS/ZeroTempAux<k>.lean`, tie `ZeroTempTie.lean`, namespace `HRS.MS.ZeroTemp`, helpers `sa11_`)

A1 (this file): `V = C_c^∞` as a submodule, jets `J : V →ₗ W^{m,p}`, density of the range, `‖Jφ‖` versus `movWNormE`.
A2: integration by parts for jets, uniqueness of weak jets (`sa11_zeroth_inj`), `wNormE = ‖G‖`.
A3: jet-norm Sobolev embedding `‖D^iφ(x)‖ ≤ C ‖Jφ‖`, `i ≤ m_*`.
A4: extension of bounded linear maps from jets, evaluation functionals, a.s. equality of dual-valued random variables.
B1: linearity of `generatorW` on `C_b²`, `CoeffHypRd` from `RdStanding`, uniqueness, linearity of `propagatorW`.
B2: `T`, `Z`, `Ξ`, the two representation clauses.  C1: commutator bridge (S.B.5).  C2: pathwise remainder bound.
D: assembly and `type_of%` tie.
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

/-! ### `C_c^∞` as a submodule -/

/-- `C_c^∞(ℝ^d)` as a real vector space of functions. -/
def sa11_V (d : ℕ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {φ | IsCcInfty φ}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c x hx => ⟨hx.1.const_smul c, hx.2.smul_left⟩

theorem sa11_mem_V {φ : Euc d → ℝ} : φ ∈ sa11_V d ↔ IsCcInfty φ := Iff.rfl

/-! ### The jet of a `C_c^∞` function -/

theorem sa11_wJet_continuous {m : ℕ} {φ : Euc d → ℝ} (hφ : IsCcInfty φ) : Continuous (wJet m φ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x => iteratedFDeriv ℝ (τ.1 : ℕ) φ x (fun l => EuclideanSpace.single (τ.2 l) 1)
  have h := hφ.1.continuous_iteratedFDeriv (m := (τ.1 : ℕ)) (by exact_mod_cast le_top)
  exact (continuous_eval_const (fun l => EuclideanSpace.single (τ.2 l) (1 : ℝ))).comp h

theorem sa11_wJet_support {m : ℕ} {φ : Euc d → ℝ} (hφ : IsCcInfty φ) : HasCompactSupport (wJet m φ) := by
  refine HasCompactSupport.intro hφ.2 fun x hx => ?_
  funext τ
  have : iteratedFDeriv ℝ (τ.1 : ℕ) φ x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset (𝕜 := ℝ) (τ.1 : ℕ) h)
  show iteratedFDeriv ℝ (τ.1 : ℕ) φ x _ = 0
  rw [this]; rfl

theorem sa11_wJet_memLp {m : ℕ} {p : ℝ} {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    MemLp (wJet m φ) (ENNReal.ofReal p) volume :=
  (sa11_wJet_continuous hφ).memLp_of_hasCompactSupport (sa11_wJet_support hφ)

theorem sa11_wJet_add {m : ℕ} {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    wJet m (φ + ψ) = wJet m φ + wJet m ψ := by
  funext x τ
  show iteratedFDeriv ℝ (τ.1 : ℕ) (φ + ψ) x _ = iteratedFDeriv ℝ (τ.1 : ℕ) φ x _ + iteratedFDeriv ℝ (τ.1 : ℕ) ψ x _
  rw [iteratedFDeriv_add_apply (hφ.1.of_le (by exact_mod_cast le_top)).contDiffAt
    (hψ.1.of_le (by exact_mod_cast le_top)).contDiffAt]
  rfl

theorem sa11_wJet_smul {m : ℕ} (c : ℝ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    wJet m (c • φ) = c • wJet m φ := by
  funext x τ
  show iteratedFDeriv ℝ (τ.1 : ℕ) (c • φ) x _ = c * iteratedFDeriv ℝ (τ.1 : ℕ) φ x _
  rw [iteratedFDeriv_const_smul_apply (hφ.1.of_le (by exact_mod_cast le_top)).contDiffAt]
  rfl

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- The jet of `φ ∈ C_c^∞` as an element of `L^p(ℝ^d; ℝ^{WIndex d m})`. -/
def sa11_jetLp (φ : sa11_V d) : WLp d m p :=
  MemLp.toLp (wJet m φ.1) (sa11_wJet_memLp φ.2)

theorem sa11_jetLp_coe (φ : sa11_V d) : ((sa11_jetLp (m := m) (p := p) φ : WLp d m p) : Euc d → (WIndex d m → ℝ))
    =ᵐ[volume] wJet m φ.1 :=
  MemLp.coeFn_toLp _

theorem sa11_jetLp_mem (φ : sa11_V d) : sa11_jetLp (m := m) (p := p) φ ∈ WmpSpace d m p := by
  refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
  exact ⟨φ.1, φ.2, sa11_jetLp_coe φ⟩

/-- The jet map `J : C_c^∞ → W^{m,p}`. -/
def sa11_J : sa11_V d →ₗ[ℝ] WmpSpace d m p where
  toFun φ := ⟨sa11_jetLp φ, sa11_jetLp_mem φ⟩
  map_add' a b := by
    apply Subtype.ext
    show sa11_jetLp (a + b) = sa11_jetLp a + sa11_jetLp b
    unfold sa11_jetLp
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by
      show wJet m (a.1 + b.1) x = (wJet m a.1 + wJet m b.1) x
      rw [sa11_wJet_add a.2 b.2])
  map_smul' c a := by
    apply Subtype.ext
    show sa11_jetLp (c • a) = c • sa11_jetLp a
    unfold sa11_jetLp
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by
      show wJet m (c • a.1) x = (c • wJet m a.1) x
      rw [sa11_wJet_smul c a.2])

theorem sa11_J_coe (φ : sa11_V d) :
    (((sa11_J (m := m) (p := p) φ : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ))
      =ᵐ[volume] wJet m φ.1 := sa11_jetLp_coe φ

/-- An element of `W^{m,p}` whose representative is a.e. the jet of `φ ∈ C_c^∞` is `J φ`. -/
theorem sa11_eq_J {φ : sa11_V d} {F : WmpSpace d m p}
    (h : ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ.1) :
    F = sa11_J φ := by
  apply Subtype.ext
  apply Lp.ext
  exact h.trans (sa11_J_coe φ).symm

theorem sa11_norm_J (φ : sa11_V d) :
    ‖sa11_J (m := m) (p := p) φ‖ = (eLpNorm (wJet m φ.1) (ENNReal.ofReal p) volume).toReal := by
  show ‖sa11_jetLp (m := m) (p := p) φ‖ = _
  unfold sa11_jetLp
  rw [Lp.norm_toLp]

theorem sa11_enorm_J (φ : sa11_V d) :
    ‖sa11_J (m := m) (p := p) φ‖ₑ = eLpNorm (wJet m φ.1) (ENNReal.ofReal p) volume := by
  show ‖sa11_jetLp (m := m) (p := p) φ‖ₑ = _
  unfold sa11_jetLp
  rw [Lp.enorm_toLp]

/-! ### Density of the jets -/

/-- The jets `J φ`, `φ ∈ C_c^∞`, are dense in `W^{m,p}`. -/
theorem sa11_denseRange_J : DenseRange (sa11_J (d := d) (m := m) (p := p)) := by
  intro F
  set R : Submodule ℝ (WLp d m p) := (LinearMap.range (sa11_J (d := d) (m := m) (p := p))).map
    (WmpSpace d m p).subtype with hR
  have hsp : Submodule.span ℝ {F : WLp d m p |
      ∃ φ : Euc d → ℝ, IsCcInfty φ ∧ (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ} ≤ R := by
    refine Submodule.span_le.2 ?_
    rintro G ⟨φ, hφ, hG⟩
    refine ⟨sa11_J ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩, ?_⟩
    apply Lp.ext
    exact (sa11_J_coe (m := m) (p := p) ⟨φ, hφ⟩).trans hG.symm
  have h1 : (F : WLp d m p) ∈ closure (R : Set (WLp d m p)) := by
    have := F.2
    have h2 : (WmpSpace d m p : Set (WLp d m p)) ⊆ closure (R : Set (WLp d m p)) := by
      intro G hG
      have : G ∈ (Submodule.span ℝ {F : WLp d m p |
          ∃ φ : Euc d → ℝ, IsCcInfty φ ∧ (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ}).topologicalClosure := hG
      have h3 := Submodule.topologicalClosure_mono hsp this
      exact h3
    exact h2 this
  have hRe : Subtype.val '' Set.range (sa11_J (d := d) (m := m) (p := p)) = (R : Set (WLp d m p)) := by
    ext G
    simp [hR, LinearMap.mem_range]
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have h1' : (F : WLp d m p) ∈ closure (Subtype.val '' Set.range (sa11_J (d := d) (m := m) (p := p))) :=
    hRe ▸ h1
  exact h1'


/-! ### The classical-derivative norm versus the jet norm -/

omit [Fact (2 ≤ p)] in
/-- The operator norm of a multilinear form on `ℝ^d` is at most the sum of its values on basis tuples. -/
theorem sa11_opNorm_le_sum {i : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ) :
    ‖A‖ ≤ ∑ τ : Fin i → Fin d, |A (fun l => EuclideanSpace.single (τ l) 1)| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  have hv : ∀ l, v l = ∑ k : Fin d, (v l k) • (EuclideanSpace.single k (1 : ℝ) : Euc d) := by
    intro l
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v l)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  have h1 : A v = ∑ τ : Fin i → Fin d, (∏ l, v l (τ l)) • A (fun l => EuclideanSpace.single (τ l) 1) := by
    have := A.toMultilinearMap.map_sum (g := fun (l : Fin i) (k : Fin d) => (v l k) • (EuclideanSpace.single k (1 : ℝ) : Euc d))
    have e : A v = A.toMultilinearMap (fun l => ∑ k : Fin d, (v l k) • (EuclideanSpace.single k (1 : ℝ) : Euc d)) := by
      show A v = A (fun l => ∑ k : Fin d, (v l k) • (EuclideanSpace.single k (1 : ℝ) : Euc d))
      congr 1
      funext l
      exact hv l
    rw [e, this]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact A.toMultilinearMap.map_smul_univ (fun l => v l (τ l)) (fun l => EuclideanSpace.single (τ l) (1 : ℝ))
  rw [h1]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ τ : Fin i → Fin d, ‖(∏ l, v l (τ l)) • A (fun l => EuclideanSpace.single (τ l) 1)‖
      ≤ ∑ τ : Fin i → Fin d, (∏ l, ‖v l‖) * |A (fun l => EuclideanSpace.single (τ l) 1)| := by
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
        refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ => ?_) (abs_nonneg _)
        have := PiLp.norm_apply_le (v l) (τ l)
        simpa [Real.norm_eq_abs] using this
    _ = (∑ τ : Fin i → Fin d, |A (fun l => EuclideanSpace.single (τ l) 1)|) * ∏ l, ‖v l‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        ring

omit [Fact (2 ≤ p)] in
/-- `‖D^iφ(x)‖ ≤ d^i ‖jet φ (x)‖` for `i ≤ m`. -/
theorem sa11_iter_le_jet {φ : Euc d → ℝ} {i : ℕ} (hi : i ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ i φ x‖ ≤ (d : ℝ) ^ i * ‖wJet m φ x‖ := by
  refine (sa11_opNorm_le_sum _).trans ?_
  have hterm : ∀ τ : Fin i → Fin d,
      |iteratedFDeriv ℝ i φ x (fun l => EuclideanSpace.single (τ l) 1)| ≤ ‖wJet m φ x‖ := by
    intro τ
    have := norm_le_pi_norm (wJet m φ x) (⟨⟨i, Nat.lt_succ_of_le hi⟩, τ⟩ : WIndex d m)
    simpa [wJet, partialDeriv, Real.norm_eq_abs] using this
  calc ∑ τ : Fin i → Fin d, |iteratedFDeriv ℝ i φ x (fun l => EuclideanSpace.single (τ l) 1)|
      ≤ ∑ _τ : Fin i → Fin d, ‖wJet m φ x‖ := Finset.sum_le_sum fun τ _ => hterm τ
    _ = (d : ℝ) ^ i * ‖wJet m φ x‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [Fintype.card_fun]

/-- The constant `∑_{i ≤ m} d^i`. -/
def sa11_cJ (d m : ℕ) : ℝ := ∑ i ∈ Finset.range (m + 1), (d : ℝ) ^ i

theorem sa11_cJ_nonneg (d m : ℕ) : 0 ≤ sa11_cJ d m :=
  Finset.sum_nonneg fun _ _ => by positivity

omit [Fact (2 ≤ p)] in
/-- `movWNormE m p φ ≤ (∑ d^i) ‖jet φ‖_{L^p}`. -/
theorem sa11_movW_le {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    movWNormE m (ENNReal.ofReal p) φ ≤
      ENNReal.ofReal (sa11_cJ d m) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
  unfold movWNormE sa11_cJ
  have hterm : ∀ i ∈ Finset.range (m + 1),
      eLpNorm (fun x => ‖iteratedFDeriv ℝ i φ x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : Continuous (iteratedFDeriv ℝ i φ) :=
      hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    calc eLpNorm (fun x => ‖iteratedFDeriv ℝ i φ x‖) (ENNReal.ofReal p) volume
        ≤ eLpNorm (((d : ℝ) ^ i) • wJet m φ) (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_ae hc.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
          rw [norm_norm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact sa11_iter_le_jet him x
      _ = ENNReal.ofReal ((d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  calc ∑ i ∈ Finset.range (m + 1), eLpNorm (fun x => ‖iteratedFDeriv ℝ i φ x‖) (ENNReal.ofReal p) volume
      ≤ ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ i ∈ Finset.range (m + 1), (d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]

/-- `C_c^∞` functions belong to the test class `wClass m p`. -/
theorem sa11_wClass_mem (φ : sa11_V d) : (wClass m p).mem φ.1 := by
  refine ⟨φ.2.1.of_le (by exact_mod_cast le_top), ?_⟩
  refine lt_of_le_of_lt (sa11_movW_le φ.2) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (sa11_wJet_memLp (m := m) (p := p) φ.2).eLpNorm_lt_top

/-- `‖φ‖_{wClass} ≤ (∑ d^i) ‖J φ‖`. -/
theorem sa11_wClass_norm_le (φ : sa11_V d) :
    (wClass m p).norm φ.1 ≤ sa11_cJ d m * ‖sa11_J (m := m) (p := p) φ‖ := by
  show (movWNormE m (ENNReal.ofReal p) φ.1).toReal ≤ _
  rw [sa11_norm_J]
  have hfin : eLpNorm (wJet m φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
    (sa11_wJet_memLp (m := m) (p := p) φ.2).eLpNorm_lt_top.ne
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (sa11_movW_le (m := m) (p := p) φ.2)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sa11_cJ_nonneg d m)] at h

end HRS.MS.ZeroTemp
