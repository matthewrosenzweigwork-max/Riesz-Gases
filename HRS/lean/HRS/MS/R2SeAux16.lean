import HRS.MS.R2SeAux15

/-!
# S9.9 `r2_static_edgeworth`, packet 16: preliminaries of the linear-term limit

Worker S99, namespace `S99`.

* `s99_integral_abs_le_sqrt`: `∫|f| ≤ (∫ f²)^{1/2}` on a probability space;
* `s99_chi1`: correctors of order one of every observable `w ∈ C_b^{k0}` (S9.8 with `k = 1`, `J = k0`), uniform constant;
* `s99_cov_eq_w`: `C_{jk} = ∫ w_{jk} dμ`;
* the definitions `Aterm`, `cc`, `Alim` of the linear term.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_integral_abs_le_sqrt {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {f : α → ℝ} (hf : MemLp f 2 P) :
    ∫ x, |f x| ∂P ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂P) := by
  have hg : MemLp (fun x => |f x|) 2 P := hf.abs
  have hv := variance_nonneg (fun x => |f x|) P
  rw [variance_eq_sub hg] at hv
  have hI0 : 0 ≤ ∫ x, |f x| ∂P := integral_nonneg fun x => abs_nonneg _
  refine Real.le_sqrt_of_sq_le ?_
  have e : ∫ x, (f x) ^ 2 ∂P = ∫ x, (|f x|) ^ 2 ∂P := by
    congr 1; funext x; rw [sq_abs]
  rw [e]
  simpa [Pi.pow_apply] using (sub_nonneg.1 hv)

theorem s99_chi1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) {C c BU : ℝ} (hT : ThermalData d s a β C c BU) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ w : Euc d → ℝ, MemCb (k0 d) w → ∃ χ : Euc d → ℝ,
      ContDiff ℝ 2 χ ∧ S46.S46Feat d s a β γ w χ (K₂ * cbNorm (k0 d) w) ∧
      (∀ x, thermalGen d s a β χ x = γ * aRep d s a β γ w x) := by
  obtain ⟨K, hK, h⟩ := s99_chi hd hs0 hsd 1 le_rfl a β γ ha hβ hγ (k0 d) (one_lt_k0 d)
  refine ⟨K, hK, fun w hw => ?_⟩
  obtain ⟨χ, h1, h2, h3, h4, h5, h6⟩ := h w hw
  refine ⟨χ, h1.of_le (by norm_num), ?_, h3⟩
  exact s99_feat_S46 hT hγ le_rfl h1 h2 h3 h4 h5

theorem s99_cov_eq_w (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU : ℝ}
    (hγ : 0 < γ) (hT : ThermalData d s a β C c BU) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ) (j k : ℕ) :
    Cf d s a β γ φ j k = ∫ x, wF F j k x ∂(thermalMeasure d s a β) := by
  have hmem : ∀ j, MemLp (φ j) 2 (thermalMeasure d s a β) := by
    haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
      HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
    exact fun j => HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 j)
  have hDφ : ∀ l x, ‖fderiv ℝ (φ l) x‖ ≤ cbNorm (J1 d) (φ l) := fun l x =>
    s45_cb_deriv_le (by unfold J1; omega) (hφ.1 l) x
  have hBφ : ∀ l x, |φ l x| ≤ cbNorm (J1 d) (φ l) := fun l x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 l) x
    rwa [Real.norm_eq_abs] at this
  exact s99_cov_corr hd hs0 hsd hγ hT (hmem j) (F.feat hT hγ j) ((hφ.1 k).1.of_le (by
    exact_mod_cast (by unfold J1; omega : 1 ≤ J1 d))) (hBφ k) (hDφ k)

/-- The linear term. -/
def Aterm (d : ℕ) (s a β γ : ℝ) {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) (N : ℕ)
    (f : SeqL2 → ℝ) (p : ℕ × ℕ) : ℝ :=
  Real.sqrt N * ∫ X, (Cf d s a β γ φ p.1 p.2 - pair (empirical X) (wF F p.1 p.2)) *
    pd (pd f p.1) p.2 (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)

/-- The limit coefficients `c_{jk,m} = ∫ w_{jk} a_m dμ`. -/
def cc (d : ℕ) (s a β γ : ℝ) {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) (p : ℕ × ℕ) (m : ℕ) : ℝ :=
  ∫ x, wF F p.1 p.2 x * aRep d s a β γ (φ m) x ∂(thermalMeasure d s a β)

/-- The limit of the linear term. -/
def Alim (d : ℕ) (s a β γ : ℝ) {φ : ℕ → Euc d → ℝ} (F : FamData d s a β γ φ) (G : Measure SeqL2)
    (f : SeqL2 → ℝ) (p : ℕ × ℕ) : ℝ :=
  -∑' m, cc d s a β γ F p m * ∫ z, pd (pd (pd f p.1) p.2) m z ∂G

end S99

end
