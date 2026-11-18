import HRS.MC.CepH3H2

/-!
# Packet CEPH3, part I1: the cut-off pull-back of a test field to chamber coordinates
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

/-- Smooth cutoff in one pair-difference. -/
def h3i_theta (δ u : ℝ) : ℝ :=
  Real.smoothTransition ((u - δ / 4) / (δ / 4)) * Real.smoothTransition (((1 - δ / 4) - u) / (δ / 4))

lemma h3i_theta_contDiff (δ : ℝ) : ContDiff ℝ ∞ (h3i_theta δ) := by
  unfold h3i_theta
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma h3i_theta_ne_zero {δ u : ℝ} (hδ : 0 < δ) (h : h3i_theta δ u ≠ 0) : δ / 4 < u ∧ u < 1 - δ / 4 := by
  unfold h3i_theta at h
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  constructor
  · by_contra hc
    push_neg at hc
    apply h1
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  · by_contra hc
    push_neg at hc
    apply h2
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

lemma h3i_theta_eq_one {δ u : ℝ} (hδ : 0 < δ) (h1 : δ / 2 ≤ u) (h2 : u ≤ 1 - δ / 2) : h3i_theta δ u = 1 := by
  unfold h3i_theta
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, one_mul]
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-- The product cutoff `χ(z) = ∏_{k<l} θ(z_l - z_k)`. -/
def h3i_chi (δ : ℝ) (z : Ch N) : ℝ :=
  ∏ k : Fin N, ∏ l : Fin N, if k < l then h3i_theta δ (z l - z k) else 1

lemma h3i_chi_contDiff (δ : ℝ) : ContDiff ℝ ∞ (h3i_chi (N := N) δ) := by
  unfold h3i_chi
  refine contDiff_prod fun k _ => contDiff_prod fun l _ => ?_
  by_cases h : k < l
  · simp only [h, ite_true]
    exact (h3i_theta_contDiff δ).comp (by fun_prop)
  · simp only [h, ite_false]; exact contDiff_const

lemma h3i_chi_periodic (δ : ℝ) (z : Ch N) [NeZero N] : h3i_chi δ (z + cep_diag N) = h3i_chi δ z := by
  unfold h3i_chi
  simp [cep_diag]

lemma h3i_chi_ne_zero {δ : ℝ} (hδ : 0 < δ) {z : Ch N} (h : h3i_chi δ z ≠ 0) :
    ∀ k l : Fin N, k < l → δ / 4 < z l - z k ∧ z l - z k < 1 - δ / 4 := by
  intro k l hkl
  unfold h3i_chi at h
  have := (Finset.prod_ne_zero_iff.mp h) k (Finset.mem_univ k)
  have := (Finset.prod_ne_zero_iff.mp this) l (Finset.mem_univ l)
  simp only [hkl, ite_true] at this
  exact h3i_theta_ne_zero hδ this

lemma h3i_chi_eq_one {δ : ℝ} (hδ : 0 < δ) {z : Ch N}
    (h : ∀ k l : Fin N, k < l → δ / 2 ≤ z l - z k ∧ z l - z k ≤ 1 - δ / 2) : h3i_chi δ z = 1 := by
  unfold h3i_chi
  refine Finset.prod_eq_one fun k _ => Finset.prod_eq_one fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    exact h3i_theta_eq_one hδ (h k l hkl).1 (h k l hkl).2
  · simp [hkl]

lemma h3i_unrank_contDiff [NeZero N] (σ₀ : Equiv.Perm (Fin N)) : ContDiff ℝ ∞ (cep_unrank σ₀ : Ch N → (Fin N → Euc 1)) := by
  refine contDiff_pi.mpr fun i => ?_
  unfold cep_unrank
  exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun _ => contDiff_piLp_apply (p := 2) (i := σ₀.symm i))

/-- The pull-back to chamber coordinates of a field on `Config`. -/
def h3i_za (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (z : Ch N) : Ch N :=
  WithLp.toLp 2 fun k => (ζ (h3d_Q σ₀ z) (σ₀ k)) 0

/-- The cut-off pull-back. -/
def h3i_zt (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (δ : ℝ) (z : Ch N) : Ch N :=
  WithLp.toLp 2 fun k => h3i_chi δ z * (ζ (h3d_Q σ₀ z) (σ₀ k)) 0

lemma h3i_comp_contDiff [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc 1 => ζ (fun i => Torus.mk (Y i)))) (k : Fin N) :
    ContDiff ℝ ∞ (fun z : Ch N => (ζ (h3d_Q σ₀ z) (σ₀ k)) 0) := by
  have h0 : ContDiff ℝ ∞ (fun Y : Fin N → Euc 1 => ζ (fun i => Torus.mk (Y i)) (σ₀ k)) := contDiff_pi.mp hζ _
  have h1 : ContDiff ℝ ∞ (fun Y : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Y i)) (σ₀ k)) 0) :=
    (contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))).comp h0
  exact h1.comp (h3i_unrank_contDiff σ₀)

lemma h3i_za_contDiff [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc 1 => ζ (fun i => Torus.mk (Y i)))) :
    ContDiff ℝ ∞ (h3i_za σ₀ ζ) :=
  contDiff_piLp' 2 fun k => h3i_comp_contDiff σ₀ hζ k

lemma h3i_zt_contDiff [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc 1 => ζ (fun i => Torus.mk (Y i)))) (δ : ℝ) :
    ContDiff ℝ ∞ (h3i_zt σ₀ ζ δ) :=
  contDiff_piLp' 2 fun k => (h3i_chi_contDiff δ).mul (h3i_comp_contDiff σ₀ hζ k)

lemma h3i_diag_eq (N : ℕ) : cep_diag N = h3d_shift (fun _ => 1) := by
  ext k; simp [cep_diag, h3d_shift]

lemma h3i_Q_diag [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) : h3d_Q σ₀ (z + cep_diag N) = h3d_Q σ₀ z := by
  rw [h3i_diag_eq]; exact h3d_Q_add_int σ₀ z _

lemma h3i_zt_periodic [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (δ : ℝ) (z : Ch N) :
    h3i_zt σ₀ ζ δ (z + cep_diag N) = h3i_zt σ₀ ζ δ z := by
  unfold h3i_zt
  rw [h3i_chi_periodic, h3i_Q_diag]

lemma h3i_za_periodic [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (z : Ch N) :
    h3i_za σ₀ ζ (z + cep_diag N) = h3i_za σ₀ ζ z := by
  unfold h3i_za
  rw [h3i_Q_diag]

/-- The closed set carrying the cutoff. -/
def h3i_Ssup (δ : ℝ) : Set (Ch N) := {z | ∀ k l : Fin N, k < l → δ / 4 ≤ z l - z k ∧ z l - z k ≤ 1 - δ / 4}

lemma h3i_Ssup_closed (δ : ℝ) : IsClosed (h3i_Ssup (N := N) δ) := by
  have : h3i_Ssup (N := N) δ = ⋂ k, ⋂ l, ⋂ (_ : k < l), {z : Ch N | δ / 4 ≤ z l - z k ∧ z l - z k ≤ 1 - δ / 4} := by
    ext z; simp [h3i_Ssup]
  rw [this]
  refine isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ => ?_
  exact IsClosed.inter (s₁ := {z : Ch N | δ / 4 ≤ z l - z k}) (s₂ := {z : Ch N | z l - z k ≤ 1 - δ / 4})
    (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const)

lemma h3i_Ssup_subset {δ : ℝ} (hδ : 0 < δ) : h3i_Ssup (N := N) δ ⊆ cep_Alcove N := by
  intro z hz
  refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
  · have := (hz k l hkl).1; linarith
  · rcases lt_trichotomy k l with h | h | h
    · have := (hz k l h).2; linarith
    · subst h; linarith
    · have := (hz l k h).1; linarith

lemma h3i_chi_support {δ : ℝ} (hδ : 0 < δ) {z : Ch N} (h : h3i_chi δ z ≠ 0) : z ∈ h3i_Ssup δ :=
  fun k l hkl => ⟨(h3i_chi_ne_zero hδ h k l hkl).1.le, (h3i_chi_ne_zero hδ h k l hkl).2.le⟩

lemma h3i_zt_eventually_zero {σ₀ : Equiv.Perm (Fin N)} {ζ : Config 1 N → (Fin N → Euc 1)} {δ : ℝ} (hδ : 0 < δ)
    {z : Ch N} (hz : z ∉ cep_Alcove N) : ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = 0 := by
  have hopen : IsOpen (h3i_Ssup (N := N) δ)ᶜ := (h3i_Ssup_closed δ).isOpen_compl
  filter_upwards [hopen.mem_nhds (fun h => hz (h3i_Ssup_subset hδ h))] with w hw
  have : h3i_chi δ w = 0 := by
    by_contra hne
    exact hw (h3i_chi_support hδ hne)
  unfold h3i_zt
  ext k
  simp [this]
end
end HRS.MC.CepH3