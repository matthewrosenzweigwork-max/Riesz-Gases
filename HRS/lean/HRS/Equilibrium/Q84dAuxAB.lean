/-
# HRS.Equilibrium.Q84dAuxAB — packet Q84d: strictly measurable modification of `G_ψ`
-/
import HRS.Equilibrium.Q84dAuxAA

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_measurable_comp_pair {α : Type*} [MeasurableSpace α] {F : Torus d → Torus d → ℝ}
    (hF : Measurable (fun p : Torus d × Torus d => F p.1 p.2)) {u v : α → Torus d}
    (hu : Measurable u) (hv : Measurable v) : Measurable (fun t => F (u t) (v t)) :=
  hF.comp (hu.prodMk hv)

/-- Measurable surrogate of `T_ψ(x,y,z)`. -/
def TsurK (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y z : Torus d) : ℝ :=
  -(∑ k, gK ψ k x y * (centeredForce d s ρ x z) k) - ∑ k, gK ψ k y x * (centeredForce d s ρ y z) k

theorem q84d_Tpsi_eq_TsurK {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) (z : Torus d) : Tpsi d s ρ ψ x y z = TsurK d s ρ ψ x y z := by
  have h1 : ∀ k, (gradFst ψ x y) k = gK ψ k x y := fun k => q84d_grad_comp hsm hxy k
  have h2 : ∀ k, (gradSnd ψ x y) k = gK ψ k y x := fun k => by
    rw [Q84a.q84a_gradSnd_eq hsymm]; exact q84d_grad_comp hsm hxy.symm k
  unfold Tpsi TsurK
  simp only [PiLp.inner_apply, h1, h2]
  simp [mul_comm]

/-- Measurable surrogate of `G_ψ`. -/
def GsurK (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ)
    (Jh : Torus d → Torus d → ℝ) (x y z : Torus d) : ℝ :=
  (1 / 3) * (TsurK d s ρ ψ x y z + TsurK d s ρ ψ x z y + TsurK d s ρ ψ y z x) -
    (1 / 3) * (Jh x y + Jh x z + Jh y z)

open Classical in
/-- Symmetrised, collision/`E`-killed version of `GsurK`. -/
def Gtil (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (E : Set (Torus d))
    (Jh : Torus d → Torus d → ℝ) (x y z : Torus d) : ℝ :=
  if x ∈ E ∨ y ∈ E ∨ z ∈ E ∨ x = y ∨ x = z ∨ y = z then 0 else
    (1 / 6) * (GsurK d s ρ ψ Jh x y z + GsurK d s ρ ψ Jh y x z + GsurK d s ρ ψ Jh x z y +
      GsurK d s ρ ψ Jh z x y + GsurK d s ρ ψ Jh y z x + GsurK d s ρ ψ Jh z y x)

theorem q84d_measurable_TsurK {α : Type*} [MeasurableSpace α] (hsd : s < d) (ρ : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) {a b c : α → Torus d} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) :
    Measurable (fun t => TsurK d s ρ ψ (a t) (b t) (c t)) := by
  unfold TsurK
  have hg : ∀ k (u v : α → Torus d), Measurable u → Measurable v →
      Measurable (fun t => gK ψ k (u t) (v t)) := fun k u v hu hv =>
    q84d_measurable_comp_pair (F := fun x y => gK ψ k x y) (q84d_measurable_gK ψ k) hu hv
  have hK : ∀ k (u v : α → Torus d), Measurable u → Measurable v →
      Measurable (fun t => (centeredForce d s ρ (u t) (v t)) k) := fun k u v hu hv =>
    q84d_measurable_comp_pair (F := fun x y => (centeredForce d s ρ x y) k)
      (q84d_measurable_centeredForce hsd ρ k) hu hv
  have hA : Measurable (fun t => ∑ k, gK ψ k (a t) (b t) * (centeredForce d s ρ (a t) (c t)) k) :=
    Finset.measurable_sum _ fun k _ => (hg k a b ha hb).mul (hK k a c ha hc)
  have hB : Measurable (fun t => ∑ k, gK ψ k (b t) (a t) * (centeredForce d s ρ (b t) (c t)) k) :=
    Finset.measurable_sum _ fun k _ => (hg k b a hb ha).mul (hK k b c hb hc)
  exact hA.neg.sub hB

theorem q84d_measurable_GsurK {α : Type*} [MeasurableSpace α] (hsd : s < d) (ρ : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) {Jh : Torus d → Torus d → ℝ}
    (hJ : Measurable (fun p : Torus d × Torus d => Jh p.1 p.2))
    {a b c : α → Torus d} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun t => GsurK d s ρ ψ Jh (a t) (b t) (c t)) := by
  unfold GsurK
  have hT : ∀ (u v w : α → Torus d), Measurable u → Measurable v → Measurable w →
      Measurable (fun t => TsurK d s ρ ψ (u t) (v t) (w t)) := fun u v w hu hv hw =>
    q84d_measurable_TsurK hsd ρ ψ hu hv hw
  have hJ' : ∀ (u v : α → Torus d), Measurable u → Measurable v →
      Measurable (fun t => Jh (u t) (v t)) := fun u v hu hv =>
    q84d_measurable_comp_pair (F := Jh) hJ hu hv
  have hA : Measurable (fun t => TsurK d s ρ ψ (a t) (b t) (c t) + TsurK d s ρ ψ (a t) (c t) (b t) +
      TsurK d s ρ ψ (b t) (c t) (a t)) :=
    ((hT a b c ha hb hc).add (hT a c b ha hc hb)).add (hT b c a hb hc ha)
  have hB : Measurable (fun t => Jh (a t) (b t) + Jh (a t) (c t) + Jh (b t) (c t)) :=
    ((hJ' a b ha hb).add (hJ' a c ha hc)).add (hJ' b c hb hc)
  exact (measurable_const.mul hA).sub (measurable_const.mul hB)

theorem q84d_GsurK_eq_Gpsi {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {Jh : Torus d → Torus d → ℝ}
    {x y z : Torus d} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hJxy : Jpair d s ρ ψ x y = Jh x y) (hJxz : Jpair d s ρ ψ x z = Jh x z)
    (hJyz : Jpair d s ρ ψ y z = Jh y z) :
    GsurK d s ρ ψ Jh x y z = Gpsi d s ρ ψ x y z := by
  unfold GsurK Gpsi
  rw [q84d_Tpsi_eq_TsurK hsymm hsm hxy, q84d_Tpsi_eq_TsurK hsymm hsm hxz,
    q84d_Tpsi_eq_TsurK hsymm hsm hyz, hJxy, hJxz, hJyz]

theorem q84d_Gtil_eq {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {E : Set (Torus d)}
    {Jh : Torus d → Torus d → ℝ} (hsd : s < d)
    (hgood : ∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → Jpair d s ρ ψ x y = Jh x y)
    {x y z : Torus d} (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : Gtil d s ρ ψ E Jh x y z = Gpsi d s ρ ψ x y z := by
  classical
  have hS := Q84.q84_Gpsi_symm (s := s) (ρ := ρ) hsymm
  have e : ∀ a b c : Torus d, a ∉ E → b ∉ E → c ∉ E → a ≠ b → a ≠ c → b ≠ c →
      GsurK d s ρ ψ Jh a b c = Gpsi d s ρ ψ a b c := fun a b c ha hb hc hab hac hbc =>
    q84d_GsurK_eq_Gpsi hsymm hsm hab hac hbc (hgood a b ha hb hab) (hgood a c ha hc hac)
      (hgood b c hb hc hbc)
  have g1 : Gpsi d s ρ ψ y x z = Gpsi d s ρ ψ x y z := ((hS x y z).1).symm
  have g2 : Gpsi d s ρ ψ x z y = Gpsi d s ρ ψ x y z := ((hS x y z).2).symm
  have g3 : Gpsi d s ρ ψ z x y = Gpsi d s ρ ψ x y z := ((hS x z y).1).symm.trans g2
  have g4 : Gpsi d s ρ ψ y z x = Gpsi d s ρ ψ x y z := ((hS y x z).2).symm.trans g1
  have g5 : Gpsi d s ρ ψ z y x = Gpsi d s ρ ψ x y z := ((hS y z x).1).symm.trans g4
  unfold Gtil
  rw [if_neg (by
    rintro (h | h | h | h | h | h)
    · exact hx h
    · exact hy h
    · exact hz h
    · exact hxy h
    · exact hxz h
    · exact hyz h)]
  rw [e x y z hx hy hz hxy hxz hyz, e y x z hy hx hz hxy.symm hyz hxz, e x z y hx hz hy hxz hxy hyz.symm,
    e z x y hz hx hy hxz.symm hyz.symm hxy, e y z x hy hz hx hyz hxy.symm hxz.symm,
    e z y x hz hy hx hyz.symm hxz.symm hxy.symm, g1, g2, g3, g4, g5]
  ring

end HRS.Q84d

end
