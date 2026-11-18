/-
# HRS.Equilibrium.Q84dAuxM — packet Q84d: integration by parts along coordinate lines

`lineCfg i k Y t` translates the `k`-th coordinate of the `i`-th particle by `t`.  If for a.e. `Y`
the function `t ↦ w(lineCfg Y t)` is differentiable on all of `ℝ` with derivative `v(lineCfg Y t)`
and `v` is integrable, then `∫ v = 0`: Fubini over the line `[0,1]` and translation invariance of
Haar measure (the line is closed, `lineCfg Y 1 = Y`).  Collisions never obstruct this since the
line avoids them for almost every `Y` when `d ≥ 2` (`q84d_ae_line_free`).
-/
import HRS.Equilibrium.Q84dAuxL

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {N : ℕ}

/-- The standard basis vector `e_k` of `ℝ^d`. -/
abbrev ek (k : Fin d) : Euc d := EuclideanSpace.single k (1 : ℝ)

/-- Translate the `k`-th coordinate of the `i`-th particle by `t`. -/
def lineCfg (i : Fin N) (k : Fin d) (Y : Config d N) (t : ℝ) : Config d N :=
  Function.update Y i (Y i + Torus.mk (t • ek k))

theorem lineCfg_eq_add (i : Fin N) (k : Fin d) (Y : Config d N) (t : ℝ) :
    lineCfg i k Y t = Y + Pi.single i (Torus.mk (t • ek k)) := by
  funext a
  by_cases h : a = i
  · subst h; simp [lineCfg]
  · simp [lineCfg, h]

theorem q84d_mk_zero : (Torus.mk (0 : Euc d)) = 0 := by
  funext a; simp [Torus.mk]

theorem lineCfg_zero (i : Fin N) (k : Fin d) (Y : Config d N) : lineCfg i k Y 0 = Y := by
  funext a
  by_cases h : a = i
  · subst h; simp [lineCfg, q84d_mk_zero]
  · simp [lineCfg, Function.update_of_ne h]

theorem lineCfg_one (i : Fin N) (k : Fin d) (Y : Config d N) : lineCfg i k Y 1 = Y := by
  have h1 : Torus.mk (ek k) = (0 : Torus d) := by
    funext a
    by_cases h : a = k
    · subst h
      simp [Torus.mk, ek]
    · simp [Torus.mk, ek, h]
  funext a
  by_cases h : a = i
  · subst h; simp [lineCfg, h1]
  · simp [lineCfg, Function.update_of_ne h]

theorem lineCfg_add (i : Fin N) (k : Fin d) (Y : Config d N) (s t : ℝ) :
    lineCfg i k (lineCfg i k Y s) t = lineCfg i k Y (s + t) := by
  rw [lineCfg_eq_add, lineCfg_eq_add, lineCfg_eq_add, add_assoc]
  congr 1
  funext a
  by_cases h : a = i
  · subst h
    simp [Torus.mk, add_smul]
    funext b; simp [Torus.mk, add_smul]
  · simp [h]

theorem q84d_measurable_lineCfg (i : Fin N) (k : Fin d) :
    Measurable (fun p : Config d N × ℝ => lineCfg i k p.1 p.2) := by
  refine measurable_pi_iff.2 fun a => ?_
  by_cases h : a = i
  · subst h
    simp only [lineCfg, Function.update_self]
    refine ((measurable_pi_apply a).comp measurable_fst).add ?_
    exact (Q84a.q84a_continuous_mk (d := d)).measurable.comp
      (measurable_snd.smul_const _)
  · simp only [lineCfg, Function.update_of_ne h]
    exact (measurable_pi_apply a).comp measurable_fst

theorem q84d_translate_mp (z : Config d N) :
    MeasurePreserving (fun Y : Config d N => Y + z) volume volume :=
  measurePreserving_pi (fun _ : Fin N => (volume : Measure (Torus d)))
    (fun _ : Fin N => (volume : Measure (Torus d))) (f := fun a => fun x : Torus d => x + z a)
    (fun a => measurePreserving_add_right volume (z a))

theorem lineCfg_mp (i : Fin N) (k : Fin d) (t : ℝ) :
    MeasurePreserving (fun Y : Config d N => lineCfg i k Y t) volume volume := by
  have : (fun Y : Config d N => lineCfg i k Y t) = fun Y => Y + Pi.single i (Torus.mk (t • ek k)) :=
    funext fun Y => lineCfg_eq_add i k Y t
  rw [this]
  exact q84d_translate_mp _

end HRS.Q84d

end
