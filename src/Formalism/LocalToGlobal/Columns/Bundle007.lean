module

public import Formalism.LocalToGlobal.Columns.Bundle004
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Columns.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)


end Formalism.L2.Col.CF

end
end

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dite_eq_left (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG (E := E) (n := n) (SG := SG)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (ψ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

structure Lev (κ K : Type) [CommRing κ] [Field K] (n : ℕ) where

  H : Subgroup (GL (Fin n) κ)

  lam : ↥H →* Kˣ

def Lev.inv {κ K : Type} [CommRing κ] [Field K] {n : ℕ} (l : Lev κ K n) : Lev κ K n := ⟨l.H, l.lam⁻¹⟩

abbrev LevFam (E K : Type) [Field E] [NumberField E] [Field K] (n : ℕ)
    (SG : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ∀ w : SG, Lev (𝓞 E ⧸ w.1.asIdeal) K n

namespace LevFam

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

def grp : Subgroup (GLG (E := E) (n := n) (SG := SG)) := Subgroup.pi Set.univ fun w => (Λ w).H

def chr : ↥Λ.grp →* Kˣ := piChar (fun w => (Λ w).H) fun w => (Λ w).lam

def inv : LevFam E K n SG := fun w => (Λ w).inv

end LevFam

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

abbrev FormG (Λ : LevFam X.E X.K n SG) : Type := UF X.E n × ↥Λ.grp

@[reducible] def FormG.incl (Λ : LevFam X.E X.K n SG) : FormG Λ →* UF X.E n × GLG (E := X.E) (n := n) (SG := SG) :=
  MonoidHom.prodMap (MonoidHom.id _) Λ.grp.subtype

instance formAct (Λ : LevFam X.E X.K n SG) : MulAction (FormG Λ) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :=
  MulAction.compHom _ (FormG.incl Λ)

def formRho (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) :
    FormG Λ →* Module.End X.K C.V where
  toFun a := ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]


open Classical in
@[reducible] def formGSD (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) : GSD X.K where
  G := FormG Λ
  D := DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)
  actD := formAct Λ
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  ρ := formRho C Λ
  Nab := C.Nab
  Del := C.Del

structure CoefPk.Eqv (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) : Prop where
  nab_smul : ∀ (a : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
    C.Nab (a • d) = (C.Nab d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  del_smul : ∀ (a : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
    C.Del (a • d) = (C.Del d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  inv : ∀ (γ : UF X.E n) (x y : C.V), C.pair (C.rho γ x) (C.rho γ y) = C.pair x y

instance formModO (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) :
    Module (𝓞 X.K) (formGSD C Λ).EqFun :=
  (fun S : GSD X.K => (inferInstance : Module (𝓞 X.K) S.EqFun)) (formGSD C Λ)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def colLev (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j < R.m then
    ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩
  else
    ⟨HXm (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.r R.t R.m,
      lamXm (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.r R.t R.m⟩

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

@[reducible] def colGSD (u : Pr.Word) (j : ℕ) : GSD X.K :=
  formGSD (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j)

abbrev ColV (u : Pr.Word) (j : ℕ) : Submodule X.K ((colGSD W Ch u j).D → (colGSD W Ch u j).V) :=
  (colGSD W Ch u j).EqFun

def ColL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) := (colGSD W Ch u j).intDel

abbrev MfV (u : Pr.Word) : Submodule X.K ((colGSD W Ch u 0).D → (colGSD W Ch u 0).V) := ColV W Ch u 0

def MfL (u : Pr.Word) : Submodule (𝓞 X.K) (MfV W Ch u) := ColL W Ch u 0

end Cols

end Formalism.L2.Col
end
end
