module

public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.Columns.HeckeSp
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.GL3MeanSquares.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Coord

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

structure CoordAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, co (x + y) = co x + co y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → co x = 0
  surj : ∀ c, ∃ x ∈ N, co x = c
  ker : ∀ x ∈ N, co x = 0 → x ∈ P.asIdeal • N

structure FunAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, f (x + y) = f x + f y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → f x = 0

def coF {P : HeightOneSpectrum (𝓞 E)} (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) (c : Fin n → 𝓞 E ⧸ P.asIdeal)
    (y : Sp E n) : 𝓞 E ⧸ P.asIdeal := ∑ i, c i * co y i

def dualV {κ : Type} [CommRing κ] (x : Fin n → κ) : Fin n → κ := Classical.epsilon fun c => ∑ i, c i * x i = 1

def liftV {P : HeightOneSpectrum (𝓞 E)} (N : Submodule (𝓞 E) (Sp E n)) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.asIdeal) : Sp E n := Classical.epsilon fun y => y ∈ N ∧ co y = x

end Coord

section Fib

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.fibF (d : Deco E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG := d.repl P d.N (coF co c)

def DecoSet.fibF (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  open Classical in if h : (d.1.fibF P co c).Ok then ⟨_, h⟩ else d

def DecoSet.fibX (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  (d.fibF P co (dualV x)).up P q (liftV d.1.N co x)

structure SepElt (ST : Finset (HeightOneSpectrum (𝓞 E))) (a : 𝓞 E) : Prop where
  conj : ∀ P : ST, cO (E := E) a ∈ P.1.asIdeal
  off : ∀ P : ST, a ∉ P.1.asIdeal

end Fib

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

variable {C Λ}

def resX {R : Type} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 X.E)
    (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)) (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) :
    (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun x => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibX P q co x))

end Ops

@[reducible] def resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

@[reducible] def resFintype {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _

section Below

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K)

def SameBelow (w : HeightOneSpectrum (𝓞 K)) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ τ, (∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') ∧
    ∀ x ∈ L', ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L

end Below

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (AddMonoidAlgebra.coeff P m)‖ ^ 2 = ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) * ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι]

end Gen

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dite_eq_left (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)


open Classical in
theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace RowPar

variable {R : Ranks} (S : RowPar R)

def lamWQ (i : Fin R.r) : ℚ := S.aPlus R.m (i.1 + 1) + (R.nV : ℚ) / 2 - S.eAt (R.m - 1)

def lamW : DomWeight R.r := ofQ S.lamWQ

end RowPar

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

def lamW (τ : X.Tau) : DomWeight R.r := (W.row τ).lamW

end Wts

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def wmVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : CoefPk X R.r (DecoSet (E := X.E) (n := R.r) (ST := ∅) (SG := SG)) :=
  roundPk X W.lamW fun d => d.1.N

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


variable (R) in
def wmTyQ (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K R.r Q := fun _ => ⟨⊤, 1⟩

def wmTy (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K R.r (rowSG Pr sel mu) :=
  P.inv.glue (wmTyQ R (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def wmGSD (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  formGSD (wmVal W (rowSG Pr sel mu)) (wmTy sel mu P).inv

end Forms

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E]

variable {SG : Finset (HeightOneSpectrum (𝓞 E))}

def wmIsRed {a b : ℕ} (d' : DecoSet (E := E) (n := a) (ST := ∅) (SG := SG)) (d : DecoSet (E := E) (n := b) (ST := ∅) (SG := SG)) (w : SG) (x : Sp E a →ₗ[E] Sp E b)
    (M : Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal)) : Prop :=
  ∀ y ∈ d'.1.at w.1, x y ∈ d.1.at w.1 ∧ d.1.be w (x y) = M.mulVec (d'.1.be w y)


open Classical in
def lemU {κ K : Type} [CommRing κ] [Field K] {r n : ℕ} (h : r ≤ n) (l : Lev κ K r) (s : κˣ →* Kˣ)
    (M : Matrix (Fin n) (Fin r) κ) : K :=
  if H : ∃ k : ↥l.H, (∀ i j, M (Fin.castLE h i) j = (k.1 : Matrix (Fin r) (Fin r) κ) i j) ∧
      ∀ (i : Fin n) (j : Fin r), r ≤ i.1 → M i j = 0
  then ((l.lam H.choose : Kˣ) : K) * (((s (Matrix.GeneralLinearGroup.det H.choose.1))⁻¹ : Kˣ) : K)
  else 0


open Classical in
def wmPhi {K : Type} [Field K] {a b : ℕ} (loc : ∀ w : SG, Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal) → K)
    (d' : DecoSet (E := E) (n := a) (ST := ∅) (SG := SG)) (d : DecoSet (E := E) (n := b) (ST := ∅) (SG := SG)) (x : Sp E a →ₗ[E] Sp E b) : K :=
  ∏ w : SG, if h : ∃ M, wmIsRed d' d w x M then loc w h.choose else 0

end Data

section Dist

variable (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (V V' : Type) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

abbrev WmTh : Type :=
  Finset (HeightOneSpectrum (𝓞 E)) → DecoSet (E := E) (n := a) (ST := ∅) (SG := SG) → DecoSet (E := E) (n := b) (ST := ∅) (SG := SG) →
    ((Sp E a →ₗ[E] Sp E b) → K) →ₗ[K] (V →ₗ[K] V')

variable {E K a b SG V V'}


end Dist

section Theta

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


open Classical in
def wmLoc (Ch : Chars X Pr R.m) (P : LevFam X.E X.K R.r Pr.vGs) :
    ∀ w : rowSG Pr sel mu, Matrix (Fin R.nV) (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal) → X.K := fun w =>
  if h : w.1 ∈ Pr.vGs then lemU (r_le_nV R) (P ⟨w.1, h⟩).inv (chiAt Ch ⟨w.1, h⟩ (R.m - 1))⁻¹
  else lemU (r_le_nV R) (⟨⊤, 1⟩ : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K R.r) (resChar (mu : Chr X.F X.E X.K) w.1)


abbrev ThM (P : LevFam X.E X.K R.r Pr.vGs) : Type :=
  WmTh X.E X.K R.r R.nV (rowSG Pr sel mu) (mtGSD W Ch sel mu P R.m).V (wmGSD W sel mu P).V

def wmKer (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (d : (mtGSD W Ch sel mu P R.m).D)
    (d' : (wmGSD W sel mu P).D) : (mtGSD W Ch sel mu P R.m).V →ₗ[X.K] (wmGSD W sel mu P).V :=
  th (rowSG Pr sel mu) d' d (wmPhi (wmLoc sel mu Ch P) d' d)

def GSD.wmCls {K : Type} [Field K] [NumberField K] [StarRing K] (S S' : GSD K) (h : S.Ok) (k : S.D → S'.D → (S.V →ₗ[K] S'.V)) :
    S.EqFun →ₗ[K] (S'.D → S'.V) where
  toFun φ d' := letI := h.fintypeCl
    ∑ c, (((S.toCSD h).wt c : K))⁻¹ • k (S.outSec.rep c) d' ((φ : S.D → S.V) (S.outSec.rep c))
  map_add' φ ψ := by
    funext d'
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext d'
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_comm]

def thetaP (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (h : (mtGSD W Ch sel mu P R.m).Ok) :
    (mtGSD W Ch sel mu P R.m).EqFun →ₗ[X.K] ((wmGSD W sel mu P).D → (wmGSD W sel mu P).V) :=
  GSD.wmCls (mtGSD W Ch sel mu P R.m) (wmGSD W sel mu P) h (wmKer W Ch sel mu P th)

end Theta

section Z

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Z

section NbFun

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]

def nbFun (P : Ideal (𝓞 E)) (i : ℕ) : (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) →ₗ[K] (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) where
  toFun ψ d := ∑ d₁ ∈ d.heckeNb P i, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFun

section Rel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Rel

end Formalism.L2.Col
end
end
