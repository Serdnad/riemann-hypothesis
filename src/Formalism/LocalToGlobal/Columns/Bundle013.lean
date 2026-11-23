module

public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.LocalToGlobal.Columns.Bundle011
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle001
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
import Mathlib.Tactic.Basify
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
public import Formalism.LocalToGlobal.Columns.Bundle006
public import Formalism.LocalToGlobal.Columns.Bundle007
import Formalism.LocalToGlobal.GlobalTheory.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory MvPolynomial

theorem minkowskiBound_holds : MinkowskiBound := card_dvd_minkowskiNumber

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Stab

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

section Loc

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Loc

section C2

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

end C2

section AtT

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtT

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG (E := X.E) (n := n) (SG := SG)) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d₁)
  set g : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

section Poly

variable {L : Type} [Field L]

end Poly

section HV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end HV

section FromRel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end FromRel

section Inh

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Inh

section Fub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Fub

section Rev

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Rev

section PhiLem

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {a b : ℕ}


end PhiLem

section Gauss

variable {L : Type} [Field L]

end Gauss

section Count

variable (E : Type) [Field E] [NumberField E] [StarRing E]


end Count

section ClassRel

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ClassRel

section RelOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RelOf

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Main

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def pairAt (v : InfinitePlace K) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (S.bV.repr x i)) * v.embedding (S.gramV i j) * v.embedding (S.bV.repr y j)

def ipAt (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

abbrev hDim (h : S.Ok) : ℕ := (S.toCSD h).dim

def hB (h : S.Ok) : Basis (Fin (S.hDim h)) K S.EqFun := (S.toCSD h).basis.map (S.res h).symm

abbrev hGram (h : S.Ok) : Matrix (Fin (S.hDim h)) (Fin (S.hDim h)) K := (S.toCSD h).H

def PosH (h : S.Ok) : Prop := ∀ v : InfinitePlace K, ((S.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K where
  V := S.EqFun
  ι := Fin (S.hDim h)
  b := S.hB h
  X := stdFrame (S.hGram h)
  L := L

abbrev hCoord (h : S.Ok) : S.EqFun ≃ₗ[K] (Fin (S.hDim h) → K) := S.coordOf h S.outSec

def toHc (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K :=
  toHLat (stdFrame (S.hGram h)) (L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def subZ (h : S.Ok) (U : Submodule K S.EqFun) : Submodule K (Fin (S.hDim h) → K) :=
  U.map (S.hCoord h).toLinearMap

def subEq (h : S.Ok) (U : Submodule K S.EqFun) : U ≃ₗ[K] S.subZ h U := (S.hCoord h).submoduleMap U

abbrev subD (h : S.Ok) (U : Submodule K S.EqFun) : ℕ := subDim (S.subZ h U)

def subB (h : S.Ok) (U : Submodule K S.EqFun) : Basis (Fin (S.subD h U)) K U :=
  (subBasis (S.subZ h U)).map (S.subEq h U).symm

def subMat (h : S.Ok) (U : Submodule K S.EqFun) : Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) K :=
  subE (S.subZ h U)

@[reducible] def subH (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (S.subD h U)
  b := S.subB h U
  X := restrFrame (S.subMat h U) (S.hGram h)
  L := L

end GSD

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

@[reducible] def latH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColL W Ch u j)

@[reducible] def Mu0H (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).toH (colOk W Ch hX u 0) (MfL W Ch u)

@[reducible] def MramH (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).subH (colOk W Ch hX u 0) (MramV W Ch u) (MramL W Ch u)

def ramInclH (u : Pr.Word) : (MramH W Ch hX u).V →ₗ[X.K] (Mu0H W Ch hX u).V := ramIncl W Ch u

end Cols

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

@[reducible] def MtildeH (P : LevFam X.E X.K R.r Pr.vGs) : HLat X.K :=
  (mtildeGSD W Ch sel mu P).toH (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)

end Rows

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_asAlgebraHom_eq (a : MonoidAlgebra K A) : ρ.asAlgebraHom a = ∑ t : A, a.coeff t • ρ t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum_fintype]

theorem rf_coord_act (t : A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ t φ) = ((S.toCSD h).actMat (S.repCSD h ρ) t).mulVec (S.coordOf h S.outSec φ) := by
  have c : ∀ x, S.coordOf h S.outSec x = (S.toCSD h).basis.equivFun (S.res h x) := fun x => rfl
  have e1 : (S.repCSD h ρ) t (S.res h φ) = S.res h (ρ t φ) := by
    show (S.res h) (ρ t ((S.res h).symm (S.res h φ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [c, c]
  unfold CSD.actMat
  simp only [Basis.equivFun_apply]
  rw [LinearMap.toMatrix_mulVec_repr, e1]

theorem rf_coord_ga (a : MonoidAlgebra K A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ.asAlgebraHom a φ) =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVec (S.coordOf h S.outSec φ) := by

  have hsum : ∀ {m : ℕ} (M : A → Matrix (Fin m) (Fin m) K) (c : A → K) (v : Fin m → K),
      (∑ t, c t • M t).mulVec v = ∑ t, c t • (M t).mulVec v := by
    intro m M c v

    rw [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]

  rw [rf_asAlgebraHom_eq, LinearMap.sum_apply, map_sum]
  unfold CSD.gaMat
  rw [hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, map_smul, rf_coord_act]

theorem rf_range_ga (a : MonoidAlgebra K A) :
    (LinearMap.range (ρ.asAlgebraHom a)).map (S.coordOf h S.outSec).toLinearMap =
      LinearMap.range ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin := by
  have e : (S.coordOf h S.outSec).toLinearMap ∘ₗ ρ.asAlgebraHom a =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin ∘ₗ (S.coordOf h S.outSec).toLinearMap := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact rf_coord_ga S h ρ a φ
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

private theorem range_subE_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (Z : Submodule K (Fin n → K)) :
    LinearMap.range (subE Z).mulVecLin = Z := by
  rw [Matrix.range_mulVecLin]
  have e : (subE Z).col = ⇑Z.subtype ∘ ⇑(subBasis Z) := by
    funext j i
    rfl
  rw [e, Set.range_comp, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem invariantSubspace_coords_X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : (mtildeKGSD W Ch sel mu).Ok) :
    (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap =
      LinearMap.range ((V0C W Ch sel mu h Xg P).E).mulVecLin := by
  unfold V0X
  rw [rf_range_ga]
  exact (range_subE_lemma _).symm

end Rows

section LvlPart

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_mem_lvlPart_iff (P : Subgroup A) (ψ : P →* Kˣ) (φ : S.EqFun) :
    S.coordOf h S.outSec φ ∈ (S.toCSD h).lvlPart (S.repCSD h ρ) P ψ ↔
      ∀ a : P, ρ (a : A) φ = ((ψ a : Kˣ) : K) • φ := by
  show (∀ a : P, ((S.toCSD h).actMat (S.repCSD h ρ) (a : A)).mulVec (S.coordOf h S.outSec φ) =
      ((ψ a : Kˣ) : K) • S.coordOf h S.outSec φ) ↔ _
  refine forall_congr' (fun a => ?_)
  rw [← rf_coord_act, ← map_smul]
  exact (S.coordOf h S.outSec).injective.eq_iff

end LvlPart

section RowsLvl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_lvlPartX_iff (h : (mtildeKGSD W Ch sel mu).Ok) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ ∈
        (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr ↔
      φ.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine Iff.trans ?_ (mem_MtildeV_iff W Ch sel mu P φ.1).symm
  exact (rf_mem_lvlPart_iff _ h (g0HatRepEqFunX W Ch sel mu) P.grp P.chr φ).trans ⟨fun H => ⟨φ.2, H⟩, fun ⟨_, H⟩ => H⟩

end RowsLvl

end Formalism.L2.Col
end
end
