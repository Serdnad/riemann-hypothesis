module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

end CrystallineSemistableComparison
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def limMod {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g)) :
    GMod R Γ where
  N j := (S j).lim
  act j g := (act j g).lim.toAddMonoidHom

def limAlg {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g))
    (one : ∀ n, (S 0).M n) (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n) : GAlg R Γ where
  toGMod := limMod S act
  one x := ∀ n, (show (S 0).lim from x).1 n = one n
  cup {i j} x y z := ∀ n, (show (S (i + j)).lim from z).1 n = cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Model

abbrev MS (M : Model l K) (j : ℕ) : Sys.{1} (Acris l) := MSys M.P j

def galS (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) : Sys.Hom (M.MS j) (M.MS j) (ACris.galCris σ) where
  f n := M.galMH σ n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_twId σ _).red_acr n.le_succ _))

def phiS (M : Model l K) (j : ℕ) : Sys.Hom (M.MS j) (M.MS j) (ACris.phi (K := ℂ_[l]) (p := l)) where
  f n := M.phiMH n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_frob _).red_acr n.le_succ _))

def pullS {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) : Sys.Hom (N.MS j) (M.MS j) (RingHom.id _) where
  f n := pullMH u hu n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def MA (M : Model l K) : GAlg (Acris l) K.fixingSubgroup :=
  limAlg M.MS (σ := fun g => ACris.galCris (IntermediateField.fixingSubgroupEquiv K g))
    (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) (fun n => CH.oneH (AcrEl M.P n))
    (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y)

end Model

end CrystallineSemistableComparison
end
end
