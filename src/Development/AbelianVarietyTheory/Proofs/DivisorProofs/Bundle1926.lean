module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IdemIsotropic

open Matrix Formalism.UG

variable {D : D7}

theorem hT_eq_hform (V : HSp D) (x y : V.V) :
    V.hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (V.frame.repr x) (V.frame.repr y) := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hform,
  HSpace.gram, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show _ = star _ * _ * _
  rw [starRingEnd_apply]
  ring

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M N : Matrix n n A) (a b : n → A) :
    hform σ J (M *ᵥ a) (N *ᵥ b) = hform σ (cT σ M * J * N) a b := by
  have h2 : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, h2, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, cT, Matrix.mul_assoc]

theorem hform_zero {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (a b : n → A) :
    hform σ (0 : Matrix n n A) a b = 0 := by
  simp [hform]

theorem cT_sub' {A : Type} [CommRing A] {n : Type} (σ : A →+* A) (M N : Matrix n n A) :
    cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem hT_toLin (V : HSp D) (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V) :
    V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
      hform (D.sp.cm.sig : D.host.E →+* D.host.E) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N)
        (V.frame.repr a) (V.frame.repr b) := by
  rw [hT_eq_hform, Matrix.repr_toLin, Matrix.repr_toLin, hform_mulVec]

theorem gram_herm (V : HSp D) : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  show star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j)
  exact V.herm.eq (V.frame j) (V.frame i)

theorem idem_isotropic_pair : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  intro D V γ ε hmem hidem hne hiso
  set σ := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJdef
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 (GlobalTheory.Mem.Vol.hspace_gram_det_ne_zero V)
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  have cancel : ∀ A B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, J * A = J * B → A = B := by
    intro A B h
    rw [← Matrix.one_mul A, ← Matrix.one_mul B, ← hJJ', Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  set ε' := J⁻¹ * cT σ ε * J with hε'
  have hR : J * ε' = cT σ ε * J := by
    rw [hε', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  clear_value ε'
  have hTL : ∀ (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V),
      V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
        hform σ (cT σ M * J * N) (V.frame.repr a) (V.frame.repr b) := hT_toLin V
  have hσσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have cTcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσσ]
  have herm : cT σ J = J := gram_herm V
  have hR' : cT σ ε' * J = J * ε := by
    have h := congrArg (cT σ) hR
    rw [cT_mul, cT_mul, herm, cTcT] at h
    exact h
  have h0 : ε' * ε = 0 := cancel _ _ (by rw [← Matrix.mul_assoc, hR, hiso, Matrix.mul_zero])
  set g := (γ.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hg
  set gi := ((γ.1⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hgi
  have hγ : cT σ g * J * g = J := γ.2
  have hggi : g * gi = 1 := Units.mul_inv γ.1
  have hgig : gi * g = 1 := Units.inv_mul γ.1
  have hmem' : ε ∈ Algebra.adjoin D.host.E {g} := hmem
  have hJg : J * g = cT σ gi * J := by
    calc J * g = cT σ (g * gi) * J * g := by rw [hggi, cT_one, Matrix.one_mul]
      _ = cT σ gi * (cT σ g * J * g) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ gi * J := by rw [hγ]
  have hεgi : Commute gi ε :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (by rw [Commute, SemiconjBy, hgig, hggi])
  have hε'g : ε' * g = g * ε' := cancel _ _ (by
    rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hJg, ← Matrix.mul_assoc J g, hJg, Matrix.mul_assoc, hR,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, ← cT_mul, hεgi.eq])
  have hcomm : Commute ε' ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' hε'g
  have hgε : Commute g ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (Commute.refl g)
  have h1 : ε * ε' = 0 := by rw [← hcomm.eq, h0]
  have mA : cT σ (1 - ε - ε') * J * ε = 0 := by
    rw [cT_sub', cT_sub', cT_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, hiso, hR', Matrix.mul_assoc, hidem, sub_zero, sub_self]
  have mB : cT σ ε' * J * (1 - ε - ε') = 0 := by
    rw [hR', Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
      hidem, h1, Matrix.mul_zero, sub_self, sub_zero]
  have mC : cT σ ε' * J * ε' = 0 := by rw [hR', Matrix.mul_assoc, h1, Matrix.mul_zero]
  have split : ∀ v : V.V, v = Matrix.toLin V.frame V.frame ε v + Matrix.toLin V.frame V.frame ε' v +
      Matrix.toLin V.frame V.frame (1 - ε - ε') v := by
    intro v
    simp only [map_sub, Matrix.toLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have mem_perp : ∀ (W : Submodule D.host.E V.V) (y : V.V),
      y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W ↔ ∀ w ∈ W, V.hT w y = 0 := by
    intro W y
    simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker]
  have ratAct_eq : ∀ x, GlobalTheory.Cusp.ratAct D.sp.cm V γ x = Matrix.toLin V.frame V.frame g x := fun _ => rfl
  refine ⟨LinearMap.range (Matrix.toLin V.frame V.frame ε), LinearMap.range (Matrix.toLin V.frame V.frame ε'),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [LinearMap.range_eq_bot] at h
    exact hne ((Matrix.toLin V.frame V.frame).map_eq_zero_iff.1 h)
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, hiso, hform_zero]
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, mC, hform_zero]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hgε.eq]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hε'g]
  · rintro _ ⟨a, rfl⟩ hy
    refine V.nondeg.2 _ fun v => ?_
    rw [split v, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hTL ε ε, hiso, hform_zero,
      hTL (1 - ε - ε') ε, mA, hform_zero, zero_add, add_zero]
    exact hy _ ⟨v, rfl⟩
  · rintro _ ⟨b, rfl⟩ hx
    refine V.nondeg.1 _ fun v => ?_
    have e1 : V.hT (Matrix.toLin V.frame V.frame ε' b) v =
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) := by
      conv_lhs => rw [split v]
      simp only [map_add (f := _)]
    have e2 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) = 0 := by
      rw [hTL, mC, hform_zero]
    have e3 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) = 0 := by
      rw [hTL, mB, hform_zero]
    have e4 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) = 0 := hx _ ⟨v, rfl⟩
    linear_combination e1 + e2 + e3 + e4

end GlobalTheory.IdemIsotropic
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSmallDict

def IsRootOne (ζ : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def IsAlgUnit (ζ : ℂ) : Prop :=
  ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1

variable {D : D7}

def IsStdLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i

def unitPt (S T : HSp D) (a : Formalism.L2.Theta.AE D) (o : ℕ) : WO S T := fun i j => if i.1 = o + j.1 then a else 0

def cosetFn {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T) : WO S T → ℂ := fun y =>
  if IsHalf a y ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - x i j)) then 1 else 0

def modul (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : Ideal (𝓞 D.host.E) :=
  ∏ w ∈ P, w.asIdeal ^ c w

def GoodIdem (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  IsIdemSum e P ∧ ∀ w ∈ P, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

theorem IsRootOne.one : IsRootOne 1 := ⟨1, one_pos, one_pow 1⟩

theorem IsRootOne.mul {a b : ℂ} (ha : IsRootOne a) (hb : IsRootOne b) : IsRootOne (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨n, hn, h'⟩ := hb
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, pow_mul, h, mul_comm m n, pow_mul, h', one_pow, one_pow, one_mul]⟩

theorem IsRootOne.ne_zero {a : ℂ} (ha : IsRootOne a) : a ≠ 0 := by
  obtain ⟨m, hm, h⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem IsRootOne.isAlgUnit {a : ℂ} (ha : IsRootOne a) : IsAlgUnit a := by
  have h0 := ha.ne_zero
  obtain ⟨m, hm, h⟩ := ha
  have hq : a ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hm (by rw [h]; exact isAlgebraic_one))
  refine ⟨h0, hq, fun p _ lam => ?_⟩
  have h1 : (⟨a, hq⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have h2 : ‖lam ⟨a, hq⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  unfold lamC
  rw [dite_eq_left hq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2

theorem IsAlgUnit.mul {a b : ℂ} (ha : IsAlgUnit a) (hb : IsAlgUnit b) : IsAlgUnit (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, Qbar.mul_mem ha.2.1 hb.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam ha.2.1 hb.2.1, norm_mul, ha.2.2 p lam, hb.2.2 p lam, one_mul]⟩

end GlobalTheory.BotSmallDict

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RaynaudAxis

theorem cubN_mul_pow {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (n : ℕ) :
    cubN θ n 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ n = t (a ^ n * b) * t 1 * (t (a ^ n))⁻¹ * (t b)⁻¹ := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e := h (a ^ n) a b
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ, pow_succ]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    linear_combination (norm := abel) e' + ih'

theorem cubN_of_torsion {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (N : ℕ) (ha : a ^ N = 1) :
    cubN θ N 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ N = 1 := by
  rw [cubN_mul_pow t θ h, ha, _root_.one_mul, mul_inv_cancel_right, mul_inv_cancel]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

def tV {L : RigLB G} (i : H ⟶ G) (τ : LB.Gen (L.L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => i.left) (ε := fun _ => 1) τ x.left z J

theorem prod_tt (i : H ⟶ G) {Y : Over S} (p : Y ⟶ H) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k : PUnit, h ((fun _ : PUnit => p.left ≫ i.left) k) ^ ((fun _ : PUnit => (1 : ℤ)) k) = h (p ≫ i).left := by
  rw [Fintype.prod_unique, zpow_one]; rfl

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

theorem cub_tV (hG : GlobalFnsSt) (hA : IsAbelianScheme H) (i : H ⟶ G) [IsMonHom i] {L : RigLB G}
    (c : CubicalStr G L) (τ : LB.Gen (L.L.pull i.left)) (hτ : τ.IsGen) (T : Over S) (x y u : T ⟶ H) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * tV i τ z J (x * y) * tV i τ z J (x * u) * tV i τ z J (y * u) *
        tV i τ z J 1 = tV i τ z J (x * y * u) * tV i τ z J x * tV i τ z J y * tV i τ z J u := by
  haveI := hA.comm
  have h3 := surjective_cube hG hA
  let a := x3 H 0
  let b := x3 H 1
  let d := x3 H 2
  let tt := fun p : G3 H ⟶ H => LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gt : ∀ p, (tt p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hτ _
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vt : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (tt p) σ.left z J = tV i τ z J (σ ≫ p) := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu
    (tt (a * b))) (tt (a * d))) (tt (b * d))) (tt 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (tt (a * b * d)) (tt a)) (tt b))
    (tt d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a ≫ i) (σ ≫ b ≫ i) (σ ≫ d ≫ i) * tV i τ z J (σ ≫ (a * b)) *
        tV i τ z J (σ ≫ (a * d)) * tV i τ z J (σ ≫ (b * d)) * tV i τ z J (σ ≫ 1) ∧
      val t₂ σ.left z J = tV i τ z J (σ ≫ (a * b * d)) * tV i τ z J (σ ≫ a) * tV i τ z J (σ ≫ b) *
        tV i τ z J (σ ≫ d) := fun σ z J hJ => by
    constructor
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt σ hJ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
  let e : 𝟙_ (Over S) ⟶ G3 H := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 H := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' L.isLB (fun V _ k => ?_) (G3 H).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gt _)) (gt _)) (gt _)) (gt _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gt _)
        (gt _)) (gt _)) (gt _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
        (prod_tt i (a * b * d) k) (prod_tt i a k)) (prod_tt i b k)) (prod_tt i d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
          (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k) (prod_tt i (a * b) k)) (prod_tt i (a * d) k))
          (prod_tt i (b * d) k)) (prod_tt i 1 k)).symm)
      simp only [MonObj.mul_comp, MonObj.one_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      have C := isCub_cubV c (T := 𝟙_ (Over S)) hI
      simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, e₀, e₁, e₂, MonObj.one_comp, _root_.mul_one]
      rw [C.face, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂] at this
  exact this

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis

theorem cubWeil_one_of_triv_pull : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H]
    (i : H ⟶ G), IsAbelianScheme H → IsMonHom i → ∀ (L : RigLB G) (c : CubicalStr G L), Triv (L.L.pull i.left) →
    ∀ (N : ℕ) (T : Over S) (a b : T ⟶ H), a ^ N = 1 → b ^ N = 1 → CubWeil c N (a ≫ i) (b ≫ i) 1 := by
  intro S G H _ _ _ i hA hi L c ⟨τ, hτ⟩ N T a b ha hb
  haveI := hA.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine ⟨by rw [← MonObj.pow_comp, ha, MonObj.one_comp], by rw [← MonObj.pow_comp, hb, MonObj.one_comp],
    fun z J hJ => ?_⟩
  let θ : (T ⟶ H) → (T ⟶ H) → (T ⟶ H) → (T.left.presheaf.stalk z)ˣ :=
    fun p q w => cubV c z J (p ≫ i) (q ≫ i) (w ≫ i)
  have h := cub_tV hG hA i c τ hτ T (z := z) (J := J) (hJ := hJ)
  have tr : ∀ p q : T ⟶ H, cubN (cubV c z J) N 1 (p ≫ i) (q ≫ i) = cubN θ N 1 p q := fun p q =>
    Finset.prod_congr rfl fun k _ => by
      simp only [θ, _root_.one_mul, MonObj.pow_comp]
  have e₁ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) a b N ha
  have e₂ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) b a N hb
  rw [mul_comm b a, mul_right_comm _ (tV i τ z J b)⁻¹] at e₂
  rw [map_one, _root_.one_mul, tr, tr]
  exact mul_right_cancel (e₁.trans e₂.symm)

end GlobalTheory.RaynaudAxis
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
open Matrix GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UAut

theorem isRealLine_oneP (D : D7) (θ : InfF D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) :
    GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  obtain ⟨-, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hZ : Xᴴ * V.gram.map (embOverOf D τ).1 + V.gram.map (embOverOf D τ).1 * X = 0 := hX
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine (isCMExt_host D) (h2 V) (embOverOf D τ) hZ
  refine ⟨placeOf D τ, embOverOf D τ, X, hZ, fun t => ⟨_, ?_, hγ t⟩⟩
  rw [oneP, ← hγ t, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]

end GlobalTheory.UAut
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
end
