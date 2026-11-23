module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WachLatticeTwists.RamifiedBlockRings.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.WachLatticeTwists.RamifiedBlockRings.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

variable {Y}

variable (Y)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)






end Formalism.MainNotions.LatticeVariant

end
end

section

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one

end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

end Formalism.MainNotions.N.CylinderCountFamily
end
end

section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
  Formalism.MainNotions.N.Inst Formalism.MainNotions.LargeLevelLemmas.Br

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

abbrev blk (R : Ranks) : Fin R.nV → Fin (R.t + 1) := blkG R.r R.t

def repX : GE N →* (N.X i → MatN N i) := MonoidHom.pi fun x => rO N i r x

theorem repX_apply (γ : GE N) (x : N.X i) : repX N r γ x = rO N i r x γ := rfl

def NormAt : Prop :=
  (∀ g a b, blk R a ≠ blk R b → rO N i r π g a b = 0) ∧
  (∀ g (c : Fin R.t), rO N i r π g (Fin.natAdd R.r c) (Fin.natAdd R.r c) =
    ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i)) ∧
  (∀ g (a b : Fin R.r), rO N i r π g (Fin.castAdd R.t a) (Fin.castAdd R.t b) = rhoO N i ρ π g a b)

theorem repX_mem (γ : GE N) : repX N r γ ∈ tSpan (N.T i) (repX N r) := by
  refine ⟨{γ}, fun _ => 1, fun _ => one_mem _, ?_⟩
  simp

theorem e_of_bd (M : MatN N i) (hM : ∀ a b, blk R a ≠ blk R b → M a b = 0)
    (B : Matrix (Fin R.r) (Fin R.r) (N.O i))
    (hB : ∀ a b, M (Fin.castAdd R.t a) (Fin.castAdd R.t b) = B a b) (χ : Fin R.t → N.O i)
    (hχ : ∀ c, M (Fin.natAdd R.r c) (Fin.natAdd R.r c) = χ c) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) ((M.map (toK N i)).mulVec u) =
      ((B.map (toK N i)).mulVec (eG R.r R.t (KK N i) u).1,
        fun c => toK N i (χ c) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec (M.map (toK N i)) (fun a b h => by
    show toK N i (M a b) = 0
    rw [hM a b h, map_zero]) u).trans ?_
  congr 1
  · congr 2
    ext a b
    show toK N i (M (Fin.castAdd R.t a) (Fin.castAdd R.t b)) = toK N i (B a b)
    rw [hB]
  · funext c
    show toK N i (M (Fin.natAdd R.r c) (Fin.natAdd R.r c)) * _ = _
    rw [hχ]

section Mk

variable (g0 : GE N) (eB e₁ X0 : N.X i → MatN N i)

abbrev Pf : N.X i → Polynomial (N.O i) := fun x => blockPoly (eB x) (X0 x)

variable (hfin : Finite (SplitPts R.t (Pf N eB X0))) (π' : SplitPts R.t (Pf N eB X0))

end Mk

theorem blockPoly_eq {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly e a = Matrix.det ((Polynomial.X : Polynomial A) • e.map (Polynomial.C (R := A)) -
      a.map (Polynomial.C (R := A)) + 1 - e.map (Polynomial.C (R := A))) := by
  rw [blockPoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem e_of_diag (β : Fin R.nV → N.O i) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) (((Matrix.diagonal fun a => if blk R a = 0 then 0 else β a : MatN N i).map
        (toK N i)).mulVec u) =
      (0, fun c => toK N i (β (Fin.natAdd R.r c)) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec _ (fun a b h => ?_) u).trans ?_
  · have hab : a ≠ b := fun hab => h (by rw [hab])
    show toK N i (if a = b then (if blk R a = 0 then (0 : N.O i) else β a) else 0) = 0
    rw [if_neg hab, map_zero]
  · congr 1
    · have h0 : ∀ a b : Fin R.r, ((Matrix.diagonal (fun a => if blk R a = 0 then (0 : N.O i) else β a)).map (toK N i)) (Fin.castAdd R.t a) (Fin.castAdd R.t b) = 0 := by
        intro a b
        show toK N i (if Fin.castAdd R.t a = Fin.castAdd R.t b then
          (if blk R (Fin.castAdd R.t a) = 0 then (0 : N.O i) else β (Fin.castAdd R.t a)) else 0) = 0
        have hblk : blk R (Fin.castAdd R.t a) = 0 := by simp [blkG]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos hblk, map_zero]
        · rw [if_neg (fun h => hab (Fin.castAdd_injective _ _ h)), map_zero]
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      exact Finset.sum_eq_zero fun b _ => by
        rw [mul_eq_zero]
        left
        exact h0 a b
    · funext c
      have hblk : blk R (Fin.natAdd R.r c) ≠ 0 := by simp [blkG, Fin.ext_iff]
      show toK N i (if Fin.natAdd R.r c = Fin.natAdd R.r c then
        (if blk R (Fin.natAdd R.r c) = 0 then (0 : N.O i) else β (Fin.natAdd R.r c)) else 0) * _ = _
      rw [if_pos rfl, if_neg hblk]

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  set_option synthInstance.maxHeartbeats 200000 in
    exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

end Formalism.MainNotions.N.PreambleDegrees
end
end

section

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLatticeFreeLocal D.loc HW D.locA F

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachCharacterisationLocal D.loc HW D.locA F

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleLocal D.loc HW D.locA F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem invariant_cocycle_le_gamma_cocycle (W : LocWach PD LL O v n) (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) :
    W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  have e := W.gamK_eq_one h1 h2
  intro x hx
  unfold Formalism.BasicNotions.LocWach.wachCocyclesDelta Formalism.BasicNotions.herrZ1Δ at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  rw [e] at hx1
  exact hx1

def coreResK (W : LocWach PD LL O v n) : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) =
      W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩


variable (PD LL O) in
def coreJumps : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a

end Local

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExtΔ ((HW l).W K s LL h)

def adm19 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreDss ((HW l).W K s LL h)

def adm20 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (_hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l),
    Formalism.MainNotions.LiftingTheory.coreCor ((D.loc l).PD K) ((D.loc l).PD K') ↥LL.1 ↥(OL LL) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1)

def adm21 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ (s = 1 → l ≠ 2 → ((HW l).W K s LL h).ClKNat)

theorem resK_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : coreResK ((HW l).W K s LL h) := by
  intro h1 h2 T w
  exact ((F l).E K s LL h).tie.clK_res (((HW l).W K s LL h).gamK_eq_one h1 h2) T w _ rfl

def adm22 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((D.loc l).PD K) ↥LL.1

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), coreJumps ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  adm1 D HW F ∧ adm2 D HW F ∧ adm3 D HW F Cm ∧ ArchimedeanSignatureMatching D HW F Cm ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F ∧ adm8 D HW F ∧
    adm9 D HW F ∧ adm10 D HW F ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D HW F ∧ adm16 D HW F ∧
    adm17 D HW F ∧ adm18 D HW F ∧ adm19 D HW F ∧ adm20 D HW F ∧ adm21 D HW F ∧ adm22 D HW F ∧ adm23 D HW F

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseB D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseA D HW F

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Conclusion1 D HW F ∧ Conclusion2 D HW F CA CB CK

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) : Prop := admitted D HW F Cm → aux₃ D HW F CA CB CK

end Formalism.MainNotions.CrystallineLiftingBounds
end
end

section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

def PGen (S : Sit) : Set S.G :=
  {g | S.W.resΓ g ∈ Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam))}

variable {l : ℕ} [Fact l.Prime]

instance contAddLL (LL : FinExt l) : ContinuousAdd ↥LL.1 :=
  ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd))⟩

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end
