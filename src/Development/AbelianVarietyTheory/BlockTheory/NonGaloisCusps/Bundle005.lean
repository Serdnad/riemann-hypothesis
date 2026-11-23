module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Mathlib.RepresentationTheory.Semisimple
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def IsJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, multV PD ρ τ a = (J.count a : ℤ)

end Local

def blockJumps (t : ℕ) : Multiset ℤ := (Multiset.range t).map (fun k : ℕ => (k : ℤ))

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsBlockSum (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ (g : GE N) (u : Fin R.nV → KK N i),
      e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)

end Glob

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < t then 1 else 0 := by
  have hn : (blockJumps t).Nodup := (Multiset.nodup_range t).map Nat.cast_injective
  have hm : a ∈ blockJumps t ↔ 0 ≤ a ∧ a < t := by
    simp only [blockJumps, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨a.toNat, by omega, by omega⟩
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem hn (hm.2 h)
  · exact Multiset.count_eq_zero.2 (fun h' => h (hm.1 h'))

end GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

section Generic

variable {O Γ : Type} [CommRing O] [Group Γ]

def blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) :
    Γ →* Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O where
  toFun g := Matrix.fromBlocks ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) 0 0
    (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O))
  map_one' := by simp
  map_mul' g h := by
    simp [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]

def repOver (K : Type) [CommRing K] [Algebra O K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Γ →* Matrix n n O) : Representation K Γ (n → K) where
  toFun g := Matrix.toLin' ((M g).map (algebraMap O K))
  map_one' := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem charpoly_blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (g : Γ) :
    (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        ∏ c ∈ Finset.Icc 1 t, (X - C ((χ c g : Oˣ) : O)) := by
  have h : (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O)).charpoly :=
    Matrix.charpoly_fromBlocks_zero₂₁ _ _ _
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_eq_prod_range (fun c => X - C ((χ (c + 1) g : Oˣ) : O)) t,
    Finset.range_eq_Ico, Finset.prod_Ico_add' (fun c => X - C ((χ c g : Oˣ) : O)) 0 t 1]
  rfl

end Generic

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def FrobeniusMatrixCompatible (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → (M σ).charpoly = heckePol N i x w

def IsRx (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  Continuous (fun g => M g) ∧ (repOver (KK N i) M).IsSemisimpleRepresentation ∧ FrobeniusMatrixCompatible N i x M

def sumChi (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    GE N →* Matrix (Fin R.r ⊕ Fin R.t) (Fin R.r ⊕ Fin R.t) (N.O i) :=
  blockSum R.t ρ (N.chi i)

def IsContRep (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)))

def IsRhoAt (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  FrobeniusMatrixCompatible N i π (sumChi N i ρ)

def IsSSSum (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  (repOver (KK N i) (sumChi N i ρ)).IsSemisimpleRepresentation

def IsComplement (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  IsRhoAt N i π ρ ∧ IsSSSum N i ρ ∧ IsContRep N i ρ

def SplitsAs (i : N.Loc) (rπ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] (Fin R.r ⊕ Fin R.t → KK N i), ∀ g u,
    e (repOver (KK N i) ((Units.coeHom _).comp rπ) g u) = repOver (KK N i) (sumChi N i ρ) g (e u)

theorem isRhoAt_iff (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    IsRhoAt N i π ρ ↔ ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) = heckePol N i π w := by
  simp only [IsRhoAt, FrobeniusMatrixCompatible, sumChi, charpoly_blockSum]

theorem isRhoAt_of_splitsAs (i : N.Loc) (π : N.X i) (rπ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : FrobeniusMatrixCompatible N i π ((Units.coeHom _).comp rπ))
    (hs : SplitsAs N i rπ ρ) : IsRhoAt N i π ρ := by
  obtain ⟨e, he⟩ := hs
  intro w hw B σ hB hσ
  rw [← hr w hw B σ hB hσ]
  apply Polynomial.map_injective (algebraMap (N.O i) (KK N i)) (IsFractionRing.injective _ _)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin',
    ← LinearEquiv.charpoly_conj e]
  congr 1
  refine LinearMap.ext fun u => ?_
  have := he σ (e.symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

end
end
