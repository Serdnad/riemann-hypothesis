module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def IsOver (i : ZMod n) (τ : K →ₐ[Qp] LL) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c

def JumpsBounded (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), IsOver W i τ →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))

def phiStar (T : LocLat G Qp LL O) (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def PartA (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiStar W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiStar W T i)

def LocRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL

instance (i : ZMod n) (ζ : LL) : CommRing (LocRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))

instance (i : ZMod n) (ζ : LL) : Algebra (LetA O n) (LocRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := LocRing W i ζ) (W.lev i ζ).toRingHom

abbrev Nloc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  LocRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)

def MemInv (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i

def MemLoc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (z : Nloc W T i ζ),
    (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) =
      (algebraMap (LetA O n) (LocRing W i ζ) (W.Q ^ k)) • z

def PartB (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), MemInv W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → MemLoc W T i ζ y)

variable {W} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
  (E : EtTie W RA RW inclR φR gR πA)

def latAinf (_E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)

def wachAinf (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {w | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ w = inclR a • E.jD T x}

def PartC (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ w ∈ latAinf E T, inclR (E.io W.X) ^ h • w ∈ wachAinf E T) ∧
  (∀ w ∈ wachAinf E T, inclR (E.io W.X) ^ M • w ∈ latAinf E T)

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨Module.finrank_pos.ne'⟩

def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup m

def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ M h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ, JumpsBounded (H.W K s LL hg) T M h →
      PartA (H.W K s LL hg) T M h ∧ PartB (H.W K s LL hg) T ∧
        PartC (F.E K s LL hg).tie T (letterMax K M) (letterMax K h)

end GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LiesOver (W : LocWach PD LL O v n) (τ : K →ₐ[Qp] LL) (i : ZMod n) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c

def JumpsOverLetters (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), LiesOver W τ i →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))

def phiPullLetter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def InLetterAwayQ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i

def PointRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL

instance PointRing.commRing (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    CommRing (PointRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))

instance PointRing.algebra (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    Algebra (LetA O n) (PointRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := PointRing W i ζ) (W.lev i ζ).toRingHom

abbrev CompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  PointRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)

def InCompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (w : CompletedAt W T i ζ),
    (1 : PointRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) = W.Q ^ k • w

def HeightBounds (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiPullLetter W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiPullLetter W T i)

def RootTest (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), InLetterAwayQ W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → InCompletedAt W T i ζ y)

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def latticeAinf (inclR : RA →ₐ[O] RW) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)

def wachAinf (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {z | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ z = inclR a • E.jD T x}

def Sandwich (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ z ∈ latticeAinf inclR T, inclR (E.io W.X) ^ h • z ∈ wachAinf E T) ∧
  (∀ z ∈ wachAinf E T, inclR (E.io W.X) ^ M • z ∈ latticeAinf inclR T)

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact ⟨Module.finrank_pos.ne'⟩

def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (f : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup f

def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ,
      JumpsOverLetters (H.W K s LL h) T Mi hi →
        HeightBounds (H.W K s LL h) T Mi hi ∧
        RootTest (H.W K s LL h) T ∧
        Sandwich (F.E K s LL h).tie T (letterMax K Mi) (letterMax K hi)

end GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

abbrev rk : ℕ := finrank O ↥T.L.T

abbrev letterModule (i : ZMod n) : Module (PowerSeries O) ↥(W.Nl T i) :=
  Module.compHom _ (Pi.constRingHom (ZMod n) (PowerSeries O))

attribute [local instance] letterModule


open Module in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

abbrev LetterBasis (i : ZMod n) : Type := Basis (Fin (rk T)) (PowerSeries O) ↥(W.Nl T i)

def LettersDecompose : Prop := iSupIndep (W.Nl T) ∧ ⨆ i, W.Nl T i = W.N T

def LettersFree : Prop := ∀ i : ZMod n, Nonempty (LetterBasis W T i)

def GlobalBasis : Prop :=
  ∃ b : Basis (Fin (rk T)) (LetA O n) ↥(W.N T),
    LinearIndependent W.EE (fun j => (b j : W.DD T)) ∧
      Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) = ⊤

variable {W T}

variable (W T)

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def IsLaurent (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0

def serMul (f : PowerSeries L) (u : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • u (k - (j : ℤ))


open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_Iic (k - m).toNat).subset ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iic]
  by_contra h
  push Not at h
  exact hj (by rw [hm _ (by omega), smul_zero])


open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one (u : ℤ → M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul (1 : PowerSeries L) u = u := by
  funext k
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

variable (L) in
def serSpan (S : Set (ℤ → M)) : Submodule L (ℤ → M) :=
  Submodule.span L {w | ∃ (f : PowerSeries L) (u : ℤ → M), u ∈ S ∧ IsLaurent u ∧ w = serMul f u}

def shiftSer (a : ℤ) (F : Submodule L M) : Submodule L (ℤ → M) where
  carrier := {u | (∀ k < -a, u k = 0) ∧ ∀ k, u k ∈ F}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => F.zero_mem⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    exact ⟨fun k hk => by simp [hu k hk, hw k hk], fun k => F.add_mem (hu' k) (hw' k)⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun k hk => by simp [hu k hk], fun k => F.smul_mem c (hu' k)⟩

def gradedSer (F : ℤ → Submodule L M) : Submodule L (ℤ → M) := ⨆ a : ℤ, shiftSer a (F a)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Dlet (i : ZMod n) : Submodule LL (T.V ⊗[Qp] B) := DcrisL PD T.ρ (W.emb i)

def FilLet (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] B) :=
  Dlet W T i ⊓
    (FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ').comap
      (ιV PD (LL := LL) (V := T.V))

def toDR (F : Submodule LL (T.V ⊗[Qp] B)) : Submodule LL (T.V ⊗[Qp] BdR) :=
  F.map (ιV PD (LL := LL) (V := T.V))

def Nlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL (Set.range (W.levN T i ζ))

def IsExpansion (i : ZMod n) (ζ : LL) (y : W.DD T) (u : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  IsLaurent u ∧ ∃ (m : ℕ) (hy : W.Q ^ m • y ∈ W.N T),
    serMul (W.lev i ζ (W.Q ^ m)) u = W.levN T i ζ ⟨W.Q ^ m • y, hy⟩

def phiNlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}

variable (PD) in
def phiSer (j : ℕ) (u : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] BdR :=
  fun k => ιV PD (LL := LL) (V := T.V)
    ((((PD.p : LL) ^ j) ^ k) • ((φVB PD (LL := LL) (V := T.V)) ^ j) (u k))


open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.levN_mem_Nlev (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) :
    W.levN T i ζ x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.Nlev W T i ζ := by
  refine Submodule.subset_span ⟨1, W.levN T i ζ x, ⟨x, rfl⟩, ?_,
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one _).symm⟩
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
  exact ⟨m, hm⟩

end Generic

section Statement

variable {l : ℕ} [Fact l.Prime]

def resEmb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IntermediateField.inclusion h.2.2.1)

def LatticeAtLevels (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
        Nlev (H.W K s LL h) T i ζ =
          shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
      (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ →
        phiNlev (H.W K s LL h) T i ζ =
            shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i)) ∧
          Nlev (H.W K s LL h) T i ζ =
            gradedSer fun a =>
              toDR (PD := P.PD K) T (FilLet (H.W K s LL h) T i (resEmb h τ) a)) ∧
      (∀ j : ℕ, 1 ≤ j → IsPrimitiveRoot ζ (l ^ (s + j)) →
        Nlev (H.W K s LL h) T i ζ =
            serSpan ↥LL.1 (phiSer (P.PD K) T j ''
              (serSpan ↥LL.1 (Set.range
                ((C.C K s LL h).tie.levB T (i - (j : ZMod _)) (ζ ^ (l ^ j)))) :
                  Set (ℤ → T.V ⊗[ℚ_[l]] P.R.B))) ∧
          ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h (i - (j : ZMod _)) (ζ ^ (l ^ j)) τ →
            Nlev (H.W K s LL h) T i ζ =
              gradedSer fun a =>
                toDR (PD := P.PD K) T
                  ((FilLet (H.W K s LL h) T (i - (j : ZMod _)) (resEmb h τ) a).map
                    ((φVB (P.PD K) (LL := ↥LL.1) (V := T.V)) ^ j)))

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end
end
