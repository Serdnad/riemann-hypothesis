module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg)

noncomputable section

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

structure IsPreFamily (x : (Σ k, J k) → Ω) (p : ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O)
    (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
    (RC : Subalgebra O C), IsTestPt p (chartRing O (mseg x) c) RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      ((D c).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

def coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) : AddSubgroup (Fin m → Ω) :=
  ⨅ (q : Cpt ξ) (_ : InChart ξ (mseg y) c q) (_ : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q),
    (L q).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom

def IsFamilyOf (y : (Σ k, J k) → Ω) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) (L L' Lc Lc' : Sg → Lat ξ V)
    (b : ∀ τ, Fin (r τ) → V) (bc : ∀ τ, Fin (s τ) → V) : Prop :=
  ∀ c, mseg y c ≠ 0 → ∀ τ, (D c).lie τ = coordLat O y (L τ) (b τ) c ∧ (D c).W τ = coordLat O y (L' τ) (b τ) c ∧
    (D c).om τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc τ) (bc τ) c) ∧
    (D c).omHT τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc' τ) (bc τ) c)

namespace Fam


omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem mem_coordLat_iff (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) (a : Fin m → Ω) :
    a ∈ coordLat O y L b c ↔ ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) →
      ∑ i, a i • b i ∈ L q := by
  simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]



omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem chartRing_le_regAt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) (h1 : InChart ξ (mseg y) c q)
    (h2 : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h1.2 j
  | algebraMap o => exact h2 o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht





end Fam

end

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure FibreCurve (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) where

  k : Type

  κ : Type
  [fk : Field k]
  [fκ : Field κ]
  [alg : Algebra k κ]
  fg : (⊤ : IntermediateField k κ).FG
  trdeg : Algebra.trdeg k κ = 1

  C : Crv.ACurve κ
  w_pos : ∀ i, 0 < C.w i
  triv : ∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1
  all : ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) → ∃! i, (C.v i).valuationSubring = W

  η : Spec (CommRingCat.of κ) ⟶ X
  η_spec : genPt ξ ⤳ centre η
  η_zero : ValAt ξ η ϖ 0

  z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  z_gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η

attribute [instance] FibreCurve.fk FibreCurve.fκ FibreCurve.alg

def FibreCurve.HasDeg {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (L : Lat ξ Ω) (d : ℤ) : Prop :=
  ∃ (e : Ω) (f : Γ.C.I → Ω) (r : Γ.C.I → Γ.κ), L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e ∧
    (∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f i)) ∧
    (∀ i, r i ≠ 0 ∧ ValAt ξ Γ.η (e / f i) (r i)) ∧ {i | Γ.C.v i (r i) ≠ 1}.Finite ∧
    ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r i))) = d

def NumTrivMod {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ Ω) (ϖ : Ω) : Prop :=
  ∀ Γ : FibreCurve ξ ϖ, Γ.HasDeg L 0

namespace FibreCurve

open ProjectiveLinePlaces

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) {L L' M : Lat ξ Ω} {d d' : ℤ}

theorem generic_centre_specializes (i : Γ.C.I) : centre Γ.η ⤳ centre (Γ.z i) := by
  have := centre_specializes (Γ.z i) (Γ.C.v i).valuationSubring.subtype
  rwa [Γ.z_gen i] at this

theorem z_spec (i : Γ.C.I) : genPt ξ ⤳ centre (Γ.z i) := Γ.η_spec.trans (Γ.generic_centre_specializes i)

theorem exists_val_of_unitAt (i : Γ.C.I) {a : Ω} (ha : unitAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩ a) :
    ∃ t : Γ.κ, ValAt ξ Γ.η a t ∧ Γ.C.v i t = 1 := by
  obtain ⟨t, ht⟩ := valAt_of_unit _ ha
  refine ⟨_, valAt_restrict _ (Γ.z_gen i) Γ.η_spec ht, ?_⟩
  have a1 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) ≤ 1 := t.1.2
  have a2 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) ≤ 1 := (t⁻¹).1.2
  have a3 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) *
      Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := a3.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _

variable {Γ}

variable (Γ)

theorem hasDeg_zero_of_gen {e : Ω} (he : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e)
    (hf : ∀ i, L.IsGenAt ⟨centre (Γ.z i), Γ.z_spec i⟩ e) : Γ.HasDeg L 0 :=
  ⟨e, fun _ => e, fun _ => 1, he, fun i => ⟨_, hf i⟩,
    fun _ => ⟨one_ne_zero, Γ.η_spec, 1, by rw [map_one, div_self he.1], map_one _⟩, by simp, by simp⟩

end FibreCurve

theorem numTrivMod_of_gen {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {e : Ω} (he : ∀ p, L.IsGenAt p e)
    (ϖ : Ω) : NumTrivMod L ϖ := fun Γ => Γ.hasDeg_zero_of_gen (he _) fun _ => he _

end General

namespace FibLine

open ProjectiveLinePlaces Crv.Inhab

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

end Proj

attribute [local instance] MvPolynomial.gradedAlgebra

end FibLine

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptHt (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, φ fun p => σ (w p))

def lineHt (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ptHt (fun k => (A.a k : ℝ)) (fun z => Real.log (A.h z)) L w

def GenUnit (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y), ∃ val : L, val ≠ 0 ∧ HasVal y a u z val

def VertBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (c : ℝ) : Prop :=
  u ≠ 0 ∧ ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * c ∧ (m : Ω) * u ^ q ∈ chartLatNm y a q ∧
    (m : Ω) * u⁻¹ ^ q ∈ chartLatNm y (-a) q

def AmpleQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∃ (m l : ℕ) (s : Fin l → Ω), (∀ i, s i ∈ chartLatNm y (fun k => m * a k - 1) 1) ∧
    ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y),
      ∃ (i : Fin l) (val : L), val ≠ 0 ∧ HasVal y (fun k => m * a k - 1) (s i) z val

end Points

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def rootHt (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, M.ι k) → L) : ℝ :=
  ∑ j, M.coef lam s j * lineHt (M.line t j) L w

def joinOf (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) : (Σ k, joinIdx M.ι R.ι k) → M.Ω :=
  joinVec M.y fun p => i (R.y p)

def joinDeg (M R : RootModel Ψ N) (j : Option (Ψ × Fin N)) : M.K ⊕ R.K → ℤ :=
  Sum.elim (M.line 1 j).a (-(R.line 1 j).a)

structure Close (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c : ℝ) : Prop where
  kA : M.kA = R.kA
  unit : ∀ j, GenUnit (joinOf M R i) (joinDeg M R j) (u j)
  vert : ∀ j, VertBound (joinOf M R i) (joinDeg M R j) (u j) c

def ArchBetween (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Wt Ψ N)
    (s lo hi : ℝ) : Prop :=
  ∀ z ∈ ptsOver ℂ (mCoordIdeal (joinOf M R i)), ∀ val : Option (Ψ × Fin N) → ℂ,
    (∀ j, HasVal (joinOf M R i) (joinDeg M R j) (u j) z (val j)) →
      ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (joinInl M.ι R.ι p)) -
        Real.log ((R.line 1 j).h fun p => z (joinInr M.ι R.ι p)) - Real.log ‖val j‖) ∈ Set.Icc lo hi

def HasRef (T : RootTower Ψ N) (R : T.Comp → RootModel Ψ N) : Prop :=
  ∃ (C s₀ : ℝ), 0 < s₀ ∧ ∀ B : ℕ, 2 ≤ B → ∀ c, ∃ (i : (R c).Ω →+* (T.M B c).Ω) (u : Option (Ψ × Fin N) → (T.M B c).Ω),
    Close (T.M B c) (R c) i u (C * Real.log B) ∧ ∀ (mu : Wt Ψ N) (s : ℝ), Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
      ArchBetween (T.M B c) (R c) i u (scale s) mu s (-(C * Real.log (1 / s)) - C) C

def RefLower (R : RootModel Ψ N) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    -C ≤ rootHt R 1 0 1 L w ∧ ∀ mu : Wt Ψ N, Dominant mu → ‖mu‖ ≤ 2 →
      -(C * Real.log (2 + C + rootHt R 1 0 1 L w)) - C ≤ rootHt R 1 mu 0 L w

def FlatUnit (R : RootModel Ψ N) : Prop :=
  ∀ τ, ∃ (k : ℕ) (u : R.Ω) (c : ℝ), 0 < k ∧ GenUnit R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u ∧
    VertBound R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u c

def FibreInput {j k : ℕ} (R : RootModel Ψ (j + k)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : L →+* L')
      (E : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L') (A : FlagPair E Ψ j k), A.IsOrthFull ∧
      (∀ τ (i : Fin j), |lineHt (R.x 1 (τ, Fin.castAdd k i)) L w - (A.W τ).grDeg i| ≤ C) ∧
      (∀ τ (i : Fin k), |lineHt (R.x 1 (τ, Fin.natAdd j i)) L w + (A.S τ).grDeg i.rev| ≤ C) ∧
      E.slopeMax ≤ ((C * Real.log (2 + C + max (-E.normDegree ⊤) 0) + C : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar.Ht
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOfTest

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem factor {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (ξ' : Spec (CommRingCat.of Ω') ⟶ X) (e : genPt ξ' = genPt ξ) :
    ∃ i : Ω →+* Ω', ξ' = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
  have key : ∀ (x x' : X) (_ : x' = x) (φ : X.presheaf.stalk x ⟶ CommRingCat.of Ω) [IsIso φ]
      (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of Ω'), ∃ i : Ω →+* Ω',
      Spec.map φ' ≫ X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom i) ≫ Spec.map φ ≫ X.fromSpecStalk x := by
    intro x x' e φ _ φ'
    subst e
    refine ⟨(inv φ ≫ φ').hom, ?_⟩
    rw [CommRingCat.ofHom_hom, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h.bij
  obtain ⟨i, hi⟩ := @key _ _ e (Scheme.stalkClosedPointTo ξ) this (Scheme.stalkClosedPointTo ξ')
  refine ⟨i, ?_⟩
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ').symm.trans (hi.trans
    (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem spec_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

section
variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

end

end GlobalTheory.CompanionTheory.Ar.TowerOfTest
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT

structure TorsTower (p : ℕ) {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] where

  Γ : ∀ n, QFGroup O (LevGrp La p n)

  i : ∀ n, (Γ n).G.left ⟶ G.left
  tors : ∀ n, (Γ n).IsTorsionAlong G y (p ^ n) (i n)
  compat : ∀ n (a : La), ((Γ n).pt (lev p n a)).left ≫ i n = ((Γ (n + 1)).pt (lev p (n + 1) (p • a))).left ≫ i (n + 1)

namespace TorsTower

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)

def IsDer {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ)
    (f : LevGrp La p n → O) (w : Module.Dual O L) : Prop :=
  ∃ s : Γ((X.Γ n).G.left, ⊤), (X.Γ n).HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))) ⟶ (X.Γ n).G.left,
      v ≫ (X.Γ n).G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (O ⧸ Ideal.span {((p ^ n : ℕ) : O)})
        (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ X.i n = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)}) (w e))

def Induces (u : G ⟶ G) (φ : La →+ La) : Prop :=
  ∀ n (a : La), ((X.Γ n).pt (lev p n (φ a))).left ≫ X.i n = ((X.Γ n).pt (lev p n a)).left ≫ X.i n ≫ u.left

def PairingRegular (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s : Γ(((X.Γ n).G ⊗ (X.Γ n).G).left, ⊤), ∀ a b : La,
    valAt (lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))).left ⊤ le_top s =
      algebraMap O (FractionRing O) ((ζ n ^ B a b : Oˣ) : O)

end TorsTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

structure RootFlat {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (τ : Ψ) where
  F : Type
  [field : Field F]
  [numberField : NumberField F]
  φ : F →+* M.Ω
  overInt : OverInt M.y φ
  A : HermLine M.ι
  A_smooth : IsSmoothHerm A
  S : FlatHerm M.y φ A
  deg : ∑ i, M.xdeg (τ, i) = A.a
  v : ℝ → ((Σ k, M.ι k) → ℂ) → ℝ
  v_inv : ∀ t (c : M.K → ℂ) z, (∀ k, c k ≠ 0) → v t (fun p => c p.1 * z p) = v t z
  v_smooth : ∀ t, SmoothFn (v t)
  prod : ∀ t, 0 < t → ∀ z ∈ mcPts M.P, ∏ i, (M.x t (τ, i)).h z = A.h z * Real.exp (-v t z)
  small : ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N →
    Tendsto (fun t => ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (v t))
      (𝓝[>] 0) (𝓝 0)

attribute [instance] RootFlat.field RootFlat.numberField

def RootFlat.ht {Ψ : Type} [Fintype Ψ] {N : ℕ} {M : RootModel Ψ N} {τ : Ψ} (R : RootFlat M τ) : ℝ := R.S.ht

def NearRecord (N : ℕ) (bad : Finset ℕ) (rd Lval h : ℝ) : Prop :=
  ∃ (hrec : ℝ) (d v : ℕ → ℝ), |hrec| ≤ N * (3 / 2 * Real.log rd + |Lval| / 2) ∧ h = hrec + ∑ p ∈ bad, d p ∧
    (∀ p ∈ bad, 0 ≤ v p ∧ |d p| ≤ (N / ((p : ℝ) - 1) + N * v p) * Real.log p) ∧
    ∑ p ∈ bad, v p * Real.log p ≤ Real.log rd

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem secVal_one {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) : secVal x W h 1 = 1 := by
  simp [secVal]

end GlobalTheory.CompanionTheory.Ar.HtLatCheck
end
end
