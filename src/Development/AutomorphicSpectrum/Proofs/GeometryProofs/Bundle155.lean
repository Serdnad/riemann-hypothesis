module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle039
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartFrac

theorem exists_eq_div_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  intro X Ω _ ξ κ x h c hc a
  have hchart : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc, fun c' => TieArith.mem_regAt_genCpt ξ h.gen _⟩
  obtain ⟨t, ht, hu, hta⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c (TieArith.genCpt ξ) hchart a).mp
    (TieArith.mem_regAt_genCpt ξ h.gen a)
  exact ⟨t * a, hta, t, ht, hu.1, (mul_div_cancel_left₀ a hu.1).symm⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrac
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusLie

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {R : Type} [CommRing R]

def pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S} {a' : Sp A' ⟶ S}
    (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) : Over.mk a' ⟶ splitTorus S X :=
  Over.homMk (spMap g ≫ t.left) (by
    have h1 := Over.w t
    simp only [Over.mk_hom] at h1 ⊢
    rw [Category.assoc, h1, h])

theorem charVal_pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S}
    {a' : Sp A' ⟶ S} (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (pullPt g h t) χ = g (charVal t χ) := by
  subst h
  exact (GlobalTheory.T.charVal_multiplicative S X A _).2.2.2.2.2 A' g t _ rfl χ

def wOf (δ : X →+ R) : Multiplicative X →* DualNumber R where
  toFun χ := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]

abbrev evZ (R : Type) [CommRing R] : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

theorem base_ev (x : Sp R ⟶ S) :
    x = spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (evZ R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]; simp
  rw [← Category.assoc, this, Category.id_comp]

theorem isTanAt_iff (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) :
    IsTanAt (splitTorus S X) x v ↔ ∀ χ, (charVal v χ).fst = 1 := by
  have hT := GlobalTheory.T.charVal_multiplicative S X
  constructor
  · intro hv χ
    have e : pullPt (evZ R) (base_ev x) v = 1 := Over.OverMorphism.ext hv
    have := charVal_pullPt (evZ R) (base_ev x) v χ
    rw [e, (hT R x).2.2.1 χ] at this
    exact this.symm
  · intro hv
    have e : pullPt (evZ R) (base_ev x) v = 1 := by
      refine (hT R x).1 _ _ fun χ => ?_
      rw [charVal_pullPt, (hT R x).2.2.1 χ]
      exact hv χ
    exact congrArg (fun t => t.left) e

def ptOf (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose

theorem charVal_ptOf (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (ptOf x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose_spec χ

theorem ptOf_ext (x : Sp R ⟶ S) (v v' : epsAt x ⟶ splitTorus S X) (h : ∀ χ, charVal v χ = charVal v' χ) : v = v' :=
  (GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).1 v v' h

theorem epsMul_comp_base (c : R) (x : Sp R ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
      spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
      ext r <;> simp [epsMul]
    rw [this]
  rw [← Category.assoc, this]

def deltaOf (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) (hv : ∀ χ, (charVal v χ).fst = 1) : X →+ R :=
  AddMonoidHom.mk' (fun χ => (charVal v χ).snd) (fun χ χ' => by
    have := ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.2.2.1 v).2 χ χ'
    simp [this, TrivSqZeroExt.snd_mul, hv, add_comm])

theorem exists_lieModel_splitTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R]
    (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  intro S X _ R _ x
  refine ⟨{ pt := ptOf x, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun δ χ => charVal_ptOf x δ χ⟩
  · intro δ
    refine (isTanAt_iff x _).2 fun χ => ?_
    rw [charVal_ptOf]; simp
  · intro δ δ' h
    ext χ
    have := congrArg TrivSqZeroExt.snd
      ((charVal_ptOf x δ χ).symm.trans ((congrArg (fun t => charVal t χ) h).trans (charVal_ptOf x δ' χ)))
    simpa using this
  · intro v hv
    have hv' := (isTanAt_iff x v).1 hv
    refine ⟨deltaOf x v hv', ptOf_ext x _ _ fun χ => ?_⟩
    rw [charVal_ptOf]
    ext
    · simp [hv']
    · simp [deltaOf]
  · intro δ δ'
    refine ptOf_ext x _ _ fun χ => ?_
    rw [(GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.1, charVal_ptOf, charVal_ptOf, charVal_ptOf]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]
  · intro c δ
    have e : ptOf x (c • δ) = pullPt (epsMul c) (epsMul_comp_base c x) (ptOf x δ) := by
      refine ptOf_ext x _ _ fun χ => ?_
      rw [charVal_pullPt, charVal_ptOf, charVal_ptOf]
      ext <;> simp [epsMul, mul_comm]
    exact congrArg (fun t => t.left) e

end GlobalTheory.CompanionTheory.Ar.TorusLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coords_join_blocks : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) → CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k => (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | exact GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | (intros; apply GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.KillsAdic

theorem ext_of_quotients {A : Type} [CommRing A] {Y Z : Scheme.{0}} {f g : Sp A ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) {N : Type} (I : N → Ideal A) (hI : ∀ x : A, (∀ n, x ∈ I n) → x = 0)
    (hU : ∀ n, spMap (Ideal.Quotient.mk (I n)) ≫ f = spMap (Ideal.Quotient.mk (I n)) ≫ g) : f = g :=
  _root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_comp {A A' : Type} [CommRing A] [CommRing A'] {a : Sp A ⟶ S} {a' : Sp A' ⟶ S} (h : A →+* A')
    (e : spMap h ≫ a = a') (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal ((Over.homMk (spMap h) e : Over.mk a' ⟶ Over.mk a) ≫ t) χ = h (charVal t χ) := by
  subst e
  exact (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 A' h t _ (by simp) χ

theorem exists_factor {M : Type} [CommMonoid M] (Y : AddSubgroup X) (f : X → M) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hY : ∀ y ∈ Y, f y = 1) :
    ∃ v : Multiplicative (X ⧸ Y) →* M, ∀ χ : X, v (Multiplicative.ofAdd (χ : X ⧸ Y)) = f χ := by
  have key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x' := by
    intro x x' e
    have hm : -x + x' ∈ Y := QuotientAddGroup.eq.1 e
    have : x' = x + (-x + x') := by abel
    rw [this, hadd, hY _ hm, _root_.mul_one]
  refine ⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q))
            map_one' := ?_
            map_mul' := ?_ }, fun χ => ?_⟩
  · rw [← h0]
    exact key _ _ (by simp)
  · intro p q
    rw [← hadd]
    exact key _ _ (by simp)
  · exact key _ _ (by simp)

theorem comp_one_over {T T' M : Over S} [GrpObj M] (f : T' ⟶ T) : f ≫ (1 : T ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem universal_one {G : Over S} [GrpObj G] [IsSeparated G.hom] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (hk : ∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b))
    (t₀ : Over.mk (spMap (algebraMap R (AddMonoidAlgebra R (X ⧸ Y))) ≫ b) ⟶ splitTorus S X)
    (ht₀ : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1) : t₀ ≫ u = 1 := by
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y)) := fun n =>
    Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))
  have hI : ∀ x, (∀ n, x ∈ I n) → x = 0 := fun x hx =>
    GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n =>
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)
  refine Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)
  · rw [Over.w, Over.w]
  · let J := IsLocalRing.maximalIdeal R ^ (n + 1)
    let gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n :=
      Ideal.quotientMap (I n) c Ideal.le_comap_map
    have e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b := by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    let m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b) :=
      Over.homMk (spMap (Ideal.Quotient.mk (I n))) e
    have hone := hk n _ gn (m ≫ t₀) (fun y hy => by
      rw [charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]
      exact map_one _)
    have h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G) := by
      exact (Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)
    exact congrArg (fun w => w.left) h4

theorem killsOver_of_forall_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  intro S G _ _ X _ u Y R _ _ _ b hk A _ g t ht
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y) :=
    (AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
  obtain ⟨t₀, ht₀⟩ := (GlobalTheory.T.charVal_multiplicative S X _ (spMap c ≫ b)).2.2.2.2.1 w₀
  have ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1 := fun χ => ht₀ χ
  have hone := universal_one u Y b hk t₀ ht₀'
  have hpts := (GlobalTheory.T.charVal_multiplicative S X A (spMap g ≫ b))
  obtain ⟨v, hv⟩ := exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht
  let h : AddMonoidAlgebra R (X ⧸ Y) →+* A :=
    AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)
  have hc : h.comp c = g := by
    ext r
    simp [h, c]
  have e : spMap h ≫ spMap c ≫ b = spMap g ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b) := Over.homMk (spMap h) e
  have htm : t = m ≫ t₀ := hpts.1 _ _ fun χ => by
    rw [charVal_comp, ht₀']
    simp [h, AddMonoidAlgebra.liftNCRingHom_single, hv]
  rw [htm, Category.assoc, hone, comp_one_over]

end GlobalTheory.CompanionTheory.Ar.KillsAdic
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.birational_of_transcendence_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → Algebra.trdeg ℤ Ω = d → Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | exact GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_herm_unit_section_avoid : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (W : Ideal (MRing ι)), OverInt y φ → IsArithVar (mCoordIdeal y) d → IsSmoothHerm A → IsMultiProjPrime W → mCoordIdeal y ≤ W → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = S.M * A.a k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * S.g - g' * S.f ∈ mCoordIdeal y ∧ IsUnitSec (mCoordIdeal y) f' g' ∧ ∀ σ z, PtOver y φ σ z → ‖evC z f'‖ = (S.κ σ * A.h z) ^ S.M * ‖evC z g'‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.CompanionTheory.Relay.full_torsion_weil_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ n : ℕ, FullTorsion G ξ n → FullTorsion G' ξ' n ∧ ∀ e, GenWeil G L ξ n e → ∃ e', GenWeil G' L' ξ' n e' ∧ ∀ (x g : Over.mk ξ ⟶ G) (x' g' : Over.mk ξ' ⟶ G'), x ^ n = 1 → g ^ n = 1 → x'.left ≫ φ = spMap i ≫ x.left → g'.left ≫ φ = spMap i ≫ g.left → (e' x' g' : Ω') = i (e x g) := by
  first | exact @PositivityTheory.HtPt.Mk.ht_weil_pull | exact PositivityTheory.HtPt.Mk.ht_weil_pull
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FrameRebase

def sabRebase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' :=
  h ▸ m

theorem sabRebase_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') :
    (sabRebase m h).φ = m.φ := by
  subst h; rfl

theorem tied_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' _ _ _ h4 h5 h6 h7 _ _ _ _
  have hπ : A'.ξ ≫ (e.hom ≫ A.f) = x ≫ Y.j := by rw [← Category.assoc, h4, h5]
  obtain ⟨t, t', tΩ, a, a', m, m', u, u', E1, E2, E3⟩ :=
    GlobalTheory.T.twist_models_common_point E H D l Xo c O O' β β' Y Y' g Φ n A'.X (e.hom ≫ A.f) A'.f Ω A'.ξ x x' hπ h6 h7
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t A.t t A.f e.hom A.m a
  obtain ⟨k', hk'⟩ := sabCancel pullCubCancel E H _ _ _ Y'.t A'.t t' A'.f (𝟙 _) A'.m
    (sabRebase a' (Category.id_comp A'.f).symm)
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ A.t t tΩ e.hom A'.ξ k m
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ A'.t t' (twistSAB tΩ g) (𝟙 _) A'.ξ k' m'
  let mA : SABMap tΩ A.t A.ξ := sabRebase n₁ h4
  let mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ := sabRebase n₂ (Category.comp_id _)
  have hmA : mA.φ = m.φ ≫ k.φ := (sabRebase_φ n₁ h4).trans hn₁
  have hmA' : mA'.φ = m'.φ ≫ k'.φ := (sabRebase_φ n₂ _).trans hn₂
  rw [sabRebase_φ] at hk'
  obtain ⟨M₁, P1, P2, -, P4⟩ := GlobalTheory.T.lie_model_iso_transport E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M h4
  obtain ⟨M₂, Q⟩ := GlobalTheory.T.exists_compatible_lie_model A'.X Ω A'.ξ t.G A'.t.G tΩ.G m.φ mA'.φ m.cart mA'.cart A.Li M₁
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₂ A'.M
  refine ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, ?_, ?_, E3, P1, ?_, P2, P4⟩
  · rw [hmA, Category.assoc, ← hk, E1]
  · rw [hmA', Category.assoc, ← hk', E2]
  · intro v
    obtain ⟨w, hw1, hw2⟩ := Q v
    exact ⟨w, hw1, by rw [hφ v]; exact hw2⟩

end GlobalTheory.CompanionTheory.Ar.FrameRebase
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.arith_variety_dedekind_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) →
    HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
      [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module Ω V] (r : ℕ) (b : Fin r → V), LinearIndependent Ω b →
    ∀ (L L' : Lat ξ V) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' b Q →
      (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) →
      ∃ (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
        (∀ c, segreVec y c ≠ 0 → B.lat c = coordLat O y L b c ∧ B'.lat c = coordLat O y L' b c) ∧
        IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | exact GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.bounded_height_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines | exact GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.vertical_bound_height_compare : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | exact GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.join_model_points_project : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω), IsArithVar (mCoordIdeal (joinOf M R i)) (dimFl Ψ N + 1) ∧ Birational (joinOf M R i) ∧ (∀ (L : Type) [Field L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) ∈ ptsOver L M.P ∧ (fun p => z (joinInr M.ι R.ι p)) ∈ ptsOver L R.P) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L], ∀ w ∈ ptsOver L M.P, ∃ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | exact GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main <;> assumption)
end
