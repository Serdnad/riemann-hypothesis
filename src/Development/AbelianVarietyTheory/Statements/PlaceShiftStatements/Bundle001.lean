module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UCls

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SelfDualLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin r → E)) = ⊤ ∧
    ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ Λ

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)

def massBd (E : Type) [Field E] [NumberField E] (r M h : ℕ) : ℝ :=
  2 * h * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2)

def TorusBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → 1 ≤ M → Unr E → SelfDualLat G Λ →
    torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M ≤ (classNumber E * M ^ (2 * fdeg E) : ℕ)

def MassBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M h m : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r)
    (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E))
    (x0 : ∀ i, Frame (X i).Ψ r) (FF : ∀ i, Set (V (nd (X i)))),
    2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ →
    torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M ≤ h →
    (∀ i, IsUA (IsCMField.complexConj E) G (g i)) →
    (∀ i j, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) →
    (∀ i, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧
      ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧
        ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth (X i) (x0 i) ∧ IsFundSet (X i) (x0 i) (FF i)) →
    ∑ i, muF (X i) (x0 i) (FF i) ≤ ENNReal.ofReal (massBd E r M h)

end GlobalTheory.UCls
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

def VFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ),
  Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) ∧ FiniteDimensional ℚ_[l] (HQ l (sch.obj X) n i)

def VInv : Prop := ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id)

end GlobalTheory.GalV

namespace GlobalTheory.GalV.GaloisTowerConditions

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem geomMap_isIso {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    (u : X ⟶ Y) [IsIso u] (hu : u ≫ q = p) : IsIso (GlobalTheory.Et.geomMap Ω p u hu) := by
  refine ⟨⟨GlobalTheory.Et.geomMap Ω q (inv u) (by simp [← hu]), ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]

instance isIso_idTower_sΩ (g : (HTower.idTower k).Γ) : IsIso ((HTower.idTower k).sΩ Ω g) :=
  geomMap_isIso Ω (k := k) (𝟙 _) rfl

theorem splits_self_of_iso {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] : Splits s s (fun _ : Unit => 𝟙 Y) := by
  refine ⟨fun _ => Category.id_comp _, ?_⟩
  have hl : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) : Y ⟶ pullback s s) := by
    have : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) ≫ pullback.fst s s) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst _ _)
  refine ⟨⟨inv (pullback.lift (𝟙 Y) (𝟙 Y) rfl : Y ⟶ pullback s s) ≫ Sigma.ι (fun _ : Unit => Y) (), ?_, ?_⟩⟩
  · apply Sigma.hom_ext; intro j; cases j; simp
  · simp

theorem idTower_isCorrOp (l : ℕ) [Fact l.Prime] (g : (HTower.idTower k).Γ) :
    IsCorrOp l ((HTower.idTower k).sΩ Ω g) ((HTower.idTower k).tΩ Ω g) LinearMap.id := by
  refine ⟨_, (HTower.idTower k).sΩ Ω g, Unit, inferInstance, inferInstance, fun _ => 𝟙 _, Unit, inferInstance,
    fun _ => 𝟙 _, ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.id_comp _).symm,
      splits_self_of_iso _⟩, splits_self_of_iso _, fun x => ?_⟩
  simp only [LinearMap.id_apply, Finset.univ_unique, Finset.sum_singleton, Category.id_comp] <;> rfl

end GlobalTheory.GalV.GaloisTowerConditions

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

def QuotGlobal : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom →
    ∃ (B : Over S) (_ : GrpObj B) (q : A ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧
      Flat q.left ∧ Surjective q.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q

def InSub {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) (x : T ⟶ A) : Prop :=
  ∃ y : T ⟶ K, y ≫ i = x

end GlobalTheory.IwLevel
end
end
