module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_of_isProper_of_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsProper s]
    {L : LB X} (hL : L.IsLB) {n : ℕ} (σ : Fin n → LB.Sec L) (ha : ∀ i, IsAffineOpen (Out.nonzeroLocus (σ i)))
    (hc : ⨆ i, Out.nonzeroLocus (σ i) = ⊤) : IsProjOver s := by
  have hA : IsAmpleLB L := by
    refine ⟨hL, ⟨?_⟩, ?_⟩
    · have hu : (Set.univ : Set X) = ⋃ i, (Out.nonzeroLocus (σ i) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup, hc]
        rfl
      rw [hu]
      exact isCompact_iUnion fun i => (ha i).isCompact
    · intro x
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      refine ⟨1, le_rfl, secToPow (σ i) 1, ?_, ?_⟩
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact hi
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact ha i
  exact hA.isProjOver s

theorem isProjOver_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  intro Γ _ _ X X' ρ π hq R _ _ s' hX
  have hQ : IsAffineQuotient ρ π :=
    ⟨hq.2.1, hq.1, fun W => (hq.2.2 W).1, fun W f hf => (hq.2.2 W).2 f (by
      unfold IsInvariantSection at hf
      exact fun g _ => (hf g).2)⟩
  have hP : IsProper (π ≫ s') := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX).1
  have hs' : IsProper s' := hQ.isProper s'
  have hXs : X.IsSeparated := by
    constructor
    rw [show terminal.from X = (π ≫ s') ≫ terminal.from (Sp R) from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨L, n, σ, hL, ha, ho⟩ := exists_sections_orbit_subset_nonzeroLocus Γ R X (π ≫ s') ρ hX
  obtain ⟨L', n', σ', hL', ha', hc'⟩ :=
    QuotientNorm.exists_affine_cover_of_quotient Γ X X' ρ π hq hXs L n σ hL ha ho
  exact isProjOver_of_isProper_of_affine_cover s' hL' σ' ha' hc'

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevUniq

theorem exists_sab_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem map_to_univ_unique : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ := by
  intro hL _ _ E _ _ _ H D l₀ l Xo B _ b S s o r r' ν ν' hS hs hν hν'
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by
      rw [show spMap (RingHom.id (KA l₀)) = 𝟙 (Sp (KA l₀)) from Spec.map_id _, Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom o.t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ o.t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ o.t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans (hν.1 a).symm), hν'.1 a]
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.etaA a).trans (hν.2 a).symm), hν'.2 a]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

end GlobalTheory.LevUniq
end
