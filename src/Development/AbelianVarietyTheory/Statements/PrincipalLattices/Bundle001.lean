module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def DegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
    IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (T : PAT H (Sp (𝓞 K))),
    Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H T.t.act ρ 1 0 →
    ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
      ((2 * deg h (F.eigLat T.t.act τ) : ℝ) : ℂ) = logOm E χ

def IndSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K)
    (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    (∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j)) →
    let N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
      ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K))
    (∀ x, N x ≤ FB.eigLat X.B.t.act x.2) ∧
    (∀ x, latRank K (N x) = open Classical in if x.2 H.rt = (if x.1.isLeft then ρ else -ρ) then 1 else 0) ∧
    (∀ j, Function.Injective (M j)) ∧
    iSupIndep (fun x => Submodule.span K (N x : Set (Fin FB.P₀.g → K))) ∧
    ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤

namespace NumInh

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem deg_conjugate_type (hD : DegSt) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) {ρ : 𝓞 K}
    {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q) (F : GenFib (X.A false).pol) {h : HermFam K (Fin F.P₀.g → K)}
    (hh : F.IsHerm h) {τ : 𝓞 E →+* 𝓞 K} (hτ : τ H.rt = -ρ) :
    2 * deg h (F.eigLat (X.A false).t.act τ) = (logOm E χ).re := by
  have hD' := hD E H χ hχ K (-ρ) (X.A false) X.split (by rw [neg_sq]; exact X.ρ_sq)
    (Test.hasType_neg X.ρ_sq X.typeM) F h hh τ hτ
  have hre := congrArg Complex.re hD'
  rwa [Complex.ofReal_re] at hre

end NumInh

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def TensorObjSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → D.p = 0 ∨ D.q = 0 →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : 𝓞 K₁) (C : Ell H (𝓞 K₁) ω) (ε : ℤˣ)
      (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K₁)))
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hk).toRingHom)),
      k ≤ K₁ ∧ C.IsPrincipalAt ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) ∧
      IsKForm D ε h ∧ Nonempty (IsTen C D h T) ∧ Nonempty (SABMap o.t T.t (spMap (algebraMap (𝓞 K₁) K₁)))

def CMExistsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
      (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
      (e : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
      (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (e b)) ∧
      (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
      ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
        x ≫ m'.φ = (e _ z ≫ X.φ j).left → x ≫ m.φ = (FU.ex i Pe (F j z)).left

namespace ExSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end ExSt

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumInh

variable {K : Type} [Field K] [NumberField K]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dim_pos_of_lieMult {S : Scheme.{0}} {O k : Type} [CommRing O] [Field k] {G : Over S} [GrpObj G] {act : OAct O G}
    {t : Sp k ⟶ S} {τ : O →+* k} (h : LieMult act t τ 1) {g : ℕ} (hg : SmoothOfRelativeDimension g G.hom) : 1 ≤ g := by
  by_contra h0
  obtain rfl : g = 0 := by omega
  have : Etale G.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  obtain ⟨v, hv, hu⟩ := h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have key : ∀ c : k, (v 0).left = spMap (epsScale c) ≫ (v 0).left := fun c => by
    refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (isNilpotent_ker_specMap _ hnil) G.hom ?_ ?_
    · rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale]
    · rw [Category.assoc, Over.w (v 0)]
      show spMap _ ≫ t = spMap _ ≫ spMap _ ≫ t
      rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have e : ∀ c : Fin 1 → k, ∃ u : Fin 1 → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ v 0 = (List.ofFn u).prod := fun c =>
    ⟨v, fun i => by rw [Subsingleton.elim i 0]; exact key _, by simp⟩
  exact zero_ne_one (congrFun ((hu _ (hv 0)).unique (e 0) (e 1)) 0)

theorem exists_char (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : ∃ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ := by
  obtain ⟨τ⟩ : Nonempty (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (hs ▸ Module.finrank_pos)).1
  have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with e | e
  · exact ⟨τ, e⟩
  · exact ⟨τ.comp H.bar.toRingHom, by
      show τ (H.bar H.rt) = ρ
      rw [Test.bar_rt, map_neg, e, neg_neg]⟩

theorem dim_pos_of_hasType (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (T : PAT H (Sp (𝓞 K))) {q : ℕ}
    (hT : HasType H T.t.act ρ 1 q) : 1 ≤ T.g := by
  obtain ⟨τ, hτ⟩ := exists_char hs hρ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact dim_pos_of_lieMult ((hT ℂ (σ.comp (algebraMap (𝓞 K) K)) (σ.injective.comp RingOfIntegers.coe_injective)
    ((σ.comp (algebraMap (𝓞 K) K)).comp τ)).1 (by rw [RingHom.comp_apply, hτ])) T.dim


end GlobalTheory.CM.NumInh
end
end
