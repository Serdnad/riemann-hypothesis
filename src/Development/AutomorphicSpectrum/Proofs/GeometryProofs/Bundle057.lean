module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_tensor_power_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)), (∀ i, (Λ i).IsVBOn T 1 ⊤) → ∀ a : I → ℤ, (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) → (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | exact GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.generic_flag_under_equiv : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport | exact GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.flag_bundle_under_equiv : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map | exact GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

theorem mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hv : ∀ p, (v p).1 = κ p.1) (f : MvPolynomial (Σ k, ι k) ℤ) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv]

theorem imageZ_coord {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hκ : Function.Injective κ) (hv : ∀ p, (v p).1 = κ p.1) :
    imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  change mConeMap y (rename v f) = 0 ↔ _
  rw [mConeMap_rename κ v y hv f]
  exact map_eq_zero_iff _ (rename_injective κ hκ)

theorem pullDeg_comp {K K' K'' : Type} (κ : K → K') (κ' : K' → K'')
    (hκ : Function.Injective κ) (hκ' : Function.Injective κ') (a : K → ℤ) :
    pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a) := by
  funext k''
  simp only [pullDeg]
  by_cases h' : ∃ k', κ' k' = k''
  · obtain ⟨k', rfl⟩ := h'
    rw [hκ'.extend_apply]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hκ.extend_apply]
      exact (hκ'.comp hκ).extend_apply a 0 k
    · have h2 : ¬∃ k, (κ' ∘ κ) k = κ' k' := fun ⟨k, hk⟩ => h ⟨k, hκ' hk⟩
      rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h2]
      rfl
  · have h2 : ¬∃ k, (κ' ∘ κ) k = k'' := fun ⟨k, hk⟩ => h' ⟨κ k, hk⟩
    rw [Function.extend_apply' _ _ _ h', Function.extend_apply' _ _ _ h2]

end GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

namespace GlobalTheory.CompanionTheory.Ar.Cmp


open GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock in
theorem join_block_maps : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K₁ _ ι₁ _ K₂ _ ι₂ _ Ω y₁ y₂
    refine ⟨⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩, ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · funext ⟨k, i⟩
      rfl
    · funext ⟨k, i⟩
      rfl
  · intro K _ ι _ K' _ ι' _ κ v Ω _ y h
    exact imageZ_coord κ v y h.1 h.2.2.1
  · intro K _ ι _ K' _ ι' _ K'' _ ι'' _ κ v κ' v' h h'
    obtain ⟨hκ, hv, hc, hs⟩ := h
    obtain ⟨hκ', hv', hc', hs'⟩ := h'
    refine ⟨⟨hκ'.comp hκ, hv'.comp hv, fun p => ?_, ?_⟩, pullDeg_comp κ κ' hκ hκ'⟩
    · simp [hc', hc]
    · rintro q ⟨k, hk⟩
      obtain ⟨q', rfl⟩ := hs' q ⟨κ k, hk⟩
      have h1 : q'.1 = κ k := hκ' ((hc' q').symm.trans hk.symm)
      obtain ⟨p, rfl⟩ := hs q' ⟨k, h1.symm⟩
      exact ⟨p, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem HostAut.s_symm_s (g : HostAut H) (a : 𝓞 E) : g.s (g.symm.s a) = a :=
  RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))

theorem HostAut.hostAut_symm_s_s (g : HostAut H) (a : 𝓞 E) : g.symm.s (g.s a) = a :=
  RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))

theorem HostAut.hostAut_refl_s (a : 𝓞 E) : (HostAut.refl H).s a = a :=
  RingOfIntegers.ext rfl

theorem oAct_eq {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] {u v : OAct O G}
    (h : ∀ a, u.act a = v.act a) : u = v := by
  cases u
  cases v
  have : ∀ a, _ = _ := h
  obtain rfl : _ = _ := funext this
  rfl

theorem twistSAB_eq_of_act {S : Scheme.{0}} (t : SAB H S) (g : HostAut H)
    (h : ∀ a, t.act.act (g.s a) = t.act.act a) : twistSAB t g = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct act g.s = act := oAct_eq h
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_twistSAB {S : Scheme.{0}} (t : SAB H S) (g g' : HostAut H)
    (h : ∀ a, g.s (g'.s a) = a) : twistSAB (twistSAB t g) g' = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct (twistAct act g.s) g'.s = act := oAct_eq fun a => congrArg act.act (h a)
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_symm_refl (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S) (g : HostAut H) :
    twistSAB (twistSAB t g) g.symm = t ∧ twistSAB (twistSAB t g.symm) g = t ∧
      twistSAB t (HostAut.refl H) = t :=
  ⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s,
    twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g  := by
  intro E _ _ _ H D l B _ b S s S' s' o o' f m g a h h'
  exact ⟨{ toSABMap := twistMap m.toSABMap g
           eta := fun x => m.eta (a.a l.M x)
           etaA := fun x => m.etaA (a.a l.A x) }, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite

end GlobalTheory.CompanionTheory.Ar.HodgeExists
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieIntertwining

theorem act_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  intro E _ _ _ H g Ω _ X X' ξ ξ' t t' tΩ m m' V V' _ _ _ _ M M' ρ ρ' φ hM hM' tie a v
  obtain ⟨w, hw, hw'⟩ := tie v
  obtain ⟨w₃, hw₃, hw₃'⟩ := tie (ρ (g.s a) v)

  have h1 : (M.pt (ρ (g.s a) v)).left = (M.pt v).left ≫ (t.act.act (g.s a)).left := by
    rw [hM (g.s a) v]; rfl
  have h2 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ m.φ = w₃.left ≫ m.φ := by
    rw [hw₃, h1, ← hw, Category.assoc, Category.assoc, m.act]
  have h3 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ tΩ.G.hom = w₃.left ≫ tΩ.G.hom := by
    rw [Category.assoc, Over.w, Over.w, Over.w]
  have h4 : w.left ≫ (tΩ.act.act (g.s a)).left = w₃.left := m.cart.1.hom_ext h2 h3
  have h5 : (M'.pt (φ (ρ (g.s a) v))).left = (M'.pt (ρ' a (φ v))).left := by
    have h6 : (tΩ.act.act (g.s a)).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
    rw [← hw₃', ← h4, hM' a (φ v), Over.comp_left, ← hw']
    exact (Category.assoc _ _ _).trans ((congrArg (w.left ≫ ·) h6).trans (Category.assoc _ _ _).symm)
  exact M'.inj (Over.OverMorphism.ext h5)

end GlobalTheory.CompanionTheory.Ar.LieIntertwining
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.patch_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (q : Cpt ξ), (∀ p ∈ S, p.Prime) →
    ((∀ p ∈ S, ¬ InFibre ξ p q) → Lat.patch S L₀ Lp q = L₀ q) ∧
      ∀ p ∈ S, InFibre ξ p q → Lat.patch S L₀ Lp q = Lp p q := by
  intro X Ω _ ξ E _ _ S L₀ Lp q hS
  exact ⟨fun h => Lat.patch_of_not S L₀ Lp h, fun p hp h => Lat.patch_of_unique S L₀ Lp hp h
    fun p' hp' h' => inFibre_unique (hS p hp) (hS p' hp') h h'⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li]
      [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O]
      (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q →
      M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) →
        (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ Li _ _ M L n g O _ ρ σ q hVB hOm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat {q} g hVB).2 q rfl
  have hD : M.htDual L n ρ σ q = M.eigLat ρ σ q := by
    refine le_antisymm (fun e he => ?_) (M.eigLat_le_htDual L n ρ σ q)
    obtain ⟨he1, he2⟩ := (M.mem_htDual_iff L n ρ σ q e).1 he
    refine ⟨(hbi e).2 fun w hw => he2 w ?_, he1⟩
    rw [hOm]
    exact hw
  refine ⟨hD, fun 𝔡 hσ ⟨d, hd, hu, _, hinv⟩ => le_antisymm ?_ fun e he => ?_⟩
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 : σ d • e ∈ M.eigLat ρ σ q := hD ▸ he.2 d hd
    have h2 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) ∈ M.eigLat ρ σ q := Submodule.smul_mem _ _ h1
    have h3 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) = e := by
      change (σ d)⁻¹ • (σ d • e) = e
      rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    rwa [h3] at h2
  · refine Submodule.subset_span ⟨he.2, fun a ha => ?_⟩
    rw [hD]
    exact Submodule.smul_mem (M.eigLat ρ σ q) (⟨σ a, hσ a⟩ : regAt ξ q) he

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigenspace_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | exact GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext <;> assumption)
end
