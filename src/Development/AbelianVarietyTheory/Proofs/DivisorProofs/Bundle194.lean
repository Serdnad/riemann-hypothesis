module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle031
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits


theorem _root_.GlobalTheory.T.isProper_eighth_fibre_power_over : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by
  first | exact @GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | exact GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | (intros; apply GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

theorem _root_.GlobalTheory.T.normalization_basicOpen_cover' : ∀ (U X : Scheme.{0}) (f : U ⟶ X), ∀ [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite), ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)), (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra; Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧ ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  first | exact @GlobalTheory.normalization_basicOpen_cover | exact GlobalTheory.normalization_basicOpen_cover | (intros; apply GlobalTheory.normalization_basicOpen_cover <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem eq_of_minimalPrimes_le_of_isDomain_localization {A : Type} [CommRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {P p q : Ideal A} [P.IsPrime] (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A)
    (hpP : p ≤ P) (hqP : q ≤ P) : p = q := by
  haveI := hA P
  let K := RingHom.ker (algebraMap A (Localization.AtPrime P))
  have hK : K.IsPrime := RingHom.ker_isPrime _
  have hle : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → K ≤ Q := by
    intro Q hQ hQP
    have h := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ
      (Set.disjoint_left.2 fun x hx hxQ ↦ hx (hQP hxQ))
    rw [← h]
    intro x hx
    rw [RingHom.mem_ker] at hx
    simp [Ideal.mem_comap, hx]
  have h1 : K = p := le_antisymm (hle p hp.1.1 hpP) (hp.2 ⟨hK, bot_le⟩ (hle p hp.1.1 hpP))
  have h2 : K = q := le_antisymm (hle q hq.1.1 hqP) (hq.2 ⟨hK, bot_le⟩ (hle q hq.1.1 hqP))
  exact h1.symm.trans h2

theorem isOpen_zeroLocus_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) : IsOpen (PrimeSpectrum.zeroLocus (p : Set A)) := by
  have hfin := (minimalPrimes.finite_of_isNoetherianRing A).subset (Set.diff_subset (t := {p}))
  have heq : (PrimeSpectrum.zeroLocus (p : Set A))ᶜ =
      ⋃ q ∈ minimalPrimes A \ {p}, PrimeSpectrum.zeroLocus (q : Set A) := by
    ext x
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
      refine ⟨q, ⟨hq, ?_⟩, hqx⟩
      rintro rfl
      exact hx hqx
    · rintro ⟨q, ⟨hq, hne⟩, hqx⟩ hpx
      exact hne (eq_of_minimalPrimes_le_of_isDomain_localization hA hq hp hqx hpx)
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _

end GlobalTheory

namespace GlobalTheory

theorem isOpenImmersion_spec_of_quasiFinite_of_normal {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] [IsNoetherianRing A] (φ : A →+* B)
    (hA : ∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭))
    (hφ : φ.FiniteType) (hqf : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)))
    (hV : ∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧
      IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨V, hVne, hVo⟩ := hV
  set f := Spec.map (CommRingCat.ofHom φ) with hf
  have hAd : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) :=
    fun P _ ↦ (hA P).1
  have hft : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ
  let η := genericPoint (Spec (CommRingCat.of B))
  have hηV : η ∈ V :=
    ((genericPoint_spec _).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  let y₀ : PrimeSpectrum A := f η
  have hsp : ∀ x, y₀ ⤳ f x := fun x ↦ (genericPoint_specializes x).map f.continuous

  have hW : IsOpen (Set.range (V.ι ≫ f)) := (V.ι ≫ f).isOpenEmbedding.isOpen_range
  have hy₀W : y₀ ∈ Set.range (V.ι ≫ f) := ⟨⟨η, hηV⟩, rfl⟩
  have hmin : y₀.asIdeal ∈ minimalPrimes A := by
    refine ⟨⟨y₀.isPrime, bot_le⟩, fun q hq hle ↦ ?_⟩
    let z : PrimeSpectrum A := ⟨q, hq.1⟩
    have hz : z ⤳ y₀ := (PrimeSpectrum.le_iff_specializes z y₀).1 hle
    obtain ⟨v, hv⟩ := hz.mem_open hW hy₀W
    have h2 : y₀ ≤ z := by
      rw [← hv, Scheme.Hom.comp_apply]
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (hsp _)
    exact h2

  have hZo : IsOpen (closure ({y₀} : Set (PrimeSpectrum A))) := by
    rw [PrimeSpectrum.closure_singleton]
    exact isOpen_zeroLocus_of_mem_minimalPrimes hAd hmin
  let Z : (Spec (CommRingCat.of A)).Opens := ⟨closure ({y₀} : Set (PrimeSpectrum A)), hZo⟩
  have hrange : Set.range f ⊆ Set.range Z.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact specializes_iff_mem_closure.1 (hsp x)
  let g : Spec (CommRingCat.of B) ⟶ Z.toScheme := IsOpenImmersion.lift Z.ι f hrange
  have hgf : g ≫ Z.ι = f := IsOpenImmersion.lift_fac _ _ _

  haveI : _root_.IsReduced A := isReduced_ofLocalizationMaximal A fun P _ ↦ by
    haveI := hAd P; infer_instance
  haveI : Nonempty Z.toScheme := ⟨⟨y₀, subset_closure rfl⟩⟩
  haveI : IrreducibleSpace Z.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y₀)).closure
  haveI : IsIntegral Z.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hZ : ∀ z : Z.toScheme, IsIntegrallyClosed (Z.toScheme.presheaf.stalk z) := by
    intro z
    have e₁ := asIso (Z.ι.stalkMap z)
    let x : PrimeSpectrum A := Z.ι z
    have hloc : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A x
    have e₂ := IsLocalization.algEquiv x.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk x) (Localization.AtPrime x.asIdeal)
    haveI := (hA x.asIdeal).2
    have hic : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv e₂.symm.toRingEquiv
    haveI : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk (Z.ι z)) := hic
    exact IsIntegrallyClosed.of_equiv (e₁.commRingCatIsoToRingEquiv)

  haveI : IsSeparated g := IsSeparated.of_comp g Z.ι
  haveI : QuasiCompact g := QuasiCompact.of_comp g Z.ι
  haveI : LocallyOfFiniteType (g ≫ Z.ι) := by rw [hgf]; exact hft
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g Z.ι
  haveI : LocallyQuasiFinite (g ≫ Z.ι) := by rw [hgf]; exact hqf
  haveI : LocallyQuasiFinite g := LocallyQuasiFinite.of_comp g Z.ι
  haveI : IsOpenImmersion ((V.ι ≫ g) ≫ Z.ι) := by rw [Category.assoc, hgf]; exact hVo
  haveI : IsOpenImmersion (V.ι ≫ g) := IsOpenImmersion.of_comp _ Z.ι
  have := isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict g hZ V hVne
  rw [← hgf]
  infer_instance

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FinNear

theorem isAffineOpen_preimage_inf_of_isSeparated_over {Y X S : Scheme.{0}} (g : Y ⟶ X) (s : X ⟶ S)
    [IsSeparated s] {T : S.Opens} (hT : IsAffineOpen T) {D : X.Opens} (hD : IsAffineOpen D)
    (hDT : D ≤ s ⁻¹ᵁ T) {V : Y.Opens} (hV : IsAffineOpen V) (hVT : V ≤ g ⁻¹ᵁ (s ⁻¹ᵁ T)) :
    IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffine T := hT
  have : IsAffine D := hD
  let g' : V.toScheme ⟶ (s ⁻¹ᵁ T).toScheme := g.resLE (s ⁻¹ᵁ T) V hVT
  have : IsAffineHom (g' ≫ (s ∣_ T)) := isAffineHom_of_isAffine _
  have : IsAffineHom g' := IsAffineHom.of_comp g' (s ∣_ T)
  have hD' : IsAffineOpen ((s ⁻¹ᵁ T).ι ⁻¹ᵁ D) := by
    have h := isAffineOpen_opensRange (X.homOfLE hDT)
    rwa [Scheme.opensRange_homOfLE] at h
  have h := (hD'.preimage g').image_of_isOpenImmersion V.ι
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h

end GlobalTheory.FinNear

namespace GlobalTheory.FinNear

end GlobalTheory.FinNear
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens, IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_snd_image | exact GlobalTheory.IdCompOpen.isOpen_snd_image | (intros; apply GlobalTheory.IdCompOpen.isOpen_snd_image <;> assumption)
end

section

open AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  first | exact @GlobalTheory.affine_inter_finite_basicOpen_cover | exact GlobalTheory.affine_inter_finite_basicOpen_cover | (intros; apply GlobalTheory.affine_inter_finite_basicOpen_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.inv_mem_identity_component_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left), y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.inv_mem_connectedComponentIn_fibre | exact GlobalTheory.inv_mem_connectedComponentIn_fibre | (intros; apply GlobalTheory.inv_mem_connectedComponentIn_fibre <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotGlue

theorem exists_glueMap (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G)
    (hb : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left)
    (hψ : ∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) (hψF : ∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) :
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  let qL : ∀ j, pullback A.hom (𝒰.f j) ⟶ (B j).left := fun j => (q j).left
  have hq : ∀ j, qL j ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := fun j => Over.w (q j)
  have hb' : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
      (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
      w ≫ pullback.fst _ _ = y ≫ qL j → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ qL k := hb
  have key : ∀ j k, pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j ≫ ψ j =
      pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL k ≫ ψ k := by
    intro j k
    have e : pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f j) =
        pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f k) :=
      pullback.condition
    have hw : (pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j) ≫ ((B j).hom ≫ 𝒰.f j) =
        (pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.snd A.hom (𝒰.f k)) ≫ 𝒰.f k := by
      rw [Category.assoc, reassoc_of% (hq j), ← pullback.condition, ← Category.assoc, e,
        Category.assoc, Category.assoc, pullback.condition]
    have h1 := hb' j k _ _ _ (pullback.lift _ _ hw) e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [← Category.assoc, ← pullback.lift_fst _ _ hw, Category.assoc, hψ, ← Category.assoc, h1, Category.assoc]
  have hc : ∀ j k, pullback.fst ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL j ≫ ψ j) =
      pullback.snd ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL k ≫ ψ k) := key
  have hι : ∀ j, pullback.fst A.hom (𝒰.f j) ≫ Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc =
      qL j ≫ ψ j := fun j => Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc j
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc, ?_, fun j => (hι j).symm⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ A.hom) _ _ fun (j : 𝒰.I₀) => ?_
  show pullback.fst A.hom (𝒰.f j) ≫ _ ≫ F = pullback.fst A.hom (𝒰.f j) ≫ A.hom
  rw [reassoc_of% (hι j), hψF, reassoc_of% (hq j), pullback.condition]

end GlobalTheory.QuotGlue
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GlueQuotPB

theorem isIso_of_isPullback_openCover {X Y : Scheme.{0}} (f : X ⟶ Y) (𝒱 : Y.OpenCover)
    {Z : 𝒱.I₀ → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (g : ∀ i, Z i ⟶ 𝒱.X i)
    (h : ∀ i, IsPullback (k i) (g i) f (𝒱.f i)) (hg : ∀ i, IsIso (g i)) : IsIso f := by
  have key := (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{0})
    (f := f) 𝒱).2
  refine key fun i => ?_
  have e : ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).hom ≫
      pullback.snd f (𝒱.f i) = g i := by simp
  change IsIso (pullback.snd f (𝒱.f i))
  have hgi := hg i
  have e2 : pullback.snd f (𝒱.f i) =
      ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).inv ≫ g i := by
    exact (Iso.eq_inv_comp _).2 e
  rw [e2]
  infer_instance

theorem isIso_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (c : X ⟶ Y)
    (hc : ∀ j, IsIso ((Over.pullback (𝒰.f j)).map c)) : IsIso c := by
  suffices hl : IsIso c.left by
    have : IsIso ((Over.forget S).map c) := hl
    exact isIso_of_reflects_iso c (Over.forget S)
  refine isIso_of_isPullback_openCover c.left (𝒰.pullback₁ Y.hom)
    (fun j => pullback.fst X.hom (𝒰.f j)) (fun j => ((Over.pullback (𝒰.f j)).map c).left) (fun j => ?_)
    (fun j => by
      have := hc j
      exact (inferInstance : IsIso ((Over.forget _).map ((Over.pullback (𝒰.f j)).map c))))
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom (𝒰.f j)) (v₂₂ := Y.hom) (h₃₁ := 𝒰.f j) ?_ ?_
    (IsPullback.of_hasPullback Y.hom (𝒰.f j))
  · convert IsPullback.of_hasPullback X.hom (𝒰.f j) using 1
    · simp only [Over.pullback_map_left]
      erw [pullback.lift_snd]
    · exact Over.w c
  · change _ = _ ≫ pullback.fst Y.hom (𝒰.f j)
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]

theorem hom_ext_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ j, (Over.pullback (𝒰.f j)).map f = (Over.pullback (𝒰.f j)).map g) : f = g := by
  ext1
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun j => ?_
  have e := congrArg (fun u => u.left ≫ pullback.fst Y.hom (𝒰.f j)) (h j)
  change pullback.fst X.hom (𝒰.f j) ≫ f.left = pullback.fst X.hom (𝒰.f j) ≫ g.left
  simp only [Over.pullback_map_left] at e
  erw [pullback.lift_fst, pullback.lift_fst] at e
  exact e

theorem baseChange_translation {T T' : Scheme.{0}} (t : T' ⟶ T) (A H : Over T) [GrpObj A] [GrpObj H] (i : H ⟶ A) :
    ∃ e : (Over.pullback t).obj (H ⊗ A) ≅ (Over.pullback t).obj H ⊗ (Over.pullback t).obj A,
      e.hom ≫ ((fst ((Over.pullback t).obj H) ((Over.pullback t).obj A) ≫ (Over.pullback t).map i) *
          snd ((Over.pullback t).obj H) ((Over.pullback t).obj A)) =
        (Over.pullback t).map ((fst H A ≫ i) * snd H A) ∧
      e.hom ≫ snd ((Over.pullback t).obj H) ((Over.pullback t).obj A) = (Over.pullback t).map (snd H A) := by
  refine ⟨(Functor.Monoidal.μIso (Over.pullback t) H A).symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, MonObj.comp_mul, Functor.map_mul, Functor.map_comp,
      Functor.OplaxMonoidal.δ_fst_assoc, Functor.OplaxMonoidal.δ_snd]
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.δ_snd]

theorem isPullback_translation_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  intro S 𝒰 A H G _ _ i Q B ψ q hψ hq hloc

  let φ : ∀ j, B j ≅ (Over.pullback (𝒰.f j)).obj G := fun j =>
    Over.isoMk (hψ j).isoPullback (by simp)
  have hQ : ∀ j, (Over.pullback (𝒰.f j)).map Q = q j ≫ (φ j).hom := by
    intro j
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_fst]
      simp [φ, hq j]
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_snd]
      simp [φ]
  choose e he₁ he₂ using fun j => baseChange_translation (𝒰.f j) A H i
  have w : ((fst H A ≫ i) * snd H A) ≫ Q = snd H A ≫ Q := by
    refine hom_ext_of_pullback_openCover 𝒰 _ _ fun j => ?_
    rw [Functor.map_comp, Functor.map_comp, ← he₁ j, ← he₂ j, hQ j, Category.assoc, Category.assoc,
      (hloc j).w_assoc]
  have hF : ∀ j, IsPullback ((Over.pullback (𝒰.f j)).map ((fst H A ≫ i) * snd H A))
      ((Over.pullback (𝒰.f j)).map (snd H A)) ((Over.pullback (𝒰.f j)).map Q)
      ((Over.pullback (𝒰.f j)).map Q) := by
    intro j
    refine IsPullback.of_iso (hloc j) (e j).symm (Iso.refl _) (Iso.refl _) (φ j) ?_ ?_ ?_ ?_
    · simp [← he₁ j]
    · simp [← he₂ j]
    · simp [hQ j]
    · simp [hQ j]
  let c : H ⊗ A ⟶ pullback Q Q := pullback.lift _ _ w
  have hc : IsIso c := by
    refine isIso_of_pullback_openCover 𝒰 c fun j => ?_
    have hP := (IsPullback.of_hasPullback Q Q).map (Over.pullback (𝒰.f j))
    have : (Over.pullback (𝒰.f j)).map c = ((hF j).isoIsPullback _ _ hP).hom := by
      apply hP.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_fst _ _ w)
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_snd _ _ w)
    rw [this]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ w)
    (pullback.lift_snd _ _ w)

end GlobalTheory.GlueQuotPB
end
end
