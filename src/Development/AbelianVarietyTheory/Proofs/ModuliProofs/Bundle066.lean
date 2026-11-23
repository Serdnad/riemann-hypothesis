module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SemiAbelianDescent

theorem exists_section {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

theorem exists_lift {X X' : Scheme.{0}} (π : X ⟶ X') [IsIntegralHom π] [Surjective π]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ X') :
    ∃ q : Spec (CommRingCat.of Ω) ⟶ X, q ≫ π = p := by
  obtain ⟨s, hs⟩ := exists_section (pullback.snd π p)
  refine ⟨s ≫ pullback.fst π p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

private theorem isClosed_range_diagonal_of_surjective_universallyClosed {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S) [Surjective j]
    {P : Scheme.{0}} (m : P ⟶ Limits.pullback f f) [UniversallyClosed m] (d : X ⟶ P)
    (hd : IsClosed (Set.range d)) (hc : d ≫ m = j ≫ pullback.diagonal f) :
    IsClosed (Set.range (pullback.diagonal f)) := by
  have key : Set.range (pullback.diagonal f) = m '' Set.range d := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩
  rw [key]
  exact m.isClosedMap _ hd

theorem isSeparated_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  have hm := MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f)
    (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl
  have hcl := isClosed_range_diagonal_of_surjective_universallyClosed j f
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f))
    (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

theorem quasiCompact_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [QuasiCompact (j ≫ f)] : QuasiCompact f := by
  refine ⟨fun U hU hU' => ?_⟩
  have h := (QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := j.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous

theorem isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩

theorem main : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G.left ⟶ G'.left), IsIntegralHom π → Surjective π → IsGrpPullback G G' π φ → Smooth G'.hom → IsSemiAbelian G → IsSemiAbelian G' ∧ ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) := by
  intro X X' π G _ G' _ _ φ hi hs h hsm hG
  have hG' : IsSemiAbelian G' := isSemiAbelian_descends h hG
  refine ⟨hG', ?_⟩
  rintro ⟨U, hU, hP⟩
  have hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G := abLocus_pullback abLocusOne hG' h.1
  have hV : IsOpen (abLocus G') := by
    have hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ := by
      ext y
      obtain ⟨x, rfl⟩ := π.surjective y
      constructor
      · intro hy
        refine ⟨x, ?_, rfl⟩
        rw [Set.mem_compl_iff, hU, ← hloc]
        exact hy
      · rintro ⟨x', hx', hxx⟩
        rw [Set.mem_compl_iff, ← hxx, hloc, ← hU]
        exact hx'
    rw [← isClosed_compl_iff, hc]
    exact π.isClosedMap _ U.isOpen.isClosed_compl
  let V' : X'.Opens := ⟨abLocus G', hV⟩
  have hpre : π ⁻¹ᵁ V' = U := by
    ext x
    change π x ∈ abLocus G' ↔ x ∈ (U : Set X)
    rw [hU, hloc]
  rw [← hpre] at hP
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V') := by
    intro x hx
    change G'.hom (φ x) ∈ V'
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact hx
  let a := φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle
  have heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V') := by
    rw [← cancel_mono V'.ι]
    simp only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, hw]
  have ha : Surjective a := by
    constructor
    intro z
    obtain ⟨w, hw'⟩ := φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)
    have hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left) := by
      rw [← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]
      exact ⟨z, rfl⟩
    have hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι := by
      rw [Scheme.Opens.range_ι]
      change π (G.hom w) ∈ V'
      rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']
      exact hz
    obtain ⟨w', rfl⟩ := hm
    refine ⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']
  have hsep : IsSeparated G'.hom := hG'.separated
  have hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V')) := by
    rw [heq]
    infer_instance
  have huc : UniversallyClosed (G'.hom ∣_ V') := UniversallyClosed.of_comp_surjective a _
  exact ⟨V', rfl, by constructor⟩

end GlobalTheory.SemiAbelianDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

private lemma mul_mul_pow_mul_inv_pow_eq {A B G G' c c' : ℂ} (m n : ℕ) (h : A * G' ^ m = G ^ n * B)
    (hGc : G * c ≠ 0) : A * (G' * c') ^ m * ((G * c) ^ n)⁻¹ = B * c' ^ m * (c ^ n)⁻¹ := by
  have hGn : G ^ n ≠ 0 := pow_ne_zero n (left_ne_zero_of_mul hGc)
  rw [mul_pow, mul_pow, mul_inv,
    show A * (G' ^ m * c' ^ m) * ((G ^ n)⁻¹ * (c ^ n)⁻¹) = A * G' ^ m * (G ^ n)⁻¹ * (c' ^ m * (c ^ n)⁻¹) by ring,
    h, mul_comm (G ^ n) B, mul_inv_cancel_right₀ hGn]
  ring

private lemma mul_pow_mul_inv_pow_eq_of_factor {s a b a' b' x x' E E' : ℂ} (m n : ℕ) (ha : a = x * E * b)
    (ha' : a' = x' * E' * b') (hE : E' ^ m = E ^ n) (hx : x ≠ 0) (hx' : x' ≠ 0) (hEne : E ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    s * b' ^ m * (b ^ n)⁻¹ = x ^ n * (x' ^ m)⁻¹ * (s * a' ^ m * (a ^ n)⁻¹) := by
  subst ha ha'
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hE]
  field_simp


open PullHermitian in
theorem semicharacter_pull_eq_of_lbIso_pow :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ₀ : ∀ l ∈ u.Λ, F l ∈ u'.Λ), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hΛ₀ l l.2⟩ ^ m := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hΛ₀ hex m n hiso

  have hH := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex m n hiso
  obtain ⟨w, hw⟩ := hiso
  unfold HolUnif.IsAH at hu hu'
  have := u.discrete
  have hxf : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by rw [hex z]; rfl

  let φ : L.ι × L'.ι → (Fin g → ℂ) → ℂ := fun p z =>
    valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m * (u.fr p.1 z ^ n)⁻¹
  let V : L.ι × L'.ι → Set (Fin g → ℂ) := fun p =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1 ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U p.2}
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have hV : ∀ p, IsOpen (V p) := fun p =>
    (u.hol (L.U p.1) 0).1.inter ((u'.hol (L'.U p.2) 0).1.preimage hFc)
  have hcov : ∀ z, ∃ p, z ∈ V p := fun z => by
    obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
    obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
    exact ⟨(i, j), hi, hj⟩
  have hdiv : ∀ i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f.left) m)).U (idx f.left m n i j) :=
    fun i j z hi hj => idx_chart _ f.left m n i j hi (by rw [← hxf]; exact hj)
  have hφd : ∀ p, DifferentiableOn ℂ (φ p) (V p) := fun p => by
    have h1 := ((u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2).mono
      (fun z (hz : z ∈ V p) => hdiv p.1 p.2 z hz.1 hz.2)
    have h2 : DifferentiableOn ℂ (fun z => u'.fr p.2 (F z)) (V p) :=
      (u'.fr_hol p.2).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn
        (fun z hz => hz.2)
    have h3 : DifferentiableOn ℂ (fun z => u.fr p.1 z) (V p) := (u.fr_hol p.1).mono (fun z hz => hz.1)
    exact (h1.mul (h2.pow m)).mul ((h3.pow n).inv fun z hz => pow_ne_zero _ (u.fr_ne _ z hz.1))
  have hagree : ∀ p q z, z ∈ V p → z ∈ V q → φ p z = φ q z := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hi, hj⟩ ⟨hi', hj'⟩
    have hj₁ : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j := by rw [← hxf]; exact hj
    have hj₁' : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j' := by rw [← hxf]; exact hj'
    have hval := val_iso_pow (u.ex z).left f.left m n w hw i i' j j' hi hi' hj₁ hj₁'
    have hc := u.fr_compat i i' z (inf_of _ hi hi')
    have hc' := u'.fr_compat j j' (F z) (inf_of _ hj hj')
    rw [hxf] at hc'
    have hne : u.fr i z ≠ 0 := u.fr_ne i z hi
    simp only [φ]
    rw [hc] at hne ⊢
    rw [hc']
    exact mul_mul_pow_mul_inv_pow_eq m n hval hne
  obtain ⟨r, hr, hrφ⟩ := exists_glue V hV hcov φ hφd hagree
  have hφne : ∀ i j z, z ∈ V (i, j) → φ (i, j) z ≠ 0 := by
    intro i j z hz
    have hd := hdiv i j z hz.1 hz.2
    simp only [φ]
    rw [valAt'_eq_unitVal _ hd]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne j _ hz.2)))
      (inv_ne_zero (pow_ne_zero _ (u.fr_ne i z hz.1)))
  have hr_ne : ∀ z, r z ≠ 0 := fun z => by
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    rw [hrφ _ z hp]
    exact hφne i j z hp
  have hexl : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have hexl' : ∀ (l : u.Λ) z, u'.ex (F (z + l)) = u'.ex (F z) := fun l z => by
    rw [map_add (f := _), u'.ex_add, (u'.ker _).2 (hΛ₀ _ l.2), _root_.mul_one]
  have hχne : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hu.2.2.1 l
  have hχne' : ∀ l, χ' l ≠ 0 := fun l h0 => by simpa [h0] using hu'.2.2.1 l
  let c : u.Λ → ℂ := fun l => χ l ^ n * (χ' ⟨F l, hΛ₀ l l.2⟩ ^ m)⁻¹
  have h0 : ∀ a b : Fin g → ℂ, hermForm (0 : Matrix (Fin g) (Fin g) ℂ) a b = 0 := fun a b => by
    simp [hermForm]
  have hper : ∀ (l : u.Λ) z, r (z + l) =
      c l * Complex.exp (Real.pi * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z (l : Fin g → ℂ) +
        Real.pi / 2 * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℂ) (l : Fin g → ℂ)) * r z := by
    intro l z
    simp only [h0, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    have hzl : z + l ∈ V (i, j) := ⟨by rw [hexl]; exact hp.1, by rw [hexl']; exact hp.2⟩
    rw [hrφ _ _ hzl, hrφ _ _ hp]
    have ha := hu.2.2.2 l i z hp.1
    have ha' := hu'.2.2.2 ⟨F l, hΛ₀ l l.2⟩ j (F z) hp.2
    dsimp only at ha'
    have hb : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl.1
    have hb' : u'.fr j (F z + F l) ≠ 0 := u'.fr_ne j _ (by rw [← map_add (f := _)]; exact hzl.2)
    simp only [φ, c]
    rw [hexl l z, map_add (f := _)]
    refine mul_pow_mul_inv_pow_eq_of_factor m n ha ha' ?_ (hχne l) (hχne' _) (Complex.exp_ne_zero _) hb hb'
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have e1 := hH z l
    have e2 := hH l l
    simp only [hermForm] at e1 e2
    linear_combination (Real.pi : ℂ) * e1 + ((Real.pi : ℂ) / 2) * e2
  have hcn : ∀ l, ‖c l‖ = 1 := fun l => by
    simp only [c, norm_mul, norm_inv, norm_pow, hu.2.2.1 l, hu'.2.2.1, one_pow, inv_one, _root_.mul_one]
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 c r
    Matrix.isHermitian_zero hcn hr hr_ne hper).2.1
  intro l
  have hl := key l
  simp only [c] at hl
  exact (mul_inv_eq_one₀ (pow_ne_zero _ (hχne' _))).1 hl

theorem appellHumbert_data_eq_of_lbIso_pow_pull :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ) (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (n : ℕ), 0 < n → L.IsLB → L'.IsLB → u.IsAH Hm χ → u'.IsAH Hm' χ' → (∀ z, u'.ex (F z) = u.ex z ≫ f) → LBIso (lbPow L n) (lbPow (L'.pull f.left) n) → (∀ z w, hermForm Hm z w = hermForm Hm' (F z) (F w)) ∧ ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hF l l.2⟩ ^ n := by
  intro A A' _ _ L L' g g' u u' Hm Hm' χ χ' f F hF n hn hL hL' hu hu' hex hiso
  have hiso' := hiso.symm
  refine ⟨fun z w => ?_,
    semicharacter_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hex n n hiso'⟩
  have h := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex n n hiso' z w
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_left_cancel₀ hn' h).symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EllipticLevel

theorem exists_stdSymp_of_rel {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j) := by
  classical

  set H : Subgroup G := (powMonoidHom k : G →* G).ker with hH
  have memH : ∀ x : G, x ∈ H ↔ x ^ k = 1 := fun x => by
    rw [hH, MonoidHom.mem_ker, powMonoidHom_apply]
  have torsH : ∀ x : H, (x : G) ^ k = 1 := fun x => (memH x).1 x.2

  let f : H → H → Rˣ := fun x y => (hW x y (torsH x) (torsH y)).exists.choose
  have hf : ∀ x y : H, W x y (f x y) := fun x y => (hW x y (torsH x) (torsH y)).exists.choose_spec
  have uniq : ∀ (x y : H) (c : Rˣ), W x y c → c = f x y := fun x y c h =>
    (hW x y (torsH x) (torsH y)).unique h (hf x y)
  have fswap : ∀ x y : H, f y x = (f x y)⁻¹ := fun x y =>
    (uniq y x _ (hsymm _ _ _ (hf x y))).symm
  have fmulL : ∀ x x' y : H, f (x * x') y = f x y * f x' y := fun x x' y =>
    (uniq _ _ _ (hmul _ _ _ _ _ (hf x y) (hf x' y))).symm
  have fmulR : ∀ x y y' : H, f x (y * y') = f x y * f x y' := fun x y y' => by
    rw [← uniq x (y * y') _ (hsymm _ _ _ (hmul _ _ _ _ _ (hf y x) (hf y' x))), fswap x y, fswap x y',
      mul_inv, inv_inv, inv_inv]
  let e : H →* H →* Rˣ :=
    MonoidHom.mk' (fun x => MonoidHom.mk' (f x) (fmulR x)) (fun x x' => by
      ext y
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply]
      rw [fmulL])
  have heq : ∀ x y : H, e x y = f x y := fun _ _ => rfl

  have hcH : ∀ d : ℕ, d ∣ k → Nat.card {x : H // x ^ d = 1} = d ^ (2 * g) := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    have eqv : {x : H // x ^ d = 1} ≃ {x : G // x ^ d = 1} :=
      { toFun := fun x => ⟨x.1, by simpa using congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, (memH _).2 (by rw [hm, pow_mul, y.2, one_pow])⟩,
          Subtype.ext (by simpa using y.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact hc d ⟨m, hm⟩
  have hkH : ∀ x : H, x ^ k = 1 := fun x => Subtype.ext (by simpa using torsH x)
  have halt' : ∀ x : H, e x x = 1 := fun x => by
    rw [heq]
    exact (uniq x x 1 (halt x (torsH x))).symm
  have hnd' : ∀ x : H, (∀ y, e x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    refine hnd x (torsH x) (fun y hy => ?_)
    have h1 := hf x ⟨y, (memH y).2 hy⟩
    rwa [← heq, hx] at h1
  obtain ⟨v, hv⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing k g H R ze hk hz hkH hcH e halt' hnd'
  refine ⟨fun i => (v i : G), fun i => torsH (v i), fun i j => ?_⟩
  have h2 := hf (v i) (v j)
  rwa [← heq, hv i j] at h2

theorem exists_symplectic_system (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (k : ℕ)
    (hk : (k : K) ≠ 0) (ze : Kˣ) (hze : IsPrimitiveRoot ze k) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), (∀ i, pt i ^ k = 1) ∧
      ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j) := by
  obtain ⟨-, -, -, -, -, hmn, -, -, -, hw, hwn, -⟩ := hL
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have := P.isAb.comm

  have hc : ∀ d, d ∣ k → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hk0
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      intro h0
      apply hk
      rw [Nat.cast_mul, h0, zero_mul]
    exact ((hmn (Sp K) P d hd0).2.2.2.2 K (𝟙 _) hdK)

  have hleft : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = a := fun a => by simp
  have hleft' : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a) = a := fun a => by simp
  haveI : IsDomain Γ(Sp K, ⊤) := Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (Function.LeftInverse.injective hleft')
  have hz' : IsPrimitiveRoot (unitOn ze) k :=
    hze.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (Function.LeftInverse.injective hleft))
  have hwB := hw (Sp K) P k (Out.baseOver (Sp K))
  obtain ⟨v, hv1, hv2⟩ := exists_stdSymp_of_rel (G := Out.baseOver (Sp K) ⟶ P.A) (R := Γ(Sp K, ⊤)) hk0 hc hz'
    (fun x y c => Out.WeilIs P.A P.L k x y c) hwB.1 hwB.2.1 hwB.2.2.1
    (fun _ _ _ h => GlobalTheory.CommPairing.weilIs_symm P.isLB h) (fun x hx h => hwn K P k hk x hx h)
  exact ⟨v, hv1, hv2⟩

end GlobalTheory.EllipticLevel

namespace GlobalTheory

end GlobalTheory
end
