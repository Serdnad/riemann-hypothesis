module

import Mathlib
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle161
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle085
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpen

theorem exists_sections {S : Scheme.{0}} (X T : Over S) [Etale X.hom] (n : ℕ) (x : Fin n → (T ⟶ X)) :
    ∃ (Z : Over S) (_ : Etale Z.hom) (z : T ⟶ Z) (σ : Fin n → (Z ⟶ X)), ∀ i, z ≫ σ i = x i := by
  induction n with
  | zero => exact ⟨𝟙_ _, inferInstanceAs (Etale (𝟙 S)), toUnit _, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨Z, hZ, z, σ, h⟩ := ih fun i => x i.succ
    refine ⟨Z ⊗ X, inferInstanceAs (Etale (pullback.fst Z.hom X.hom ≫ Z.hom)), lift z (x 0),
      Fin.cons (snd Z X) fun i => fst Z X ≫ σ i, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [h]

theorem comp_eq_iff {S : Scheme.{0}} {X Z : Over S} [Etale X.hom] [IsSeparated X.hom] (a b : Z ⟶ X)
    {K : Type} [Field K] {t : Sp K ⟶ S} (z : Over.mk t ⟶ Z) (p : Sp K) :
    z ≫ a = z ≫ b ↔ z.left p ∈ Set.range (equalizer.ι a b).left := by
  constructor
  · intro h
    refine ⟨(equalizer.lift z h).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · rintro ⟨e, he⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := (equalizer.ι a b).left) p e he.symm
    have : Nonempty ↥(pullback z.left (equalizer.ι a b).left) := ⟨w⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
    refine Over.OverMorphism.ext (eq_of_preconnected_of_unramified X.hom
      ((Over.w (z ≫ a)).trans (Over.w (z ≫ b)).symm) (pullback.fst z.left (equalizer.ι a b).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, ← Over.comp_left,
      ← Over.comp_left, equalizer.condition]

theorem exists_open_injective {S : Scheme.{0}} (X : Over S) [Etale X.hom] [IsSeparated X.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (n : ℕ) (x : Fin n → (Over.mk t ⟶ X))
    (hx : Function.Injective x) :
    ∃ U : Set S, IsOpen U ∧ t p ∈ U ∧ ∀ s ∈ U, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (t' : Sp K' ⟶ S),
      s ∈ Set.range t' ∧ ∃ x' : Fin n → (Over.mk t' ⟶ X), Function.Injective x' := by
  obtain ⟨Z, hZ, z, σ, h⟩ := exists_sections X (Over.mk t) n x
  let V : Set Z.left := ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), (Set.range (equalizer.ι (σ i) (σ j)).left)ᶜ
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => by
      have := isClosedImmersion_equalizer_ι_left (σ i) (σ j)
      exact (equalizer.ι (σ i) (σ j)).left.isClosedEmbedding.isClosed_range.isOpen_compl
  refine ⟨Z.hom '' V, Z.hom.isOpenMap V hV, ⟨z.left p, ?_, ?_⟩, ?_⟩
  · refine Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun hij hm => hij (hx ?_)
    rw [← h, ← h]
    exact (comp_eq_iff _ _ z p).2 hm
  · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  · rintro _ ⟨v, hv, rfl⟩
    let K' := AlgebraicClosure (Z.left.residueField v)
    let u : Sp K' ⟶ Z.left := spMap (algebraMap (Z.left.residueField v) K') ≫ Z.left.fromSpecResidueField v
    have q : Sp K' := (default : PrimeSpectrum K')
    have hu : u q = v := Scheme.fromSpecResidueField_apply v _
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    refine ⟨K', inferInstance, inferInstance, u ≫ Z.hom, ⟨q, congrArg (fun y => Z.hom y) hu⟩,
      fun i => u' ≫ σ i, fun i j hij => by_contra fun hne => ?_⟩
    have hm := (comp_eq_iff _ _ u' q).1 hij
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hv i) j) hne (hu ▸ hm)

theorem isProper_of_subsingleton {K : Type} [Field K] (G : Over (Sp K)) [GrpObj G] (T : TorusExtension G)
    (hT : Subsingleton T.X) : IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have hp := T.isKernel
  have : Mono T.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ T.q = toUnit _ ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := (GlobalTheory.splitTorusPointsEquiv (Sp K) T.X Y).injective (Subsingleton.elim _ _)
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono T.q.left := inferInstanceAs (Mono ((Over.forget _).map T.q))
  have : EffectiveEpi T.q.left := inferInstance
  have : IsIso T.q.left := isIso_of_mono_of_strongEpi _
  have := T.isAbelian.proper
  rw [← Over.w T.q]
  infer_instance

theorem isProper_of_injective {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G)
    (T : TorusExtension G) {g n : ℕ} (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : (n : k) ≠ 0)
    (x : Fin (n ^ (2 * g)) → {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1}) (hx : Function.Injective x) :
    IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have hc := card_torsion_mul_card_toric_torsion k G T g n hG hg hn
  have h0 : n ^ (2 * g) ≠ 0 := pow_ne_zero _ (by omega)
  have f₁ := Nat.finite_of_card_ne_zero (left_ne_zero_of_mul (hc ▸ h0))
  have f₂ := Nat.finite_of_card_ne_zero (right_ne_zero_of_mul (hc ▸ h0))
  have hle := Nat.card_le_card_of_injective x hx
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  have hd : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i} ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [hc, Nat.mul_one]; exact hle) (Nat.pos_of_ne_zero (left_ne_zero_of_mul (hc ▸ h0)))
  obtain ⟨e⟩ := SemiAbTorsionCount.nonempty_torus_points_mulEquiv k T.X
  have hcard := (SemiAbTorsionCount.divisible_and_card e n hn).2
  let i := IsMonHom.monoidHom T.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => T.isKernel.hom_ext h (toUnit_unique _ _)
  have h3 := Nat.card_le_card_of_injective
    (fun t : {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X // t ^ n = 1} =>
      (⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩ :
        {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i}))
    fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  rw [hcard] at h3
  have h4 : Module.finrank ℤ T.X = 0 := by
    by_contra hne
    exact absurd (h3.trans hd) (not_le.2 (Nat.one_lt_pow hne h2))
  exact isProper_of_subsingleton G T (Module.finrank_zero_iff.1 h4)

theorem nonempty_torsion_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {K : Type} [Field K] (t : Sp K ⟶ S) :
    Nonempty ((Over.mk t ⟶ torsion G n) ≃ {x : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G // x ^ n = 1}) := by
  obtain ⟨e, -⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G t) (𝟙 _) t (Category.id_comp t).symm
  refine ⟨(TorsionUnram.torsionEquiv G n _).trans (e.toEquiv.subtypeEquiv fun x => ?_).symm⟩
  show x ^ n = 1 ↔ e x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem isOpen_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) {g n : ℕ}
    (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : IsUnit (n : Γ(S, ⊤))) : IsOpen (abLocus G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have := GrpTangent.etale_torsion G hn
  have hm : IsSeparated ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have hm' : IsSeparated (mulN G n).left := IsSeparated.of_comp _ G.hom
  have : IsSeparated (torsion G n).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (GrpTangent.isPullback_torsion G n) hm'
  have hK : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), (n : K) ≠ 0 := fun K _ t => by
    have := ((hn.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero
    simpa using this
  have hd : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    fun K _ t => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  let K := AlgebraicClosure (S.residueField s)
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s
  have p : Sp K := (default : PrimeSpectrum K)
  have ht : t p = s := Scheme.fromSpecResidueField_apply s _
  have hB : IsAbelianScheme ((Over.pullback t).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hs K t ⟨p, ht⟩,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  have hc := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim K _ g n hB (hd K t) (hK K t)
  have := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega : n ≠ 0))
  obtain ⟨e⟩ := nonempty_torsion_equiv G n t
  let x := ((Finite.equivFinOfCardEq hc).symm.trans e.symm)
  obtain ⟨U, hU, hp, h⟩ := exists_open_injective (torsion G n) t p _ x x.injective
  refine ⟨U, fun s' hs' => ?_, hU, ht ▸ hp⟩
  obtain ⟨K', _, _, t', hr, x', hx'⟩ := h s' hs'
  obtain ⟨e'⟩ := nonempty_torsion_equiv G n t'
  obtain ⟨T⟩ := hG.fibres K' t'
  exact abLocusOne S G hG K' t' (isProper_of_injective _ (IsSemiAbelian.pullback _ G hG) T (hd K' t') h2 (hK K' t')
    (e' ∘ x') (e'.injective.comp hx')) hr

theorem isOpen_abLocus_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty G.left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom x₀
  obtain ⟨n, h2, hn⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  exact isOpen_abLocus G hG hg h2 (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

end GlobalTheory.AbLocusOpen
end

section

namespace GlobalTheory.MarkDet

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_sub_prod {ι : Type} (M : ℕ) (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (y z : ι → RA F E) (hy : ∀ i, y i ∈ hat1 F (I i : Set E)) (hz : ∀ i, z i ∈ hat1 F (I i : Set E)) :
    ∃ w ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ i ∈ s, (y i + M • z i) - ∏ i ∈ s, y i = M • w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, e⟩ := ih
    have hp := prod_mem_adelicCompletionOfElementSet F s I y (fun i _ => hy i)
    have mul := (adelicCompletion_fractionalIdeal_properties F E).1 (I a) (∏ i ∈ s, I i)
    refine ⟨y a * w + z a * (∏ i ∈ s, y i + M • w), ?_, ?_⟩
    · rw [Finset.prod_insert ha]
      exact add_mem (mul _ (hy a) _ hw) (mul _ (hz a) _ (add_mem hp (nsmul_mem hw M)))
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, sub_eq_iff_eq_add.1 e]
      simp only [nsmul_eq_mul]
      ring

theorem det_one_add_sub_one {n : ℕ} (M : ℕ) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (K : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, K i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E), (1 + M • K).det - 1 = M • w := by
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (RA F E)) i j ∈
      hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_inv_cancel₀ (hc i), Algebra.TensorProduct.one_def]
      exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem _
  have key : ∀ σ : Equiv.Perm (Fin n), ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ j, (1 + M • K) (σ j) j - ∏ j, (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j = M • w := by
    intro σ
    have := prod_sub_prod F M Finset.univ (fun j => cI (σ j) * (cI j)⁻¹)
      (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j) (fun j => K (σ j) j)
      (fun j => h1 _ _) (fun j => h _ _)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ cI, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i)] at this
    exact this
  choose w hw e using key
  refine ⟨∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • w σ, sum_mem fun σ _ => ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (hw σ) _
  · have d1 : (1 : RA F E) = (1 : Matrix (Fin n) (Fin n) (RA F E)).det := Matrix.det_one.symm
    rw [d1, Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_sub, e, Units.smul_def, Units.smul_def, smul_comm]

theorem det_sub_one_of_cong {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : ℕ) (hM : M ≠ 0)
    (G : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), G *ᵥ z - z = M • y) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), G.det - 1 = M • w := by
  have hone : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rw [← hone]
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  obtain ⟨m, hm⟩ : ∃ m : RA F E, m * (M : RA F E) = 1 :=
    ⟨algebraMap F (RA F E) (M : F)⁻¹, by
      rw [← map_natCast (algebraMap F (RA F E)) M, ← map_mul, inv_mul_cancel₀ hMF, map_one]⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) (RA F E), N = m • (G - 1) := ⟨_, rfl⟩
  have hGN : G = 1 + M • N := by
    rw [hN, ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, mul_comm, hm, one_smul, add_sub_cancel]
  have hNz : ∀ z ∈ hat F (L : Set (Fin n → E)), N *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
    intro z hz
    obtain ⟨y, hy, ey⟩ := hg z hz
    rw [hN, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ey,
      ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, hm, one_smul]
    exact hy
  obtain ⟨k, hk0⟩ : ∃ k : Matrix (Fin n) (Fin n) (RA F E), k = Q * N * P := ⟨_, rfl⟩
  have hPk : P * k = N * P := by
    simp only [hk0, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : (1 + M • k).det = G.det := by
    have h1 : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    have h2 : 1 + M • k = Q * G * P := by
      rw [hGN, hk0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP, Matrix.mul_smul, Matrix.smul_mul]
    rw [h2]
    simp only [Matrix.det_mul]
    linear_combination G.det * h1
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hNz _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  rw [← hkdet]
  exact det_one_add_sub_one F M cI hc k hk

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem gLat_eq_of_finCong {D : D7} {V : HSp D} {N : ℕ} {u : GA D V} (hu : FinCong V N u) :
    gLat V u = latHat V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact PrincLevel.finCong_map hu y hy
  · intro hz
    refine ⟨_, PrincLevel.finCong_map (PrincLevel.finCong_inv hu) z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]


end GlobalTheory.MarkDet
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_principalLevel_subgroup_open : ∀ (D : D7) (V : HSp D), ∀ N : ℕ, (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧ (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) := by
  first | exact @GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | exact GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | (intros; apply GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem map_span_eq_latG (D : D7) (V : HSp D) :
    (Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ V.L0, v = a • x}).map
      ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) = latG V 1 := by
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp⟩

theorem exists_iotaOK : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  intro D Q hP j hj
  obtain ⟨⟨-, hrt, hrt0, -⟩, -, -, hD⟩ := hP
  obtain ⟨hp, hq, φ, ε, hinj, hrange, hiso⟩ := hD j hj
  have hk := D.R.m_add_three_le_k
  obtain ⟨h1, h2⟩ := hj
  refine ⟨?_, ?_, hq, ?_⟩
  · let e := (((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E]
      (Fin (D.sp.W j).rank → D.host.E)).restrictScalars (𝓞 D.host.E))
    have hr : LinearMap.range (e ∘ₗ φ) = latG (D.sp.W j) 1 := by
      rw [LinearMap.range_comp, hrange]
      exact map_span_eq_latG D (D.sp.W j)
    have hspan : Submodule.span D.host.E (Set.range φ) = ⊤ := by
      have h := (GlobalTheory.T.adelicElementLattice_full_and_completion D (D.sp.W j) 1).2.1
      rw [← hr] at h
      have hs : ((LinearMap.range (e ∘ₗ φ) : Submodule _ _) : Set (Fin (D.sp.W j).rank → D.host.E)) =
          ((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E] (Fin (D.sp.W j).rank → D.host.E)) ''
            Set.range φ := by
        rw [← Set.range_comp]
        rfl
      rw [hs, ← Submodule.map_span] at h
      exact (Submodule.map_eq_top_iff (e := (D.sp.W j).frame.equivFun)).mp h
    have hε : ε = 1 := GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one D Q.H (Q.Dw j) j ⟨h1, h2⟩ hrt hrt0 hp hq φ ε hinj hspan hiso
    refine ⟨e ∘ₗ φ, hrt, hrt0, ⟨(D.sp.W j).frame.equivFun.injective.comp hinj, hr⟩, fun x y => ?_⟩
    have hx : ∀ z, (D.sp.W j).frame.equivFun.symm ((e ∘ₗ φ) z) = φ z := fun z =>
      (D.sp.W j).frame.equivFun.symm_apply_apply (φ z)
    rw [hx, hx, hiso x y, hε]
    simp
  · rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  · rw [hq]
    simp only [Ranks.sigW, Ranks.r]
    omega

end GlobalTheory.Member
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.latticeModel_of_same_signature_hasseNorm : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw Di : Datum H) (r : ℕ) (Ψ : Finset (E →+* ℂ)) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), Di.p = Dw.p → Di.q = Dw.q → (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → cc ξ₀ = -ξ₀ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → LatModel l Ψ Gm ξ₀ Dw.q Di := by
  first | exact @GlobalTheory.FrameUnif.latModel_of_same_signature | exact GlobalTheory.FrameUnif.latModel_of_same_signature | (intros; apply GlobalTheory.FrameUnif.latModel_of_same_signature <;> assumption)
end
