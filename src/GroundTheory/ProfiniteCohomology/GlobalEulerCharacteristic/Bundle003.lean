module

public import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Bundle002
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.OrbitInvariants
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
public import GroundTheory.ProfiniteCohomology.PoitouTate.Bundle001
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
import GroundTheory.ProfiniteCohomology.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global MulAction NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

section Complex

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem stabilizer_eq_bot_of_isComplex {w : NumberField.InfinitePlace L}
    (hw : (w.comap (algebraMap K L)).IsComplex) : MulAction.stabilizer (L ≃ₐ[K] L) w = ⊥ :=
  NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1
    (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inr hw))

theorem stabilizer_eq_bot_of_isReal {w : NumberField.InfinitePlace L} (hw : w.IsReal) :
    MulAction.stabilizer (L ≃ₐ[K] L) w = ⊥ :=
  NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1
    (NumberField.InfinitePlace.isUnramified_iff.2 (Or.inl hw))

end Complex

section InfPlace

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1} (L : FiniteSubfield) [Fact (K ≤ L)]

theorem infPlaceOfEmbedding_eq_inv_smul (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (τ : L.1 ≃ₐ[K.1] L.1) (h : ∀ x : L.1, ι' x = ι (τ x)) :
    (infPlaceOfEmbedding ι' L : NumberField.InfinitePlace L.1) =
      τ⁻¹ • (infPlaceOfEmbedding ι L : NumberField.InfinitePlace L.1) := by
  set w₀ := infPlaceOfEmbedding ι L
  have hcomap : (w₀ : NumberField.InfinitePlace L.1).comap ((τ : L.1 ≃+* L.1) : L.1 →+* L.1) =
      τ⁻¹ • (w₀ : NumberField.InfinitePlace L.1) :=
    AdeleBaseChange.comap_eq_inv_smul τ w₀
  have hu : ((w₀ : NumberField.InfinitePlace L.1).comap
      ((τ : L.1 ≃+* L.1) : L.1 →+* L.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w₀.2
  let u : v.placesOver L.1 := ⟨_, hu⟩
  let j : (u : NumberField.InfinitePlace L.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
    (infCompletionEmbedding ι L).comp
      { AdeleBaseChange.infiniteCompletionMap (τ : L.1 ≃+* L.1) w₀ with
        commutes' := infiniteCompletionMap_algebraMap_completion L τ w₀ }
  have hj : ∀ x : L.1, j (algebraMap L.1 _ x) = ι' x := by
    intro x
    change infCompletionEmbedding ι L (AdeleBaseChange.infiniteCompletionMap
      (τ : L.1 ≃+* L.1) w₀ (algebraMap L.1 _ x)) = ι' x
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap,
      AlgEquiv.coe_toRingEquiv, h x]
  have e := congrArg Subtype.val (eq_infPlaceOfEmbedding ι' L j hj)
  rw [← e]
  exact hcomap

end InfPlace

section Real

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : NumberField.InfinitePlace K.1 // v.IsReal},
    ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)] [IsGalois K.1 L.1]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem apply_gsRestrictGal_gsRealFamily (v : {v : NumberField.InfinitePlace K.1 // v.IsReal})
    (g : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (x : L.1) :
    ιr v ((gsRestrictGal hL (gsRealFamily S ιr v g) x : L.1) : ℚ̄) = g (ιr v (x : ℚ̄)) := by
  rw [show ((gsRestrictGal hL (gsRealFamily S ιr v g) x : L.1) : ℚ̄) =
      ((gsEmbedding hL (gsRestrictGal hL (gsRealFamily S ιr v g) x) :
        maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl, gsEmbedding_gsRestrictGal, gsRealFamily_apply]
  rfl

theorem gsRealDecompGroup_le_stabilizer (v : {v : NumberField.InfinitePlace K.1 // v.IsReal}) :
    gsRealDecompGroup S ιr hL v ≤
      MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) := by
  rintro _ ⟨g, rfl⟩
  rw [mem_stabilizer_iff]
  set τ := gsRestrictGal hL (gsRealFamily S ιr v g)
  have e1 := infPlaceOfEmbedding_eq_inv_smul L (ιr v)
    (((g : AlgebraicClosure v.1.Completion ≃ₐ[v.1.Completion] AlgebraicClosure v.1.Completion).toAlgHom.restrictScalars
      K.1).comp (ιr v)) τ fun x => (apply_gsRestrictGal_gsRealFamily S ιr hL v g x).symm
  rw [infPlaceOfEmbedding_gal_comp] at e1
  change τ • (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) = _
  conv_lhs => rw [e1]
  exact smul_inv_smul τ _

theorem stabilizer_infPlaceOfEmbedding (v : {v : NumberField.InfinitePlace K.1 // v.IsReal}) :
    MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) =
      gsRealDecompGroup S ιr hL v := by
  set w₀ : NumberField.InfinitePlace L.1 := (infPlaceOfEmbedding (ιr v) L).1
  have hle := gsRealDecompGroup_le_stabilizer S ιr hL v
  by_cases hw : w₀.IsReal
  · rw [stabilizer_eq_bot_of_isReal hw] at hle ⊢
    exact (le_bot_iff.1 hle).symm
  · have hcomap : w₀.comap (algebraMap K.1 L.1) = v.1 := by
      have := (infPlaceOfEmbedding (ιr v) L).2
      exact NumberField.InfinitePlace.LiesOver.comap_eq _ _
    have hram : ¬ NumberField.InfinitePlace.IsUnramified K.1 w₀ := by
      rw [NumberField.InfinitePlace.isUnramified_iff, hcomap]
      exact not_or.2 ⟨hw, NumberField.InfinitePlace.not_isComplex_iff_isReal.2 v.2⟩
    have h2 := NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hne : gsRealDecompGroup S ιr hL v ≠ ⊥ := by
      intro hbot
      apply hw
      refine (isReal_infPlaceOfEmbedding_iff L v.2 (ιr v)).2 fun g x => ?_
      have h1 : gsRestrictGal hL (gsRealFamily S ιr v g) = 1 := by
        have hmem : gsRestrictGal hL (gsRealFamily S ιr v g) ∈ gsRealDecompGroup S ιr hL v := ⟨g, rfl⟩
        rw [hbot] at hmem
        exact hmem
      rw [← apply_gsRestrictGal_gsRealFamily S ιr hL v g x, h1]
      rfl
    have hfin : Finite (gsRealDecompGroup S ιr hL v) := inferInstance
    have h1 := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    symm
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)

variable {k N : Type*} [Field k] [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  (σN : Representation k (L.1 ≃ₐ[K.1] L.1) N)


omit [FiniteDimensional k N] [IsGalois K.1 L.1] in
theorem finrank_invariants_comp_bot :
    Module.finrank k (Representation.invariants (σN.comp (⊥ : Subgroup (L.1 ≃ₐ[K.1] L.1)).subtype)) =
      Module.finrank k N := by
  have htop : Representation.invariants (σN.comp (⊥ : Subgroup (L.1 ≃ₐ[K.1] L.1)).subtype) = ⊤ := by
    refine eq_top_iff.2 fun x _ g => ?_
    obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  rw [htop, finrank_top]


open Classical in
theorem finrank_invariants_funPermRep_infinitePlace :
    Module.finrank k ((funPermRep k (L.1 ≃ₐ[K.1] L.1)
        (NumberField.InfinitePlace L.1)).tprod σN).invariants =
      ∑ v : {v : NumberField.InfinitePlace K.1 // v.IsReal},
          Module.finrank k (Representation.invariants (σN.comp (gsRealDecompGroup S ιr hL v).subtype)) +
        Fintype.card {v : NumberField.InfinitePlace K.1 // v.IsComplex} * Module.finrank k N := by
  classical
  let _ := Fintype.ofFinite
    (orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1))
  rw [finrank_invariants_funPermRep_tprod]
  set e := NumberField.InfinitePlace.orbitRelEquiv (k := K.1) (K := L.1)
  set f : orbitRel.Quotient (L.1 ≃ₐ[K.1] L.1) (NumberField.InfinitePlace L.1) → ℕ := fun ω =>
    Module.finrank k (Representation.invariants
      (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) ω.out).subtype))
  rw [← e.symm.sum_comp f, ← Fintype.sum_subtype_add_sum_subtype (fun v : NumberField.InfinitePlace K.1 => v.IsReal)]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hv : e.symm v.1 = Quotient.mk'' (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1) := by
      apply e.injective
      rw [Equiv.apply_symm_apply, NumberField.InfinitePlace.orbitRelEquiv_apply_mk'']
      have := (infPlaceOfEmbedding (ιr v) L).2
      exact (NumberField.InfinitePlace.LiesOver.comap_eq _ _).symm
    change f (e.symm v.1) = _
    rw [hv, ← stabilizer_infPlaceOfEmbedding S ιr hL v]
    have h1 := orbitMover_smul (Γ := L.1 ≃ₐ[K.1] L.1)
      (infPlaceOfEmbedding (ιr v) L : NumberField.InfinitePlace L.1)
    change Module.finrank k (Representation.invariants (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1)
      (Quotient.mk (orbitRel _ _) (infPlaceOfEmbedding (ιr v) L :
        NumberField.InfinitePlace L.1)).out).subtype)) = _
    conv_rhs => rw [← h1]
    rw [finrank_invariants_stabilizer_smul]
  · have hc : ∀ v : {v : NumberField.InfinitePlace K.1 // ¬ v.IsReal}, f (e.symm v.1) = Module.finrank k N := by
      intro v
      have hcx : ((e.symm v.1).out.comap (algebraMap K.1 L.1)).IsComplex := by
        have h := e.apply_symm_apply v.1
        conv_lhs at h => rw [← Quotient.out_eq (e.symm v.1)]
        rw [← Quotient.mk''_eq_mk, NumberField.InfinitePlace.orbitRelEquiv_apply_mk''] at h
        rw [h]
        exact NumberField.InfinitePlace.not_isReal_iff_isComplex.1 v.2
      change Module.finrank k (Representation.invariants
        (σN.comp (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (e.symm v.1).out).subtype)) = _
      rw [stabilizer_eq_bot_of_isComplex hcx, finrank_invariants_comp_bot]
    rw [Finset.sum_congr rfl fun v _ => hc v, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun v =>
      NumberField.InfinitePlace.not_isReal_iff_isComplex)

end Real

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

universe u

noncomputable section

section PoitouTateCount

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G} [Fintype ι]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n}
  {inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ}

theorem natCard_cohomology_two_mul_of_poitouTate (P : PoitouTateDualityHypotheses φ D t inv)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep D M) 0) =
      Nat.card (ptSha φ M 2) * ∏ v, Nat.card (cohomology (Rep.res (φ v).toMonoidHom M) 2) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hex, hsurj⟩ := P.nineTerm M hM
  set F := (ptGlobalToLocal φ M 2).hom.toAddMonoidHom
  set Gm := ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have hMD : ∀ f : dualRep D M, n • f = 0 :=
    nsmul_dualRep_eq_zero (nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv)
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (cohomology (dualRep D M) 0) := P.finite_cohomology (dualRep D M) hMD 0
  have h1 : Nat.card (cohomology M 2) = Nat.card F.range * Nat.card (ptSha φ M 2) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (ptSha φ M 2)]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange F).toEquiv
  have hker : Gm.ker = F.range := by
    ext y
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact hex y
  have h2 : Nat.card (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) 2) =
      Nat.card (cohomology (dualRep D M) 0 →+ QZ) * Nat.card F.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Gm.ker, ← hker]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Gm hsurj).toEquiv
  rw [Nat.card_pi, QZ.card_hom] at h2
  rw [h1, h2]
  ring

end PoitouTateCount

section GSPoitouTate

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)
  (H : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)


omit [Fintype S] [NeZero N] in
instance isDiscreteRep_res_gsFinFamily_dualRep (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) :=
  isDiscreteRep_res_dualRep_of_finite (gsRoots S N) M (gsFinFamily S ιs v)


omit [Fintype S] in
include hS hM in
theorem natCard_gs_local_cohomology_two (v : S) :
    Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 2) =
      Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have : Finite (gsRoots S N) := Finite.of_equiv _ hD.some.symm.toEquiv
  have : Finite (dualRep (gsRoots S N) M) := finite_dualRep
  have : Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
    have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)).ρ.invariants :=
      Subtype.finite (α := dualRep (gsRoots S N) M)
    exact Finite.of_equiv _ (H0Iso (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (dualRep (gsRoots S N) M))).toLinearEquiv.toEquiv.symm
  rw [Nat.card_congr (Equiv.ofBijective _ (bijective_gsLocalPairing S ιs N hD M hM v (show 2 + 0 = 2 from rfl))),
    QZ.card_hom]


include H hM in
theorem natCard_gs_cohomology_two_mul :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep (gsRoots S N) M) 0) =
      Nat.card (ptSha (gsFinFamily S ιs) M 2) *
        ∏ v : S, Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  rw [natCard_cohomology_two_mul_of_poitouTate (gsPoitouTateDualityHypotheses S ιs hS hK H) M hM]
  congr 1
  exact Finset.prod_congr rfl fun v _ => natCard_gs_local_cohomology_two S ιs hS M hM v

end GSPoitouTate

end

end GroundTheory.ProfCoh
end
