module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle029
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtaleComp

theorem isIndEtale_of_model (X E Y G F : Type) [CommRing X] [CommRing E] [CommRing Y] [CommRing G]
    [CommRing F] [Algebra X E] [Algebra X Y] [Algebra E Y] [IsScalarTower X E Y]
    [Algebra.Etale X E] [Algebra E G] [Algebra.Etale E G] [Algebra Y F]
    (e : Y ⊗[E] G ≃ₐ[Y] F) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap X Y)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap Y F).comp (algebraMap X Y)) := by
  have h1 := GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale X E Y h
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left E Y G h1
  letI : Algebra G F :=
    ((e : Y ⊗[E] G →+* F).comp (Algebra.TensorProduct.includeRight : G →ₐ[E] Y ⊗[E] G).toRingHom).toAlgebra
  let e' : G ⊗[E] Y ≃ₐ[G] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm E G Y).toRingEquiv.trans e.toRingEquiv)
      (fun g => rfl)
  have h3 := GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e' h2
  have h4 : RingHom.Etale ((algebraMap E G).comp (algebraMap X E)) :=
    RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance)
  have h5 := GlobalTheory.EtC.isIndEtale_comp_etale _ h4 _ h3
  have h6 : (algebraMap Y F).comp (algebraMap X Y) =
      (algebraMap G F).comp ((algebraMap E G).comp (algebraMap X E)) := by
    ext x
    change _ = e ((1 : Y) ⊗ₜ[E] algebraMap E G (algebraMap X E x))
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply E Y (Y ⊗[E] G),
      e.commutes, ← IsScalarTower.algebraMap_apply X E Y]
    rfl
  rw [h6]
  exact h5

theorem isIndEtale_etale_comp {X Y F : Type} [CommRing X] [CommRing Y] [CommRing F]
    (f : X →+* Y) (g : Y →+* F) (hf : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f) (hg : g.Etale) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  have hf' := hf
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hf'
  letI : Algebra Y F := g.toAlgebra
  haveI : Algebra.Etale Y F := hg
  obtain ⟨i, G, _, _, hG, ⟨e⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D (Cocone.mk (CommRingCat.of Y) t) hs F
  letI : Algebra (D.obj i) Y := (t.app i).hom.toAlgebra
  letI : Algebra X (D.obj i) := (s.app i).hom.toAlgebra
  letI : Algebra X Y := f.toAlgebra
  haveI : Algebra.Etale X (D.obj i) := (hj i).1
  haveI : IsScalarTower X (D.obj i) Y := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun φ : CommRingCat.of X ⟶ CommRingCat.of Y => φ.hom x) (hj i).2).symm)
  exact isIndEtale_of_model X (D.obj i) Y G F e hf

theorem isIndEtale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  intro X Y Z _ _ _ f g hf hg
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom f) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · exact isIndEtale_etale_comp (F := D.obj j) f (s.app j).hom hf (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom f ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp f)
    rw [h2]
    rfl

end GlobalTheory.IndEtaleComp
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.StalkNoeth

theorem noeth_of_directed_subrings : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S :=
  GlobalTheory.T.isNoetherianRing_of_directed_pure_union'

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) :=
  GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale

noncomputable def stageHom {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) : Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)) →+* O :=
  IsLocalization.lift (M := ((maximalIdeal O).comap (v : W →+* O)).primeCompl) (g := (v : W →+* O))
    (fun y => by by_contra hy; exact y.2 hy)

theorem stageHom_algebraMap {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) (w : W) : stageHom v (algebraMap W _ w) = v w :=
  IsLocalization.lift_eq _ _

theorem stage_props {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    [Algebra.Etale A W] (hO : IndEt A O) (v : W →ₐ[A] O) :
    (∀ J : Ideal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))), (J.map (stageHom v)).comap (stageHom v) = J) ∧
      (maximalIdeal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)))).map (stageHom v) = maximalIdeal O := by
  set q := (maximalIdeal O).comap (v : W →+* O) with hq
  letI : Algebra W O := (v : W →+* O).toAlgebra
  haveI : IsScalarTower A W O := IsScalarTower.of_algebraMap_eq (fun a => (v.commutes a).symm)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := isIndEtale_of_etale_of_isIndEtale A W O hO
  letI : Algebra (Localization.AtPrime q) O := (stageHom v).toAlgebra
  haveI : IsScalarTower W (Localization.AtPrime q) O :=
    IsScalarTower.of_algebraMap_eq (fun w => (stageHom_algebraMap v w).symm)
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime q) O) :=
    GlobalTheory.StrictHensUnion.indEtale_over_localization W (Localization.AtPrime q) O q.primeCompl h1
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) O) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨w, y⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl a
    rw [IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q]
    have hu : IsUnit (v (y : W)) := by
      by_contra hy
      exact y.2 hy
    have h3 : algebraMap (Localization.AtPrime q) O (IsLocalization.mk' (Localization.AtPrime q) w y) * v y = v w := by
      rw [← stageHom_algebraMap v (y : W), ← stageHom_algebraMap v w]
      change stageHom v _ * stageHom v _ = stageHom v _
      rw [← map_mul, IsLocalization.mk'_spec]
    have h4 : IsUnit (v w) := h3 ▸ ha.mul hu
    intro hw
    exact hw h4
  obtain ⟨hfl, hmax, -⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable (Localization.AtPrime q) O h2
  haveI : Module.FaithfullyFlat (Localization.AtPrime q) O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨fun J => Ideal.comap_map_eq_self_of_faithfullyFlat J, hmax⟩

theorem stage_le {A W W' O : Type} [CommRing A] [CommRing W] [CommRing W'] [CommRing O] [IsLocalRing O] [Algebra A W]
    [Algebra A W'] [Algebra A O] (v : W →ₐ[A] O) (v' : W' →ₐ[A] O) (k : W →ₐ[A] W') (hk : v'.comp k = v) :
    (stageHom v).range ≤ (stageHom v').range := by
  have hle : ((maximalIdeal O).comap (v : W →+* O)).primeCompl ≤
      ((maximalIdeal O).comap (v' : W' →+* O)).primeCompl.comap (k : W →+* W') := by
    intro y hy
    change v' (k y) ∉ maximalIdeal O
    rw [← AlgHom.comp_apply, hk]
    exact hy
  let ψ := IsLocalization.map (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (Localization.AtPrime ((maximalIdeal O).comap (v' : W' →+* O))) (k : W →+* W') hle
  have hψ : (stageHom v').comp ψ = stageHom v := by
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) ((maximalIdeal O).comap (v : W →+* O)).primeCompl ?_
    ext w
    simp only [RingHom.comp_apply, ψ, IsLocalization.map_eq, stageHom_algebraMap]
    rw [← hk]
    rfl
  rw [← hψ]
  rintro _ ⟨x, rfl⟩
  exact ⟨ψ x, rfl⟩

theorem isNoetherianRing_of_indEt : ∀ (A O : Type) [CommRing A] [IsNoetherianRing A] [CommRing O] [IsLocalRing O]
    [Algebra A O], IndEt A O → IsNoetherianRing O := by
  intro A O _ _ _ _ _ hO
  let ι := {T : Subring O // ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (v : W →ₐ[A] O),
    T = (stageHom v).range}
  have fac : ∀ (Z : Type) [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z] (g : Z →ₐ[A] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (u : Z →ₐ[A] W) (v : W →ₐ[A] O),
        v.comp u = g := fun Z _ _ _ g => GlobalTheory.IndEtaleLocal.exists_etale_factor hO g
  have mem : ∀ x : O, ∃ T : ι, x ∈ T.1 := by
    intro x
    obtain ⟨W, _, _, _, u, v, huv⟩ := fac (Polynomial A) (Polynomial.aeval x)
    refine ⟨⟨_, W, inferInstance, inferInstance, inferInstance, v, rfl⟩, algebraMap W _ (u Polynomial.X), ?_⟩
    rw [stageHom_algebraMap]
    have := DFunLike.congr_fun huv Polynomial.X
    simpa using this
  haveI : Nonempty ι := ⟨(mem 0).choose⟩
  haveI : IsDirected ι (· ≤ ·) := by
    refine ⟨fun T1 T2 => ?_⟩
    obtain ⟨T1, W1, _, _, _, v1, rfl⟩ := T1
    obtain ⟨T2, W2, _, _, _, v2, rfl⟩ := T2
    haveI : Algebra.FinitePresentation A (TensorProduct A W1 W2) := Algebra.FinitePresentation.trans A W1 _
    obtain ⟨W3, _, _, _, u, v3, huv⟩ := fac (TensorProduct A W1 W2) (Algebra.TensorProduct.productMap v1 v2)
    refine ⟨⟨_, W3, inferInstance, inferInstance, inferInstance, v3, rfl⟩, ?_, ?_⟩
    · exact stage_le v1 v3 (u.comp Algebra.TensorProduct.includeLeft) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_left v1 v2)
    · exact stage_le v2 v3 (u.comp Algebra.TensorProduct.includeRight) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_right v1 v2)
  refine noeth_of_directed_subrings O ι (fun T => T.1) (fun _ _ h => h) mem ?_ ?_ ?_
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    haveI : IsNoetherianRing W := Algebra.FiniteType.isNoetherianRing A W
    haveI : IsNoetherianRing (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) :=
      IsLocalization.isNoetherianRing ((maximalIdeal O).comap (v : W →+* O)).primeCompl _ inferInstance
    exact isNoetherianRing_range (stageHom v)
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    obtain ⟨-, hmax⟩ := stage_props hO v
    refine le_antisymm Ideal.map_comap_le ?_
    conv_lhs => rw [← hmax]
    rw [Ideal.map_le_iff_le_comap]
    intro l hl
    have h1 : stageHom v l ∈ maximalIdeal O := hmax.le (Ideal.mem_map_of_mem _ hl)
    have h2 : (⟨stageHom v l, l, rfl⟩ : (stageHom v).range) ∈ (maximalIdeal O).comap (stageHom v).range.subtype := h1
    exact Ideal.mem_map_of_mem _ h2
  · rintro ⟨T, W, _, _, _, v, rfl⟩ J
    obtain ⟨hc, -⟩ := stage_props hO v
    refine le_antisymm ?_ Ideal.le_comap_map
    intro x hx
    obtain ⟨y, rfl⟩ := (stageHom v).rangeRestrict_surjective x
    have hJ : J = (J.comap (stageHom v).rangeRestrict).map (stageHom v).rangeRestrict :=
      (Ideal.map_comap_of_surjective _ (stageHom v).rangeRestrict_surjective J).symm
    have h2 : stageHom v y ∈ (J.comap (stageHom v).rangeRestrict).map (stageHom v) := by
      rw [hJ, Ideal.map_map] at hx
      exact hx
    have h3 := (hc (J.comap (stageHom v).rangeRestrict)).le h2
    exact h3

theorem isNoetherianRing_of_isStalk : ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (O : Type) [CommRing O]
    [IsLocalRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of B)), IsStalk O s → IsNoetherianRing O := by
  intro B _ _ O _ _ s hs
  obtain ⟨_, -, hind, -⟩ := isStalk_affine B O s hs
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  exact isNoetherianRing_of_indEt B O hind

end GlobalTheory.StalkNoeth
end

section

noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

theorem monic_eq_prod_of_aic {T : Type} [CommRing T] (hT : AIC T) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∃ s : Multiset T, f = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro f hf hn
    exact ⟨0, by simpa using Polynomial.eq_one_of_monic_natDegree_zero hf hn⟩
  | succ n ih =>
    intro f hf hn
    rcases subsingleton_or_nontrivial T with hT0 | hT0
    · have h0 : f = 0 := Subsingleton.elim _ _
      rw [h0, natDegree_zero] at hn; omega
    obtain ⟨a, ha⟩ := hT f hf (by omega)
    have hmul : (X - C a) * (f /ₘ (X - C a)) = f := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hf)
    have hd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    obtain ⟨s, hs⟩ := ih _ hq hd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem henselianLocalRing_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₁ _ := by
    classical
    obtain ⟨s, hs⟩ := monic_eq_prod_of_aic hT _ f hf rfl
    have hev : f.eval a₀ = (s.map fun a => a₀ - a).prod := by
      conv_lhs => rw [hs]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun a _ => by simp)
    rw [hev] at h₁
    obtain ⟨c, hc, hcm⟩ := ((IsLocalRing.maximalIdeal.isMaximal T).isPrime.multiset_prod_mem_iff_exists_mem _).1 h₁
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hc
    refine ⟨a, ?_, ?_⟩
    · show f.eval a = 0
      rw [hs, Polynomial.eval_multiset_prod, Multiset.map_map]
      exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp⟩)
    · rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hcm

theorem isAlgClosed_residueField_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨q, hqp, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective (p.coeff n)) hp
  have hdeg : 0 < q.natDegree := by
    rw [hqd]; exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hT q hqm hdeg
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

theorem sh_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) : SH T := by
  haveI := isAlgClosed_residueField_of_aic hT
  exact ⟨henselianLocalRing_of_aic hT, inferInstance⟩

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Fibres
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] {X : Scheme.{0}}

abbrev spFib (p : X ⟶ Spec (CommRingCat.of T)) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T)))

abbrev spInc (p : X ⟶ Spec (CommRingCat.of T)) : spFib p ⟶ X := pullback.fst _ _

abbrev genFib (p : X ⟶ Spec (CommRingCat.of T)) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))))

abbrev genInc (p : X ⟶ Spec (CommRingCat.of T)) : genFib p ⟶ X := pullback.fst _ _

end Fibres

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Torsion
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T]

theorem eqv_spInc (hE2 : E2) (hT : AIC T) (q : ℕ) (hq : IsUnit (q : T)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of T)) [IsProper p] (i : ℤ) : Eqv (ZMod q) (sch.map (spInc p)) (tw q i) :=
  hE2 q T (sh_of_aic hT) hq p i

theorem eqv_genInc (hE3 : E3) (hT : AIC T) (q : ℕ) [NeZero q] (hq : IsUnit (q : T)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (genInc p)) (tw q i) :=
  hE3 q T hT hq p i

end Torsion

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Adic
variable (l : ℕ) [Fact l.Prime]

theorem pullHl_bijective {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hf : ∀ k : ℕ, Function.Bijective (pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHl l f n i) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext k
    exact (hf k).1 (congrArg (fun z => z.1 k) hxy)
  · intro y
    choose x hx using fun k => (hf k).2 (y.1 k)
    refine ⟨⟨x, fun k => (hf k).1 ?_⟩, Subtype.ext (funext hx)⟩
    change pull _ f _ n (red (l ^ (k + 1)) (l ^ k) E' n i (x (k + 1))) = pull _ f _ n (x k)
    rw [pull_red, hx, hx]
    exact y.2 k

theorem pullHQ_bijective {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hf : ∀ k : ℕ, Function.Bijective (pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHQ l f n i) := by
  let e := LinearEquiv.ofBijective (pullHl l f n i) (pullHl_bijective l f n i hf)
  have h : pullHQ l f n i = (e.baseChange ℤ_[l] ℚ_[l] _ _).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    rfl
  rw [h]
  exact (e.baseChange ℤ_[l] ℚ_[l] _ _).bijective

end Adic

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Main
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (l : ℕ) [Fact l.Prime]

end Main

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

theorem aic_of_isAlgClosed' (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := fun p hp hd =>
  IsAlgClosed.exists_root p (by rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')

end GlobalTheory.GenusTwoPureComparison.Cmp

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

theorem _root_.GlobalTheory.T.om_quotient_twist_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), OmQuot μ σ τ ↔ OmQuot 1 (twist σ (detChar (Fin r) μ⁻¹)) (twist τ (detChar (Fin n) μ)) := by
  first | exact @GlobalTheory.OmTwist.main | exact GlobalTheory.OmTwist.main | (intros; apply GlobalTheory.OmTwist.main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

theorem _root_.GlobalTheory.T.om_quotient_trivial_rank_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), r = 0 ∨ n = 0 → σ.IsIrreducible → τ.IsIrreducible → OmQuot 1 σ τ → Nonempty (σ.Equiv (detRep (Fin r) (1 : kˣ →* ℂˣ))) ∧ Nonempty (τ.Equiv (detRep (Fin n) (1 : kˣ →* ℂˣ))) := by
  first | exact @GlobalTheory.HoweZero.main | exact GlobalTheory.HoweZero.main | (intros; apply GlobalTheory.HoweZero.main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

theorem _root_.GlobalTheory.T.om_quotient_transpose_inverse : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k), (∀ g, (θr g).val = (g⁻¹).val.transpose) → (∀ g, (θn g).val = (g⁻¹).val.transpose) → OmQuot 1 σ τ → OmQuot 1 (τ.comp θn : Representation ℂ (GL (Fin n) k) W) (σ.comp θr : Representation ℂ (GL (Fin r) k) V) := by
  first | exact @GlobalTheory.omQuot_transpose | exact GlobalTheory.omQuot_transpose | (intros; apply GlobalTheory.omQuot_transpose <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Tr

def SplitBy {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) {m : ℕ} (s : Fin m → (V ⟶ Z)) : Prop :=
  ∃ hs : ∀ j, s j ≫ f = y, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
    ∐ (fun _ : Fin m => V) ⟶ pullback f y)

def Splits {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) : Prop :=
  ∃ (m : ℕ) (s : Fin m → (V ⟶ Z)), SplitBy f y s

def splitSieve {Z X S : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) : Sieve S :=
  Sieve.generate (fun V (v : V ⟶ S) => Splits f (v ≫ x))

theorem IsTransfer.apply_of_splitBy (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z}
    (ht : IsTransfer R f t) {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)} (hs : SplitBy f y s) :
    (free R).map (yoneda.map y) ≫ t = ∑ j, (free R).map (yoneda.map (s j)) :=
  ht V y m s hs.1 hs.2

end GlobalTheory.EtC.Tr
end
end

section


theorem _root_.GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice : ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  first | exact @GlobalTheory.weyl_rename_castLE_mem | exact GlobalTheory.weyl_rename_castLE_mem | (intros; apply GlobalTheory.weyl_rename_castLE_mem <;> assumption)
end
