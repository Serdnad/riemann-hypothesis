module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCocyclePeriodicNonvanishingSections
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_isDominant_geometricPoint_of_isPreimmersion {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨z, hz⟩ := genericPoints_subset_range_of_isDominant a hη
  let k := AlgebraicClosure (Z.residueField z)
  let t : Sp k ⟶ Z := spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z
  refine ⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩
  have h₁ : z ⤳ z' := by
    rw [← a.isEmbedding.isInducing.specializes_iff, hz]
    exact genericPoint_specializes _
  have h₂ : z ∈ Set.range t :=
    ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩
  exact closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)

theorem isOpenImmersion_of_etale_of_mono_pullback_snd {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by
  let r : pullback q q ⟶ X := pullback.fst q q ≫ q
  have := isNormalScheme_of_smooth r
  have := isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap
  have h : pullback.lift (f := q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j)
        (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
            exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]
  have h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q := by
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q j) h
  have he : pullback.fst q q = pullback.snd q q :=
    ext_of_isDominant_of_isSeparated q pullback.condition _ h'
  have : Mono q := ⟨fun a b hab => by
    rw [← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩
  exact IsOpenImmersion.of_flat_of_mono q

theorem exists_opens_isOpenImmersion_extending_section : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by
  intro X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let W : Y.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  have hy : y ∈ W := mem_irreducibleComponent
  have : IsIntegral W.toScheme := inferInstance
  let q : W.toScheme ⟶ X := W.ι ≫ p
  have := isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap
  have : ∀ z, IsIso ((pullback.fst q j).stalkMap z) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks _
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)
  obtain ⟨k, _, _, t, _⟩ := exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)
  obtain ⟨i, hi⟩ := hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι)
    (by simp only [Category.assoc]; rw [← pullback.condition])
  have he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i :=
    ext_of_isDominant_of_isSeparated p
      (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t
      (by rw [hi, Category.assoc])
  have : Mono (pullback.snd q j ≫ σ i) := by rw [← he]; infer_instance
  have : Mono (pullback.snd q j) := mono_of_mono _ (σ i)
  exact ⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), Smooth p → IsProper p →
      GeometricallyConnected p → Function.Bijective p.appTop.hom := by
  intro K _ X p hs hp hg

  haveI := hs
  haveI := hp
  haveI := hg
  haveI : GeometricallyIntegral p :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X _ p hs hg
  haveI : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  exact ConcreteCategory.bijective_of_isIso p.appTop

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj : ∀ (X : Scheme.{0}) (P Q : Over X), Smooth P.hom → Smooth Q.hom → GeometricallyIntegral P.hom → GeometricallyIntegral Q.hom → Smooth (P ⊗ Q).hom ∧ GeometricallyIntegral (P ⊗ Q).hom ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus P ∩ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus Q ⊆ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus (P ⊗ Q) := by
  intro X P Q hPs hQs hPi hQi
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral P.hom
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral Q.hom
  refine ⟨_root_.GlobalTheory.smooth_tensorObj_hom P Q, _root_.GlobalTheory.geometricallyIntegral_tensorObj_hom P Q, ?_⟩
  intro s hs'
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus, Set.mem_inter_iff, Set.mem_setOf_eq] at hs' ⊢
  obtain ⟨hP, hQ⟩ := hs'
  intro K _ _ t hs
  haveI : IsProper ((Over.pullback t).obj P).hom := hP K t hs
  haveI : IsProper ((Over.pullback t).obj Q).hom := hQ K t hs
  haveI : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left :=
    Functor.map_isIso (Over.forget (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
      (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q)
  have h : IsProper ((CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left ≫
      ((Over.pullback t).obj P ⊗ (Over.pullback t).obj Q).hom) := by
    rw [Over.tensorObj_hom]; infer_instance
  rw [Over.w] at h
  exact h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LieEtale

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {k : Type} [Field k]
    (s : Sp (DualNumber k) ⟶ Y) (x₀ : Sp k ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber k) ⟶ X,
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber k, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  have hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥ := fun a ha =>
    Ideal.mem_sInf.mpr fun {J} hJ => hJ.2.isPrime.mem_of_pow_mem 2 (by
      rw [pow_two, hsq a a ha ha]; exact J.zero_mem)
  refine existsUnique_of_exists_of_unique ?_ fun x₁ x₂ h₁ h₂ =>
    lift_ext_of_unramified f π hπ hj (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint k)) = s (Spec.map π (IsLocalRing.closedPoint k)) :=
      congr($h (IsLocalRing.closedPoint k))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    have hs : Function.Surjective π' := fun c => (hπ c).imp fun b hb => (hπ' b).trans hb
    have hk : IsNilpotent (RingHom.ker (π' : CommRingCat.of (DualNumber k) →+* CommRingCat.of k)) := by
      convert hnil using 2
      exact RingHom.ext hπ'
    exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hs hk⟩

section Formal

variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

def Eig {G : Over S} [GrpObj G] (z : P ⟶ E) (sc : k → (E ⟶ E)) (act : O → (G ⟶ G)) (τ : O → k)
    (v : E ⟶ G) : Prop :=
  z ≫ v = 1 ∧ ∀ a, v ≫ act a = sc (τ a) ≫ v

theorem comp_listProd {G : Over S} [GrpObj G] (z : P ⟶ E) (l : List (E ⟶ G))
    (h : ∀ u ∈ l, z ≫ u = 1) : z ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one z
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, h u (by simp), ih fun w hw => h w (by simp [hw]),
      _root_.mul_one]

theorem ofFn_prod_comp {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod :=
  (map_list_prod (IsMonHom.monoidHom ψ E) _).trans (by rw [List.map_ofFn]; rfl)

theorem mult_iff {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by
  have htan : ∀ v : E ⟶ A, z ≫ v = 1 → z ≫ v ≫ ψ = 1 := fun v hv => by
    rw [← Category.assoc, hv, MonObj.one_comp]
  have hinj : ∀ v v' : E ⟶ A, z ≫ v = 1 → z ≫ v' = 1 → v ≫ ψ = v' ≫ ψ → v = v' :=
    fun v v' hv hv' e => (H _ (htan v' hv')).unique ⟨hv, e⟩ ⟨hv', rfl⟩
  have hsc : ∀ (c : k) (v : E ⟶ A), z ≫ v = 1 → z ≫ sc c ≫ v = 1 := fun c v hv => by
    rw [← Category.assoc, hz, hv]
  have heig : ∀ v : E ⟶ A, z ≫ v = 1 → (Eig z sc a τ v ↔ Eig z sc b τ (v ≫ ψ)) := fun v hv => by
    refine ⟨fun h => ⟨htan v hv, fun c => ?_⟩, fun h => ⟨hv, fun c => hinj _ _ ?_ (hsc _ _ hv) ?_⟩⟩
    · rw [Category.assoc, ← hab, ← Category.assoc, h.2, Category.assoc]
    · have := ha c
      rw [← Category.assoc, hv, MonObj.one_comp]
    · rw [Category.assoc, hab, ← Category.assoc, h.2, Category.assoc]
  have hcomb : ∀ (v : Fin n → (E ⟶ A)) (w : E ⟶ A), (∀ i, z ≫ v i = 1) → z ≫ w = 1 →
      ∀ c : Fin n → k, (w = (List.ofFn fun i => sc (c i) ≫ v i).prod ↔
        w ≫ ψ = (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod) := fun v w hv hw c => by
    have e : (List.ofFn fun i => sc (c i) ≫ v i).prod ≫ ψ =
        (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod := by
      simp only [ofFn_prod_comp, Category.assoc]
    rw [← e]
    refine ⟨fun h => by rw [← h], hinj _ _ hw (comp_listProd z _ fun u hu => ?_)⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hsc _ _ (hv i)
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨fun i => v i ≫ ψ, fun i => (heig _ (hv i).1).mp (hv i), fun w hw => ?_⟩
    obtain ⟨w', ⟨hw', rfl⟩, -⟩ := H w hw.1
    exact (existsUnique_congr (hcomb v w' (fun i => (hv i).1) hw')).mp (h w' ((heig _ hw').mpr hw))
  · rintro ⟨v, hv, h⟩
    choose v' hv' using fun i => (H (v i) (hv i).1).exists
    obtain rfl : v = fun i => v' i ≫ ψ := funext fun i => (hv' i).2.symm
    refine ⟨v', fun i => (heig _ (hv' i).1).mpr (hv i), fun w hw => ?_⟩
    exact (existsUnique_congr (hcomb v' w (fun i => (hv' i).1) hw.1)).mpr
      (h _ ((heig _ hw.1).mp hw))

end Formal

section Dual

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)

def epsPtZero : Over.mk x ⟶ epsPt x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) =
      RingHom.id k := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

def epsPtScale (c : k) : epsPt x ⟶ epsPt x :=
  Over.homMk (spMap (epsScale c)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).commutes r)

theorem epsPtZero_epsPtScale (c : k) : epsPtZero x ≫ epsPtScale x c = epsPtZero x := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem isLieEigen_iff (v : epsPt x ⟶ G) :
    IsLieEigen act x τ v ↔ Eig (epsPtZero x) (epsPtScale x) act.act τ v :=
  ⟨fun h => ⟨Over.OverMorphism.ext h.1, fun a => Over.OverMorphism.ext (h.2 a)⟩,
    fun h => ⟨congrArg (·.left) h.1, fun a => congrArg (·.left) (h.2 a)⟩⟩

theorem lieMult_iff (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by
  simp only [LieMult, isLieEigen_iff]
  refine exists_congr fun v => and_congr_right fun _ => forall_congr' fun w =>
    imp_congr_right fun _ => existsUnique_congr fun c => ⟨?_, fun h => ⟨_, fun _ => rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i => epsPtScale x (c i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (hu i)
  rfl

theorem existsUnique_tangent_lift {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift ψ.left w.left (1 : Over.mk x ⟶ A).left
    (congrArg (·.left) ((MonObj.one_comp ψ).trans hw.symm))
  refine ⟨Over.homMk v ?_, ⟨Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩,
    fun v' hv' => Over.OverMorphism.ext
      (hu _ ⟨congrArg (·.left) hv'.1, congrArg (·.left) hv'.2⟩)⟩
  rw [← Over.w ψ, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h₂).trans (Over.w w)

end Dual

theorem lieMult_iff_of_etale :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n := by
  intro O _ S A B _ _ ψ a b _ _ hab k _ x τ n
  rw [lieMult_iff, lieMult_iff]
  exact mult_iff ψ _ _ (epsPtZero_epsPtScale x) a.act b.act a.hom hab τ
    (existsUnique_tangent_lift x ψ) n

end GlobalTheory.LieEtale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.quotient_isReduced_isNormal_flat_of_invariant_sections : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X → IsReduced X') ∧ (IsLocallyNoetherian X → IsNormalScheme X → IsNormalScheme X') ∧ ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (s' : X' ⟶ Sp R), Flat (π ≫ s') → Flat s' := by
  first | exact @GlobalTheory.quotient_isReduced_isNormal_flat | exact GlobalTheory.quotient_isReduced_isNormal_flat | (intros; apply GlobalTheory.quotient_isReduced_isNormal_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  first | exact @GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | exact GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | (intros; apply GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend <;> assumption)
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.exists_periodic_smooth_solution_torus_system : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  first | exact @GlobalTheory.torus_elliptic_system_solvable | exact GlobalTheory.torus_elliptic_system_solvable | (intros; apply GlobalTheory.torus_elliptic_system_solvable <;> assumption)
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  first | exact @GlobalTheory.PeriodSymm.period_symm | exact GlobalTheory.PeriodSymm.period_symm | (intros; apply GlobalTheory.PeriodSymm.period_symm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isAffineOpen_le_of_isQProjOver :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      ∀ (F : Set X) (U : X.Opens), F.Finite → F ⊆ U →
        ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ V ≤ U := by
  intro R _ X s hs F U hF hFU
  haveI := FiniteSubsetsInAffineOpens.of_isQProjOver hs
  exact FiniteSubsetsInAffineOpens.exists_isAffineOpen_le hF U hFU

end GlobalTheory
end

section

namespace GlobalTheory.CMGeneratorSquareModuli

open NumberField

theorem cm_generator_sq_quadratic_eq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ k : ℤ, H.w0 * H.w0 = H.w0 - (k : NumberField.RingOfIntegers E) := by
  have hm := H.d_mod
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (H.d : ℤ) + 1 = 4 * k := ⟨((H.d : ℤ) + 1) / 4, by omega⟩
  refine ⟨k, ?_⟩
  have hkc : (H.d : NumberField.RingOfIntegers E) + 1 = 4 * (k : NumberField.RingOfIntegers E) := by
    have := congrArg (fun z : ℤ => (z : NumberField.RingOfIntegers E)) hk
    push_cast at this
    exact this
  have h4 : (4 : NumberField.RingOfIntegers E) * (H.w0 * H.w0 - (H.w0 - (k : NumberField.RingOfIntegers E))) = 0 := by
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hkc
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E},
    a ∈ Algebra.adjoin ℤ ({ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H} : Set (NumberField.RingOfIntegers E)) →
    ∃ u v : ℤ, a = (u : NumberField.RingOfIntegers E) + (v : NumberField.RingOfIntegers E) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  obtain ⟨k, hk⟩ := cm_generator_sq_quadratic_eq H
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    exact ⟨u1 + u2, v1 + v2, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    refine ⟨u1 * u2 - v1 * v2 * k, u1 * v2 + u2 * v1 + v1 * v2, ?_⟩
    push_cast
    linear_combination ((v1 : NumberField.RingOfIntegers E) * v2) * hk

end GlobalTheory.CMGeneratorSquareModuli
end
