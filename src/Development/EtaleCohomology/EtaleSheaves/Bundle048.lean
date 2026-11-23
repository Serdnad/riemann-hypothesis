module

public import Development.EtaleCohomology.EtaleSheaves.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle033
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwSecPf

def ρ {B : Type} [CommRing B] (U : Over (Spec (CommRingCat.of B))) : B →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ U.hom.appTop).hom

abbrev Pr (q : ℕ) (k : ℤ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Over.forget X).op ⋙ (Scheme.Γ ⋙ twF q k)

abbrev Cst (q : ℕ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Functor.const _).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))

def gen {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) (U : Over (Spec (CommRingCat.of B))) :
    (Pr q k _).obj (op U) :=
  Submodule.Quotient.mk (Finsupp.single (Prim.map (ρ U) ζ) 1)

theorem gen_map {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) {U V : Over (Spec (CommRingCat.of B))}
    (f : V ⟶ U) : ((Pr q k _).map f.op).hom (gen ζ k U) = gen ζ k V := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single _ _)) = _
  rw [Finsupp.mapDomain_single]
  have h : Prim.map (Scheme.Γ.map f.left.op).hom (Prim.map (ρ U) ζ) = Prim.map (ρ V) ζ := by
    apply Subtype.ext
    change (Scheme.Γ.map f.left.op).hom (ρ U ζ.1) = ρ V ζ.1
    simp only [ρ]
    rw [← Over.w f]
    first | rfl | simp [Scheme.Hom.comp_appTop] | simp
  exact congrArg (fun z => Submodule.Quotient.mk (p := twRel q k _) (Finsupp.single z (1 : ULift.{1} (ZMod q)))) h

def cmap {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) : Cst q _ ⟶ Pr q k (Spec (CommRingCat.of B)) where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (gen ζ k U.unop))
  naturality := by
    intro U V f
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k V.unop)) (1 : ULift.{1} (ZMod q)) =
      ((Pr q k _).map f).hom ((LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k U.unop)) (1 : ULift.{1} (ZMod q)))
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (gen_map ζ k f.unop).symm

def LeafTwLB : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  IsIso ((presheafToSheaf (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (ModuleCat.{1} (ULift.{1} (ZMod q)))).map
    (cmap ζ k))

theorem LeafTwSec_of (h : LeafTwLB) : LateralTheory.E.LeafTwistPf.LeafTwSec := by
  intro q _ B _ ζ i j
  let K := (Over.forget (Spec (CommRingCat.of B))).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{1} (ULift.{1} (ZMod q))) (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) Scheme.etaleTopology
  haveI := h q B ζ i
  haveI := h q B ζ j
  let Φ := (K.app (Scheme.Γ ⋙ twF q i)).symm ≪≫ (asIso ((presheafToSheaf _ _).map (cmap ζ i))).symm ≪≫
    asIso ((presheafToSheaf _ _).map (cmap ζ j)) ≪≫ K.app (Scheme.Γ ⋙ twF q j)
  let Ψ := (sheafToPresheaf _ _).mapIso Φ
  refine ⟨fun U x => (Ψ.app (op (Over.mk x))).toLinearEquiv, ?_⟩
  intro V U g x s
  have := congrArg (fun f => f.hom s) (Ψ.hom.naturality (Over.homMk g : Over.mk (g ≫ x) ⟶ Over.mk x).op)
  exact this

def LeafTwSurj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

def LeafTwInj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallyInjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

theorem LeafTwLB_of (hI : LeafTwInj) (hS : LeafTwSurj) : LeafTwLB := by
  intro q _ B _ ζ k
  haveI := hI q B ζ k
  haveI := hS q B ζ k
  exact (GrothendieckTopology.W_iff _ _).1 (GrothendieckTopology.W_of_isLocallyBijective _ _)

theorem LeafTwSec_of' (hI : LeafTwInj) (hS : LeafTwSurj) : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LeafTwSec_of (LeafTwLB_of hI hS)

end LateralTheory.E.LeafTwSecPf
end
end

section

open AlgebraicGeometry CategoryTheory Topology

namespace LateralTheory.E.LeafFibreFieldPf

open Cardinal IntermediateField in
theorem alg_part (k K : Type) [Field k] [Field K] [Algebra k K] (S : Finset K)
    (hgen : IntermediateField.adjoin k (S : Set K) = ⊤) (d : ℕ) (hd : Algebra.trdeg k K = d + 1) :
    ∃ (F : IntermediateField k K) (s : Finset F) (t : K), s.card ≤ d ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
      FiniteDimensional (IntermediateField.adjoin F {t}) K := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k K
  have hcard : #B = ((d + 1 : ℕ) : Cardinal) := by
    rw [hB.cardinalMk_eq_trdeg, hd]; push_cast; rfl
  obtain ⟨T, hTB, hTc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  set T' := T.erase a with hT'
  let F : IntermediateField k K := IntermediateField.adjoin k (T' : Set K)
  let sF : Finset F := T'.attach.image fun x => ⟨x.1, IntermediateField.subset_adjoin k _ x.2⟩
  have hsF : (F.val '' (sF : Set F)) = (T' : Set K) := by
    ext y; simp [sF]; intro h; exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr h)
  refine ⟨F, sF, a, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem haT, hTc]; simp
  · have hmem : ∀ y : F, y ∈ IntermediateField.adjoin k (sF : Set F) := by
      intro y
      have : (y : K) ∈ (IntermediateField.adjoin k (sF : Set F)).map F.val := by
        rw [IntermediateField.adjoin_map, hsF]; exact y.2
      rw [← SetLike.mem_coe, IntermediateField.coe_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    exact ⟨fun y => by
      have := isAlgebraic_algebraMap (R := IntermediateField.adjoin k (sF : Set F)) (A := F) ⟨y, hmem y⟩
      exact this⟩
  · have hind := hB.1
    have hnot : (⟨a, hTB ▸ haT⟩ : B) ∉ {i : B | (i : K) ≠ a} := by simp
    have htr := hind.transcendental_adjoin hnot
    have himg : (Subtype.val '' {i : B | (i : K) ≠ a}) = (T' : Set K) := by
      ext y; simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, hT', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, ← hTB]
      tauto
    rw [himg, ← IntermediateField.transcendental_adjoin_iff] at htr
    exact htr
  ·
    set L := IntermediateField.adjoin F {a} with hL
    have hBT : (B : Set K) = (T : Set K) := hTB.symm
    have halgB := hB.isAlgebraic_field
    rw [Subtype.range_coe] at halgB
    set E := IntermediateField.adjoin k B with hE
    have hEL : ∀ x ∈ E, x ∈ L := by
      intro x hx
      have hle : E ≤ L.restrictScalars k := by
        rw [hE, IntermediateField.adjoin_le_iff]
        intro b hb
        rw [← hTB] at hb
        by_cases hba : b = a
        · subst hba; exact IntermediateField.mem_adjoin_simple_self F b
        · have hbF : b ∈ F := IntermediateField.subset_adjoin k _ (by simp [hT', hba, hb])
          exact (IntermediateField.algebraMap_mem L (⟨b, hbF⟩ : F))
      exact hle hx
    let g : E →+* L :=
      { toFun := fun x => ⟨x.1, hEL x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    let _ : Algebra E L := g.toAlgebra
    have : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint : ∀ x : K, IsIntegral L x := fun x =>
      ((halgB.isAlgebraic x).extendScalars g.injective).isIntegral
    have hfd := IntermediateField.finiteDimensional_adjoin (K := L) (S := (S : Set K)) (fun x _ => hint x)
    have htop : IntermediateField.adjoin L (S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hgen ▸ trivial
      let M : IntermediateField k K :=
        { carrier := (IntermediateField.adjoin L (S : Set K) : Set K)
          mul_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).mul_mem ha hb
          add_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).add_mem ha hb
          inv_mem' := fun _ hx => (IntermediateField.adjoin L (S : Set K)).inv_mem hx
          algebraMap_mem' := fun c => by
            have h1 := IntermediateField.algebraMap_mem (IntermediateField.adjoin L (S : Set K))
              (⟨algebraMap F K (algebraMap k F c), IntermediateField.algebraMap_mem L _⟩ : L)
            rw [IsScalarTower.algebraMap_apply k F K]
            exact h1 }
      have hle : IntermediateField.adjoin k (S : Set K) ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        show y ∈ (IntermediateField.adjoin L (S : Set K) : Set K)
        exact IntermediateField.subset_adjoin L _ hy
      exact (hle hx : x ∈ (IntermediateField.adjoin L (S : Set K) : Set K))
    rw [htop] at hfd
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv

theorem gen_top (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ S : Finset (FractionRing A), IntermediateField.adjoin k (S : Set (FractionRing A)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType k A›).out
  refine ⟨s.image (algebraMap A (FractionRing A)), ?_⟩
  have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈
      IntermediateField.adjoin k ((s.image (algebraMap A (FractionRing A)) : Finset _) : Set (FractionRing A)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : algebraMap A (FractionRing A) a ∈ (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A (FractionRing A)) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    simpa [Finset.coe_image] using h1
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  exact div_mem (hA a) (hA b)

theorem dimX_eq (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (e : ℕ)
    (he : letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
      Algebra.trdeg k X.functionField = e) :
    topologicalKrullDim X = e := by
  have h := GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := (Set.univ : Set X))
    ⟨genericPoint X, trivial⟩ (d := (e : WithBot ℕ∞)) (fun x _ => by
      obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p x
      refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
      rw [Set.inter_univ, GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
      have hA := GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans he)
      rw [← hA]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  rw [← h]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (e := (id : X → X)) IsEmbedding.id (Set.range_id)).symm

theorem LeafFibreField_of : LateralTheory.E.LeafCurveVCut.LeafFibreField := by
  intro k _ X _ p _ hd
  letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p (genericPoint X)
  obtain ⟨e, -, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  have hdim := dimX_eq k p e (htr.symm.trans he2)
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    cases e with
    | zero => rw [hdim] at hd; simp at hd
    | succ d => exact ⟨d, rfl⟩
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have htrK : Algebra.trdeg k (FractionRing A) = d + 1 := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (FractionRing A), he2]; push_cast; rfl
  obtain ⟨S, hS⟩ := gen_top k A
  obtain ⟨F, s, t, hs, halg, ht, hfin⟩ := alg_part k (FractionRing A) S hS d htrK
  refine ⟨F, inferInstance, inferInstance, FractionRing A, inferInstance, inferInstance, d, s, t,
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ j, ?_, hs, halg, ht, hfin, ?_, ?_⟩
  · rw [hdim]; exact_mod_cast Nat.lt_succ_self d
  · rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  · obtain ⟨q, hq⟩ := hx
    obtain ⟨pt⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
    refine ⟨pt, ?_⟩
    have hz : (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      show Ideal.comap (algebraMap A (FractionRing A)) pt.asIdeal ≤ q.asIdeal
      have hbot : pt.asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
        · exact h
        · exact absurd h pt.isPrime.ne_top
      intro a ha
      rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at ha
      rw [(IsFractionRing.injective A (FractionRing A)) (ha.trans (map_zero _).symm)]
      exact zero_mem _
    have h1 := hz.map j.continuous
    rw [hq] at h1
    have h2 := (genericPoint_spec X).specializes
      (Set.mem_univ (j ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt)))
    rw [Scheme.Hom.comp_apply]
    exact (h1.antisymm h2).eq

end LateralTheory.E.LeafFibreFieldPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtaleTopologySheaves
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

abbrev EtTop (B : Scheme.{0}) : GrothendieckTopology B.Etale := Scheme.smallEtaleTopology B

abbrev SShv (B : Scheme.{0}) (q : ℕ) : Type 2 := Sheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))

instance (B : Scheme.{0}) (q : ℕ) : HasSheafify (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  infer_instance

noncomputable instance (B : Scheme.{0}) (q : ℕ) : HasDerivedCategory.{2} (SShv B q) := HasDerivedCategory.standard _

def OU (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ DerivedCategory (SShv B q) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q))) ⋙ presheafToSheaf (EtTop B) _ ⋙
    DerivedCategory.singleFunctor (SShv B q) 0

def top (B : Scheme.{0}) : B.Etale := MorphismProperty.Over.mk ⊤ (𝟙 B) (inferInstanceAs (Etale (𝟙 B)))

abbrev YU {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : Scheme.{0} := pullback p U.hom

abbrev prU {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ YU p U :=
  pullback.fst _ _

abbrev resY {Y B : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : YU p U' ⟶ YU p U :=
  pullback.map p U'.hom p U.hom (𝟙 Y) a.left (𝟙 B) (by simp) (by simpa using a.w.symm)

abbrev resYW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    pullback (pullback.snd p U'.hom ≫ U'.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (resY p a) (𝟙 W) (𝟙 B)
    (by
      have h : U'.hom = a.left ≫ U.hom := by simpa using a.w.symm
      simp only [resY, pullback.lift_snd_assoc]
      exact congrArg (fun t => pullback.snd p U'.hom ≫ t) h) (by simp)

abbrev prB {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) : pullback U.hom ι ⟶ U.left := pullback.fst _ _

abbrev toBY {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : YU p U ⟶ U.left := pullback.snd _ _

abbrev toBW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ (toBY p U) (𝟙 W) (𝟙 B) (by simp) (by simp)

abbrev mY {Y Y' B : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (U : B.Etale) : YU (g ≫ p) U ⟶ YU p U :=
  pullback.map (g ≫ p) U.hom p U.hom g (𝟙 _) (𝟙 B) (by simp) (by simp)

abbrev mW {Y Y' B W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd (g ≫ p) U.hom ≫ U.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (mY p g U) (𝟙 W) (𝟙 B) (by simp only [mY, pullback.lift_snd_assoc]; simp only [Functor.id_obj, Category.comp_id]; exact Category.comp_id _) (by simp)

variable (q : ℕ) (i : ℤ)

abbrev LocE {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def Rep {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) (e : LocE q i p ι K) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n y,
    e U' n (rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm n y) =
      (OU B q).map a ≫ e U n y

abbrev LocEB {B W : Scheme.{0}} (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def MorRep {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) {K K' : DerivedCategory (SShv B q)}
    (e : LocE q i p ι K) (e' : LocE q i (g ≫ p) ι K') (f : K ⟶ K') : Prop :=
  ∀ U n y, e' U n (rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm n y) =
    e U n y ≫ (shiftFunctor _ n).map f

def MorRepB {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {L K : DerivedCategory (SShv B q)}
    (eL : LocEB q i ι L) (e : LocE q i p ι K) (ℓ : L ⟶ K) : Prop :=
  ∀ U n c, e U n (rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm n c) =
    eL U n c ≫ (shiftFunctor _ n).map ℓ

abbrev resBW {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : pullback U'.hom ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ a.left (𝟙 W) (𝟙 B) (by simpa using a.w.symm) (by simp)

def RepB {B W : Scheme.{0}} (ι : W ⟶ B) (L : DerivedCategory (SShv B q)) (e : LocEB q i ι L) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n c,
    e U' n (rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm n c) =
      (OU B q).map a ≫ e U n c


open CategoryTheory.Limits in
def LeafCons : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

def LeafDeg : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
    MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K0)) ∧
    (DerivedCategory.homologyFunctor (SShv B q) 2).map f = 0 ∧ (DerivedCategory.homologyFunctor (SShv B q) 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor (SShv B q) 0).map ℓ)

theorem goal_of (hC : LeafCons) (hD : LeafDeg) : LateralTheory.E.LeafGhostRelCut.LeafRep := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, hinj, hsurj, c0, cL⟩ :=
    hC q i ι p g1 g2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ :=
    hD hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨SShv B q, inferInstance, inferInstance, inferInstance, (OU B q).obj (top B), K0, K1, K2, L, f, g, ℓ, e0, e2, eL,
    d1, d2, d3, d4, d5, d6, hinj, hsurj, c0, cL⟩

end LateralTheory.E.EtaleTopologySheaves
end
end

section

namespace LateralTheory.E.E4

def LeafOrdInfHom : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B))

def LeafIntBoth : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L), Transcendental k t → ∀ x : L,
  IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x

theorem LeafOrdAtInfinity_of (hV : LeafOrdInfHom) (hI : LeafIntBoth) : LeafOrdAtInfinity := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨n, φ, hφ⟩ := hV k B g hg hf
  refine ⟨n, φ, fun u hu => ?_⟩
  set L := FractionRing B
  set T : L := algebraMap B L (g Polynomial.X)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  let G : Polynomial k →ₐ[k] L := (IsScalarTower.toAlgHom k B L).comp g
  have hG : Function.Injective G := hinjL.comp hg
  have hT : Transcendental k T := by
    intro ⟨p, hp0, hp⟩
    apply hp0
    apply hG
    rw [map_zero]
    have : G p = Polynomial.aeval T p := by
      rw [show G p = G (Polynomial.aeval Polynomial.X p) by simp, ← Polynomial.aeval_algHom_apply]; rfl
    rw [this]; exact hp
  have hint : IsIntegral (Algebra.adjoin k {T}) (algebraMap B L (u : B)) := by
    obtain ⟨p, hpm, hp⟩ := (RingHom.IsIntegral.of_finite hf) (u : B)
    let f : Polynomial k →ₐ[k] Algebra.adjoin k {T} := Polynomial.aeval ⟨T, Algebra.subset_adjoin rfl⟩
    have hfG : ((algebraMap (Algebra.adjoin k {T}) L).comp f.toRingHom) = (algebraMap B L).comp g.toRingHom := by
      have : (IsScalarTower.toAlgHom k (Algebra.adjoin k {T}) L).comp f = G := by
        apply Polynomial.algHom_ext; simp [f, G, T]
      exact congrArg AlgHom.toRingHom this
    refine ⟨p.map f.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hfG, ← Polynomial.hom_eval₂]
    change algebraMap B L (Polynomial.eval₂ g.toRingHom (u : B) p) = 0
    rw [hp, map_zero]
  have := hI k L T hT _ hint (hφ u hu)
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k B L) hinjL).mp this

end LateralTheory.E.E4
end
