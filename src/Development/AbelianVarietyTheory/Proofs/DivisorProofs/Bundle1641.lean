module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle129
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  first | exact @GlobalTheory.RealWeilFinFix.actOF_fin | exact GlobalTheory.RealWeilFinFix.actOF_fin | (intros; apply GlobalTheory.RealWeilFinFix.actOF_fin <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPartsF

theorem exists_real_finite_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J) :
    ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y : AEF F E, infPartF F E x = infPartF F E y → finPartF F E x = finPartF F E y → x = y :=
    fun x y h1 h2 => GlobalTheory.AdelicOrbit.parts_inj x y h1 h2
  have hs : ∀ a b, ∃ x : AEF F E, infPartF F E x = a ∧ finPartF F E x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  set g : GL (Fin n) (AEF F E) := matHomF σ J p with hg
  have hgm : g ∈ HR (AF F) σ J := p.2
  have hparts := (GlobalTheory.AdelicOrbit.mem_parts σ J g).1 hgm
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs (Formalism.UG.bc (infPartF F E) g) 1
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs 1 (Formalism.UG.bc (finPartF F E) g)
  have ha : a ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J a).2 ⟨a1 ▸ hparts.1, a2 ▸ one_mem _⟩
  have hk : k ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J k).2 ⟨k1 ▸ one_mem _, k2 ▸ hparts.2⟩
  refine ⟨⟨a, ha⟩, ?_, ⟨k, hk⟩, ?_, ?_, ?_⟩
  · exact MonoidHom.mem_ker.2 a2
  · exact MonoidHom.mem_ker.2 k1
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (a * k)
      rw [map_mul, a1, k1, mul_one]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (a * k)
      rw [map_mul, a2, k2, one_mul]
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (k * a)
      rw [map_mul, a1, k1, one_mul]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (k * a)
      rw [map_mul, a2, k2, mul_one]

end GlobalTheory.WeilPartsF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}}
  {A : Over S} [GrpObj A] [IsCommMonObj A] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

theorem spMap_comp_spMap_lieAt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₂ →+* R₃)
    (g : R₁ →+* R₂) : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem tanScal_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (v : epsPtR x ⟶ A) :
    IsTanScal act x (algebraMap (𝓞 D.F) D.O c) r v ↔
      (smT x 0 v = 1 ∧ v ≫ (act.toF D).act c = smT x r v) := by
  have e0 : epsMul (0 : R') = (algebraMap R' (DualNumber R')).comp (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsPtR x ⟶ A).left) = spMap (algebraMap R' (DualNumber R')) ≫ (1 : Over.mk x ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [spMap_comp_spMap_lieAt]
    have : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (algebraMap R' (DualNumber R')) = RingHom.id R' := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  have t1 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      smT x 0 v = 1 := by
    constructor
    · intro hp
      apply Over.OverMorphism.ext
      rw [smT_left, e1, e0, ← spMap_comp_spMap_lieAt, Category.assoc, hp]
    · intro hp
      have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ V.left) hp
      rw [e1, ← Category.assoc, e2, Category.id_comp, smT_left, e0, ← spMap_comp_spMap_lieAt,
        ← Category.assoc, ← Category.assoc, e2, Category.id_comp] at this
      exact this
  have t2 : (v ≫ act.act (algebraMap (𝓞 D.F) D.O c)).left = spMap (epsScaleR r) ≫ v.left ↔
      v ≫ (act.toF D).act c = smT x r v := by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [smT_left]
      exact h
    · intro h
      have := congrArg (fun V => V.left) h
      rw [smT_left] at this
      exact this
  unfold IsTanScal
  rw [t1, t2]

theorem tv_sum_lieAt {κ : Type} (s : Finset κ) (f : κ → TanM x A) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tv_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

theorem eig_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (u : TanM x A) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D) c u = r • u ↔
      tv u ≫ (act.toF D).act c = smT x r (tv u) := by
  constructor
  · intro h
    have := congrArg tv h
    rw [tv_actR, tv_smul] at this
    exact this
  · intro h
    apply tanM_ext
    rw [tv_actR, tv_smul]
    exact h

end

theorem lieAt_iff_lieMod : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  intro p _ D R _ b S A _ _ act R' _ β x
  constructor
  · intro h v hv
    have hv' := (eig_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (tv v) ((tanScal_iff_lieAt x act D.ω (β b.ρ) (tv v)).2 ⟨tv_mem v, hv'⟩)
    have h0 : ∀ i, smT x 0 (w i) = 1 := fun i => ((tanScal_iff_lieAt x act 0 _ (w i)).1 (hw i 0)).1
    refine ⟨fun i => mkT (w i) (h0 i), fun i => ?_, ?_⟩
    · rw [mem_eigSub]
      intro c
      exact (eig_iff_lieAt x act c _ _).2 ((tanScal_iff_lieAt x act c _ (w i)).1 (hw i c)).2
    · apply tanM_ext
      rw [hsum, tv_sum_lieAt, List.prod_ofFn]
      rfl
  · intro h v hv
    obtain ⟨h0, hω⟩ := (tanScal_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (mkT v h0) ((eig_iff_lieAt x act D.ω (β b.ρ) (mkT v h0)).2 hω)
    refine ⟨fun i => tv (w i), fun i c => ?_, ?_⟩
    · exact (tanScal_iff_lieAt x act c _ (tv (w i))).2 ⟨tv_mem _, (eig_iff_lieAt x act c _ (w i)).1 ((mem_eigSub.1 (hw i)) c)⟩
    · have := congrArg tv hsum
      rw [tv_mkT, tv_sum_lieAt] at this
      rw [List.prod_ofFn]
      exact this

end GlobalTheory.UPel.HT.LieLin
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_etLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  intro p _ D R _ b N w0 r _hNp hw S _ s o
  obtain ⟨r', hrr', H, i, hHf, hHfl, hHk, hHu⟩ := GlobalTheory.T.finite_flat_torsion_subgroup p D R b N w0 hw.1 hw.2.1 S s o r
  have hHe : Etale H.hom := GlobalTheory.T.torsion_subgroup_universal p D R b N w0 r' S s o H i hHf hHfl hHk hHu
    (fun k _ _ x v h0 hv => GlobalTheory.T.infinitesimal_point_trivial p D R b N w0 r' hw S s o k x v h0 hv)
  obtain ⟨K, κ, hKf, hKe, hKk, hKu⟩ := GlobalTheory.T.etale_torsion_subgroup_universal p D R b N w0 r r' hrr' S s o H i hHf hHe hHk hHu
  obtain ⟨Z, et, hZf, hZe, eadd, elin, eker, huniv⟩ := GlobalTheory.T.etale_level_kernel_universal p D R b N w0 r hw S s o K κ hKf hKe hKk hKu
  have c1 := GlobalTheory.T.clopenCond_injective_geom_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  have c2 := GlobalTheory.T.clopenCond_onto_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  obtain ⟨U, hU, HU⟩ := c1.and c2
  haveI := hZf
  haveI := hZe
  obtain ⟨V, j, hV1, hV2, hmono, Hj⟩ := GlobalTheory.LevCover.exists_sub U hU
  have hPV := (HU V j).2 ((Hj V j).2 ⟨𝟙 V, Category.id_comp j⟩)
  refine ⟨V.left, V.hom, fun y => j ≫ et y, hV1, hV2, ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_,
    fun k _ _ x => ⟨hPV.1 k x, hPV.2 k x⟩⟩, fun T l hl => ?_⟩
  · beta_reduce
    rw [eadd, MonObj.comp_mul]
  · beta_reduce
    rw [elin, Category.assoc]
  · beta_reduce
    rw [eker x hx, MonObj.comp_one]
  obtain ⟨hadd, hlin, hker, hgeo⟩ := hl
  obtain ⟨h, hh, hu⟩ := huniv T l hadd hlin hker
  have hP : (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
        ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = g) := by
    refine ⟨fun k _ _ x y hy => (hgeo k x).1 y (by rw [← hh y]; exact hy), fun k _ _ x g hg => ?_⟩
    obtain ⟨y, hy⟩ := (hgeo k x).2 g hg
    exact ⟨y, by rw [hh y]; exact hy⟩
  obtain ⟨h', hh'⟩ := (Hj T h).1 ((HU T h).1 hP)
  refine ⟨h', fun y => ?_, fun g hg => ?_⟩
  · beta_reduce
    rw [← Category.assoc, hh', hh]
  · have : g ≫ j = h := hu _ fun y => by rw [Category.assoc]; exact hg y
    exact (cancel_mono j).1 (this.trans hh'.symm)

end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_oAct_desc : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  obtain ⟨hfin, het, hsurj⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq
  haveI : Surjective ψ.left := hsurj
  haveI : Flat ψ.left := inferInstance
  haveI : QuasiCompact ψ.left := inferInstance
  haveI : IsMonHom ψ := hq.1
  have : Epi ψ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ
  have : Epi (ψ ⊗ₘ ψ) := GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ
  have hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ := fun a => by
    haveI := o.act.hom a
    refine GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_
    have h1 : (x₁ / x₂) ≫ ψ = 1 := by rw [GrpObj.div_comp, h, div_self']
    have h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1 := hst W W.hom (Category.comp_id _) _ h1 a
    rwa [GrpObj.div_comp, div_eq_one] at h2
  choose t ht using hd
  refine ⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ },
    fun a => (ht a).symm⟩
  · haveI := o.act.hom a
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
    · rw [← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht,
        ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]
  · rw [← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]
  · rw [← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]
  · rw [← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc,
      Category.assoc, IsMonHom.mul_hom]

end GlobalTheory.UPel.HT.ES
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem lie_of_isQuasiInv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq act' hact
  obtain ⟨e, rfl⟩ := hc
  have hcY : IsUnit (((p ^ e : ℕ) : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_pow, map_natCast] at this
    rw [Nat.cast_pow]
    exact this
  obtain ⟨-, hEt, -⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B (p ^ e) ψ ψ' o.ab hB hcY hq
  haveI : IsMonHom ψ := hq.1
  haveI : Etale ψ.left := hEt
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ B).left := by
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left =
            (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i a => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i a).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ B).left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i a).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) Y o.A B ψ (o.act.toF D) (act'.toF D) inferInstance hEt
      (fun a => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv


open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in
theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L →
          (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmooth.contDiff_thetaTr_real | exact GlobalTheory.ThetaSmooth.contDiff_thetaTr_real | (intros; apply GlobalTheory.ThetaSmooth.contDiff_thetaTr_real <;> assumption)
end
