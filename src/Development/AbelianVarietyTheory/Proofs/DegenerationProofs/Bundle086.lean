module

public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitReduction

open IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueEmb (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ResidueField (integralClosure ℤ_[p] K) →+* GlobalTheory.ZJ.kb p :=
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  ResidueField.map (integralClosureToPadicAlgClIntegers K)

noncomputable def intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] K' :=
  ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure

instance isLocalHom_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') : IsLocalHom (intIncl h) :=
  isLocalHom_of_injective_integralClosure _ (mapIntegralClosure_padicInt_injective (IntermediateField.inclusion h))

theorem exists_subset_range (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (s : Set (GlobalTheory.ZJ.kb p)) (hs : s.Finite) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : K ≤ K') (_ : FiniteDimensional ℚ_[p] K'),
      s ⊆ Set.range (residueEmb K') := by
  choose l hl using residue_surjective (R := GlobalTheory.ZJ.OO p)
  let t : Set (PadicAlgCl p) := (fun x => (l x : PadicAlgCl p)) '' s
  haveI : Finite t := (hs.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] t) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K ⊔ IntermediateField.adjoin ℚ_[p] t, le_sup_left, inferInstance, fun x hx => ?_⟩
  have hm : (l x : PadicAlgCl p) ∈ K ⊔ IntermediateField.adjoin ℚ_[p] t :=
    (le_sup_right : IntermediateField.adjoin ℚ_[p] t ≤ _) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
  refine ⟨residue _ ⟨⟨_, hm⟩, (mem_integralClosure_padicInt_iff _ _).2
    ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (l x).2)⟩, ?_⟩
  exact hl x

theorem residueEmb_comp {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K'] (h : K ≤ K') :
    (residueEmb K').comp (ResidueField.map (intIncl h)) = residueEmb K :=
  RingHom.ext fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    exact congrArg (residue (GlobalTheory.ZJ.OO p)) (Subtype.ext rfl)

theorem algebraMap_comp_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    (IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K) =
      (algebraMap (integralClosure ℤ_[p] K') K').comp (intIncl h) :=
  RingHom.ext fun _ => rfl

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_iso_of_square {R R₁ R₂ T : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    (G : Over (Sp R)) [GrpObj G] :
    ∃ i : (Over.pullback (spMap b)).obj ((Over.pullback (spMap a)).obj G) ≅
      (Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G), IsMonHom i.hom := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_comp, e, ← spMap_comp]) rfl)
    ((isGrpPullback_pullback ((Over.pullback (spMap c)).obj G) (spMap d)).comp (isGrpPullback_pullback G _))
  exact ⟨i, hi⟩

theorem exists_finite_torusExtension_specialFibre {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [IsAlgClosed Ω]
    (σ : ResidueField R →+* Ω) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
      (β : ResidueField R' →+* Ω), β.comp (ResidueField.map f) = σ → s ⊆ Set.range β →
      ∃ E : SplitExt (Sp (ResidueField R')),
        E.IsGt ((Over.pullback (spMap (residue R'))).obj ((Over.pullback (spMap f)).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  obtain ⟨T⟩ := h₀.fibres _ (spMap σ)
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ _ T
  refine ⟨s, hs, fun R' _ _ f _ β hβ hr => ?_⟩
  obtain ⟨T'⟩ := H _ (ResidueField.map f) β hβ hr
  obtain ⟨i, hi⟩ := exists_iso_of_square (ResidueField.map_comp_residue f) G
  haveI := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T'⟩

theorem exists_isGrpPullback_of_square {R R₁ R₂ T K : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    [CommRing K] {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    {u : K →+* R₁} {v : K →+* T} (e' : b.comp u = v) (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A]
    {φ : pullback G.hom (spMap a) ⟶ A.left} (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ : pullback ((Over.pullback (spMap c)).obj G).hom (spMap d) ⟶ A.left,
      IsGrpPullback ((Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G)) A (spMap v) ψ := by
  obtain ⟨i, hi⟩ := exists_iso_of_square e.symm G
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_comp, e']) rfl⟩

end GlobalTheory.SplitReduction

namespace GlobalTheory


open SplitReduction in
theorem exists_semiAbelian_model_split_specialFibre : GlobalTheory.Published.SemistableReductionSt → ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K') (_ : IsLocalRing (integralClosure ℤ_[p] K')), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧
    (∃ E : SplitExt (Sp (IsLocalRing.ResidueField (integralClosure ℤ_[p] K'))),
      let f := spMap (IsLocalRing.residue (integralClosure ℤ_[p] K'))
      letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
      @SplitExt.IsGt _ E ((Over.pullback f).obj G) (Functor.grpObjObj (F := Over.pullback f))) ∧
    ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro H p _ K _ P
  obtain ⟨K₁, h₁, f₁, G, gG, hG, φ, hφ⟩ := H p K P
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := p)
  obtain ⟨s, hs, T⟩ := exists_finite_torusExtension_specialFibre (residueEmb K₁) G hG
  obtain ⟨K', h, f', hr⟩ := exists_subset_range K₁ s hs
  exact ⟨K', h₁.trans h, inferInstance, f', (Over.pullback (spMap (intIncl h))).obj G, inferInstance,
    IsSemiAbelian.pullback _ G hG, T _ (intIncl h) (residueEmb K') (residueEmb_comp h) hr,
    exists_isGrpPullback_of_square (algebraMap_comp_intIncl h) (RingHom.ext fun _ => rfl) G P.A hφ⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LabelMap

theorem exists_lift_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {Γ : Type} [AddCommGroup Γ]
    (pt : Γ → (baseOver S ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) :
    ∃ xx : Multiplicative Γ →* (T ⟶ G'),
      (∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = xx (Multiplicative.ofAdd a)) ∧
      ∀ (k : ℕ), (∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ k = 1 → ∃ a, (T.hom ≫ f) ≫ (pt a).left = z.left) →
        ∀ x : T ⟶ G', x ^ k = 1 → ∃ a, xx (Multiplicative.ofAdd a) = x := by
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hΦ : ∀ x, (Φ x).left = x.left ≫ φ := fun _ => rfl
  have inj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext (h.1.hom_ext
    ((hΦ x).symm.trans ((congrArg (fun z => z.left) e).trans (hΦ y))) ((Over.w x).trans (Over.w y).symm))
  have surj : Function.Surjective Φ := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective Φ ⟨inj, surj⟩
  let U : Over.mk (T.hom ≫ f) ⟶ baseOver S := Over.homMk (T.hom ≫ f) (Category.comp_id _)
  let q : Multiplicative Γ →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun a => U ≫ pt a.toAdd) fun a b =>
      (congrArg (U ≫ ·) (hadd a.toAdd b.toAdd)).trans (MonObj.comp_mul U _ _)
  have key : ∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = e.symm (q (Multiplicative.ofAdd a)) := fun a x =>
    ⟨fun H => e.eq_symm_apply.2 (Over.OverMorphism.ext H),
      fun H => congrArg (fun z => z.left) (e.eq_symm_apply.1 H)⟩
  refine ⟨e.symm.toMonoidHom.comp q, key, fun k hk x hx => ?_⟩
  obtain ⟨a, ha⟩ := hk (Φ x) (by rw [← map_pow, hx, map_one])
  exact ⟨a, ((key a x).1 ha.symm).symm⟩


attribute [local instance] TorusExt.gtGroup in

theorem pow_eq_one_of_qkAdd {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (heq : ∀ q q', QkPt.Equiv D F q q' → f q = f q') (hadd : ∀ q q' q'', QkAdd q q' q'' → f q'' = f q * f q')
    (q : QkPt D F k) : f q ^ k = 1 := by
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkMk (y : D.X) (g : GtPtF D F) (h : k • g = iota y) : QkPt D F k :=
    ⟨y, g, k • g, (TorusExt.isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq _ _).2 h⟩
  let qkZero : QkPt D F k := qkMk 0 0 (by rw [nsmul_zero, map_zero])
  let qkAdd (p p' : QkPt D F k) : QkPt D F k :=
    qkMk (p.y + p'.y) (p.g + p'.g) (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])
  have qkAdd_rel (p p' : QkPt D F k) : QkAdd p p' (qkAdd p p') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  have fz : f qkZero = 1 := by
    have e := hadd _ _ _ (qkAdd_rel (qkZero) (qkZero))
    rw [show qkAdd (qkZero) (qkZero) = qkZero from
      TorusExt.qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  let m : ℕ → QkPt D F k := fun n => qkMk (n • q.y) (n • q.g) (by
    rw [smul_comm, qk_nsmul, map_nsmul])
  have hm : ∀ n, f (m n) = f q ^ n := fun n => by
    induction n with
    | zero => exact (congrArg f (TorusExt.qk_ext (zero_nsmul _) (zero_nsmul _))).trans (fz.trans (pow_zero _).symm)
    | succ n ih =>
      rw [pow_succ, ← ih, ← hadd _ _ _ (qkAdd_rel _ _)]
      exact congrArg f (TorusExt.qk_ext (succ_nsmul _ _) (succ_nsmul _ _))
  rw [← hm, ← fz]
  exact (heq _ _ ⟨q.y, (zero_add _).symm, iota q.y, (isIota_iff_eq _ _).2 rfl, (TorusExt.isAdd_iff_eq _ _ _).2 ((qk_nsmul q).trans (zero_add _).symm)⟩).symm

theorem exists_labelMap : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro L _ hU o Ω _ _ _ _ S ρ p _ y₀ u
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    exact (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap _ _))).symm.trans
      (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := u.D.tau_bimult
  have wd : ∀ q q' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  let D := u.D.toPre
  let F := PadicAlgCl p
  let R := u.V
  let k := S.r * S.N
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkAdd (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) :=
    ⟨v.y + v'.y, v.g + v'.g, (S.r * S.N) • (v.g + v'.g),
      (TorusExt.isNsmul_iff_eq _ _ _).2 rfl,
      (isIota_iff_eq _ _).2 (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])⟩
  have qkAdd_rel (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkAdd v v' (qkAdd v v') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (qkAdd (P a) (P b)) (by
      rw [hadd _ _ _ (qkAdd_rel _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := PadicAlgCl p) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

end GlobalTheory.ZH.LabelMap
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ker_le_ker_of_range_subset_of_isReduced {X T Y : Scheme.{0}} [IsReduced T] (f : X ⟶ Y)
    [IsClosedImmersion f] (g : T ⟶ Y) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g
    ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact f.range_subset_ker_support

theorem exists_iso_isMonHom_of_isGt_of_range_eq :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Over (Sp k)) (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (f : G ⟶ Y) (f' : G' ⟶ Y), E.IsGt G → E'.IsGt G' → IsClosedImmersion f.left → IsClosedImmersion f'.left → Set.range f.left = Set.range f'.left → η[G] ≫ f = η[G'] ≫ f' → ∃ e : G ≅ G', IsMonHom e.hom ∧ e.hom ≫ f' = f := by
  intro k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1
  have hs := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1
  have hs' := (UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have hk : f'.left.ker = f.left.ker :=
    le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le)
      (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)
  have := IsClosedImmersion.isIso_lift f'.left f.left hk
  have hl := IsClosedImmersion.lift_fac f'.left f.left hk.le
  let e : G ≅ G' := Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by
    rw [asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])
  have he : e.hom ≫ f' = f := Over.OverMorphism.ext hl
  have : Mono f' := Over.mono_of_mono_left f'
  refine ⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩
  rw [← cancel_mono f', Category.assoc, he, h1]

end GlobalTheory
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.TorusPull

open ReciprocityTheory.ChartRestriction.G.DVR

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem mem_torus_iff {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) :
    (∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z) ↔
      z ≫ g.pG.left = z ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A := by
  have hb : (fstG I e G).left ≫ G.hom ≫ eSec D.P.A =
      ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D.P.A) (Over.w (fstG I e G)))
  constructor
  · rintro ⟨τ, rfl⟩
    have c := ((CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w).trans (congrArg (g.i.left ≫ ·) hb)
    exact (Category.assoc _ _ _).trans ((congrArg (τ ≫ ·) c).trans (Category.assoc _ _ _).symm)
  · intro h
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (z ≫ (thickObj R I e G).hom)
    let a : FinalForm ⟶ thickObj R I e G := Over.homMk z rfl
    have k := (CharAgree.comp_q_eq_one_iff g a).2 (h.trans (congrArg (z ≫ ·) hb.symm))
    exact ⟨(g.isKernel.lift a (toUnit _) k).left,
      congrArg (fun q => q.left) (g.isKernel.lift_fst a (toUnit _) k)⟩

theorem val_torus {T : Scheme.{0}}
    (τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left) (χ : D.X) {y : T}
    {J : (T ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) :
    val (g.t χ) (τ ≫ g.i.left) y J = gm τ y ⊤ (charUnit _ D.X χ) := by
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (τ ≫ (splitTorus _ D.X).hom)
  let a : FinalForm ⟶ splitTorus _ D.X := Over.homMk τ rfl
  exact (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm a 1 y J hJ χ).1

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))}
  {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)


include hp in
theorem unit_iff {Z : Scheme.{0}} (z : Z ⟶ T'.left) :
    z ≫ p'.left = z ≫ T'.hom ≫ eSec D'.P.A ↔ (z ≫ h) ≫ p.left = (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
  have b := TorusCoordPull.over_base hD p p' h hp
  have l : (z ≫ p'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = (z ≫ h) ≫ p.left := by
    rw [Category.assoc, hp, Category.assoc]
  have r : (z ≫ T'.hom ≫ eSec D'.P.A) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
    rw [Category.assoc, Category.assoc, hD.he, Category.assoc, reassoc_of% b]
  refine ⟨fun H => l.symm.trans ((congrArg (· ≫ _) H).trans r), fun H => ?_⟩
  refine (pull_grp hD).1.hom_ext (l.trans (H.trans r.symm)) ?_
  have u : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  rw [Category.assoc, Category.assoc, Category.assoc, u, Over.w]
  exact congrArg (z ≫ ·) (Category.comp_id _).symm

end Two

theorem appTop_ext {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (r' : Z ⟶ Y') (a : Γ(Y, ⊤)ˣ) (b : Γ(Y', ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = gm r' z ⊤ b) : r.appTop.hom a.val = r'.appTop.hom b.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have := congrArg Units.val (h z)
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at this
  exact this

theorem torus_point_iff : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  intro R R' _ _ _ _ I I' φ D D' hD G _ _ G' _ _ e g g' h hp ht T z a
  have mem := (mem_torus_iff g' z).trans ((unit_iff hD g.pG g'.pG h hp z).trans (mem_torus_iff g (z ≫ h)).symm)
  have ch : ∀ τ' τ, τ' ≫ g'.i.left = z → τ ≫ g.i.left = z ≫ h → ∀ x,
      τ'.appTop.hom (charUnit _ D'.X x).val = τ.appTop.hom (charUnit _ D.X (hD.xe x)).val := by
    intro τ' τ h' h₀ x
    refine appTop_ext _ _ _ _ fun y => ?_
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB y
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB y
    obtain ⟨hψ, H⟩ := ht x
    have P := (maps_iff hD.w _ _ _ (g'.t x) (g.t (hD.xe x)) h _
      (GeneratorPullback.pullAlong_le D.P.L _ h _ _ hψ) (fun _ => rfl)).1 H
    let FinalForm : Over (Spec (CommRingCat.of R')) :=
      Over.mk (z ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom)
    let ρ : FinalForm ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk z rfl
    have hρ : ρ ≫ g'.pG = 1 := by
      refine Over.OverMorphism.ext (((mem_torus_iff g' z).1 ⟨τ', h'⟩).trans ?_)
      have k : (toUnit FinalForm).left = FinalForm.hom := (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D'.P.A) k.symm)
    have v := TorusCoordPull.val_unit_pull hD g.pG g'.pG h hp P ρ hρ (y := y) hJ hJ'
    have v' := val_torus g' τ' x hJ'
    have v₀ := val_torus g τ (hD.xe x) hJ
    rw [h'] at v'
    rw [h₀] at v₀
    exact v'.symm.trans (v.symm.trans v₀)
  constructor
  · rintro ⟨τ', h', hx⟩
    obtain ⟨τ, h₀⟩ := mem.1 ⟨τ', h'⟩
    exact ⟨τ, h₀, fun x => (ch τ' τ h' h₀ x).symm.trans (hx x)⟩
  · rintro ⟨τ, h₀, hx⟩
    obtain ⟨τ', h'⟩ := mem.2 ⟨τ, h₀⟩
    exact ⟨τ', h', fun x => (ch τ' τ h' h₀ x).trans (hx x)⟩

end GlobalTheory.TorusPull
end
end
