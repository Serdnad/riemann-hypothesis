module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.simplicialCochain_classes_basic_properties :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
      cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op (SimplexCategory.mk n))) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  have differential (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) :
      δ (n : ℤ) ((n + 1 : ℕ) : ℤ)
          (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
        (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
    rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring)
      (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
    rw [Category.assoc, Category.assoc, ClsBasic.resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
    congr 2
    rw [ClsBasic.chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc]
    congr 1
    rw [cobd, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp]
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_,
    fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk
      (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [differential, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow •
      Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, differential, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties : (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧ (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧ ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B := by
  first | (exact @GlobalTheory.EtC.etFF_basic) | (exact GlobalTheory.EtC.etFF_basic) | (intros; apply GlobalTheory.EtC.etFF_basic  <;> assumption)
end

section

open TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_unitDescentCocycle_descendedSubmodule_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], descMod A B 1 ≤ 1 → ∀ I : (Submodule A B)ˣ, ∃ u : (B ⊗[A] B)ˣ, UCoc A B u ∧ descMod A B u = (I : Submodule A B) := by
  first | exact @GlobalTheory.PicCech.exists_unitCocycle_descMod_eq | exact GlobalTheory.PicCech.exists_unitCocycle_descMod_eq | (intros; apply GlobalTheory.PicCech.exists_unitCocycle_descMod_eq; all_goals assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.filteredColimitCohomology_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.contH_transport_quasiIso) | (exact GlobalTheory.EtC.contH_transport_quasiIso) | (intros; apply GlobalTheory.EtC.contH_transport_quasiIso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_descends_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
      IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g →
      ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B),
        EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  intro J _ _ D c hc B g hg
  obtain ⟨-, hsurj⟩ := (etFF_iff_spec g).1 hg
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hgh, hcov⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc Unit (fun _ ↦ B)
      (fun _ ↦ g) (fun _ ↦ hg.1)
      (fun p ↦ by
        obtain ⟨v, hv⟩ := hsurj.surj p
        exact ⟨(), v, hv⟩) j₀
  refine ⟨j, B' (), g' (), h (), ?_, (hgh ()).2⟩
  rw [etFF_iff_spec]
  refine ⟨HasRingHomProperty.Spec_iff.2 (hgh ()).1, ⟨fun p ↦ ?_⟩⟩
  obtain ⟨i, v, hv⟩ := hcov p
  cases i
  exact ⟨v, hv⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.of_etaleCohomologyEquivalence_diagram : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt), (∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) → (∀ i, Eqv R (α.app i) F) → Eqv R β F → (ContCone R F c ↔ ContCone R F c') := by
  first | (exact @GlobalTheory.EtC.ContCone.iff_of_eqv) | (exact GlobalTheory.EtC.ContCone.iff_of_eqv) | (intros; apply GlobalTheory.EtC.ContCone.iff_of_eqv  <;> assumption)
end

section

open TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : (B ⊗[A] B)ˣ), UCoc A B u → (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  first | exact @GlobalTheory.DescTop.top_mul_descMod_eq_top | exact GlobalTheory.DescTop.top_mul_descMod_eq_top | (intros; apply GlobalTheory.DescTop.top_mul_descMod_eq_top; all_goals assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.isEtaleCoordinates_section_quotients : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U → (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → Etale A U (A.zmap t0 t) := by
  first | exact @GlobalTheory.OTY.etale_zmap_main | exact GlobalTheory.OTY.etale_zmap_main | (intros; apply GlobalTheory.OTY.etale_zmap_main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CechPts

variable {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y))
  (h : ∀ i, y i ≫ f = x)

def cmp : yoneda.obj Z ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])

theorem cechPt_eq : cechPt f k x y h = (cmp f k x y h).app (op Z) (𝟙 Z) := rfl

theorem map_cechPt {U : Scheme.{0}} (g : U ⟶ Z) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) = (cmp f k x y h).app (op U) g := by
  rw [cechPt_eq]
  have hn := (congrArg (fun t => t (𝟙 Z)) ((cmp f k x y h).naturality g.op)).symm
  change _ = (cmp f k x y h).app (op U) (g ≫ 𝟙 Z)
  change ((cech f).obj (op ⦋k⦌)).map g.op ((cmp f k x y h).app (op Z) (𝟙 Z)) =
    (cmp f k x y h).app (op U) (g ≫ 𝟙 Z) at hn
  exact hn

theorem app_eq {U : Scheme.{0}} (g : U ⟶ Z) :
    (cmp f k x y h).app (op U) g = yonedaEquiv (yoneda.map g ≫ cmp f k x y h) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

theorem bij (hc : IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h)) (U : Scheme.{0}) :
    Function.Bijective ((cmp f k x y h).app (op U)) := by
  constructor
  · intro g g' hg
    rw [app_eq, app_eq] at hg
    have hm := yonedaEquiv.injective hg
    apply WidePullbackCone.IsLimit.hom_ext hc
    · apply yoneda.map_injective
      have := hm =≫ WidePullback.base _
      simp only [cmp, Category.assoc, WidePullback.lift_base] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
    · intro i
      apply yoneda.map_injective
      have := hm =≫ WidePullback.π _ i
      simp only [cmp, Category.assoc, WidePullback.lift_π] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
  · intro v
    obtain ⟨m, rfl⟩ := yonedaEquiv.surjective v
    have w : ∀ i, yonedaEquiv (m ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) ≫ f =
        yonedaEquiv (m ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      intro i
      rw [← WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i, ← Category.assoc, yonedaEquiv_comp]
      rfl
    refine ⟨WidePullbackCone.IsLimit.lift hc _ _ w, (app_eq f k x y h _).trans ?_⟩
    congr 1
    apply WidePullback.hom_ext
    · intro i
      apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_π hc _ _ w i
      simp only [WidePullbackCone.mk_π] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_π]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)
    · apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_base hc _ _ w
      simp only [WidePullbackCone.mk_base] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_base]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)

end GlobalTheory.EtC.CechPts


open GlobalTheory.EtC.CechPts in
theorem GlobalTheory.EtC.CechPts.main : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F => val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((map_cechPt f k x y h g).symm.trans (hg.trans (map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (map_cechPt f k x y h g).trans hg⟩
  have hext : ∀ s s' : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F,
      (∀ U v, val s U v = val s' U v) → s = s' := by
    intro s s' hs
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    exact hs U.unop v
  have hnat : ∀ (s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
      val s V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (val s U v) := by
    intro s V U g v
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (((cech f).obj (op ⦋k⦌)).map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk _ g.op v]
    exact congrArg (fun t => t.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  have hex : ∀ φ : ∀ U : Scheme.{0}, ((cech f).obj (op ⦋k⦌)).obj (op U) → Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) v, φ V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (φ U v)) →
      ∃ s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F, ∀ U v, val s U v = φ U v := by
    intro φ hφ
    refine ⟨GlobalTheory.EtC.FreeHom.desc _ F φ hφ, ?_⟩
    intro U v
    change ((toSheafify Scheme.etaleTopology ((freeP R).obj _) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom).app (op U)).hom (ModuleCat.freeMk (ULift.up v)) = _
    have hd : toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom = GlobalTheory.EtC.FreeHom.descP _ F φ hφ := by
      have ht := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (GlobalTheory.EtC.FreeHom.descP _ F φ hφ)
      rw [Adjunction.homEquiv_unit] at ht
      exact ht
    rw [hd]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
        ((cech f).obj (op ⦋k⦌)).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op ⦋k⦌)).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op ⦋k⦌)).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op ⦋k⦌)).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op ⦋k⦌)).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op ⦋k⦌)).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id]
      change _ = ((cech f).obj (op ⦋k⦌)).map (𝟙 (op Z)) _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [h2]
    simp [Sec.res]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  first | exact @GlobalTheory.EtC.HCElements.main | exact GlobalTheory.EtC.HCElements.main | (intros; apply GlobalTheory.EtC.HCElements.main <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O], IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  first | (exact @GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (exact GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (intros; apply GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
end
