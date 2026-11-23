module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem sym_inv_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁, Hom.inv_def] at e
  refine e.trans ?_
  show ((𝟙 G' : G' ⟶ G').left ≫ φ) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_of_cover (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A]
    (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (hU : iSup U = ⊤)
    (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (L : LB A.left) (M : ∀ i, LB (G i).left) (hL : L.IsLB)
    (hM : ∀ i, (M i).IsLB) (hw : ∀ i, LBIso (M i) (L.pull (ψ i))) (hs : ∀ i, Out.Sym (G i) (M i)) :
    Out.Sym A L := by
  intro s
  obtain ⟨i, hi⟩ : ∃ i, s ∈ U i := TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial)
  obtain ⟨V, hV, c, hc⟩ := hs i ⟨s, hi⟩
  obtain ⟨w, hw⟩ := hw i
  refine ⟨(U i).ι ''ᵁ V, ⟨⟨s, hi⟩, hV, rfl⟩, ?_⟩
  have hp := (hψ i).1

  obtain ⟨b, hb⟩ : ∃ b : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ V.toScheme,
      b ≫ V.ι ≫ (U i).ι = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom :=
    ⟨IsOpenImmersion.lift (V.ι ≫ (U i).ι) _ (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz, e⟩ := y.2
      exact ⟨⟨z, hz⟩, e⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom = (b ≫ V.ι) ≫ (U i).ι := by rw [Category.assoc, hb]
  let m := hp.lift _ _ sq
  have m₁ : m ≫ ψ i = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι := hp.lift_fst _ _ _
  have m₂ : m ≫ (G i).hom = b ≫ V.ι := hp.lift_snd _ _ _
  obtain ⟨n, hn⟩ : ∃ n : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ ((G i).hom ⁻¹ᵁ V).toScheme,
      n ≫ ((G i).hom ⁻¹ᵁ V).ι = m :=
    ⟨IsOpenImmersion.lift _ m (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ V) m₂).mpr (b y).2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL (hM i) c hc
  refine gen_chartPull (chartPullSame L _ _ _ n fun k => ?_) c₂ h₂
  fin_cases k
  · show _ ≫ _ = n ≫ (_ ≫ _) ≫ ψ i
    rw [Category.assoc, sym_inv_comm (hψ i), ← Category.assoc n, hn, ← Category.assoc m, m₁]
  · show (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι = n ≫ ((G i).hom ⁻¹ᵁ V).ι ≫ ψ i
    rw [← Category.assoc n, hn, m₁]

end GlobalTheory.CoverGlue
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem isCommMonObj_of_isGrpPullback [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

theorem isAbelianScheme_of_isGrpPullback [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G)
    (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
  have := hG.comm
  exact
    { comm := isCommMonObj_of_isGrpPullback h
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected }

theorem relAmple_restrict (h : IsPullback φ G'.hom G.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hA : Out.RelAmple G L) (V : S.Opens) (hV : IsAffineOpen V) :
    Out.RelAmple (Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (G'.hom ∣_ (f ⁻¹ᵁ V)) G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict G'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullPull L' _ _ rfl)
      (chartPullSame L (fun _ : PUnit => (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => φ) (fun _ => 1) _ fun _ => rfl) e
  let i := (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
  have hPull : (L'.pull i).IsLB := by
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨j, hj⟩ := exists_chart hL' (i y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g L' i (𝟙 _) y J J hy hy]
      exact gm_self hL' i y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g L' i (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g L' i (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g L' i (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hL' i y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  exact relAmple_pull (A' := Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) H hL hPull
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

theorem pol_pull_of_relAmple_local
    (hloc : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
        Out.RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → Out.RelAmple A L) :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') := by
  intro S S' G G' _ _ f φ L L' hL hL' hG h e
  have hG' := isAbelianScheme_of_isGrpPullback hG h
  have := hG'.proper
  refine ⟨hG', fun hA => hloc S' G' L' hL' inferInstance inferInstance fun s => ?_, fun hK => ?_⟩
  · obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 hL hL' e hA V hV⟩
  · obtain ⟨w, hw⟩ := e
    exact kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.PolPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldDescentAb

set_option backward.isDefEq.respectTransparency.types false

theorem fpqc_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap i) := by
  refine ⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.Flat.of_isField (Field.toIsField K₀) _

theorem isSeparated_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f)
    [IsSeparated q] : IsSeparated p := by
  have h : (MorphismProperty.diagonal @UniversallyClosed) p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf
      (show UniversallyClosed (pullback.diagonal q) from inferInstance)
  have h' : UniversallyClosed (pullback.diagonal p) := h
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩

theorem geometricallyConnected_of_isPullback {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {X Y : Scheme.{0}} {g : Y ⟶ X} {p : X ⟶ Sp K₀} {q : Y ⟶ Sp K}
    (H : IsPullback g q p (spMap i)) [hq : GeometricallyConnected q] :
    GeometricallyConnected p := by
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  obtain ⟨Ω, _, _, j, j', e⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom
  have e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext e
  have h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p
      (spMap j ≫ spMap i) := by
    rw [e']
    exact (IsPullback.of_hasPullback snd (spMap j')).paste_horiz h
  have h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst)
      (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc]))
      (pullback.snd snd (spMap j')) q (spMap j) :=
    IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H
  have hc : ConnectedSpace ↥(pullback snd (spMap j')) :=
    hq.geometrically_connectedSpace _ _ _ h₂
  have : Surjective (spMap j') := (fpqc_spMap j').1.1
  exact (pullback.fst snd (spMap j')).surjective.connectedSpace
    (pullback.fst snd (spMap j')).continuous

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (A₀ : Over S)
    (A : Over S') [GrpObj A₀] [GrpObj A] {φ : A.left ⟶ A₀.left} (H : IsGrpPullback A A₀ f φ)
    [Flat f] [Surjective f] [IsCommMonObj A] : IsCommMonObj A₀ := by
  have key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀ := by
    intro T₀ x₀ y₀
    let T : Over S' := Over.mk (pullback.snd T₀.hom f)
    let r : Over.mk (T.hom ≫ f) ⟶ T₀ :=
      Over.homMk (pullback.fst T₀.hom f) pullback.condition
    let up : (T₀ ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk
      (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f)
        (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)
    have hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ := fun x =>
      (H.1.lift_fst _ _ _).symm
    have h₁ := H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)
    have h₂ := H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)
    rw [mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul] at h₂
    have : Epi (pullback.fst T₀.hom f) := Flat.epi_of_flat_of_surjective _
    ext1
    rw [← cancel_epi (pullback.fst T₀.hom f)]
    exact h₂.symm
  constructor
  have := key _ (fst A₀ A₀) (snd A₀ A₀)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
  exact this.symm

theorem isAbelianScheme_and_relDim_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  intro K₀ K _ _ i A₀ A _ _ φ H hA
  have hf := fpqc_spMap i
  have := hf.1.1
  have := hf.1.2
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsep : IsSeparated A₀.hom := isSeparated_of_isPullback H.1 hf
  have huc : UniversallyClosed A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf
      inferInstance
  have hsm : Smooth A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance
  have h₀ : IsAbelianScheme A₀ :=
    { comm := isCommMonObj_of_isGrpPullback A₀ A H
      smooth := hsm
      proper := {}
      geomConnected := geometricallyConnected_of_isPullback i H.1 }
  refine ⟨h₀, fun g hg => ?_⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀
  have h' : SmoothOfRelativeDimension g' A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'
  obtain ⟨x, -⟩ := A.hom.surjective (Nonempty.some inferInstance)
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]
  exact hg'

end GlobalTheory.FieldDescentAb
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPullComp

theorem iso_pull {X Y : Scheme.{0}} {L M : LB X} (d : Y ⟶ X) (h : LBIso L M) : LBIso (L.pull d) (M.pull d) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨LB.linCombIso w (fun _ : PUnit => d) (fun _ => 1), DVR.linCombIso_isGen w hw _ _⟩

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  unfold gm
  rw [dite_eq_left hy, dite_eq_left (h hy)]
  simp only [MonoidHom.comp_apply]
  rw [pullU_res₂]
  ext
  simp [res]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem lbIso_of_chart_le_of_gm_transition_eq {Y : Scheme.{0}} {A' B : LB Y} (hB : LBIso B B) (idx : A'.ι → B.ι)
    (le : ∀ i, A'.U i ≤ B.U (idx i))
    (hg : ∀ (y : Y) i j, y ∈ A'.U i → y ∈ A'.U j →
      gm (𝟙 Y) y (A'.U i ⊓ A'.U j) (A'.g i j) = gm (𝟙 Y) y (B.U (idx i) ⊓ B.U (idx j)) (B.g (idx i) (idx j))) :
    LBIso A' B := by
  obtain ⟨w, hw⟩ := hB
  have cp : ChartPull (B.div A') (B.div B) (𝟙 Y) :=
    { idx := fun p => (p.1, idx p.2)
      le := fun p y hy => ⟨hy.1, le p.2 hy.2⟩
      g := by
        rintro y ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq
        have hp' : y ∈ B.U p1 ⊓ A'.U p2 := hp
        have hq' : y ∈ B.U q1 ⊓ A'.U q2 := hq
        change gm (𝟙 Y) y ((B.U p1 ⊓ A'.U p2) ⊓ (B.U q1 ⊓ A'.U q2)) (res _ (B.g p1 q1) * (res _ (A'.g p2 q2))⁻¹) =
          gm (𝟙 Y) y ((B.U p1 ⊓ B.U (idx p2)) ⊓ (B.U q1 ⊓ B.U (idx q2)))
            (res _ (B.g p1 q1) * (res _ (B.g (idx p2) (idx q2)))⁻¹)
        rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y,
          gm_res_eq_gm (𝟙 Y) y, hg y p2 q2 hp'.2 hq'.2]
        all_goals first
          | exact ⟨hp', hq'⟩
          | exact ⟨⟨hp'.1, le _ hp'.2⟩, ⟨hq'.1, le _ hq'.2⟩⟩ }
  obtain ⟨t, ht⟩ := gen_chartPull cp w hw
  exact ⟨t, ht⟩

theorem iso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (d : Z ⟶ Y) :
    LBIso ((L.pull a).pull d) (L.pull (d ≫ a)) := by
  have base : LBIso (L.pull (d ≫ a)) (L.pull (d ≫ a)) :=
    exists_iso_linComb hL (fun _ : PUnit => d ≫ a) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ K : ((L.pull a).pull d).ι, ((L.pull a).pull d).U K ≤ (L.pull (d ≫ a)).U (fun _ => K ⟨⟩ ⟨⟩) :=
    fun K y hy => by
      have h1 : d y ∈ (L.pull a).U (K ⟨⟩) := mem_pull.1 hy
      have h2 : a (d y) ∈ L.U (K ⟨⟩ ⟨⟩) := mem_pull.1 h1
      exact mem_pull.2 h2
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun K _ => K ⟨⟩ ⟨⟩) le ?_
  intro y K K' hK hK'
  rw [gm_pull_g (L.pull a) d (𝟙 Z) y K K' hK hK', gm_pull_g L (d ≫ a) (𝟙 Z) y _ _ (le K hK) (le K' hK')]
  simp only [Category.id_comp]
  rw [gm_pull_g L a d y (K ⟨⟩) (K' ⟨⟩) (mem_pull.1 hK) (mem_pull.1 hK')]

theorem iso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) := by
  have base : LBIso (L.pull (𝟙 X)) (L.pull (𝟙 X)) :=
    exists_iso_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ i : L.ι, L.U i ≤ (L.pull (𝟙 X)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun i _ => i) le ?_
  intro y i j hi hj
  rw [gm_pull_g L (𝟙 X) (𝟙 X) y _ _ (le i hi) (le j hj), Category.id_comp]

variable {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem pb_id (c : SiegPre h k ζ s) : SiegPB c c (𝟙 _) := by
  unfold SiegPB
  have : IsMonHom (Iso.refl c.A).hom := by
    show IsMonHom (𝟙 c.A)
    infer_instance
  refine ⟨𝟙 _, 𝟙 _, ?_, ?_, iso_pull_id c.isLB, fun a => by simp⟩
  · exact (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl
  · unfold Geo.Tor.IsSquare
    simp

theorem pb_comp {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (m' : SiegPB c'' c' f') : SiegPB c'' c (f' ≫ f) := by
  unfold SiegPB at m m' ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hg', ⟨ht1, ht2⟩, hl', hlev'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hg'.comp hg, ?_, ?_, fun a => ?_⟩
  · unfold Geo.Tor.IsSquare
    constructor
    · rw [Category.assoc, hs1, ← Category.assoc, ht1, Category.assoc]
    · rw [Category.assoc, hs2, ← Category.assoc, ht2, Category.assoc]
  · exact LBIso.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB c.isLB _) hl'
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull ψ₂ hl) (iso_pull_pull c.isLB φ₂ ψ₂))
  · rw [← Category.assoc, hlev' a, Category.assoc, hlev a, ← Category.assoc]

private theorem hom_ext_tensor_left_of_fst_snd_eq {T : Scheme.{0}} {A : Over T} {X : Scheme.{0}} {a b : X ⟶ (A ⊗ A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b := by
  have hw : b ≫ (A ⊗ A).hom = a ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← Category.assoc, h₁]
  have key : (Over.homMk a rfl : Over.mk (a ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk b hw := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₁
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₂
  exact congrArg CommaMorphism.left key

theorem pb_cancel {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (n : SiegPB c'' c (f' ≫ f)) : SiegPB c'' c' f' := by
  unfold SiegPB at m n ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hn, ⟨ht1, ht2⟩, hln, hlevn⟩ := n
  have hw : ψ ≫ c.A.hom = (c''.A.hom ≫ f') ≫ f := by rw [hn.1.w, Category.assoc]
  obtain ⟨χ, hχ1, hχ2⟩ : ∃ χ : c''.A.left ⟶ c'.A.left, χ ≫ φ = ψ ∧ χ ≫ c'.A.hom = c''.A.hom ≫ f' :=
    ⟨hg.1.lift ψ (c''.A.hom ≫ f') hw, hg.1.lift_fst _ _ _, hg.1.lift_snd _ _ _⟩
  have hgc : IsGrpPullback c''.A c'.A f' χ := IsGrpPullback.cancel hg (hn.congr rfl hχ1.symm) hχ2
  have q1 : ((fst c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (fst c''.A c''.A)]
    rfl
  have q2 : ((snd c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (snd c''.A c''.A)]
    rfl
  obtain ⟨χ₂, hq1, hq2⟩ : ∃ χ₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left,
      χ₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ χ ∧
      χ₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ χ := by
    refine ⟨(lift (Over.homMk _ q1 : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A) (Over.homMk _ q2)).left, ?_, ?_⟩
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have e : χ₂ ≫ φ₂ = ψ₂ := by
    apply hom_ext_tensor_left_of_fst_snd_eq
    · rw [Category.assoc, hs1, ← Category.assoc, hq1, Category.assoc, hχ1, ht1]
    · rw [Category.assoc, hs2, ← Category.assoc, hq2, Category.assoc, hχ1, ht2]
  refine ⟨χ, χ₂, hgc, ⟨hq1, hq2⟩, ?_, fun a => ?_⟩
  · rw [← e] at hln
    exact LBIso.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB c'.isLB _) hln
      (LBIso.symm (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull χ₂ hl) (iso_pull_pull c.isLB φ₂ χ₂)))
  · apply hg.1.hom_ext
    · simp only [Category.assoc, hχ1, hlevn, hlev]
    · simp only [Category.assoc, hχ2]
      rw [reassoc_of% (Over.w (c''.lev a)), Over.w (c'.lev a)]
      simp

theorem id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  intro h k B B' B'' _ _ _ ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f'
  exact ⟨pb_id c, fun m => ⟨fun m' => pb_comp m m', fun n => pb_cancel m n⟩⟩

end GlobalTheory.SiegelPullComp
end
end
