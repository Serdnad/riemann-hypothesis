module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.ProjFinite

theorem exists_relAmple_of_isProjBy {R : Type} [CommRing R] {A : Over (Sp R)} (h : GlobalTheory.AbLaw.IsProjBy A.hom) :
    ∃ H : LB A.left, H.IsLB ∧ Out.RelAmple A H := by
  obtain ⟨H, hH, m, s, hs⟩ := h
  have e : GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ) = H := by
    cases H
    simp [GlobalTheory.AbLaw.pw]
  have k : ∀ s : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy A.hom (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)) s → Out.RelAmple A H :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hH le_rfl s hs
  rw [e] at k
  exact ⟨H, hH, k s hs⟩

theorem isProjBy_of_fieldExtension {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)}
    {A : Over (Sp K)} [IsProper A₀.hom] {φ : A.left ⟶ A₀.left} (h : IsPullback φ A.hom A₀.hom (spMap i))
    {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB) (hw : LBIso L (L₀.pull φ))
    (hA : Out.RelAmple A L) : GlobalTheory.AbLaw.IsProjBy A₀.hom := by
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  have h₀ : Out.RelAmple A₀ L₀ :=
    (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull i h hL₀
      ((isAmpleLB_of_relAmple_of_isAffine A hL hA).of_lbIso (LB.isLB_pull hL₀ φ) hw.symm))
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K₀ A₀ L₀ hL₀).1 h₀
  exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL₀ d, n, s, hs⟩

theorem exists_isPullback {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
    {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S} (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, φ ≫ π₁ = π₂ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, h₁.lift_fst _ _ _, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_finite_isProjBy : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  let Ω := AlgebraicClosure K
  let a : K →+* Ω := algebraMap K Ω
  let B : Over (Sp Ω) := (Over.pullback (spMap a)).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap a)) B.hom A.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨H, hH, hamp⟩ := exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme Ω B hB)
  let K₀ : Subfield Ω := a.fieldRange
  let j : K →+* K₀ := a.rangeRestrictField
  have sq₀ := IsPullback.of_hasPullback A.hom (spMap j)
  obtain ⟨φ, hφ, sq⟩ := exists_isPullback sq₀ sqB (spMap K₀.subtype) (spMap_comp _ _)
  obtain ⟨s, hs⟩ := GlobalTheory.LBDescent.exists_lb_subfield Ω K₀ _ _ _ _ φ H hH sq
  let L : IntermediateField K Ω := IntermediateField.adjoin K (s : Set Ω)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have h : K₀ ≤ L.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  refine ⟨L, inferInstance, inferInstance, hfin, ?_⟩
  let C : Over (Sp L) := (Over.pullback (spMap (algebraMap K L))).obj A
  have sqC : IsPullback (pullback.fst A.hom (spMap (algebraMap K L))) C.hom A.hom (spMap (algebraMap K L)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨φ₁, hφ₁, sq₁⟩ := exists_isPullback sq₀ sqC (spMap (Subfield.inclusion h)) (spMap_comp _ _)
  obtain ⟨ψ, hψ, sq₂⟩ := exists_isPullback sqC sqB (spMap L.toSubfield.subtype) (spMap_comp _ _)
  obtain ⟨L₁, hL₁, hw⟩ := hs L.toSubfield h (IntermediateField.subset_adjoin K _) C.left C.hom φ₁ ψ sq₁
    (sq₀.hom_ext (by rw [Category.assoc, hφ₁, hψ, hφ]) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc, sq.w]
      exact congrArg _ (spMap_comp _ _))) sq₂.w
  have : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) sqC hA.proper
  exact isProjBy_of_fieldExtension L.toSubfield.subtype sq₂ hL₁ hH hw hamp

end GlobalTheory.ProjFinite

end
end

section

namespace GlobalTheory.LN

open IsLocalRing

theorem isIntegral_or_isIntegral_inv (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F]
    [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (x : F) :
    IsIntegral O x ∨ IsIntegral O x⁻¹ := by
  let K := FractionRing O
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := inferInstance
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : IsDiscreteValuationRing (integralClosure O L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  let f : L →ₐ[O] F := (IntermediateField.val L).restrictScalars O
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    have h : IsIntegral O y := hz ▸ z.2
    exact h.map f
  · right
    have h : IsIntegral O y⁻¹ := hz ▸ z.2
    have h' := h.map f
    rwa [map_inv₀] at h'

theorem exists_valuationSubring_isIntegral : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  intro O _ _ _ ϖ h F _ _ _ _ _
  rcases h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩
  · refine ⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    have ha : IsAlgebraic O x :=
      (IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    letI := hF.toField
    exact ha.isIntegral
  · haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc
    exact ⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩,
      fun x => Iff.rfl⟩

end GlobalTheory.LN
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.ThetaLocal

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_resG {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  have : X.basicOpen (resG X h a) = V ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_basicOpen_appLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ X.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ X.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_basicOpen_mul {U : X.Opens} (a b : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (a * b) ↔ x ∈ X.basicOpen a ∧ x ∈ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem nonvanishing_of_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) (p : M.ι)
    (hp : x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) :
    ∃ q, x ∈ X.basicOpen (coord s q) := by
  have hp' := X.basicOpen_le _ hp
  obtain ⟨q, hq⟩ := exists_chart hL x
  have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
    inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
  have e' := congrArg (fun a => x ∈ X.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
  have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp', hp'.1, hq⟩
  exact ⟨q, (e'.1 ⟨hx, hp⟩).2.2⟩

theorem exists_sec_pull {L : LB X} {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) (F : Y ⟶ X) (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {O : X.Opens} (hO : ⊤ ≤ F ⁻¹ᵁ O) (θ : ∀ i, Γ(X, O ⊓ L.U i)) (hθ : θ ∈ secOn L O) :
    ∃ θ' : L'.Sec, ∀ (y : Y) (i : L.ι), F y ∈ X.basicOpen (θ i) → ∃ k, y ∈ Y.basicOpen (θ'.f k) := by
  have hP : (L.pull F).IsLB := Semi.LB.isLB_pull hL F
  let e := isoOfGen hL' hP w hw
  let s : Γ(toMod (L.pull F), F ⁻¹ᵁ O) := mkSec
    (fun j => (F.appLE _ _ (pull_inf_le F O j)).hom (θ (j PUnit.unit))) (by
      intro i j
      have e : F ⁻¹ᵁ O ⊓ (L.pull F).U i ⊓ (L.pull F).U j ≤
          F ⁻¹ᵁ (O ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
        inf_le_inf (pull_inf_le F O i) (pull_U_le F j)
      have h := congrArg (F.appLE _ _ e).hom (hθ (i PUnit.unit) (j PUnit.unit))
      rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at h
      rw [resG_appLE, resG_appLE, resG_pull_g]
      exact h)
  have hcoord (j : (L.pull F).ι) : coord s j =
      (F.appLE _ _ (pull_inf_le F O j)).hom (θ (j PUnit.unit)) := by
    exact congrFun (coord_mkSec _ _) j
  let s' : Γ(toMod L', F ⁻¹ᵁ O) := e.inv.app _ s
  have hs : e.hom.app _ s' = s := by
    have := congrArg (fun q => q.app (F ⁻¹ᵁ O) s) e.inv_hom_id
    exact this
  let t : Γ(toMod L', ⊤) := (toMod L').presheaf.map (homOfLE hO).op s'
  refine ⟨⟨fun k => resG Y (le_inf le_top le_rfl) (coord t k), fun i j => ?_⟩, fun y i hy => ?_⟩
  · change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [resG_resG, resG_resG, coord_rel t i j _ _ le_rfl, resG_self]
  obtain ⟨k, hk⟩ := nonvanishing_of_iso hL' hP w hw s' y (fun _ => i) (by
    change y ∈ Y.basicOpen (coord (e.hom.app _ s') _)
    rw [hs]
    rw [hcoord (fun _ => i)]
    exact (mem_basicOpen_appLE F (pull_inf_le F O (fun _ => i)) (θ i) y).2
      ⟨⟨(X.basicOpen_le _ hy).1, mem_pull.2 (X.basicOpen_le _ hy).2⟩, hy⟩)
  refine ⟨k, ?_⟩
  dsimp only [t]
  rw [coord_map, mem_basicOpen_resG, mem_basicOpen_resG]
  have := (Y.basicOpen_le _ hk).2
  exact ⟨this, ⟨trivial, this⟩, hk⟩

theorem thetaNZ_of_pushInvertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H S t₀ h R _ _ ξ t m
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h (ξ (IsLocalRing.closedPoint R))
  have hall : ∀ y : Sp R, ξ y ∈ V := fun y =>
    ((IsLocalRing.specializes_closedPoint y).map ξ.continuous).mem_open V.isOpen hV
  have hc : IsPullback m.cm.F t.G.hom t₀.G.hom ξ := m.cart.1
  have hpt : ∀ g : t.G.left, t₀.G.hom (m.cm.F g) = ξ (t.G.hom g) := fun g =>
    congrArg (fun q => q g) hc.w
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨θ', h'⟩ := exists_sec_pull t₀.PP.isLB t.PP.isLB m.cm.F w hw (O := t₀.G.hom ⁻¹ᵁ V)
    (fun g _ => by
      change t₀.G.hom (m.cm.F g) ∈ V
      rw [hpt]; exact hall _) θ hθ
  refine ⟨θ', fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := h2 (ξ y) (hall y)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hc g y hg
  obtain ⟨k, hk⟩ := h' z i (by rw [hz₁]; exact hi)
  exact ⟨z, k, hz₂, hk⟩

end GlobalTheory.ThetaLocal
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PolFrames

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)

theorem exists_pullSec [GrpObj G] (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s' : LB.Sec (LPow G L (N : ℤ) T'),
    IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s' ∧
    ∀ (z : (T' ⊗ G).left) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s', h0, h1⟩ := SectionLimit.exists_pull (K := Fin 1) s (h ▷ G).left (fun _ => (snd T' G).left)
    (fun _ => congrArg CommaMorphism.left (whiskerRight_snd h G))
  exact ⟨s', fun j => h0 j _, fun z J hJ => (h1 _ _ z J hJ).trans (by rw [Category.id_comp])⟩

theorem sval_of_isPullSec [GrpObj G] {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')}
    (hs : IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s') (z : (T' ⊗ G).left) (J) (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s'', h0, h1⟩ := exists_pullSec G L N h s
  obtain rfl : s' = s'' := SecOps.sec_ext fun j => (hs j).trans (h0 j).symm
  exact h1 z J hJ

theorem lin_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) :
    Lin G L N h b c s ↔ ∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T') = SecM.ofSec G s := by
  let σ := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b'
  have ev : ∀ j, (∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T')).1 j = σ.f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hv : Lin G L N h b c σ := fun z J hJ => by
    rw [SectionScalarValuation.sval_lin (s := σ) (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (sval_of_isPullSec G L N h (hb i) z J hJ)
    exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  constructor
  · intro H
    refine Subtype.ext (funext fun j => (ev j).trans ?_)
    exact sec_ext_val hL (fun y J hJ => (hv y J hJ).trans (H y J hJ).symm) j
  · intro H
    obtain rfl : s = σ := SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val H) j).symm.trans (ev j)
    exact hv

theorem basisAlong_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i)) :
    BasisAlong G L N h b ↔
      LinearIndependent Γ(T'.left, ⊤) (fun i => (SecM.ofSec G (b' i) : SecM G L N T')) ∧
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec G (b' i) : SecM G L N T')) = ⊤ := by
  unfold BasisAlong
  simp only [lin_iff G L N h hL hb]
  constructor
  · intro H
    refine ⟨Fintype.linearIndependent_iffₛ.2 fun c c' e i => ?_, eq_top_iff.2 fun x _ => ?_⟩
    · exact congrFun ((H (SecM.toSec G (∑ i, c' i • (SecM.ofSec G (b' i) : SecM G L N T')))).unique e rfl) i
    · exact (Submodule.mem_span_range_iff_exists_fun _).2 (H (SecM.toSec G x)).exists
  · rintro ⟨hli, hsp⟩ s
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec G s ∈ ⊤))
    exact ⟨r, hr, fun r' hr' => funext fun i => Fintype.linearIndependent_iffₛ.1 hli _ _ (hr'.trans hr.symm) i⟩

theorem exists_local_basisAlong (hS : SecBaseChangeSt) [IsLocallyNoetherian S] (P : PolAV S) (hN : 1 ≤ N) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk V.ι)),
      ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ V.ι) ⟶ Over.mk V.ι) b := by
  obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
  have key : ∀ f : V.toScheme ⟶ S, (overRes (T := baseOver S) V).hom = f →
      ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk f)), ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ f) ⟶ Over.mk f) b := by
    rintro _ rfl
    refine ⟨b, fun R _ χ => ?_⟩
    choose b' hb' _ using fun i => exists_pullSec P.A P.L N (homAt χ) (b i)
    exact (basisAlong_iff P.A P.L N (homAt χ) P.isLB hb').2 (hb R χ b' hb')
  exact ⟨V, hV, key V.ι (Category.comp_id _)⟩

end GlobalTheory.LN.PolFrames
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.GenericPoint

theorem exists_extend {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (g : V →+* K) : ∃ g' : F →+* K, g'.comp V.subtype = g := by
  have hinj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    by_contra h0
    have hF : IsAlgebraic ℤ (a : F) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hV : IsAlgebraic ℤ a :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 hF
    refine Ideal.comap_ne_bot_of_algebraic_mem h0 ha hV (eq_bot_iff.2 fun n hn => ?_)
    have e : (n : K) = 0 := by simpa using hn
    exact_mod_cast e
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] {U : Set (Sp R)} (hU : IsOpen U) (h : U.Nonempty)
    (q : Sp (FractionRing R)) : jK R q ∈ U := by
  obtain ⟨x, hx⟩ := h
  refine Specializes.mem_open (x := jK R q) (y := x) ?_ hU hx
  refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun a ha => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  have h1 : algebraMap R (FractionRing R) a ∈ q.asIdeal := ha
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
  rw [h1]; exact Ideal.zero_mem _

theorem lbIso_pull {W X Y : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y)
    {a' : W ⟶ X} (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ _ _ j fun _ => ha) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_of_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem polAt_of_lift {X S Z : Scheme.{0}} {T : SAB H X} {t : SAB H S} {t' : SAB H Z} {ξ : S ⟶ X} {j : Z ⟶ X}
    (m : SABMap t T ξ) (m' : SABMap t' T j) (hp : IsProper t'.G.hom) (hA : RelAmple t'.G t'.PP.L)
    (hK : KTriv t'.G t'.PP.L) {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Z) (h : y ≫ j = x ≫ ξ) : PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) T.G (x ≫ ξ) (pullback.fst t.G.hom x ≫ m.φ) :=
    (isGrpPullback_pullback t.G x).comp m.cart
  have w : (pullback.fst t.G.hom x ≫ m.φ) ≫ T.G.hom = (pullback.snd t.G.hom x ≫ y) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m'.φ = pullback.fst t.G.hom x ≫ m.φ ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ y :=
    ⟨_, m'.cart.1.lift_fst _ _ w, m'.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G y ψ :=
    m'.cart.cancel (g₁.congr h.symm h₁.symm) h₂
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (t'.PP.L.pull ψ) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB T.PP.isLB _) (pull_isLB t'.PP.isLB _)
      (lbIso_pull (lbIso_of_sabMap m) _ rfl) (lbIso_pull (lbIso_of_sabMap m') _ h₁.symm).symm
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp
  have hq := amplePt Z K y t'.G ((Over.pullback x).obj t.G) ψ g₂ t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    t'.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

end GlobalTheory.LN.GenericPoint


open GlobalTheory.LN.GenericPoint in
theorem GlobalTheory.LN.generic_point_of_meets_abLocus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y p ⟨_, _, _, ⟨U, hU, _⟩, _⟩ R _ _ _ ξ t m hne
  have hop : IsOpen (ξ ⁻¹' abLocus Y.t.G) := by
    rw [← hU]; exact U.isOpen.preimage ξ.continuous
  have := c.fin
  obtain ⟨g, hg⟩ := exists_extend (K := FractionRing R) (c.V W₀) (Spec.preimage ((jK R ≫ ξ) ≫ Y.s)).hom
  have sq : (jK R ≫ ξ) ≫ Y.s = spMap g ≫ spMap (c.V W₀).subtype := by
    rw [← Geo.Tor.spMap_comp, hg]
    exact (Spec.map_preimage _).symm
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ sq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact jK_mem hop hne q
  have hy : IsOpenImmersion.lift Y.jQ _ hr ≫ Y.j = jK R ≫ ξ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  exact ⟨⟨_, hy⟩, polAt_of_lift m Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv _ _ hy,
    Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi m.cart.1 x⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_unit_weightZero_integral_coords : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  first | exact @GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | exact GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | (intros; apply GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point <;> assumption)
end
