module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ValBound

theorem exists_maximalIdeal_pow_le_map_stalkMap (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    ∃ e : ℕ, maximalIdeal (X.presheaf.stalk x) ^ e ≤
      (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro P ⟨hP, hPp⟩
  let q : Sp (X.presheaf.stalk x) := ⟨P, hPp⟩
  have hcomap : P.comap (f.stalkMap x).hom = maximalIdeal _ :=
    ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.1 hP)).symm
  have h1 : Spec.map (f.stalkMap x) q = closedPoint (Y.presheaf.stalk (f x)) := by
    exact PrimeSpectrum.ext hcomap
  have e₁ := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  have hy : f (X.fromSpecStalk x q) = f x := by
    have := congrArg (fun g => g q) e₁
    simp only [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint] at this
    exact this.symm
  have hs : X.fromSpecStalk x q ⤳ x := by
    have : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨_, hy⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr hs
  have h3 : X.fromSpecStalk x q = X.fromSpecStalk x (closedPoint _) :=
    (congrArg Subtype.val h2.eq).trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 : q = closedPoint _ := (X.fromSpecStalk x).isEmbedding.injective h3
  exact (congrArg PrimeSpectrum.asIdeal h4).ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_valHom {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    ∃ φ : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p, (∀ a, t.val a = φ a) ∧ ∀ a, ‖φ a‖ ≤ 1 :=
  ⟨(OO p).subtype.comp ((RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom),
    fun a => by
      show X₁.M.val _ ((X₁.M.stalkEquiv z₁ a : X₁.Ω₁)) = _
      rw [RatModel.val_gPt t.cen]
      rfl,
    fun a => (mem_OO_iff _).1 (Subtype.prop _)⟩

theorem val_germ {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (t : UCTrait X p z) {V : X.M.Z.Opens}
    (hz : z ∈ V) (g : Γ(X.M.Z, V)) :
    t.val (X.M.Z.presheaf.germ V z hz g) = valF (gPt p ≫ t.y) V g := by
  rw [UCTrait.val, RatModel.stalkHom_germ]
  refine RatModel.val_valF ?_ g
  rintro _ ⟨w, rfl⟩
  exact (RatModel.gPt_specializes t.cen w).mem_open V.isOpen hz

theorem val_stalkMap_germ {X₁ X' : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {z' : X'.M.Z}
    (t : UCTrait X₁ p z₁) (t' : UCTrait X' p z') (hc : t.y ≫ X₁.π = t'.y ≫ X'.π)
    {U : C.Z.Opens} (hU' : X'.π z' ∈ U) (hU₁ : X₁.π z₁ ∈ U) (s : Γ(C.Z, U)) :
    t'.val (X'.π.stalkMap z' (C.Z.presheaf.germ U _ hU' s)) =
      t.val (X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s)) := by
  rw [Scheme.Hom.germ_stalkMap_apply, val_germ t' (V := X'.π ⁻¹ᵁ U) hU', val_germ t hU₁]
  have e1 := GlobalTheory.Points.valR_comp (gPt p ≫ t'.y) X'.π U s
  have e2 := GlobalTheory.Points.valR_comp (gPt p ≫ t.y) X₁.π U s
  rw [Category.assoc, ← hc, ← Category.assoc] at e1
  exact e1.symm.trans e2

theorem exists_pow_norm_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ X' z₁
  have hnoeth : ∀ z' : X'.M.Z, IsNoetherianRing (X'.M.Z.presheaf.stalk z') := fun z' => by
    have : IsDedekindDomain X'.o₁ := ArithBase.ded (Ω := X'.Ω₁)
    have := X'.M.lft
    have : IsLocallyNoetherian X'.M.Z := LocallyOfFiniteType.isLocallyNoetherian X'.M.s
    infer_instance
  haveI := X'.fin
  have hfin := X'.π.finite_preimage_singleton (X₁.π z₁)
  choose e he using fun z' : X'.M.Z => haveI := hnoeth z'; exists_maximalIdeal_pow_le_map_stalkMap X'.M.Z C.Z X'.π z'
  refine ⟨hfin.toFinset.sup e + 1, by omega, ?_⟩
  intro p _ t z' t' hc h' hh'
  have hz' : X'.π z' = X₁.π z₁ := by
    have := congrArg (fun g : Sp (OO p) ⟶ C.Z => g (cPt p)) hc
    simp only [Scheme.Hom.comp_apply, t.cen, t'.cen] at this
    exact this.symm
  have hmem : z' ∈ hfin.toFinset := by simp [hz']
  have hle : e z' ≤ hfin.toFinset.sup e + 1 := (Finset.le_sup hmem).trans (Nat.le_succ _)
  have hpow : h' ^ (hfin.toFinset.sup e + 1) ∈ (maximalIdeal _).map (X'.π.stalkMap z').hom :=
    he z' (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hh' _))
  obtain ⟨φ', hφ', hφ'1⟩ := exists_valHom t'
  obtain ⟨φ₁, hφ₁, -⟩ := exists_valHom t
  have key : ∀ x ∈ (maximalIdeal (C.Z.presheaf.stalk (X'.π z'))).map (X'.π.stalkMap z').hom,
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖φ' x‖ ≤ ‖φ₁ h‖ := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨U, hU, s, rfl⟩ := C.Z.presheaf.germ_exist g
      have hU₁ : X₁.π z₁ ∈ U := hz' ▸ hU
      refine ⟨X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s), ?_, ?_⟩
      · rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have h1 : z₁ ∈ X₁.M.Z.basicOpen (X₁.π.app U s) := (X₁.M.Z.mem_basicOpen _ z₁ hU₁).2 hu
        rw [← Scheme.preimage_basicOpen] at h1
        have h2 : X₁.π z₁ ∈ C.Z.basicOpen s := h1
        rw [← hz'] at h2
        exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hg)) ((C.Z.mem_basicOpen s _ hU).1 h2)
      · rw [← hφ', ← hφ₁, val_stalkMap_germ t t' hc hU hU₁ s]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      rcases le_total ‖φ₁ a‖ ‖φ₁ b‖ with hab | hab
      · exact ⟨b, hb, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hxa.trans hab) hyb)⟩
      · exact ⟨a, ha, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxa (hyb.trans hab))⟩
    | smul b x _ hx =>
      obtain ⟨a, ha, hxa⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖φ' b‖ * ‖φ' x‖ ≤ 1 * ‖φ' x‖ := mul_le_mul_of_nonneg_right (hφ'1 b) (norm_nonneg _)
        _ = ‖φ' x‖ := one_mul _
        _ ≤ ‖φ₁ a‖ := hxa
  obtain ⟨h, hh, hnorm⟩ := key _ hpow
  refine ⟨h, hh, ?_⟩
  rw [hφ', hφ₁, ← norm_pow, ← map_pow]
  exact hnorm

end GlobalTheory.UPoinc.ValBound
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc.ChartAt

theorem spec_ext_of_isFractionRing {A K T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing T] (h₁ h₂ : Sp T ⟶ Sp K) (e : h₁ ≫ spMap (algebraMap A K) = h₂ ≫ spMap (algebraMap A K)) : h₁ = h₂ := by
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective h₁
  obtain ⟨g₂, rfl⟩ := Spec.map_surjective h₂
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (nonZeroDivisors A) e'

theorem exists_int_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {cf : Coeff l} (C : UCompact Xo cf) {a : C.o} (ha : a ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ a ∣ (n : C.o) := by
  haveI := C.ded
  have h1 : IsAlgebraic ℚ (C.b a) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 : IsAlgebraic ℤ (C.b a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ cf.F).2 h1
  have h3 : IsAlgebraic ℤ a := (isAlgebraic_algHom_iff C.b.toIntAlgHom C.inj).1 h2
  have h4 := Ideal.comap_ne_bot_of_algebraic_mem ha (Ideal.mem_span_singleton_self a) h3
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨n, hn0, ?_⟩
  have := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hn)
  simpa using this

end GlobalTheory.UPoinc.ChartAt

namespace GlobalTheory.UPoinc.ChartAt

theorem exists_affine_chart_ratLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw l Xo cf C X w hw
  haveI := X.ar.char
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  set V' : X.M.Z.Opens := X.π ⁻¹ᵁ ⟨V, hVo⟩ with hV'def
  have hwV : w ∈ V' := by
    obtain ⟨x, hx⟩ := hw
    show X.π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) (U := V') hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  set R₀ := X.M.ringOn U with hR₀
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ X.π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : cf.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o cf.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o cf.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hU, hwU, ?_⟩
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  have hfst : spMap (ratHull R₀).val.toRingHom ≫ g = X.uΩ ≫ C.i := by
    show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ X.π = _
    rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf, X.comp]
    simp only [USetup.uΩ, Category.assoc]
  rw [← cancel_mono C.iF, Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hfst]
    simp only [UCompact.i, Category.assoc]
  · have key : spMap (ratHull R₀).val.toRingHom ≫ g' ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b =
        X.uΩ ≫ C.iF ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b := by
      rw [← pullback.condition, ← Category.assoc g', pullback.lift_fst, reassoc_of% hfst]
      simp only [UCompact.i, Category.assoc]
    exact spec_ext_of_isFractionRing (A := C.o) _ _ (by simpa only [Category.assoc] using key)

end GlobalTheory.UPoinc.ChartAt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_genericPoint_closure_eq_of_isClopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ η ∈ genericPoints (Xo.XF c), closure {C.i η} = A := by
  intro E _ _ _ H Dw _ l Xo c C A hA hirr hne
  obtain ⟨_, hyA, y, rfl⟩ := hne
  have hζ : IsGenericPoint hirr.genericPoint A := hirr.isGenericPoint_genericPoint hA.isClosed
  set ζ := hirr.genericPoint
  have h1 : ζ ⤳ C.i y := hζ.specializes hyA
  have hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y)) := by
    have := congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))
    simpa using this
  have hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥ := by
    intro q
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
    show Ideal.comap C.b q.asIdeal = ⊥
    rw [hq]
    exact Ideal.comap_bot_of_injective C.b C.inj
  have h2 : C.z ζ = C.z (C.i y) := by
    have hs : C.z ζ ⤳ C.z (C.i y) := h1.map C.z.continuous
    have hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
    rw [hcomp, hbot] at hle
    apply PrimeSpectrum.ext
    rw [hcomp, hbot]
    exact le_bot_iff.1 hle
  obtain ⟨p', hp', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ
    (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
    infer_instance
  have h3 : p' ⤳ C.iF y := by
    apply (IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1
    rw [hp']
    exact h1
  haveI := C.iF_open
  obtain ⟨η, hη⟩ := h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  have hCi : C.i η = ζ := by
    rw [← hp', ← hη]
    rfl
  have hinj : Function.Injective C.i := (IsPreimmersion.isEmbedding C.i).injective
  refine ⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩
  have hη' : IsGenericPoint hT.closure.genericPoint (closure T) :=
    hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hs : hT.closure.genericPoint ⤳ η := hη'.specializes (subset_closure (hle (subset_closure rfl)))
  have hs' : C.i hT.closure.genericPoint ⤳ ζ := hCi ▸ hs.map C.i.continuous
  have hmem : C.i hT.closure.genericPoint ∈ A := hs'.mem_open hA.isOpen hζ.mem
  have heq : hT.closure.genericPoint = η := hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)
  rw [← heq, hη']
  exact subset_closure

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ker_eq_bot_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K]
    [CharZero K] (φ : o →+* K) : RingHom.ker φ = ⊥ := by
  by_contra h
  haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h
  letI := Ideal.Quotient.field (RingHom.ker φ)
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ)
    (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))

theorem UCompact.range_subset_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) {K : Type} [Field K] [CharZero K]
    (x : Sp K ⟶ Sp C.o) : Set.range x ⊆ Set.range (spMap C.b) := by
  haveI := C.ded
  haveI := C.ft
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  rintro _ ⟨w, rfl⟩
  refine ⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩
  show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal
  rw [Subsingleton.elim w (⊥ : PrimeSpectrum K)]
  exact ((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm

theorem exists_open_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  intro E _ _ _ H Dw l Xo c C
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨U, hU, hUe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := hUe ▸ ⟨x, rfl⟩
    exact this
  · intro p _ y hy
    rintro _ ⟨w, rfl⟩
    have h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :) := by
      rw [Scheme.Pullback.range_fst]
      exact C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := h1
    have h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := by
      show _ ∈ U
      rw [ht]
      exact hy ⟨w, rfl⟩
    rw [hUe] at h2
    obtain ⟨x, rfl⟩ := h2
    exact ⟨x, ht⟩

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.TraitUniq

theorem jK_comp_spMap {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (fK : FractionRing V →+* FractionRing W) (hK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) :
    spMap fK ≫ jK V = jK W ≫ spMap f := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact hK a

theorem exists_common_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∃ tW : SAB H (Sp W), Nonempty (SABMap tW T.t (spMap f)) ∧ Nonempty (SABMap tW T'.t (spMap f')) := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' _ hdvr _ _ _ _ hK hK' hy
  obtain ⟨tW, ⟨mW⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) T.t
  obtain ⟨tW', ⟨mW'⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f') T'.t
  obtain ⟨tK, ⟨a⟩, ⟨b⟩⟩ := T.gen
  obtain ⟨tK', ⟨a'⟩, ⟨b'⟩⟩ := T'.gen
  obtain ⟨uK, ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap fK ≫ T.y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨c₁⟩ := GlobalTheory.TraitOrder.cancel rfl b n
  have e' : spMap fK' ≫ T'.y ≫ pullback.fst _ _ = spMap fK ≫ T.y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hy, Category.assoc]
  obtain ⟨c₂⟩ := GlobalTheory.TraitOrder.cancel e' b' n
  obtain ⟨d₁⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f fK hK) a c₁
  obtain ⟨d₂⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f' fK' hK') a' c₂
  obtain ⟨x₁⟩ := GlobalTheory.TraitOrder.cancel rfl mW d₁
  obtain ⟨x₂⟩ := GlobalTheory.TraitOrder.cancel rfl mW' d₂
  obtain ⟨ψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map W (FractionRing W) tW tW' uK x₁ x₂
  exact ⟨tW, ⟨mW⟩, GlobalTheory.TraitOrder.comp (Category.id_comp _) mW' ψ⟩

end GlobalTheory.UPoinc.TraitUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_twoHom_normalisedAtOrigin : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  first | exact @GlobalTheory.Mum.Two.exists_lamVal_origin_two | exact GlobalTheory.Mum.Two.exists_lamVal_origin_two | (intros; apply GlobalTheory.Mum.Two.exists_lamVal_origin_two <;> assumption)
end
