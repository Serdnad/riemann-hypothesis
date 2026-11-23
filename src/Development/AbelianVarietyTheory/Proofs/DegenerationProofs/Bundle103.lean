module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime] {X Y Z : Scheme.{0}}

abbrev z₀ (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)

def sn (p : ℕ) [Fact p.Prime] : (Sp (PadicAlgCl p)).presheaf.stalk (z₀ p) →* ℝ :=
  (normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (ev (z₀ p)).toRingHom.toMonoidHom

def un (p : ℕ) [Fact p.Prime] : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ →* ℝ :=
  (sn p).comp (Units.coeHom _)

theorem sn_val (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : sn p u.val = un p u := rfl

theorem un_pos (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : 0 < un p u :=
  norm_pos_iff.2 (u.isUnit.map (ev (z₀ p))).ne_zero

theorem sn_gs (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)) :
    sn p (gs x (z₀ p) U a) = ‖valF x U a‖ := congrArg norm (ev_gs x _ h a)

theorem un_gm (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm x (z₀ p) U a) = ‖valF x U a.val‖ := congrArg norm (ev_gm x _ h a)

theorem gs_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem mem_of_cPt (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : ⊤ ≤ b ⁻¹ᵁ U :=
  fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (b ⁻¹ᵁ U).isOpen h

theorem gen_mem (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : (gPt p ≫ b) (z₀ p) ∈ U :=
  mem_of_cPt b h (show gPt p (z₀ p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)

theorem isUnit_iff_norm (v : OO p) : IsUnit v ↔ ‖(v : PadicAlgCl p)‖ = 1 := by
  have le : ∀ u : OO p, ‖(u : PadicAlgCl p)‖ ≤ 1 := fun u =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ‖(v : PadicAlgCl p)‖ * ‖(u : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun t : OO p => ‖(t : PadicAlgCl p)‖) hu).trans norm_one
    have := le u
    have := le v
    have := norm_nonneg (v : PadicAlgCl p)
    nlinarith
  · intro h
    have h0 : (v : PadicAlgCl p) ≠ 0 := norm_pos_iff.1 (by rw [h]; exact one_pos)
    refine IsUnit.of_mul_eq_one ⟨(v : PadicAlgCl p)⁻¹,
      (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).2 (by rw [norm_inv, h, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)

theorem sn_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)) :
    sn p (gs (gPt p ≫ b) (z₀ p) U a) ≤ 1 ∧
      (sn p (gs (gPt p ≫ b) (z₀ p) U a) = 1 ↔ b (cPt p) ∈ X.basicOpen a) := by
  have h' := mem_of_cPt b h
  have hg := gen_mem b h
  let v : OO p := (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom.hom ((b.appLE U ⊤ h').hom a)
  have e : valF (gPt p ≫ b) U a = (v : PadicAlgCl p) := by
    rw [valF, dite_eq_left ((top_le_iff_mem _ U _).2 hg)]
    have e₁ := Scheme.Hom.appLE_comp_appLE (gPt p) b U ⊤ ⊤ h' le_top
    have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (OO p).subtype)
    have e₃ : (gPt p).appLE ⊤ ⊤ le_top = (gPt p).appTop := (Scheme.Hom.app_eq_appLE _).symm
    rw [← e₁, e₃]
    exact congrArg (fun q => q.hom ((b.appLE U ⊤ h').hom a)) e₂
  rw [sn_gs _ hg, e]
  refine ⟨(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 v.2, (isUnit_iff_norm v).symm.trans ?_⟩
  have e₄ : (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) = PrimeSpectrum.basicOpen v :=
    basicOpen_eq_of_affine' _
  have e₅ := Scheme.basicOpen_appLE b ⊤ U h' a
  have e₆ : cPt p ∈ (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) ↔ b (cPt p) ∈ X.basicOpen a := by
    erw [e₅]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [← e₆, e₄]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem un_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm (gPt p ≫ b) (z₀ p) U a) = 1 := by
  rw [← sn_val, ← gs_unit _ _ _ (gen_mem b h)]
  refine (sn_integral b h a.val).2.2 ?_
  rw [Scheme.basicOpen_of_isUnit _ a.isUnit]
  exact h

theorem un_eq_of_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (r : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ)
    (hU : ∀ x, ∃ a, x ∈ U a)
    (hr : ∀ a a' x, j x ∈ U a → j x ∈ U a' →
      gm (𝟙 HK) x _ (r a) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a')) :
    ∃ u : Γ(Sp K, ⊤)ˣ, ∀ (c : Sp (OO p) ⟶ H) (cK : Sp (PadicAlgCl p) ⟶ HK), cK ≫ j = gPt p ≫ c → ∀ a,
      c (cPt p) ∈ U a → un p (gm cK (z₀ p) _ (r a)) = un p (gm (cK ≫ fK) (z₀ p) ⊤ u) := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let eK : Sp K ⟶ HK := hK.lift (spMap (algebraMap V K) ≫ e) (𝟙 _) (by simp [he])
  have h₁ : eK ≫ j = spMap (algebraMap V K) ≫ e := hK.lift_fst _ _ _
  have h₂ : eK ≫ fK = 𝟙 _ := hK.lift_snd _ _ _
  obtain ⟨a₀, ha₀⟩ := hU (e (IsLocalRing.closedPoint V))
  have hA : ⊤ ≤ e ⁻¹ᵁ U a₀ := fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (e ⁻¹ᵁ U a₀).isOpen ha₀
  have hA'' : ⊤ ≤ eK ⁻¹ᵁ (j ⁻¹ᵁ U a₀) := fun y _ => by
    show (eK ≫ j) y ∈ U a₀
    rw [h₁]
    exact hA (show spMap (algebraMap V K) y ∈ (⊤ : (Sp V).Opens) from trivial)
  let u : Γ(Sp K, ⊤)ˣ := res hA'' (pullU eK _ (r a₀))
  let r' : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ := fun a => r a * res (le_top : j ⁻¹ᵁ U a ≤ fK ⁻¹ᵁ ⊤) (pullU fK ⊤ u⁻¹)
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a, j (q z) ∈ U a →
      gm q z _ (r' a) = gm q z _ (r a) * (gm (q ≫ fK) z ⊤ u)⁻¹ := fun Z q z a h =>
    (map_mul _ _ _).trans (congrArg (_ * ·) (((gm_res q z _ h _).trans (gm_pull q fK z ⊤ trivial _)).trans
      (map_inv _ _)))
  obtain ⟨s, ⟨hs₁, -, hs₂⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U) (g := fun a b => (g a b).val)
    (W := fun a => j ⁻¹ᵁ U a) (fun _ => rfl) hU (fun a b => (g a b).isUnit) (r := fun a => (r' a).val)
    (fun a b => fn_ext fun x hx => by
      refine (gs_res (𝟙 HK) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 HK) x _ hx _ _).trans
        (congrArg₂ (· * ·) (gs_appLE j _ _ _ (𝟙 HK) x hx _) (gs_res (𝟙 HK) x _ hx _))).symm)
      rw [Category.id_comp, gs_unit (𝟙 HK) x _ hx.1, gs_unit (𝟙 HK) x _ hx.2, gs_unit j x (U a ⊓ U b) hx,
        v _ (𝟙 HK) x a hx.1, v _ (𝟙 HK) x b hx.2, hr a b x hx.1 hx.2, _root_.mul_assoc, Units.val_mul])
    (fun a => (r' a).isUnit) he h₁ (A := ⊤) trivial hA (A' := ⊤) rfl hA'' (u := 1) isUnit_one (by
      rw [map_one]
      refine fn_ext fun y hy => ?_
      refine Eq.trans ?_ (gs_appLE eK _ _ _ (𝟙 _) y hy _).symm
      rw [Category.id_comp, gs_unit eK y _ (hA'' hy), v _ eK y a₀ (hA'' hy), h₂]
      have : gm (𝟙 (Sp K)) y ⊤ u = gm eK y _ (r a₀) := by
        refine ((gm_res _ y _ hy _).trans (gm_pull (𝟙 _) eK y _ (hA'' hy) _)).trans ?_
        rw [Category.id_comp]
      rw [this, mul_inv_cancel, gs_eq _ y ⊤ hy, map_one, map_one, Units.val_one])
  refine ⟨u, fun c cK hc a ha => ?_⟩
  have hm : j (cK (z₀ p)) ∈ U a := by
    show (cK ≫ j) _ ∈ U a
    rw [hc]
    exact gen_mem c ha
  have e₁ : un p (gm cK (z₀ p) _ (r' a)) = 1 := by
    rw [← un_integral c ha (hs₁ a).unit, ← hc]
    refine congrArg (un p) (Units.ext ?_)
    rw [← gs_unit cK _ _ hm, ← gs_unit (cK ≫ j) _ _ hm, ← hs₂ a]
    exact gs_appLE j _ _ _ cK _ hm _
  rw [v _ cK _ a hm, map_mul, map_inv] at e₁
  exact (mul_inv_eq_one₀ (un_pos _).ne').1 e₁

theorem un_eq_of_fine_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α κ : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (W : α → κ → HK.Opens)
    (r : ∀ a b, Γ(HK, W a b)ˣ) (hU : ∀ x, ∃ a, x ∈ U a) (hW : ∀ a x, j x ∈ U a ↔ ∃ b, x ∈ W a b)
    (hr : ∀ a b a' b' x, x ∈ W a b → x ∈ W a' b' →
      gm (𝟙 HK) x _ (r a b) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a' b'))
    {c c' : Sp (OO p) ⟶ H} {cK cK' : Sp (PadicAlgCl p) ⟶ HK} (hc : cK ≫ j = gPt p ≫ c) (hc' : cK' ≫ j = gPt p ≫ c')
    (h : c ≫ f = c' ≫ f) {a a' : α} {b b' : κ} (ha : c (cPt p) ∈ U a) (ha' : c' (cPt p) ∈ U a')
    (hb : cK (z₀ p) ∈ W a b) (hb' : cK' (z₀ p) ∈ W a' b') :
    un p (gm cK (z₀ p) _ (r a b)) = un p (gm cK' (z₀ p) _ (r a' b')) := by
  have le : ∀ a b, W a b ≤ j ⁻¹ᵁ U a := fun a b x hx => (hW a x).2 ⟨b, hx⟩
  choose R hR using fun a => glue_unit (j ⁻¹ᵁ U a) (W a) (le a)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ((hW a x).1 hx)) (r a) (fun b b' x hx => by
      rw [hr a b a b' x hx.1 hx.2, mul_eq_right.1 (hr a b a b x hx.1 hx.1).symm, _root_.one_mul])
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a b, q z ∈ W a b → gm q z _ (r a b) = gm q z _ (R a) :=
    fun Z q z a b h => by rw [← hR a b, gm_res q z _ h]
  obtain ⟨u, hu⟩ := un_eq_of_charts (p := p) hK e he U g R hU fun a a' x hx hx' => by
    obtain ⟨b, hb⟩ := (hW a x).1 hx
    obtain ⟨b', hb'⟩ := (hW a' x).1 hx'
    rw [← v _ (𝟙 HK) x a b hb, ← v _ (𝟙 HK) x a' b' hb', hr a b a' b' x hb hb']
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_id_snd (f := spMap (algebraMap V K)))
  rw [v _ _ _ _ _ hb, v _ _ _ _ _ hb', hu c cK hc a ha, hu c' cK' hc' a' ha']
  refine congrArg (fun q => un p (gm q (z₀ p) ⊤ u)) ?_
  rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, Category.assoc, ← hK.w, ← Category.assoc, hc,
    ← Category.assoc, hc', Category.assoc, Category.assoc, h]

theorem exists_norm_ext {L : LB X} (hL : L.IsLB) (x : Sp (PadicAlgCl p) ⟶ X) (S : L.ι → ℝ → Prop)
    (hS : ∀ j t, S j t → 0 < t ∧ x (z₀ p) ∈ L.U j)
    (hS' : ∀ j t j' t', S j t → S j' t' → un p (gm x (z₀ p) _ (L.g j j')) * t = t') :
    ∃ n : L.ι → ℝ, (∀ j, 0 < n j) ∧ (∀ j j', x (z₀ p) ∈ L.U j → x (z₀ p) ∈ L.U j' →
      un p (gm x (z₀ p) _ (L.g j j')) * n j = n j') ∧ ∀ j t, S j t → n j = t := by
  classical
  obtain ⟨i, t₀, h₀, hi, H⟩ : ∃ i t₀, 0 < t₀ ∧ x (z₀ p) ∈ L.U i ∧
      ∀ j t, S j t → un p (gm x (z₀ p) _ (L.g i j)) * t₀ = t := by
    by_cases h : ∃ j t, S j t
    · obtain ⟨i, t₀, h⟩ := h
      exact ⟨i, t₀, (hS _ _ h).1, (hS _ _ h).2, fun j t h' => hS' _ _ _ _ h h'⟩
    · obtain ⟨i, hi⟩ := exists_chart hL (x (z₀ p))
      exact ⟨i, 1, one_pos, hi, fun j t h' => absurd ⟨j, t, h'⟩ h⟩
  refine ⟨fun j => un p (gm x (z₀ p) _ (L.g i j)) * t₀, fun j => mul_pos (un_pos _) h₀, fun j j' hj hj' => ?_, H⟩
  rw [← _root_.mul_assoc, ← map_mul, _root_.mul_comm (gm x _ _ _), gm_cocycle hL x _ hi hj hj']

end GlobalTheory.ZJ.TestNorm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.SquareLevel

open GlobalTheory.ThetaCoord

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem labelSymp_eq (g M : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) :
    labelSymp (a ∘ (halves g).symm) (b ∘ (halves g).symm) = eStd g M a b := by
  have h₁ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inl, if_neg (by omega), if_neg (by omega)]
  have h₂ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₃ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_neg (by omega), if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₄ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inr, halves_inr, if_neg (by omega), if_neg (by omega)]
  rw [labelSymp, ← (halves g).sum_comp]
  simp_rw [← (halves g).sum_comp]
  simp [Fintype.sum_sum_type, h₁, h₂, h₃, h₄, eStd, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {S : Scheme.{0}}

theorem linComb_pow_left {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb (fun i => y i ^ M) c = linComb y (fun i => M * c i) := by
  simp only [linComb, pow_mul]

theorem linComb_pow_right {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb y c ^ M = linComb y (fun i => M * c i) := by
  simp only [linComb, List.prod_ofFn, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem comp_linComb {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : h ≫ linComb y c = linComb (fun i => h ≫ y i) c := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) (fun a b => MonObj.comp_mul _ _ _)
  simp only [linComb, List.prod_ofFn]
  exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)

theorem existsUnique_lab {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ} [NeZero M]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ (M ^ 2) = 1)
    (ind : ∀ c c' : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c')
    (z : T ⟶ A) (hz : z ^ M = 1) (sp : ∃ c : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = z) :
    ∃! a : Fin n → ZMod M, lab (fun i => y i ^ M) a = z := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have lt : ∀ a : ZMod M, M * a.val < M ^ 2 := fun a => by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hM
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_
  · obtain ⟨c, hc⟩ := sp
    have h₀ := ind (fun i => ⟨(M * c i) % M ^ 2, Nat.mod_lt _ (pow_pos hM 2)⟩) (fun _ => ⟨0, pow_pos hM 2⟩) (by
      have e : linComb y (fun i => (M * c i) % M ^ 2) = linComb y (fun i => M * c i) := by
        simp only [linComb]
        exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (hy i)).symm)
      refine e.trans ?_
      rw [← linComb_pow_right, hc, hz]
      simp [linComb])
    have h₁ : ∀ i, M ∣ (c i : ℕ) := fun i => by
      have q : (M * c i) % M ^ 2 = 0 := congrArg Fin.val (congrFun h₀ i)
      exact Nat.dvd_of_mul_dvd_mul_left hM (sq M ▸ Nat.dvd_of_mod_eq_zero q)
    refine ⟨fun i => ((c i : ℕ) / M : ℕ), (linComb_pow_left _ _ _).trans
      ((congrArg (linComb y) (funext fun i => ?_)).trans hc)⟩
    rw [ZMod.val_cast_of_lt (Nat.div_lt_of_lt_mul (sq M ▸ (c i).2)), Nat.mul_div_cancel' (h₁ i)]
  · have h := ind (fun i => ⟨_, lt (a i)⟩) (fun i => ⟨_, lt (b i)⟩)
      ((linComb_pow_left _ _ _).symm.trans ((ha.trans hb.symm).trans (linComb_pow_left _ _ _)))
    funext i
    exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left hM (congrArg Fin.val (congrFun h i)))

theorem weilIs_pow_pow (hW : WeilSt) [IsLocallyNoetherian S] (P : PolAV S) {M : ℕ} {T : Over S}
    (hu : IsUnit (M : Γ(T.left, ⊤))) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hM : 1 ≤ M) (hx : x ^ (M ^ 2) = 1)
    (hy : y ^ (M ^ 2) = 1) (H : WeilIs P.A P.L (M ^ 2 : ℕ) x y c) :
    WeilIs P.A P.L M (x ^ M) (y ^ M) (c ^ M) := by
  have H' := CommPairing.weilIs_symm P.isLB H
  have k : ∀ n, WeilIs P.A P.L (M ^ 2 : ℕ) (y ^ (n + 1)) x (c⁻¹ ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using H'
    | succ n ih => rw [pow_succ y, pow_succ c⁻¹]; exact (hW S P _ T).2.1 _ _ _ _ _ ih H'
  have k' := CommPairing.weilIs_symm P.isLB (k (M - 1))
  rw [Nat.sub_add_cancel hM, inv_pow, inv_inv] at k'
  refine ((hW S P M T).2.2.2 M x _ _ (by rw [Nat.cast_mul]; exact hu.mul hu) (by rw [← sq, hx])
    (by rw [← pow_mul, ← sq, hy])).1 ?_
  rwa [← Nat.cast_mul, ← sq]

end GlobalTheory.SquareLevel

namespace GlobalTheory


open SquareLevel ThetaCoord in
theorem exists_torsionPoints_of_squareLevel : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  intro hL S _ P M ze hM hu lev
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  refine ⟨fun a => lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm), fun a b => lab_add hq _ _,
    fun K _ _ x z hz => ?_, fun a b => ?_, fun a => ?_, fun i i₁ i₂ h₁ h₂ => ?_⟩
  · have H := existsUnique_lab (M := M)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ lev.pt i)
      (fun i => by rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]) (lev.indep K x) z hz
      (lev.span K x z (by rw [sq, pow_mul, hz, one_pow]))
    refine ((Equiv.arrowCongr (halves P.g) (Equiv.refl (ZMod M))).existsUnique_congr fun a => ?_).2 H
    rw [lab, comp_linComb]
    simp only [MonObj.comp_pow]
    rfl
  · have hze : (ze ^ M) ^ M = 1 := by rw [← pow_mul, ← sq, lev.prim.pow_eq_one]
    have := weilIs_lab hL.globalFns P (T := baseOver S) hq (ze := ze ^ M) hze (fun i j => by
      have := weilIs_pow_pow hL.weil P (T := baseOver S) hu hM (lev.torsion i) (lev.torsion j) (lev.pairing i j)
      convert this using 1
      show (ze ^ M) ^ stdSymp P.g i j = (ze ^ stdSymp P.g i j) ^ M
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm])
      (fun a b => ((hL.weil S P M _).1 _ _ (lab_pow hq a) (lab_pow hq b)).exists)
      (a ∘ (halves P.g).symm) (b ∘ (halves P.g).symm)
    rw [labelSymp_eq] at this
    rw [pow_mul]
    exact this
  · refine ⟨linComb lev.pt fun i => (a ((halves P.g).symm i)).val, ?_, ?_⟩
    · simp only [linComb, List.prod_ofFn, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]
    exact (linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm
  · have k : ∀ s, lab (fun i => lev.pt i ^ M) ((Pi.single s (1 : ZMod M) : _ → ZMod M) ∘ (halves P.g).symm) =
        lev.pt (halves P.g s) ^ M := fun s => by
      rw [← lab_single (M := M) hq (halves P.g s)]
      congr 1
      funext j
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    have e₁ : i₁ = halves P.g (.inl i) := Fin.ext h₁
    have e₂ : i₂ = halves P.g (.inr i) := Fin.ext (h₂.trans (Nat.add_comm _ _))
    rw [e₁, e₂]
    exact ⟨k _, k _⟩

end GlobalTheory

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.polarisedRingAction_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  first | exact @GlobalTheory.polOAct_descend_of_generators | exact GlobalTheory.polOAct_descend_of_generators | (intros; apply GlobalTheory.polOAct_descend_of_generators <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.RealDimOne

open GlobalTheory.TorsionGenerators NumberField

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u n

end GlobalTheory.ZH.RealDimOne
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_thetaExtension_test : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  first | exact @GlobalTheory.ZJ.Core.Theta.nonempty_ext | exact GlobalTheory.ZJ.Core.Theta.nonempty_ext | (intros; apply GlobalTheory.ZJ.Core.Theta.nonempty_ext <;> assumption)
end
