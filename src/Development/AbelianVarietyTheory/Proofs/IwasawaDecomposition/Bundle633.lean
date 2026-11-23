module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsReadingResetBaseEnlargement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)
open GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB GlobalTheory.LieVB.TangentSurj
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.TanFibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ π = 𝟙 X)
  {x : Sp k ⟶ X} {v v' : (specO k (DualNumber k)).left ⟶ Y}

def form (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e) :
    (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k) :=
  baseMap (sec_hom (epsZero k)) w we ≫ (epsIso k).hom

theorem form_d (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ e ⁻¹ᵁ W) (f : Γ(Y, W)) {U : (Sp k).Opens} (hU : U ≤ x ⁻¹ᵁ V)
    (q : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W) (a b : Γ(Sp k, U))
    (H : v.appLE W _ q f = (specO k (DualNumber k)).hom.appLE U _ le_rfl a +
      (specO k (DualNumber k)).hom.appLE U _ le_rfl b * resG _ le_top (epsFn k)) :
    (form w we).app U (pullbackSections x _ hU (d he h f)) = b := by
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  refine (congrArg ((epsIso k).hom.app U) (baseMap_d he (sec_hom (epsZero k)) w we h hU hV q f)).trans ?_
  rw [H, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : U ≤ ⊤)))).trans (_root_.mul_one b)

theorem preimage_le (we : sec (epsZero k) ≫ v = x ≫ e) {U : (Sp k).Opens} {W : Y.Opens}
    (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ e) ⁻¹ᵁ W := h h₁
  rw [← we] at h₂
  exact h₂

theorem appLE_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {U : (Sp k).Opens} (hU : IsAffineOpen U) {W : Y.Opens} (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(Y, W)) :
    v.appLE W _ (preimage_le we h) f =
      (specO k (DualNumber k)).hom.appLE U _ le_rfl ((x ≫ e).appLE W U h f) +
        (specO k (DualNumber k)).hom.appLE U _ le_rfl
          ((form w we).app U (pullbackSections x _ h (d he le_rfl f))) * resG _ le_top (epsFn k) := by
  obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k U hU).2 (v.appLE W _ (preimage_le we h) f)
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have hb := form_d he w we le_rfl f h (preimage_le we h) a b E.symm
  have ha : (x ≫ e).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero k)).appLE _ U hV) E
    simp only [map_add (f := _), map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      resG_self, appLE_appLE we _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact E.symm


include he in
theorem eq_of_form_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    (w' : v' ≫ π = (specO k (DualNumber k)).hom ≫ x) (we' : sec (epsZero k) ≫ v' = x ≫ e)
    (H : form w we = form w' we') : v = v' := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, hW', -⟩ := QCoh.exists_affine_mem_le (U := ⊤)
    (e (x ((specO k (DualNumber k)).hom t))) trivial
  obtain ⟨U, hU, hU', h⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ e ⁻¹ᵁ W)
    ((specO k (DualNumber k)).hom t) hW'
  have hT : IsAffineOpen ((specO k (DualNumber k)).hom ⁻¹ᵁ U) := hU.preimage _
  have E : v.appLE W _ (preimage_le we h) = v'.appLE W _ (preimage_le we' h) := by
    ext f
    exact (appLE_eq he w we hU h f).trans (H ▸ (appLE_eq he w' we' hU h f).symm)
  refine ⟨(specO k (DualNumber k)).hom ⁻¹ᵁ U, hU', ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we h),
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we' h), E]


include he in
theorem exists_form_eq [QuasiSeparated π]
    (L : (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k)) :
    ∃ (v : (specO k (DualNumber k)).left ⟶ Y) (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x)
      (we : sec (epsZero k) ≫ v = x ≫ e), form w we = L := by
  let e' : Sp k ⟶ pullback π x := pullback.lift (x ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd π x = 𝟙 _ := pullback.lift_snd _ _ _
  have we' : e' ≫ pullback.fst π x = x ≫ e := pullback.lift_fst _ _ _
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have : QuasiCompact e' :=
    have : QuasiCompact (e' ≫ pullback.snd π x) := he' ▸ inferInstance
    .of_comp _ (pullback.snd π x)
  have := isIso_baseMap he he' (IsPullback.of_hasPullback π x) we'
  let β := baseMap he' (IsPullback.of_hasPullback π x).w we'
  let D := homEquivDer _ he' (inv β ≫ L)
  let u := deform (specO k (DualNumber k)).hom (epsFn k) (epsFn_sq k) D
  have w : (u ≫ pullback.fst π x) ≫ π = (specO k (DualNumber k)).hom ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, deform_comp _ _ _ D he']
  have we : sec (epsZero k) ≫ u ≫ pullback.fst π x = x ≫ e := by
    rw [← Category.assoc, comp_deform _ _ (epsFn_sq k) D (sec_hom (epsZero k)) (epsZero_epsFn k), we']
  refine ⟨_, w, we, pullback_hom_ext he fun W f => ?_⟩
  have k₁ : x ⁻¹ᵁ e ⁻¹ᵁ W ≤ e' ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := le_of_sq we' le_rfl le_rfl
  have k₂ := (specO k (DualNumber k)).hom.preimage_mono k₁
  let g := (pullback.fst π x).appLE W _ le_rfl f
  refine (form_d he w we le_rfl f le_rfl (preimage_le we le_rfl) (e'.appLE _ _ k₁ g) (val D k₁ g) ?_).trans ?_
  · have k₃ : (specO k (DualNumber k)).hom ⁻¹ᵁ x ⁻¹ᵁ e ⁻¹ᵁ W ≤ u ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := k₂
    have e₁ : u.appLE _ _ k₃ g = resG _ k₂ (psi _ _ (epsFn_sq k) D _ g) :=
      deform_appLE _ _ (epsFn_sq k) D _ k₂ g
    rw [← appLE_appLE (f := u) (g := pullback.fst π x) rfl le_rfl k₃, e₁, psi_apply, map_add (f := _), map_mul, LB.resG_resG, DualPull.resG_appLE, DualPull.resG_appLE,
      ← DualPull.resG_appLE e' k₁ le_rfl, DualPull.appLE_resG,
      show val D k₁ g = resG _ k₁ (val D le_rfl g) from (D.res_app le_rfl k₁ g).symm, DualPull.appLE_resG]
  · have b := baseMap_d he he' (IsPullback.of_hasPullback π x).w we' le_rfl le_rfl k₁ le_rfl f
    have c : val D k₁ g = (inv β ≫ L).app _ (d he' k₁ g) := homEquivDer_app he' (inv β ≫ L) k₁ g
    rw [c, ← b]
    generalize pullbackSections x (conormal e) _ (d he _ f) = s
    have i : β ≫ inv β ≫ L = L := IsIso.hom_inv_id_assoc β L
    conv_rhs => rw [← i]
    rw [Scheme.Modules.Hom.comp_app β, AddCommGrpCat.comp_apply]

theorem exists_hom_of_isFrame {F : X.Modules} {n : ℕ} {s : Fin n → Γ(F, ⊤)} (hs : IsFrame s) (c : Fin n → Γ(X, ⊤)) :
    ∃ L : F ⟶ structureModule X, ∀ l, L.app ⊤ (s l) = c l := by
  refine ⟨homGlobalEquiv _ _ (∑ i, c i • hs.coord i), fun l => ?_⟩
  change dualApp (∑ i, c i • hs.coord i) le_rfl (s l) = c l
  have hsum (T : Finset (Fin n)) : dualApp (∑ i ∈ T, c i • hs.coord i) le_rfl (s l) = if l ∈ T then c l else 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have := dualApp_smul (0 : Γ(X, ⊤)) (hs.coord l) le_rfl
      rw [zero_smul, map_zero, zero_smul] at this
      rw [Finset.sum_empty, this]
      simp
    | insert i T hi ih =>
      have := hs.dualApp_coord_frame i l le_rfl
      rw [Twist.resM_self] at this
      rw [Finset.sum_insert hi, dualApp_add, LinearMap.add_apply, ih, dualApp_smul, LinearMap.smul_apply, this,
        resG_self]
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  simpa using hsum Finset.univ

theorem existsUnique_tanEv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  intro E _ _ _ H X t k _ x V h n m hm c
  have := t.semi
  have hf : IsFrame fun l => pullbackSections x (omega t.G) h (m l) := by
    have := (hm.pullback x).res h
    exact (funext fun l => QCoh.res_pullbackSections x (omega t.G) le_rfl h (m l)) ▸ this
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame hf fun l => cst k (c l)
  obtain ⟨v, w, we, hv⟩ := exists_form_eq (sec_hom η[t.G]) L
  have hv' : IsTanAtG t x v := ⟨w, we.trans (by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl)⟩
  have hval (l) : tanEv t hv' h (m l) = c l :=
    (congrArg (fun (a : Γ(Sp k, ⊤)) => (Scheme.ΓSpecIso (.of k)).hom a)
      ((congr(($hv).app ⊤ _)).trans (hL l))).trans (Iso.inv_hom_id_apply _ _)
  refine ⟨v, ⟨hv', hval⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  refine eq_of_form_eq (sec_hom η[t.G]) hu.1 (epsZero_comp_of_isTanAtG t hu) w we (hom_ext_of_isFrame hf fun l => ?_)
  exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ((hu' l).trans (hval l).symm)

end GlobalTheory.TanFibre
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem stalkId_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) (y : Y) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.ofIdealTop K) y = K.map (Y.presheaf.germ ⊤ y trivial).hom := by
  rw [ds_stalkId_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ y trivial, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact Y.presheaf.germ_res (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) y (by trivial)

theorem ideal_top_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top Y⟩ = K := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [← Y.presheaf.map_id]; rfl
  rw [this]
  simp

theorem comap_eq_ofIdealTop (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    J.comap χ = Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom) := by
  refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
  have hz : χ z ∈ U.1 := hle trivial
  rw [stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
  congr 3
  exact (Sp R).presheaf.germ_res (homOfLE hle) z (by trivial)

theorem idlAlong_eq_idealAlong (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) : idlAlong J χ = idealAlong J χ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  unfold idlAlong idealAlong
  rw [comap_eq_ofIdealTop X J R χ ⟨U, hU⟩ hle, ideal_top_ofIdealTop, ds_stalkId_eq_map J ⟨U, hU⟩ _ hx,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

end GlobalTheory.LocM
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

section Cpt

variable {C : FlagCpt Z e}

end Cpt

section Core

end Core

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

end GlobalTheory.CuspFrom
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
set_option maxSynthPendingDepth 32
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
private theorem eigFrame_isComb_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}
    {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → S) (w : TanM x t.G) :
    IsCombAtG t x (fun i => (tv (u i)).left) a (tv w).left ↔ w = ∑ i, a i • u i := by
  have e : tv (∑ i, a i • u i) = combT x (fun i => tv (u i)) a := by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  refine (isCombAtG_iff t x (fun i => tv (u i)) a _).trans ?_
  rw [← e]
  exact ⟨fun h => (tan_ext h).symm, fun h => h ▸ rfl⟩


theorem _root_.GlobalTheory.T.exists_eigFrame_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => eigFrame_isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => eigFrame_isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsEigBasis {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ)
    {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (v i)) ∧ (∀ i (a : 𝓞 E), v i ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x v a w

variable {O : Type} [CommRing O] {β : O →+* c.F}

theorem EigFrame.isEigBasis {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (g : EigFrame Z φ x) (τ : E →+* ℂ) : IsEigBasis Z.t φ x τ (g.v τ) :=
  ⟨g.tan τ, g.eig τ, g.basis τ⟩

def eigFrameOf {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : ∀ τ, IsEigBasis Z.t φ x τ (v τ)) :
    EigFrame Z φ x :=
  ⟨v, fun τ => (h τ).1, fun τ => (h τ).2.1, fun τ => (h τ).2.2⟩

section Transport

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ S'} {τ : E →+* ℂ} {n : ℕ}

theorem isEigBasis_push {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (h : IsEigBasis t' φ x τ v) :
    IsEigBasis t φ (x ≫ f) τ (fun i => v i ≫ m.φ) := by
  have hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := fun i => (h.1 i).1
  refine ⟨fun i => (tan_iff m rfl (hv i)).2 (h.1 i), fun i a => (eig_iff m (hv i) a _).2 (h.2.1 i a),
    fun w hw he => ?_⟩
  obtain ⟨w', hw1, rfl⟩ := exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) w (by rw [hw.1, Category.assoc])
  have hb := h.2.2 w' ((tan_iff m rfl hw1).1 hw) fun a => (eig_iff m hw1 a _).1 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv cf hw1).2 hb

theorem isEigBasis_pull {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsEigBasis t φ (x ≫ f) τ v) :
    ∃ v' : Fin n → (Sp (DualNumber R) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = v i) ∧ IsEigBasis t' φ x τ v' := by
  choose v' hv1 hv2 using fun i =>
    exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) (v i) (by rw [(h.1 i).1, Category.assoc])
  have e : v = fun i => v' i ≫ m.φ := funext fun i => (hv2 i).symm
  subst e
  refine ⟨v', fun i => rfl, fun i => (tan_iff m rfl (hv1 i)).1 (h.1 i), fun i a => (eig_iff m (hv1 i) a _).1 (h.2.1 i a),
    fun w hw he => ?_⟩
  have hb := h.2.2 (w ≫ m.φ) ((tan_iff m rfl hw.1).2 hw) fun a => (eig_iff m hw.1 a _).2 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv1 cf hw.1).1 hb

end Transport

end GlobalTheory.CuspFrom
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_over_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, hw τ i⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.definiteFormsReading_reset_baseEnlargement : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → (∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) → Seed.FrmC.StdLat (w'.st Z').toD7.sp.X' → ValsIn w'.I →
    ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideA z Wt' R₁ := by
  first | exact @GlobalTheory.Mem.R3.RsA.reset_side | exact GlobalTheory.Mem.R3.RsA.reset_side | (intros; apply GlobalTheory.Mem.R3.RsA.reset_side <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_integer_exponent_section_of_chart_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  first | exact @GlobalTheory.SecGlueInt.exists_secZ_of_regular | exact GlobalTheory.SecGlueInt.exists_secZ_of_regular | (intros; apply GlobalTheory.SecGlueInt.exists_secZ_of_regular <;> assumption)
end
