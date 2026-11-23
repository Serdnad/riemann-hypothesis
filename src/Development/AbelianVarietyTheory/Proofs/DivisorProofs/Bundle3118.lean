module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalZarhinBundleEqZetaPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellEtale

theorem etale_of_isOpenImmersion_spec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) : φ.Etale := by
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 this

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) :
    φ.Etale := by
  letI := φ.toAlgebra
  have : IsLocalization.Away (0 : A) B := by
    refine ⟨fun ⟨y, _⟩ => isUnit_of_subsingleton _, fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩,
      fun {x y} _ => ⟨⟨0, 1, pow_one 0⟩, by simp⟩⟩
  have : Algebra.Etale A B := Algebra.Etale.of_isLocalizationAway (0 : A)
  exact RingHom.etale_algebraMap.2 this

theorem normal_mvPolynomial : ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (CommRingCat.of K)) [Smooth s] (U : X.affineOpens) (ι : Type) [Finite ι], IsNoetherianRing (MvPolynomial ι Γ(X, U.1)) ∧ ∀ (𝔭 : Ideal (MvPolynomial ι Γ(X, U.1))) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭) := by
  intro X K _ s _ U ι _
  have h1 := HasRingHomProperty.appLE (P := @Smooth) s inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  let g : K →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp ?_ h1
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  let G : K →+* MvPolynomial ι Γ(X, U.1) := MvPolynomial.C.comp g
  have hC : (MvPolynomial.C : Γ(X, U.1) →+* MvPolynomial ι Γ(X, U.1)).Smooth :=
    RingHom.smooth_algebraMap.2 { formallySmooth := inferInstance, finitePresentation := Algebra.FinitePresentation.mvPolynomial Γ(X, U.1) Γ(X, U.1) ι }
  have hG : G.Smooth := RingHom.Smooth.comp hg hC
  algebraize [G]
  refine ⟨?_, fun 𝔭 _ => GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth K 𝔭 _⟩
  have : Algebra.FiniteType K (MvPolynomial ι Γ(X, U.1)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing K _

theorem isDomain_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (W : (Y₀ TF.X Z).Opens), IsAffineOpen W → Nonempty W → IsDomain Γ(Y₀ TF.X Z, W) := by
  intro E _ _ _ H Dw l Xo c TF Z hF W hW hne
  obtain ⟨hs, hp, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) _
  have : GeometricallyIntegral (str₀ TF.X Z) := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _
  have hY : IsIntegral (Y₀ TF.X Z) := GeometricallyIntegral.geometrically_isIntegral (f := str₀ TF.X Z) (K := c.F)
    (𝟙 _) (𝟙 _) (str₀ TF.X Z) IsPullback.of_id_fst
  infer_instance

theorem finiteType_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).FiniteType := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [MvPolynomial.eval₂Hom_comp_C]
  exact h1

theorem etale_cellCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).Etale := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  by_cases hW : Nonempty W
  · haveI := isDomain_sections E H Dw l Xo c TF Z hF W h.1 hW
    haveI := TF.smooth
    have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth (n := Dw.dim) TF.Y.s
    obtain ⟨hN, hA⟩ := normal_mvPolynomial TF.Y.X c.F TF.Y.s U (VIx Dw)
    exact etale_of_isOpenImmersion_spec _ (GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal _ hA
      (finiteType_cell E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.locallyQuasiFinite_bigCell_to_base_prod_affineSpace E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW))
  · haveI : Subsingleton Γ(Y₀ TF.X Z, W) := by
      have hE : IsEmpty W := not_nonempty_iff.1 hW
      have : IsEmpty (Spec Γ(Y₀ TF.X Z, W)) := (Scheme.Hom.homeomorph h.1.isoSpec.hom).isEmpty_congr.1 hE
      by_contra hs
      rw [not_subsingleton_iff_nontrivial] at hs
      obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(Y₀ TF.X Z, W)
      exact this.elim ⟨m, hm.isPrime⟩
    exact etale_of_subsingleton _

end GlobalTheory.CellEtale
end
end

section

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CompHS
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open scoped Classical
open GlobalTheory.AllWt (exOf)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem glue_field_cover {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (loc : ∀ p ∈ V, ∃ (W : Z.Opens) (a : Γ(Z, W)), p ∈ W ∧ W ≤ V ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ W → ∀ x y, R L z x → R L z y → x = y) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  choose! W a hp hWV ha hu using loc
  let I := {p // p ∈ V}
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ W i.1 := fun p h => ⟨⟨p, h⟩, hp p h⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => W i.1) V (fun i => homOfLE (hWV i.1 i.2))
    (fun p h => TopologicalSpace.Opens.mem_iSup.2 (hc p h)) (fun i => a i.1) (fun i j => by
      refine GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i.1)) (b := resG Z inf_le_right (a j.1)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
      exact hu i.1 i.2 L z hi _ _ (ha i.1 i.2 L z hi) (ha j.1 j.2 L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ W i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ W i.1)).1 hi).ge
  have e : ev z V hz s = ev z (W i.1) hi' (a i.1) :=
    (GlobalTheory.FlagMod.ev_res z (hWV i.1 i.2) hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i.1 i.2 L z hi'

theorem exists_local (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens) (hW : W ≤ ksOpen M i k) (p : M.X) (hp : p ∈ W) :
    ∃ (W' : M.X.Opens) (a : Γ(M.X, W')), p ∈ W' ∧ W' ≤ W ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W'), KSRel M i k z (ev z W' hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ W' → ∀ x y, KSRel M i k z x → KSRel M i k z y → x = y := by
  have hWk : ksOpen M i k ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    ⟨hs.1, (((common₀ X Z).pull M.σ).mem _ _ _).1 hs.2.2⟩
  have hWi : ksOpen M i k ≤ M.K.bundle.U i := fun s hs => hs.2.1
  obtain ⟨V, f, hpV, hf⟩ := exists_isFrame_dOn M.str (dimFlag Dw) p
  obtain ⟨W₁, hW₁, hpW₁, hW₁V⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show p ∈ W ⊓ V from ⟨hp, hpV⟩)
  obtain ⟨W', hW', eH, hpW', hWW', eH1, eH2⟩ := GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover M hP hKS k W₁
    ((hW₁V.trans inf_le_left).trans (hW.trans hWk)) p hpW₁
  have hWV : W' ≤ W := hWW'.trans (hW₁V.trans inf_le_left)
  have hW'k : W' ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := hWV.trans (hW.trans hWk)
  have hW'i : W' ≤ M.K.bundle.U i := hWV.trans (hW.trans hWi)
  obtain ⟨eV, eV1, eV2⟩ := GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine M k W' hW' hW'k
  let e : TIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W')) := Sum.elim eH eV
  have e1 : ∀ b s, (e b s).fst = s := by
    rintro (b | b) s
    · exact eH1 b s
    · exact eV1 b s

  have e2 : ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
      (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
      X.F.ChartFr k _ hk Q → ∃ v, IsTanFrame (psiSet H) Q v ∧
        ∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b) := by
    intro K _ _ ψ hk Q hQ
    choose w₁ hw₁ hw₁' hw₁'' using eH2 K ψ hk Q hQ
    choose w₂ hw₂ hw₂' using eV2 K ψ hk Q hQ
    refine ⟨Sum.elim w₁ w₂, ⟨fun b => ⟨hw₁ b, hw₁' b⟩, fun b => hw₂ b⟩, ?_⟩
    rintro (b | b)
    · exact hw₁'' b
    · exact hw₂' b
  let g : Fin (dimFlag Dw) → Γ(M.X, W') := fun a => resG M.X (hWW'.trans (hW₁V.trans inf_le_right)) (f a)
  have hu : IsUnit (M.K.jacobian i hW'i g) := (M.K.isUnit_jacobian_iff i hW' hW'i g).2 (by
    have := hf.res hW' (hWW'.trans (hW₁V.trans inf_le_right))
    rwa [resForm_dOn] at this)
  let A : Matrix (Fin (dimFlag Dw)) (Fin (dimFlag Dw)) Γ(M.X, W') :=
    Matrix.of fun a b => (e (tanOrd Dw b) (g a)).snd

  let zv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) :=
    fun ψ b => spMap ((dualMap ψ).comp (e b)) ≫ tau hW'
  have hzvW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b, ⊤ ≤ zv ψ b ⁻¹ᵁ W' := fun ψ b =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have hred : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b,
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zv ψ b = spMap ψ ≫ tau hW' := fun {K} _ ψ b => by
    simp only [zv]
    rw [← Category.assoc, ← spMap_comp]
    congr 2
    ext s
    simp [dualMap, e1]
  have hev : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) a b,
      (evalPt (zv ψ b) W' (hzvW ψ b) (g a)).snd = ψ (e b (g a)).snd := fun ψ a b => by
    have := ev_spMap_tau hW' ((dualMap ψ).comp (e b)) (hzvW ψ b)
    have h2 : evalPt (zv ψ b) W' (hzvW ψ b) (g a) = ((dualMap ψ).comp (e b)) (g a) := congrFun (congrArg DFunLike.coe this) _
    rw [h2]
    simp [dualMap]
  have hdet : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K),
      (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) W' (hzvW ψ _) (g a)).snd).det = ψ A.det := fun ψ => by
    rw [RingHom.map_det]
    congr 1
    ext a b
    exact hev ψ a _
  have hzW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ W' := fun ψ =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have ho : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ M.off := fun ψ =>
    le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_left))
  have hkk : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k :=
    fun ψ => by
      show ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ (toFlag M ⁻¹ᵁ X.F.U k)
      exact le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_right))
  have chart : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ∃ (_ : Algebra c.F K) (Q : FrPt Xo c K),
      X.F.ChartFr k _ (hkk ψ) Q := fun ψ => by
    have hF : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
      have := ho ψ (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    obtain ⟨a, h⟩ := exists_chartFr _ hF
    exact ⟨a, h k (hkk ψ)⟩
  have hJ : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), evalPt (spMap ψ ≫ tau hW') W' (hzW ψ) (M.K.jacobian i hW'i g) = ψ (M.K.jacobian i hW'i g) :=
    fun ψ => congrFun (congrArg DFunLike.coe (ev_spMap_tau hW' ψ (hzW ψ))) _
  have hl' : ∀ {K : Type} [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)},
      (∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b)) → ∀ b, zv ψ b ≫ toFlag M = X.ptY (v b) :=
    fun ψ _ h b => (Category.assoc _ _ _).trans (h b)
  have hne : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det ≠ 0 := fun {K} _ ψ => by
    obtain ⟨_, Q, hQ⟩ := chart ψ
    obtain ⟨v, hv, hl⟩ := e2 K ψ _ Q hQ
    have := GlobalTheory.T.det_derivatives_tangentLift_ne_zero M hKS (spMap ψ ≫ tau hW') (ho ψ) (FlagCover.eq_ptY hQ.lies) hv (hl' ψ hl) i W' hW'i g (hzW ψ)
      (hzvW ψ) (by rw [hJ]; exact (hu.map ψ).ne_zero)
    rwa [hdet] at this
  have hAu : IsUnit A.det := by
    by_contra h
    obtain ⟨m, hm, hdm⟩ := exists_max_ideal_of_mem_nonunits h
    letI := Ideal.Quotient.field m
    exact hne (Ideal.Quotient.mk m) (Ideal.Quotient.eq_zero_iff_mem.2 hdm)
  let a : Γ(M.X, W') := M.K.jacobian i hW'i g * ↑(hAu.unit⁻¹)
  have hinv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det * ψ ↑(hAu.unit⁻¹) = 1 := fun ψ => by
    rw [← map_mul]
    have : A.det * ↑(hAu.unit⁻¹) = 1 := hAu.mul_val_inv
    rw [this, map_one]
  have rel : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), KSRel M i k (spMap ψ ≫ tau hW') (ψ a) := by
    intro K _ ψ _ P Q t v zv' O hO g' hz hzv hk hQ ht hv hl
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ hk Q hQ
    have hzO : ∀ b, ⊤ ≤ zv ψ b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ O
      (by rw [hred]; exact hz)
    have tc := GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight M hKS (spMap ψ ≫ tau hW') (ho ψ) t (FlagCover.eq_ptY hQ.lies) ht hv hv0 hl (hl' ψ hl0) O g' hzv hzO
    have jc := GlobalTheory.T.det_derivatives_div_jacobian_independent M (spMap ψ ≫ tau hW') i (fun b => zv ψ (tanOrd Dw b)) (fun b => hred ψ _) O W' hO hW'i g' g hz
      (hzW ψ) (fun b => hzO _) (fun b => hzvW ψ _)
    rw [hJ, hdet] at jc
    rw [tc]
    generalize (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) O (hzO _) (g' a)).snd).det = D0 at jc ⊢
    generalize evalPt (spMap ψ ≫ tau hW') O hz (M.K.jacobian i hO g') = J1 at jc ⊢
    generalize ((∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix : Kˣ) : K) = T
    have h1 := hinv ψ
    simp only [a, map_mul]
    generalize ψ ↑(hAu.unit⁻¹) = u at h1 ⊢
    generalize ψ A.det = d at jc h1
    generalize ψ (M.K.jacobian i hW'i g) = J0 at jc ⊢
    calc J0 * u * (T * D0) = T * u * (D0 * J0) := by ring
      _ = T * u * (d * J1) := by rw [jc]
      _ = (d * u) * (T * J1) := by ring
      _ = T * J1 := by rw [h1, one_mul]
  have uniq : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) (x y : K), KSRel M i k (spMap ψ ≫ tau hW') x →
      KSRel M i k (spMap ψ ≫ tau hW') y → x = y := by
    intro K _ ψ x y hx hy
    obtain ⟨alg, Q, hQ⟩ := chart ψ
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ _ Q hQ
    have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q
    have a1 := @hx alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    have a2 := @hy alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    rw [hdet] at a1 a2
    exact mul_right_cancel₀ (hne ψ) (a1.trans a2.symm)
  refine ⟨W', a, hpW', hWV, fun L _ z hz => ?_, fun L _ z hz x y hx hy => ?_⟩
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    have h : KSRel M i k (spMap (ev z W' hz) ≫ tau hW') (ev z W' hz a) := @rel L _ (ev z W' hz)
    rwa [e0] at h
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    rw [← e0] at hx hy
    exact uniq _ x y hx hy

theorem exists_regular_ksRel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS i k W _ hW
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  exact glue_field_cover W (fun L _ z x => KSRel M i k z x) (exists_local M hP hKS i k W hW)

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseVar

open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem j_mem_range_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Xo.XF c) :
    Y.j x ∈ Set.range X.π := by
  let xF : Sp ((Xo.XF c).residueField x) ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField x
  letI : Algebra c.F ((Xo.XF c).residueField x) := (Spec.preimage (xF ≫ pullback.snd _ _)).hom.toAlgebra
  have hsnd : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F ((Xo.XF c).residueField x)) :=
    (Spec.map_preimage _).symm
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frPt (S := (Xo.XF c).residueField x) (Xo := Xo) (c := c)
    (xF ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, sOf, ← Spec.map_comp]; rfl)
  have hx : xF = GlobalTheory.FlagMod.frX P := GlobalTheory.FlagMod.eq_frX P hP.symm hsnd
  let pt : Sp ((Xo.XF c).residueField x) := IsLocalRing.closedPoint _
  refine ⟨X.ptY P pt, ?_⟩
  have e1 : X.π (X.ptY P pt) = (X.ptY P ≫ X.π) pt := (Scheme.Hom.comp_apply _ _ _).symm
  rw [e1, (X.lies_ptY P).1, ← hx, Scheme.Hom.comp_apply]
  exact congrArg Y.j (Scheme.fromSpecResidueField_apply x _)

theorem surjective_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Function.Surjective X.π := by
  have := X.proper
  have hc : IsClosed (Set.range X.π) := X.π.isClosedMap.isClosed_range
  have hd : closure (Set.range Y.j) ⊆ Set.range X.π :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact j_mem_range_π X x) hc
  exact fun y => hd (LogKS.dense_interior Y y)

theorem surjective_π₀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) :
    Function.Surjective (π₀ X Z) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_π X ((barComp Y Z).ι y)
  have hzU : z ∈ X.π ⁻¹ᵁ barComp Y Z := by
    show X.π z ∈ barComp Y Z
    have : (barComp Y Z).ι y ∈ Set.range (barComp Y Z).ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι, ← hz] at this
  obtain ⟨z', hz'⟩ : z ∈ Set.range (inc₀ X Z) := by rwa [Scheme.Opens.range_ι]
  refine ⟨z', (barComp Y Z).ι.isOpenEmbedding.injective ?_⟩
  have e1 := Scheme.Hom.comp_apply (π₀ X Z) (barComp Y Z).ι z'
  have e2 := Scheme.Hom.comp_apply (inc₀ X Z) X.π z'
  rw [morphismRestrict_ι] at e1
  rw [← e1, e2, hz', hz]

theorem exists_var (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed (Xo := Xo) (c := c)) :
    ∃ (B : GlobalTheory.ProjVar.Var c.F) (φ : B.X ⟶ X₀ TF.Y Z), IsIso φ ∧ φ ≫ s₀ TF.Y Z = B.str ∧ B.dim = Dw.dim := by
  have hsm := GlobalTheory.VarFlag.smooth_gen TF.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) TF.Y c.F (RingEquiv.refl _) hF hsm
  have hJ : ∀ w : gen TF.Y, genι TF.Y w ∈ barComp TF.Y Z ↔ w ∈ Set.range (j Z) :=
    GlobalTheory.VarFlag.barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have := (hB Z).1
  have hr : Set.range (j Z ≫ genι TF.Y) ⊆ Set.range (barComp TF.Y Z).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨b, rfl⟩
    exact (hJ _).2 ⟨b, rfl⟩
  let φ := IsOpenImmersion.lift (barComp TF.Y Z).ι (j Z ≫ genι TF.Y) hr
  have hφ : φ ≫ (barComp TF.Y Z).ι = j Z ≫ genι TF.Y := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (φ ≫ (barComp TF.Y Z).ι) := by rw [hφ]; infer_instance
  have : IsOpenImmersion φ := IsOpenImmersion.of_comp φ (barComp TF.Y Z).ι
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, genι TF.Y w = (barComp TF.Y Z).ι y :=
      ⟨inv (genι TF.Y) ((barComp TF.Y Z).ι y), by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hm : genι TF.Y w ∈ barComp TF.Y Z := by
      have : (barComp TF.Y Z).ι y ∈ Set.range (barComp TF.Y Z).ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι, ← hw] at this
    obtain ⟨b, rfl⟩ := (hJ w).1 hm
    refine ⟨b, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, hw]
  have hiso : IsIso φ := (isIso_iff_isOpenImmersion_and_surjective φ).2 ⟨inferInstance, ⟨hsurj⟩⟩
  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  refine ⟨B Z, φ, hiso, ?_, (hB Z).2.1⟩
  have h3 := (hB Z).2.2.1
  rw [hspid, Category.comp_id] at h3
  rw [← h3, GlobalTheory.VarFlag.genStr_eq, s₀, ← Category.assoc, hφ, Category.assoc]

theorem isVariety_barComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  intro E _ _ _ H Dw l Xo c TF Z hF
  obtain ⟨B, φ, hφ, hs, hd⟩ := exists_var TF Z hF
  have hs' : s₀ TF.Y Z = inv φ ≫ B.str := by rw [← hs, IsIso.inv_hom_id_assoc]
  have : Nonempty (X₀ TF.Y Z) := ⟨φ (genericPoint B.X)⟩
  have hint : IsIntegral (X₀ TF.Y Z) := isIntegral_of_isOpenImmersion (inv φ)
  refine ⟨hint, ?_, ?_, ?_, ⟨surjective_π₀ TF.X Z⟩, ?_, ?_⟩
  · rw [hs', ← hd]
    exact GlobalTheory.VarFlag.smooth_iso _ _ B.smooth
  · obtain ⟨N, i, hi, hs2⟩ := B.isProjOver
    exact ⟨N, inv φ ≫ i, inferInstance, by rw [Category.assoc, hs2, hs']⟩
  · rw [hs']
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (inv φ) (inv φ ≫ B.str) B.str (𝟙 _)) inferInstance
  · haveI : GlobalTheory.IsNormalScheme TF.Y.X := GlobalTheory.IsNormalScheme.of_pred TF.Y.normal
    exact GlobalTheory.IsNormalScheme.of_isOpenImmersion (i₀ TF.Y Z ≫ TF.Y.j)
  · intro v hv
    have : IsOpenImmersion (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) := by rw [j₀_ι]; infer_instance
    have : IsOpenImmersion (j₀ TF.Y Z) := IsOpenImmersion.of_comp _ (barComp TF.Y Z).ι
    have hgen : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
      have hirr : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
      exact IsIrreducible.isGenericPoint_genericPoint hirr (isClosed_of_mem_irreducibleComponents _ Z.2)
    have hsub : Set.range (j₀ TF.Y Z) ⊆ closure {j₀ TF.Y Z v} := by
      rintro _ ⟨w, rfl⟩
      have hw : i₀ TF.Y Z w ∈ (Z : Set (Xo.XF c)) := (j_mem_barComp (Y := TF.Y) Z _).1 w.2
      have h1 : i₀ TF.Y Z v ⤳ i₀ TF.Y Z w := hv ▸ hgen.specializes hw
      have h2 : v ⤳ w := (i₀ TF.Y Z).isOpenEmbedding.isInducing.specializes_iff.1 h1
      exact specializes_iff_mem_closure.1 (h2.map (j₀ TF.Y Z).continuous)
    have hdense : Dense (Set.range (j₀ TF.Y Z)) :=
      (j₀ TF.Y Z).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, rfl⟩⟩
    have hg : IsGenericPoint (j₀ TF.Y Z v) (Set.univ : Set (X₀ TF.Y Z)) := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← hdense.closure_eq]
      exact closure_minimal hsub isClosed_closure
    exact hg.eq (genericPoint_spec (X₀ TF.Y Z))

end GlobalTheory.BaseVar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.weilPairing_diagonal_zarhinBundle_eq_zeta_pow : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → ∀ a b : Fin 8 → (Fin h ⊕ Fin h → ℤ), Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la)) (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (b (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (b (Fin.natAdd 4 j)) ≫ la)) (unitOn (z ^ (2 * GlobalTheory.ZarhinFam.formZ d h a b))) := by
  first | (exact @GlobalTheory.ZarhinWeil.weilIs_formZ) | (exact GlobalTheory.ZarhinWeil.weilIs_formZ) | (intros; apply GlobalTheory.ZarhinWeil.weilIs_formZ  <;> assumption)
end
