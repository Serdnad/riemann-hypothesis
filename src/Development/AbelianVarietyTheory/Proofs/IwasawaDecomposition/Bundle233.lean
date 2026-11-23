module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle224
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

end GlobalTheory.ProjModel
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ModelCharts

theorem exists_etale_coords_of_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (D : ℕ)
    (W : X.Opens) [SmoothOfRelativeDimension D (W.ι ≫ p)] {z : X} (hz : z ∈ W) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have hzr : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨z', rfl⟩ := hzr
  obtain ⟨U', x', hU', hzU', hx'⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'
  let e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U') := (W.ι.appIso U').commRingCatIsoToRingEquiv
  refine ⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩
  have h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) =
      p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom := by
    first
    | rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    | (rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    | simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]
    | (simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])
  have halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX
    rw [h2]
    rfl
  have heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' =
      (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp
        (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [halg]
    · intro i; simp
  rw [heq] at hx'
  have h3 := RingHom.Etale.respectsIso.left _ e.symm hx'
  convert h3 using 1
  ext <;> simp


private theorem exists_algChart_mem_source {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := by
  obtain ⟨a, ha⟩ := y
  obtain ⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ :=
    ⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩
  have hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K) := by
    rw [ha]; unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨b, hb⟩ : ∃ b, b ≫ j = a := ⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩
  haveI : Flat (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K
  obtain ⟨W, hW, hsm⟩ := GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D
    (b (IsLocalRing.closedPoint ℂ))
  haveI := hsm
  have hz : a (IsLocalRing.closedPoint ℂ) ∈ W := by
    rw [← hb]
    first | exact hW | simpa using hW
  obtain ⟨U, x, hU, hzU, hx⟩ := exists_etale_coords_of_opens p D W hz
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩)
    (GlobalTheory.CxPts.mem_ptsIn.2 hzU)
  exact ⟨c, hc⟩

theorem exists_chart {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := exists_algChart_mem_source h hτ y

end GlobalTheory.ModelCharts
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  first | exact @GlobalTheory.FlagBundle.Bears.transfer | exact GlobalTheory.FlagBundle.Bears.transfer | (intros; apply GlobalTheory.FlagBundle.Bears.transfer <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_spMap | exact GlobalTheory.FlagBundle.coBear_spMap | (intros; apply GlobalTheory.FlagBundle.coBear_spMap <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagRoot_term_big {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.p) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩ =
      -(C ((la τ (Fin.castAdd Dw.q i) : ℤ) : ℝ) * X (τ, Fin.castAdd Dw.q i)) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (τ.1, (i : ℕ)) := rfl
  rw [he, GlobalTheory.AllWt.wtOf_big la 0 τ i i.2]
  unfold flagRoot
  rw [dite_eq_left τ.2]
  simp only [sub_zero, map_neg, neg_mul, neg_neg]
  rfl

theorem flagRoot_term_small {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.q) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0
          (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩ =
      -(C ((la τ (Fin.natAdd Dw.p (Fin.rev i)) : ℤ) : ℝ) * X (τ, Fin.natAdd Dw.p (Fin.rev i))) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0
      (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (conjEmb τ.1, (i : ℕ)) := rfl
  have hj : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p (Fin.rev i) := by
    ext; simp [Fin.val_rev]; omega
  rw [he, GlobalTheory.AllWt.wtOf_small la 0 τ i i.2, hj]
  unfold flagRoot
  rw [dite_eq_right (GlobalTheory.AllWt.conj_not_mem τ)]
  have hτ : (⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  have hx : ((⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H),
      (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q))) = (τ, Fin.natAdd Dw.p (Fin.rev i)) := by
    rw [hτ, hj]
  simp only [Fin.val_cast] at *
  rw [hx]
  simp only [sub_zero, Int.cast_neg, neg_neg, mul_neg]

theorem chernRootSubstitution_weightLineBundle_eq_linRoot (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) :
    flagMap Dw (∑ x : GlobalTheory.GoodMetric.Root Dw.mult,
        MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) =
      Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) := by

  simp only [flagMap, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
  rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  let e : GlobalTheory.AllWt.Psi H ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  rw [← e.sum_comp]
  unfold Formalism.DegreeFormula.linRoot
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨τ.1, i⟩)
      (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_big Dw la τ i
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change ∑ i : Fin (Dw.mult (conjEmb τ.1)), C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩ = _
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩) (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm,
      ← Equiv.sum_comp (Fin.revPerm (n := Dw.q)) (fun i => C ((la τ (Fin.natAdd Dw.p i) : ℤ) : ℝ) *
        X (τ, Fin.natAdd Dw.p i)), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_small Dw la τ i

end GlobalTheory.Schubert
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.Schubert

theorem degFl_rename_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (ρ : ι → Equiv.Perm (Fin N))
    (P : MvPolynomial (ι × Fin N) ℝ) :
    Formalism.DegreeFormula.degFl ι N (rename (fun x : ι × Fin N => (x.1, ρ x.1 x.2)) P) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * Formalism.DegreeFormula.degFl ι N P := by
  set f : ι × Fin N → ι × Fin N := fun x => (x.1, ρ x.1 x.2) with hfdef
  have hinj : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [(ρ a).injective h2]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, j⟩
    exact ⟨(a, (ρ a).symm j), by simp [hfdef]⟩
  have hexp : ∀ σ : ι → Equiv.Perm (Fin N),
      Formalism.DegreeFormula.permExp (σ * ρ⁻¹) = (Formalism.DegreeFormula.permExp σ).mapDomain f := by
    intro σ
    ext y
    obtain ⟨⟨a, i⟩, rfl⟩ := hsurj y
    rw [Finsupp.mapDomain_apply_of_injective hinj]
    simp [Formalism.DegreeFormula.permExp, hfdef, Pi.mul_apply, Pi.inv_apply]
  have hsgn : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign ((σ * ρ⁻¹) τ) : ℤ) : ℝ)) =
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Pi.mul_apply, Pi.inv_apply, Equiv.Perm.sign_inv]
  have key : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        (rename f P).coeff (Formalism.DegreeFormula.permExp σ) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * ∑ σ : ι → Equiv.Perm (Fin N),
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (Formalism.DegreeFormula.permExp σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (ρ⁻¹ : ι → Equiv.Perm (Fin N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.coe_mulRight, hsgn, hexp, coeff_rename_mapDomain _ hinj]
    ring
  unfold Formalism.DegreeFormula.degFl
  rw [key]
  ring

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perm_val_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) (i : ℕ) (h1 : i < Dw.mult a) (h2 : i < Dw.mult b) :
    ((w a ⟨i, h1⟩ : Fin (Dw.mult a)) : ℕ) = ((w b ⟨i, h2⟩ : Fin (Dw.mult b)) : ℕ) := by
  subst e; rfl

theorem sign_perm_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) : Equiv.Perm.sign (w a) = Equiv.Perm.sign (w b) := by
  subst e; rfl

def flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm (Fin (Dw.p + Dw.q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr
    ((finCongr (GlobalTheory.PointChern.mult_of_mem Dw τ.2)).permCongr (w τ.1))
    (Fin.revPerm.permCongr ((finCongr (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ))).permCongr
      (w (conjEmb τ.1)))))

theorem sign_flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm.sign (flagPerm Dw w τ) = Equiv.Perm.sign (w τ.1) * Equiv.Perm.sign (w (conjEmb τ.1)) := by
  simp only [flagPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem flagPerm_big {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    ((flagPerm Dw w τ ⟨i, hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) = ((w τ.1 i : Fin (Dw.mult τ.1)) : ℕ) := by
  have hp : (i : ℕ) < Dw.p := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw τ.2; omega
  have e : (⟨i, hi⟩ : Fin (Dw.p + Dw.q)) = Fin.castAdd Dw.q ⟨i, hp⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd, Equiv.permCongr_apply]
  simp

theorem flagPerm_small {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) {σ : E →+* ℂ}
    (hσ : ¬ σ (H.rt : E) = H.rt0) (i : Fin (Dw.mult σ)) (hi : Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p + Dw.q) :
    ((flagPerm Dw w ⟨conjEmb σ, GlobalTheory.AllWt.conj_mem hσ⟩ ⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) =
      Dw.p + (Dw.q - 1 - ((w σ i : Fin (Dw.mult σ)) : ℕ)) := by
  have hq : (i : ℕ) < Dw.q := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw hσ; omega
  have e : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p ⟨Dw.q - 1 - i, by omega⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, finCongr_apply, finCongr_symm, Fin.coe_cast]
  have key : ∀ x : Fin (Dw.mult (conjEmb (conjEmb σ))), (x : ℕ) = (i : ℕ) →
      ((w (conjEmb (conjEmb σ)) x : Fin _) : ℕ) = ((w σ i : Fin (Dw.mult σ)) : ℕ) := by
    rintro ⟨x, hx⟩ hxi
    simp only at hxi
    subst hxi
    exact perm_val_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb σ) _ _ i.2
  rw [key _ (by simp; omega)]
  omega

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagMap_rename {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    flagMap Dw (rename (fun x : GlobalTheory.GoodMetric.Root Dw.mult =>
        (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q) =
      rename (fun x : GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) => (x.1, flagPerm Dw w x.1 x.2)) (flagMap Dw Q) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun x => ?_
  simp only [AlgHom.comp_apply, rename_X, flagMap, aeval_X]
  obtain ⟨σ, i⟩ := x
  by_cases h : σ (H.rt : E) = H.rt0
  · simp only [flagRoot, dif_pos h, rename_X]
    congr 2
    exact Fin.ext (flagPerm_big Dw w ⟨σ, h⟩ i _).symm
  · simp only [flagRoot, dif_neg h, map_neg, rename_X]
    congr 3
    exact Fin.ext (flagPerm_small Dw w h i _).symm

theorem prod_sign_eq {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) :
    (∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) = ∏ τ : GlobalTheory.AllWt.Psi H, Equiv.Perm.sign (flagPerm Dw w τ) := by
  simp only [sign_flagPerm, Finset.prod_mul_distrib]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  refine Fintype.prod_equiv
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) } _ _ ?_
  intro τ
  simp only [Equiv.coe_fn_mk]
  exact sign_perm_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb τ.1).symm

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

theorem degFl_flagMap_rename_perm (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw (MvPolynomial.rename
              (fun x : GlobalTheory.GoodMetric.Root Dw.mult => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q)) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) *
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
  rw [flagMap_rename, degFl_rename_perm, prod_sign_eq]
  push_cast
  rfl

end GlobalTheory.Schubert
end
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  first | exact @GlobalTheory.TypeSum.isClosed_fam | exact GlobalTheory.TypeSum.isClosed_fam | (intros; apply GlobalTheory.TypeSum.isClosed_fam <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one | exact GlobalTheory.SobolevHaar.sobolev_at_one | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_blockSymbol_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) = GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | exact GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | (intros; apply GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) = ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  first | exact @GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | exact GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | (intros; apply GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb <;> assumption)
end
