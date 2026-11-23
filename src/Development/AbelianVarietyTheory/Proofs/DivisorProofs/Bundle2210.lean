module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfVac

open GlobalTheory.RealLift GlobalTheory.KInfPol

theorem gaussD_of_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA f₀ hf₀
  have hB := hP.base
  have hw := hP.weil
  rw [← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hB.std] at hf₀ ⊢
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
  have hv := at_mul_right hu (mat k⁻¹)ᵀ
  have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
  have h1 := hint _ hv f₀
  have h2 := hint _ hv' f₀
  rw [hcan] at h1 h2
  have e1 := (hL _ _ _).2.2.1 _ hg h1
  have e2 := (hL _ _ _).2.2.1 _ hg' h2
  have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
  · rw [e1, e2, key, map_smul]
  · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul]
      change (mat (k⁻¹ * k)).map _ = 1
      rw [inv_mul_cancel]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
    have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
      calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
            ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
        _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
            (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]

end GlobalTheory.KInfVac

end
end

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

namespace GlobalTheory.EtaleReducedEq

theorem isRadical_map_of_etale {Q C : Type} [CommRing Q] [CommRing C] [Algebra Q C]
    [Algebra.Etale Q C] (I : Ideal Q) (hI : I.IsRadical) :
    (I.map (algebraMap Q C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have : _root_.IsReduced (TensorProduct Q (Q ⧸ I) C) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Q ⧸ I) _
  have : _root_.IsReduced (TensorProduct Q C (Q ⧸ I)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm Q C (Q ⧸ I)).toRingEquiv (RingEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
    (RingEquiv.injective _)

theorem etale_eval₂Hom_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale) :
    (MvPolynomial.eval₂Hom ψ N).Etale := by
  have : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway g
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have : Algebra.Etale (MvPolynomial ι R) (MvPolynomial ι A) :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R (MvPolynomial ι R) A (MvPolynomial ι A))
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  letI : Algebra (MvPolynomial ι R) C :=
    (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).toAlgebra
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι A) C :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  have : Algebra.Etale (MvPolynomial ι R) C := hE
  exact Algebra.Etale.of_restrictScalars (MvPolynomial ι R) (MvPolynomial ι A) C

theorem isRadical_span_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g δ : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale)
    (hδ : (Ideal.span {algebraMap R A δ}).IsRadical) :
    (Ideal.span {ψ (algebraMap R A δ)}).IsRadical := by
  have he := etale_eval₂Hom_of_away g ψ N hE
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  have : Algebra.Etale (MvPolynomial ι A) C := he
  have hI : (Ideal.map (MvPolynomial.C (σ := ι)) (Ideal.span {algebraMap R A δ})).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced] at hδ ⊢
    exact isReduced_of_injective
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (Ideal.span {algebraMap R A δ})).symm.toRingEquiv
      (RingEquiv.injective _)
  have h2 := isRadical_map_of_etale (C := C) _ hI
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, MvPolynomial.eval₂Hom_C] at h2
  exact h2

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_ger_iff_not_mem {X : Scheme.{0}} (Z : Closeds X) (U' : X.affineOpens)
    (δ : Γ(X, U'.1)) (h : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U' = Ideal.span {δ})
    (x : X) (hx : x ∈ U'.1) : IsUnit (ger x hx δ) ↔ x ∉ Z := by
  obtain ⟨P, rfl⟩ : x ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hx
  have hS : IsClosed (X := PrimeSpectrum Γ(X, U'.1)) (U'.2.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage U'.2.fromSpec.continuous
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at h
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, U'.2.fromSpec_preimage_basicOpen]
  change δ ∉ P.asIdeal ↔ _
  rw [not_iff_not]
  have e := congrArg (P ∈ ·)
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U'.2.fromSpec ⁻¹' (Z : Set X)))
  rw [hS.closure_eq, h, PrimeSpectrum.zeroLocus_span] at e
  have e3 : (δ ∈ P.asIdeal) = (P ∈ PrimeSpectrum.zeroLocus {δ}) :=
    propext ((PrimeSpectrum.mem_zeroLocus (P : PrimeSpectrum Γ(X, U'.1)) {δ}).trans
      Set.singleton_subset_iff).symm
  exact (e3.trans e).to_iff

theorem mem_iff_not_isUnit_ger {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Y, W)) (hP : hW.fromSpec P ∈ W) (c : Γ(Y, W)) :
    c ∈ P.asIdeal ↔ ¬ IsUnit (ger (hW.fromSpec P) hP c) := by
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, hW.fromSpec_preimage_basicOpen]
  change _ ↔ ¬ ¬ c ∈ P.asIdeal
  rw [not_not]

theorem reducedEq_pullback_etale : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  intro X Y _ q ι _ Vo U U' hU' W hW hWU N hEt δ hδ
  have part1 : ∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 →
      (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo) := by
    intro z hz hzU'
    rw [ger_appLE q hWU z hz δ, isUnit_map_iff, ← ger_resG hU' (q z) hzU' δ,
      isUnit_ger_iff_not_mem _ U' _ hδ]
    exact not_not
  refine ⟨part1, ?_⟩
  intro W' hW' hW'U' f hf z hz
  obtain ⟨g, hgU', hzg⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨q z, hW'U' hz⟩ (hWU (hW' hz))
  set g' := resG X hU' g
  set V := X.basicOpen g'
  have hV' : V = X.basicOpen g := by
    simp only [V, g', resG, Scheme.basicOpen_res]
    exact inf_eq_right.2 hgU'
  have hVU' : V ≤ U'.1 := X.basicOpen_le g'
  have hVU : V ≤ U.1 := hVU'.trans hU'
  letI : Algebra Γ(X, U.1) Γ(X, V) := (resG X hVU).toAlgebra
  haveI : IsLocalization.Away g Γ(X, V) := U.2.isLocalization_of_eq_basicOpen g (homOfLE hVU) hV'
  have hδV : (Ideal.span {algebraMap Γ(X, U.1) Γ(X, V) δ}).IsRadical := by
    have e := (Scheme.IdealSheafData.vanishingIdeal Vo.compl).map_ideal_basicOpen U' g'
    rw [hδ, Ideal.map_span, Set.image_singleton] at e
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal
        (X.affineBasicOpen g')).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    rw [← e] at hrad
    have e2 : algebraMap Γ(X, U.1) Γ(X, V) δ =
        (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom (resG X hU' δ) :=
      (resG_resG hU' hVU' δ).symm
    rw [e2]
    exact hrad
  have hzV : q z ∈ V := hV' ▸ hzg
  obtain ⟨h, hhle, hzh⟩ := hW.exists_basicOpen_le (V := W' ⊓ q ⁻¹ᵁ V) ⟨z, hz, hzV⟩ (hW' hz)
  set W1 := Y.basicOpen h
  have hW1W : W1 ≤ W := Y.basicOpen_le h
  have hW1V : W1 ≤ q ⁻¹ᵁ V := hhle.trans inf_le_right
  have hW1W' : W1 ≤ W' := hhle.trans inf_le_left
  have hW1 : IsAffineOpen W1 := hW.basicOpen h
  let ψ : Γ(X, V) →+* Γ(Y, W1) := (q.appLE V W1 hW1V).hom
  have hcomp : MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i)) =
      (resG Y hW1W).comp (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra, ψ, resG]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
    · intro i
      simp
  have hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i))).Etale := by
    rw [hcomp]
    have h2 : (resG Y hW1W).Etale := by
      letI : Algebra Γ(Y, W) Γ(Y, W1) := (resG Y hW1W).toAlgebra
      haveI : IsLocalization.Away h Γ(Y, W1) := hW.isLocalization_basicOpen h
      exact Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ hEt h2
  have rad := isRadical_span_of_away g δ ψ (fun i => resG Y hW1W (N i)) hE hδV
  have hd : ψ (algebraMap Γ(X, U.1) Γ(X, V) δ) = resG Y hW1W ((q.appLE U.1 W hWU).hom δ) := by
    have := congrArg (fun F => F (MvPolynomial.C δ)) hcomp
    simpa using this
  set d := ψ (algebraMap Γ(X, U.1) Γ(X, V) δ)
  set b := resG Y hW1W' f
  have hb : b ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hdP, hP⟩
    let P' : Spec Γ(Y, W1) := ⟨P, hP⟩
    have hz' : hW1.fromSpec P' ∈ W1 := by
      rw [← SetLike.mem_coe, ← hW1.range_fromSpec]; exact Set.mem_range_self _
    have hdP' : d ∈ P'.asIdeal := hdP (Ideal.mem_span_singleton_self d)
    rw [mem_iff_not_isUnit_ger hW1 P' hz', hd, ger_resG] at hdP'
    have hq : q (hW1.fromSpec P') ∉ Vo := by
      rw [← part1 _ (hW1W hz') (hVU' (hW1V hz'))]
      exact hdP'
    have hm := hf _ (hW1W' hz') hq
    change b ∈ P'.asIdeal
    rw [mem_iff_not_isUnit_ger hW1 P' hz', ger_resG]
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (rad hb)
  refine ⟨ger z hzh c, ?_⟩
  rw [← ger_resG hW1W' z hzh f, ← ger_resG hW1W z hzh, ← hd]
  change ger z hzh b = _
  rw [← hc, map_mul, mul_comm]

end GlobalTheory.EtaleReducedEq
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    apply Subtype.ext
    change f.hom = (0 : A ⟶ B).hom
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    apply Subtype.ext
    exact hom_eq_of_isIso hi _ _

end GlobalTheory.AV.AbVar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj


theorem _root_.GlobalTheory.T.geometric_point_abelian_variety_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  have push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
      (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A))
      (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
      (z : T ⟶ (Over.pullback x).obj A) :
      e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
    have map_fst : ((Over.pullback x).map f).left ≫ pullback.fst A.hom x =
        pullback.fst A.hom x ≫ f.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, map_fst, Category.assoc]
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB), IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | exact GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | (intros; apply GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff <;> assumption)
end
