module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CechPicMul


open Classical in
def cl {X : Scheme.{0}} (L : LB X) : Multiplicative (CechPic.Pic X) :=
  if h : L.IsLB then Multiplicative.ofAdd (CechPic.cls L h) else 1

theorem cl_eq {X : Scheme.{0}} {L : LB X} (h : L.IsLB) : cl L = Multiplicative.ofAdd (CechPic.cls L h) := dif_pos h

theorem exists_picardGroup : ∃ (Pic : Scheme.{0} → Type 1) (_ : ∀ X, CommGroup (Pic X)) (cl : ∀ {X : Scheme.{0}}, LB X → Pic X) (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y)),
  (∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (cl L = cl M ↔ LBIso L M)) ∧ (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen)) ∧
  (∀ (X : Scheme.{0}) (c : Pic X), pl (𝟙 X) c = c) ∧ (∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c)) ∧
  (∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ), (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k) ∧
  ∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (LB.div M L).IsLB ∧ cl (LB.div M L) = cl M / cl L := by
  refine ⟨fun X => Multiplicative (CechPic.Pic X), fun X => inferInstance, cl,
    fun f => AddMonoidHom.toMultiplicative (CechPic.pull f), fun X L M hL hM => ?_, fun X L hL => ?_,
    fun X c => CechPic.pull_id c.toAdd, fun X Y Z f g c => CechPic.pull_comp g f c.toAdd,
    fun X Y L hL I _ φ ε => ⟨LB.isLB_linComb hL φ ε, ?_⟩, fun X L M hL hM => ⟨LB.isLB_div hM hL, ?_⟩⟩
  · beta_reduce
    rw [cl_eq hL, cl_eq hM]
    exact CechPic.cls_eq_iff hL hM
  · beta_reduce
    rw [cl_eq hL]
    exact CechPic.cls_eq_zero_iff hL
  · beta_reduce
    rw [cl_eq (LB.isLB_linComb hL φ ε), cl_eq hL, CechPic.cls_linComb hL, ofAdd_sum]
    rfl
  · beta_reduce
    rw [cl_eq (LB.isLB_div hM hL), cl_eq hL, cl_eq hM, CechPic.cls_div hM hL]
    rfl

end GlobalTheory.CechPicMul
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomIntegral

theorem isLieComb_single_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨fun _ => w, fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_fibre {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {G H : Over (Sp R)} [GrpObj H]
    {G' H' : Over (Sp R')} [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hψ : IsPullback ψ H'.hom H.hom (spMap g)) {F : G ⟶ H} {f : G' ⟶ H'} (hf : f.left ≫ ψ = φ ≫ F.left)
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'} (hv : IsVecOver g φ v v')
    (ht : IsVecOver g ψ t t') {b : R} (h : IsLieComb ![b] ![t] (v ≫ F)) : IsLieComb ![g b] ![t'] (v' ≫ f) := by
  rw [isLieComb_single_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h
    rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht,
      ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Over.w, Category.assoc, Over.w t']
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = spMap _
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_extension {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f)
    {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ (isGrpPullback_pullback H j)
  obtain ⟨F, ⟨hF, e⟩, -⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  have e₁ : ((Over.pullback j).map F).left ≫ pullback.fst H.hom j = pullback.fst G.hom j ≫ F.left :=
    pullback.lift_fst _ _ _
  have e₂ : f ≫ b.hom = a.hom ≫ (Over.pullback j).map F := by rw [e, Iso.hom_inv_id_assoc]
  rw [← ha', ← hb', ← Category.assoc, ← Over.comp_left, e₂, Over.comp_left, Category.assoc, Category.assoc]
  exact congrArg (a.hom.left ≫ ·) e₁

end HomIntegral


open HomIntegral in
theorem isIntegral_of_hom_derivative : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  intro hext hB M _ _ P Q v t a hv ht hf
  have key : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      a ∈ Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro 𝔭
    set T := Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors with hT
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 M) 𝔭.ne_bot T
    have : IsFractionRing T M := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.asIdeal.primeCompl T M
    have e : (algebraMap T M).comp (algebraMap (𝓞 M) T) = algebraMap (𝓞 M) M :=
      (IsScalarTower.algebraMap_eq _ _ _).symm
    obtain ⟨P₀, φ₀, hP₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) P
    obtain ⟨Q₀, ψ₀, hQ₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) Q
    obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap T M) P₀
    obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap T M) Q₀
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀.2.1.1 v
    obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀.2.1.1 t
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hP₁.2.1.1 v₀
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hQ₁.2.1.1 t₀
    have hP := e ▸ PolFibre.comp hP₀ hP₁
    have hQ := e ▸ PolFibre.comp hQ₀ hQ₁
    have hv' := e ▸ (PolFibre.vec_iff hP₀.2.1.1 hP₁.2.1.1.w hv₀).1 hv₁
    have ht' := e ▸ (PolFibre.vec_iff hQ₀.2.1.1 hQ₁.2.1.1.w ht₀).1 ht₁
    obtain ⟨f, hfm, hfa⟩ := hf P₁ Q₁ _ _ v₁ t₁ hP hQ hv' ht'
    obtain ⟨F, hF, hFf⟩ := exists_extension (hext T M P₀.A Q₀.A (isSemiAbelian_of_isAbelianScheme _ P₀.isAb)
      (isSemiAbelian_of_isAbelianScheme _ Q₀.isAb)) hP₁.2.1 hQ₁.2.1 f
    have tv₀ := hv₀.isTangent hP₀.2.1 hv
    obtain ⟨c, hc, -⟩ := (ht T _ Q₀ ψ₀ t₀ hQ₀ ht₀).2 _ (isTangent_comp_of_isMonHom F v₀ tv₀)
    have ec : c = ![c 0] := by funext i; fin_cases i; rfl
    rw [ec] at hc
    have h₁ := isLieComb_fibre hQ₁.2.1.1 hFf hv₁ ht₁ hc
    have u := ((ht M _ Q₁ _ t₁ hQ ht').2 _
      (isTangent_comp_of_isMonHom f v₁ (hv₁.isTangent hP₁.2.1 tv₀))).unique hfa h₁
    have ea : a = algebraMap T M (c 0) := congrFun u 0
    rw [ea]
    exact (c 0).2
  have h := Algebra.mem_iInf.2 key
  rw [IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at h
  obtain ⟨x, rfl⟩ := h
  exact x.isIntegral_coe

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem lattice_unif_fibre_eq_of_period : ThetaUnifAV → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair) (c₀ ω : ℂ), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → c₀ ≠ 0 → (∀ z, z ∈ L.lattice ↔ ∃ m n : ℤ, z = c₀ * (m + n * ω)) → ∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsPolFibre s P P' φ → ∀ u : HolUnif P'.A P'.L P'.g, ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * ω) := by
  intro hU R _ P v s L c₀ ω hg hv H hc hL P' φ hφ u
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  have htan : IsTangent v' := IsVecOver.isTangent hφ.2.1 hv' hv
  obtain ⟨w, hw, -⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).1 v' htan
  obtain ⟨hw0, hwL⟩ := H P' φ v' u w hφ hv' hw

  have hg' : P'.g = 1 := hφ.1.trans hg
  have i0 : Fin P'.g := ⟨0, by omega⟩
  have : Subsingleton (Fin P'.g) := by rw [hg']; infer_instance
  have hwi : w i0 ≠ 0 := by
    intro h
    apply hw0
    funext i
    rw [Subsingleton.elim i i0, h]
    rfl
  refine ⟨c₀ * w i0, mul_ne_zero hc hwi, fun z => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = z i0 / w i0 := ⟨_, rfl⟩
  have hz : z = t • w := by
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, ht, div_mul_cancel₀ _ hwi]
  constructor
  · intro hzm
    rw [hz] at hzm
    obtain ⟨m, n, hmn⟩ := (hL t).1 ((hwL t).2 hzm)
    refine ⟨m, n, ?_⟩
    rw [hz]
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, hmn]
    ring
  · rintro ⟨m, n, hmn⟩
    have hzi : z i0 = c₀ * w i0 * (m + n * ω) := congrFun hmn i0
    have htL : t ∈ L.lattice := by
      rw [hL]
      refine ⟨m, n, ?_⟩
      rw [ht, hzi]
      field_simp
    rw [hz]
    exact (hwL t).1 htL

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomDerivDescent

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (a : R) (t w : epsR R ⟶ G) :
    IsLieComb ![a] ![t] w ↔ w.left = spMap (epsScaleR a) ≫ t.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact h

theorem epsScaleR_comp_dualMapR (g : R →+* R') (a : R) :
    (epsScaleR (g a)).comp (Chart.dualMapR g) = (Chart.dualMapR g).comp (epsScaleR a) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR, epsScaleR, mul_comm]

theorem isLieComb_pull {g : R →+* R'} {G H : Over (Sp R)} {G' H' : Over (Sp R')} [GrpObj H] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hψ : IsPullback ψ H'.hom H.hom (spMap g))
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'}
    (hv : IsVecOver g φ v v') (ht : IsVecOver g ψ t t') {f : G ⟶ H} {f' : G' ⟶ H'}
    (hf : f'.left ≫ ψ = φ ≫ f.left) {a : R} (h : IsLieComb ![a] ![t] (v ≫ f)) :
    IsLieComb ![g a] ![t'] (v' ≫ f') := by
  rw [isLieComb_one_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h ⊢
    rw [Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (spMap_comp_spMap _ _).trans
      ((congrArg spMap (epsScaleR_comp_dualMapR g a).symm).trans (spMap_comp_spMap _ _).symm)
  · rw [Over.w, Category.assoc, Over.w]
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = _
    congr 1
    ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_descent (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {Pc Qc : Out.PolAV (Sp ℂ)} {φc : Pc.A.left ⟶ P.A.left}
    {ψc : Qc.A.left ⟶ Q.A.left} (hP : IsPolFibre (algebraMap k ℂ) P Pc φc) (hQ : IsPolFibre (algebraMap k ℂ) Q Qc ψc)
    (fc : Pc.A ⟶ Qc.A) [IsMonHom fc] :
    ∃ (K : IntermediateField k ℂ) (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (m : Pc.A.left ⟶ P₁.A.left) (n : Qc.A.left ⟶ Q₁.A.left) (f₁ : P₁.A ⟶ Q₁.A), FiniteDimensional k K ∧
      IsPolFibre (algebraMap k K) P P₁ φ₁ ∧ IsPolFibre (algebraMap k K) Q Q₁ ψ₁ ∧
      IsPolFibre (algebraMap K ℂ) P₁ Pc m ∧ IsPolFibre (algebraMap K ℂ) Q₁ Qc n ∧ m ≫ φ₁ = φc ∧ n ≫ ψ₁ = ψc ∧
      IsMonHom f₁ ∧ fc.left ≫ n = m ≫ f₁.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ.2.1 (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f, j, hK, hf, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ fc ≫ d.hom) inferInstance
  obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap k K) P
  obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap k K) Q
  obtain ⟨m, hm, hm'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hP₁ hP
  obtain ⟨n, hn, hn'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hQ₁ hQ
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hP₁.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback Q.A _) hQ₁.2.1
  refine ⟨K, P₁, Q₁, φ₁, ψ₁, m, n, a.hom ≫ f ≫ b.hom, hK, hP₁, hQ₁, hm, hn, hm', hn', inferInstance, ?_⟩
  have key : m ≫ a.hom.left = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) ha').trans hm')).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (Over.w a.hom)).trans hm.2.1.1.w)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (Over.w e.hom))))).symm
  refine hQ₁.2.1.1.hom_ext ?_ ?_
  · have r : e.hom.left ≫ (e.inv ≫ fc ≫ d.hom).left = fc.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    rw [Category.assoc, hn', Over.comp_left, Over.comp_left]
    simp only [Category.assoc]
    rw [hb', ← Category.assoc, key, Category.assoc, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, hn.2.1.1.w, hm.2.1.1.w, ← Category.assoc, Over.w]

end HomDerivDescent


open HomDerivDescent in
theorem hom_deriv_descends_to_numberField : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (k : IntermediateField ℚ ℂ) (ρ : R →+* k) (α : ℂ), FiniteDimensional ℚ k → IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre ((algebraMap k ℂ).comp ρ) P P₁ φ₁ → IsPolFibre ((algebraMap k ℂ).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k ℂ).comp ρ) φ₁ v v₁ → IsVecOver ((algebraMap k ℂ).comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁)) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (a : K₁), FiniteDimensional ℚ K₁ ∧ (a : ℂ) = α ∧ (∀ (P₁ Q₁ : Out.PolAV (Sp K₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR K₁ ⟶ P₁.A) (t₁ : epsR K₁ ⟶ Q₁.A), IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) P P₁ φ₁ → IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) Q Q₁ ψ₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) φ₁ v v₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro hT hB R _ P Q v t k ρ α hk hv hbas hhom
  obtain ⟨Pk, φk, hPk⟩ := exists_isPolFibre hB ρ P
  obtain ⟨Qk, ψk, hQk⟩ := exists_isPolFibre hB ρ Q
  obtain ⟨Pc, φc, hPc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Pk
  obtain ⟨Qc, ψc, hQc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Qk
  have hPc' := PolFibre.comp hPk hPc
  have hQc' := PolFibre.comp hQk hQc
  obtain ⟨vc, hvc, -⟩ := existsUnique_isVecOver hPc'.2.1.1 v
  obtain ⟨tc, htc, -⟩ := existsUnique_isVecOver hQc'.2.1.1 t
  obtain ⟨fc, hfc, hα⟩ := hhom Pc Qc _ _ vc tc hPc' hQc' hvc htc
  obtain ⟨K, P₀, Q₀, φ₀, ψ₀, m, n, f₀, hK, hP₀, hQ₀, hm, hn, em, en, hf₀, ef⟩ :=
    exists_descent hT hB k Pk Qk hPc hQc fc
  have hP₀' := PolFibre.comp hPk hP₀
  have hQ₀' := PolFibre.comp hQk hQ₀
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀'.2.1.1 v
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀'.2.1.1 t
  obtain ⟨c, hc, -⟩ := (hbas _ _ _ _ _ hQ₀' ht₀).2 (v₀ ≫ f₀)
    (HomDescent.isTangent_comp f₀ (hv₀.isTangent hP₀'.2.1 hv))
  obtain ⟨a, rfl⟩ : ∃ a, c = ![a] := ⟨c 0, by ext i; fin_cases i; rfl⟩
  have hv' : IsVecOver (algebraMap K ℂ) m v₀ vc :=
    (PolFibre.vec_iff hP₀'.2.1.1 hm.2.1.1.w hv₀).2 (by rw [← Category.assoc, em]; exact hvc)
  have ht' : IsVecOver (algebraMap K ℂ) n t₀ tc :=
    (PolFibre.vec_iff hQ₀'.2.1.1 hn.2.1.1.w ht₀).2 (by rw [← Category.assoc, en]; exact htc)
  have hα' := isLieComb_pull hn.2.1.1 hv' ht' ef hc
  have haα : algebraMap K ℂ a = α := congrFun (((hbas _ _ _ _ _ hQc' htc).2 (vc ≫ fc)
    (HomDescent.isTangent_comp fc (hvc.isTangent hPc'.2.1 hv))).unique hα' hα) 0
  have main : ∀ (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (v₁ : epsR K ⟶ P₁.A) (t₁ : epsR K ⟶ Q₁.A), IsPolFibre ((algebraMap k K).comp ρ) P P₁ φ₁ →
      IsPolFibre ((algebraMap k K).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k K).comp ρ) φ₁ v v₁ →
      IsVecOver ((algebraMap k K).comp ρ) ψ₁ t t₁ →
      ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁) := by
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁
    obtain ⟨p, hp, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hP₀' hP₁
    obtain ⟨q, hq, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hQ₀' hQ₁
    obtain ⟨f₁, hf₁, e₁⟩ := HomDescent.exists_isMonHom_pull hp.2.1 hq.2.1 f₀
    exact ⟨f₁, hf₁, isLieComb_pull hq.2.1.1 ((PolFibre.vec_iff hP₀'.2.1.1 hp.2.1.1.w hv₀).2 hv₁)
      ((PolFibre.vec_iff hQ₀'.2.1.1 hq.2.1.1.w ht₀).2 ht₁) e₁ hc⟩
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  exact ⟨K.restrictScalars ℚ, fun x hx => K.algebraMap_mem ⟨x, hx⟩, a, hfin, haα, main⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem abelianScheme_hom_extends_dedekind_of_isGrpPullback :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (G₀ G₀' : Over (Sp K)) [GrpObj G₀] [GrpObj G₀'] (φ : G₀.left ⟶ G.left) (φ' : G₀'.left ⟶ G'.left), IsAbelianScheme G → IsAbelianScheme G' → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → IsGrpPullback G₀' G' (spMap (algebraMap R K)) φ' → ∀ f : G₀ ⟶ G₀', IsMonHom f → ∃ F : G ⟶ G', IsMonHom F ∧ f.left ≫ φ' = φ ≫ F.left ∧ ∀ F' : G ⟶ G', f.left ≫ φ' = φ ≫ F'.left → F' = F := by
  intro H R K _ _ _ _ _ G G' _ _ G₀ G₀' _ _ φ φ' hG hG' hφ hφ' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G _) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := abelianScheme_hom_extends_dedekind H R K G G' hG hG'
    (a.hom ≫ f ≫ b.hom) inferInstance
  have key : f.left ≫ φ' = φ ≫ F.left := by
    have h₁ := ExtUnique.pullback_map_left_fst (spMap (algebraMap R K)) F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  exact ⟨F, hF, key, fun F' h' => ExtUnique.over_hom_ext_of_isPullback (j := spMap (algebraMap R K)) hφ.1 (h'.symm.trans key)⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open GlobalTheory.CechPic in
theorem exists_rigLB_extension_dedekind :
    ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ (X' : Scheme.{0}) (π : X' ⟶ G.left) (p : X' ⟶ Sp K), IsPullback π p G.hom (spMap (algebraMap R K)) → ∀ L : LB X', L.IsLB → ∃ L' : RigLB G, LBIso (L'.L.pull π) L := by
  intro R K _ _ _ _ _ A _ hA X' φ p hφ N hN
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, hLN⟩ := exists_lineBundle_extension_of_generalizing A.left X' φ
    (Flat.generalizingMap φ) hst N hN
  let e : Sp R ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hL' : (L.pull (A.hom ≫ e)).IsLB := pull_isLB hL _
  have hM : (LB.div L (L.pull (A.hom ≫ e))).IsLB := LB.isLB_div hL hL'
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen ((LB.div L (L.pull (A.hom ≫ e))).pull e), t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hM e)).1 ?_
    rw [cls_pull hM e (pull_isLB hM e), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, he,
      Category.id_comp, sub_self]
  refine ⟨⟨LB.div L (L.pull (A.hom ≫ e)), t, hM, ht⟩, (cls_eq_iff (pull_isLB hM φ) hN).1 ?_⟩
  have h0 : pull (spMap (algebraMap R K) ≫ e) (cls L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 (DVR.exists_gen_of_local L hL _ _)
  rw [cls_pull hM φ (pull_isLB hM φ), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, hφ.w,
    Category.assoc, pull_comp, h0, map_zero, sub_zero]
  exact (cls_eq_iff (pull_isLB hL φ) hN).2 hLN

end GlobalTheory.CM
end
