module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix


theorem _root_.GlobalTheory.T.adelic_schwartz_support_compact_invariance : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  first | exact @GlobalTheory.FinLocSchA.compact_support_locally_constant_fin | exact GlobalTheory.FinLocSchA.compact_support_locally_constant_fin | (intros; apply GlobalTheory.FinLocSchA.compact_support_locally_constant_fin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicSchwartzSpace_translate_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ, (fun x => φ (x + a)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchwartzTranslate.main | exact GlobalTheory.SchwartzTranslate.main | (intros; apply GlobalTheory.SchwartzTranslate.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchAConj.star_mem_schA | exact GlobalTheory.SchAConj.star_mem_schA | (intros; apply GlobalTheory.SchAConj.star_mem_schA <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

end GlobalTheory.CurveClosure
end
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.AmplePos

theorem pos_of_bound {h : ℕ → ℕ} {d C m₀ : ℕ} {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hf : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ h m)
    (hb : ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d| ≤
      C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) : 0 < a := by
  by_contra ha
  rw [not_lt] at ha
  obtain ⟨m, hm1, hm2⟩ := (hf.and_eventually (eventually_ge_atTop
    (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm2
  have hm1' : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  have hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m := by
    have h1 := Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))
    have h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hmK'
    push_cast at h2
    linarith
  have hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
    have h3 := (abs_le.mp (hb m hmm₀)).2
    have h4 : a * (m : ℤ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (by positivity)
    linarith
  have hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1)) := by
    have h5 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h5
    exact h5
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one] at hreal hm1
    linarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hreal hmK
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
    have h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) e
    have hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c := mul_pos hF hc
    rw [div_lt_iff₀ hFc] at hmK
    have h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤
        (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hF.le
    have hCpos : (0 : ℝ) ≤ C := by positivity
    have h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤
        (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hme : (0 : ℝ) < (m : ℝ) ^ e := by positivity
    have h8 := mul_lt_mul_of_pos_right hmK hme
    have h9 : (m : ℝ) ^ (e + 1) = m * m ^ e := by ring
    rw [h9] at h6
    nlinarith [h6, hreal, h7, h8]

theorem topSelf_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) →
    ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  intro k _ _ X _ _ hp d hd A hA
  obtain ⟨D, hD, c, hc, hf⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDd : D = d := by
    rw [hD] at hd
    exact_mod_cast hd
  subst hDd
  have hsupp : suppDim (structureModule X) ≤ (D : ℕ) := by
    unfold GlobalTheory.QCoh.suppDim
    rw [← hD]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨C, m₀, hb⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA
  rw [topSelf_def]
  exact pos_of_bound hc hf hb

end GlobalTheory.AmplePos
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

variable {B : LB Y} {B' : LB Y'}


omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in
theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

namespace HilbertSamuel

end HilbertSamuel

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.exists_smooth_lift_of_abelian : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  intro hF hP R R₀ _ _ I hI π hπ hk A₀ _ g hab hsm
  haveI := hsm
  haveI : Smooth A₀.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A₀ ⊗ A₀).hom := inferInstanceAs (Smooth (Limits.pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ I hI π hπ hk
  obtain ⟨hPar, hProj, hadd⟩ := hF R₀ A₀ g hab hsm
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff A₀.hom) (fun T ↦ smooth_sec_affine A₀.hom T.unop)
  obtain ⟨L₂⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff (A₀ ⊗ A₀).hom)
    (fun T ↦ smooth_sec_affine (A₀ ⊗ A₀).hom T.unop)
  have key : ∀ w, L.IsOb2 α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L w
    have nat : ∀ (f : A₀ ⊗ A₀ ⟶ A₀) (w' : GlobForm (A₀ ⊗ A₀).hom) (c' : CatCoh.H2 (ext R₁ (OAff (A₀ ⊗ A₀).hom))),
        IsPullForm (overW f) w w' → L₂.IsOb2 α w' c' → IsExtendedPullbackDegTwo R₁ (overW f) c c' := by
      intro f w' c' hw hc'
      refine GlobalTheory.T.degreeTwoObstructionClass_natural R R₀ I hI π hπ hk R₁ α _ (OAff A₀.hom) _ (OAff (A₀ ⊗ A₀).hom) _ (pairFst f.left)
        (pairPull (overW f)) L L₂ w w' c c' (fun T ↦ ?_) hc hc'
      exact (congrArg (fun z : Glob1 (OPair f.left (A₀ ⊗ A₀).hom) ↦ z.1 T) hw).trans
        (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff (A₀ ⊗ A₀).hom) (pairFst f.left) T _)
    obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (fst A₀ A₀)) w)
    obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (snd A₀ A₀)) w)
    have hm : pullForm (overW μ[A₀]) w = pullForm (overW (fst A₀ A₀)) w + pullForm (overW (snd A₀ A₀)) w :=
      hadd w _ _ _ (isPullForm_pullForm _ w) (isPullForm_pullForm _ w) (isPullForm_pullForm _ w)
    have hcm : L₂.IsOb2 α (pullForm (overW μ[A₀]) w) (c₁ + c₂) := by
      rw [hm]; exact isOb2_add R R₀ I hI π hπ hk R₁ α _ _ L₂ _ _ c₁ c₂ hc₁ hc₂
    have h0 : c = 0 := hP R₀ R₁ α.q α.sq A₀ g hab hsm c c₁ c₂
      (nat _ _ _ (isPullForm_pullForm _ w) hcm) (nat _ _ _ (isPullForm_pullForm _ w) hc₁)
      (nat _ _ _ (isPullForm_pullForm _ w) hc₂)
    rw [← h0]; exact hc
  obtain ⟨L', hL'⟩ := GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero R R₀ I hI π hπ hk R₁ α _ A₀.hom hPar hProj L key
  obtain ⟨S⟩ := GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun R R₀ I hI π hπ hk _ A₀.hom L' hL'
  obtain ⟨X, s, i, hci, hsi, ⟨hpres⟩⟩ := GlobalTheory.LiftGlue.exists_presents R R₀ I hI π hπ hk _ A₀.hom S
  obtain ⟨hpb, hsmooth⟩ := GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk _ A₀.hom S X s i hci hsi hpres
  exact ⟨Over.mk s, i, hpb, hsmooth⟩
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.schwartzBruhat_rank_deficient_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  first | exact @GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | exact GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.span_character_translates_coinvariant : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  first | exact @GlobalTheory.RankFibre.coinv_or_fullRank_le | exact GlobalTheory.RankFibre.coinv_or_fullRank_le | (intros; apply GlobalTheory.RankFibre.coinv_or_fullRank_le <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

theorem _root_.GlobalTheory.T.smooth_character_of_trivial_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  first | exact @GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | exact GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | (intros; apply GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lintegral_norm_sq_right_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.SplitFlip.lintegral_mul_invT_sq | exact GlobalTheory.SplitFlip.lintegral_mul_invT_sq | (intros; apply GlobalTheory.SplitFlip.lintegral_mul_invT_sq <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Monic → aeval u (Q.map e.symm.toRingHom) = 0 → ∀ y : GLw m w, y ∈ GlobalTheory.LFun.KGL w (n := m) → y.val.charpoly = Q → IsIntegral K.O u := by
  first | exact @GlobalTheory.TwLat.isIntegral_of_charpoly_intGL | exact GlobalTheory.TwLat.isIntegral_of_charpoly_intGL | (intros; apply GlobalTheory.TwLat.isIntegral_of_charpoly_intGL <;> assumption)
end
