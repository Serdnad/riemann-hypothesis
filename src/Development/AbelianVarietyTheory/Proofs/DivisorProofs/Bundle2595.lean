module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem fp_HH1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : FP R (HH1 A.hom) (2 * g) := by
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have h0 := (GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs).2.1
  have hinj : Function.Injective (clAll (OAff A.hom) hcl) := by
    unfold clAll
    exact (ofForm_injective_of_H0Const R _ _ h0).comp (LinearEquiv.ofTop _ hcl).symm.injective
  have hex : Function.Exact (clAll (OAff A.hom) hcl) (toHO1 A.hom) := by
    rw [LinearMap.exact_iff]
    change Fil1 (OAff A.hom) = _
    rw [Fil1_eq_range]
    unfold clAll
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).1 R _ _ _ g g _ _ hinj (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs) hex
    (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).1
  rwa [two_mul]

theorem rank_prim_HH1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  intro R _ A _ g hA hs
  refine ⟨fp_HH1 R A g hA hs, fun x ↦ ?_⟩
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have ax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.2
  set i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : HH1 A.hom × HH1 A.hom →ₗ[R] HH1 (A ⊗ A).hom :=
    (deRhamH1Pullback (fst A A)).coprod (deRhamH1Pullback (snd A A))
  let r : HH1 (A ⊗ A).hom →ₗ[R] HH1 A.hom × HH1 A.hom := (deRhamH1Pullback i₁).prod (deRhamH1Pullback i₂)
  have hrf : ∀ p, r (f p) = p := by
    rintro ⟨a, b⟩
    show (deRhamH1Pullback i₁ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b), deRhamH1Pullback i₂ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b)) = (a, b)
    rw [map_add (f := _), map_add (f := _), (ax a).1, (ax b).2.1, (ax a).2.2.2.1, (ax b).2.2.2.2.1, add_zero, zero_add]
  have hM : FP R (HH1 A.hom × HH1 A.hom) (2 * (g + g)) := by
    have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ _ _ (fp_HH1 R A g hA hs) (fp_HH1 R A g hA hs)
    rwa [← mul_add] at this
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ _ hM (fp_HH1 R (A ⊗ A) (g + g) hAA hsAA) f r hrf
  obtain ⟨p, hp⟩ := hbij.2 (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)
  have hry : r (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x) = 0 := by
    show (deRhamH1Pullback i₁ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x),
      deRhamH1Pullback i₂ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)) = (0, 0)
    rw [map_sub, map_sub, map_sub, map_sub, (ax x).1, (ax x).2.1, (ax x).2.2.1,
      (ax x).2.2.2.1, (ax x).2.2.2.2.1, (ax x).2.2.2.2.2, sub_self, sub_zero, sub_zero, sub_self]
  have hp0 : p = 0 := by rw [← hrf p, hp, hry]
  have h0 : deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x = 0 := by rw [← hp, hp0, map_zero]
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.AbCoh
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.FLower

open MvPolynomial

abbrev Deg (D q : ℕ) : Type := {α : Fin (D + 1) →₀ ℕ // α.degree = q}

scoped instance (D q : ℕ) : Finite (Deg D q) :=
  Nat.finite_of_card_ne_zero <| by
    rw [(GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1]
    exact (Nat.choose_pos (Nat.le_add_left D q)).ne'

scoped instance (D q : ℕ) : Fintype (Deg D q) := Fintype.ofFinite _

theorem card_deg (D q : ℕ) : Fintype.card (Deg D q) = (q + D).choose D := by
  rw [← Nat.card_eq_fintype_card]; exact (GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1

def xm {K : Type} [CommRing K] {D : ℕ} (x : Fin (D + 1) → K) (α : Fin (D + 1) →₀ ℕ) : K := ∏ l, x l ^ α l

theorem aeval_eq_sum {K : Type} [CommRing K] {D q : ℕ} (x : Fin (D + 1) → K) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous q) : aeval x T = ∑ α : Deg D q, AddMonoidAlgebra.coeff T α.1 • xm x α.1 := by
  rw [aeval_def, eval₂_eq']
  have hsub : T.support ⊆ Finset.univ.map (Function.Embedding.subtype fun α : Fin (D + 1) →₀ ℕ => α.degree = q) := by
    intro d hd
    have h := hT (mem_support_iff.1 hd)
    refine Finset.mem_map.2 ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩
    rw [Finsupp.degree_eq_weight_one]; exact h
  rw [Finset.sum_subset hsub (fun d _ hd => by rw [notMem_support_iff.1 hd, map_zero, zero_mul]), Finset.sum_map]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [zsmul_eq_mul, xm, algebraMap_int_eq, eq_intCast]
  rfl

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem H_congr (P : Pair p) {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {f : X.functionField} (hf : f ∈ P.H a b) :
    f ∈ P.H a' b' := by subst ha hb; exact hf

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem prod_pow_mem (P : Pair p) (e : ℤ) {D : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (s : Finset (Fin (D + 1))) :
    (∏ l ∈ s, x l ^ α l) ∈ P.H ((∑ l ∈ s, (α l : ℤ)) * e) 0 ∧ ∀ σ y,
      P.nu ((∑ l ∈ s, (α l : ℤ)) * e) 0 σ y (∏ l ∈ s, x l ^ α l) = ∏ l ∈ s, P.nu e 0 σ y (x l) ^ α l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x 0) (hx 0) 0
    simp only [Finset.prod_empty, Finset.sum_empty, pow_zero, Nat.cast_zero, zero_mul] at h1 h2 ⊢
    exact ⟨h1, fun σ y => h2 σ y⟩
  | insert l s hl ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx l) (α l)
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 ih.1
    have ea : ((α l : ℕ) : ℤ) * e + (∑ l ∈ s, (α l : ℤ)) * e = (∑ l ∈ insert l s, (α l : ℤ)) * e := by
      rw [Finset.sum_insert hl]; ring
    have eb : ((α l : ℕ) : ℤ) * 0 + 0 = 0 := by ring
    rw [Finset.prod_insert hl]
    refine ⟨H_congr P ea eb h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [eb, ea] at h5
    rw [Finset.prod_insert hl, h5, h2 σ y, ih.2 σ y]

theorem xm_mem (P : Pair p) (e : ℤ) {D q : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (hα : α.degree = q) :
    xm x α ∈ P.H (e * q) 0 ∧ ∀ σ y, P.nu (e * q) 0 σ y (xm x α) = ∏ l, P.nu e 0 σ y (x l) ^ α l := by
  have hq : (∑ l, (α l : ℤ)) * e = e * q := by
    subst hα; rw [mul_comm, Finsupp.degree_eq_sum]; push_cast; rfl
  obtain ⟨h1, h2⟩ := prod_pow_mem P e x hx α Finset.univ
  exact ⟨H_congr P hq rfl h1, fun σ y => by rw [← hq, xm, h2]⟩

theorem sum_zsmul (P : Pair p) (a b : ℤ) {J : Type} [Fintype J] (f : J → X.functionField) (hf : ∀ j, f j ∈ P.H a b)
    (n : J → ℤ) : (∑ j, n j • f j) ∈ P.H a b ∧ ∀ σ y,
      P.nu a b σ y (∑ j, n j • f j) ≤ ∑ j, |(n j : ℝ)| * P.nu a b σ y (f j) := by
  refine ⟨AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hf j) _, fun σ y => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y
  let F : P.H a b := ∑ j, n j • (⟨f j, hf j⟩ : P.H a b)
  have hF : (F : X.functionField) = ∑ j, n j • f j := by simp [F]

  rw [← hF, ← norm_val, ← hℓ, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, norm_mul, Complex.norm_intCast, hℓ, norm_val]

theorem count_rank_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (∃ v : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) → X.functionField, (∀ i, v i ∈ P.H (e * (q + c : ℕ) + a) b) ∧ LinearIndependent ℤ v) ∧ ∀ R : ℝ, 0 ≤ R → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (((2 * ⌊R⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + D).choose D) : ℕ) : ℕ∞) ≤ (P.Bl (e * (q + c : ℕ) + a) b (C * (q + D).choose D * R)).encard := by
  intro k _ X _ p D hX P hA e x hx a b
  haveI : CharZero X.functionField := (GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hX).1
  obtain ⟨hx0, halg, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hx
  set δ := Module.finrank (ratF x) X.functionField with hδ
  obtain ⟨c, g, hg, hgi⟩ : ∃ (c : ℕ) (g : Fin δ → X.functionField), (∀ i, g i ∈ P.H (e * c + a) b) ∧
      LinearIndependent (ratF x) g := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hX P hA e x hx a b
  have hbd : ∀ i, ∃ M : ℝ, ∀ σ y, P.nu (e * c + a) b σ y (g i) ≤ M := fun i =>
    ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P _ b).2 (g i) (hg i)).2
  choose M hM using hbd
  set M' : ℝ := 1 + ∑ i, |M i| with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have hgM : ∀ i σ y, P.nu (e * c + a) b σ y (g i) ≤ M' := fun i σ y => by
    have := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg (M i)) (Finset.mem_univ i)
    have := le_abs_self (M i)
    have := hM i σ y
    simp only [hM'] at *
    linarith
  refine ⟨c, ((δ : ℝ) + 1) * M', by positivity, fun q => ?_⟩
  let w : Fin δ × Deg D q → X.functionField := fun ia => xm x ia.2.1 * g ia.1
  have hidx : (e : ℤ) * q + (e * c + a) = e * ((q + c : ℕ) : ℤ) + a := by push_cast; ring
  have hw : ∀ ia, w ia ∈ P.H (e * ((q + c : ℕ) : ℤ) + a) b ∧ ∀ σ y,
      P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) =
        (∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l) * P.nu (e * c + a) b σ y (g ia.1) := by
    intro ia
    obtain ⟨h1, h2⟩ := xm_mem P e x hx.mem ia.2.1 ia.2.2
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 (hg ia.1)
    have h0b : (0 : ℤ) + b = b := zero_add b
    refine ⟨H_congr P hidx h0b h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [hidx, h0b] at h5
    rw [h5, h2 σ y]
  constructor
  · have hcard : δ * (q + D).choose D = Nat.card (Fin δ × Deg D q) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Deg D q), card_deg, Nat.card_eq_fintype_card, Fintype.card_fin]
    let E : Fin (δ * (q + D).choose D) ≃ Fin δ × Deg D q := (finCongr hcard).trans (Finite.equivFin _).symm
    refine ⟨w ∘ E, fun i => (hw (E i)).1, (linearIndependent_equiv E).2 ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro n hn ia
    let T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ := fun i => ∑ α : Deg D q, monomial α.1 (n (i, α))
    have hT : ∀ i, (T i).IsHomogeneous q := fun i =>
      IsHomogeneous.sum _ _ _ fun α _ => isHomogeneous_monomial _ α.2
    have hTe : ∀ i, aeval x (T i) = ∑ α : Deg D q, n (i, α) • xm x α.1 := fun i => by

      simp only [T, map_sum, aeval_monomial, Finsupp.prod_pow, algebraMap_int_eq, eq_intCast, zsmul_eq_mul, xm]
    have h0 := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q T hT (by
      rw [← hn, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc])
    have h1 := congrArg (AddMonoidAlgebra.coeff · ia.2.1) (congrFun h0 ia.1)
    simp only [T, coeff_sum, coeff_monomial, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    have h2 : ∀ α : Deg D q, (if (α : Fin (D + 1) →₀ ℕ) = ia.2.1 then n (ia.1, α) else 0) =
        if α = ia.2 then n (ia.1, α) else 0 := fun α => by simp only [Subtype.coe_inj]
    rw [Finset.sum_congr rfl fun α _ => h2 α] at h1
    simpa using h1
  · intro R hR hxl
    obtain ⟨hfinS, hcnt, -, -, -⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D q δ R hR
    let Φ : (Fin δ → MvPolynomial (Fin (D + 1)) ℤ) → X.functionField := fun T => ∑ i, aeval x (T i) * g i
    have hΦ : ∀ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous q) →
        Φ T = ∑ ia : Fin δ × Deg D q, AddMonoidAlgebra.coeff (T ia.1) ia.2.1 • w ia := by
      intro T hT
      simp only [Φ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aeval_eq_sum x (T i) (hT i), Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc]
    have hinj : Set.InjOn Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R} := by
      intro T hT T' hT' h
      have := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q (T - T')
        (fun i => (hT.1 i).sub (hT'.1 i)) (by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          exact sub_eq_zero.2 h)
      exact sub_eq_zero.1 this
    have hmaps : Set.MapsTo Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}
        (P.Bl (e * (q + c : ℕ) + a) b (((δ : ℝ) + 1) * M' * (q + D).choose D * R)) := by
      intro T hT
      rw [Set.mem_ofPred_eq] at hT
      rw [hΦ T hT.1]
      obtain ⟨h1, h2⟩ := sum_zsmul P _ b w (fun ia => (hw ia).1) (fun ia => AddMonoidAlgebra.coeff (T ia.1) ia.2.1)
      refine ⟨h1, fun σ y => (h2 σ y).trans ?_⟩
      have hterm : ∀ ia : Fin δ × Deg D q,
          |((AddMonoidAlgebra.coeff (T ia.1) ia.2.1 : ℤ) : ℝ)| * P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) ≤ R * M' := by
        intro ia
        rw [(hw ia).2 σ y]
        have hp : ∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l ≤ 1 :=
          Finset.prod_le_one₀ (fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _)
            (fun l _ => pow_le_one₀ (nu_nonneg _ _ _ _ _ _) (hxl l σ y))
        refine mul_le_mul (hT.2 _ _) ?_
          (mul_nonneg (Finset.prod_nonneg fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _) (nu_nonneg _ _ _ _ _ _)) hR
        calc _ ≤ 1 * M' := mul_le_mul hp (hgM _ σ y) (nu_nonneg _ _ _ _ _ _) zero_le_one
          _ = M' := one_mul _
      refine (Finset.sum_le_sum fun ia _ => hterm ia).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_deg, nsmul_eq_mul,
        Nat.cast_mul]
      have h0 : 0 ≤ ((q + D).choose D : ℝ) * R * M' := by positivity
      have key : ((δ : ℝ) + 1) * M' * ((q + D).choose D : ℝ) * R =
          (δ : ℝ) * ((q + D).choose D : ℝ) * (R * M') + ((q + D).choose D : ℝ) * R * M' := by ring
      rw [key]
      linarith
    rw [← hcnt, hfinS.cast_ncard_eq, ← hinj.encard_image]
    exact Set.encard_le_encard hmaps.image_subset

end GlobalTheory.HSAmp.FLower
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.GeoInt

open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem mem_span_pow_lin {ι : Type} [Fintype ι] (d : ℕ) (F : MvPolynomial ι ℝ) (hF : F.IsHomogeneous d) :
    F ∈ Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := by
  by_contra hnot
  obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ n : ι → ℤ, φ (lin (fun i => (n i : ℝ)) ^ d) = 0 := by
    intro n
    have hm : lin (fun i => (n i : ℝ)) ^ d ∈ Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := Submodule.subset_span ⟨n, rfl⟩
    have h2 : φ (lin (fun i => (n i : ℝ)) ^ d) ∈ (Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)).map φ := Submodule.mem_map_of_mem hm
    rw [hφ] at h2
    exact (Submodule.mem_bot ℝ).mp h2
  have hP : PowLinSpan.polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ d)
      (fun _ => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ d x)
    · intro v hv
      have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
        intro i
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
        exact ⟨k, hk⟩
      choose k hk using hv'
      rw [PowLinSpan.eval_polOf]
      have h := hkill (fun i => (k i : ℤ))
      have he : (∑ x, C (v x) * X x : MvPolynomial ι ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
        simp only [lin, Int.cast_natCast, hk]
      rw [he]
      exact h
  exact hφF (PowLinSpan.homog_kill φ d hP F hF)

section Linear

variable {M : Type} [TopologicalSpace M] {m : ℕ} (A : HolAtlas M m) {ι : Type} (w : ι → A.Pt → Ev m)

theorem evalF_add (G₁ G₂ : MvPolynomial ι ℝ) : evalF A w (G₁ + G₂) = evalF A w G₁ + evalF A w G₂ := by
  funext x
  simp [evalF, fld]

theorem evalF_smul (t : ℝ) (G : MvPolynomial ι ℝ) : evalF A w (t • G) = (t : ℂ) • evalF A w G := by
  funext x
  simp [evalF, fld, Algebra.smul_def]

end Linear

end GlobalTheory.LineForm.GeoInt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CuspDim.IsoPow

variable {Z : Scheme.{0}} {B : LB Z}

theorem res_res {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Z, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  change (Z.presheaf.map (homOfLE h).op ≫ Z.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

theorem pow_le (n : ℕ) (j : PUnit → B.ι) : (lbPow B n).U j ≤ B.U (j PUnit.unit) :=
  LB.wchart_le B (fun _ => 𝟙 Z) j PUnit.unit

theorem res_pow_g (n : ℕ) (j j' : PUnit → B.ι) {W : Z.Opens} (h : W ≤ (lbPow B n).U j ⊓ (lbPow B n).U j') :
    res h ((lbPow B n).g j j') =
      res (h.trans (inf_le_inf (pow_le n j) (pow_le n j'))) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
  have e : (lbPow B n).g j j' =
      res (inf_le_inf (pow_le n j) (pow_le n j')) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) :=
    Fintype.prod_unique fun a : PUnit.{1} => res (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => 𝟙 Z) j a))
      (inf_le_right.trans (LB.wchart_le B (fun _ => 𝟙 Z) j' a))) (pullU (𝟙 Z) _ (B.g (j a) (j' a))) ^ (n : ℤ)
  rw [e, zpow_natCast, map_pow, res_res]



theorem ev_res_pow {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} {U W : Z.Opens} {y : CxPts q σ} (h : W ≤ U)
    (hy : y ∈ ptsIn q σ W) (u : Γ(Z, U)ˣ) (n : ℕ) :
    ev q σ W (res h u ^ n).val y = ev q σ U u.val y ^ (n : ℤ) := by
  rw [zpow_natCast, ← ev_res h hy, ev_eq hy, ev_eq hy, Units.val_pow_eq_pow_val, map_pow]
  rfl

end GlobalTheory.CuspDim.IsoPow
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem exists_ccIs_equivAt_serOf_oneMapRow_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) (u • cc) 1 := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hI i Tp tup O hP
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.exists_frameConstants_of_characterisationCore hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := GlobalTheory.T.exists_adelicLift_eq_geometric_classSum_all_tuples hC D G Pl0 T0 A T R F κ v₀ hR hT hI i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu, GlobalTheory.T.levelAction_equivariant_at_frameConstants_of_clauses hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP cc hcc u, hS,
    GlobalTheory.AdTh.oneMapRow_of_serOf_core D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP (u • cc) hS
      (GlobalTheory.T.exists_cuspForm_classSum_normalisedData hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.AdTh
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ≃ Σ k₂ : {k₂ // π k₂ = k}, ↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
  first | exact @GlobalTheory.LevModel.frLifts_equiv_cosets | exact GlobalTheory.LevModel.frLifts_equiv_cosets | (intros; apply GlobalTheory.LevModel.frLifts_equiv_cosets <;> assumption)
end
