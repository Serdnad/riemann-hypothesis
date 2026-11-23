module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle144
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawLocal

theorem dense_affine {S X : Scheme.{0}} (f : X ⟶ S) (N : LB X) {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion j]
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K),
      p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen}) :
    Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ pullback f j) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' (pullback.snd f j) (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((N.pull (pullback.fst f j)).pull π)} := by
  refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
  rintro q ⟨K, hK, x, Y, ρ, h, ⟨z, hz⟩, hpb, c, hc⟩
  have hsub : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ⟨q, by rw [Subsingleton.elim w z]; exact hz.symm⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), x' ≫ j = x :=
    ⟨IsOpenImmersion.lift j x hr, IsOpenImmersion.lift_fac j x hr⟩
  have hmap : Spec.map (CommRingCat.ofHom (Spec.preimage x').hom) = x' := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨K, hK, (Spec.preimage x').hom, Y,
    pullback.lift ρ (h ≫ x') (by rw [hpb.w, Category.assoc, hx']), h, ?_, ?_, ?_⟩
  · have h1 : j (x' z) = j q := by rw [← hz, ← hx']; rfl
    have h2 : x' z = q := j.isOpenEmbedding.injective h1
    have h3 : Spec.map (Spec.preimage x') z = q := by rw [Spec.map_preimage]; exact h2
    rw [← h3]
    change RingHom.ker (Spec.preimage x').hom =
      Ideal.comap (Spec.preimage x').hom (z : PrimeSpectrum K).asIdeal
    rw [@Ideal.eq_bot_of_prime K _ (z : PrimeSpectrum K).asIdeal (z : PrimeSpectrum K).isPrime]
    exact RingHom.ker_eq_comap_bot _
  · rw [hmap]
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
    rw [pullback.lift_fst, hx']
    exact hpb
  · apply CubeOpen.triv_pull_pull
    rw [pullback.lift_fst]
    exact ⟨c, hc⟩

theorem triv_locally_of_dense : ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ c : (N.pull (f ⁻¹ᵁ U).ι).Gen, c.IsGen := by
  intro S₀ B _ M hA hM hRel S X _ t π f N hpb hN hd s
  obtain ⟨R, j, hj, ⟨pt, hpt⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := s) (U := ⊤) trivial
  have hRed : _root_.IsReduced R := by
    have := isReduced_of_isOpenImmersion j
    exact (affine_isReduced_iff R).mp inferInstance
  have hsq : IsPullback (pullback.fst f j ≫ π) (pullback.snd f j) B.hom (j ≫ t) :=
    (IsPullback.of_hasPullback f j).paste_horiz hpb
  obtain ⟨hP, hSm, hPr, hGI⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral
    S₀ B M hA hM hRel R (j ≫ t) _ _ _ hsq
  obtain ⟨r, hr, H⟩ := SeesawReduced.triv_locally_of_dense R (pullback f j) (pullback.snd f j)
    (N.pull (pullback.fst f j)) (pull_isLB hN _) hSm hPr hGI hP (dense_affine f N j hd) pt
  set p : PrimeSpectrum R := pt with hp
  have h0 : p ∈ PrimeSpectrum.basicOpen r := hr
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at h0
  obtain ⟨w, hw⟩ := h0
  obtain ⟨j', hj'⟩ : ∃ j' : Spec (CommRingCat.of (Localization.Away r)) ⟶ S,
      j' = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j := ⟨_, rfl⟩
  have hjo : IsOpenImmersion j' := by rw [hj']; infer_instance
  refine ⟨j'.opensRange, ?_, ?_⟩
  · show s ∈ Set.range j'
    refine ⟨w, ?_⟩
    rw [hj']
    change j ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) w) = s
    rw [← hpt]
    exact congrArg j hw
  · have hU : IsPullback (f ⁻¹ᵁ j'.opensRange).ι (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        f j' := by
      have hb : IsPullback j'.opensRange.ι j'.isoOpensRange.inv (𝟙 S) j' :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      simpa using (isPullback_morphismRestrict f j'.opensRange).flip.paste_vert hb
    obtain ⟨π₀, h₁, h₂⟩ : ∃ π₀ : (f ⁻¹ᵁ j'.opensRange).toScheme ⟶ pullback f j,
        π₀ ≫ pullback.fst f j = (f ⁻¹ᵁ j'.opensRange).ι ∧
        π₀ ≫ pullback.snd f j = (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) :=
      ⟨pullback.lift _ _ (by rw [hU.w]; simp only [Category.assoc]; rw [← hj']), pullback.lift_fst _ _ _,
        pullback.lift_snd _ _ _⟩
    have hsq' : IsPullback π₀ (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        (pullback.snd f j) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
      refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f j)
      rw [h₁, ← hj']
      exact hU
    obtain ⟨c, hc⟩ := H (Localization.Away r) (algebraMap R (Localization.Away r)) _ π₀ _ hsq'
      (IsLocalization.Away.algebraMap_isUnit r)
    obtain ⟨d, hd'⟩ := GlobalTheory.exists_isGen_linComb_of_pull N _ _ π₀ c hc
    exact CubeOpen.triv_comp (f := π₀ ≫ pullback.fst f j) (𝟙 _) (by rw [Category.id_comp, h₁]) ⟨d, hd'⟩

end GlobalTheory.SeesawLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.exists_completeDVR_point_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  first | exact @GlobalTheory.GenTrait.exists_trait_genericPoint | exact GlobalTheory.GenTrait.exists_trait_genericPoint | (intros; apply GlobalTheory.GenTrait.exists_trait_genericPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PosDefAmple

open GlobalTheory.CechPic

theorem exists_smul_eq_transpose_mul_self {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℤ)
    (hQ : (Q.map (Int.cast : ℤ → ℝ)).PosDef) :
    ∃ (N m : ℕ) (d : ℤ) (c : Matrix (Fin m) (Fin n) ℤ) (b : Matrix (Fin n) (Fin m) ℤ), 0 < N ∧ d ≠ 0 ∧
      (N : ℤ) • Q = c.transpose * c ∧ b * c = d • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  obtain ⟨N, a, l, hN, ha, hl, h⟩ := exists_smul_eq_transpose_mul_diagonal_mul n Q hQ
  let e := Fintype.equivFin (Σ i, Fin (a i))
  let c : Matrix (Fin (Fintype.card (Σ i, Fin (a i)))) (Fin n) ℤ := fun j => l (e.symm j).1
  have hc : c.transpose * c = l.transpose * Matrix.diagonal (fun i => (a i : ℤ)) * l := by
    ext u v
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine ((e.symm.sum_comp (fun p => l p.1 u * l p.1 v)).trans (Fintype.sum_sigma _)).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    simp [Matrix.mul_diagonal]
    ring
  refine ⟨N, _, (c.transpose * c).det, c, (c.transpose * c).adjugate * c.transpose, hN, ?_, h.trans hc.symm, ?_⟩
  · rw [hc, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (ha i).ne')) hl
  · rw [Matrix.mul_assoc, Matrix.adjugate_mul]

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isAffineHom {G G' : Over S} [IsProper G.hom] (φ : G ⟶ G') [IsAffineHom φ.left]
    {L : LB G'.left} (hL : L.IsLB) (h : Out.RelAmple G' L) : Out.RelAmple G (L.pull φ.left) := by
  refine relAmple_of_isAmpleLB G (pull_isLB hL _) fun U hU => ?_
  have e : G.hom ⁻¹ᵁ U = φ.left ⁻¹ᵁ (G'.hom ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, Over.w φ]
  rw [e]
  have : IsAffineHom (φ.left ∣_ (G'.hom ⁻¹ᵁ U)) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict φ.left (G'.hom ⁻¹ᵁ U)).flip inferInstance
  have h₁ := (isAmpleLB_of_relAmple G' hL h U hU).pull_of_isAffineHom (φ.left ∣_ (G'.hom ⁻¹ᵁ U))
  have h₂ := pull_isLB (pull_isLB hL φ.left) (φ.left ⁻¹ᵁ (G'.hom ⁻¹ᵁ U)).ι
  refine h₁.of_lbIso h₂ ((cls_eq_iff h₂ h₁.isLB).1 ?_)
  rw [cls_pull (pull_isLB hL _), cls_pull hL, cls_pull (pull_isLB hL _), cls_pull hL, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_nsmul {G : Over S} [IsProper G.hom] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB) {N : ℕ}
    (hN : 1 ≤ N) (e : N • cls L hL = cls M hM) (h : Out.RelAmple G M) : Out.RelAmple G L := by
  refine relAmple_of_isAmpleLB G hL fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple G hM h U hU
  have h₂ := pull_isLB hL (G.hom ⁻¹ᵁ U).ι
  refine (isAmpleLB_pow_iff h₂ hN).1 (h₁.of_lbIso (isLB_lbPow h₂ N) ((cls_eq_iff (isLB_lbPow h₂ N) h₁.isLB).1 ?_))
  rw [cls_lbPow h₂, cls_pull hL, cls_pull hM, ← e, map_nsmul]

theorem isProper_powObj (A : Over S) [IsProper A.hom] : ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => by
    have := isProper_powObj A n
    exact inferInstanceAs (IsProper (pullback.fst A.hom (Out.powObj A n).hom ≫ A.hom))

theorem comp_prod_zpow {T T' A : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A))
    (c : Fin n → ℤ) : f ≫ (∏ i, x i ^ c i) = ∏ i, (f ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun y => f ≫ y) (comp_mul f)
  change F _ = ∏ i, F (x i) ^ c i
  simp only [map_prod, map_zpow]

theorem cls_form_eq_sum (hG : Out.GlobalFnsSt) {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h k ζ s) (hA : Out.RelAmple o.A o.diag) {T : Over S} {n m : ℕ} (x : Fin n → (T ⟶ o.A))
    (W : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (hW : W + W.transpose = (2 : ℤ) • (c.transpose * c)) :
    ∑ uv : Fin n × Fin n, W uv.1 uv.2 • pull (lift (x uv.1) (x uv.2)).left (cls o.P o.isLB) =
      ∑ j, pull (∏ i, x i ^ c j i).left (cls o.diag (pull_isLB o.isLB _)) := by
  have H := (cls_eq_iff (LB.isLB_linComb o.isLB _ _) (LB.isLB_linComb o.isLB _ _)).2
    (GlobalTheory.BilinCalc.main S o.A o.P o.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A o.diag o.ab (pull_isLB o.isLB _) hA o.P o.isLB o.rig₁ o.rig₂) o.symm T n m x 1 W c
      (by rw [hW, Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, two_smul]))
  rw [cls_linComb o.isLB, cls_linComb o.isLB] at H
  rw [H, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zero_smul]) (by simp),
    Matrix.one_apply_eq, one_smul]
  refine Eq.trans ?_ (pull_comp (∏ i, x i ^ c j i).left (lift (𝟙 o.A) (𝟙 o.A)).left (cls o.P o.isLB))
  rw [← Over.comp_left, comp_lift, Category.comp_id]

theorem pull_cls_boxLB {T G A : Over S} {n : ℕ} (pr : Fin n → (G ⟶ A)) {L : LB A.left} (hL : L.IsLB) (φ : T ⟶ G) :
    pull φ.left (cls (Out.boxLB L pr) (LB.isLB_linComb hL _ _)) = ∑ j, pull (φ ≫ pr j).left (cls L hL) := by
  refine (congrArg _ (cls_linComb hL _ _ _)).trans ?_

  simp only [map_sum, one_smul, ← pull_comp, Over.comp_left]

theorem relAmple_linComb_of_posDef : Out.GlobalFnsSt → ∀ (h k n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h k ζ s) (G : Over S) [GrpObj G] (pr : Fin n → (G ⟶ c.A)) (W : Matrix (Fin n) (Fin n) ℤ), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin n → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → Out.RelAmple c.A c.diag → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Out.RelAmple G (LB.LinComb c.P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro hG h k n B _ ζ S s o G _ pr W hpr up hA hW
  have := o.ab.proper
  have hD : o.diag.IsLB := pull_isLB o.isLB _
  let p : Out.IsPowGrp G o.A n := ⟨pr, hpr, mkFanLimit _ (fun t => (up t.pt t.proj).choose)
    (fun t j => (up t.pt t.proj).choose_spec.1 j) (fun t y hy => (up t.pt t.proj).choose_spec.2 y hy)⟩
  have hp : IsProper G.hom := by
    have := isProper_powObj o.A n
    let e : G ≅ Out.powObj o.A n := p.lim.conePointUniqueUpToIso (Out.powIsLimit o.A n)
    have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨N, m, d, c, b, hN, hd, hc, hb⟩ := exists_smul_eq_transpose_mul_self _ hW
  have := isProper_powObj o.A m
  let φ : G ⟶ Out.powObj o.A m := (Out.powIsLimit o.A m).lift (Fan.mk G fun j => ∏ i, pr i ^ c j i)
  have hφ : ∀ j, φ ≫ Out.powPr o.A j = ∏ i, pr i ^ c j i := fun j => (Out.powIsLimit o.A m).fac _ ⟨j⟩
  obtain ⟨ψ, hψ, -⟩ := up (Out.powObj o.A m) fun i => ∏ j, Out.powPr o.A j ^ b i j
  have hμ : ∀ u, (φ ≫ ψ) ≫ pr u = ∏ i, pr i ^ (d • (1 : Matrix (Fin n) (Fin n) ℤ)) u i := fun u => by
    rw [Category.assoc, hψ, comp_prod_zpow, ← hb]
    simp only [hφ, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [mul_comm (c _ i)]
    exact (map_prod (zpowersHom _ (pr i)) (fun j => Multiplicative.ofAdd (b u j * c j i)) Finset.univ).symm
  have hE : (Out.boxLB o.diag pr).IsLB := LB.isLB_linComb hD _ _
  have hfin : IsFinite (φ ≫ ψ).left := by
    obtain ⟨α, hα⟩ := (cls_eq_zero_iff (LB.isLB_linComb hE (K := Fin 2) ![𝟙 G.left, (φ ≫ ψ).left]
      ![((d.natAbs ^ 2 : ℕ) : ℤ), -1])).1 (by
        have e₁ := cls_form_eq_sum hG o hA pr ((d * d) • (1 : Matrix (Fin n) (Fin n) ℤ)) (d • 1) (by
          rw [Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
            smul_smul d, two_smul])
        have e₂ := cls_form_eq_sum hG o hA pr 1 1 (by rw [Matrix.transpose_one, Matrix.one_mul, two_smul])
        have e₃ : ∀ j, ∏ i, pr i ^ (1 : Matrix (Fin n) (Fin n) ℤ) j i = 𝟙 G ≫ pr j := fun j => by
          rw [Finset.prod_eq_single j (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zpow_zero]) (by simp),
            Matrix.one_apply_eq, zpow_one, Category.id_comp]
        simp only [← hμ] at e₁
        simp only [e₃] at e₂
        rw [← pull_cls_boxLB pr hD] at e₁ e₂
        rw [cls_linComb hE, Fin.sum_univ_two]
        change _ • pull (𝟙 G : G ⟶ G).left _ + (-1 : ℤ) • pull (φ ≫ ψ).left _ = 0
        rw [← e₁, ← e₂]
        simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.cons_val_zero]
        rw [Nat.cast_pow, Int.natAbs_sq, pow_two, mul_smul, neg_one_smul, add_neg_cancel])
    exact MulFinite.isFinite_of_relAmple G _ hE (relAmple_boxLB S G o.A n p _ hD hA) (φ ≫ ψ) _
      (pow_ne_zero _ (Int.natAbs_ne_zero.2 hd)) α hα
  have : IsSeparated (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsSeparated ψ.left := .of_comp _ G.hom
  have : IsAffineHom (φ.left ≫ ψ.left) := inferInstanceAs (IsAffineHom (φ ≫ ψ).left)
  have : IsAffineHom φ.left := .of_comp _ ψ.left
  have hF : (Out.boxLB o.diag (Out.powPr o.A (n := m))).IsLB := LB.isLB_linComb hD _ _
  refine relAmple_of_nsmul (LB.isLB_linComb o.isLB _ _) (pull_isLB hF φ.left) (N := 2 * N) (by omega) ?_
    (relAmple_pull_of_isAffineHom φ hF (relAmple_boxLB S _ o.A m (Out.powIsPowGrp o.A m) _ hD hA))
  have e := cls_form_eq_sum hG o hA pr (((2 * N : ℕ) : ℤ) • W) c (by
    rw [← hc, Matrix.transpose_smul, ← smul_add, smul_smul, Nat.cast_mul, Nat.cast_ofNat])
  simp only [← hφ] at e
  rw [cls_pull hF, pull_cls_boxLB _ hD, ← e, cls_linComb o.isLB, Finset.smul_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, natCast_zsmul]

end GlobalTheory.PosDefAmple
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.isQProjOver_of_isCompl_openImmersions : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ → IsCompl (Set.range f₁) (Set.range f₂) → IsQProjOver (f₁ ≫ s) → IsQProjOver (f₂ ≫ s) → IsQProjOver s := by
  first | exact @GlobalTheory.ProjSpace.isQProjOver_of_isCompl | exact GlobalTheory.ProjSpace.isQProjOver_of_isCompl | (intros; apply GlobalTheory.ProjSpace.isQProjOver_of_isCompl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.lbIso_linComb_lam_of_appellHumbert | exact GlobalTheory.lbIso_linComb_lam_of_appellHumbert | (intros; apply GlobalTheory.lbIso_linComb_lam_of_appellHumbert <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  first | exact @GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | exact GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | (intros; apply GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  first | exact @GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | exact GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | (intros; apply GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.biadditive_of_trivial_on_axes : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  first | exact @GlobalTheory.Biadditive.biadditive_of_triv_axes | exact GlobalTheory.Biadditive.biadditive_of_triv_axes | (intros; apply GlobalTheory.Biadditive.biadditive_of_triv_axes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem cube_of_exists_relAmple {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀)
    {M : LB B.left} (hM : M.IsLB) : ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have hG := GlobalTheory.laws_without_cohomology.1
  exact GlobalTheory.Biadditive.triv_of_faces hG hB hH hamp hM (thφ B (x3 B)) thε
    (fun r i b h => GlobalTheory.AbLaw.CubeGen.trivAt_of_formal hM r (GlobalTheory.AbLaw.CubeGen.prod_face r i b h))
    (fun r b h U _ k => GlobalTheory.AbLaw.CubeGen.prod_face r 0 b h U k)

theorem cube_of_relAmple :
    ∀ (S : Scheme.{0}) [IsReduced S] (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ t : LB.Gen (Theta B M), t.IsGen := fun _ _ _ _ _ _ hB hM hamp => cube_of_exists_relAmple hB hM hamp hM

end GlobalTheory.HkFam
end
