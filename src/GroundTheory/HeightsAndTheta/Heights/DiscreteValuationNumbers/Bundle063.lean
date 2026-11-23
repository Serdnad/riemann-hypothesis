module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle017
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle052
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle057
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureModel

theorem exists_flag_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by
  have hN : 0 < N := by omega
  by_contra! h0

  let θ : Fin P → Module.Dual Ω E := fun l =>
    ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j
  have hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j := by
    intro l i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : ∀ l, θ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by
      rw [← h0 l]

      simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0 := by
    intro l
    have h := congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj])
      (by simp)] at h
    simpa [show (0 : ℕ) < k by omega] using h
  have hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hw0 l
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)
  simp at this

end SegreFlagClosureModel


open GenericProjClosureDim GenericProjClosureDivisor SegreFlagClosureModel in
theorem SegreFlagClosureModel.proof (hTr : SegreFlagClosureTrdeg.Statement) :
    SegreFlagClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  have hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k) := rfl

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k')
    · exact exists_flag_ne_zero w e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN
    · exact exists_flag_ne_zero w e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN
    · exact ⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ)
        (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy

  have hdy := DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  have hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) := by
    refine ⟨hP, hnt, ?_⟩
    rw [DvrConeDimTrdeg.proof _ _ _ _ hP hnt,
      hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty,
      ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
      show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (k + 1) + 1 by omega]
    norm_cast
  refine ⟨hZ, ?_⟩

  rw [hpt] at hZ ⊢
  have hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP' le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace PairNumberRelabelAlt

theorem mcIdeal_map_rename {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (y ∘ σ)).map (rename σ) = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y :=
  pointIdeal_map_rename e σ hσ y

theorem mem_ratios {Ω₁ : Type*} [Field Ω₁] {K₀ : Type} {κ : K₀ → Type} (y : (Σ k, κ k) → Ω₁) (z : Ω₁) :
    z ∈ Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ↔
      ∃ a b : Σ k, κ k, a.1 = b.1 ∧ y a / y b = z := by
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨k, i⟩, ⟨k, j⟩, rfl, rfl⟩
  · rintro ⟨⟨k, i⟩, ⟨k', j⟩, h, rfl⟩
    dsimp only at h
    subst h
    exact ⟨⟨k, i, j⟩, rfl⟩

theorem fnField_comp {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} (O : Type) [CommRing O] {Ω : Type}
    [Field Ω] [Algebra O Ω] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Ω) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (y ∘ σ) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 1
  ext z
  simp only [Set.mem_union]
  refine or_congr_right ?_
  rw [mem_ratios, mem_ratios]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨σ.symm a, σ.symm b, ?_, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩
    apply e.injective
    rw [← hσ, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨σ a, σ b, by rw [hσ, hσ, hab], rfl⟩

theorem pairNum_eq_intNum (hF : VerticalComponentFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : IFamily (IsLocalRing.ResidueField O) ι) (hI : IsFieldIntersection I)
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d)
    {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P (y l - y' l) (f l) (g l))
    (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hM := ((BundleExamples.isModelOver_iff O P d).1 hP).2
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv := (VerticalDivisorCharacterisation.proof O K ι P ϖ (y l - y' l) (f l) (g l) hϖ hM.multiProj).1 (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hvar : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW0
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hvar
  · rfl

end PairNumberRelabelAlt


open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal) in
theorem PairNumberRelabelAlt.proof (hF : VerticalComponentFibre.Statement) : PairNumberRelabelAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K₁ _ ι₁ _ K₂ _ ι₂ _ e σ hσ y d hM
  have hmap := PairNumberRelabelAlt.mcIdeal_map_rename O e σ hσ y
  have hM₁ := (BundleExamples.isModelOver_iff O (mcIdeal O (y ∘ σ)) d).1 hM
  have hM₂' : IsModelOver ((mcIdeal O (y ∘ σ)).map (rename σ)) d := by
    rw [PairNumberRelabel.map_rename_eq σ]
    exact PairNumberRelabel.isModelOver_map e σ hσ _ d hM₁.2
  have hM₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d := by
    rw [← hmap]
    exact (BundleExamples.isModelOver_iff O _ d).2 ⟨⟨e hM₁.1.some⟩, hM₂'⟩
  have hvd : ∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
      IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g → IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g) := by
    intro b f g h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h1 := (VerticalDivisorCharacterisation.proof O K₁ ι₁ _ ϖ (b ∘ e) f g hϖ hM₁.2.multiProj).1 h
    have h2 := PairNumberRelabel.isVerticalDivisor_map e σ hσ _ ϖ b f g h1
    rw [← PairNumberRelabel.map_rename_eq σ] at h2
    rw [← hmap]
    exact (VerticalDivisorCharacterisation.proof O K₂ ι₂ _ ϖ b _ _ hϖ hM₂'.multiProj).2 h2
  refine ⟨hM₂, PairNumberRelabelAlt.fnField_comp O e σ hσ y, hvd, ?_⟩
  intro I₁ I hI₁ hI n a a' f g hfg H hH
  have hfg' : ∀ i, IsVertDiv O (mcIdeal O y) (a i - a' i) (rename σ (f i)) (rename σ (g i)) :=
    fun i => hvd (a i - a' i) (f i) (g i) (hfg i)
  rw [PairNumberRelabelAlt.pairNum_eq_intNum hF I₁ hI₁ _ d hM (fun i => a i ∘ e) (fun i => a' i ∘ e) f g hfg H,
    PairNumberRelabelAlt.pairNum_eq_intNum hF I hI _ d hM₂ a a' _ _ hfg' H,
    BundleExamples.pairNum_eq _ d _ _ f g hH, BundleExamples.pairNum_eq _ d a a' _ _ hH, ← hmap,
    PairNumberRelabel.map_rename_eq σ, PairNumberRelabel.pairNum_map e σ hσ _ a a' f g]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPlainValueIndependence

theorem vEval_intNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (d : ℕ) {m : ℕ} (deg : Fin m → K → ℤ)
    (H : MvPolynomial (Fin m) ℤ) (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d deg H) Z =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
        (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          W d deg H) Z := by
  classical
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hV := hZ W (Finsupp.mem_support_iff.mp hW)
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h
  · rw [Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hV]
  · rfl

theorem pairNum_intNum (hSupp : VerticalDivisorSupportFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V}
    (hM : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (r : ℕ) (L : Fin r → K → ℤ)
    (H : MvPolynomial (Fin (N + r)) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                              (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
                              (Fin.append φ.g fun _ => 1) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
        (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
        (Fin.append φ.g fun _ => 1) H := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  induction l using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact vEval_intNum I hI d _ _ _ fun W hW => hSupp O K ι _ d hM _ _ _ (φ.vert i) W hW
  | right j =>
    simp only [Fin.append_right]
    have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 := sub_self _
    exact vEval_intNum I hI d _ _ _ fun W hW => absurd (by rw [h0]; rfl) hW

theorem exists_isFlagPair (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} (hN : 0 < N) {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V} {ϖ : O}
    (hϖ : Irreducible ϖ) (hM : IsModelOver (pointIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E') :
    ∃ w w' : Module.Basis (Fin N) Ω V, IsFlagPair ϖ x E E' w w' φ.deg φ.deg' φ.f φ.g := by
  have hne : ∀ k, ∃ j, x ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hM.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : ∃ c, segreVec x c ≠ 0 := ⟨c, Finset.prod_ne_zero_iff.mpr fun k _ => hc k⟩
  have hiff := hF O Ω K ι x N V E E' ϖ hϖ hM.multiProj
  obtain ⟨hl, hl'⟩ := hiff.2 hyc φ
  have hrank : Fintype.card (Fin N) = Module.finrank Ω V := by
    rw [Fintype.card_fin, ← finrank_top Ω V, ← φ.top, φ.dim]
    rfl
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl hrank,
    basisOfLinearIndependentOfCardEqFinrank hl' hrank, (hiff.1 _ _ _ _ _ _).mpr ⟨φ, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl hrank).symm
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl' hrank).symm

theorem proof (hFlag : FlagIndependence.Statement) (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hSupp : VerticalDivisorSupportFibre.Statement) : FlagPlainValueIndependence.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r L c Q hc hGc hQ
  rw [pairNum_intNum hSupp hM φ₁ I hI r L, pairNum_intNum hSupp hM φ₂ I hI r L,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ]
  refine Finset.sum_congr rfl fun μ hμ => congrArg (Q.coeff μ * ·) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : φ₁.deg = φ₂.deg := Subsingleton.elim _ _
    have h2 : φ₁.deg' = φ₂.deg' := Subsingleton.elim _ _
    have h3 : φ₁.f = φ₂.f := Subsingleton.elim _ _
    have h4 : φ₁.g = φ₂.g := Subsingleton.elim _ _
    rw [h1, h2, h3, h4]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, hM'⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
    have hS' := (BundleExamples.sameGeneric_iff hϖ x E E').mp hS
    obtain ⟨w₁, w₁', h₁⟩ := exists_isFlagPair hF hN hϖ hM' φ₁
    obtain ⟨w₂, w₂', h₂⟩ := exists_isFlagPair hF hN hϖ hM' φ₂
    have hE := dividedDifferenceExpansion.proof N c G hGc
    exact hFlag O ϖ hϖ Ω K ι x d hM' N V E E' hS' w₁ w₁' w₂ w₂' _ _ _ _ _ _ _ _ h₁ h₂ c G hGc hG _ _ hE hE
      (classList L μ) (by rw [classList_length_of_mem_support L hQ hμ]; omega)

end FlagPlainValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorFibreVariety.proof : VerticalDivisorFibreVariety.Statement := by
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  exact VerticalDivisorSupportFibre.proof O K ι P d hP b f g hV W (Finsupp.mem_support_iff.mp hW)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
