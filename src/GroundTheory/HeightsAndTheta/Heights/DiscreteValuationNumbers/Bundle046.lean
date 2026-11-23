module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ hvert _ hH]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem le_of_mem_ratCyc_support {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    (hW : W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support) : P ≤ W := by
  have key : ∀ s, ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0 → P ≤ W := by
    intro s hs
    by_contra hPW
    apply hs
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    exact hPW (le_trans le_sup_left hmin.1.2)
  rw [Finsupp.mem_support_iff] at hW
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0
  · by_cases hg : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W = 0
    · simp [hf, hg] at hW
    · exact key g hg
  · exact key f hf

theorem FullFlagVerticalSymmetric.proof (hFib : VerticalDivisorFibreVariety.Statement)
    (hRes : FullFlagRestriction.Statement)
    (hSeg : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
      (ι : K → Type) [∀ k, Fintype (ι k)], IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι) :
    FullFlagVerticalSymmetric.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B hM fl₁ fl₂ I hI G hG n Y R b f g hD
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  congr 1
  have hV := hFib O K ι _ d hM b f g hD W hW
  have : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).IsPrime := hV.1.1
  obtain ⟨hmc, B', -, hfl⟩ := hRes O Ω K ι x d N V B hM (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) hV.1
    (Ideal.map_mono (le_of_mem_ratCyc_support hW))
  obtain ⟨fl₁', h₁, -⟩ := hfl fl₁
  obtain ⟨fl₂', h₂, -⟩ := hfl fl₂
  have hV' : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W))) d := by
    rw [hmc]
    exact hV
  have := SegreFlagIndep.segreFlagIndep_homogeneous_implies_general _ _ ι (hSeg (IsLocalRing.ResidueField O) _ K ι)
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W)) d hV' N _ B' fl₁' fl₂' I hI G hG n Y R
  rw [hmc, h₁, h₂] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinDivCycle

variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinIdxEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

def joinPolyEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+* Polynomial (MRing ι R) :=
  ((renameEquiv R (joinIdxEquiv (ι := ι))).trans (optionEquivLeft R (Σ k, ι k))).toRingEquiv

theorem joinPolyEquiv_comp_rename :
    (joinPolyEquiv (R := R) (ι := ι)).toRingHom.comp (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [joinPolyEquiv, optionEquivLeft_C]
  · intro p
    simp [joinPolyEquiv, joinIdxEquiv, liftVar, optionEquivLeft_X_some]

theorem rename_eq_symm_comp_C :
    (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      (joinPolyEquiv (R := R) (ι := ι)).symm.toRingHom.comp Polynomial.C := by
  rw [← joinPolyEquiv_comp_rename, ← RingHom.comp_assoc]
  ext x <;> simp

set_option hygiene false in
local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)

set_option hygiene false in
local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)

theorem joinPolyEquiv_rename (x : MRing ι R) : joinPolyEquiv (ε x) = Polynomial.C x :=
  RingHom.congr_fun joinPolyEquiv_comp_rename x

theorem map_rename_eq (I : Ideal (MRing ι R)) :
    I.map ε = (I.map (Polynomial.C : MRing ι R →+* _)).comap (joinPolyEquiv (R := R) (ι := ι)).toRingHom := by
  have h : I.map ε = I.map (ε).toRingHom := rfl
  rw [h, rename_eq_symm_comp_C, ← Ideal.map_map]
  exact Ideal.map_symm _

theorem mem_map_rename_iff (I : Ideal (MRing ι R)) (x) :
    x ∈ I.map ε ↔ joinPolyEquiv x ∈ I.map (Polynomial.C : MRing ι R →+* _) := by
  rw [map_rename_eq]
  rfl

theorem rename_mem_map_rename_iff (I : Ideal (MRing ι R)) (x : MRing ι R) : ε x ∈ I.map ε ↔ x ∈ I := by
  rw [mem_map_rename_iff, joinPolyEquiv_rename, ← Ideal.mem_comap, comap_C_map_C_polynomial]

theorem comap_map_rename (I : Ideal (MRing ι R)) : (I.map ε).comap ε = I := by
  ext x
  exact rename_mem_map_rename_iff I x

theorem isPrime_map_rename (Q : Ideal (MRing ι R)) [Q.IsPrime] : (Q.map ε).IsPrime := by
  rw [map_rename_eq]
  infer_instance

theorem mem_minimalPrimes_map_rename_iff (J : Ideal (MRing ι R))
    (W : Ideal (MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R)) :
    W ∈ (J.map ε).minimalPrimes ↔ ∃ Q ∈ J.minimalPrimes, Q.map ε = W := by
  constructor
  · intro hW
    have : W.IsPrime := hW.1.1
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hW.1.2)
    have : Q.IsPrime := hQ.1.1
    have hle : Q.map ε ≤ W := Ideal.map_le_iff_le_comap.mpr hQle
    exact ⟨Q, hQ, le_antisymm hle (hW.2 ⟨isPrime_map_rename Q, Ideal.map_mono hQ.1.2⟩ hle)⟩
  · rintro ⟨Q, hQ, rfl⟩
    have : Q.IsPrime := hQ.1.1
    refine ⟨⟨isPrime_map_rename Q, Ideal.map_mono hQ.1.2⟩, fun W hW hWle => ?_⟩
    have : W.IsPrime := hW.1
    have h1 : W.comap ε ≤ Q := (Ideal.comap_mono hWle).trans (comap_map_rename Q).le
    exact Ideal.map_le_iff_le_comap.mpr (hQ.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hW.2⟩ h1)

theorem isRelevant_map_rename_iff (Q : Ideal (MRing ι R)) (hQ : Q ≠ ⊤) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (Q.map ε) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h (.inl k)
    refine ⟨i, fun hx => hi ?_⟩
    have hX : (X ⟨.inl k, i⟩ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) = ε (X ⟨k, i⟩) := by
      simp [liftVar]
    rw [hX]
    exact Ideal.mem_map_of_mem _ hx
  · intro h k
    rcases k with k | u
    · obtain ⟨i, hi⟩ := h k
      refine ⟨i, fun hx => hi ?_⟩
      rw [← rename_mem_map_rename_iff Q]
      simpa [liftVar] using hx
    · refine ⟨(0 : Fin 1), fun hx => hQ ?_⟩
      rw [mem_map_rename_iff] at hx
      have hX : joinPolyEquiv (R := R) (ι := ι)
          (X ⟨.inr u, (0 : Fin 1)⟩ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) = Polynomial.X := by
        cases u
        simp [joinPolyEquiv, joinIdxEquiv, optionEquivLeft_X_none]
      rw [hX, Ideal.mem_map_C_iff] at hx
      have h1 := hx 1
      rw [Polynomial.coeff_X_one] at h1
      exact (Ideal.eq_top_iff_one Q).mpr h1

theorem multAt_map_rename (P Q : Ideal (MRing ι R)) [Q.IsPrime] (hPQ : P ≤ Q) (f : MRing ι R) :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (P.map ε ⊔ Ideal.span {ε f}) (Q.map ε) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {f}) Q := by
  have hm : ∀ I : Ideal (MRing ι R),
      I.map ε = (I.map (Polynomial.C : MRing ι R →+* _)).map ((ψ).symm : Polynomial (MRing ι R) →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) := by
    intro I
    rw [map_rename_eq]
    exact (Ideal.map_symm (joinPolyEquiv (R := R) (ι := ι))).symm
  have hf : ε f = (ψ).symm (Polynomial.C f) := by
    rw [← joinPolyEquiv_rename, RingEquiv.symm_apply_apply]
  haveI : (Q.map (Polynomial.C : MRing ι R →+* _)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hQp : ((Q.map (Polynomial.C : MRing ι R →+* _)).map ((ψ).symm : Polynomial (MRing ι R) →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R)).IsPrime := by
    rw [← hm]
    exact isPrime_map_rename Q
  haveI := hQp
  have key := GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.length_map (ψ).symm
    (P.map (Polynomial.C : MRing ι R →+* _)) (Q.map (Polynomial.C : MRing ι R →+* _)) (Ideal.map_mono hPQ)
    (Polynomial.C f)
  have hsup : P.map (Polynomial.C : MRing ι R →+* _) ⊔ Ideal.span {Polynomial.C f} =
      (P ⊔ Ideal.span {f}).map (Polynomial.C : MRing ι R →+* _) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hsup, PolynomialLocalizedLength.full (MRing ι R) Q (P ⊔ Ideal.span {f})] at key
  rw [hm P, hm Q, hf]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt
  rw [dite_eq_left hQp, dite_eq_left ‹Q.IsPrime›]
  exact congrArg ENat.toNat key

end JoinDivCycle


open JoinDivCycle in
theorem JoinDivCycle.proof : JoinDivCycle.Statement := by
  intro R _ _ K _ ι _ P f
  classical
  have hinj : Function.Injective (Ideal.map (rename (R := R) (liftVar (ι := ι) ptIdx))) := fun I I' h => by
    rw [← comap_map_rename I, ← comap_map_rename I']
    exact congrArg (Ideal.comap (rename (R := R) (liftVar (ι := ι) ptIdx))) h
  have hsup : P.map (rename (R := R) (liftVar (ι := ι) ptIdx)) ⊔
      Ideal.span {rename (R := R) (liftVar (ι := ι) ptIdx) f} =
      (P ⊔ Ideal.span {f}).map (rename (R := R) (liftVar (ι := ι) ptIdx)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hsupp : ∀ Q, Q.map (rename (R := R) (liftVar (ι := ι) ptIdx)) ∈
      ReciprocityTheory.ChartRestriction.G.Geo.divSupp (P.map (rename (R := R) (liftVar (ι := ι) ptIdx)))
        (rename (R := R) (liftVar (ι := ι) ptIdx) f) ↔ Q ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P f := by
    intro Q
    show (_ ∈ _ ∧ _) ↔ (_ ∈ _ ∧ _)
    rw [hsup, mem_minimalPrimes_map_rename_iff]
    constructor
    · rintro ⟨⟨Q₀, hQ₀, h⟩, hr⟩
      obtain rfl := hinj h
      exact ⟨hQ₀, (isRelevant_map_rename_iff Q₀ hQ₀.1.1.ne_top).1 hr⟩
    · rintro ⟨hQ, hr⟩
      exact ⟨⟨Q, hQ, rfl⟩, (isRelevant_map_rename_iff Q hQ.1.1.ne_top).2 hr⟩
  ext W
  by_cases hW : ∃ Q : Ideal (MRing ι R), Q.map (rename (R := R) (liftVar (ι := ι) ptIdx)) = W
  · obtain ⟨Q, rfl⟩ := hW
    rw [Finsupp.mapDomain_apply_of_injective hinj]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    by_cases hQ : Q ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P f
    · haveI : Q.IsPrime := hQ.1.1.1
      rw [if_pos ((hsupp Q).2 hQ), if_pos hQ,
        multAt_map_rename P Q (le_sup_left.trans hQ.1.1.2) f]
    · rw [if_neg (fun h => hQ ((hsupp Q).1 h)), if_neg hQ]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨Q, hQ⟩; exact hW ⟨Q, hQ⟩)]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    rw [hsup, mem_minimalPrimes_map_rename_iff] at hmin
    obtain ⟨Q, -, hQ⟩ := hmin
    exact hW ⟨Q, hQ⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def flagProjPt {K' : Type*} (j : K' ↪ Option (Option K)) (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (k : ℕ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' (j o)) → Φ :=
  fun p => flagClosurePt y w e φ φ' t k (FieldNumbers.blockIncl j (bundleIdx (bundleIdx ι M) M') p)

end Objects

theorem comap_pointIdeal_blockIncl {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K K' : Type*}
    (j : K ↪ K') {ι' : K' → Type*} (pt : (Σ k', ι' k') → Φ) :
    (pointIdeal R pt).comap (rename (FieldNumbers.blockIncl j ι')) =
      pointIdeal R (fun p => pt (FieldNumbers.blockIncl j ι' p)) := by
  have key : ((pointConeMap R pt).comp (rename (FieldNumbers.blockIncl j ι'))) =
      ((rename j).restrictScalars R).comp (pointConeMap R (fun p => pt (FieldNumbers.blockIncl j ι' p))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, FieldNumbers.blockIncl]
  ext f
  simp only [pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ j.injective)

def SegreFlagCutLiesOver.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')))) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M'))))

def SegreFlagProjSpecialDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ)) ∧
        FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
