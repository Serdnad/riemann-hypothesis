module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle057
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle083
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AmpleForm

theorem relAmple_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  intro K _ _ B _ hB M L hM hL ha hk hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls M hM - cls L hL)
  have hlam0 : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L hL hk O hO hlam0
  have hN : (RigidTranslate.rigTransl L x).IsLB := DVR.linComb_isLB _ hL _ _
  have hA := RigidTranslate.relAmple_rigTransl_point K B hB L hL x ha
  have e1 := PrimitiveOverField.lam_const (cls L hL) x (𝟙 B)
  have e2 : ((toUnit B ≫ x) * 𝟙 B) = PolTranslate.transl x := by
    rw [PolTranslate.transl, _root_.mul_comm]
  have e3 : CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, CechPic.pull_comp, ThetaExtend.pic_local (CechPic.pull x.left (cls L hL)), map_zero]
  have e : cls M hM = cls _ hN := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, e3, neg_zero, add_zero]
    rw [e2, Over.id_left, CechPic.pull_id] at e1
    exact sub_left_inj.1 (eO.symm.trans (hx.trans e1))
  have hN' := pull_isLB hN (𝟙 _)
  have e' : cls M hM = cls _ hN' := by
    rw [CechPic.cls_pull hN, CechPic.pull_id]; exact e
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hM hN').1 e'
  exact relAmple_pull (A' := B) (A := B) (φ := 𝟙 _) (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hA

end GlobalTheory.CompanionTheory.AmpleForm
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.CkRelations

noncomputable def allOne (q : ℕ) : Fin q →₀ ℕ := ∑ j, Finsupp.single j 1

theorem toMultiset_allOne (q : ℕ) : (allOne q).toMultiset = Finset.univ.val := by
  ext j
  simp [allOne, Finsupp.count_toMultiset, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem degree_allOne (q : ℕ) : (allOne q).degree = q := by

  simp [allOne, map_sum]

theorem isHomogeneous_allOne (q n : ℕ) (h : q = n) :
    (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).IsHomogeneous n :=
  isHomogeneous_monomial _ ((degree_allOne q).trans h)

theorem classList_allOne {K : Type} (Q : List (K → ℤ)) :
    (classList Q.get (allOne Q.length)).Perm Q := by
  rw [← Multiset.coe_eq_coe, classList, Multiset.coe_toList, toMultiset_allOne, Fin.univ_val_map,
    List.ofFn_get]

theorem sum_allOne (q : ℕ) (F : (Fin q →₀ ℕ) → ℤ) :
    ∑ μ ∈ (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).support,
      (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).coeff μ * F μ = F (allOne q) := by
  classical
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]

theorem classNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    {Q Q' : List (K → ℤ)} (h : Q.Perm Q') (W : Ideal (MRing ι O)) :
    classNum cls H Q W = classNum cls H Q' W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  simp only [vNumL, vNum, intNum, mixedDiff, List.ofFn_get]
  rw [(h.append_left _).foldr_eq]

theorem key (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (ϖ : O) (hϖ : Irreducible ϖ) (d : ℕ)
    (hM : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V)
    (hE : SameGeneric O x E E') (T : LocPair ι O (Fin N)) (b b' : Module.Basis (Fin N) Ω V)
    (hT : IsFlagPair ϖ x E E' b b' T.x T.x' T.f T.g) (k : ℕ) (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    ck O x d N E E' k Q.get (monomial (allOne Q.length) 1) = T.ck (pointIdeal O x) k Q ∧
    ∀ a : O, a ≠ 0 →
      (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) Q.get (monomial (allOne Q.length) 1) a =
        laNum (pointIdeal O x) a T.x k Q := by
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  obtain ⟨h1, h2⟩ := hC O ϖ hϖ Ω K ι x d hK hW N V E E'
    ((BundleExamples.sameGeneric_iff hϖ x E E').mp hE) b b' T.x T.x' T.f T.g hT
  refine ⟨?_, fun a ha => ?_⟩
  · refine (h1 k hk (by omega) _ (isPairExpansion_psum N k) _ Q.get _
      (isHomogeneous_allOne _ _ (by omega))).trans ?_
    rw [sum_allOne Q.length
      (fun μ => pairNum (pointIdeal O x) T.x T.x' T.f T.g (psumExpansion N k) (classList Q.get μ))]
    simp only [LocPair.ck, pairNum, classNum_perm _ _ (classList_allOne Q)]
  · have h3 := h2 (k - 1) _ (psum_isSymmetric _ _ (k - 1)) (isHomogeneous_psum N (k - 1)) (by omega)
      _ Q.get _ (isHomogeneous_allOne _ _ (by omega)) a ha
    rw [sum_allOne Q.length
      (fun μ => cycEval (fun W => classNum T.x (psum (Fin N) ℤ (k - 1)) (classList Q.get μ) W)
        (divCycle (pointIdeal O x) (C a)))] at h3
    simp only [classNum_perm _ _ (classList_allOne Q)] at h3
    unfold laNum
    exact congrArg _ h3

theorem main_of (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM Sg r s p hp φ VL VO _ _ _ _ Lie W Om OmHT hS hR lie om hF
    k hk Q hQ
  obtain ⟨h, h1, h2⟩ := hR k hk (by omega) Q.length Q.get _
    (isHomogeneous_allOne _ _ (by omega))
  have hL := fun τ => (hF τ).1.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).1 (lie τ) b b' hb' k hk Q hQ
  have hO := fun τ => (hF τ).2.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).2 (om τ) b b' hb' k hk Q hQ
  refine ⟨h, fun τ => ?_, fun τ => ?_⟩
  · rw [← (hL τ).1, ← (hO τ).1, ← (hL τ).2 _ hp, h1 τ]
    push_cast
    ring
  · rw [← (hL (φ τ)).2 _ hp, h2 τ]
    push_cast
    ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om :=
  main_of GlobalTheory.T.chern_class_on_flag_pair

end GlobalTheory.CompanionTheory.CkRelations
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Constants

theorem cycEval_natCast_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Ideal (MRing ι O) → ℤ) (P : Ideal (MRing ι O)) (c : MRing ι O) (n : ℕ) :
    cycEval F (fun W => (n : ℤ) * divCycle P c W) = (n : ℤ) * cycEval F (divCycle P c) := by
  unfold cycEval
  have hfin : (Function.support fun W => divCycle P c W * F W).Finite :=
    (ScalarQuotient.divCycle_support_finite P c).subset fun W hW => by
      rw [Function.mem_support] at hW ⊢
      exact fun h0 => hW (by rw [h0, zero_mul])
  rw [mul_finsum' _ _ hfin]
  exact finsum_congr fun W => by ring

theorem length_classList {K : Type} {q : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ} {e : ℕ}
    (hQ : Q.IsHomogeneous e) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = e := by
  have h := hQ (MvPolynomial.mem_support_iff.mp hμ)
  have h2 : Finsupp.degree μ = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact h
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  simpa [Finsupp.sum, Finsupp.degree_apply] using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bd.Statement.{0,0,0} O Ω ι := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' g hg hmod hlat k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  have hsame : SameGeneric O x E E' := fun s hs =>
    ⟨fun v hv => ⟨_, hg, (hlat s hs _).2 ⟨v, hv, rfl⟩⟩, fun v hv => by
      obtain ⟨e, he, rfl⟩ := (hlat s hs v).1 hv
      exact ⟨_, hg, E.stable s _ (Subalgebra.algebraMap_mem _ _) _
        (E.stable s _ (Subalgebra.algebraMap_mem _ _) _ he)⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hJ, hbir, hall⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hmod N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact fun s hs => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
          fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
      · exact hsame)
  have p0 : IsPull O x z E (EB 0) := (hall 0).1
  have p1 : IsPull O x z E' (EB 1) := (hall 1).1
  have hpull := GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1
  have hsameJ := hpull.2.1 hsame
  have hscJ := hpull.2.2 _ hlat
  have hmodJ : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((BundleExamples.isModelOver_iff O _ d).1 hJ).2
  obtain ⟨-, f, f', hpair⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hmodJ N V
    (EB 0) (EB 1) hsameJ w w (b 0) (b 1) (hall 0).2 (hall 1).2 (fun i j hij => by
      simp [Module.Basis.repr_self, hij.ne])
  have hnum := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hmod N V E E' hsame K' ι' z hJ hbir (EB 0) (EB 1) p0 p1
    w w (b 0) (b 1) f f' hpair
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hroot := hnum.2 (k - 1) (psum (Fin N) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum N (k - 1)) (by omega) q L Q hQ'
  have hP : (pointIdeal O (joinCoord x z)).IsPrime := hmodJ.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing (Sum.elim ι ι') O) ∉ pointIdeal O (joinCoord x z) := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O (joinCoord x z)).comap (C : O →+* MRing (Sum.elim ι ι') O) := hmem
    rw [hmodJ.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hdiv : ∀ (v : Oˣ) (m : ℕ),
      rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ((v : O) * ϖ ^ m) =
        (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ := by
    intro v m
    rw [hroot _ (mul_ne_zero v.ne_zero (pow_ne_zero _ hϖ.ne_zero)), hroot _ hϖ.ne_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [ScalarQuotient.divCycle_const _ hC hϖ.ne_zero v m, cycEval_natCast_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnum.1 k hk1 hk2 q L Q hQ, hdiv, hroot _ hϖ.ne_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [GlobalTheory.T.scalar_quotient_statement O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hmodJ N V (EB 0) (EB 1) n u
      hscJ w w (b 0) (b 1) f f' hpair k (psumExpansion N k) (isPairExpansion_psum N k) _
      (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · intro m n' h w' hw' hm hEq
    obtain ⟨W, rfl⟩ := hw'
    by_cases h0 : h = 0
    · subst h0
      have hn' : n' = 0 := by
        by_contra hne
        rw [zero_pow hne, mul_zero] at hEq
        exact pow_ne_zero m hg hEq
      subst hn'
      have hnm : n * m = 0 := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) W _ _ ?_
        rw [pow_zero, mul_one] at hEq ⊢
        rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hEq]
      have hn0 : n = 0 := by
        rcases Nat.mul_eq_zero.mp hnm with h | h
        · exact h
        · omega
      subst hn0
      rw [hdiv u 0]
      simp
    · obtain ⟨a, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      have hnm : n * m = a * n' := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) (W * v ^ n') _ _ ?_
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        rw [pow_mul, pow_mul, ← mul_pow, hEq, mul_pow, mul_assoc]
      have hnm' : (n : ℤ) * m = a * n' := by exact_mod_cast hnm
      rw [hdiv u n, hdiv v a]
      linear_combination rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ * hnm'

end GlobalTheory.CompanionTheory.Ar.Num.Constants
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTransport

theorem mseg_restrict {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    mseg x (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.restrictChart s) ≠ 0 := by
  unfold mseg at hs ⊢
  rw [Finset.prod_ne_zero_iff] at hs ⊢
  intro k _
  exact hs (Sum.inl k) (Finset.mem_univ _)

theorem pull_transport (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁)
    (h : ∀ s, mseg x s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (EB : ChartBundle O (mseg (joinCoord x z)) N V) (FB : ChartBundle O (mseg (joinCoord x z)) N V₁)
    (hE : IsPull O x z E EB) (hF : IsPull O x z F FB) :
    ∀ s, mseg (joinCoord x z) s ≠ 0 → ∀ v, e v ∈ FB.lat s ↔ v ∈ EB.lat s := by
  intro s hs v
  have hr := h _ (mseg_restrict x z s hs)
  have key : FB.lat s = (EB.lat s).map (e : V →+ V₁) := by
    rw [hE s hs, hF s hs, AddMonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      refine ⟨a • e.symm t, ⟨a, ha, e.symm t, (hr _).1 (by simpa using ht), rfl⟩, ?_⟩
      simp
    · rintro ⟨_, ⟨a, ha, t, ht, rfl⟩, rfl⟩
      exact ⟨a, ha, e t, (hr _).2 ht, by simp⟩
  rw [key]
  constructor
  · rintro ⟨u, hu, huv⟩
    have : u = v := e.injective huv
    exact this ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem frame_transport {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (segreVec y) N V) (F : ChartBundle O (segreVec y) N V₁)
    (h : ∀ s, segreVec y s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (hw : IsFlagFrame y E w b) :
    IsFlagFrame y F (w.map e) b := by
  refine ⟨fun c hc i => ?_⟩
  rw [← hw.graded c hc i]
  ext u
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e.symm v, (h c hc _).1 (by simpa using hv), ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e v, (h c hc _).2 hv, ?_, ?_⟩
    · simpa using h1
    · simpa using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (e : V ≃ₗ[Ω] V₁) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), SameGeneric O x E E' → (∀ s, mseg x s ≠ 0 → ∀ v, (e v ∈ F.lat s ↔ v ∈ E.lat s) ∧ (e v ∈ F'.lat s ↔ v ∈ E'.lat s)) → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N F G L Q a = rootNum O x d N E G L Q a) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hW N V _ _ V₁ _ _ e E E' F F' hEE' he
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hFF' : SameGeneric O x F F' := by
    intro s hs
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).1 (e.symm v) ((he s hs _).1.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).2.2 h⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).2 (e.symm v) ((he s hs _).2.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).1.2 h⟩
  have hEE : SameGeneric O x E E := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hW', hfn, hj⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hW N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact hEE
      · exact hEE')
  have hp0 : IsPull O x z E (EB 0) := (hj 0).1
  have hp1 : IsPull O x z E' (EB 1) := (hj 1).1
  have hB : SameGeneric O (joinCoord x z) (EB 0) (EB 1) :=
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) hp0 hp1).2.1 hEE'
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hW').2 N V (EB 0) (EB 1) hB w w (b 0) (b 1) (hj 0).2 (hj 1).2
    (fun i j hij => by simp [Finsupp.single_apply, hij.ne])
  obtain ⟨FB, hF⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F).1 K' ι' z
  obtain ⟨FB', hF'⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F').1 K' ι' z
  have hfpF : IsFlagPair ϖ (joinCoord x z) FB FB' (w.map e) (w.map e) (b 0) (b 1) f g := by
    refine ⟨frame_transport _ e (EB 0) FB
        (pull_transport O x z e E F (fun s hs v => (he s hs v).1) _ _ hp0 hF) w _ hfp.flag,
      frame_transport _ e (EB 1) FB'
        (pull_transport O x z e E' F' (fun s hs v => (he s hs v).2) _ _ hp1 hF') w _ hfp.flag',
      fun i j hij => ?_, hfp.vertical, fun i => ?_⟩
    · rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hij.ne]
    · have := hfp.generic i
      rw [Module.Basis.repr_self] at this ⊢
      exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V E E' hEE' K' ι' z hW' hfn (EB 0) (EB 1)
    hp0 hp1 w w (b 0) (b 1) f g hfp
  obtain ⟨h3, h4⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V₁ F F' hFF' K' ι' z hW' hfn FB FB'
    hF hF' (w.map e) (w.map e) (b 0) (b 1) f g hfpF
  refine ⟨fun k hk hkd q L Q hQ => ?_, fun c G hG hc hcd q L Q hQ a ha => ?_⟩
  · rw [h1 k hk hkd q L Q hQ, h3 k hk hkd q L Q hQ]
  · rw [h2 c G hG hc hcd q L Q hQ a ha, h4 c G hG hc hcd q L Q hQ a ha]

end GlobalTheory.CompanionTheory.Ar.Num.CkTransport
end
