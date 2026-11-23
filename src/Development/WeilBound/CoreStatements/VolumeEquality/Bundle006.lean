module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.WithBotTop
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

section

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem fnField_toSubfield (y : (Σ b, ι b) → Ω) :
    (fnField k y).toSubfield = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y := by
  rw [fnField, IntermediateField.adjoin_toSubfield]
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 2
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only at hpq
    subst hpq
    exact ⟨⟨a, i, j⟩, rfl⟩
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩

theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

theorem krull_pointIdeal (y : (Σ b, ι b) → Ω) (d : ℕ) (h : IsPt k y d) [(pointIdeal k y).IsPrime] :
    ringKrullDim (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hnz, hfin, htr⟩ := h
  have hcone := ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz
  have hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω) := by
    rw [← fnField_toSubfield k y]
    rfl
  have hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y) := by
    rw [hset]
    have : Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra :=
      Algebra.adjoin_eq (fnField k y).toSubalgebra
    rw [this]
    rfl
  haveI : FiniteDimensional (fnField k y) Ω := hfin
  have htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal) := hcone
    rw [e, hadj, trdeg_eq_of_finite k (fnField k y), htr]
    push_cast
    rfl
  exact ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'

end

theorem ptDim : PtDim := by
  intro k _ Ω _ _ K _ ι _ y d h
  classical
  have hmp : IsMultiProjPrime (pointIdeal k y) := PointIdealMultiProj.proof k Ω K ι y h.1
  have hdim := krull_pointIdeal k y d h
  refine ⟨?_, ?_, ?_⟩
  · convert hmp
  · unfold FieldNumbers.relDim
    rw [hdim]
    have e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ) := by
      push_cast
      ring
    change (WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))
    rw [e]
    rfl
  · refine ⟨?_, hdim⟩
    exact (Bridge.isMultiProjPrime_iff _).1 hmp

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition.Fib

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

theorem ker_map {σ τ : Type} (k : Type) [Field k] [Algebra ℚ k] (g : σ → MvPolynomial τ ℚ) :
    RingHom.ker (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) =
      (RingHom.ker (aeval g : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ)).map (map (algebraMap ℚ k)) := by
  classical
  have hc : ∀ f : MvPolynomial σ ℚ, (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
      (map (algebraMap ℚ k) f) = map (algebraMap ℚ k) (aeval g f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [algebraMap_eq]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun f hf => ?_)
  · let b := Module.Basis.ofVectorSpace ℚ k
    let T : Finset _ := f.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff f m)).support
    let F : _ → MvPolynomial σ ℚ := fun i => ∑ m ∈ f.support, monomial m (b.repr (AddMonoidAlgebra.coeff f m) i)
    have hf' : f = ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (F i) := by
      conv_lhs => rw [f.as_sum]

      simp only [F, map_sum, Finset.mul_sum, map_monomial, C_mul_monomial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_

      rw [← map_sum (monomial m)]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff f m), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun m => (b.repr (AddMonoidAlgebra.coeff f m)).support) hm)
          (fun i a => a • b i) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    have h0 : ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (aeval g (F i)) = 0 := by
      rw [RingHom.mem_ker, hf'] at hf

      simpa only [map_sum, map_mul, hc, aeval_C, algebraMap_eq] using hf
    have h1 : ∀ i ∈ T, aeval g (F i) = 0 := fun i hi => by
      ext m
      have := congrArg (AddMonoidAlgebra.coeff · m) h0
      simp only [coeff_sum, coeff_C_mul, coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
      refine linearIndependent_iff'.1 b.linearIndependent T (fun i => AddMonoidAlgebra.coeff (aeval g (F i)) m) ?_ i hi
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    rw [hf']
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h1 i hi))
  · rw [Ideal.mem_comap, RingHom.mem_ker, hc, (RingHom.mem_ker.1 hf : aeval g f = 0), map_zero]

variable {S : Type} {r : S → ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

abbrev Ent (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

def genU (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s)) (MvPolynomial (Ent r) ℚ) := fun l m =>
  if h : m < l then X ⟨s, ⟨(l, m), h⟩⟩ else if l = m then 1 else 0

def genMinor (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial (Ent r) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin (x.1.2 + 1) => genU r x.1.1 (x.2 a) (Fin.castLE x.1.2.2 b))

def genCone (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) ℚ :=
  rename Sum.inr (genMinor r x) * X (Sum.inl x.1)

def uNum (r : S → ℕ) {n : ℕ} (a : Fin n → (Σ s, Fin (r s)) → ℤ) : ℤ :=
  @intNum _ (fun _ _ => Classical.propDecidable _) (PlIx r) ℚ _
    (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)) n a

theorem plPt_eq [Algebra ℚ Ω] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (x) :
    plPt u x = aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genMinor r x) := by
  have e : ∀ s l m, aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genU r s l m) = u s l m := fun s l m => by
    unfold genU
    split_ifs with h h'
    · simp
    · subst h'; simp [h1]
    · rw [map_zero, h0 s l m (lt_of_le_of_ne (not_lt.1 h) h')]
  unfold plPt genMinor
  rw [AlgHom.map_det]
  congr 1
  ext a b
  exact (e _ _ _).symm

theorem pointIdeal_plPt [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    pointIdeal k (plPt u) =
      (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)).map (map (algebraMap ℚ k)) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  let φ : MvPolynomial (Ent r) k →ₐ[k] Ω := aeval fun q : Ent r => u q.1 q.2.1.1 q.2.1.2
  have hφ : Function.Injective φ := h.2.2.1
  let Θ : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) k →+* MvPolynomial (Σ s, Fin (r s)) Ω :=
    (map φ.toRingHom).comp (sumAlgEquiv k _ _).toRingHom
  have hΘ : Function.Injective Θ := (map_injective _ hφ).comp (sumAlgEquiv k _ _).injective
  have hr : ∀ f : MvPolynomial (Ent r) ℚ, Θ (map (algebraMap ℚ k) (rename Sum.inr f)) =
      C (aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [Θ, φ]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f i hf => simp only [map_mul, hf]; simp [Θ, φ]
  have key : (pointConeMap k (plPt u) : MvPolynomial _ k →+* MvPolynomial _ Ω) = Θ.comp
      (aeval (fun s => map (algebraMap ℚ k) (genCone r s)) : MvPolynomial _ k →ₐ[k] MvPolynomial _ k).toRingHom := by
    refine ringHom_ext (fun a => ?_) fun x => ?_
    · simp [pointConeMap, Θ, φ, algebraMap_eq]
    · simp only [pointConeMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply, genCone, map_mul, hr, plPt_eq u h.1 h.2.1]
      simp [Θ]
  rw [← ker_map]
  ext f
  rw [pointIdeal, RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff Θ hΘ]
  exact (RingHom.congr_fun key f).congr_left

theorem inum_plPt [Fintype S] [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) {n : ℕ}
    (a : Fin n → (Σ s, Fin (r s)) → ℤ) : inum k (plPt u) a = uNum r a := by
  unfold inum uNum
  rw [pointIdeal_plPt u h]
  exact (@GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ _ k _ _ _ _ (fun _ _ => Classical.propDecidable _)
    (PlIx r) _ _).2 n a

def rowIx {n : ℕ} (m l : Fin n) : Fin (m + 1) → Fin n := fun a => if a = Fin.last m then l else Fin.castLE m.2 a

theorem plPt_row (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (s : S) (m l : Fin (r s)) : plPt u ⟨⟨s, m⟩, rowIx m l⟩ = u s l m := by
  unfold plPt
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · simp only [Matrix.of_apply, rowIx, if_true]
      rfl
    · intro a _
      simp only [Matrix.of_apply, rowIx, if_neg (Fin.castSucc_lt_last a).ne, h1]
  · intro a b hab
    have hab' : a < b := hab
    simp only [Matrix.of_apply, rowIx, if_neg (hab'.trans_le (Fin.le_last b)).ne]
    exact h0 _ _ _ hab'

theorem plPt_ne (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (b) : ∃ i, plPt u ⟨b, i⟩ ≠ 0 :=
  ⟨rowIx b.2 b.2, by rw [show b = ⟨b.1, b.2⟩ from rfl, plPt_row u h1 h0, h1]; exact one_ne_zero⟩

theorem fnField_plPt [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) : fnField k (plPt u) =
      IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
  · have : ∀ x, plPt u x ∈ IntermediateField.adjoin k
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := fun x => by
      unfold plPt
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ =>
        IntermediateField.subset_adjoin _ _ ⟨⟨_, _, _⟩, rfl⟩)
    rintro _ ⟨p, q, -, rfl⟩
    exact div_mem (this p) (this q)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨⟨⟨s, m⟩, rowIx m l⟩, ⟨⟨s, m⟩, rowIx m m⟩, rfl, ?_⟩
    rw [plPt_row u h1 h0, plPt_row u h1 h0, h1, div_one]

theorem vdeg_plDeg [Fintype S] (O : ValuationSubring Ω) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (b : Σ s, Fin (r s)) :
    vdeg O (plPt u) (plDeg b) = (Finset.univ.sup fun i => O.valuation (plPt u ⟨b, i⟩))⁻¹ := by
  unfold vdeg
  rw [Finset.prod_eq_single b (fun b' _ h => by simp [plDeg, h]) (by simp)]
  simp [plDeg]

theorem trdeg_eq [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    Algebra.trdeg k Ω = Nat.card (Ent r) := by
  obtain ⟨h1, h0, hi, hd, hf⟩ := h
  have e : IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k (Set.range fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro _ ⟨⟨s, l, m⟩, rfl⟩
      rcases lt_trichotomy l m with h | h | h
      · simp only [h0 s l m h]; exact zero_mem _
      · subst h; simp only [h1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l, m), h⟩, rfl⟩
    · rintro _ ⟨⟨s, ⟨l, m⟩, h⟩, rfl⟩
      exact ⟨⟨s, l, m⟩, rfl⟩
  rw [e] at hf
  have := Module.finite_of_finrank_pos (hf ▸ hd)
  have hb : IsTranscendenceBasis k fun q : Ent r => u q.1 q.2.1.1 q.2.1.2 :=
    hi.isTranscendenceBasis_iff_isAlgebraic.2 (IntermediateField.isAlgebraic_adjoin_iff_top.1 inferInstance)
  rw [← hb.cardinalMk_eq_trdeg]
  exact (Nat.cast_card).symm

end SheetDecomposition.Fib
end
end
