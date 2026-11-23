module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3337
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G)
    (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧
    IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG' N hL
  have hNoeth : IsNoetherianRing R := hA.1
  have hIC : IsIntegrallyClosed R := hA.2.2.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hG' N hL
  obtain ⟨G, β, i, hsm, hpb, hop, hu, hc⟩ := GlobalTheory.T.semiAbelian_descends_near_closedFibre R hA S π hP hS hI G' hG' N hL φ hφ
  obtain ⟨g, c, hsa, hgp⟩ := GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective R S π hP hS hI G' hG' G β hsm hpb φ hφ.1 hc
  exact ⟨G, g, c, β, i, hsa, hgp, hop, hu⟩

end GlobalTheory.Mum
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)


include hI hR hq hd hT in
theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl


include hI hR hq hd hT in
theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact GlobalTheory.T.arithmetic_curve_degree_independent_of_section k Y q hq hY N L r hr r' hr'
  | succ e => exact GlobalTheory.T.mixedHeightInduction_independent_of_section hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := GlobalTheory.T.inductive_height_formula_rhs_transport_iso k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem traitExtSt_of (h₁ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
      GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
        ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
          (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
          ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
            IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
            ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
              IsSemiAbelian G ∧ IsMonHom gen.hom)
    (h₂ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
      [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
      ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
      IsSemiAbelian G → IsMonHom gen.hom →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
          (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
          ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
            (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
            (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
            IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
            LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂'))
    (h₃ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
      ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
        IsMonomial D.toPre ![ϖ] ![β]) : TraitExtSt := by
  intro g n o _ ζ F V _ _ _ hB hD y
  obtain ⟨V₁, _, _, _, f, fK, hC₁, hinj₁, hloc₁, hfin₁, hK₁, A, α, α₂, hcart, hsq, hlb, G, _, _, gen, hsemi, hmon⟩ :=
    h₁ g n o ζ F V hB hD y
  obtain ⟨W, _, _, _, f', fK', hCW, hinj₂, hloc₂, hfin₂, hK₂, G', _, _, D, A', U, α', α₂', hsemi', hcart', hsq', hlb'⟩ :=
    h₂ g n o ζ F V₁ hC₁ (spMap fK ≫ y) A α α₂ hcart hsq hlb G gen hsemi hmon
  obtain ⟨hdvr, hcpl, hchar⟩ := hCW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨β, hβs, hβm⟩ := h₃ W ⟨hdvr, hcpl, hchar⟩ ϖ hϖ D
  have hsp : spMap (fK'.comp fK) = spMap fK' ≫ spMap fK := by
    unfold spMap
    simp
  refine ⟨
    { V := W
      complete := hcpl
      ϖ := ϖ
      irr := hϖ
      y := spMap (fK'.comp fK) ≫ y
      G := G'
      semi := hsemi'
      D := D
      A := A'
      U := U
      α := α'
      α₂ := α₂'
      cart := ?_
      sq := hsq'
      lb := hlb'
      β := β
      symm := hβs
      mono := hβm },
    f'.comp f, fK'.comp fK, hinj₂.comp hinj₁, ?_, hfin₂.comp hfin₁, ?_, rfl⟩
  · rw [hsp, Category.assoc]
    exact hcart'
  · exact RingHom.isLocalHom_comp f' f
  · intro a
    simp [hK₁, hK₂]

theorem traitExtSt : TraitExtSt :=
  traitExtSt_of GlobalTheory.T.exists_polarisedAbelian_semiAbelian_siegelPoint GlobalTheory.T.exists_uniformisation_finiteExtension_siegelFamily GlobalTheory.T.exists_monomialPeriods_symmetric_exponentForm

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_conj_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  intro g l hl hlo W hW
  obtain ⟨jB, hB⟩ := GlobalTheory.T.theta_series_sharp_reference_sixteen_terms g l hl hlo W hW
  obtain ⟨jD, hD⟩ := GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates g l hl hlo W hW
  refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
  obtain ⟨f, h0, h1, h2⟩ :=
    hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
  exact ⟨f, h0, h1, h2,
    hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
      (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_closedFibre_theta_embedding_of_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  first | exact @GlobalTheory.Mum.SecEmb.emb_of_secs | exact GlobalTheory.Mum.SecEmb.emb_of_secs | (intros; apply GlobalTheory.Mum.SecEmb.emb_of_secs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_sec_exp_intFam_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  intro R _ _ _ hR D C F₁
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_map_thetaExpansion_all_traits R hR D C 0
  refine ⟨Φ F₁, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hΦ W T
  exact ⟨a, b, ha, hb, h F₁⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  first | exact @GlobalTheory.UChartGeo.exists_monoFam_algClosed | exact GlobalTheory.UChartGeo.exists_monoFam_algClosed | (intros; apply GlobalTheory.UChartGeo.exists_monoFam_algClosed <;> assumption)
end
