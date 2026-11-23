module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle025
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportional
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GeoModel

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem intNumL_ofFn' {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem geoMono_mapDomain_some (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (μ : Ψ × Fin N →₀ ℕ) (hμ : μ.degree = dimFl Ψ N) :
    M.geoMono (μ.mapDomain some) = (intNumL ℚ (extTo ℚ M.P) (classList M.xdeg μ) : ℝ) / (M.δ : ℝ) := by
  have hcard : (Finsupp.toMultiset μ).card = dimFl Ψ N := by
    rw [Finsupp.card_toMultiset, ← hμ, Finsupp.degree_apply]
    rfl
  have hmap : Finsupp.toMultiset (μ.mapDomain some) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map μ some).symm
  have hdeg : (μ.mapDomain some).degree = dimFl Ψ N := by
    rw [← hμ]
    induction μ using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [Finsupp.mapDomain_add]
    | single a b => simp
  have hnone : (μ.mapDomain some) none = 0 := Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (μ.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [Multiset.length_toList, hmap, Multiset.card_map, hcard]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  set L := monoLines (M.line 1) (μ.mapDomain some) (dimFl Ψ N) with hLdef
  have hL : ∀ k : Fin (dimFl Ψ N), L k = M.line 1 ((Finsupp.toMultiset (μ.mapDomain some)).toList.get
      ⟨k, by rw [hlen]; exact k.2⟩) := by
    intro k
    simp only [hLdef, monoLines]
    rw [dite_eq_left (by rw [hlen]; exact k.2)]
  have hline : ∀ o, IsSmoothHerm (M.line 1 o) := by
    rintro (_ | r)
    · exact M.A_smooth
    · exact M.x_smooth 1 r
  have hsm : ∀ j, IsSmoothHerm (L j) := fun j => by rw [hL j]; exact hline _
  rw [GlobalTheory.T.log_integral_eq_generic_intersection M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII _ _) L hsm, ← intNumL_ofFn']
  congr 2
  refine NumericalSegreProof.intNumL_perm ℚ _ ?_
  have hlist : List.ofFn (fun j => (L j).a) =
      (Finsupp.toMultiset (μ.mapDomain some)).toList.map (fun o => (M.line 1 o).a) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      rw [hL]
      rfl
  rw [hlist, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, hmap, Multiset.map_map]
  rw [classList, Multiset.coe_toList]
  refine Multiset.map_congr rfl fun r _ => ?_
  exact M.x_deg 1 r

theorem geoFun_toA_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K]
    (II : IntersectionSystem), IsIntersectionSystem II → ∀ (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N) →
    M.geoFun (toA F) = genNum ℚ (extTo ℚ M.P) M.xdeg F [] / (M.δ : ℝ) := by
  intro Ψ _ _ N M _ II hII F hF
  have h1 : toA F = ∑ μ ∈ F.support, F.coeff μ • basisMonomials (Option (Ψ × Fin N)) ℝ (μ.mapDomain some) := by

    conv_lhs => rw [toA, F.as_sum, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]

  rw [h1, map_sum, genNum, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : μ.degree = dimFl Ψ N := by
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one μ).trans (hF (mem_support_iff.1 hμ))
  rw [map_smul, RootModel.geoFun, Module.Basis.constr_basis, geoMono_mapDomain_some M II hII μ hd,
    smul_eq_mul, List.append_nil, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num.GeoModel
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.TopLink

section Cyc

variable {K : Type} [DecidableEq K] {ι : K → Type}

theorem intNumL_perm (F : Type) [Field F] (V : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) := ⟨fun a b g => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cycList_perm (Z : Ideal (MRing ι O) → ℤ) {l l' : List (K → ℤ)} (h : l.Perm l') :
    cycList Z l = cycList Z l' := by
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm (IsLocalRing.ResidueField O) (specialIdeal W) h


omit [DecidableEq K] in
theorem divCycle_mul_finite {R : Type} [CommRing R] [IsNoetherianRing (MRing ι R)] (P : Ideal (MRing ι R))
    (f : MRing ι R) (n : Ideal (MRing ι R) → ℤ) :
    (Function.support fun W => divCycle P f W * n W).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1), zero_mul]

theorem cycList_ratDiv [Fintype K] [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (f g : MRing ι O)
    (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  unfold cycList cycEval ratDiv
  simp only [sub_mul]
  exact finsum_sub_distrib (divCycle_mul_finite P f _) (divCycle_mul_finite P g _)

end Cyc

theorem link_monomial {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hT : T.IsVertOff P S)
    {A A' : σ → HermLine ι} (hA : ∀ i, IsSmoothHerm (A i)) (hA' : ∀ i, IsSmoothHerm (A' i))
    (hiso : T.IsIsometric P A A') (i : σ) (μ : σ ⊕ σ →₀ ℕ) (hμ : μ.toMultiset.card = D) :
    arList I P (((μ + Finsupp.single (Sum.inl i) 1).toMultiset.map (Sum.elim A A')).toList) -
      arList I P (((μ + Finsupp.single (Sum.inr i) 1).toMultiset.map (Sum.elim A A')).toList) =
    ∑ p ∈ S, Real.log (p : ℕ) *
      (cycList (ratDiv (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) (T.f i))
        (MvPolynomial.map (Int.castRingHom (ZP p)) (T.g i))) (classList (Sum.elim T.x T.x') μ ++ []) : ℝ) := by
  classical
  set m := μ.toMultiset.toList with hm
  have hlen : m.length = D := by rw [hm, Multiset.length_toList, hμ]
  subst hlen
  let L : Fin m.length → HermLine ι := fun j => Sum.elim A A' (m.get j)
  have hB : ∀ s, IsSmoothHerm (Sum.elim A A' s) := by
    rintro (s | s)
    · exact hA s
    · exact hA' s
  have hL : ∀ j, IsSmoothHerm (L j) := fun j => hB _
  have hofL : List.ofFn L = m.map (Sum.elim A A') := by
    conv_rhs => rw [← List.ofFn_get m]
    rw [List.map_ofFn]
    rfl
  have key : ∀ s, arList I P (((μ + Finsupp.single s 1).toMultiset.map (Sum.elim A A')).toList) =
      I P (m.length + 1) (Fin.snoc L (Sum.elim A A' s)) := by
    intro s
    apply arList_eq_of_perm hP hI
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; exact hB s
      · rw [Fin.snoc_castSucc]; exact hL j
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [show (List.ofFn fun j => L j) = m.map (Sum.elim A A') from hofL, ← Multiset.coe_eq_coe,
        Multiset.coe_toList, List.concat_eq_append, ← Multiset.coe_add, ← Multiset.map_coe, hm,
        Multiset.coe_toList, map_add, Finsupp.toMultiset_single, Multiset.map_add]
      simp
  have hdeg : (List.ofFn fun j => (L j).a).Perm (classList (Sum.elim T.x T.x') μ ++ []) := by
    have h1 : (List.ofFn fun j => (L j).a) = m.map (Sum.elim T.x T.x') := by
      conv_rhs => rw [← List.ofFn_get m]
      rw [List.map_ofFn]
      congr 1
      funext j
      change (Sum.elim A A' (m.get j)).a = Sum.elim T.x T.x' (m.get j)
      cases h : m.get j with
      | inl s => exact (hiso s).1
      | inr s => exact (hiso s).2.1
    rw [h1, List.append_nil, classList, ← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, hm,
      Multiset.coe_toList]
  rw [key, key]
  have step := GlobalTheory.T.isometric_vertical_intersection_eq K ι P m.length hP I hI S (T.comp fun _ : Unit => i) (fun _ => hT i)
    (A i) (A' i) (hA i) (hA' i) (fun _ => hiso i) L hL
  refine step.trans (Finset.sum_congr rfl fun p _ => ?_)
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -⟩ := hT i
  have e1 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bf (T.f i) hf hfP (List.ofFn fun j => (L j).a) (by simp)
  have e2 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bg (T.g i) hg hgP (List.ofFn fun j => (L j).a) (by simp)
  rw [← cycList_perm _ hdeg, cycList_ratDiv, ← e1, ← e2]
  push_cast
  rfl

theorem arNum_eq_sum_log_val : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  intro K _ _ ι _ P D hP I hI σ _ S T hT A A' hA hA' hiso V Gs hV
  classical
  obtain ⟨rfl, hG⟩ := hV
  rw [arNum_sum']
  simp only [LocPair.val, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cycNum, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [(Gs i).as_sum, Finset.mul_sum, arNum_sum']
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hcard : μ.toMultiset.card = D := by
    have h := hG i (MvPolynomial.mem_support_iff.1 hμ)
    rw [Finsupp.card_toMultiset, ← h, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hpoly : (X (Sum.inl i) - X (Sum.inr i)) * monomial μ (AddMonoidAlgebra.coeff (Gs i) μ) =
      monomial (μ + Finsupp.single (Sum.inl i) 1) (AddMonoidAlgebra.coeff (Gs i) μ) +
        monomial (μ + Finsupp.single (Sum.inr i) 1) (-AddMonoidAlgebra.coeff (Gs i) μ) := by
    rw [monomial_add_single, monomial_add_single, map_neg]
    ring
  have hmono := link_monomial hP hI hT hA hA' hiso i μ hcard
  rw [hpoly, arNum_add', arNum_monomial', arNum_monomial', neg_mul, ← sub_eq_add_neg, ← mul_sub, hmono,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [LocPair.map]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.TopLink
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.flag_height_power_sum_one_zero : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (Q : RP Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_pk_one_mul <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.real_tower_proportional : PB.Proportional → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (R : RealTower T), R.Unif → T.Proportional := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | exact GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.Swap

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arList_swap_one {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A'))
    (pre post : List (HermLine ι)) (hpre : ∀ b ∈ pre, IsSmoothHerm b)
    (hpost : ∀ b ∈ post, IsSmoothHerm b) (hP : IsArithVar P ((pre ++ post).length + 1)) :
    arList I P (pre ++ A :: post) = arList I P (pre ++ A' :: post) := by
  have hL : ∀ j, IsSmoothHerm ((pre ++ post).get j) := fun j => by
    rcases List.mem_append.1 (List.get_mem _ j) with h | h
    · exact hpre _ h
    · exact hpost _ h
  have hsnoc : ∀ B : HermLine ι, IsSmoothHerm B → arList I P (pre ++ B :: post) =
      I P ((pre ++ post).length + 1) (Fin.snoc (pre ++ post).get B) := by
    intro B hB
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hB
      · simpa using hL i
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get, List.concat_eq_append]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  rw [hsnoc A hA, hsnoc A' hA']
  have h := GlobalTheory.T.isometric_vertical_intersection_eq K ι P _ hP I hI ∅ T hT A A' hA hA' hiso (pre ++ post).get hL
  simpa [sub_eq_zero] using h

theorem arList_swap_map {J : Type} {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A')) (F G : J → HermLine ι)
    (hF : ∀ j, IsSmoothHerm (F j)) (hG : ∀ j, IsSmoothHerm (G j))
    (hFG : ∀ j, F j = G j ∨ (F j = A ∧ G j = A')) (l : List J) :
    ∀ (pre : List (HermLine ι)), (∀ b ∈ pre, IsSmoothHerm b) →
      IsArithVar P (pre.length + l.length) →
      arList I P (pre ++ l.map F) = arList I P (pre ++ l.map G) := by
  induction l with
  | nil => intro pre _ _; rfl
  | cons j l ih =>
    intro pre hpre hP
    have e1 : pre ++ (j :: l).map F = (pre ++ [F j]) ++ l.map F := by simp
    have e2 : (pre ++ [F j]) ++ l.map G = pre ++ F j :: l.map G := by simp
    have hpre' : ∀ b ∈ pre ++ [F j], IsSmoothHerm b := fun b hb => by
      rcases List.mem_append.1 hb with h | h
      · exact hpre b h
      · rw [List.mem_singleton.1 h]; exact hF j
    have hlen : (pre ++ [F j]).length + l.length = pre.length + (j :: l).length := by
      simp; omega
    rw [e1, ih _ hpre' (hlen ▸ hP), e2, List.map_cons]
    rcases hFG j with h | ⟨h, h'⟩
    · rw [h]
    · rw [h, h']
      refine arList_swap_one hI T hT hA hA' hiso pre _ hpre ?_ ?_
      · intro b hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
        exact hG i
      · have : (pre ++ l.map G).length + 1 = pre.length + (j :: l).length := by
          simp; omega
        exact this ▸ hP

theorem ofFn_monoLines {J : Type} (ℓ : J → HermLine ι) (m : J →₀ ℕ) (d : ℕ)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
  subst hd
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp [monoLines]

end GlobalTheory.CompanionTheory.Ar.Num.Swap

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

open GlobalTheory.CompanionTheory.Ar.Top.Link

theorem arMono_swapA : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  intro Ψ _ N M _ II hII A' hs hc T hT hiso t m
  set M' := Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc with hM'
  have hI : IsIntersectionFamily (II M.K M.ι) := hII.1 M.K M.ι
  have hP : IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hF : ∀ j, IsSmoothHerm (M.line t j) := fun j => by
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hG : ∀ j, IsSmoothHerm (M'.line t j) := fun j => by
    cases j with
    | none => exact hs
    | some r => exact M.x_smooth t r
  have hFG : ∀ j, M.line t j = M'.line t j ∨ (M.line t j = M.A ∧ M'.line t j = A') := fun j => by
    cases j with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some r => exact Or.inl rfl
  show (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0) =
    (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0)
  split_ifs with hd
  swap
  · rfl
  have hlen : (Finsupp.toMultiset m).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hd]
    rfl
  have hmono : ∀ ℓ : Option (Ψ × Fin N) → HermLine M.ι, (∀ j, IsSmoothHerm (ℓ j)) →
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines ℓ m (dimFl Ψ N + 1)) =
        arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map ℓ) := by
    intro ℓ hℓ
    symm
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      unfold monoLines
      split_ifs with h
      · exact hℓ _
      · exact absurd (by have := j.2; omega) h
    · rw [Swap.ofFn_monoLines ℓ m _ hlen]
  have key : arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M.line t)) =
      arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M'.line t)) :=
    Swap.arList_swap_map hI T hT M.A_smooth hs hiso _ _ hF hG hFG _ [] (by simp) (by simpa [hlen] using hP)
  exact congrArg (· / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))
    ((hmono _ hF).trans (key.trans (hmono (M'.line t) hG).symm))

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.real_tower_conv_I2 : PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), T.Conv II ∧ T.I2 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | exact GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 <;> assumption)
end
