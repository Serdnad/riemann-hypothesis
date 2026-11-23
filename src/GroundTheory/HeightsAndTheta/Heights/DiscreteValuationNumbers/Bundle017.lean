module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ProjIdealFormValue

theorem weight_blockWeight_apply {K : Type*} [DecidableEq K] {ι : K → Type*} (m : (Σ k, ι k) →₀ ℕ)
    (k : K) : Finsupp.weight (blockWeight ι) m k = Finsupp.mapDomain Sigma.fst m k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finset.sum_apply,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.1 = k
  · simp [blockWeight, h]
  · simp [blockWeight, Ne.symm h]

theorem eval₂_monomial_cone {F Φ : Type*} [CommRing F] [CommRing Φ] (α : F →+* Φ) {K : Type*}
    {ι : K → Type*} (z : (Σ k, ι k) → Φ) (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    eval₂ (C.comp α) (fun p => C (z p) * X p.1) (monomial m c) =
      C (eval₂ α z (monomial m c)) * monomial (Finsupp.mapDomain Sigma.fst m) (1 : Φ) := by
  rw [eval₂_monomial, eval₂_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [mul_pow, Finsupp.prod_mul, map_mul, RingHom.coe_comp, Function.comp_apply,
    map_finsuppProd, map_pow, mul_assoc]

theorem proof : ProjIdealFormValue.Statement := by
  intro F _ Ω _ _ K _ ι y N E _ _ w M φ Φ _ _ t d x hx
  have hx' : IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) x d := hx
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  obtain ⟨m₀, hm₀⟩ : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hx0
  have hD : ∀ m ∈ x.support, Finsupp.mapDomain Sigma.fst m = Finsupp.mapDomain Sigma.fst m₀ := by
    intro m hm
    ext o
    rw [← weight_blockWeight_apply, ← weight_blockWeight_apply, hx' (mem_support_iff.mp hm),
      hx' (mem_support_iff.mp hm₀)]
  have key : eval₂ (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1) x =
      C (eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x) *
        monomial (Finsupp.mapDomain Sigma.fst m₀) 1 := by
    conv_lhs => rw [x.as_sum]
    conv_rhs => rw [x.as_sum]

    rw [eval₂_sum, eval₂_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval₂_monomial_cone, hD m hm]
  rw [key, mul_eq_zero, C_eq_zero, monomial_eq_zero]
  simp

end ProjIdealFormValue

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem idealCycle_support_finite {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  intro W hW
  by_contra hmin
  apply hW
  unfold idealCycle
  rw [dite_eq_right]
  exact fun h => hmin h.1

theorem finsum_mul_finsum_comm {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by
  classical
  set S := ha.toFinset
  set T := S.biUnion (fun W => (hc W).toFinset)
  have hcT : ∀ W ∈ S, Function.support (c W) ⊆ ↑T := by
    intro W hW U hU
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨W, hW, (hc W).mem_toFinset.mpr hU⟩
  have hin : ∀ U, ∑ᶠ W, a W * c W U = ∑ W ∈ S, a W * c W U := by
    intro U
    apply finsum_eq_sum_of_support_subset
    intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
  simp_rw [hin]
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_congr rfl (g := fun W => a W * ∑ U ∈ T, c W U * n U)]
    · simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    · intro W hW
      congr 1
      apply finsum_eq_sum_of_support_subset
      intro U hU
      exact hcT W hW (left_ne_zero_of_mul hU)
  · intro U hU
    obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hU)
    exact hcT W hW (right_ne_zero_of_mul hne)
  · intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW

theorem RightExpansion.proof (hV : VertCutEff.Statement.{u})
    (hD : DivisorIdealCycle.Statement.{u}) : RightExpansion.Statement.{u} := by
  classical
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hmodel b f g heff c s hs hsP hhor hnc L
  have hPmh : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) :=
    SupSpanMultiHomog.proof O K ι P s c hmodel.multiProj.multiHomog hs
  have key : ∀ W : Ideal (MRing ι O),
      divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) =
        divCycle P s W * cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g)) := by
    intro W
    by_cases hW : divCycle P s W = 0
    · rw [hW, zero_mul, zero_mul]
    congr 1
    obtain ⟨hWp, hPW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    split_ifs with hϖW
    · exact hV O ϖ hϖ K ι P d hmodel b f g heff W s hsP hWmin hWrel
        (MinimalPrimeMultiHomog.proof O K ι _ W hPmh hWmin) hϖW (hnc W hϖW hW) L
    · have hv := hhor W hW hϖW
      have hP : P.IsPrime := hmodel.multiProj.isPrime
      rw [hD O K ι P W f g g f hP hWp hPW heff.1.den_not_mem
        (fun U hU hWU hUrel => heff.2 U hU (hPW.trans hWU) hUrel)
        hv.den_not_mem hv.num_not_mem (by rw [mul_comm, sub_self]; exact P.zero_mem)]
  exact (finsum_congr key).trans <| finsum_mul_finsum_comm _ (fun W U => idealCycle (W ⊔ divisorIdeal P f g) U) _
    (DivCycleFiniteSupport.proof O K ι P s) (fun W => idealCycle_support_finite _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section General

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem idealCycle_eq_of_mul_mem {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by
  unfold idealCycle
  by_cases h : U ∈ J.minimalPrimes ∧ IsRelevant U
  · have h' : U ∈ J'.minimalPrimes ∧ IsRelevant U :=
      ⟨mem_minimalPrimes_of_mul_mem hs ht hsJ htJ h.1, h.2⟩
    rw [dite_eq_left h, dite_eq_left h']
    have : U.IsPrime := h.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hs ht hsJ htJ]
  · have h' : ¬ (U ∈ J'.minimalPrimes ∧ IsRelevant U) := fun h' =>
      h ⟨mem_minimalPrimes_of_mul_mem ht hs htJ hsJ h'.1, h'.2⟩
    rw [dite_eq_right h, dite_eq_right h']

theorem divCycle_eq_zero_of_not_mem {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end General

theorem DivisorIdealCycle.proof : DivisorIdealCycle.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W f g u v hP hW hPW hg hloc hu hv huv
  funext U
  by_cases hU : U.IsPrime ∧ W ≤ U ∧ IsRelevant U
  · obtain ⟨hUp, hWU, hUrel⟩ := hU
    obtain ⟨u', v', hu'U, hloc'⟩ := hloc U hUp hWU hUrel
    have hu'W : u' ∉ W := fun h => hu'U (hWU h)
    have h1U : (1 : MRing ι R) ∉ U := (Ideal.ne_top_iff_one U).mp hUp.ne_top

    have hcross : u * v' - u' * v ∈ P := by
      have hmem : (u * v' - u' * v) * g ∈ P := by
        rw [show (u * v' - u' * v) * g = u' * (u * f - v * g) - u * (u' * f - v' * g) by ring]
        exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ hloc')
      exact (hP.mem_or_mem hmem).resolve_right hg
    have hv'W : v' ∉ W := by
      intro h
      have hmem : u' * v ∈ W := by
        rw [show u' * v = u * v' - (u * v' - u' * v) by ring]
        exact W.sub_mem (W.mul_mem_left u h) (hPW hcross)
      exact (hW.mem_or_mem hmem).elim hu'W hv

    have hmul := congrFun (DivCycleMul.proof R K ι W u' v hW hu'W hv) U
    have hmul' := congrFun (DivCycleMul.proof R K ι W u v' hW hu hv'W) U
    have heq : divCycle W (u' * v) U = divCycle W (u * v') U :=
      divCycle_eq_of_mul_sub_mem (P := W) (W := U) (u := 1) (v := 1) h1U h1U (by
        rw [show 1 * (u' * v) - 1 * (u * v') = -(u * v' - u' * v) by ring]
        exact W.neg_mem (hPW hcross))
    have hu'0 : divCycle W u' U = 0 := divCycle_eq_zero_of_not_mem hu'U
    simp only [Pi.add_apply] at hmul hmul'

    have hv'D : v' ∈ divisorIdeal P f g := by
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul,
        show v' * g = u' * f - (u' * f - v' * g) by ring]
      exact Submodule.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
        (Ideal.mem_sup_left hloc')
    have hsJ : ∀ x ∈ W ⊔ Ideal.span {v'}, 1 * x ∈ W ⊔ divisorIdeal P f g := by
      intro x hx
      rw [one_mul]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hv'D) W hx
    have htJ : ∀ x ∈ W ⊔ divisorIdeal P f g, u' * x ∈ W ⊔ Ideal.span {v'} := by
      intro x hx
      obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul] at hd
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hd
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have h1 : (u' * d - a * v') * g ∈ P := by
        have e : (u' * d - a * v') * g = u' * p + a * (u' * f - v' * g) := by
          calc (u' * d - a * v') * g = u' * (d * g) - a * v' * g := by ring
            _ = u' * p + a * (u' * f - v' * g) := by rw [← hpr]; ring
        rw [e]
        exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hloc')
      have h2 : u' * d - a * v' ∈ P := (hP.mem_or_mem h1).resolve_right hg
      rw [show u' * (w + d) = (u' * w + (u' * d - a * v')) + a * v' by ring]
      exact Submodule.add_mem_sup (W.add_mem (W.mul_mem_left _ hw) (hPW h2))
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hR : idealCycle (W ⊔ divisorIdeal P f g) U = divCycle W v' U := by
      rw [divCycle_eq_idealCycle]
      exact (idealCycle_eq_of_mul_mem h1U hu'U hsJ htJ).symm
    rw [hR]
    show divCycle W v U - divCycle W u U = divCycle W v' U
    omega
  · have hcomp : ∀ J : Ideal (MRing ι R), W ≤ J → ¬ (U ∈ J.minimalPrimes ∧ IsRelevant U) := by
      rintro J hWJ ⟨h, hrel⟩
      exact hU ⟨h.1.1, hWJ.trans h.1.2, hrel⟩
    show divCycle W v U - divCycle W u U = idealCycle (W ⊔ divisorIdeal P f g) U
    unfold divCycle idealCycle
    rw [dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left),
      sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem VNumCut.proof (h : CutByForm.Statement.{u}) : VNumCut.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs
  set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hπ
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => rfl
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := ker_map_residue_eq_span hϖ

  have hGbp : (specialIdeal G).IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1
  have hGbh : IsMultiHomogIdeal (specialIdeal G) := SpecialIdealMultiHomog.proof O K ι G hGh
  have hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) <
      ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]; exact hdim
  have hsb : IsMultiHomog (π s) c := isWeightedHomogeneous_map_of _ _ hs
  have hsbG : π s ∉ specialIdeal G := by
    intro hm
    apply hsG
    have hcm : (G.map π).comap π = G := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hϖG
    rw [← hcm]
    exact hm

  have hcut := h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb
    hsbG bs

  have hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s} := by
    rw [sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left hϖG
  have hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ) := by
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]
  have hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s} := by
    rw [hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have htr := SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof
    SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s})
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [hmapJ, ← divCycle_eq_idealCycle] at htr
  show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ =
    cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)
  rw [hcut, hdiv, htr]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensExpress.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, ∃ n : ℕ, f ^ n * t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨m, hm⟩ := ht q
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (a q * t q) = (f ^ n * a q) * (f ^ m * t q) := by ring
    rw [this]
    exact mul_mem hn hm

theorem TwistedDualGensExpress.proof : TwistedDualGensExpress.Statement := by
  unfold TwistedDualGensExpress.Statement
  intro R _ ϖ Ω _ _ K _ ι y N E _ _ B B' hsame a a' M M' φ φ' hφ hφ' c hc m
  set A := chartRing R (segreVec y) c with hA
  set w : Ω := algebraMap R Ω ϖ with hw
  have hwA : w ∈ A := Subalgebra.algebraMap_mem _ ϖ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  set ψ : Module.Dual Ω E := (∏ k, y ⟨k, c k⟩ ^ (-a' k)) • φ' m with hψ
  have hψA : ∀ v ∈ B'.lat c, ψ v ∈ A := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := hφ'.sections c hc m v hv
    have : ψ v = s := by
      rw [hψ, LinearMap.smul_apply, hsv, smul_eq_mul, mul_comm s, ← mul_assoc,
        ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
          rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy k))]), one_mul]
    rw [this]
    exact hs
  obtain ⟨k0, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbq : ∀ l q, ∃ n : ℕ, f l ≠ 0 → ∃ e : ℕ, f l ^ e * (w ^ n * ψ (b l q)) ∈ A := by
    intro l q
    by_cases hl : f l = 0
    · exact ⟨0, fun h => (h hl).elim⟩
    obtain ⟨e, he⟩ := (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
        by_cases h : q' = q
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := (hsame c hc).1 _ he
    refine ⟨n, fun _ => ⟨e, ?_⟩⟩
    have h := hψA _ hn
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    rw [show f l ^ e * (w ^ n * ψ (b l q)) = w ^ n * (f l ^ e * ψ (b l q)) by ring]
    exact h
  choose nb hnb using hbq
  set n := Finset.univ.sup (fun p : Fin k0 × Fin N => nb p.1 p.2) with hn
  have hle : ∀ l q, nb l q ≤ n := fun l q =>
    Finset.le_sup (f := fun p : Fin k0 × Fin N => nb p.1 p.2) (Finset.mem_univ (l, q))
  have hmain : ∀ v ∈ B.lat c, (w ^ n • ψ) v ∈ A := by
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
    intro l
    by_cases hl : f l = 0
    · exact ⟨1, by simp [hl]⟩
    obtain ⟨a'', ha'', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨e, he⟩ := TwistedDualGensExpress.sum_mul_mem_localized A (hf l) a''
      (fun q => w ^ n * ψ (b l q)) ha'' (fun q => by
        obtain ⟨e, he⟩ := hnb l q hl
        refine ⟨e, ?_⟩
        rw [← pow_sub_mul_pow w (hle l q)]
        rw [show f l ^ e * (w ^ (n - nb l q) * w ^ nb l q * ψ (b l q)) =
          w ^ (n - nb l q) * (f l ^ e * (w ^ nb l q * ψ (b l q))) by ring]
        exact mul_mem (pow_mem hwA _) he)
    refine ⟨e, ?_⟩
    have : w ^ n * ψ v = ∑ q, a'' q * (w ^ n * ψ (b l q)) := by

      rw [hrep, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    rw [smul_eq_mul, this]
    exact he
  obtain ⟨u, hu, hsum'⟩ := hφ.generate c hc (w ^ n • ψ) hmain
  refine ⟨n, u, hu, ?_⟩
  have hY : (∏ k, y ⟨k, c k⟩ ^ a' k) * ∏ k, y ⟨k, c k⟩ ^ (-a' k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hy k))]
  have h1 : w ^ n • φ' m = (∏ k, y ⟨k, c k⟩ ^ a' k) • (w ^ n • ψ) := by
    rw [hψ, smul_comm (w ^ n) (∏ k, y ⟨k, c k⟩ ^ (-a' k)), smul_smul, hY, one_smul]
  rw [h1, hsum', Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_add₀ (hy k), sub_eq_add_neg]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
