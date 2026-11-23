module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.GenPb
import GroundTheory.PAdicHodge.NormalizedTraceTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eid (hC : CupLaws) (hS : Slant) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (Dt : Dat hC P M d)
    {a' n : ℕ} (x : Hdg M.q a' n) {α : ℕ} (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))) :
    lhsF hC P Dt x φ' = rhsF hC P Dt x φ' := by
  funext β ψ
  have hL : lhsF hC P Dt x φ' β ψ =
      (∑ s, if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0) +
      ∑ s, if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 := by
    simp only [lhsF, Pi.add_apply, Finset.sum_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun s _ => ?_ <;> split_ifs <;> rfl
  rw [hL]
  simp only [rhsF]
  by_cases hlt : a' ≤ α + β
  · obtain ⟨A, hA⟩ : ∃ A, α + β = A + a' := ⟨α + β - a', by omega⟩
    have hPM := sm_gen hM
    have := hPM.1
    have := hPM.2
    obtain ⟨sl, hsl⟩ := slantR hS K M.gen M.gen Dt.S.P.gen M.q M.q (Model.genMap Dt.S.p₁ Dt.S.h₁)
      (Model.genMap Dt.S.p₂ Dt.S.h₂) (gen_pb _ _ _ _ Dt.S.prod) Dt.S.P.q (Model.genMap_q _ _) (Model.genMap_q _ _)
      α (2 + 2 * d) β n (A + a') (2 + 2 * d + n) hA rfl φ'
    have hsl' : IsSl Dt.S hA φ' sl := hsl
    have hy : pullH (Model.genMap Dt.S.Δ Dt.S.hΔ) (Model.genMap_q Dt.S.Δ Dt.S.hΔ) a' n
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = 0 := by
      rw [map_sub, sub_eq_zero]
      have c7 := (hC K M.gen M.q).2.2.2.2.2.2
      rw [c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₁) a' n x,
        c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₂) a' n x]
    have hk := Dt.kill A a' n _ hy (ψ ∘ₗ sl)
    have split : (ψ ∘ₗ sl) ∘ₗ (cupL hC Dt.S.P.q (a := A) (a' := a') (i := 2 + 2 * d) (j := n) rfl rfl).flip
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = th hC Dt.S sl ψ (Dt.S.pl₁ a' n x) - th hC Dt.S sl ψ (Dt.S.pl₂ a' n x) := by
      ext C
      simp [th]
    rw [split, map_sub, sub_eq_zero, Dt.dec] at hk

    simp only [map_add (f := _), map_sum, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply] at hk
    have e1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s) rfl
    have e2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s)
    have f1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) =
        P.h M α _ (M.toV _ (Dt.a₀ s)) φ' * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ) :=
      fun s => t2z hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s)
    have f2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) = 0 :=
      fun s => t2a hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s) (Dt.jne s)
    simp only [e1, e2, f1, f2, Finset.sum_const_zero, add_zero] at hk
    exact hk
  · have hk : ∀ {i : ℕ} (X : M.T i), kap hC P x φ' X = 0 := by
      intro i X
      rw [kap, Fx, dite_eq_right (fun h => hlt (by omega)), map_zero, smul_zero]
    have hg : Gx hC x ψ = 0 := by
      rw [Gx, dite_eq_right (by omega)]
    simp only [hk, hg, zero_mul, map_zero, mul_zero, dite_eq_ite, ite_self, Finset.sum_const_zero, add_zero]

end CrystallineSemistableComparison.Onto

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap IsProjOver)

def retractPt (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    Spec (CommRingCat.of (OK l K)) ⟶ PSpace (OK l K) 2 :=
  GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) (fun _ => 1)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

theorem retractPt_str (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    retractPt l K ≫ PSpace.str (OK l K) 2 = 𝟙 _ := by
  have hstr : ∀ (v : Fin (2 + 1) → OK l K) (hv : Ideal.span (Set.range v) = ⊤),
      GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) v hv ≫ PSpace.str (OK l K) 2 =
        spMap (RingHom.id (OK l K)) := by
    intro v hv
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, GlobalTheory.ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ v r
  rw [retractPt, hstr]
  simp [spMap]

theorem retract_pf : Retract := by
  intro l _ K _ M d hM hd
  let N : Model l K := ⟨pullback M.p (PSpace.str (OK l K) 2), pullback.fst _ _ ≫ M.p⟩
  have h2 : SmoothOfRelativeDimension 2 (pullback.fst M.p (PSpace.str (OK l K) 2)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 2)
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 2) _ _
      (GlobalTheory.Adelic.smoothOfRelativeDimension_pspace _ 2)
  have hN : SmoothOfRelativeDimension (d + 1 + 1) N.p := by
    have := h2
    have := hd
    have : SmoothOfRelativeDimension (2 + d) (pullback.fst M.p (PSpace.str (OK l K) 2) ≫ M.p) :=
      smoothOfRelativeDimension_comp 2 d _ _
    rw [show d + 1 + 1 = 2 + d by omega]
    exact this
  have hsm : Smooth N.p := SmoothOfRelativeDimension.smooth (d + 1 + 1) N.p
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  refine ⟨N, pullback.fst _ _, pullback.lift (𝟙 _) (M.p ≫ retractPt l K) ?_, rfl, pullback.lift_fst _ _ _,
    ⟨⟨?_, ϖ, hϖ, ?_⟩, hsm⟩, hN⟩
  · rw [Category.assoc, retractPt_str, Category.comp_id, Category.id_comp]
  · exact GlobalTheory.ProjSpace.isProjOver_pullback hproj (GlobalTheory.ProjSpace.isProjOver_pspace_str _ 2)
  · intro x
    exact GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth _ ϖ N.X N.p ⊤ x trivial inferInstance

end CrystallineSemistableComparison.Onto

end
end
