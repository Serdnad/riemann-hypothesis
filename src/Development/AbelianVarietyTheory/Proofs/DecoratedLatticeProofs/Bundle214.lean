module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  first | exact @GlobalTheory.fixes_latV_of_mem_grpOff | exact GlobalTheory.fixes_latV_of_mem_grpOff | (intros; apply GlobalTheory.fixes_latV_of_mem_grpOff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  first | exact @GlobalTheory.VacMove.vac_of_moves | exact GlobalTheory.VacMove.vac_of_moves | (intros; apply GlobalTheory.VacMove.vac_of_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)

theorem _root_.GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.glued_last_integral | exact GlobalTheory.FinPl.glued_last_integral | (intros; apply GlobalTheory.FinPl.glued_last_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_integralBasis_of_latticeAtPlace_stable : ∀ (D : D7) (n : ℕ) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin n → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) → (∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ) → (∃ m : ℕ, 0 < m ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) → (∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v)) → ∃ β β' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ (∀ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) := by
  exact @GlobalTheory.IwaPlace.FreeAt.exists_basis
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIdemFacts

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem algebraMap_pairA (α : Af D.host.F) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem placeIdem_mem_idAt {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {P : Pl D → Prop} (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  rw [algebraMap_pairA]
  exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => h0 w fun h => hw (h ▸ hP)) 1

theorem infPart_placeIdem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := hε
  exact TensorProduct.zero_tmul _ _

theorem placeIdem_mul {v v' : Pl D} {ε ε' : AF D.host.F} (hε : IsPlaceIdem D v ε) (hε' : IsPlaceIdem D v' ε')
    (h : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨α', rfl, -, h0'⟩ := hε'
  have hαα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α') = evalV D.host.F w 0
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      rw [h0' w h, mul_zero]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hαα]
  rfl

theorem idem_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k), cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (∀ (P : Pl D → Prop), P q.v → ∀ (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w →
        MxAt P w ∧ w.map (infPart D) = 0) ∧
      ∀ (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q' : SplitPt D k'),
        q.v ≠ q'.v → (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  intro D k _ _ _ _ q
  obtain ⟨ε, hε, heq⟩ := q.above
  refine ⟨by rw [map_add (f := _), cA_cA, add_comm], fun P hP m n w hw => ⟨fun i j => ?_, ?_⟩,
    fun k' _ _ _ _ q' hv => ?_⟩
  · rw [← hw i j, heq]
    exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt hε hP)
  · ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, ← hw i j, map_mul, heq, infPart_placeIdem hε, zero_mul]
  · obtain ⟨ε', hε', heq'⟩ := q'.above
    rw [heq, heq', ← map_mul, placeIdem_mul hε hε' hv, map_zero]

end GlobalTheory.PlaceIdemFacts

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ConjHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vecMul_jA_eq_zero (p : SplitPt D k) {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr = 0 := by
  have h0 : o.iAᴴ * HSpace.gram S₀ * o.iB = 0 := by
    have := congrArg Matrix.conjTranspose o.orth
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, gram_conjTranspose] using this
  have h1 : o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ) = 0 := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  funext l
  have h2 : ∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l =
      star ((o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ)) l) := by
    rw [Matrix.mulVec, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
  have h3 : ((fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr) l =
      (p.pr.comp (incA D)) (∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l) := by
    show ∑ i, (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) * (p.pr.comp (incA D)) (o.iA i l) = _

    rw [map_sum]
    simp only [map_mul]
  rw [h3, h2, h1, Pi.zero_apply, star_zero, map_zero]
  rfl

theorem sum_mul_star_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  have e1 : ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = vecB o ζ ⬝ᵥ star (HSpace.gram S₀ *ᵥ vecB o ζ) := rfl
  rw [e1, Matrix.star_mulVec, gram_conjTranspose, dotProduct_comm, ← Matrix.dotProduct_mulVec, vecB,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem sumFrame_dot (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (hsum : IsSumFrame o ζ α α₀)
    (x' : n ⊕ Fin 1 → k) :
    (α₀.b *ᵥ x') ⬝ᵥ (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
      x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
  have e2 : ((o.jA.map p.pr * α.b) *ᵥ (x' ∘ Sum.inl)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_jA_eq_zero]
    simp only [Matrix.zero_vecMul, zero_dotProduct]
  have e3 : ((replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) *ᵥ (x' ∘ Sum.inr)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
        x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
    rw [← sum_mul_star_eq]
    show ∑ i, (∑ j : Fin 1, (p.pr.comp (incA D)) (vecB o ζ i) * x' (Sum.inr j)) *
        (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) =
      x' (Sum.inr 0) * (p.pr.comp (incA D)) (∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i))

    rw [map_sum, Finset.mul_sum]
    simp only [Fin.sum_univ_one, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Matrix.fromCols_mulVec, add_dotProduct, e2, e3]
  exact zero_add _

theorem pair_eq (p : SplitPt D k) (S₀ : HSp D) (z : Fin S₀.rank → D.host.E) (c : AE D) (x : Fin S₀.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (HSpace.gram S₀ i j))) * (p.pr (cA D c) * p.pr (incA D (star (z j))))
      = p.pr (cA D c) * (x ⬝ᵥ fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ z) i)))) := by

  simp only [dotProduct, Finset.mul_sum, Matrix.mulVec, star_sum, map_sum, FrameLat.cA_incA, star_mul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conj_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hM hsum hlat c
  have hy : (fun r => cA D p.e * (c * incA D (vecB o ζ r))) =
      fun r => cA D (p.sec (p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))))) := by
    funext r
    have : p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))) = p.pr (cA D (c * incA D (vecB o ζ r))) := by
      simp only [map_mul, FrameLat.cA_incA]
    rw [this, p.sec_pr, map_mul, cA_cA]
  rw [hy, FrameLat.csec_mem_iff hM]
  constructor
  · intro H
    obtain ⟨x1, hx1l, hx1r⟩ : ∃ x1 : n ⊕ Fin 1 → k, x1 ∘ Sum.inl = 0 ∧ x1 (Sum.inr 0) = 1 :=
      ⟨Sum.elim 0 (fun _ => 1), Sum.elim_comp_inl _ _, rfl⟩
    have hx' : x1 ∈ lastKer Λ := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hx1l, hx1r]
      exact ⟨zero_mem _, one_mem _⟩
    have hx := H (α₀.b *ᵥ x1) ((hlat _).1 hx')
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum, hx1r, one_mul] at hx
    exact hx
  · intro H x hx
    have hxx : x = α₀.b *ᵥ (α₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
    rw [hxx] at hx ⊢
    have hl := ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer).1 ((hlat _).2 hx)).2
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum]
    convert mul_mem hl H using 1
    ring

end GlobalTheory.FinPl.ConjHalf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

theorem _root_.GlobalTheory.T.exists_padicCoordinates_of_degreeOne_splitPlace : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  first | exact @GlobalTheory.FinPl.SplitQT.exists_coord_padic | exact GlobalTheory.FinPl.SplitQT.exists_coord_padic | (intros; apply GlobalTheory.FinPl.SplitQT.exists_coord_padic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem mem_prime_iff_pr_inv_notMem {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt p.e P) (x : 𝓞 D.host.E) (hx : x ≠ 0) :
    x ∈ P.asIdeal ↔ p.pr (incA D ((x : D.host.E)⁻¹)) ∉ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr]
  exact h.2 x hx

theorem exists_denom_notMem_of_pr_int : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ a : D.host.E, p.pr (incA D a) ∈ 𝒪[k] →
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 D.host.E,
      algebraMap (𝓞 D.host.E) D.host.E c = algebraMap (𝓞 D.host.E) D.host.E s * a := by
  intro D k _ _ _ _ p P h a ha
  obtain ⟨n, ⟨d, hd⟩, hnd | hnd⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := D.host.E) a
  · exact ⟨d, hd, n, by rw [← hnd, mul_comm]⟩
  · have hd' : d ∉ P.asIdeal := hd
    have hd0 : d ≠ 0 := fun h0 => hd' (h0 ▸ P.asIdeal.zero_mem)
    have hnd' : a * (n : D.host.E) = (d : D.host.E) := hnd
    have hdE : (d : D.host.E) ≠ 0 := fun h0 => hd0 (RingOfIntegers.coe_eq_zero_iff.mp h0)
    have hnE : (n : D.host.E) ≠ 0 := fun h0 => hdE (by rw [← hnd', h0, mul_zero])
    have hn0 : n ≠ 0 := fun h0 => hnE (by rw [h0]; rfl)
    refine ⟨n, fun hn => ?_, d, by rw [mul_comm]; exact hnd.symm⟩
    have h1 := (mem_prime_iff_pr_inv_notMem p P h n hn0).1 hn
    have h2 := not_not.1 (mt (mem_prime_iff_pr_inv_notMem p P h d hd0).2 hd')
    apply h1
    have h3 : (n : D.host.E)⁻¹ = a * (d : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hdE, ← hnd', mul_comm a, inv_mul_cancel_left₀ hnE]
    rw [h3, map_mul, map_mul]
    exact mul_mem ha h2

end GlobalTheory.PhiOneVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

open IsDedekindDomain NumberField

namespace GlobalTheory.LocMod.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

theorem splitPt_v_eq_under {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.L2.NTheta.IsIdemAt q.e P) : q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, hsum⟩ := q.above
  have hc0 : Φ (cA D q.e) P = 0 := by
    have := ev_mul (Φ := Φ) q.e (cA D q.e) P
    rw [q.split.2.1, ev_zero, hd.2.1, one_mul] at this
    exact this.symm
  have h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0 := by
    rw [← hsum, ev_add, hd.2.1, hc0, add_zero]; exact one_ne_zero
  by_contra hne
  exact h1 ((place_comp hΦ hε).2.2 P (Ne.symm hne))

end GlobalTheory.LocMod.LevelPlaces

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem alg_int_ev (c : D.host.F) : ∀ᶠ w in Filter.cofinite,
    algebraMap D.host.F (Fv D.host.F w) c ∈ (w : Pl D).adicCompletionIntegers D.host.F :=
  (algebraMap D.host.F (Af D.host.F) c).2

theorem repr_tmul_loc (w : Pl D) (x : Fv D.host.F w) (e : D.host.E) (i : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (x ⊗ₜ[D.host.F] e) i =
      x * algebraMap D.host.F (Fv D.host.F w) ((Module.finBasis D.host.F D.host.E).repr e i) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem int_coords_ev : ∀ᶠ w in Filter.cofinite, ∀ z ∈ intAE D, ∀ i,
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
      (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z) i ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ w in Filter.cofinite, ∀ i j,
      algebraMap D.host.F (Fv D.host.F w) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) i) ∈
        (w : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact alg_int_ev _
  filter_upwards [hev] with w hw
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, o, rfl⟩ := hy
    intro i
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [hc, repr_tmul_loc]
    refine mul_mem (hα w) ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl

    rw [ho, map_sum, Finset.sum_apply', map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hw i j) _
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  | neg x _ hx => intro i; rw [map_neg, map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem sum_repr_tmul (w : Pl D) (y : Fv D.host.F w ⊗[D.host.F] D.host.E) :
    ∑ i, (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr y i ⊗ₜ[D.host.F]
      (Module.finBasis D.host.F D.host.E) i = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem glue : ∀ (D : D7) (a : Pl D → AE D), (∀ x, a x ∈ idAt D (· = x)) →
    (∃ T : Finset (Pl D), ∀ x ∉ T, a x ∈ intAt D (· = x)) →
    ∃ s : AE D, infPart D s = 0 ∧ ∀ x, s - a x ∈ idOff D (· = x) := by
  intro D a _ ⟨T, hT⟩
  classical
  set b := Module.finBasis D.host.F D.host.E
  let c : Fin (Module.finrank D.host.F D.host.E) → (w : Pl D) → Fv D.host.F w := fun i w =>
    (Algebra.TensorProduct.basis (Fv D.host.F w) b).repr (compAt D w (a w)) i
  have hc : ∀ i, ∀ᶠ w in Filter.cofinite, c i w ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
    intro i
    filter_upwards [int_coords_ev (D := D), T.finite_toSet.compl_mem_cofinite] with w hw hwT
    exact hw _ (hT w hwT).2 i
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun i => RestrictedProduct.mk (c i) (hc i)
  refine ⟨∑ i, pairA D.host.F 0 (C i) ⊗ₜ[D.host.F] b i, ?_, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      simp only [infPart_pair, Finset.sum_const_zero]
  · unfold idOff
    refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
    obtain ⟨w, rfl⟩ := w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, sub_eq_zero]
    simp only [compAt_pair]
    exact sum_repr_tmul w (compAt D w (a w))

end GlobalTheory.FinPlLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  first | exact @GlobalTheory.Unf.CutChar.conjBessel_isTh | exact GlobalTheory.Unf.CutChar.conjBessel_isTh | (intros; apply GlobalTheory.Unf.CutChar.conjBessel_isTh <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  first | exact @GlobalTheory.Unf.exists_central_ne | exact GlobalTheory.Unf.exists_central_ne | (intros; apply GlobalTheory.Unf.exists_central_ne <;> assumption)
end
