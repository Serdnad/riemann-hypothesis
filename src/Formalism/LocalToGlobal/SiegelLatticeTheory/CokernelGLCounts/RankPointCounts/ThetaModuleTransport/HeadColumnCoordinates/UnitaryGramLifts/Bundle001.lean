module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.GamConIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section DuU

theorem firstProj_conj_eq_secondProj (x : E) : ph1 g ((M.L.cj : E →+* E) x) = ph2 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_conj_eq_firstProj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem firstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  simp [firstProj_apply]

theorem ph2_algebraMap_eq (a : F) : ph2 g (algebraMap F E a) = a := by
  simp [secondProj_apply]

theorem firstProj_corner (a b : Fin (r + 1)) (X : E) : ph1 g (cor r a b X) = cor r a b (ph1 g X) := by
  unfold cor; split_ifs <;> simp

theorem firstProj_iotaOne_inl (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inl a) : M.L.O) : E) = ph1 g (l a : E) := by
  simp [iota1, firstProj_apply]

theorem firstProj_iotaOne_inr (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inr a) : M.L.O) : E) = (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) := by
  simp [iota1, firstProj_apply, secondProj_apply]

theorem firstProj_conj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((M.L.cj : E →+* E) ((iota2 hs l i : M.L.O) : E)) = ph1 g ((iota1 hs l i : M.L.O) : E) := by
  simp [iota2, firstProj_apply, g.e_cj, M.L.cj_cj]

theorem duU_formG_sub (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y W - formG O cj qi Z T T' Y W' =
      ∑ i, (Y i : E) * (Matrix.mulVec (gramG cj qi Z T T')⁻¹ fun j => cj (W j) - cj (W' j)) i := by
  unfold formG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, mul_assoc]

theorem firstProj_sum_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (c : Ix r → E) :
    ph1 g (∑ i, ((iota1 hs l i : M.L.O) : E) * c i) =
      ∑ a, ph1 g (l a : E) * ph1 g (c (Sum.inl a)) +
        ∑ a, (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) * ph1 g (c (Sum.inr a)) := by

  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, firstProj_iotaOne_inl, firstProj_iotaOne_inr]

theorem duU_sum_single1 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) * f b = ph1 g (x : E) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem duU_sum_single2 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, (ph2 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) - ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E)) / (g.q : F) * f b =
      (ph2 g (x : E) - ph1 g (x : E)) / (g.q : F) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem ph1_mem_integers_of_mem_O {y : E} (hy : y ∈ M.L.O) : ph1 g y ∈ 𝒪[F] := by
  have hidem : (g.e.symm (1, 0) : E) * g.e.symm (1, 0) = g.e.symm (1, 0) := by
    rw [← map_mul]
    simp
  have hu : y * g.e.symm (1, 0) ∈ M.L.O := M.L.O.mul_mem hy (idem_mem_O M.L hidem)
  have hw : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) ∈ M.L.O :=
    M.L.O.add_mem hu (cj_mem_O M.L hu)
  have heq : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) = algebraMap F E (ph1 g y) := by
    apply g.e.injective
    refine Prod.ext ?_ ?_ <;> simp [g.e_cj, firstProj_apply]
  haveI : Nontrivial E := g.e.toEquiv.nontrivial
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (heq ▸ hw)

theorem duU_c_int (hs : M.split = some g) (c : Ix r → E)
    (h : ∀ l : Fin (r + 1) → M.R, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O) :
    ∀ i, ph1 g (c i) ∈ 𝒪[F] := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)
  intro i
  rcases i with a | a
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a 1))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa using h1
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a (q2 hs)))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa [firstProj_apply, secondProj_apply, embedding_uniformizer hs, hq] using h1

theorem duU_sum_cor (a : Fin (r + 1)) (X : F) (f : Fin (r + 1) → F) :
    ∑ b, cor r a b X * f b = if a = Fin.last r then X * f (Fin.last r) else 0 := by
  unfold cor
  split_ifs with ha
  · simp [ha, ite_mul]
  · simp [ha]

theorem firstProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      ph2 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

end DuU

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA7

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E} (q : E)

theorem gamTup_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (Y Y' Y'' : Ix r → O) :
    ((Submodule.Quotient.mk (scPhi h Y) : DDg O cj qi (Zh * dlast r α) T T'),
      (Submodule.Quotient.mk (scPhi h Y'') : DDg O cj qi (Zh * dlast r α) T T'),
      (((scPhi h Y (Sum.inl (Fin.last r)) : O) : E),
        lamStarC cj (Zh * dlast r α) (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O))),
      (lamC (Zh * dlast r α) (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)),
        ((scPhi h Y' (Sum.inl (Fin.last r)) : O) : E) + q * (scPhi h Y' (Sum.inr (Fin.last r)) : O))) =
    scTr h Zh ((Submodule.Quotient.mk Y : DDg O cj qi Zh T T'), (Submodule.Quotient.mk Y'' : DDg O cj qi Zh T T'),
      ((Y (Sum.inl (Fin.last r)) : E), lamStarC cj Zh (fun b => (Y (Sum.inl b) : E) + q * Y (Sum.inr b))),
      (lamC Zh (fun a => (Y' (Sum.inl a) : E)), (Y' (Sum.inl (Fin.last r)) : E) + q * Y' (Sum.inr (Fin.last r)))) := by
  have hc : (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O)) =
      fun b => cj (if b = Fin.last r then α else 1) * ((Y (Sum.inl b) : E) + q * Y (Sum.inr b)) :=
    funext (phi_comb h q hq Y)
  have hl : (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)) = fun a => (Y' (Sum.inl a) : E) := funext (phi_inl h Y')
  have hz := phi_comb h q hq Y' (Fin.last r)
  simp only [if_true] at hz
  simp only [scTr, scBar_mk, psiD, Prod.mk.injEq]
  refine ⟨trivial, trivial, ⟨phi_inl h Y _, ?_⟩, ?_, hz⟩
  · rw [hc, lamStarC_scale h Zh]
  · rw [hl, lamC_scale h Zh]

theorem gamRC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    GamRC O cj q qi (Zh * dlast r α) T T' = scTr h Zh '' GamRC O cj q qi Zh T T' := by
  ext p
  constructor
  · rintro ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
    have hc := (gamCon_iff q h hqO ((scPhi h).symm Y) ((scPhi h).symm Y') ((scPhi h).symm Y'')).2
    simp only [LinearEquiv.apply_symm_apply] at hc
    obtain ⟨d1, d2, d3⟩ := hc ⟨c1, c2, c3⟩
    refine ⟨_, ⟨(scPhi h).symm Y, (scPhi h).symm Y', (scPhi h).symm Y'', d1, d2, d3, rfl⟩, ?_⟩
    rw [← gamTup_scale q h hq]
    simp only [LinearEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨Y, Y', Y'', c1, c2, c3, rfl⟩, rfl⟩
    obtain ⟨d1, d2, d3⟩ := (gamCon_iff q h hqO Y Y' Y'').1 ⟨c1, c2, c3⟩
    exact ⟨scPhi h Y, scPhi h Y', scPhi h Y'', d1, d2, d3, (gamTup_scale q h hq Zh Y Y' Y'').symm⟩

theorem scBar_symm_mk (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y : Ix r → O) :
    (scBar h Zh).symm (Submodule.Quotient.mk Y) = Submodule.Quotient.mk ((scPhi h).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, scBar_mk, LinearEquiv.apply_symm_apply]

def scConj (h : ScHyp O cj qi T T' α) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') ≃
      (DDg O cj qi (Zh₁ * dlast r α) T T' ≃ₗ[O] DDg O cj qi (Zh₂ * dlast r α) T T') where
  toFun θ := (scBar h Zh₁).symm.trans (θ.trans (scBar h Zh₂))
  invFun θ' := (scBar h Zh₁).trans (θ'.trans (scBar h Zh₂).symm)
  left_inv θ := by ext x; simp
  right_inv θ' := by ext x; simp

theorem thetaGC_scale_iff (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (θ : DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') :
    θ ∈ ThetaGC O cj q qi Zh₁ Zh₂ T T' ↔
      scConj h Zh₁ Zh₂ θ ∈ ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T' := by
  have hθ' : ∀ Y : Ix r → O, scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) =
      scBar h Zh₂ (θ (Submodule.Quotient.mk Y)) := by
    intro Y
    show scBar h Zh₂ (θ ((scBar h Zh₁).symm (Submodule.Quotient.mk (scPhi h Y)))) = _
    rw [scBar_symm_mk, LinearEquiv.symm_apply_apply]
  have hcomm : (fun p => (scConj h Zh₁ Zh₂ θ p.1, scConj h Zh₁ Zh₂ θ p.2.1, p.2.2.1, p.2.2.2)) ∘ scTr h Zh₁ =
      scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) := by
    funext p
    simp only [Function.comp_apply, scTr]
    show (scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.1))),
      scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.2.1))), _) = _
    simp only [LinearEquiv.symm_apply_apply]
  unfold ThetaGC
  simp only [Set.mem_setOf_eq]
  rw [gamRC_scale q h hq hqO Zh₁, gamRC_scale q h hq hqO Zh₂, Set.image_image]
  rw [show (fun p => (scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).1, scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).2.1,
      (scTr h Zh₁ p).2.2.1, (scTr h Zh₁ p).2.2.2)) = scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) from
      hcomm, Set.image_comp, (Set.image_injective.2 (scTr_inj h Zh₂)).eq_iff]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hF Y W Y₂ W₂ hY hW
    have eY : θ (Submodule.Quotient.mk ((scPhi h).symm Y)) = Submodule.Quotient.mk ((scPhi h).symm Y₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hY
    have eW : θ (Submodule.Quotient.mk ((scPhi h).symm W)) = Submodule.Quotient.mk ((scPhi h).symm W₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hW
    have := hF _ _ _ _ eY eW
    rw [← formG_scale h Zh₂, ← formG_scale h Zh₁] at this
    simpa only [LinearEquiv.apply_symm_apply] using this
  · intro hF Y W Y₂ W₂ hY hW
    have eY : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) = Submodule.Quotient.mk (scPhi h Y₂) := by
      rw [hθ', hY, scBar_mk]
    have eW : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h W)) = Submodule.Quotient.mk (scPhi h W₂) := by
      rw [hθ', hW, scBar_mk]
    have := hF _ _ _ _ eY eW
    rwa [formG_scale h Zh₂, formG_scale h Zh₁] at this

theorem card_thetaGC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Nat.card (ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T') = Nat.card (ThetaGC O cj q qi Zh₁ Zh₂ T T') :=
  (Nat.card_congr ((scConj h Zh₁ Zh₂).subtypeEquiv (thetaGC_scale_iff q h hq hqO Zh₁ Zh₂))).symm

end ScaleA7

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
