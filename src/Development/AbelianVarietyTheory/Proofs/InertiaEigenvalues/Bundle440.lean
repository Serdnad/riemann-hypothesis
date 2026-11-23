module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle366
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle423
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle426
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mul {Γ k : Type} [Group Γ] [CommRing k] {r : ℕ} (σ : Γ →* GL (Fin r) k) (g h : Γ) :
    mat σ g * mat σ h = mat σ (g * h) := by
  simp [mat]

theorem span_eq_top_of_trace_eq {Γ k : Type} [Group Γ] [Field k] {r : ℕ}
    (σ ρ : Γ →* GL (Fin r) k) (ht : ∀ g, (mat σ g).trace = (mat ρ g).trace)
    (h : Submodule.span k (Set.range (mat ρ)) = ⊤) :
    Submodule.span k (Set.range (mat σ)) = ⊤ := by
  classical
  let L := Finsupp.linearCombination k (mat σ)
  let L0 := Finsupp.linearCombination k (mat ρ)
  have hker : LinearMap.ker L ≤ LinearMap.ker L0 := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h1 : ∀ y : Γ, (L0 c * mat ρ y).trace = 0 := by
      intro y
      have e1 : (L c * mat σ y).trace = 0 := by rw [hc]; simp
      rw [← e1]
      simp only [L, L0, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Matrix.smul_mul,
        Matrix.trace_sum, Matrix.trace_smul, mat_mul, ht]
    have h2 : ∀ Y : Matrix (Fin r) (Fin r) k, (L0 c * Y).trace = 0 := by
      intro Y
      have hY : Y ∈ Submodule.span k (Set.range (mat ρ)) := h ▸ Submodule.mem_top
      induction hY using Submodule.span_induction with
      | mem Y hY => obtain ⟨y, rfl⟩ := hY; exact h1 y
      | zero => simp
      | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.trace_add, hY, hZ, add_zero]
      | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.trace_smul, hY, smul_zero]
    ext p q
    have := h2 (Matrix.single q p 1)
    simpa [Matrix.trace_mul_single] using this
  have hL0 : LinearMap.range L0 = ⊤ := by
    rw [Finsupp.range_linearCombination]; exact h
  let f : LinearMap.range L →ₗ[k] Matrix (Fin r) (Fin r) k :=
    ((LinearMap.ker L).liftQ L0 hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[k] _)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_liftQ, hL0]
  have h3 := LinearMap.finrank_range_le f
  rw [hf, finrank_top] at h3
  have h4 : LinearMap.range L = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h3)
  rw [← Finsupp.range_linearCombination]; exact h4

theorem absIrrSub_of_span_eq_top {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (hr : 0 < r)
    (σ : Γ →* GL (Fin r) k) (h : Submodule.span k (Set.range (mat σ)) = ⊤) : AbsIrrSub σ ⊤ := by
  refine GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (algebraMap k (AlgebraicClosure k)) hr σ fun W hW => ?_
  refine GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (mat σ) h W fun g x hx => ?_
  have e : (mat σ g).map (algebraMap k (AlgebraicClosure k)) =
      ((mapRep (algebraMap k (AlgebraicClosure k)) σ g : GL (Fin r) (AlgebraicClosure k)) :
        Matrix (Fin r) (Fin r) (AlgebraicClosure k)) := by
    ext p q; simp [mat, mapRep]
  rw [e]; exact hW g x hx

theorem pos_of_absIrrSub {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (σ : Γ →* GL (Fin r) k)
    (h : AbsIrrSub σ ⊤) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    exact absurd (Subsingleton.elim _ _) h.1
  · exact h0

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (σ : Γ →* GL (Fin k) A) (g : Γ) : mat (mapRep f σ) g = (mat σ g).map f := by
  ext p q; simp [mat, mapRep]

theorem charpoly_eq_of_isHeckeGalois (hC : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep) (π : D.nd.X i)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0) (g : GE D.nd) :
    (mat (rep π) g).charpoly = (mat r0 g).charpoly := by
  classical
  let rep' := Function.update rep π r0
  have hr' : GoodR D.nd i rep' := by
    intro y
    by_cases hy : y = π
    · subst hy; simpa [rep'] using hr0
    · simpa [rep', Function.update_of_ne hy] using hr y
  obtain ⟨Pm, hPm⟩ := GlobalTheory.PointRepConj.main hC D.nd i rep rep' hr hr' π
  have h1 := hPm g
  have h2 : (rO D.nd i rep' π g) = mat r0 g := by simp [rep', rO, mat]
  rw [h2] at h1
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have h1' : (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (mat (rep π) g).map (toK D.nd i) =
      (mat r0 g).map (toK D.nd i) * (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := h1
  have h3 : (mat (rep π) g).map (toK D.nd i) =
      ((Pm⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix _ _ _) * (mat r0 g).map (toK D.nd i) *
        (Pm : Matrix _ _ _) := by
    rw [Matrix.mul_assoc, ← h1', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [h3]
  have := Matrix.charpoly_units_conj (Pm⁻¹) ((mat r0 g).map (toK D.nd i))
  rwa [← Matrix.coe_units_inv, inv_inv] at this

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.LocGL

section FiniteGroup

variable {G V W X Y : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ W]

theorem charIdem_apply (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v =
      ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v := by
  simp [charIdem, LinearMap.sum_apply]

theorem map_charIdem {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : V) : φ (charIdem σ τ v) = charIdem σ' τ (φ v) := by

  simp only [charIdem_apply, map_smul, map_sum, φ.isIntertwining]

theorem charIdem_apply_rep (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) (v : V) :
    charIdem σ τ (σ h v) = σ h (charIdem σ τ v) := by

  simp only [charIdem_apply, map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  have e : LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) = LinearMap.trace ℂ W (τ g⁻¹) := by
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group]
    exact τ.char_conj g⁻¹ h
  show _ = LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) • σ (h * g * h⁻¹) (σ h v)
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem commute_charIdem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) :
    Commute (charIdem σ τ) (σ h) := LinearMap.ext (charIdem_apply_rep σ τ h)

def coeffMap (σ : Representation ℂ G V) (τ : Representation ℂ G W) (ℓ : Module.Dual ℂ W) (v : V) :
    τ.IntertwiningMap σ where
  toLinearMap := ∑ g : G, (ℓ ∘ₗ τ g⁻¹).smulRight (σ g v)
  isIntertwining' h := LinearMap.ext fun w => by

    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
    simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem charIdem_mem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v ∈ isotypic σ τ := by
  classical
  let b := Module.finBasis ℂ W
  have key : ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v = ∑ i, coeffMap σ τ (b.coord i) v (b i) := by
    have : ∀ i, coeffMap σ τ (b.coord i) v (b i) = ∑ g : G, b.repr (τ g⁻¹ (b i)) i • σ g v := fun i => by
      show (∑ g : G, (b.coord i ∘ₗ τ g⁻¹).smulRight (σ g v)) (b i) = _
      simp [LinearMap.sum_apply]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  rw [charIdem_apply, key]
  exact (isotypic σ τ).toSubmodule.smul_mem _ (Submodule.sum_mem _ fun i _ => apply_mem_isotypic _ _)

theorem charIdem_self {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) : charIdem τ τ = 1 := by
  have := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
    ⟨charIdem τ τ, fun g => commute_charIdem τ τ g⟩
  have h1 : charIdem τ τ = c • (1 : Module.End ℂ W) :=
    LinearMap.ext fun w => (congrArg (fun f : τ.IntertwiningMap τ => f w) hc).symm
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have ho := Representation.char_orthonormal τ τ
  rw [if_pos ⟨.refl _⟩, Nat.card_eq_fintype_card] at ho
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 : LinearMap.trace ℂ W (charIdem τ τ) = Module.finrank ℂ W := by

    simp only [charIdem, map_smul, map_sum, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
    refine (congrArg _ (Eq.trans ?_ ho)).trans (mul_one _)
    exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)
  rw [h1, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
  rw [h1, mul_right_cancel₀ hd (h2.trans (one_mul _).symm), one_smul]

theorem charIdem_of_mem {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) {v : V}
    (hv : v ∈ isotypic σ τ) : charIdem σ τ v = v := by
  refine Submodule.iSup_induction _ (motive := fun v => charIdem σ τ v = v) hv ?_ (map_zero _) fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact (map_charIdem f τ w).symm.trans (by rw [charIdem_self hτ]; rfl)
  · rw [map_add (f := _), hx, hy]

end FiniteGroup

section Compact

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}

theorem map_idem (hπ : IsSmooth π) (hσ : IsSmooth σ) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) (v : V) :
    f (idem hπ hH v) = idem hσ hH (f v) := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  rw [idem_eq_cosetSum hπ hH U hU, idem_eq_cosetSum hσ hH U fun u hu => by rw [← f.isIntertwining, hU u hu]]

  simp only [map_smul, map_sum, f.isIntertwining]

theorem map_idem_of_mem (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : f (idem hπ hH v) = f v := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [idem_eq_cosetSum hπ hH U hU]

  simp only [map_smul, map_sum, f.isIntertwining]
  rw [Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_mem_fixed_map_eq (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : ∃ u ∈ fixed π H, f u = f v :=
  ⟨_, idem_mem hπ hH v, map_idem_of_mem hπ hH f hv⟩

theorem map_fixed_of_surjective (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) {f : π.IntertwiningMap σ}
    (hf : Function.Surjective f) : (fixed π H).map f.toLinearMap = fixed σ H := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_fixed.2 fun u hu => by rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  · obtain ⟨v, rfl⟩ := hf w
    exact exists_mem_fixed_map_eq hπ hH f hw

end Compact

section LevelZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W}
  {ρ : Representation ℂ (GL n k) X}

theorem levelZeroMap_injective {f : π.IntertwiningMap σ} (hf : Function.Injective f) :
    Function.Injective (levelZeroMap f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem levelZeroMap_surjective (hπ : IsSmooth π) {f : π.IntertwiningMap σ} (hf : Function.Surjective f) :
    Function.Surjective (levelZeroMap f) := by
  rintro ⟨x, hx⟩
  obtain ⟨v, rfl⟩ := hf x
  obtain ⟨u, hu, h⟩ := exists_mem_fixed_map_eq hπ (levelPre_bot (k := k) (n := n) ▸ isCompact_levelPre ⊥) f hx
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

end LevelZero

end GlobalTheory.LocGL
end
end

section

noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.IwahoriFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [Fintype n] in
theorem one_same (e : (Σ a, m a) ≃ n) (a : α) (i j : m a) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j := by
  simp [Matrix.one_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem one_ne (e : (Σ a, m a) ≃ n) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 :=
  Matrix.one_apply_ne fun e' => h (congrArg Sigma.fst (e.injective e'))

theorem exists_jPlus_mul_KOne (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x := by
  obtain ⟨h1, h3⟩ := mem_proRad.1 hg
  obtain ⟨h1, h2⟩ := mem_parahoric.1 h1
  let U : Matrix n n k := Matrix.of fun i j => if blk e i < blk e j then g.val i j else (1 : Matrix n n k) i j
  have hU : StepData.MaxM (U - g.val) := by
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [U, Matrix.sub_apply, Matrix.of_apply, blk_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · rw [if_neg (lt_irrefl a), one_same, Valuation.map_sub_swap]
      exact h3 a i j
    · rw [if_neg h.not_gt, one_ne e h.ne', zero_sub, Valuation.map_neg]
      exact h2 a b i j h
  obtain ⟨x, hx, hgx⟩ := StepData.exists_mul_KOne h1 hU
  refine ⟨g * x, ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j h => ?_, fun a i j => ?_⟩,
    mul_mem h1 (StepData.KOne_le_KO hx)⟩, x⁻¹, inv_mem hx, by simp⟩
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg h.not_gt, one_ne e h.ne']
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg (lt_irrefl a), one_same]

theorem exists_KOne_mul_jPlus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  exact ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hu.2) x).1 hx, u, hu, by simp⟩

theorem proRad_eq_sup (e : (Σ a, m a) ≃ n) : proRad k e = KOne k n ⊔ jPlus k e := by
  refine le_antisymm (fun g hg => ?_) (sup_le (KOne_le_proRad e) (jPlus_le_proRad e))
  obtain ⟨x, hx, u, hu, rfl⟩ := exists_KOne_mul_jPlus e hg
  exact Subgroup.mul_mem_sup hx hu

theorem exists_mul_mem_parab (e : (Σ a, m a) ≃ n) {x : GL n k} (hx : x ∈ KOne k n) :
    ∃ c ∈ jMinus k e, x * c ∈ parab k e := by
  have hx' := StepData.mem_KOne.1 hx
  have hA : ∀ a : α, ∃ y ∈ KOne k n, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix n n k) i l := fun a =>
    StepData.exists_mem_KOne fun i l => by
      simp only [Matrix.sub_apply, Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := StepData.exists_mem_KOne (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => StepData.mem_KOne.1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix n n k) i l) * c.val l j =
      (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix n n k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩, hc⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem exists_jLevi_mul_jPlus (e : (Σ a, m a) ≃ n) {p : GL n k} (hp : p ∈ parab k e) (h : p ∈ KOne k n) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, p = d * u := by
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k e ⟨p, hp⟩
  have hd : leviEmb k e (leviProj k e ⟨p, hp⟩) ∈ jLevi k e :=
    ⟨_, fun a _ => StepData.mem_KOne.2 fun i j => by
      have := StepData.mem_KOne.1 h (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at this
      exact this, rfl⟩
  refine ⟨_, hd, u, ⟨hu, ?_⟩, hpu⟩
  rw [(inv_mul_eq_iff_eq_mul.2 hpu).symm]
  exact StepData.KOne_le_KO (mul_mem (inv_mem (jLevi_le_KOne e hd)) h)

theorem conj_mem_jPlus (e : (Σ a, m a) ≃ n) {d u : GL n k} (hd : d ∈ jLevi k e) (hu : u ∈ jPlus k e) :
    d * u * d⁻¹ ∈ jPlus k e := by
  have h := StepData.KOne_le_KO (jLevi_le_KOne e hd)
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e g) u).1 hu.1,
    (KO k n).mul_mem ((KO k n).mul_mem h hu.2) ((KO k n).inv_mem h)⟩

theorem plus_levi_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab e hx
  obtain ⟨d, hd, v, hv, h⟩ := exists_jLevi_mul_jPlus e hp (mul_mem hx hc.2)
  refine ⟨_, mul_mem hu (conj_mem_jPlus e hd hv), d, hd, c⁻¹, inv_mem hc, ?_⟩
  rw [eq_mul_inv_of_mul_eq h]
  group

theorem levi_plus_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨d, hd, _, conj_mem_jPlus e (inv_mem hd) hu, c, hc, by group⟩

end GlobalTheory.LocGL.IwahoriFactor
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  first | exact @GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | exact GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | (intros; apply GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.emptyPiTensor_isSubquotient_jacquetModule_degreeZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  first | exact @GlobalTheory.piTensor_isSubquotient_jac_degZero | exact GlobalTheory.piTensor_isSubquotient_jac_degZero | (intros; apply GlobalTheory.piTensor_isSubquotient_jac_degZero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.dualSelmerClass_from_coeffsKilledBy_mul : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  first | exact @GlobalTheory.DualSub.dualSel_of_smul_cob | exact GlobalTheory.DualSub.dualSel_of_smul_cob | (intros; apply GlobalTheory.DualSub.dualSel_of_smul_cob <;> assumption)
end
