module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

@[expose] public section

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.T.UnitaryGeneratorRelations

variable {K : Type} [Field K] [CharZero K] {Δ : K}

private def om (K : Type) [Field K] (Δ : K) : Lsq K Δ := ⟨0, 1⟩

private theorem star_om : star (om K Δ) = - om K Δ := by
  ext <;> simp [om]

private theorem om_om (v : Fin 3 → Lsq K Δ) : om K Δ • om K Δ • v = Δ • v := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ext <;> simp [om]

private theorem star_smulK (r : K) (z : Lsq K Δ) : star (r • z) = r • star z := by
  ext <;> simp

private def S (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) : (Fin 3 → Lsq K Δ) →ₗ[K] (Fin 3 → Lsq K Δ) where
  toFun v := B *ᵥ star v
  map_add' x y := by rw [star_add, mulVec_add]
  map_smul' r x := by
    have : star (r • x) = r • star x := by
      funext i
      exact star_smulK r (x i)
    rw [this, RingHom.id_apply, mulVec_smul]

private theorem S_apply (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B v = B *ᵥ star v := rfl

private theorem star_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ) :
    star (M *ᵥ v) = M.map star *ᵥ star v := by
  funext i
  simp [mulVec, dotProduct, star_sum, mul_comm]

private theorem S_S {B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : B * B.map star = 1) (v) : S B (S B v) = v := by
  rw [S_apply, S_apply, star_mulVec', star_star, mulVec_mulVec, h, one_mulVec]

private theorem S_om (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B (om K Δ • v) = - (om K Δ • S B v) := by
  have e : star (om K Δ • v) = -(om K Δ • star v) := by
    funext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, star_mul', star_om]
    ring
  rw [S_apply, S_apply, e, mulVec_neg, mulVec_smul]

end UpperTheory.V.T.UnitaryGeneratorRelations

open UpperTheory.V.T.UnitaryGeneratorRelations in
theorem UpperTheory.exists_isUnit_det_mul_map_star_eq_of_unitary :
    ∀ (K : Type) [Field K] [CharZero K] (Δ : K), Δ ≠ 0 → ∀ B : Matrix (Fin 3) (Fin 3) (Lsq K Δ), B * B.map star = 1 →
        ∃ Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ), IsUnit Q.det ∧ B * Q.map star = Q := by
  intro K _ _ Δ hΔ B hB
  have dec : ∀ v : Fin 3 → Lsq K Δ, ∃ w1 w2, S B w1 = w1 ∧ S B w2 = w2 ∧ v = w1 + om K Δ • w2 := by
    intro v
    refine ⟨(1/2 : K) • (v + S B v), (1/(2*Δ) : K) • om K Δ • (v - S B v), ?_, ?_, ?_⟩
    · rw [map_smul, map_add (f := _), S_S hB, add_comm]
    · rw [map_smul, S_om, map_sub, S_S hB, ← smul_neg, neg_sub]
    · rw [smul_comm (om K Δ) (1/(2*Δ) : K), om_om, smul_smul]
      have h2 : 1/(2*Δ) * Δ = (1/2 : K) := by field_simp
      rw [h2, ← smul_add]
      module
  have uniq : ∀ w1 w2 : Fin 3 → Lsq K Δ, S B w1 = w1 → S B w2 = w2 → w1 + om K Δ • w2 = 0 → w1 = 0 ∧ w2 = 0 := by
    intro w1 w2 h1 h2 h
    have hs : w1 - om K Δ • w2 = 0 := by
      have := congrArg (S B) h
      rwa [map_add, S_om, h1, h2, map_zero, ← sub_eq_add_neg] at this
    have e1 : w1 = 0 := by
      have : (2 : K) • w1 = 0 := by rw [two_smul]; linear_combination (exp := 1) h + hs
      simpa using this
    refine ⟨e1, ?_⟩
    rw [e1, zero_add] at h
    have : Δ • w2 = 0 := by rw [← om_om, h, smul_zero]
    exact (smul_eq_zero.mp this).resolve_left hΔ
  have hV : Module.finrank K (Fin 3 → Lsq K Δ) = 6 := by
    rw [Module.finrank_pi_fintype, Module.finrank_eq_card_basis (QuadraticAlgebra.basis Δ 0)]
    simp
  let W : Submodule K (Fin 3 → Lsq K Δ) := LinearMap.ker (S B - LinearMap.id)
  have memW : ∀ w, w ∈ W ↔ S B w = w := by
    intro w
    simp [W, sub_eq_zero]
  let f : (W × W) →ₗ[K] (Fin 3 → Lsq K Δ) := W.subtype.coprod (om K Δ • W.subtype)
  have fapp : ∀ p : W × W, f p = (p.1 : Fin 3 → Lsq K Δ) + om K Δ • (p.2 : Fin 3 → Lsq K Δ) := fun p => rfl
  have fbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      rw [fapp] at hp
      obtain ⟨a, b⟩ := uniq _ _ ((memW _).mp p.1.2) ((memW _).mp p.2.2) hp
      exact Prod.ext (Subtype.ext a) (Subtype.ext b)
    · intro v
      obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
      exact ⟨(⟨w1, (memW _).mpr h1⟩, ⟨w2, (memW _).mpr h2⟩), rfl⟩
  have h3 : Module.finrank K W = 3 := by
    have := (LinearEquiv.ofBijective f fbij).finrank_eq
    rw [Module.finrank_prod, hV] at this
    omega
  let bW := Module.finBasisOfFinrankEq K W h3
  have inW : ∀ j, S B (bW j : Fin 3 → Lsq K Δ) = bW j := fun j => (memW _).mp (bW j).2
  let Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun i j => (bW j : Fin 3 → Lsq K Δ) i
  have span : ∀ w (hw : w ∈ W), w = ∑ j, (bW.repr ⟨w, hw⟩ j) • (bW j : Fin 3 → Lsq K Δ) := by
    intro w hw
    have := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  refine ⟨Q, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
    have s1 := span w1 ((memW _).mpr h1)
    have s2 := span w2 ((memW _).mpr h2)
    set c := bW.repr ⟨w1, (memW _).mpr h1⟩
    set d := bW.repr ⟨w2, (memW _).mpr h2⟩
    refine ⟨fun j => algebraMap K (Lsq K Δ) (c j) + om K Δ * algebraMap K (Lsq K Δ) (d j), ?_⟩
    rw [s1, s2]
    funext i
    simp only [mulVec, dotProduct, Q, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Algebra.smul_def, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun j _ => by simp only [Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]; ring
  · refine Matrix.ext fun i j => ?_
    have := congrFun (inW j) i
    rw [S_apply] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, Q] using this
end

section

open UpperTheory.V.Hi

theorem UpperTheory.injective_on_span_of_integral_free_submodule :
    ∀ (O Ω V α : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] (m : ℕ) (ψ : V →ₗ[Ω] (α → Fin m → Ω)) (S : Submodule O V), Function.Injective (algebraMap O Ω) → Module.Free O S → (∀ F ∈ S, ∀ g i, ψ F g i ∈ (algebraMap O Ω).range) → (∀ F ∈ S, ψ F = 0 → F = 0) → ∀ F ∈ Submodule.span Ω (S : Set V), ψ F = 0 → F = 0 := by
  intro O Ω V α _ _ _ _ _ _ _ _ m ψ S hinj hfree hrange hker F hF hψF
  classical
  haveI := hfree
  let b := Module.Free.chooseBasis O S
  have hex : ∀ i g j, ∃ r : O, algebraMap O Ω r = ψ (b i : V) g j := fun i g j =>
    RingHom.mem_range.1 (hrange _ (b i).2 g j)
  choose v hv using hex
  have hvli : LinearIndependent O v := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have hx : ψ ((∑ k ∈ s, c k • b k : S) : V) = 0 := by
      funext g j
      have h0 := congrFun (congrFun hsum g) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0

      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, Finset.sum_apply, Pi.zero_apply]
      calc ∑ k ∈ s, ψ (c k • (b k : V)) g j = ∑ k ∈ s, algebraMap O Ω (c k * v k g j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← algebraMap_smul Ω (c k) (b k : V), map_smul, Pi.smul_apply, Pi.smul_apply,
              smul_eq_mul, map_mul, hv]
        _ = 0 := by rw [← map_sum, h0, map_zero]
    have hx0 : (∑ k ∈ s, c k • b k : S) = 0 := Subtype.ext (hker _ (Submodule.coe_mem _) hx)
    exact linearIndependent_iff'.1 b.linearIndependent s c hx0 i hi
  have hw : LinearIndependent Ω (fun i => ψ (b i : V)) := by
    have h1 := UpperTheory.V.Hi.fnIndep O Ω α _ hinj m v hvli
    convert h1 using 1
    funext i g j
    exact (hv i g j).symm
  have hS : Submodule.span O (Set.range (fun i => (b i : V))) = S := by
    have h2 : Set.range (fun i => (b i : V)) = S.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [h2, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsub : (S : Set V) ⊆ Submodule.span Ω (Set.range (fun i => (b i : V))) := by
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range (fun i => (b i : V))) := by
      rw [hS]
      exact hx
    exact Submodule.span_le_restrictScalars O Ω _ hx'
  have hF' := Submodule.span_le.2 hsub hF
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hF'
  have hc : c = 0 := by
    refine linearIndependent_iff.1 hw c ?_
    rw [Finsupp.linearCombination_apply]

    simpa only [Finsupp.sum, map_sum, map_smul] using hψF
  rw [hc, Finsupp.sum_zero_index]
end
