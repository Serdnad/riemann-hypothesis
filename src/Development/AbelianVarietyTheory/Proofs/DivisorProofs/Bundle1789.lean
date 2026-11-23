module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingActionCommutesTranslation
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mulVec_int_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((M *ᵥ v) i) ≤ 1) ↔
      ∀ i j, Valued.v (M i j) ≤ 1 := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single] using this
  · intro h v hv i
    rw [hmem]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ ((hmem _).1 (h i k)) ((hmem _).1 (hv k))

theorem mem_KGL_of_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (M : GLw n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h1 i j)⟩
  let N' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h2 i j)⟩
  have hinj : Function.Injective ((Formalism.UG.Ov E w).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro a b hab
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  have hN : (Formalism.UG.Ov E w).subtype.mapMatrix N = (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  have hN' : (Formalism.UG.Ov E w).subtype.mapMatrix N' = ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  refine ⟨⟨N, N', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hN, hN', map_one]; exact M.mul_inv
  · rw [map_mul, hN, hN', map_one]; exact M.inv_mul
  · apply Units.ext
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe]
    exact hN

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mem_KGL_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) {n : ℕ} (w : Pl E)
    (hw : ¬ IsSplitAt w) (M : GLw n w) (hM : M ∈ UL n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hcj := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  rw [UL, if_neg hw] at hM
  have hM' : Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := hM
  have hinv : ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    have := congrArg (· * ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hM'
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv] at this
    exact this.symm
  refine mem_KGL_of_int w M h1 fun i j => ?_
  rw [hinv]
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hcj]
  exact h1 j i

theorem e_mulVec {K F : Type} [Field K] [Field F] (e : K ≃+* F) {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (u : Fin n → K) (i : Fin n) : e ((Q.map e.symm *ᵥ u) i) = (Q *ᵥ fun j => e (u j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  intro E _ _ _ hU w hw K e _ hint n B ψ γ hg q
  let ψ' : B.A → Fin n → w.adicCompletion E := fun y i => e (ψ y i)
  have hsurj : Function.Surjective ψ' := fun u => ⟨ψ.symm fun i => e.symm (u i), by funext i; simp [ψ']⟩
  set Qi := (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQi
  set Qm := (((q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  set Gm := (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hGm
  set Mm := (((q⁻¹ * γ * q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hMm'
  have hMm : Mm = Qi * Gm * Qm := rfl
  have hQiQm : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hQmQi : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ ∀ i, Valued.v ((Qi *ᵥ ψ' y) i) ≤ 1 := by
    intro y
    show (∀ i, ((Qi.map e.symm) *ᵥ ψ y) i ∈ (algebraMap K.O K.E).range) ↔ _
    refine forall_congr' fun i => ?_
    rw [hint, e_mulVec]
  have hgψ : ∀ y, ψ' (B.g * y) = Gm *ᵥ ψ' y := by
    intro y; funext i
    simp only [ψ']
    rw [hg, e_mulVec]
  have hstab : (∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((Mm *ᵥ v) i) ≤ 1 := by
    constructor
    · intro hst v hv
      obtain ⟨y, hy⟩ := hsurj (Qm *ᵥ v)
      have hyL : y ∈ unitLat e B ψ q := (hmemL y).2 (by rw [hy, Matrix.mulVec_mulVec, hQiQm, Matrix.one_mulVec]; exact hv)
      have := (hmemL _).1 (hst y hyL)
      rw [hgψ, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      rw [hMm]; exact this
    · intro h y hy
      rw [hmemL] at hy ⊢
      rw [hgψ]
      have key : Qi *ᵥ (Gm *ᵥ ψ' y) = Mm *ᵥ (Qi *ᵥ ψ' y) := by
        simp only [hMm, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQmQi, Matrix.mul_one]
      rw [key]
      exact h _ hy
  rw [hstab, mulVec_int_iff, KL, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_KGL_of_unitary hU w hw _ (q⁻¹ * γ * q).2 h
  · rintro ⟨N, hN⟩ i j
    have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
    rw [hmem, hMm', ← hN]
    exact ((N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w)) i j).2

end GlobalTheory.InertUnitOrb.LatStable
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α → ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  first | exact @GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | exact GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | (intros; apply GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem cavg_conj_KGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (k⁻¹ * x * k) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f x := by
  intro E _ _ n w f _ k hk x
  unfold GlobalTheory.LeviDesc.cavg
  rw [← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w (n := n) => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]
  congr 1
  funext k'
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem twistedOrbitalIntegral_parabolic_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  intro E _ _ _ n a ha w f hf m hsep hγ
  obtain ⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩ := GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w
  have hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m := Subtype.ext (hs m).symm
  have hfin := GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ
  have hcent := GlobalTheory.T.mem_twisted_centralizer_block_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  have hcpt := GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  rw [hγs] at hfin hcent hcpt ⊢
  have hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X =>
      (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X)) := by
    funext m'
    unfold GlobalTheory.LeviDesc.orbN
    refine congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
  rw [hrhs]
  refine GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin
  · intro p
    rw [hcent]
    simp only [Subtype.ext_iff, hs]
  · intro p
    rw [hcpt]
    simp only [Subtype.ext_iff, hs]
  · intro q
    exact GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q
  · intro X
    obtain ⟨U, hU, hUi, hUk⟩ := GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)
    refine ⟨U, hU, hUi, fun k hk => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
    exact hUk k hk
  · intro k hk x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _

end GlobalTheory.LeviDesc
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.SepLat

theorem kottwitz_lattice_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  intro p _ G Y hsep hdeg
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (Y : G.C) hdeg hsep, GlobalTheory.OrbFinAf.isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (Y : G.C))] with w hA _ hY1
  intro k h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  let γ₀ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  have hγv : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (Y : G.C) := rfl
  have hγi : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = inC G (w.1.adicCompletion ℚ) (Y : G.C) := rfl
  have hγ0 : GlobalTheory.OrbFinAf.IsIntV G w (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hY1
    rw [hγv]; exact hY1
  have hconj : GlobalTheory.OrbFinAf.IsIntV G w (((k⁻¹)⁻¹ * γ₀ * k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
      w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [inv_inv, Units.val_mul, Units.val_mul, hγi]
    exact h1
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ (by rw [hγv]; exact hQm)
    ((hInt _).1 hγ0) k⁻¹ ((hInt _).1 hconj)
  have hcomm : k⁻¹ * U⁻¹ * γ₀ = γ₀ * (k⁻¹ * U⁻¹) := by
    have e : U * (k * γ₀ * k⁻¹) = γ₀ * U := by simpa using hU
    calc k⁻¹ * U⁻¹ * γ₀ = k⁻¹ * U⁻¹ * (γ₀ * U) * U⁻¹ := by group
      _ = k⁻¹ * U⁻¹ * (U * (k * γ₀ * k⁻¹)) * U⁻¹ := by rw [e]
      _ = γ₀ * (k⁻¹ * U⁻¹) := by group
  refine ⟨k⁻¹ * U⁻¹, U, ?_, (hInt _).2 hU1, (hInt _).2 hU2, by group⟩
  show _ * _ = _ * _
  rw [← hγi, ← Units.val_mul, ← Units.val_mul, hcomm]

end GlobalTheory.FinClsLoc.SepLat
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (exact GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (intros; apply GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep  <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ENNReal.ofReal (ε ^ ((p + q) ^ 2 - 1) / ((p + q : ℕ) : ℝ) ^ (p + q - 1)) ≤ m {u | (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧ 0 < (UpqT.mat u).det.im} := by
  first | exact @GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | exact GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | (intros; apply GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.sections_of_pulled_back_line_bundles_on_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  first | exact @GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk | exact GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk | (intros; apply GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox


theorem _root_.GlobalTheory.T.norm_skewHermitianBasisVector_eq_sqrt_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox


theorem _root_.GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r), Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | exact GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox


theorem _root_.GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical


theorem _root_.GlobalTheory.T.skewHermitianCoordinate_dual_basisVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.enveloping_action_commutes_translation : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V), (∀ a ∈ GinfC V, ∀ (f : SmF θ V) (hfa : (fun x => f.1 (x * a)) ∈ SmF θ V), (envRepAll R u ⟨_, hfa⟩).1 = fun x => (envRepAll R u f).1 (x * a)) → ∀ x : GlobalTheory.AutFinLit.LieC V, envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) * envRepAll R u = envRepAll R u * envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) := by
  first | exact @GlobalTheory.EnvCommLie.envRepAll_comm_lie | exact GlobalTheory.EnvCommLie.envRepAll_comm_lie | (intros; apply GlobalTheory.EnvCommLie.envRepAll_comm_lie <;> assumption)
end
