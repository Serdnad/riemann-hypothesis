module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicFin
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle433
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Mathlib.LinearAlgebra.Matrix.Block
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle127

@[expose] public section

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem GlobalTheory.upperTriangular_signForm_diagonal : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  intro r b s hs hdet hup hJ
  classical
  set J : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => (s a : ℂ)) with hJdef
  have hss : ∀ a, (s a : ℂ) * (s a : ℂ) = 1 := by
    intro a; rcases hs a with h | h <;> simp [h]
  have hJJ : J * J = 1 := by
    rw [hJdef, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hss]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hbt : BlockTriangular b id := fun i j hij => hup i j hij
  haveI : Invertible b := b.invertibleOfIsUnitDet hdet
  have hinv : BlockTriangular b⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  have hright : bᵀ * (J * b.map (starRingEnd ℂ) * J) = 1 := by
    calc bᵀ * (J * b.map (starRingEnd ℂ) * J) = (bᵀ * J * b.map (starRingEnd ℂ)) * J := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have heq : J * b.map (starRingEnd ℂ) * J = (bᵀ)⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  rw [← Matrix.transpose_nonsing_inv] at heq
  have hoff : ∀ a c : Fin r, a < c → b a c = 0 := by
    intro a c hac
    have h1 := congrFun (congrFun heq a) c
    have h2 : (b⁻¹)ᵀ a c = 0 := by
      rw [transpose_apply]; exact hinv hac
    rw [h2, hJdef, mul_diagonal, diagonal_mul] at h1
    simp only [map_apply] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have hsc : (s c : ℂ) ≠ 0 := by rcases hs c with h | h <;> simp [h]
    have : (starRingEnd ℂ) (b a c) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hsa
        · exact h
      · exact absurd h hsc
    simpa using this
  have hdiag : ∀ a c : Fin r, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hoff a c h
    · exact hup a c h
  refine ⟨hdiag, fun a => ?_⟩
  have h1 := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · have hJaa : J a a = (s a : ℂ) := by simp [hJdef]
    rw [mul_diagonal, transpose_apply, map_apply, hJaa] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have h2 : b a a * (starRingEnd ℂ) (b a a) = 1 := by
      have : (s a : ℂ) * (b a a * (starRingEnd ℂ) (b a a)) = (s a : ℂ) * 1 := by
        linear_combination h1
      exact mul_left_cancel₀ hsa this
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (b a a) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : 0 ≤ ‖b a a‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖b a a‖ - 1), sq_nonneg (‖b a a‖ + 1)]
  · intro k _ hk
    rw [mul_diagonal, transpose_apply, map_apply, hdiag k a hk]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
end

section

noncomputable section

open Matrix Topology

namespace GlobalTheory.JSW.Orbit

theorem isClopen_orbit : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)),
    IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 →
    IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  intro F _ n B hBc hBo r₀ hr₀
  classical
  have hset : {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} =
      (fun b : GL (Fin n) F => r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)) '' (B : Set (GL (Fin n) F)) := by
    ext r
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact (hBc.image (continuous_const.matrix_vecMul Units.continuous_val)).isClosed
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    set r := r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F) with hr
    have hr0 : r ≠ 0 := by
      intro h
      apply hr₀
      have : r ᵥ* ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = r₀ := by
        rw [hr, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [← this, h, zero_vecMul]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hr0
    let c : Fin n → F := Pi.single i (r i)⁻¹
    have hc : r ⬝ᵥ c = 1 := by
      simp only [c, dotProduct_single]
      exact mul_inv_cancel₀ hi
    obtain ⟨O, hO, hOB⟩ := GlobalTheory.JSW.KirFin.isEmbedding_coe.isInducing.isOpen_iff.1 hBo
    let s : (Fin n → F) → Matrix (Fin n) (Fin n) F := fun y => 1 + vecMulVec c (y - r)
    have hs : Continuous s :=
      continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))
    have hs1 : s r = 1 := by simp [s]
    have h1O : (1 : Matrix (Fin n) (Fin n) F) ∈ O := by
      have : (1 : GL (Fin n) F) ∈ (B : Set (GL (Fin n) F)) := B.one_mem
      rw [← hOB] at this
      exact this
    have e1 : ∀ᶠ y in 𝓝 r, s y ∈ O := hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1O))
    have e2 : ∀ᶠ y in 𝓝 r, (s y).det ≠ 0 := hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])
    filter_upwards [e1, e2] with y hy1 hy2
    let u : GL (Fin n) F := GeneralLinearGroup.mkOfDetNeZero _ hy2
    have hu : u ∈ B := by
      have : u ∈ (fun g : GL (Fin n) F => g.val) ⁻¹' O := hy1
      rw [hOB] at this
      exact this
    refine ⟨b * u, B.mul_mem hb hu, ?_⟩
    change y = r₀ ᵥ* ((b : Matrix (Fin n) (Fin n) F) * s y)
    rw [← vecMul_vecMul, ← hr]
    change y = r ᵥ* (1 + vecMulVec c (y - r))
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hc]
    simp

end GlobalTheory.JSW.Orbit
end
end

section

open Polynomial

namespace GlobalTheory

theorem exists_normal_finiteType_subring_le_valuationSubring :
    ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ),
    (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) →
    (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) →
    ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R),
      ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧
      IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro κ _ _ V T hc hT hgen
    classical
    haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap ℂ κ).injective
    let A : Subalgebra ℂ κ := Algebra.adjoin ℂ (T : Set κ)
    haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite T.finite_toSet
    haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
    have hAV : ∀ y ∈ A, y ∈ V := fun y hy => by
      let E' : Subalgebra ℂ κ := { V.toSubring with algebraMap_mem' := fun a => hc a }
      have : A ≤ E' := Algebra.adjoin_le fun x hx => hT x hx
      exact this hy
    haveI : Algebra.IsAlgebraic A κ := ⟨fun f => by
      obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
      have hf : f = a / b := by rw [eq_div_iff hb0, he]
      have ha' : IsAlgebraic A a := isAlgebraic_algebraMap (⟨a, ha⟩ : A)
      have hb' : IsAlgebraic A b := isAlgebraic_algebraMap (⟨b, hb⟩ : A)
      rw [hf, div_eq_mul_inv]
      exact ha'.mul hb'.inv⟩
    have htop : Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) = ⊤ := by
      refine eq_top_iff.mpr fun f _ => ?_
      have hle : A.toSubring ≤ (Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ))).toSubring := by
        rw [show A.toSubring = Subring.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) from
          Algebra.adjoin_eq_ring_closure _]
        exact Subring.closure_le.mpr Subfield.subset_closure
      obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
      have hf : f = a / b := by rw [eq_div_iff hb0, he]
      rw [hf]
      exact Subfield.div_mem _ (hle ha) (hle hb)
    haveI : Algebra.EssFiniteType ℂ κ := by
      refine essFiniteType_of_finiteDimensional_subfield_closure T.finite_toSet ?_
      rw [htop]
      exact finiteDimensional_top_subfield κ
    haveI : Algebra.EssFiniteType A κ := .of_comp ℂ A κ
    haveI : Module.Finite A (integralClosure A κ) := finite_integralClosure_of_essFiniteType_field (R := A) ℂ κ
    let S := integralClosure A κ
    haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
    haveI : IsFractionRing S κ := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
    haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff κ).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
    have hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ S.toSubring := fun a =>
      S.algebraMap_mem (⟨algebraMap ℂ κ a, A.algebraMap_mem a⟩ : A)
    refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
    · intro x hx
      exact S.algebraMap_mem (⟨x, Algebra.subset_adjoin hx⟩ : A)
    · intro x hx
      obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
      let ι : A →+* V :=
        { toFun := fun a => ⟨a, hAV a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hE : IsIntegral V x := by
        refine ⟨q.map ι, hqm.map ι, ?_⟩
        rw [eval₂_map]
        exact hq
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
      exact y.2
    · exact (inferInstance : IsNoetherianRing S)
    · exact (inferInstance : IsIntegrallyClosed S)
    · exact (inferInstance : IsFractionRing S κ)

end GlobalTheory
end

section

open Polynomial

noncomputable section

namespace GlobalTheory.PicDiv.LinSys

section Bounded

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra k[X] A]
  [IsScalarTower k k[X] A]

theorem repr_smul_const {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (c : k) (f : A) (i : Fin n) :
    b.repr (c • f) i = C c * b.repr f i := by
  rw [← algebraMap_smul k[X] c f, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Polynomial.algebraMap_eq]

def boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) : Submodule k A where
  carrier := {f | f ∈ D ∧ ∀ i, (b.repr f i).natDegree ≤ d}
  zero_mem' := ⟨D.zero_mem, fun i => by simp⟩
  add_mem' := fun {f g} hf hg => ⟨D.add_mem hf.1 hg.1, fun i => by
    rw [map_add (f := _), Finsupp.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hf.2 i) (hg.2 i))⟩
  smul_mem' := fun c f hf => ⟨by rw [Algebra.smul_def]; exact D.mul_mem_left _ hf.1, fun i => by
    rw [repr_smul_const]
    exact (natDegree_C_mul_le _ _).trans (hf.2 i)⟩

def coeffMap {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    boundedIn b D d →ₗ[k] (Fin n → Fin (d + 1) → k) where
  toFun f i j := (b.repr (f : A) i).coeff j
  map_add' f g := by ext i j; simp [coeff_add]
  map_smul' c f := by ext i j; simp [repr_smul_const, coeff_C_mul]

theorem coeffMap_injective {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    Function.Injective (coeffMap b D d) := by
  apply _root_.GlobalTheory.LinSys.coeffMap_injective <;> assumption

instance finiteDimensional_boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A)
    (d : ℕ) : FiniteDimensional k (boundedIn b D d) :=
  Module.Finite.of_injective (coeffMap b D d) (coeffMap_injective b D d)

end Bounded

theorem isCoprime_of_not_le {A : Type} [CommRing A] {M D : Ideal A} (hM : M.IsMaximal)
    (h : ¬ D ≤ M) : IsCoprime M D := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h'
  exact h (le_sup_right.trans (hM.eq_of_le h' le_sup_left).ge)

end GlobalTheory.PicDiv.LinSys


open GlobalTheory.PicDiv.LinSys in
theorem GlobalTheory.PicDiv.linear_system_setup : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  intro k A _ _ _ _ _ _ _ _ _ hred N P₀ hN hP
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set n := Module.finrank k[X] A
  let b : Module.Basis (Fin n) k[X] A := Module.finBasis k[X] A
  obtain ⟨c, lam, hdeg1, hdeg2⟩ := GlobalTheory.NormDegree.natDegree_norm_of_coord_degree k A n b
  obtain ⟨p, hp2, hpP, hpP2⟩ := GlobalTheory.PicDiv.exists_deg_lt_two_correction_simple k A n b P₀ (∑ i, (C (lam i) * X ^ 2) • b i) hP
  set f₁ : A := ∑ i, (C (lam i) * X ^ 2 + p i) • b i with hf₁def
  have hf₁eq : (∑ i, (C (lam i) * X ^ 2) • b i) + ∑ i, p i • b i = f₁ := by
    rw [hf₁def, ← Finset.sum_add_distrib]; simp [add_smul]
  rw [hf₁eq] at hpP hpP2
  obtain ⟨hf₁0, hf₁deg⟩ := hdeg2 2 p hp2
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hDP : ¬ D ≤ P₀ := by
    intro h
    apply hpP2
    have : Ideal.span {f₁} ≤ P₀ ^ 2 := by rw [hD, sq]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  have hf₁D : f₁ ∈ D := by
    have : Ideal.span {f₁} ≤ D := hD ▸ Ideal.mul_le_right
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  set s := n * 2 + c with hs
  obtain ⟨q, r, Q, hqm, hqdeg, hQmax, hQinj, hf₁Q, hqQ⟩ := GlobalTheory.PicDiv.SquarefreeFibre.main k A hred f₁ s hf₁0
  set d := 2 + (M + 1) * s with hd
  have hspan : ∀ m : ℕ, Ideal.span {f₁ * algebraMap k[X] A (q ^ m)} = P₀ * D * ∏ i, Q i ^ m := by
    intro m
    rw [← Ideal.span_singleton_mul_span_singleton, hD, map_pow, ← Ideal.span_singleton_pow, hqQ,
      Finset.prod_pow]
  have hrepr₁ : ∀ i, b.repr f₁ i = C (lam i) * X ^ 2 + p i := by
    intro i; rw [hf₁def, b.repr_sum_self]
  have hdeg₁ : ∀ i, (b.repr f₁ i).natDegree ≤ 2 := by
    intro i
    rw [hrepr₁]
    exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _)
      (natDegree_le_iff_degree_le.2 (le_of_lt (hp2 i))))
  set f₀ : A := f₁ * algebraMap k[X] A (q ^ (M + 1)) with hf₀def
  have hf₀smul : f₀ = q ^ (M + 1) • f₁ := by rw [hf₀def, Algebra.smul_def, mul_comm]
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀smul]; exact smul_ne_zero (pow_ne_zero _ hqm.ne_zero) hf₁0
  have hf₀V : f₀ ∈ boundedIn b D d := by
    refine ⟨D.mul_mem_right _ hf₁D, fun i => ?_⟩
    rw [hf₀smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine (natDegree_mul_le).trans ?_
    rw [hqm.natDegree_pow, hqdeg]
    have := hdeg₁ i
    omega
  have hnorm₁ : Algebra.norm k[X] f₁ ≠ 0 := Algebra.norm_ne_zero_iff.2 hf₁0
  have hf₀deg : (Algebra.norm k[X] f₀).natDegree = n * d + c := by
    rw [hf₀def, map_mul, Algebra.norm_algebraMap_of_basis b, Fintype.card_fin,
      natDegree_mul hnorm₁ (pow_ne_zero _ (pow_ne_zero _ hqm.ne_zero)), hf₁deg,
      natDegree_pow, hqm.natDegree_pow, hqdeg, hd, hs]
    ring
  refine ⟨r, boundedIn b D d, D, Q, f₀, ⟨inferInstance, fun v hv => hv.1, hQmax, hQinj,
    fun i h => hf₁Q i (h ▸ hpP), fun i h => hf₁Q i (h hf₁D), hDP, hf₀V, hf₀0, hspan (M + 1),
    ?_⟩, ?_⟩
  · intro u
    have hcop : IsCoprime (P₀ * ∏ i, Q i ^ M) D :=
      (isCoprime_of_not_le hP hDP).mul_left
        (IsCoprime.prod_left fun i _ => (isCoprime_of_not_le (hQmax i) (fun h => hf₁Q i (h hf₁D))).pow_left)
    have h1 : (1 : A) ∈ (P₀ * ∏ i, Q i ^ M) ⊔ D := by
      rw [Ideal.isCoprime_iff_sup_eq.1 hcop]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    have hqd : (Algebra.norm k[X] f₁).natDegree + (q ^ M).natDegree ≤ d + 1 := by
      rw [hqm.natDegree_pow, hqdeg, hf₁deg, hd, hs]; nlinarith
    obtain ⟨p', hp'd, hp'⟩ := GlobalTheory.exists_lowDegree_coords_mod k A n b f₁ (q ^ M) d hf₁0 (pow_ne_zero _ hqm.ne_zero)
      hqd (u * y)
    rw [hspan M] at hp'
    have hP0 : P₀ * D * ∏ i, Q i ^ M ≤ D := Ideal.mul_le_left.trans Ideal.mul_le_right
    have hPI : P₀ * D * ∏ i, Q i ^ M ≤ P₀ * ∏ i, Q i ^ M := Ideal.mul_mono_left Ideal.mul_le_left
    refine ⟨∑ i, p' i • b i, ⟨?_, fun i => ?_⟩, ?_⟩
    · have : ∑ i, p' i • b i = u * y - (u * y - ∑ i, p' i • b i) := by ring
      rw [this]; exact D.sub_mem (D.mul_mem_left _ hy) (hP0 hp')
    · rw [b.repr_sum_self]; exact hp'd i
    · have : u - ∑ i, p' i • b i = u * x + (u * y - ∑ i, p' i • b i) := by
        linear_combination (-u) * hxy
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (hPI hp')
  · intro f hf hf0
    rw [finrank_quotient_span_eq_natDegree_norm b hf0, finrank_quotient_span_eq_natDegree_norm b hf₀0,
      hf₀deg]
    have := hdeg1 d (fun i => b.repr f i) hf.2
    rwa [b.sum_repr] at this
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleGeomDescent

open scoped TensorProduct

theorem eq_of_geometric_points' {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rwa [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this

theorem descent : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ _ hff het b hb
  have hBr : _root_.IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced A B
  have : Algebra.Smooth B (B ⊗[A] B) := inferInstance
  have hCr : _root_.IsReduced (B ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B (B ⊗[A] B)
  have hC : (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b := by
    refine eq_of_geometric_points' _ _ fun k _ _ χ => ?_
    have key := hb k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom) ?_
    · simpa using key
    · ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hx := (Algebra.IsEffective.of_faithfullyFlat A B b).mp (by simp [hC])
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha⟩

end GlobalTheory.EtaleGeomDescent
end
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (f : S), KaehlerDifferential.D k S f = 0 → ∃ h : S, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain | exact GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain | (intros; apply GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain <;> assumption)
end
