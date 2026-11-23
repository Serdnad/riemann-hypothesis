module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle307
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.HarmLift

theorem lemA : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W),
    (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := GlobalTheory.T.exists_fockHarmonic_representative

theorem lemB : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧
      KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable

theorem lemC : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 →
    ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) →
      (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) →
      (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) →
      ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (hZ : IsKC Z) : IsKC (adjZ Z) := by
  intro a b hab
  rw [GlobalTheory.FockAdj.adjZ_apply, hZ b a (fun h => hab (by revert h; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock])),
    star_zero, mul_zero]

theorem trace_PC {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  simp only [Eab, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hcd
  · rfl

end GlobalTheory.HarmLift
end
end

section

open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMaxExt

open Module Matrix

section One

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}


omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem fg_of_le (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) : M.FG := by
  haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.1 inferInstance M hM

theorem exists_slope_eq (hN : HasGram N) (hL : L.FG) (h0 : L ≠ ⊥) :
    ∃ M : Submodule (𝓞 K) V, M ≤ L ∧ M ≠ ⊥ ∧ slope_sq N M = slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨hLat, -, -⟩ := Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL
  obtain ⟨-, -, ⟨M, hM, hM0, hMs⟩, -, -⟩ := Formalism.HN.muChar _ _ _ _ L hLat h0
  refine ⟨M, hM.1, hM0, ?_⟩
  rw [slope_sq_eq hG (fg_of_le hL hM.1), (slopeMax_slopeMin_eq hG hL h0).1]
  simp only [Formalism.HN.muDef, Formalism.HN.muMaxDef, hMs]

theorem slope_le_slopeMax (hN : HasGram N) (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) (hM0 : M ≠ ⊥) :
    slope_sq N M ≤ slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  have h0 : L ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hM))
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have l1 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) M (fg_of_le hL hM)).1
  have l2 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL).1
  have m1 := Formalism.HN.muChar _ _ _ _ _ l1 hM0
  have m2 := (Formalism.HN.muChar _ _ _ _ _ l2 h0).1
  have key := (m1.1 _).2 fun P hP => (m2 _).1 le_rfl P (hP.trans hM)
  have := m1.2.2.2.2
  rw [slope_sq_eq hG (fg_of_le hL hM), (slopeMax_slopeMin_eq hG hL h0).1]
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

end One

section Two

variable {K K' V V' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
  (ι : V →ₛₗ[algebraMap K K'] V')


omit [NumberField K] [NumberField K'] in
theorem map_mem_of_mem_span {s : Set V} {P : Submodule (𝓞 K') V'} (hs : ∀ x ∈ s, ι x ∈ P) {x : V}
    (hx : x ∈ Submodule.span (𝓞 K) s) : ι x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
  | smul a x _ hx =>
    have : ι (a • x) = algebraMap (𝓞 K) (𝓞 K') a • ι x := by
      rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
      rfl
    rw [this]; exact P.smul_mem _ hx


omit [NumberField K] [NumberField K'] in
theorem fg_span_image {L : Submodule (𝓞 K) V} (hL : L.FG) :
    (Submodule.span (𝓞 K') (ι '' (L : Set V))).FG := by
  obtain ⟨s, rfl⟩ := hL
  refine Submodule.fg_def.2 ⟨ι '' s, s.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_of_mem_span ι (fun y hy => Submodule.subset_span (Set.mem_image_of_mem _ hy)) hx


omit [NumberField K] [NumberField K'] [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K') K' V'] in
theorem span_image_ne_bot
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    {L : Submodule (𝓞 K) V} (h0 : L ≠ ⊥) : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have h1 := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 hx0)).ne_zero 0
  intro h
  exact h1 (Submodule.span_eq_bot.1 h _ ⟨x, hx, rfl⟩)

end Two

theorem exists_frame {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (τ : K →+* ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
      t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := by
  have hs : ∀ u : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := fun u => by
    unfold Formalism.HermitianLatticesTheory.cnorm
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have key : ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsUnit Z.det →
      (∀ x, Formalism.HermitianLatticesTheory.cnorm (Z *ᵥ fun i => τ (b.repr x i)) = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x) →
      ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
        t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := fun Z hZ h => by
    have hu : IsUnit ((t : ℂ) • Z).det := by
      rw [det_smul]
      exact (IsUnit.pow _ (Ne.isUnit (by exact_mod_cast ht.ne'))).mul hZ
    refine ⟨((t : ℂ) • Z)⁻¹, isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    rw [nonsing_inv_nonsing_inv _ hu, smul_mulVec, hs, h]
  have hi := isUnit_nonsing_inv_det _ (hX (InfinitePlace.mk τ))
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine key _ hi fun x => ?_
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    rw [h]
  · refine key ((starRingEnd ℂ).mapMatrix (X (InfinitePlace.mk τ))⁻¹) ?_ fun x => ?_
    · rw [← RingHom.map_det]; exact hi.map _
    · unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.HermitianLatticesTheory.cnorm
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.norm_conj]
      simp [Matrix.mulVec, dotProduct]

def coordExt {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) : V →ₛₗ[algebraMap K F] (Fin n → F) where
  toFun x i := algebraMap K F (b.repr x i)
  map_add' x y := by funext i; simp
  map_smul' a x := by funext i; simp

theorem coordExt_li {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (m : ℕ) (e : Fin m → V) (he : LinearIndependent K e) :
    LinearIndependent F fun k => coordExt F b (e k) :=
  (linearIndependent_algebraMap_comp_iff (S := F) (v := fun k => b.equivFun (e k))).2
    (he.map' b.equivFun.toLinearMap b.equivFun.ker)

theorem slopeMax_sq_span_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L c B hN hN' hc hli hL h0 hcB hι
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsAlgClosure K (AlgebraicClosure K') := ⟨inferInstance, Algebra.IsAlgebraic.trans K K' _⟩
  let F : Type := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  haveI : IsGalois K F := inferInstance
  haveI : NumberField F := NumberField.of_module_finite K F
  have hL' := fg_span_image ι hL
  obtain ⟨M, hM, hM0, hMs⟩ := exists_slope_eq hN' hL' (span_image_ne_bot ι hli h0)
  have hMfg := fg_of_le hL' hM
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN'
  letI : StarRing K' := starRingOfComm
  let N₁ : (K' →+* ℂ) → V' → ℝ := fun σ x => N' (InfinitePlace.mk σ).embedding x
  have hG₁ : IsGram b X N₁ := fun v => ⟨(hG v).1, fun x => by
    simp only [N₁, InfinitePlace.mk_embedding]; exact (hG v).2 x⟩
  have hc₁ : ∀ σ x, N₁ ((starRingEnd ℂ).comp σ) x = N₁ σ x := fun σ x => by
    have : InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ := InfinitePlace.mk_conjugate_eq σ
    simp only [N₁, this]
  choose Y hY hYn using fun τ : K' →+* ℂ => exists_frame b X (fun v => (hG v).1) τ
    (inv_pos.2 (hcB (InfinitePlace.mk τ).embedding).1)
  let N₂ : (F →+* ℂ) → (Fin n → F) → ℝ := fun σ y =>
    Formalism.HermitianLatticesTheory.cnorm ((Y (σ.comp (algebraMap K' F)))⁻¹ *ᵥ fun i => σ (y i))
  have hG₂ : IsGram (Pi.basisFun F (Fin n)) (fun u => Y (u.embedding.comp (algebraMap K' F))) N₂ :=
    fun u => ⟨hY _, fun y => by
      unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
      simp only [N₂, Pi.basisFun_repr]⟩
  have hN₂ : HasGram N₂ := ⟨⟨n, ⟨(_, _), hG₂⟩⟩⟩
  let φ := coordExt F b
  have hφ : ∀ (σ : F →+* ℂ) x, N₂ σ (φ x) = (c (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding)⁻¹ *
      N₁ (σ.comp (algebraMap K' F)) x := fun σ x => (hYn _ x).trans (by rw [(hG _).2])
  let ψ : V →ₛₗ[algebraMap K F] (Fin n → F) :=
    { toFun := fun x => φ (ι x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        rw [map_smulₛₗ, map_smulₛₗ, ← IsScalarTower.algebraMap_apply] }
  have h1 := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span K' F V' (Fin n → F) N₁ N₂ φ M B ⟨⟨n, ⟨(b, X), hG₁⟩⟩⟩ hN₂ hc₁
    (coordExt_li F b) hMfg hM0 (fun σ x => by
      rw [hφ]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · obtain ⟨h1, h2⟩ := hcB (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding
        rw [← Real.exp_log h1, ← Real.exp_neg]
        exact Real.exp_le_exp.2 ((neg_le_abs _).trans h2)
      · show 0 ≤ N' _ x
        rw [← (hG _).2]; exact Real.sqrt_nonneg _)
  have h2 := GlobalTheory.T.maxSlope_extendedLattice_galois_le K F V (Fin n → F) N N₂ ψ L hN hN₂ hc
    (fun m e he => coordExt_li F b m _ (hli m e he)) hL h0 (fun σ x => by
      show N₂ σ (φ (ι x)) = _
      rw [hφ]
      show _ * N' _ (ι x) = _
      rw [hι, inv_mul_cancel_left₀ (hcB _).1.ne', IsScalarTower.algebraMap_eq K K' F, ← RingHom.comp_assoc]
      rcases InfinitePlace.embedding_mk_eq (σ.comp (algebraMap K' F)) with h | h
      · rw [h]
      · rw [h]; exact hc ((σ.comp (algebraMap K' F)).comp (algebraMap K K')) x)
  have h3 : slope_sq N₂ (Submodule.span (𝓞 F) (φ '' (M : Set V'))) ≤
      slopeMax_sq N₂ (Submodule.span (𝓞 F) (ψ '' (L : Set V))) := by
    refine slope_le_slopeMax hN₂ (fg_span_image ψ hL) (Submodule.span_le.2 ?_)
      (span_image_ne_bot φ (coordExt_li F b) hM0)
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_of_mem_span φ ?_ (hM hx)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h4 : slope_sq N₁ M = slope_sq N' M := by rw [slope_sq_eq hG₁ hMfg, slope_sq_eq hG hMfg]
  linarith

end GlobalTheory.SlopeMaxExt
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.hostIntegerCharacter_comp_conj_eq_conjEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ a, ((t.comp (H.bar : 𝓞 E →+* 𝓞 E) a : 𝓞 K) : K) = algebraMap c.F K (embK c (conjEmb τ.1) a) := by
  first | exact @GlobalTheory.ConjHostChar.conj_char | exact GlobalTheory.ConjHostChar.conj_char | (intros; apply GlobalTheory.ConjHostChar.conj_char <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V
open Formalism.L2.Host

namespace GlobalTheory.HenQ

theorem local_bound (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (h1 : ∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) (h2 : ∀ x, x ≠ 0 → 0 < (Bf x x).re)
    (h3 : ∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w ρ B) :
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ^ n := by
  obtain ⟨x, hx0, hxK, hcard, hT⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  set q := Formalism.UG.qV E w with hqdef
  have hq2 : 2 ≤ q := GlobalTheory.LFun.one_lt_absNorm w
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)

  have he : ∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ (q : ℝ) ^ (n * n) := by
    intro j _ hjn
    obtain ⟨hfin, hc⟩ := GlobalTheory.T.heckeTj_cosets_finite_card_le E w n ϖ hϖ j hjn
    have hh : ∀ g, ‖Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g‖ ≤ 1 := fun g => by
      unfold Formalism.UG.Tj
      exact (norm_indicator_le_norm_self _ _).trans (by simp)
    have k1 := GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets _ (GlobalTheory.LFun.KGL w (n := n)) V ρ Bf h1 h2 h3 _ x _ hh hfin hx0 (hT ϖ hϖ j hjn)
    have k2 : ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ ‖GlobalTheory.LFun.satEig q n B j‖ := by
      unfold GlobalTheory.LFun.satEig
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow hq1 ?_)
      have : (((j : ℂ) * ((n : ℂ) - j)) / 2).re = (j : ℝ) * ((n : ℝ) - j) / 2 := by simp
      rw [this]
      have : (j : ℝ) ≤ n := by exact_mod_cast hjn
      positivity
    refine k2.trans (k1.trans ?_)
    refine le_trans ((Nat.cast_le (α := ℝ)).2 hc) ?_
    push_cast
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left n hjn)
  have hnq : (n : ℝ) ≤ (q : ℝ) ^ n := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have h2n : (2 : ℝ) ^ n ≤ (q : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq2) n
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast this.le
    linarith
  have hup : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ (n * n + n) := by
    intro b hb
    refine (GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le n B _ hcard (one_le_pow₀ hq1) he b hb).trans ?_
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left hnq (by positivity)
  refine fun b hb => ⟨hup b hb, ?_⟩

  obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation E w n V ρ ϖ hϖ x hxK
  have hn := hT ϖ hϖ n le_rfl
  have hsat : GlobalTheory.LFun.satEig q n B n = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    simp only [sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    have : (B.map fun b : ℂˣ => (b : ℂ)).card = n := by rw [Multiset.card_map, hcard]
    rw [← this, Multiset.esymm, Multiset.powersetCard_self]
    simp
  rw [hg, hsat] at hn
  have hp : ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 := by
    set c := (B.map fun b : ℂˣ => (b : ℂ)).prod
    have e := h3 g x x
    rw [hn, map_smul, map_smulₛₗ, LinearMap.smul_apply] at e
    have hx : Bf x x ≠ 0 := fun h0 => by simpa [h0] using h2 x hx0
    simp only [smul_eq_mul] at e
    have e2 : starRingEnd ℂ c * c = 1 := by
      refine mul_right_cancel₀ hx ?_
      rw [one_mul]
      nth_rewrite 2 [← e]
      ring
    have e3 : ‖c‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : (Complex.normSq c : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact e2
      exact_mod_cast this
    nlinarith [norm_nonneg c]
  have := GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' B _ (one_le_pow₀ hq1) hup hp b hb
  rwa [hcard] at this

end GlobalTheory.HenQ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  first | exact @GlobalTheory.MBLow.key_basis_change | exact GlobalTheory.MBLow.key_basis_change | (intros; apply GlobalTheory.MBLow.key_basis_change <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.KeyLieChg

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem lieComb_of_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left)
    (hu'v' : ∀ i, (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left) (i : Fin m) :
    IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i) := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).1 (hu'v' i)

theorem constFn_one {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    Geo.Tor.constFn p U (1 : R) = 1 := by
  simp [Geo.Tor.constFn]

theorem exists_keyPB_det : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  intro κ hκ R _ y x f hxy v' hv' M hM
  obtain ⟨φ, he, w, hg, F, hp, hw, hrig, hsec, hF, hε, hlie⟩ := hxy
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  subst hF'
  haveI := y.P.isAb.comm
  haveI := x.P.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R ℂ f y.P.A x.P.A φ hp y.P.isAb.smooth y.P.g v' hv'
  have hb : IsLieBasis (fun i : Fin x.P.g => u (i.cast hg)) := isLieBasis_cast hg hu
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, fun i => u (i.cast hg), hb⟩,
    ⟨φ, he, w, hg, Chart.dualMapR f, hp, hw, hrig, hsec, hF, hε, fun i => huv (i.cast hg)⟩, ?_⟩
  have hc := lieComb_of_over f hp hg M y.v v' x.v (fun i => u (i.cast hg)) hM hlie (fun i => huv (i.cast hg))
  have k := hκ ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne (fun i => u (i.cast hg)) hb 1
    (fun i j => f (M (i.cast hg) (j.cast hg))) (fun i => by rw [constFn_one, _root_.one_mul]) hc
  have hd : (Matrix.of fun i j : Fin x.P.g => f (M (i.cast hg) (j.cast hg))).det = (M.map f).det :=
    Matrix.det_submatrix_equiv_self (finCongr hg) (M.map f)
  simp only [Nat.mul_one, one_pow, _root_.one_mul] at k
  rw [k]
  exact congrArg (· ^ 4 * (κ ℂ x : ℂ)) hd

end GlobalTheory.KeyLieChg
end
end
