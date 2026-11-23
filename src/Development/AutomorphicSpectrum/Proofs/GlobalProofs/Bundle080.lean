module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle077
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle070
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLift
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermRestrictSmoothModerate
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle079
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle078
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  first | exact @GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | exact GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.GeoLink

theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := GlobalTheory.T.induced_cell_semisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.block_embedding_parabolic_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (k : Fin r), k ∈ T → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → k.val + 1 = l + d → 1 ≤ d →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ T) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
      glPart σ J X Y T k = ι.range := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.restricted_automorphic_invariance : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (N : Subgroup (GA D V)) (N₁ : Subgroup (GA D V')), (∀ p ∈ N, ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → (∀ v ∈ N, ∃ u ∈ N₁, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → ∃ π : N →* N₁, Continuous π ∧ (∀ (v : N) (u : N₁), π v = u ↔ (v : GA D V) * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) ∧ ∀ v : N, (v : GA D V) ∈ GQ V → (π v : GA D V') ∈ GQ V' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_decomposition_hermitian_centralizer : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ mH ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ mo ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * mo = mo * t) ∧ mm = mH * mo := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.restricted_cusp_constant_term_vanish : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b ∈ unip D.sp.cm.sig V'.gram X' {k}, s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.restricted_constant_term_compatible : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem eichler_frame : ∀ {n m : ℕ} (ε : Fin n → Bool) (G Q : Matrix (Fin n) (Fin n) ℂ) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    IsUnit Q → Qᴴ * Formalism.REAL.Jm ε * Q = G → xᴴ * G * x = 0 → xᴴ * G * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * G ∈ Formalism.QuantumDeterminants.UH G ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)) := by
  intro n m ε G Q x y A hQ hG hxx hxy
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have ex : ∀ z : Matrix (Fin n) (Fin m) ℂ, xᴴ * G * z = (Q * x)ᴴ * Formalism.REAL.Jm ε * (Q * z) := fun z => by
    rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨u, w, hu, hw, hux, hN, hJ⟩ := GlobalTheory.T.unitary_element_prescribed_blocks ε (Q * x) (Q * y) A (by rw [← ex, hxx]) (by rw [← ex, hxy])
  refine ⟨u * Q, Q⁻¹ * w, fun i v hi => ?_, fun v i hi => ?_, fun i j hj => ?_, ?_⟩
  · simp [Matrix.mul_apply, hu i _ hi]
  · simp [Matrix.mul_apply, hw _ i hi]
  · rw [Matrix.mul_assoc]; exact hux i j hj
  have key : Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) = (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q := by
    rw [← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q⁻¹, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · show _ = _
    have e : (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)ᴴ * G * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) =
        (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G))ᴴ * Formalism.REAL.Jm ε * (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) := by
      rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, key, Matrix.conjTranspose_mul]
    have hN' : _ = _ := hN
    calc Qᴴ * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q)
        = Qᴴ * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)) * Q := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hN', ← hG, Matrix.mul_assoc]
  · have cx : ∀ z : Matrix (Fin n) (Fin m) ℂ, ∀ i : A, (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) *ᵥ (fun j => z j i) =
        (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => (Q * z) j i := fun z i => by
      rw [key, ← Matrix.mulVec_mulVec]
      congr 1
    simp only [cx]
    exact hJ

theorem iwasawa_adapted : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  intro D θ hθ V ε fr hfr m X Y hW T b
  classical
  have hQ := isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b
  let Q : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹
  let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => X.map (tauE D τ)
  let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => Y.map (tauE D τ)
  have hmap : ∀ τ (Z Z' : Matrix (Fin V.rank) (Fin m) D.host.E), (Z.map (tauE D τ))ᴴ * gramAt D V τ * Z'.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z').map (tauE D τ) := by
    intro τ Z Z'
    have e : (Z.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (tauE D τ) := by
      ext i j
      simp [Formalism.UG.cT, GlobalTheory.Mem.Isom.tauE_sig]
    rw [e, gramAt, Matrix.map_mul, Matrix.map_mul]
  have hxx : ∀ τ, (x τ)ᴴ * gramAt D V τ * x τ = 0 := fun τ => by
    rw [hmap, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hxy : ∀ τ, (x τ)ᴴ * gramAt D V τ * y τ = 1 := fun τ => by
    rw [hmap, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  choose u w hu hw hux hN hJ using fun τ =>
    eichler_frame (ε τ) (gramAt D V τ) (Q τ) (x τ) (y τ) (upTo T) (hQ τ).1 (hQ τ).2 (hxx τ) (hxy τ)
  obtain ⟨g, hg, U, W, hU, hW', hUX, hgM⟩ := GlobalTheory.T.archimedean_unitary_element_lift D θ hθ V X u w hN
  have hgu : g ∈ unip D.sp.cm.sig V.gram X T :=
    GlobalTheory.T.unitary_adelic_unipotent_lift D.sp.cm.sig V.gram X T g U W hW.xx (fun i v hi => hU i v fun τ => hu τ i v hi)
      (fun v i hi => hW' v i fun τ => hw τ v i hi) (fun i j hj => hUX i j fun τ => hux τ i j hj) hgM
  refine ⟨g, hgu, 1, one_mem _, g⁻¹ * b, by rw [mul_one, mul_inv_cancel_left], fun τ => ?_⟩
  have e1 : (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g := by
    rw [Formalism.L2.Fam.ThC.infMat_mul, Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have e2 : fr τ * (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * (1 + x τ * u τ + w τ * (x τ)ᴴ * gramAt D V τ) := by
    rw [e1, hg τ, ← Matrix.mul_assoc]
  obtain ⟨k, S, hk⟩ := GlobalTheory.T.involution_stable_subspace_coordinate (ε τ) _ (hJ τ)
  refine ⟨k, S, ?_⟩
  beta_reduce
  rw [e2]
  exact hk

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.frame_adapted_subspace_unitary_group : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → ∀ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∃ (ε' : D.what₂.Tau → Fin V'.rank → Bool) (fr' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (j : ∀ τ, Formalism.REAL.KG (ε' τ) →* Formalism.REAL.KG (ε τ)), IsFrameFam V' ε' fr' ∧ (∀ τ, Continuous (j τ)) ∧ ∀ τ k, s (kAt θ V' τ (ε' τ) (fr' τ) k) = kAt θ V τ (ε τ) (fr τ) (j τ k) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep

open MeasureTheory GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem finiteDimensional_coeffs {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (_root_.GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w))
      (fun ℓ₁ ℓ₂ w => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
      (fun ℓ w₁ w₂ => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
  have hle : _root_.GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T) := by
    unfold _root_.GlobalTheory.Published.AutFin.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, by simp [T]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → K) (a : ι → K → ℂ), (∀ i, a i ∈ A) ∧
      ∀ f ∈ A, ∀ k, f k = ∑ i, f (p i) * a i k := by
  classical
  let E : K → Module.Dual ℂ A := fun k => (LinearMap.proj k).comp A.subtype
  have htop : Submodule.span ℂ (Set.range E) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      funext k
      have h := hf (E k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [E] using h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range E)
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A)) := by
    rw [Subtype.range_coe, hbspan, htop]
  let B : Module.Basis b ℂ (Module.Dual ℂ A) := Module.Basis.mk hbli hbtop
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A) := fun i => hbsub i.2
  choose p hpE using hp
  let a : b → A := fun i => (Module.evalEquiv ℂ A).symm (B.coord i)
  refine ⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩
  intro f hf k
  have key := B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)
  have key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i := by
    apply (Module.evalEquiv ℂ A).injective
    conv_lhs => rw [← key]

    rw [map_sum]
    simp only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hk := congrArg (fun g : A => (g : K → ℂ) k) key2
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  rw [hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBi : B i = (i : Module.Dual ℂ A) := by simp [B]
  rw [hBi, ← hpE i]
  rfl

theorem hasTypeAt_of_isConstAlong : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  intro D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc
  classical
  have hst := GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) hW
  obtain ⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩ := hst.1 T
  haveI := hμ
  have hcI := hc μ 𝓕 hμ h𝓕 h1
  haveI := finiteDimensional_coeffs ρ
  obtain ⟨ι, _, p, a, ha, hrep⟩ := exists_interp (_root_.GlobalTheory.Published.AutFin.coeffSpan ρ)
  have hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T) := by
    obtain ⟨K, hK, hKc⟩ := hcoc
    refine ⟨K, hK, fun n => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKc n
    refine ⟨γ, ?_, hγK⟩
    rw [Subgroup.inf_subgroupOf_right]
    exact hγ
  have h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf
      (unip D.sp.cm.sig V.gram X T)) 𝓕 μ := by
    rw [Subgroup.inf_subgroupOf_right]
    exact h𝓕
  haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance
  haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) :=
    DiscreteTopology.of_subset hdQ (fun y hy => hy.1)
  have hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ := by
    intro g
    exact GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕'
      (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g
  intro x
  have hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcI (x * kAt θ V τ e P k)]
    have hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) =
        ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k := by
      intro u
      have h := hrep _ (hty ((u : GA D V) * x)) k
      simpa [mul_assoc] using h
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, hcI]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.rational_unipotent_le_parabolic : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.constant_term_moderate_growth_inherited : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong <;> assumption)
end
