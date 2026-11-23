module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolveUnitriangular
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle365
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle364
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CoeffBound

theorem exists_radius {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (b : ℝ) (hb0 : 0 < b)
    (hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < b ∧ ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < ρ := by
  classical
  have hfin : Set.Finite {μ : ℂ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  let s : Finset ℝ := insert 0 (hfin.toFinset.image fun μ => ‖μ‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hM : s.max' hs < b := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hb0
    · obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hy
      exact hb μ (hfin.mem_toFinset.1 hμ)
  have h0 : 0 ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨(s.max' hs + b) / 2, by linarith, by linarith, fun μ hμ => ?_⟩
  have h1 : ‖μ‖ ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hμ)))
  linarith

theorem exists_coordinates (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    ∃ (d : ℕ) (e : W ≃ₗ[ℂ] (Fin d → ℂ))
      (φ : Module.End ℂ W →ₐ[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))),
      (∀ (S : Module.End ℂ W) (x : W), φ S (e x) = e (S x)) ∧
      ∀ (S : Module.End ℂ W) (μ : ℂ),
        Module.End.HasEigenvalue ((φ S : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ)) μ →
          S.HasEigenvalue μ := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  let φ : Module.End ℂ W →ₐ[ℂ] ((Fin (Module.finrank ℂ W) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Fin (Module.finrank ℂ W) → ℂ)).toAlgHom.comp
      (e.conjAlgEquiv ℂ).toAlgHom
  have hφ : ∀ (S : Module.End ℂ W) (x : Fin (Module.finrank ℂ W) → ℂ), φ S x = e (S (e.symm x)) := by
    intro S x
    simp [φ, LinearEquiv.conjAlgEquiv_apply]
    rfl
  refine ⟨_, e, φ, fun S x => by rw [hφ]; simp, fun S μ h => ?_⟩
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hx1 : φ S x = μ • x := Module.End.mem_eigenspace_iff.1 hx.1
  rw [hφ] at hx1
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm x)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h0 => hx.2 (by simpa using h0)⟩
  apply e.injective
  rw [hx1]
  simp

theorem diagPow_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) : Zls.diagPow k N 0 = 1 := by
  refine Units.ext ?_
  ext i j
  simp [Zls.diagPow, Matrix.one_apply, Matrix.diagonal_apply]

theorem lamOf_zero (N : ℕ) : Zls.lamOf (0 : Fin (N - 1) → ℕ) = 0 := by
  funext i
  simp [Zls.lamOf]

theorem hecke_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hsm : IsSmooth π) {m : ℕ} (hm : 1 ≤ m)
    (j : Fin (N - 1)) (T : Module.End ℂ (fixed π (Zls.Km k N m)))
    (hT : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1))) T) (n : ℕ) :
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf (Pi.single j n : Fin (N - 1) → ℕ))) (T ^ n) := by
  induction n with
  | zero =>
    rw [Pi.single_zero, lamOf_zero, diagPow_zero, pow_zero]
    intro v l _
    simp
  | succ n ih =>
    have hs : (Pi.single j (n + 1) : Fin (N - 1) → ℕ) = Pi.single j n + Pi.single j 1 := by
      rw [← Pi.single_add]
    rw [hs, ((GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1 _ _), pow_succ]
    refine GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _ ih ?_
    rw [(GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).2 j]
    exact hT

theorem radius_sq_lt {q ρ : ℝ} (hq : 0 < q) (a : ℕ) (h0 : 0 ≤ ρ)
    (h : ρ < q ^ (-((a : ℝ) / 2))) : q ^ a * ρ ^ 2 < 1 := by
  have h1 : ρ ^ 2 < (q ^ (-((a : ℝ) / 2))) ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  have h2 : (q ^ (-((a : ℝ) / 2))) ^ 2 = (q ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q a, ← Real.rpow_neg hq.le]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  have h3 : 0 < q ^ a := pow_pos hq a
  calc q ^ a * ρ ^ 2 < q ^ a * (q ^ a)⁻¹ := mul_lt_mul_of_pos_left h1 h3
    _ = 1 := mul_inv_cancel₀ h3.ne'

theorem coeff_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → Zls.HeckeSpectral π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hrad := fun j : Fin (N - 1) => exists_radius (T j) _ (Real.rpow_pos_of_pos hq
      (-(((((((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) : ℕ) : ℝ)) / 2)))
    (fun μ hμ => hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ)
  choose ρ hρ0 hρb hρe using hrad
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact radius_sq_lt hq _ (hρ0 j) (hρb j)
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

end GlobalTheory.CompanionTheory.CoeffBound
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_of_mem_ker {N m : ℕ} {A : GL (Fin N) 𝒪[k]}
    (hA : A ∈ (Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))).ker) (i j : Fin N) :
    (A : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈
      Ideal.span {Zls.unif k ^ m} := by
  rw [MonoidHom.mem_ker] at hA
  have h := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => u.val i j) hA
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h
  rw [← Ideal.Quotient.eq]
  rw [h]
  by_cases e : i = j
  · subst e
    simp
  · simp [Matrix.one_apply_ne e]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (B : Matrix (Fin N) (Fin N) 𝒪[k])
    (hB : ∀ i j, B i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ Ideal.span {Zls.unif k ^ m}) :
    ∃ b ∈ Zls.Km k N m, (b : Matrix (Fin N) (Fin N) k) = B.map (algebraMap 𝒪[k] k) := by
  set J : Ideal 𝒪[k] := Ideal.span {Zls.unif k ^ m} with hJ
  have hmap : B.map (Ideal.Quotient.mk J) = 1 := by
    ext i j
    have := Ideal.Quotient.eq.2 (hB i j)
    simp only [Matrix.map_apply]
    rw [this]
    by_cases e : i = j
    · subst e
      simp
    · simp [Matrix.one_apply_ne e]
  have hdet : Ideal.Quotient.mk J B.det = 1 := by
    have := RingHom.map_det (Ideal.Quotient.mk J) B
    rw [this]
    show (B.map (Ideal.Quotient.mk J)).det = 1
    rw [hmap, Matrix.det_one]
  have hmem : B.det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, hdet, map_one]
  have hJm : J ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [hJ, Ideal.span_singleton_le_iff_mem]
    have : Zls.unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [Zls.irreducible_unif.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_mem_of_mem _ this m (by omega)
  have hunit : IsUnit B.det := by
    by_contra hn
    have h1 : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 := hJm hmem
    have h3 : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h3
  let G : GL (Fin N) 𝒪[k] := Matrix.GeneralLinearGroup.mk'' B hunit
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) G, ?_, ?_⟩
  · refine ⟨G, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    have h := congrFun (congrFun hmap i) j
    simpa [G, Matrix.GeneralLinearGroup.map_apply] using h
  · rfl

theorem conj_mem_Km {N m : ℕ} {p b : GL (Fin N) k} (hp : p ∈ KO k (Fin N)) (hb : b ∈ Zls.Km k N m) :
    p * b * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨A, hA, rfl⟩ := hb
  refine ⟨P * A * P⁻¹, ?_, by simp⟩
  exact (MonoidHom.normal_ker _).conj_mem A hA P

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    ((Zls.diagPow k N lam : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ lam i) := by
  ext i j
  simp [Zls.diagPow, Zls.unifU, Matrix.diagonal_apply]

theorem exists_cover (N m : ℕ) (hm : 1 ≤ m) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ s : Finset (GL (Fin N) k),
      s.card ≤ Nat.card 𝓀[k] ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, ∃ c ∈ s, ∃ b ∈ Zls.Km k N m,
        x * Zls.diagPow k N lam * y = c * b := by
  classical
  obtain ⟨s0, hcard, hs0⟩ := GlobalTheory.CompanionTheory.KmCover.double_coset_cover 𝒪[k] k N (Zls.unif k) m
    Zls.irreducible_unif hm lam hlam
  let f : Matrix (Fin N) (Fin N) k → GL (Fin N) k := fun M =>
    if h : ∃ c : GL (Fin N) k, c.val = M then h.choose else 1
  refine ⟨s0.image f, Finset.card_image_le.trans hcard, ?_⟩
  rintro x ⟨A1, hA1, rfl⟩ y ⟨A2, hA2, rfl⟩
  obtain ⟨M, hM, B, hB, e⟩ := hs0 A1.val A2.val (entries_of_mem_ker hA1) (entries_of_mem_ker hA2)
  obtain ⟨b, hb, hbv⟩ := exists_mem_Km hm B hB
  set X : GL (Fin N) k := Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A1 *
    Zls.diagPow k N lam * Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A2 with hX
  have hXv : X.val = M * b.val := by
    rw [hbv, ← e, hX, Units.val_mul, Units.val_mul, diagPow_val]
    rfl
  have hex : ∃ c : GL (Fin N) k, c.val = M := by
    refine ⟨X * b⁻¹, ?_⟩
    rw [Units.val_mul, hXv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨f M, Finset.mem_image_of_mem f hM, b, hb, ?_⟩
  apply Units.ext
  have hf : (f M).val = M := by
    simp only [f, dif_pos hex]
    exact hex.choose_spec
  rw [Units.val_mul (f M) b, hf]
  exact hXv

theorem measure_translated_doubleCoset_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  intro k _ _ _ _ N _ _ μ hμ m hm p1 p2 hp1 hp2 g
  classical
  obtain ⟨hanti, hgap⟩ := GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N g
  obtain ⟨s, hcard, hcov⟩ := exists_cover (k := k) N m hm (Zls.lamOf g) hanti
  rw [hgap] at hcard
  set U : Set (AdGL k N) :=
    (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k)) with hU
  let T : GL (Fin N) k → Set (AdGL k N) := fun c =>
    (fun q => (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * q) ⁻¹' U
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m,
      ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2} ⊆ ⋃ c ∈ s, T c := by
    rintro _ ⟨h, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc, b, hb, e⟩ := hcov x hx y hy
    refine Set.mem_biUnion hc ?_
    refine ⟨p2⁻¹ * b * p2, ?_, ?_⟩
    · have := conj_mem_Km (inv_mem hp2) hb
      simpa using this
    · have e2 : p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2 = p1 * (c * b) * p2 := by
        rw [← e]
        group
      rw [e2]
      show (QuotientGroup.mk (p2⁻¹ * b * p2) : AdGL k N) =
        (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * QuotientGroup.mk (p1 * (c * b) * p2)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      group
  calc μ _ ≤ μ (⋃ c ∈ s, T c) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ (T c) := measure_biUnion_finset_le _ _
    _ = ∑ _c ∈ s, μ U := Finset.sum_congr rfl fun c _ => measure_preimage_mul μ _ U
    _ = (s.card : ENNReal) * μ U := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard

end GlobalTheory.CompanionTheory.KmVolume
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.ordered_forms_interleave_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)), ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k), IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧ Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | exact GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | (intros; apply GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.OneTermOrder

theorem nabs_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : nabs k (Zls.unifU k) < 1 := by
  rw [nabs_uniformiser (Zls.irreducible_unif (k := k)) (x := Zls.unifU k) rfl]
  have hq : 1 < resCard k := Finite.one_lt_card
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)

theorem norm_absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (j : ℕ) :
    ‖((absPow k (j : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ j := by
  rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (nabs_pos' k t).le]

theorem isOrderedForm_single_rev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)),
    PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif k ξ) →
    IsOrderedForm (fun i : Fin n => Segment.single (IrrGL.ofChar (ξ (Fin.rev i))
      (isSmoothChar_of_isUnram (hξ (Fin.rev i)))) (IrrGL.isCusp_ofChar _ _)) (PositivityTheory.SphericalProduct.msOne ξ hξ) := by
  intro k _ _ _ _ n ξ hξ hanti
  refine ⟨?_, fun i j hij hp => ?_⟩
  · have h := Multiset.map_univ_val_equiv (Fin.revPerm (n := n))
    rw [PositivityTheory.SphericalProduct.msOne]
    conv_rhs => rw [← h, Multiset.map_map]
    rfl
  · obtain ⟨-, m, hm, he⟩ := hp
    have he' : IrrGL.ofChar (ξ (Fin.rev j)) (isSmoothChar_of_isUnram (hξ (Fin.rev j))) =
        (IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))).nu (m : ℂ) := he
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at he'
    have hle : ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ ≤ ‖((ξ (Fin.rev j) (Zls.unifU k) : ℂˣ) : ℂ)‖ :=
      hanti (Fin.rev_le_rev.2 hij.le)
    rw [he', MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_natCast] at hle
    have hpos : 0 < ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have hlt : nabs k (Zls.unifU k) ^ m < 1 :=
      pow_lt_one₀ (nabs_pos' k _).le (nabs_unifU_lt_one k) hm.ne'
    nlinarith

end GlobalTheory.CompanionTheory.OneTermOrder
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.segment_generic_of_jacquet_nu_pair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.LSegGeneric k := by
  first | exact @GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | exact GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | (intros; apply GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem isDominant_one_and_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (J : Subgroup (GL (Fin N) k)) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N),
      IsDominant k N J d hd 1 ∧ ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t →
        IsDominant k N J d hd t' → IsDominant k N J d hd (t * t') := by
  intro k _ _ _ _ N J h d hd
  refine ⟨⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ?_⟩, ?_⟩
  · simpa using hn
  · simpa using hn
  · simpa using hx
  · rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · have key := h1 _ (h1' n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := h2' _ (h2 n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := (h3 _ (h3' x hx).1).1
      convert key using 1
      group
    · have key := (h3' _ (h3 x hx).2).2
      convert key using 1
      group

end GlobalTheory.CompanionTheory.Lbc
end
