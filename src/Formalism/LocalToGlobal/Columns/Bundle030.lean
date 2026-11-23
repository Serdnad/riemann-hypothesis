module

public import Formalism.LocalToGlobal.Columns.Bundle001
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.SizeWindowBrackets.Bundle002
public import Formalism.LocalToGlobal.Columns.Bundle002
public import Formalism.MonomialMeanResidues.FilteredDegree
public import Formalism.LocalToGlobal.Columns.Bundle029
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Loc

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem localization_map₃ (p : Ideal (𝓞 K)) [p.IsPrime] (f : V →ₗ[K] V') (A : Submodule (𝓞 K) V) :
    localization₂ p (A.map (f.restrictScalars (𝓞 K))) = (localization₂ p A).map (f.restrictScalars (𝓞 K)) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by exact_mod_cast h0
      rw [this]; exact p.zero_mem
    refine ⟨((s : K)⁻¹) • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul]
      rw [show (algebraMap (𝓞 K) K s) * (s : K)⁻¹ = 1 from mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · simp only [LinearMap.restrictScalars_apply, map_smul]
      simp only [LinearMap.restrictScalars_apply] at hax
      rw [hax, ← algebraMap_smul K s x, smul_smul]
      rw [show (s : K)⁻¹ * (algebraMap (𝓞 K) K s) = 1 from inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    simp only [LinearMap.restrictScalars_apply]
    rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]

end Loc

section LocDel

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpRhoEquiv (lam : DomWeight n) (B : GL (Fin n) K) : VV K (oneW lam) ≃ₗ[K] VV K (oneW lam) :=
  LinearEquiv.ofLinear (rhoK (oneW lam) (fun _ => B)) (rhoK (oneW lam) (fun _ => B⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B) * fun _ => B⁻¹) = 1 := by funext; simp
      rw [this, map_one]; rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B⁻¹) * fun _ => B) = 1 := by funext; simp
      rw [this, map_one]; rfl)

def brpMatEquiv (B : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (B : Matrix (Fin n) (Fin n) K)) (Matrix.mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.mulVecLin_mul]; simp)
    (by rw [← Matrix.mulVecLin_mul]; simp)

theorem brp_lidx_colLat (M : Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K)
    (hB : IsBasisAt w M B) :
    lidx w.asIdeal (colLat (1 : GL (Fin n) K)) M = vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
  have hfull : Submodule.IsFullLattice K (colLat (1 : GL (Fin n) K)) := by
    refine { toIsLattice := brz_colLat_one_lattice K, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    change (Pi.single i 1 : Fin n → K) ∈ colLat (1 : GL (Fin n) K)
    rw [lc_mem_colLat_one]
    simpa [stdLat, Submodule.mem_pi] using (single_mem_stdLat (E := K) (n := n) i 1)
  rw [bridge_lidx_det_holds K (Fin n → K) w (colLat 1) M (brpMatEquiv K B) hfull ?_]
  · show vAdd w (LinearMap.det (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))) = _
    rw [LinearMap.det_toLin']
  · rw [hB, lc_colLat_eq_gLat B]
    rfl

end LocDel

section Sum

end Sum

section Weyl

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]

theorem brp_span_lattice {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {j : ℕ}
    (e : Fin j → V) (hsp : Submodule.span K (Set.range e) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) := by
  exact Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range e))
theorem brp_colLat_one_span (n : ℕ) :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K)) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem brp_lcvInf_std (n : ℕ) :
    Formalism.LFunctionChainParameters.LLcv.lcvInf (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 0 := by
  unfold Formalism.LFunctionChainParameters.LLcv.lcvInf
  have : ∀ v, gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 1 := by
    intro v
    ext a c
    simp only [gramPl, Matrix.of_apply, majAt, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = c
      · subst h; simp
      · simp [Pi.single_apply, Matrix.one_apply, h, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [this]

end Weyl

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def stdHL (N : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := N

theorem brp_hStd_basis (i j : Fin n) :
    hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j) = if i = j then 1 else 0 := by
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, Pi.basisFun_apply, Pi.single_apply]
  split_ifs with h
  · subst h; simp
  · rw [Finset.sum_eq_zero]; intro k _; split_ifs <;> simp_all

theorem brp_hStd_pos (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j))).PosDef := by
  convert Matrix.PosDef.one (n := Fin n) (R := ℂ) using 1
  ext i j
  rw [Matrix.of_apply, brp_hStd_basis, Matrix.one_apply]
  split_ifs <;> simp

theorem brp_formAt_std (v : InfinitePlace K) (x y : Fin n → K) :
    formAt (Pi.basisFun K (Fin n)) (hStd K n) v x y = ∑ i, starRingEnd ℂ (v.embedding (x i)) * v.embedding (y i) := by
  unfold formAt
  simp only [Pi.basisFun_repr, brp_hStd_basis]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem brp_normAt_std (v : InfinitePlace K) (x : Fin n → K) :
    normAt (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x =
      Real.sqrt (formAt (Pi.basisFun K (Fin n)) (hStd K n) v x x).re := by
  rw [brp_formAt_std]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 1
  simp only [inv_one, Matrix.one_mulVec, Complex.re_sum, Pi.basisFun_repr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem brp_latK_mu (N : Submodule (𝓞 K) (Fin n → K)) (hN : N.FG) : (latK K N).mu = (stdHL K N).mu := by
  have hs := formH_spec (Pi.basisFun K (Fin n)) (hStd K n) (brp_hStd_pos K) N
  have h := frame_free K (Fin n → K) (Fin n) (Fin n) (Pi.basisFun K (Fin n)) (latK K N).X (Pi.basisFun K (Fin n))
    (fun _ => 1) hs.1 (fun _ => by simp) (fun v x => by rw [hs.2.2, brp_normAt_std]) N hN
  exact h.2.1

end Std

section Dual

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

end Dual

section Star

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpCO : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

theorem brp_star_smul (c : 𝓞 K) (x : Fin n → K) : star (c • x) = brpCO K c • star x := by
  funext i
  show star (c • x i) = brpCO K c • star (x i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  congr 1

def starLat (N : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) where
  carrier := {x | star x ∈ N}
  add_mem' := by
    intro x y hx hy
    show star (x + y) ∈ N
    rw [star_add]
    exact N.add_mem hx hy
  zero_mem' := by
    show star (0 : Fin n → K) ∈ N
    rw [star_zero]
    exact N.zero_mem
  smul_mem' := by
    intro c x hx
    show star (c • x) ∈ N
    rw [brp_star_smul]
    exact N.smul_mem _ hx

theorem mem_starLat (N : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) : x ∈ starLat K N ↔ star x ∈ N := Iff.rfl

theorem brp_star_mem_span (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span (𝓞 K) S) :
    star y ∈ Submodule.span (𝓞 K) (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smul]; exact Submodule.smul_mem _ _ hx

theorem brp_starLat_span (S : Set (Fin n → K)) :
    starLat K (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K) (star '' S) := by
  ext x
  rw [mem_starLat]
  constructor
  · intro h
    have := brp_star_mem_span K S (star x) h
    rwa [star_star] at this
  · intro h
    have hS : star '' (star '' S) = S := by
      rw [Set.image_image]; simp
    have := brp_star_mem_span K (star '' S) x h
    rwa [hS] at this

end Star

section StarMu

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

theorem brp_star_smulK (a : K) (x : Fin n → K) : star (a • x) = star a • star x := by
  funext i
  show star (a * x i) = star a * star (x i)
  rw [star_mul', mul_comm]

theorem brp_star_mem_spanK (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span K S) :
    star y ∈ Submodule.span K (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smulK]; exact Submodule.smul_mem _ _ hx

theorem brp_star_span_top (S : Set (Fin n → K)) (h : Submodule.span K S = ⊤) : Submodule.span K (star '' S) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have := brp_star_mem_spanK K S (star x) (h ▸ Submodule.mem_top)
  rwa [star_star] at this

theorem brp_starLat_lattice (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (starLat K N) := by
  classical
  obtain ⟨S, hS⟩ := hN.fg
  apply Submodule.IsLattice.of_fg
  refine ⟨S.image star, ?_⟩
  rw [Finset.coe_image, ← brp_starLat_span, hS]

variable [_root_.NumberField.IsTotallyComplex K]

end StarMu

section ESide

variable (E : Type) [Field E] [NumberField E] [StarRing E] {n : ℕ}

variable [_root_.NumberField.IsTotallyComplex E]

end ESide

section Tau

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [_root_.NumberField.IsTotallyComplex E] [Field K] [NumberField K] [StarRing K]
  [_root_.NumberField.IsTotallyComplex K] {n : ℕ}

theorem brp_mu_degT {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (h0 : L ≠ ⊥) (hr : 0 < rkK L) :
    muDef b X L = 2 * Formalism.HermiteSiegelSlopes.degT b X L / (rkK L : ℝ) := by
  rw [T2.mu_eq_log_ht b X hX L hL h0]
  unfold Formalism.HermiteSiegelSlopes.degT
  have h1 : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have h2 : (0 : ℝ) < (rkK L : ℝ) := by exact_mod_cast hr
  field_simp

end Tau

section EE

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end EE

end Formalism.L2.Col
end
end
