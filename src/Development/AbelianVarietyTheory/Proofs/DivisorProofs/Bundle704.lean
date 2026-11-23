module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
public import Formalism.LocalRingCardinality.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate

namespace GlobalTheory.SUVol.FrameSkew

theorem gram_eq_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sgn_mul_self (p0 a : ℕ) : sgn p0 a * sgn p0 a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_ne_zero (p0 a : ℕ) : sgn p0 a ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

theorem det_ne_of_orth {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (p0 : ℕ)
    (h : gram τ G P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : P.det ≠ 0 := by
  rw [gram_eq_mul] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  intro h0
  rw [h0, zero_mul, zero_mul] at hd
  exact (Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast sgn_ne_zero p0 a) hd.symm

theorem entries_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (hx : IsOrth X x) (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r))
    (hY : fromFrame x Y ∈ realLie X.Ψ X.Gm) :
    (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧
      ∀ τ, ∑ a, Y (τ, a, a) = 0 := by
  have hL := (GlobalTheory.SUVol.DensOne.mem_realLie_iff X.Ψ X.Gm (fromFrame x Y)).1 hY
  have hP : ∀ τ, (mat x τ).det ≠ 0 := fun τ => det_ne_of_orth τ.1 X.Gm (mat x τ) X.p0 (hx τ)
  constructor
  · intro τ a b
    set P := mat x τ with hPdef
    set Ym : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYm
    set Gt := X.Gm.map τ.1
    set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
    have hO : Pᵀ * Gt * P.map (starRingEnd ℂ) = D := by rw [← gram_eq_mul]; exact hx τ
    have hu : IsUnit P.det := isUnit_iff_ne_zero.2 (hP τ)
    have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
    have hinvT : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have hinvC : (P⁻¹).map (starRingEnd ℂ) * P.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM : Matrix.of (fromFrame x Y τ) = P * Ym * P⁻¹ := rfl
    have h1 := (hL τ).1
    rw [hM] at h1
    have h2 : Pᵀ * ((P * Ym * P⁻¹)ᵀ * Gt + Gt * (P * Ym * P⁻¹).map (starRingEnd ℂ)) * P.map (starRingEnd ℂ) = 0 := by
      rw [h1, Matrix.mul_zero, Matrix.zero_mul]
    have h3 : Ymᵀ * D + D * Ym.map (starRingEnd ℂ) = 0 := by
      rw [← h2, ← hO]
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      congr 1
      · rw [← Matrix.mul_assoc Pᵀ P⁻¹ᵀ, hinvT, Matrix.one_mul]
      · rw [hinvC, Matrix.mul_one]
    have h4 := congrFun (congrFun h3 a) b
    simp only [hD, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.map_apply, hYm, Matrix.of_apply, Matrix.zero_apply] at h4
    have hs : ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast sgn_mul_self X.p0 b
    push_cast
    linear_combination (((sgn X.p0 (b : ℕ) : ℝ) : ℂ)) * h4 - Y (τ, b, a) * hs
  · intro τ
    have h1 := (hL τ).2
    have hM : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hP τ)), Matrix.one_mul] at h1
    simpa [Matrix.trace] using h1

end GlobalTheory.SUVol.FrameSkew
end

section

noncomputable section

open ValuativeRel GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.GLDoubling

namespace GlobalTheory.IwahoriUnit

section Gen

variable {G : Type} [Group G]

def cosets (I : Subgroup G) (x : G) : Set (G ⧸ I) :=
  (QuotientGroup.mk : G → G ⧸ I) '' DoubleCoset.doubleCoset x I I

theorem cosets_eq_orbit (I : Subgroup G) (x : G) : cosets I x = MulAction.orbit I (x : G ⧸ I) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * x : G) : G ⧸ I) = ((a * x * b : G) : G ⧸ I)
    rw [QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨a, rfl⟩
    exact ⟨a * x * 1, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, 1, one_mem _, rfl⟩, by rw [mul_one]; rfl⟩

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem fixed_eq_fixd (π : Representation E G V) (I : Subgroup G) : fixed π I = UpperTheory.V.Hi.fixd π I := by
  ext v
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

theorem hk_apply (π : Representation E G V) (I : Subgroup G) (x : G) (h : (cosets I x).Finite)
    (v : UpperTheory.V.Hi.fixd π I) :
    (UpperTheory.V.AlgebraTools.hk π I x v : V) = ∑ᶠ q ∈ cosets I x, π q.out v := by
  rw [cosets_eq_orbit] at h ⊢
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := h
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply E G V π I I x h).1 v, UpperTheory.V.Hi.dc,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem finite_cosets (x : GL (Fin N) k) : (cosets (iwahori k (Fin N)) x).Finite := by
  rw [cosets_eq_orbit, ← (UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1]
  exact (UpperTheory.V.AlgebraTools.heckePairIwC k N ⊤).1 x

theorem dom_of_antitone {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {ν : Fin N → ℤ} (hν : Antitone ν) :
    UpperTheory.V.AlgebraTools.Dom (fun i => ϖ ^ ν i) := by
  intro i j hij
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hν hij)

theorem torusElt_pow (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    torusElt k (Fin N) ϖ ν ^ m = diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m) := by
  rw [map_pow]; rfl

theorem dom_pow {t : Fin N → kˣ} (ht : UpperTheory.V.AlgebraTools.Dom t) (m : ℕ) : UpperTheory.V.AlgebraTools.Dom (t ^ m) := by
  intro i j hij
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_left₀ zero_le' (ht i j hij) m

theorem exists_equiv_doubleCoset (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (ν : Fin N → ℤ) (hν : Antitone ν) (E V : Type) [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (π : Representation E (GL (Fin N) k) V) :
    (∀ m : ℕ, (cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m)).Finite) ∧
    ∃ T : fixed π (iwahori k (Fin N)) ≃ₗ[E] fixed π (iwahori k (Fin N)),
      (∀ v, (T v : V) = ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν), π q.out v) ∧
      ∀ (m : ℕ) v, ((T ^ m) v : V) =
        ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m), π q.out v := by
  refine ⟨fun m => finite_cosets _, ?_⟩
  have hd := dom_of_antitone hϖ hν
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : E) := by
    refine IsUnit.mk0 _ (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul k N ⊤ E V π
  rw [(UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1] at hmul hunit
  rw [fixed_eq_fixd]
  have hone : UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) 1) = 1 := by
    have h := hmul 1 1 UpperTheory.V.AlgebraTools.dom_one UpperTheory.V.AlgebraTools.dom_one
    rw [mul_one] at h
    exact (hunit hq 1 UpperTheory.V.AlgebraTools.dom_one).mul_left_cancel (h.trans (mul_one _).symm)
  have hpow : ∀ m : ℕ, UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) fun i => ϖ ^ ν i) ^ m =
      UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m)) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih => rw [pow_succ, pow_succ, ih, hmul _ _ (dom_pow hd m) hd]
  have hb := (Module.End.isUnit_iff _).1 (hunit hq _ hd)
  refine ⟨LinearEquiv.ofBijective _ hb, fun v => hk_apply π _ _ (finite_cosets _) v, fun m v => ?_⟩
  rw [← hk_apply π _ _ (finite_cosets _) v, torusElt_pow, ← hpow]
  congr 1
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end GlobalTheory.IwahoriUnit
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem perCol_base_smul_form (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ)
    (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

theorem perCol_eq_pairing_of_kills (D : D7) (h : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (φ : D.what₂.Mu u)
    (hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK n hnU, add_zero]

theorem span_range_inf_ker_le_of_basis {K : Type} [Field K] (σ : K →+* ℂ) {W E A I : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module K A]
    [Finite I] {n : ℕ} (b : Module.Basis I K A)
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : A →ₛₗ[σ] E) (f : W →ₗ[ℂ] E) (g : (Fin n → K) →ₗ[K] A)
    (hli : LinearIndependent ℂ (fun i => j' (b i))) (hf : ∀ x, f (j x) = j' (g x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f = Submodule.span ℂ (j '' {x | g x = 0}) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let b' := b.reindex e
  let M := LinearMap.toMatrix' (b'.equivFun.toLinearMap ∘ₗ g)
  have hM : ∀ x, M.mulVec x = b'.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have key := span_range_inf_ker_eq_span_rational_ker σ j
    (j'.comp b'.equivFun.symm.toLinearMap) f M ?_ ?_
  · rw [key]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, hM, EmbeddingLike.map_eq_zero_iff]
  · have h1 : (fun l => (j'.comp b'.equivFun.symm.toLinearMap) (Pi.single l 1))
        = (fun i => j' (b i)) ∘ e.symm := by
      funext l
      simp [b', Pi.single_apply]
    rw [h1]
    exact hli.comp _ e.symm.injective
  · intro x
    rw [hf, hM]
    simp

end GlobalTheory
end

section

open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dite_eq_left h]
  exact h.choose_spec P

end GlobalTheory.FrobEmb
end

section

open Formalism.BasicNotions

namespace GlobalTheory

theorem thick_density_le (D : D7) (L : SizeData₂ D) (h8 : 8 * D.host.Lw < D.R.n) :
    L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  have hn : D.R.n0 ≤ D.R.n := by
    have h : addOrderOf D.R.toFrame.a0 ≤ Fintype.card D.R.toFrame.A := addOrderOf_le_card_univ
    rw [D.R.toFrame.card_A] at h
    exact h
  set n := D.R.n with hn'
  set Lw := D.host.Lw with hLw
  have hL2 : 2 ≤ Lw := D.host.two_le_Lw
  have hrange : ∀ s ∈ D.host.T2, 4 * Lw * s < n := by
    intro s hs; exact lt_of_lt_of_le (D.host.second_set_range s hs) hn
  set N := (n - 1) / (4 * Lw) + 1 with hN
  have hsub : D.host.T2 ⊆ Finset.range N := by
    intro s hs
    have h := hrange s hs
    rw [Finset.mem_range, hN, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
    have : s * (4 * Lw) = 4 * Lw * s := by ring
    omega
  have hN3 : 3 ≤ N := by
    have : 2 ≤ (n - 1) / (4 * Lw) := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    omega
  have hne : ¬ Finset.range N ⊆ D.host.T2 := by
    intro hs
    have h0 : 0 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h1 : 1 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h2 : 2 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have hnr := D.host.second_set_no_relation
    have hL2' : (2 : ℤ) ≤ (Lw : ℤ) := by exact_mod_cast hL2
    exact hnr 0 h0 1 h1 2 h2 (by norm_num) (by norm_num) (by norm_num) 1 2
      (by norm_num) (by simp; omega) (by norm_num) (by rw [abs_of_pos (by norm_num)]; exact hL2')
      (by norm_num) (by norm_num)
  have hcard : D.host.T2.card ≤ (n - 1) / (4 * Lw) := by
    have h1 : D.host.T2.card ≤ N := by simpa using Finset.card_le_card hsub
    have h2 : D.host.T2.card ≠ N := by
      intro heq
      exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [heq])).symm.subset
    omega
  have hmul : D.host.T2.card * (4 * Lw) < n := by
    have := (Nat.le_div_iff_mul_le (by omega)).1 hcard
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < 4 * (Lw : ℝ) := by
    have : (2 : ℝ) ≤ Lw := by exact_mod_cast hL2
    linarith
  rw [L.typeDensity_eq_card_div, div_le_div_iff₀ hnpos hLpos, one_mul]
  have : ((D.host.T2.card * (4 * Lw) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmul.le
  push_cast at this
  linarith

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.RealLift.Dbl

def dblCol {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Ix (R + S) (S + R) → β ⊕ β → ℂ
  | .inl p => Sum.elim (fun r => Sum.elim (fun i => C i (.inl r)) (0 : β → ℂ))
      (fun s => Sum.elim (0 : β → ℂ) (fun i => C i (.inr s))) (finSumFinEquiv.symm p)
  | .inr q => Sum.elim (fun s => Sum.elim (fun i => C i (.inr s)) (0 : β → ℂ))
      (fun r => Sum.elim (0 : β → ℂ) (fun i => C i (.inl r))) (finSumFinEquiv.symm q)

def dblM {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Matrix (β ⊕ β) (Ix (R + S) (S + R)) ℂ :=
  Matrix.of fun i j => dblCol C j i

end GlobalTheory.RealLift.Dbl

end
end

section

open Formalism.L2.DIV

namespace GlobalTheory.IdemChar


open Classical in
theorem sum_coeff_chiIdem_mul {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
    {φ χ : G → K} (hφ : IsAbsIrrChar φ) (hχ : IsAbsIrrChar χ) :
    ∑ g : G, (chiIdem φ).coeff g * χ g = if φ = χ then χ 1 else 0 := by
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  have hc := conv_char hχ hφ 1
  have hre : ∑ s : G, χ s⁻¹ * φ (s * 1) = ∑ g : G, φ g⁻¹ * χ g :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun s => by simp [mul_comm])
  rw [hre] at hc
  have hsum : ∑ g : G, (chiIdem φ).coeff g * χ g
      = ((∑ g : G, φ g⁻¹ * χ g) * φ 1) / (Fintype.card G : K) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_chiIdem]
    ring
  rw [hsum, hc]
  by_cases h : φ = χ
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_div_cancel_left₀ _ hG]
  · have h' : ¬ χ = φ := fun e => h e.symm
    rw [if_neg h', if_neg h, zero_div]

theorem sum_coeff_idemOf_mul : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ χ ∈ X, ∑ g : G, (idemOf X).coeff g * χ g = χ 1 := by
  intro K _ _ G _ _ X hX χ hχ
  classical
  calc ∑ g : G, (idemOf X).coeff g * χ g
      = ∑ g : G, ∑ ψ ∈ X, (chiIdem ψ).coeff g * χ g := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [coeff_idemOf, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [coeff_chiIdem]
    _ = ∑ ψ ∈ X, ∑ g : G, (chiIdem ψ).coeff g * χ g := Finset.sum_comm
    _ = ∑ ψ ∈ X, if ψ = χ then χ 1 else 0 :=
        Finset.sum_congr rfl fun ψ hψ => sum_coeff_chiIdem_mul (hX ψ hψ) (hX χ hχ)
    _ = χ 1 := by simp [hχ]

end GlobalTheory.IdemChar
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.indEtale_localizedPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.indEtale_localPieces_trans | exact GlobalTheory.indEtale_localPieces_trans | (intros; apply GlobalTheory.indEtale_localPieces_trans <;> assumption)
end
