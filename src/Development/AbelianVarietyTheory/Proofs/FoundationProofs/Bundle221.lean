module

public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Formalism.QuotientMetricDivisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle002
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle110
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PadicPlaceBound

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

def smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) : Ideal (𝓞 K) where
  carrier := {a | ‖φ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have h := IsUltrametricDist.norm_add_le_max (φ (a : K)) (φ (b : K))
    have h2 : φ ((a + b : 𝓞 K) : K) = φ (a : K) + φ (b : K) := by simp
    change ‖φ ((a + b : 𝓞 K) : K)‖ < 1
    rw [h2]
    exact h.trans_lt (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    have h2 : φ ((c • a : 𝓞 K) : K) = φ (c : K) * φ (a : K) := by simp
    change ‖φ ((c • a : 𝓞 K) : K)‖ < 1
    rw [h2, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
      (map_isIntegral_int φ c.isIntegral_coe))).trans_lt ha

theorem mem_smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    a ∈ smallIdeal φ ↔ ‖φ (a : K)‖ < 1 := Iff.rfl

theorem norm_int_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    ‖φ (a : K)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int φ a.isIntegral_coe)

theorem smallIdeal_isPrime {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) :
    (smallIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    by_contra h
    rw [not_or, mem_smallIdeal, mem_smallIdeal, not_lt, not_lt] at h
    have h2 : φ ((a * b : 𝓞 K) : K) = φ (a : K) * φ (b : K) := by simp
    rw [mem_smallIdeal, h2, norm_mul] at hab
    exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)

theorem exists_embedding_smallIdeal_eq {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] {l : ℕ} (hl : l.Prime) (hlC : ‖(l : C)‖ < 1) (w : HeightOneSpectrum (𝓞 K))
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : ∃ φ : K →+* C, smallIdeal φ = w.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ φ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] C)) : Set (K →ₐ[ℚ] C)), (smallIdeal φ.toRingHom : Set (𝓞 K)) := by
    intro a ha
    by_contra hna
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
      not_exists, mem_smallIdeal, not_lt] at hna
    have h1 : ∀ φ : K →ₐ[ℚ] C, ‖φ (a : K)‖ = 1 := fun φ =>
      le_antisymm (norm_int_le_one φ.toRingHom a) (hna φ)
    have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ C (a : K))
    rw [norm_prod, Finset.prod_eq_one (fun φ _ => h1 φ), ← Algebra.coe_norm_int, map_intCast] at h2
    have h3 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).2 ha (Ideal.absNorm_mem _)
    rw [Ideal.absNorm_span_singleton] at h3
    have h4 : l ∣ (Algebra.norm ℤ a).natAbs := by
      by_contra hnd
      have hc : IsCoprime (l : 𝓞 K) (((Algebra.norm ℤ a).natAbs : ℕ) : 𝓞 K) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨u, v, huv⟩ := hc
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hw) (w.asIdeal.mul_mem_left v h3)))
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h4
    rw [hc, Int.cast_mul, Int.cast_natCast, norm_mul] at h2
    have h5 := (mul_le_of_le_one_right (norm_nonneg (l : C))
      (IsUltrametricDist.norm_intCast_le_one C c)).trans_lt hlC
    exact absurd h2 h5.ne
  have φ₀ : K →ₐ[ℚ] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨φ, -, hφ⟩ := (Ideal.subset_union_prime φ₀ φ₀
    (fun φ _ _ _ => smallIdeal_isPrime φ.toRingHom)).1 hsub
  exact ⟨φ.toRingHom, (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hφ).symm⟩

theorem norm_le_one_of_valuation_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C)
    (w : HeightOneSpectrum (𝓞 K)) (hφ : smallIdeal φ = w.asIdeal) (y : K) (hy : w.valuation K y ≤ 1) :
    ‖φ y‖ ≤ 1 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
  have hd' : d ∉ smallIdeal φ := by rw [hφ]; exact hd
  rw [mem_smallIdeal, not_lt] at hd'
  have h1 : ‖φ y‖ * ‖φ (d : K)‖ = ‖φ (n : K)‖ := by
    rw [← norm_mul, ← map_mul]
    exact congrArg (fun z => ‖φ z‖) hnd
  calc ‖φ y‖ ≤ ‖φ y‖ * ‖φ (d : K)‖ := le_mul_of_one_le_right (norm_nonneg _) hd'
    _ = ‖φ (n : K)‖ := h1
    _ ≤ 1 := norm_int_le_one φ n

theorem exists_lamC_eq {l : ℕ} [Fact l.Prime] (σ : K →+* ℂ) (φ : K →+* ℂ_[l]) :
    ∃ lam : Qbar →+* ℂ_[l], ∀ x : K, lamC lam (σ x) = φ x := by
  have hmem : ∀ x : K, σ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  let σ' : K →+* Qbar := σ.codRestrict Qbar hmem
  letI : Algebra K Qbar := σ'.toAlgebra
  letI : Algebra K ℂ_[l] := φ.toAlgebra
  haveI : IsScalarTower ℚ K Qbar := IsScalarTower.of_algebraMap_eq fun q =>
    ((eq_ratCast (algebraMap ℚ Qbar) q).trans (map_ratCast σ' q).symm).trans
      (congrArg σ' (eq_ratCast (algebraMap ℚ K) q).symm)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic K Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let lam : Qbar →ₐ[K] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lam.toRingHom, fun x => ?_⟩
  unfold lamC
  rw [dite_eq_left (hmem x)]
  exact lam.commutes x

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    ← Padic.norm_p]
  exact PadicAlgCl.norm_extends l _

theorem neg_mul_vw_le_vw : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (l : ℕ) [Fact l.Prime] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e : ℝ), x ≠ 0 → (l : 𝓞 K) ∈ w.asIdeal → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam (σ x)‖ ≤ (l : ℝ) ^ e) → -(e * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w x : ℝ) := by
  intro K _ _ σ x l hl w e hx hw h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := one_pos.trans hl1
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  obtain ⟨φ, hφ⟩ := exists_embedding_smallIdeal_eq (C := ℂ_[l]) hl.out
    (by rw [norm_prime_padicComplex]; exact inv_lt_one_of_one_lt₀ hl1) w hw
  obtain ⟨lam, hlam⟩ := exists_lamC_eq σ φ
  have hb := h lam
  rw [hlam] at hb
  have hvx : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  have hvl : w.valuation K (l : K) = WithZero.exp (-Formalism.DivisionValues.vw w (l : K)) :=
    GlobalTheory.Idele.valuation_eq_exp_neg_count w hlK
  set n := Formalism.DivisionValues.vw w x
  set m := Formalism.DivisionValues.vw w (l : K)
  have hm : 0 ≤ m := by
    have h1 : w.valuation K (l : K) ≤ 1 := by
      simpa using w.valuation_le_one (K := K) (l : 𝓞 K)
    rw [hvl, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  have hy : w.valuation K ((l : K) ^ n / x ^ m) ≤ 1 := by
    rw [map_div₀, map_zpow₀, map_zpow₀, hvx, hvl, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    nlinarith
  have h1 := norm_le_one_of_valuation_le_one φ w hφ _ hy
  have hφx : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  rw [map_div₀, map_zpow₀, map_zpow₀, norm_div, norm_zpow, norm_zpow, map_natCast,
    norm_prime_padicComplex, div_le_one (zpow_pos hφx _)] at h1
  have h2 : ‖φ x‖ ^ m ≤ ((l : ℝ) ^ e) ^ m := zpow_le_zpow_left₀ hm hφx.le hb
  have h3 := h1.trans h2
  rw [inv_zpow', ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hl0.le,
    Real.rpow_le_rpow_left_iff hl1] at h3
  push_cast at h3
  linarith

end GlobalTheory.PadicPlaceBound
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LcvSub

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_eq {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m k ℂ) (B : Matrix n k ℂ) (h : Aᴴ * A = Bᴴ * B) (u : k → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ u) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  apply Complex.ofReal_injective
  rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fcoord_std {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  congr 1

theorem gram_eq {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))ᴴ *
      ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply]

theorem gram_single {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  have h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Function.swap, Pi.single_apply]
    · simp [hab, Matrix.one_apply]
  rw [gram_eq, h, Matrix.mul_one]

end GlobalTheory.LcvSub


open GlobalTheory.LcvSub in
theorem GlobalTheory.neg_rank_mul_log_le_lcv : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint
  classical
  set j := Formalism.HN.rkK L with hj
  let W : Submodule K (Fin d → K) := Submodule.span K (L : Set (Fin d → K))
  let b : Module.Basis (Fin j) K W := Module.finBasis K W
  let e : Fin j → Fin d → K := fun a => (b a : Fin d → K)
  have he : LinearIndependent K e := b.linearIndependent.map' W.subtype W.ker_subtype
  let ψ : (Fin j → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Injective ψ := W.injective_subtype.comp b.equivFun.symm.injective
  have hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x := by
    intro x
    ext i
    simp [ψ, e, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : LinearMap.range ψ = W := by
    simp [ψ, LinearMap.range_comp]
  obtain ⟨hne, hpos⟩ := GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he
  choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)
  let L' : Submodule (𝓞 K) (Fin j → K) := L.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have : x ∈ LinearMap.range ψ := by
      rw [hrange]; exact Submodule.subset_span hx
    exact this
  have hfg : L'.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)
  have hlat : Submodule.IsFullLattice K L' := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }
    apply LinearMap.map_injective (LinearMap.ker_eq_bot.mpr hψ)
    have himage : ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K)) :=
      congrArg (fun M : Submodule (𝓞 K) (Fin d → K) => (M : Set (Fin d → K))) hmap
    rw [← Submodule.span_image, himage, Submodule.map_top, hrange]
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x := by
    intro v x
    unfold Formalism.HermitianLatticesTheory.normAt
    rw [fcoord_std, fcoord_std,
      cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))
        (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]
    congr 2
    ext i
    rw [hψE]
    simp [Matrix.mulVec, dotProduct]
  have hht := (Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X'
    (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1
  rw [hmap] at hht
  have hlcv : lcv X L = lcv X' L' := by
    unfold lcv; rw [hht]
  rw [hlcv]
  refine GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' (by first | exact hlat | exact hlat.toIsLattice) ?_
  · have h := GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e
    simp only [gram_single, hX'g]
    exact h
  · intro x hx y hy
    have h := hint (ψ x) hx (ψ y) hy
    have hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) =
        ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ) := by
      ext a c
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] at h
    rw [hG]
    exact h
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CompactCoverIrr

theorem isKC_of_compact {n : ℕ} (X : Mat n 0) : IsKC X := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

theorem map_stable {n : ℕ} (hn : 1 ≤ n) (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hj : IsHCMod τ M j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) (g : T.G) : ∀ x ∈ N.map j, τ.π g x ∈ N.map j := by
  have hg := GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T g (isKC_of_compact _)
  have key : (∀ x ∈ N.map j, τ.π g x ∈ N.map j) ∧ (∀ x ∈ N.map j, τ.π g⁻¹ x ∈ N.map j) := by
    induction hg using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨X, ⟨hX, -⟩, rfl⟩ := hk
      have hf := GlobalTheory.RealPar.flow_mem_map j (M.act X) N (hN X) (fun t => τ.π (T.expt (t • X)))
        (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (hj.2.2 X hX)
      have hinv : (T.expt X)⁻¹ = T.expt ((-1 : ℝ) • X) := by
        have h := T.expt_add X hX 1 (-1)
        rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at h
        exact (eq_inv_of_mul_eq_one_right h.symm).symm
      refine ⟨?_, ?_⟩
      · have := hf 1
        rwa [one_smul] at this
      · rw [hinv]
        exact hf (-1)
    | one => refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simpa using hx
    | mul a b _ _ ha hb =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_mul]
        exact ha.1 _ (hb.1 x hx)
      · rw [mul_inv_rev, map_mul]
        exact hb.2 _ (ha.2 x hx)
    | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
  exact key.1

theorem eq_bot_or_top {n : ℕ} (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hτ : IrrU τ) (hj : Function.Injective j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ g, ∀ x ∈ N.map j, τ.π g x ∈ N.map j) : N = ⊥ ∨ (N = ⊤ ∧ N.map j = ⊤) := by
  rcases hτ.2 (N.map j) (Submodule.closed_of_finiteDimensional _) hN with h | h
  · left
    apply Submodule.map_injective_of_injective hj
    rw [h, Submodule.map_bot]
  · right
    refine ⟨?_, h⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ : j v ∈ N.map j := h ▸ Submodule.mem_top
    exact hj hwv ▸ hw

theorem hcMod_finite_irr : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n hn T τ M j hτ hj hM
  obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
  obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
  have hW := (eq_bot_or_top T τ M j hτ hj.1 W
    (map_stable hn T τ M j hj W fun Z => hWs Z (isKC_of_compact Z))).resolve_left
    (fun h => hv (by rw [h] at hvW; exact hvW))
  have hfin : FiniteDimensional ℂ M.V := by
    rw [hW.1] at hWf
    exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule ℂ M.V) ≃ₗ[ℂ] M.V)
  have hsurj : ∀ x, ∃ v', j v' = x := fun x => by
    obtain ⟨w, -, hw⟩ : x ∈ W.map j := hW.2 ▸ Submodule.mem_top
    exact ⟨w, hw⟩
  refine ⟨hfin, ⟨hM, fun N hN => ?_⟩, fun h v => hsurj _, fun N hN => ?_⟩
  · exact (eq_bot_or_top T τ M j hτ hj.1 N (map_stable hn T τ M j hj N hN)).imp_right And.left
  · refine (eq_bot_or_top T τ M j hτ hj.1 N ?_).imp_right And.left
    rintro g _ ⟨w, hw, rfl⟩
    obtain ⟨v', hv'⟩ := hsurj (τ.π g (j w))
    exact ⟨v', hN g w hw v' hv', hv'⟩

end GlobalTheory.CompactCoverIrr
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

def cval (g : GL3Theta.G1 p) (s : ℂ) : ℂ_[p] := lamC g.lam (U1 g.abelian₂ s (sgStar g.abelian₂) 0)

def tau (g : GL3Theta.G1 p) (s : ℂ) : PowerSeries ℂ_[p] :=
  (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ s (sgStar g.abelian₂))

def logc (g : GL3Theta.G1 p) (s : ℂ) : ℝ := if s ∈ g.abelian₂ then 0 else Real.log ‖cval g s‖

end GlobalTheory.ThetaTransl
end
end
