module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem coord_injective_range_mem : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → IsCrys PD T.ρ → Function.Injective (coord W R jE T (fun k => (b k : W.DD T))) ∧ LinearMap.range (coord W R jE T (fun k => (b k : W.DD T))) = DDinv W T ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF hE hb hc
  obtain ⟨-, hFr, -⟩ := hF
  obtain ⟨hext, hinj, hEr, -⟩ := hE
  let c : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hc).basis b
  have hcb : ∀ k, c k = (b k : W.DD T) := fun k => IsBaseChange.basis_apply b (W.N_base T hc) k
  have huniq : ∀ y y' : Fin r → W.EE,
      ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y' := by
    intro y y' h
    apply c.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply, hcb]
    exact h
  have hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m := by
    intro m
    refine ⟨c.repr m, ?_⟩
    simp only [← hcb]
    exact c.sum_repr m
  have hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) =
      ∑ k, W.γE δ (y k) • (b k : W.DD T) := by
    intro δ hδ y

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, (hb k).2 δ hδ]
  have hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) =
      coord W R jE T (fun k => (b k : W.DD T)) x := by
    intro x δ hδ
    rw [coord_apply, hγ δ hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hEr _).1 ⟨_, rfl⟩ δ hδ]
  refine ⟨?_, ?_, ?_⟩
  · intro x x' h
    have := huniq _ _ h
    funext i k
    exact congrFun (hinj (congrFun this k)) i
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hinv x
    · intro m hm
      obtain ⟨y, rfl⟩ := hex m
      have hy : ∀ k, ∃ x, jE x = y k := fun k => (hEr _).2 fun δ hδ =>
        congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k
      choose x hx using hy
      refine ⟨fun i k => x k i, ?_⟩
      rw [coord_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k]
  · intro x
    constructor
    · rintro ⟨hN, -⟩
      set a := b.repr ⟨_, hN⟩ with ha
      have h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) =
          ∑ k, jE (fun i => x i k) • (b k : W.DD T) := by
        have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)

        rw [map_sum] at this
        simp only [algebraMap_smul]
        exact this
      have h2 := huniq _ _ h1
      intro i k _
      have h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k) := congrFun h2 k
      have h4 : ∀ i', ∃ a', j a' = a k i' := fun i' => (hFr _).2 fun δ hδ => by
        have h5 := (hEr _).1 ⟨_, h3.symm⟩ δ hδ
        rw [W.γE_ext] at h5
        exact congrFun (W.EE_inj h5) i'
      choose a' ha' using h4
      have h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k) := by
        rw [hext, ← h3]
        congr 1
        funext i'
        exact ha' i'
      exact ⟨a' i, congrFun (hinj h6) i⟩
    · intro hx
      refine ⟨?_, hinv x⟩
      rw [coord_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h4 : ∀ i, ∃ a', R.ι a' = x i k := fun i => hx i k (Set.mem_univ _)
      choose a' ha' using h4
      have : (fun i => x i k) = fun i => R.ι (a' i) := funext fun i => (ha' i).symm
      rw [this, hext, algebraMap_smul]
      exact (W.N T).smul_mem _ (b k).2

end GlobalTheory.WachTie
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

open Matrix

theorem schurSquareMatrixToBlocks_mul {R : Type} [CommRing R] {m r : ℕ} (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk (M * N) = blk M * blk N := by
  simp only [blk]
  exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem schur_mul_conjLowUni : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  intro R _ m r g k hD hD'
  have hL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R, blk (lowUni Z) = fromBlocks 1 0 Z 1 :=
    fun Z => blk_unblk _
  have hLL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R,
      fromBlocks (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 (-Z) (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) * fromBlocks 1 0 Z 1 = 1 := by
    intro Z
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  set Y := Yof g with hY
  set k' := conjLowUni Y k with hk'
  have hK : blk k' = fromBlocks 1 0 Y 1 * blk k * fromBlocks 1 0 (-Y) 1 := by
    rw [hk', conjLowUni, schurSquareMatrixToBlocks_mul, schurSquareMatrixToBlocks_mul, hL, hL]
  have hkk : blk k = fromBlocks 1 0 (-Y) 1 * blk k' * fromBlocks 1 0 Y 1 := by
    rw [hK]
    calc blk k = 1 * blk k * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) * blk k * (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) := by
          rw [hLL]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hG : blk g = fromBlocks (Aof g) (Bof g) (Cof g) (Dof g) := (fromBlocks_toBlocks _).symm
  have hK' : blk k' = fromBlocks (Aof k') (Bof k') (Cof k') (Dof k') := (fromBlocks_toBlocks _).symm
  set A := Aof g
  set B := Bof g
  set C := Cof g
  set D := Dof g
  set A' := Aof k'
  set B' := Bof k'
  set C' := Cof k'
  set D' := Dof k'
  set Sc := Scof g with hSc
  have i1 : D⁻¹ * D = 1 := nonsing_inv_mul D hD
  have i2 : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have i3 : D'⁻¹ * D' = 1 := nonsing_inv_mul D' hD'
  have i4 : D' * D'⁻¹ = 1 := mul_nonsing_inv D' hD'
  have j1 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D⁻¹ * (D * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D * (D⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have j3 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D'⁻¹ * (D' * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i3, Matrix.one_mul]
  have j4 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D' * (D'⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i4, Matrix.one_mul]
  have hGL : blk g * fromBlocks 1 0 (-Y) 1 = fromBlocks Sc B 0 D := by
    rw [hG, fromBlocks_multiply]
    congr 1
    · rw [hSc, Scof, hY, Yof]; simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.mul_assoc]; abel
    · simp
    · have hDY : D * Y = C := j2 C
      rw [Matrix.mul_one, Matrix.mul_neg, hDY, add_neg_cancel]
    · simp
  have hprod : blk (g * k) = fromBlocks (Sc * A' + B * C' + (Sc * B' + B * D') * Y) (Sc * B' + B * D')
      (D * C' + D * D' * Y) (D * D') := by
    rw [schurSquareMatrixToBlocks_mul, hkk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGL, hK', fromBlocks_multiply, fromBlocks_multiply]
    simp
  have eD : Dof (g * k) = D * D' := by simp only [Dof, hprod, toBlocks_fromBlocks₂₂]
  have eC : Cof (g * k) = D * C' + D * D' * Y := by simp only [Cof, hprod, toBlocks_fromBlocks₂₁]
  have eB : Bof (g * k) = Sc * B' + B * D' := by simp only [Bof, hprod, toBlocks_fromBlocks₁₂]
  have eA : Aof (g * k) = Sc * A' + B * C' + (Sc * B' + B * D') * Y := by simp only [Aof, hprod, toBlocks_fromBlocks₁₁]
  refine ⟨?_, eD, ?_, ?_, ?_⟩
  · rw [eD, det_mul]; exact hD.mul hD'
  · rw [Yof, Yof, eD, eC, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.mul_assoc, j1, j3]
    abel
  · rw [Scof, Scof, eA, eB, eC, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, j1, j3, j4]
    abel
  · rw [Xof, Xof, Xof, eB, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, j4, i4]
    abel

end GlobalTheory.SchurExt
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem residue_generates : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  intro K K' d φ hU B ψ hψ hnt hO s Q hQm hQg hQr y
  set Ψ : K'.O →+* B.A := ψ.comp (algebraMap K'.O K'.E) with hΨdef
  have hΨφ : ∀ a : K.O, Ψ (intMap hU a) = algebraMap K.O B.A a := by
    intro a
    simp only [Ψ, RingHom.comp_apply, intMap_spec, hψ]
    exact (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hcomp : (algebraMap K'.O K'.E).comp (intMap hU) = φ.comp (algebraMap K.O K.E) := by
    ext a; simp [intMap_spec]
  obtain ⟨f, hf⟩ : ∃ f : K.O[X], aeval B.g f = ψ (algebraMap K'.O K'.E y) := by
    have := hO y
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  refine ⟨f, y - f.eval₂ (intMap hU) s, ?_, ?_⟩
  swap
  · rw [map_sub, Polynomial.hom_eval₂, hcomp]; ring

  by_contra hz
  have hzu : IsUnit (y - f.eval₂ (intMap hU) s) := by
    by_contra h; exact hz ((IsLocalRing.mem_maximalIdeal _).2 h)
  set z := y - f.eval₂ (intMap hU) s with hzdef
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hRdef
  haveI := hnt

  have hΨz : Ψ z = aeval B.g f - aeval (Ψ s) f := by
    rw [hzdef, map_sub, hf, Polynomial.hom_eval₂]
    have : Ψ.comp (intMap hU) = algebraMap K.O B.A := by ext a; exact hΨφ a
    rw [this]; rfl
  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let x' : R := ⟨Ψ s, hO s⟩
  obtain ⟨h, hh⟩ := Polynomial.sub_dvd_eval_sub g' x' (f.map (algebraMap K.O R))
  have hh' : Ψ z = (B.g - Ψ s) * (h : B.A) := by
    rw [hΨz]
    have := congrArg Subtype.val hh
    simp only [Polynomial.eval_map_algebraMap, Subalgebra.coe_sub, Subalgebra.coe_mul,
      Polynomial.aeval_subalgebra_coe] at this
    exact this

  obtain ⟨zu, hzu'⟩ := hzu
  let zi : R := ⟨Ψ ((zu⁻¹ : K'.Oˣ) : K'.O), hO _⟩
  have hunit : (g' - x') * (h * zi) = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, g', x', zi]
    rw [← mul_assoc, ← hh', ← hzu', ← map_mul, Units.mul_inv, map_one]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hmax : IsLocalRing.maximalIdeal K'.O = Ideal.span {intMap hU ϖ} := by
    rw [← map_maximalIdeal hU, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.map_span, Set.image_singleton]
  have hdvd : C (intMap hU ϖ) ∣ Q - (X - C s) ^ Q.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [← Ideal.mem_span_singleton, ← hmax, ← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map,
      Polynomial.map_sub, hQr]
    simp
  obtain ⟨R', hR'⟩ := hdvd
  have hev := congrArg (Polynomial.eval₂ Ψ B.g) hR'
  rw [Polynomial.eval₂_sub, hQg, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hΨφ] at hev
  have hRmem : ∀ P : K'.O[X], P.eval₂ Ψ B.g ∈ R := by
    intro P
    rw [Polynomial.eval₂_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ =>
      Subalgebra.mul_mem _ (hO _) (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O B.g) _)
  let r : R := ⟨R'.eval₂ Ψ B.g, hRmem R'⟩
  have hpow : (g' - x') ^ Q.natDegree = -(algebraMap K.O R ϖ * r) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_neg, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, g', x', r]
    rw [← hev]; ring
  set u := h * zi
  have hinv : algebraMap K.O R ϖ * (-(r * u ^ Q.natDegree)) = 1 := by
    have : ((g' - x') * u) ^ Q.natDegree = 1 := by rw [hunit, one_pow]
    rw [mul_pow, hpow] at this
    rw [← this]; ring

  letI : Algebra K'.O B.A := Ψ.toAlgebra
  have hgint : IsIntegral K'.O B.g := ⟨Q, hQm, hQg⟩
  have hRint : ∀ w ∈ R, IsIntegral K'.O w := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hgint
    | algebraMap a =>
      rw [← hΨφ a]; exact isIntegral_algebraMap (R := K'.O) (x := intMap hU a)
    | add x y _ _ hx hy => exact hx.add hy
    | mul x y _ _ hx hy => exact hx.mul hy
  set v : R := -(r * u ^ Q.natDegree)
  have hvint : IsIntegral K'.O (v : B.A) := hRint _ v.2
  have hv1 : Ψ (intMap hU ϖ) * (v : B.A) = 1 := by
    have := congrArg Subtype.val hinv
    simpa [hΨφ] using this
  have hϖ0 : intMap hU ϖ ≠ 0 := fun h0 => hϖ.ne_zero ((intMap_injective hU) (by rw [h0, map_zero]))
  have hπ0 : algebraMap K'.O K'.E (intMap hU ϖ) ≠ 0 := by
    intro h0; exact hϖ0 (IsFractionRing.injective K'.O K'.E (by rw [h0, map_zero]))
  set t : K'.E := (algebraMap K'.O K'.E (intMap hU ϖ))⁻¹
  have hψt : ψ t = v := by
    have h1 : Ψ (intMap hU ϖ) * ψ t = 1 := by
      rw [hΨdef, RingHom.comp_apply, ← map_mul, mul_inv_cancel₀ hπ0, map_one]
    calc ψ t = ((v : B.A) * Ψ (intMap hU ϖ)) * ψ t := by rw [mul_comm (v : B.A), hv1, one_mul]
      _ = v := by rw [mul_assoc, h1, mul_one]
  let ψA : K'.E →ₐ[K'.O] B.A := { toRingHom := ψ, commutes' := fun _ => rfl }
  have htint : IsIntegral K'.O t := by
    rw [← isIntegral_algHom_iff ψA ψ.injective]
    show IsIntegral K'.O (ψ t)
    rw [hψt]; exact hvint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 htint
  have hb1 : intMap hU ϖ * b = 1 := by
    apply IsFractionRing.injective K'.O K'.E
    rw [map_mul, hb, mul_inv_cancel₀ hπ0, map_one]
  have hmem : intMap hU ϖ ∈ IsLocalRing.maximalIdeal K'.O := by
    rw [hmax]; exact Ideal.subset_span rfl
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem ⟨⟨_, b, hb1, by rw [mul_comm]; exact hb1⟩, rfl⟩

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.MeetsGen

noncomputable section
namespace GlobalTheory.MeetsTypeVec

theorem lift_apply_mem {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (W : Submodule K V) (hW : ∀ g x, x ∈ W → φ g x ∈ W)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ W) :
    MonoidAlgebra.lift K (Module.End K V) G φ a x ∈ W := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => by
    rw [LinearMap.smul_apply]; exact W.smul_mem _ (hW g x hx)

theorem proj_eigen {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (y : V) (u' : U) :
    φ u' (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y)
      = ((ψ u' : Kˣ) : K) • MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y := by
  have hφ : ∀ u : U, φ u' (φ u y) = φ ((u' * u : U) : G) y := by
    intro u; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

  simp only [pU, map_sum, MonoidAlgebra.lift_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
  Finset.smul_sum, hφ]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, smul_smul]
  congr 1
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : ((ψ u' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

theorem meets : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  intro K G V _ _ _ _ _ ρ U _ ψ e b he W hW0 hWs hWe
  set φ : G →* Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hφdef
  have hφ : ∀ g x, φ g x = ρ g x := fun _ _ => rfl
  have hWs' : ∀ g x, x ∈ W → φ g x ∈ W := fun g x hx => by rw [hφ]; exact hWs g x hx
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : x = ∑ g : G, φ g (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x)) := by
    conv_lhs => rw [← hWe x hxW, he]

    simp only [map_sum, map_mul, MonoidAlgebra.lift_single, one_smul, LinearMap.sum_apply, Module.End.mul_apply]
  intro hbot
  apply hx0
  rw [hsum]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hmem : MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x) ∈
      W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) := by
    refine ⟨lift_apply_mem φ W hWs' _ (lift_apply_mem φ W hWs' _ hxW), ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun u => LinearMap.mem_ker.2 ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ← hφ, proj_eigen,
      sub_self]
  rw [hbot] at hmem
  rw [(Submodule.mem_bot K).1 hmem, map_zero]

end GlobalTheory.MeetsTypeVec
end
end

section

open Matrix

namespace GlobalTheory.MulVecProduct

theorem mulVec_eq_prod_smul {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ}
    (h1 : Φ (1 : ι → GL (Fin n) ℂ) = (1 : Matrix κ κ ℂ))
    (hmul : ∀ (g h : ι → GL (Fin n) ℂ), Φ (g * h) = Φ g * Φ h)
    {v : κ → ℂ} {lam : ι → Fin n → ℤ}
    (hv : ∀ (τ : ι), GlobalTheory.AlgWtHW.IsBEig (fun (B : GL (Fin n) ℂ) ↦ Φ (Pi.mulSingle τ B)) v (lam τ))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ (τ : ι), Matrix.BlockTriangular (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) id) :
    Matrix.mulVec (Φ g) v =
      (∏ τ : ι, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
  classical
  have key : ∀ S : Finset ι, Φ (fun τ => if τ ∈ S then g τ else 1) *ᵥ v =
      (∏ τ ∈ S, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1 := by
        funext τ
        simp
      rw [h0, h1, Finset.prod_empty, one_smul, Matrix.one_mulVec]
    | insert a S ha ih =>
      have hsplit : (fun τ => if τ ∈ insert a S then g τ else 1) =
          Pi.mulSingle a (g a) * (fun τ => if τ ∈ S then g τ else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · simp [hτ]
      have ha' := (hv a).2 (g a) (hg a)
      simp only at ha'
      rw [hsplit, hmul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ha', smul_smul,
        Finset.prod_insert ha]
      congr 1
      ring
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset ι) then g τ else 1) = g := by
    funext τ
    simp
  have := key Finset.univ
  rw [hall] at this
  exact this

end GlobalTheory.MulVecProduct
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  first | exact @GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | exact GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | (intros; apply GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_finExt_embedding_splitting' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  first | exact @GlobalTheory.exists_finExt_embedding_splitting | exact GlobalTheory.exists_finExt_embedding_splitting | (intros; apply GlobalTheory.exists_finExt_embedding_splitting <;> assumption)
end
