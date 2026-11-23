module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqProdOfMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetAevalRoots

open Polynomial

theorem det_aeval_X_sub_C {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (r : Ω) :
    (aeval N (Polynomial.X - C r)).det
      = (N.charpoly.roots.map fun a => (Polynomial.X - C r).eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h : aeval N (Polynomial.X - C r) = -(Matrix.scalar (Fin n) r - N) := by
    simp [Matrix.algebraMap_eq_diagonal]
  rw [h, Matrix.det_neg, Fintype.card_fin, ← Matrix.eval_charpoly]
  conv_lhs => rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic N)]
  rw [eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  have e2 : (N.charpoly.roots.map fun x => x - r)
      = (N.charpoly.roots.map fun x => r - x).map Neg.neg := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun _ _ => by simp)
  rw [e2, Multiset.prod_map_neg, Multiset.card_map, hR]

theorem det_aeval_eq_prod_roots {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (G : Polynomial Ω) :
    (aeval N G).det = (N.charpoly.roots.map fun a => G.eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have key : ∀ (c : Ω) (s : Multiset Ω),
      (aeval N (C c * (s.map fun r => Polynomial.X - C r).prod)).det
        = (N.charpoly.roots.map fun a =>
            (C c * (s.map fun r => Polynomial.X - C r).prod).eval a).prod := by
    intro c s
    induction s using Multiset.induction_on with
    | empty =>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal, hR]
    | cons r s ih =>
      have e : C c * ((r ::ₘ s).map fun r => Polynomial.X - C r).prod
          = (Polynomial.X - C r) * (C c * (s.map fun r => Polynomial.X - C r).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]; ring
      rw [e, map_mul, Matrix.det_mul, ih, det_aeval_X_sub_C, ← Multiset.prod_map_mul]
      simp only [eval_mul]
  have hG := C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((IsAlgClosed.splits G).natDegree_eq_card_roots).symm
  rw [← hG]
  exact key _ _

end GlobalTheory.DetAevalRoots


open Polynomial in
theorem GlobalTheory.det_aeval_eq_prod_aroots_charpoly : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro k Ω V _ _ _ _ _ _ _ φ F
  let b := Module.finBasis k V
  let f := algebraMap k Ω
  have h1 : LinearMap.det (aeval φ F) = (aeval (LinearMap.toMatrix b b φ) F).det := by
    rw [← LinearMap.det_toMatrix b]
    congr 1
    exact (aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom φ F).symm
  have h2 : f.mapMatrix (aeval (LinearMap.toMatrix b b φ) F)
      = aeval ((LinearMap.toMatrix b b φ).map f) (F.map f) := by
    refine map_aeval_eq_aeval_map (φ := f) (ψ := RingHom.mapMatrix (m := Fin (Module.finrank k V)) f) ?_ F _
    ext x i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]
  have h3 : φ.charpoly.aroots Ω = ((LinearMap.toMatrix b b φ).map f).charpoly.roots := by
    rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [h1, RingHom.map_det, h2, h3, GlobalTheory.DetAevalRoots.det_aeval_eq_prod_roots]
  simp only [eval_map_algebraMap, f]
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPolyNorm

open Polynomial GlobalTheory.PolyNorm

theorem eq_prod_aroots : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro Ω _ _ _ d δ P hm hΦ0 hP hPd hPe
  choose Φ hh hΦ using fun r : ℕ => hΦ0 r (fun i : Fin r => (X : ℤ[X]) ^ (i : ℕ))
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → δ F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    have e : ∑ i : Fin r, F.coeff i • (X : ℤ[X]) ^ (i : ℕ) = F := by
      conv_rhs => rw [← gen_coeff F hF]
      unfold gen
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [e] at this
    rw [← this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have h11 : δ 1 = δ 1 * δ 1 := by rw [← hm, _root_.one_mul]
  have h1 : δ 1 = 1 := by
    by_contra hne
    have h0 : δ 1 = 0 := by
      have : δ 1 * (δ 1 - 1) = 0 := by rw [mul_sub, ← h11]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hne
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
        (Set.infinite_range_of_injective Int.cast_injective)
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, IsRoot.def]
      rw [hPe, ← _root_.one_mul (C n - Polynomial.X : ℤ[X]), hm, h0, zero_mul]
    exact hP.ne_zero hP0
  obtain ⟨M, hM⟩ := exists_ext δ Φ hN h1 hm Ω
  have hPP : ev (Φ 2) (C Polynomial.X - Polynomial.X : ℚ[X][X]) = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
      (Set.infinite_range_of_injective Int.cast_injective)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hPe, hN 2 _ (lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)), ← coe_evalRingHom, ev_map]
    congr 1
    simp
  have ha : P.map (algebraMap ℚ Ω) = ((P.aroots Ω).map fun x => Polynomial.X - C x).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hac : Multiset.card (P.aroots Ω) = 2 * d := by
    rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = ((P.aroots Ω).map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M (P.aroots Ω) (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← _root_.mul_one (C c), ev_homog (hh 1), ev_one δ Φ hN h1, _root_.mul_one, hac]
    · have := congrArg (eval β) ha
      rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map, ← coe_eval₂RingHom, ← hPP,
        ev_map, hPP] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  intro F
  have := hMa (F.map (algebraMap ℤ Ω))
  simp only [eval_map_algebraMap] at this
  rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le),
    hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

end GlobalTheory.MulPolyNorm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
open Polynomial

namespace GlobalTheory.AV.AbVar

theorem int_of_charpoly_rat_of_monic_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  intro k V _ _ _ _ _ φ P Q hQ hφ hP
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hPm : P.Monic := Polynomial.monic_of_injective hinj (by rw [hP]; exact LinearMap.charpoly_monic φ)
  set Qq : ℚ[X] := Q.map (algebraMap ℤ ℚ) with hQq
  have hmap : Qq.map (algebraMap ℚ k) = Q.map (algebraMap ℤ k) := by
    rw [hQq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hG : aeval φ (Q.map (algebraMap ℤ k)) = 0 := by
    rw [aeval_map_algebraMap]; exact hφ
  have hd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank φ _ hG
  rw [← hP, ← hmap, ← Polynomial.map_pow, Polynomial.map_dvd_map' (algebraMap ℚ k)] at hd
  have hd' : P ∣ (Q ^ Module.finrank k V).map (algebraMap ℤ ℚ) := by
    rw [Polynomial.map_pow]; exact hd
  obtain ⟨P₀, hP₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ (hQ.pow _) hd'
  refine ⟨P₀, ?_⟩
  rw [hPm.leadingCoeff, Polynomial.C_1, _root_.mul_one] at hP₀
  exact hP₀

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace DetIndexPadic

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {x}) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [Padic.norm_p_pow]

theorem det_ne_zero_of_finite_coker (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T)
    (hc : Nat.card (T ⧸ LinearMap.range φ) ≠ 0) : LinearMap.det φ ≠ 0 := by
  classical
  set n := Nat.card (T ⧸ LinearMap.range φ)
  have hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x := by
    intro x
    have h0 := card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ)
      (x := Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose c hc' using fun i => hk (b i)
  let ψ : T →ₗ[ℤ_[l]] T := b.constr ℤ_[l] c
  have hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id := by
    refine b.ext fun i => ?_
    simp [ψ, hc']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm

theorem norm_det_eq_of_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ),
    Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  intro l _ T _ _ _ _ φ a hcard
  classical
  have hl := (Fact.out : l.Prime)
  have hdet : LinearMap.det φ ≠ 0 := det_ne_zero_of_finite_coker l φ
    (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  set N := LinearMap.range φ with hN
  let e : T ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis ℤ_[l] T
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[l]] N := b'.equiv cb (Equiv.refl _)
  let f : T →ₗ[ℤ_[l]] T := N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)
  have hc : ∀ i, f (b' i) = c i • b' i := by
    intro i
    have : f (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det φ) (LinearMap.det f) at hass
  rw [h1] at hass
  have hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  have hne : ∏ i, c i ≠ 0 := fun h0 => hdet (hass.eq_zero_iff.2 h0)
  obtain ⟨u, hu⟩ := hass
  have h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]
  have h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖ := by
    rw [hcq, Nat.cast_prod, norm_prod, norm_prod]
    exact Finset.prod_congr rfl fun i hi =>
      (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm
  rw [h2, h3, hcard]
  push_cast
  rw [Padic.norm_p_pow]

end DetIndexPadic
end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm

    rw [hx, MultilinearMap.map_sum]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [RingHom.id_apply]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL


open GlobalTheory.LatticeModL in
theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add (f := _), map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
end
