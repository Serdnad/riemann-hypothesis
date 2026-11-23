module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle280
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle266
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle283
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.NormVal

section General

variable {K : Type*} [Field K]

end General

open GlobalTheory.Per.Val

open TensorProduct in
private lemma addValuation_pow_mul_pow_div_pow {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℚ)) {π : F} (hu : u π = 1) {x : F} {t : ℚ} (hx : u x = t)
    (b M N : ℕ) : u (x ^ b * π ^ M / π ^ N) = ((b * t + M - N : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_div, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_pow, hx, hu]
  norm_cast
  simp [nsmul_eq_mul]

open TensorProduct in
private lemma le_of_nonneg_imp_nonneg {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ)) {π : F}
    (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y → 0 ≤ w y) {x : F} {t s : ℚ}
    (hvx : v x = t) (hwx : w x = s) : t ≤ s := by
  have hMN : ((t.num.toNat : ℕ) : ℚ) - ((-t.num).toNat : ℕ) = t.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg t.num
  have hbt : (t.den : ℚ) * t = t.num := by rw [mul_comm]; exact Rat.mul_den_eq_num t
  have hy := h (x ^ t.den * π ^ (-t.num).toNat / π ^ t.num.toNat) (by
    rw [addValuation_pow_mul_pow_div_pow v hv hvx]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t.den * t + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ)))
  rw [addValuation_pow_mul_pow_div_pow w hw hwx] at hy
  have hy' : (0 : ℚ) ≤ t.den * s + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ) := by exact_mod_cast hy
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  nlinarith

open TensorProduct in
private lemma addValuation_eq_of_nonneg_iff {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ))
    {π : F} (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y ↔ 0 ≤ w y) (x : F) : v x = w x := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff v).mp hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff w).mp hx)
  rw [← ht, ← hs]
  have h1 := le_of_nonneg_imp_nonneg v w hv hw (fun y => (h y).mp) ht.symm hs.symm
  have h2 := le_of_nonneg_imp_nonneg w v hw hv (fun y => (h y).mpr) hs.symm ht.symm
  exact congrArg _ (le_antisymm h1 h2)


open TensorProduct in
theorem _root_.GlobalTheory.HWL.NormVal.locPrime_v_normalised : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), (∀ (x : ↥LL.1) (q : ℚ), P.v LL x = (q : WithTop ℚ) ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-(q : ℝ))) ∧ (∀ (x : ↥LL.1) (q : ℚ), (q : WithTop ℚ) ≤ P.v LL x ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ (l : ℝ) ^ (-(q : ℝ))) ∧ ∀ x : ↥LL.1, x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  intro l _ P LL
  set w : AddValuation (↥LL.1) (WithTop ℚ) :=
    (_root_.GlobalTheory.Per.Val.vOm l).comap (algebraMap (↥LL.1) (_root_.Formalism.BasicNotions.Loc.Om l)) with hwdef
  have hwx : ∀ x : ↥LL.1, w x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x => rfl
  have hw : w (l : ↥LL.1) = 1 := by
    rw [hwx]
    have : ((l : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l) = (l : _root_.Formalism.BasicNotions.Loc.Om l) := by simp
    rw [this]
    exact _root_.GlobalTheory.Per.Val.vf_l
  have hnn : ∀ y : ↥LL.1, 0 ≤ P.v LL y ↔ 0 ≤ w y := by
    intro y
    rw [_root_.Formalism.BasicNotions.LocPrime.v_O, _root_.GlobalTheory.Per.Val.mem_OL_iff, hwx]
    have := _root_.GlobalTheory.Per.Val.le_vf_iff (y : _root_.Formalism.BasicNotions.Loc.Om l) 0
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero, WithTop.coe_zero] at this
    exact this.symm
  have key : ∀ x : ↥LL.1, P.v LL x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x =>
    (addValuation_eq_of_nonneg_iff (P.v LL) w (P.v_l LL) hw hnn x).trans (hwx x)
  refine ⟨fun x q => ?_, fun x q => ?_, fun x => _root_.GlobalTheory.Per.Val.mem_OL_iff LL x⟩
  · rw [key]; exact _root_.GlobalTheory.Per.Val.vf_eq_iff _ q
  · rw [key]; exact _root_.GlobalTheory.Per.Val.le_vf_iff _ q

end GlobalTheory.HWL.NormVal
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobIntegralCoeff

section Generic

variable {R O : Type} [CommRing R] [CommRing O] [Algebra R O] {I : Type} [Fintype I] [DecidableEq I]
  (b : Module.Basis I R O)

def regRep (W : Type) [CommRing W] [Algebra R W] : O ⊗[R] W →ₐ[R] Matrix I I W :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId R W)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom R W (Matrix I I W))
    (fun _ w => (Algebra.commutes w _).symm)

variable {W W' : Type} [CommRing W] [Algebra R W] [CommRing W'] [Algebra R W']

theorem regRep_tmul (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = Algebra.leftMulMatrix b o i j • w := by
  erw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal, mul_comm]

theorem regRep_map (f : W →ₐ[R] W') (z : O ⊗[R] W) (i j : I) :
    regRep b W' (Algebra.TensorProduct.map (AlgHom.id O O) f z) i j = f (regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regRep_tmul, regRep_tmul, map_smul]
  | add x y hx hy => simp [map_add (f := _), Matrix.add_apply, hx, hy]

private theorem regRep_tmul' (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = b.repr (o * b j) i • w := by
  rw [regRep_tmul, Algebra.leftMulMatrix_eq_repr_mul]

theorem eq_sum_regRep (z : O ⊗[R] W) :
    z = ∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [regRep_tmul', ← TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← TensorProduct.sum_tmul, b.sum_repr, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    congr 1
    simp_rw [← mul_smul_comm, ← Finset.mul_sum, b.sum_repr, mul_one]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [map_add (f := _), Matrix.add_apply, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]

theorem mem_range_of_regRep (f : W →ₐ[R] W') (z : O ⊗[R] W')
    (h : ∀ i j, regRep b W' z i j ∈ Set.range f) :
    z ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  choose g hg using h
  refine ⟨∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] g i j), ?_⟩
  conv_rhs => rw [eq_sum_regRep b z]

  simp_rw [TensorProduct.smul_tmul', map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]

def blow {p q : Type} (Z : Matrix p q (O ⊗[R] W)) : Matrix (p × I) (q × I) W :=
  Matrix.of fun x y => regRep b W (Z x.1 y.1) x.2 y.2

theorem blow_map {p q : Type} (f : W →ₐ[R] W') (Z : Matrix p q (O ⊗[R] W)) :
    blow b (Z.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) = (blow b Z).map f := by
  ext x y
  simp [blow, regRep_map]

theorem blow_add {p q : Type} (Z Z' : Matrix p q (O ⊗[R] W)) :
    blow b (Z + Z') = blow b Z + blow b Z' := by
  ext x y
  simp [blow, map_add (f := _)]

theorem blow_mul {p q r : Type} [Fintype q] (Z : Matrix p q (O ⊗[R] W))
    (Z' : Matrix q r (O ⊗[R] W)) : blow b (Z * Z') = blow b Z * blow b Z' := by
  ext x y

  simp [blow, Matrix.mul_apply, map_sum, Matrix.sum_apply, Fintype.sum_prod_type]


omit b [Fintype I] [DecidableEq I] in
theorem integrality_baseChange [Module.Free R O] [Module.Finite R O] (f : W →ₐ[R] W')
    (φ : W' →ₐ[R] W')
    (H : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q W') (S : Matrix p p W)
      (S' : Matrix q q W) (Y : Matrix p q W),
      Z.map φ = S.map f * Z * S'.map f + Y.map f → ∀ a b, Z a b ∈ Set.range f)
    (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (O ⊗[R] W')) (S : Matrix p p (O ⊗[R] W))
    (S' : Matrix q q (O ⊗[R] W)) (Y : Matrix p q (O ⊗[R] W))
    (h : Z.map (Algebra.TensorProduct.map (AlgHom.id O O) φ) =
      S.map (Algebra.TensorProduct.map (AlgHom.id O O) f) * Z *
        S'.map (Algebra.TensorProduct.map (AlgHom.id O O) f) +
      Y.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) (x : p) (y : q) :
    Z x y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (O ⊗[R] W')
    exact ⟨0, Subsingleton.elim _ _⟩
  classical
  let c := Module.Free.chooseBasis R O
  have key := congrArg (blow c) h
  rw [blow_map, blow_add, blow_mul, blow_mul, blow_map, blow_map, blow_map] at key
  apply mem_range_of_regRep c f (Z x y)
  intro i j
  exact H _ _ (blow c Z) (blow c S) (blow c S') (blow c Y) key (x, i) (y, j)

private theorem module_free_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Free ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  have : Module.IsTorsionFree ℤ_[l] K := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  exact IsIntegralClosure.module_free ℤ_[l] ℚ_[l] K _

private theorem module_finite_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Finite ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _

end Generic

theorem frobenius_integrality_coeff : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  intro l _ LL p q _ _ Z S S' Y h a b
  unfold RW RA inclR φRW at *
  have := module_free_zpadic_OL l LL
  have := module_finite_zpadic_OL l LL
  exact integrality_baseChange (R := ℤ_[l]) (O := OL LL) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf l p q Z S S' Y h) p q Z S S' Y h a b

end GlobalTheory.FrobIntegralCoeff
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.ArtinSchreierWitt

open Polynomial

theorem frob_sub_mul_surjective (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p]
    [PerfectRing k p] (h : ∀ c y : k, ∃ x : k, x ^ p - c * x = y) (c y : WittVector p k) :
    ∃ β : WittVector p k, WittVector.frobenius β - c * β = y := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) (WittVector p k) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := WittVector p k), Ideal.map_span,
      Set.image_singleton, map_natCast]
    infer_instance
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    (WittVector.frobenius (p := p) (R := k)).toAddMonoidHom.toIntLinearMap
      - (AddMonoidHom.mulLeft c).toIntLinearMap
  have hf : ∀ β, f β = WittVector.frobenius β - c * β := fun β => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    obtain ⟨x, hx⟩ := h (c.coeff 0) (g.coeff 0)
    refine ⟨WittVector.teichmuller p x, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have h0 : (WittVector.frobenius (WittVector.teichmuller p x)
        - c * WittVector.teichmuller p x - g) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul]
      simp only [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
        WittVector.teichmuller_coeff_zero]
      rw [hx, sub_self]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
    rw [hu]
    have : (p : WittVector p k) * u = (p : ℤ) • u := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨β, hβ⟩ := hs y
  exact ⟨β, (hf β).symm.trans hβ⟩

theorem monic_as (p : ℕ) [hp : Fact p.Prime] {k : Type} [CommRing k] [Nontrivial k] (c y : k) :
    (X ^ p - (C c * X + C y) : k[X]).Monic ∧ (X ^ p - (C c * X + C y) : k[X]).degree = p := by
  have h1 : (C c * X + C y : k[X]).degree < (p : WithBot ℕ) :=
    lt_of_le_of_lt degree_linear_le (by exact_mod_cast hp.out.one_lt)
  refine ⟨monic_X_pow_sub h1, ?_⟩
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

theorem exists_root_field (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K]
    (c y : K) : ∃ x : K, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ p - (C c * X + C y) : K[X]) (by
    rw [(monic_as p c y).2]; exact_mod_cast hp.out.ne_zero)
  refine ⟨x, ?_⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at hx
  linear_combination hx

theorem exists_root_ring (p : ℕ) [hp : Fact p.Prime] {O K : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [IsAlgClosed K]
    (c y : O) : ∃ x : O, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := exists_root_field p (algebraMap O K c) (algebraMap O K y)
  have hi : IsIntegral O x := by
    refine ⟨X ^ p - (C c * X + C y), (monic_as p c y).1, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    linear_combination hx
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨z, IsFractionRing.injective O K ?_⟩
  rw [map_sub, map_pow, map_mul, hx]

theorem fixed_frob (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (b : WittVector p K)
    (hb : WittVector.map (frobenius K p) b = b) : ∃ z : ℤ_[p], b = zlW p K z := by
  have h : ∀ n, ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ p = b.coeff n := by
      have := congrArg (fun w => WittVector.coeff w n) hb
      simpa [WittVector.map_coeff, frobenius_def] using this
    have h2 := (Subfield.mem_bot_iff_pow_eq_self K p).2 h1
    have h3 : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl p) K).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∀ y : WCb l, ∃ b, frobW l b - b = y) ∧ (∀ b : WCb l, frobW l b = b → ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z) ∧ ∀ (c p : Ainf l), ∃ β : Ainf l, WittVector.frobenius β - c * β = p := by
  intro l _
  obtain ⟨hK, hV⟩ := GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing l
  refine ⟨fun y => ?_, fun b hb => fixed_frob l (Cb l) b hb, fun c p => ?_⟩
  · obtain ⟨β, hβ⟩ := frob_sub_mul_surjective l (Cb l) (exists_root_field l) 1 y
    refine ⟨β, ?_⟩
    rw [one_mul, WittVector.frobenius_eq_map_frobenius] at hβ
    exact hβ
  · exact frob_sub_mul_surjective l (OCb l) (exists_root_ring l (K := Cb l)) c p

end GlobalTheory.ArtinSchreierWitt
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CocN

open GlobalTheory.Cut.Coc

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    delta GlobalTheory.Cut.Coc.tw
    simp [hp, Formalism.MainNotions.N.mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.CocN

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit : ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  first | exact @GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | exact GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | (intros; apply GlobalTheory.finite_module_killed_by_pow_of_not_isUnit <;> assumption)
end
