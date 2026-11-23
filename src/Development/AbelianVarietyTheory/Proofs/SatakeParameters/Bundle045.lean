module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Mathlib.AlgebraicGeometry.FunctionField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.RowTie.EigTwist

theorem roots_charpoly_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly.roots = M.charpoly.roots.map (· * u) := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  suffices (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod by
    rw [this, roots_multiset_prod_X_sub_C]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem roots_charpoly_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (u : ℂ) : (u • f).charpoly.roots = f.charpoly.roots.map (· * u) := by
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), map_smul, roots_charpoly_smul_matrix]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem eig_lpTw (x : WD h) {φ : Weil h} (hφ : deg φ = 1) (s : ℝ) :
    (x.lpTw s).eig φ = (x.eig φ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.eig_mk, WD.eig_mk, WDRep.tw_ρ, hφ, zpow_one, roots_charpoly_smul]

theorem eig_lpChar (x y : WD h) (φ : Weil h) (hy : y.lpDim = 1) (c : ℂ) (hc : y.eig φ = {c}) :
    (x.lpChar y).eig φ = (x.eig φ).map (· * c) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
    subst hy
    rw [WD.eig_mk] at hc
    have hb : b.ρ φ = c • 1 := by
      have hp : (b.ρ φ).charpoly = X - C c := by
        rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _), hc]
        simp
      have h3 := LinearMap.aeval_self_charpoly (b.ρ φ)
      rw [hp, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
      exact h3
    rw [WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, hb]
    let e : (Fin n → ℂ) ⊗[ℂ] (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      (TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
        (TensorProduct.rid ℂ _)
    have he : e.conj (TensorProduct.map (a.ρ φ) (c • 1)) = c • a.ρ φ := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨t, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [LinearEquiv.symm_apply_apply]
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e, smul_smul, mul_comm]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [← LinearEquiv.charpoly_conj e, he, roots_charpoly_smul]

end GlobalTheory.RowTie.EigTwist

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.directSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | exact GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | (intros; apply GlobalTheory.WeilDeligne.WD.lpSum_cancel_right <;> assumption)
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.ResEv

open MvPolynomial

theorem ker_aeval_zero (k : Type) [Field k] (d : ℕ) :
    RingHom.ker (aeval (R := k) (fun _ : Fin d ↦ (0 : k))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p = AddMonoidAlgebra.coeff p 0 := by
      rw [show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp

theorem res_aeval (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F)
    (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes k x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d ↦ x j.succ / x 0) p) = aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [hρ.1]
    · obtain ⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by
        by_contra h; push_neg at h; exact hn (Finsupp.ext h)
      have h0 : ∏ j : Fin d, (0 : k) ^ n j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)
      rw [h0, smul_zero]
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))
      have hsum : ∑ i, m i = 0 := by
        rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        have := congrFun h j0.succ
        simp [m] at this
        exact hj0 this
      have hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]
        rw [Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib,
          Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]
      rw [hprod, hρ.2 m hsum hm, mul_zero]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]

end GlobalTheory.PD.ResEv

open MvPolynomial in
theorem GlobalTheory.PD.ResEv.chart0 : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  intro k _ F _ _ d x hx ρ hρ
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0
  have hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p := by
    intro p
    have h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [he]
    exact congrArg (fun f => f p) (congrArg DFunLike.coe h1)
  refine ⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩
  · have := GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)
    rw [← hv, AlgEquiv.apply_symm_apply] at this
    simpa using this
  · have ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X := by
      rw [← Set.range_comp]
      congr 1
      funext j
      apply Subtype.ext
      simp [he]
    rw [ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]
    ext a
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
end
end

section

open CategoryTheory AlgebraicGeometry Module ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeFin

open GlobalTheory.CechDR GlobalTheory.QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k)

theorem finiteType_sec [LocallyOfFiniteType s] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (Sec s U) := by
  have h1 := LocallyOfFiniteType.finiteType_appLE s (isAffineOpen_top (Sp k)) hU
    (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end GlobalTheory.HodgeFin
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

end GlobalTheory.W1.Lef
end
end

section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.deRhamFormTrace_exists_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  first | (exact @GlobalTheory.W1.trDR_isTrDR_unique) | (exact GlobalTheory.W1.trDR_isTrDR_unique) | (intros; apply GlobalTheory.W1.trDR_isTrDR_unique <;> assumption)
end

section

open GlobalTheory.LatHecke

namespace GlobalTheory.HeckeSeries

open Classical

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_subIdx_sub_iff {n k : ℕ} (hk : k ≤ n) {L M' M : Lat O K r}
    (hM' : M' ∈ subElem k L) :
    M ∈ subIdx (n - k) M' ↔ M ∈ subIdx n L ∧ M.1 ≤ M'.1 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hM'
  have hq : 0 < qRes O := lt_of_lt_of_le two_pos two_le_qRes
  have hpow : qRes O ^ n = qRes O ^ (n - k) * qRes O ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨⟨h3.trans h1, ?_⟩, h3⟩
    rw [← AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1, h4, h2, hpow]
  · rintro ⟨⟨-, h4⟩, h5⟩
    refine ⟨h5, ?_⟩
    have h := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h5 h1
    rw [h4, h2, hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq k) h

theorem heckeElem_heckeAll_eq {E : Type} [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E)
    {n k : ℕ} (hk : k ≤ n) (L : Lat O K r) :
    heckeElem k (heckeAll (n - k) φ) L = ∑ M ∈ (subIdx_finite n L).toFinset,
      ((((subElem_finite k L).toFinset.filter (fun M' => M.1 ≤ M'.1)).card : ℂ)) • φ M := by
  rw [heckeElem_eq_sum]
  have h : ∀ M' ∈ (subElem_finite k L).toFinset, heckeAll (n - k) φ M' =
      ∑ M ∈ (subIdx_finite n L).toFinset, if M.1 ≤ M'.1 then φ M else 0 := by
    intro M' hM'
    rw [heckeAll_eq_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext M
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact mem_subIdx_sub_iff hk ((Set.Finite.mem_toFinset _).1 hM')
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem heckeSeries_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r),
    1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) •
      heckeElem k (heckeAll (n - k) φ) L = 0 := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ n L hn
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [heckeElem_heckeAll_eq φ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) L])]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [← Finset.sum_smul]
  have hM' : M ∈ subIdx n L := (Set.Finite.mem_toFinset _).1 hM
  have h := GlobalTheory.T.sum_alternating_card_elementarySublattices_above O K r n L M hn hM'
  convert zero_smul ℂ (φ M) using 2
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M'
  simp

end GlobalTheory.HeckeSeries
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmptyProd

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lineEquiv {α n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype n] [DecidableEq n]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) : IndSp e (piTensor σ) ≃ₗ[ℂ] ℂ :=
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  (LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)

theorem multiProd_equiv_of_isEmpty : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α']
    [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
    (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)),
    Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  intro k _ _ _ _ α α' n _ _ _ _ _ _ _ _ m _ _ m' _ _ e e' X _ _ X' _ _ σ σ'
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  refine ⟨Representation.Equiv.mk ((lineEquiv e σ).trans (lineEquiv e' σ').symm) fun g => ?_⟩
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

end GlobalTheory.EmptyProd
end
end
