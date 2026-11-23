module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntCoeffPrimitiveGLCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle017
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEqStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle046
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle040
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CuspFormula

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.GoodCharsCompare

theorem esymm_mem_virt (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k s : ℕ) :
    (fun x : GL (Fin d) F => (((Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)).map
      (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s) ∈ Virt ℂ ℂ (GL (Fin d) F) := by
  refine GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues _ _ _ (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F θ hθ d k) (fun x j _ => ?_) s
  rw [rootSum, ← Matrix.charpoly_map, ← Matrix.charpoly_map, Units.val_pow_eq_pow_val, Matrix.map_pow,
    GlobalTheory.T.roots_charpoly_pow_eq_map_pow, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp, map_pow, ← pow_mul, mul_comm]

theorem exists_regular (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ : GL (Fin d) F → ℂ) (hi : IsIrrChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ k : ℕ, (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) ∧
      ∀ x : GL (Fin d) F, χ x = (-1) ^ (d - 1) *
        psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
  classical
  have h := isCharacter_of_isIrreducibleCharacter_complex hi
  have hv : χ ∈ Virt ℂ ℂ (GL (Fin d) F) := AddSubgroup.subset_closure h
  obtain ⟨hval, -, hip, hcl⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  have hc := hcl (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one ℂ ℂ _ χ h).2.1
  have hr : Module.finrank F (Fin d → F) = d := by simp
  have hg := generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha, -⟩ := GlobalTheory.T.exists_int_coeff_primitive_GL_character F θ hθ d χ hd h hp
  have haa := sum_coef_mul_eq_pair F θ hθ d hd χ χ h h hp hp a a ha ha
  rw [GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed ℂ _ χ hi, mul_one] at haa
  have hinv : ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1] → a k = a l := by
    intro k l i hkl
    have := GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F (Fin d → F) θ _ hc hp (by rw [hr]; exact hd) k l i (by rw [hr]; exact hkl)
    rw [ha, ha] at this
    exact_mod_cast mul_right_cancel₀ hg this
  have hdvd : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro k s
    obtain ⟨m, hm⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card _ χ _ hv (esymm_mem_virt F θ hθ d k s)
    refine ⟨m, ?_⟩
    have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
    have key : ((∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) : ℤ) : ℂ) * glCard F d =
        d * (m * glCard F d) := by
      push_cast
      rw [Finset.sum_mul]
      simp only [← ha, hip]
      rw [glCard, ← hm]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hval, ← star_sum, Matrix.charpoly_toLin']
      by_cases hx : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
          LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = f ^ m
      · obtain ⟨f, m, hf, hirr, -, e⟩ := hx
        rw [Matrix.charpoly_toLin'] at e
        have hdeg : (f ^ m).natDegree = d := by rw [← e, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have := GlobalTheory.T.natDegree_mul_esymm_roots_pow' F θ f m k s hf hirr
        rw [hdeg] at this
        rw [e, ← this, star_mul', star_natCast]
        ring
      · have := GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F _ _ hc hp (by rw [hr]; exact hd) _ hx
        rw [hval] at this
        simp [this]
    rw [← mul_assoc] at key
    exact_mod_cast mul_right_cancel₀ hg key
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_regular_exponent_of_sum_sq_eq' _ d a hq hd hinv (by simp only [sq]; exact_mod_cast haa)
    (GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' _ d a hq hd hinv hdvd)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h', hn⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular F θ hθ d k hd hk
  have hv' := AddSubgroup.subset_closure (k := {χ | IsChar ℂ ℂ χ}) h'
  have hsq : ((-1 : ℂ) ^ (d - 1)) * (-1) ^ (d - 1) = 1 := by rw [← mul_pow]; simp
  have hi' := ((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one _ _ hv' (by
    rw [hip] at hn
    rw [← glCard, ← hn]
    refine finsum_congr fun x => ?_
    rw [star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, hsq, one_mul])).2 h').1
  by_contra hne
  have h0 := GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible _ _ _ hi hi' (fun e => hne (congrFun e))
  have h1 := GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse F (Fin d → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1 _ hp
  rw [ha, hip] at h1
  rw [pair, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hg (inv_eq_zero.1 h0)
  · have h2 : ∑ᶠ x : GL (Fin d) F, χ x * ((-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F)
        (Matrix.toLin' ((x⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) = (-1) ^ (d - 1) * (a k * glCard F d) := by
      have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
      rw [← h1]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ hv' x, hval, star_mul', star_pow, star_neg, star_one]
      ring
    rw [h2] at h0
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (mul_ne_zero (by exact_mod_cast hk0) hg) h0

variable {g : ℕ} [Fact g.Prime]

theorem cuspVal_eq_psi (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    {x : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1) {k : ℕ} (hk : ω x = rootC (g ^ Fintype.card ι - 1) ^ k)
    (M : Matrix ι ι (ZMod g)) (hM : M.det ≠ 0) :
    cuspVal ω x M = (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar g →* ℂ) k) (ι → ZMod g) (Matrix.toLin' M) := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) (ω : Fbar g →* ℂ) k).1
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, m, hp, hm⟩ := hh
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) p (degree_pos_of_irreducible hp).ne'
    have hdeg := M.charpoly_natDegree_eq_dim
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hdeg
        simp at hdeg
        omega
      · exact h
    have hf : M.charpoly = minpoly (ZMod g) y ^ m := by
      have h1 := minpoly.eq_of_irreducible hp hy
      have h2 : p.leadingCoeff ^ m = 1 := by
        rw [← leadingCoeff_pow, ← hm]
        exact M.charpoly_monic
      rw [← h1, mul_pow, ← C_pow, inv_pow, h2, inv_one, C_1, mul_one, hm]
    have hirr := minpoly.irreducible (isInt y)
    have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
      rw [hf, rootsBar_pow, Multiset.toFinset_nsmul _ _ hm0.ne']
    have hcard : (rootsBar M.charpoly).toFinset.card = dg y := by
      rw [hR, Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
    have he := fun z (hz : aeval z (minpoly (ZMod g) y) = 0) => GlobalTheory.T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace' (ZMod g) ι M _ z hirr hz
    rw [GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq (ZMod g) _ _ hs _ _ m _ (minpoly.monic (isInt y)) hirr hm0
      (by rw [Matrix.charpoly_toLin', hf]) (he y (minpoly.aeval _ _)), Nat.card_zmod]
    congr 1
    have e1 : rootSum (ω : Fbar g →* ℂ) k (minpoly (ZMod g) y) =
        ∑ z ∈ (rootsBar M.charpoly).toFinset, ω z ^ k := by
      rw [hR, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, (nodup_minpoly y).dedup]
      rfl
    rw [e1, Finset.sum_mul]
    convert Finset.sum_congr rfl (s₁ := (rootsBar M.charpoly).toFinset) fun z hz => ?_
    have hz1 := root_pow hM hp hm (Multiset.mem_toFinset.1 hz)
    have hz2 : aeval z (minpoly (ZMod g) y) = 0 := by
      rw [hR, Multiset.mem_toFinset] at hz
      exact (mem_rootsBar hirr.ne_zero).1 hz
    obtain ⟨a, ha⟩ := exists_log ω hd hz1
    have ht := Nat.eq_of_mul_eq_mul_left (dg_pos y) ((he z hz2).symm.trans (he y (minpoly.aeval _ _)))
    rw [labelChar_eq ω hd hx ha, hk, ha, ← pow_mul, ← pow_mul, mul_comm a k, ht]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcard]
  · rw [GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow (ZMod g) _ _ (fun e u => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ e u) (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse _ _ _ hs) (by simpa using hd),
      mul_zero]
    rintro ⟨f, m, -, hf, -, e⟩
    exact hh ⟨f, m, hf, by rw [← e, Matrix.charpoly_toLin']⟩

end GlobalTheory.CuspFormula
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

theorem sncChart_germ_eqn_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  intro R _ Y g n s L σ hL C C' y hy hy' c
  have hyi : y ∈ (L c).U (C.c c) := C.le c hy
  have hyj : y ∈ (L c).U (C'.c c) := C'.le c hy'
  have hyij : y ∈ (L c).U (C.c c) ⊓ (L c).U (C'.c c) := ⟨hyi, hyj⟩
  have e1 := congrArg (Y.presheaf.germ C.U y hy).hom (C.eq c)
  have e2 := congrArg (Y.presheaf.germ C'.U y hy').hom (C'.eq c)
  have e3 := congrArg (Y.presheaf.germ _ y hyij).hom ((σ c).2 (C.c c) (C'.c c))
  simp only [resG, map_mul, TopCat.Presheaf.germ_res_apply] at e1 e2 e3
  let w0 := Units.map (Y.presheaf.germ C.U y hy).hom.toMonoidHom (C.u c)
  let w1 := Units.map (Y.presheaf.germ C'.U y hy').hom.toMonoidHom (C'.u c)
  let wg := Units.map (Y.presheaf.germ _ y hyij).hom.toMonoidHom ((L c).g (C.c c) (C'.c c))
  refine ⟨w0⁻¹ * wg * w1, ?_⟩
  have key : (w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) =
      (wg : Y.presheaf.stalk y) * ((w1 : Y.presheaf.stalk y) * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t)) := by
    exact e1.symm.trans (e3.trans (congrArg (fun z => _ * z) e2))
  calc (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)
      = ((w0⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) * ((w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [key]; simp only [Units.val_mul, mul_assoc]

end GlobalTheory.LogPair
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

private lemma res_res_eq_res_trans {X : Scheme.{0}} {U W Z : X.Opens} (h : W ≤ U) (h' : Z ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma pullU_res_eq_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    pullU f W (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private lemma res_pullU_res_eq_res_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (k : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res k (pullU f W (res h x)) = res (k.trans fun _ hy ↦ h hy) (pullU f U x) := by
  rw [pullU_res_eq_res_pullU, res_res_eq_res_trans]

theorem isFrame_pull (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ)
    (Z : Scheme.{0}) (φ : Z ⟶ X) (C' : Type) [Category.{0} C'] (V' : C' → Z.Opens)
    (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ φ ⁻¹ᵁ V (H.obj T)) :
    IsFrame L V hV u → IsFrame (L.pull φ) V' hV' fun T T' a ↦ res (hH T') (pullU φ _ (u _ _ (H.map a))) := by
  rintro ⟨τ, hgen, hcomp⟩
  have hle : ∀ (T : C') (j : PUnit → L.ι), V' T ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit)) :=
    fun T j x hx ↦ ⟨hH T hx.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hx.2⟩
  refine ⟨fun T j ↦ res (hle T j) (pullU φ _ (τ (H.obj T) (j PUnit.unit))), fun T j j' ↦ ?_, fun T T' a j ↦ ?_⟩
  · have e := congrArg (fun x ↦ res (fun y hy ↦ ⟨⟨hH T hy.1.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hy.1.2⟩,
        LB.wchart_le L (fun _ ↦ φ) j' PUnit.unit hy.2⟩ : V' T ⊓ (L.pull φ).U j ⊓ (L.pull φ).U j' ≤
          φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) (pullU φ _ x))
      (hgen (H.obj T) (j PUnit.unit) (j' PUnit.unit))
    simp only [map_mul] at e
    erw [res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU'] at e
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    erw [res_res_eq_res_trans, res_res_eq_res_trans, res_res_eq_res_trans]
    exact e
  · have e := congrArg (fun x ↦ res (hle T' j) (pullU φ _ x)) (hcomp (H.obj T) (H.obj T') (H.map a) (j PUnit.unit))
    simp only [map_mul, res_pullU_res_eq_res_pullU', res_res_eq_res_trans] at e
    simp only [res_res_eq_res_trans]
    exact e
end LBObs
end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBTrans

variable {X : Scheme.{0}}

theorem res_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {U : X.Opens} (a b : Γ(X, U)ˣ)
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ res hW a = res hW b) : a = b := by
  let J := {W : X.Opens // ∃ hW : W ≤ U, res hW a = res hW b}
  have hc : U ≤ ⨆ j : J, j.1 := fun x hx => by
    obtain ⟨W, hW, hx', e⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, e⟩, hx'⟩
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun j : J => j.1) U (fun j => homOfLE j.2.1) hc _ _ (fun j => ?_)
  exact congrArg Units.val j.2.2

theorem glue_units {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

variable {C : Type} [Category.{0} C] {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
  {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ}

theorem res_quot (hu : IsCoc V hV u) {T₁ T₂ T T'' : C} (a : T₁ ⟶ T) (b : T₂ ⟶ T) (c : T ⟶ T'') :
    res (hV c) (u T₂ T b * (u T₁ T a)⁻¹) = u T₂ T'' (b ≫ c) * (u T₁ T'' (a ≫ c))⁻¹ := by
  rw [hu b c, hu a c, map_mul, map_inv, mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

theorem transition_units (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [thin : Quiver.IsThin C]
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) :
    IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ,
      ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  intro hB hu T₁ T₂
  have sub : ∀ {T T' : C} (f f' : T ⟶ T'), f = f' := fun f f' => @Subsingleton.elim _ (thin _ _) f f'
  let J := {T : C // Nonempty (T₁ ⟶ T) ∧ Nonempty (T₂ ⟶ T)}
  let W : J → X.Opens := fun j => V j.1
  have hW : ∀ j : J, W j ≤ V T₁ ⊓ V T₂ := fun j => le_inf (hV j.2.1.some) (hV j.2.2.some)
  let w : ∀ j : J, Γ(X, W j)ˣ := fun j => u T₂ j.1 j.2.2.some * (u T₁ j.1 j.2.1.some)⁻¹
  have hw : ∀ (j : J) (a : T₁ ⟶ j.1) (b : T₂ ⟶ j.1), w j = u T₂ j.1 b * (u T₁ j.1 a)⁻¹ :=
    fun j a b => by simp only [w]; rw [sub j.2.2.some b, sub j.2.1.some a]
  have hc : V T₁ ⊓ V T₂ ≤ iSup W := fun x hx => by
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨T, ⟨a⟩, ⟨b⟩⟩, hxT⟩
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (w i) = res inf_le_right (w j) := by
    intro i j
    apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨c⟩, ⟨d⟩, hxT, hle⟩ := hB.2 i.1 j.1 x (W i ⊓ W j) hx hx.1 hx.2
    refine ⟨V T, hle, hxT, ?_⟩
    rw [res_comp, res_comp]
    have e1 := res_quot hu i.2.1.some i.2.2.some c
    have e2 := res_quot hu j.2.1.some j.2.2.some d
    change res (hV c) (w i) = res (hV d) (w j)
    simp only [w]
    rw [e1, e2, sub (i.2.1.some ≫ c) (j.2.1.some ≫ d), sub (i.2.2.some ≫ c) (j.2.2.some ≫ d)]
  obtain ⟨s, hs⟩ := glue_units (V T₁ ⊓ V T₂) W hW hc w hh
  have key : ∀ (g : Γ(X, V T₁ ⊓ V T₂)ˣ) (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T),
      res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b ↔
        res (le_inf (hV a) (hV b)) g = u T₂ T b * (u T₁ T a)⁻¹ :=
    fun g T a b => (eq_mul_inv_iff_mul_eq).symm
  refine ⟨s, fun T a b => (key s T a b).2 ?_, fun g hg => ?_⟩
  · have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this
  · apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    refine ⟨V T, le_inf (hV a) (hV b), hxT, ?_⟩
    rw [(key g T a b).1 (hg T a b)]
    have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this.symm

end GlobalTheory.LBTrans
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k), (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) := by
  first | exact @GlobalTheory.Dieu.isog_basics | exact GlobalTheory.Dieu.isog_basics | (intros; apply GlobalTheory.Dieu.isog_basics <;> assumption)
end
