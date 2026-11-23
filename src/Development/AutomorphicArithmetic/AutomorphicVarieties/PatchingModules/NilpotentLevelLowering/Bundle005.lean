module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unip_eq_one {n d : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hd : d ≠ 0) (h1 : M ^ d = 1)
    (hc : M.charpoly = (Polynomial.X - 1) ^ n) : M = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hsep : (Polynomial.X ^ d - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd) one_ne_zero
  have h1' : minpoly ℂ M ∣ Polynomial.X ^ d - Polynomial.C 1 := minpoly.dvd ℂ M (by simp [h1])
  have hsq : Squarefree (minpoly ℂ M) := hsep.squarefree.squarefree_of_dvd h1'
  have h2 : minpoly ℂ M ∣ (Polynomial.X - 1) ^ n := hc ▸ Matrix.minpoly_dvd_charpoly M
  have h3 : minpoly ℂ M ∣ Polynomial.X - 1 := (hsq.dvd_pow_iff_dvd hn.ne').mp h2
  have h4 := (minpoly.dvd_iff).mp h3
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Pa.Lev.wdChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (x : WD hB), IsWDOf ι r x → (∀ σ : Weil hB, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = x.charPol σ) ∧ ∀ σ ∈ GlobalTheory.TameQuot.ineKer E Bq l, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro l _ E Ω _ _ _ _ _ Bq w hB hl n ι r x hx
  have hxe : wdOf (h := hB) hl ι r = x := IsWDOf.wdOf_eq hl hx
  obtain ⟨t, ht, φ, hφ, N, a, hmon, -, -⟩ := hx
  constructor
  · intro σ
    rw [← hxe, IsMonodromy.charPol_wdOf hl ht hmon ι σ]
    exact Matrix.charpoly_map _ ι.toRingHom
  · intro σ hσ hc
    have hσI : σ ∈ Ine Bq := GlobalTheory.TameQuot.ineKer_le_Ine Bq l hσ
    let τ : Ine Bq := ⟨σ, hσI⟩
    have htτ : t τ = 1 := (GlobalTheory.TameQuot.eq_one_iff_mem_ineKer E Ω l Bq w hB hl t ht.1 ht.2 τ).mpr hσ
    have hval : tval t τ = 0 := by simp [tval, htτ]
    obtain ⟨-, U, hU, hUr⟩ := hmon
    haveI := compactSpace_Ine (E := E) Bq
    haveI : Finite (Ine Bq ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
    haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hd : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hpow : τ ^ U.normalCore.index ∈ U := U.normalCore_le (U.normalCore.pow_index_mem τ)
    have hr : (r σ : Matrix (Fin n) (Fin n) (Qbar l)) ^ U.normalCore.index = 1 := by
      have := hUr _ hpow
      rw [tval_pow, hval, mul_zero, zero_smul, IsNilpotent.exp_zero, Subgroup.coe_pow, map_pow,
        Units.val_pow_eq_pow_val] at this
      exact this
    have hM : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = 1 := by
      apply unip_eq_one _ hd _ hc
      have e : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = ι.toRingHom.mapMatrix (r σ : Matrix (Fin n) (Fin n) (Qbar l)) := rfl
      rw [e, ← map_pow, hr, map_one]
    apply Units.ext
    refine Matrix.map_injective ι.injective ?_
    show (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = (1 : Matrix (Fin n) (Fin n) (Qbar l)).map ι
    rw [hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def uP (q n : ℕ) (j : Fin q) : Polynomial (MvPolynomial (Fin q × Fin n) ℤ) :=
  Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (MvPolynomial.X (j, k)) * Polynomial.X ^ (k : ℕ)

private theorem prod_coeff (R : Type) [CommRing R] (q n : ℕ) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).coeff k =
      (-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) := by
  have hh : (emb ℤ R j : MvPolynomial (Fin n) ℤ →+* PU R q n) =
      (MvPolynomial.aeval (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => by simp [emb])
  rw [show emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) = _ from RingHom.congr_fun hh _]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have key := Multiset.prod_X_sub_C_coeff
    (Finset.univ.val.map (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))) (k := k) (by simpa using hk)
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.map_map] at key
  rw [← key]
  rfl

private theorem exists_mvPolynomial_action_extending_inc (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup V] [Module R V] (σ : Type) (β : R →+* B) (act : MvPolynomial σ R →ₐ[R] Module.End R V)
    (inc : M →+ V) (hinc : ∀ (t : R) m, inc (β t • m) = t • inc m) :
    ∃ G : MvPolynomial σ B →+ M →+ V, (∀ m, G 1 m = inc m) ∧
      (∀ u h m, G (MvPolynomial.map β u * h) m = act u (G h m)) ∧
      (∀ b h m, G (MvPolynomial.C b * h) m = G h (b • m)) := by
  let X : (σ →₀ ℕ) → B →+ M →+ V := fun e =>
    { toFun := fun b =>
        { toFun := fun m => act (MvPolynomial.monomial e 1) (inc (b • m))
          map_zero' := by simp
          map_add' := fun x y => by simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := fun x y => by ext m; simp [add_smul] }
  let G : MvPolynomial σ B →+ M →+ V :=
    (Finsupp.liftAddHom X).comp (AddMonoidAlgebra.coeffAddEquiv (R := B) (M := σ →₀ ℕ)).toAddMonoidHom
  have hG : ∀ e b m, G (MvPolynomial.monomial e b) m = act (MvPolynomial.monomial e 1) (inc (b • m)) := by
    intro e b m
    show (Finsupp.liftAddHom X (Finsupp.single e b)) m = _
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  refine ⟨G, ?_, ?_, ?_⟩
  · intro m
    rw [← MvPolynomial.C_1, MvPolynomial.C_apply, hG, one_smul, ← MvPolynomial.C_apply, MvPolynomial.C_1, map_one]
    rfl
  · intro u h m
    induction u using MvPolynomial.induction_on' with
    | monomial e r =>
      induction h using MvPolynomial.induction_on' with
      | monomial e' c =>
        have h1 : MvPolynomial.monomial (e + e') (1 : R) =
            MvPolynomial.monomial e 1 * MvPolynomial.monomial e' 1 := by
          rw [MvPolynomial.monomial_mul, one_mul]
        have h2 : MvPolynomial.monomial e r = r • MvPolynomial.monomial e (1 : R) := by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [MvPolynomial.map_monomial, MvPolynomial.monomial_mul, hG, hG, mul_smul, hinc]
        generalize inc (c • m) = v
        rw [h1, h2]
        simp only [map_smul, map_mul, Module.End.mul_apply, LinearMap.smul_apply]
      | add p q hp hq =>
        simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hp, hq]
    | add p q hp hq =>
      simp only [map_add (f := _), add_mul, AddMonoidHom.add_apply, hp, hq, LinearMap.add_apply]
  · intro b h m
    induction h using MvPolynomial.induction_on' with
    | monomial e c =>
      rw [MvPolynomial.C_mul_monomial, hG, hG, mul_comm, mul_smul]
    | add p q hp hq =>
      simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hp, hq]

theorem UpperTheory.V.Pa.Lev.multiPhi :
    ∀ (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (inc : M →+ V), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) m, inc (β t • m) = t • inc m) → (∀ j k, k ≤ n → ∀ m, act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) (inc m) = inc (((-1) ^ k * (P j).coeff (n - k)) • m)) → ∃ φ : MSplitAlg P n ⊗[B] M →+ V, (∀ m, φ (1 ⊗ₜ m) = inc m) ∧ ∀ (t : PU R q n) z, φ (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • z) = act t (φ z) := by
  intro R B M V _ _ _ _ _ _ q n β P act inc hmon hdeg hinc hact
  obtain ⟨G, h1, hL, hC⟩ := exists_mvPolynomial_action_extending_inc R B M V (Fin q × Fin n) β act inc hinc
  have hgen : ∀ jk : Fin q × ℕ, ∀ m, G ((∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (jk.1, i))) -
      Polynomial.map MvPolynomial.C (P jk.1)).coeff jk.2) m = 0 := by
    rintro ⟨j, k⟩ m
    dsimp only
    have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : MvPolynomial (Fin q × Fin n) B))) =
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).map (MvPolynomial.map β) := by
      simp [Polynomial.map_prod]
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hprod, Polynomial.coeff_map]
    rcases le_or_gt k n with hk | hk
    · rw [prod_coeff R q n j k hk, map_sub, AddMonoidHom.sub_apply]
      have e1 := hL ((-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k))) 1 m
      rw [mul_one, h1] at e1
      have e2 := hC ((P j).coeff k) 1 m
      rw [mul_one, h1] at e2
      rw [e1, e2, map_mul, map_pow, map_neg, map_one, Module.End.mul_apply, hact j (n - k) (Nat.sub_le n k) m,
        Nat.sub_sub_self hk]
      rcases Nat.even_or_odd (n - k) with hp | hp
      · simp [hp.neg_one_pow]
      · simp [hp.neg_one_pow, neg_smul]
    · have hd : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).natDegree ≤ n :=
        (Polynomial.natDegree_prod_le _ _).trans
          ((Finset.sum_le_sum fun i _ => Polynomial.natDegree_X_sub_C_le _).trans (by simp))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_lt hk)]
      simp
  have hI : ∀ x ∈ mSplitIdeal P n, ∀ a m, G (a * x) m = 0 := by
    intro x hx
    unfold mSplitIdeal Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨jk, rfl⟩ := hx
      intro a m
      induction a using MvPolynomial.induction_on' with
      | monomial e b =>
        have hm : MvPolynomial.monomial e b = MvPolynomial.C b * MvPolynomial.map β (MvPolynomial.monomial e 1) := by
          rw [MvPolynomial.map_monomial, map_one, MvPolynomial.C_mul_monomial, mul_one]
        rw [hm, mul_assoc, hC, hL, hgen jk (b • m), map_zero]
      | add p q hp hq => simp only [add_mul, map_add (f := _), AddMonoidHom.add_apply, hp, hq, add_zero]
    | zero => intro a m; simp
    | add x y _ _ hx hy => intro a m; simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hx, hy, add_zero]
    | smul c x _ hx => intro a m; rw [smul_eq_mul, ← mul_assoc, hx]
  have hvan : (mSplitIdeal P n).toAddSubgroup ≤ G.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    ext m
    simpa using hI x hx 1 m
  let F : MSplitAlg P n →+ M →+ V := QuotientAddGroup.lift (mSplitIdeal P n).toAddSubgroup G hvan
  have hF : ∀ f, F (Ideal.Quotient.mk (mSplitIdeal P n) f) = G f := fun f => rfl
  have hbal : ∀ (b : B) (x : MSplitAlg P n) (m : M), F (b • x) m = F x (b • m) := by
    intro b x m
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hF, hF, MvPolynomial.algebraMap_eq, hC]
  refine ⟨TensorProduct.liftAddHom F hbal, ?_, ?_⟩
  · intro m
    rw [TensorProduct.liftAddHom_tmul, ← map_one (Ideal.Quotient.mk (mSplitIdeal P n)), hF, h1]
  · intro t z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul, smul_eq_mul,
        ← map_mul, hF, hF, hL]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_pairs_dvd {A : Type} [CommRing A] {n : ℕ} (u : Fin n → A) (c : A) :
    ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) ∣ ∏ i, ∏ i' ∈ Finset.univ.erase i, (u i - u i') * (u i - c * u i') := by
  have h1 : ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) =
      ∏ i, ∏ i' ∈ Finset.univ.filter (fun i' => i' < i), (u i - c * u i') := by
    unfold Hk.pairs
    rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter]
  rw [h1]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  refine (Finset.prod_dvd_prod_of_subset _ (Finset.univ.erase i) _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => dvd_mul_left _ _)
  intro i' hi'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  simp [hi'.ne]

private theorem twoMaps_of_dvd {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V]
    [Module R V] {q n : ℕ} (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) {f g : PU R q n}
    (hfg : f ∣ g) (h : TwoMaps (M := M) β P act f) : TwoMaps (M := M) β P act g := by
  obtain ⟨c, rfl⟩ := hfg
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨φ, ψ.comp (act c).toAddMonoidHom, h1, fun t v => ?_, fun v => ?_, fun z => ?_⟩
  · show ψ (act c (act t v)) = _ • ψ (act c v)
    rw [← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · show φ (ψ (act c v)) = _
    rw [h3, map_mul, Module.End.mul_apply]
  · show ψ (act c (φ z)) = _
    rw [h2, h4, mul_comm f c, map_mul, map_mul, mul_smul]

theorem UpperTheory.V.Pa.Lev.twoMul :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (Nq : Fin q → ℕ), TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) → TwoMaps (M := M) β P act (fEl Nq fun j i => MvPolynomial.X (j, i)) := by
  intro O R B M V _ _ _ _ _ _ _ _ q n β P act Nq h
  refine twoMaps_of_dvd β P act ?_ h
  unfold fEl
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  have e : emb O R j (Hk.NN n (Nq j : O)) = ∏ p ∈ Hk.pairs n,
      ((MvPolynomial.X (j, p.2) : PU R q n) - (Nq j : PU R q n) * MvPolynomial.X (j, p.1)) := by
    unfold Hk.NN
    rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [emb]
  rw [e]
  exact prod_pairs_dvd (fun i => (MvPolynomial.X (j, i) : PU R q n)) _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem one_place {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n : ℕ}
    (e : MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ s t z, z.IsSymmetric → Φ s (t * e z) = Φ (s * e z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (x : MvPolynomial (Fin n) O) (s t : A) :
    ∑ k, Φ (e (a k) * s) (e (c k) * t * e x) = ∑ k, Φ (e x * (e (a k) * s)) (e (c k) * t) := by
  have hd := UpperTheory.V.AlgebraTools.hkDualExp O n ι a c h
  have hs := (UpperTheory.V.AlgebraTools.hkDdProps O n).2.2.1
  have e1 : ∀ k, Φ (e (a k) * s) (e (c k) * t * e x)
      = ∑ m, Φ (e (a k * Hk.dd (c k * (x * a m))) * s) (e (c m) * t) := by
    intro k
    have : e (c k) * t * e x = ∑ m, e (c m) * t * e (Hk.dd (c k * (x * a m))) := by

      rw [mul_right_comm, ← map_mul, ← (hd (c k * x)).2, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_right_comm, show a m * (c k * x) = c k * (x * a m) by ring]
    rw [this, h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h3 _ _ _ (hs _), map_mul, mul_right_comm]
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_

  rw [← h2, ← Finset.sum_mul, ← map_sum, (hd _).1, map_mul, mul_assoc]

private theorem many_places {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n q : ℕ}
    (e : Fin q → MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ j s t z, z.IsSymmetric → Φ s (t * e j z) = Φ (s * e j z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (j : Fin q) (x : MvPolynomial (Fin n) O) :
    ∑ i : Fin q → ι, Φ (∏ j, e j (a (i j))) ((∏ j, e j (c (i j))) * e j x)
      = ∑ i : Fin q → ι, Φ (e j x * ∏ j, e j (a (i j))) (∏ j, e j (c (i j))) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := j.pos; omega⟩
  rw [← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp, ← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp,
    Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.prod_univ_succAbove _ j, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact one_place (e j) Φ h1 h2 (h3 j) h x _ _

private theorem esymm_root {O R B : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing B] {q n : ℕ} (β : R →+* B)
    (P : Fin q → Polynomial B) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (emb O R j (MvPolynomial.esymm (Fin n) O k)))
      = algebraMap B (MSplitAlg P n) ((-1) ^ k * (P j).coeff (n - k)) := by
  have h0 := congrArg (fun p => p.coeff (n - k)) (MSplitAlg.prod_root P n j)
  have hc : Multiset.card (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i) = n := by simp
  have h1 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i)
    (k := n - k) (by rw [hc]; omega)
  rw [hc, Multiset.map_map, show n - (n - k) = k by omega, Finset.esymm_map_val] at h1
  simp only [Polynomial.coeff_map] at h0
  rw [map_mul, ← h0, Finset.prod_eq_multiset_prod]
  simp only [Function.comp_def] at h1
  rw [h1, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]

  simp [emb, MvPolynomial.esymm, MSplitAlg.root, map_sum, map_prod]

theorem UpperTheory.V.Pa.Lev.multiPsi :
    ∀ (O R B M V : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (tr : V →+ M) (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c → (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) v, tr (t • v) = β t • tr v) → (∀ j k, k ≤ n → ∀ v, tr (act (emb O R j (MvPolynomial.esymm (Fin n) O k)) v) = ((-1) ^ k * (P j).coeff (n - k)) • tr v) → ∀ ψ : V →+ MSplitAlg P n ⊗[B] M, (∀ v, ψ v = ∑ i : Fin q → ι, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ tr (act (∏ j, emb O R j (c (i j))) v)) → ∀ (t : PU R q n) v, ψ (act t v) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • ψ v := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β P act tr ι _ a c hd _ _ hβ he ψ hψ
  let π : PU R q n →+* MSplitAlg P n := (Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β)
  have hπ : ∀ t, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) = π t := fun _ => rfl
  simp only [hπ] at hψ ⊢
  have sc : ∀ (b : B) (y : MSplitAlg P n) (m : M), y ⊗ₜ[B] (b • m) = (y * algebraMap B _ b) ⊗ₜ[B] m := by
    intro b y m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  have hC : ∀ (r : R) (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (MvPolynomial.C r) w) = (y * π (MvPolynomial.C r)) ⊗ₜ[B] tr w := by
    intro r y w
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, hβ, sc, ← hπ,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  have bal : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → ∀ (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (emb O R j z) w) = (y * π (emb O R j z)) ⊗ₜ[B] tr w := by
    intro j z hz
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective O (σ := Fin n) (n := n) (by simp) ⟨z, hz⟩
    obtain rfl : z = (MvPolynomial.esymmAlgHom (Fin n) O n p : MvPolynomial (Fin n) O) := by rw [hp]
    clear hp hz
    rw [MvPolynomial.esymmAlgHom_apply]
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : emb O R j (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) O (i + 1))
          (MvPolynomial.C r : MvPolynomial (Fin n) O)) = MvPolynomial.C (algebraMap O R r) := by simp [emb]
      rw [this]
      exact hC _
    | add p p' hp hp' =>
      intro y w
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, map_add (f := _), TensorProduct.tmul_add, hp, hp', mul_add,
        TensorProduct.add_tmul]
    | mul_X p i hp =>
      intro y w
      rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, hp, MvPolynomial.aeval_X, he j _ i.2, sc,
        ← esymm_root (O := O) β P j _ i.2, hπ, mul_assoc]
  intro t
  induction t using MvPolynomial.induction_on with
  | C r =>
    intro v
    rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hC, TensorProduct.smul_tmul',
      smul_eq_mul, mul_comm]
  | add p p' hp hp' =>
    intro v
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, map_add (f := _), hp, hp', add_smul]
  | mul_X p ji hp =>
    intro v
    obtain ⟨j, i⟩ := ji
    have hX : (MvPolynomial.X (j, i) : PU R q n) = emb O R j (MvPolynomial.X i) := by simp [emb]
    rw [map_mul, map_mul, Module.End.mul_apply, hp, mul_smul, hX, hψ, hψ, Finset.smul_sum (r := π (emb O R j _))]
    congr 1
    have := many_places (emb O R) (fun s t => π s ⊗ₜ[B] tr (act t v))
      (fun s f => by simp only [map_sum, LinearMap.sum_apply, TensorProduct.tmul_sum])
      (fun s f => by simp only [map_sum, TensorProduct.sum_tmul])
      (fun j s t z hz => by
        show π s ⊗ₜ[B] tr (act (t * emb O R j z) v) = π (s * emb O R j z) ⊗ₜ[B] tr (act t v)
        rw [mul_comm t, map_mul, Module.End.mul_apply, bal j z hz, map_mul]) hd j (MvPolynomial.X i)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [this]
    simp only [TensorProduct.smul_tmul', smul_eq_mul]
end
