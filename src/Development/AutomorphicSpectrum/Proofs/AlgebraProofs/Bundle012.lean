module

import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.WeilBound.CoreStatements.HodgeTatePoints.RaTlog
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle007
import Mathlib.Algebra.GroupWithZero.Torsion
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle006
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle003
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import ReciprocityTheory.DualLattices.Bundle004
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Dual.Basis

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  apply PositivityTheory.HtPt.Htat.ext_span <;> assumption

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
end

section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem val_one_sub_pow_le {K : Type} [Field K] (v : Valuation K NNReal) {x : K} (hx : v x = 1)
    (i : ℕ) : v (1 - x ^ i) ≤ v (1 - x) := by
  have h : 1 - x ^ i = (1 - x) * ∑ j ∈ Finset.range i, x ^ j := (mul_neg_geom_sum x i).symm
  rw [h, map_mul]
  refine mul_le_of_le_one_right' ?_
  exact v.map_sum_le (fun j _ => by rw [map_pow, hx, one_pow])

theorem val_eq_one_of_pow_eq_one {K : Type} [Field K] (v : Valuation K NNReal) {x : K} {n : ℕ}
    (hn : n ≠ 0) (hx : x ^ n = 1) : v x = 1 := by
  have h : v x ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_left_inj₀ zero_le zero_le_one hn).mp (by simpa using h)

theorem val_sub_one_pow {K : Type} [Field K] (v : Valuation K NNReal) (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : K) := by
  apply PositivityTheory.HtPt.Ra.val_prim <;> assumption

theorem exists_mulShift_eq {F K : Type} [Field F] [Fintype F] [Field K] (ψ₀ ψ : AddChar F K)
    (h₀ : ψ₀ ≠ 1) : ∃ c, ψ = AddChar.mulShift ψ₀ c :=
  _root_.UpperTheory.Reformulated.B.Yde4.main ψ₀ ψ h₀

def ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

theorem mem_ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ ltOneIdeal v R hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem ltOneIdeal_isPrime {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : (ltOneIdeal v R hv).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : R) ∈ ltOneIdeal v R hv := h ▸ Submodule.mem_top
    rw [mem_ltOneIdeal] at h1
    simp at h1
  · rw [mem_ltOneIdeal, map_mul, map_mul] at hab
    by_contra hcon
    push Not at hcon
    simp only [mem_ltOneIdeal, not_lt] at hcon
    have ha : v (algebraMap R C a) = 1 := le_antisymm (hv.map_le_one a) hcon.1
    have hb : v (algebraMap R C b) = 1 := le_antisymm (hv.map_le_one b) hcon.2
    simp [ha, hb] at hab

theorem gauss_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard hF σ hσ ψ hψ
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI hprime : (ltOneIdeal v R hv).IsPrime := ltOneIdeal_isPrime v R hv

  have hpm : (p : R) ∈ ltOneIdeal v R hv := by
    rw [mem_ltOneIdeal, map_natCast]; exact hp
  have hspan : Ideal.span {(p : R)} ≤ ltOneIdeal v R hv :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpm
  let ι : F →+* R ⧸ ltOneIdeal v R hv :=
    { toFun := fun a => Ideal.Quotient.mk _ (σ a)
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp [MulChar.map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _), Ideal.Quotient.eq]
        have := hspan (hσ a b)
        rwa [sub_sub] at this }

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hvζ : v ζ = 1 := val_eq_one_of_pow_eq_one v hpp.ne_zero hζ.pow_eq_one
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvζ.le
  have hzp : z ^ p = 1 := hv.hom_inj (by rw [map_pow, hζ.pow_eq_one, map_one])
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨y, hym, hy⟩ := ReciprocityTheory.PGsh.gaussCongruence p F R (ltOneIdeal v R hv) ι σ z hF hzp
    (fun a => rfl)

  let ψ₀ : AddChar F C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ₀ : ∀ a, ψ₀ a = algebraMap R C z ^ (Algebra.trace (ZMod p) F a).val := fun a => rfl
  have hψ₀1 : ψ₀ ≠ 1 := by
    haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
    obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod p) F 1
    intro h
    have h1 : ψ₀ b = 1 := by rw [h]; simp
    rw [hψ₀] at h1
    have hb0 : (Algebra.trace (ZMod p) F b).val ≠ 0 := by
      rw [hb, Ne, ZMod.val_eq_zero]
      exact one_ne_zero
    exact hζ.pow_ne_one_of_pos_of_lt hb0 (ZMod.val_lt _) h1
  obtain ⟨c, rfl⟩ := exists_mulShift_eq ψ₀ ψ hψ₀1
  have hc : c ≠ 0 := by
    rintro rfl
    exact hψ (AddChar.mulShift_zero _)
  have hσc : σ c * σ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  have hsum : ∑ a, algebraMap R C (σ⁻¹ a) * AddChar.mulShift ψ₀ c a =
      algebraMap R C (σ c) * ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ (fun a => ?_)
    simp only [Equiv.mulLeft₀_apply, AddChar.mulShift_apply, map_mul, ← mul_assoc]
    rw [← map_mul, hσc, map_one, one_mul]
  have hvσ : v (algebraMap R C (σ c)) = 1 := by
    have h1 : v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) = 1 := by
      rw [← map_mul, ← map_mul, hσc, map_one, map_one]
    refine le_antisymm (hv.map_le_one _) ?_
    calc (1 : NNReal) = v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) := h1.symm
      _ ≤ v (algebraMap R C (σ c)) := mul_le_of_le_one_right' (hv.map_le_one _)
  have hG : ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b =
      (algebraMap R C z - 1) * (algebraMap R C y - 1) := by
    have := congrArg (algebraMap R C) hy

    simp only [map_sum, map_mul, map_pow, map_sub, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by rw [hψ₀]
  have hvy : v (algebraMap R C y - 1) = 1 := by
    have h : v (algebraMap R C y) < v (1 : C) := by
      rw [map_one]; exact hym
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left v h, map_one]
  rw [hsum, hG, map_mul, map_mul, hvσ, hvy, one_mul, mul_one]
  exact val_sub_one_pow v p hζ

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.padic_embeddings_conjugate_of_units : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (κ κ' : K →+* ℂ_[p]), (∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) → ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | exact GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem ideal_local_generator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I :=
  @PositivityTheory.Xgf.ideal_padic_generator_log_norm

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.hopf_order_translation_invariant : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.DualLattice

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.Reflexive

theorem locFree_dual : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (β : E →ₗ[Ω] E₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∀ (r : ℕ) (L : AddSubgroup E) (L₁ : AddSubgroup E₁), LocFree R r L → (∀ w, w ∈ L₁ ↔ ∀ v ∈ L, β v w ∈ R) → LocFree R r L₁ ∧ ∀ v, v ∈ L ↔ ∀ w ∈ L₁, β v w ∈ R := by
  intro o Ω _ _ _ R E E₁ _ _ _ _ β hβ r L L₁ h h₁
  classical
  refine ⟨?_, fun v => ⟨fun hv w hw => (h₁ w).1 hw v hv, fun hv => ?_⟩⟩
  swap
  · refine locFree_reflexive R r L h v fun ψ hψ => ?_
    obtain ⟨w, rfl⟩ := hβ.2 ψ
    exact hv w ((h₁ w).2 hψ)
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine ⟨fun a ha w hw => (h₁ _).2 fun v hv => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact R.mul_mem ha ((h₁ w).1 hw v hv)
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  let e : E₁ ≃ₗ[Ω] Module.Dual Ω E := LinearEquiv.ofBijective β.flip hβ
  let C : Module.Basis (Fin r) Ω E₁ := B.dualBasis.map e.symm
  have hrepr : ∀ w q, C.repr w q = β (b q) w := fun w q => by
    simp [C, e, ← hB]
  have hsum : ∀ (a : Fin r → Ω) q, β (b q) (∑ q', a q' • C q') = a q := fun a q => by
    rw [← hrepr]
    exact congrFun (C.repr_sum_self a) q
  refine ⟨C, C.linearIndependent, C.span_eq, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => C.repr w q, fun q => ?_, (C.sum_repr w).symm⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, f l ^ m • b q ∈ L := by
      refine (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · by_cases hq : q' = q
        · subst hq; simp
        · simp [hq]
      · simp [Pi.single_apply]
    refine ⟨n + m, ?_⟩
    have h2 := (h₁ _).1 hn _ hm
    have h3 : β (f l ^ m • b q) (f l ^ n • w) = f l ^ (n + m) * C.repr w q := by
      rw [hrepr]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rwa [h3] at h2
  · rintro ⟨a, ha, rfl⟩
    let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
    have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
    obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l)
      (β.flip (∑ q, a q • C q)) fun v hv => by
        obtain ⟨a', ha', rfl⟩ := (hb v).1 ⟨0, by simpa using hv⟩
        have key : ∀ q, ∃ n : ℕ, f l ^ n • (a' q * a q) ∈ R' := fun q => by
          obtain ⟨n, hn⟩ := ha q
          obtain ⟨n', hn'⟩ := ha' q
          refine ⟨n' + n, ?_⟩
          have h4 : f l ^ (n' + n) • (a' q * a q) = f l ^ n' * a' q * (f l ^ n * a q) := by
            rw [smul_eq_mul]; ring
          rw [h4]
          exact R.mul_mem hn' hn
        obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f l) (hf l) _ key
        refine ⟨n, ?_⟩
        have h5 : β.flip (∑ q, a q • C q) (∑ q, a' q • b q) = ∑ q, a' q * a q := by

          rw [map_sum (β.flip (∑ q, a q • C q))]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, LinearMap.flip_apply, hsum, smul_eq_mul]
        rw [h5, Finset.mul_sum]
        exact R'.sum_mem fun q _ => hn q
    refine ⟨m, (h₁ _).2 fun v hv => ?_⟩
    rw [map_smul, smul_eq_mul]
    exact hm v hv

end GlobalTheory.CompanionTheory.Ar.Num.DualLattice
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_finite_projective_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup → Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧ IsBaseChange Ω L.subtype := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_of_finite_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective <;> assumption)
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem ProIso.nonempty_of_forall_prime : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_crt

end GlobalTheory.CompanionTheory.Ar
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem proIsoAt_of_padic_isometry : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_lift

end GlobalTheory.CompanionTheory.Ar
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.hopf_order_contains_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.HhGraded

open GlobalTheory.CompanionTheory.Ar.Num

theorem mem_dotDual_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    (L : AddSubgroup (Fin n → Ω)) (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_annSub_iff {Ω : Type} [Field Ω] {n k : ℕ} (l : Fin n → Ω) :
    l ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

theorem single_mem_annSub {Ω : Type} [Field Ω] {n k : ℕ} (j : Fin n) (hj : k ≤ (j : ℕ)) :
    (Pi.single j 1 : Fin n → Ω) ∈ annSub Ω n k := by
  rw [mem_annSub_iff]
  intro m hm
  have : m ≠ j := fun h => by subst h; omega
  simp [Pi.single_apply, this]

theorem map_eq_sum {Ω : Type} [Field Ω] {n : ℕ} (ρ : (Fin n → Ω) →ₗ[Ω] (Fin n → Ω)) (l : Fin n → Ω) :
    ρ l = ∑ j, l j • ρ (Pi.single j 1) := by
  have h : l = ∑ j, l j • (Pi.single j 1 : Fin n → Ω) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]

  conv_lhs => rw [h, map_sum]
  simp only [map_smul]

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ)
    (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) →
    ∀ (i : Fin n) (u : Ω), u ≠ 0 →
    (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔
      ∃ a ∈ R, c = a * u) →
    ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  intro o Ω _ _ _ R n L _ hS i u hu hc t
  constructor
  · rintro ⟨v, hv, hz, rfl⟩
    obtain ⟨l, hl, hlu⟩ := (hc u).2 ⟨1, R.one_mem, (one_mul u).symm⟩
    have hlL : l ∈ L := (AddSubgroup.mem_inf.1 hl).1
    have hlA : l ∈ annSub Ω n i := (AddSubgroup.mem_inf.1 hl).2
    have hlu' : l i = u := hlu
    have h2 : l ⬝ᵥ v = u * v i := by
      rw [dotProduct, Finset.sum_eq_single i, hlu']
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [(mem_annSub_iff l).1 hlA j h, zero_mul]
        · rw [hz j h, mul_zero]
      · simp
    refine ⟨u * v i, ?_, ?_⟩
    · rw [← h2]
      exact (mem_dotDual_iff R L v).1 hv l hlL
    · field_simp
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ρ, hρU, hρid, hρL⟩ := hS i
    have hfix : ∀ j : Fin n, i ≤ j → ρ (Pi.single j 1) = Pi.single j 1 := fun j hj =>
      hρid _ (single_mem_annSub j hj)
    refine ⟨fun j => (a * u⁻¹) * ρ (Pi.single j 1) i, ?_, ?_, ?_⟩
    · rw [mem_dotDual_iff]
      intro l hl
      have key : l ⬝ᵥ (fun j => (a * u⁻¹) * ρ (Pi.single j 1) i) = (a * u⁻¹) * ρ l i := by
        rw [map_eq_sum ρ l, dotProduct, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hl' : ρ l i ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map
          (Pi.evalAddMonoidHom (fun _ => Ω) i) :=
        ⟨ρ l, AddSubgroup.mem_inf.2 ⟨hρL l hl, hρU l⟩, rfl⟩
      obtain ⟨b, hb, hbe⟩ := (hc _).1 hl'
      have h3 : a * u⁻¹ * (b * u) = a * b := by field_simp
      rw [key, hbe, h3]
      exact R.mul_mem ha hb
    · intro j hj
      have hne : i ≠ j := ne_of_lt hj
      simp only [hfix j hj.le, Pi.single_apply, hne, if_false, mul_zero]
    · simp only [hfix i le_rfl, Pi.single_eq_same, mul_one]

end GlobalTheory.CompanionTheory.Ar.Num.HhGraded
end
