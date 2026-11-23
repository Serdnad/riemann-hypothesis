module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSq
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
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
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Filtration
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_lagrange_resolvent : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G →
    ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  intro L _ p hp G _ _ _ _ _ hG ζ hζ hfix
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup p G hG
  set ψ : G → L := fun g => ζ ^ (Multiplicative.toAdd (χ g)).val with hψdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hmod : ∀ n : ℕ, ζ ^ n = ζ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζp, one_pow, one_mul]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    simp only [hψdef, map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (hmod _).symm
  have hψp : ∀ g, ψ g ^ p = 1 := by
    intro g; simp only [hψdef]; rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hψne : ∀ g, ψ g ≠ 0 := fun g h => by
    have := hψp g; rw [h, zero_pow hp.ne_zero] at this; exact zero_ne_one this
  have hψfix : ∀ g h : G, g • ψ h = ψ h := fun g h => by simp only [hψdef, smul_pow', hfix]
  let f : G → (L →* L) := fun g => (MulSemiringAction.toRingHom G L g : L →* L)
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact DFunLike.congr_fun hgh x
  have hli : LinearIndependent L (fun g : G => ((f g : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp f hf
  have hex : ∃ x : L, ∑ g : G, ψ g⁻¹ * (g • x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ g : G, ψ g⁻¹ • ((f g : L →* L) : L → L) = 0 := by
      funext x
      simpa [f, Finset.sum_apply] using hcon x
    exact hψne _ ((Fintype.linearIndependent_iff.mp hli) (fun g => ψ g⁻¹) h0 1)
  obtain ⟨x, hx⟩ := hex
  set α := ∑ g : G, ψ g⁻¹ * (g • x) with hα
  have hact : ∀ h : G, h • α = ψ h * α := by
    intro h
    rw [hα, Finset.smul_sum, Finset.mul_sum]
    simp only [smul_mul', hψfix, smul_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft]
    have e : ψ h * ψ h⁻¹ = 1 := by
      rw [← hψmul, mul_inv_cancel]; simp [hψdef]
    rw [mul_inv_rev, hψmul g⁻¹ h⁻¹]
    linear_combination (-(ψ g⁻¹ * ((h * g) • x))) * e
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨σ, α, hx, ?_, ?_⟩
  · rw [hact σ]
    congr 1
    simp [hψdef, hσ, ZMod.val_one]
  · intro g
    rw [smul_pow', hact g, mul_pow, hψp, one_mul]

end GlobalTheory.AlmostEt
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Equiv Finset

theorem card_cycleType_cons_mul (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (m : Multiset ℕ)
    (hpm : p ∉ m) (hs : m.sum ≤ N - p) (h2 : ∀ a ∈ m, 2 ≤ a) :
    (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card * p * (N - p).factorial
      = N.factorial * (univ.filter fun σ : Perm (Fin (N - p)) => σ.cycleType = m).card := by
  have hA := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin N) (p ::ₘ m)
  have hB := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (N - p)) m
  rw [Fintype.card_fin] at hA hB
  have hcA : (p ::ₘ m).sum ≤ N ∧ ∀ a ∈ p ::ₘ m, 2 ≤ a := by
    refine ⟨by rw [Multiset.sum_cons]; omega, fun a ha => ?_⟩
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hp
    · exact h2 a ha
  rw [if_pos hcA] at hA
  rw [if_pos ⟨hs, h2⟩] at hB
  have hsum : N - (p ::ₘ m).sum = N - p - m.sum := by
    rw [Multiset.sum_cons, Nat.sub_sub]
  have hfac : ∏ n ∈ (p ::ₘ m).toFinset, ((p ::ₘ m).count n).factorial =
      ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hpm), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hpm, zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hne : n ≠ p := fun h => hpm (h ▸ Multiset.mem_toFinset.1 hn)
    rw [Multiset.count_cons_of_ne hne]
  rw [hsum, Multiset.prod_cons, hfac] at hA
  rw [← hB, ← hA]
  ring

theorem card_mem_cycleType_mul (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by
  have hTm : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
      m.sum ≤ N - p ∧ ∀ a ∈ m, 2 ≤ a := by
    intro m hm
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨?_, fun a ha => Perm.two_le_of_mem_cycleType ha⟩
    simpa using τ.sum_cycleType_le
  have hpT : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType, p ∉ m := by
    intro m hm hpm
    have h1 := Multiset.le_sum_of_mem hpm
    have h2 := (hTm m hm).1
    omega
  have hfib : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card =
      ∑ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
        (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => σ.cycleType.erase p)
      (t := (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rw [← h2, Multiset.cons_erase h1]
      · intro h
        rw [h]
        exact ⟨Multiset.mem_cons_self _ _, Multiset.erase_cons_head _ _⟩
    · intro σ hσ
      have hσ' : p ∈ σ.cycleType := by simpa using hσ
      have hsum := Multiset.sum_erase hσ'
      have hle := σ.sum_cycleType_le
      rw [Fintype.card_fin] at hle
      have hc : (σ.cycleType.erase p).sum ≤ Fintype.card (Fin (N - p)) ∧
          ∀ a ∈ σ.cycleType.erase p, 2 ≤ a := by
        refine ⟨by rw [Fintype.card_fin]; omega, fun a ha => ?_⟩
        exact Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)
      obtain ⟨τ, hτ⟩ := (Perm.exists_with_cycleType_iff (Fin (N - p))).2 hc
      exact Finset.mem_image.2 ⟨τ, Finset.mem_univ _, hτ⟩
  have hmain : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p * (N - p).factorial
      = N.factorial * (N - p).factorial := by
    rw [hfib, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_congr rfl fun m hm =>
        card_cycleType_cons_mul N p hp hpN m (hpT m hm) (hTm m hm).1 (hTm m hm).2,
      ← Finset.mul_sum]
    congr 1
    have hc := Finset.card_eq_sum_card_image Perm.cycleType (univ : Finset (Perm (Fin (N - p))))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc
    exact hc.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hmain

theorem card_perm_long_cycle : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by
  intro N p hN hpN
  rcases Nat.lt_or_ge p 2 with hp | hp
  · obtain rfl : p = 1 := by omega
    obtain rfl : N = 1 := by omega
    have hall : ∀ σ : Equiv.Perm (Fin 1), 1 ∈ σ.partition.parts := by
      intro σ
      have hs : σ.partition.parts.sum = 1 := σ.partition.parts_sum.trans (Fintype.card_fin 1)
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := σ.partition.parts)
        (fun h => by rw [h, Multiset.sum_zero] at hs; exact absurd hs (by norm_num))
      have h1 := σ.partition.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      obtain rfl : a = 1 := by omega
      exact ha
    rw [Finset.filter_true_of_mem (fun σ _ => hall σ), Finset.card_univ, Fintype.card_perm]
    simp
  · have hiff : ∀ σ : Equiv.Perm (Fin N), p ∈ σ.partition.parts ↔ p ∈ σ.cycleType := by
      intro σ
      rw [Equiv.Perm.parts_partition, Multiset.mem_add]
      constructor
      · rintro (h | h)
        · exact h
        · have := Multiset.eq_of_mem_replicate h
          omega
      · exact Or.inl
    simp_rw [hiff]
    exact card_mem_cycleType_mul N p hp hN hpN

end GlobalTheory.BadShare
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.card_dual_zmod_module_eq_card : ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A], Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  first | exact @GlobalTheory.ZModDual.card_dual_eq | exact GlobalTheory.ZModDual.card_dual_eq | (intros; apply GlobalTheory.ZModDual.card_dual_eq <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.LangWitt

open Matrix

section Field

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

end Field

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

variable [IsAlgClosed k]

theorem map_add' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A + B).map f = A.map f + B.map f :=
  map_add f.mapMatrix A B

end Witt

end GlobalTheory.LangWitt
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl : ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  first | exact @GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | exact GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | (intros; apply GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem end_eq_one_of_pow_prime {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {p : ℕ} (hp : p.Prime) (hV : Module.finrank ℚ V + 1 < p) (f : Module.End ℚ V)
    (hf : f ^ p = 1) : f = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hf]
  have hdeg : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ V := by
    rw [← LinearMap.charpoly_natDegree f]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.pos
  have hne : minpoly ℚ f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral f)
  have hnd : ¬ cyclotomic p ℚ ∣ minpoly ℚ f := by
    intro h
    have h2 := natDegree_le_of_dvd h hne
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    omega
  have hcop : IsCoprime (minpoly ℚ f) (cyclotomic p ℚ) :=
    ((hirr.coprime_iff_not_dvd).2 hnd).symm
  have h3 : minpoly ℚ f ∣ X - 1 := hcop.dvd_of_dvd_mul_left h1
  obtain ⟨q, hq⟩ := h3
  have h4 : aeval f (X - 1 : ℚ[X]) = 0 := by
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

theorem gl_eq_one_of_pow_prime (E : Type) [Field E] [NumberField E] (N p : ℕ) (hp : p.Prime)
    (h : Module.finrank ℚ E * N + 1 < p) (γ : GL (Fin N) E) (hγ : γ ^ p = 1) : γ = 1 := by
  have hfin : Module.finrank ℚ (Fin N → E) = Module.finrank ℚ E * N := by
    rw [← Module.finrank_mul_finrank ℚ E (Fin N → E)]
    simp
  have hM : (γ : Matrix (Fin N) (Fin N) E) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hγ, Units.val_one]
  have hg : (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hM, Matrix.toLin'_one]; rfl
  have hf : ((Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)).restrictScalars ℚ :
      Module.End ℚ (Fin N → E)) ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hg v
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h1 := end_eq_one_of_pow_prime hp (by rw [hfin]; exact h) _ hf
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one]
  exact LinearMap.ext fun v => LinearMap.congr_fun h1 v

theorem gl_eq_one_of_pow_prime_pow :
    ∀ (E : Type) [Field E] [NumberField E] (N p : ℕ), p.Prime →
      Module.finrank ℚ E * N + 1 < p → ∀ γ : GL (Fin N) E, ∀ a : ℕ, γ ^ (p ^ a) = 1 → γ = 1 := by
  intro E _ _ N p hp h γ a
  induction a with
  | zero => intro h0; simpa using h0
  | succ a ih =>
    intro h0
    apply ih
    apply gl_eq_one_of_pow_prime E N p hp h
    rw [← pow_mul, ← pow_succ]
    exact h0

end GlobalTheory.BadShare
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_torsionFree_of_card_quotient_pow (l : ℕ) [Fact l.Prime] (C : Type)
    [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C]
    (h : ∀ r : ℕ, 0 < r →
      Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) :
    ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let N : ℕ → AddSubgroup C := fun r =>
    (LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))).toAddSubgroup
  have hmem : ∀ r (x : C), x ∈ N r ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := fun r x => Iff.rfl
  have hidx : ∀ r, 0 < r → (N r).index = l ^ r := fun r hr => h r hr
  let f : C →+ C := (LinearMap.lsmul ℤ_[l] C (l : ℤ_[l])).toAddMonoidHom
  have hf : ∀ x, f x = (l : ℤ_[l]) • x := fun x => rfl
  have hrange : f.range = N 1 := by
    ext x
    rw [hmem]
    simp only [AddMonoidHom.mem_range, hf, pow_one]
  have key : ∀ c : C, (l : ℤ_[l]) • c = 0 → ∀ k, 0 < k → c ∈ N k := by
    intro c hc k hk
    have h1 : N (k + 1) ≤ N 1 := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨(l : ℤ_[l]) ^ k • y, by rw [smul_smul, ← pow_add, add_comm]⟩
    have h2 := AddSubgroup.relIndex_mul_index h1
    rw [hidx 1 one_pos, hidx (k + 1) k.succ_pos, pow_one, pow_succ] at h2
    have h3 : ((N (k + 1)).comap f).index = l ^ k := by
      rw [AddSubgroup.index_comap, hrange]
      exact Nat.eq_of_mul_eq_mul_right hl h2
    have h4 : N k ≤ (N (k + 1)).comap f := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨y, by rw [hf, smul_smul, pow_succ']⟩
    have h5 := AddSubgroup.relIndex_mul_index h4
    rw [h3, hidx k hk] at h5
    have h6 : (N k).relIndex ((N (k + 1)).comap f) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hl k) (by rw [h5, one_mul])
    apply AddSubgroup.relIndex_eq_one.1 h6
    show f c ∈ N (k + 1)
    rw [hf, hc]
    exact zero_mem _
  have one : ∀ c : C, (l : ℤ_[l]) • c = 0 → c = 0 := by
    intro c hc
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C)
      (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [← Submodule.mem_bot ℤ_[l], ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨y, hy⟩ := (hmem _ _).1 (key c hc (i + 1) i.succ_pos)
    rw [← hy, pow_succ, mul_smul]
    refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ i) Submodule.mem_top
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  intro r
  induction r with
  | zero => intro c hc; simpa using hc
  | succ r ih =>
    intro c hc
    rw [pow_succ, mul_smul] at hc
    exact one c (ih _ hc)

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.algebraic_subring_closure_common_denominator : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω), ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω), ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  first | exact @GlobalTheory.finite_subring_common_denominator | exact GlobalTheory.finite_subring_common_denominator | (intros; apply GlobalTheory.finite_subring_common_denominator <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q : ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  first | exact @GlobalTheory.powerSeries_to_hahnSeries_rat | exact GlobalTheory.powerSeries_to_hahnSeries_rat | (intros; apply GlobalTheory.powerSeries_to_hahnSeries_rat <;> assumption)
end
