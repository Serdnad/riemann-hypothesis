module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Formalism.GaloisCohomology.StatementLoc
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle191
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.CyclotomicH2Bound

open GlobalTheory.ShapeNeg

theorem cycK_eq_of_prim {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (n : ℕ)
    (g : Formalism.GaloisCohomology.GK p K) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) (a : ℕ)
    (ha : g ζ = ζ ^ a) : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (a : ZMod (p ^ n)) := by
  have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have h1 : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [h1, ha] at hsp
  have h3 : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) =
      (PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]) := rfl
  rw [h3]
  set b := ((PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]))
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hz : ζ ^ ((a : ℤ) - (b.val : ℤ)) = 1 := by
    rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
  have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
  have h0 : (((a : ℤ) - (b.val : ℤ) : ℤ) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hd
  push_cast at h0
  rw [ZMod.natCast_zmod_val] at h0
  exact (sub_eq_zero.1 h0).symm

theorem exists_prim (p : ℕ) [Fact p.Prime] (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem finite_quot [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ k}) := by
  have hI : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm
  haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
    rw [hI]; exact (inferInstance : Finite (IsLocalRing.ResidueField O))
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

theorem lev_cyclic {M : Type} [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] Formalism.NG.KO O)
    {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ x₀ : Lev M (ϖ ^ n), ∀ y : Lev M (ϖ ^ n), ∃ t : O, y = t • x₀ := by
  have hϖ0 : (algebraMap O (FractionRing O) ϖ) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖ.ne_zero
  let z₀ : FractionRing O := (algebraMap O (FractionRing O) ϖ ^ n)⁻¹
  have hk : (ϖ ^ n) • eM.symm (Submodule.Quotient.mk z₀) = 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, map_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hϖ0)]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.one_le.1 le_rfl), map_zero]
  refine ⟨Lev.mk _ hk, fun y => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (eM y.val)
  have hy := y.smul_val
  have hm : (ϖ ^ n) • (Submodule.Quotient.mk z : Formalism.NG.KO O) = 0 := by
    rw [hz, ← map_smul, hy, map_zero]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, Lev.ext ?_⟩
  rw [Lev.val_smul, Lev.val_mk, ← eM.symm_apply_apply y.val, ← hz, ← map_smul,
    ← Submodule.Quotient.mk_smul]
  congr 2
  rw [Algebra.smul_def, ht, Algebra.smul_def, map_pow, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_mul]

theorem td_nsmul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M) (k : ℕ)
    (y : M) : φ (k • y) = k • φ y := map_nsmul (show M →ₗ[R] R from φ) k y
theorem td_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x - y) = φ x - φ y := (show M →ₗ[R] R from φ).map_sub x y
theorem td_add {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x + y) = φ x + φ y := (show M →ₗ[R] R from φ).map_add x y

theorem out_smul {N : Type} [AddCommGroup N] [Module O N] {ϖ : O} (k : ℕ) {z : N}
    (hz : (ϖ ^ k) • z = 0) (t : O) : (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out • z = t • z := by
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t := Ideal.Quotient.mk_out _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
  rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hz, smul_zero]

theorem h2_bounded_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hLTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ ε hε e M _ _ eM ρ hρ σ₀ hσ hcont
  have hw : ((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1 ≠ 0 := by
    intro h0; apply hσ; ext; rw [Units.val_one]; exact sub_eq_zero.1 h0
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hpϖ
  haveI hQ := finite_quot hϖ c
  refine ⟨(p ^ c) ^ ((p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hkn : ∀ y : Lev M (ϖ ^ n), (ϖ ^ n) • y = 0 := fun y => Lev.ext (by
    rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  haveI : Finite (Lev M (ϖ ^ n)) := by
    haveI := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) (fun y => ?_)
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n (hkn x₀) t⟩
  obtain ⟨⟨eB⟩, -, -, -, hcup, -⟩ := hLTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)
  have hpn : ∀ y : Lev M (ϖ ^ n), ((p : O) ^ n) • y = 0 := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hr, mul_smul, hkn, smul_zero]
  obtain ⟨ζ, hζ⟩ := exists_prim p n
  obtain ⟨a₀, ha₀, hdiff⟩ := hε σ₀ n ζ hζ.pow_eq_one
  have hcyc := cycK_eq_of_prim n σ₀ hζ a₀ ha₀
  have hεy : ∀ y : Lev M (ϖ ^ n), ((ε σ₀ : Oˣ) : O) • y = (a₀ : O) • y := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hdiff
    rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hpn, smul_zero]
  have hεk : ∀ (k : ℕ) (y : Lev M (ϖ ^ n)), ((ε σ₀ : Oˣ) : O) ^ k • y = (a₀ ^ k : ℕ) • y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, mul_smul, hεy, ih, ← Nat.cast_smul_eq_nsmul O (a₀ ^ k),
        ← Nat.cast_smul_eq_nsmul O (a₀ ^ (k + 1)), smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_succ]
  have hinv : ∀ y : Lev M (ϖ ^ n), levRepZ p n h ρ σ₀⁻¹ y = ((ε σ₀ : Oˣ) : O) ^ e • y := by
    intro y; apply Lev.ext
    rw [levRepZ_apply, levRep_val, hρ, Lev.val_smul, map_inv, inv_pow, inv_inv, Units.val_pow_eq_pow_val]
  let A := H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id _))
  have hfix : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n))) * (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y := by
    intro a y
    have h1 := DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 a.2 σ₀) y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at h1
    rw [hinv, hεk, td_nsmul, nsmul_eq_mul, hcyc, ← mul_assoc] at h1
    have h2 : ((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n)) = (a₀ : ZMod (p ^ n)) * ((a₀ ^ e : ℕ) : ZMod (p ^ n)) := by
      push_cast; ring
    rw [h2]; exact h1
  have hkill : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((ϖ ^ c) • y) = 0 := by
    intro a y
    have hy : (ϖ ^ c) • y = (((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1) • (((u⁻¹ : Oˣ) : O) • y) := by
      rw [hu, smul_smul, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]
    rw [hy, sub_smul, one_smul, Units.val_pow_eq_pow_val, hεk, td_sub, td_nsmul, nsmul_eq_mul, hfix,
      sub_self]
  have hkillp : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((p ^ c : ℕ) • y) = 0 := by
    intro a y
    have hy : (p ^ c : ℕ) • y = (ϖ ^ c) • ((s ^ c) • y) := by
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← mul_pow, mul_comm ϖ s, hs, Nat.cast_pow]
    rw [hy, hkill]
  have hA : ∀ a : A, (p ^ c : ℕ) • a = 0 := by
    intro a; apply Subtype.ext; apply LinearMap.ext; intro y
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), Submodule.coe_smul]
    change ((p ^ c : ℕ) : ZMod (p ^ n)) •
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y = 0
    rw [Nat.cast_smul_eq_nsmul, ← td_nsmul, hkillp]
  let T := {x : ZMod (p ^ n) // (p ^ c) • x = 0}
  have hT : Nat.card T ≤ p ^ c := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsAddCyclic.card_nsmul_eq_zero_le (pow_pos (Fact.out : p.Prime).pos c)
  have hq : ∀ (a : A) (t : O), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n)))
      ((Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀) =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (t • x₀) := by
    intro a t
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t)))
    have h1 : (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀ = t • x₀ + (ϖ ^ c) • (r • x₀) := by
      rw [smul_smul, mul_comm (ϖ ^ c) r, hr, sub_smul, add_sub_cancel]
    rw [h1, td_add, hkill, add_zero]
  let G : A → (O ⧸ Ideal.span {ϖ ^ c} → T) := fun a q =>
    ⟨(a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (q.out • x₀), by rw [← td_nsmul, hkillp]⟩
  have hGinj : Function.Injective G := by
    intro a a' hG; apply Subtype.ext; apply LinearMap.ext; intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    have h1 := congrArg Subtype.val (congrFun hG (Ideal.Quotient.mk _ t))
    simp only [G] at h1
    rwa [hq a t, hq a' t] at h1
  haveI : Finite A := Finite.of_injective G hGinj
  have hAcard : Nat.card A ≤ (p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c}) :=
    (Nat.card_le_card_of_injective G hGinj).trans (by rw [Nat.card_fun]; exact Nat.pow_le_pow_left hT _)
  let F : H2 ((levRepZ p n h ρ).comp (MonoidHom.id _)) → (A → T) := fun f a =>
    ⟨eB (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) f a), by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ← LinearEquiv.map_smul, ← LinearMap.map_smul,
        Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), hA a, LinearMap.map_zero, LinearEquiv.map_zero]⟩
  have hFinj : Function.Injective F := by
    intro f f' hF; apply hcup; apply LinearMap.ext; intro a; apply eB.injective
    exact congrArg Subtype.val (congrFun hF a)
  show Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id _))) ≤ _
  calc _ ≤ Nat.card (A → T) := Nat.card_le_card_of_injective F hFinj
    _ = Nat.card T ^ Nat.card A := Nat.card_fun
    _ ≤ (p ^ c) ^ Nat.card A := Nat.pow_le_pow_left hT _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos c) hAcard

end GlobalTheory.CyclotomicH2Bound
end
end

section

open Formalism.GaloisCohomology ReciprocityTheory.Gal

namespace GlobalTheory

theorem finite_H1_H2_of_localTateDuality : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hC, -, h11, h11f, h20⟩ := hT l K hK r M rho hr hrho
  obtain ⟨e⟩ := hC
  haveI hCfin : Finite (H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hAB := GlobalTheory.T.finite_of_bijective_pairing_zmod (l ^ r) _ _ _ _ ⟨e⟩ h11 h11f
  refine ⟨hAB.2, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K)))) :=
    Subtype.finite
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  exact Finite.of_injective _ h20.1

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycLevel

theorem toZModPow_eq_of_norm_sub_le {l : ℕ} [Fact l.Prime] (u : ℤ_[l]) (a : ℕ) (r : ℕ)
    (h : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ))) :
    (PadicInt.toZModPow r u : ZMod (l ^ r)) = (a : ZMod (l ^ r)) := by
  have h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
    rw [PadicInt.norm_def]; push_cast; exact h
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (u - (a : ℤ_[l])) r).mp h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  exact h2

theorem chi_reduces (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧
      (PadicInt.toZModPow r u : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr K.1
    (IntermediateField.fixingSubgroupEquiv K.1 g) r
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) r ζ hζ1
  have key := hζ a hga
  have hr : (l : ℝ) ^ (-(r : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · simp
  have hnorm : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have e : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha.trans hr) ?_)
    have := PadicInt.norm_le_one (a : ℤ_[l])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  let u : ℤ_[l] := ⟨_, hnorm⟩
  have hu : (u : ℚ_[l]) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := rfl
  have ha' : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by rw [hu]; exact ha
  refine ⟨u, (P.PD_χ K g).trans hu.symm, ?_⟩
  rw [toZModPow_eq_of_norm_sub_le u a r ha', key]
  rfl

end GlobalTheory.CycLevel
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
end

section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add (f := _), Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.FrobDense

theorem conj_ne {R : Ranks} (H : Host R) :
    starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem sqrt_sq {R : Ranks} (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  apply H.φ₀.injective
  rw [map_pow, h3, h0]
  simp

theorem exists_finite_split {R : Ranks} (H : Host R) :
    ∃ A : Set (HeightOneSpectrum (𝓞 H.E)), A.Finite ∧
    ∀ v, v ∉ A → v.asIdeal.inertiaDeg ℤ = 1 → IsSplitPl H v := by
  have hint : IsIntegral ℤ H.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    have := (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg
    simpa using this
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  let b : 𝓞 H.E := ⟨_, hint⟩
  have hb : c b - b ≠ 0 := by
    intro h
    have h1 : H.conj H.sqrtMinusD = H.sqrtMinusD := congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)
    have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
    have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := h2
    rw [h1, h3] at h4
    exact conj_ne H h4.symm
  refine ⟨{v | v.asIdeal ∣ Ideal.span {c b - b}},
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩
  by_contra hs
  apply hv
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 hd
  have hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal := by
    intro x hx
    by_contra hx'
    refine hs ⟨x, hx, fun y hy => ?_⟩
    have : y = c x := RingOfIntegers.ext hy
    rwa [this]
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have := v.isPrime
  have htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard one_ne_zero
  have hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) := by
    rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq, ← hn]; simp
  have h2 := hst _ h1
  rw [map_sub, map_intCast] at h2
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  have := v.asIdeal.sub_mem h2 h1
  simpa using this

end GlobalTheory.FrobDense
end
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)
end

section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_le_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  first | exact @GlobalTheory.few_roots_small_disc | exact GlobalTheory.few_roots_small_disc | (intros; apply GlobalTheory.few_roots_small_disc <;> assumption)
end
