module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem sumOp_comp_of_between : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle
  have hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hle hb)
    exact ⟨c, hc.1, hc.2, by simpa using ha.2⟩
  have hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B := by
    intro x hxA hxC
    refine (hB x).2 fun b hb => ?_
    obtain ⟨c, -, hcC, hcA⟩ := hdec b hb
    have e : b = (b - c) + c := by abel
    rw [e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]
  obtain ⟨tAB, tAB2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A B hB
  obtain ⟨tBC, tBC2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h B C hC
  obtain ⟨tAC, -, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A C hC
  obtain ⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩ := tAB2 hAB
  obtain ⟨⟨m, g, hgC, hg⟩, -, -⟩ := tBC2 hBC
  choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)
  have hf : ∀ b ∈ B, ∃! i, b - f i ∈ A := by
    intro b hb
    have key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A := by
      intro i
      have e : b - f i = (b - f0 i) + (f0 i - f i) := by abel
      rw [e]
      exact A.add_mem_iff_left (hfA i)
    simp only [key]
    exact hf0 b hb
  have hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C := fun p => C.add_mem (hgC _) (hfC _)
  have hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A := by
    intro x hx
    obtain ⟨j, hj, hju⟩ := hg x hx
    obtain ⟨i, hi, hiu⟩ := hf _ hj
    refine ⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩
    rintro ⟨j', i'⟩ hp
    have hp' : x - (g j' + f i') ∈ A := hp
    have h1 : x - (g j' + f i') ∈ B := hAC _ hp' (C.sub_mem hx (hkC (j', i')))
    have h2 : x - g j' ∈ B := by
      have e : x - g j' = (x - (g j' + f i')) + f i' := by abel
      rw [e]
      exact B.add_mem h1 (hfB i')
    obtain rfl : j' = j := hju j' h2
    obtain rfl : i' = i := hiu i' (by simpa [sub_add_eq_sub_sub] using hp')
    rfl
  have z : ∀ D : Submodule R X, Fixes W D 0 := fun D a _ => map_zero _
  refine ⟨?_, fun v hv => ?_⟩
  · rw [(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2,
      (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]
  · rw [(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1,
      (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v

end GlobalTheory.FinWeil
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique_of_gauss : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have key : ∀ W : ValuationSubring L, Gauss t V W →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.gaussExtension_coeff_mem_nonunits t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ h₁ h₂ (key W₁ h₁))
    (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ h₂ h₁ (key W₂ h₂))

end GlobalTheory.BertiniNoether
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem rootOfUnity_eq_one_of_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {m : ℕ} (hm : ¬ v (m : K) < 1) {η : K} (hη : η ^ m = 1) (h1 : v (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hm
  have hv : v η = 1 := by
    have := v.map_one_add_of_lt h1
    simpa using this
  have hi : ∀ i : ℕ, v (1 - η ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - η ^ (i + 1) = (1 - η ^ i) + -(η ^ i * (η - 1)) := by ring
      rw [e]
      refine v.map_add_lt ih ?_
      rw [v.map_neg, map_mul, map_pow, hv, one_pow, one_mul]
      exact h1
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have e : (m : K) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact v.map_sum_lt one_ne_zero fun i _ => hi i

theorem not_val_lt_one_of_coprime {K : Type*} [Field K] (V : ValuationSubring K) {m q : ℕ} (h : Nat.Coprime m q)
    (hq : V.valuation (q : K) < 1) : ¬ V.valuation (m : K) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : (1 : K) = (a : K) * m + (b : K) * q := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hz : ∀ (c : ℤ) (x : K), V.valuation x < 1 → V.valuation ((c : K) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    have hc : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (intCast_mem V c)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx
  have := V.valuation.map_add_lt (hz a _ hm) (hz b _ hq)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem FrobV.apply_rootOfUnity {Ω : Type} [Field Ω] [Algebra ℚ Ω] {V : ValuationSubring Ω} {q : ℕ}
    {s : Ω ≃ₐ[ℚ] Ω} (hs : FrobV V q s) {m : ℕ} (hm0 : m ≠ 0) (hm : Nat.Coprime m q) {ζ : Ω} (hζ : ζ ^ m = 1) :
    s ζ = ζ ^ q := by
  have hq : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.mp hs.1
  have hv : V.valuation ζ = 1 := by
    have := congrArg V.valuation hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_left hm0).mp this
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : ζ ∈ V := (V.valuation_le_one_iff _).mp hv.le
  have h := (hs.2 ζ hV).2.2
  have hq0 : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : s ζ / ζ ^ q = 1 := by
    refine rootOfUnity_eq_one_of_val V.valuation (not_val_lt_one_of_coprime V hm hq) ?_ ?_
    · rw [div_pow, ← map_pow, hζ, map_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
    · rw [div_sub_one hq0, map_div₀, map_pow, hv, one_pow, div_one]
      exact h
  exact (div_eq_one_iff_eq hq0).mp key

theorem cyclotomicCharacter_frobV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l q : ℕ) [Fact l.Prime],
    q.Prime → q ≠ l → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q := by
  intro Ω _ _ _ l q hl hq hql V s hs
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, NeZero ((l ^ i : ℕ) : Ω) := fun i => ⟨by exact_mod_cast pow_ne_zero i hl.out.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ (l ^ n) = 1 := (mem_rootsOfUnity' _ _).mp ht
  have hc : Nat.Coprime (l ^ n) q := ((Nat.coprime_primes hl.out hq).mpr hql.symm).pow_left n
  have := hs.apply_rootOfUnity (pow_ne_zero n hl.out.ne_zero) hc ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod q ht']
  exact this

end GlobalTheory.KZ.ES
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CongruenceDescent

theorem mem_Gamma_iff_exists {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma N ↔ ∃ B : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have d00 : (N : ℤ) ∣ γ 0 0 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
    have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
    have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
    have d11 : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
    obtain ⟨a, ha⟩ := d00; obtain ⟨b, hb⟩ := d01; obtain ⟨c, hc⟩ := d10; obtain ⟨d, hd⟩ := d11
    refine ⟨!![a, b; c, d], ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨B, hB⟩
    have e : ∀ i j, γ i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := fun i j => by
      rw [show γ i j = (γ : Matrix (Fin 2) (Fin 2) ℤ) i j from rfl, hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  obtain ⟨c, rfl⟩ := h
  exact mem_Gamma_iff_exists.2 ⟨(c : ℤ) • B, by rw [hB, smul_smul]; push_cast; ring_nf⟩

theorem pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    γ ^ q ∈ CongruenceSubgroup.Gamma (L * q) := by
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  have key : ∀ m : ℕ, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ m = 1 + ((m : ℤ) * L) • B + ((L : ℤ) * L) • (B * B * Y) := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      refine ⟨(m : ℤ) • 1 + Y + Y * ((L : ℤ) • B), ?_⟩
      rw [pow_succ, hY, hB]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, Matrix.mul_assoc]
      push_cast
      module
  obtain ⟨Y, hY⟩ := key q
  obtain ⟨c, rfl⟩ := hq
  refine mem_Gamma_iff_exists.2 ⟨B + (c : ℤ) • (B * B * Y), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hY, smul_add, smul_smul]
  push_cast
  module

theorem pow_pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) (j : ℕ) :
    γ ^ (q ^ j) ∈ CongruenceSubgroup.Gamma (L * q ^ j) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, mul_one] using hγ
  | succ j ih =>
    rw [pow_succ, pow_mul, ← mul_assoc]
    exact pow_mem_Gamma_mul (hq.mul_right _) ih

theorem coprime_card_of_pow_eq_one {Q : Type} [Group Q] [Finite Q] {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m)
    (h : ∀ x : Q, x ^ m = 1) : l.Coprime (Nat.card Q) := by
  rw [hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  exact (hl.coprime_iff_not_dvd.1 hm) this

theorem exists_invariant {H A : Type} [Group H] [CommGroup A] (s : H → A →* A)
    (hs : ∀ g h a, s (g * h) a = s h (s g a)) (D : Subgroup H) [D.Normal] [Finite (H ⧸ D)] {m : ℕ}
    (hm : m.Coprime (Nat.card (H ⧸ D))) (f : A) (hD : ∀ δ ∈ D, s δ f = f) (hf : ∀ γ, ∃ g : A, s γ f = f * g ^ m) :
    ∃ h : A, ∀ γ, s γ (f * h ^ m) = f * h ^ m := by
  classical
  haveI := Fintype.ofFinite (H ⧸ D)
  choose g hg using hf
  have hwd : ∀ a b : H, (a : H ⧸ D) = b → s a f = s b f := by
    intro a b hab
    have h1 : a * (a⁻¹ * b) * a⁻¹ ∈ D :=
      Subgroup.Normal.conj_mem (a⁻¹ * b) (QuotientGroup.eq.1 hab) a
    have h2 : b = (a * (a⁻¹ * b) * a⁻¹) * a := by group
    conv_rhs => rw [h2, hs, hD _ h1]
  set F : A := ∏ x : H ⧸ D, s x.out f with hF
  have hinv : ∀ γ, s γ F = F := by
    intro γ
    rw [hF, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (γ : H ⧸ D)) _ _ fun x => ?_
    rw [← hs]
    apply hwd
    simp
  have hFeq : F = f ^ Nat.card (H ⧸ D) * (∏ x : H ⧸ D, g x.out) ^ m := by
    rw [hF]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hm
  refine ⟨f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v, fun γ => ?_⟩
  have e : f * (f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v) ^ m = F ^ v := by
    have e1 : f * f ^ (-u * (m : ℤ)) = f ^ ((Nat.card (H ⧸ D) : ℤ) * v) := by
      rw [← _root_.zpow_one_add]
      congr 1
      linear_combination -huv
    rw [hFeq, mul_pow, _root_.mul_zpow, ← _root_.zpow_natCast, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_natCast]
    simp only [← _root_.zpow_mul]
    rw [← mul_assoc, e1, mul_comm v]
  rw [e, map_zpow, hinv]

end GlobalTheory.KZ.ES.CongruenceDescent

namespace GlobalTheory.KZ.ES


open CongruenceDescent CongruenceSubgroup in
theorem exists_lev_mul_pow_of_invariant_mod_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M e hl hM f hlev hf
  obtain ⟨a, q, hq, hMq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have hlq : l.Coprime q := hl.coprime_iff_not_dvd.2 hq
  let H : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma (M * l ^ (a * e))
  haveI := CongruenceSubgroup.Gamma_normal (M ^ e)
  haveI : NeZero (M ^ e) := ⟨(pow_pos hM e).ne'⟩
  let D : Subgroup H := (CongruenceSubgroup.Gamma (M ^ e)).subgroupOf H
  haveI : D.FiniteIndex := inferInstance
  have hcard : l.Coprime (Nat.card (H ⧸ D)) := by
    refine CongruenceDescent.coprime_card_of_pow_eq_one hl (hlq.pow_right e) fun x => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    refine CongruenceDescent.Gamma_le_of_dvd ?_ (CongruenceDescent.pow_pow_mem_Gamma_mul (q := q) ?_ γ.2 e)
    · exact ⟨M, by rw [hMq]; ring⟩
    · exact ⟨l ^ a * l ^ (a * e), by rw [hMq]; ring⟩
  obtain ⟨h, hh⟩ := CongruenceDescent.exists_invariant (H := H) (A := X.Kˣ)
    (fun γ => Units.map (X.sl (ofSL γ) : X.K →* X.K))
    (fun g h a => Units.ext (by simp [X.sl_mul])) D (hcard.pow_left n) f
    (fun δ hδ => Units.ext (by simpa using hlev δ hδ))
    (fun γ => by
      obtain ⟨g, hg⟩ := hf γ (CongruenceDescent.Gamma_le_of_dvd (dvd_mul_right _ _) γ.2)
      exact ⟨g, Units.ext (by simpa using hg)⟩)
  refine ⟨a * e, h, fun γ hγ => ?_⟩
  have := congrArg Units.val (hh ⟨γ, hγ⟩)
  simpa using this

end GlobalTheory.KZ.ES
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s → (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) → (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) → (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  first | exact @GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | exact GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | (intros; apply GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero <;> assumption)
end
