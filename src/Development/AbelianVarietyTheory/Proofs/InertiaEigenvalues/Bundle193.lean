module

public import Formalism.GaloisCohomology.StatementLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle181
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
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
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.ZMod.UnitsCyclic
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Module.ZMod
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open ReciprocityTheory.Gal

open Polynomial IntermediateField

namespace GlobalTheory.ShapeNeg

theorem natDegree_minpoly_le_mul {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) (hx : IsIntegral K x) :
    (minpoly ℚ_[p] x).natDegree ≤ (minpoly K x).natDegree * Module.finrank ℚ_[p] K := by
  set E := K⟮x⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hx
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  have h1 : Module.finrank ℚ_[p] K * Module.finrank K E = Module.finrank ℚ_[p] E :=
    Module.finrank_mul_finrank ℚ_[p] K E
  rw [adjoin.finrank hx] at h1
  have hxE : x ∈ E := mem_adjoin_simple_self K x
  haveI : IsScalarTower ℚ_[p] E (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h2 : minpoly ℚ_[p] (⟨x, hxE⟩ : E) = minpoly ℚ_[p] x :=
    (minpoly.algebraMap_eq (algebraMap E (PadicAlgCl p)).injective (⟨x, hxE⟩ : E)).symm
  have h3 := minpoly.natDegree_le (A := ℚ_[p]) (⟨x, hxE⟩ : E)
  rw [h2] at h3
  rw [mul_comm]
  omega

theorem natDegree_minpoly_le_card_pow_eq_one {p : ℕ} [Fact p.Prime]
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {N : ℕ} [NeZero N] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ) :
    (minpoly K ζ).natDegree ≤ Nat.card {x : ZMod N // x ^ k = 1} := by
  classical
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hirr : Irreducible (minpoly K ζ) := minpoly.irreducible hint
  have hsep : (minpoly K ζ).Separable := hirr.separable
  have hspl : Splits ((minpoly K ζ).map (algebraMap K (PadicAlgCl p))) := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl, ← Nat.card_eq_fintype_card]
  have hχ : ∀ σ : Formalism.GaloisCohomology.GK p K, ((hζ.autToPow K σ : ZMod N)) ^ k = 1 := by
    intro σ
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 := hζ.autToPow_spec K (σ ^ k)
    rw [hfix σ] at h1
    have h0 : ζ ^ (1 % N) = ζ := by rw [hζ.eq_orderOf, pow_mod_orderOf, pow_one]
    have h2 : ζ ^ (hζ.autToPow K (σ ^ k) : ZMod N).val = ζ ^ (1 % N) := h1.trans h0.symm
    have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
    rw [← ZMod.val_one_eq_one_mod] at h3
    exact ZMod.val_injective N h3
  have horb : ∀ y : (minpoly K ζ).rootSet (PadicAlgCl p), ∃ σ : Formalism.GaloisCohomology.GK p K, σ ζ = y := by
    intro y
    have hy : aeval (y : PadicAlgCl p) (minpoly K ζ) = 0 :=
      (mem_rootSet.1 y.2).2
    have he : minpoly K ζ = minpoly K (y : PadicAlgCl p) :=
      minpoly.eq_of_irreducible_of_monic hirr hy (minpoly.monic hint)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (PadicAlgCl p)).1 he.symm
    exact ⟨σ, hσ⟩
  choose σ hσ using horb
  refine Nat.card_le_card_of_injective (fun y => ⟨(hζ.autToPow K (σ y) : ZMod N), hχ (σ y)⟩) ?_
  intro y y' hyy
  have h : (hζ.autToPow K (σ y) : ZMod N) = (hζ.autToPow K (σ y') : ZMod N) :=
    congrArg Subtype.val hyy
  have h' : (σ y) ζ = (σ y') ζ := by
    rw [← hζ.autToPow_spec K (σ y), ← hζ.autToPow_spec K (σ y'), h]
  exact Subtype.ext (by rw [← hσ y, ← hσ y']; exact h')

theorem exists_pow_ne_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  intro p _ K hK k hk
  by_contra hcon
  push_neg at hcon
  have hp : p.Prime := Fact.out
  set d := Module.finrank ℚ_[p] K with hd
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * d < p ^ n := ⟨2 * k * d, Nat.lt_pow_self hp.one_lt⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  have hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ := fun σ => hcon σ (n + 1) ζ hζ.pow_eq_one
  have hB := natDegree_minpoly_le_card_pow_eq_one hζ k hfix
  have hC : Nat.card {x : ZMod (p ^ (n + 1)) // x ^ k = 1} ≤ 2 * k := by
    by_cases h2 : p = 2
    · subst h2
      exact GlobalTheory.card_pow_eq_one_two_pow_le (n + 1) (by omega) hk
    · haveI : IsCyclic (ZMod (p ^ (n + 1)))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 (n + 1)
      have := GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (p ^ (n + 1)) hk
      omega
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  have hA := natDegree_minpoly_le_mul hK ζ hint
  have hcyc : cyclotomic (p ^ (n + 1)) ℚ_[p] = minpoly ℚ_[p] ζ := by
    refine minpoly.eq_of_irreducible_of_monic (GlobalTheory.Cyc.Model.cyc_irred n) ?_ (cyclotomic.monic _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos _)
  rw [← hcyc, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hA
  rw [← hd] at hA
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h1 : p ^ n ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ hp1
  have h2 : (minpoly K ζ).natDegree * d ≤ 2 * k * d := Nat.mul_le_mul_right _ (hB.trans hC)
  omega

end GlobalTheory.ShapeNeg
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_trace_form_integral_iff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  intro l _ LL _ _ _ O _ _ hG
  have hint := (good_coeff_integers l LL O hG).1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let A : Subring LL := (algebraMap O LL).range
  have hZ : ∀ u : ℤ_[l], algebraMap ℤ_[l] LL u ∈ A := fun u =>
    padicInt_mem A (by rw [RingHom.coe_range]; exact hopen) u
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  let ψ : O ≃+* A := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  have hψ : ∀ a : A, algebraMap O LL (ψ.symm a) = a := fun a =>
    congrArg Subtype.val (ψ.apply_symm_apply a)
  let f : ℤ_[l] →+* O := ψ.symm.toRingHom.comp ((algebraMap ℤ_[l] LL).codRestrict A hZ)
  letI : Algebra ℤ_[l] O := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O LL := IsScalarTower.of_algebraMap_eq
    (fun u => (hψ ((algebraMap ℤ_[l] LL).codRestrict A hZ u)).symm)
  haveI : IsIntegralClosure O ℤ_[l] LL :=
    { algebraMap_injective := hinj
      isIntegral_iff := fun {x} => by
        rw [← Set.mem_range]
        exact (hint x).symm }
  let D : FractionalIdeal (nonZeroDivisors O) LL := FractionalIdeal.dual ℤ_[l] ℚ_[l] 1
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ_[l] ℚ_[l] one_ne_zero
  haveI hP : (D : Submodule O LL).IsPrincipal := FractionalIdeal.isPrincipal D
  set c : LL := Submodule.IsPrincipal.generator (D : Submodule O LL) with hc
  have hDc : (D : Submodule O LL) = Submodule.span O {c} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hD0
    apply FractionalIdeal.coeToSubmodule_injective
    show (D : Submodule O LL) = ((0 : FractionalIdeal (nonZeroDivisors O) LL) : Submodule O LL)
    rw [hDc, h, FractionalIdeal.coe_zero]
    exact Submodule.span_singleton_eq_bot.2 rfl
  refine ⟨(Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c), fun a => ?_⟩
  have key : (∀ b : O, ∃ u : ℤ_[l], (Algebra.trace ℚ_[l] LL) (c * (a * algebraMap O LL b)) = (u : ℚ_[l]))
      ↔ c * a ∈ D := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors O) LL) ≠ 0)]
    constructor
    · intro h y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨u, hu⟩ := h b
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc, hu]
      rfl
    · intro h b
      obtain ⟨u, hu⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc] at hu
      rw [← hu]
      rfl
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, ← FractionalIdeal.mem_coe, hDc, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, mul_comm] at hz
    exact mul_left_cancel₀ hc0 hz
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩

end GlobalTheory.GoodCoeff
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.coefficient_ring_integers_compact_adic_properties : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first | exact @GlobalTheory.GoodCoeff.good_coeff_integers | exact GlobalTheory.GoodCoeff.good_coeff_integers | (intros; apply GlobalTheory.GoodCoeff.good_coeff_integers <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_finset_pow_torsion : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  intro l _ LL _ _ _ O _ _ hG k
  classical
  haveI hfin : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ k}) :=
    (good_coeff_integers l LL O hG).2.2.1 k
  have hl : (l : LL) ≠ 0 := by
    have := (algebraMap ℚ_[l] LL).injective.ne
      (show (l : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using this
  have hlk : (l : LL) ^ k ≠ 0 := pow_ne_zero _ hl
  let f : O ⧸ Ideal.span {((l : ℕ) : O) ^ k} → LL ⧸ LinearMap.range (Algebra.linearMap O LL) :=
    fun q => Submodule.Quotient.mk (((l : LL) ^ k)⁻¹ * algebraMap O LL q.out)
  refine ⟨(Set.finite_range f).toFinset, fun e he => ?_⟩
  rw [Set.Finite.mem_toFinset]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at he
  obtain ⟨a, ha⟩ := he
  rw [Algebra.linearMap_apply, Algebra.smul_def, map_pow, map_natCast] at ha
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have h1 : (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : O) ^ k}) a).out - a ∈
      Ideal.span {((l : ℕ) : O) ^ k} :=
    Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have hc' := congrArg (algebraMap O LL) hc
  rw [map_mul, map_pow, map_natCast, RingHom.map_sub, ha] at hc'
  refine (Submodule.Quotient.eq _).2 ⟨c, ?_⟩
  rw [Algebra.linearMap_apply]
  field_simp
  linear_combination hc'

end GlobalTheory.GoodCoeff
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  first | exact @GlobalTheory.LatTorsFinite.finite_ker_pow_smul | exact GlobalTheory.LatTorsFinite.finite_ker_pow_smul | (intros; apply GlobalTheory.LatTorsFinite.finite_ker_pow_smul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

private lemma pairing_smul_left' {p : ℕ} [NeZero p] {M M' : Type} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod p) M] (β : M →+ M' →+ ZMod p) (a : ZMod p) (v : M) (m' : M') :
    β (a • v) m' = a * β v m' := by
  have h : a • v = a.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val v
  rw [h, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem exists_sum_mul_of_finite_torsion (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  refine ⟨_, hS.toFinset.biUnion (fun m => (b.repr m).support),
    fun i => (b.coord i).toAddMonoidHom, fun i => β (b i), ?_⟩
  intro m hm m'
  have hsub : (b.repr m).support ⊆ hS.toFinset.biUnion (fun m => (b.repr m).support) :=
    Finset.subset_biUnion_of_mem (fun m => (b.repr m).support) (hS.mem_toFinset.2 hm)
  have hm' : m = ∑ i ∈ (b.repr m).support, b.repr m i • b i := by
    conv_lhs => rw [← b.linearCombination_repr m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hm']

  rw [map_sum, AddMonoidHom.finsetSum_apply]
  simp only [pairing_smul_left', LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
  refine Finset.sum_subset hsub ?_
  intro k _ hk
  have hz : b.repr m k = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.2 h)
  rw [hz, zero_mul]

theorem inv_cup_pairing_of_inv_cup_characters : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  intro Γ _ _ _ _ l _ μ hμ e I u γ φ hchar M M' _ _ _ _ _ _ hl β x y hxc hyc hxa hya hyI w hw
  classical
  haveI hp : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod (l ^ 1)) M :=
    AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
  have hfin : (Set.range x).Finite := (isCompact_range hxc).finite_of_discrete
  obtain ⟨ι, s, c, d, hdec⟩ :=
    exists_sum_mul_of_finite_torsion (l ^ 1) M M' β (Set.range x) hfin
  have hmem : ∀ k, (fun q : Γ × Γ => c k (x q.1) * d k (y q.2)) ∈ Z2 μ := by
    intro k
    rw [mem_cocycles2]
    refine ⟨?_, ?_⟩
    · exact ((continuous_of_discreteTopology.comp hxc).comp continuous_fst).mul
        ((continuous_of_discreteTopology.comp hyc).comp continuous_snd)
    · intro g h k'
      simp only [hμ, hxa, hya, map_add (f := _)]
      ring
  let W : ι → Z2 μ := fun k => ⟨_, hmem k⟩
  have hWsum : w = ∑ k ∈ s, W k := by
    apply Subtype.ext
    funext q
    rcases q with ⟨g, h⟩
    rw [Submodule.coe_sum, Finset.sum_apply, hw g h]
    exact hdec (x g) ⟨g, rfl⟩ (y h)
  have hW : ∀ k, e (Submodule.Quotient.mk (W k)) = u * (c k (x γ) * d k (y φ)) := fun k =>
    hchar (fun g => c k (x g)) (fun g => d k (y g))
      (continuous_of_discreteTopology.comp hxc) (continuous_of_discreteTopology.comp hyc)
      (fun g h => by simp only [hxa, map_add (f := _)]) (fun g h => by simp only [hya, map_add (f := _)])
      (fun g hg => by simp only [hyI g hg, map_zero]) (W k) (fun g h => rfl)
  have hq : (Submodule.Quotient.mk (∑ k ∈ s, W k) : H2 μ) =
      ∑ k ∈ s, (Submodule.Quotient.mk (W k) : H2 μ) :=
    map_sum (Submodule.mkQ _) W s

  rw [hWsum, hq, map_sum]
  simp only [hW]
  rw [← Finset.mul_sum, ← hdec (x γ) ⟨γ, rfl⟩ (y φ)]

end GlobalTheory
end

section

open Polynomial

theorem GlobalTheory.onto_OC_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  intro l hl E N a hNE ha haN b hb
  set f : ℂ_[l][X] := (∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k)) - C b with hf
  have hl1 : 1 < l := hl.out.one_lt
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl.out.two_le
  have hcoeff : ∀ j, f.coeff j = (∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0) - (if j = 0 then b else 0) := by
    intro j
    simp only [hf, coeff_sub, finsetSum_coeff, coeff_monomial, coeff_C, Finsupp.single_apply]
  have hcN : f.coeff (l ^ N) = a N := by
    rw [hcoeff]
    have h0 : l ^ N ≠ 0 := pow_ne_zero _ (by omega)
    rw [if_neg h0, sub_zero, Finset.sum_eq_single N]
    · simp
    · intro k _ hk; rw [if_neg]; intro h; exact hk (hinj h)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hbound : ∀ j, ‖f.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro k hk
      split_ifs
      · exact ha k (by have := Finset.mem_range.1 hk; omega)
      · simp
    · rw [norm_neg]; split_ifs
      · exact hb
      · simp
  have hne : f.coeff (l ^ N) ≠ 0 := by
    rw [hcN]; intro h; rw [h, norm_zero] at haN; exact zero_ne_one haN
  have key := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] f 1 (l ^ N) zero_lt_one hne).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcN, haN]; exact hbound j)
  have hpos : 0 < Multiset.card (f.roots.filter fun z => ‖z‖ ≤ 1) :=
    lt_of_lt_of_le (pow_pos (by omega) N) key
  obtain ⟨W, hW⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hW
  obtain ⟨hr, hWn⟩ := hW
  refine ⟨W, hWn, ?_⟩
  have hroot := (mem_roots'.1 hr).2
  rw [IsRoot, hf, eval_sub, eval_finsetSum, eval_C] at hroot
  simp only [eval_monomial] at hroot
  exact sub_eq_zero.1 hroot
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  first | exact @GlobalTheory.IrrQuot.main | exact GlobalTheory.IrrQuot.main | (intros; apply GlobalTheory.IrrQuot.main <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧ f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y → y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  first | exact @GlobalTheory.IsoIdem.isoIdem | exact GlobalTheory.IsoIdem.isoIdem | (intros; apply GlobalTheory.IsoIdem.isoIdem <;> assumption)
end

section

open ValuativeRel

theorem _root_.GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  first | exact @GlobalTheory.neg_one_mem_norm_of_valuation_eq | exact GlobalTheory.neg_one_mem_norm_of_valuation_eq | (intros; apply GlobalTheory.neg_one_mem_norm_of_valuation_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_primitiveRoot_sub_one | exact GlobalTheory.Cyc.norm_primitiveRoot_sub_one | (intros; apply GlobalTheory.Cyc.norm_primitiveRoot_sub_one <;> assumption)
end
