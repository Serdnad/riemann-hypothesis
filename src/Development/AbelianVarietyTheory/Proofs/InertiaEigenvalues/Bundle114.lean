module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle074
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPrimePowAutomorphismInertialAtPrime
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
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
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Trace.Basic
public import ReciprocityTheory.DualLattices.Bundle004
public import ReciprocityTheory.DualLattices.Bundle005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001

@[expose] public section

section

open NumberField Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem exists_digits_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (ϖ : V) (hϖ : Irreducible ϖ) (s : ResidueField V → V) (hs : ∀ r, residue V (s r) = r) :
    ∀ (n : ℕ) (x : V), ∃ f : Fin n → ResidueField V,
      x - ∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) ∈ maximalIdeal V ^ n := by
  intro n
  induction n with
  | zero => intro x; exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨f, hf⟩ := ih x
    have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have hf' := hf
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hf'
    obtain ⟨y, hy⟩ := hf'
    refine ⟨Fin.snoc f (residue V y), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    have hxy : x - (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) + s (residue V y) * ϖ ^ n) =
        ϖ ^ n * (y - s (residue V y)) := by
      rw [← sub_sub, hy]; ring
    rw [hxy, pow_succ]
    have hϖm : ϖ ∈ maximalIdeal V := (mem_maximalIdeal _).2 hϖ.not_isUnit
    have hym : y - s (residue V y) ∈ maximalIdeal V := by
      rw [← residue_eq_zero_iff, map_sub, hs, sub_self]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖm n) hym

theorem countable_quotient_pow_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let s : ResidueField V → V := Function.surjInv (residue_surjective (R := V))
  have hs : ∀ r, residue V (s r) = r := Function.surjInv_eq _
  have hsurj : Function.Surjective (fun f : Fin n → ResidueField V =>
      Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨f, hf⟩ := exists_digits_of_dvr V ϖ hϖ s hs n x
    exact ⟨f, (Ideal.Quotient.eq.2 hf).symm⟩
  exact hsurj.countable

theorem mk_le_continuum_of_countable_residueField (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_fractionField_of_finite :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V),
      Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) →
      ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T T' g _ hfin hc io
  have hV : #T.V ≤ 𝔠 := mk_le_continuum_of_countable_residueField T.V
  letI : Algebra T.V T'.V := g.toAlgebra
  haveI : Module.Finite T.V T'.V := hfin
  obtain ⟨d, φ, hφ⟩ := Module.Finite.exists_fin' T.V T'.V
  have hV' : #T'.V ≤ 𝔠 := by
    refine (mk_le_of_surjective hφ).trans ?_
    rw [mk_arrow, mk_fin, lift_id, lift_natCast]
    refine (power_le_power_right hV).trans ?_
    exact power_nat_le aleph0_le_continuum
  have hF : #T'.Fr ≤ 𝔠 := by
    rw [show #T'.Fr = #T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact hV'
  exact @exists_embedding_of_mk_le_continuum K T'.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

section

namespace GlobalTheory.IntegralPowerMultiple

theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

theorem _root_.GlobalTheory.T.cyclotomicPrimePow_automorphism_inertial_at_prime : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) → ∀ τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ}), (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧ (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  first | exact @GlobalTheory.CycInertial.main | exact GlobalTheory.CycInertial.main | (intros; apply GlobalTheory.CycInertial.main <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocalTraceNonzero

theorem isUnit_of_cast_ne_zero (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) (x : ZMod (l ^ b))
    (hx : ZMod.castHom (dvd_pow_self l hb) (ZMod l) x ≠ 0) : IsUnit x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff] at hx
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hx))

theorem henselian_of_finite (A : Type) [CommRing A] [Finite A] [IsLocalRing A] :
    HenselianLocalRing A := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

theorem exists_trace_ne_zero_adjoinRoot (l : ℕ) [Fact l.Prime] (p : (ZMod l)[X]) (hp : Irreducible p) :
    ∃ z : AdjoinRoot p, Algebra.trace (ZMod l) (AdjoinRoot p) z ≠ 0 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : FiniteDimensional (ZMod l) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI : Algebra.IsSeparable (ZMod l) (AdjoinRoot p) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (ZMod l) (AdjoinRoot p) 1
  exact ⟨z, by rw [hz]; exact one_ne_zero⟩

theorem exists_trace_ne_zero : ∀ (l b e : ℕ) [Fact l.Prime] (B : Type) [CommRing B] [Finite B] [Algebra (ZMod (l ^ b)) B] (π : B), 0 < e → (∀ x : B, ¬ IsUnit x ↔ π ∣ x) → Ideal.span {((l : ℕ) : B)} = Ideal.span {π ^ e} → Nat.card B = Nat.card (B ⧸ Ideal.span {π}) ^ (b * e) → ¬ l ^ b ∣ e → ∃ c : B, Algebra.trace (ZMod (l ^ b)) B c ≠ 0 := by
  intro l b e _ B _ _ _ π he hunit hspan hcard hdvd
  have hb : b ≠ 0 := by rintro rfl; exact hdvd (by simp)
  have hl := (Fact.out : l.Prime)
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (hunit 0).2 (dvd_zero π) (by rw [Subsingleton.elim (0 : B) 1]; exact isUnit_one)
  have hnon : ∀ x : B, x ∈ nonunits B ↔ π ∣ x := fun x => hunit x
  haveI : IsLocalRing B := IsLocalRing.of_nonunits_add
    (fun a c ha hc => (hnon _).2 (dvd_add ((hnon a).1 ha) ((hnon c).1 hc)))
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {π} := by
    ext x; rw [IsLocalRing.mem_maximalIdeal, hnon, Ideal.mem_span_singleton]
  set K := IsLocalRing.ResidueField B
  have hlmax : ((l : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [hmax, Ideal.mem_span_singleton]
    have : ((l : ℕ) : B) ∈ Ideal.span {π ^ e} := hspan ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at this
    exact (dvd_pow_self π he.ne').trans this
  haveI : CharP K l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue B),
      IsLocalRing.residue_eq_zero_iff]
    exact hlmax
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  haveI : Finite K := Finite.of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨a, p, hpm, hpirr, hpa, hpa', hgen, hcardK⟩ := GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree l K
  set g : ZMod (l ^ b) →+* ZMod l := ZMod.castHom (dvd_pow_self l hb) (ZMod l) with hg
  have hgs : Function.Surjective g := ZMod.ringHom_surjective g
  obtain ⟨h, hhp, hdeg, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hgs p)) hpm
  have hcomp : (algebraMap B K).comp (algebraMap (ZMod (l ^ b)) B) =
      (algebraMap (ZMod l) K).comp g := RingHom.ext_zmod _ _
  have key : ∀ q : (ZMod (l ^ b))[X],
      aeval a (q.map (algebraMap (ZMod (l ^ b)) B)) = aeval a (q.map g) := by
    intro q
    simp only [aeval_def, eval₂_map, hcomp]
  haveI : HenselianLocalRing B := henselian_of_finite B
  have H2 := ((HenselianLocalRing.TFAE B).out 1 2).mp ‹_›
  obtain ⟨ω, hω, hωa⟩ := H2 (h.map (algebraMap _ B)) (hmon.map _) a
    (by rw [key, hhp]; exact hpa)
    (by rw [derivative_map, key, ← derivative_map, hhp]; exact hpa')
  have hω' : eval₂ (algebraMap (ZMod (l ^ b)) B) ω h = 0 := by
    rw [← eval_map]; exact hω

  set C := AdjoinRoot h
  let φ : C →+* B := AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω'
  have hsurj : ∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π} := by
    intro x
    obtain ⟨q, hq⟩ := hgen (IsLocalRing.residue B x)
    obtain ⟨q', rfl⟩ := map_surjective g hgs q
    refine ⟨AdjoinRoot.mk h q', ?_⟩
    rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hq]
    show _ = IsLocalRing.residue B (AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω' (AdjoinRoot.mk h q'))
    rw [AdjoinRoot.lift_mk, hom_eval₂, hωa, ← key, aeval_def, eval₂_map]
    rfl
  have hlb : ((l : ℕ) : B) ^ b = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (l ^ b)) B), ZMod.natCast_self, map_zero]
  have hpe : π ^ e ∈ Ideal.span {φ (l : C)} := by
    rw [map_natCast, hspan]; exact Ideal.mem_span_singleton_self _
  have hE := GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent C B φ π (l : C) e b hsurj hpe (by rw [map_natCast]; exact hlb)

  letI : Algebra C B := φ.toAlgebra
  have hsmul : ∀ (c : C) (x : B), c • x = φ c * x := fun c x => Algebra.smul_def c x
  let T : (Fin e → C) →ₗ[C] B := Fintype.linearCombination C (fun j : Fin e => π ^ (j : ℕ))
  have hTsurj : Function.Surjective T := by
    intro x
    obtain ⟨c, hc⟩ := hE x
    refine ⟨c, ?_⟩
    rw [Fintype.linearCombination_apply, hc]
    simp only [hsmul]
  let pb := AdjoinRoot.powerBasis' hmon
  have hcardC : Nat.card C = (l ^ b) ^ p.natDegree := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hdeg]
  have hcardB : Nat.card B = Nat.card (Fin e → C) := by
    rw [Nat.card_fun, hcardC, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin, hcard, ← hmax]
    change Nat.card K ^ (b * e) = _
    rw [hcardK, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Module.Finite (ZMod (l ^ b)) C := pb.finite
  haveI : Finite C := Module.finite_of_finite (ZMod (l ^ b))
  have hTbij : Function.Bijective T := hTsurj.bijective_of_nat_card_le hcardB.ge
  let bB : Module.Basis (Fin e) C B := Module.Basis.ofEquivFun (LinearEquiv.ofBijective T hTbij).symm
  haveI : IsScalarTower (ZMod (l ^ b)) C B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have htr : ∀ y : C, Algebra.trace (ZMod (l ^ b)) B (φ y) = (e : ZMod (l ^ b)) * Algebra.trace (ZMod (l ^ b)) C y := by
    intro y
    rw [← Algebra.trace_trace_of_basis pb.basis bB]
    change Algebra.trace (ZMod (l ^ b)) C (Algebra.trace C B (algebraMap C B y)) = _
    rw [Algebra.trace_algebraMap_of_basis bB, map_nsmul, Fintype.card_fin, nsmul_eq_mul]

  have hirr' : Irreducible (h.map g) := hhp ▸ hpirr
  obtain ⟨z, hz⟩ := exists_trace_ne_zero_adjoinRoot l (h.map g) hirr'
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q', rfl⟩ := map_surjective g hgs q
  have hmap : AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h q') =
      AdjoinRoot.mk (h.map g) (q'.map g) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map,
      AdjoinRoot.algebraMap_eq]
  have hu : IsUnit (Algebra.trace (ZMod (l ^ b)) C (AdjoinRoot.mk h q')) := by
    apply isUnit_of_cast_ne_zero l b hb
    rw [← hg, GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map _ _ g h hmon, hmap]; exact hz
  refine ⟨φ (AdjoinRoot.mk h q'), ?_⟩
  rw [htr]
  intro h0
  exact hdvd ((ZMod.natCast_eq_zero_iff _ _).1 (hu.mul_left_eq_zero.1 h0))

end GlobalTheory.LocalTraceNonzero
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.FockIsotypic

variable {σ : Type} [Fintype σ]

def flat (σ : Type) [Fintype σ] : σ ≃ Fin (Fintype.card σ) × Unit :=
  (Fintype.equivFin σ).trans (Equiv.prodPUnit _).symm

def fis (P Q : MvPolynomial σ ℂ) : ℂ :=
  ReciprocityTheory.PGsh.fischer (rename (flat σ) P) (rename (flat σ) Q)

theorem fis_conj (P Q : MvPolynomial σ ℂ) : starRingEnd ℂ (fis P Q) = fis Q P := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  set Q' := rename (flat σ) Q

  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' Q' (P'.support ∪ Q'.support) Finset.subset_union_left,
  ReciprocityTheory.PGsh.fischer_eq_sum Q' P' (P'.support ∪ Q'.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [ReciprocityTheory.PGsh.fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fis_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (fis P P).re := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' P' P'.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, ReciprocityTheory.PGsh.fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fis_self_ne_zero {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : fis P P ≠ 0 :=
  ReciprocityTheory.PGsh.fischer_self_ne_zero _ fun h =>
    hP (rename_injective _ (flat σ).injective (h.trans (map_zero _).symm))

theorem fis_add_right (P Q Q' : MvPolynomial σ ℂ) : fis P (Q + Q') = fis P Q + fis P Q' := by
  unfold fis
  rw [map_add (f := _), ReciprocityTheory.PGsh.fischer_add_right]

theorem fis_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis P (c • Q) = starRingEnd ℂ c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_right]

theorem fis_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis (c • P) Q = c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_left]

@[reducible] def fisCore (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := fis y.1 x.1
  conj_inner_symm x y := fis_conj _ _
  re_inner_nonneg x := fis_self_re_nonneg _
  add_left x y z := fis_add_right _ _ _
  smul_left x y r := fis_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fis_self_ne_zero (fun h' => h (Subtype.ext h')) hx

end GlobalTheory.FockIsotypic

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  first | exact @GlobalTheory.CutOff.exists_cutoff | exact GlobalTheory.CutOff.exists_cutoff | (intros; apply GlobalTheory.CutOff.exists_cutoff <;> assumption)
end

section

namespace GlobalTheory

theorem normalisedPeriod_algebraic_estimate :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t →
      (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z →
      (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) →
      ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  intro E _ _ n _ _ σ r M Mi Z a s t ha hs ht hσ hMMi hr hZ hM hD hrt i j
  set D := Mi - Z with hDdef
  set C := M * Z with hCdef
  have hC1 : C = 1 - M * D := by
    rw [hCdef, hDdef, Matrix.mul_sub, hMMi]; abel
  have hCσ : C.map σ = M.map σ * Z := by
    rw [hCdef, Matrix.map_mul, hZ]
  have hrC : r * C.map σ = C := by rw [hCσ, ← Matrix.mul_assoc, hr]
  have hX : C.map σ - 1 = -((M * D).map σ) := by
    rw [hC1, Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]; abel
  have hkey : σ (-C i j) - (-C i j) - (r - 1) i j = ((r - 1) * (C.map σ - 1)) i j := by
    have h2 : ((r - 1) * (C.map σ - 1)) = C - C.map σ - (r - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hrC, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul]; abel
    rw [h2]
    simp [Matrix.sub_apply, Matrix.map_apply, map_neg]
    ring
  have hMD : ∀ i j, ‖(M * D) i j‖ ≤ a * s :=
    GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n M D a s ha hs hM hD
  have hXb : ∀ i j, ‖(C.map σ - 1) i j‖ ≤ a * s := by
    intro i j
    rw [hX, Matrix.neg_apply, norm_neg, Matrix.map_apply, hσ]
    exact hMD i j
  rw [hkey]
  exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (r - 1) (C.map σ - 1) t (a * s) ht (mul_nonneg ha hs) hrt hXb i j

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ s : Submodule F V, s ≠ ⊤ → μ (s : Set V) = 0 := by
  first | exact @GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | exact GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | (intros; apply GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero <;> assumption)
end
