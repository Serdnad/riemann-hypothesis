module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.StatementLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle256
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Localization.Finiteness
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GaloisTransport

section Generic

variable {R G' G Q M : Type} [CommRing R] [Group G'] [TopologicalSpace G'] [Group G]
  [TopologicalSpace G] [AddCommGroup Q] [Module R Q] {N : ℕ} [AddCommGroup M] [Module (ZMod N) M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem card_H1_transport (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (act : G' → Q → Q) (Z B : Submodule R (G' → Q))
    (hZ : ∀ c, c ∈ Z ↔ IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + act g (c h))
    (hB : ∀ c, c ∈ B ↔ ∃ t, ∀ g, c g = act g t - t)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card (↥Z ⧸ B.comap Z.subtype) = Nat.card (ReciprocityTheory.Gal.H1 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  let F : (G' → Q) → (G → M) := fun c g => e (c (φ.symm g))
  have hF : ∀ c g, F c (φ g) = e (c g) := fun c g => by simp only [F, MulEquiv.symm_apply_apply]
  have hFB : ∀ c, c ∈ B ↔ F c ∈ ReciprocityTheory.Gal.B1 rho := by
    intro c
    rw [hB, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, fun g => ?_⟩
      simp only [F, ht, map_sub, hr]
    · rintro ⟨m, hm⟩
      refine ⟨e.symm m, fun g => ?_⟩
      have h1 := hm (φ g)
      rw [hF] at h1
      apply e.injective
      rw [h1, map_sub, ← hr', e.apply_symm_apply]
  have hZf : ∀ c : ↥Z, F c.1 ∈ ReciprocityTheory.Gal.Z1 rho := fun c => by
    obtain ⟨hc1, hc2⟩ := (hZ c.1).1 c.2
    refine ⟨((hc1.comp_continuous hφ.2).comp e).continuous, fun g h => ?_⟩
    simp only [F, map_mul, hc2, map_add (f := _), hr]
  have hZb : ∀ f : ↥(ReciprocityTheory.Gal.Z1 rho), (fun g => e.symm (f.1 (φ g))) ∈ Z := fun f => by
    obtain ⟨hf1, hf2⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 f.2
    refine (hZ _).2 ⟨((IsLocallyConstant.iff_continuous _).2 (hf1.comp hφ.1)).comp e.symm,
      fun g h => ?_⟩
    apply e.injective
    have h2 := hr' g (e.symm (f.1 (φ h)))
    rw [e.apply_symm_apply] at h2
    simp only [map_mul, hf2, map_add (f := _), AddEquiv.apply_symm_apply, h2]
  let E : ↥Z ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨F c.1, hZf c⟩
      invFun := fun f => ⟨fun g => e.symm (f.1 (φ g)), hZb f⟩
      left_inv := fun c => Subtype.ext (funext fun g => by
        show e.symm (F c.1 (φ g)) = c.1 g
        rw [hF, e.symm_apply_apply])
      right_inv := fun f => Subtype.ext (funext fun g => by
        show e (e.symm (f.1 (φ (φ.symm g)))) = f.1 g
        rw [e.apply_symm_apply, MulEquiv.apply_symm_apply]) }
  have hEsub : ∀ a b : ↥Z, ((E a - E b : ↥(ReciprocityTheory.Gal.Z1 rho)) : G → M) = F ((a - b : ↥Z) : G' → Q) :=
    fun a b => funext fun g => by
      show e (a.1 (φ.symm g)) - e (b.1 (φ.symm g)) = e (a.1 (φ.symm g) - b.1 (φ.symm g))
      rw [map_sub]
  refine Nat.card_congr (Quotient.congr E fun a b => ?_)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hEsub, hFB]

theorem card_H0_transport (φ : G' ≃* G) (act : G' → Q → Q)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card {x : Q // ∀ g, act g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by rw [hr, x.2]⟩
      invFun := fun m => ⟨e.symm m.1, fun g => by
        apply e.injective
        rw [← hr', e.apply_symm_apply]
        exact (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2 (φ g)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

end Generic

theorem card_H1_H0_transport : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  intro l _ K LL _ _ _ O _ _ A LA I hI N M _ _ _ _ e rho hrho
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hφ := GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1
  refine ⟨card_H1_transport _ hφ (fun g x => actQ LA I hI g x) (quotientCocycles LA I hI) (BQ LA I hI)
    (fun c => Iff.rfl) (fun c => ?_) e rho hrho,
    card_H0_transport _ (fun g x => actQ LA I hI g x) e rho hrho⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g => (congrFun ht g).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun g => (ht g).symm⟩

end GlobalTheory.GaloisTransport
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (x : A.V), ∃ n : ℕ, ((l : ℕ) : O) ^ n • x ∈ LA.T := by
  intro l _ K LL _ _ _ O _ _ hG A LA x
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  haveI := IsModuleTopology.toContinuousSMul LL A.V
  have h1 : Filter.Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have h2 : Filter.Tendsto (fun n : ℕ => algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x) Filter.atTop (nhds 0) := by
    have := ((GlobalTheory.GoodCoeff.continuous_algebraMap_padic (l := l) (LL := LL)).tendsto 0).comp h1
    rw [map_zero] at this
    simpa using this.smul_const x
  have h3 : ∀ n : ℕ, ((l : ℕ) : O) ^ n • x = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x := by
    intro n
    rw [← algebraMap_smul LL, map_pow, map_pow, map_natCast, map_natCast]
  obtain ⟨n, hn⟩ := (h2.eventually (hT.mem_nhds LA.T.zero_mem)).exists
  exact ⟨n, by rw [h3]; exact hn⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem not_isUnit_l : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ¬ IsUnit ((l : ℕ) : O) := by
  intro l _ LL _ _ _ O _ _ hG hu
  obtain ⟨u, hu⟩ := hu
  have hint := ((GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).1 (algebraMap O LL (↑u⁻¹ : O))).1 ⟨_, rfl⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hx : algebraMap O LL (↑u⁻¹ : O) = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by
    have h1 : algebraMap O LL (↑u⁻¹ : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap O LL (u : O) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by
      rw [hu, map_natCast, map_natCast]
    rw [h2] at h1
    calc algebraMap O LL (↑u⁻¹ : O)
        = algebraMap O LL (↑u⁻¹ : O) * (algebraMap ℚ_[l] LL (l : ℚ_[l]) * algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹)) := by
          rw [← map_mul, mul_inv_cancel₀ hl0, map_one, mul_one]
      _ = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by rw [← mul_assoc, h1, one_mul]
  rw [hx] at hint
  obtain ⟨p, hpm, hp⟩ := hint
  have hp' : Polynomial.eval₂ (algebraMap ℤ_[l] ℚ_[l]) ((l : ℚ_[l])⁻¹) p = 0 := by
    apply (algebraMap ℚ_[l] LL).injective
    rw [map_zero, Polynomial.hom_eval₂]
    exact hp
  have hI : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have h1 : ‖(z : ℚ_[l])‖ ≤ 1 := PadicInt.norm_le_one z
  have h3 : algebraMap ℤ_[l] ℚ_[l] z = (z : ℚ_[l]) := rfl
  rw [← h3, hz, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem finite_finrank_of_localizes : ∀ (O LL M N : Type) [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup M] [Module O M] [Module.Finite O M] [AddCommGroup N] [Module LL N] [Module O N] [IsScalarTower O LL N] (f : M →ₗ[O] N) (t : O), t ≠ 0 → (∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) → (∀ x : M, f x = 0 → ∃ n : ℕ, t ^ n • x = 0) → Module.Finite LL N ∧ finrank LL N = finrank O M := by
  intro O LL M N _ _ _ _ _ _ _ _ _ _ _ _ f t ht hs hk
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors O := fun n => pow_mem (mem_nonZeroDivisors_of_ne_zero ht) n
  haveI : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        have ha : algebraMap O LL (s : O) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (nonZeroDivisors.ne_zero s.2)
        have he : ∀ y : N, (algebraMap O (Module.End O N) (s : O)) y = algebraMap O LL (s : O) • y := fun y => by
          rw [Module.algebraMap_end_apply, algebraMap_smul]
        refine ⟨fun y z h => ?_, fun y => ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩⟩
        · rw [he, he] at h
          exact smul_right_injective N ha h
        · rw [he, smul_smul, mul_inv_cancel₀ ha, one_smul]
      surj := by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        exact ⟨(x, ⟨t ^ n, htn n⟩), hx.symm⟩
      exists_of_eq := by
        intro x₁ x₂ h
        obtain ⟨n, hn⟩ := hk (x₁ - x₂) (by rw [map_sub, h, sub_self])
        exact ⟨⟨t ^ n, htn n⟩, by rw [Submonoid.smul_def]; rw [smul_sub, sub_eq_zero] at hn; exact hn⟩ }
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) f, ?_⟩
  rw [IsLocalization.finrank_eq LL (nonZeroDivisors O) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_B1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ latticeCocycles LA, c ∈ B1 A.ρ → ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCoboundaries LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c _ hc
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨n, hn⟩ := pow_smul_mem_lattice l K LL O hG A LA x
  exact ⟨n, _, hn, by rw [LinearMap.map_smul_of_tower]; rfl⟩

theorem pow_smul_mem_Z1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ continuousCocycles A.ρ, ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCocycles LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c hc
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  have hG' := hG
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG'
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  let U : ℕ → Set A.V := fun n => (fun v : A.V => ((l : ℕ) : O) ^ n • v) ⁻¹' (LA.T : Set A.V)
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    refine hT.preimage ?_
    have : (fun v : A.V => ((l : ℕ) : O) ^ n • v) = fun v : A.V => algebraMap O LL (((l : ℕ) : O) ^ n) • v :=
      funext fun v => (algebraMap_smul LL _ v).symm
    rw [this]
    exact continuous_const_smul _
  have hUm : Monotone U := by
    refine monotone_nat_of_le_succ fun n v hv => ?_
    show ((l : ℕ) : O) ^ (n + 1) • v ∈ LA.T
    rw [pow_succ', mul_smul]
    exact LA.T.smul_mem _ hv
  have hcov : Set.range c ⊆ ⋃ n, U n := fun v _ => Set.mem_iUnion.2 (pow_smul_mem_lattice l K LL O hG A LA v)
  obtain ⟨n, hn⟩ := (isCompact_range hc.1).elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨n, ⟨(continuousCocycles A.ρ).smul_of_tower_mem _ hc, fun g _ => hn ⟨g, rfl⟩⟩⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank
section
variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A : GRep ↥(GK K) ℚ_[l] LL O} (LA : Lattice (O := O) A.ρ)

def incl : ↥(latticeCocycles LA) →ₗ[O] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def toH1V : LatticeCohomology LA →ₗ[O] H1V A.ρ :=
  Submodule.liftQ ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype)
    ((((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ.restrictScalars O).comp (incl LA)) (by
      intro c hc
      obtain ⟨x, -, hx⟩ := hc
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, hx⟩)

theorem toH1V_mk (c : ↥(latticeCocycles LA)) :
    toH1V LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incl LA c) := rfl
end
end GlobalTheory.H1Rank
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.RedLocConst

theorem mem_span_smul_top' {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem redT_mem_Z1Q : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL (ϖ ^ r) with hcdef
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hc).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = ϖ ^ r • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = ϖ ^ r • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

end GlobalTheory.RedLocConst
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI h K
  exact GlobalTheory.DeRhamSymbol.exists_symbol l P AI h K
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_torsionCocycle_finite_level_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  first | exact @GlobalTheory.TorsionLevel.exists_cocycle_level | exact GlobalTheory.TorsionLevel.exists_cocycle_level | (intros; apply GlobalTheory.TorsionLevel.exists_cocycle_level <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  first | exact @GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | exact GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | (intros; apply GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  first | exact @GlobalTheory.HWL.exists_kappa | exact GlobalTheory.HWL.exists_kappa | (intros; apply GlobalTheory.HWL.exists_kappa <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem _root_.GlobalTheory.T.deRham_fil_quotient_xi_power_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (J : ThetaL P AI) (n : ℕ), (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧ (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧ (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧ J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1)  := by
  first | exact @GlobalTheory.BdRQuot.fil_quotient | exact GlobalTheory.BdRQuot.fil_quotient | (intros; apply GlobalTheory.BdRQuot.fil_quotient <;> assumption)
end

section

open GlobalTheory.UnitDiscAlg

namespace GlobalTheory

theorem norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  intro E _ _ n x hx
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, x (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, norm_neg]; exact hp

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.phi_injective_quotient_H2 : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G], PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.NatQuot.phi_quot_pow_injective | exact GlobalTheory.NatQuot.phi_quot_pow_injective | (intros; apply GlobalTheory.NatQuot.phi_quot_pow_injective <;> assumption)
end
