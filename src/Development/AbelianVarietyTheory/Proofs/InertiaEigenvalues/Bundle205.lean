module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle035
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLattice
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.ZMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle195
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TraceConj

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

def colRep (ρ : Γ →* GL (Fin a) k) : Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem colRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := rfl

theorem colRep_semisimple (ρ : Γ →* GL (Fin a) k) (h : Formalism.MainNotions.N.IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem conj_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (a : ℕ)
    (ρ ρ' : Γ →* GL (Fin a) k), Formalism.MainNotions.N.IsSSRep ρ → Formalism.MainNotions.N.IsSSRep ρ' →
    (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace =
      ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace) →
    ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹ := by
  intro Γ k _ _ _ a ρ ρ' hρ hρ' ht
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq (colRep ρ) (colRep ρ')
    (colRep_semisimple ρ hρ) (colRep_semisimple ρ' hρ') fun g => by
      rw [colRep_apply, colRep_apply, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, ht]
  let h : GL (Fin a) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨h, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (h : Matrix (Fin a) (Fin a) k) = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  rw [hh]
  exact LinearMap.ext fun v => (he g v).symm

end GlobalTheory.TraceConj

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  first | exact @GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | exact GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | (intros; apply GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.PointsKey.key | exact GlobalTheory.PointsKey.key | (intros; apply GlobalTheory.PointsKey.key <;> assumption)
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory

theorem exists_lt_commutator_mem_of_ne_top {G : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    (K : Subgroup G) (hK : K ≠ ⊤) :
    ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  have hlt : K < Subgroup.normalizer (K : Set G) :=
    Group.normalizerCondition_of_isNilpotent K (lt_top_iff_ne_top.mpr hK)
  obtain ⟨x, hxN, hxK⟩ := SetLike.exists_of_lt hlt
  have hconj : ∀ i : ℤ, ∀ k ∈ K, x ^ i * k * (x ^ i)⁻¹ ∈ K := fun i k hk =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hxN i) k).mp hk
  let A : Subgroup G :=
    { carrier := {g | ∃ k ∈ K, ∃ i : ℤ, g = k * x ^ i}
      one_mem' := ⟨1, K.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, i, rfl⟩ ⟨k', hk', j, rfl⟩
        exact ⟨k * (x ^ i * k' * (x ^ i)⁻¹), K.mul_mem hk (hconj i k' hk'), i + j, by
          rw [zpow_add]; group⟩
      inv_mem' := by
        rintro _ ⟨k, hk, i, rfl⟩
        exact ⟨x ^ (-i) * k⁻¹ * (x ^ (-i))⁻¹, hconj (-i) _ (K.inv_mem hk), -i, by group⟩ }
  have hKA : K ≤ A := fun k hk => (⟨k, hk, 0, by simp⟩ : ∃ k' ∈ K, ∃ i : ℤ, k = k' * x ^ i)
  have hxA : x ∈ A := (⟨1, K.one_mem, 1, by simp⟩ : ∃ k ∈ K, ∃ i : ℤ, x = k * x ^ i)
  refine ⟨A, SetLike.lt_iff_le_and_exists.mpr ⟨hKA, x, hxA, hxK⟩, ?_⟩
  rintro _ ⟨k, hk, i, rfl⟩ _ ⟨k', hk', j, rfl⟩
  have h : k * x ^ i * (k' * x ^ j) * (k * x ^ i)⁻¹ * (k' * x ^ j)⁻¹ =
      k * (x ^ i * k' * (x ^ i)⁻¹) * (x ^ j * k⁻¹ * (x ^ j)⁻¹) * k'⁻¹ := by group
  rw [h]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk (hconj i k' hk')) (hconj j _ (K.inv_mem hk)))
    (K.inv_mem hk')

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_totallyPositive_approx_at_finite_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ), ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  first | exact @GlobalTheory.FinPlaceApproxPos.approxpos_target | exact GlobalTheory.FinPlaceApproxPos.approxpos_target | (intros; apply GlobalTheory.FinPlaceApproxPos.approxpos_target <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  first | exact @GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | exact GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | (intros; apply GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary <;> assumption)
end

section

open Polynomial IsLocalRing

theorem _root_.GlobalTheory.T.involution_residue_pow_and_roots_of_unity : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ), Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) → (∃ x, residue S (τ x) ≠ residue S x) → (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  first | exact @GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | exact GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | (intros; apply GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.inv_cup_pairing_of_inv_cup_characters_alt : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  first | exact @GlobalTheory.inv_cup_pairing_of_inv_cup_characters | exact GlobalTheory.inv_cup_pairing_of_inv_cup_characters | (intros; apply GlobalTheory.inv_cup_pairing_of_inv_cup_characters <;> assumption)
end
