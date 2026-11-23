module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruentOneMatricesTransitiveNearHermitian
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.NonGenericCompare

section Place
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [StarRing E]
variable (o : Type) [CommRing o] [Algebra o F] [Algebra o E]

variable {o}

end Place

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [StarRing E]
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Algebra o F]
  [IsFractionRing o F] [Algebra o E] [IsScalarTower o F E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

namespace Match
variable {P : LocNG.FPair H r} {S : Frames M.L r k}
variable (c : Coord P S)

end Match

end GlobalTheory.NonGenericCompare
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), Stable G X → Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → orbSum G X (fun x => N (f x)) = orbSum G' Y N := by
  first | exact @GlobalTheory.Mass.OrbTransport.main | exact GlobalTheory.Mass.OrbTransport.main | (intros; apply GlobalTheory.Mass.OrbTransport.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.lattice_quotient_gens_and_intermediate_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  first | exact @GlobalTheory.Mass.LatticeGens.gens_and_count | exact GlobalTheory.Mass.LatticeGens.gens_and_count | (intros; apply GlobalTheory.Mass.LatticeGens.gens_and_count <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  first | exact @GlobalTheory.HL.cont_independent_pos | exact GlobalTheory.HL.cont_independent_pos | (intros; apply GlobalTheory.HL.cont_independent_pos <;> assumption)
end

section

open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise

theorem _root_.GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  first | exact @GlobalTheory.HL.unistab_iff | exact GlobalTheory.HL.unistab_iff | (intros; apply GlobalTheory.HL.unistab_iff <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitStabilizerMass_prod_eq_mul : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β), (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y → (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) → orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  first | exact @GlobalTheory.Mass.ProdMass.orbMass_prod | exact GlobalTheory.Mass.ProdMass.orbMass_prod | (intros; apply GlobalTheory.Mass.ProdMass.orbMass_prod <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_restrict_slice : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  first | exact @GlobalTheory.Mass.Slice.orbSum_restrict | exact GlobalTheory.Mass.Slice.orbSum_restrict | (intros; apply GlobalTheory.Mass.Slice.orbSum_restrict <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  first | exact @GlobalTheory.LatComm.stab_commensurable | exact GlobalTheory.LatComm.stab_commensurable | (intros; apply GlobalTheory.LatComm.stab_commensurable <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.relative_lattice_volume_of_det_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  first | exact @GlobalTheory.HL.LatDet.relVol_map | exact GlobalTheory.HL.LatDet.relVol_map | (intros; apply GlobalTheory.HL.LatDet.relVol_map <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unipotent_stabilizes_some_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  first | exact @GlobalTheory.HL.exists_isLat_stabL_of_unipotent | exact GlobalTheory.HL.exists_isLat_stabL_of_unipotent | (intros; apply GlobalTheory.HL.exists_isLat_stabL_of_unipotent <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.congruence_subgroup_lattice_stabilizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by
  first | exact @GlobalTheory.HL.congruence_subgroup_facts | exact GlobalTheory.HL.congruence_subgroup_facts | (intros; apply GlobalTheory.HL.congruence_subgroup_facts <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ i : ℕ, 1 ≤ i → ∃ j : ℕ, ∀ X ∈ horb L ϖ Γ i, ∀ D : Matrix (Fin m) (Fin m) E, IsHerm L D → IsIntM L D → ∃ A ∈ congK L ϖ m i, X + algebraMap F E ((ϖ : F) ^ j) • D = cT L A * X * A := by
  first | exact @GlobalTheory.CongTrans.congK_transitive | exact GlobalTheory.CongTrans.congK_transitive | (intros; apply GlobalTheory.CongTrans.congK_transitive <;> assumption)
end
