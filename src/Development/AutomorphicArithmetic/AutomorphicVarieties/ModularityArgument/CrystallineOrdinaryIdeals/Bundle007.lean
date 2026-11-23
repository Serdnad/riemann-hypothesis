module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle004
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CocycleDim

theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    (hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)) :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

theorem top_image {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B Z : Submodule E M) :
    (Z.comap Z.subtype).map (B.comap Z.subtype).mkQ = ⊤ := by
  rw [Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.CocycleDim

open GlobalTheory.CocycleDim in
theorem GlobalTheory.cocycleDim_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → Module.Finite E ↥(Z1 ρ) ∧ finrank E ↥(Z1 ρ) = finrank E ↥(finiteCocycles φ ρ) + finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨hH0, -, hfinf, hdimf⟩ := posBasic hP φ hφ ρ hρ hpos
  obtain ⟨hf1, -, e1, e2⟩ := tateRat hP (v := l) (l := l) φ hφ ρ hρ
  rw [if_pos rfl, hH0, finrank_bot, e2] at e1
  have hBf : Module.Finite E ↥(B1 ρ) := by
    unfold B1; infer_instance
  have hBS := (z1fMap (l := l) φ ρ ρ).1 hρ
  have hSZ : finiteCocycles φ ρ ≤ Z1 ρ := fun c h => h.1
  obtain ⟨-, hSd⟩ := sandwich _ _ _ hBS hSZ hfinf
  replace hSd : finrank E ↥(finiteCocycles φ ρ) = finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(B1 ρ) := hSd
  have hQ : Module.Finite E ↥(((Z1 ρ).comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ) := by
    rw [top_image]; exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm
  obtain ⟨hZ, hZd⟩ := sandwich _ _ _ (coboundaries_le_cocycles ρ hρ) le_rfl hQ
  rw [top_image, finrank_top] at hZd
  refine ⟨hZ, ?_⟩
  change finrank E ↥(Z1 ρ) = finrank E (H1 ρ) + finrank E ↥(B1 ρ) at hZd
  rw [hZd, hSd, e1, hdimf]
  ring
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.isUnit_characterDiff_at_chosenInertia : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B], (∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D)) - algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b (GlobalTheory.OrdLoc.s0 D)))) ∧ ∀ a, IsUnit (algebraMap O B (GlobalTheory.OrdLoc.cc D a)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _
  obtain ⟨-, -, -, hΨ, hs0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  rw [UpperTheory.V.Loc.Dat3.IsInertiaInfiniteCyclotomic.eq_1] at hs0
  obtain ⟨hH, hI, hc⟩ := hs0
  have key : ∀ a : Fin 3, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 =
      algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro a
    rw [UpperTheory.V.UnitaryThreeInertia.psi.eq_1, hΨ _ hH hI, cycA.eq_1, MonoidHom.comp_apply, ← map_pow, ← map_zpow,
      Units.coe_map, zpow_mul, zpow_natCast]
    rfl
  have unitQ : ∀ z : ℤ_[l], z ≠ 0 → IsUnit (algebraMap ℤ_[l] B z) := by
    intro z hz
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
    apply IsUnit.map
    apply Ne.isUnit
    simpa using hz
  have expo : ∀ a b : Fin 3, a ≠ b → (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b := by
    intro a b hab hw
    apply hab
    have he0 : (D.e : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ D.e := by exact_mod_cast D.e_pos
      omega
    have hw' := mul_left_cancel₀ he0 hw
    rw [wt1.eq_1, wt1.eq_1] at hw'
    apply Fin.ext
    omega
  have ne : ∀ m n : ℤ, m ≠ n →
      ((cyc l l D.s0 ^ m : ℤ_[l]ˣ) : ℤ_[l]) - ((cyc l l D.s0 ^ n : ℤ_[l]ˣ) : ℤ_[l]) ≠ 0 := by
    intro m n hmn hz
    apply hc
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨m - n, sub_ne_zero.mpr hmn, ?_⟩
    have hu : cyc l l D.s0 ^ m = cyc l l D.s0 ^ n := Units.ext (sub_eq_zero.mp hz)
    rw [zpow_sub, hu, mul_inv_cancel]
  have diff : ∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) -
      algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
    intro a b hab
    rw [key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub]
    exact unitQ _ (ne _ _ (expo a b hab))
  refine ⟨diff, ?_⟩
  intro a
  rw [UpperTheory.V.Loc.Dat3.cc.eq_1, map_mul, map_sub, map_sub]
  refine IsUnit.mul (diff a (a + 1) ?_) (diff a (a + 2) ?_)
  · fin_cases a <;> decide
  · fin_cases a <;> decide
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem icr_le_ker_of_conj : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (S : Type) [CommRing S] [IsDomain S] [Algebra O S] (i α : U.R →ₐ[O] S) (u : GL (Fin 3) S), push α U.r.hom = conjBy u (push i U.r.hom) → GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker i → i (GlobalTheory.OrdLoc.del D U.r.hom) ≠ 0 → GlobalTheory.OrdLoc.Icr D U ≤ RingHom.ker α := by
  intro l _ O _ _ _ D U S _ _ _ i α u hc hY hd
  have hm : HasMult D.η (push i U.r.hom) := U.r.hasMult
  obtain ⟨hcI, -, hcd⟩ := GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D (push i U.r.hom) u hm
  obtain ⟨hiI, -, hid⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D i U.r.hom
  obtain ⟨haI, -, had⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D α U.r.hom
  have hord : ordIdeal D U.r.hom ≤ IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hbot : ordIdeal D (push i U.r.hom) = ⊥ := by
    rw [← hiI, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    simpa [Ideal.mem_comap] using hY (hord ha)
  have hα : ordIdeal D (push α U.r.hom) = ⊥ := by rw [hc, hcI, hbot]
  have hdel : α (del D U.r.hom) ≠ 0 := by
    rw [had, hc, hcd, ← hid]; exact hd
  intro x hx
  obtain ⟨k, n, hn⟩ := hx
  have h1 : α (del D U.r.hom ^ n * x ^ k) ∈ ordIdeal D (push α U.r.hom) := by
    rw [← haI]; exact Ideal.mem_map_of_mem _ hn
  rw [hα, Ideal.mem_bot, map_mul, map_pow, map_pow] at h1
  have h2 : α x ^ k = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (pow_eq_zero_iff'.1 h).1 hdel
    · exact h
  exact RingHom.mem_ker.2 (pow_eq_zero_iff'.1 h2).1

end GlobalTheory.OrdLoc
end
