module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBot
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.cocycle_eq_crys_add_sub : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ W _ _ _ _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρW ρ hcW hc hpW hp i hi hiρ hdim c hcZ
  obtain ⟨hfinW, hdW⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρW hcW hpW
  obtain ⟨hfin, hd⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.compLeft_apply, Function.comp_apply,
        c'.2.2 g h, map_add, hiρ]⟩)
  have hM : ∀ c' g, ((M c' : Z1 ρ) : G → V) g = i ((c' : G → W) g) := fun _ _ => rfl
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      exact (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h
    · intro h
      exact (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1
  rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  refine ⟨c', c'.2, ?_⟩
  have := (Submodule.Quotient.eq S).1 hc'.symm
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  exact this
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.saturatingElement_unramified_twist_eq_pow_mul_unit : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (t : C), IsNilpotent t → ∃ u : GQ l →* Cˣ, QCont l (fun g => (u g : C)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : C) - 1)) ∧ ∃ (j : ℕ) (v : Cˣ), j ≤ 2 ∧ GlobalTheory.OrdLoc.del D (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u)) = t ^ j * v := by
  first | exact @GlobalTheory.OrdLoc.del_unr_twist | exact GlobalTheory.OrdLoc.del_unr_twist | (intros; apply GlobalTheory.OrdLoc.del_unr_twist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG (m := 3) (R := B)), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  first | exact @GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | exact GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | (intros; apply GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot <;> assumption)
end
