module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.GaloisCohomology.StatementLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCocyclesFinitelyGeneratedModPrime
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecomposition
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon.StPairing

section

variable {F : Type} [Field F] {B : Type} [CommRing B] [Algebra F B]
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

def tensorPairing (m : V →ₗ[F] V' →ₗ[F] F) : V ⊗[F] B →ₗ[F] V' ⊗[F] B →ₗ[F] B :=
  (TensorProduct.map₂ m (LinearMap.mul F B)).compr₂ (TensorProduct.lid F B).toLinearMap

@[simp] theorem tensorPairing_tmul (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (a : B) (v' : V') (b : B) :
    tensorPairing m (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b) = m v v' • (a * b) := by
  simp [tensorPairing, TensorProduct.map₂_apply_tmul]

theorem tensorPairing_one (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (y : V' ⊗[F] B) :
    tensorPairing m (v ⊗ₜ[F] (1 : B)) y = TensorProduct.lid F B (LinearMap.rTensor B (m v) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b => simp [tensorPairing_tmul]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem induction_two {p : V ⊗[F] B → V' ⊗[F] B → Prop} (h0 : ∀ y, p 0 y) (h0' : ∀ x, p x 0)
    (ht : ∀ v a v' b, p (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b))
    (ha : ∀ x x' y, p x y → p x' y → p (x + x') y)
    (ha' : ∀ x y y', p x y → p x y' → p x (y + y')) (x : V ⊗[F] B) (y : V' ⊗[F] B) : p x y := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0 y
  | tmul v a =>
    induction y using TensorProduct.induction_on with
    | zero => exact h0' _
    | tmul v' b => exact ht v a v' b
    | add y y' hy hy' => exact ha' _ _ _ hy hy'
  | add x x' hx hx' => exact ha _ _ _ hx hx'

end

theorem exists_stPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  intro l _ P K V _ _ _ V' _ _ _ ρ ρ' m hm
  obtain ⟨hg, -, hr, -⟩ := hm
  have hcyc : ∀ g : ↥(GK K), ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    have h := P.PD_χ K g
    simp [cycLL, h]
  refine ⟨tensorPairing m, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) =
      phiSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp [tensorPairing_tmul, map_mul, map_smul]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy']
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (monV P ℚ_[l] V x) y +
      tensorPairing m x (monV P ℚ_[l] V' y) = monSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp only [monV_tmul, tensorPairing_tmul]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [monSt_apply, Polynomial.derivative_mul]
      ring
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, ← hx, ← hx']
      abel
    · intro x y y' hy hy'
      simp only [map_add (f := _), ← hy, ← hy']
      abel
  · intro g x y
    refine induction_two (p := fun x y => tensorPairing m (stRep P ρ g x) (stRep P ρ' g y) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (tensorPairing m x y))
      (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      rw [stRep_tmul, stRep_tmul, tensorPairing_tmul, tensorPairing_tmul, hg, hcyc, map_smul, map_mul,
        smul_smul]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx', smul_add]
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy', smul_add]
  · intro a x y
    refine induction_two (p := fun x y => tensorPairing m (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y =
      a * tensorPairing m x y) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v b v' c
      rw [onB_tmul, tensorPairing_tmul, tensorPairing_tmul, LinearMap.mulLeft_apply, mul_smul_comm,
        mul_assoc]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx', mul_add]
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy', mul_add]
  · intro y hy
    refine GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero ℚ_[l] (Bst P) V V' m hr y fun v => ?_
    rw [← tensorPairing_one]
    exact hy v

end GlobalTheory.PMon.StPairing
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_stable_lattice_compact_group : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  first | exact @GlobalTheory.StableLat.exists_lattice | exact GlobalTheory.StableLat.exists_lattice | (intros; apply GlobalTheory.StableLat.exists_lattice <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem cocycles_finite (hT : Formalism.GaloisCohomology.LocalTateDualityK) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M) (h1 : ∀ m, a 1 m = m)
    (hmul : ∀ g h m, a (g * h) m = a g (a h m)) (hr : ∀ m : M, l ^ r • m = 0)
    (hlc : ∀ m, IsLocallyConstant fun g => a g m) :
    {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have ha : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : M), (rho g : M →ₗ[ZMod (l ^ (r + 1))] M) m = a (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  have hH := (GlobalTheory.T.finite_H1_H2_local hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho).1
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have hH1 : 0 < Nat.card (ReciprocityTheory.Gal.H1 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hZ
    exact (Nat.mul_pos hH1 hM).ne hZ
  let E : ↥{c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} →
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
  refine Set.finite_coe_iff.1 (Finite.of_injective E fun c c' h => Subtype.ext (funext fun g => ?_))
  have := congrFun (congrArg Subtype.val h) (φ g)
  simpa only [E, φ.symm_apply_apply] using this

theorem dvd_and_finite (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    ϖ ^ n ∣ ((l : ℕ) : O) ^ n ∧ Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  obtain ⟨-, -, hfin, hcomp⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := hO
  have hnu : ¬ IsUnit ((l : ℕ) : O) := fun hu => by
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
    have hH : IsHausdorff (Ideal.span {((l : ℕ) : O)}) O := hcomp.toIsHausdorff
    have h1 : (1 : O) = 0 := hH.haus 1 fun k => by
      rw [htop, SModEq.zero]
      simp [Ideal.top_pow]
    exact one_ne_zero h1
  have hdvd : ϖ ∣ ((l : ℕ) : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hnu
  have hd : ϖ ^ n ∣ ((l : ℕ) : O) ^ n := pow_dvd_pow_of_dvd hdvd n
  refine ⟨hd, ?_⟩
  have := hfin n
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.2 hd))

theorem finite_Z1Q : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA ϖ hϖ n hI
  obtain ⟨hd, hfin⟩ := dvd_and_finite l LL O hO ϖ hϖ n
  have hring : IsTopologicalRing LL := hO.2.2.2.1
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO.2.2.2.2 LA.T LA.fg LA.span
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := hO
  have hTfin : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  have hQ : Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) := by
    have : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
        (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) :=
      Module.Finite.of_restrictScalars_finite O _ _
    exact Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})
  have hmem : ∀ t : ↥LA.T, ϖ ^ n • t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun t =>
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hc : algebraMap O LL (ϖ ^ n) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact pow_ne_zero _ hϖ.ne_zero
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  refine cocycles_finite hT l K n _ (fun g => (actQ LA _ hI g).toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA 1 x) = _
      congr 1
      apply Subtype.ext
      change A.ρ 1 x = x
      simp
  · intro g h m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA (g * h) x) =
        Submodule.Quotient.mk (actT LA g (actT LA h x))
      congr 1
      apply Subtype.ext
      change A.ρ (g * h) x = A.ρ g (A.ρ h x)
      simp
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨b, hb⟩ := hd
      rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Nat.cast_pow, hb, mul_smul]
      exact hmem _
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g₀
      have hcont : Continuous fun g : ↥(GK K) =>
          (algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x) :=
        ((A.cont x).sub continuous_const).const_smul _
      have hev := (hopen.preimage hcont).mem_nhds (x := g₀) (by simp)
      filter_upwards [hev] with g hg
      change Submodule.Quotient.mk (actT LA g x) = Submodule.Quotient.mk (actT LA g₀ x)
      rw [Submodule.Quotient.eq]
      convert hmem ⟨_, hg⟩ using 1
      apply Subtype.ext
      change A.ρ g x - A.ρ g₀ x = ϖ ^ n • ((algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x))
      rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.CocycleModPow
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ s : Finset ↥(latticeCocycles LA), ∀ c : ↥(latticeCocycles LA), ∃ (a : ↥(latticeCocycles LA) → O) (c' : ↥(latticeCocycles LA)), ((c : ↥(GK K) → A.V) - ∑ i ∈ s, a i • (i : ↥(GK K) → A.V) - ((l : ℕ) : O) • (c' : ↥(GK K) → A.V)) ∈ latticeCoboundaries LA := by
  first | exact @GlobalTheory.LatRed.cocycles_fg_mod_l | exact GlobalTheory.LatRed.cocycles_fg_mod_l | (intros; apply GlobalTheory.LatRed.cocycles_fg_mod_l <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.card_H1_H0_transport_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  first | exact @GlobalTheory.GaloisTransport.card_H1_H0_transport | exact GlobalTheory.GaloisTransport.card_H1_H0_transport | (intros; apply GlobalTheory.GaloisTransport.card_H1_H0_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isDR_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  intro l _ P n _ _ K V _ _ b ρ Q hQ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK
  haveI : Nontrivial P.R.BdR := by
    refine ⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] P.R.BdR V n b
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x :=
    fun g x => P.PD_actdR K g x
  have key := GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K)
    (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR))
    (fun x => ⟨fun h => (P.PD K).invdR x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actdR g).commutes c⟩) Q
    (fun g => by
      have h := hQ g
      have : (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l) :=
        funext (hact g)
      rw [this]
      exact h)
    ((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔
          y ∈ DdR (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y
      have h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b] at key
  exact key

end GlobalTheory.PMon
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  first | exact @GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | exact GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | (intros; apply GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  first | exact @GlobalTheory.RedLocConst.redT_mem_Z1Q | exact GlobalTheory.RedLocConst.redT_mem_Z1Q | (intros; apply GlobalTheory.RedLocConst.redT_mem_Z1Q <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_modPow_action_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  first | exact @GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | exact GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | (intros; apply GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant <;> assumption)
end

section

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  first | exact @GlobalTheory.norm_det_le_one_of_entries_le_one | exact GlobalTheory.norm_det_le_one_of_entries_le_one | (intros; apply GlobalTheory.norm_det_le_one_of_entries_le_one <;> assumption)
end

section

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.matrix_commutant_valuation_decomposition : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  first | exact @GlobalTheory.ValDecomp.valuation_decomp | exact GlobalTheory.ValDecomp.valuation_decomp | (intros; apply GlobalTheory.ValDecomp.valuation_decomp <;> assumption)
end
