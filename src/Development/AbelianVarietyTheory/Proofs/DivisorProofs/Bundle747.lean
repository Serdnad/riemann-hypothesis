module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle414
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam

theorem derivWeierstrassP_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  rw [← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]

theorem derivWeierstrassP_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  have hs := Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)
  rw [hs]
  have hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3) := by
    intro l
    rw [← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem lattice_eq_scalePair_tauPair {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.lattice = (scalePair (tauPair τ) c h.1).lattice := by
  ext x
  rw [h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨u, v, ?_⟩
    change (u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))
    rw [← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn
    rw [mul_one] at hmn
    rw [hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]

theorem homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  intro L c τ h
  have hl := lattice_eq_scalePair_tauPair h
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]
  · rw [Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]
  · rw [derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]
  · rw [Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]
  · rw [Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]

end GlobalTheory.WpFam
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.IrrTensor

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (A : ι → Module.End ℂ V)

theorem density [Nontrivial V]
    (hirr : ∀ N : Submodule ℂ V, (∀ Z, ∀ y ∈ N, A Z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V →ₗ[ℂ] V, (∀ Z, T ∘ₗ A Z = A Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (f : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ m ∈ s, f m = r m := by
  let R := Algebra.adjoin ℂ (Set.range A)
  have hA : ∀ Z, A Z ∈ R := fun Z => Algebra.subset_adjoin ⟨Z, rfl⟩
  haveI : IsSimpleModule R V := by
    refine (isSimpleModule_iff R V).2 ?_
    refine { toNontrivial := (Submodule.nontrivial_iff R).2 inferInstance, eq_bot_or_eq_top := fun N => ?_ }
    rcases hirr (N.restrictScalars ℂ) (fun Z y hy => N.smul_mem (⟨A Z, hA Z⟩ : R) hy) with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  let F : Module.End (Module.End R V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g x => by
        obtain ⟨c, hc⟩ := hsch (g.restrictScalars ℂ) (fun Z => LinearMap.ext fun y =>
          g.map_smul (⟨A Z, hA Z⟩ : R) y)
        have hg : ∀ y, g y = c • y := fun y => LinearMap.congr_fun hc y
        show f (g x) = g (f x)
        rw [hg, hg, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := R) F s
  exact ⟨r.1, r.2, fun m hm => hr m hm⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end General

variable {p q : ℕ}

theorem mem_wtSub {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem root_shift {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (hl : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : v ∈ wtSub act μ) (a b : Ix p q) :
    act (Eab a b) v ∈ wtSub act (fun c => μ c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wtSub] at hv ⊢
  intro c
  have h := LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v
  have e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b := by
    unfold Eab
    have e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) =
        (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, h]
    have e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) =
        (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
    rw [e1, e2, ← sub_smul]
    congr 1
    split_ifs <;> simp
  rw [e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq] at h
  rw [← h, Rat.cast_add, add_smul, add_comm]

theorem exists_highest (M : GKMod p q) [Nontrivial M.V] : ∃ μ v, IsHW M.act μ v := by
  obtain ⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.V)
    have : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥ :=
      iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)
    have h2 := M.wts x
    rw [this] at h2
    exact hx h2
  obtain ⟨U, hfd, hU, hK⟩ := M.kfin v₀
  let k : Ix p q → ℚ := Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))
  let h : (Ix p q → ℚ) → ℚ := fun μ => ∑ a, k a * μ a
  let H : Mat p q := ∑ a, ((k a : ℚ) : ℂ) • Eab a a
  have hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    unfold Eab
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  have hH : ∀ x ∈ U, M.act H x ∈ U := by
    intro x hx

    simp only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)
  let S : Set (Ix p q → ℚ) := {μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}
  have hfin : (h '' S).Finite := by
    have h1 := Module.End.finite_hasEigenvalue ((M.act H).restrict hH)
    refine (h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_
    rintro _ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    show M.act H v = ((h μ : ℚ) : ℂ) • v

    simp only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]
    push_cast
    rfl
  obtain ⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩ :=
    Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩
  refine ⟨μ, v, hv0, hv, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a b hab
  by_contra hne
  have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab
  have hlt : k b < k a := by
    cases a <;> cases b <;> first | exact hab.elim | skip
    all_goals
      simp only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      exact hab
  have := hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩
  simp only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

theorem schur (M : GKMod p q) (hI : IrrGK M) (hA : AdmGK M) (T : M.V →ₗ[ℂ] M.V)
    (hT : ∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  haveI := hI.1
  obtain ⟨μ, v, hv0, hv⟩ := exists_highest M
  have hf : ∀ Z x, T (M.act Z x) = M.act Z (T x) := fun Z x => LinearMap.congr_fun (hT Z) x
  have hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ := by
    intro x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    refine ⟨fun c => ?_, fun c d h => ?_⟩
    · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
    · rw [← hf, hx.2 c d h, map_zero]
  haveI := hA μ
  haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x = c • (x : M.V) := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hy ⊢
    rw [hf, hy, map_smul]) with h | h
  · exact absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

end GlobalTheory.IrrTensor
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem resolution_lift_of_exact {O : Type} [CommRing O] {P A B C : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P]
    [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    {u : A →ₗ[O] B} {v : B →ₗ[O] C} (huv : Function.Exact u v) (w : P →ₗ[O] B)
    (hw : v ∘ₗ w = 0) : ∃ l : P →ₗ[O] A, u ∘ₗ l = w := by
  have hr : ∀ x, w x ∈ LinearMap.range u := fun x => by
    rw [← LinearMap.exact_iff.mp huv, LinearMap.mem_ker]
    exact LinearMap.congr_fun hw x
  obtain ⟨l, hl⟩ := Module.projective_lifting_property u.rangeRestrict (w.codRestrict _ hr)
    u.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext x
  have := congrArg Subtype.val (LinearMap.congr_fun hl x)
  simpa using this

theorem resolutions_homotopy_equivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  intro O _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _ G₂ _ _ _ _
    ε d₁ d₂ d₃ ν e₁ e₂ hε hd1 hd2 hd3 hν he1 he2
  obtain ⟨a₀, ha₀⟩ := Module.projective_lifting_property ν ε hν
  obtain ⟨b₀, hb₀⟩ := Module.projective_lifting_property ε ν hε
  have ha₀' : ∀ x, ν (a₀ x) = ε x := fun x => LinearMap.congr_fun ha₀ x
  have hb₀' : ∀ x, ε (b₀ x) = ν x := fun x => LinearMap.congr_fun hb₀ x
  obtain ⟨a₁, ha₁⟩ := resolution_lift_of_exact he1 (a₀ ∘ₗ d₁) (by
    ext x; simp [ha₀', Function.Exact.apply_apply_eq_zero hd1])
  have ha₁' : ∀ x, e₁ (a₁ x) = a₀ (d₁ x) := fun x => LinearMap.congr_fun ha₁ x
  obtain ⟨a₂, ha₂⟩ := resolution_lift_of_exact he2 (a₁ ∘ₗ d₂) (by
    ext x; simp [ha₁', Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨b₁, hb₁⟩ := resolution_lift_of_exact hd1 (b₀ ∘ₗ e₁) (by
    ext x; simp [hb₀', Function.Exact.apply_apply_eq_zero he1])
  have hb₁' : ∀ x, d₁ (b₁ x) = b₀ (e₁ x) := fun x => LinearMap.congr_fun hb₁ x
  obtain ⟨b₂, hb₂⟩ := resolution_lift_of_exact hd2 (b₁ ∘ₗ e₂) (by
    ext x; simp [hb₁', Function.Exact.apply_apply_eq_zero he2])
  obtain ⟨h₀, hh₀⟩ := resolution_lift_of_exact hd1 (LinearMap.id - b₀ ∘ₗ a₀) (by
    ext x; simp [hb₀', ha₀'])
  have hh₀' : ∀ x, d₁ (h₀ x) = x - b₀ (a₀ x) := fun x => by
    simpa using LinearMap.congr_fun hh₀ x
  obtain ⟨h₁, hh₁⟩ := resolution_lift_of_exact hd2 (LinearMap.id - b₁ ∘ₗ a₁ - h₀ ∘ₗ d₁) (by
    ext x; simp [hb₁', ha₁', hh₀'])
  have hh₁' : ∀ x, d₂ (h₁ x) = x - b₁ (a₁ x) - h₀ (d₁ x) := fun x => by
    simpa using LinearMap.congr_fun hh₁ x
  obtain ⟨h₂, hh₂⟩ := resolution_lift_of_exact hd3 (LinearMap.id - b₂ ∘ₗ a₂ - h₁ ∘ₗ d₂) (by
    ext x
    have e1 := LinearMap.congr_fun hb₂ (a₂ x)
    have e2 := LinearMap.congr_fun ha₂ x
    simp only [LinearMap.comp_apply] at e1 e2
    simp [hh₁', e1, e2, Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨k₀, hk₀⟩ := resolution_lift_of_exact he1 (LinearMap.id - a₀ ∘ₗ b₀) (by
    ext x; simp [hb₀', ha₀'])
  have hk₀' : ∀ x, e₁ (k₀ x) = x - a₀ (b₀ x) := fun x => by
    simpa using LinearMap.congr_fun hk₀ x
  obtain ⟨k₁, hk₁⟩ := resolution_lift_of_exact he2 (LinearMap.id - a₁ ∘ₗ b₁ - k₀ ∘ₗ e₁) (by
    ext x; simp [hb₁', ha₁', hk₀'])
  refine ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, ha₁, ha₂, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [hh₁, sub_add_cancel]
  · rw [hh₂, sub_add_cancel]
  · rw [hk₁, sub_add_cancel]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem baseChange_middle_equiv_of_exact : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  intro R R' _ _ _ W M H _ _ _ _ _ _ W' M' H' _ _ _ _ _ _ i p i' p' a b c hp hip hi' hip' hb hc hW hH
  obtain ⟨eW, heW⟩ := hW
  obtain ⟨eH, heH⟩ := hH
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  haveI : IsScalarTower R R' M' := ⟨fun r s x => by
    show (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let b' : M →ₗ[R] M' :=
    { toFun := b, map_add' := b.map_add, map_smul' := fun r m => b.map_smulₛₗ r m }
  let f : R' ⊗[R] M →ₗ[R'] M' := b'.liftBaseChange R'
  have hf1 : ∀ x, f (1 ⊗ₜ x) = b x := by
    intro x; simp [f, b']
  have hfp : ∀ s, p' (f s) = eH (LinearMap.baseChange R' p s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have h1 : (r ⊗ₜ[R] m : R' ⊗[R] M) = r • (1 ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heH, hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hfi : ∀ u, f (LinearMap.baseChange R' i u) = i' (eW u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      have h1 : (r ⊗ₜ[R] w : R' ⊗[R] W) = r • (1 ⊗ₜ w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heW, hb]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex : Function.Exact (LinearMap.baseChange R' i) (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    first | exact lTensor_exact R' hip hp | exact LinearMap.lTensor_exact R' hip hp
  have hsurj : Function.Surjective (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective R' hp
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have h0 : LinearMap.baseChange R' p s = 0 := by
      have := hfp s
      rw [hs, map_zero] at this
      exact (LinearEquiv.map_eq_zero_iff eH).1 this.symm
    obtain ⟨u, rfl⟩ := (hex s).1 h0
    have h2 : i' (eW u) = 0 := by rw [← hfi u, hs]
    have h3 : eW u = 0 := hi' (by rw [h2, map_zero])
    rw [(LinearEquiv.map_eq_zero_iff eW).1 h3, map_zero]
  have hsur : Function.Surjective f := by
    intro m'
    obtain ⟨s, hs⟩ := hsurj (eH.symm (p' m'))
    have h0 : p' (m' - f s) = 0 := by
      rw [map_sub, hfp, hs, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨w', hw'⟩ := (hip' _).1 h0
    refine ⟨s + LinearMap.baseChange R' i (eW.symm w'), ?_⟩
    rw [map_add (f := _), hfi, LinearEquiv.apply_symm_apply, hw', add_sub_cancel]
  have hbij : Function.Bijective f := ⟨hinj, hsur⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun x => hf1 x⟩

end GlobalTheory.AbCoh
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem exists_basis_fin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] : ∃ N, Nonempty (Module.Basis (Fin N) A B) := by
  by_cases hA : Nontrivial A
  · exact ⟨_, ⟨Module.finBasis A B⟩⟩
  · rw [not_nontrivial_iff_subsingleton] at hA
    have : Subsingleton B := Module.subsingleton A B
    exact ⟨0, ⟨Module.Basis.empty B⟩⟩

theorem hilbertScheme_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ _ _ r
  obtain ⟨N, ⟨e⟩⟩ := exists_basis_fin A B
  let F := GlobalTheory.HilbAff.functor A B r
  choose X x hX hlft hbas huniv using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  choose W hW _ using fun (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : F.obj (op Z)) =>
    GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ Z y
  have stab : ∀ σ (Z : Scheme.{0}) (g : Z ⟶ X σ), GlobalTheory.HilbAff.Basic A B e σ (F.map g.op (x σ)) := by
    intro σ Z g
    have htop : Set.range (𝟙 (X σ)) ⊆ (W σ (X σ) (x σ) : Set (X σ)) :=
      (hW σ _ _ _ (𝟙 _)).2 (by rw [op_id, F.map_id]; exact hbas σ)
    exact (hW σ _ _ _ g).1 (fun z _ => htop ⟨z, rfl⟩)
  have hrep : F.IsRepresentable := by
    refine GlobalTheory.GeneratorFunctor.isRepresentable_of_charts F (GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski A B r) X x W ?_ ?_ ?_
    · intro σ Z y Z' a
      rw [hW]
      constructor
      · intro hb
        obtain ⟨g, hg, -⟩ := huniv σ Z' _ hb
        exact ⟨g, hg⟩
      · rintro ⟨g, hg⟩
        rw [← hg]
        exact stab σ Z' g
    · intro σ Z g g' h
      obtain ⟨g₀, -, hu⟩ := huniv σ Z _ (stab σ Z g)
      exact (hu g rfl).trans (hu g' h.symm).symm
    · intro Z y z
      obtain ⟨σ, U, hz, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e Z y z
      refine ⟨σ, (hW σ Z y U U.ι).2 hb ?_⟩
      simpa using hz
  let R := F.representableBy
  obtain ⟨U, u, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.affineHilbert_representing_universal_subscheme A B r F.reprX R
  obtain ⟨q1, q2, q3⟩ := GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType A B r F.reprX R
  refine ⟨F.reprX, (R.homEquiv (𝟙 _)).1, U, u, ?_, h1, h2, h3, h4, h5⟩
  rw [IsProper.eq_valuativeCriterion, ValuativeCriterion.eq]
  exact ⟨⟨⟨⟨GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence A B r F.reprX R, GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness A B r F.reprX R⟩, q1⟩, q2⟩, q3⟩

end GlobalTheory.HilbAff
end
end
