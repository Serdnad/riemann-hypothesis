module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Algebra.Module.Lattice.Full
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.Algebra.Module.Lattice.Basic

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.finite_field_enough_roots_of_unity (k : Type) [Field k] [Finite k] :
    HasEnoughRootsOfUnity k (Nat.card kˣ) := by
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Nat.card kˣ) k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top]

private theorem UpperTheory.V.Loc.mem_closure_of_kernel_containment {G k J : Type} [Group G] [Field k] [Finite k] [Finite J]
    (χ : J → G →* kˣ) (ω : G →* kˣ) (h : ∀ g, (∀ j, χ j g = 1) → ω g = 1) :
    ω ∈ Subgroup.closure (Set.range χ) := by
  classical
  let Φ : G →* (J → kˣ) := Pi.monoidHom χ
  let A := Φ.range
  have hker : Φ.ker ≤ ω.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g fun j => congrFun hg j
  let ψ : A →* kˣ := (QuotientGroup.lift Φ.ker ω hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g := by
    intro g
    have hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)
        = (g : G ⧸ Φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Φ.ker ω hker
      ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g
    rw [hs]
    rfl
  let e : J → (A →* kˣ) := fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype
  have he : ∀ j, (e j).comp Φ.rangeRestrict = χ j := fun j => by
    ext g
    rfl
  have hω : ω = ψ.comp Φ.rangeRestrict := by
    ext g
    rw [MonoidHom.comp_apply, hψ]
  haveI : Finite (A →* kˣ) :=
    Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    refine Subtype.ext (funext fun j => ?_)
    simp [pow_card_eq_one']
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
    refine MonoidHom.ext fun a => ?_
    simp [pow_card_eq_one']
  have hS : ψ ∈ Subgroup.closure (Set.range e) := by
    rw [← CommGroup.forall_monoidHom_apply_eq_one_iff k]
    intro η hη
    have ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1 := by
      refine Subtype.ext (funext fun j => ?_)
      have hj := CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η
      rw [hη _ (Subgroup.subset_closure ⟨j, rfl⟩)] at hj
      exact hj
    rw [← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]
  have key : ∀ φ ∈ Subgroup.closure (Set.range e),
      φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [he]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [MonoidHom.one_comp]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [MonoidHom.mul_comp]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [MonoidHom.inv_comp]
      exact inv_mem hx
  rw [hω]
  exact key ψ hS

theorem UpperTheory.V.Loc.v0e :
    ∀ {G k ι : Type} [Group G] [Field k] [Finite k] [Finite ι] (κ : ι → G →* kˣ) (ω : G →* kˣ), (∃ g, (∀ i j, κ i g = κ j g) ∧ ω g ≠ 1) ↔ ω ∉ Subgroup.closure (Set.range fun q : ι × ι => κ q.1 / κ q.2) := by
  intro G k ι _ _ _ _ κ ω
  constructor
  · rintro ⟨g, hg, hω⟩ hmem
    apply hω
    refine Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨q, rfl⟩
      simp [hg q.1 q.2]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
  · intro hn
    by_contra hc
    apply hn
    refine UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_
    by_contra hne
    refine hc ⟨g, fun i j => ?_, hne⟩
    have := hg (i, j)
    simpa [div_eq_one] using this
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc UpperTheory.V.U3

section Gen

variable {Q A V V' : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [AddCommGroup V'] [Module A V'] [Module Q V'] [IsScalarTower Q A V']

private noncomputable def tr (B : Type) [AddCommGroup B] [Module Q B] (e : V ≃ₗ[A] V') :
    V ⊗[Q] B ≃ₗ[A] V' ⊗[Q] B := AlgebraTensorModule.congr e (LinearEquiv.refl Q B)

variable {B B' : Type} [AddCommGroup B] [Module Q B] [AddCommGroup B'] [Module Q B'] (e : V ≃ₗ[A] V')

private theorem tr_map {f : V →ₗ[A] V} {f' : V' →ₗ[A] V'} (h : ∀ x, e (f x) = f' (e x)) (b : B →ₗ[Q] B')
    (x : V ⊗[Q] B) :
    tr B' e (AlgebraTensorModule.map f b x) = AlgebraTensorModule.map f' b (tr B e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tr, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem tr_smul {K : Type} [AddCommGroup K] [Module Q K] (s : K →ₗ[Q] Module.End Q B) (c : A ⊗[Q] K)
    (x : V ⊗[Q] B) :
    tr B e (((TensorProduct.homTensorHomMap (RingHom.id Q) V B V B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap s)) c x) =
    ((TensorProduct.homTensorHomMap (RingHom.id Q) V' B V' B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V' : A →ₐ[Q] Module.End Q V').toLinearMap s)) c (tr B e x) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd]
  | tmul a k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [tr]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

section Per

variable {l : ℕ} [Fact l.Prime] {A V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V'] (e : V ≃ₗ[A] V')

end Per
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse :
    ∀ {B : Type} [CommRing B] [IsDomain B] {d r : ℕ} (X : Matrix (Fin d) (Fin r) B) (Z : Matrix (Fin r) (Fin d) B), Z * X = 1 → ∃ s : Fin r → Fin d, (X.submatrix s id).det ≠ 0 := by
  intro B _ _ d r X Z hZX
  classical
  by_contra h
  push_neg at h
  have hM : (Z * X) = fun a => ∑ k, Z a k • X k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det := by
    have e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k) := by
      rw [← hM]
      rfl
    rw [e1]
    have e2 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum
      (fun a k => Z a k • X k)
    simp only [AlternatingMap.coe_multilinearMap] at e2
    rw [e2]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have e3 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ
      (fun a => Z a (s a)) (fun a => X (s a))
    simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3
    rw [e3]
    rfl
  have h0 : (Z * X).det = 0 := by
    rw [key]
    exact Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])
  rw [hZX, Matrix.det_one] at h0
  exact one_ne_zero h0
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_pow_mul_norm_le {l : ℕ} [Fact l.Prime] (C : ℝ) :
    ∃ m : ℕ, ∀ a : ℚ_[l], ‖a‖ ≤ C → ‖(l : ℚ_[l]) ^ m * a‖ ≤ 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C h1
  refine ⟨m, fun a ha => ?_⟩
  have hp : (0 : ℝ) < (l : ℝ) ^ m := by positivity
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hp, mul_one]
  exact ha.trans hm.le

private theorem exists_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    ∃ L : Submodule ℤ_[l] V, Submodule.IsLattice ℚ_[l] L ∧ ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
  classical
  let b := Module.finBasis ℚ_[l] V
  let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
  have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
    refine continuous_pi fun i => ?_
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
      (h.comp (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
  have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  refine ⟨Submodule.span ℤ_[l] S, ⟨?_, ?_⟩, ?_⟩
  · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, i⟩, rfl⟩
    have e := b.sum_repr (ρ g (b i))
    simp only [SetLike.mem_coe]
    rw [← e]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
      ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
        (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, hm _ hk⟩
    have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
      rw [← algebraMap_smul ℚ_[l] z, smul_smul]
      congr 1
      change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
      field_simp
    rw [this]
    exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).mp hli
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.exists_invariant_lattice_openEmbedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∃ (ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l])) (j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT ∧ IsOpenEmbedding j ∧ (∀ g x, j (ρT g x) = ρ g (j x)) ∧ ∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  have hex : ∃ L : Submodule ℤ_[l] V, Submodule.IsFullLattice ℚ_[l] L ∧
      ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
    classical
    let b := Module.finBasis ℚ_[l] V
    let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
    have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
      refine continuous_pi fun i => ?_
      exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
        (h.comp (continuous_id.prodMk continuous_const))
    obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
    have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    refine ⟨Submodule.span ℤ_[l] S, { toIsLattice := ⟨?_, ?_⟩, span_eq_top := ?_ }, ?_⟩
    · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
      have hN : N.FG := Submodule.fg_span (Set.finite_range _)
      refine hN.of_le ?_
      rw [Submodule.span_le]
      rintro _ ⟨⟨g, i⟩, rfl⟩
      have e := b.sum_repr (ρ g (b i))
      simp only [SetLike.mem_coe]
      rw [← e]
      refine Submodule.sum_mem _ fun k _ => ?_
      have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
        ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
          (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
      let z : ℤ_[l] := ⟨_, hm _ hk⟩
      have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
        rw [← algebraMap_smul ℚ_[l] z, smul_smul]
        congr 1
        change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
        field_simp
      rw [this]
      exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).mp hli
    · rw [eq_top_iff, ← b.span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨(1, i), by simp⟩
    · intro g x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨g', i⟩, rfl⟩ := hx
        exact Submodule.subset_span ⟨(g * g', i), by simp⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  
  obtain ⟨L, hL, hst⟩ := hex
  letI : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  letI : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  have hr : finrank ℤ_[l] L = finrank ℚ_[l] V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ_[l] L]
  let bL : Basis (Fin (finrank ℚ_[l] V)) ℤ_[l] L := Module.finBasisOfFinrankEq ℤ_[l] L hr
  let b : Basis (Fin (finrank ℚ_[l] V)) ℚ_[l] V := bL.extendOfIsFullLattice ℚ_[l]
  let j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V := L.subtype ∘ₗ bL.equivFun.symm.toLinearMap
  have hj : ∀ x, j x = b.equivFun.symm (fun i => (x i : ℚ_[l])) := fun x => by

    simp only [j, b, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, map_sum, map_smul,
    Submodule.subtype_apply, Basis.extendOfIsFullLattice_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ℚ_[l] (x i) _).symm
  let e : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₜ V :=
    { toEquiv := b.equivFun.symm.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap }
  have hjo : IsOpenEmbedding j := by
    have : (j : _ → V) = e ∘ Pi.map (fun _ => ((↑) : ℤ_[l] → ℚ_[l])) := funext hj
    rw [this]
    exact e.isOpenEmbedding.comp (IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe)
  let r : G → L →ₗ[ℤ_[l]] L := fun g => ((ρ g).restrictScalars ℤ_[l]).restrict (hst g)
  let ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l]) :=
    { toFun := fun g => bL.equivFun.toLinearMap ∘ₗ r g ∘ₗ bL.equivFun.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        change ρ 1 _ = _
        rw [map_one]; rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          Module.End.mul_apply]
        change ρ (g * g') _ = _
        rw [map_mul]; rfl }
  have hρ : ∀ g x, j (ρT g x) = ρ g (j x) := fun g x => by
    change L.subtype (bL.equivFun.symm (bL.equivFun (r g (bL.equivFun.symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  refine ⟨ρT, j, ?_, hjo, hρ, fun y => ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [hjo.isEmbedding.continuous_iff]
    have : (j ∘ fun p : G × (Fin (finrank ℚ_[l] V) → ℤ_[l]) => ρT p.1 p.2) = fun p => ρ p.1 (j p.2) :=
      funext fun p => hρ _ _
    rw [this]
    exact h.comp (continuous_fst.prodMk (hjo.continuous.comp continuous_snd))
  · obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) ‖b.equivFun y‖
    refine ⟨m, fun i => ⟨_, hm _ (norm_le_pi_norm (b.equivFun y) i)⟩, ?_⟩
    refine (hj _).trans ?_
    rw [LinearEquiv.symm_apply_eq, ← algebraMap_smul ℚ_[l] ((l : ℤ_[l]) ^ m) y, map_smul]
    funext i
    change (l : ℚ_[l]) ^ m * b.equivFun y i = _
    simp
end
