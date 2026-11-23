module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle096
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle099
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w' w₁ w₂ w₃ w₄ w₅ t₁ t₂ t₃ t₄ t₅

section Alg

theorem five_add {A₁ : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {A₄ : Type w₄} {A₅ : Type w₅}
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : A₁ →+ A₂) (u₂ : A₂ →+ A₃) (u₃ : A₃ →+ A₄) (u₄ : A₄ →+ A₅)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (g₁ : A₁ →+ L₁) (g₂ : A₂ →+ L₂) (g₃ : A₃ →+ L₃) (g₄ : A₄ →+ L₄) (g₅ : A₅ →+ L₅)
    (c₁ : ∀ x, g₂ (u₁ x) = v₁ (g₁ x)) (c₂ : ∀ x, g₃ (u₂ x) = v₂ (g₂ x))
    (c₃ : ∀ x, g₄ (u₃ x) = v₃ (g₃ x)) (c₄ : ∀ x, g₅ (u₄ x) = v₄ (g₄ x))
    (eA₂ : Function.Exact u₁ u₂) (eA₃ : Function.Exact u₂ u₃) (eA₄ : Function.Exact u₃ u₄)
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (s₁ : Function.Surjective g₁) (b₂ : Function.Bijective g₂) (b₄ : Function.Bijective g₄)
    (i₅ : Function.Injective g₅) : Function.Bijective g₃ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : u₃ x = 0 := b₄.1 (by rw [c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (eA₃ x).1 h1
    have h2 : v₂ (g₂ y) = 0 := by rw [← c₂, hx]
    obtain ⟨z, hz⟩ := (eL₂ _).1 h2
    obtain ⟨t, rfl⟩ := s₁ z
    have h3 : u₁ t = y := b₂.1 (by rw [c₁, hz])
    exact (eA₂ _).2 ⟨t, h3⟩
  · intro t
    obtain ⟨p, hp⟩ := b₄.2 (v₃ t)
    have h1 : u₄ p = 0 := i₅ (by
      rw [c₄, hp, map_zero]
      exact (eL₄ _).2 ⟨t, rfl⟩)
    obtain ⟨q, rfl⟩ := (eA₄ p).1 h1
    have h2 : v₃ (t - g₃ q) = 0 := by rw [map_sub, ← c₃, hp, sub_self]
    obtain ⟨y', hy'⟩ := (eL₃ _).1 h2
    obtain ⟨y, rfl⟩ := b₂.2 y'
    refine ⟨q + u₂ y, ?_⟩
    rw [map_add (f := _), c₂, hy']
    abel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_ext {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (g h : (∀ i, N i ⊗[R] M i) →+ P) (H : ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = h (Pi.single i (n ⊗ₜ x))) : g = h := by
  refine AddMonoidHom.functions_ext _ g h fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact H i n x
  | add x y hx hy => rw [Pi.single_add, map_add (f := _), map_add (f := _), hx, hy]

def piT {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) :
    (∀ i, N i ⊗[R] M i) →+ (∀ i, N i ⊗[R] M' i) where
  toFun t i := (u i).lTensor (N i) (t i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem piT_single {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) (i : ι) (n : N i) (x : M i) :
    piT (N := N) u (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ u i x) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [piT]
  · simp [piT, Pi.single_eq_of_ne h]

theorem piT_exact [∀ i, Module.Flat R (N i)] {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (u : ∀ i, M₁ i →ₗ[R] M₂ i) (v : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (u i) (v i)) : Function.Exact (piT (N := N) u) (piT (N := N) v) := by
  intro t
  constructor
  · intro ht
    have h1 : ∀ i, ∃ s, (u i).lTensor (N i) s = t i := fun i =>
      (Module.Flat.lTensor_exact (N i) (h i) (t i)).1 (congrFun ht i)
    choose s hs using h1
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext i
    exact (Module.Flat.lTensor_exact (N i) (h i) _).2 ⟨s i, rfl⟩

theorem tens_zero {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (hM : ∀ i, Subsingleton (M i)) (hM' : Subsingleton M') (f : ∀ i, N i → M i → M') :
    Tens R (N := N) (M := M) (M' := M') f := by
  have h0 : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => by
    refine ⟨fun x y => ?_⟩
    have : ∀ z : N i ⊗[R] M i, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [this x, this y]
  refine ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ _ => by simp⟩,
    fun i n x => Subsingleton.elim _ _⟩

theorem tens_transfer {M : ι → Type w₁} {L : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)] {M' : Type t₁} {L' : Type t₂} [AddCommGroup M'] [AddCommGroup L']
    (u : ∀ i, M i ≃ₗ[R] L i) (u' : M' ≃+ L') (f : ∀ i, N i → M i → M') (h : ∀ i, N i → L i → L')
    (hc : ∀ i n x, h i n (u i x) = u' (f i n x))
    (hf : Tens R (N := N) (M := M) (M' := M') f) : Tens R (N := N) (M := L) (M' := L') h := by
  obtain ⟨g, hg⟩ := hf
  let e : (∀ i, N i ⊗[R] L i) ≃+ (∀ i, N i ⊗[R] M i) :=
    { toFun := piT (N := N) fun i => ((u i).symm : L i →ₗ[R] M i)
      invFun := piT (N := N) fun i => ((u i) : M i →ₗ[R] L i)
      left_inv := fun t => by
        funext i
        change (((u i) : M i →ₗ[R] L i).lTensor (N i)) ((((u i).symm : L i →ₗ[R] M i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      right_inv := fun t => by
        funext i
        change (((u i).symm : L i →ₗ[R] M i).lTensor (N i)) ((((u i) : M i →ₗ[R] L i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      map_add' := map_add _ }
  refine ⟨(e.trans g).trans u', fun i n x => ?_⟩
  obtain ⟨y, rfl⟩ := (u i).surjective x
  have : e (Pi.single i (n ⊗ₜ u i y)) = Pi.single i (n ⊗ₜ y) := by
    change piT (N := N) (fun i => ((u i).symm : L i →ₗ[R] M i)) _ = _
    rw [piT_single]
    simp
  simp only [AddEquiv.trans_apply, this, hg, hc]

theorem tens_five [∀ i, Module.Flat R (N i)]
    {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃} {M₄ : ι → Type w₄} {M₅ : ι → Type w₅}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (u₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (u₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (u₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (f₁ : ∀ i, N i → M₁ i → L₁) (f₂ : ∀ i, N i → M₂ i → L₂) (f₃ : ∀ i, N i → M₃ i → L₃)
    (f₄ : ∀ i, N i → M₄ i → L₄) (f₅ : ∀ i, N i → M₅ i → L₅)
    (c₁ : ∀ i n x, f₂ i n (u₁ i x) = v₁ (f₁ i n x)) (c₂ : ∀ i n x, f₃ i n (u₂ i x) = v₂ (f₂ i n x))
    (c₃ : ∀ i n x, f₄ i n (u₃ i x) = v₃ (f₃ i n x)) (c₄ : ∀ i n x, f₅ i n (u₄ i x) = v₄ (f₄ i n x))
    (eM₂ : ∀ i, Function.Exact (u₁ i) (u₂ i)) (eM₃ : ∀ i, Function.Exact (u₂ i) (u₃ i))
    (eM₄ : ∀ i, Function.Exact (u₃ i) (u₄ i))
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (h₁ : Tens R (N := N) (M := M₁) (M' := L₁) f₁) (h₂ : Tens R (N := N) (M := M₂) (M' := L₂) f₂)
    (h₄ : Tens R (N := N) (M := M₄) (M' := L₄) f₄) (h₅ : Tens R (N := N) (M := M₅) (M' := L₅) f₅)
    (hadd : ∀ i, ∃ F : N i ⊗[R] M₃ i →+ L₃, ∀ n x, F (n ⊗ₜ x) = f₃ i n x) :
    Tens R (N := N) (M := M₃) (M' := L₃) f₃ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨g₄, hg₄⟩ := h₄
  obtain ⟨g₅, hg₅⟩ := h₅
  choose F hF using hadd
  let g₃ : (∀ i, N i ⊗[R] M₃ i) →+ L₃ := ∑ i, (F i).comp (Pi.evalAddMonoidHom _ i)
  have hg₃ : ∀ i n x, g₃ (Pi.single i (n ⊗ₜ x)) = f₃ i n x := by
    intro i n x
    simp only [g₃, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single i]
    · simp [hF]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have b := five_add (piT (N := N) u₁) (piT (N := N) u₂) (piT (N := N) u₃) (piT (N := N) u₄) v₁ v₂ v₃ v₄
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃ g₄.toAddMonoidHom g₅.toAddMonoidHom
    (fun x => DFunLike.congr_fun (tens_ext (g₂.toAddMonoidHom.comp (piT (N := N) u₁)) (v₁.comp g₁.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₁, hg₂, c₁]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₃.comp (piT (N := N) u₂)) (v₂.comp g₂.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₂, hg₃, c₂]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₄.toAddMonoidHom.comp (piT (N := N) u₃)) (v₃.comp g₃)
      fun i n x => by simp [piT_single, hg₃, hg₄, c₃]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₅.toAddMonoidHom.comp (piT (N := N) u₄)) (v₄.comp g₄.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₄, hg₅, c₄]) x)
    (piT_exact u₁ u₂ eM₂) (piT_exact u₂ u₃ eM₃) (piT_exact u₃ u₄ eM₄) eL₂ eL₃ eL₄
    g₁.surjective g₂.bijective g₄.bijective g₅.injective
  exact ⟨AddEquiv.ofBijective g₃ b, hg₃⟩

end Alg

end GlobalTheory.CompanionTheory.LocBC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w w'

namespace GlobalTheory.CompanionTheory.CosieveBC

section Pairing

variable (R : Type) [CommRing R] {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

def Bal {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (p : ∀ i, N i → M i → P) : Prop :=
  (∀ i n n' x, p i (n + n') x = p i n x + p i n' x) ∧ (∀ i n x x', p i n (x + x') = p i n x + p i n x') ∧
    ∀ i (r : R) n x, p i (r • n) x = p i n (r • x)

variable {R}
variable {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]

def lift1 {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) : N i ⊗[R] M i →+ P :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun n => AddMonoidHom.mk' (p i n) (hp.2.1 i n))
      fun a b => AddMonoidHom.ext fun x => hp.1 i a b x)
    fun r n x => hp.2.2 i r n x

theorem balanced_lift_tmul {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (n : N i) (x : M i) :
    lift1 hp i (n ⊗ₜ x) = p i n x := rfl

variable [Fintype ι] [DecidableEq ι]

def gmap {p : ∀ i, N i → M i → P} (hp : Bal R p) : (∀ i, N i ⊗[R] M i) →+ P :=
  ∑ i, (lift1 hp i).comp (Pi.evalAddMonoidHom _ i)

theorem gmap_single {p : ∀ i, N i → M i → P} (hp : Bal R p) (i : ι) (t : N i ⊗[R] M i) :
    gmap hp (Pi.single i t) = lift1 hp i t := by
  unfold gmap
  rw [AddMonoidHom.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem hom_ext {Q : Type w'} [AddCommGroup Q] {a b : (∀ i, N i ⊗[R] M i) →+ Q}
    (h : ∀ i n x, a (Pi.single i (n ⊗ₜ x)) = b (Pi.single i (n ⊗ₜ x))) : a = b := by
  refine AddMonoidHom.functions_ext _ _ _ fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact h i n x
  | add s t hs ht => rw [Pi.single_add, map_add (f := _), map_add (f := _), hs, ht]

theorem tens_iff {p : ∀ i, N i → M i → P} (hp : Bal R p) :
    Tens R (N := N) (M := M) (M' := P) p ↔ Function.Bijective (gmap hp) := by
  constructor
  · rintro ⟨g, hg⟩
    have e : g.toAddMonoidHom = gmap hp := hom_ext fun i n x => by
      rw [gmap_single, balanced_lift_tmul]
      exact hg i n x
    rw [← e]
    exact g.bijective
  · intro h
    refine ⟨AddEquiv.ofBijective (gmap hp) h, fun i n x => ?_⟩
    change gmap hp _ = _
    rw [gmap_single, balanced_lift_tmul]

def tmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] (a : ∀ i, M i →ₗ[R] M₂ i) :
    (∀ i, N i ⊗[R] M i) →+ ∀ i, N i ⊗[R] M₂ i :=
  AddMonoidHom.mk' (fun t i => (a i).lTensor (N i) (t i)) fun s t => funext fun i => map_add _ _ _

theorem tmap_single {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    (a : ∀ i, M i →ₗ[R] M₂ i) (i : ι) (n : N i) (x : M i) :
    tmap (N := N) a (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ a i x) := by
  funext k
  change (a k).lTensor (N k) ((Pi.single i (n ⊗ₜ x) : ∀ i, N i ⊗[R] M i) k) = _
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem tmap_exact [∀ i, Module.Flat R (N i)] {M₂ M₃ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (a : ∀ i, M i →ₗ[R] M₂ i) (b : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (a i) (b i)) : Function.Exact (tmap (N := N) a) (tmap (N := N) b) := by
  have e := fun i => Module.Flat.lTensor_exact (N i) (h i)
  intro y
  constructor
  · intro hy
    have hy' := fun i => (e i (y i)).1 (congrFun hy i)
    choose t ht using hy'
    exact ⟨t, funext ht⟩
  · rintro ⟨t, rfl⟩
    exact funext fun i => (e i _).2 ⟨t i, rfl⟩

theorem comm_gmap {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (a : ∀ i, M i →ₗ[R] M₂ i) (b : P →+ P₂) (c : ∀ i n x, b (p i n x) = q i n (a i x)) :
    b.comp (gmap hp) = (gmap hq).comp (tmap a) := hom_ext fun i n x => by
  simp only [AddMonoidHom.comp_apply]
  rw [tmap_single, gmap_single, gmap_single, balanced_lift_tmul, balanced_lift_tmul, c]

theorem tens_five [∀ i, Module.Flat R (N i)] {M₁ M₂ M₃ M₄ M₅ : ι → Type w}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {P₁ P₂ P₃ P₄ P₅ : Type w'} [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup P₃] [AddCommGroup P₄] [AddCommGroup P₅]
    (a₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (a₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (a₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (a₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (b₁ : P₁ →+ P₂) (b₂ : P₂ →+ P₃) (b₃ : P₃ →+ P₄) (b₄ : P₄ →+ P₅)
    (ea₁ : ∀ i, Function.Exact (a₁ i) (a₂ i)) (ea₂ : ∀ i, Function.Exact (a₂ i) (a₃ i))
    (ea₃ : ∀ i, Function.Exact (a₃ i) (a₄ i))
    (eb₁ : Function.Exact b₁ b₂) (eb₂ : Function.Exact b₂ b₃) (eb₃ : Function.Exact b₃ b₄)
    {p₁ : ∀ i, N i → M₁ i → P₁} {p₂ : ∀ i, N i → M₂ i → P₂} {p₃ : ∀ i, N i → M₃ i → P₃}
    {p₄ : ∀ i, N i → M₄ i → P₄} {p₅ : ∀ i, N i → M₅ i → P₅}
    (B₁ : Bal R p₁) (B₂ : Bal R p₂) (B₃ : Bal R p₃) (B₄ : Bal R p₄) (B₅ : Bal R p₅)
    (c₁ : ∀ i n x, b₁ (p₁ i n x) = p₂ i n (a₁ i x)) (c₂ : ∀ i n x, b₂ (p₂ i n x) = p₃ i n (a₂ i x))
    (c₃ : ∀ i n x, b₃ (p₃ i n x) = p₄ i n (a₃ i x)) (c₄ : ∀ i n x, b₄ (p₄ i n x) = p₅ i n (a₄ i x))
    (t₁ : Tens R (N := N) (M := M₁) (M' := P₁) p₁) (t₂ : Tens R (N := N) (M := M₂) (M' := P₂) p₂)
    (t₄ : Tens R (N := N) (M := M₄) (M' := P₄) p₄) (t₅ : Tens R (N := N) (M := M₅) (M' := P₅) p₅) :
    Tens R (N := N) (M := M₃) (M' := P₃) p₃ := by
  rw [tens_iff B₁] at t₁
  rw [tens_iff B₂] at t₂
  rw [tens_iff B₄] at t₄
  rw [tens_iff B₅] at t₅
  rw [tens_iff B₃]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (tmap (N := N) a₁) (tmap (N := N) a₂) (tmap (N := N) a₃) (tmap (N := N) a₄) b₁ b₂ b₃ b₄
    (gmap B₁) (gmap B₂) (gmap B₃) (gmap B₄) (gmap B₅)
    (comm_gmap B₁ B₂ a₁ b₁ c₁) (comm_gmap B₂ B₃ a₂ b₂ c₂) (comm_gmap B₃ B₄ a₃ b₃ c₃) (comm_gmap B₄ B₅ a₄ b₄ c₄)
    (tmap_exact a₁ a₂ ea₁) (tmap_exact a₂ a₃ ea₂) (tmap_exact a₃ a₄ ea₃) eb₁ eb₂ eb₃ t₁.2 t₂ t₄ t₅.1

theorem tens_of_bij {M₂ : ι → Type w} [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {P₂ : Type w'} [AddCommGroup P₂]
    {p : ∀ i, N i → M i → P} {q : ∀ i, N i → M₂ i → P₂} (hp : Bal R p) (hq : Bal R q)
    (e : ∀ i, M₂ i ≃ₗ[R] M i) (b : P₂ ≃+ P) (c : ∀ i n x, b (q i n x) = p i n (e i x))
    (t : Tens R (N := N) (M := M) (M' := P) p) : Tens R (N := N) (M := M₂) (M' := P₂) q := by
  obtain ⟨g, hg⟩ := t
  refine ⟨(AddEquiv.piCongrRight fun i => ((e i).lTensor (N i)).toAddEquiv).trans (g.trans b.symm), fun i n x => ?_⟩
  refine b.injective ?_
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [c, ← hg]
  congr 1
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end Pairing

end GlobalTheory.CompanionTheory.CosieveBC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_vanishing_along_ideal_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A),
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  first | exact @GlobalTheory.CompanionTheory.TowerEnd.vanish | exact GlobalTheory.CompanionTheory.TowerEnd.vanish | (intros; apply GlobalTheory.CompanionTheory.TowerEnd.vanish <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Completion

theorem mem_pow_smul_top_iff {T : Type} [CommRing T] (t y : T) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule T T) ↔ y ∈ Ideal.span {t ^ n} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem aic_of_isCompl : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := by
  intro B _ T _ π g hc hπ hA hV P hP hd
  have step := GlobalTheory.T.hensel_polynomial_refinement B T π g hc hπ hA hV P hP hd
  set d := P.natDegree with hdd
  set t := g π with ht

  let S : ℕ → Type := fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}
  have s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)} := by simp
  let seq : (M : ℕ) → S M := fun M =>
    Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M
  have hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M} := fun M =>
    (step M (seq M).1 (seq M).2).choose_spec.1
  let a : ℕ → T := fun M => g (seq M).1
  have hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M} := by
    intro M
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (hstep M)
    refine Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩
    simp only [a, ht, ← map_pow, ← map_mul, hc', map_sub]
  have hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} := by
    intro m n hmn
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn
  have hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := Ideal.add_mem _ ih (hpow hmn (hg n))
      simpa using this
  have hpre := hc.compl.toIsPrecomplete
  obtain ⟨x, hx⟩ := hpre.prec' a (fun {m n} hmn => by
    rw [SModEq.sub_mem, mem_pow_smul_top_iff]
    have := Ideal.neg_mem_iff _ |>.2 (hcau hmn)
    simpa using this)
  refine ⟨x, ?_⟩
  have hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n} := by
    intro n
    have h1 : a n - x ∈ Ideal.span {t ^ n} := by
      have := hx n
      rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    have h2 : P.eval (a n) ∈ Ideal.span {t ^ n} :=
      hpow (Nat.le_mul_of_pos_left n hd) (seq n).2
    have h3 : a n - x ∣ P.eval (a n) - P.eval x := Polynomial.sub_dvd_eval_sub _ _ _
    have h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n} := Ideal.mem_of_dvd _ h3 h1
    have := Ideal.sub_mem _ h2 h4
    simpa using this
  have := hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by
    rw [SModEq.zero, mem_pow_smul_top_iff]
    exact hz n)
  exact this

end GlobalTheory.CompanionTheory.Completion
end

section

open Zc.Comb
universe u

theorem _root_.GlobalTheory.T.shuffle_weight_antisymmetric_eq : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L → AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) → InSh s (L : Multiset (ASeg T)) (wt s M) → (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | exact GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | (intros; apply GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm <;> assumption)
end

section


theorem _root_.GlobalTheory.T.crossing_of_walls_and_heights : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.HtLip → PositivityTheory.RgEis.PiLocalization₂ → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Cross := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.cross | exact GlobalTheory.CompanionTheory.RgEisCross.cross | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.cross <;> assumption)
end
