module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Invariant.Profinite
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
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open AlgebraicGeometry CategoryTheory

namespace CrystallineSemistableComparison

namespace RelDim

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

def Chart (n : ℕ) (x : X) : Prop :=
  ∃ (U : (Spec (CommRingCat.of K)).Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
    (e : V ≤ f ⁻¹ᵁ U), RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

theorem eq_top {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) :
    U = ⊤ := by
  have : Subsingleton (Spec (CommRingCat.of K)) := by
    refine ⟨fun a b => PrimeSpectrum.ext ?_⟩
    have := a.isPrime
    have := b.isPrime
    rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal]
  have hy : f x ∈ U := e hx
  refine eq_top_iff.mpr fun z _ => ?_
  rwa [Subsingleton.elim z (f x)]

theorem basicOpen {n : ℕ} {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) (a : Γ(X, V))
    (W : X.Opens) (hW : X.basicOpen a = W) (e' : W ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e').hom := by
  subst hW
  have := hV.isLocalization_basicOpen a
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    Γ(X, X.basicOpen a) a (f.appLE U V e).hom h
  convert h2 using 1
  rw [← Scheme.Hom.appLE_map f e (homOfLE (X.basicOpen_le a)).op]
  rfl

theorem uniq {n m : ℕ} {U : (Spec (CommRingCat.of K)).Opens} (W : X.Opens) [Nonempty W] (e : W ≤ f ⁻¹ᵁ U)
    (hn : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e).hom)
    (hm : RingHom.IsStandardSmoothOfRelativeDimension m (f.appLE U W e).hom) : n = m := by
  let := (f.appLE U W e).hom.toAlgebra
  have h1 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n hn
  have h2 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m hm
  exact_mod_cast h1.symm.trans h2

theorem chart_uniq {n m : ℕ} {x : X} (hn : Chart f n x) (hm : Chart f m x) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn
  obtain ⟨U', hU', V', hV', hx', e', h'⟩ := hm
  have h1 := eq_top f e hx
  have h2 := eq_top f e' hx'
  subst h1 h2
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter hV hV' x ⟨hx, hx'⟩
  have ea : X.basicOpen a ≤ f ⁻¹ᵁ ⊤ := (X.basicOpen_le a).trans e
  have ha := basicOpen f hV e h a _ rfl ea
  have hb := basicOpen f hV' e' h' b _ hab.symm ea
  have : Nonempty (X.basicOpen a) := ⟨⟨x, hxa⟩⟩
  exact uniq f _ ea ha hb

theorem exists_chart [Smooth f] (x : X) : ∃ n, Chart f n x := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, U, hU, V, hV, hx, e, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem isOpen_chart (n : ℕ) : IsOpen {x | Chart f n x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, V, hV, hx, e, h⟩
  exact ⟨V, fun y hy => ⟨U, hU, V, hV, hy, e, h⟩, V.isOpen, hx⟩

end RelDim


open RelDim in
theorem exists_smoothOfRelativeDimension {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [ConnectedSpace X] : ∃ d, SmoothOfRelativeDimension d f := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨n, hn⟩ := exists_chart f x0
  have hclopen : IsClopen {x | Chart f n x} := by
    refine ⟨?_, isOpen_chart f n⟩
    rw [← isOpen_compl_iff]
    have : {x | Chart f n x}ᶜ = ⋃ m ∈ {m | m ≠ n}, {x | Chart f m x} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_chart f x
        exact ⟨m, fun h => hx (h ▸ hm), hm⟩
      · rintro ⟨m, hmn, hm⟩ hx
        exact hmn (chart_uniq f hm hx)
    rw [this]
    exact isOpen_biUnion fun m _ => isOpen_chart f m
  have huniv := (isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x0, hn⟩)
  refine ⟨n, ⟨fun x => ?_⟩⟩
  have hx : x ∈ {x | Chart f n x} := huniv ▸ Set.mem_univ x
  exact hx

end CrystallineSemistableComparison
end

section

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.GeoA

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Type) [CommRing R] [Algebra k R]

def act (σ : Ω ≃ₐ[k] Ω) : (Ω ⊗[k] R) ≃ₐ[k] (Ω ⊗[k] R) := Algebra.TensorProduct.congr σ AlgEquiv.refl

@[simp] theorem act_tmul (σ : Ω ≃ₐ[k] Ω) (a : Ω) (r : R) : act R σ (a ⊗ₜ r) = σ a ⊗ₜ r := rfl

theorem smul_eq_act (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [TensorProduct.smul_tmul', act_tmul, AlgEquiv.smul_def]
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _)]

scoped instance instAct : MulSemiringAction (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) :=
  { TensorProduct.leftDistribMulAction with
    smul_one := fun σ => by rw [smul_eq_act, map_one]
    smul_mul := fun σ x y => by rw [smul_eq_act, smul_eq_act, smul_eq_act, map_mul] }

theorem smul_def (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := smul_eq_act R σ x

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance smulComm : SMulCommClass (Ω ≃ₐ[k] Ω) R (Ω ⊗[k] R) where
  smul_comm σ r x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_def, smul_def, map_mul]
    congr 1
    change act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp

theorem repr_act {ι : Type} (b : Module.Basis ι k R) (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) (i : ι) :
    (Algebra.TensorProduct.basis Ω b).repr (act R σ x) i = σ ((Algebra.TensorProduct.basis Ω b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    simp only [act_tmul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, AlgEquiv.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

variable [IsGalois k Ω]

open Classical in
theorem isInvariant : Algebra.IsInvariant R (Ω ⊗[k] R) (Ω ≃ₐ[k] Ω) where
  isInvariant x hx := by
    let b := Module.Free.chooseBasis k R
    let B := Algebra.TensorProduct.basis Ω b
    have hc : ∀ i, ∃ c : k, algebraMap k Ω c = B.repr x i := fun i =>
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 fun σ => by
        rw [← repr_act R b σ x]
        exact congrArg (fun y => B.repr y i) (hx σ)
    let φ : Ω → k := fun ω => if h : ∃ c : k, algebraMap k Ω c = ω then h.choose else 0
    have hφ0 : φ 0 = 0 := by
      simp only [φ]
      split_ifs with h
      · exact (algebraMap k Ω).injective (h.choose_spec.trans (map_zero _).symm)
      · rfl
    have hφ : ∀ i, algebraMap k Ω (φ (B.repr x i)) = B.repr x i := fun i => by
      simp only [φ, dif_pos (hc i)]
      exact (hc i).choose_spec
    let f : Module.Free.ChooseBasisIndex k R →₀ k := Finsupp.mapRange φ hφ0 (B.repr x)
    refine ⟨b.repr.symm f, B.repr.injective ?_⟩
    ext i
    change B.repr (1 ⊗ₜ (b.repr.symm f)) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Module.Basis.repr_symm_apply,
      Module.Basis.repr_linearCombination]
    exact hφ i

omit [IsGalois k Ω] in
theorem isOpen_stabilizer [Algebra.IsIntegral k Ω] (x : Ω ⊗[k] R) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[k] Ω) x : Set (Ω ≃ₐ[k] Ω)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ => by rw [MulAction.mem_stabilizer_iff, smul_zero]) ?_
    rw [Subgroup.coe_top]; exact isOpen_univ
  | tmul a r =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) a) ?_ (stabilizer_isOpen_of_isIntegral a)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    rw [smul_def, act_tmul]
    exact congrArg (· ⊗ₜ[k] r) hσ
  | add x y hx hy =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) x ⊓ MulAction.stabilizer (Ω ≃ₐ[k] Ω) y)
      ?_ (by rw [Subgroup.coe_inf]; exact hx.inter hy)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    rw [smul_add, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).1,
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).2]

theorem exists_comap_eq (P Q : Ideal (Ω ⊗[k] R)) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom =
      Q.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom) :
    ∃ σ : Ω ≃ₐ[k] Ω, Q = P.comap (act R σ).toRingEquiv.toRingHom := by
  let _ : TopologicalSpace (Ω ⊗[k] R) := ⊥
  have : DiscreteTopology (Ω ⊗[k] R) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    exact isOpen_stabilizer R
  have := isInvariant (k := k) (Ω := Ω) R
  have := smulComm (k := k) (Ω := Ω) R
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R) (G := Ω ≃ₐ[k] Ω) P Q h
  refine ⟨g⁻¹, ?_⟩
  rw [hg, Ideal.pointwise_smul_eq_comap]
  ext x
  simp only [Ideal.mem_comap]
  have e : (MulSemiringAction.toRingAut (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) g).symm x = act R g⁻¹ x := by
    rw [← smul_def]; rfl
  rw [e]; rfl

end CrystallineSemistableComparison.GeoA
end
end
