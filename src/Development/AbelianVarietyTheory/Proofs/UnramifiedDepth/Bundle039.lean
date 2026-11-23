module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReciprocityTheory.DualLattices.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.IsLocalOfIntegers
import ReciprocityTheory.DualLattices.Bundle013
import ReciprocityTheory.DualLattices.UpSmith
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hasLen_of_fp {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.FinitePresentation O M) : ∃ x, HasLen v O M x := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hk : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hk
  have hsmith : ∀ (b : ℕ) {idx : Type} [Fintype idx] (g : idx → Fin b → O),
      ∃ c : Fin b → O, Nonempty (((Fin b → O) ⧸ Submodule.span O (Set.range g)) ≃ₗ[O]
        ((i : Fin b) → O ⧸ Ideal.span {c i})) := by
    intro b
    induction b with
    | zero =>
      intro idx _ g
      exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | succ b ih =>
      intro idx _ g
      obtain ⟨i0, a, u, s, hu, hau, hs, -, -⟩ := Smith.exists_pivot hv g
      obtain ⟨e1⟩ := Smith.pivot_equiv g i0 a u s hu hau hs
      obtain ⟨c, ⟨e2⟩⟩ := ih (fun j => Fin.removeNth i0 (g j - s j • a • u))
      exact ⟨Fin.cons a c, ⟨(e1.trans ((LinearEquiv.refl O _).prodCongr e2)).trans
        (Smith.consEquiv a c)⟩⟩
  obtain ⟨c, e⟩ := hsmith n g
  have hc : HasLen v O ((Fin n → O) ⧸ Submodule.span O (Set.range g))
      (∏ i, v (algebraMap O C (c i))) := ⟨n, c, e, rfl⟩
  exact ⟨_, hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hg).trans
    (f.quotKerEquivOfSurjective hf)).symm hc⟩

private theorem hasLen_mono {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') {z z' : NNReal} (hf : Function.Surjective f)
    (hz : HasLen v R M z) (hz' : HasLen v R M' z') : z ≤ z' := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  obtain ⟨r, q, ⟨e'⟩, hzq⟩ := hz'
  let π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q t}) := e'.toLinearMap ∘ₗ f
  have hπ : Function.Surjective π := e'.surjective.comp hf
  let y : Fin m → ((t : Fin r) → R ⧸ Ideal.span {q t}) :=
    fun i => π (e.symm (Pi.single i 1))
  have hspan : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := hπ w
    have hx := eq_sum_single c (e x)
    have : x = ∑ i, (Quotient.out (e x i) : R) • e.symm (Pi.single i 1) := by
      calc x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = e.symm (∑ i, (Quotient.out (e x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
            (i : Fin m) → R ⧸ Ideal.span {c i})) := congrArg e.symm hx
        _ = _ := by simp only [map_sum, map_smul]

    rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • y i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, y]
      rw [← map_smul, ← map_smul, single_smul_self, map_zero, map_zero]
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdet := det_mem_span_prod r q m y hspan (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at hdet
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hdet
  have hle := hv.le_of_dvd (⟨w, by rw [← hw, mul_comm]⟩ : ∏ t : Fin r, q t ∣ ∏ i, c i)
  rw [map_prod, map_prod, map_prod, map_prod] at hle
  rw [← hzc, ← hzq]
  exact hle

private theorem fp_quot {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (n : ℕ) (M N : Submodule O (Fin n → O)) (hM : M.FG)
    (hN : N.FG) (hle : N ≤ M) : Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O M := Module.Finite.iff_fg.2 hM
  have : Module.Flat O M := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O M := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  refine Module.finitePresentation_of_surjective (N.comap M.subtype).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  refine Submodule.fg_of_fg_map_injective M.subtype M.injective_subtype ?_
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle]

theorem hasLen_exists_mono_fp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∀ (M : Type) [AddCommGroup M] [Module O M], Module.FinitePresentation O M → ∃ x, HasLen v O M x) ∧ (∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (x x' : NNReal), Function.Surjective f → HasLen v O M x → HasLen v O M' x' → x ≤ x') ∧ ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M → Module.FinitePresentation O (M ⧸ N.comap M.subtype) :=
  fun _ _ _ _ _ _ hv => ⟨fun M _ _ h => hasLen_of_fp hv M h,
    fun _ _ _ _ _ _ f _ _ hf hx hx' => hasLen_mono hv f hf hx hx',
    fun n M N hM hN hle => fp_quot hv n M N hM hN hle⟩

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def latConv {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C) :
    (N → C) →ₗ[C] C where
  toFun f := φ (fun x => ψ (fun y => f (x + y)))
  map_add' f g := by
    rw [← map_add (f := _)]; congr 1; funext x
    rw [Pi.add_apply, ← map_add (f := _)]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x
    rw [Pi.smul_apply, ← map_smul]; rfl

private theorem latConv_sum {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C)
    {m : ℕ} (f : N → C) (g h : Fin m → N → C) (hf : ∀ x y, f (x + y) = ∑ i, g i x * h i y) :
    latConv φ ψ f = ∑ i, φ (g i) * ψ (h i) := by
  have h1 : ∀ x, (fun y => f (x + y)) = ∑ i, g i x • h i := by
    intro x; funext y; simp [hf, Finset.sum_apply]
  have h2 : (fun x => ψ (fun y => f (x + y))) = ∑ i, ψ (h i) • g i := by
    funext x; rw [h1]; simp [Finset.sum_apply, mul_comm]
  change φ (fun x => ψ (fun y => f (x + y))) = _
  rw [h2]; simp [mul_comm]

private theorem lat_bound {C V : Type} [Field C] [AddCommGroup V] [Module C V]
    (v : Valuation C NNReal) (S : Set V) {k : V} (hk : k ∈ Submodule.span C S) :
    ∃ M : NNReal, ∀ φ : V →ₗ[C] C, (∀ f ∈ S, v (φ f) ≤ 1) → v (φ k) ≤ M := by
  induction hk using Submodule.span_induction with
  | mem x hx => exact ⟨1, fun φ hφ => hφ x hx⟩
  | zero => exact ⟨0, fun φ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨max M M', fun φ hφ => ?_⟩
    rw [map_add (f := _)]
    exact (v.map_add _ _).trans (max_le_max (hM φ hφ) (hM' φ hφ))
  | smul c x _ hx =>
    obtain ⟨M, hM⟩ := hx
    refine ⟨v c * M, fun φ hφ => ?_⟩
    rw [map_smul, smul_eq_mul, map_mul]
    gcongr
    exact hM φ hφ

private theorem lat_dual {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {N : Type} (A : Submodule O (N → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (N → C)) = ⊤) (k : N → C)
    (hk : ∀ φ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (φ f) ≤ 1) → v (φ k) ≤ 1) : k ∈ A := by
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : N → C) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → N → C := fun i => (b i : N → C)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hb : ∀ i, bC i = w i := fun i => Module.Basis.mk_apply _ _ _
  have hco : ∀ i, ∀ f ∈ A, v (bC.coord i f) ≤ 1 := by
    intro i f hf
    rw [← hspR] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [← algebraMap_smul C c x, map_smul, smul_eq_mul, map_mul]
      exact mul_le_one' (hv.map_le_one c) hx
  rw [← bC.sum_repr k]
  refine A.sum_mem fun i _ => ?_
  obtain ⟨o, ho⟩ := hv.exists_of_le_one (hk _ (hco i))
  have ho' : bC.repr k i = algebraMap O C o := ho.symm
  rw [ho', algebraMap_smul, hb]
  exact A.smul_mem _ (b i).2

theorem character_mem_lattice_of_comul : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (N : Type) [AddCommMonoid N] [Finite N] (A : Submodule O (N → C)), A.FG → Submodule.span C (A : Set (N → C)) = ⊤ → (∀ f ∈ A, ∃ (m : ℕ) (g h : Fin m → N → C), (∀ i, g i ∈ A) ∧ (∀ i, h i ∈ A) ∧ ∀ x y, f (x + y) = ∑ i, g i x * h i y) → (∀ f ∈ A, ∃ o : O, algebraMap O C o = f 0) → ∀ κ : N → C, κ 0 = 1 → (∀ x y, κ (x + y) = κ x * κ y) → κ ∈ A := by
  intro C _ v O _ _ hv N _ _ A hfg hsp hco h0 k hk0 hk
  refine lat_dual v hv A hfg hsp k fun φ hφ => ?_
  obtain ⟨M, hM⟩ := lat_bound v (A : Set (N → C)) (k := k) (by rw [hsp]; trivial)
  have hpow : ∀ n : ℕ, ∃ ψ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (ψ f) ≤ 1) ∧ ψ k = φ k ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨LinearMap.proj 0, fun f hf => ?_, by simpa using hk0⟩
      obtain ⟨o, ho⟩ := h0 f hf
      rw [LinearMap.proj_apply, ← ho]
      exact hv.map_le_one o
    | succ n ih =>
      obtain ⟨ψ, hψ, hψk⟩ := ih
      refine ⟨latConv ψ φ, fun f hf => ?_, ?_⟩
      · obtain ⟨m, g, h, hg, hh, hf⟩ := hco f hf
        rw [latConv_sum ψ φ f g h hf]
        refine v.map_sum_le fun i _ => ?_
        rw [map_mul]
        exact mul_le_one' (hψ _ (hg i)) (hφ _ (hh i))
      · rw [latConv_sum ψ φ k (fun _ : Fin 1 => k) (fun _ => k) (by simpa using hk)]
        simp [hψk, pow_succ]
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  obtain ⟨ψ, hψ, hψk⟩ := hpow n
  have := hM ψ hψ
  rw [hψk, map_pow] at this
  exact absurd hn (not_lt.2 this)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem squarefree_map_minpoly_int (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Finite ℤ OE] (a : OE) :
    Squarefree ((minpoly ℤ a).map (Int.castRingHom C)) := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : Irreducible (minpoly ℤ a) := minpoly.irreducible hi
  have h2 : Irreducible ((minpoly ℤ a).map (algebraMap ℤ ℚ)) :=
    ((minpoly.monic hi).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp h1
  have h3 := (h2.separable.map (f := algebraMap ℚ C)).squarefree
  rw [Polynomial.map_map] at h3
  have h4 : (algebraMap ℚ C).comp (algebraMap ℤ ℚ) = Int.castRingHom C := RingHom.ext_int _ _
  rwa [h4] at h3

private theorem aeval_map_minpoly_int (C : Type) [Field C] (OE : Type)
    [CommRing OE] (A : Type) [Ring A] [Algebra C A] (ρ : OE →+* A) (a : OE) :
    Polynomial.aeval (ρ a) ((minpoly ℤ a).map (Int.castRingHom C)) = 0 := by
  have h4 : Int.castRingHom C = algebraMap ℤ C := RingHom.ext_int _ _
  rw [h4, Polynomial.aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at this
  exact this

private theorem finite_ringHom_order (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    Finite (OE →+* C) := by
  classical
  let b := Module.Free.chooseBasis ℤ OE
  let p : OE → Polynomial C := fun a => (minpoly ℤ a).map (Int.castRingHom C)
  have hfin : ∀ a, Finite ((p a).rootSet C) := fun a => (Polynomial.rootSet_finite _ _).to_subtype
  let F : (OE →+* C) → ∀ i, (p (b i)).rootSet C := fun τ i =>
    ⟨τ (b i), Polynomial.mem_rootSet.mpr
      ⟨(squarefree_map_minpoly_int C OE (b i)).ne_zero, aeval_map_minpoly_int C OE C τ (b i)⟩⟩
  refine Finite.of_injective F fun τ σ h => ?_
  have : τ.toAddMonoidHom.toIntLinearMap = σ.toAddMonoidHom.toIntLinearMap :=
    b.ext fun i => congrArg Subtype.val (congrFun h i)
  exact RingHom.ext fun a => LinearMap.congr_fun this a

private theorem mem_iSup_of_eigenvector (C : Type) [Field C] (OE : Type) [CommRing OE]
    (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V) (χ : OE → C) (x : V)
    (hx : ∀ a, ρ a x = χ a • x) :
    x ∈ ⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a) := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hinj : Function.Injective fun c : C => c • x := smul_left_injective C h0
  let τ : OE →+* C :=
    { toFun := χ
      map_one' := hinj (by simp only [← hx, map_one, one_smul, Module.End.one_apply])
      map_mul' := fun a b => hinj (by
        simp only
        rw [← hx, map_mul, Module.End.mul_apply, hx b, map_smul, hx a, smul_smul, mul_comm])
      map_zero' := hinj (by simp only [← hx, map_zero, zero_smul, LinearMap.zero_apply])
      map_add' := fun a b => hinj (by
        simp only
        rw [← hx, map_add (f := _), LinearMap.add_apply, hx a, hx b, add_smul]) }
  refine Submodule.mem_iSup_of_mem τ ((Submodule.mem_iInf _).mpr fun a => ?_)
  exact Module.End.mem_eigenspace_iff.mpr (hx a)

theorem order_rep_diagonalisable : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], Finite (OE →+* C) ∧ ∀ (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V), iSupIndep (fun τ : OE →+* C => ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) ∧ (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) = ⊤ := by
  intro C _ _ _ OE _ _ _ _ _
  refine ⟨finite_ringHom_order C OE, fun V _ _ ρ => ⟨?_, ?_⟩⟩
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : OE => ρ a)
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
    have h2 := h.comp (f := fun τ : OE →+* C => (τ : OE → C)) DFunLike.coe_injective
    refine h2.mono fun τ => ?_
    exact iInf_mono fun a => (Module.End.genEigenspace (ρ a) (τ a)).mono le_top
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have hss : ∀ a, (ρ a).IsSemisimple := fun a =>
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero (squarefree_map_minpoly_int C OE a)
        (aeval_map_minpoly_int C OE _ ρ a)
    rw [eq_top_iff]
    rintro v -
    let W : Submodule C V := Submodule.span C (Set.range fun a : OE => ρ a v)
    have hW : ∀ a, W ∈ (ρ a).invtSubmodule := by
      intro a
      rw [Module.End.mem_invtSubmodule, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine Submodule.subset_span ⟨a * b, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    have hfin : FiniteDimensional C W := by
      let b := Module.Free.chooseBasis ℤ OE
      have hle : W ≤ Submodule.span C (Set.range fun i => ρ (b i) v) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
        simp only [SetLike.mem_coe]
        induction ha using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add (f := _), LinearMap.add_apply]
          exact Submodule.add_mem _ hx hy
        | smul n x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply]
          exact zsmul_mem hx n
      have : FiniteDimensional C (Submodule.span C (Set.range fun i => ρ (b i) v)) :=
        FiniteDimensional.span_of_finite C (Set.finite_range _)
      exact Submodule.finiteDimensional_of_le hle
    let f : OE → Module.End C W := fun a => (ρ a).restrict (hW a)
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => LinearMap.restrict_commute (hcomm a b) (hW a) (hW b))
      (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
    have hv : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
    have hle : (⊤ : Submodule C W) ≤ Submodule.comap W.subtype
        (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) := by
      rw [← htop]
      refine iSup_le fun χ x hx => ?_
      refine mem_iSup_of_eigenvector C OE V ρ χ x fun a => ?_
      have h1 := (Submodule.mem_iInf _).mp hx a
      have h2 : (f a).IsSemisimple := (hss a).restrict (hW a)
      rw [h2.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
        Module.End.mem_eigenspace_iff] at h1
      exact congrArg Subtype.val h1
    exact hle (Submodule.mem_top (x := (⟨v, hv⟩ : W)))

end GlobalTheory
end
