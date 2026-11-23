module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptOrd_of :
    OrdCount → PtIdOfOrd := by
  intro hC l q n Y π T hO V _ _ _ _ hl y hy φ hφ I _ z hz
  apply hC
  obtain ⟨k, H, x, hk, x2, x3, hf, C, A, e, h1, h2, h3, h4⟩ := hO V hl y hy φ hφ
  exact ⟨k, H, x, hk, x2, x3, hf, C, A, fun j => (Equiv.ofBijective (z j) (hz j)).trans (e j),
    h1, h2, h3, fun j i => h4 j (z j i)⟩
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charAnn_of :
    CharOfAnn := by
  intro K _ n M s hcard hgen hann hdet
  classical
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  have hf : Function.Injective f := f.injective
  set M' : Matrix (Fin n) (Fin n) L := M.map f
  have hchar : M'.charpoly = M.charpoly.map f := Matrix.charpoly_map M f
  have hpmap : (rootPol s).map f = (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (s.map f)).prod := by
    simp [rootPol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hannL : Polynomial.aeval M' (rootPol s) = 0 := by
    have h1 : M' = (Algebra.ofId K L).mapMatrix M := by
      rw [AlgHom.mapMatrix_apply]; rfl
    rw [h1, Polynomial.aeval_algHom_apply, hann, map_zero]
  set R := M'.charpoly.roots
  have hmem : ∀ r ∈ R, r ∈ s.map f := by
    intro r hr
    have hroot : M'.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M').ne_zero).1 hr
    have hsp : r ∈ spectrum L M' := Matrix.mem_spectrum_of_isRoot_charpoly hroot
    have hev : Polynomial.eval r ((rootPol s).map f) ∈ spectrum L (Polynomial.aeval M' ((rootPol s).map f)) :=
      spectrum.subset_polynomial_aeval M' _ ⟨r, hsp, rfl⟩
    have hz : Polynomial.aeval M' ((rootPol s).map f) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]; exact hannL
    rw [hz] at hev
    have h0 : Polynomial.eval r ((rootPol s).map f) = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 hev) (by
        simpa using (isUnit_iff_ne_zero.2 hne).map (algebraMap L (Matrix (Fin n) (Fin n) L)))
    have hne0 : (rootPol s).map f ≠ 0 := by
      rw [hpmap]; exact (Polynomial.monic_multiset_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero
    have : r ∈ ((rootPol s).map f).roots := (Polynomial.mem_roots hne0).2 h0
    rwa [hpmap, Polynomial.roots_multiset_prod_X_sub_C] at this
  set g := Function.invFun f
  set t := R.map g
  have htR : t.map f = R := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro r hr
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (hmem r hr)
    exact Function.invFun_eq ⟨a, ha⟩
  have hRcard : R.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htcard : t.card = s.card := by simp [t, hRcard, hcard]
  have htsub : ∀ x ∈ t, x ∈ s := by
    intro x hx
    have : f x ∈ s.map f := hmem (f x) (by rw [← htR]; exact Multiset.mem_map_of_mem f hx)
    obtain ⟨a, ha, hax⟩ := Multiset.mem_map.1 this
    rw [← hf hax]; exact ha
  have htprod : t.prod = s.prod := by
    apply hf
    rw [map_multiset_prod, htR, ← Matrix.det_eq_prod_roots_charpoly, ← hdet, RingHom.map_det]
    rfl
  have hts : t = s := hgen t htcard htsub htprod
  apply Polynomial.map_injective f hf
  rw [← hchar, hpmap, ← hts, htR]
  exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M')
    (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charts_of :
    ChartsExist := by
  intro l Y hY J _ T y
  haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin
  let S : Set Y := {y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})
  have hS : S.Finite := (Set.finite_singleton y).union
    (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)
  obtain ⟨V, hV, hSV⟩ := hY hS.toFinset
  have hSV' : ∀ x ∈ S, x ∈ V := fun x hx => hSV x (hS.mem_toFinset.mpr hx)
  have hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ) :=
    isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl
  let O : Y.Opens := ⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyO : y ∈ O := by
    show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ
    rintro hy
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    apply hz
    show (T j).r z ∈ V
    exact hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))
  obtain ⟨U, hU, hyU, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  refine ⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩
  by_contra h
  have hz' : (T j).p z ∈ (O : Set Y) := hUO hz
  exact hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)
end

section

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

def Dinv (ρ : Representation L G V) : Submodule L (V ⊗[F] B) :=
  ⨅ g, LinearMap.ker (AlgebraTensorModule.map (ρ g) (σ g) - LinearMap.id)

theorem mem_Dinv {ρ : Representation L G V} {x : V ⊗[F] B} :
    x ∈ Dinv σ ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (σ g) x = x := by
  simp [Dinv, Submodule.mem_iInf, sub_eq_zero]


variable (L V) in
def onPer : End L (V ⊗[F] B) := AlgebraTensorModule.map LinearMap.id ψ

def admitted (e : ℕ) (ρ : Representation L G V) : Prop := finrank L (Dinv σ ρ) = e * finrank L V

def AnnD (q n : ℕ) (ρ : Representation L G V) (T : ℕ → End L V) : Prop :=
  ∀ x ∈ Dinv σ ρ, ∑ j ∈ Finset.range (n + 1),
    ((-1) ^ j * (q : ℤ) ^ (j.choose 2)) • AlgebraTensorModule.map (T j) (ψ ^ (n - j)) x = 0

def NilD (ρ : Representation L G V) (Q : Polynomial L) : Prop :=
  ∃ N : ℕ, ∀ x ∈ Dinv σ ρ, (Polynomial.aeval (onPer ψ L V) Q ^ N) x = 0


variable (L) in
def Bound (e : ℕ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U] (ρ : Representation L G U),
    Module.Finite L (Dinv σ ρ) ∧ finrank L (Dinv σ ρ) ≤ e * finrank L U

end

def Inter {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W) : Prop := ∀ g v, f (ρ g v) = ρ' g (f v)

def Subq {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) : Prop :=
  ∃ (U : Type) (_ : AddCommGroup U) (_ : Module L U) (ρU : Representation L G U) (i : U →ₗ[L] V) (p : U →ₗ[L] W),
    Inter ρU ρ i ∧ Function.Injective i ∧ Inter ρU ρ' p ∧ Function.Surjective p

def extRep {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] (L : Type) [Field L] [Algebra F L]
    (ρ : Representation F G V) : Representation L G (L ⊗[F] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one F V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def DinvExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (U V W : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W) (i : U →ₗ[L] V) (p : V →ₗ[L] W),
    Inter ρU ρV i → Inter ρV ρW p → Function.Injective i → Function.Exact i p → Module.Finite L (Dinv σ ρV) →
    (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) ≤ Dinv σ ρW ∧
    finrank L (Dinv σ ρV) = finrank L (Dinv σ ρU) +
      finrank L ((Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))

def AdmExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L] (e : ℕ),
    Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W), Inter ρ ρ' f →
    (Function.Injective f → admitted σ e ρ' → admitted σ e ρ) ∧
    (Function.Surjective f → admitted σ e ρ → admitted σ e ρ' ∧
      (Dinv σ ρ).map (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρ')

def NilEmb : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (ρ : Representation L G V)
    (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)] [∀ i, Module F (W i)]
    [∀ i, IsScalarTower F L (W i)] (ρ' : ∀ i, Representation L G (W i)) (f : ∀ i, V →ₗ[L] W i),
    (∀ i, Inter ρ (ρ' i) (f i)) → (∀ v, (∀ i, f i v = 0) → v = 0) →
    ∀ Q : Polynomial L, (∀ i, NilD σ ψ (ρ' i) Q) → NilD σ ψ ρ Q

def NilSubq : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (e : ℕ), Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρ : Representation L G V) (ρ' : Representation L G W), Subq ρ ρ' → admitted σ e ρ →
    admitted σ e ρ' ∧ ∀ Q : Polynomial L, NilD σ ψ ρ Q → NilD σ ψ ρ' Q

def NilOfAnn : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (ρ : Representation L G V) (q n : ℕ) (T : ℕ → End L V) (θ : ℕ → L), (∀ j g, Commute (T j) (ρ g)) → (∀ i j, Commute (T i) (T j)) →
    (∀ j ≤ n, IsNilpotent (T j - θ j • (1 : End L V))) → AnnD σ ψ q n ρ T → NilD σ ψ ρ (heckePol q n θ)

def AnnSub : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (U V : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] (ρU : Representation L G U) (ρ : Representation L G V) (i : U →ₗ[L] V), Inter ρU ρ i → Function.Injective i →
    ∀ (q n : ℕ) (TU : ℕ → End L U) (T : ℕ → End L V), (∀ j u, i (TU j u) = T j (i u)) → AnnD σ ψ q n ρ T → AnnD σ ψ q n ρU TU

def DinvExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (Dinv σ (extRep L ρ)).map (AlgebraTensorModule.assoc F F L L V B).toLinearMap = (Dinv σ ρ).baseChange L

def AnnExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (∀ e, admitted σ e ρ → admitted σ e (extRep L ρ)) ∧
    ∀ (q n : ℕ) (T : ℕ → End F V), AnnD σ ψ q n ρ T → AnnD σ ψ q n (extRep L ρ) fun j => (T j).baseChange L

def AnnPer : Prop :=
  ∀ (F G B B' : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (σ : G → End F B) (ψ : End F B) (σ' : G → End F B') (ψ' : End F B') (c : B →ₗ[F] B'), Function.Injective c →
    (∀ g b, c (σ g b) = σ' g (c b)) → (∀ b, c (ψ b) = ψ' (c b)) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ' L e →
    ∀ (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V] (ρ : Representation L G V),
      admitted σ e ρ → admitted σ' e ρ ∧ ∀ (q n : ℕ) (T : ℕ → End L V), AnnD σ ψ q n ρ T → AnnD σ' ψ' q n ρ T

def JoinAbs : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ L e →
    ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] (ρ : Representation F G V) (q n : ℕ) (T : ℕ → End F V),
      admitted σ e ρ → AnnD σ ψ q n ρ T →
    ∀ (U : Type) [AddCommGroup U] [Module L U] (ρU : Representation L G U) (i : U →ₗ[L] L ⊗[F] V) (TU : ℕ → End L U) (θ : ℕ → L),
      Inter ρU (extRep L ρ) i → Function.Injective i → (∀ j u, i (TU j u) = (T j).baseChange L (i u)) →
      (∀ j g, Commute (TU j) (ρU g)) → (∀ j j', Commute (TU j) (TU j')) → (∀ j ≤ n, IsNilpotent (TU j - θ j • (1 : End L U))) →
    ∀ (W : Type) [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] (ρW : Representation L G W)
      (I : Type) [Finite I] (C : I → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module L (C a)] (ρC : ∀ a, Representation L G (C a))
      (f : ∀ a, W →ₗ[L] C a), (∀ a, Subq ρU (ρC a)) → (∀ a, Inter ρW (ρC a) (f a)) → (∀ v, (∀ a, f a v = 0) → v = 0) →
      NilD σ ψ ρW (heckePol q n θ)

end UpperTheory.Gal.crystallineComparison
end
end
