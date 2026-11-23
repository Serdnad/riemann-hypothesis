module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Mathlib.RingTheory.Flat.Basic
public import ReciprocityTheory.DualLattices.Bundle002
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mj

variable {R : Type} [CommRing R]

theorem exists_dual_family (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    ∃ (n : ℕ) (l : Fin n → N →ₗ[R] R) (b : Fin n → N), ∀ a, ∑ i, l i a • b i = a := by
  classical
  obtain ⟨n, p, g, -, -, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  refine ⟨n, fun i => (LinearMap.proj i).comp g, fun i => p fun j => if i = j then 1 else 0, fun a => ?_⟩
  have hx : p (g a) = a := LinearMap.congr_fun hpg a
  rw [LinearMap.pi_apply_eq_sum_univ p (g a)] at hx
  exact hx

variable {X Y Z : Type}

def pspan (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) : Submodule R (X × Y → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ B, g = fun z => a z.1 * b z.2}

theorem mul_mem_pspan {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {a : X → R} {b : Y → R}
    (ha : a ∈ A) (hb : b ∈ B) : (fun z : X × Y => a z.1 * b z.2) ∈ pspan A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem pspan_comp {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} (N : Submodule R (Z → R))
    (σ : Z → X × Y) (h : ∀ a ∈ A, ∀ b ∈ B, (fun z => a (σ z).1 * b (σ z).2) ∈ N) {g : X × Y → R}
    (hg : g ∈ pspan A B) : (fun z => g (σ z)) ∈ N := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact h a ha b hb
  | zero => exact N.zero_mem
  | add g g' _ _ h h' => exact N.add_mem h h'
  | smul r g _ h => exact N.smul_mem r h

theorem slice_mem {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {g : X × Y → R}
    (hg : g ∈ pspan A B) (y : Y) : (fun x => g (x, y)) ∈ A :=
  pspan_comp (Subalgebra.toSubmodule A) (fun x => (x, y)) (fun a ha b _ => by
    have := A.smul_mem ha (b y)
    rw [Subalgebra.mem_toSubmodule]
    convert this using 1
    funext x
    simp [mul_comm]) hg

theorem mem_pspan_of {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} [Module.Finite R A]
    [Module.Projective R A] {g : X × Y → R} (h1 : ∀ y, (fun x => g (x, y)) ∈ A)
    (h2 : ∀ l : A →ₗ[R] R, (fun y => l ⟨_, h1 y⟩) ∈ B) : g ∈ pspan A B := by
  obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
  have := Submodule.sum_mem (pspan A B) (t := Finset.univ) fun i _ => mul_mem_pspan (b i).2 (h2 (l i))
  convert this using 1
  funext z
  have e := congrFun (congrArg Subtype.val (h ⟨_, h1 z.2⟩)) z.1
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← e]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_tensor_equiv (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) [Module.Finite R A]
    [Module.Projective R A] (E : X × Y ≃ Z) (C : Subalgebra R (Z → R))
    (hC : ∀ f, f ∈ C ↔ (fun z => f (E z)) ∈ pspan A B) :
    ∃ e : A ⊗[R] B ≃ₐ[R] C, ∀ (a : A) (b : B) (x : X) (y : Y), (e (a ⊗ₜ b)).1 (E (x, y)) = a.1 x * b.1 y := by
  let p : A →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : X => R) (E.symm z).1).comp A.val
  let q : B →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : Y => R) (E.symm z).2).comp B.val
  let m : A ⊗[R] B →ₐ[R] (Z → R) := Algebra.TensorProduct.lift p q fun _ _ => Commute.all _ _
  have hm : ∀ (a : A) (b : B) z, m (a ⊗ₜ b) (E z) = a.1 z.1 * b.1 z.2 := fun a b z => by
    simp [m, p, q]
  have hmem : ∀ w, m w ∈ C := fun w => by
    induction w with
    | tmul a b =>
      rw [hC]
      simp only [hm]
      exact mul_mem_pspan a.2 b.2
    | add a b ha hb => rw [map_add (f := _)]; exact C.add_mem ha hb
  have hinj : Function.Injective m := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
    let c : (A →ₗ[R] R) → A ⊗[R] B →ₗ[R] B := fun l => (TensorProduct.lid R B).toLinearMap ∘ₗ l.rTensor B
    let s : Y → A ⊗[R] B →ₗ[R] A := fun y =>
      (TensorProduct.rid R A).toLinearMap ∘ₗ ((LinearMap.proj y).comp B.val.toLinearMap).lTensor A
    have h1 : ∀ y x w, (s y w).1 x = m w (E (x, y)) := fun y x w => by
      induction w with
      | tmul a b => rw [hm]; simp [s, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h2 : ∀ l y w, (c l w).1 y = l (s y w) := fun l y w => by
      induction w with
      | tmul a b => simp [s, c, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h3 : ∀ w, ∑ i, b i ⊗ₜ c (l i) w = w := fun w => by
      induction w with
      | tmul a b' =>
        conv_rhs => rw [← h a, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb => simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib, ha, hb]
    have h4 : ∀ y, s y w = 0 := fun y => Subtype.ext (funext fun x => by rw [h1, hw]; rfl)
    have h5 : ∀ l, c l w = 0 := fun l => Subtype.ext (funext fun y => by rw [h2, h4, map_zero]; rfl)
    rw [← h3 w]
    simp [h5]
  refine ⟨AlgEquiv.ofBijective (m.codRestrict C hmem) ⟨fun u v huv => hinj (congrArg Subtype.val huv), ?_⟩,
    fun a b x y => hm a b (x, y)⟩
  rintro ⟨f, hf⟩
  have := pspan_comp (LinearMap.range m.toLinearMap) E.symm
    (fun a ha b hb => ⟨(⟨a, ha⟩ : A) ⊗ₜ (⟨b, hb⟩ : B), funext fun z => by
      have := hm ⟨a, ha⟩ ⟨b, hb⟩ (E.symm z)
      rwa [E.apply_symm_apply] at this⟩) ((hC f).1 hf)
  obtain ⟨w, hw⟩ := this
  refine ⟨w, Subtype.ext ?_⟩
  simp only [E.apply_symm_apply] at hw
  exact hw

variable {T H : Type} [CommGroup T] [CommGroup H]

theorem res_mem (ι : H →* T) {A : Subalgebra R (T → R)} {f : T → R} (hf : f ∈ A) :
    (fun h => f (ι h)) ∈ resOrder ι A := ⟨f, hf, rfl⟩

theorem mem_quotOrder {π : T →* H} {A : Subalgebra R (T → R)} {g : H → R} :
    g ∈ quotOrder π A ↔ (fun t => g (π t)) ∈ A := Iff.rfl

def resMap (ι : H →* T) (A : Subalgebra R (T → R)) : A →ₗ[R] resOrder ι A where
  toFun f := ⟨fun h => f.1 (ι h), res_mem ι f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resMap_surjective (ι : H →* T) (A : Subalgebra R (T → R)) : Function.Surjective (resMap ι A) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem res_hopf {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    (hp : Module.Projective R (resOrder ι A)) : IsHopfOrder (resOrder ι A) := by
  have := hA.finite
  refine ⟨Module.Finite.of_surjective _ (resMap_surjective ι A), hp, ?_, ?_, ?_⟩
  · obtain ⟨d, hd, h⟩ := hA.full
    refine ⟨d, hd, fun f => ⟨_, h (Function.extend ι f 0), ?_⟩⟩
    funext x
    change d * Function.extend ι f 0 (ι x) = d * f x
    rw [hι.extend_apply]
  · rintro _ ⟨f, hf, rfl⟩
    have := pspan_comp (prodSpan (resOrder ι A)) (fun z : H × H => (ι z.1, ι z.2))
      (fun a ha b hb => mul_mem_pspan (res_mem ι ha) (res_mem ι hb)) (hA.comul f hf)
    simp only [← map_mul] at this
    exact this
  · rintro _ ⟨f, hf, rfl⟩
    have := res_mem ι (hA.inv f hf)
    simp only [← map_inv] at this
    exact this

theorem res_hopf_of_section {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)}
    (hA : IsHopfOrder A) (s : (H → R) →ₗ[R] (T → R)) (hs : ∀ f ∈ A, s (fun h => f (ι h)) ∈ A)
    (hs' : ∀ g h, s g (ι h) = g h) : IsHopfOrder (resOrder ι A) := by
  have := hA.projective
  refine res_hopf hι hA (Module.Projective.of_split (M := A)
    (LinearMap.codRestrict (Subalgebra.toSubmodule A) (s ∘ₗ (resOrder ι A).val.toLinearMap) ?_) (resMap ι A) ?_)
  · rintro ⟨_, f, hf, rfl⟩
    exact hs f hf
  · ext g h
    exact hs' g h

end PositivityTheory.HtPt.Mj
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem ext_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  let S : Submonoid (T → R') :=
    { carrier := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}
      one_mem' := ⟨1, one_mem A, funext fun t => by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
        exact ⟨f * f', mul_mem hf hf', funext fun t => by simp⟩ }
  have h := Algebra.adjoin_eq_span R' (S : Set (T → R'))
  rw [Submonoid.closure_eq] at h
  exact (Subalgebra.mem_toSubmodule _).symm.trans (h ▸ Iff.rfl)

theorem mem_descent : ∀ (R : Type) [CommRing R] (ι : Type) [Finite ι] (N : Submodule R (ι → R)) (f : ι → R), (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ (fun i => algebraMap R R' (f i)) ∈ Submodule.span R' {g : ι → R' | ∃ n ∈ N, g = fun i => algebraMap R R' (n i)}) → f ∈ N := by
  intro R _ ι _ N f h
  classical
  let _ := Fintype.ofFinite ι
  let q : (ι → R) ⧸ N := N.mkQ f
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R _ q)
  by_contra hf
  have hI : I ≠ ⊤ := fun hI => hf (by
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : R) • q = 0 := h1
    rw [one_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero N).1 h2)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨R', _, _, _, hflat, hc, hmem⟩ := h P hP
  let ψ : (ι → R') →ₗ[R'] R' ⊗[R] ((ι → R) ⧸ N) :=
    (N.mkQ.baseChange R') ∘ₗ (TensorProduct.piScalarRight R R' R' ι).symm.toLinearMap
  have hψ : ∀ n : ι → R, ψ (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ N.mkQ n := fun n => by
    have : (TensorProduct.piScalarRight R R' R' ι).symm (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ n := by
      rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [Algebra.algebraMap_eq_smul_one]
    show (N.mkQ.baseChange R') ((TensorProduct.piScalarRight R R' R' ι).symm _) = _
    rw [this, LinearMap.baseChange_tmul]
  have h0 : (1 : R') ⊗ₜ[R] q = 0 := by
    rw [← hψ]
    refine (Submodule.span_le (p := LinearMap.ker ψ)).2 ?_ hmem
    rintro _ ⟨n, hn, rfl⟩
    show ψ _ = 0
    rw [hψ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hn, tmul_zero]
  let g : (R ⧸ I) →ₗ[R] ((ι → R) ⧸ N) := I.liftQ (LinearMap.toSpanSingleton R _ q) le_rfl
  have hg : Function.Injective g := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have h1 : (1 : R') ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := R') g hg
    rw [LinearMap.lTensor_tmul, map_zero, ← h0]
    congr 1
    exact one_smul R q
  let k := R' ⧸ IsLocalRing.maximalIdeal R'
  let a : (R ⧸ I) →ₗ[R] k := I.liftQ (Algebra.linearMap R k) fun r hr => by
    have : r ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := hc ▸ hle hr
    exact Ideal.Quotient.eq_zero_iff_mem.2 this
  have h2 := congrArg (LinearMap.mul' R k ∘ₗ
    TensorProduct.map (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R')).toLinearMap a) h1
  rw [map_zero, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply] at h2
  have h3 : a (Submodule.Quotient.mk 1) = 1 := map_one (algebraMap R k)
  rw [h3, mul_one] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R').ne_top
    ((Ideal.eq_top_iff_one _).2 (Ideal.Quotient.eq_zero_iff_mem.1 h2))

end PositivityTheory.HtPt.Htat
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Mk

theorem bt_pgsh : ∀ (R C : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field C] [Algebra R C], Function.Injective (algebraMap R C) → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (A : Subalgebra R (Multiplicative N → R)), IsHopfOrder A → ∃ AA : ReciprocityTheory.PGsh.L2.HopfOrder R (C := C) N, ∀ f : N → C, f ∈ AA.carrier ↔ ∃ g ∈ A, ∀ x, f x = algebraMap R C (g (Multiplicative.ofAdd x)) := by
  intro R C _ _ _ _ _ hinj N _ _ _ A hA
  classical
  let φ : (Multiplicative N → R) →ₗ[R] (N → C) :=
    { toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x))
      map_add' := by
        intro g h
        funext x
        simp
      map_smul' := by
        intro r g
        funext x
        simp [Algebra.smul_def] }
  have hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x)) := fun _ _ => rfl
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, hd0, hd⟩ := hA.full
  have hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Multiplicative.toAdd
  have hrank : Module.finrank R A = Fintype.card N := by
    apply le_antisymm
    · rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective
    · let sc : (Multiplicative N → R) →ₗ[R] A :=
        { toFun := fun f => ⟨d • f, hd f⟩
          map_add' := fun f g => Subtype.ext (smul_add d f g)
          map_smul' := fun r f => Subtype.ext (smul_comm d r f) }
      have hsc : Function.Injective sc := by
        intro f g hfg
        have h2 : d • f = d • g := congrArg Subtype.val hfg
        exact smul_right_injective _ hd0 h2
      rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective hsc
  let b : Module.Basis N R A := (Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm
  refine ⟨{ carrier := (Subalgebra.toSubmodule A).map φ
            lat := ?_
            le_int := ?_
            one_mem := ?_
            mul_mem := ?_
            comul := ?_
            antipode := ?_ }, ?_⟩
  · refine ⟨fun x j => φ (b j) x, ?_, ?_⟩
    · let M : Matrix N N R := fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)
      have hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det := by
        rw [RingHom.map_det]
        rfl
      rw [hdet]
      apply isUnit_iff_ne_zero.mpr
      rw [map_ne_zero_iff _ hinj]
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      have hsum : ∑ j, v j • b j = 0 := by
        apply Subtype.ext
        funext t
        have h3 := congrFun hv (Multiplicative.toAdd t)
        simpa [Matrix.mulVec, dotProduct, M, mul_comm] using h3
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)
    · apply le_antisymm
      · rintro f ⟨g, hg, rfl⟩
        have hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j := (b.sum_repr _).symm
        have hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R) := by
          have h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R)
              = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R) := congrArg Subtype.val hg'
          rw [AddSubmonoidClass.coe_finsetSum] at h4
          exact h4

        rw [hgs, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨b j, (b j).2, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ x
    exact ⟨g (Multiplicative.ofAdd x), rfl⟩
  · refine ⟨1, A.one_mem, ?_⟩
    funext x
    simp [hφ]
  · rintro f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    refine ⟨f' * g', A.mul_mem hf' hg', ?_⟩
    funext x
    simp [hφ]
  · rintro f ⟨g, hg, rfl⟩
    let ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C) :=
      { toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2))
        map_add' := by
          intro F G
          funext p
          simp
        map_smul' := by
          intro r F
          funext p
          simp [Algebra.smul_def] }
    have hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤
        (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ := by
      rw [GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      apply Submodule.subset_span
      refine ⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩
      funext p
      simp [hφ, ψ]
    have h5 := hle (hA.comul g hg)
    rw [Submodule.mem_comap] at h5
    convert h5 using 1
    funext p
    simp [hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]
  · rintro f ⟨g, hg, rfl⟩
    refine ⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩
    funext x
    simp [hφ]
  · intro f
    show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun x => rfl⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg, funext fun x => (hfg x).symm⟩

end PositivityTheory.HtPt.Mk
end

section

namespace PositivityTheory.HtPt.Mi

theorem algHom_of_system : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  intro R A B _ _ _ _ _ _ _ I _ f hf
  have := GlobalTheory.isAdicComplete_map_of_finite I A
  let J := I.map (algebraMap R A)
  have hJ : ∀ e, (I ^ e).map (algebraMap R A) = J ^ e := fun e => Ideal.map_pow _ _ _
  have ha : StrictMono fun e : ℕ => e + 1 := fun _ _ h => Nat.succ_lt_succ h
  let f' : ∀ e : ℕ, B →+* A ⧸ J ^ (e + 1) := fun e => (Ideal.quotEquivOfEq (hJ (e + 1))).toRingHom.comp (f e).toRingHom
  have key : ∀ e (a : A) (b : B), Ideal.Quotient.mk _ a = f' e b ↔ Ideal.Quotient.mk _ a = f e b := fun e a b => by
    rw [← (Ideal.quotEquivOfEq (hJ (e + 1))).injective.eq_iff, Ideal.quotEquivOfEq_mk]
    rfl
  have hf' : ∀ {m}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f' (m + 1)) = f' m := fun {m} => by
    ext b
    obtain ⟨a, hb⟩ := Ideal.Quotient.mk_surjective (f' (m + 1) b)
    rw [RingHom.comp_apply, ← hb, ← (key m a b).2 (hf m b a ((key _ a b).1 hb))]
    rfl
  let g := IsAdicComplete.StrictMono.liftRingHom J ha f' hf'
  have hg : ∀ e b, Ideal.Quotient.mk _ (g b) = f' e b := fun e b =>
    IsAdicComplete.StrictMono.mk_liftRingHom J ha f' hf' b
  have ext : ∀ a a' : A, (∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a = Ideal.Quotient.mk (J ^ (e + 1)) a') → a = a' :=
    fun a a' h => congrFun (IsHausdorff.StrictMono.funext' J ha (f := fun _ : Unit => a) (g := fun _ => a')
      fun e _ => h e) ()
  refine ⟨{ g with commutes' := fun r => ext _ _ fun e => ?_ }, fun e b => (key e _ b).1 (hg e b),
    fun g' hg' => AlgHom.ext fun b => ext _ _ fun e => ?_⟩
  · refine (hg e _).trans ((key e _ _).2 ?_).symm
    rw [AlgHom.commutes]; rfl
  · exact ((key e _ b).2 (hg' e b)).trans (hg e b).symm

end PositivityTheory.HtPt.Mi
end
