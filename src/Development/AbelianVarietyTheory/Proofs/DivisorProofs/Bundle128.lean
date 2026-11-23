module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

section

open Matrix TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemRankStalk

theorem finrank_range_baseChange_eq {R S M : Type} [CommRing R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] (e : M →ₗ[R] M) (he : e ∘ₗ e = e) :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank S (S ⊗[R] LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj]

theorem finrank_range_map_eq_rankAtStalk (A : Type) [CommRing A] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (k : Type) [Field k] (g : A →+* k) :
    Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
      Module.rankAtStalk (LinearMap.range P.mulVecLin)
        (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  letI : Algebra A k := g.toAlgebra
  set e : (Fin n → A) →ₗ[A] (Fin n → A) := P.mulVecLin with he_def
  have he : e ∘ₗ e = e := by
    rw [he_def, ← Matrix.mulVecLin_mul, hP]

  let r : (Fin n → A) →ₗ[A] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[A] (Fin n → A) := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  haveI : Module.Projective A (LinearMap.range e) := Module.Projective.of_split i r hri

  have hst := Module.rankAtStalk_baseChange (R := A) (M := LinearMap.range e) (S := k) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hst
  have hcomap : PrimeSpectrum.comap (algebraMap A k) (⊥ : PrimeSpectrum k) =
      (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
    ext x
    change x ∈ Ideal.comap (algebraMap A k) (⊥ : Ideal k) ↔ x ∈ RingHom.ker g
    rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
    rfl
  rw [hcomap] at hst
  rw [← hst, ← finrank_range_baseChange_eq e he]

  let Φ : k ⊗[A] (Fin n → A) ≃ₗ[k] (Fin n → k) := TensorProduct.piScalarRight A k k (Fin n)
  have hΦ : ∀ x, Φ (e.baseChange k x) = (P.map g).mulVecLin (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      ext j
      simp [Φ, e, TensorProduct.piScalarRight_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hrange : LinearMap.range (P.map g).mulVecLin =
      (LinearMap.range (e.baseChange k)).map (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) := by
    have hc : (P.map g).mulVecLin ∘ₗ (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) =
        (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) ∘ₗ e.baseChange k :=
      LinearMap.ext fun x => (hΦ x).symm
    rw [← LinearMap.range_comp, ← hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range Φ)]
  rw [hrange, LinearEquiv.finrank_map_eq]
  rfl

end GlobalTheory.IdemRankStalk
end
end

section

open TensorProduct WithConv

namespace GlobalTheory.HopfShear

variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]


open Algebra.TensorProduct Bialgebra HopfAlgebra in
@[reducible] noncomputable def pointsGroup : Group (WithConv (A →ₐ[R] X)) where
  __ := (inferInstance : Monoid (WithConv (A →ₐ[R] X)))
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
  inv_mul_cancel f := by
    have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
    trans toConv <|
      ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
        (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (Bialgebra.comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp
      (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] X)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

attribute [local instance] pointsGroup

noncomputable def pre (f : B →ₐc[R] A) : WithConv (A →ₐ[R] X) →* WithConv (B →ₐ[R] X) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (x.ofConv.comp (f : B →ₐ[R] A))) fun x y => by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

noncomputable def post (h : X →ₐ[R] Y) : WithConv (A →ₐ[R] X) →* WithConv (A →ₐ[R] Y) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (h.comp x.ofConv)) fun x y => by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

theorem pre_apply (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := rfl

theorem conv_ext {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y :=
  ofConv_injective (AlgHom.ext h)

theorem shear (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by
  set S := AlgHom.range (f : B →ₐ[R] A) with hS
  set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI
  let l : WithConv (A →ₐ[R] A ⊗[S] A) := toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))
  let r : WithConv (A →ₐ[R] A ⊗[S] A) :=
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)
  let l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) := toConv (IsScalarTower.toAlgHom R A _)
  let p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) :=
    toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp
      (Ideal.Quotient.mkₐ R I))
  have hl : ∀ a, l.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hr : ∀ a, r.ofConv a = 1 ⊗ₜ a := fun a => rfl
  have hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a := fun a => rfl
  have hlr : pre f l = pre f r := conv_ext fun b => by
    rw [pre_apply, pre_apply, hl, hr]
    have := TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)
    simpa [Subalgebra.smul_def] using this
  have hpf : pre f p = 1 := conv_ext fun b => by
    rw [pre_apply, hp]
    have hb : b - algebraMap R B (Coalgebra.counit b) ∈
        RingHom.ker (Bialgebra.counitAlgHom R B) := by
      simp [RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)
      rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes] at h2
      exact h2
    rw [h1]
    exact (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _
  let g : A →ₐ[S] A ⊗[R] (A ⧸ I) :=
    { (l' * p).ofConv.toRingHom with
      commutes' := by
        rintro ⟨_, b, rfl⟩
        have h : pre f (l' * p) = pre f l' := by rw [map_mul, hpf, mul_one]
        have h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1 := congrArg (fun x => x.ofConv b) h
        exact h2 }
  let Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _
  have hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0 := by
    have h : pre f (l⁻¹ * r) = 1 := by rw [map_mul, map_inv, hlr, inv_mul_cancel]
    have : I ≤ RingHom.ker (l⁻¹ * r).ofConv := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      have h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b) :=
        congrArg (fun x => x.ofConv b) h
      have h3 : Coalgebra.counit (R := R) b = 0 := hb
      rw [h3, map_zero] at h2
      exact h2
    exact fun a ha => this ha
  let k : (A ⧸ I) →ₐ[R] A ⊗[S] A := Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk
  let Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _
  have hΦl : post (Φ.restrictScalars R) l = l' := conv_ext fun a => Φ.commutes a
  have hΦr : post (Φ.restrictScalars R) r = l' * p := conv_ext fun a => by
    change Φ (1 ⊗ₜ a) = g a
    simp [Φ, ← Algebra.TensorProduct.one_def]
  have hΨl : post (Ψ.restrictScalars R) l' = l := conv_ext fun a => Ψ.commutes a
  have hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r := conv_ext fun a => by
    change Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)
    simp [Ψ, ← Algebra.TensorProduct.one_def]
  have h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a := fun a => by
    have h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p := by
      rw [hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  have h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a := fun a => by
    have h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r := by
      rw [hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  refine ⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact h1 a
  · exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)

end GlobalTheory.HopfShear
end

section

open IsLocalRing

namespace GlobalTheory.CoordsAlg

noncomputable def cotFun {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) : Module.Dual R I.Cotangent :=
  ((I • ⊤ : Submodule A I).restrictScalars R).liftQ f (fun x hx => by
      refine LinearMap.mem_ker.mpr (hf x ?_)
      rw [← Ideal.toCotangent_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (I • ⊤ : Submodule A I)).symm.toLinearMap

theorem coords_of_derivation_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  intro R A _ _ _ _ _ _ e he hfree hfin n dv hadd hmul halg huniq
  set I := RingHom.ker e with hIdef
  let dH : Fin n → A →+ R := fun a => AddMonoidHom.mk' (dv a) (hadd a)
  have hdH : ∀ a x, dv a x = dH a x := fun _ _ => rfl
  have hsmul : ∀ a r x, dv a (algebraMap R A r * x) = r * dv a x := by
    intro a r x; rw [hmul, he, halg]; ring
  have hI2 : ∀ a x, x ∈ I ^ 2 → dv a x = 0 := by
    intro a x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro u hu v hv
      rw [hmul, (RingHom.mem_ker).1 hu, (RingHom.mem_ker).1 hv]; ring
    · intro u v hu hv; rw [hadd, hu, hv, add_zero]
  have hdec : ∀ x : A, x - algebraMap R A (e x) ∈ I := fun x => by
    simp [I, RingHom.mem_ker, he]
  let fa : Fin n → (I →ₗ[R] R) := fun a =>
    { toFun := fun x => dv a x
      map_add' := fun x y => hadd a x y
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, RingHom.id_apply, smul_eq_mul]
        exact hsmul a r x }
  let ℓ : Fin n → Module.Dual R I.Cotangent := fun a => cotFun I (fa a) (fun x hx => hI2 a x hx)
  have hℓ : ∀ a (x : I), ℓ a (I.toCotangent x) = dv a x := fun _ _ => rfl
  let Ψ : (Fin n → R) →ₗ[R] Module.Dual R I.Cotangent :=
    ∑ a, (LinearMap.proj a : (Fin n → R) →ₗ[R] R).smulRight (ℓ a)
  have hΨ : ∀ c (x : I), Ψ c (I.toCotangent x) = ∑ a, c a * dv a x := by
    intro c x
    simp [Ψ, LinearMap.sum_apply, hℓ]

  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∀ x : A, ∑ a, c a * dv a x = 0 := by
      intro x
      have hx := hΨ c ⟨_, hdec x⟩
      rw [hc] at hx
      have : ∀ a, dv a (x - algebraMap R A (e x)) = dv a x := by
        intro a; rw [hdH, map_sub, ← hdH, ← hdH, halg, sub_zero]
      simp only [this] at hx
      exact hx.symm
    obtain ⟨c0, -, hc0⟩ := huniq (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp)
      (fun _ => rfl)
    have h1 : c = c0 := hc0 c (fun x => (h0 x).symm)
    have h2 : (0 : Fin n → R) = c0 := hc0 0 (fun x => by simp)
    rw [h1, ← h2]
  have hΨsurj : Function.Surjective Ψ := by
    intro φ
    let D : A → R := fun x => φ (I.toCotangent ⟨_, hdec x⟩)
    have Dadd : ∀ x y, D (x + y) = D x + D y := by
      intro x y
      simp only [D, ← map_add (f := _)]
      congr 2
      ext; simp; ring
    have Dalg : ∀ r, D (algebraMap R A r) = 0 := by
      intro r
      simp only [D]
      have : (⟨_, hdec (algebraMap R A r)⟩ : I) = 0 := by ext; simp [he]
      rw [this, map_zero, map_zero]
    have Dmul : ∀ x y, D (x * y) = e x * D y + e y * D x := by
      intro x y
      have hsq : (x - algebraMap R A (e x)) * (y - algebraMap R A (e y)) ∈ I ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul (hdec x) (hdec y)
      have key : (⟨_, hdec (x * y)⟩ : I) = e x • (⟨_, hdec y⟩ : I) + e y • (⟨_, hdec x⟩ : I) +
          ⟨_, Ideal.pow_le_self two_ne_zero hsq⟩ := by
        ext
        simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
        ring
      have hw0 : I.toCotangent ⟨(x - algebraMap R A (e x)) * (y - algebraMap R A (e y)),
          Ideal.pow_le_self two_ne_zero hsq⟩ = 0 := (I.toCotangent_eq_zero _).2 hsq
      simp only [D]
      rw [key]
      simp only [map_add (f := _), LinearMap.map_smul_of_tower, hw0,
        map_zero, add_zero, map_smul, smul_eq_mul]
    obtain ⟨c, hc, -⟩ := huniq D Dadd Dmul Dalg
    refine ⟨c, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, ← hc]
    simp only [D]
    congr 2
    ext
    simp [(RingHom.mem_ker).1 x.2]
  let Ψe : (Fin n → R) ≃ₗ[R] Module.Dual R I.Cotangent :=
    LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨsingle : ∀ a, Ψ (Pi.single a 1) = ℓ a := by
    intro a
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, hℓ]
    simp [Pi.single_apply]
  let w : Fin n → I.Cotangent := fun i =>
    (Module.evalEquiv R I.Cotangent).symm
      ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ Ψe.symm.toLinearMap)
  have hw : ∀ a i, ℓ a (w i) = if a = i then 1 else 0 := by
    intro a i
    simp only [w, Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.proj_apply]
    have : Ψe.symm (ℓ a) = Pi.single a 1 := by
      rw [LinearEquiv.symm_apply_eq]; exact (hΨsingle a).symm
    rw [this]
    by_cases h : a = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  choose y hy using fun i => I.toCotangent_surjective (w i)
  have hzI : ∀ i, (y i : A) ∈ I := fun i => (y i).2
  have hdz : ∀ a i, dv a (y i : A) = if a = i then 1 else 0 := by
    intro a i; rw [← hℓ, hy, hw]
  have hImax : I ≤ maximalIdeal A := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [(RingHom.mem_ker).1 hx] at this
    exact not_isUnit_zero this
  have hnak : I ≤ Ideal.span (Set.range fun i => (y i : A)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian I) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      set s := ∑ a, algebraMap R A (dv a x) * (y a : A) with hs
      have hsI : s ∈ Ideal.span (Set.range fun i => (y i : A)) :=
        Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
      have hsI' : s ∈ I := Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hzI a)
      have hr : x - s ∈ I := I.sub_mem hx hsI'
      have hdr : ∀ b, dv b (x - s) = 0 := by
        intro b

        rw [hdH, map_sub, hs, map_sum]
        simp only [← hdH, hsmul, hdz]
        simp
      have hcot : I.toCotangent ⟨x - s, hr⟩ = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
        obtain ⟨c, rfl⟩ := hΨsurj φ
        rw [hΨ]; simp [hdr]
      have hsq : x - s ∈ I ^ 2 := (I.toCotangent_eq_zero _).1 hcot
      have hxs : x = s + (x - s) := by ring
      rw [hxs]
      refine Submodule.add_mem_sup hsI ?_
      rw [pow_two] at hsq
      exact Submodule.smul_mono_left hImax hsq
  refine ⟨fun i => (y i : A), fun i => (RingHom.mem_ker).1 (y i).2, hdz, ?_⟩
  have hmapR : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [he] at this
    exact (mem_maximalIdeal r).1 hr this
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : algebraMap R A (e x) ∈ maximalIdeal A := by
        have := (maximalIdeal A).sub_mem hx (hImax (hdec x))
        simpa using this
      exact (mem_maximalIdeal _).1 h1 (hu.map _)
    have hxe : x = algebraMap R A (e x) + (x - algebraMap R A (e x)) := by ring
    rw [hxe]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hex) (hnak (hdec x))
  · refine sup_le hmapR ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hImax (hzI i)

end GlobalTheory.CoordsAlg
end

section

namespace GlobalTheory.IntegralAddSum

theorem add_sum_integral {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x = ∑ m : Fin n, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ y = ∑ m : Fin n, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x + y = ∑ m : Fin n, gc (c m) * gk (b m) := by
  obtain ⟨n, c, b, hb, rfl⟩ := hx
  obtain ⟨n', c', b', hb', rfl⟩ := hy
  refine ⟨n + n', Fin.append c c', Fin.append b b', ?_, ?_⟩
  · intro m
    refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

end GlobalTheory.IntegralAddSum
end
