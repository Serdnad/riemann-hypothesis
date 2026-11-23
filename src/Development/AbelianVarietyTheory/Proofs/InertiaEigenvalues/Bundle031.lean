module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable

@[expose] public section

section

open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_finrank_le_finrank_inf_comap_sub_id :
    ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  intro k _ M W _ _ _ _ D R _ F B hRD hFD hBR hBF hnd

  let RV : Submodule k ↥D := R.comap D.subtype
  let T : ↥D →ₗ[k] ↥D := F.restrict hFD - LinearMap.id
  let Q : ↥D →ₗ[k] ↥D ⧸ RV := RV.mkQ ∘ₗ T

  let P : W →ₗ[k] Module.Dual k ↥D := (B ∘ₗ D.subtype).flip
  have hP : ∀ w, P w ∈ RV.dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hBR x.1 hx w
  let L : W →ₗ[k] Module.Dual k (↥D ⧸ RV) :=
    RV.dualCopairing ∘ₗ P.codRestrict RV.dualAnnihilator hP
  have hL : ∀ w (x : ↥D), L w (RV.mkQ x) = B x.1 w := fun _ _ => rfl

  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply hnd
    intro x hx
    have h := LinearMap.congr_fun hw (RV.mkQ ⟨x, hx⟩)
    rw [hL, LinearMap.zero_apply] at h
    exact h

  have hLQ : ∀ w, L w ∈ (LinearMap.range Q).dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨x, rfl⟩
    have hTx : ((T x : ↥D) : M) = F x.1 - x.1 := rfl
    show L w (RV.mkQ (T x)) = 0
    rw [hL, hTx, map_sub, LinearMap.sub_apply, hBF x.1 x.2, sub_self]
  have hW : finrank k W ≤ finrank k (LinearMap.range Q).dualAnnihilator :=
    LinearMap.finrank_le_finrank_of_injective (f := L.codRestrict _ hLQ)
      (fun a b h => hLinj (congrArg Subtype.val h))

  have hker : LinearMap.ker Q = (D ⊓ R.comap (F - LinearMap.id)).comap D.subtype := by
    ext x
    constructor
    · intro h
      have h' : T x ∈ RV := (Submodule.Quotient.mk_eq_zero RV).mp h
      exact ⟨x.2, h'⟩
    · intro h
      exact (Submodule.Quotient.mk_eq_zero RV).mpr h.2
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range Q)
  have h2 := Submodule.finrank_quotient_add_finrank RV
  have h3 := LinearMap.finrank_range_add_finrank_ker Q
  have h4 : finrank k ↥RV = finrank k ↥R := (Submodule.comapSubtypeEquivOfLe hRD).finrank_eq
  have h5 : finrank k ↥(LinearMap.ker Q) = finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  omega

end GlobalTheory
end

section

namespace GlobalTheory

theorem isSquare_one_add_of_pow_two_pow_eq_zero {A : Type} [CommRing A] (c : A)
    (hc : 2 * c = 1) : ∀ (m : ℕ) (n : A), n ^ (2 ^ m) = 0 → IsSquare (1 + n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    simp only [pow_zero, pow_one] at hn
    exact ⟨1, by rw [hn]; ring⟩
  | succ m ih =>
    intro n hn
    have hnil : IsNilpotent (c * n) := ⟨2 ^ (m + 1), by rw [mul_pow, hn, mul_zero]⟩
    obtain ⟨v, hv⟩ := (hnil.isUnit_one_add).exists_right_inv
    have hn' : (-(c ^ 2 * n ^ 2 * v ^ 2)) ^ (2 ^ m) = 0 := by
      have : -(c ^ 2 * n ^ 2 * v ^ 2) = n ^ 2 * (-(c ^ 2 * v ^ 2)) := by ring
      rw [this, mul_pow, ← pow_mul, ← pow_succ', hn, zero_mul]
    obtain ⟨z, hz⟩ := ih _ hn'
    refine ⟨(1 + c * n) * z, ?_⟩
    linear_combination (1 + c * n) ^ 2 * hz + (c ^ 2 * n ^ 2 * ((1 + c * n) * v + 1)) * hv
      + (-n) * hc

theorem isSquare_one_add_of_isNilpotent {A : Type} [CommRing A] (c : A) (hc : 2 * c = 1)
    {n : A} (hn : IsNilpotent n) : IsSquare (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  exact isSquare_one_add_of_pow_two_pow_eq_zero c hc N n
    (pow_eq_zero_of_le (Nat.lt_two_pow_self).le hN)

theorem units_modSq_finite_of_fields : ∀ (k : Type) [Field k] [CharZero k],
    (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L],
      Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) →
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
      Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  intro k _ _ hL A _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hc : (2 : A) * algebraMap k A (1 / 2) = 1 := by
    have h2 : (2 : A) * algebraMap k A (1 / 2) = algebraMap k A (2 * (1 / 2)) := by
      rw [map_mul, map_ofNat]
    rw [h2]
    norm_num
  let Q : MaximalSpectrum A → Type := fun I =>
    (A ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range
  haveI hQ : ∀ I, Finite (Q I) := by
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact hL (A ⧸ I.asIdeal)
  let φ : Aˣ →* ((I : MaximalSpectrum A) → Q I) := MonoidHom.pi fun I =>
    (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have key : ∀ (I : MaximalSpectrum A) (u : Aˣ), φ u I = 1 ↔
      Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u ∈
        (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range :=
    fun I u => QuotientGroup.eq_one_iff _
  have hS : (powMonoidHom 2 : Aˣ →* Aˣ).range ≤ φ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext I
    rw [Pi.one_apply, key]
    exact ⟨Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom y, by simp⟩
  have hk : ∀ x : Aˣ, φ x = 1 → x ∈ (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    intro x hx
    have hloc : ∀ I : MaximalSpectrum A, ∃ w : (A ⧸ I.asIdeal)ˣ,
        (w : A ⧸ I.asIdeal) ^ 2 = Ideal.Quotient.mk I.asIdeal x := by
      intro I
      have h1 := (key I x).1 (congrFun hx I)
      obtain ⟨w, hw⟩ := h1
      refine ⟨w, ?_⟩
      have := congrArg (fun u : (A ⧸ I.asIdeal)ˣ => (u : A ⧸ I.asIdeal)) hw
      simpa using this
    choose w hw using hloc
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun I : MaximalSpectrum A => I.asIdeal)
      (fun I J h => MaximalSpectrum.isCoprime_of_ne h) (fun I => (w I : A ⧸ I.asIdeal))
    have hmem : ∀ I : MaximalSpectrum A, (x : A) - a ^ 2 ∈ I.asIdeal := by
      intro I
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      rw [ha I, hw I, sub_self]
    have hjac : (x : A) - a ^ 2 ∈ (⊥ : Ideal A).jacobson := by
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    have hnil : IsNilpotent ((x : A) - a ^ 2) := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      refine ⟨N, ?_⟩
      have := Ideal.pow_mem_pow hjac N
      rw [hN] at this
      simpa using this
    set m := (x : A) - a ^ 2 with hm
    have ha2 : IsUnit (a ^ 2) := by
      have : a ^ 2 = (x : A) + (-m) := by rw [hm]; ring
      rw [this]
      exact hnil.neg.isUnit_add_left_of_commute x.isUnit (Commute.all _ _)
    have hau : IsUnit a := (isUnit_pow_iff (by norm_num)).1 ha2
    obtain ⟨b, hb⟩ := hau
    have hn2 : IsNilpotent (((b⁻¹ : Aˣ) : A) ^ 2 * m) :=
      (Commute.all _ _).isNilpotent_mul_left hnil
    obtain ⟨z, hz⟩ := isSquare_one_add_of_isNilpotent _ hc hn2
    have hzu : IsUnit z := by
      have hu : IsUnit (1 + ((b⁻¹ : Aˣ) : A) ^ 2 * m) := hn2.isUnit_one_add
      rw [hz] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine ⟨b * hzu.unit, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec]
    have hbb : (b : A) * ((b⁻¹ : Aˣ) : A) = 1 := by simp
    have hxm : (x : A) = a ^ 2 + m := by rw [hm]; ring
    rw [hxm, ← hb]
    linear_combination (b : A) ^ 2 * hz.symm + (m * ((b : A) * ((b⁻¹ : Aˣ) : A) + 1)) * hbb
  let ψ := QuotientGroup.lift _ φ hS
  have hinj : Function.Injective ψ := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H x =>
    induction q using QuotientGroup.induction_on with
    | H y =>
    rw [QuotientGroup.eq]
    apply hk
    have h1 : φ x = φ y := hpq
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact Finite.of_injective ψ hinj

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory


open TensorProduct in
theorem _root_.GlobalTheory.exists_embedding_idempotent_tensor (F K L : Type) [Field F] [CharZero F] [Field K]
    [Field L] [Algebra F K] [Algebra F L] [FiniteDimensional F K] (τ : K →ₐ[F] L) :
    ∃ (m : ℕ) (c : Fin m → L) (k : Fin m → K), ∑ j, c j * τ (k j) = 1 ∧
      ∀ y : K, ∑ j, c j ⊗ₜ[F] (y * k j) = ∑ j, (τ y * c j) ⊗ₜ[F] k j := by
  classical
  have hB : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  have hsymm : (Algebra.traceForm F K).IsSymm := Algebra.traceForm_isSymm F
  let b := Module.finBasis F K
  let d := (Algebra.traceForm F K).dualBasis hB b
  have hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j
  set s : K := ∑ j, b j * d j with hs
  have hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x := by
    intro x
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]

    rw [Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hbd]
  have hs0 : s ≠ 0 := by
    intro h
    have htr : Algebra.trace F K s = (Module.finrank F K : F) := by

      rw [hs, map_sum]
      simp [hbd]
    rw [h, map_zero] at htr
    exact (Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp htr.symm)
  refine ⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩
  · calc ∑ j, τ (s⁻¹ * b j) * τ (d j) = τ (s⁻¹ * s) := by

          simp only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]
      _ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]
  · have lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) =
        ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← hd (y * d j)]
      rw [TensorProduct.tmul_sum]
      simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i =
        ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, mul_left_comm]
      conv_lhs => rw [← hb (y * b i)]

      rw [Finset.mul_sum, map_sum, TensorProduct.sum_tmul]
      simp_rw [mul_smul_comm, map_smul]
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_right_comm y (d j) (b i)]

end GlobalTheory
end

section

open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  intro k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap
  set Q := LinearMap.range π with hQ
  set Z' : Submodule k Q := Z.comap Q.subtype
  set R' : Submodule k U := R.comap U.subtype
  have hZ' : finrank k Z' = finrank k Z := (Submodule.comapSubtypeEquivOfLe hZ).finrank_eq
  have hR' : finrank k R' = finrank k R := (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq
  set K : Submodule k E := U.comap ν
  let g : K →ₗ[k] Q ⧸ Z' := Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype
  let f : K →ₗ[k] U ⧸ R' := R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨u, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨e, he⟩ := hU u.2
    have heU : ν e ∈ U := he ▸ u.2
    refine ⟨⟨e, heU⟩, ?_⟩
    have hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u := Subtype.ext he
    exact congrArg R'.mkQ hu
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    have h0 : Submodule.Quotient.mk (p := Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx
    have hx' : π (x : E) ∈ Z := (Submodule.Quotient.mk_eq_zero (p := Z')).mp h0
    have hy : ν (x : E) ∈ R := hmap _ hx'
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (p := R')
      (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy
  let gq := (LinearMap.ker g).liftQ g le_rfl
  let fq := (LinearMap.ker g).liftQ f hker
  have hgq : Function.Injective gq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfq : Function.Surjective fq := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have : Module.Finite k (K ⧸ LinearMap.ker g) := Module.Finite.of_injective gq hgq
  have key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z') :=
    (LinearMap.finrank_le_finrank_of_surjective hfq).trans
      (LinearMap.finrank_le_finrank_of_injective hgq)
  have h1 := Submodule.finrank_quotient_add_finrank R'
  have h2 := Submodule.finrank_quotient_add_finrank Z'
  omega

end GlobalTheory
end

section

open TensorProduct Module

namespace GlobalTheory

theorem rTensor_pairing_eq_zero_of_flip_injective : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  intro F _ B _ _ V V' _ _ _ _ _ m hm y hy
  have hinj : Function.Injective m.flip :=
    (injective_iff_map_eq_zero m.flip).2 fun z h =>
      hm z fun x => by simpa using LinearMap.congr_fun h x
  have hsurj : Function.Surjective m := LinearMap.flip_injective_iff₂.1 hinj
  let b := Module.finBasis F V'
  have key : ∀ z : V' ⊗[F] B,
      z = ∑ j, b j ⊗ₜ (TensorProduct.lid F B (LinearMap.rTensor B (b.coord j) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add z₁ z₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
  rw [key y]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨v, hv⟩ := hsurj (b.coord j)
  rw [← hv, hy v, TensorProduct.tmul_zero]

end GlobalTheory
end

section

namespace GlobalTheory

theorem freeModule_adicComplete_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  intro R _ ϖ hc hs M _ _ _ _
  classical
  let b := Module.Free.chooseBasis R M
  haveI : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  constructor
  · intro x
    choose a ha using fun i => hc (fun j => b.equivFun (x j) i)
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    choose c hc' using fun i => ha i n
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext i

    simp only [map_sub, map_sum, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hc' i
  · intro m hm
    apply b.equivFun.injective
    funext i
    show b.equivFun m i = b.equivFun 0 i
    rw [map_zero]
    show b.equivFun m i = 0
    apply hs
    intro n
    obtain ⟨z, hz⟩ := hm n
    refine ⟨b.equivFun z i, ?_⟩
    rw [hz, map_smul]
    rfl

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.FinOrd

theorem eq_one_of_pow_eq_one_of_charpoly (K : Type) [Field K] [CharZero K] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) K) (h : ∃ m : ℕ, 0 < m ∧ M ^ m = 1)
    (hc : M.charpoly = (X - 1) ^ N) : M = 1 := by
  obtain ⟨m, hm, hM⟩ := h
  have hpr : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)

  have hsep : (X ^ m - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have h1 : minpoly K M ∣ X ^ m - 1 := minpoly.dvd_iff.2 (by simp [hM])

  have h2 : minpoly K M ∣ (X - 1) ^ N := by
    rw [← hc]; exact minpoly.dvd_iff.2 (Matrix.aeval_self_charpoly M)
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr N).1 h2

  have hsi : ((X - 1 : K[X]) ^ i).Separable := hsep.of_dvd (hi.symm.dvd.trans h1)
  have hle : minpoly K M ∣ X - 1 := by
    rcases hsi.of_pow' with hu | ⟨-, rfl⟩ | rfl
    · exact absurd hu hpr.not_unit
    · simpa using hi.dvd
    · exact hi.dvd.trans (by simp)
  have h0 : Polynomial.aeval M (X - 1 : K[X]) = 0 := minpoly.dvd_iff.1 hle
  simpa [sub_eq_zero] using h0

end GlobalTheory.FinOrd
end
