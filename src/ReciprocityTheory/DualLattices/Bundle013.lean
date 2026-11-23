module

public import ReciprocityTheory.DualLattices.Bundle006
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import ReciprocityTheory.DualLattices.Bundle007
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma LHom.ext' {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

def mkLHom {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : ∀ a, IsUnit (f a) → IsUnit a) : LHom R S :=
  ⟨f, ⟨fun a ha => h a ha⟩⟩

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma sq_ker {a b : (Dp.D : Type u)} (ha : a ∈ RingHom.ker Dp.π.1)
    (hb : b ∈ RingHom.ker Dp.π.1) : a * b = 0 := by
  rw [Dp.ker_eq, Ideal.mem_span_singleton'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  linear_combination (a' * b') * Dp.η_sq

lemma sub_σ_mem {d : (Dp.D : Type u)} {r : (R : Type u)} (h : Dp.π.1 d = r) :
    d - Dp.σ.1 r ∈ RingHom.ker Dp.π.1 := by
  rw [RingHom.mem_ker, map_sub, Dp.sect, h, sub_self]

lemma sub_mem (d : (Dp.D : Type u)) : d - Dp.σ.1 (Dp.π.1 d) ∈ RingHom.ker Dp.π.1 :=
  Dp.sub_σ_mem rfl

lemma π_η : Dp.π.1 Dp.η = 0 := RingHom.mem_ker.mp (show Dp.η ∈ RingHom.ker Dp.π.1 from Dp.η_mem)

lemma isUnit_of_π {d : (Dp.D : Type u)} (h : IsUnit (Dp.π.1 d)) : IsUnit d := by
  obtain ⟨w, hw⟩ := h
  have hk : d * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1 ∈ RingHom.ker Dp.π.1 := by
    change Dp.π.1 (d * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1) = 0
    rw [map_sub, map_mul, Dp.sect, ← hw, Units.mul_inv, map_one, sub_self]
  have hkk := Dp.sq_ker hk hk
  exact isUnit_iff_exists_inv.mpr
    ⟨Dp.σ.1 (↑w⁻¹ : (R : Type u)) * (2 - d * Dp.σ.1 (↑w⁻¹ : (R : Type u))),
      by linear_combination -hkk⟩

lemma π_comp_σ : Dp.π.comp Dp.σ = LHom.id R := LHom.ext' Dp.sect

def fμ (c : (R : Type u)) (d : (Dp.D : Type u)) : (Dp.D : Type u) :=
  Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 c * (d - Dp.σ.1 (Dp.π.1 d))

def μA (c : (R : Type u)) : (Dp.D : Type u) →ₐ[R₀] (Dp.D : Type u) where
  toFun := Dp.fμ c
  map_one' := by simp [fμ]
  map_mul' a b := by
    have h := Dp.sq_ker (Dp.sub_mem a) (Dp.sub_mem b)
    simp only [fμ, map_mul]
    linear_combination (Dp.σ.1 c - Dp.σ.1 c ^ 2) * h
  map_zero' := by simp [fμ]
  map_add' a b := by simp only [fμ, map_add (f := _)]; ring
  commutes' r := by simp [fμ]

lemma μA_apply (c : (R : Type u)) (d : (Dp.D : Type u)) : Dp.μA c d = Dp.fμ c d := rfl

lemma π_μA (c : (R : Type u)) (d : (Dp.D : Type u)) : Dp.π.1 (Dp.μA c d) = Dp.π.1 d := by
  simp [μA_apply, fμ, Dp.sect]

def μL (c : (R : Type u)) : LHom Dp.D Dp.D :=
  mkLHom (Dp.μA c) fun a ha => Dp.isUnit_of_π (by simpa [Dp.π_μA] using ha.map Dp.π.1)

def fpS : Subalgebra R₀ (Dp.D.carrier × Dp.D.carrier) :=
  AlgHom.equalizer (Dp.π.1.comp (AlgHom.fst R₀ (Dp.D : Type u) (Dp.D : Type u)))
    (Dp.π.1.comp (AlgHom.snd R₀ (Dp.D : Type u) (Dp.D : Type u)))

lemma fp_eq (q : Dp.fpS) : Dp.π.1 q.1.1 = Dp.π.1 q.1.2 := q.2

lemma fp_isUnit (q : Dp.fpS) (h : IsUnit (Dp.π.1 q.1.1)) : IsUnit q := by
  obtain ⟨w, hw⟩ := h
  let e : Dp.fpS := ⟨(Dp.σ.1 (↑w⁻¹ : (R : Type u)), Dp.σ.1 (↑w⁻¹ : (R : Type u))), rfl⟩
  have m1 : q.1.1 * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1 ∈ RingHom.ker Dp.π.1 := by
    change Dp.π.1 (q.1.1 * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1) = 0
    rw [map_sub, map_mul, Dp.sect, ← hw, Units.mul_inv, map_one, sub_self]
  have m2 : q.1.2 * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1 ∈ RingHom.ker Dp.π.1 := by
    change Dp.π.1 (q.1.2 * Dp.σ.1 (↑w⁻¹ : (R : Type u)) - 1) = 0
    rw [map_sub, map_mul, Dp.sect, ← Dp.fp_eq, ← hw, Units.mul_inv, map_one,
      sub_self]
  have hkk : (q * e - 1) * (q * e - 1) = 0 :=
    Subtype.ext (Prod.ext (Dp.sq_ker m1 m1) (Dp.sq_ker m2 m2))
  exact isUnit_iff_exists_inv.mpr ⟨e * (2 - q * e), by linear_combination -hkk⟩

instance fpS_local : IsLocalRing Dp.fpS := by
  have : Nontrivial Dp.fpS := ⟨⟨0, 1, fun h => zero_ne_one (α := (Dp.D : Type u))
    (by simpa using congrArg (fun q : Dp.fpS => q.1.1) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun q => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Dp.π.1 q.1.1) with h | h
  · exact Or.inl (Dp.fp_isUnit q h)
  · refine Or.inr (Dp.fp_isUnit _ ?_)
    show IsUnit (Dp.π.1 (1 - q.1.1))
    rwa [map_sub, map_one]

abbrev F : LAlg R₀ := ⟨Dp.fpS⟩

def p₁L : LHom Dp.F Dp.D :=
  mkLHom ((AlgHom.fst R₀ _ _).comp Dp.fpS.val) fun q hq => Dp.fp_isUnit q (hq.map Dp.π.1)

def p₂L : LHom Dp.F Dp.D :=
  mkLHom ((AlgHom.snd R₀ _ _).comp Dp.fpS.val) fun q hq =>
    Dp.fp_isUnit q (by rw [Dp.fp_eq]; exact hq.map Dp.π.1)

def fs (q : Dp.fpS) : (Dp.D : Type u) := q.1.1 + q.1.2 - Dp.σ.1 (Dp.π.1 q.1.1)

def sA : (Dp.F : Type u) →ₐ[R₀] (Dp.D : Type u) where
  toFun := Dp.fs
  map_one' := by simp [fs]
  map_mul' a b := by
    have e₃ := Dp.sq_ker (Dp.sub_mem a.1.1) (Dp.sub_σ_mem (Dp.fp_eq b).symm)
    have e₄ := Dp.sq_ker (Dp.sub_σ_mem (Dp.fp_eq a).symm) (Dp.sub_mem b.1.1)
    simp only [fs, Subalgebra.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination -e₃ - e₄
  map_zero' := by simp [fs]
  map_add' a b := by
    simp only [fs, Subalgebra.coe_add, Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
  commutes' r := by
    show algebraMap R₀ (Dp.D : Type u) r + algebraMap R₀ (Dp.D : Type u) r -
      Dp.σ.1 (Dp.π.1 (algebraMap R₀ (Dp.D : Type u) r)) = algebraMap R₀ (Dp.D : Type u) r
    simp

lemma π_sA (q : Dp.fpS) : Dp.π.1 (Dp.sA q) = Dp.π.1 q.1.1 := by
  show Dp.π.1 (q.1.1 + q.1.2 - Dp.σ.1 (Dp.π.1 q.1.1)) = _
  rw [map_sub, map_add (f := _), Dp.sect, ← Dp.fp_eq]; ring

def sL : LHom Dp.F Dp.D :=
  mkLHom Dp.sA fun q hq => Dp.fp_isUnit q (by simpa [Dp.π_sA] using hq.map Dp.π.1)

lemma nilSurj : Dp.π.NilSurj := by
  unfold LHom.NilSurj
  exact ⟨Dp.sqZero.1, 2, Dp.sqZero.2⟩

lemma isFibreSq : IsFibreSq Dp.p₁L Dp.p₂L Dp.π Dp.π := by
  unfold IsFibreSq
  refine ⟨AlgHom.ext fun q => Dp.fp_eq q, Dp.nilSurj, Dp.nilSurj, fun a b h =>
    ⟨⟨(a, b), h⟩, ⟨rfl, rfl⟩, ?_⟩⟩
  rintro c ⟨h1, h2⟩
  exact Subtype.ext (Prod.ext h1 h2)

end DualPair

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y

lemma red_mulVec (H : HodgeTateDatum p g v R O σ cp) (a : O) (t : TT p g) :
    red p g (H.ρ a *ᵥ t) = nbAct H a (red p g t) := by
  funext i
  exact RingHom.map_mulVec PadicInt.toZMod (H.ρ a) t i

lemma red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma comp_mem (H : HodgeTateDatum p g v R O σ cp) (a : O) {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    (fun y => f (nbAct H a y)) ∈ H.AA.carrier := by
  obtain ⟨f', hf', hf'e⟩ := H.h3 a f hf
  have hfun : (fun y => f (nbAct H a y)) = f' := by
    funext y
    obtain ⟨t, rfl⟩ := red_surj y
    rw [hf'e, red_mulVec]
  rw [hfun]
  exact hf'

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

private lemma smul_cancel_lemma {S K : Type*} [CommRing S] [Field K] [Algebra S K]
    (hinj : Function.Injective (algebraMap S K)) {ι κ : Type*} {M : Matrix ι κ S} (hM : M ≠ 0)
    {a b : S} (h : a • M = b • M) : a = b := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext fun x y => by simpa using hc x y)
  have h2 : a * M x y = b * M x y := by
    have := congrFun (congrFun h x) y
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  have h3 : algebraMap S K (a - b) * algebraMap S K (M x y) = 0 := by
    rw [← map_mul, sub_mul, h2, sub_self, map_zero]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (hinj (by rw [h4, map_zero]))
  · exact absurd (hinj (by rw [h4, map_zero])) hxy

end Lift

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

section

variable {R : Type} [CommRing R]

lemma single_smul_self {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
  · simp [Pi.single_eq_of_ne hk]

lemma eq_sum_single {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)]
  simp [Algebra.smul_def]

end

theorem hasLen_ext {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by
  classical
  obtain ⟨m, α, ⟨eA⟩, hαa⟩ := ha
  obtain ⟨m', δ, ⟨eD⟩, hδc⟩ := hc
  set gA : Fin m → A := fun i => eA.symm (Pi.single i 1) with hgA
  set gD : Fin m' → D := fun j => eD.symm (Pi.single j 1) with hgD
  have hgA0 : ∀ i, α i • gA i = 0 := fun i => by
    simp only [hgA]
    rw [← map_smul, single_smul_self, map_zero]
  have hgD0 : ∀ j, δ j • gD j = 0 := fun j => by
    simp only [hgD]
    rw [← map_smul, single_smul_self, map_zero]
  have reprA : ∀ y : A, y = ∑ i, (Quotient.out (eA y i) : R) • gA i := fun y => by
    conv_lhs => rw [← eA.symm_apply_apply y, eq_sum_single α (eA y)]

    simp only [hgA, map_sum, map_smul]
  have reprD : ∀ y : D, y = ∑ j, (Quotient.out (eD y j) : R) • gD j := fun y => by
    conv_lhs => rw [← eD.symm_apply_apply y, eq_sum_single δ (eD y)]

    simp only [hgD, map_sum, map_smul]
  have memA : ∀ r : Fin m → R, ∑ i, r i • gA i = 0 → ∀ i, r i ∈ Ideal.span {α i} := by
    intro r hr i
    have h1 : eA (∑ i, r i • gA i) = 0 := by rw [hr, map_zero]

    simp only [hgA, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have memD : ∀ r : Fin m' → R, ∑ j, r j • gD j = 0 → ∀ j, r j ∈ Ideal.span {δ j} := by
    intro r hr i
    have h1 : eD (∑ j, r j • gD j) = 0 := by rw [hr, map_zero]

    simp only [hgD, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have hπι : ∀ y : A, π (ι y) = 0 := fun y => by
    have h1 : ι y ∈ LinearMap.range ι := ⟨y, rfl⟩
    rw [hex] at h1
    exact h1
  choose b hb using fun j => hπ (gD j)
  have hdb : ∀ j, ∃ y : A, ι y = δ j • b j := fun j => by
    have h1 : δ j • b j ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_smul, hb, hgD0]
    rw [← hex] at h1
    exact h1
  choose aj haj using hdb
  set x : Fin m' → Fin m → R := fun j i => (Quotient.out (eA (aj j) i) : R) with hxdef
  have hx : ∀ j, aj j = ∑ i, x j i • gA i := fun j => reprA (aj j)
  set gen : Fin m ⊕ Fin m' → B := Sum.elim (fun i => ι (gA i)) b with hgen
  let Φ : (Fin m ⊕ Fin m' → R) →ₗ[R] B :=
    { toFun := fun p => ∑ k, p k • gen k
      map_add' := fun p q => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c p => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ p, Φ p = ∑ i, p (Sum.inl i) • ι (gA i) + ∑ j, p (Sum.inr j) • b j := fun p => by
    show ∑ k, p k • gen k = _
    rw [Fintype.sum_sum_type]
    rfl
  let X : Matrix (Fin m ⊕ Fin m') (Fin m ⊕ Fin m') R :=
    Matrix.fromBlocks (Matrix.diagonal α) (Matrix.of fun i j => -x j i) 0 (Matrix.diagonal δ)
  have hdet : X.det = (∏ i, α i) * ∏ j, δ j := by
    simp [X, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  have hXl : ∀ w i, X.mulVec w (Sum.inl i) = α i * w (Sum.inl i) - ∑ j, x j i * w (Sum.inr j) := by
    intro w i
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hXr : ∀ w j, X.mulVec w (Sum.inr j) = δ j * w (Sum.inr j) := by
    intro w j
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply]
  have hιx : ∀ j, ι (aj j) = ∑ i, x j i • ι (gA i) := fun j => by

    rw [hx j, map_sum]
    simp only [map_smul]
  have hΦX : ∀ w, Φ (X.mulVec w) = 0 := by
    intro w
    rw [hΦ]
    simp only [hXl, hXr, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∀ i, (α i * w (Sum.inl i)) • ι (gA i) = 0 := by
      intro i
      rw [mul_comm, mul_smul, ← map_smul, hgA0, map_zero, smul_zero]
    have e2 : ∀ j, (δ j * w (Sum.inr j)) • b j = w (Sum.inr j) • ι (aj j) := by
      intro j
      rw [mul_comm, mul_smul, haj]
    have e3 : ∑ i, (∑ j, x j i * w (Sum.inr j)) • ι (gA i) = ∑ j, w (Sum.inr j) • ι (aj j) := by
      simp only [hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    simp only [e1, e2, Finset.sum_const_zero, zero_sub, e3, neg_add_cancel]
  have hker : LinearMap.ker Φ = LinearMap.range X.mulVecLin := by
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker, hΦ] at hp
      have hπs : ∑ j, p (Sum.inr j) • gD j = 0 := by
        have h1 := congrArg π hp

        simpa [map_add (f := _), map_sum, map_smul, hb, hπι] using h1
      choose t ht using fun j => Ideal.mem_span_singleton'.1 (memD _ hπs j)
      have hsb : ∑ j, p (Sum.inr j) • b j = ι (∑ i, (∑ j, t j * x j i) • gA i) := by

        rw [map_sum]
        simp only [map_smul]
        have e4 : ∀ j, p (Sum.inr j) • b j = t j • ι (aj j) := by
          intro j
          rw [← ht j, mul_smul, haj]
        simp only [e4, hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hι0 : ι (∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i) = 0 := by
        rw [← hp, hsb]

        simp only [add_smul, Finset.sum_add_distrib, map_add (f := _), map_sum, map_smul]
      have hA0 : ∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i = 0 :=
        hι (hι0.trans (map_zero ι).symm)
      choose q hq using fun i => Ideal.mem_span_singleton'.1 (memA _ hA0 i)
      refine ⟨Sum.elim q t, ?_⟩
      funext k
      cases k with
      | inl i =>
        show X.mulVec (Sum.elim q t) (Sum.inl i) = p (Sum.inl i)
        rw [hXl]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hqi := hq i
        rw [show ∑ j, x j i * t j = ∑ j, t j * x j i from Finset.sum_congr rfl fun j _ => mul_comm _ _]
        linear_combination hqi
      | inr j =>
        show X.mulVec (Sum.elim q t) (Sum.inr j) = p (Sum.inr j)
        rw [hXr]
        simp only [Sum.elim_inr]
        rw [mul_comm]
        exact ht j
    · rintro ⟨w, rfl⟩
      exact hΦX w
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin m' → R := fun j => (Quotient.out (eD (π y) j) : R) with hs
    have hys : y - ∑ j, s j • b j ∈ LinearMap.range ι := by

      rw [hex, LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hb]
      rw [← reprD (π y), sub_self]
    obtain ⟨zA, hzA⟩ := hys
    refine ⟨Sum.elim (fun i => (Quotient.out (eA zA i) : R)) s, ?_⟩
    rw [hΦ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have e5 : ∑ i, (Quotient.out (eA zA i) : R) • ι (gA i) = ι zA := by
      conv_rhs => rw [reprA zA]

      rw [map_sum]
      simp only [map_smul]
    rw [e5, hzA, sub_add_cancel]
  let e1 : ((Fin m ⊕ Fin m' → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R] B :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  obtain ⟨k, cc, ⟨e2⟩, hcc⟩ := hS2 (Fin m ⊕ Fin m') X
  refine ⟨k, cc, ⟨e1.symm.trans e2⟩, ?_⟩
  rw [hcc, hdet, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod, hαa, hδc]

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def PrimeHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ AA : HopfOrder (C := C) R (ZMod p),
    ∃ (x ω : ZMod p → C) (δ : R),
      x ∈ AA.carrier ∧ x 0 = 0 ∧ (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      (∀ a, x a = ω a * x 1) ∧ x ^ p = (fun a => algebraMap R C δ * x a) ∧
      v (algebraMap R C δ) = v (x 1) ^ (p - 1) ∧
      AA.carrier = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ)) ∧
      augIdeal AA.carrier = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ∧
      sqIdeal (augIdeal AA.carrier) = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) ∧
      HasColen R v AA.carrier (v (x 1) ^ (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
end
end
