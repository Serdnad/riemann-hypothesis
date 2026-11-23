module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTrace
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.NumberTheory.GaussSum
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem hat_eq_sum_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold hat
  have step : ∀ i ∈ Finset.range N, φ (i : ZMod N) * cexp (2 * π * Complex.I * ((i : ℂ) * (d : ℂ)) / N)
      = φ (i : ZMod N) * ZMod.stdAddChar ((i : ZMod N) * (d : ZMod N)) := by
    intro i _
    congr 1
    have : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl step]
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro y _; simp [ZMod.val_lt]
  · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi; simp [ZMod.val_cast_of_lt hi]
  · intro y _; simp
  · intro i _; rfl

theorem hat_add_period {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (x : ℤ) : hat φ (x + N) = hat φ x := by
  rw [hat_eq_sum_std, hat_eq_sum_std]
  push_cast
  simp

theorem hat_mul_unit {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (d x : ℤ) (hd : IsUnit (d : ZMod N)) :
    hat θ (x * d) = ch θ⁻¹ d * hat θ x := by
  have h := gaussSum_mulShift_eq θ ((ZMod.stdAddChar (N := N)).mulShift (x : ZMod N)) hd.unit
  simp only [gaussSum, AddChar.mulShift_apply, IsUnit.unit_spec] at h
  rw [hat_eq_sum_std, hat_eq_sum_std]
  unfold ch
  calc ∑ y : ZMod N, θ y * ZMod.stdAddChar (y * ((x * d : ℤ) : ZMod N))
      = ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * ((d : ZMod N) * y)) := by
        refine Fintype.sum_congr _ _ (fun y => ?_); push_cast; ring_nf
    _ = θ⁻¹ (d : ZMod N) * ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * y) := h
    _ = _ := by
        congr 1; refine Fintype.sum_congr _ _ (fun y => ?_); ring_nf

theorem hat_zero_of_ne_one {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (h : θ ≠ 1) : hat θ 0 = 0 := by
  rw [hat_eq_sum_std]
  simp only [Int.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one h

theorem isUnit_of_isCoprime {N : ℕ} (d : ℤ) (h : IsCoprime d N) : IsUnit (d : ZMod N) := by
  obtain ⟨a, b, hab⟩ := h
  have : ((a * d + b * N : ℤ) : ZMod N) = 1 := by rw [hab]; simp
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one (a : ZMod N) (by rw [mul_comm]; exact this)

theorem hat_prime_one {l : ℕ} [Fact l.Prime] (x : ℤ) :
    hat (1 : DirichletCharacter ℂ l) x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1 := by
  classical
  rw [hat_eq_sum_std]
  have hterm : ∀ y : ZMod l, (1 : DirichletCharacter ℂ l) y * ZMod.stdAddChar (y * (x : ZMod l))
      = ZMod.stdAddChar (y * (x : ZMod l)) - if y = 0 then 1 else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy; rw [MulChar.map_zero]; simp
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)]; simp [hy]
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_sub_distrib, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l)]
  simp [ZMod.card, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem hat_prime_ne_one {l : ℕ} [Fact l.Prime] (ψ : DirichletCharacter ℂ l) (hψ : ψ ≠ 1) :
    hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x := by
  constructor
  · have h := gaussSum_mul_gaussSum_eq_card hψ (ZMod.isPrimitive_stdAddChar l)
    rw [hat_eq_sum_std]
    intro h0
    simp only [Int.cast_one, mul_one] at h0
    rw [gaussSum, h0, zero_mul, ZMod.card] at h
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm
  · intro x
    by_cases hx : (x : ZMod l) = 0
    · have h1 : hat ψ x = 0 := by
        rw [hat_eq_sum_std, hx]
        simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
        exact MulChar.sum_eq_zero_of_ne_one hψ
      rw [h1]; unfold ch; rw [hx, MulChar.map_zero, mul_zero]
    · have := hat_mul_unit ψ x 1 (isUnit_iff_ne_zero.mpr hx)
      rw [one_mul] at this
      rw [this, mul_comm]

theorem stdAddChar_nat_mul_int {M : ℕ} [NeZero M] (a : ZMod M) (x : ℤ) :
    (ZMod.stdAddChar (a * (x : ZMod M)) : ℂ) = cexp (2 * π * Complex.I * ((a.val : ℂ) * x) / M) := by
  have : a * (x : ZMod M) = (((a.val : ℤ) * x : ℤ) : ZMod M) := by push_cast; simp
  rw [this, ZMod.stdAddChar_coe]; push_cast; ring_nf

theorem hat_mul_coprime (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (φ : DirichletCharacter ℂ (N * l)) (hN : 0 < N) (hl : 0 < l) (hc : N.Coprime l)
    (hφ : ∀ d : ℤ, ch φ d = ch θ d * ch ψ d) (x : ℤ) :
    hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
  have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
    fun k => map_natCast _ k
  have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
    fun k => map_natCast _ k
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  have hinj : Function.Injective f := by
    intro p q hpq
    have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
    have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
    simp only [f, hcN, hcl] at h1 h2
    push_cast at h1 h2
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
    exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [ZMod.card]⟩
  rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun a => ?_)
  rw [Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun b => ?_)
  have hf : f (a, b) = (((a.val * l + b.val * N : ℕ) : ℤ) : ZMod (N * l)) := by simp [f]
  have hval : φ (f (a, b)) = θ a * θ l * (ψ b * ψ N) := by
    have := hφ ((a.val * l + b.val * N : ℕ) : ℤ)
    unfold ch at this
    rw [hf, this]
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val, map_mul]
  have he : (ZMod.stdAddChar (f (a, b) * (x : ZMod (N * l))) : ℂ)
      = ZMod.stdAddChar (a * (x : ZMod N)) * ZMod.stdAddChar (b * (x : ZMod l)) := by
    have : f (a, b) * (x : ZMod (N * l)) = ((((a.val * l + b.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
      rw [hf]; push_cast; rfl
    rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int a x, stdAddChar_nat_mul_int b x, ← Complex.exp_add]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    push_cast
    field_simp
  rw [hval, he]
  unfold ch
  simp only [Int.cast_natCast]
  ring

theorem hat_char_props : (∀ (N : ℕ) (θ : DirichletCharacter ℂ N), 0 < N → (∀ x : ℤ, hat θ (x + N) = hat θ x) ∧ (∀ d x : ℤ, IsCoprime d N → hat θ (x * d) = ch θ⁻¹ d * hat θ x) ∧ (θ ≠ 1 → hat θ 0 = 0)) ∧ (∀ (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)), 0 < N → 0 < l → N.Coprime l → (∀ d : ℤ, ch φ d = ch θ d * ch ψ d) → ∀ x, hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x)) ∧ ∀ (l : ℕ) (ψ : DirichletCharacter ℂ l), l.Prime → (ψ ≠ 1 → hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x) ∧ (ψ = 1 → ∀ x : ℤ, hat ψ x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N θ hN
    haveI : NeZero N := ⟨hN.ne'⟩
    exact ⟨fun x => hat_add_period _ x, fun d x hd => hat_mul_unit θ d x (isUnit_of_isCoprime d hd),
      hat_zero_of_ne_one θ⟩
  · intro N l θ ψ φ hN hl hc hφ x
    exact hat_mul_coprime N l θ ψ φ hN hl hc hφ x
  · intro l ψ hl
    haveI : Fact l.Prime := ⟨hl⟩
    refine ⟨hat_prime_ne_one ψ, ?_⟩
    rintro rfl x
    exact hat_prime_one x

end GlobalTheory.EisM
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.CocPot

theorem I_mem : Complex.I ∈ Hs := by
  show (0 : ℝ) < Complex.I.im
  simp

theorem hom_inc {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    (γ : SL(2, ℤ)) (z : ℂ) :
    (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z).IsHomogeneous w :=
  (Betti.polySlash_isHomogeneous _ (hF.1 _)).sub (hF.1 z)

theorem inc_eq {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ Hs) :
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z =
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I := by
  obtain ⟨p, hp⟩ := hF.2 γ hγ
  rw [hp z hz, hp _ I_mem]

theorem inc_mul {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (δ : SL(2, ℤ)) :
    slP ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL (γ * δ)) Complex.I)) - F Complex.I =
      slP (δ : Matrix (Fin 2) (Fin 2) ℤ)
          (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I) +
        (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) Complex.I)) - F Complex.I) := by
  have hδI := mob_laws.1 (ofSL δ) _ I_mem
  have hm : mob (ofSL (γ * δ)) Complex.I = mob (ofSL γ) (mob (ofSL δ) Complex.I) := by
    rw [map_mul]
    exact mob_laws.2.1 _ _ _ I_mem
  rw [hm, Matrix.SpecialLinearGroup.coe_mul, ← Betti.polySlash_polySlash, ← inc_eq hF hγ hδI, map_sub]
  abel

end GlobalTheory.KZ.CocPot

namespace GlobalTheory.KZ


open CocPot in
theorem cocP_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro w N l _ _
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w
  refine ⟨fun F hF => ⟨⟨fun γ => ?_, fun γ δ => ?_⟩, fun γ τ hτ => ?_, fun hB => ?_⟩, fun F G => ?_, fun c F => ?_⟩
  · exact d2 _ (hom_inc hF _ _)
  · have hγ : (γ : SL(2, ℤ)) ∈ Gam N l := γ.2
    have key := inc_mul hF hγ (δ : SL(2, ℤ))
    have e1 := d1 ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ (hom_inc hF (γ : SL(2, ℤ)) Complex.I)
    show deh (slP (((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        (F (mob (ofSL ((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ))) Complex.I)) - F Complex.I) = _
    rw [Subgroup.coe_mul, key, map_add (f := _), e1]
    rfl
  · show _ = deh _
    rw [inc_eq hF (show (γ : SL(2, ℤ)) ∈ Gam N l from γ.2) hτ]
  · obtain ⟨⟨q, hq⟩, hqe⟩ := hB
    obtain ⟨p, hp, rfl⟩ := d3 q hq
    refine ⟨fun z => F z - p, p, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have e := congrFun hqe ⟨γ, hγ⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at e
    change _ = deh _ at e
    rw [← d1 _ _ hp, ← map_sub] at e
    have e2 := d4 _ _ ((Betti.polySlash_isHomogeneous _ hp).sub hp) (hom_inc hF _ _) e
    have e3 := inc_eq hF hγ hz
    simp only [map_sub]
    linear_combination e3 - e2
  · funext γ
    simp only [cocP, Pi.add_apply, map_add (f := _), map_sub]
    abel
  · funext γ
    simp only [cocP, Pi.smul_apply, map_smul, map_sub, smul_sub]

end GlobalTheory.KZ
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DictHk

theorem mat_mul {Γ : Subgroup SL(2, ℤ)} (a b : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat ((a * b : Γ) : SL(2, ℤ)) = GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat b := rfl

theorem mat_mul_inv {Γ : Subgroup SL(2, ℤ)} (a : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ)) = 1 := by
  rw [← mat_mul, mul_inv_cancel]; rfl

theorem mat_one {Γ : Subgroup SL(2, ℤ)} : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := rfl

theorem cancel_right {Γ : Subgroup SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (a : Γ)
    (h : A * GlobalTheory.HeckeFamilyMatrices.mat a = B * GlobalTheory.HeckeFamilyMatrices.mat a) : A = B := by
  have := congrArg (· * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ))) h
  simpa only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] using this

theorem det_pos {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type}
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hα : 0 < α.det) (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (i : ι) :
    0 < (δ i).det := by
  obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
  rw [h, det_mul, det_mul]
  simpa using hα

theorem exists_perm {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} [Fintype ι]
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ (π i) := by
  classical
  have hf : ∀ i, ∃ j, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ j := by
    intro i
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨j, ⟨γ', h'⟩, -⟩ := hδ.2 γ₁ (γ₂ * γ)
    refine ⟨j, γ', ?_⟩
    rw [h, ← h', mat_mul, Matrix.mul_assoc]
  choose f g hfg using hf
  have hinj : Function.Injective f := by
    intro i i' hii
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨k, -, hk⟩ := hδ.2 γ₁ γ₂
    have e1 : i = k := hk i ⟨1, by rw [mat_one, Matrix.one_mul, h]⟩
    have e2 : i' = k := by
      refine hk i' ⟨g i * (g i')⁻¹, ?_⟩
      rw [← h]
      apply cancel_right γ
      rw [hfg i, Matrix.mul_assoc, hfg i', ← hii, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel_right]
    rw [e1, e2]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ⟨g i, hfg i⟩⟩

theorem incr {N l w : ℕ} {ι : Type} [Fintype ι] {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : ∀ i, 0 < (δ i).det) {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w (Gam N l))
    (γ : GlobalTheory.HeckeFamilyMatrices.Lev N l) (π : Equiv.Perm ι) (g : ι → GlobalTheory.HeckeFamilyMatrices.Lev N l)
    (hg : ∀ i, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i)) (z : ℂ) (hz : z ∈ Hs) :
    slP (GlobalTheory.HeckeFamilyMatrices.mat γ) ((∑ i, opP ℂ (δ i) F) (mob (ofSL γ) z)) - (∑ i, opP ℂ (δ i) F) z =
      ∑ i, slP (δ (π i)) (slP (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (F (mob (ofSL (g i)) Complex.I)) - F Complex.I) := by
  obtain ⟨hmem, hmul, -, -, hSL, htoGQ⟩ := GlobalTheory.KZ.mob_laws
  obtain ⟨hslmul, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 : ∀ a : GlobalTheory.HeckeFamilyMatrices.Lev N l, 0 < (GlobalTheory.HeckeFamilyMatrices.mat a).det := fun a => by simp

  simp only [Finset.sum_apply, map_sum]
  rw [← Equiv.sum_comp π (fun i => opP ℂ (δ i) F z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨p, hp⟩ := hF.2 (g i) (g i).2
  have hz' := hmem (toGQ (δ (π i))) z hz
  rw [hp _ hI, ← hp _ hz']
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [sub_left_inj]
  have hL : mob (toGQ (δ i)) (mob (ofSL γ) z) = mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z := by
    rw [htoGQ _ _ (hdet i) (h1 γ), hSL, hmul _ _ _ hz]
  have hR : mob (ofSL (g i)) (mob (toGQ (δ (π i))) z) =
      mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z := by
    rw [htoGQ _ _ (h1 (g i)) (hdet (π i)), hSL, hmul _ _ _ hz]
  have hs1 := hslmul (δ i) (GlobalTheory.HeckeFamilyMatrices.mat γ) (F (mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z))
  have hs2 := hslmul (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (δ (π i)) (F (mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z))
  rw [hL, hR, ← hs1, ← hs2, hg i]

theorem dict_hk : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι]
    (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det →
    GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l),
    (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) =
        GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro N l w α ι _ δ _ _ hα hδ F hF
  have hdet := det_pos hα hδ
  obtain ⟨-, -, hslhom, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  refine ⟨⟨fun z => ?_, fun γ hγ => ?_⟩, ?_⟩
  · simp only [Finset.sum_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => hslhom _ w _ (hF.1 _)
  · obtain ⟨π, hπ⟩ := exists_perm hδ (⟨γ, hγ⟩ : GlobalTheory.HeckeFamilyMatrices.Lev N l)
    choose g hg using hπ
    exact ⟨_, fun z hz => incr hdet hF ⟨γ, hγ⟩ π g hg z hz⟩
  · funext γ
    have hex := exists_perm hδ γ
    simp only [GlobalTheory.HeckeFamilyMatrices.hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]

    rw [cocP, incr hdet hF γ hex.choose (fun i => (hex.choose_spec i).choose)
    (fun i => (hex.choose_spec i).choose_spec) _ hI, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w).1 _ _ ((hslhom _ w _ (hF.1 _)).sub (hF.1 _))]
    rfl

end GlobalTheory.KZ.DictHk
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem germ_eq_of_eqOn_Hs {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  rw [Filter.Germ.coe_eq]
  exact Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h z hz)

theorem kum_kmap_sl : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det →
      Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  intro Ω _ _ ε X l _ n m x χ hm hK
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩ := hK
  obtain ⟨mobHs, mobMul, mobOne, mobDiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨cj1, -, cj3⟩ := GlobalTheory.T.integralConjugateSL2Int_laws
  obtain ⟨-, -, gcomp, -, -⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  have hcls := (GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.2.1 (X.sl (toGQ m)).toRingEquiv x f hx
  refine ⟨Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f, fun z => a (mob (toGQ m) z),
    fun z => b (mob (toGQ m) z), M * m.det.natAbs, ?_, hcls, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Nat.mul_pos hM (Int.natAbs_pos.2 hm.ne')
  · exact ha.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · exact hb.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · intro h0
    apply hb0
    have h0' : ((fun z => b (mob (toGQ m) z) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h0
    have h1 := gcomp (toGQ m)⁻¹ _ _ h0'
    calc (b : Mero) = ((fun z => b (mob (toGQ m) (mob (toGQ m)⁻¹ z)) : ℂ → ℂ) : Mero) := by
          refine germ_eq_of_eqOn_Hs fun z hz => ?_
          rw [← mobMul _ _ z hz, mul_inv_cancel, mobOne]
      _ = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h1
      _ = 0 := rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
      (Quotient.exists_rep (X.an (f : X.K))).imp fun _ h => h.symm
    have h1 : X.an ((Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K) =
        ((fun z => φ (mob (toGQ m) z) : ℂ → ℂ) : Mero) := X.an_sl (toGQ m) f φ hφ
    rw [h1]
    rw [hφ] at hab
    have e := gcomp (toGQ m) (φ * b ^ (l ^ n)) (a ^ (l ^ n))
      (by rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab)
    rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]
    exact e
  · intro δ hδ z hz
    obtain ⟨hmδ, hcj⟩ := cj1 m M hm δ hδ
    have e := cj3 m δ (cj m δ) hm hmδ z hz
    show a (mob (toGQ m) (mob (ofSL δ) z)) * b (mob (toGQ m) z) = _ * (a (mob (toGQ m) z) * b (mob (toGQ m) (mob (ofSL δ) z)))
    rw [e]
    exact hrel (cj m δ) hcj (mob (toGQ m) z) (mobHs _ z hz)

end GlobalTheory.KZ.H3
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  first | (exact @GlobalTheory.Glue.CorShap.cores_law) | (exact GlobalTheory.Glue.CorShap.cores_law) | (intros; apply GlobalTheory.Glue.CorShap.cores_law  <;> assumption)
end
