module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem exists_coef_ge (l : ℕ) [Fact l.Prime] (A : Subalgebra ℤ_[l] (PadicAlgCl l)) [hA : Module.Finite ℤ_[l] A] :
    ∃ c : Coef l, A ≤ c.O := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule A).FG := Module.Finite.iff_fg.1 hA
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  change Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule ((integralClosure ℤ_[l] K).map f)
  rw [← hs, Submodule.span_le]
  intro x hx
  have hxA : x ∈ A := by
    change x ∈ Subalgebra.toSubmodule A
    rw [← hs]
    exact Submodule.subset_span hx
  have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hxA⟩ : A)).map A.val
  exact ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩

private theorem unram_adjoin {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    {ζ : S} (hζ : ζ ^ n = 1) : Algebra.FormallyUnramified R (Algebra.adjoin R {ζ}) := by
  let z : Algebra.adjoin R {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton R ζ⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  let D := KaehlerDifferential.D R (Algebra.adjoin R {ζ})
  have hDz : D z = 0 := by
    have h := D.leibniz_pow z n
    rw [hz, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R] at h
    exact ((IsUnit.of_pow_eq_one hz hn0).pow _).smul_eq_zero.1 (hn.smul_eq_zero.1 h.symm)
  have hD : ∀ x (hx : x ∈ Algebra.adjoin R {ζ}), D ⟨x, hx⟩ = 0 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hDz
    | algebraMap r => exact D.map_algebraMap r
    | add x y hx hy h1 h2 =>
      have := D.map_add ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, add_zero] at this
      exact this
    | mul x y hx hy h1 h2 =>
      have := D.leibniz ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := KaehlerDifferential.span_range_derivation R (Algebra.adjoin R {ζ})
  have h0 : (⊤ : Submodule (Algebra.adjoin R {ζ}) Ω[Algebra.adjoin R {ζ}⁄R]) ≤ ⊥ := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD x.1 x.2
  rw [(Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := a))), (Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := b)))]

private theorem eO_eq_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hm : Ideal.span {(l : O)} = IsLocalRing.maximalIdeal O) : eO l O = 1 := by
  unfold eO
  rw [hm, Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩

private theorem exists_unram (l : ℕ) [hl : Fact l.Prime] (n : ℕ) [NeZero n] (hn : ¬ l ∣ n) :
    ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have hu : IsUnit (n : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
  let A : Subalgebra ℤ_[l] (PadicAlgCl l) := Algebra.adjoin ℤ_[l] {ζ}
  haveI hfin : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.2 hζi.fg_adjoin_singleton
  haveI : Algebra.FormallyUnramified ℤ_[l] A := unram_adjoin (NeZero.ne n) hu hζ.pow_eq_one
  obtain ⟨c, hc⟩ := exists_coef_ge l A
  let f : A →ₐ[ℤ_[l]] c.O := Subalgebra.inclusion hc
  have hf : Function.Injective f := Subalgebra.inclusion_injective hc
  haveI hloc : IsLocalRing A := by
    letI : Algebra A c.O := f.toAlgebra
    haveI : IsScalarTower ℤ_[l] A c.O := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    haveI : Algebra.IsIntegral A c.O := Algebra.IsIntegral.tower_top ℤ_[l]
    haveI : FaithfulSMul A c.O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
    haveI : IsLocalHom (algebraMap A c.O) := inferInstance
    exact (algebraMap A c.O).domain_isLocalRing
  have hinj : Function.Injective (algebraMap ℤ_[l] A) := by
    intro a b hab
    have h := congrArg (fun x : A => (x : PadicAlgCl l)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)
  haveI : FaithfulSMul ℤ_[l] A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsLocalHom (algebraMap ℤ_[l] A) := inferInstance
  have hm : Ideal.span {(l : A)} = IsLocalRing.maximalIdeal A := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ℤ_[l]), PadicInt.maximalIdeal_eq_span_p,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have hnf : ¬ IsField A := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := hm ▸ inferInstance
  have hd : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hp
  refine ⟨⟨A, hd, hfin⟩, ?_, ?_⟩
  · exact eO_eq_one l A hm
  · refine ⟨⟨⟨ζ, Algebra.self_mem_adjoin_singleton _ ζ⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective

theorem UpperTheory.V.HV.coefSup :
    ∀ (l : ℕ) [Fact l.Prime], (∀ c c' : Coef l, ∃ c'' : Coef l, c.O ≤ c''.O ∧ c'.O ≤ c''.O) ∧
      (∀ (n : ℕ) [NeZero n], ¬ l ∣ n → ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n) ∧
      (∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O) ∧
      ∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → (∃ a b : c.O, (b : PadicAlgCl l) ≠ 0 ∧ x * b = a) → x ∈ c.O := by
  intro l _
  refine ⟨fun c c' => ?_, fun n _ hn => exists_unram l n hn, fun c x hx => ?_, fun c x hx ⟨a, b, hb, hab⟩ => ?_⟩
  · haveI := Subalgebra.finite_sup c.O c'.O
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ c'.O)
    exact ⟨d, le_sup_left.trans hd, le_sup_right.trans hd⟩
  · haveI : Module.Finite ℤ_[l] (Algebra.adjoin ℤ_[l] {x}) := Module.Finite.iff_fg.2 hx.fg_adjoin_singleton
    haveI := Subalgebra.finite_sup c.O (Algebra.adjoin ℤ_[l] {x})
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ Algebra.adjoin ℤ_[l] {x})
    exact ⟨d, le_sup_left.trans hd, (le_sup_right.trans hd) (Algebra.self_mem_adjoin_singleton _ x)⟩
  · let g : FractionRing c.O →ₐ[c.O] PadicAlgCl l :=
      IsFractionRing.liftAlgHom (g := Algebra.ofId c.O (PadicAlgCl l)) Subtype.val_injective
    have hg : g (algebraMap c.O _ a / algebraMap c.O _ b) = x := by
      rw [map_div₀, g.commutes, g.commutes]
      exact (div_eq_iff hb).2 hab.symm
    have hi : IsIntegral c.O (algebraMap c.O (FractionRing c.O) a / algebraMap c.O _ b) := by
      rw [← isIntegral_algHom_iff g g.injective, hg]
      exact hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hg, ← hy, g.commutes]
    exact y.2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orderOf_pow_coprime_parts {Γ : Type} [Group Γ] (x : Γ) (P C e : ℕ) (hn : orderOf x = P * C)
    (hP : 0 < P) (hC : 0 < C) (hco : P.Coprime C) (h1 : C ∣ e) (h2 : e ≡ 1 [MOD P]) :
    orderOf (x ^ e) = P ∧ orderOf (x * (x ^ e)⁻¹) = C := by
  have hcx : Commute (x ^ e) x := (Commute.refl x).pow_left e
  have hcomm : Commute (x ^ e) (x * (x ^ e)⁻¹) := hcx.mul_right (Commute.refl _).inv_right
  have hyz : x ^ e * (x * (x ^ e)⁻¹) = x := by
    rw [← mul_assoc, hcx.eq, mul_inv_cancel_right]
  have hoy : orderOf (x ^ e) ∣ P := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.mp]
    rw [hn, mul_comm P C]
    exact Nat.mul_dvd_mul_right h1 P
  have hoz : orderOf (x * (x ^ e)⁻¹) ∣ C := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(hcx.symm.inv_right).mul_pow, inv_pow, ← pow_mul]
    have : x ^ (e * C) = x ^ C := by
      rw [pow_eq_pow_iff_modEq, hn]
      have := Nat.ModEq.mul_right' C h2
      simpa using this
    rw [this, mul_inv_cancel]
  have hco' : (orderOf (x ^ e)).Coprime (orderOf (x * (x ^ e)⁻¹)) := Nat.Coprime.of_dvd hoy hoz hco
  have hprod : orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹) = P * C := by
    rw [← hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco', hyz, hn]
  obtain ⟨a, ha⟩ := hoy
  obtain ⟨b, hb⟩ := hoz
  have hab : a * b = 1 := by
    have : P * C * (a * b) = P * C * 1 := by
      calc P * C * (a * b)
          = (orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹)) * (a * b) := by rw [hprod]
        _ = (orderOf (x ^ e) * a) * (orderOf (x * (x ^ e)⁻¹) * b) := by ring
        _ = P * C * 1 := by rw [← ha, ← hb, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hP hC) this
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right hab
  have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
  refine ⟨?_, ?_⟩
  · rw [ha, ha1, mul_one]
  · rw [hb, hb1, mul_one]

theorem UpperTheory.V.HV.partOrd :
    ∀ (Γ : Type) [Group Γ] (l : ℕ), l.Prime → ∀ x : Γ, 0 < orderOf x →
      orderOf (lPart l x) = ordProj[l] (orderOf x) ∧ orderOf (lPrime l x) = ordCompl[l] (orderOf x) ∧ ¬ l ∣ orderOf (lPrime l x) ∧
      lPart l x ∈ Subgroup.zpowers x ∧ lPrime l x ∈ Subgroup.zpowers x ∧ (¬ l ∣ orderOf x → lPart l x = 1 ∧ lPrime l x = x) ∧
      ∀ a b : Γ, Commute a b → a * b = x → ¬ l ∣ orderOf a → (∃ s, b ^ l ^ s = 1) → lPrime l x = a ∧ lPart l x = b := by
  intro Γ _ l hl x hx
  have hn0 : orderOf x ≠ 0 := hx.ne'
  obtain ⟨P, hPd⟩ : ∃ P, P = ordProj[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = ordCompl[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = C ^ Nat.totient P := ⟨_, rfl⟩
  have hPC : P * C = orderOf x := by rw [hPd, hCd]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hP : 0 < P := by rw [hPd]; exact pow_pos hl.pos _
  have hC : 0 < C := by rw [hCd]; exact Nat.ordCompl_pos l hn0
  have hlC : ¬ l ∣ C := by rw [hCd]; exact Nat.not_dvd_ordCompl hl hn0
  have hcoC : l.Coprime C := (Nat.Prime.coprime_iff_not_dvd hl).2 hlC
  have hco : P.Coprime C := by rw [hPd]; exact hcoC.pow_left _
  have hlp : lPart l x = x ^ e := by rw [hed, hPd, hCd]; rfl
  have hlpr : lPrime l x = x * (lPart l x)⁻¹ := rfl
  have h1 : C ∣ e := by rw [hed]; exact dvd_pow_self _ (Nat.totient_pos.2 hP).ne'
  have h2 : e ≡ 1 [MOD P] := by rw [hed]; exact Nat.ModEq.pow_totient hco.symm
  obtain ⟨hA, hB⟩ := orderOf_pow_coprime_parts x P C e hPC.symm hP hC hco h1 h2
  rw [← hlp] at hA hB
  rw [← hlpr] at hB
  rw [← hCd, ← hPd]
  refine ⟨hA, hB, hB ▸ hlC, ?_, ?_, ?_, ?_⟩
  · rw [hlp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  · rw [hlpr, hlp]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  · intro hnd
    have hf : (orderOf x).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    have ho : orderOf (lPart l x) = 1 := by rw [hA, hPd, hf, pow_zero]
    have h1' := orderOf_eq_one_iff.mp ho
    exact ⟨h1', by rw [hlpr, h1', inv_one, mul_one]⟩
  · rintro a b hab habx hna ⟨s, hs⟩
    have hcoa : (orderOf a).Coprime l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hna)
    have hob : orderOf b ∣ l ^ s := orderOf_dvd_of_pow_eq_one hs
    have hab' : (orderOf a).Coprime (orderOf b) := Nat.Coprime.coprime_dvd_right hob (hcoa.pow_right s)
    have hx' : orderOf x = orderOf a * orderOf b := by
      rw [← habx]; exact hab.orderOf_mul_eq_mul_orderOf_of_coprime hab'
    have hoaC : orderOf a ∣ C := by
      have hd : orderOf a ∣ P * C := by rw [hPC, hx']; exact dvd_mul_right _ _
      have hcP : (orderOf a).Coprime P := by rw [hPd]; exact hcoa.pow_right _
      exact hcP.dvd_of_dvd_mul_left hd
    have hobP : orderOf b ∣ P := by
      have hd : orderOf b ∣ P * C := by rw [hPC, hx']; exact dvd_mul_left _ _
      have hcC : (orderOf b).Coprime C := Nat.Coprime.coprime_dvd_left hob (hcoC.pow_left s)
      exact hcC.dvd_of_dvd_mul_right hd
    have hae : a ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (hoaC.trans h1)
    have hbe : b ^ e = b := by
      have := (pow_eq_pow_iff_modEq (x := b) (n := e) (m := 1)).2 (h2.of_dvd hobP)
      simpa using this
    have hpart : lPart l x = b := by
      calc lPart l x = x ^ e := hlp
        _ = (a * b) ^ e := by rw [habx]
        _ = b := by rw [hab.mul_pow, hae, hbe, one_mul]
    refine ⟨?_, hpart⟩
    rw [hlpr, hpart, ← habx, mul_inv_cancel_right]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)

def Congr (a b : G ℚ Ω →* c.Oˣ) : Prop := ∀ σ, ((a σ : c.Oˣ) : c.O) - ((b σ : c.Oˣ) : c.O) ∈ IsLocalRing.maximalIdeal c.O

def IsOmT (w : G ℚ Ω →* c.Oˣ) : Prop :=
  w ^ (l - 1) = 1 ∧ Congr c w (UpperTheory.V.Base.chiO (k := ℚ) (Ω := Ω) l c.O)

structure GDlit (K : Type) [Field K] [NumberField K] [Algebra K Ω] (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (w η : G ℚ Ω →* c.Oˣ) (a : ℕ) : Prop where
  om : IsOmT c w
  eta_ker : η.ker = galOf ℚ K Ω
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ σ = w σ ^ a
  a_lt : a < l - 1
  two_a : l - 1 ∣ 2 * a
  par : ∀ σ : G ℚ Ω, IsCC σ → UpperTheory.V.Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ∀ i j : ℕ, ¬ Congr c η (w ^ i * (Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹) ^ j)
  gen : ¬ l - 1 ∣ 2 * (e + a)

end UpperTheory.V.HV

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

def lossAll (l N n e : ℕ) : ℕ := Chr.loss l N n e + N.primeFactors.card * n.factorization l

def LayerLe (χ : PChar) (l : ℕ) [Fact l.Prime] (j t : ℕ) (B : ℝ) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField (Lchi χ l) L₀ →
    ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l j L₀ L₁ → VVat l L₁ t B

def CountIV : Prop :=
  ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, LayerLe χ l j t B → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (c : Coef l)
      (ψ : DirichletCharacter c.O h.N), h.IsChar ψ → Odd (orderOf (chiP l ψ)) →
        Chr.SumLe l c.O (fun e => Vlen Ω c e ψ) t (B + ((h.N : ℝ) * t) ^ C)

def PlusLe {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (S : Finset Nat.Primes) (t : ℕ) (B : ℝ) : Prop :=
  (∀ l ∈ S, ∀ e : ℕ, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
    ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤ B

def SumIn : Prop :=
  ∀ (χ : PChar) (l : Nat.Primes) (j : ℕ), (l : ℕ) ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, 0 ≤ B → LayerLe χ l j t B → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
        PlusLe ld {l} t (((h.N : ℝ) * t) ^ C + C * B)

def SumOut : Prop :=
  ∀ χ : PChar, ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ → r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d →
    ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p)
        (S : Finset Nat.Primes), (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∉ Bchi χ) → PlusLe ld S t (((h.N : ℝ) * t) ^ C)

def PointHV : Prop :=
  ∀ (χ : PChar) (j : ℕ → ℕ), ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ B : ℝ, 0 ≤ B →
      (∀ l ∈ Bchi χ, ∀ [Fact l.Prime], LayerLe χ l (j l) t B) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
        VVplusLe E t (((h.N : ℝ) * t) ^ C + C * B)

end UpperTheory.V.HV

end
end
