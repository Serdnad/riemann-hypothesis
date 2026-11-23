module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle001
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem embQ_smul (l : ℕ) [Fact l.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (z : ℤ_[l]) (x : M)
    (hx : (l : ℤ_[l]) • x = 0) : z • x = z.zmodRepr • x := by
  have hm := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  calc z • x = (z - (z.zmodRepr : ℤ_[l])) • x + (z.zmodRepr : ℤ_[l]) • x := by
        rw [sub_smul, sub_add_cancel]
    _ = z.zmodRepr • x := by
        rw [← hb, mul_smul, hx, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]

private theorem embQ_fl (l : ℕ) [hl : Fact l.Prime] (T : Type) [AddCommGroup T] (r : ℕ) (hTn : ∀ x : T, l • x = 0)
    (hcard : CardLe T (l ^ r)) : ∃ g : T →+ (Fin r → ZMod l), Function.Injective g := by
  obtain ⟨hfin, hc⟩ := hcard
  letI : Module (ZMod l) T := AddCommGroup.zmodModule hTn
  haveI := Fintype.ofFinite T
  haveI hF : Module.Finite (ZMod l) T := Module.Finite.of_finite
  haveI hFr : Module.Free (ZMod l) T := Module.Free.of_divisionRing (ZMod l) T
  set d := Module.finrank (ZMod l) T with hd_def
  have hcardT : Fintype.card T = l ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod l) (V := T), ZMod.card]
  have hd : d ≤ r := by
    have : l ^ d ≤ l ^ r := by rw [← hcardT, ← Nat.card_eq_fintype_card]; exact hc
    exact (Nat.pow_le_pow_iff_right hl.out.one_lt).mp this
  let b := @Module.finBasis (ZMod l) T _ _ _ hFr _ hF
  let E := b.equivFun
  have hadd : ∀ s t : T, E.toFun (s + t) = E.toFun s + E.toFun t := E.map_add'
  have hzero : E.toFun 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    exact left_eq_add.mp this
  let g : T →+ (Fin r → ZMod l) :=
    { toFun := fun t i => if h : (i : ℕ) < d then E.toFun t ⟨i, h⟩ else 0
      map_zero' := by
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hzero, Pi.zero_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.zero_apply]
      map_add' := by
        intro s t
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hadd, Pi.add_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply, add_zero] }
  refine ⟨g, ?_⟩
  intro s t hst
  have key : E.toFun s = E.toFun t := by
    funext j
    have := congr_fun hst (Fin.castLE hd j)
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.coe_castLE, Fin.eta] at this
    rwa [dif_pos j.isLt, dif_pos j.isLt] at this
  calc s = E.invFun (E.toFun s) := (E.left_inv s).symm
    _ = E.invFun (E.toFun t) := by rw [key]
    _ = t := E.left_inv t

theorem UpperTheory.V.Two.embedQZ :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      ∃ f : D →ₗ[ℤ_[l]] (Fin r → QZ l), Function.Injective f := by
  intro l _ D _ _ r htors hcard
  set Tl := Submodule.torsionBy ℤ_[l] D (l : ℤ_[l]) with hTl
  have hTl' : ∀ t : Tl, (l : ℤ_[l]) • t = 0 := by
    intro t
    have h := t.2
    rw [Submodule.mem_torsionBy_iff] at h
    exact Subtype.ext h
  have hTn : ∀ t : Tl, l • t = 0 := by
    intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    exact hTl' t
  obtain ⟨g, hg⟩ := embQ_fl l Tl r hTn hcard
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let e : ZMod l ≃+* ZMod (l ^ 1) := ZMod.ringEquivCongr (pow_one l).symm
  have hιl : ∀ a, (l : ℤ_[l]) • ι a = 0 := by
    intro a
    have := (hιrange (ι a)).mp ⟨a, rfl⟩
    simpa using this
  let ψ : Fin r → Tl →+ QZ l := fun i =>
    ((ι : ZMod (l ^ 1) →+ QZ l).comp e.toAddMonoidHom).comp ((Pi.evalAddMonoidHom (fun _ => ZMod l) i).comp g)
  have hψl : ∀ i t, (l : ℤ_[l]) • ψ i t = 0 := fun i t => hιl _
  let ψL : Fin r → Tl →ₗ[ℤ_[l]] QZ l := fun i =>
    { toFun := ψ i
      map_add' := (ψ i).map_add
      map_smul' := by
        intro z t
        simp only [RingHom.id_apply]
        rw [embQ_smul l z t (hTl' t), map_nsmul, ← embQ_smul l z (ψ i t) (hψl i t)] }
  have hext := fun i => (UpperTheory.V.PropA.qzInj l).out Tl.subtype Subtype.val_injective (ψL i)
  choose y hy using hext
  refine ⟨LinearMap.pi y, ?_⟩
  have hzeroT : ∀ t : Tl, (∀ i, y i t = 0) → t = 0 := by
    intro t ht
    have hgt : g t = 0 := by
      funext i
      have h1 := hy i t
      rw [Submodule.coe_subtype, ht i] at h1
      have h2 : ι (e (g t i)) = ι 0 := by
        rw [map_zero]
        exact h1.symm
      have h3 := hιinj h2
      simpa using h3
    exact hg (by rw [hgt, map_zero])
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hxi : ∀ x : D, LinearMap.pi y x = 0 → ∀ i, y i x = 0 := by
    intro x hx i
    have := congr_fun hx i
    simpa using this
  obtain ⟨k, hk⟩ := htors x
  induction k generalizing x with
  | zero =>
    simpa using hk
  | succ k ih =>
    have hlx : (l : ℤ_[l]) • x = 0 := by
      apply ih ((l : ℤ_[l]) • x)
      · rw [map_smul, hx, smul_zero]
      · rw [← mul_smul, ← pow_succ]
        exact hk
    have hmem : x ∈ Tl := (Submodule.mem_torsionBy_iff _ _).mpr hlx
    have := hzeroT ⟨x, hmem⟩ (hxi x hx)
    simpa using congrArg Subtype.val this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p m : ℕ} (h : p.Coprime m)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    rfl
  have hcast : (p : Ω) * (Nat.gcdA p m : Ω) + (m : Ω) * (Nat.gcdB p m : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) h1
    push_cast at this
    exact this
  have ha : A.valuation ((p : Ω) * (Nat.gcdA p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hp
  have hb : A.valuation ((m : Ω) * (Nat.gcdB p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hm
  have := lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
  rw [hcast, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Two.ineTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p : ℕ) (A : ValuationSubring Ω), p.Coprime (2 * M.m) → A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ cycU 2 (abU Ω (withI M)) := by
  intro Ω _ _ _ M p A hcop hp
  have h2 : p.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M.m) hcop
  have hM : p.Coprime M.m := Nat.Coprime.coprime_dvd_right (dvd_mul_left M.m 2) hcop
  have hW : p.Coprime (withI M).m := by
    show p.Coprime (M.m * max 4 1)
    exact Nat.Coprime.mul_right hM (by simpa using Nat.Coprime.pow_right 2 h2)
  intro g hg
  refine ⟨?_, ?_⟩
  · have := ineChar Ω (withI M).m A (not_lt_one_of_coprime A hW hp) hg
    rw [MonoidHom.mem_ker] at this
    show galChar Ω (withI M).m g ∈ (withI M).H
    rw [this]
    exact Subgroup.one_mem _
  · exact (places ℚ Ω 2 A).2.2.2 (not_lt_one_of_coprime A h2 hp) hg
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.invTwo_sign (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (hσ : σ ∈ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hn : σ ∉ U) (hS : ∀ s ∈ S, s ∈ V → s ∈ U) :
    ∃ ε ∈ CharOff V S 2, ε ⟨σ, hσ⟩ = 1 ∧ ∀ v : V, v.1 ∈ U → ε v = 0 := by
  classical
  set H : Subgroup V := U.subgroupOf V with hH
  have hidx : H.index = 2 := hi
  have hσH : (⟨σ, hσ⟩ : V) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]; exact hn
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · convert ho using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide
    · intro u hu
      have : u ∈ H := by
        rw [hH, Subgroup.mem_subgroupOf]; exact hS _ hu u.2
      simp [ε, this]
  refine ⟨ε, hmem, ?_, ?_⟩
  · simp [ε, hσH]
  · intro v hv
    have : v ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hv
    simp [ε, this]

theorem UpperTheory.V.Two.invTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (n : ℕ), U ≤ V → σ ∈ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n := by
  intro Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  classical
  obtain ⟨ε, hε, hεσ, hεU⟩ := UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS
  have hσσ : σ * σ ∈ U := by
    have h2 : (U.subgroupOf V).index = 2 := hi
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at this
  set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP
  let val : P → ZMod 2 := fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by
    by_cases hex : ∃ φ : P, val φ ≠ 0
    · obtain ⟨φ, hφ⟩ := hex
      exact ⟨φ, fun _ _ => (two _).resolve_left hφ⟩
    · push_neg at hex
      exact ⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩
  let χ : P → U → ZMod 2 := fun φ =>
    if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)
  have hχmem : ∀ φ, χ φ ∈ CharOff U S 2 := by
    intro φ
    simp only [χ]
    split_ifs
    · exact φ.1.2
    · exact add_mem φ.1.2 φ0.1.2
  have hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u := by
    intro φ u u' h
    simp only [χ]
    split_ifs
    · exact φ.2 u u' h
    · simp only [Pi.add_apply]
      rw [φ.2 u u' h, φ0.2 u u' h]
  have hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0 := by
    intro φ
    simp only [χ]
    split_ifs with h
    · exact h
    · have h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := (two _).resolve_left h
      have h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := hφ0 φ h
      simp only [Pi.add_apply]
      rw [h1, h2]
      rfl
  have hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u :=
    fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)
  choose ψ hψmem hψσ hψU using hext
  let f : P → CharOff V S 2 := fun φ =>
    ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩
  refine UpperTheory.V.Two.CardLe.of_injective hQ f ?_
  intro φ φ' hff
  have hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε) :=
    congrArg Subtype.val hff
  have hbranch : (val φ = 0 ↔ val φ' = 0) := by
    have := congrFun hfun ⟨σ, hσ⟩
    simp only [Pi.add_apply] at this
    rw [hψσ φ, hψσ φ'] at this
    by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢
  have hχ : χ φ = χ φ' := by
    funext u
    have := congrFun hfun ⟨u, hUV u.2⟩
    simp only [Pi.add_apply] at this
    rw [hψU φ u, hψU φ' u] at this
    have hu : ε ⟨u, hUV u.2⟩ = 0 := hεU _ u.2
    split_ifs at this <;> simpa [hu] using this
  apply Subtype.ext
  apply Subtype.ext
  simp only [χ] at hχ
  by_cases h : val φ = 0
  · have h' := hbranch.mp h
    simpa [h, h'] using hχ
  · have h' : ¬ val φ' = 0 := fun h' => h (hbranch.mpr h')
    simp only [h, h', if_false] at hχ
    exact add_right_cancel hχ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_valuation_lt_one_of_coprime_of_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ}
    (h : p.Coprime l) (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have hg := Nat.gcd_eq_gcd_ab p l
  rw [h.gcd_eq_one] at hg
  have hΩ : (1 : Ω) = (p : Ω) * ((p.gcdA l : ℤ) : Ω) + (l : Ω) * ((p.gcdB l : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hg
    push_cast at this
    exact this
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => by
    simpa using A.valuation_le_one (z : A)
  have h1 : A.valuation ((p : Ω) * ((p.gcdA l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hp
  have h2 : A.valuation ((l : Ω) * ((p.gcdB l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hΩ, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Two.charStep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (V : Subgroup (G F Ω)) (N p n k : ℕ), p.Coprime l → OrbLe V p k → (∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Ine (F := F) A ≤ V) →
      CardLe (CharOff V (ineOff F Ω N) l) n → CardLe (CharOff V (ineOff F Ω (N * p)) l) (n * l ^ k) := by
  intro F Ω _ _ _ _ _ l _ V N p n k hcop hT hV hN
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨T, hTc, hTp, hTcov⟩ := hT
  have hl : ∀ B ∈ T, ¬ B.valuation (l : Ω) < 1 := fun B hB => not_valuation_lt_one_of_coprime_of_lt_one B hcop (hTp B hB)
  choose γ hγ using fun B : {B // B ∈ T} => tameGen F Ω l B.1 (hl B.1 B.2)
  let L : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) := fun φ B =>
    (φ : V → ZMod l) ⟨(γ B : G F Ω), hV B.1 (hTp B.1 B.2) (γ B).2⟩
  have key : ∀ φ ψ : CharOff V (ineOff F Ω (N * p)) l, L φ = L ψ →
      ((φ : V → ZMod l) - (ψ : V → ZMod l)) ∈ CharOff V (ineOff F Ω N) l := by
    intro φ ψ h
    let χ : V → ZMod l := (φ : V → ZMod l) - (ψ : V → ZMod l)
    have hm : IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω (N * p) → χ u = 0 := (φ - ψ).2
    obtain ⟨hlc, hadd, hoff⟩ := hm
    change IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω N → χ u = 0
    refine ⟨hlc, hadd, fun u hu => ?_⟩
    obtain ⟨A, hAN, huA⟩ := hu
    by_cases hAp : A.valuation (p : Ω) < 1
    · obtain ⟨B, hB, v, hv, rfl⟩ := hTcov A hAp
      have hg : v⁻¹ * (u : G F Ω) * v ∈ Ine B := (ineConj F Ω v).1 B u huA
      have hBV : Ine (F := F) B ≤ V := hV B (hTp B hB)
      let Bt : {B // B ∈ T} := ⟨B, hB⟩
      let ι : Ine (F := F) B → V := fun σ => ⟨(σ : G F Ω), hBV σ.2⟩
      have hι : ∀ a b : Ine (F := F) B, ι (a * b) = ι a * ι b := fun a b => rfl
      let χ' : Ine (F := F) B → ZMod l := fun σ => χ (ι σ)
      have hcont : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
      have hχlc : IsLocallyConstant χ' := hlc.comp_continuous hcont
      have hχadd : ∀ a b : Ine (F := F) B, χ' (a * b) = χ' a + χ' b := by
        intro a b
        show χ (ι (a * b)) = χ (ι a) + χ (ι b)
        rw [hι]
        exact hadd _ _
      have hχγ : χ' (γ Bt) = 0 := by
        have := congrFun h Bt
        exact sub_eq_zero.mpr this
      have h0 := hγ Bt χ' hχlc hχadd hχγ ⟨_, hg⟩
      let v' : V := ⟨v, hv⟩
      have e3 : χ (v'⁻¹ * u * v') = 0 := h0
      have e1 : χ (v'⁻¹ * u * v') = χ v'⁻¹ + χ u + χ v' := by
        rw [hadd, hadd]
      have h1 : χ 1 = 0 := by
        have := hadd 1 1
        rw [mul_one] at this
        linear_combination -this
      have e2 : χ v'⁻¹ + χ v' = 0 := by
        rw [← hadd, inv_mul_cancel, h1]
      linear_combination e3 - e1 - e2
    · apply hoff u
      refine ⟨A, ?_, huA⟩
      push_cast
      rw [map_mul]
      intro hlt
      exact (not_lt.mpr (one_le_mul (not_lt.mp hAN) (not_lt.mp hAp))) hlt
  haveI : Nonempty (CharOff V (ineOff F Ω (N * p)) l) := ⟨0⟩
  let s := Function.invFun L
  have hs : ∀ φ, L (s (L φ)) = L φ := fun φ => Function.invFun_eq ⟨φ, rfl⟩
  let f : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l :=
    fun φ => (L φ, ⟨(φ : V → ZMod l) - (s (L φ) : V → ZMod l), key φ (s (L φ)) (hs φ).symm⟩)
  have hf : Function.Injective f := by
    intro φ ψ hfe
    have h1 : L φ = L ψ := congrArg Prod.fst hfe
    have h2 := congrArg (fun x => ((x.2 : CharOff V (ineOff F Ω N) l) : V → ZMod l)) hfe
    simp only [f] at h2
    rw [h1] at h2
    exact Subtype.ext (sub_left_inj.mp h2)
  haveI : Finite (CharOff V (ineOff F Ω N) l) := hN.1
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (CharOff V (ineOff F Ω (N * p)) l)
      ≤ Nat.card (({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l) :=
        Nat.card_le_card_of_injective f hf
    _ = l ^ T.card * Nat.card (CharOff V (ineOff F Ω N) l) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod]
        simp
    _ ≤ l ^ k * n := Nat.mul_le_mul (Nat.pow_le_pow_right (Fact.out : l.Prime).pos hTc) hN.2
    _ = n * l ^ k := Nat.mul_comm _ _
end
