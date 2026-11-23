module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.SetTheory.ZFC.PSet
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestCharacter

theorem emb_pow (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Fintype F] [CharP F p] [Field k]
    (f g : F →+* k) : ∃ n : ℕ, ∀ a, g a = f a ^ p ^ n := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra F k := f.toAlgebra
  letI : Algebra (ZMod p) k := (f.comp (algebraMap (ZMod p) F)).toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : F →ₐ[ZMod p] k :=
    { g with
      commutes' := fun r => by
        have : g.comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) k := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun this r }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 (g'.restrictNormal F)
  refine ⟨n, fun a => ?_⟩
  have h1 := g'.restrictNormal_commutes F a
  have h2 := DFunLike.congr_fun hn a
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h2
  rw [← h2, map_pow] at h1
  exact h1.symm

theorem eq_of_root {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (q : ℕ)
    (hq : (q : R) ∈ IsLocalRing.maximalIdeal R) {x y : R} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue R x = IsLocalRing.residue R y) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y q
  rw [hx, hy] at h1
  have h2 : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 :=
    mul_right_cancel₀ (sub_ne_zero.2 hne) (by rw [h1, _root_.one_mul])
  have h3 := congrArg (IsLocalRing.residue R) h2

  rw [map_sum, map_one] at h3
  simp only [map_mul, map_pow, h] at h3
  rw [geom_sum₂_self] at h3
  have h4 : ((q : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact hq
  rw [h4, zero_mul] at h3
  exact zero_ne_one h3

theorem fund {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {x y z : R}
    (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y) (hz : z ^ p ^ n = z)
    (h : z - x - y ∈ IsLocalRing.maximalIdeal R) : z - x - y ∈ Ideal.span {(p : R)} := by
  set d := z - x - y with hd
  have hz' : z = (x + y) + d := by rw [hd]; ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (x + y) d n
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp x y n
  rw [← hz', hz, hs, hx, hy] at hr
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 2 := by
    have := Nat.one_lt_pow hn hp.one_lt
    exact ⟨p ^ n - 2, by omega⟩
  have hu : IsUnit (1 - d ^ (m + 1)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal R) h _ (Nat.succ_pos m)
  have h1 : d * (1 - d ^ (m + 1)) ∈ Ideal.span {(p : R)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨x * y * s + (x + y) * d * r, ?_⟩
    rw [hm] at hr
    linear_combination hd - hr
  exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h1

theorem core (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (ρ : Sg → F →+* IsLocalRing.ResidueField R) (χ : Sg → F →*₀ R)
    (hχ : ∀ τ a, IsLocalRing.residue R (χ τ a) = ρ τ a) (hφ : ∀ τ a, ρ (φ' τ) a = ρ τ a ^ p) :
    ∃ (σ' : MulChar F R) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a) ∧
      ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : ((Fintype.card F : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hn, Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hp _ n.pos
  have hroot : ∀ τ a, χ τ a ^ Fintype.card F = χ τ a := fun τ a => by
    rw [← map_pow, FiniteField.pow_card]
  choose ee hee using fun τ => emb_pow p (ρ τ₀) (ρ τ)
  let σ' : MulChar F R :=
    { (χ τ₀).toMonoidHom with
      map_nonunit' := fun a ha => by
        have : a = 0 := by simpa using ha
        subst this
        exact map_zero (χ τ₀) }
  have hσ : ∀ a, σ' a = χ τ₀ a := fun _ => rfl
  have key : ∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a := fun τ a => by
    rw [MulChar.pow_apply' _ (pow_ne_zero _ hpp.ne_zero), hσ, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hee, map_pow]
  refine ⟨σ', ee, fun a b => ?_, key, fun τ => ?_⟩
  · rw [hσ, hσ, hσ]
    refine fund hpp n.ne_zero (hn ▸ hroot _ _) (hn ▸ hroot _ _) (hn ▸ hroot _ _) ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, hχ, hχ, hχ, map_add (f := _)]
    ring
  · ext a
    rw [← key, pow_succ, pow_mul, MulChar.pow_apply' _ hpp.ne_zero, ← key, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hφ, map_pow]

theorem overC (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (hvp : v (p : C) < 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (σ : Sg → F →+* IsLocalRing.ResidueField O) (χ : Sg → F →*₀ C)
    (hχ : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1)
    (hφ : ∀ τ a, σ (φ' τ) a = σ τ a ^ p) :
    ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧
      (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hunit : ∀ a : RC, v (a : C) = 1 → IsUnit a := fun a ha => by
    have h0 : (a : C) ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
    refine IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, (hv _).2 (by rw [map_inv₀, ha, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  haveI : IsLocalRing RC := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases ((hv _).1 a.2).eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · exact Or.inr (hunit _ (v.map_one_sub_of_lt h))
  have hnu : ∀ x : RC, (∀ u ∈ RC, u * (x : C) ≠ 1) → x ∈ IsLocalRing.maximalIdeal RC := fun x hx hu => by
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    exact hx u u.2 (congrArg Subtype.val hu)
  have hp : (p : RC) ∈ IsLocalRing.maximalIdeal RC := hnu _ fun u hu h => by
    have h1 := congrArg v h
    rw [map_mul, map_one] at h1
    have h2 : v u * v ((p : RC) : C) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 hu) zero_le (by simpa using hvp)
    exact h2.ne h1
  have hmem : ∀ τ a, χ τ a ∈ RC := fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have := RC.add_mem (hχ τ a o ho).1 (RC.algebraMap_mem o)
    simpa using this
  let χ' : Sg → F →*₀ RC := fun τ =>
    { toFun := fun a => ⟨χ τ a, hmem τ a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  have hdiff : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ' τ a - algebraMap O RC o ∈ IsLocalRing.maximalIdeal RC := fun τ a o ho =>
    hnu _ (hχ τ a o ho).2
  haveI : IsLocalHom (algebraMap O RC) := ⟨fun o ho => by
    by_contra hno
    have h1 := hdiff τ₀ 0 o (by rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hno)
    rw [map_zero, zero_sub, neg_mem_iff] at h1
    exact h1 ho⟩
  let ψ := IsLocalRing.ResidueField.map (algebraMap O RC)
  obtain ⟨σ', ee, h1, h2, h3⟩ := core p hp τ₀ φ' (fun τ => ψ.comp (σ τ)) χ' (fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have h := hdiff τ a o ho
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h
    rw [h, RingHom.comp_apply, ← ho]
    rfl) (fun τ a => by rw [RingHom.comp_apply, RingHom.comp_apply, hφ, map_pow])
  exact ⟨σ', ee, h1, fun τ a => congrArg Subtype.val (h2 τ a), h3⟩

theorem inj_loc {A Ω O : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime]
    [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro o ho
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
  have h1 := congrArg (algebraMap O Ω) h
  rw [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at h1
  have ha : a = 0 := IsIntegralClosure.algebraMap_injective A ℤ Ω (by rw [map_zero]; exact h1.symm)
  rw [ha, map_zero] at h
  exact (IsLocalization.map_units O s).mul_left_eq_zero.1 h

theorem exists_lift {A Ω T : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    [CommRing T] [Algebra.IsIntegral ℤ T] (f : T →+* Ω) : ∃ g : T →+* A, ∀ t, algebraMap A Ω (g t) = f t := by
  letI : Algebra T Ω := f.toAlgebra
  exact ⟨(IsIntegralClosure.lift ℤ A Ω (S := T) : T →ₐ[ℤ] A), fun t => IsIntegralClosure.algebraMap_lift ℤ A Ω t⟩

end PositivityTheory.Xgn.TestCharacter

theorem PositivityTheory.Xgn.test_character_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ _ _ _ b _ φ hφ A _ _ _ m _ _ O _ _ _ _ _ _ _ t₀ Sg _ e φ' F
    _ _ _ pq sc w σ hO _ G c' _ P i _ _ C _ _ _ _ RC hT χ hχ
  obtain ⟨⟨τ₀, -⟩, -, he, hsurj, hσ, -, ⟨-, -, hpO⟩, -⟩ := hO
  obtain ⟨-, ⟨v, hv, hvp⟩, -⟩ := hT
  refine PositivityTheory.Xgn.TestCharacter.overC p RC v hv hvp τ₀ φ' σ χ hχ fun τ a => ?_
  have hinj := PositivityTheory.Xgn.TestCharacter.inj_loc (Ω := Ω) (O := O) m
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.Xgn.TestCharacter.exists_lift (A := A)
    (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))
  let g : 𝓞 c.F →+* O := (algebraMap A O).comp g₀
  have hg : ∀ t, algebraMap O Ω (g t) = 𝔐.cst (t : c.F) := fun t => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hg₀]; rfl
  obtain ⟨a, rfl⟩ := hsurj a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hint : ∀ s, IsIntegral ℤ (labelEmb c s a) := fun s =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom
  obtain ⟨o₁, h₁, h₁'⟩ := hσ (φ' τ) a
  obtain ⟨o₂, h₂, h₂'⟩ := hσ τ a
  obtain ⟨u₁, hu₁⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (φ (e τ)) a := ⟨⟨_, hint (φ (e τ))⟩, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (e τ) a := ⟨⟨_, hint (e τ)⟩, rfl⟩
  have hn := hφ ((IsLocalRing.maximalIdeal O).comap g) (Ideal.comap_isPrime _ _)
    (by rw [Ideal.mem_comap, map_natCast]; exact hpO) (e τ) a u₁ u₂ hu₁ hu₂
  have e₁ : g u₁ = o₁ := hinj (by rw [hg, h₁, he, hu₁]; rfl)
  have e₂ : g u₂ = o₂ := hinj (by rw [hg, h₂, hu₂]; rfl)
  rw [Ideal.mem_comap, map_sub, map_pow, e₁, e₂, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero] at hn
  rw [← h₁', ← h₂', hn]
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ProperZeroNumerical

theorem subset_of_specializes {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T]
    {Z V : Set T} (hZ : IsClosed Z) (hc : IsPreconnected Z) (hV : IsOpen V) (hne : (Z ∩ V).Nonempty)
    (hs : ∀ y x : T, y ∈ Z → y ∈ V → y ⤳ x → x ∈ V) : Z ⊆ V := by
  have hcl : IsClosed (Z ∩ V) := by
    obtain ⟨S, hfin, hScl, hSirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
    have e : Z ∩ V = ⋃ t ∈ {t ∈ S | (t ∩ V).Nonempty}, t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨hx, hxV⟩
        rw [hU] at hx
        obtain ⟨t, ht, hxt⟩ := hx
        exact ⟨t, ⟨ht, x, hxt, hxV⟩, hxt⟩
      · rintro ⟨t, ⟨ht, htV⟩, hxt⟩
        have hsub : t ⊆ Z := by rw [hU]; exact Set.subset_sUnion_of_mem ht
        obtain ⟨y, hy⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
        exact ⟨hsub hxt, hs y x (hsub hy.mem) ((hy.mem_open_set_iff hV).2 htV) (hy.specializes hxt)⟩
    rw [e]
    exact (hfin.subset (by exact fun t ht => ht.1)).isClosed_biUnion fun t ht => hScl t ht.1
  intro x hx
  by_contra hxV
  obtain ⟨z, hz, hzV, hz'⟩ := hc V (Z ∩ V)ᶜ hV hcl.isOpen_compl
    (fun w hw => by
      by_cases h : w ∈ V
      · exact Or.inl h
      · exact Or.inr fun h' => h h'.2) hne ⟨x, hx, fun h => hxV h.2⟩
  exact hz' ⟨hz, hzV⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem unit_change {L : Lat ξ Ω} {p : Cpt ξ} {σ π e f : Ω} {M : ℕ} (he : L.IsGenAt p e) (hf : L.IsGenAt p f)
    (h : unitAt ξ p (π / (σ / f) ^ M)) : unitAt ξ p (π / (σ / e) ^ M) := by
  rw [CurvePositivity.change_gen σ π e f M hf.1]
  exact unit_mul h (unit_pow (ProjectiveLinePlaces.unitAt_div he hf) M)

theorem exists_local_gen {L : Lat ξ Ω} (h : L.IsVB 1 ⊤) (p : Cpt ξ) :
    ∃ (U : X.Opens) (e : Ω), p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q e := by
  obtain ⟨U, hp, b, -, hb⟩ := h p (Set.mem_univ p)
  refine ⟨U, b 0, hp, fun q hq => ?_⟩
  obtain ⟨hli, hspan⟩ := hb q (Set.mem_univ q) hq
  refine ⟨hli.ne_zero 0, ?_⟩
  rw [hspan]
  congr 1
  ext x
  simp [eq_comm]

end PositivityTheory.Xgn.ProperZeroNumerical

open PositivityTheory.Xgn.ProperZeroNumerical in
theorem PositivityTheory.Xgn.normal_proper_line_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb hnum hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := { }
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, e₀, c₀, he₀, hL₀, hσ₀, hu₀⟩ :=
    exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.1 L σ hvb hgen
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  set π : Ω := algebraMap O Ω ϖ ^ a with hπ
  let Good : Cpt ξ → Prop := fun p => ∃ e, L.IsGenAt p e ∧ unitAt ξ p (π / (σ / e) ^ M)
  let V : Set X := ⋃₀ {W | IsOpen W ∧ ∀ q : Cpt ξ, q.1 ∈ W → Good q}
  have hVo : IsOpen V := isOpen_sUnion fun W hW => hW.1
  have hV : ∀ q : Cpt ξ, q.1 ∈ V ↔ Good q := by
    intro q
    constructor
    · rintro ⟨W, hW, hq⟩
      exact hW.2 q hq
    · rintro ⟨e, he, hu⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      obtain ⟨U', hqU', hU'⟩ := (regAt_unitAt_open X Ω ξ q _).2 (unit_change (hb q hqU) he hu)
      exact ⟨(U : Set X) ∩ U', ⟨U.isOpen.inter U'.isOpen, fun r hr => ⟨b, hb r hr.1, hU' r hr.2⟩⟩, hqU, hqU'⟩
  have hZ : IsClosed (zeroSet ξ (algebraMap O Ω ϖ)) := by
    have e : zeroSet ξ (algebraMap O Ω ϖ) =
        closure {genPt ξ} ∩ s ⁻¹' (PrimeSpectrum.zeroLocus ({ϖ} : Set O)) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.1 h1,
          Set.singleton_subset_iff.2 (not_not.1 fun h => h2 ((hunit ⟨x, h1⟩ ϖ).2 h))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.2 h1, fun h =>
          (hunit ⟨x, specializes_iff_mem_closure.2 h1⟩ ϖ).1 h (Set.singleton_subset_iff.1 h2)⟩
    rw [e]
    exact isClosed_closure.inter ((PrimeSpectrum.isClosed_zeroLocus _).preimage s.continuous)
  have hsub : zeroSet ξ (algebraMap O Ω ϖ) ⊆ V := by
    refine subset_of_specializes hZ hconn.2 hVo ⟨p₀.1, ⟨p₀.2, hp₀⟩, (hV p₀).2 ⟨e₀, ⟨he₀, hL₀⟩, ?_⟩⟩ ?_
    · have e1 : σ / e₀ = c₀ := by rw [hσ₀, smul_eq_mul, mul_div_cancel_right₀ _ he₀]
      rw [e1, ← inv_div]
      exact unit_inv hu₀
    · rintro y x ⟨hy, hyn⟩ hyV hyx
      obtain ⟨x', hx', hcl⟩ :=
        (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton ⟨x, subset_closure rfl⟩
      have hxx : x ⤳ x' := specializes_iff_mem_closure.2 hx'
      refine hxx.mem_open hVo ?_
      have hyx' : y ⤳ x' := hyx.trans hxx
      let q : Cpt ξ := ⟨x', hy.trans hyx'⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      refine (hV q).2 ⟨b, hb q hqU, ?_⟩
      by_contra hnu
      obtain ⟨e, he, hue⟩ := (hV ⟨y, hy⟩).1 hyV
      obtain ⟨Γ, i, -, hη, hz⟩ := GlobalTheory.T.special_fibre_closed_specialization X Ω ξ O s ϖ hϖ hinj hs hg ⟨y, hy⟩ q (π / (σ / b) ^ M) hyn hyx' hcl
        (hreg q b (hb q hqU)) (unit_change (hb ⟨y, hy⟩ (hyx'.mem_open U.isOpen hqU)) he hue) hnu
      have hq : q = ⟨centre (Γ.z i), Γ.z_spec i⟩ := Subtype.ext hz.symm
      have hηU : centre Γ.η ∈ U := (Γ.generic_centre_specializes i).mem_open U.isOpen (by rw [hz]; exact hqU)
      apply hnu
      have hbq := hb q hqU
      rw [hq] at hbq ⊢
      exact PositivityTheory.Xgn.degree_zero_curve_positive X Ω ξ O s _ L σ π M Γ hg hvb hM (hnum Γ) hreg
        (fun e' he' => unit_change he' (hb ⟨centre Γ.η, Γ.η_spec⟩ hηU) hη) i (Γ.z_spec i) b hbq
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hu : unitAt ξ p (algebraMap O Ω ϖ)
  · have hp : p ∈ genFibre O ξ := by
      intro o ho
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
      rw [map_mul, map_pow]
      refine unit_mul ((hunit p _).2 fun h => ?_) (unit_pow hu n)
      exact (s p.1).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
    refine ⟨σ, 1, (hgen p hp).1, (hgen p hp).2, (one_smul _ _).symm, ?_⟩
    rw [one_pow, one_div]
    refine unit_inv ⟨zpow_ne_zero a hu.1, ZLat.zpow_mem_regAt hu a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hu _
  · obtain ⟨e, he, hue⟩ := (hV p).1 (hsub ⟨p.2, hu⟩)
    refine ⟨e, σ / e, he.1, he.2, ?_, ?_⟩
    · rw [smul_eq_mul, div_mul_cancel₀ _ he.1]
    · rw [← inv_div]
      exact unit_inv hue
end
