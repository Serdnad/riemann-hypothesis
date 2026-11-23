module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaLevel_object_descends_fg_subfield : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  first | exact @GlobalTheory.ThetaDescent.descends_to_fg_subfield | exact GlobalTheory.ThetaDescent.descends_to_fg_subfield | (intros; apply GlobalTheory.ThetaDescent.descends_to_fg_subfield <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  first | exact @GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | exact GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | (intros; apply GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.JoinRing

def coprimeNat (p : ℕ) (A : Type) [CommRing A] : Submonoid A where
  carrier := {x | ∃ m : ℕ, m.Coprime p ∧ x = m}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Nat.Coprime.mul_left ha hb, by simp⟩

theorem ne_zero_of_coprime {p m : ℕ} (hp : p.Prime) (hm : m.Coprime p) : m ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hm)

theorem coprimeNat_le {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] [IsDomain A] [CharZero A] :
    coprimeNat p A ≤ nonZeroDivisors A := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm))

theorem isLocalization_of_le_closure {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] (T : Subring ℂ) [Algebra A T]
    (hinj : Function.Injective (algebraMap A T)) (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsLocalization (coprimeNat p A) T := by
  have h0 : ∀ m : ℕ, m.Coprime p → (m : ℂ) ≠ 0 := fun m hm => Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm)
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹}),
      ∃ m : ℕ, m.Coprime p ∧ ∃ a, z * m = (algebraMap A T a : ℂ) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨m, hm, rfl⟩
      · exact ⟨1, by simp, a, by simp⟩
      · exact ⟨m, hm, 1, by simp [h0 m hm]⟩
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * k + b * m, ?_⟩
      simp only [map_add (f := _), map_mul, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, hm, a, ha⟩ := hx
      refine ⟨m, hm, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    simp only [map_natCast]
    refine IsUnit.of_mul_eq_one ⟨_, hinv m hm⟩ (Subtype.ext ?_)
    simp [h0 m hm]
  · intro z
    obtain ⟨m, hm, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨m, m, hm, rfl⟩), Subtype.ext ?_⟩
    simp only [map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem inv_mem_ZP {p m : ℕ} (k : ℕ) (hm : m.Coprime p) : (m : ℂ)⁻¹ ∈ ZP p k :=
  Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)


open CycBase in
theorem isDedekindDomain_ZP {n p : ℕ} (e : ℕ) (hn : n.Prime) (hp : p.Prime) : IsDedekindDomain (ZP p (n ^ e)) := by
  open GlobalTheory.ZM.CycBase in
  haveI := Fact.mk hn
  have hk : n ^ e ≠ 0 := NeZero.ne _
  haveI : IsCyclotomicExtension {n ^ e} ℚ (CF (n ^ e)) := cyc
  haveI : NumberField (CF (n ^ e)) := IsCyclotomicExtension.numberField {n ^ e} ℚ _
  let io : 𝓞 (CF (n ^ e)) →+* ℂ := (CF (n ^ e)).val.toRingHom.comp (algebraMap _ (CF (n ^ e)))
  have hio : Function.Injective io :=
    Subtype.val_injective.comp (RingOfIntegers.coe_injective (K := CF (n ^ e)))
  letI : Algebra (𝓞 (CF (n ^ e))) (ZP p (n ^ e)) := (io.codRestrict _ (mem_ZP p n e hn)).toAlgebra
  have : IsLocalization (coprimeNat p (𝓞 (CF (n ^ e)))) (ZP p (n ^ e)) := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => hio (congrArg (fun z : ZP p (n ^ e) => (z : ℂ)) h))
      (fun m hm => inv_mem_ZP _ hm) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨(zF_prim hk).toInteger, rfl⟩
    · exact Or.inr h
  exact IsLocalization.isDedekindDomain _ (coprimeNat_le hp (𝓞 (CF (n ^ e)))) _

theorem isDedekindDomain_RZ_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S A e : ℕ}
    (hS : 0 < S) (hA : 0 < A) (h : A ∣ S ^ e) : IsDedekindDomain (RZ H S A) := by
  obtain ⟨l, rfl⟩ : ∃ l : Level H, l.A = A := ⟨GlobalTheory.HostModel.level H A hA, rfl⟩
  exact GlobalTheory.BaseRing.isDedekindDomain_RZ l hS h

theorem flat_inclusion {S T : Subring ℂ} (h : S ≤ T) [IsDedekindDomain S] : Flat (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have htf : Module.IsTorsionFree S T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S T))

theorem noetherian_preimmersion {p : ℕ} (hp : p.Prime) {S T : Subring ℂ} (h : S ≤ T) [IsNoetherianRing S]
    (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ((S : Set ℂ) ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsNoetherianRing T ∧ IsPreimmersion (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have hL : IsLocalization (coprimeNat p S) T := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h))
      hinv (hT.trans (Subring.closure_mono ?_))
    rintro x (hx | hx)
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr hx
  exact ⟨IsLocalization.isNoetherianRing (coprimeNat p S) _ inferInstance,
    IsPreimmersion.of_isLocalization (R := S) (S := T) (coprimeNat p S)⟩

theorem join_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N p : ℕ), n.Prime → (∃ j, 1 ≤ j ∧ N = n ^ j) → p.Prime → p ≠ n → IsDedekindDomain (RZ H n N) ∧ IsNoetherianRing ↥(RZ H n N ⊔ ZP p N) ∧ Flat (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ IsPreimmersion (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ Flat (spMap (Subring.inclusion (le_sup_right : ZP p N ≤ RZ H n N ⊔ ZP p N))) := by
  rintro E _ _ _ H n N p hn ⟨j, -, hN⟩ hp -
  have hD : IsDedekindDomain (RZ H n N) :=
    isDedekindDomain_RZ_of_dvd H (e := j) hn.pos (hN ▸ pow_pos hn.pos j) (hN ▸ dvd_rfl)
  have hZ : IsDedekindDomain (ZP p N) := hN ▸ isDedekindDomain_ZP j hn hp
  have h := noetherian_preimmersion hp (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N)
    (fun m hm => (le_sup_right : ZP p N ≤ _) (inv_mem_ZP _ hm))
    (sup_le (fun x hx => Subring.subset_closure (Or.inl hx)) (Subring.closure_mono (by
      rintro x (rfl | h)
      · exact Or.inl (RZ.ze H n N).2
      · exact Or.inr h)))
  exact ⟨hD, h.1, flat_inclusion _, h.2, flat_inclusion _⟩

end GlobalTheory.JoinRing
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.isVeryAmpleSectionSystem_of_projectiveCoordinates : ∀ (K σ : Type) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (Z : Scheme.{0}) (p : Z ⟶ Sp K) (M : LB Z) (th : σ → M.Sec), ProjRep I p M th → VAmp p M th := by
  first | exact @GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep | exact GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep | (intros; apply GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_quotient_model_by_tame_finite_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  first | exact @GlobalTheory.Models.exists_quotient_model | exact GlobalTheory.Models.exists_quotient_model | (intros; apply GlobalTheory.Models.exists_quotient_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPrime

theorem eval₂_smul_of_isHomogeneous {o K I : Type} [CommRing o] [CommRing K] (β : o →+* K)
    (v : I → K) (c : K) {F : MvPolynomial I o} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval₂ β (c • v) F = c ^ n * MvPolynomial.eval₂ β v F := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ i ∈ m.support, m i = n := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem exists_homogenisation {o I D : Type} [CommRing o] (a₀ : I) (a : D → I)
    (G : MvPolynomial D o) : ∃ (n : ℕ) (H : MvPolynomial I o),
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K), v a₀ ≠ 0 →
        MvPolynomial.eval₂ β v H = v a₀ ^ n * MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, fun K _ β v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, H, hH⟩ := hp
    obtain ⟨m, H', hH'⟩ := hq
    refine ⟨n + m, MvPolynomial.X a₀ ^ m * H + MvPolynomial.X a₀ ^ n * H', fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, hH K β v hv, hH' K β v hv]
    ring
  | mul_X p i hp =>
    obtain ⟨n, H, hH⟩ := hp
    refine ⟨n + 1, H * MvPolynomial.X (a i), fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hH K β v hv]
    field_simp
    ring

noncomputable def coneIdeal {o I Z : Type} [CommRing o] (em : o →+* ℂ) (B : Set Z) (θ : Z → I → ℂ) :
    Ideal (MvPolynomial I o) :=
  ⨅ (z : Z) (_ : z ∈ B) (c : ℂ) (_ : c ≠ 0), RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z))

theorem mem_coneIdeal {o I Z : Type} [CommRing o] {em : o →+* ℂ} {B : Set Z} {θ : Z → I → ℂ}
    {F : MvPolynomial I o} : F ∈ coneIdeal em B θ ↔
      ∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ em (c • θ z) F = 0 := by
  simp [coneIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem coneIdeal_isPrime {o I : Type} [CommRing o] [Countable o] [Countable I] (em : o →+* ℂ)
    {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ) (ho : IsOpen B)
    (hc : IsPreconnected B) (hn : B.Nonempty) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B) :
    (coneIdeal em B θ).IsPrime := by
  obtain ⟨z, hz, c, hc0, h⟩ :=
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em I d B θ ho hc hn hd
  have : coneIdeal em B θ = RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z)) := by
    ext F
    rw [mem_coneIdeal, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
    exact ⟨fun hF => hF z hz c hc0, h F⟩
  rw [this]
  exact RingHom.ker_isPrime _

theorem exists_ratios {o I : Type} [CommRing o] [Finite I] (em : o →+* ℂ)
    (hem : Function.Injective em) {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ)
    (ho : IsOpen B) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B)
    (hf : ∀ z ∈ B, {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) (a₁ : I)
    (h₁ : MvPolynomial.X a₁ ∉ coneIdeal em B θ) :
    ∃ (a₀ : I) (a : Fin d → I), MvPolynomial.X a₀ ∉ coneIdeal em B θ ∧
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K),
        RingHom.ker (MvPolynomial.eval₂Hom β v) = coneIdeal em B θ →
        ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 →
          G = 0 := by
  rw [mem_coneIdeal] at h₁
  push Not at h₁
  obtain ⟨z₁, hz₁, c₁, -, h₁⟩ := h₁
  have h₁' : θ z₁ a₁ ≠ 0 := by
    intro h
    apply h₁
    simp [h]
  have hcont : ContinuousAt (fun z => θ z a₁) z₁ :=
    (hd a₁).continuousOn.continuousAt (ho.mem_nhds hz₁)
  have hU : {z | z ∈ B ∧ θ z a₁ ≠ 0} ∈ nhds z₁ :=
    Filter.inter_mem (ho.mem_nhds hz₁) (hcont.eventually_ne h₁')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsub : Metric.ball z₁ ε ⊆ B := fun z hz => (hball hz).1
  obtain ⟨a₀, a, ⟨z₀, hz₀, h₀⟩, hind⟩ := GlobalTheory.CountableFibres.exists_independent_ratios d I
    (Metric.ball z₁ ε) θ Metric.isOpen_ball (convex_ball z₁ ε).isPreconnected
    ⟨z₁, Metric.mem_ball_self hε⟩ (fun a => (hd a).mono hsub)
    (fun z hz => ⟨fun h => (hball hz).2 (by rw [h]; rfl),
      Set.Countable.mono (fun z' hz' => And.intro (hsub hz'.1) hz'.2) (hf z (hsub hz))⟩)
  have hX : MvPolynomial.X a₀ ∉ coneIdeal em B θ := by
    intro h
    have := mem_coneIdeal.1 h z₀ (hsub hz₀) 1 one_ne_zero
    simp [h₀] at this
  refine ⟨a₀, a, hX, fun K _ β v hv G hG => ?_⟩
  have hv₀ : v a₀ ≠ 0 := by
    intro h
    apply hX
    rw [← hv, RingHom.mem_ker]
    simp [h]
  obtain ⟨n, H, hH⟩ := exists_homogenisation a₀ a G
  have hHP : H ∈ coneIdeal em B θ := by
    rw [← hv, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hH K β v hv₀, hG, mul_zero]
  have hmap : MvPolynomial.map em G = 0 := by
    refine hind _ fun z hz hz0 => ?_
    have := mem_coneIdeal.1 hHP z (hsub hz) 1 one_ne_zero
    rw [one_smul, hH ℂ em _ hz0] at this
    rw [MvPolynomial.eval_map]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hz0)
  exact MvPolynomial.map_injective em hem (by rw [hmap, map_zero])

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) :
    Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (by simp)
  exact hf.countable

theorem span_range_eq_top {K I : Type} [Field K] {v : I → K} (hv : v ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (IsUnit.mk0 _ ha)

theorem exists_prime_independent_ratios : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  intro hL hL2 g N' J Mat κ w w' o _ b em C d hAr hG p a₁ hN hp hle hX
  obtain ⟨-, hft, hem⟩ := hAr
  have : Countable o := countable_of_finiteType o hft
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨r, B, θ, hfam, hcov⟩ := hG.fam
  have hmem : ∀ F, F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v →
      MvPolynomial.eval₂ em v F = 0 := by
    intro F
    simp [thIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  have hinf : (Finset.univ : Finset (Fin r)).inf (fun i => coneIdeal em (B i) (θ i)) ≤ p := by
    refine le_trans (fun F hF => ?_) hle
    rw [hmem]
    intro t v ht hv
    obtain ⟨i, z, hz, hθ⟩ := hcov t ht
    have hFi : F ∈ coneIdeal em (B i) (θ i) :=
      (Finset.inf_le (f := fun i => coneIdeal em (B i) (θ i)) (Finset.mem_univ i)) hF
    have key : ∃ c : ℂ, c ≠ 0 ∧ v = c • θ i z := by
      by_cases h0 : θ i z = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        by_contra hne
        rw [h0, smul_zero] at hne
        obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ v (θ i z) hv hθ
          (span_range_eq_top hne)
        apply hne
        funext a
        have := hu a
        rw [h0] at this
        simpa using this
      · obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ (θ i z) v hθ hv
          (span_range_eq_top h0)
        exact ⟨u, u.ne_zero, funext hu⟩
    obtain ⟨c, hc, rfl⟩ := key
    exact mem_coneIdeal.1 hFi z hz c hc
  obtain ⟨i, -, hi⟩ := hp.inf_le'.1 hinf
  obtain ⟨ho, hc, hd, hz⟩ := hfam i
  have hX' : MvPolynomial.X a₁ ∉ coneIdeal em (B i) (θ i) := fun h => hX (hi h)
  have hn : (B i).Nonempty := by
    by_contra hne
    apply hX'
    rw [mem_coneIdeal]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  obtain ⟨a₀, a, h₀, hind⟩ := exists_ratios em hem (θ i) ho hd (fun z hz' => (hz z hz').2) a₁ hX'
  refine ⟨_, a₀, a, coneIdeal_isPrime em (θ i) ho hc hn hd, fun F hF => ?_, hi, h₀, hind⟩
  rw [mem_coneIdeal]
  intro z hz' c _
  obtain ⟨t, ht, hθ⟩ := (hz z hz').1
  have hcomp := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [eval₂_smul_of_isHomogeneous em _ c (MvPolynomial.homogeneousComponent_isHomogeneous e F),
    (hmem _).1 (hcomp e) t _ ht hθ, mul_zero]

end GlobalTheory.ThetaPrime
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

theorem _root_.GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  first | exact @GlobalTheory.KS.tMap_of_isConst | exact GlobalTheory.KS.tMap_of_isConst | (intros; apply GlobalTheory.KS.tMap_of_isConst <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_flat_projective_through_points_goodFibres : ∀ (R σ Hh : Type) [CommRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), Ideal (MvPolynomial σ K) → Prop), (∀ (K : Type) [Field K] (x : R →+* K) I, G K x I → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p h i))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : _), RingHom.ker x = q ∧ G K x I} → ∃ (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d p) Z.hom M th ∧ IsProjOver Z.hom ∧ Flat Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), G K x I → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  first | exact @GlobalTheory.ZM.FlatFamily.exists_flat_projRep_vanIdeal | exact GlobalTheory.ZM.FlatFamily.exists_flat_projRep_vanIdeal | (intros; apply GlobalTheory.ZM.FlatFamily.exists_flat_projRep_vanIdeal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_ksMatrix_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  first | exact @GlobalTheory.KSField.exists_ksMatrix | exact GlobalTheory.KSField.exists_ksMatrix | (intros; apply GlobalTheory.KSField.exists_ksMatrix <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.polarisedIso_commutes_fieldAutomorphism_of_torsion : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  first | exact @GlobalTheory.SerreTwist.whisker_comp_eq | exact GlobalTheory.SerreTwist.whisker_comp_eq | (intros; apply GlobalTheory.SerreTwist.whisker_comp_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.siegel_principal_object_descends_large_subfield : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.SiegDesc.siegPre_descends | exact GlobalTheory.SiegDesc.siegPre_descends | (intros; apply GlobalTheory.SiegDesc.siegPre_descends <;> assumption)
end
