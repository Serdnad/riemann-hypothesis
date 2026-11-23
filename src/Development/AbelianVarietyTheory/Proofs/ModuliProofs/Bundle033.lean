module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PrimUnif

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ)
    (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  have hz : u.ex 0 = 1 := by
    have h := u.ex_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem unitOn_inj' {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro a b h
  ext
  have h' := congrArg (fun x : Γ(Sp K, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h'

theorem unitS_spMap {o K : Type} [CommRing o] [CommRing K] (em : o →+* K) (c : oˣ) :
    unitS (spMap em) c = unitOn (Units.map em.toMonoidHom c) := by
  ext
  simp only [unitS, unitOn, spMap, Units.coe_map]
  have h := congrArg (fun φ => φ.hom (c : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em))
  exact h.symm

theorem exists_unif_of_prim :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)), t.Prim w w' → ∃ (La : Type) (_ : AddCommGroup La) (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro hL _ _ hU o _ g k J b em w w' t hP
  have hk : ((k : ℕ) : ℂ) ≠ 0 := by
    have h := b.unit.map em
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨rig, hrig⟩ := t.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hEnd, -, hEf, hEfb, hWeil⟩ := hU t.pol rig hrig
  choose F hF using fun j => hEnd (t.act j) (t.hom j)
  have hone : ∀ j, (1 : 𝟙_ (Over (Sp ℂ)) ⟶ t.A) ≫ t.act j = 1 := fun j => by
    have := t.hom j
    simp [Hom.one_def]
  have hFm : ∀ j (l : u.Λ), F j l ∈ u.Λ := fun j l => by
    rw [← u.ker, hF, (u.ker _).2 l.2]
    exact hone j
  choose z hz using fun i => u.ex_onto (t.pt i)
  have hlam : ∀ i, ((k : ℕ) : ℂ) • z i ∈ u.Λ := fun i => by
    rw [← u.ker, ex_nsmul, hz]
    exact t.torsion i
  have hlev : ∀ i, u.ex (((k : ℕ) : ℂ)⁻¹ • (((k : ℕ) : ℂ) • z i)) = t.pt i := fun i => by
    rw [inv_smul_smul₀ hk, hz]
  refine ⟨u.Λ, inferInstance, Ef, fun i => ⟨_, hlam i⟩, fun j x => ⟨F j x, hFm j x⟩,
    u.Λ.subtype.toAddMonoidHom, Hm, hEfb, ⟨Subtype.val_injective, ?_, ?_, hAH.1, hAH.2.1,
      fun x y => (hEf x y).symm⟩, ?_, u, χ, hAH, ?_, ?_, ?_, ?_⟩
  · have key : ∀ S : AddSubgroup (Fin g → ℂ), (∀ x, x ∈ S ↔ x ∈ u.Λ) → DiscreteTopology S := by
      intro S hS
      obtain rfl : S = u.Λ.toAddSubgroup := AddSubgroup.ext hS
      exact u.discrete
    refine key _ (fun x => ⟨fun h => ?_, fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩⟩)
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · have hs : Set.range (fun x : u.Λ => (x : Fin t.pol.g → ℂ)) = (u.Λ : Set (Fin t.pol.g → ℂ)) :=
      Subtype.range_coe
    have hfull := u.full
    rw [← hs] at hfull
    exact hfull
  · intro i₁ i₂
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h => hk (by simp [h]))
    have hW := hWeil k ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩
      (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (Ef ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩ : ℂ) / ((k : ℕ) : ℂ))))
      hkpos rfl
    simp only [hlev] at hW
    have hP2 := t.pairing i₁ i₂
    rw [unitS_spMap] at hP2
    have hu := ((hL.weil (Sp ℂ) t.pol k (𝟙_ _)).1 (t.pt i₁) (t.pt i₂) (t.torsion i₁) (t.torsion i₂)).unique hW hP2
    have hpow : ∀ (x : ℂˣ) (n : ℤ), unitOn x ^ n = unitOn (x ^ n) := by
      intro x n
      unfold unitOn
      rw [map_zpow]
    rw [hpow] at hu
    have hc := congrArg Units.val (unitOn_inj' hu)
    simpa [Units.val_zpow_eq_zpow_val] using hc
  · intro x
    refine ⟨fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩, fun h => ?_⟩
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · intro x l hl
    have hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) := fun X x => valAt'_rules X x
    have : IsCommMonObj t.pol.A := t.ab.comm
    have hAHd := GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube hv (GlobalTheory.holFamily_lift hv) t.pol u Hm χ Ef
      ⟨hAH.1, hAH.2.2.1, fun a c => hEf a c, hAH.2.2.2⟩ (t.act w) (F w) (fun m hm => hFm w ⟨m, hm⟩) (hF w) hP.2.2
    obtain rfl : l = x := Subtype.ext hl
    exact hAHd.2 l
  · intro i
    exact congrArg (fun p => p.left) (hlev i).symm
  · intro j
    exact ⟨F j, fun x => rfl, hF j⟩

end GlobalTheory.PrimUnif

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IntegersAway

theorem isPrimitiveRoot_map_of_natCast_ne_zero {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by
  have : NeZero (k : K) := ⟨hβ⟩
  have h : (Polynomial.cyclotomic k R).IsRoot z := hz.isRoot_cyclotomic hk
  apply (Polynomial.isRoot_cyclotomic_iff (n := k) (R := K)).mp
  rw [← Polynomial.map_cyclotomic k β]
  exact h.map β

theorem exists_tBase_of_numberField {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {k : ℕ} (hk : 0 < k)
    {z r : F} (hz : IsPrimitiveRoot z k) (hr : IsIntegral ℤ r) :
    ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (ρ : o) (_ : Algebra o F), ArBase em ∧
      IsFractionRing o F ∧ (∀ x, φ (algebraMap o F x) = em x) ∧ algebraMap o F ρ = r ∧
      algebraMap o F (b.ζ : o) = z := by
  obtain ⟨em, hem, hcomp⟩ := exists_arBase_away φ hk.ne'
  have hn' : (k : 𝓞 F) ≠ 0 := by exact_mod_cast hk.ne'
  have hM : Submonoid.powers (k : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  let o := Localization.Away (k : 𝓞 F)
  have hu : IsUnit (algebraMap (𝓞 F) F (k : 𝓞 F)) := by simpa using hk.ne'
  let j : o →+* F := IsLocalization.Away.lift (k : 𝓞 F) hu
  have hj : ∀ x, j (algebraMap (𝓞 F) o x) = algebraMap (𝓞 F) F x := IsLocalization.Away.lift_eq _ hu
  let alg : Algebra o F := j.toAlgebra
  have : IsScalarTower (𝓞 F) o F := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  let z₀ : 𝓞 F := ⟨z, hz.isIntegral hk⟩
  have hz₀ : IsPrimitiveRoot z₀ k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hz RingOfIntegers.coe_injective
  have hko : IsUnit (k : o) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := o) (k : 𝓞 F)
  have hzu : IsUnit (algebraMap (𝓞 F) o z₀) := (hz₀.isUnit hk.ne').map _
  refine ⟨o, inferInstance, ⟨hzu.unit, hko, fun K _ β => ?_⟩, em, algebraMap (𝓞 F) o ⟨r, hr⟩, alg, hem,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (k : 𝓞 F)) o F, ?_, hj _, hj _⟩
  · refine isPrimitiveRoot_map_of_natCast_ne_zero hk hz₀ (β.comp (algebraMap (𝓞 F) o)) ?_
    simpa using (hko.map β).ne_zero
  · have : φ.comp j = em := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (k : 𝓞 F)) ?_
      rw [hcomp]
      ext x
      simp [hj]
    exact fun x => DFunLike.congr_fun this x

theorem exists_tBase_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by
  intro E _ _ _ H l
  have : FiniteDimensional ℚ (KA l) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | rfl
    · refine IsIntegral.of_pow two_pos ?_
      rw [H.sqrt_neg_disc_sq]
      exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
    · refine IsIntegral.of_pow l.A_pos ?_
      rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
      exact isIntegral_one
  have : NumberField (KA l) := {}
  have hr : IsIntegral ℤ (baseKA l).ρ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [(baseKA l).ρ_sq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := KA l) (x := (H.d : ℤ))).neg
  exact exists_tBase_of_numberField (KA l).val.toRingHom l.A_pos (baseKA l).ζ_prim hr

end GlobalTheory.ZM.IntegersAway
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isDominant_pullback_fst_of_flat_of_injective {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (hβ : Function.Injective β) {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap β)) := by
  constructor
  intro x
  have hη : (spMap β) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O)
      (PrimeSpectrum.comap β (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : β a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := hβ (by rw [ha', map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

theorem isPrimitiveRoot_map_of_isUnit {O k : Type} [CommRing O] [IsDomain O] [Field k] (ψ : O →+* k)
    {z : O} {A : ℕ} (hA : 0 < A) (hz : IsPrimitiveRoot z A) (hu : IsUnit (A : O)) :
    IsPrimitiveRoot (ψ z) A := by
  have : NeZero (A : k) := ⟨by simpa using (hu.map ψ).ne_zero⟩
  rw [← (Polynomial.isRoot_cyclotomic_iff (R := k) (n := A)), ← Polynomial.map_cyclotomic A ψ]
  exact Polynomial.IsRoot.map ψ (hz.isRoot_cyclotomic hA)

theorem galoisPart_eq_refl_of_fixes_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ρ : C.X ≅ C.X) (σ : KA l ≃+* KA l), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → ∀ (k : Type) [Field k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → σ = RingEquiv.refl _ := by
  intro E _ _ _ H D l Xo S β C r ρ σ hinc hS ⟨e, he⟩ hj hρ hr k _ x hx
  have hA := l.A_pos
  have : NeZero l.A := ⟨hA.ne'⟩
  have hβ : Function.Injective β := fun a b h => Subtype.ext (by
    have h1 := hinc a
    rw [h, hinc b] at h1
    exact h1.symm)
  let z : RZ H S l.A := ⟨zeta l.A, Subring.subset_closure (by simp)⟩
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hβz : β z = (baseKA l).ζ := Subtype.ext (hinc z)
  have hζ : IsPrimitiveRoot (baseKA l).ζ l.A := (baseKA l).ζ_prim
  have hz : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (hβz ▸ hζ) hβ
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have := C.flat
  have hd₁ := isDominant_pullback_fst_of_flat_of_injective β hβ C.s
  have hd₂ : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have hd : IsDominant C.j := by unfold Cpt.j; infer_instance
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  let ev : RZ H S l.A → (Polynomial ℤ →+* RZ H S l.A) := fun y => (Polynomial.aeval y).toRingHom
  have hev : σ.toRingHom.comp (β.comp (ev z)) = β.comp (ev (z ^ a)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ev, hβz, ha]
  have key : ρ.hom ≫ C.s ≫ spMap (ev z) = C.s ≫ spMap (ev (z ^ a)) := by
    refine ext_of_isDominant C.j ?_
    rw [reassoc_of% hj, reassoc_of% hjs, reassoc_of% hjs, reassoc_of% hr]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← hev]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ C.s)
  have key₂ : CommRingCat.ofHom (ev z) ≫ ψ = CommRingCat.ofHom (ev (z ^ a)) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, Category.assoc, Category.assoc, ← key, reassoc_of% hx]
  have key₃ : ψ.hom z = ψ.hom z ^ a := by
    have := congrArg (fun f => f.hom Polynomial.X) key₂
    simpa [ev] using this
  have hp : IsPrimitiveRoot (ψ.hom z) l.A := isPrimitiveRoot_map_of_isUnit ψ.hom hA hz hAu
  have hmod : a ≡ 1 [MOD l.A] := by
    have hfin : IsOfFinOrder (ψ.hom z) := hp.isOfFinOrder hA.ne'
    rw [hp.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
    exact key₃.symm
  have hσζ : σ (baseKA l).ζ = (baseKA l).ζ := by
    rw [← ha]
    have hfin : IsOfFinOrder (baseKA l).ζ := hζ.isOfFinOrder hA.ne'
    rw [hζ.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one] at hmod
    exact hmod
  have hfinal : σ.toRingHom.toRatAlgHom = AlgHom.id ℚ (KA l) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl ?_
    rintro y (rfl | rfl)
    · exact hρ
    · exact hσζ
  ext1 y
  exact DFunLike.congr_fun hfinal y

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

def twistSnd {h : ℕ} (A : Matrix (Fin 8) (Fin 8) ℤ) :
    (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun y := fun u => Sum.elim (fun a => y u (.inl a)) (fun a => A.mulVec (fun w => y w (.inr a)) u)
  map_add' y y' := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem twistSnd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hAB : A * B = 1)
    (y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) : twistSnd A (twistSnd B y) = y := by
  funext u c
  rcases c with a | a
  · rfl
  · change A.mulVec (B.mulVec (fun w => y w (.inr a))) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

theorem sum_omegaStd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hA : A.transpose = A)
    (hAB : A * B = 1) (y y' : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, A u v * omegaStd (twistSnd B y u) (twistSnd B y' v) = ∑ u, omegaStd (y u) (y' u) := by
  have key : ∀ (z : Fin 8 → ℤ) (u : Fin 8), ∑ v, A u v * B.mulVec z v = z u := by
    intro z u
    change A.mulVec (B.mulVec z) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have hs : ∀ u v, A u v = A v u := fun u v => by
    conv_lhs => rw [← hA]
    rfl
  have h1 : ∑ u, ∑ v, A u v * ∑ a, y u (.inl a) * B.mulVec (fun w => y' w (.inr a)) v
      = ∑ u, ∑ a, y u (.inl a) * y' u (.inr a) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y' w (.inr a)) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ u, ∑ v, A u v * ∑ a, B.mulVec (fun w => y w (.inr a)) u * y' v (.inl a)
      = ∑ u, ∑ a, y u (.inr a) * y' u (.inl a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y w (.inr a)) v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hs u v]; ring
  simp only [omegaStd, Finset.sum_sub_distrib, mul_sub]
  rw [← h1, ← h2]
  rfl

def sharpIndex (h : ℕ) : Fin 8 × (Fin h ⊕ Fin h) ≃ Fin (2 * (8 * h)) :=
  (Equiv.prodSumDistrib _ _ _).trans <|
    (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans <|
      finSumFinEquiv.trans (finCongr (two_mul _).symm)

theorem sharpIndex_inl (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inl a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) := by
  simp [sharpIndex]

theorem sharpIndex_inr (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inr a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) + 8 * h := by
  simp [sharpIndex]

theorem sum_omegaStd_single (h : ℕ) (i j : Fin (2 * (8 * h))) :
    ∑ u, omegaStd (fun c => (Pi.single i 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c)))
      (fun c => (Pi.single j 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c))) = Out.stdSymp (8 * h) i j := by
  obtain ⟨⟨u, c⟩, rfl⟩ := (sharpIndex h).surjective i
  obtain ⟨⟨v, d⟩, rfl⟩ := (sharpIndex h).surjective j
  have hinj : ∀ (u v : Fin 8) (a b : Fin h),
      ((finProdFinEquiv (u, a) : ℕ) = (finProdFinEquiv (v, b) : ℕ)) ↔ (u = v ∧ a = b) := by
    intro u v a b
    rw [Fin.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rcases c with a | a <;> rcases d with b | b
  all_goals
    have h1 := (finProdFinEquiv (u, a)).isLt
    have h2 := (finProdFinEquiv (v, b)).isLt
    have h3 := hinj u v a b
    simp only [omegaStd, Out.stdSymp, Pi.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
      sharpIndex_inl, sharpIndex_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      if_false, mul_zero, zero_mul, sub_zero, zero_sub, Finset.sum_const_zero, sub_self]
    generalize (finProdFinEquiv (u, a) : ℕ) = m at *
    generalize (finProdFinEquiv (v, b) : ℕ) = n at *
  · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_neg (by omega), if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · rw [if_neg (by omega), if_neg (by omega)]

def sharpReindex (h : ℕ) : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x := fun u c => x (sharpIndex h (u, c))
  invFun y := fun i => y ((sharpIndex h).symm i).1 ((sharpIndex h).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext u c; simp

theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ, ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  refine ⟨GlobalTheory.W8, ?_, fun h => ?_⟩
  · unfold IsE8
    rw [GlobalTheory.w8_add_transpose_eq_e8]
    exact ⟨GlobalTheory.e8_posDef, GlobalTheory.e8_det_eq_one⟩
  · let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
      { twistSnd GlobalTheory.E8inv with
        invFun := twistSnd GlobalTheory.E8
        left_inv := twistSnd_twistSnd _ _ GlobalTheory.e8_mul_e8inv
        right_inv := twistSnd_twistSnd _ _ GlobalTheory.e8inv_mul_e8 }
    refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
    rw [GlobalTheory.w8_add_transpose_eq_e8, ← sum_omegaStd_single h i j]
    exact sum_omegaStd_twistSnd _ _ GlobalTheory.e8_transpose GlobalTheory.e8_mul_e8inv _ _

end GlobalTheory.ZM
end
end
