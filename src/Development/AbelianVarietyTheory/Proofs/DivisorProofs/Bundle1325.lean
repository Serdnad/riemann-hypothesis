module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_uniformiser_cons : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (E : Place c) (t : E.ring)
  (w : Fin n → E.ring), Irreducible t →
  (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ E.const w P)) →
  (∃ x : Fin (n + 1) → K, TrBasis c x) →
  (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K)) = 0 := by
  intro k K _ _ _ c n E t w ht hw hx
  obtain ⟨x, hx⟩ := hx
  have e : dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K) =
      E.toRat (n + 1) (dForm E.const (Fin.cons t w : Fin (n + 1) → E.ring)) := by
    have h := TopForm.formMap_dForm (D := n + 1) (α := E.const) (β := c) E.ring.subtype rfl
      (Fin.cons t w : Fin (n + 1) → E.ring)
    refine Eq.trans ?_ h.symm
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t', ht'⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht'
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m := by
    have : n + 1 = m + 1 := by exact_mod_cast h2
    omega
  have hG := isFreeGen_dForm_uniformiser_cons k E.ring E.const n t w E.essFiniteType ht ⟨b⟩ hw
  rw [e]
  exact E.formOrd_toRat hG

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_place_isPrimeOf_of_height_eq_one {K : Type} [Field K] (cK : ℂ →+* K)
    (R : Subring K) (hR : IsLocModel cK R) (hic : IsIntegrallyClosed R) (p : Ideal R)
    (hpp : p.IsPrime) (hp : p.height = 1) :
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  classical
  letI : Algebra ℂ R := (cK.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  set S := primeLocalSubalgebra K p with hS
  have hmem : ∀ x : K, x ∈ S ↔ ∃ s : R, s ∉ p ∧ ∃ a : R, (a : K) = s * x := by
    intro x
    rw [hS, mem_primeLocalSubalgebra_iff]
    rfl
  have hne : ∀ s : R, s ∉ p → (s : K) ≠ 0 := fun s hs h =>
    hs ((Subtype.ext h : s = 0) ▸ p.zero_mem)
  have h1p : (1 : R) ∉ p := (Ideal.ne_top_iff_one p).mp hpp.ne_top
  have hRS : ∀ r : R, (r : K) ∈ S := fun r =>
    (hmem _).2 ⟨1, h1p, r, by simp⟩
  have hinv : ∀ s : R, s ∉ p → (s : K)⁻¹ ∈ S := fun s hs =>
    (hmem _).2 ⟨s, hs, 1, by simp [mul_inv_cancel₀ (hne s hs)]⟩
  have hor : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ S.zero_mem)
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx,
      mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero hx),
      heightOneOrd_vw_inv]
    omega
  let V : ValuationSubring K := { S.toSubring with mem_or_inv_mem' := hor }
  have hV : ∀ x : K, x ∈ V ↔ x ∈ S := fun _ => Iff.rfl
  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRS r⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra R V := ι.toAlgebra
  have hunit : ∀ s : R, s ∉ p → IsUnit (algebraMap R V s) := fun s hs =>
    isUnit_iff_exists_inv.mpr ⟨⟨(s : K)⁻¹, hinv s hs⟩, Subtype.ext (mul_inv_cancel₀ (hne s hs))⟩
  haveI hloc : IsLocalization.AtPrime V p := by
    refine ⟨fun y => hunit y y.2, fun z => ?_, fun {x y} h => ?_⟩
    · obtain ⟨s, hs, a, e⟩ := (hmem z).1 z.2
      refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
      show (z : K) * s = a
      rw [e, mul_comm]
    · refine ⟨1, ?_⟩
      have hxy : (x : K) = y := congrArg (fun z : V => (z : K)) h
      have : x = y := Subtype.ext hxy
      rw [this]
  haveI : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  have hc : ∀ a, cK a ∈ V := fun a => hRS ⟨cK a, hR.const_mem a⟩
  have hess : (cK.codRestrict V hc).EssFiniteType := by
    have h0 : (cK.codRestrict R hR.const_mem).EssFiniteType := hR.essFiniteType
    have h1 : (algebraMap R V).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization V p.primeCompl)
    convert h0.comp h1 using 1
    exact RingHom.ext fun _ => rfl
  let P0 : Place cK := ⟨V, hc, inferInstance, hess⟩
  refine ⟨P0, ⟨fun f hf => hRS ⟨f, hf⟩, fun f hf => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨s, hs, a, e⟩ := (hmem f).1 hf
    refine ⟨a, a.2, s, s.2, hne s hs, P0.ord_eq_zero (u := algebraMap R V s) (hunit s hs), ?_⟩
    rw [e, mul_comm]
  · have hg0 : (g : K) ≠ 0 := fun h => hg (Subtype.ext h)
    constructor
    · intro h hgp
      have h' : 0 ≤ P0.ord (g : K)⁻¹ := by rw [P0.ord_inv, h]; rfl
      obtain ⟨s, hs, a, e⟩ := (hmem _).1 ((P0.ord_nonneg_iff (inv_ne_zero hg0)).1 h')
      have : s = a * g := Subtype.ext (by
        show (s : K) = a * g
        rw [e, mul_assoc, inv_mul_cancel₀ hg0, mul_one])
      exact hs (this ▸ p.mul_mem_left a hgp)
    · intro hgp
      exact P0.ord_eq_zero (u := algebraMap R V g) (hunit g hgp)

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem preimage_fromSpecStalk_eq_constFn {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom = Cartier.constFn p := by
  ext a
  have n := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv a))
    (Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)))
  simp only [Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at n
  rw [← n]
  have hid : (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤))
      = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [hid, CommRingCat.id_apply, Iso.inv_hom_id_apply]
  have e2 : Scheme.Hom.appLE p ⊤ ⊤ (by simp) = Scheme.Hom.appTop p := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  simp only [Cartier.constFn, Cartier.fnOf, algX, e2, RingHom.comp_apply]

theorem isLocModel_locRing_and_exists_trBasis {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ) (x : X) (hn : topologicalKrullDim X = n) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ z : Fin n → X.functionField, TrBasis (Cartier.constFn p) z := by
  refine ⟨isLocModel_locRing x, ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : (U : Set X).Nonempty := ⟨x, hxU⟩
  obtain ⟨d, h₁, h₂⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen k p hU hne
  have e₁ := GlobalTheory.OpenDim.topologicalKrullDim_open k p U hne
  have e₂ : topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have hdn : d = n := by
    have : ((d : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by rw [← h₁, ← e₂, e₁, hn]
    exact_mod_cast this
  subst hdn
  rw [preimage_fromSpecStalk_eq_constFn] at h₂
  letI := (Cartier.constFn p).toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k X.functionField
  have hc : Cardinal.mk s = (d : Cardinal) := hs.cardinalMk_eq_trdeg.trans h₂
  have hfin : Fintype s := (Cardinal.lt_aleph0_iff_fintype.mp (hc ▸ Cardinal.natCast_lt_aleph0 (n := d))).some
  have hcard : Fintype.card s = d := by
    have := hc; rw [Cardinal.mk_fintype] at this; exact_mod_cast this
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : X.functionField), ?_⟩
  unfold TrBasis
  exact hs.comp_equiv e

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem Place.exists_smooth_subalgebra : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  intro κ' _ _ F S hS
  classical
  let R := F.ring
  letI : Algebra ℂ R := F.const.toAlgebra
  haveI : IsScalarTower ℂ R κ' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := F.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  let R' : Subalgebra ℂ κ' :=
    { F.ring.toSubring with algebraMap_mem' := F.const_mem }
  let T : Set κ' := ((σ.image (fun x : R => (x : κ')) ∪ S : Finset κ') : Set κ')
  let A₀ : Subalgebra ℂ κ' := Algebra.adjoin ℂ T
  have hT : T ⊆ R' := by
    intro x hx
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with ⟨y, -, rfl⟩ | hx
    · exact y.2
    · exact hS x hx
  have hA₀R : A₀ ≤ R' := Algebra.adjoin_le hT

  have memA₀ : ∀ x : R, x ∈ Algebra.adjoin ℂ (σ : Set R) → (x : κ') ∈ A₀ := by
    intro x hx
    have h1 : (IsScalarTower.toAlgHom ℂ R κ') x ∈
        (Algebra.adjoin ℂ (σ : Set R)).map (IsScalarTower.toAlgHom ℂ R κ') := ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe]
    exact Or.inl ⟨y, hy, rfl⟩
  have hfg : Algebra.FiniteType ℂ A₀ :=
    (Subalgebra.fg_iff_finiteType A₀).mp (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FinitePresentation ℂ A₀ := Algebra.FinitePresentation.of_finiteType.mp hfg
  let ι : A₀ →+* R := (A₀.val.toRingHom).codRestrict R (fun x => hA₀R x.2)
  letI : Algebra A₀ R := ι.toAlgebra
  haveI : IsScalarTower ℂ A₀ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let q : Ideal A₀ := (IsLocalRing.maximalIdeal R).comap ι
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization q.primeCompl R := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      by_contra h; exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
    · intro r
      obtain ⟨t, htA, ht, h⟩ := hσ r
      refine ⟨⟨⟨_, memA₀ _ h⟩, ⟨⟨_, memA₀ _ htA⟩, fun hq => ?_⟩⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · intro x y e
      refine ⟨1, ?_⟩
      have : (x : κ') = y := congrArg (fun z : R => (z : κ')) e
      simp [Subtype.ext this]
  haveI : Algebra.FormallySmooth ℂ R := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ R
  haveI : Algebra.IsSmoothAt ℂ q := by
    have e := (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars ℂ
    exact Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨g, hgq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℂ q
  have hgu : IsUnit (ι g) := by
    by_contra h; exact hgq ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hg0 : (g : κ') ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have := congrArg (fun x : R => (x : κ')) hu
    simp [ι, h0] at this
  have hgu' : IsUnit (A₀.val g) := (isUnit_iff_ne_zero).2 hg0
  let φ : Localization.Away g →ₐ[ℂ] κ' := IsLocalization.Away.liftAlgHom g hgu'

  have hφ : ∀ a : A₀, φ (algebraMap A₀ (Localization.Away g) a) = a := by
    intro a; simp [φ]
  have hginv : (g : κ')⁻¹ ∈ F.ring := by
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have h1 : (g : κ') * (u : κ') = 1 := by
      have := congrArg (fun x : R => (x : κ')) hu; simpa [ι] using this
    rw [inv_eq_of_mul_eq_one_right h1]; exact u.2
  have hpow : ∀ s ∈ Submonoid.powers g, (s : κ') ≠ 0 ∧ (s : κ')⁻¹ ∈ F.ring := by
    rintro s ⟨n, rfl⟩
    refine ⟨by simpa using pow_ne_zero n hg0, ?_⟩
    simpa [inv_pow] using pow_mem hginv n
  have hrep : ∀ x : Localization.Away g, ∃ a : A₀, ∃ s ∈ Submonoid.powers g,
      φ x * (s : κ') = a := by
    intro x
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨a, s, hs, ?_⟩
    have := congrArg φ e
    rw [map_mul, hφ, hφ] at this
    exact this
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    have h1 := congrArg φ e
    rw [map_mul, hφ, hφ, hx, zero_mul] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units (Localization.Away g) (⟨s, hs⟩ : Submonoid.powers g)).mul_left_eq_zero.1 e
  let A : Subalgebra ℂ κ' := φ.range
  haveI : Algebra.Smooth ℂ A := Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)
  have hA₀A : ∀ a ∈ A₀, a ∈ A := fun a ha => ⟨algebraMap A₀ _ ⟨a, ha⟩, hφ ⟨a, ha⟩⟩
  refine ⟨A, inferInstance, ?_, fun x hx => hA₀A x (Algebra.subset_adjoin ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, s, hs, e⟩ := hrep x
    obtain ⟨hs0, hsi⟩ := hpow s hs
    have : φ x = a * (s : κ')⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    show φ x ∈ F.ring
    rw [this]; exact F.ring.mul_mem _ _ (hA₀R a.2) hsi
  · simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inr hx
  · intro f
    have hfrac : ∃ a ∈ F.ring, ∃ b ∈ F.ring, b ≠ 0 ∧ f * b = a := by
      obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := F.ring) f
      have hb0 : (b : κ') ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
      refine ⟨a, a.2, b, b.2, hb0, ?_⟩
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hfrac
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    have unit_ne : ∀ t : R, IsUnit t → (t : κ') ≠ 0 := by
      intro t ht h0
      obtain ⟨u, hu⟩ := ht.exists_right_inv
      have := congrArg (fun x : R => (x : κ')) hu
      simp [h0] at this
    refine ⟨r1 * t1 * t2, hA₀A _ ?_, r2 * t2 * t1, hA₀A _ ?_, ?_, ?_⟩
    · simpa using A₀.mul_mem (memA₀ _ h1) (memA₀ _ ht2A)
    · simpa using A₀.mul_mem (memA₀ _ h2) (memA₀ _ ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PrimeElementPlace

theorem main : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  intro L K _ _ cL cK n T hT ψ f _ hc hker hf hR
  classical
  haveI hfr : IsFractionRing T L := IsFractionRing.of_field T L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hT.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let A : Subalgebra T L :=
    Localization.subalgebra.ofField L (RingHom.ker ψ).primeCompl (RingHom.ker ψ).primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime A (RingHom.ker ψ) := (inferInstance : IsLocalization (RingHom.ker ψ).primeCompl A)
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (RingHom.ker ψ)
  letI : Algebra ℂ T := (cL.codRestrict T hT.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T := hT.essFiniteType
  haveI : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing ℂ T
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ψ).primeCompl A inferInstance
  have hinjA : Function.Injective (algebraMap T A) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A => (z : L)) h)
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap T A f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ψ) A, hker, Ideal.map_span,
      Set.image_singleton]
  have hf' : algebraMap T A f ≠ 0 := fun h => hf (hinjA (h.trans (map_zero _).symm))
  have hprinc : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsPrincipalIdealRing A :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := A)).out 1 5).2 hprinc
  haveI hdvrA : IsDiscreteValuationRing A := by
    refine ⟨?_⟩
    rw [hmax]
    intro h
    exact hf' ((Ideal.span_singleton_eq_bot).1 h)
  have hval : ∀ x : L, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring := fun x => by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left; rw [← hy]; exact y.2
    · right; rw [← hy]; exact y.2
  let V : ValuationSubring L := ValuationSubring.ofSubring A.toSubring hval
  let e : A ≃+* V :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  have hTA : ∀ t : L, t ∈ T → t ∈ V := fun t ht => A.algebraMap_mem (⟨t, ht⟩ : T)
  have hcV : ∀ a, cL a ∈ V := fun a => hTA _ (hT.const_mem a)
  have heft : (cL.codRestrict V hcV).EssFiniteType := by
    have h2 : (algebraMap T A).EssFiniteType := RingHom.essFiniteType_algebraMap.2
      (Algebra.EssFiniteType.of_isLocalization A (RingHom.ker ψ).primeCompl)
    have h3 := (hT.essFiniteType.comp h2).comp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    have e' : e.toRingHom.comp ((algebraMap T A).comp (cL.codRestrict T hT.const_mem)) =
        cL.codRestrict V hcV := RingHom.ext fun a => Subtype.ext rfl
    exact e' ▸ h3
  let S : Place cL := ⟨V, hcV, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, heft⟩
  have hS : S.IsPrimeOf T := by
    refine ⟨fun t ht => hTA t ht, fun x hx => ?_⟩
    obtain ⟨a, s, hs, rfl⟩ := hx
    have hs0 : (s : L) ≠ 0 := fun h => hs (by
      rw [show s = 0 from Subtype.ext h]; exact (RingHom.ker ψ).zero_mem)
    have hinv : (s : L)⁻¹ ∈ V := ⟨1, s, hs, by rw [map_one, one_mul]; rfl⟩
    have hsV : (s : L) ∈ V := hTA _ s.2
    have hu : IsUnit (⟨(s : L), hsV⟩ : S.ring) :=
      isUnit_iff_exists_inv.2 ⟨⟨(s : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
    have hord : S.ord (s : L) = 0 := S.ord_eq_zero (u := ⟨(s : L), hsV⟩) hu
    refine ⟨a, a.2, s, s.2, hs0, hord, ?_⟩
    change (a : L) * (s : L)⁻¹ * s = a
    rw [inv_mul_cancel_right₀ hs0]
  have hunit : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ψS : S.ring →+* K :=
    (IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (S := A) hunit).comp e.symm.toRingHom
  have hgen : ∀ (t : T) (h : (t : L) ∈ S.ring), ψS ⟨t, h⟩ = ψ t := by
    intro t h
    have h1 : e.symm ⟨t, h⟩ = algebraMap T A t := Subtype.ext rfl
    show IsLocalization.lift _ (e.symm ⟨t, h⟩) = ψ t
    rw [h1, IsLocalization.lift_eq]
  refine ⟨S, hS, ψS, fun z => ?_, fun a => ?_, fun t => hgen t _, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb0, e1⟩ := hR.frac z
    have hb : b ∈ (RingHom.ker ψ).primeCompl := fun h => hb0 (RingHom.mem_ker.1 h)
    refine ⟨e (IsLocalization.mk' A a ⟨b, hb⟩), ?_⟩
    show IsLocalization.lift _ (e.symm (e _)) = z
    rw [RingEquiv.symm_apply_apply, IsLocalization.lift_mk'_spec]
    exact e1.symm.trans (mul_comm _ _)
  · exact (hgen ⟨cL a, hT.const_mem a⟩ _).trans (hc a)
  · have h1 : (⟨f, hS.1 f f.2⟩ : S.ring) = e (algebraMap T A f) := Subtype.ext rfl
    rw [h1, MulEquiv.irreducible_iff]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax

end GlobalTheory.FieldPair.PrimeElementPlace

end
end
