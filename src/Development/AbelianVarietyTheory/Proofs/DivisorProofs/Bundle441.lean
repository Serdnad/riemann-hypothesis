module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle391
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle390
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThickStalkEq

theorem isLocalHom_mk {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (Ideal.Quotient.mk I) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨v, hv⟩ := ha
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)
  have h1 : Ideal.Quotient.mk I (a * b - 1) = 0 := by
    rw [map_sub, map_mul, hb, ← hv]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have hm : a * b - 1 ∈ maximalIdeal A := le_maximalIdeal hI h1
  have ha' : a * b ∈ maximalIdeal A := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 hna)
  have h2 : (1 : A) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ ha' hm
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem pow_succ_ne_top (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    maximalIdeal A ^ (e + 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e))

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    Nontrivial (A ⧸ maximalIdeal A ^ (e + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top A e)

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (e + 1)) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) :=
  isLocalHom_mk _ (pow_succ_ne_top A e)

theorem eq_of_forall_pow {X : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (u u' : Spec A ⟶ X)
    (h : ∀ e : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u') :
    u = u' := by
  obtain ⟨⟨y, ψ, hψ⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u
  obtain ⟨⟨y', ψ', hψ'⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u'
  have key : ∀ e : ℕ, ∃ h₁ : y = y',
      ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) =
        (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫
          ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) := by
    intro e
    have he := h e
    simp only [SpecToEquivOfLocalRing_symm_apply, ← Spec.map_comp_assoc] at he
    have l1 : IsLocalHom (ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have l2 : IsLocalHom (ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have hinj := (SpecToEquivOfLocalRing X (.of (A ⧸ maximalIdeal A ^ (e + 1)))).symm.injective
      (a₁ := ⟨y, ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l1⟩)
      (a₂ := ⟨y', ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l2⟩)
      (by simpa only [SpecToEquivOfLocalRing_symm_apply] using he)
    obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
    exact ⟨h₁, h₂⟩
  obtain ⟨rfl, -⟩ := key 0
  have hψψ : ψ = ψ' := by
    ext f
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
      Ideal.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ e =>
      obtain ⟨_, h₂⟩ := key e
      simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp] at h₂
      have := congrArg (fun g => g.hom f) h₂
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact Ideal.Quotient.eq.mp this
  subst hψψ
  rfl

end GlobalTheory.ThickStalkEq

namespace GlobalTheory.ThickStalkEq

theorem fromSpecStalk_comp_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G),
    (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b =
      (Over.pullback (thick R (maximalIdeal R) e)).map b') →
    ∀ x : G.left, G.hom x = closedPoint R →
      G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  intro R _ _ _ G hG b b' hb x hx
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let A := G.left.presheaf.stalk x
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (G.left.fromSpecStalk x ≫ G.hom)
  have hφ : Spec.map φ = G.left.fromSpecStalk x ≫ G.hom := Spec.map_preimage _
  have h1 : (Spec.map φ) (closedPoint A) = closedPoint R := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg G.hom Scheme.fromSpecStalk_closedPoint).trans hx)
  have hloc : ∀ r ∈ maximalIdeal R, φ.hom r ∈ maximalIdeal A := by
    intro r hr
    have hc : PrimeSpectrum.comap φ.hom (closedPoint A) = closedPoint R := h1
    have : r ∈ (PrimeSpectrum.comap φ.hom (closedPoint A)).asIdeal := by rw [hc]; exact hr
    exact this
  refine eq_of_forall_pow A _ _ (fun e => ?_)
  have hle : maximalIdeal R ^ (e + 1) ≤ (maximalIdeal A ^ (e + 1)).comap φ.hom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hloc) _
  let χ : R ⧸ maximalIdeal R ^ (e + 1) →+* A ⧸ maximalIdeal A ^ (e + 1) :=
    Ideal.quotientMap _ φ.hom hle
  have hw : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫
      G.left.fromSpecStalk x) ≫ G.hom = Spec.map (CommRingCat.ofHom χ) ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, thick, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have := congrArg (fun g => pullback.lift _ _ hw ≫ g.left ≫ pullback.fst _ _) (hb e)
  simp only [Over.pullback_map_left] at this
  simpa only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] using this

end GlobalTheory.ThickStalkEq
end

section

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open IsDiscreteValuationRing in
theorem mul_dvd_pow_of_quadratic_bound_dvr {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Type} [AddCommGroup X] (h h' : X →+ X) (C : ℕ)
    (hq : ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y) {N : ℕ} (hN : C + 1 ≤ N) (k : X → V) (hk0 : ∀ y, k y ≠ 0)
    (h1 : ∀ y, k (-y) = k y) (h2 : k 0 = 1)
    (h3 : ∀ x y z, k (x + y + z) * k x * k y * k z = k (x + y) * k (x + z) * k (y + z))
    (h4 : ∀ y z, ∃ u : V, IsUnit u ∧
      k (h y + z) * k y * k (h' z) = u * (k (y + h' z) * k (h y) * k z)) (y : X) :
    k y * k (h y) ∣ k y ^ N := by
  have hn : ∀ z, ∃ n : ℕ, addVal V (k z) = n := fun z =>
    (ENat.ne_top_iff_exists.1 (mt addVal_eq_top_iff.1 (hk0 z))).imp fun _ e => e.symm
  choose n hn using hn
  have key := hq (fun z => (n z : ℤ)) (fun _ => Int.natCast_nonneg _)
    (by
      have := hn 0
      rw [h2, addVal_one] at this
      exact_mod_cast this.symm)
    (fun z => by
      have := hn (-z)
      rw [h1, hn] at this
      exact_mod_cast this.symm)
    (fun a b c => by
      have := congrArg (addVal V) (h3 a b c)
      simp only [addVal_mul, hn] at this
      exact_mod_cast this)
    (fun a b => by
      obtain ⟨u, hu, e⟩ := h4 a b
      have := congrArg (addVal V) e
      simp only [addVal_mul, hn, addVal_eq_zero_iff.2 hu, zero_add] at this
      exact_mod_cast this) y
  have key' : n (h y) ≤ C * n y := by exact_mod_cast key
  rw [← addVal_le_iff_dvd, addVal_mul, addVal_pow, hn, hn, nsmul_eq_mul]
  have : n y + n (h y) ≤ N * n y := by nlinarith [Nat.mul_le_mul_right (n y) hN]
  exact_mod_cast this

theorem exists_pow_eq_mul_of_quadratic_bound :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR X _ h h' C hq N hN κ h1 h2 h3 hκ h4 y
  obtain ⟨hno, -, hic, -⟩ := hR
  have hx : ∃ r : R, algebraMap R (FractionRing R) r =
      ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) := by
    refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hRV _ => ?_
    have hm : ∀ z, (κ z : FractionRing R) ∈ V := fun z => by
      obtain ⟨r, e⟩ := hκ z
      exact e ▸ hRV r
    obtain ⟨c, hc⟩ := mul_dvd_pow_of_quadratic_bound_dvr (V := V) h h' C hq hN
      (fun z => ⟨κ z, hm z⟩) (fun z e => (κ z).ne_zero (congrArg Subtype.val e))
      (fun z => Subtype.ext (congrArg Units.val (h1 z)))
      (Subtype.ext (congrArg Units.val h2))
      (fun a b c => Subtype.ext (congrArg Units.val (h3 a b c)))
      (fun a b => by
        obtain ⟨u, e⟩ := h4 a b
        exact ⟨(algebraMap R (FractionRing R)).codRestrict V hRV u, u.isUnit.map _,
          Subtype.ext e⟩) y
    have hc' : (κ y : FractionRing R) ^ N = κ y * κ (h y) * (c : FractionRing R) := by
      simpa using congrArg Subtype.val hc
    have : ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = c := by
      rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_pow_eq_pow_val, hc', Units.val_mul, mul_comm]
    exact this ▸ c.2
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [hr, mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  first | exact @GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | exact GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | (intros; apply GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ Y : Matrix (Fin r) (Fin r) E, Y.trace = 0 → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace = 0) → X = 0 := by
  first | exact @GlobalTheory.TraceSkew.traceForm_nondegenerate | exact GlobalTheory.TraceSkew.traceForm_nondegenerate | (intros; apply GlobalTheory.TraceSkew.traceForm_nondegenerate <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.exists_reps_mod_lattice_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E), T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  first | exact @GlobalTheory.lattice_mod_reps_card_le | exact GlobalTheory.lattice_mod_reps_card_le | (intros; apply GlobalTheory.lattice_mod_reps_card_le <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem E₄_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₄ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 4 = 12 * (Λ.g₂ / Ω ^ 4) := by
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 4 = 16 * (Real.pi : ℂ) ^ 4 := by
    rw [mul_pow, Complex.I_pow_four]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₂_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem E₆_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₆ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 6 = -(216 * (Λ.g₃ / Ω ^ 6)) := by
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 6 = -(64 * (Real.pi : ℂ) ^ 6) := by
    rw [mul_pow, h6]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₃_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem map_E₄_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4) :
    g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4)
      = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 := by
  rw [E₄_div_period_eq h₀, E₄_div_period_eq h₁, map_mul, h, map_ofNat]

theorem map_E₆_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) :
    g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6)
      = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 := by
  rw [E₆_div_period_eq h₀, E₆_div_period_eq h₁, map_neg, map_mul, h, map_ofNat]

theorem map_eisenstein_div_period :
    ∀ (g : ℂ ≃+* ℂ) (Λ₀ Λ₁ : PeriodPair) (c₀ c₁ Ω₀ Ω₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 → g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 → g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4) = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 ∧ g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6) = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 :=
  fun g _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃ =>
    ⟨map_E₄_div_period g h₀ h₁ h₂, map_E₆_div_period g h₀ h₁ h₃⟩

end GlobalTheory.QFam
end
