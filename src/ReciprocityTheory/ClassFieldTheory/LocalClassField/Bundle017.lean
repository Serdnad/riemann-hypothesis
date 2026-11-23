module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle003
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle013
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

theorem continuous_gal_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.2 fun s hs => ?_
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  let b := Module.finBasis k' E
  choose c hc using h
  have hopen : IsOpen (⋂ i, {σ : F ≃ₐ[k] F | σ (c (b i : F')) = c (b i : F')}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := k) (c (b i : F'))
  refine Filter.mem_of_superset (hopen.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun σ hσ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : F') := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)

    rw [map_sum] at this
    exact this.symm
  rw [hx']
  show φ σ _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact congrArg _ (hc _ σ (Set.mem_iInter.1 hσ i))

theorem exists_topAb_iso {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  apply GlobalTheory.HeckeGal.exists_topAbelianization_mulEquiv <;> assumption

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

theorem Model.E_symm_coe (x : m.K') :
    m.E.symm (x : PadicAlgCl p) = algebraMap K (AlgebraicClosure K) (m.e.symm x) := by
  rw [RingEquiv.symm_apply_eq, m.comm, RingEquiv.apply_symm_apply]

include m in
theorem Model.charZero : CharZero K :=
  charZero_of_injective_ringHom (f := (m.e.symm : m.K' →+* K)) m.e.symm.injective

noncomputable def Model.galIso : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K' where
  toFun σ :=
    { m.E.symm.trans (σ.toRingEquiv.trans m.E) with
      commutes' := fun x => by
        show m.E (σ (m.E.symm (x : PadicAlgCl p))) = (x : PadicAlgCl p)
        rw [m.E_symm_coe, AlgEquiv.commutes, m.comm, RingEquiv.apply_symm_apply] }
  invFun τ :=
    { m.E.trans (τ.toRingEquiv.trans m.E.symm) with
      commutes' := fun x => by
        show m.E.symm (τ (m.E (algebraMap K (AlgebraicClosure K) x))) = algebraMap K (AlgebraicClosure K) x
        rw [m.comm, show τ ((m.e x : m.K') : PadicAlgCl p) = _ from τ.commutes (m.e x)]
        show m.E.symm ((m.e x : m.K') : PadicAlgCl p) = _
        rw [m.E_symm_coe, RingEquiv.symm_apply_apply] }
  left_inv σ := by
    ext x
    show m.E.symm (m.E (σ (m.E.symm (m.E x)))) = σ x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  right_inv τ := by
    ext x
    show m.E (m.E.symm (τ (m.E (m.E.symm x)))) = τ x
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_mul' σ τ := by
    ext x
    show m.E (σ (τ (m.E.symm x))) = m.E (σ (m.E.symm (m.E (τ (m.E.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem Model.isGalIso_galIso : m.IsGalIso m.galIso := fun σ x => by
  show m.E (σ (m.E.symm (m.E x))) = m.E (σ x)
  rw [RingEquiv.symm_apply_apply]

variable {m}

theorem Model.IsGalIso.symm_apply {φ} (hφ : m.IsGalIso φ) (τ : GK p m.K') (x : AlgebraicClosure K) :
    m.E (φ.symm τ x) = τ (m.E x) := by
  rw [← hφ, MulEquiv.apply_symm_apply]

theorem Model.IsGalIso.galois_iso_isHomeomorph {φ} (hφ : m.IsGalIso φ) : IsHomeomorph φ := by
  have hint : Algebra.IsIntegral m.K' (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have h1 : Continuous φ.toMonoidHom := continuous_gal_of_fix φ.toMonoidHom fun y => ⟨m.E.symm y, fun σ hσ => by
    show φ σ y = y
    have := hφ σ (m.E.symm y)
    rwa [hσ, RingEquiv.apply_symm_apply] at this⟩
  have h2 : Continuous φ.symm.toMonoidHom := continuous_gal_of_fix φ.symm.toMonoidHom fun y => ⟨m.E y, fun τ hτ => by
    show φ.symm τ y = y
    apply m.E.injective
    rw [hφ.symm_apply, hτ]⟩
  exact (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph

theorem Model.isFrobeniusLift_iff_model [IsNonarchimedeanLocalField K] {φ} (hφ : m.IsGalIso φ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : IsFrobeniusLift K g ↔ IsFrob p m.K' (φ g) := by
  constructor
  · intro h y hy
    have h1 := h (m.E.symm y) ((m.mem_integral_closure_iff_norm _).2 (by rwa [RingEquiv.apply_symm_apply]))
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, RingEquiv.apply_symm_apply, m.card_residue_field_model] at h1
    exact h1
  · intro h x hx
    have h1 := h (m.E x) ((m.mem_integral_closure_iff_norm _).1 hx)
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, m.card_residue_field_model]
    exact h1

theorem Model.exists_abelianization_iso {φ} (hφ : m.IsGalIso φ) :
    ∃ ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K', IsHomeomorph ψ ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g) :=
  exists_topAb_iso φ hφ.galois_iso_isHomeomorph

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem card_le_mul_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [Finite B] [Finite C] (f : A →+ B)
    (g : C → A) (hg : ∀ a, f a = 0 → ∃ c, g c = a) : Finite A ∧ Nat.card A ≤ Nat.card C * Nat.card B := by
  classical
  have hsec : ∀ x : A, ∃ c : C, g c = x - Function.invFun f (f x) := fun x => by
    apply hg
    rw [map_sub, sub_eq_zero]
    exact (Function.invFun_eq (f := f) ⟨x, rfl⟩).symm
  choose σ hσ using hsec
  have hinj : Injective fun x : A => (σ x, f x) := fun x y hxy => by
    have h1 : σ x = σ y := congrArg Prod.fst hxy
    have h2 : f x = f y := congrArg Prod.snd hxy
    have e1 := hσ x
    have e2 := hσ y
    rw [h1, h2] at e1
    exact sub_left_injective (e1.symm.trans e2)
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_BrKer_le_mul {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (h' : K' ≤ L)
    (h1 : Finite (BrKer h)) (h2 : Finite (BrKer h')) :
    Finite (BrKer (h.trans h')) ∧ Nat.card (BrKer (h.trans h')) ≤ Nat.card (BrKer h) * Nat.card (BrKer h') := by
  let f : BrKer (h.trans h') →+ BrKer h' :=
    { toFun := fun x => ⟨(resPair h).hom.H 2 x.1, by
        show (resPair h').hom.H 2 _ = 0
        rw [← resPair_trans]; exact x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  refine card_le_mul_of_ker f (fun c : BrKer h => ⟨c.1, ?_⟩) (fun a ha => ⟨⟨a.1, congrArg Subtype.val ha⟩, rfl⟩)
  show (resPair (h.trans h')).hom.H 2 c.1 = 0
  rw [resPair_trans h h', show (resPair h).hom.H 2 c.1 = 0 from c.2, map_zero]

theorem card_BrKer_cyclic (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (BrKer h) = degLK p K L := by
  rw [BrKer_eq_BrLK hL h, card_BrLK, card_h2_cyclic_layer hK hL h g₀ hg]

theorem card_BrKer_prime (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (hp : (degLK p K L).Prime) : Nat.card (BrKer h) = degLK p K L := by
  have : Fact (degLK p K L).Prime := ⟨hp⟩
  have hc : IsCyclic (GalLK p K L) := isCyclic_of_prime_card (p := degLK p K L) card_GalLK
  obtain ⟨g₀, hg⟩ := hc.exists_generator
  exact card_BrKer_cyclic hK hL h g₀ hg

theorem exists_field_of_quotient (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (N : Subgroup (GalLK p K L)) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧ FiniteDimensional ℚ_[p] K' ∧
      subG p K K' = N.comap (QuotientGroup.mk' (subG p K L)) ∧ degLK p K K' = N.index := by
  have hle : subG p K L ≤ N.comap (QuotientGroup.mk' (subG p K L)) := fun σ hσ => by
    rw [Subgroup.mem_comap]
    have : QuotientGroup.mk' (subG p K L) σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
    rw [this]; exact N.one_mem
  obtain ⟨K', h1, h2, h3⟩ := exists_subG_eq_of_isOpen hK (N.comap (QuotientGroup.mk' (subG p K L)))
    (Subgroup.isOpen_mono hle (isOpen_subG hL))
  refine ⟨K', h1, ?_, h2, h3, ?_⟩
  · have := (subG_le_iff (L' := L) h1).1 (h3 ▸ hle)
    rwa [sup_eq_right.2 h] at this
  · show (subG p K K').index = _
    rw [h3, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem card_BrKer_le_of_prime_pow (l : ℕ) (hl : l.Prime) (k : ℕ) :
    ∀ (K L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → FiniteDimensional ℚ_[p] L →
      ∀ h : K ≤ L, (subG p K L).Normal → degLK p K L = l ^ k →
        Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ l ^ k := by
  have : Fact l.Prime := ⟨hl⟩
  induction k with
  | zero =>
    intro K L hK hL h hn hd
    have hs : Subsingleton (BrKer h) := ⟨fun x y => by
      have h0 : ∀ z : BrKer h, z = 0 := fun z => Subtype.ext (by
        have := degLK_smul_eq_zero hL h z.1 z.2
        rwa [hd, pow_zero, one_smul] at this)
      rw [h0 x, h0 y]⟩
    exact ⟨inferInstance, by rw [Nat.card_unique]; simp⟩
  | succ k ih =>
    intro K L hK hL h hn hd
    have hfin := finite_GalLK (K := K) hL
    have hcard : Nat.card (GalLK p K L) = l ^ (k + 1) := hd
    have hnt : Nontrivial (GalLK p K L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      exact Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt
    obtain ⟨N, hN, hNi⟩ := exists_normal_index_eq_prime l (IsPGroup.of_card hcard)
    obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h N
    have hn1 : (subG p K K').Normal := by rw [h4]; infer_instance
    have hn2 : (subG p K' L).Normal := subG_normal_of_le h1 h hn
    have hd1 : degLK p K K' = l := h5.trans hNi
    have hd2 : degLK p K' L = l ^ k := by
      have := degLK_mul h1 h2
      rw [hd, hd1, pow_succ'] at this
      exact (Nat.eq_of_mul_eq_mul_left hl.pos this).symm
    have hc1 : Nat.card (BrKer h1) = l := by
      rw [card_BrKer_prime hK h3 h1 (hd1 ▸ hl), hd1]
    have hf1 : Finite (BrKer h1) := Nat.finite_of_card_ne_zero (hc1 ▸ hl.ne_zero)
    obtain ⟨hf2, hc2⟩ := ih K' L h3 hL h2 hn2 hd2
    obtain ⟨hf, hc⟩ := card_BrKer_le_mul h1 h2 hf1 hf2
    refine ⟨hf, hc.trans ?_⟩
    rw [hc1, pow_succ']
    exact Nat.mul_le_mul_left _ hc2

theorem card_le_of_primary {A : Type*} [AddCommGroup A] (n : ℕ) (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (h : ∀ l : ℕ, l.Prime → Finite {a : A // ∃ k : ℕ, l ^ k • a = 0} ∧
      Nat.card {a : A // ∃ k : ℕ, l ^ k • a = 0} ≤ l ^ n.factorization l) :
    Finite A ∧ Nat.card A ≤ n := by
  classical
  let T : n.primeFactors → Type _ := fun l => {a : A // ∃ k : ℕ, l.1 ^ k • a = 0}
  have hfin : ∀ l, Finite (T l) := fun l => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).1
  let F : A → ∀ l, T l := fun a l => ⟨(n / l.1 ^ n.factorization l.1) • a, n.factorization l.1, by
    rw [smul_smul, Nat.mul_div_cancel' (Nat.ordProj_dvd n l.1)]; exact hA a⟩
  have hF0 : ∀ a : A, (∀ l : n.primeFactors, (n / l.1 ^ n.factorization l.1) • a = 0) → a = 0 := fun a ha => by
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqn : q ∣ n := hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (hA a))
    have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
    exact Nat.not_dvd_ordCompl hq hn.ne' (hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (ha ⟨q, hmem⟩)))
  have hinj : Injective F := fun a b hab => by
    rw [← sub_eq_zero]
    refine hF0 _ fun l => ?_
    rw [smul_sub, sub_eq_zero]
    exact congrArg Subtype.val (congrFun hab l)
  refine ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans ?_⟩
  rw [Nat.card_pi]
  calc ∏ l : n.primeFactors, Nat.card (T l) ≤ ∏ l : n.primeFactors, l.1 ^ n.factorization l.1 :=
        Finset.prod_le_prod' fun l _ => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).2
    _ = n := by
        rw [Finset.prod_coe_sort n.primeFactors (fun l => l ^ n.factorization l)]
        exact Nat.prod_factorization_pow_eq_self hn.ne'

theorem exists_sylow_field (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (l : ℕ) (hl : l.Prime) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧
      degLK p K' L = l ^ (degLK p K L).factorization l ∧ ¬ l ∣ degLK p K K' := by
  have : Fact l.Prime := ⟨hl⟩
  have hfin := finite_GalLK (K := K) hL
  obtain ⟨S⟩ : Nonempty (Sylow l (GalLK p K L)) := inferInstance
  obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h (S : Subgroup (GalLK p K L))
  refine ⟨K', h1, h2, ?_, h5 ▸ S.not_dvd_index⟩
  have e1 := degLK_mul h1 h2
  have e2 : (S : Subgroup (GalLK p K L)).index * Nat.card (S : Subgroup (GalLK p K L)) = degLK p K L :=
    (S : Subgroup (GalLK p K L)).index_mul_card
  rw [h5, ← e2] at e1
  have e3 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) e1
  rw [← e3, S.card_eq_multiplicity]
  rfl

theorem finiteDimensional_of_le' {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K' ≤ L)
    (hL : FiniteDimensional ℚ_[p] L) : FiniteDimensional ℚ_[p] K' :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective

theorem eq_of_resPair_eq_of_coprime {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hK' : FiniteDimensional ℚ_[p] K')
    (h : K ≤ K') (l : ℕ) (hl : l.Prime) (hd : ¬ l ∣ degLK p K K') (x y : Br p K) (kx ky : ℕ) (hx : l ^ kx • x = 0)
    (hy : l ^ ky • y = 0) (hxy : (resPair h).hom.H 2 x = (resPair h).hom.H 2 y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_BrKer_of_coprime hK' h _ ?_ (l ^ (kx + ky)) ?_
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd))
  · exact (map_sub ((resPair h).hom.H 2) x y).trans (sub_eq_zero.2 hxy)
  · rw [smul_sub, pow_add, mul_comm, mul_smul, hx, smul_zero, mul_comm, mul_smul, hy, smul_zero, sub_zero]

theorem card_BrKer_le (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] : Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ degLK p K L := by
  refine card_le_of_primary (degLK p K L) (degLK_pos hL)
    (fun a => Subtype.ext (degLK_smul_eq_zero hL h a.1 a.2)) fun l hl => ?_
  obtain ⟨K', h1, h2, h3, h4⟩ := exists_sylow_field hK hL h l hl
  have hK' := finiteDimensional_of_le' h2 hL
  obtain ⟨hf, hc⟩ := card_BrKer_le_of_prime_pow l hl _ K' L hK' hL h2 (subG_normal_of_le h1 h inferInstance) h3
  let F : {a : BrKer h // ∃ k : ℕ, l ^ k • a = 0} → BrKer h2 := fun a => ⟨(resPair h1).hom.H 2 a.1.1, by
    show (resPair h2).hom.H 2 _ = 0
    rw [← resPair_trans h1 h2]; exact a.1.2⟩
  have hinj : Injective F := fun a b hab => by
    obtain ⟨ka, hka⟩ := a.2
    obtain ⟨kb, hkb⟩ := b.2
    exact Subtype.ext (Subtype.ext (eq_of_resPair_eq_of_coprime hK' h1 l hl h4 a.1.1 b.1.1 ka kb
      (congrArg Subtype.val hka) (congrArg Subtype.val hkb) (congrArg Subtype.val hab)))
  exact ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans hc⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
