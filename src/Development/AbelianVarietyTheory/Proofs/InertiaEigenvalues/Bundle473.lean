module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle465
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  first | exact @GlobalTheory.gl_list_product_perm_char | exact GlobalTheory.gl_list_product_perm_char | (intros; apply GlobalTheory.gl_list_product_perm_char <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped IntermediateField

noncomputable section

theorem GlobalTheory.LocLanglands.exists_isLocalExt_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j c hφ hc L hL hloc
  classical
  haveI := IsAlgClosure.isAlgebraic (R := E) (K := Ω)
  haveI := IsAlgClosure.isAlgebraic (R := E') (K := Ω')

  obtain ⟨α, rfl⟩ : ∃ α : Ω, E⟮α⟯ = L := by
    obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element E L
    refine ⟨(α₀ : Ω), ?_⟩
    have := congrArg (IntermediateField.map L.val) hα₀
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this
  have hint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  set α' : Ω' := φ α with hα'
  have hint' : IsIntegral E' α' := Algebra.IsIntegral.isIntegral α'
  set p := minpoly E α with hp
  set m' := minpoly E' α' with hm'
  have hcomp : (algebraMap E' Ω').comp j = (φ : Ω →+* Ω').comp (algebraMap E Ω) := by
    ext x; exact (hφ x).symm
  have key : ∀ β : Ω, φ (aeval β p) = aeval (φ β) (p.map j) := by
    intro β
    rw [aeval_def, aeval_def, eval₂_map, hcomp]
    exact Polynomial.hom_eval₂ p (algebraMap E Ω) (φ : Ω →+* Ω') β
  have hpmon : p.Monic := minpoly.monic hint
  have hqne : p.map j ≠ 0 := (hpmon.map j).ne_zero
  have hdvd : m' ∣ p.map j := minpoly.dvd E' α' (by rw [← key, minpoly.aeval]; simp)
  have hm'root : ∀ σ' : G E' Ω', aeval (σ' α') m' = 0 := by
    intro σ'
    rw [show σ' α' = (σ' : Ω' →ₐ[E'] Ω') α' from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hq : ∀ y : Ω', aeval y m' = 0 → aeval y (p.map j) = 0 := by
    intro y hy
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, hy, zero_mul]

  have horb : ∀ β : Ω, aeval β p = 0 → ∃ τ : Weil h, (τ : G E Ω) α = β := by
    intro β hβ
    have hmin : minpoly E β = minpoly E α :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ hpmon).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 hmin
    obtain ⟨τ, hτ⟩ := hloc σ
    refine ⟨τ, ?_⟩
    have := hτ ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩
    simp only [IntermediateField.algebraMap_apply] at this
    rw [this]; exact hσ

  set L' : IntermediateField E' Ω' := E'⟮α'⟯ with hL'
  have hsub : ∀ x : E⟮α⟯, φ (x : Ω) ∈ L' := by
    let S : IntermediateField E Ω := Subfield.toIntermediateField
      (L'.toSubfield.comap (φ : Ω →+* Ω')) (fun x => by
        show φ (algebraMap E Ω x) ∈ L'
        rw [hφ]; exact L'.algebraMap_mem (j x))
    have hle : E⟮α⟯ ≤ S := IntermediateField.adjoin_simple_le_iff.2
      (show φ α ∈ L' from IntermediateField.mem_adjoin_simple_self E' α')
    intro x
    exact hle x.2
  let jL : E⟮α⟯ →+* L' := RingHom.codRestrict ((φ : Ω →+* Ω').comp (algebraMap E⟮α⟯ Ω)) L' hsub
  refine ⟨L', jL, IntermediateField.adjoin.finiteDimensional hint', ?_, ?_, fun x => rfl, ?_⟩
  ·
    intro σ'
    have h1 : aeval (σ' α') (p.map j) = 0 := hq _ (hm'root σ')
    have h2 : aeval (φ.symm (σ' α')) p = 0 := by
      apply φ.injective; rw [key, φ.apply_symm_apply, h1, map_zero]
    obtain ⟨τ, hτ⟩ := horb _ h2
    refine ⟨c τ, fun x => ?_⟩
    have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
    have hx : (c τ : G E' Ω') α' = σ' α' := by
      rw [← e, hτ, φ.apply_symm_apply]
    have hle : L'.toSubalgebra ≤ AlgHom.equalizer ((c τ : G E' Ω') : Ω' →ₐ[E'] Ω') (σ' : Ω' →ₐ[E'] Ω') := by
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      exact hx
    exact hle x.2
  · rw [IntermediateField.adjoin.finrank hint', IntermediateField.adjoin.finrank hint]
    apply le_antisymm
    · calc m'.natDegree ≤ (p.map j).natDegree := natDegree_le_of_dvd hdvd hqne
        _ = p.natDegree := natDegree_map j
    · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
      haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed E'
      have hsep : p.Separable := (minpoly.irreducible hint).separable
      have hnd : (p.aroots Ω).Nodup := nodup_roots (hsep.map)
      have hm'ne : m' ≠ 0 := minpoly.ne_zero hint'
      have hpne : p ≠ 0 := hpmon.ne_zero
      have himg : (p.aroots Ω).toFinset.image φ ⊆ (m'.aroots Ω').toFinset := by
        intro y hy
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hy
        rw [Multiset.mem_toFinset, mem_aroots] at hβ ⊢
        obtain ⟨τ, rfl⟩ := horb _ hβ.2
        refine ⟨hm'ne, ?_⟩
        have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
        rw [e]; exact hm'root _
      calc p.natDegree = (p.aroots Ω).card := IsAlgClosed.card_aroots_eq_natDegree.symm
        _ = (p.aroots Ω).toFinset.card := (Multiset.toFinset_card_of_nodup hnd).symm
        _ = ((p.aroots Ω).toFinset.image φ).card := (Finset.card_image_of_injective _ φ.injective).symm
        _ ≤ (m'.aroots Ω').toFinset.card := Finset.card_le_card himg
        _ ≤ (m'.aroots Ω').card := Multiset.toFinset_card_le _
        _ = m'.natDegree := IsAlgClosed.card_aroots_eq_natDegree
  ·
    apply Subalgebra.map_injective (f := L'.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, IntermediateField.range_val]
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (jL x).2
    · have hsg : ({α'} : Set Ω') ⊆ L'.val '' Set.range jL :=
        Set.singleton_subset_iff.2 ⟨jL ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩, ⟨_, rfl⟩, rfl⟩
      refine le_trans ?_ (Algebra.adjoin_mono hsg)
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic]

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairEpsTransport

section Maps
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_longElt (n : ℕ) : GeneralLinearGroup.map f (longElt n R) = longElt n S := by
  ext i j; simp [longElt, GeneralLinearGroup.map]

theorem map_invT (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R g) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f g) := by
  ext i j
  have h := congrArg (fun h : GL (Fin n) S => (h : Matrix (Fin n) (Fin n) S) j i)
    (map_inv (GeneralLinearGroup.map f) g)
  exact h

theorem map_tilde {n : ℕ} (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (tilde g) = tilde (GeneralLinearGroup.map f g) := by
  rw [tilde, tilde, map_mul, map_longElt, map_invT]

theorem map_corner {m : ℕ} (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (corner g) = corner (GeneralLinearGroup.map f g) := by
  ext i j
  show f ((emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1) : Matrix _ _ R) i j) =
    (emb₂ S (stdSum (rfl : m + 1 = m + 1)) (GeneralLinearGroup.map f g, 1) : Matrix _ _ S) i j
  rw [val_emb₂, val_emb₂]
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, GeneralLinearGroup.map] <;> split_ifs <;> simp

theorem superDiag_map {n : ℕ} (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map f g) = f (GlobalTheory.Whittaker.superDiag g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.Whittaker.superDiag, map_sum, GeneralLinearGroup.map]

theorem map_mem_unipB {n : ℕ} {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) :
    GeneralLinearGroup.map f g ∈ unipB S (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [GeneralLinearGroup.map, hg.1 i j h]
  · simp [GeneralLinearGroup.map, hg.2 i]

end Maps

section Core

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem map_map_symm {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem map_symm_map {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k) :
    GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem continuous_mapGL {n : ℕ} (i : k ≃+* k') (hi : Continuous i) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hi
  · exact Units.continuous_coe_inv.matrix_map hi

end Core

section Transport

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem isTestFun_comp {m : ℕ} (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {f : GL (Fin m) k → ℂ} (hf : IsTestFun f) :
    IsTestFun (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g)) := by
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  refine ⟨fun u hu g => ?_, h2.comp_continuous (continuous_mapGL i.symm hi'), ?_⟩
  · show f (GeneralLinearGroup.map i.symm.toRingHom (u * g)) = f (GeneralLinearGroup.map i.symm.toRingHom g)
    rw [map_mul]
    exact h1 _ (map_mem_unipB _ hu) _
  · refine ⟨GeneralLinearGroup.map i.toRingHom '' C, hC.image (continuous_mapGL i hi), fun g hg => ?_⟩
    obtain ⟨u, hu, c, hc, he⟩ := h3 _ hg
    refine ⟨GeneralLinearGroup.map i.toRingHom u, map_mem_unipB _ hu, GeneralLinearGroup.map i.toRingHom c,
      ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← he, map_map_symm]

variable {m : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem hasPairEps_of_equiv (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {ψ : AddChar k Circle} {ψ' : AddChar k' Circle} (hψ : ∀ x, ψ' (i x) = ψ x)
    {π : Representation ℂ (GL (Fin (m + 1)) k) V} {π' : Representation ℂ (GL (Fin (m + 1)) k') V'}
    {τ : Representation ℂ (GL (Fin m) k) W} {τ' : Representation ℂ (GL (Fin m) k') W'}
    (A : V ≃ₗ[ℂ] V') (hA : ∀ g v, A (π g v) = π' (GeneralLinearGroup.map i.toRingHom g) (A v))
    (B : W ≃ₗ[ℂ] W') (hB : ∀ g v, B (τ g v) = τ' (GeneralLinearGroup.map i.toRingHom g) (B v))
    {c : ℂ} (H : HasPairEps ψ π τ c) : HasPairEps ψ' π' τ' c := by
  intro ω' hω' l' L' hl' hL' I' hI' v' w'
  have hψinv : ∀ x, (ψ'⁻¹) (i x) = (ψ⁻¹) x := by
    intro x; simp only [AddChar.inv_apply]; rw [← map_neg, hψ]
  have hω : HasCentralChar τ (ω'.comp (Units.map i.toRingHom.toMonoidHom)) := by
    intro z w
    apply B.injective
    rw [hB, GeneralLinearGroup.map_scalar, hω', map_smul]
    rfl
  have hl : GlobalTheory.Whittaker.IsFunctional ψ π (l'.comp A.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hA, hl' _ (map_mem_unipB _ hu), superDiag_map]
    simp [hψ]
  have hL : GlobalTheory.Whittaker.IsFunctional ψ⁻¹ τ (L'.comp B.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hB, hL' _ (map_mem_unipB _ hu), superDiag_map]
    have := hψinv (GlobalTheory.Whittaker.superDiag u)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
  have hI : IsInvIntegral (I'.comp (LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom))) := by
    intro f hf x
    change I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g * x)) =
      I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g))
    have := hI' _ (isTestFun_comp i hi hi' hf) (GeneralLinearGroup.map i.toRingHom x)
    refine Eq.trans ?_ this
    congr 1
    funext g
    rw [map_mul, map_symm_map]
  have key := H _ hω _ _ hl hL _ hI (A.symm v') (B.symm w')
  have e1 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (tilde (corner g)) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ (tilde g) (B.symm w'))) =
      fun g => l' (π' (tilde (corner g)) v') * L' (τ' (tilde g) w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_tilde, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e2 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (corner g) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ g (B.symm w'))) =
      fun g => l' (π' (corner g) v') * L' (τ' g w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e3 : (ω'.comp (Units.map i.toRingHom.toMonoidHom)) (-1) = ω' (-1) := by
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3] at key
  exact key
end Transport

section Main

theorem equiv_apply_rep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) v

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_equiv_of_repRel (i : k ≃+* k') {n : ℕ} {π : IrrRep (GL (Fin n) k)} {π' : IrrRep (GL (Fin n) k')}
    (h : RepRel i (cls π) (cls π')) :
    ∃ E : π.V ≃ₗ[ℂ] π'.V, ∀ g v, E (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (E v) := by
  obtain ⟨n₀, π₀, π₀', e, h1, h2, he⟩ := h
  obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.1 h1
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h2
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h1)
  obtain ⟨φ'⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h2)
  refine ⟨φ.toLinearEquiv ≪≫ₗ e ≪≫ₗ φ'.toLinearEquiv.symm, fun g v => ?_⟩
  apply φ'.toLinearEquiv.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [equiv_apply_rep φ, he, equiv_apply_rep φ', LinearEquiv.apply_symm_apply]

end Main

end GlobalTheory.PairEpsTransport


open GlobalTheory.PairEpsTransport in
theorem GlobalTheory.LocLanglands.hasPairEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' hψ m π π' τ τ' c hπ hτ H
  have hi' : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
  obtain ⟨A, hA⟩ := exists_equiv_of_repRel i hπ
  obtain ⟨B, hB⟩ := exists_equiv_of_repRel i hτ
  exact hasPairEps_of_equiv i hi hi' hψ A hA B hB H

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.Unique

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_congr (rc rc' : IrrGL (k := w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E)))
    (H : ∀ Δ ∈ l, rc Δ.first = rc' Δ.first) : segSum rc l = segSum rc' l := by
  unfold segSum
  congr 1
  exact List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]

theorem first_fst_le_of_isL {k V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {𝔪 : Multiset (Segment k)}
    (hL : IsL 𝔪 π) {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : Δ.first.1 ≤ N := by
  obtain ⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩ := hL
  rw [← hmap] at hΔ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have h1 := (hLs i).deg_eq
  have h2 : (xs i).1 ≤ ∑ a, (xs a).1 := Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (Δs i).d ≤ (Δs i).deg := Nat.le_mul_of_pos_left _ (Δs i).len_pos
  show (Δs i).d ≤ N
  omega

theorem eq_of_isCusp (hLC : LocalConverseGL) (hBZ : BernsteinZelevinskyFiniteness)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc rc' : IrrGL (k := w.adicCompletion E) → WD h}
    {ψ : AddChar (w.adicCompletion E) Circle} (hψc : Continuous ψ) (hψ : ψ ≠ 1) (he : e ψ = e' ψ)
    (H : LawsMin a ha e rc) (H' : LawsMin a ha e' rc') (x : IrrGL (k := w.adicCompletion E)) (hx : x.IsCusp)
    (ih : ∀ y : IrrGL (k := w.adicCompletion E), y.1 < x.1 → rc y = rc' y) : rc x = rc' x := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨n, c⟩ := x
  obtain ⟨hn, hc⟩ := hx
  rcases n with _ | m
  · exact absurd hn (lt_irrefl 0)
  rcases m with _ | m
  · obtain ⟨χ, hχ, hx⟩ := GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl
    rw [hx, H.one, H'.one]
  · obtain ⟨x', hx'⟩ := H'.bij.2 (rc ⟨m + 2, c⟩)
    have hd : x'.1 = m + 2 := by
      have := H'.dim x'
      rw [hx', H.dim] at this
      exact this.symm
    have hcx' : x'.IsCusp := (H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)
    obtain ⟨n', c'⟩ := x'
    obtain rfl : n' = m + 2 := hd
    have hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩ := fun d => by
      simp [cls, IrrCl.cl_rep]
    have key : c = c' := by
      rw [← c.cl_rep, ← c'.cl_rep]
      refine IrrRep.cl_eq_iff.2 ?_
      refine hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_
      have h2 : rc (cls τ) = rc' (cls τ) := ih _ (by show m + 1 < m + 2; omega)
      refine ⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩
      have h1 := H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2
      rw [hcls] at h1 ⊢
      rw [he, ← hx', h2]
      exact h1
    subst key
    exact hx'.symm

theorem eq_of_lawsMin : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  intro hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have main : ∀ n, ∀ x : IrrGL (k := w.adicCompletion E), x.1 = n → rc x = rc' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      obtain ⟨𝔪, h𝔪⟩ := hEx _ x
      have hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
      rw [H.langlands _ x hL, H'.langlands _ x hL]
      refine segSum_congr rc rc' _ fun Δ hΔ => ?_
      have hle : Δ.first.1 ≤ n := hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)
      exact eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first
        fun y hy => ih y.1 (by omega) y rfl
  funext x
  exact main _ x rfl

end GlobalTheory.LocLanglands.Unique

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  first | exact @GlobalTheory.LocGL.isL_map_tw_of_isL | exact GlobalTheory.LocGL.isL_map_tw_of_isL | (intros; apply GlobalTheory.LocGL.isL_map_tw_of_isL <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  first | exact @GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | exact GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | (intros; apply GlobalTheory.isL_of_irreducible_prod_unitarisable_nu <;> assumption)
end
