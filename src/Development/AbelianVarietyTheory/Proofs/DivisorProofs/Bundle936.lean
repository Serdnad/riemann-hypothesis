module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle911
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.DenomBound

theorem cE_le_of_inZl : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  intro F _ _ z l a n _ ha hn h
  unfold cE
  apply Finset.sup_le
  intro C _
  unfold denomExp
  by_cases hz : z C = 0
  · simp [hz]
  have hpow : 2 ≤ a ^ n := le_trans ha (Nat.le_self_pow (by omega) a)
  have hA : (a ^ n - 1 : ℕ) ≠ 0 := by omega
  have hAq : ((a ^ n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hA
  have h1 := h C
  rw [inZl_iff, padicValRat.mul hAq hz, padicValRat.of_nat] at h1
  rw [← Nat.padicValNat_def] at h1
  have h2 : (2 : ℚ) ^ finrank ℚ F ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : padicValRat l (z C / 2 ^ finrank ℚ F) = padicValRat l (z C) - (finrank ℚ F : ℤ) * (padicValNat l 2 : ℤ) := by
    rw [padicValRat.div hz h2, padicValRat.pow (q := (2:ℚ))]
    have : padicValRat l (2 : ℚ) = padicValNat l 2 := by
      have := padicValRat.of_nat (p := l) (n := 2)
      simpa [Nat.padicValNat_def] using this
    rw [this]
  rw [h3]
  omega

end GlobalTheory.DenomBound
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.HcIso

theorem kills_hcTw : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b →
    ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A →
      Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  intro F _ _ t a b n hn α A β B hA hB hαA hβB
  obtain ⟨H, π, hmem, hsurj, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
  have hE : ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (z : GL (Fin n) F),
      (if InPar a z then α (tlG a z) * β (brG a b z) else 0) =
        ext0 H (fun p => α (π p).1 * β (π p).2) z := by
    intro α β z
    unfold ext0
    by_cases h : InPar a z
    · have hz : z ∈ H := (hmem z).2 h
      rw [if_pos h, dite_eq_left hz]
      show _ = α (π ⟨z, hz⟩).1 * β (π ⟨z, hz⟩).2
      rw [hπ]
    · have hz : z ∉ H := fun hz => h ((hmem z).1 hz)
      rw [if_neg h, dite_eq_right hz]
  have h1 : hcTw t a b α β n = fun x => (Nat.card H : ℂ)⁻¹ *
      ∑ᶠ y : GL (Fin n) F, ext0 H (fun p => α (π p).1 * β (π p).2) (y⁻¹ * x * (fun y => gal t n y) y) := by
    funext x
    unfold hcTw
    rw [hcard]
    congr 1
    congr 1
    funext y
    exact hE α β _
  have hid : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := by
    intro y
    ext i j
    simp [gal]
  have h2 : hc a b A B n = ind H (fun p => A (π p).1 * B (π p).2) := by
    funext x
    unfold hc hcTw ind
    rw [hcard]
    congr 1
    congr 1
    funext y
    rw [hid, hE]
  have hk := GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection H (GL (Fin a) F) (GL (Fin b) F) π hsurj α A β B hA hB hαA hβB
  rw [h1, h2]
  exact GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction (GL (Fin n) F) H (fun y => gal t n y) _ _ hk

end GlobalTheory.Shin.HcIso
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  first | exact @GlobalTheory.WpFam.Transp.main | exact GlobalTheory.WpFam.Transp.main | (intros; apply GlobalTheory.WpFam.Transp.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_sameDiv_of_lbIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M →
    ∃ τ : M.Sec, SameDiv σ τ := by
  intro X L M σ hL hM h
  obtain ⟨u, hu⟩ := LBIso.symm h
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  refine ⟨M.U j ⊓ L.U i, i, j, inf_le_right, inf_le_left,
    ReciprocityTheory.ChartRestriction.G.Semi.res (ReciprocityTheory.ChartRestriction.G.DVR.divLe j i) (u.s (i, j)), ⟨hj, hi⟩, ?_⟩
  have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (u := u) σ hu hM hL j i
  unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e
  change _ = _ * (ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : M.U j ⊓ L.U i ≤ M.U j)
    ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL).f j))
  rw [e, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end GlobalTheory.LogPair
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem uCoc_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : UCoc A B 1 := by
  unfold UCoc
  simp [Algebra.TensorProduct.one_def]

theorem uCoc_mul {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u v : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (n : ℕ) : UCoc A B (u ^ n) := by
  induction n with
  | zero => simpa using uCoc_one A B
  | succ n ih => rw [pow_succ]; exact uCoc_mul ih hu

theorem kummer_vanishing : B6h1 := by
  intro q _ A _ hq hu hp
  suffices h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0 := by
    have : spMap (algebraMap A B) = sch.map h ≫ sch.map f := by
      rw [← sch.map_comp, hhf]; rfl
    rw [this, pull_comp, hx, map_zero]
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A
  obtain ⟨hγ0, hγs, -, -⟩ := hγ B
  obtain ⟨u, rfl⟩ := hγs x hxB
  rw [hγ0]

  obtain ⟨e, he⟩ := GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q
  have hqB : IsUnit (q : (B : Type)) := by simpa using hq.map (algebraMap A B)
  have hqBB : IsUnit (q : B ⊗[A] B) := by simpa using hq.map (algebraMap A (B ⊗[A] B))
  have hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B)) := by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1 :=
    (mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2
  have hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) := by
    have h2 := u.2
    change _ = _ at h2
    have h3 := congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2
    simp only [AddMonoidHom.add_apply, map_add (f := _), toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3
    rw [he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB] at h3
    have h4 := congrArg Units.val h3
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4
    exact h4

  set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A
  obtain ⟨hmul, hone, -, -, -⟩ := hδ B
  have hδ1 : δ B 1 = 1 := by
    have := hmul 1 1 (uCoc_one A B) (uCoc_one A B)
    rw [mul_one] at this
    simpa using this
  have hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n := by
    intro n
    induction n with
    | zero => simpa using hδ1
    | succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]
  have hδU : δ B U = 1 := hp _ (by rw [← hδpow, hUq, hδ1])
  obtain ⟨w, hw⟩ := (hone U hUc).1 hδU
  let iL : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  have hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w :=
    Units.ext (by simpa [iL, iR] using hw)
  have hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q) := by
    rw [map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]
  have hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹ := by
    rw [map_inv, map_inv, hWq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')
  have haa : a * a' = 1 :=
    FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])
  obtain ⟨v, hv⟩ := hu ⟨a, a', haa, by rw [mul_comm, haa]⟩
  let vB : (B : Type)ˣ := Units.map (algebraMap A B).toMonoidHom v
  have hvB : vB ^ q = w ^ q := by
    apply Units.ext
    rw [← map_pow, ← hv, Units.coe_map]
    exact ha
  have hT : (vB * w⁻¹) ^ q = 1 := by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]
  let Tr : rootsOfUnity q (B : Type) := ⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩
  have hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB := by
    apply Units.ext
    simp [vB, iL, iR]
  refine ⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩
  apply (e _ hqBB).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]
  change U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)
  rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]
  rw [mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]
end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.continuousCone_descends_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first | (exact @GlobalTheory.EtC.contCone_of_etale_surjective) | (exact GlobalTheory.EtC.contCone_of_etale_surjective) | (intros; apply GlobalTheory.EtC.contCone_of_etale_surjective <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.peak_sections_finite_weighted_atlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  first | exact @GlobalTheory.OTY.peak_sections_finite | exact GlobalTheory.OTY.peak_sections_finite | (intros; apply GlobalTheory.OTY.peak_sections_finite <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem isEtCoord_openImmersion (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X)
    [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)) :
    IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t →
      IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  intro hU hW ht
  have hφ : (e.appLE U W h).hom.Etale := e.etale_appLE hU hW h
  have hc : (e.appLE U W h).hom.comp (cstOn f U) = cstOn (e ≫ f) W := by
    have e₁ : f.appLE ⊤ U le_top ≫ e.appLE U W h = (e ≫ f).appLE ⊤ W le_top :=
      Scheme.Hom.appLE_comp_appLE e f ⊤ U W le_top h
    have e₂ : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) ≫ e.appLE U W h =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (e ≫ f).appLE ⊤ W le_top := by
      rw [Category.assoc, e₁]
    exact congrArg CommRingCat.Hom.hom e₂
  unfold IsEtCoord
  rw [← hc, ← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ ht hφ

end GlobalTheory.LogPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SecFlatBC

theorem pullLE_ofSec {X X' : Scheme.{0}} {L : LB X} (τ : L.Sec) (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens)
    (e : V' ≤ π ⁻¹ᵁ V) :
    AbLaw.SecOn.pullLE L π V V' e (LB.ofSec τ V) = LB.ofSec (Cartier.secPull τ π) V' := by
  refine LB.sec_ext fun j => ?_
  rw [AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]
  simp only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sum_smul_f {X' : Scheme.{0}} {R' : Type} [CommRing R'] (f' : X' ⟶ Sp R') {M : LB X'} {n : ℕ}
    (c : Fin n → R') (τ : Fin n → M.Sec) (i : M.ι) :
    (∑ a, AbLaw.cst f' ⊤ (c a) • τ a).f i = ∑ a, cstOn f' _ (c a) * (τ a).f i := by
  let F : M.Sec →+ Γ(X', M.U i) := ⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩
  change F _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _
  rw [show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]
  rfl

theorem exists_sum_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  intro R R' _ _ φ X X' f f' π _ _ L hφ H hL σ
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  have H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := H
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := GlobalTheory.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) :=
    GlobalTheory.isAffineOpen_finset_biInf hD
  have hc' := AbLaw.PerfOfModel.iSup_preimage π hc
  let E := AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'
  let E₀ := AbLaw.CechOne.secKerEquiv L f hc
  let d := ((AbLaw.cechLB f L D).d 0 1).hom
  obtain ⟨x, hx, hxy⟩ := (AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2
  have hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R') :=
    Module.Flat.ker_lTensor_eq (R := R) R' R' d
  rw [hker] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let e := S.equivFin
  refine ⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩

  have key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π := by
    apply E.injective
    apply Subtype.ext

    rw [← hxy, map_sum, map_sum, map_sum, Submodule.coe_sum,
    ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]
    funext s
    have hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s =
        AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i)) := by
      rw [← AbLaw.CechOne.secKerEquiv_val L f hc]
      exact congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm
    change (e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) =
      (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s
    rw [hk, AbLaw.CechOne.secKerEquiv_val]
    change _ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _
    rw [AbLaw.SecOnR.pull_of, pullLE_ofSec]
    rfl
  intro i
  rw [key, sum_smul_f]

end GlobalTheory.SecFlatBC
end
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.flat_base_change_sections : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  first | exact @_root_.GlobalTheory.SecFlatBC.exists_sum_secPull | exact _root_.GlobalTheory.SecFlatBC.exists_sum_secPull | (intros; apply _root_.GlobalTheory.SecFlatBC.exists_sum_secPull <;> assumption)

end
end
