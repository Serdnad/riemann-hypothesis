module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle031
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section Mean

open GroundTheory.Automorphic (stabilizerOf mem_stabilizerOf)

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private noncomputable def mean (T : Subgroup H) [T.FiniteIndex] (v : V) : V :=
  (Nat.card (H ⧸ T) : ℂ)⁻¹ • ∑ q : H ⧸ T, ρ q.out v

private theorem card_ne (T : Subgroup H) [T.FiniteIndex] : (Nat.card (H ⧸ T) : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Subgroup.FiniteIndex.index_ne_zero

private theorem out_apply {T : Subgroup H} {v : V} (hv : ∀ t ∈ T, ρ t v = v) (x : H) :
    ρ (x : H ⧸ T).out v = ρ x v := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T x
  rw [ht, map_mul, Module.End.mul_apply, hv t t.2]

private theorem mean_eq {T' T : Subgroup H} [T'.FiniteIndex] [T.FiniteIndex] (hle : T' ≤ T) {v : V}
    (hv : ∀ t ∈ T, ρ t v = v) : mean ρ T' v = mean ρ T v := by
  unfold mean
  have hcard : Nat.card (H ⧸ T') = Nat.card (H ⧸ T) * Nat.card (T ⧸ T'.subgroupOf T) := by
    rw [Nat.card_congr (Subgroup.quotientEquivProdOfLE hle), Nat.card_prod]
  have hsum : ∑ q : H ⧸ T', ρ q.out v =
      ∑ x : (H ⧸ T) × (T ⧸ T'.subgroupOf T), ρ x.1.out v := by
    refine Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ _ ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.quotientEquivProdOfLE_apply]
    show ρ (x : H ⧸ T').out v = ρ (x : H ⧸ T).out v
    rw [out_apply ρ (fun t ht => hv t (hle ht)), out_apply ρ hv]
  have hm : (Nat.card (T ⧸ T'.subgroupOf T) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [hsum, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]

private theorem mean_mem {T : Subgroup H} [T.FiniteIndex] {v : V} (hv : ∀ t ∈ T, ρ t v = v) (h : H) :
    ρ h (mean ρ T v) = mean ρ T v := by
  unfold mean

  rw [map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((h * q.out : H) : H ⧸ T) = h • q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (h * q.out), hq]
  rfl

private theorem mean_lin {W : Type} [AddCommGroup W] [Module ℂ W] (T : Subgroup H) [T.FiniteIndex]
    (p : V →ₗ[ℂ] W) {v : V} (hp : ∀ h, p (ρ h v) = p v) : p (mean ρ T v) = p v := by

  simp only [mean, map_smul, map_sum, hp, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
  ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne T), one_smul]

private theorem mean_add (T : Subgroup H) [T.FiniteIndex] (x y : V) :
    mean ρ T (x + y) = mean ρ T x + mean ρ T y := by
  simp only [mean, map_add (f := _), Finset.sum_add_distrib, smul_add]

private theorem mean_smul (T : Subgroup H) [T.FiniteIndex] (c : ℂ) (x : V) :
    mean ρ T (c • x) = c • mean ρ T x := by
  simp only [mean, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem mean_act {T : Subgroup H} [T.FiniteIndex] [T.Normal] {v : V} (hv : ∀ t ∈ T, ρ t v = v)
    (h : H) : mean ρ T (ρ h v) = mean ρ T v := by
  unfold mean
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight (h : H ⧸ T)) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((q.out * h : H) : H ⧸ T) = q * (h : H ⧸ T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (q.out * h), hq]
  rfl

private theorem exists_avg (hfin : ∀ v, (stabilizerOf ρ v).FiniteIndex) : ∃ e : V →ₗ[ℂ] V,
    (∀ h v, ρ h (e v) = e v) ∧ (∀ h v, e (ρ h v) = e v) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V),
        (∀ h, p (ρ h v) = p v) → p (e v) = p v := by
  let E : V → V := fun v => @mean H V _ _ _ ρ (stabilizerOf ρ v) (hfin v) v
  have hE : ∀ (v : V) (T : Subgroup H) [T.FiniteIndex], T ≤ stabilizerOf ρ v → E v = mean ρ T v := by
    intro v T _ hle
    haveI := hfin v
    exact (mean_eq ρ hle (fun t ht => mem_stabilizerOf.1 ht)).symm
  have hfx : ∀ v, ∀ t ∈ stabilizerOf ρ v, ρ t v = v := fun v t ht => mem_stabilizerOf.1 ht
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    haveI := hfin x
    haveI := hfin y
    haveI := hfin (x + y)
    show E (x + y) = E x + E y
    rw [hE (x + y) (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_left),
      hE y (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_right),
      mean_add]
  · intro c x
    haveI := hfin x
    haveI := hfin (c • x)
    show E (c • x) = c • E x
    rw [hE (c • x) (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_left, mean_smul]
  · intro h v
    haveI := hfin v
    exact mean_mem ρ (hfx v) h
  · intro h v
    haveI := hfin v
    haveI := hfin (ρ h v)
    have hle : (stabilizerOf ρ v).normalCore ≤ stabilizerOf ρ (ρ h v) := by
      intro t ht
      rw [mem_stabilizerOf]
      have h1 : h⁻¹ * t * h ∈ (stabilizerOf ρ v).normalCore := by
        have := (Subgroup.normalCore_normal (stabilizerOf ρ v)).conj_mem t ht h⁻¹
        simpa using this
      have h2 := hfx v _ (Subgroup.normalCore_le _ h1)
      calc ρ t (ρ h v) = ρ (t * h) v := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (h * (h⁻¹ * t * h)) v := by rw [show h * (h⁻¹ * t * h) = t * h by group]
        _ = ρ h (ρ (h⁻¹ * t * h) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ h v := by rw [h2]
    show E (ρ h v) = E v
    rw [hE (ρ h v) _ hle, hE v _ (Subgroup.normalCore_le _),
      mean_act ρ (fun t ht => hfx v t (Subgroup.normalCore_le _ ht)) h]
  · intro W _ _ p v hp
    haveI := hfin v
    exact mean_lin ρ _ p hp

end Mean

theorem UpperTheory.Gal.Join.avgEx :
    UpperTheory.Gal.Join.AvgEx := by
  intro G V _ _ _ _ _ π hsm K hK
  unfold IsSmooth at hsm
  unfold CO at hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  let ρ : Representation ℂ K V := π.comp K.subtype
  have hfin : ∀ v, (GroundTheory.Automorphic.stabilizerOf ρ v).FiniteIndex := by
    intro v
    haveI := Subgroup.quotient_finite_of_isOpen (GroundTheory.Automorphic.stabilizerOf ρ v) ((hsm v).preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨e, he1, he2, he3⟩ := exists_avg ρ hfin
  have hfix : ∀ w, (∀ g ∈ K, π g w = w) → e w = w := by
    intro w hw
    have := he3 V LinearMap.id w (fun h => hw h h.2)
    simpa using this
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro g hg
    exact he1 ⟨g, hg⟩ v
  · intro v hv
    rw [GlobalTheory.Parabolic.mem_fixed] at hv
    exact hfix v hv
  · intro g hg v
    exact he2 ⟨g, hg⟩ v
  · intro W _ _ p v hp
    exact he3 W p v (fun h => hp h h.2)
  · intro s A hA hs hsurj v
    have h1 : e (A (e v)) = A (e v) := by
      apply hfix
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hsurj g hg
      rw [← hA]
      congr 1
      exact he1 ⟨h, hh⟩ v
    have h2 : e (A (e v)) = e (A v) := by
      refine he3 V (e ∘ₗ A) v (fun h => ?_)
      show e (A (π h v)) = e (A v)
      rw [hA]
      exact he2 ⟨s h, hs h h.2⟩ (A v)
    rw [← h1, h2]
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
end

section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private lemma exists_common_eigenvector {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, f i * f j = f j * f i) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ y ∈ W, f i y ∈ W) :
    ∃ y ∈ W, y ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i y = c • y :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector f hc W hW hst

theorem UpperTheory.Gal.Join.twExp :
    UpperTheory.Gal.Join.TwExp := by
  intro T X _ _ _ ρ P _ s A hρ hA hAρ t₁ htr
  let r : T → Module.End ℂ P := fun t => (ρ t).restrict (hρ t)
  let A' : Module.End ℂ P := A.restrict hA
  have r_apply : ∀ t (y : P), ((r t y : P) : X) = ρ t y := fun t y => rfl
  have A_apply : ∀ y : P, ((A' y : P) : X) = A y := fun y => rfl
  have r_mul : ∀ a b, r (a * b) = r a * r b := by
    intro a b
    ext y
    simp [r_apply, Module.End.mul_apply, map_mul]
  have hcomm : ∀ a b, r a * r b = r b * r a := by
    intro a b
    rw [← r_mul, ← r_mul, mul_comm]
  have hsemi : ∀ t, A' * r t = r (s t) * A' := by
    intro t
    ext y
    simp [r_apply, A_apply, Module.End.mul_apply, hAρ]
  let N : (T → ℂ) → Submodule ℂ P := fun χ => ⨅ t, (r t).maxGenEigenspace (χ t)
  have hmaps : ∀ a b c, Set.MapsTo (r a) ((r b).maxGenEigenspace c) ((r b).maxGenEigenspace c) :=
    fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c
  have hind : iSupIndep N := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo r hmaps
  have htop : ⨆ χ, N χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute r
      (fun a b _ => hcomm a b) (fun t => Module.End.iSup_maxGenEigenspace_eq_top (r t))
  let f : Module.End ℂ P := r t₁ * A'
  have hAN : ∀ χ, Set.MapsTo f (N χ) (N (χ ∘ s.symm)) := by
    intro χ y hy
    have hy' : ∀ t, y ∈ (r t).maxGenEigenspace (χ t) := fun t => (Submodule.mem_iInf _).mp hy t
    refine (Submodule.mem_iInf _).mpr fun t => ?_
    have key : A' y ∈ (r t).maxGenEigenspace (χ (s.symm t)) := by
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hy' (s.symm t))
      refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
      have hsb : SemiconjBy A' (r (s.symm t) - χ (s.symm t) • (1 : Module.End ℂ P))
          (r t - χ (s.symm t) • (1 : Module.End ℂ P)) := by
        have h1 := hsemi (s.symm t)
        rw [MulEquiv.apply_symm_apply] at h1
        unfold SemiconjBy
        rw [mul_sub, sub_mul, h1]
        simp
      have := congrArg (fun g : Module.End ℂ P => g y) (hsb.pow_right k).eq
      simp only [Module.End.mul_apply, hk, map_zero] at this
      exact this.symm
    exact hmaps t₁ t _ key

  have hex : ∃ χ : T → ℂ, χ ∘ s = χ ∧ N χ ≠ ⊥ := by
    by_contra hno
    push_neg at hno
    let J := {χ : T → ℂ // χ ∘ s ≠ χ}
    let N' : J → Submodule ℂ P := fun j => N j.1
    have hind' : iSupIndep N' := hind.comp Subtype.val_injective
    have htop' : ⨆ j, N' j = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun χ => ?_
      by_cases h : χ ∘ s = χ
      · rw [hno χ h]
        exact bot_le
      · exact le_iSup N' ⟨χ, h⟩
    have hint : DirectSum.IsInternal N' :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind' htop'
    have hne : ∀ χ : T → ℂ, χ ∘ s ≠ χ → χ ∘ s.symm ≠ χ := by
      intro χ h e
      apply h
      funext t
      have := congrFun e (s t)
      simpa using this.symm
    let σ : J → J := fun j => ⟨j.1 ∘ s.symm, by
      intro e
      apply hne j.1 j.2
      funext t
      have := congrFun e t
      simpa [Function.comp] using this.symm⟩
    have hσ : ∀ j, σ j ≠ j := fun j e => hne j.1 j.2 (congrArg Subtype.val e)
    have hzero : LinearMap.trace ℂ P f = 0 :=
      LinearMap.trace_eq_zero_of_mapsTo_ne hint σ hσ (fun j => hAN j.1)
    apply htr
    have hst : ∀ y ∈ P, (ρ t₁ ∘ₗ A) y ∈ P := fun y hy => hρ t₁ _ (hA y hy)
    have hfeq : (ρ t₁ ∘ₗ A).restrict hst = f := by
      ext y
      rfl
    unfold trIn
    rw [dite_eq_left hst, hfeq, hzero]
  obtain ⟨χ, hχ, hN⟩ := hex
  have hNst : ∀ t, ∀ y ∈ N χ, r t y ∈ N χ := by
    intro t y hy
    exact (Submodule.mem_iInf _).mpr fun t' => hmaps t t' _ ((Submodule.mem_iInf _).mp hy t')
  obtain ⟨y, hyN, hy0, hy⟩ := exists_common_eigenvector r hcomm (N χ) hN hNst
  choose c hc using hy
  have hcχ : ∀ t, c t = χ t := by
    intro t
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp ((Submodule.mem_iInf _).mp hyN t)
    have hpow : ∀ m : ℕ, ((r t - χ t • (1 : Module.End ℂ P)) ^ m) y = (c t - χ t) ^ m • y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hc t]
        simp only [LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ']
        ring_nf
    rw [hpow k] at hk
    have := (smul_eq_zero.mp hk).resolve_right hy0
    by_contra hne
    exact pow_ne_zero k (sub_ne_zero.mpr hne) this
  have hc1 : c 1 = 1 := by
    have h1 : r 1 = 1 := by
      ext v
      simp [r_apply]
    have h2 := hc 1
    rw [h1, Module.End.one_apply] at h2
    have h3 : (c 1 - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
  have hcmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h2 := hc (a * b)
    rw [r_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul] at h2
    have h3 : (c (a * b) - c b * c a) • y = 0 := by
      rw [sub_smul, ← h2, sub_self]
    rw [sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0), mul_comm]
  let m : T →* ℂ := { toFun := c, map_one' := hc1, map_mul' := hcmul }
  refine ⟨m.toHomUnits, fun t => ?_, (y : X), y.2, fun h => hy0 (Subtype.ext h), fun t => ?_⟩
  · apply Units.ext
    simp only [MonoidHom.coe_toHomUnits]
    change c (s t) = c t
    rw [hcχ, hcχ]
    exact congrFun hχ t
  · simp only [MonoidHom.coe_toHomUnits]
    change ρ t (y : X) = c t • (y : X)
    exact congrArg Subtype.val (hc t)
end
