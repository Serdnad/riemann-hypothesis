module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameGenPowers
open scoped Pointwise

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  apply GlobalTheory.TameEig.wild_mem_Ine <;> assumption

theorem finite_roots (K : Type) [Field K] (m : ℕ) (hm : m ≠ 0) :
    {u : Kˣ | u ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  have : Finite (rootsOfUnity m K) := inferInstance
  have h := Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)
  exact h.subset fun u hu => (mem_rootsOfUnity m u).2 hu

theorem eq_one_of_wild_prime (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (K : Type) [Field K] [TopologicalSpace K] [T2Space K]
    (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ) (hr : Continuous r) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : r σ ^ l = 1) : r σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite := (finite_roots K l hl.ne_zero).diff
  have hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hr
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : r σ ^ n = 1 := by
    have h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1}) := hsub hτ
    by_contra hne
    apply h2
    refine ⟨?_, by rwa [map_pow]⟩
    show r (σ ^ n) ^ l = 1
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem mem_zpowers_of_tameGen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (γ : Formalism.ConjugateSelfDual.G E Ω), TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ m : ℕ, ((m : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) → ∀ σ ∈ Ine (F := E) A, r σ ∈ Subgroup.zpowers (r γ) := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hm
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith
  have hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite := by
    refine (finite_roots K m hm0).subset ?_
    rintro u ⟨z, rfl⟩
    show (r γ ^ z) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]
  have hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
      Set (Formalism.ConjugateSelfDual.G E Ω)) := hfin.isClosed.preimage hr
  refine closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)
  rintro τ (rfl | hτ)
  · exact Subgroup.mem_zpowers _
  · show r τ ∈ Subgroup.zpowers (r γ)
    rw [hw τ hτ]
    exact one_mem _

end GlobalTheory.TameGenPowers
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  first | exact @GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | exact GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | (intros; apply GlobalTheory.RealGeo.BaseFrame.exists_baseFrame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RealGeo.Upd

section
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section
variable (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (kap lam err)

abbrev upE : RealDat D A C.Q.c.F := { R.upd6 kap lam with err0 := err }



def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat C.toCore R i Tp tup) :
    OMDat C.toCore (upE C R kap lam err) i Tp tup := { O with }



def updFWT {κ v₀} (t : FWTie C R κ v₀) : FWTie C (upE C R kap lam err) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

variable {C R}
variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (O : ∀ i, OMDat C.toCore R i Unit (fun _ => A.μ0))



theorem omPins_upE (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (upE C R kap lam err) κ v₀ (fun i => updO C R kap lam err (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end

end

end GlobalTheory.RealGeo.Upd

namespace GlobalTheory.RealGeo



theorem geoHalf_upd : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (ph : Fin D.R.m → ℂ) kap lam err (g : GlobalTheory.RealGeo.GeoHalf C R ph), ∃ g' : GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph, g'.κ = g.κ ∧ HEq g'.v₀ g.v₀ ∧ (GlobalTheory.RealGeo.InGeo g → GlobalTheory.RealGeo.InGeo g') := by
  intro D G _ _ Pl0 T A C _ R ph kap lam err g
  refine ⟨⟨g.κ, g.v₀, Upd.updFWT C R kap lam err g.fw, g.bar, fun i => Upd.updO C R kap lam err (g.O i),
    fun i => Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩, rfl, HEq.rfl, ?_⟩
  intro h
  exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

end GlobalTheory.RealGeo
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.RamRational

section General

variable {K V W M N ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}

theorem exists_complex_extension [Fintype ι] (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (hli : LinearIndependent ℂ (fun i => e (b i))) (g : V →ₛₗ[σ] N) :
    ∃ G : M →ₗ[ℂ] N, ∀ x, G (e x) = g x := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℂ (fun i => g (b i))) ∘ₗ hli.repr)
  have hb : ∀ i, G (e (b i)) = g (b i) := by
    intro i
    have hm : e (b i) ∈ Submodule.span ℂ (Set.range (fun i => e (b i))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hG ⟨e (b i), hm⟩
    have h2 : hli.repr ⟨e (b i), hm⟩ = Finsupp.single i 1 := hli.repr_eq_single i _ rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2,
      Finsupp.linearCombination_single, one_smul] at h1
    exact h1
  refine ⟨G, fun x => ?_⟩
  rw [← b.sum_repr x]

  simp only [map_sum, LinearMap.map_smulₛₗ, hb, RingHom.id_apply]

theorem mem_span_of_kernel [Fintype ι] {J : Type} [Fintype J] (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (hli : LinearIndependent ℂ (fun i => e (b i)))
    (F : J → M →ₗ[ℂ] M) (hF : ∀ j x, ∃ y, e y = F j (e x)) (m : M)
    (hm : m ∈ Submodule.span ℂ (Set.range (fun i => e (b i)))) (h0 : ∀ j, F j m = 0) :
    m ∈ Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b hli
  let f : J → V →ₗ[K] V := fun j => descend e e hinj (F j) (hF j)
  have hf : ∀ j x, e (f j x) = F j (e x) := fun j x => descend_spec e e hinj (F j) (hF j) x
  let g : V →ₗ[K] (J → V) := LinearMap.pi f
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨h, hh⟩ := LinearMap.exists_extend s
  have hg : ∀ x, g (h (g x)) = g x := by
    intro x
    have h1 : h (g x) = s (g.rangeRestrict x) := LinearMap.congr_fun hh (g.rangeRestrict x)
    have h2 := LinearMap.congr_fun hs (g.rangeRestrict x)
    rw [h1]
    exact congrArg Subtype.val h2
  choose H hH using fun j : J =>
    exists_complex_extension e b hli (e.comp (h ∘ₗ LinearMap.single K (fun _ : J => V) j))
  let P : M →ₗ[ℂ] M := LinearMap.id - ∑ j, H j ∘ₗ F j
  have hP : ∀ x, P (e x) = e (x - h (g x)) := by
    intro x
    have h1 : g x = ∑ j, Pi.single j (f j x) := (Finset.univ_sum_single (g x)).symm
    rw [h1]

    simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_sub, map_sum, ← hf, hH, LinearMap.coe_single]
  have hPm : P m = m := by
    simp [P, LinearMap.sum_apply, h0]
  rw [← hPm]
  have hle : Submodule.span ℂ (Set.range (fun i => e (b i))) ≤
      (Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0})).comap P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨b i - h (g (b i)), fun j => ?_, (hP _).symm⟩
    have h1 : g (b i - h (g (b i))) = 0 := by rw [map_sub, hg, sub_self]
    have h2 : f j (b i - h (g (b i))) = 0 := congrFun h1 j
    rw [← hf, h2, map_zero]
  exact hle hm

theorem preserves_of_span (e : V →ₛₗ[σ] M) (S : Set V) (hS : Submodule.span K S = ⊤)
    (F : M →ₗ[ℂ] M) (hF : ∀ x ∈ S, ∃ y, e y = F (e x)) (x : V) : ∃ y, e y = F (e x) := by
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hF x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by simp [LinearMap.map_smulₛₗ, ha]⟩

end General

theorem span_ramSub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL]
    {embLL : LL →+* ℂ} {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) :
    Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) = A.Mram := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro m hm
    have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
      (M.emb_basis 0).2.trans M.Fi_zero
    have hrho : ∀ v a x, ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := fun v a =>
      preserves_of_span (M.emb 0) _ (M.lat_good 0).2.2 (A.rhoT v a) (fun x hx => by
        obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx
        exact ⟨y, hy⟩)
    have hNm : ∀ v x, ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
      intro v x
      choose y hy using fun a => hrho v a x
      exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩
    have hall : ∀ x, M.emb 0 x ∈ A.Mu0 := by
      intro x

      rw [← hsp, ← (M.lat 0).b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := mem_span_of_kernel (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm hNm m
      (hsp ▸ hm.1) (fun v => (Submodule.mem_iInf _).1 hm.2 v)
    refine Submodule.span_mono (Set.image_mono ?_) h
    intro x hx
    exact ⟨hall x, (Submodule.mem_iInf _).2 hx⟩

theorem span_ramSub_cols : ∀ (B : Base) (C : Cols B) (u : B.Word),
    Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) =
      (C.mem u).A.Mram :=
  fun _ C u => span_ramSub (C.fm u)

end GlobalTheory.RamRational
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelChoice

theorem mod_eq_one_of_norm {E : Type} [Field E] [NumberField E] (c : E →+* E) (π : 𝓞 E) (p m : ℕ) (hm : 1 < m)
    (hn : (π : E) * c (π : E) = (p : E)) (hc : π - 1 ∈ Ideal.span {((m : ℕ) : 𝓞 E)}) : p % m = 1 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
  have hπ : (π : E) = 1 + (a : E) * (m : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) ha
    simp only [map_mul, map_natCast, map_sub, map_one] at h
    change (a : E) * (m : E) = (π : E) - 1 at h
    rw [h]; ring
  have hai : IsIntegral ℤ (a : E) := a.2
  have hci : IsIntegral ℤ (c (a : E)) := hai.map c.toIntAlgHom
  have hmi : IsIntegral ℤ ((m : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a) := by
    rw [map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add (f := _), map_one, map_mul, map_natCast]
    field_simp
    ring
  have hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m)) := by
    rw [hx]
    exact (hai.add hci).add (hmi.mul (hai.mul hci))
  have hqi : IsIntegral ℤ (((p : ℚ) - 1) / m) :=
    (isIntegral_algebraMap_iff ).1 hxi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqi
  have hk' : ((p : ℚ) - 1) = (k : ℚ) * m := by
    have : (k : ℚ) = ((p : ℚ) - 1) / m := by simpa using hk
    rw [this]; field_simp
  have hz : (p : ℤ) = 1 + (m : ℤ) * k := by
    have : ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : ((p % m : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, hz, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)
  exact_mod_cast h1

theorem exists_levCh : ∀ (P : PreCh) (du : P.Word → ℕ) (Ds Ga : ℝ), (∀ u, 0 < du u) → 0 < Ds → 1 < Ga → (∀ u, ∃ (π : 𝓞 P.H.E) (p : ℕ), p.Prime ∧ p ≠ P.H.pde ∧ p ≠ P.H.pde' ∧ (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (p : P.H.E) ∧ π - 1 ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)} ∧ (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) * ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ L : LevCh P, L.duStar = du ∧ L.Dstar = Ds ∧ L.GamP = Ga := by
  intro P du Ds Ga hdu hDs hGa h
  choose π p hp h1 h2 hK hN hc hlo hhi using h
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.H.QS := P.H.QS_pos
  have hm : 1 < P.H.QS * P.H.q * P.H.d := by
    have hq : 0 < P.H.q := by omega
    have hd : 0 < P.H.d := by omega
    have h1 : P.H.q ≤ P.H.QS * P.H.q := Nat.le_mul_of_pos_left _ hn
    have h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_right _ hd
    omega
  have hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1 := fun u => by
    refine mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_
    refine Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)
    exact Nat.cast_dvd_cast (Dvd.intro _ rfl)
  exact ⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc,
           T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs,
           GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl⟩

end GlobalTheory.Mem.LevelChoice
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
end
