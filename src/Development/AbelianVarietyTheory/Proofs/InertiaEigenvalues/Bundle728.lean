module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle491
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle714
public import Formalism.SharpRestriction.LevelLetterCocycles.JInvJumpGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle700
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTwCoef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise Formalism.UG

namespace GlobalTheory.DefiniteDense

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infPt (y : UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) : UA E n :=
  ⟨infGL E n y.1, infGL_mem_UA y.1 (by
    have h : cT (starRingEnd (Cinf E)) (y.1 : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * y.1 = 1 := y.2
    rw [mul_one] at h
    exact h)⟩

theorem continuous_infPt : Continuous (infPt (E := E) (n := n)) :=
  (GlobalTheory.DefU.continuous_infGL.comp continuous_subtype_val).subtype_mk _

theorem mem_closure_rat_fin (x : UA E n) (hx : x ∈ infU E n) :
    x ∈ closure ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
  have hne : ∃ z, (IsCMField.complexConj E : E →+* E) z ≠ z := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hd := GlobalTheory.RealApprox.dense_unitary (GlobalTheory.CuspRep.InfType.diagInf E) (IsCMField.complexConj E : E →+* E)
    (starRingEnd (Cinf E)) (fun z => (pInf_complexConj z).symm) (fun z => IsCMField.complexConj_apply_apply E z) hne
    (fun z => star_star z) continuous_star GlobalTheory.CuspRep.InfType.denseRange_diagInf Units.isOpen
    (fun z hz => by obtain ⟨u, rfl⟩ := hz; exact NormedRing.inverse_continuousAt u)
    (1 : Matrix (Fin n) (Fin n) E)
    (by rw [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]) (by simp)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at hd
  have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) := fun a => (infEq E).symm_apply_apply _
  have hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
    have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
    rw [mul_one] at h0
    have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
        (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
      ext i j
      simp [Formalism.UG.cT, hp]
    change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
      (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
    rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hxe : infPt ⟨_, hM⟩ = x := by
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans hx.symm
  rw [← hxe]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPt ⟨_, hd ⟨_, hM⟩, rfl⟩)
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 hh
  have hγ0 : cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * γ = 1 := hγ
  rw [mul_one] at hγ0
  have hr : ratGL E n γ ∈ UA E n := by
    have e : cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
        (cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
      ext i j
      simp [Formalism.UG.cT, conjAd_algebraMap]
    change cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * 1 *
      (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1
    rw [e, mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]
  let r : UA E n := ⟨ratGL E n γ, hr⟩
  have hrU : r ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩
  have hk : r⁻¹ * infPt h ∈ finU (E := E) (n := n) := by
    have e1 : GeneralLinearGroup.map (pInf E) (ratGL E n γ) = h.1 := by
      rw [← hγh]
      exact Units.ext rfl
    change GeneralLinearGroup.map (pInf E) ((ratGL E n γ)⁻¹ * infGL E n h.1) = 1
    rw [map_mul, map_inv, e1, pInf_infGL, inv_mul_cancel]
  exact ⟨r, hrU, r⁻¹ * infPt h, hk, mul_inv_cancel_left r _⟩

theorem eq_zero_of_finU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ),
    IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  intro L _ _ _ n φ hφ h0
  have hS : ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) ⊆ {g | φ g = 0} := by
    rintro _ ⟨γ, hγ, k, hk, rfl⟩
    change φ (γ * k) = 0
    rw [hφ.left γ hγ k]
    exact h0 k hk
  have hZ : IsClosed {g : UA L n | φ g = 0} := isClosed_eq hφ.cont continuous_const
  funext g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU L n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA L n → UA L n) := continuous_mul_const k
  have hxk : x * k ∈ closure ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) := by
    refine closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, mem_closure_rat_fin x hx, rfl⟩)
    rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
    exact ⟨γ, hγ, k' * k, (finU (E := L) (n := n)).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩
  exact hZ.closure_subset_iff.2 hS hxk

end GlobalTheory.DefiniteDense
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.UnitaryDual GlobalTheory.GenericUnitary

namespace GlobalTheory.GenericUnitaryBridge

theorem eq_of_isSpeh_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ w : IrrGL (k := k)} (h : IsSpeh δ 1 w.rep) : w = δ := by
  obtain ⟨n, c⟩ := w
  obtain ⟨n', c'⟩ := δ
  obtain ⟨hd1, hc1⟩ := h
  obtain ⟨hd2, hc2⟩ := isSpeh_one (⟨n', c'⟩ : IrrGL (k := k))
  obtain rfl : n = n' := hd1.symm.trans hd2
  obtain ⟨φ⟩ := hc2.unique hc1
  exact ((IrrGL.of_rep _).symm.trans (IrrGL.of_eq_of.2 ⟨φ⟩)).trans (IrrGL.of_rep _)

theorem of_lemmas (hA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) (hB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π) (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep) (hF : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ))) :
    GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL →
      GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  intro hU hSq hGen hLM hSC k _ _ _ _ _ N V _ _ π hs hi hu hg
  have ord := GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes k
  let Good : Segment k → Prop := fun Δ => ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)
  have key : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → ∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (w.nu (r : ℂ)).rep ∧
      (∀ Γ ∈ 𝔫, Good Γ) ∧ (IsUnitaryLSeg w ∨ ∃ (Γ : Segment k) (t : ℝ), Γ.nu (t : ℂ) ∈ 𝔫 ∧
        Γ.nu ((t - 1 : ℝ) : ℂ) ∈ 𝔫) := by
    rintro w r ⟨δ, m, hsq, hm, hsp⟩
    obtain ⟨Δ, hΔ⟩ := hSq k δ hsq
    refine ⟨_, hD k ord δ w Δ m hΔ hsq.2.1 hsp r, ?_, ?_⟩
    · intro Γ hΓ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hΓ)
      exact ⟨δ, Δ, _, hΔ, hsq.2.1, rfl⟩
    · rcases Nat.lt_or_ge m 2 with h2 | h2
      · left
        obtain rfl : m = 1 := by omega
        obtain rfl := eq_of_isSpeh_one hsp
        exact ⟨⟨Δ, hΔ⟩, hsq.2.1⟩
      · right
        refine ⟨Δ, r + ((m : ℝ) - 1) / 2, Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩),
          Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨1, by omega⟩, ?_⟩)⟩
        · simp
        · congr 2
          push_cast
          ring
  obtain ⟨u, τ, hu1, hτ1, h, x, hd, hx, ⟨φ⟩⟩ := hU k N V π hs hi hu
  have hfac : ∀ j, ∃ (y : IrrGL (k := k)) (s : ℝ), IsUnitarySpeh y ∧ x j = y.nu (s : ℂ) := by
    intro j
    have hm : x j ∈ factors u τ := hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact ⟨x j, 0, hu1 _ hm, by simp⟩
    · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.1 hm
      rcases List.mem_pair.1 hm with e | e
      · exact ⟨p.1, p.2, (hτ1 p hp).1, e⟩
      · exact ⟨p.1, -p.2, (hτ1 p hp).1, e⟩
  choose y s hy hxs using hfac
  have h𝔪 : ∀ j, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (x j).rep ∧ ∀ Γ ∈ 𝔪, Good Γ := fun j => by
    obtain ⟨𝔪, h1, h2, -⟩ := key (y j) (s j) (hy j)
    exact ⟨𝔪, hxs j ▸ h1, h2⟩
  choose 𝔪 h𝔪L h𝔪G using h𝔪
  have hL : IsL (∑ j, 𝔪 j) π :=
    hB k hLM Good (fun 𝔫 h𝔫 => hA k hSC ord 𝔫 h𝔫) h N x hd 𝔪 h𝔪L h𝔪G V π hi ⟨φ⟩
  obtain ⟨h', Δ', z, hd', hunl, hz, ⟨ψ⟩⟩ := hGen k N V π hs hi hg
  have hL' : IsL (Finset.univ.val.map Δ') π :=
    ⟨h', z, hd', ⟨Δ', ⟨rfl, fun i j hij hP => hunl i j hij.ne hP.1⟩, hz⟩,
      (isCosocle_self hi).of_equiv (.refl _) ψ⟩
  have heq : ∑ j, 𝔪 j = Finset.univ.val.map Δ' :=
    (hLM k).1 _ _ (IrrGL.of π hs hi) (hL.of_equiv (IrrGL.equivOf π hs hi)) (hL'.of_equiv (IrrGL.equivOf π hs hi))
  have hno : ∀ Γ ∈ ∑ j, 𝔪 j, ∀ Γ' ∈ ∑ j, 𝔪 j, ¬ Γ.Linked Γ' := by
    rw [heq]
    intro Γ hΓ Γ' hΓ' hl
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΓ
    obtain ⟨i', -, rfl⟩ := Multiset.mem_map.1 hΓ'
    by_cases e : i = i'
    · subst e
      exact Segment.not_linked_self _ hl
    · exact hunl i i' e hl
  have hgood : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → w.nu (r : ℂ) ∈ List.ofFn x → IsUnitaryLSeg w := by
    intro w r hw hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hmem
    obtain ⟨𝔫, h1, -, h3⟩ := key w r hw
    rcases h3 with h3 | ⟨Γ, t, h4, h5⟩
    · exact h3
    · have e : 𝔫 = 𝔪 j := (hLM k).1 _ _ (x j) (hj ▸ h1) (h𝔪L j)
      subst e
      exact absurd (hF k Γ t) (hno _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h4⟩) _
        (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h5⟩))
  refine ⟨u, τ, fun w hw => hgood w 0 (hu1 w hw) ?_, fun p hp => ⟨hgood p.1 p.2 (hτ1 p hp).1 ?_, (hτ1 p hp).2⟩,
    h, x, hd, hx, ⟨φ⟩⟩
  · rw [hx]
    simp only [Complex.ofReal_zero, IrrGL.nu_zero]
    exact List.mem_append_left _ hw
  · rw [hx]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩)

theorem genericUnitaryDualGL_of_hypotheses : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment →
    GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL →
    GlobalTheory.Published.GenericUnitaryDualGL :=
  of_lemmas GlobalTheory.T.langlands_classification_unitary GlobalTheory.T.standard_module_properties GlobalTheory.T.speh_langlands_quotient GlobalTheory.T.segment_linked_shift

end GlobalTheory.GenericUnitaryBridge
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical



theorem GlobalTheory.exists_letter_vector_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  intro l _ P AI hT K LL x hx c hc μ τ₀' τ' j hμ hτ d hd hd1
  have := (P.PD K).finK₀
  obtain ⟨m, cc, kk, h1, hsum⟩ := GlobalTheory.exists_embedding_idempotent_tensor ℚ_[l] ↥(K0 K) ↥LL.1 τ'
  set y := (⇑P.φB)^[j] x with hy
  set z := P.ιB y with hzdef
  clear_value z y
  let f : ↥(K0 K) →ₗ[ℚ_[l]] P.R.B := (LinearMap.mulRight ℚ_[l] y) ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hB : ∀ s : ↥(K0 K), ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) = ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by
    intro s
    have := congrArg (LinearMap.lTensor ↥LL.1 f) (hsum s)

    simpa [f, map_sum, LinearMap.lTensor_tmul] using this
  have hφK : ∀ k : ↥(K0 K), P.φB (algebraMap ↥(K0 K) P.R.B k) = algebraMap ↥(K0 K) P.R.B ((P.PD K).σ k) := by
    intro k; rw [← P.PD_φ K]; exact (P.PD K).φ_K₀ k
  have hact : ∀ g : ↥(GK K), ∀ n : ℕ, P.actQ (g : GQ l) ((⇑P.φB)^[n] x) = algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[n] (c g : ↥(K0 K))) * (⇑P.φB)^[n] x := by
    intro g n
    have hcomm : ∀ b, P.actQ (g : GQ l) (P.φB b) = P.φB (P.actQ (g : GQ l) b) := by
      intro b
      have := (P.PD K).φ_comm g b
      rw [P.PD_φ, P.PD_φ, P.PD_actB, P.PD_actB] at this
      exact this.symm
    induction n with
    | zero => simpa using hc g
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [hcomm, ih, map_mul, hφK]
  have hterm : ∀ (g : ↥(GK K)) (a : ↥LL.1) (k : ↥(K0 K)),
      actVB (P.PD K) (charRep μ) g (a ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B k * y)) =
        (((μ g : (↥LL.1)ˣ) : ↥LL.1) * a) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[j] (c g : ↥(K0 K)) * k) * y) := by
    intro g a k
    simp only [actVB, AlgebraTensorModule.map_tmul]
    congr 1
    change (P.PD K).actB g (algebraMap ↥(K0 K) P.R.B k * y) = _
    rw [map_mul, AlgEquiv.commutes, P.PD_actB, hy, hact g j, map_mul]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ↥LL.1 ⊗[ℚ_[l]] P.R.B, w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := ⟨_, rfl⟩
  have hinv : ∀ g : ↥(GK K), actVB (P.PD K) (charRep μ) g w = w := by
    intro g
    set s := (⇑(P.PD K).σ)^[j] (c g : ↥(K0 K))

    simp only [hw, map_sum, hterm]
    calc ∑ i, (((μ g : (↥LL.1)ˣ) : ↥LL.1) * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y)
        = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) := by
          rw [Finset.smul_sum]; simp only [TensorProduct.smul_tmul', smul_eq_mul]
      _ = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by rw [hB]
      _ = _ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← mul_assoc, hτ, hμ, one_mul]

  have hlet : ∀ a : ↥(K0 K), mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := ↥LL.1) (LL := ↥LL.1) a w = τ' a • w := by
    intro a

    simp only [hw, map_sum, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    have : ∀ i, algebraMap ↥(K0 K) P.R.B a * (algebraMap ↥(K0 K) P.R.B (kk i) * y) = algebraMap ↥(K0 K) P.R.B (a * kk i) * y := by
      intro i; rw [map_mul, mul_assoc]
    simp only [this]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hι : ∀ k : ↥(K0 K), (P.PD K).ι (algebraMap ↥(K0 K) P.R.B k * y) = algebraMap ↥(K0 K) P.R.BdR k * z := by
    intro k; rw [map_mul, AlgHom.commutes, P.PD_ι, ← hzdef]
  have hιw : ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.BdR (kk i) * z) := by

    simp only [hw, map_sum, ιV, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact hι (kk i)
  have hmem : ∀ k : ↥(K0 K), algebraMap ↥(K0 K) P.R.BdR k * z ∈ (P.PD K).Fil d := by
    intro k
    rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, ← Algebra.smul_def]
    exact (P.PD K).Fil d |>.smul_mem _ hd
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Dcris
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hinv g, LinearMap.id_apply, sub_self]
  · refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hlet a, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
  · rw [hιw]
    refine ⟨∑ i, cc i ⊗ₜ[ℚ_[l]] (⟨algebraMap ↥(K0 K) P.R.BdR (kk i) * z, hmem (kk i)⟩ : ↥(((P.PD K).Fil d).restrictScalars ℚ_[l])), ?_⟩

    simp [map_sum, AlgebraTensorModule.map_tmul]
  · intro hcon
    have hyu : ∀ n : ℕ, IsUnit ((⇑P.φB)^[n] x) := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.map P.φB
    have hz : IsUnit z := by rw [hzdef, hy]; exact (hyu j).map P.ιB
    obtain ⟨v, hzv⟩ := hz.exists_right_inv
    have hvz : v * z = 1 := by rw [mul_comm]; exact hzv
    have hv : v ∈ (P.PD K).Fil (-d) := GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d z v hzv hd hd1
    let Mv : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] P.R.BdR :=
      AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) (LinearMap.mulLeft ℚ_[l] v)
    have hvmul : ∀ b ∈ ((P.PD K).Fil (d + 1)).restrictScalars ℚ_[l], LinearMap.mulLeft ℚ_[l] v b ∈ ((P.PD K).Fil 1).restrictScalars ℚ_[l] := by
      intro b hb
      have := (P.PD K).Fil_mul (-d) (d + 1) v b hv hb
      rw [show -d + (d + 1) = 1 by ring] at this
      exact this
    have hMv : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1), Mv t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1 := by
      rintro t ⟨s, rfl⟩
      refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) ((LinearMap.mulLeft ℚ_[l] v).restrict hvmul) s, ?_⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Mv, AlgebraTensorModule.map_tmul]
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have hE : Mv (ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w) = ∑ i, cc i ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.BdR (kk i) := by

      rw [hιw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Mv, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [mul_left_comm, hvz, mul_one]
    have hF1 := hMv _ hcon
    rw [hE] at hF1
    let q := (((P.PD K).Fil 1).restrictScalars ℚ_[l]).mkQ
    let h0 : ↥(K0 K) →ₗ[ℚ_[l]] P.R.BdR ⧸ (((P.PD K).Fil 1).restrictScalars ℚ_[l]) :=
      q ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.BdR).toLinearMap
    have hinj : Function.Injective h0 := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro k hk
      have hk' : algebraMap ↥(K0 K) P.R.BdR k ∈ (P.PD K).Fil 1 := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hk
        exact this
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR] at hk'
      have := JsetEmb.field_inter_filtration_one_eq_zero (P.PD K) _ hk'
      exact (map_eq_zero_iff _ (algebraMap ↥(K0 K) ↥K.1).injective).1 this
    have hq : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1, LinearMap.lTensor ↥LL.1 q t = 0 := by
      rintro t ⟨s, rfl⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
        rw [show q ((((P.PD K).Fil 1).restrictScalars ℚ_[l]).subtype b) = 0 from (Submodule.Quotient.mk_eq_zero _).2 b.2, tmul_zero]
      | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht, add_zero]
    have hzero : LinearMap.lTensor ↥LL.1 h0 (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 0 := by
      have := hq _ hF1

      simpa [h0, map_sum, LinearMap.lTensor_tmul] using this
    have he : (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) h0 hinj (hzero.trans (map_zero _).symm)
    let Λ : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] ↥LL.1 := TensorProduct.lift ((LinearMap.mul ℚ_[l] ↥LL.1).compl₂ τ'.toLinearMap)
    have hΛ : Λ (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 1 := by

      simp [Λ, map_sum, h1]
    rw [he, map_zero] at hΛ
    exact zero_ne_one hΛ
end

section

namespace GlobalTheory.TopSteps.CharVanish
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem cls_eq_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (hC : S.CrysCalc) (hR : S.Real)
    (c : ℕ) (h2 : 2 ≤ c) (ht : c ≤ S.D.t) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] :
    S.cls (S.Γ.Wchi c) X = {0} := by
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hL : S.Lem0 (S.Γ.Wchi c) :=
    (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl (GlobalTheory.TopSteps.StdAdm.stdAdm S hC hcl)).2 c (by omega) ht
  exact GlobalTheory.TopSteps.CharAllCoef.main S c hL
    ((GlobalTheory.TopSteps.CharBound.resBound_chars S hR).1 c h2 ht hL) X

theorem stmt_of_real : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → (∀ S : TopSit P, S.Real) → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P := by
  intro l _ P AI hT hR K LL n r emb D Γ hyp c h2 ht X _ _ _
  have : NeZero n := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hyp.1⟩
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, hyp⟩
  exact cls_eq_zero S (GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S) (hR S) c h2 ht X

end GlobalTheory.TopSteps.CharVanish
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  first | exact @GlobalTheory.FilInv.inv_mem_Fil_neg | exact GlobalTheory.FilInv.inv_mem_Fil_neg | (intros; apply GlobalTheory.FilInv.inv_mem_Fil_neg <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | exact GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | (intros; apply GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.unramified_trivial_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  first | exact @GlobalTheory.UnramifiedTrivial.unrTriv | exact GlobalTheory.UnramifiedTrivial.unrTriv | (intros; apply GlobalTheory.UnramifiedTrivial.unrTriv <;> assumption)
end
