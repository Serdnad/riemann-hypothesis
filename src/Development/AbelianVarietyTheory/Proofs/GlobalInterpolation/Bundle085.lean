module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle078
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem apply_smul (x : HomE E a b) (s : 𝓞 E) (y : Sp E a) : x (s • y) = s • x y := x.map_smul_of_tower s y

theorem exists_common (S : Submonoid (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG) (N' : Submodule (𝓞 E) (Sp E b))
    (x : HomE E a b) (h : ∀ y ∈ N, ∃ s ∈ S, s • x y ∈ N') : ∃ s ∈ S, s • x ∈ homO N N' := by
  classical
  obtain ⟨T, hT⟩ := hN
  have hgen : ∀ y ∈ T, ∃ s ∈ S, s • x y ∈ N' := fun y hy =>
    h y (hT ▸ Submodule.subset_span (Finset.mem_coe.mpr hy))
  choose! f hfS hf using hgen
  refine ⟨∏ y ∈ T, f y, prod_mem fun y hy => hfS y hy, ?_⟩
  intro y hy
  rw [← hT] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [LinearMap.smul_apply, ← Finset.mul_prod_erase T f (Finset.mem_coe.mp hy), mul_comm, mul_smul]
    exact N'.smul_mem _ (hf y (Finset.mem_coe.mp hy))
  | zero => rw [map_zero]; exact N'.zero_mem
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact N'.add_mem hy hz
  | smul r y _ hy => rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact N'.smul_mem r hy

theorem smul_mem_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {r : E} (hr : r ∈ AA) {x : HomE E a b} (hx : x ∈ homO N N') : r • x ∈ perO AA N N' :=
  Submodule.subset_span ⟨r, hr, x, hx, rfl⟩

theorem mono (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a))
    (N₁' N₂' : Submodule (𝓞 E) (Sp E b)) (hN : N₂.FG) (h : localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁)
    (h' : localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂') :
    localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
  have hgen : perO AA N₁ N₁' ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, x, hx, rfl⟩
    have hmult : ∀ y ∈ N₂, ∃ s ∈ Q.asIdeal.primeCompl, s • x y ∈ N₂' := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := h (mem_localization_of_mem Q hy)
      have hxy : x (u • y) ∈ N₁' := hx _ huy
      rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul] at hxy
      obtain ⟨v, hv, hvxy⟩ := h' (mem_localization_of_mem Q hxy)
      exact ⟨v * u, mul_mem hv hu, by rw [mul_smul]; exact hvxy⟩
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common Q.asIdeal.primeCompl hN N₂' x hmult
    exact ⟨t, ht, by rw [smul_comm]; exact GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hr htx⟩
  calc localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (localization₂ Q.asIdeal (perO AA N₂ N₂')) :=
        localization_mono Q hgen
    _ = localization₂ Q.asIdeal (perO AA N₂ N₂') := localization_localization₂ Q _

theorem eq_homAt (AA : Submodule (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    localization₂ P.asIdeal (perO AA N N') = homAt {P} N N' := by
  apply le_antisymm
  · have hgen : perO AA N N' ≤ homAt {P} N N' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, x, hx, rfl⟩
      intro P' hP' y hy
      rw [Finset.mem_singleton] at hP'
      subst hP'
      obtain ⟨u, hu, huy⟩ := hy
      have hr1 : r ∈ localization₂ P'.asIdeal (1 : Submodule (𝓞 E) E) := by
        rw [← hA]; exact mem_localization_of_mem P' hr
      obtain ⟨v, hv, hvr⟩ := hr1
      obtain ⟨w, hw⟩ := Submodule.mem_one.mp hvr
      have hxy : u • x y ∈ N' := by
        rw [← GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact hx _ huy
      refine ⟨v * u, mul_mem hv hu, ?_⟩
      rw [LinearMap.smul_apply, mul_smul, smul_comm u r, ← smul_assoc v r, ← hw, algebraMap_smul]
      exact N'.smul_mem w hxy
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hz
    have h1 := hgen hsz
    intro P' hP' y hy
    obtain ⟨t, ht, hty⟩ := h1 P' hP' y hy
    rw [Finset.mem_singleton] at hP'
    subst hP'
    refine ⟨t * s, mul_mem ht hs, ?_⟩
    rw [mul_smul, ← LinearMap.smul_apply]
    exact hty
  · intro x hx
    have h1 : (1 : E) ∈ localization₂ P.asIdeal AA := by
      rw [hA]; exact mem_localization_of_mem P (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    obtain ⟨v, hv, hv1⟩ := h1
    have hmult : ∀ y ∈ N, ∃ s ∈ P.asIdeal.primeCompl, s • x y ∈ N' := fun y hy =>
      hx P (Finset.mem_singleton_self P) y (mem_localization_of_mem P hy)
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common P.asIdeal.primeCompl hN N' x hmult
    refine ⟨v * t, mul_mem hv ht, ?_⟩
    have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hv1 htx
    rwa [smul_one_smul, ← mul_smul] at h2

private theorem exists_nsmul_mem_of_isLattice (N' : Submodule (𝓞 E) (Sp E b)) (hN' : Submodule.IsFullLattice E N') (v : Sp E b) :
    ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ N' := by
  have hv : v ∈ Submodule.span E (N' : Set (Sp E b)) := by
    let _ : Submodule.IsFullLattice E N' := hN'
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := N')]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact hw⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact N'.zero_mem⟩
  | add v w _ _ hv hw =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem _ hmv
    · rw [mul_smul]; exact N'.smul_mem _ hkw
  | smul c v _ hv =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
    have h1 : IsIntegral ℤ ((y : E) * c) := by
      simpa [zsmul_eq_mul] using hyint c (Finset.mem_singleton_self c)
    have hint : IsIntegral ℤ ((y.natAbs : E) * c) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h] at h1; simpa using h1
      · rw [h] at h1; simpa using h1.neg
    refine ⟨y.natAbs * m, Nat.mul_pos (Int.natAbs_pos.mpr hy0) hm, ?_⟩
    have key : ((y.natAbs * m : ℕ) : 𝓞 E) • (c • v) =
        (⟨(y.natAbs : E) * c, hint⟩ : 𝓞 E) • ((m : 𝓞 E) • v) := by
      ext i
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, map_natCast]
      push_cast
      have hα : ∀ z : ↥(integralClosure ℤ E), algebraMap (↥(integralClosure ℤ E)) E z = (z : E) :=
        fun _ => rfl
      simp only [hα]
      ring
    rw [key]
    exact N'.smul_mem _ hmv

theorem full (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hN' : Submodule.IsFullLattice E N') (hA : AA ≠ ⊥) : Full (perO AA N N') := by
  obtain ⟨r, hrA, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro x
  let S : Submonoid (𝓞 E) :=
    { carrier := {s | ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) = s}
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨k, hk, rfl⟩
        exact ⟨m * k, Nat.mul_pos hm hk, by push_cast; rfl⟩
      one_mem' := ⟨1, one_pos, Nat.cast_one⟩ }
  have hmult : ∀ y ∈ N, ∃ s ∈ S, s • (r⁻¹ • x) y ∈ N' := fun y _ => by
    obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_isLattice N' hN' ((r⁻¹ • x) y)
    exact ⟨n, ⟨n, hn, rfl⟩, h⟩
  obtain ⟨s, hsS, hs⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common S hN N' (r⁻¹ • x) hmult
  obtain ⟨n, hn, rfl⟩ := hsS
  refine ⟨n, hn, ?_⟩
  have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hrA hs
  rwa [smul_comm r, smul_inv_smul₀ hr0] at h2

theorem perO_components : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E), (∀ (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), N₂.FG → localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁ → localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂' → localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂')) ∧ (∀ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) → localization₂ P.asIdeal (perO AA N N') = homAt {P} N N') ∧ ∀ (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → Submodule.IsFullLattice E N' → AA ≠ ⊥ → Full (perO AA N N') := by
  intro E _ _ _ a b AA
  exact ⟨fun Q N₁ N₂ N₁' N₂' hN h h' => GlobalTheory.ThetaMove.PeriodComp.mono AA Q N₁ N₂ N₁' N₂' hN h h',
    fun P N N' hN hA => GlobalTheory.ThetaMove.PeriodComp.eq_homAt AA P N N' hN hA,
    fun N N' hN hN' hA => GlobalTheory.ThetaMove.PeriodComp.full AA N N' hN hN' hA⟩

end GlobalTheory.ThetaMove.PeriodComp
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Step

open GlobalTheory.ThetaInter

section Transversal

variable {G : Type*} [AddCommGroup G]

def IsTransv {I : Type*} (A B : AddSubgroup G) (r : I → G) : Prop :=
  (∀ i, r i ∈ A) ∧ (∀ i j, r i - r j ∈ B → i = j) ∧ ∀ a ∈ A, ∃ i, a - r i ∈ B

theorem IsTransv.finsum_eq {I J M : Type*} [AddCommMonoid M] {A B : AddSubgroup G} {r : I → G} {r' : J → G}
    (h : IsTransv A B r) (h' : IsTransv A B r') (F : G → M) (hF : ∀ a ∈ A, ∀ a' ∈ A, a - a' ∈ B → F a = F a') :
    ∑ᶠ i, F (r i) = ∑ᶠ j, F (r' j) := by
  choose e he using fun i => h'.2.2 (r i) (h.1 i)
  refine finsum_eq_of_bijective e ⟨fun i j hij => h.2.1 i j ?_, fun j => ?_⟩ fun i => hF _ (h.1 i) _ (h'.1 _) (he i)
  · have := B.sub_mem (he i) (he j)
    rwa [hij, sub_sub_sub_cancel_right] at this
  · obtain ⟨i, hi⟩ := h.2.2 (r' j) (h'.1 j)
    refine ⟨i, (h'.2.1 _ _ ?_).symm⟩
    have := B.add_mem hi (he i)
    rwa [sub_add_sub_cancel] at this

theorem IsTransv.finite {I : Type*} {A B : AddSubgroup G} {r : I → G} (h : IsTransv A B r) (hf : B.relIndex A ≠ 0) :
    Finite I := by
  have : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hf
  refine Finite.of_injective (fun i => ((⟨r i, h.1 i⟩ : A) : A ⧸ B.addSubgroupOf A)) fun i j hij => h.2.1 i j ?_
  have := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hij.symm)
  simpa [neg_add_eq_sub] using this

theorem isTransv_out (A B : AddSubgroup G) :
    IsTransv A B fun c : A ⧸ B.addSubgroupOf A => ((Quotient.out c : A) : G) := by
  refine ⟨fun c => (Quotient.out c).2, fun c c' h => ?_, fun a ha => ⟨((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A), ?_⟩⟩
  · rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  · have := AddSubgroup.mem_addSubgroupOf.1
      (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A)))
    simpa [neg_add_eq_sub] using this

theorem isTransv_surjInv {R : Type*} [Ring R] [Module R G] (A B : Submodule R G) :
    IsTransv A.toAddSubgroup B.toAddSubgroup fun z : ↥A ⧸ B.comap A.subtype =>
      ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : G) := by
  have hs := Function.surjInv_eq (Submodule.Quotient.mk_surjective (B.comap A.subtype))
  refine ⟨fun c => Subtype.prop _, fun c c' h => ?_, fun a ha => ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩⟩
  · rw [← hs c, ← hs c', Submodule.Quotient.eq]
    exact h
  · exact (Submodule.Quotient.eq (B.comap A.subtype)).1 (hs (Submodule.Quotient.mk ⟨a, ha⟩)).symm

end Transversal

section Heis

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ}

theorem alpha_neg (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : α (-x) = α x := by
  have h0 : α 0 = 1 := by
    have h := hs.2 0 A.zero_mem 0 A.zero_mem
    rw [alpha_sq hs A.zero_mem] at h
    simpa [altE] using h
  have h1 : altE H x (-x) = 0 := by
    have := altE_swap hH x x
    simp only [altE, map_neg, Complex.neg_im] at this ⊢
    linarith
  have h := hs.2 x hx (-x) (A.neg_mem hx)
  rw [add_neg_cancel, h0, h1] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  linear_combination α (-x) * alpha_sq hs hx * (-1) - α x * h

theorem alpha_opU_congr (hH : IsHerm H) {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α B) {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x - y ∈ B) (z : V) :
    α x * opU H x F z = α y * opU H y F z := by
  have h := alpha_opU_add hH hd hs hy (A.sub_mem hx hy) F z
  rw [add_sub_cancel, ← opU_mul y (α (x - y))] at h
  rw [h]
  congr 2
  funext w
  exact hF _ hxy w

end Heis

theorem cosSum_inter (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W] (V : Type)
    [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L₁ L₂ : Submodule (𝓞 E) W) (θ : V → ℂ)
    (Ξ : W → ℂ) (hH : IsHerm H) (hι : Function.Injective ι) (hdA : IsSelfDual H (As.toAddSubgroup.map ι))
    (hsA : IsSemiChar H (As.toAddSubgroup.map ι) α) (hd₁ : IsSelfDual H (L₁.toAddSubgroup.map ι))
    (hs₁ : IsSemiChar H (L₁.toAddSubgroup.map ι) α) (hθ : θ ∈ fixedBy H α (L₂.toAddSubgroup.map ι))
    (h21 : L₂ ⊓ As ≤ L₁) (h1 : L₁ ≤ (L₁ ⊓ As) ⊔ (L₁ ⊓ L₂))
    (hfin : L₂.toAddSubgroup.relIndex As.toAddSubgroup ≠ 0)
    (hΞ : ∀ t ∈ As, ∀ y ∈ L₁ ⊓ As, Ξ (t + y) = Ξ t) (z : V) :
    cosSum H α ι As L₁ (inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ) Ξ z =
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ * cosSum H α ι As L₂ θ Ξ z := by
  classical
  obtain ⟨I, r, hr, hI⟩ : ∃ (I : Type) (r : I → W), IsTransv As.toAddSubgroup L₁.toAddSubgroup r ∧
      ∀ F : W → ℂ, latSum As L₁ F = ∑ᶠ i, F (r i) := ⟨_, _, isTransv_surjInv As L₁, fun _ => rfl⟩
  obtain ⟨J, y, hy⟩ : ∃ (J : Type) (y : J → W), IsTransv (L₁ ⊓ As).toAddSubgroup L₂.toAddSubgroup y :=
    ⟨_, _, isTransv_out _ _⟩
  have hy₁ : ∀ j, y j ∈ L₁ := fun j => (hy.1 j).1
  have hyA : ∀ j, y j ∈ As := fun j => (hy.1 j).2
  have hrA : ∀ i, r i ∈ As := hr.1
  have hp : IsTransv As.toAddSubgroup L₂.toAddSubgroup fun p : I × J => r p.1 - y p.2 := by
    refine ⟨fun p => As.sub_mem (hrA _) (hyA _), fun p q h => ?_, fun a ha => ?_⟩
    · have h2 : r p.1 - y p.2 - (r q.1 - y q.2) ∈ L₁ :=
        h21 ⟨h, As.sub_mem (As.sub_mem (hrA _) (hyA _)) (As.sub_mem (hrA _) (hyA _))⟩
      have h3 : p.1 = q.1 := hr.2.1 _ _ (by
        have := L₁.add_mem h2 (L₁.sub_mem (hy₁ p.2) (hy₁ q.2))
        have e : r p.1 - y p.2 - (r q.1 - y q.2) + (y p.2 - y q.2) = r p.1 - r q.1 := by abel
        rwa [e] at this)
      refine Prod.ext h3 (hy.2.1 _ _ ?_).symm
      have e : r p.1 - y p.2 - (r q.1 - y q.2) = y q.2 - y p.2 := by rw [h3]; abel
      rw [← e]
      exact h
    · obtain ⟨i, hi⟩ := hr.2.2 a ha
      obtain ⟨j, hj⟩ := hy.2.2 (-(a - r i)) ⟨L₁.neg_mem hi, As.neg_mem (As.sub_mem ha (hrA i))⟩
      refine ⟨(i, j), ?_⟩
      have := L₂.neg_mem hj
      have e : -(-(a - r i) - y j) = a - (r i - y j) := by abel
      rwa [e] at this
  have hq : IsTransv (L₁.toAddSubgroup.map ι) (L₂.toAddSubgroup.map ι) fun j => ι (y j) := by
    refine ⟨fun j => ⟨_, hy₁ j, rfl⟩, fun i j h => hy.2.1 i j ?_, ?_⟩
    · obtain ⟨s, hs, e⟩ := h
      rw [← map_sub] at e
      rw [← hι e]
      exact hs
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h1 ha)
      obtain ⟨j, hj⟩ := hy.2.2 u hu
      refine ⟨j, u - y j + v, L₂.add_mem hj hv.2, ?_⟩
      rw [← map_sub]
      congr 1
      abel
  have hfp := hp.finite hfin
  have : Nonempty I := let ⟨i, _⟩ := hr.2.2 0 As.zero_mem; ⟨i⟩
  have : Nonempty J := let ⟨i, _⟩ := hy.2.2 0 (L₁ ⊓ As).zero_mem; ⟨i⟩
  have : Finite I := Finite.prod_left J
  have : Finite J := Finite.prod_right I
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have mA : ∀ {t : W}, t ∈ As → ι t ∈ As.toAddSubgroup.map ι := fun ht => ⟨_, ht, rfl⟩
  have hint : inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ = fun w =>
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ j, α (ι (y j)) * opU H (ι (y j)) θ w := by
    funext w
    rw [inter, relIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hι,
      (isTransv_out _ _).finsum_eq hq (fun x => α x * opU H x θ w)
        fun a ha a' ha' h => alpha_opU_congr hH hd₁ hs₁ hθ ha ha' h w, finsum_eq_sum_of_fintype]
  have hR : cosSum H α ι As L₂ θ Ξ z =
      ∑ p : I × J, Ξ (r p.1 - y p.2) * (α (ι (r p.1 - y p.2)) * opU H (-(ι (r p.1 - y p.2))) θ z) := by
    rw [← finsum_eq_sum_of_fintype]
    refine (isTransv_surjInv As L₂).finsum_eq hp (fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)) fun a ha a' ha' h => ?_
    have h2 := hΞ a' ha' (a - a') ⟨h21 ⟨h, As.sub_mem ha ha'⟩, As.sub_mem ha ha'⟩
    rw [add_sub_cancel] at h2
    rw [h2, ← alpha_neg hH hsA (mA ha), ← alpha_neg hH hsA (mA ha'),
      alpha_opU_congr hH hdA hsA hθ (neg_mem (mA ha)) (neg_mem (mA ha'))]
    refine ⟨-(a - a'), L₂.neg_mem h, ?_⟩
    rw [map_neg, map_sub]
    abel
  rw [hR, hint, cosSum, hI, finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [opU_mul, opU_sum, mul_left_comm (α _), mul_left_comm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := hΞ (r i) (hrA i) (-y j) (neg_mem (hy.1 j))
  rw [← sub_eq_add_neg] at h2
  have e : -ι (r i - y j) = -ι (r i) + ι (y j) := by rw [map_sub]; abel
  rw [h2, ← alpha_neg hH hsA (mA (As.sub_mem (hrA i) (hyA j))), e,
    alpha_opU_add hH hdA hsA (neg_mem (mA (hrA i))) (mA (hyA j)), alpha_neg hH hsA (mA (hrA i)), opU_mul]

end GlobalTheory.ThetaMove.Step
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.boxSum_ne_zero_invariant_affineChange : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  first | exact @GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | exact GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | (intros; apply GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  first | exact @GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | exact GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | (intros; apply GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.LocCharVal

theorem isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : P.valuation E b = 1) : IsUnit (redP P b) := by
  have h1 : Formalism.L2.Col.IntAt P b := (GlobalTheory.CharVal.intAt_iff _).2 hb.le
  have h2 : Formalism.L2.Col.IntAt P b⁻¹ := (GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h3 := reduction_mul h1 h2
  rw [mul_inv_cancel₀ hb0] at h3
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem locChar_eq_zpow_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), P.valuation E (q : E) = WithZero.exp (-1 : ℤ) → a ≠ 0 → ∃ (z : ℤ) (ζ : Kˣ), IsOfFinOrder ζ ∧ LocE.locChar q cq χ a = cq ^ z * (ζ : K) := by
  intro E K _ _ _ P q cq χ a hq ha
  have hv : P.valuation E a ≠ 0 := by simpa using ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
    refine ⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩
    rw [map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  have hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := Classical.epsilon_spec hex
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left hu]

end GlobalTheory.LocCharVal
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  first | exact @GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | exact GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | (intros; apply GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.jetC_constr_aeval_monomial : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ), (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar ι a b →₀ ℕ, jetC cD (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) m = (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (MvPolynomial.aeval (fun k : DVar ι a b => ∑ i : Fin b, ∑ j : Fin a, (MvPolynomial.C (h k.1 i k.2.1 * g k.1 k.2.2 j) * MvPolynomial.X (k.1, i, j) : MvPolynomial (DVar ι a b) ℂ)) (MvPolynomial.monomial m (1 : ℂ))) := by
  first | exact @GlobalTheory.Glob.JetChainLin.jetC_comp_subst | exact GlobalTheory.Glob.JetChainLin.jetC_comp_subst | (intros; apply GlobalTheory.Glob.JetChainLin.jetC_comp_subst <;> assumption)
end

section

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.LocUnr

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_exp_neg_one (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (h1 : r ∈ P.asIdeal)
    (h2 : r ∉ P.asIdeal ^ 2) : P.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp (-1 : ℤ) := by
  have e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r := P.valuation_of_algebraMap r
  rw [e]
  have hr : r ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have a1 := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)
  have a2 := mt (P.intValuation_le_pow_iff_mem r 2).1 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero r hr)] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  push_cast at a1 a2
  omega

end GlobalTheory.LvT.LocUnr
end
