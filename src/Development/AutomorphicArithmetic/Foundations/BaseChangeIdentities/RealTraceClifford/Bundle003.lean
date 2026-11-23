module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem kspan_stb {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) :
    Stb F (Formalism.REAL.kSpan (fun _ => true) F x) := by
  intro a b y hy
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b rfl y (hy S hS)

private theorem proj_comm {n : ℕ} {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {F : Fin n → Fin n → Module.End ℂ N} (hF : UF F) (S : Submodule ℂ N) [S.HasOrthogonalProjection]
    (hS : Stb F S) (a b : Fin n) (y : N) :
    S.starProjection (F a b y) = F a b (S.starProjection y) := by
  have hz : F a b (y - S.starProjection y) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← hF.unit b a w]
    exact Submodule.inner_right_of_mem_orthogonal (hS b a w hw)
      (Submodule.sub_starProjection_mem_orthogonal y)
  refine Submodule.eq_starProjection_of_mem_orthogonal' (hS a b _ (S.starProjection_apply_mem y)) hz ?_
  rw [← map_add (f := _), add_sub_cancel]

theorem UpperTheory.RealTr.homSurj :
    ∀ (n : ℕ) (N V : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F : Fin n → Fin n → Module.End ℂ N) (K : Fin n → Fin n → Module.End ℂ V), UF F → UF K → LocF K → ∀ (ν : Wt n) (φ : hw F ν →ₗ[ℂ] hw K ν), ∃ t ∈ homL F K, (∀ x : hw F ν, t x = φ x) ∧ ∀ μ, μ ≠ ν → ∀ x ∈ hw F μ, t x = 0 := by
  intro n N V _ _ _ _ _ F K hF hK hL ν φ
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ => hF.unit a b
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp N n (fun _ => true) F ⊤ inferInstance hKR hKU
    (fun a b _ y _ => trivial)
  obtain ⟨P, hP⟩ : ∃ P : Fin m → N →L[ℂ] N,
      ∀ i, P i = (Formalism.REAL.kSpan (fun _ => true) F (x i)).starProjection := ⟨_, fun _ => rfl⟩
  have hPmem : ∀ i y, P i y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) := by
    intro i y
    rw [hP]
    exact Submodule.starProjection_apply_mem _ y
  have hPself : ∀ i y, y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → P i y = y := by
    intro i y hy
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.mpr hy
  have hPorth : ∀ i j y, j ≠ i → y ∈ Formalism.REAL.kSpan (fun _ => true) F (x j) → P i y = 0 := by
    intro i j y hji hy
    rw [hP]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (zero_mem _) (fun w hw => ?_)
    rw [sub_zero]
    exact horth j i hji y hy w hw
  have hcomm : ∀ i a b y, P i (F a b y) = F a b (P i y) := by
    intro i a b y
    rw [hP]
    exact proj_comm hF _ (kspan_stb F (x i)) a b y
  have hcomp : ∀ (μ' : Wt n) (y : N), KHighest (fun _ => true) F μ' y →
      ∀ i, KHighest (fun _ => true) F μ' (P i y) := by
    intro μ' y hy i
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hcomm, hy.1 a, map_smul]
    · rw [← hcomm, hy.2 a b hab he, map_zero]
  have huniq : ∀ (μ' : Wt n) (y : N) i, KHighest (fun _ => true) F μ' y →
      y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → y = 0 ∨ μ' = μ i ∧ ∃ c : ℂ, y = c • x i :=
    fun μ' y i hy hm => Formalism.REAL.kHiUniq N n _ F (μ i) μ' (x i) y hKR hKU (hx i).2.2 hm hy
  have hsum : ∀ y : N, y = ∑ i, P i y := by
    intro y
    have hy : y ∈ ⨆ i, Formalism.REAL.kSpan (fun _ => true) F (x i) := by
      rw [hsup]
      trivial
    refine Submodule.iSup_induction (motive := fun y => y = ∑ i, P i y) _ hy ?_ ?_ ?_
    · intro j z hz
      rw [Finset.sum_eq_single j (fun i _ hij => hPorth i j z (Ne.symm hij) hz)
        (fun h => absurd (Finset.mem_univ j) h), hPself j z hz]
    · simp
    · intro a b ha hb
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← ha, ← hb]
  have hg : ∀ i, ∃ g : N →ₗ[ℂ] V, (∀ a b (y : N), g (F a b y) = K a b (g y)) ∧
      (μ i = ν → ∀ h : x i ∈ hw F ν, g (x i) = (φ ⟨x i, h⟩ : V)) ∧ (μ i ≠ ν → g = 0) := by
    intro i
    by_cases h : μ i = ν
    · have hxi : x i ∈ hw F ν := by
        rw [← h]
        exact (hx i).2.2
      obtain ⟨S, hSf, hvS, hSstb⟩ := hL (φ ⟨x i, hxi⟩ : V)
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hHWMap n (fun _ => true) N V F K ν (x i)
        (φ ⟨x i, hxi⟩ : V) S (fun a b c d _ _ => hF.gl a b c d) (fun a b _ => hF.unit a b)
        (fun a b c d _ _ => hK.gl a b c d) (fun a b _ => hK.unit a b) (hx i).2.1 hxi
        (φ ⟨x i, hxi⟩).2 hSf (fun a b _ => hSstb a b) hvS
      exact ⟨g, fun a b y => hg2 a b rfl y, fun _ _ => hg1, fun hne => absurd h hne⟩
    · exact ⟨0, fun a b y => by simp, fun h' => absurd h' h, fun _ => rfl⟩
  choose g hgL hgv hg0 using hg
  have happ : ∀ y, (∑ i, (g i).comp (P i : N →ₗ[ℂ] N)) y = ∑ i, g i (P i y) := by
    intro y
    simp [LinearMap.sum_apply]
  refine ⟨∑ i, (g i).comp (P i : N →ₗ[ℂ] N), ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    show ∀ a b (y : N), (g i).comp (P i : N →ₗ[ℂ] N) (F a b y) = K a b ((g i).comp (P i : N →ₗ[ℂ] N) y)
    intro a b y
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hcomm i a b y]
    exact hgL i a b _
  · intro y
    have key : ∀ i, g i (P i y) = (φ ⟨P i y, hcomp ν y y.2 i⟩ : V) := by
      intro i
      rcases huniq ν (P i y) i (hcomp ν y y.2 i) (hPmem i y) with h0 | ⟨hμ, c, hc⟩
      · have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = 0 := Subtype.ext h0
        rw [e, map_zero, Submodule.coe_zero, h0, map_zero]
      · have hxi : x i ∈ hw F ν := by
          rw [hμ]
          exact (hx i).2.2
        have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = c • ⟨x i, hxi⟩ := Subtype.ext hc
        rw [e, map_smul, Submodule.coe_smul, hc, map_smul, hgv i hμ.symm hxi]
    have hs : (∑ i, (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν)) = y := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (hsum y).symm

    rw [happ, Finset.sum_congr rfl (fun i _ => key i), ← Submodule.coe_sum, ← map_sum, hs]
  · intro μ' hne y hy
    rw [happ]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : μ i = ν
    · rcases huniq μ' (P i y) i (hcomp μ' y hy i) (hPmem i y) with h0 | ⟨hμ, _⟩
      · rw [h0, map_zero]
      · exact absurd (hμ.trans h) hne
    · rw [hg0 i h, LinearMap.zero_apply]
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem kSpan_self (F : Fin n → Fin n → Module.End ℂ V) (y : V) :
    y ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf]
  exact fun S hS => hS.1

private theorem kSpan_stb (F : Fin n → Fin n → Module.End ℂ V) (y : V) (a b : Fin n) {z : V}
    (hz : z ∈ Formalism.REAL.kSpan (fun _ => true) F y) : F a b z ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hz ⊢
  exact fun S hS => hS.2 a b rfl z (hz S hS)

private theorem kSpan_le (F : Fin n → Fin n → Module.End ℂ V) {y : V} {Q : Submodule ℂ V}
    (hy : y ∈ Q) (hQ : Stb F Q) : Formalism.REAL.kSpan (fun _ => true) F y ≤ Q :=
  sInf_le ⟨hy, fun a b _ x hx => hQ a b x hx⟩

private theorem le_isoPart (F : Fin n → Fin n → Module.End ℂ V) {T : Set (Wt n)} {S : Submodule ℂ V}
    {y : V} {μ : Wt n} (hy : y ∈ S) (hμ : μ ∈ T) (h : KHighest (fun _ => true) F μ y) :
    Formalism.REAL.kSpan (fun _ => true) F y ≤ Formalism.REAL.isoPart (fun _ => true) F T S :=
  le_iSup₂_of_le (f := fun (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest (fun _ => true) F μ y) =>
    Formalism.REAL.kSpan (fun _ => true) F y) y ⟨hy, μ, hμ, h⟩ le_rfl

private theorem isoPart_map (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (f : Module.End ℂ V) (Q : Submodule ℂ V)
    (h : ∀ y, y ∈ S → ∀ μ ∈ T, KHighest (fun _ => true) F μ y →
      ∀ z ∈ Formalism.REAL.kSpan (fun _ => true) F y, f z ∈ Q) :
    ∀ z ∈ Formalism.REAL.isoPart (fun _ => true) F T S, f z ∈ Q := by
  have hle : Formalism.REAL.isoPart (fun _ => true) F T S ≤ Q.comap f := by
    unfold Formalism.REAL.isoPart
    refine iSup₂_le fun y hy => ?_
    obtain ⟨hyS, μ, hμ, hk⟩ := hy
    exact fun w hw => h y hyS μ hμ hk w hw
  exact fun z hz => hle hz

private theorem isoPart_stb (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V) :
    Stb F (Formalism.REAL.isoPart (fun _ => true) F T S) := fun a b =>
  isoPart_map F T S (F a b) _ fun y hy μ hμ hk z hz =>
    le_isoPart F hy hμ hk (kSpan_stb F y a b hz)

private theorem isoPart_cm (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (B : Module.End ℂ V) (hB : Cm F S B) :
    ∀ x ∈ Formalism.REAL.isoPart (fun _ => true) F T S, B x ∈ Formalism.REAL.isoPart (fun _ => true) F T S := by
  have hc : ∀ a b x, B (F a b x) = F a b (B x) := fun a b x => LinearMap.congr_fun (hB.1 a b) x
  refine isoPart_map F T S B _ fun y hy μ hμ hk z hz => ?_
  have hkB : KHighest (fun _ => true) F μ (B y) :=
    ⟨fun a => by rw [← hc, hk.1 a, map_smul], fun a b hab he => by rw [← hc, hk.2 a b hab he, map_zero]⟩
  have hle : Formalism.REAL.kSpan (fun _ => true) F y ≤ (Formalism.REAL.kSpan (fun _ => true) F (B y)).comap B :=
    kSpan_le F (kSpan_self F (B y)) fun a b x hx => by
      rw [Submodule.mem_comap, hc]
      exact kSpan_stb F (B y) a b hx
  exact le_isoPart F (hB.2 y hy) hμ hkB (hle hz)

private theorem parts_zero {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂) {u v : V} (hu : u ∈ S₁)
    (hv : v ∈ S₂) (h : u + v = 0) : u = 0 ∧ v = 0 := by
  have hv' : v = -u := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hv1 : v ∈ S₁ := hv' ▸ S₁.neg_mem hu
  have h0 : v = 0 := (Submodule.disjoint_def.mp hd) v hv1 hv
  refine ⟨?_, h0⟩
  rw [h0, add_zero] at h
  exact h

private theorem wt_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : IsWeight F μ (y₁ + y₂)) : IsWeight F μ y₁ ∧ IsWeight F μ y₂ := by
  have key : ∀ a, F a a y₁ = ↑(μ a) • y₁ ∧ F a a y₂ = ↑(μ a) • y₂ := by
    intro a
    have e := h a
    rw [map_add (f := _), smul_add] at e
    have hz := parts_zero hd (S₁.sub_mem (s1 a a y₁ h₁) (S₁.smul_mem _ h₁))
      (S₂.sub_mem (s2 a a y₂ h₂) (S₂.smul_mem _ h₂)) (by rw [sub_add_sub_comm, e, sub_self])
    exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩
  exact ⟨fun a => (key a).1, fun a => (key a).2⟩


private theorem hw_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : KHighest (fun _ => true) F μ (y₁ + y₂)) :
    KHighest (fun _ => true) F μ y₁ ∧ KHighest (fun _ => true) F μ y₂ := by
  obtain ⟨w1, w2⟩ := wt_comp F hd s1 s2 h₁ h₂ h.1
  refine ⟨⟨w1, fun a b hab e => ?_⟩, ⟨w2, fun a b hab e => ?_⟩⟩
  · have h0 := h.2 a b hab e
    rw [map_add (f := _)] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).1
  · have h0 := h.2 a b hab e
    rw [map_add (f := _)] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).2

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.isoSplit :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → S ≠ ⊥ → ∃ (ν : Wt n) (S₁ S₂ : Submodule ℂ V), S₁ ≠ ⊥ ∧ hw F ν ⊓ S₁ ≠ ⊥ ∧ S₁ ⊔ S₂ = S ∧ Disjoint S₁ S₂ ∧ Stb F S₁ ∧ Stb F S₂ ∧
      (∀ B, Cm F S B → Cm F S₁ B ∧ Cm F S₂ B) ∧ (∀ μ, μ ≠ ν → hw F μ ⊓ S₁ = ⊥) ∧
      ∀ μ, wsp F μ ⊓ S = (wsp F μ ⊓ S₁) ⊔ (wsp F μ ⊓ S₂) ∧ hw F μ ⊓ S = (hw F μ ⊓ S₁) ⊔ (hw F μ ⊓ S₂) := by
  intro n V _ _ F hF S hS hst hne
  have hK := Formalism.REAL.glRel_kRel (fun _ : Fin n => true) F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨x, hxS, hx0, ν, hxk⟩ := Formalism.REAL.kHiExist V n _ F S hS hK hU hSt hne
  obtain ⟨horth, hsup⟩ := Formalism.REAL.kIsoSplit V n _ F S {ν} hS hK hU hSt
  set S₁ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν} S with hS₁
  set S₂ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν}ᶜ S with hS₂
  have hd : Disjoint S₁ S₂ := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h0 := horth v h1 v h2
    rwa [inner_self_eq_zero] at h0
  have h1S : S₁ ≤ S := hsup ▸ le_sup_left
  have h2S : S₂ ≤ S := hsup ▸ le_sup_right
  have hst1 : Stb F S₁ := isoPart_stb F _ S
  have hst2 : Stb F S₂ := isoPart_stb F _ S
  have hx1 : x ∈ S₁ := le_isoPart (T := {ν}) F hxS (Set.mem_singleton ν) hxk (kSpan_self F x)
  refine ⟨ν, S₁, S₂, ?_, ?_, hsup, hd, hst1, hst2, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx1
    exact hx0 ((Submodule.mem_bot ℂ).mp hx1)
  · intro h
    have hm : x ∈ hw F ν ⊓ S₁ := Submodule.mem_inf.mpr ⟨hxk, hx1⟩
    rw [h] at hm
    exact hx0 ((Submodule.mem_bot ℂ).mp hm)
  · intro B hB
    exact ⟨⟨hB.1, isoPart_cm F _ S B hB⟩, ⟨hB.1, isoPart_cm F _ S B hB⟩⟩
  · intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyk, hy1⟩ := Submodule.mem_inf.mp hy
    have hy2 : y ∈ S₂ := le_isoPart (T := {ν}ᶜ) F (h1S hy1) (show μ ∈ ({ν}ᶜ : Set (Wt n)) from hμ) hyk (kSpan_self F y)
    exact (Submodule.mem_bot ℂ).mpr (Submodule.disjoint_def.mp hd y hy1 hy2)
  · intro μ
    constructor
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨w1, w2⟩ := wt_comp F hd hst1 hst2 h₁ h₂ hyw
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨w1, h₁⟩) (Submodule.mem_inf.mpr ⟨w2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyk, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨k1, k2⟩ := hw_comp F hd hst1 hst2 h₁ h₂ hyk
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨k1, h₁⟩) (Submodule.mem_inf.mpr ⟨k2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trace_restrict_sup_disjoint {V : Type} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (S S' : Submodule ℂ V) (hF : FiniteDimensional ℂ S) (hF' : FiniteDimensional ℂ S')
    (hd : Disjoint S S') (hS : ∀ x ∈ S, f x ∈ S) (hS' : ∀ x ∈ S', f x ∈ S')
    (hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S') :
    LinearMap.trace ℂ ↥(S ⊔ S') (f.restrict hT) =
      LinearMap.trace ℂ S (f.restrict hS) + LinearMap.trace ℂ S' (f.restrict hS') := by
  let φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S') :=
    ((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by
      simpa using Submodule.add_mem_sup p.1.2 p.2.2))
  have hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have h0 : (a : V) + (b : V) = 0 := by simpa [hφ] using congrArg Subtype.val h
    have ha : (a : V) ∈ S' := by
      have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact S'.neg_mem b.2
    have ha0 : (a : V) = 0 := (Submodule.disjoint_def.1 hd) _ a.2 ha
    have hb0 : (b : V) = 0 := by simpa [ha0] using h0
    ext <;> simp [ha0, hb0]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩
  let e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S') := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := fun p => hφ p
  have hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS')) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨p, rfl⟩ := e.surjective x
    have hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) =
        e ((f.restrict hS).prodMap (f.restrict hS') p) := by
      simp [LinearEquiv.conj_apply]
    rw [hc]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, he, he, map_add (f := _)]
    rfl
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem UpperTheory.RealTr.trAdd :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V),
      (∀ S S' : Submodule ℂ V, FiniteDimensional ℂ S → FiniteDimensional ℂ S' → Disjoint S S' → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S', f x ∈ S') →
        trOn (S ⊔ S') f = trOn S f + trOn S' f) ∧
      (∀ (S : Submodule ℂ V) (g : Module.End ℂ V) (c : ℂ), (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, g x ∈ S) →
        trOn S (f + g) = trOn S f + trOn S g ∧ trOn S (c • f) = c * trOn S f ∧ ((∀ x ∈ S, f x = g x) → trOn S f = trOn S g)) ∧
      (∀ (S S' : Submodule ℂ V) (g : Module.End ℂ V), FiniteDimensional ℂ S → FiniteDimensional ℂ S' → (∀ x ∈ S, f x ∈ S') → (∀ x ∈ S', g x ∈ S) →
        trOn S (g * f) = trOn S' (f * g)) ∧
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → trOn S (1 : Module.End ℂ V) = Module.finrank ℂ S := by
  intro V _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hF hF' hd hS hS'
    have hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S' := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hS a ha) (hS' b hb)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left hT, dite_eq_left hS, dite_eq_left hS']
    exact trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT
  · intro S g c hf hg
    have hfg : ∀ x ∈ S, (f + g) x ∈ S := fun x hx => S.add_mem (hf x hx) (hg x hx)
    have hcf : ∀ x ∈ S, (c • f) x ∈ S := fun x hx => S.smul_mem c (hf x hx)
    refine ⟨?_, ?_, ?_⟩
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hfg, dite_eq_left hf, dite_eq_left hg, ← map_add (f := _)]
      congr 1
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hcf, dite_eq_left hf]
      have : (c • f).restrict hcf = c • f.restrict hf := by ext x; simp
      rw [this, map_smul, smul_eq_mul]
    · intro he
      unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dite_eq_left hf, dite_eq_left hg]
      congr 1
      ext x
      simp [he x x.2]
  · intro S S' g hF hF' hf hg
    have h1 : ∀ x ∈ S, (g * f) x ∈ S := fun x hx => hg _ (hf x hx)
    have h2 : ∀ x ∈ S', (f * g) x ∈ S' := fun x hx => hf _ (hg x hx)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left h1, dite_eq_left h2]
    let a : S →ₗ[ℂ] S' := f.restrict hf
    let b : S' →ₗ[ℂ] S := g.restrict hg
    have e1 : (g * f).restrict h1 = b ∘ₗ a := by ext x; rfl
    have e2 : (f * g).restrict h2 = a ∘ₗ b := by ext x; rfl
    rw [e1, e2]
    exact LinearMap.trace_comp_comm' a b
  · intro S hF
    have h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S := fun x hx => hx
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dite_eq_left h1]
    have : (1 : Module.End ℂ V).restrict h1 = LinearMap.id := by ext x; rfl
    rw [this, LinearMap.trace_id]
end
end
