module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem isIso_reindex {W P : Scheme.{0}} {J : Type} {m : ℕ} (e : Fin m ≃ J) (f : J → (W ⟶ P))
    (h : IsIso (Sigma.desc f : ∐ (fun _ : J => W) ⟶ P)) :
    IsIso (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) := by
  have heq : (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) =
      (Sigma.reindex e (fun _ : J => W)).hom ≫ Sigma.desc f := by
    ext i
    have h2 : Sigma.ι (fun _ : Fin m => W) i ≫ (Sigma.reindex e (fun _ : J => W)).hom =
        Sigma.ι (fun _ : J => W) (e i) := Sigma.ι_reindex_hom e (fun _ : J => W) i
    rw [← Category.assoc, h2]
    simp
  rw [heq]
  infer_instance

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  classical
  set D : ∐ (fun _ : Fin m => U) ⟶ P := Sigma.desc s' with hD
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ D = s' j := fun j => Sigma.ι_desc _ _
  have huniq : ∀ j₁ j₂, x0 ≫ s' j₁ = x0 ≫ s' j₂ → j₁ = j₂ := by
    intro j₁ j₂ h
    rw [← hι j₁, ← hι j₂, ← Category.assoc, ← Category.assoc, cancel_mono] at h
    have h2 := congrArg (fun f : gp Ω ⟶ ∐ (fun _ : Fin m => U) => f (IsLocalRing.closedPoint Ω)) h
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 := (sigmaι_eq_iff (fun _ : Fin m => U) j₁ j₂ _ _).mp h2
    exact (Sigma.mk.inj_iff.mp h3).1
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (sigmaMk (fun _ : Fin m => U)).surjective ((y ≫ inv D) (IsLocalRing.closedPoint Ω))
  rw [sigmaMk_mk] at hju
  have hrange : Set.range (y ≫ inv D).base ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j).base := by
    rintro _ ⟨z, rfl⟩
    refine ⟨u, ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hju
  obtain ⟨t, ht⟩ : ∃ t, t ≫ Sigma.ι (fun _ : Fin m => U) j = y ≫ inv D :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hy2 : t ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have htx : t = x0 := by
    rw [← hy, ← hy2, Category.assoc, hs, Category.comp_id]
  have hy3 : x0 ≫ s' j = y := by
    rw [← htx]
    exact hy2
  exact ⟨j, hy3, fun j₁ hj₁ => huniq _ _ (hj₁.trans hy3.symm)⟩

private theorem push_one {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Surjective c] {G : Type} [Finite G]
    (a : G → (W ⟶ W)) (hs : Splits c c a) : (Wt.const W 1).push c = Wt.const S (Nat.card G : ℤ) := by
  classical
  obtain ⟨hac, hiso⟩ := hs
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ G) := ⟨Nat.card G, ⟨(Finite.equivFin G).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  funext Ω _ _ x
  show ∑ᶠ (z : gp Ω ⟶ W) (_ : z ∈ fib c x), (1 : ℤ) = (Nat.card G : ℤ)
  obtain ⟨v, hv⟩ := c.surjective (pt x)
  obtain ⟨z0, hz0, -⟩ := TranscendenceTraces.ptLift_holds c Ω x v hv
  have key := fun (y : gp Ω ⟶ pullback c c) (hy : y ≫ pullback.snd c c = z0) =>
    existsUnique_sec (pullback.snd c c)
      (fun j => pullback.lift (a (e j)) (𝟙 W) (by rw [hac, Category.id_comp]))
      (fun j => pullback.lift_snd _ _ _) hiso' z0 y hy
  have hlift : ∀ g : G, z0 ≫ pullback.lift (a g) (𝟙 W) (by rw [hac, Category.id_comp]) =
      pullback.lift (z0 ≫ a g) z0 (by rw [Category.assoc, hac]) := by
    intro g
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have hfib : fib c x = Set.range (fun g : G => z0 ≫ a g) := by
    ext z
    constructor
    · intro hz
      have hzc : z ≫ c = z0 ≫ c := by
        rw [hz0]
        exact hz
      obtain ⟨j, hj, -⟩ := key (pullback.lift z z0 hzc) (pullback.lift_snd _ _ _)
      refine ⟨e j, ?_⟩
      have h1 := congrArg (· ≫ pullback.fst c c) hj
      simp only [Category.assoc, pullback.lift_fst] at h1
      exact h1
    · rintro ⟨g, rfl⟩
      show (z0 ≫ a g) ≫ c = x
      rw [Category.assoc, hac, hz0]
  have hinj : Function.Injective (fun g : G => z0 ≫ a g) := by
    intro g₁ g₂ h
    have h' : z0 ≫ a g₁ = z0 ≫ a g₂ := h
    obtain ⟨j, -, huniq⟩ := key (pullback.lift (z0 ≫ a g₁) z0 (by rw [Category.assoc, hac]))
      (pullback.lift_snd _ _ _)
    have e1 := huniq (e.symm g₁) (by
      simp only [Equiv.apply_symm_apply]
      exact hlift g₁)
    have e2 := huniq (e.symm g₂) (by
      simp only [Equiv.apply_symm_apply]
      rw [hlift g₂]
      congr 1
      exact h'.symm)
    exact e.symm.injective (e1.trans e2.symm)
  rw [hfib, finsum_mem_range hinj]
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

private theorem pull_inj (l : ℕ) [Fact l.Prime] {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Etale c] [Surjective c]
    {G : Type} [Finite G] [Nonempty G] (a : G → (W ⟶ W)) (hs : Splits c c a) (hl : IsUnit (l : Γ(S, ⊤))) (k : ℤ) :
    Function.Injective (pullHQ l (sch.map c) k 0) := by
  have wt : IsWt c (Wt.const W 1) := by
    rw [← UpperTheory.Gal.TranscendenceTraces.multBasic_holds.2.2 c]
    exact UpperTheory.Gal.TranscendenceTraces.wtFlat_holds c
  have hd := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.1 l k 0 c (Wt.const W 1) (Nat.card G : ℤ) wt hl (push_one c a hs)
  have hne : (((Nat.card G : ℤ) : ℤ) : ℚ_[l]) ≠ 0 := by
    have : (Nat.card G : ℤ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast this
  intro x y hxy
  have h1 := LinearMap.congr_fun hd x
  have h2 := LinearMap.congr_fun hd y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  rw [hxy, h2] at h1
  exact (smul_right_injective _ hne h1).symm

theorem UpperTheory.Gal.Mod.corrOpEq :
    CorrOpEq := by
  intro l _ S c _ hw hl T hT
  obtain ⟨W, c', G, _, _, a, J, _, σ, hgal, hsplit, hTx⟩ := hT
  obtain ⟨hfin, het, hsurj, -, -, hsc⟩ := hgal
  haveI := hfin
  haveI := het
  haveI := hsurj
  haveI : IsFinite c.p := c.fin
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨hσ, hiso⟩ := hsplit
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ J) := ⟨Fintype.card J, ⟨(Fintype.equivFin J).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  have hsplitQ : ∀ k : ℤ, pullHQ l (sch.map c') k 0 ∘ₗ TranscendenceTraces.trHQ l c.p (Wt.const c.Z 1) k 0 =
      ∑ j : Fin m, pullHQ l (sch.map (σ (e j))) k 0 := fun k =>
    TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l k 0 c.p hl W c' m (fun j => σ (e j)) (fun j => hσ (e j)) hiso'
  have hinj : Function.Injective (pullTot l (sch.map c')) := by
    intro x y hxy
    refine DFinsupp.ext fun k => ?_
    have h := congrArg (fun z => z k) hxy
    simp only [pullTot, DirectSum.lmap_apply] at h
    exact pull_inj l c' a hsc hl k h
  apply LinearMap.ext
  intro x
  apply hinj
  rw [hTx x]
  refine DFinsupp.ext fun k => ?_
  have h1 := LinearMap.congr_fun (hsplitQ k) (pullHQ l (sch.map c.f) k 0 (x k))
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1
  erw [DirectSum.sum_apply]
  simp only [pullTot, DirectSum.lmap_apply, TranscendenceTraces.Corr.opQ, hw, LinearMap.comp_apply, h1,
    TranscendenceTraces.pullHQ_comp]
  exact (e.sum_comp (fun j => pullHQ l (sch.map (σ j)) k 0 (pullHQ l (sch.map c.f) k 0 (x k)))).symm
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem push_const_one {Z Z' : Scheme.{0}} (u : Z ⟶ Z') [IsFinite u] (δ : ℕ)
    (hδ : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Z'), (fib u x).ncard = δ) :
    (Wt.const Z 1).push u = Wt.const Z' (δ : ℤ) := by
  funext Ω _ _ x
  simp only [Wt.push, Wt.const]
  rw [← hδ Ω x]
  obtain hs | hs := (fib u x).infinite_or_finite
  · rw [hs.ncard, Nat.cast_zero]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hs)
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card _ hs]
    simp

theorem UpperTheory.Gal.Mod.opCover :
    OpCover := by
  intro l _ S S' c c' u _ δ hw hw' hp hf hl hδ k i
  haveI := c.fin
  haveI := c'.fin
  have hadic := TranscendenceTraces.all_holds.2.2
  have hwl := TranscendenceTraces.all_holds.1.2.2.1
  have hwc : IsWt (u ≫ c'.p) (Wt.const c.Z 1) := by
    have h0 := c.wt
    rw [hw, ← hp] at h0
    exact h0
  have hwc' : IsWt c'.p (Wt.const c'.Z 1) := by
    have h0 := c'.wt
    rw [hw'] at h0
    exact h0
  have hpush := TranscendenceTraces.trPushQ_of TranscendenceTraces.trPush_holds hadic.2.1 TranscendenceTraces.wtPush_holds l k i u c'.p
    (Wt.const c.Z 1) hwc hl
  rw [push_const_one u δ hδ] at hpush
  have hcomp := hadic.2.2.2.1 l k i c'.p (𝟙 S) (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) hwc'
    (hwl.2.2 (𝟙 S) (δ : ℤ)) hl
  have hmul : Wt.mul c'.p (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) = Wt.const c'.Z (δ : ℤ) := by
    funext Ω _ _ z
    simp [Wt.mul, Wt.const]
  rw [Category.comp_id, hmul, TranscendenceTraces.trIdQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance l k i S δ hl,
    LinearMap.smul_comp, LinearMap.id_comp] at hcomp
  have hpull : pullHQ l (sch.map (u ≫ c'.f)) k i =
      pullHQ l (sch.map u) k i ∘ₗ pullHQ l (sch.map c'.f) k i := by
    simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
  unfold TranscendenceTraces.Corr.opQ
  rw [← hf, ← hp, hw, hw', hpull, ← LinearMap.comp_assoc, hpush, hcomp, LinearMap.smul_comp]
  first
    | rfl
    | simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    | (norm_cast; simp [Nat.cast_smul_eq_nsmul])
end
