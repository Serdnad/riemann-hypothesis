module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle009
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

private theorem mem_basicOpen_of_ne {p : ℕ} {Y : Scheme.{0}} (Ω : Type) [Field Ω]
    (x : gp Ω ⟶ Y) (hp : (p : Ω) ≠ 0) : pt x ∈ Y.basicOpen (p : Γ(Y, ⊤)) := by
  have hu : IsUnit ((p : ℕ) : Γ(gp Ω, ⊤)) := by
    have h1 : IsUnit ((p : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hp
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    simpa using h2
  have h3 : (gp Ω).basicOpen (x.appTop (p : Γ(Y, ⊤))) = ⊤ := by
    rw [map_natCast]
    exact Scheme.basicOpen_of_isUnit _ hu
  have h4 : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h3]
    trivial
  exact h4

theorem nwtOne : NwtOne := by
  intro p Y T hL _
  obtain ⟨_, _, _, _, _, _, _, hMB, _, _, hWN, _, hNF, _, _⟩ := all_holds.1
  haveI := T.fin
  have hN : IsNwt T.p (nwt T.p) := hWN T.p hL
  refine ⟨hN.1, ?_⟩
  intro Ω _ _ z hp
  haveI := T.et
  have hD : Dense {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} := by
    have hs : {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} =
        {s | GenPt s} := by
      ext s
      exact genBasic_of.2.1 (Y.basicOpen (p : Γ(Y, ⊤))).ι s
    rw [hs]
    exact genBasic_of.1 _
  have hc := hNF (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤))) T.p
    (Y.basicOpen (p : Γ(Y, ⊤))).ι (isPullback_morphismRestrict T.p _).flip hN hD
  rw [hMB.2.2 (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤)))] at hc
  have hmem : pt (z ≫ T.p) ∈ Y.basicOpen (p : Γ(Y, ⊤)) := mem_basicOpen_of_ne Ω (z ≫ T.p) hp
  have hr : Set.range z ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hq
    exact hmem
  have hz := IsOpenImmersion.lift_fac (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι z hr
  have h5 := congrArg (fun w : Wt _ => w Ω (IsOpenImmersion.lift _ z hr)) hc
  simp only [Wt.comap, hz] at h5
  rw [h5]
  rfl

end UpperTheory.Gal.Mod

end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma sp_twist {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (u : gp Ω ⟶ Y) :
    sp a ≫ twist φ Y u = twist φ' Y (sp a ≫ u) := by
  have h : sp a ≫ sp φ = sp φ' ≫ sp a := by
    simp only [UpperTheory.Gal.Mod.sp, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  change sp a ≫ sp φ ≫ u = sp φ' ≫ sp a ≫ u
  rw [← Category.assoc, h, Category.assoc]

private lemma sp_iter {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (m : ℕ) (u : gp Ω ⟶ Y) :
    sp a ≫ (twist φ Y)^[m] u = (twist φ' Y)^[m] (sp a ≫ u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sp_twist a φ φ' hc]

private lemma pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] {Z : Scheme.{0}} (a : Ω →+* Ω') (z : gp Ω ⟶ Z) :
    pt (sp a ≫ z) = pt z := by
  have h : ∀ c : gp Ω', (sp a ≫ z) c = z (sp a c) := fun c => Scheme.Hom.comp_apply _ _ _
  exact (h _).trans (congrArg (fun t : gp Ω => z t) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _))

private lemma sum_eq (hF : FibExt) (hWt : TranscendenceTraces.WtPt) {p : ℕ} {Y : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z)
    (hw : IsWt T.p w) (m : ℕ) {Ω Ω' : Type} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (x y : gp Ω ⟶ Y) :
    ∑ᶠ z ∈ {z : gp Ω ⟶ T.Z | z ≫ T.p = x ∧ (twist φ Y)^[m] (z ≫ T.r) = y}, w Ω z =
      ∑ᶠ z ∈ {z : gp Ω' ⟶ T.Z | z ≫ T.p = sp a ≫ x ∧ (twist φ' Y)^[m] (z ≫ T.r) = sp a ≫ y}, w Ω' z := by
  haveI : IsFinite T.p := T.fin
  obtain ⟨-, hb, hinj⟩ := hF T.p Ω Ω' a x
  refine finsum_mem_eq_of_bijOn (fun z => sp a ≫ z) ⟨?_, ?_, ?_⟩ ?_
  · rintro z ⟨h1, h2⟩
    refine ⟨by simp only [Category.assoc, h1], ?_⟩
    rw [Category.assoc, ← sp_iter a φ φ' hc, h2]
  · intro z hz z' hz' h
    exact hb.injOn (show z ∈ fib T.p x from hz.1) (show z' ∈ fib T.p x from hz'.1) h
  · rintro z' ⟨h1, h2⟩
    obtain ⟨z, hz, rfl⟩ := hb.surjOn (show z' ∈ fib T.p (sp a ≫ x) from h1)
    refine ⟨z, ⟨hz, hinj _ _ ?_⟩, rfl⟩
    rw [sp_iter a φ φ' hc, ← Category.assoc] at *
    simpa [Category.assoc] using h2
  · intro z _
    exact hWt T.p w hw Ω Ω' z (sp a ≫ z) (pt_sp a z).symm

theorem UpperTheory.Gal.Mod.cycExt :
    FibExt → CycExt := by
  intro hF p q n Y T w hw Ω Ω' _ _ _ _ a φ φ' hc x
  have hWt : TranscendenceTraces.WtPt := TranscendenceTraces.all_holds.1.2.2.2.2.1
  have hs := fun (j : Fin (n + 1)) y => sum_eq hF hWt (T j) (w j) (hw j) (n - j) a φ φ' hc x y
  constructor
  · intro h y'
    by_cases hy : ∃ y : gp Ω ⟶ Y, y' = sp a ≫ y
    · obtain ⟨y, rfl⟩ := hy
      have := h y
      simp only [hs] at this
      exact this
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : {z : gp Ω' ⟶ (T j).Z | z ≫ (T j).p = sp a ≫ x ∧ (twist φ' Y)^[n - j] (z ≫ (T j).r) = y'} = ∅ := by
        ext z'
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        haveI : IsFinite (T j).p := (T j).fin
        obtain ⟨z, -, rfl⟩ := (hF (T j).p Ω Ω' a x).2.1.surjOn (show z' ∈ fib (T j).p (sp a ≫ x) from h1)
        refine hy ⟨(twist φ Y)^[n - j] (z ≫ (T j).r), ?_⟩
        rw [sp_iter a φ φ' hc, ← h2, Category.assoc]
      rw [this]
      simp
  · intro h y
    have := h (sp a ≫ y)
    simp only [← hs] at this
    exact this
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private noncomputable def frPow {S : Scheme.{0}} (Fr : S ⟶ S) : ℕ → (S ⟶ S)
  | 0 => 𝟙 S
  | m + 1 => frPow Fr m ≫ Fr

private theorem frPow_bS {S B : Scheme.{0}} (Fr : S ⟶ S) (bS : S ⟶ B) (h : Fr ≫ bS = bS) (m : ℕ) :
    frPow Fr m ≫ bS = bS := by
  induction m with
  | zero => simp [frPow]
  | succ m ih => simp only [frPow, Category.assoc, h, ih]

private theorem frPow_twist {S Y : Scheme.{0}} (Fr : S ⟶ S) (s : S ⟶ Y) {Ω : Type} [Field Ω] (φ : Ω →+* Ω)
    (h : ∀ x : gp Ω ⟶ S, x ≫ Fr ≫ s = twist φ Y (x ≫ s)) (m : ℕ) (u : gp Ω ⟶ S) :
    u ≫ frPow Fr m ≫ s = (twist φ Y)^[m] (u ≫ s) := by
  induction m with
  | zero => simp [frPow]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih, ← Category.assoc u (frPow Fr m) s, ← h]
    simp [frPow]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i).comp (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem pullHQ_pow (l : ℕ) [Fact l.Prime] {S : Scheme.{0}} (Fr : S ⟶ S) (k i : ℤ) (m : ℕ) :
    pullHQ l (sch.map (frPow Fr m)) k i =
      (pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ m := by
  induction m with
  | zero =>
    simp only [frPow, CategoryTheory.Functor.map_id, pow_zero]
    unfold pullHQ
    rw [pullHl_id, LinearMap.baseChange_id]
    rfl
  | succ m ih =>
    rw [pow_succ, ← ih]
    simp only [frPow, Functor.map_comp]
    rw [pullHQ_comp']
    rfl

theorem UpperTheory.Gal.Mod.esPt :
    CycAll → ESPt := by
  intro hC l _ p f n hp Y π T w hone hpt hdense hπ S B s bS _ _ Fr hl hD hinj hFrB hFrTw c v hpb hf hb hw k i
  have hCE : TranscendenceTraces.CorrEqQ := TranscendenceTraces.all_holds.2.2.2.2.2.2.2.1
  let c' : Fin (n + 1) → TranscendenceTraces.Corr S S := fun j =>
    ⟨(c j).Z, (c j).p, (c j).f ≫ frPow Fr (n - j), (c j).w, (c j).fin, (c j).wt⟩
  have hop : ∀ j : Fin (n + 1), (c' j).opQ l k i = (c j).opQ l k i *
      (pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ (n - (j : ℕ)) := by
    intro j
    have e : pullHQ l (sch.map ((c j).f ≫ frPow Fr (n - (j : ℕ)))) k i =
        (pullHQ l (sch.map (c j).f) k i).comp
          ((pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ (n - (j : ℕ))) := by
      rw [Functor.map_comp, pullHQ_comp', pullHQ_pow]
    apply LinearMap.ext
    intro x
    show TranscendenceTraces.trHQ l (c j).p (c j).w k i (pullHQ l (sch.map ((c j).f ≫ frPow Fr (n - (j : ℕ)))) k i x) = _
    rw [e]
    rfl
  have hbase : ∀ j : Fin (n + 1), (c' j).f ≫ bS = (c' j).p ≫ bS := by
    intro j
    show ((c j).f ≫ frPow Fr (n - (j : ℕ))) ≫ bS = (c j).p ≫ bS
    rw [Category.assoc, frPow_bS Fr bS hFrB, hb j]
  have key := hCE l k i bS bS (Fin (n + 1)) c' (fun j => co (p ^ f) j) hbase hl _ hD (by
    intro Ω _ _ x y hx
    have hgen : crystallineComparison.GenPt π (pt (x ≫ s)) := by
      have e : pt (x ≫ s) = s (pt x) := rfl
      rw [e]
      exact hx
    obtain ⟨φ, hφ, hcyc⟩ := hC p f n hp Y π T w hone hpt hdense hπ Ω (x ≫ s) hgen
    have hit := frPow_twist Fr s φ (hFrTw Ω φ hφ)
    by_cases hy : y ≫ bS = x ≫ bS
    · rw [← hcyc (y ≫ s)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      show ∑ᶠ z ∈ {z : gp Ω ⟶ (c j).Z | z ≫ (c j).p = x ∧ z ≫ (c j).f ≫ frPow Fr (n - (j : ℕ)) = y}, (c j).w Ω z = _
      refine finsum_mem_eq_of_bijOn (fun z => z ≫ v j) ⟨?_, ?_, ?_⟩ ?_
      · rintro z ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · show (z ≫ v j) ≫ (T j).p = x ≫ s
          rw [Category.assoc, (hpb j).w, ← Category.assoc, h1]
        · show (twist φ Y)^[n - (j : ℕ)] ((z ≫ v j) ≫ (T j).r) = y ≫ s
          rw [Category.assoc, ← hf j, ← Category.assoc, ← hit, ← h2]
          simp
      · intro z h z' h' e
        exact (hpb j).hom_ext e (h.1.trans h'.1.symm)
      · rintro t ⟨h1, h2⟩
        obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ v j = t ∧ L ≫ (c j).p = x :=
          ⟨(hpb j).lift t x h1, (hpb j).lift_fst _ _ _, (hpb j).lift_snd _ _ _⟩
        refine ⟨L, ⟨hL2, ?_⟩, hL1⟩
        apply hinj Ω
        · have e : ((L ≫ (c j).f) ≫ frPow Fr (n - (j : ℕ))) ≫ s = y ≫ s := by
            rw [Category.assoc, hit, Category.assoc, hf j, ← Category.assoc, hL1]
            exact h2
          simpa only [Category.assoc] using e
        · simp only [Category.assoc]
          rw [frPow_bS Fr bS hFrB, hb j, ← Category.assoc, hL2, hy]
      · intro z _
        rw [hw j]
        rfl
    · refine Finset.sum_eq_zero fun j _ => ?_
      have e : {z : gp Ω ⟶ (c' j).Z | z ≫ (c' j).p = x ∧ z ≫ (c' j).f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        apply hy
        rw [← h2, ← h1]
        exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) (hbase j)).trans (Category.assoc _ _ _).symm)
      show _ * ∑ᶠ z ∈ {z : gp Ω ⟶ (c' j).Z | z ≫ (c' j).p = x ∧ z ≫ (c' j).f = y}, (c' j).w Ω z = 0
      rw [e]
      simp)
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) key
  rw [hop j]
end
