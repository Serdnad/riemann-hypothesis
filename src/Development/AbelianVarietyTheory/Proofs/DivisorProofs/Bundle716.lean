module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle682
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelTors

theorem mul_mem_iff {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (z : ℂ) :
    c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice := by
  rw [h.2, PeriodPair.mem_lattice]
  simp only [tauPair, mul_one]
  constructor
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, (mul_left_cancel₀ h.1 e).symm⟩
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, by rw [← e]⟩

theorem main : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  intro K _ _ ι Λ₀ Λ₁ T c₀ c₁ τ₀ τ₁ hT h0 h1 N _ R hR
  obtain ⟨-, a2, a3, a4, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ₀
  obtain ⟨-, b2, b3, b4, b5⟩ := GlobalTheory.WpFam.TorsMem.main N τ₁
  have H0 := mul_mem_iff h0
  have H1 := mul_mem_iff h1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have T00 : T 0 0 := hT.triv 0 0 (by simp) (by simp)
  have Tneg : ∀ a b, T a b → T (-a) (-b) := fun a b h => by
    simpa using hT.sub 0 0 a b T00 h
  have Tadd : ∀ a b c d, T a b → T c d → T (a + c) (b + d) := fun a b c d h h' => by
    simpa using hT.sub _ _ _ _ h (Tneg _ _ h')
  have Tnat : ∀ (n : ℕ) a b, T a b → T (n * a) (n * b) := by
    intro n a b h
    induction n with
    | zero => simpa using T00
    | succ n ih => simpa [add_mul] using Tadd _ _ _ _ ih h
  have adj : ∀ k k' m m', T k k' → ι k - ι m ∈ Λ₀.lattice → ι k' - ι m' ∈ Λ₁.lattice → T m m' := by
    intro k k' m m' h hm hm'
    have := hT.sub _ _ _ _ h (hT.triv (k - m) (k' - m') (by rwa [map_sub]) (by rwa [map_sub]))
    simpa using this
  have real0 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₀.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₀ _ h
    exact ⟨k + l, by rw [map_add (f := _), hl]; ring⟩
  have real1 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₁.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₁ _ h
    exact ⟨k + l, by rw [map_add (f := _), hl]; ring⟩
  refine ⟨fun x => ?_, fun x y x' y' hxy hxy' => ?_, fun x y hxy => ?_⟩
  ·
    obtain ⟨l, hl⟩ := hT.rat₀ ((N : ℂ) * (c₀ * tors N τ₀ x))
      (by rw [show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]; exact a4 x)
    set k : K := l / N with hkdef
    have hk : ι k = c₀ * tors N τ₀ x := by
      rw [hkdef, map_div₀, hl, map_natCast]; field_simp
    obtain ⟨k'', hk''⟩ := hT.left k
    have m1 : ι ((N : K) * k'') ∈ Λ₁.lattice := by
      refine (hT.mem_iff _ _ (Tnat N _ _ hk'')).1 ?_
      rw [map_mul, map_natCast, hk, show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]
      exact a4 x
    have hc1 := h1.1
    have hz : (N : ℂ) * (ι k'' / c₁) ∈ (tauPair τ₁).lattice := by
      rw [← H1]
      convert m1 using 1
      rw [map_mul, map_natCast]; field_simp
    obtain ⟨y, hy⟩ := b5 _ hz
    have hy' : ι k'' - c₁ * tors N τ₁ y ∈ Λ₁.lattice := by
      have := (H1 _).2 hy
      convert this using 1
      field_simp
    obtain ⟨k', hk'⟩ := real1 (c₁ * tors N τ₁ y) k'' (by rw [← neg_sub]; exact neg_mem hy')
    exact ⟨y, (hR x y).2 ⟨k, k', hk, hk', adj k k'' k k' hk'' (by simp) (by rw [hk']; exact hy')⟩⟩
  ·
    obtain ⟨k₁, k₁', e₁, e₁', t₁⟩ := (hR _ _).1 hxy
    obtain ⟨k₂, k₂', e₂, e₂', t₂⟩ := (hR _ _).1 hxy'
    have t₁₂ := hT.sub _ _ _ _ t₁ t₂
    have d0 : c₀ * tors N τ₀ (x - x') - ι (k₁ - k₂) ∈ Λ₀.lattice := by
      rw [map_sub, e₁, e₂, show c₀ * tors N τ₀ (x - x') - (c₀ * tors N τ₀ x - c₀ * tors N τ₀ x')
        = c₀ * -(tors N τ₀ (x - x' + x') - (tors N τ₀ (x - x') + tors N τ₀ x')) by
          rw [sub_add_cancel]; ring, H0]
      exact neg_mem (a2 _ _)
    have d1 : c₁ * tors N τ₁ (y - y') - ι (k₁' - k₂') ∈ Λ₁.lattice := by
      rw [map_sub, e₁', e₂', show c₁ * tors N τ₁ (y - y') - (c₁ * tors N τ₁ y - c₁ * tors N τ₁ y')
        = c₁ * -(tors N τ₁ (y - y' + y') - (tors N τ₁ (y - y') + tors N τ₁ y')) by
          rw [sub_add_cancel]; ring, H1]
      exact neg_mem (b2 _ _)
    obtain ⟨m, hm⟩ := real0 _ _ d0
    obtain ⟨m', hm'⟩ := real1 _ _ d1
    exact (hR _ _).2 ⟨m, m', hm, hm', adj _ _ m m' t₁₂
      (by rw [hm, ← neg_sub]; exact neg_mem d0) (by rw [hm', ← neg_sub]; exact neg_mem d1)⟩
  ·
    obtain ⟨k, k', e, e', t⟩ := (hR _ _).1 hxy
    rw [← a3 x, ← b3 y, ← H0, ← H1, ← e, ← e']
    exact hT.mem_iff k k' t

end GlobalTheory.RelTors
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixTransport

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X)
    (G' : Z ⟶ Y') (h : G ≫ F = G' ≫ F') : LBIso ((L.pull F).pull G) ((L.pull F').pull G') :=
  LBIso.chartPull
    (chartPullLinComb L F (fun _ : PUnit => G) (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)
    (chartPullLinComb L F' (fun _ : PUnit => G') (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => by rw [Category.id_comp, h])
    (lbIso_self (pull_isLB hL (G ≫ F)))

theorem lbIso_pull {X Y : Scheme.{0}} {L M : LB X} (H : LBIso L M) (h : Y ⟶ X) : LBIso (L.pull h) (M.pull h) :=
  LBIso.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl) H

theorem lbIso_congr {X : Scheme.{0}} {P P' Q Q' : LB X} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (hQ' : Q'.IsLB)
    (e₁ : LBIso P' P) (H : LBIso P Q) (e₂ : LBIso Q Q') : LBIso P' Q' :=
  LBIso.trans hP' hQ hQ' (LBIso.trans hP' hP hQ e₁ H) e₂

section Transport

variable {S S₁ S₂ : Scheme.{0}} (e : S₁ ≅ S₂) {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  (hL : L.IsLB) (hM : M.IsLB) {Af Bf : Over S₂} [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left)
  (φB : Bf.left ⟶ B.left)

def transport (R : HomFixRep Af Bf (L.pull φA) (M.pull φB)) :
    HomFixRep ((Over.pullback e.hom).obj Af) ((Over.pullback e.hom).obj Bf)
      (L.pull (pullback.fst Af.hom e.hom ≫ φA)) (M.pull (pullback.fst Bf.hom e.hom ≫ φB)) where
  H := R.H
  π := R.π ≫ e.inv
  AH := R.AH
  BH := R.BH
  φA := pullback.lift R.φA (R.AH.hom ≫ R.π ≫ e.inv) (by simp [R.pbA.1.w])
  φB := pullback.lift R.φB (R.BH.hom ≫ R.π ≫ e.inv) (by simp [R.pbB.1.w])
  pbA := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbA.congr (by simp) rfl)
  pbB := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbB.congr (by simp) rfl)
  Φ := R.Φ
  hom := R.hom
  iso := lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
    (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _ _ _ (by erw [pullback.lift_fst_assoc])) R.iso
    (lbIso_pull (lbIso_pull_pull hM _ _ _ _ (by erw [pullback.lift_fst_assoc])) _)
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ hI
    have hA₂ := hA.comp (isGrpPullback_pullback Af e.hom)
    have hB₂ := hB.comp (isGrpPullback_pullback Bf e.hom)
    obtain ⟨h, ⟨hπ, ψA, ψB, pA, pB, eA, eB, eΦ⟩, hu⟩ := R.rep T (t ≫ e.hom) A' B'
      (φA' ≫ pullback.fst Af.hom e.hom) (φB' ≫ pullback.fst Bf.hom e.hom) Φ' hA₂ hB₂ hΦ
      (lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
        (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
        (lbIso_pull_pull hL φA (φA' ≫ pullback.fst Af.hom e.hom) (pullback.fst Af.hom e.hom ≫ φA) φA' (by simp)) hI
        (lbIso_pull (lbIso_pull_pull hM (pullback.fst Bf.hom e.hom ≫ φB) φB' φB (φB' ≫ pullback.fst Bf.hom e.hom)
          (by simp)) Φ'.left))
    refine ⟨h, ⟨?_, ψA, ψB, pA, pB, ?_, ?_, eΦ⟩, ?_⟩
    · rw [← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eA
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pA.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hA.1.w.symm
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eB
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pB.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hB.1.w.symm
    · rintro h' ⟨hπ', ψA', ψB', pA', pB', eA', eB', eΦ'⟩
      refine hu h' ⟨by rw [← hπ']; simp, ψA', ψB', pA', pB', by rw [← eA', Category.assoc]; erw [pullback.lift_fst],
        by rw [← eB', Category.assoc]; erw [pullback.lift_fst], eΦ'⟩

end Transport

end GlobalTheory.HomFixTransport


open GlobalTheory.HomFixTransport in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.HomFixTransport.homFixRep_basicOpen : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (f : Rg), L.IsLB → M.IsLB → (∀ (Af Bf : Over (Sp (Localization.Away f))) [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left) (φB : Bf.left ⟶ B.left), IsGrpPullback Af A (spMap (algebraMap Rg (Localization.Away f))) φA → IsGrpPullback Bf B (spMap (algebraMap Rg (Localization.Away f))) φB → ∃ R : HomFixRep Af Bf (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∀ U : (Sp Rg).Opens, U = PrimeSpectrum.basicOpen f → ∃ (AU : Over U.toScheme) (_ : GrpObj AU) (BU : Over U.toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A U.ι φA ∧ IsGrpPullback BU B U.ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ A B _ _ L M f hL hM hyp U hU
  have hr : Set.range U.ι = Set.range (spMap (algebraMap Rg (Localization.Away f))) := by
    rw [Scheme.Opens.range_ι, hU]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  haveI : IsOpenImmersion (spMap (algebraMap Rg (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Rg (Localization.Away f)))))
  let e := IsOpenImmersion.isoOfRangeEq U.ι (spMap (algebraMap Rg (Localization.Away f))) hr
  have he : e.hom ≫ spMap (algebraMap Rg (Localization.Away f)) = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨R, h₁, h₂, h₃⟩ := hyp _ _ _ _ (isGrpPullback_pullback A (spMap (algebraMap Rg (Localization.Away f))))
    (isGrpPullback_pullback B (spMap (algebraMap Rg (Localization.Away f))))
  refine ⟨_, inferInstance, _, inferInstance, _, _,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback A _)).congr he rfl,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback B _)).congr he rfl,
    transport e hL hM _ _ R, ?_, ?_, ?_⟩
  · show QuasiCompact (R.π ≫ e.inv); infer_instance
  · show IsSeparated (R.π ≫ e.inv); infer_instance
  · show LocallyOfFiniteType (R.π ≫ e.inv); infer_instance
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_fou | exact GlobalTheory.KSp.heisFun_fou | (intros; apply GlobalTheory.KSp.heisFun_fou <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.siegelParabolic_weylElement_generate_unitary : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  first | exact @GlobalTheory.KSp.sieg_weyl_generate | exact GlobalTheory.KSp.sieg_weyl_generate | (intros; apply GlobalTheory.KSp.sieg_weyl_generate <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ), ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  first | exact @GlobalTheory.KSp.sc_eventually_eq_one | exact GlobalTheory.KSp.sc_eventually_eq_one | (intros; apply GlobalTheory.KSp.sc_eventually_eq_one <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.ClassInvAny


open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates in
theorem classInv_of_unit_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E), HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ u = 1) → ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ), (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y' → IsLatSum φ (2 * s) κ (lattice c y) S → IsLatSum φ (2 * s) κ (lattice c y') S' → ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹ * S' 0 := by
  intro E _ _ _ I _ φ hφ s κ c χ hχ hunit y y' S S' hq hS hS'
  classical
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := GlobalTheory.ClassInv.lattice_princ_mul_unit (c := c) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 :=
    (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := hunit u hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, GlobalTheory.ClassInv.lamInf_eq hφ hχ α]
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInvAny
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.heckeChar_unramified_inverse_split_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E)) (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P → UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | exact GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | (intros; apply GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

def ObjMap.comp {R : Type} [CommRing R] {D : Datum p} {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
    by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT

namespace GlobalTheory.RelTan

end GlobalTheory.RelTan
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.ObjMapComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {s'' : S'' ⟶ Sp R}
  {o : Obj b N s} {o' : Obj b N s'} {o'' : Obj b N s''} {f : S' ⟶ S} {g : S'' ⟶ S'}

def comp (m₁ : ObjMap o'' o' g) (m₂ : ObjMap o' o f) : ObjMap o'' o (g ≫ f) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
         by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o''.isLB (pull_isLB o'.isLB m₁.φ₂) (pull_isLB o.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o'.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT.ObjMapComp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  first | exact @GlobalTheory.UPel.HT.rep_conj_of_trace_eq | exact GlobalTheory.UPel.HT.rep_conj_of_trace_eq | (intros; apply GlobalTheory.UPel.HT.rep_conj_of_trace_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_level_pairing_eq_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (r : ℕ) (W : Q → Q → kˣ) (ζ : kˣ), IsPrimitiveRoot ζ (p ^ r) → (∀ a a' b : Q, a ^ (p ^ r) = 1 → a' ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (a * a') b = W a b * W a' b) → (∀ a b : Q, a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W a b * W b a = 1) → (∀ (c : D.O) (a b : Q), a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (act c a) b = W a (act (D.star c).unop b)) → (∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W a b = 1) → a = 1) → ∀ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) → ∃ f' : D.La → Q, ((∀ x y, f' (x + y) = f' x * f' y) ∧ (∀ (c : D.O) x, f' (c • x) = act c (f' x)) ∧ (∀ x, f' x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f' x = g)) ∧ ∀ x y, W (f' x) (f' y) = ζ ^ D.EF x y := by
  first | (exact @GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq) | (exact GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq) | (intros; apply GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq <;> assumption)
end
