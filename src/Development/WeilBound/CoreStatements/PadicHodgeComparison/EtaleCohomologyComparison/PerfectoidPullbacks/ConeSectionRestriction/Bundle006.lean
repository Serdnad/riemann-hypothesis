module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.InfinityCoordAlgebraicIndependent
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

theorem resid_alg : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R) :=
  by
  intro K _ _ n R _ _ _ t ht D hD B hTB hFG hInt hMono hFrac ω η hω hη heq
  have hne : ∀ i : Fin (n + 2), (Finset.univ.erase i).Nonempty := fun i => by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hune : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  have hfin : FiniteDimensional (fldF K t) (FractionRing R) :=
    fldF_findim t (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac
  obtain ⟨res, hres1, hres0, hresD⟩ := res_R t ht D hD

  let Φ : R →+ FractionRing R :=
    ((algebraMap (fldF K t) (FractionRing R)).toAddMonoidHom.comp
      (Algebra.trace (fldF K t) (FractionRing R)).toAddMonoidHom).comp
      (algebraMap R (FractionRing R)).toAddMonoidHom
  have hΦ : ∀ x, Φ x = algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) x)) := fun _ => rfl

  have hchart : ∀ i : Fin (n + 2), ∃ B' : Subalgebra K R, B (Finset.univ.erase i) ≤ B' ∧
      torusS K t (Finset.univ.erase i) ≤ B' ∧ B'.FG ∧
      (∀ b ∈ B', IsIntegral (torusS K t (Finset.univ.erase i)) b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := fun i => by
    obtain ⟨w, hwA, hw0, hscale⟩ := torus_scale (K := K) t i
    obtain ⟨B', hB', hFG', hInt', hFrac'⟩ := chart_ext (torusS K t (Finset.univ.erase i)) (torusS K t Finset.univ)
      (B (Finset.univ.erase i)) (B Finset.univ) (torusS_le_univ t _) (hTB _ (hne i)) (hMono i) (hTB _ hune)
      (hFG _ (hne i)) (hInt _ (hne i)) (hFG _ hune) (hInt _ hune) hFrac w hwA hw0 hscale
    exact ⟨B', hB', (hTB _ (hne i)).trans hB', hFG', hInt', hFrac'⟩

  have hω' : ∀ i, ∃ a : R, Φ (ω i) = algebraMap R (FractionRing R) a ∧ res a = 0 := by
    intro i
    obtain ⟨B', hB', hTB', hFG', hInt', hFrac'⟩ := hchart i
    induction i using Fin.cases with
    | zero =>
      obtain ⟨y', hy', hyeq⟩ := jacobian_infinityDerivation t D (B (Finset.univ.erase 0)) (ω 0) (hω 0)
      obtain ⟨hinj, hloc⟩ := infinityCoord_localization t ht
      obtain ⟨a', ha'S, ha'⟩ := trace_chart t (Finset.univ.erase 0) (fun k => ⟨u0 t k, infinityCoord_mem_torus t k⟩) hinj hloc
        (torusS_frac t _ (hne 0)) B' hTB' hFG' hInt' hFrac' (infinityDerivation t D) (fun k j => infinityDerivation_coord t D hD k j) id
        Function.injective_id y' (jacS_mono _ _ hB' _ _ hy')
      set c : R := -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) with hc
      have hcT : c ∈ torusS K t Finset.univ := neg_mem (pow_mem (inv_mem_univ t 0) _)
      let cF : fldF K t := ⟨algebraMap R (FractionRing R) c, torus_mem_fldF t Finset.univ c hcT⟩
      refine ⟨c * a', ?_, ?_⟩
      · rw [hΦ, hyeq, RingHom.map_mul (algebraMap R (FractionRing R)) c y']
        have h1 : algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) y' =
            cF • algebraMap R (FractionRing R) y' := rfl
        rw [h1, LinearMap.map_smul, smul_eq_mul, RingHom.map_mul, ha', RingHom.map_mul]
        rfl
      · rw [hc, neg_mul, map_neg, hres0 _ (infinityCoord_span_residue_ne t a' ha'S), neg_zero]
    | succ k =>
      have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
        Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
      obtain ⟨hinj, hloc⟩ := torusS_loc t ht _ h0
      obtain ⟨a, haS, ha⟩ := trace_chart t (Finset.univ.erase k.succ)
        (fun k => ⟨t k, t_mem_torusS t _ h0 k⟩) hinj hloc
        (torusS_frac t _ (hne _)) B' hTB' hFG' hInt' hFrac' D (fun k j => hD k j) id
        Function.injective_id (ω k.succ) (jacS_mono _ _ hB' _ _ (hω k.succ))
      exact ⟨a, ha, hres0 _ (torusS_succ_span t k a haS)⟩

  have hη' : ∀ k, ∃ b : R, Φ (D k (η k)) = algebraMap R (FractionRing R) b ∧ res b = 0 := by
    intro k
    obtain ⟨hinj, hloc⟩ := torusS_loc t ht Finset.univ (Finset.mem_univ 0)
    obtain ⟨b, hbT, hb⟩ := trace_chart t Finset.univ (fun k => ⟨t k, t_mem_torusS t _ (Finset.mem_univ 0) k⟩)
      hinj hloc (torusS_frac t _ hune) (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac D
      (fun k j => hD k j) (Fin.succAbove k) Fin.succAbove_right_injective (η k) (hη k)
    have hDc : ∀ j, D k (t j : R) ∈ Set.range (algebraMap K R) := fun j => by
      rw [hD]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    exact ⟨D k b, trace_deriv t (D k) hDc (η k) b hbT hb, hresD k b hbT⟩
  choose a ha using hω'
  choose b hb using hη'

  have : Module.Free (fldF K t) (FractionRing R) := Module.Free.of_divisionRing _ _
  have hp : (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := prod_inv_mem t
  let pF : fldF K t := ⟨algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R), torus_mem_fldF t _ _ hp⟩
  have hsign : ∀ (k : Fin (n + 1)) (x : R), (-1 : R) ^ (k : ℕ) * x = ((-1 : ℤ) ^ (k : ℕ)) • x := fun k x => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hrel : Module.finrank (fldF K t) (FractionRing R) • (((∏ k, t k)⁻¹ : Rˣ) : R) =
      ∑ i, a i + ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • b k := by
    apply IsFractionRing.injective R (FractionRing R)
    have h1 := congrArg Φ heq

    simp only [map_add (f := _), map_sum, hsign] at h1

    rw [map_nsmul, map_add (f := _), map_sum, map_sum]
    simp only [map_zsmul]
    simp only [map_zsmul, fun i => (ha i).1, fun k => (hb k).1] at h1
    rw [← h1, hΦ]
    have h2 : algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R) =
        algebraMap (fldF K t) (FractionRing R) pF := rfl
    rw [h2, Algebra.trace_algebraMap, map_nsmul]
  have hres := congrArg res hrel

  rw [map_nsmul, hres1, map_add (f := _), map_sum, map_sum] at hres
  simp only [map_zsmul, fun i => (ha i).2, fun k => (hb k).2, smul_zero, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one] at hres
  rw [Nat.cast_eq_zero] at hres
  exact (Module.finrank_pos (R := fldF K t) (M := FractionRing R)).ne' hres

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def CLiftK.precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) : CLiftK (h ⋙ g) D where
  p c := Λ.p (h.obj c)
  hp c := Λ.hp (h.obj c)
  w φ := Λ.w (h.map φ)
  hw φ hh := Λ.hw (h.map φ) hh

def zK {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ) :
    CH.Cn (g ⋙ O (smFun X q)) 2 :=
  fun σ => (show (g.obj (σ.obj (Fin.last 2))).B from
    plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1))

def 𝒱D (D : E.LineData X) : Set X.Opens := {V | ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι}

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) : T.B :=
  Classical.choose (Ideal.Quotient.mk_surjective (ev T h g))

def dlogC (Q : ObjectProperty (Thick (smFun X q))) (s : ℕ) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) :
    CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    plogK (σ.obj (Fin.last 1)).obj.δ s (ĝ (σ.obj (Fin.last 1)) *
      Ring.inverse ((σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0))) - 1))

def jacSpan {V V' : X.Opens} (h : V ≤ V') {A : Type} [CommRing A] (ι : Γ(X, V) →+* A) {d m : ℕ}
    (D : Fin d → Γ(X, V) → A) (κ : Fin m → Fin d) : AddSubgroup A :=
  AddSubgroup.closure {y | ∃ (b : Γ(X, V')) (bs : Fin m → Γ(X, V')),
    y = ι (rs h b) * (Matrix.of fun k l => D (κ k) (rs h (bs l))).det}

section KS
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V V' : X.Opens} (h : V ≤ V') {T : Thick (smFun X q)} (hT : InU V T) : InU V' T :=
  fun x hx => h (hT hx)

theorem ks_le (s : ℕ) {V V' : X.Opens} (h : V ≤ V') : KS q s {V} ≤ KS q s {V'} := by
  rintro T ⟨hT, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  subst hW
  exact ⟨hT, V', rfl, inU_mono q h hTW⟩

theorem ks_in (s : ℕ) (V : X.Opens) : ∀ T, KS q s {V} T → InU V T := by
  rintro T ⟨-, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  exact hW ▸ hTW

def resKS (s : ℕ) {V V' : X.Opens} (h : V ≤ V') (r r' : ℤ) (j : ℕ) :
    HQ (KS q s {V'}) r r' j →ₗ[K] HQ (KS q s {V}) r r' j :=
  ((incl (ks_le q s h)).sq (incl_fil _ r) (incl_fil _ r')).pull j

end KS

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem powK_pull {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {C : Type 1} [Category.{0} C]
    (g : C ⥤ Thick (smFun X q)) (c : HdR q 2) (z : CH.Cn (CH.modF (g ⋙ thA (smFun X q))) 2) (hz : CH.d _ 2 z = 0)
    (hcz : (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 c) (k : ℕ) :
    ∃ h, (CH.cx _).cls (cupPowC (g ⋙ thA (smFun X q)) z k) h = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * k) (powK q c k) := by
  induction k with
  | zero =>
    change ∃ h : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0,
      (CH.cx (CH.modF (g ⋙ thA (smFun X q)))).cls (n := 0) (cupPowC (g ⋙ thA (smFun X q)) z 0) h =
        (CH.Mor.restrict (O (smFun X q)) g).hom.mapH 0 (CH.oneH (thA (smFun X q)))
    have h0 : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0 := by
      funext s
      simp only [CH.d, cupPowC, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two]
      simp [CH.modF]
      change (((thA (smFun X q)).map (g.map (GlobalTheory.CatH.toLast 0 s))).hom 1) +
        -(((thA (smFun X q)).map (g.map (GlobalTheory.CatH.toLast 1 s))).hom 1) = 0
      simp only [map_one, add_neg_cancel]
    refine ⟨h0, ?_⟩
    unfold CH.oneH
    exact (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (O (smFun X q)) g).hom 0
      (fun s => (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) _ (by exact h0)).symm
  | succ k ih =>
    obtain ⟨hk, ek⟩ := ih
    obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP (g ⋙ thA (smFun X q))) (show 2 * k + 2 = 2 * (k + 1) by omega)
      (cupPowC (g ⋙ thA (smFun X q)) z k) z hk hz
    refine ⟨hc, ?_⟩
    have key := CrystallineSemistableComparison.P.cup_pull (CH.mulP (thA (smFun X q))) (CH.mulP (g ⋙ thA (smFun X q))) g
      (fun _ => LinearMap.id) (fun _ => LinearMap.id) (fun _ => LinearMap.id)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c
    change _ = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * (k + 1))
      ((CH.mulP (thA (smFun X q))).cup (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c)
    refine (ec.symm.trans ?_).trans key.symm
    rw [ek, hcz]
    rfl

end CrystallineSemistableComparison.Pb
end
end
