module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_coprime_mul_le {A : Type} [CommRing A] [IsDedekindDomain A] (𝔞 J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (m : ℕ) (𝔟 : Ideal A), IsCoprime 𝔞 𝔟 ∧ 𝔞 ^ m * 𝔟 ≤ J := by
  classical
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ u hu =>
    refine ⟨0, ⊤, Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq _), ?_⟩
    rw [Ideal.isUnit_iff.mp hu]; exact le_top
  | h₃ a p ha hp ih =>
    have ha0 : a ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    have hp0 : p ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    obtain ⟨m, b, hcop, hle⟩ := ih ha0
    by_cases hap : 𝔞 ≤ p
    · refine ⟨m + 1, b, hcop, ?_⟩
      calc 𝔞 ^ (m + 1) * b = 𝔞 * (𝔞 ^ m * b) := by rw [pow_succ', _root_.mul_assoc]
        _ ≤ p * a := Ideal.mul_mono hap hle
    · have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have hc : IsCoprime 𝔞 p := by
        rw [Ideal.isCoprime_iff_sup_eq]
        by_contra h
        have h2 := hpm.eq_of_le h le_sup_right
        exact hap (h2 ▸ le_sup_left)
      refine ⟨m, p * b, IsCoprime.mul_right hc hcop, ?_⟩
      calc 𝔞 ^ m * (p * b) = p * (𝔞 ^ m * b) := by ring
        _ ≤ p * a := Ideal.mul_mono_right hle

theorem UpperTheory.Gal.crystallineComparison.Mod.idealSplit_of :
    IdealSplit := by
  intro A _ _ 𝔞 x hx ρ
  have hJ : Ideal.span {x} ≠ ⊥ := by simpa using hx
  obtain ⟨m, 𝔟, hc, hle⟩ := exists_coprime_mul_le 𝔞 (Ideal.span {x}) hJ
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp (hc.pow_left (m := ρ))
  refine ⟨m, j, ?_, fun a ha => hle (Ideal.mul_mem_mul ha hj)⟩
  have : j - 1 = -i := by rw [← hij]; ring
  rw [this]
  exact neg_mem hi
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def powSuccIso {S : Scheme.{0}} (A : Over S) (k : ℕ) :
    GlobalTheory.KS.pow A (k + 1) ≅ A ⨯ GlobalTheory.KS.pow A k :=
  let f : GlobalTheory.KS.pow A (k + 1) ⟶ A := Pi.π _ 0
  let g : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
    Pi.lift fun i : Fin k => Pi.π (fun _ : Fin (k + 1) => A) i.succ
  have hf : Limits.prod.lift f g ≫ Limits.prod.fst = f := Limits.prod.lift_fst f g
  have hg : Limits.prod.lift f g ≫ Limits.prod.snd = g := Limits.prod.lift_snd f g
  have hgi (i : Fin k) : g ≫ Pi.π (fun _ : Fin k => A) i = Pi.π (fun _ : Fin (k + 1) => A) i.succ :=
    Pi.lift_comp_π _ _
  let b : A ⨯ GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A (k + 1) :=
    Pi.lift (Fin.cases Limits.prod.fst (fun i => Limits.prod.snd ≫ Pi.π _ i))
  have hb0 : b ≫ Pi.π (fun _ : Fin (k + 1) => A) 0 = Limits.prod.fst := Pi.lift_comp_π _ _
  have hbs (i : Fin k) : b ≫ Pi.π (fun _ : Fin (k + 1) => A) i.succ =
      Limits.prod.snd ≫ Pi.π (fun _ : Fin k => A) i := Pi.lift_comp_π _ _
  { hom := Limits.prod.lift f g
    inv := b
    hom_inv_id := by
      apply Pi.hom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Category.assoc, hb0, hf, Category.id_comp]
      · rw [Category.assoc, hbs, ← Category.assoc, hg, hgi, Category.id_comp]
    inv_hom_id := by
      apply Limits.prod.hom_ext
      · rw [Category.assoc, hf, Category.id_comp]
        exact hb0
      · rw [Category.assoc, hg, Category.id_comp]
        apply Pi.hom_ext
        intro i
        rw [Category.assoc, hgi, hbs] }

private theorem flat_pow {S : Scheme.{0}} (A : Over S) (h : Flat A.hom) :
    ∀ k, Flat (GlobalTheory.KS.pow A k).hom
  | 0 => by
    have t : IsTerminal (GlobalTheory.KS.pow A 0) :=
      IsTerminal.ofUniqueHom (fun Y => Pi.lift (fun i => i.elim0))
        (fun Y m => Pi.hom_ext _ _ (fun i => i.elim0))
    let e := t.uniqueUpToIso Over.mkIdTerminal
    have h1 : (GlobalTheory.KS.pow A 0).hom = e.hom.left := by simpa using (Over.w e.hom).symm
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance
  | k + 1 => by
    haveI := flat_pow A h k
    let e := powSuccIso A k
    have h1 : (GlobalTheory.KS.pow A (k + 1)).hom = e.hom.left ≫ (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom ≫
        pullback.fst A.hom (GlobalTheory.KS.pow A k).hom ≫ A.hom := by
      rw [← Category.assoc (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom, Over.prodLeftIsoPullback_hom_fst]
      simp
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.powExt_of :
    PowExt := by
  intro S A k
  refine ⟨fun h => flat_pow A inferInstance k, ?_⟩
  intro X u v h1 h2
  exact GlobalTheory.KS.PowPB.pow_left_hom_ext u v h1 h2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w 𝔞 : Ideal (𝓞 D.F)} {j c ρ : ℕ}
  {E : EtModel b N 𝔞 ρ} {π : E.X ⟶ M.X} {mπ : ObjMap E.univ M.univ π} {T : TjD M r w j c}

private theorem pm_hom {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A' m).hom ≫ f := by
  unfold GlobalTheory.KS.powMap
  exact Over.w _

private theorem pm_pr {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pr A i).left = (GlobalTheory.KS.pr A' i).left ≫ φ := by
  simp only [GlobalTheory.KS.powMap, GlobalTheory.KS.pr, ← Over.comp_left, Pi.lift_comp_π, Over.homMk_left]

private theorem ksR_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.t := by
  unfold TjE.ksR
  rw [Category.assoc, pm_hom, ← Category.assoc, Over.w]

private theorem ksR_pr (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ψ.left ≫ L.mt.φ := by
  rw [TjE.ksR, Category.assoc, pm_pr, ← Category.assoc, ← Over.comp_left, Pi.map_π, Over.comp_left, Category.assoc]

private theorem localMap_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.s := pm_hom _ _ _ _

private theorem localMap_projection (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ms.φ := pm_pr _ _ _ _ _

private theorem ks_pb (L : TjE E mπ T) (k : ℕ) :
    IsPullback (L.ksP k) ((GlobalTheory.KS.pow L.o.A k).hom ≫ L.g) ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) T.s := by
  rw [TjE.ksP]
  exact (GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback _ _ _ _ _ _ _ L.ms.cart.1 k).paste_vert L.pb

private theorem img_of (L : TjE E mπ T) {X : Scheme.{0}} (c : X ⟶ L.o.A.left) (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left)
    (hz : z = c ≫ L.o.A.hom ≫ L.g) (ha : a = c ≫ L.ms.φ ≫ mπ.φ) (e : a ≫ M.univ.A.hom = z ≫ T.s) :
    T.img z a e = c ≫ L.ψ.left ≫ L.mt.φ ≫ mπ.φ := by
  have key : ∀ hp : IsPullback T.ms.φ T.o.A.hom M.univ.A.hom T.s, hp.lift a z e = c ≫ L.m₀.φ := by
    intro hp
    apply hp.hom_ext
    · rw [hp.lift_fst, Category.assoc, L.tri, ha]
    · rw [hp.lift_snd, Category.assoc, L.m₀.cart.1.w, hz]
  rw [TjD.img, key]
  simp only [Category.assoc]
  rw [← Category.assoc L.m₀.φ, L.sq]
  simp only [Category.assoc]
  rw [L.tri']

end

theorem UpperTheory.Gal.crystallineComparison.Mod.ordKSE_of :
    CorrBC → OrdEmb → PowExt → EtInj → OrdKSE := by
  intro hBC hOE hPE hEI p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ T 𝔞 ρ E π hπ hfl mπ L k
  have hK : ∀ j : Fin (D.n + 1), KSOKE (L j) k (Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ))) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hBC p D O f b N r w hs M j (Nat.le_of_lt_succ j.isLt) (T j) _ _ _ _ _ (ks_pb (L j) k)
    exact ⟨h1, h2, h3⟩
  have heq : ∀ j, (L j).t ≫ E.s = (L j).s ≫ E.s := by
    intro j
    calc (L j).t ≫ E.s = (L j).t ≫ π ≫ M.s := by rw [hπ]
      _ = (L j).g ≫ (T j).t ≫ M.s := by rw [← Category.assoc, (L j).tπ, Category.assoc]
      _ = (L j).g ≫ (T j).s ≫ M.s := by rw [(T j).st]
      _ = (L j).s ≫ π ≫ M.s := by rw [← Category.assoc, ← (L j).pb.w, Category.assoc]
      _ = (L j).s ≫ E.s := by rw [hπ]
  refine ⟨fun j => Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ)), hK, ?_, ?_⟩
  · intro j
    change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s
    rw [← Category.assoc, ksR_hom, ← Category.assoc ((L j).ksP k), localMap_hom, Category.assoc, Category.assoc, heq j]
  · have hsm : Smooth E.univ.A.hom := @IsAbelianScheme.smooth _ _ _ E.univ.ab
    obtain ⟨hfl', hinj⟩ := hPE E.X E.univ.A k
    have hflat : Flat ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) := by
      haveI := hfl' hsm
      infer_instance
    have hM : ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) ≫ M.s = (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s := by
      rw [Category.assoc, hπ]
    rw [← hM]
    refine hOE p D O f b N r w hs M ϖ hϖ T _ _ hflat (Fin k ⊕ D.La)
      (Sum.elim (fun i => (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ)
        (fun y => (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ)) ?_ ?_ (fun j => (hK j).corr)
      (fun j => (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) (fun j => ks_pb (L j) k) ?_ ?_
    · rintro (i | y)
      · simp only [Sum.elim_inl]
        rw [Category.assoc, mπ.cart.1.w, ← Category.assoc, Over.w]
      · simp only [Sum.elim_inr]
        rw [Category.assoc, Category.assoc, mπ.cart.1.w, ← Category.assoc (E.lv y).left, Over.w]
        simp
    · intro X u v huv hi
      have h0 : u ≫ (GlobalTheory.KS.pow E.univ.A k).hom = v ≫ (GlobalTheory.KS.pow E.univ.A k).hom :=
        hEI p D O b N hs.three hs.cop M 𝔞 ρ E π hπ mπ X _ _ (by simpa [Category.assoc] using huv)
          (fun y => by simpa [Category.assoc] using hi (Sum.inr y))
      apply hinj X u v h0
      intro i
      apply mπ.cart.1.hom_ext
      · simpa [Category.assoc] using hi (Sum.inl i)
      · simp only [Category.assoc, Over.w]
        exact h0
    · intro j
      change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ π = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) ≫ (T j).t
      rw [← Category.assoc, ksR_hom, Category.assoc, (L j).tπ]
      simp only [Category.assoc]
    · intro j i e
      rcases i with i | y
      · have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [← Category.assoc, Over.w]
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc, localMap_projection, Category.assoc]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc, ksR_pr]
          simp only [Category.assoc]
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm
      · obtain ⟨l, hl⟩ : ∃ l : 𝟙_ (Over (L j).Z) ⟶ (L j).o.A, l.left ≫ (L j).ms.φ = (L j).s ≫ (E.lv y).left := by
          refine ⟨Over.homMk ((L j).ms.cart.1.lift ((L j).s ≫ (E.lv y).left) (𝟙 _) ?_) ?_, ?_⟩
          · rw [Category.assoc, Over.w]
            simp
          · rw [IsPullback.lift_snd]
            simp
          · simp
        have hlev := (L j).lev y l hl
        have hlev' : l.left ≫ (L j).ψ.left ≫ (L j).mt.φ = (L j).t ≫ (E.lv y).left := by
          rw [← Category.assoc, ← Over.comp_left]
          exact hlev
        have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [Category.assoc, ← Category.assoc l.left, Over.w]
          simp
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksP k), localMap_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hl]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksR k), ksR_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hlev']
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secCard_of :
    SecCard := by
  intro p _ D R _ b N M r w j c T hm K _ _ hp x y hxy
  subst hxy
  let β : R →+* K := (Spec.preimage (y ≫ T.s ≫ M.s)).hom
  haveI : CharZero K := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · exfalso
      have hcast : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      by_cases hqp : ringChar K = p
      · rw [hqp] at hcast
        exact hp hcast
      · have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hq (Fact.out)).mpr hqp
        have hu := (b.unit _ hcop).map β
        rw [map_natCast, hcast] at hu
        exact not_isUnit_zero hu
    · haveI : CharP K 0 := ringChar.of_eq hq
      exact CharP.charP_to_charZero K
  obtain ⟨-, hcard⟩ := T.tj K y
  rw [hm, Nat.one_mul] at hcard
  rw [← hcard]
  symm
  have hK : ∀ a : Over.mk y ⟶ T.o.A,
      KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a) := by
    intro a
    unfold KilledBy
    refine forall₂_congr (fun c _ => ?_)
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]
  have hker : ∀ a : Over.mk y ⟶ T.o.A,
      KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1 := by
    intro a
    rw [ObjMap.ptEquiv_left]
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have ha : a' = a := by
        apply (T.ms.ptEquiv (Over.mk y)).injective
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']
      rw [ha]
      exact h
  refine Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))
  exact ⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem img_comp (T : TjD M r w j c) {X X' : Scheme.{0}} (u : X' ⟶ X) (z : X ⟶ T.Y)
    (a : X ⟶ M.univ.A.left) (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : (u ≫ a) ≫ M.univ.A.hom = (u ≫ z) ≫ T.s) :
    u ≫ T.img z a h = T.img (u ≫ z) (u ≫ a) h' := by
  unfold TjD.img
  rw [← Category.assoc]
  congr 1
  apply T.ms.cart.1.hom_ext <;> simp

private theorem img_congr (T : TjD M r w j c) {X : Scheme.{0}} {z z' : X ⟶ T.Y}
    {a a' : X ⟶ M.univ.A.left} (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : a' ≫ M.univ.A.hom = z' ≫ T.s) (hz : z = z') (ha : a = a') :
    T.img z a h = T.img z' a' h' := by
  subst hz; subst ha; rfl

end

private theorem resPt_apply (V : Type) [CommRing V] [IsLocalRing V]
    (q : Spec (CommRingCat.of (IsLocalRing.ResidueField V))) :
    (resPt V) q = IsLocalRing.closedPoint V := by
  have : q = IsLocalRing.closedPoint (IsLocalRing.ResidueField V) := Subsingleton.elim _ _
  subst this
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.ordEmb_of :
    OrdGen → GenDown → ResClosed → OrdReadOf → EW → OrdEmb := by
  intro hOG hGD hRC hOR hEW
  intro p _ D O _ _ _ _ f b N r w _ hS M ϖ hϖ T Y h hflat I a ha hsep C g hpb hr himg
  intro V _ _ _ _ hpV y hgen φ hφ
  haveI := hRC V
  obtain ⟨hcl, hmax⟩ := hGD O ϖ hϖ M.X Y M.s h hflat _ hgen
  have hi : 0 < D.a := by rw [hS.a1]; exact Nat.one_pos
  have hcom : (IsLocalRing.maximalIdeal O).comap (b.t ⟨0, hi⟩) = w := by
    symm
    refine Ideal.IsMaximal.eq_of_le inferInstance ?_ fun x hx => hS.tw _ x hx
    exact Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hord : IsWOrd M.univ w (resPt V ≫ y ≫ h) := by
    refine hOG p D O b N hS.three hS.cop hS.pmem hS.m1 ⟨0, hi⟩ w hcom M _ hcl hmax _ _ fun q => ?_
    simp only [Scheme.Hom.comp_apply, resPt_apply]
    rfl
  obtain ⟨H, _, _, _, C₀, e, hfr, hfr1, hA, hB⟩ := hEW p D O f b N r w hS M T V hpV (y ≫ h)
    hcl hord φ hφ
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← hS.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let s : ∀ j, (C j).Sec y ≃ {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = y ≫ h} := fun j =>
    { toFun := fun z => ⟨z.1 ≫ g j, by rw [Category.assoc, ← (hpb j).w, ← Category.assoc, z.2]⟩
      invFun := fun z => ⟨(hpb j).lift y z.1 z.2.symm, (hpb j).lift_fst _ _ _⟩
      left_inv := fun z => Subtype.ext ((hpb j).hom_ext (by simpa using z.2.symm) (by simp))
      right_inv := fun z => Subtype.ext ((hpb j).lift_snd _ _ _) }
  have key : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I) (e),
      resPt V ≫ z.1 ≫ (C j).r ≫ a i = (T j).img (resPt V ≫ z.1 ≫ g j) (resPt V ≫ y ≫ a i) e := by
    intro j z i e
    have e0 : ((C j).p ≫ a i) ≫ M.univ.A.hom = g j ≫ (T j).s := by
      rw [Category.assoc, ha, (hpb j).w]
    rw [himg j i e0]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (img_comp (T j) (resPt V ≫ z.1) (g j) _ e0
      (by simp only [Category.assoc]; rw [ha, (hpb j).w])).trans ?_
    refine img_congr _ _ _ (by simp) ?_
    simp only [Category.assoc]
    rw [← Category.assoc z.1, z.2]
  have hae : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I),
      (resPt V ≫ y ≫ a i) ≫ M.univ.A.hom = (resPt V ≫ z.1 ≫ g j) ≫ (T j).s := by
    intro j z i
    simp only [Category.assoc]
    rw [ha, ← (hpb j).w, ← Category.assoc z.1, z.2]
  refine hOR (p ^ f) D.n _ (twist φ Y) _ _ (𝓞 D.F ⧸ w) H C₀ (fun j => (s j).trans (e j)) hcard hfr hfr1 ?_ ?_
  · intro j z z' h1 h2 h3
    obtain ⟨t1, t2⟩ := hA j (s j z) (s j z') h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t = resPt V ≫ (z'.1 ≫ g j) ≫ (T j).t := t1
      simp only [Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [Category.assoc]
      rw [key j z i (hae j z i), key j z' i (hae j z' i)]
      exact t2 _ _ _
  · intro j j' z z' hj h1 h2 h3
    obtain ⟨t1, t2⟩ := hB j j' (s j z) (s j' z') hj h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t =
          spMap φ ≫ resPt V ≫ (z'.1 ≫ g j') ≫ (T j').t := t1
      simp only [twist, Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [twist, Category.assoc]
      rw [key j z i (hae j z i), key j' z' i (hae j' z' i)]
      exact t2 _ _ _
end
