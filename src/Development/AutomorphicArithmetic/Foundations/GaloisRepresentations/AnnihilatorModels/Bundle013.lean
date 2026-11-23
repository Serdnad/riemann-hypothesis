module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

def CongKS : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ → (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) →
    ∀ (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Flat π → ∀ (mπ : ObjMap E.univ M.univ π) (k : ℕ),
    ∃ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j))) (L : ∀ j, TjE E mπ (T j)) (d : Fin (D.n + 1) → ℕ)
      (h : ∀ j, KSOKE (L j) k (d j)), (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (h j).corr.p ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ∧
      PtId p (p ^ f) D.n (fn ((GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ϖ) fun j => (h j).corr

theorem congKS_of (h1 : TjExF) (h2 : TjEEx) (h3 : OrdKSE) (h4 : PtIdOfOrd) : CongKS := by
  intro p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ 𝔞 ρ ha hu E π hπ hf mπ k
  choose T hT using fun j : Fin (D.n + 1) => h1 p D O f b N r w hs M j (Nat.lt_succ_iff.1 j.2)
  have L := fun j : Fin (D.n + 1) => (h2 p D O f b N r w hs M j _ (T j) (hT j) 𝔞 ρ ha hu E π hπ mπ).some
  obtain ⟨d, h, e, ho⟩ := h3 p D O f b N r w hs M ϖ hϖ T 𝔞 ρ E π hπ hf mπ L k
  exact ⟨T, L, d, h, e, h4 _ _ _ _ _ _ ho⟩

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable abbrev resU {V : Type} [CommRing V] [IsDomain V] {S : Scheme.{0}} (z : Sp V ⟶ S) :
    Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
  Over.homMk (spMap (algebraMap V (FractionRing V))) rfl

private theorem res_inj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S) {g g' : Over.mk z ⟶ A}
    (e : resU z ≫ g = resU z ≫ g') : g = g' := by
  apply Over.OverMorphism.ext
  have e' := congrArg CommaMorphism.left e
  simp only [Over.comp_left, Over.homMk_left] at e'
  exact (hV S A.left A.hom hA V z).1 g.left g'.left (by simpa using Over.w g)
    (by simpa using Over.w g') e'

private theorem res_surj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S)
    (g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A) :
    ∃ g' : Over.mk z ⟶ A, resU z ≫ g' = g := by
  obtain ⟨l, h₁, h₂⟩ := (hV S A.left A.hom hA V z).2 g.left (by simpa using Over.w g)
  exact ⟨Over.homMk l h₁, Over.OverMorphism.ext h₂⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.wVal_of :
    ValPtsX → WVal := by
  intro hV p _ D R _ b N M w V _ _ _ x
  have hU : IsProper M.univ.A.hom := @IsAbelianScheme.proper _ M.univ.A M.univ.grp M.univ.ab
  let φ : (Over.mk x ⟶ M.univ.A) →* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A) :=
    { toFun := fun g => resU x ≫ g
      map_one' := comp_one _
      map_mul' := fun g h => comp_mul _ g h }
  let ρ := MulEquiv.ofBijective φ
    ⟨fun g g' e => res_inj hV hU x e, fun g => res_surj hV hU x g⟩
  have hρ : ∀ g, ρ g = resU x ≫ g := fun _ => rfl
  refine ⟨ρ, ?_⟩
  simp only [hρ]
  refine ⟨fun g => by simp, fun g a => (Category.assoc _ _ _).symm, fun g => ?_, ?_⟩
  · constructor
    · intro hg a ha
      rw [Category.assoc, hg a ha, comp_one]
    · intro hg a ha
      apply res_inj hV hU x
      rw [comp_one, ← Category.assoc]
      exact hg a ha
  · intro r j c T z hz g
    have hO : IsProper T.o.A.hom := @IsAbelianScheme.proper _ T.o.A T.o.grp T.o.ab
    have hO' : IsProper T.o'.A.hom := @IsAbelianScheme.proper _ T.o'.A T.o'.grp T.o'.ab
    constructor
    · intro hk b' hb'
      obtain ⟨a', ha'⟩ := res_surj hV hO z b'
      have ha2 := congrArg CommaMorphism.left ha'
      simp only [Over.comp_left, Over.homMk_left] at ha2
      have hb2 : b'.left ≫ T.ms.φ = spMap (algebraMap V (FractionRing V)) ≫ g.left := by
        simpa using hb'
      have hw : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
        rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
        exact hz
      have key : (Over.homMk (a'.left ≫ T.ms.φ) hw : Over.mk x ⟶ M.univ.A) = g := by
        apply res_inj hV hU x
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        rw [← Category.assoc, ha2, hb2]
      have hg : a'.left ≫ T.ms.φ = g.left := by
        rw [← key]
        simp
      rw [← ha', Category.assoc, hk a' hg, comp_one]
    · intro hk a' ha'
      apply res_inj hV hO' z
      rw [comp_one, ← Category.assoc]
      apply hk
      simp [ha']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.levPull_of :
    PullKer → LevPull := by
  intro _ p _ D R _ b N S S' s s' f o o₁ m 𝔞 ρ lv h
  exact GlobalTheory.UPel.HT.EtLev.isEtLev_exists_pull m h
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.grCard_of :
    GrCard := by
  intro k H _ _ _ _ n j hn
  have hdim : Module.finrank k H = Module.finrank k (Fin n → k) := by simp [hn]
  let e : H ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq H (Fin n → k) hdim
  apply Nat.card_congr
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro D
  change Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j
  rw [LinearEquiv.finrank_map_eq]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma exists_alg {κ B Λ : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing Λ] [Algebra κ Λ]
    (u : Sp Λ ⟶ Sp B) (h : u ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ)) :
    ∃ ν : B →ₐ[κ] Λ, u = spMap ν.toRingHom := by
  obtain ⟨φ, rfl⟩ : ∃ φ, u = Spec.map φ := ⟨Spec.preimage u, (Spec.map_preimage u).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ Λ := by
    have h' : Spec.map (CommRingCat.ofHom (algebraMap κ B) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Λ)) := by
      rw [Spec.map_comp]
      exact h
    have h'' := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom h''
  refine ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, ?_⟩
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.infE_of :
    SplitAlg → InfE := by
  intro hS κ _ A _ P d hRep hcard Λ _ _ _ ε g hP hInf
  obtain ⟨B, _, _, hfin, hfree, hrank, i, hmono, hiff⟩ := hRep
  haveI : Mono i := hmono
  have key : ∀ (Λ' : Type) [CommRing Λ'] [Algebra κ Λ'] (ν : B →ₐ[κ] Λ'),
      spMap ν.toRingHom ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ') := by
    intro Λ' _ _ ν
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  have hid : spMap (algebraMap κ κ) = 𝟙 (Sp κ) := by simp [spMap]
  let F : (B →ₐ[κ] κ) → { g // P (𝟙_ (Over (Sp κ))) g } := fun ν =>
    ⟨Over.homMk (U := 𝟙_ (Over (Sp κ))) (V := algPt κ B) (spMap ν.toRingHom)
        (by
          show spMap ν.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
          rw [key κ ν, hid]) ≫ i,
      (hiff _ _).1 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro ν₁ ν₂ h
      have h1 := congrArg Subtype.val h
      have h2 := (cancel_mono i).1 h1
      have h3 := congrArg CommaMorphism.left h2
      have h4 : CommRingCat.ofHom ν₁.toRingHom = CommRingCat.ofHom ν₂.toRingHom :=
        Spec.map_injective h3
      ext x
      exact congrArg (fun φ => φ.hom x) h4
    · rintro ⟨g₀, hg₀⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg₀
      obtain ⟨ν, hν⟩ := exists_alg (Λ := κ) y.left (by
        rw [hid]
        exact Over.w y)
      refine ⟨ν, Subtype.ext ?_⟩
      show _ ≫ i = g₀
      rw [← hy]
      congr 1
      apply Over.OverMorphism.ext
      simp [hν]
  have hpts : Nat.card (B →ₐ[κ] κ) = Module.finrank κ B := by
    rw [hrank, ← hcard]
    exact Nat.card_congr (Equiv.ofBijective F hF)
  obtain ⟨y, hy⟩ := (hiff _ _).2 hP
  obtain ⟨ν, hν⟩ := exists_alg y.left (Over.w y)
  have hsplit := hS κ B Λ hpts ε ν
  have e1 : spMap ν.toRingHom = spMap (algebraMap κ Λ) ≫ spMap (ε.comp ν).toRingHom := by
    conv_lhs => rw [hsplit]
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e2 : spMap ε.toRingHom ≫ spMap (algebraMap κ Λ) = 𝟙 (Sp κ) := by
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show ε.toRingHom.comp (algebraMap κ Λ) = RingHom.id κ from by ext r; simp]
    simp
  have gl : g.left = y.left ≫ i.left := by
    rw [← hy]
    rfl
  have one_l : ∀ T : Over (Sp κ), (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
    intro T
    show (toUnit T ≫ η[A]).left = _
    rw [Over.comp_left]
    congr 1
  have hI : spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left := hInf
  rw [one_l, gl, hν, e1] at hI
  simp only [← Category.assoc, e2, Category.id_comp] at hI
  apply Over.OverMorphism.ext
  rw [one_l, gl, hν, e1, Category.assoc, hI]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

private theorem spMap_inj' {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'} (h : spMap f = spMap g) : f = g := by
  have h' := Spec.map_injective h
  ext x
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) h'

private theorem spMap_algComp {V B C D : Type} [CommRing V] [CommRing B] [CommRing C] [CommRing D] [Algebra V B] [Algebra V C]
    [Algebra V D] (a : C →ₐ[V] D) (b : B →ₐ[V] C) :
    spMap (a.comp b).toRingHom = spMap a.toRingHom ≫ spMap b.toRingHom := by
  rw [spMap_comp']; rfl

private theorem pt_alg {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    (w : algPt V Λ ⟶ algPt V B) : ∃ ν : B →ₐ[V] Λ, w.left = spMap ν.toRingHom := by
  have e : Spec.map (CommRingCat.ofHom (Spec.preimage w.left).hom) = w.left := by
    simp
  have hw := Over.w w
  have key : (Spec.preimage w.left).hom.comp (algebraMap V B) = algebraMap V Λ := by
    apply spMap_inj'
    rw [← spMap_comp']
    change Spec.map (CommRingCat.ofHom (Spec.preimage w.left).hom) ≫ spMap (algebraMap V B) = spMap (algebraMap V Λ)
    rw [e]
    simpa using hw
  exact ⟨{ (Spec.preimage w.left).hom with commutes' := fun r => congrArg (fun φ => φ r) key }, e.symm⟩

private noncomputable def ptOf {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    (ν : B →ₐ[V] Λ) : algPt V Λ ⟶ algPt V B :=
  Over.homMk (spMap ν.toRingHom) (by
    show spMap ν.toRingHom ≫ spMap (algebraMap V B) = spMap (algebraMap V Λ)
    rw [spMap_comp']
    congr 1
    exact ν.comp_algebraMap)

private theorem surj_of_mono {κ B B' : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing B'] [Algebra κ B'] [Module.Finite κ B']
    (π : B →ₐ[κ] B') (h : Mono (spMap π.toRingHom)) : Function.Surjective π := by
  have hm : Mono (CommRingCat.ofHom π.toRingHom).op :=
    Functor.mono_of_mono_map Scheme.Spec (f := (CommRingCat.ofHom π.toRingHom).op) h
  have he : Epi (CommRingCat.ofHom π.toRingHom) := (op_mono_iff _).mp hm
  have hfin : π.toRingHom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := algebraMap κ B)
    convert RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite κ B') using 1
    exact π.comp_algebraMap
  exact RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom π.toRingHom) hfin

end UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_integer_mul_eq_of_valuation_le {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    {A : Over (Sp V)} (i : algPt V B ⟶ A) [Mono i] {φ ψ : B →ₐ[V] Λ}
    (h : spMap φ.toRingHom ≫ i.left = spMap ψ.toRingHom ≫ i.left) : φ = ψ := by
  haveI := Over.mono_left_of_mono i
  have h1 := Mod.spMap_inj' ((cancel_mono i.left).mp h)
  ext x
  exact RingHom.congr_fun h1 x

private theorem inSub_iff_exists_algHom_factor {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    {A : Over (Sp V)} (i : algPt V B ⟶ A) (g : algPt V Λ ⟶ A) :
    InSub i g ↔ ∃ ν : B →ₐ[V] Λ, g.left = spMap ν.toRingHom ≫ i.left := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨ν, hν⟩ := Mod.pt_alg y
    exact ⟨ν, by rw [← hy, Over.comp_left, hν]⟩
  · rintro ⟨ν, hν⟩
    exact ⟨Mod.ptOf ν, Over.OverMorphism.ext (by rw [Over.comp_left, hν]; rfl)⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.infW_of :
    RingHomog → CotanOne → ChainRing → RepHomog → FrobRing → InfW := by
  intro hRH hCO hCR hRP hFR
  intro p f hp κ _ _ _ A _ P P' d d' hRA hSub hcard hd hRA' hle hTan Λ _ _ _ ε g hP'g hInf
  obtain ⟨B, _, _, hBfin, hBfree, hBrank, i, hi, hiP⟩ := hRA
  obtain ⟨B', _, _, hB'fin, _, _, i', hi', hiP'⟩ := hRA'
  obtain ⟨hcardB, ε₀, hInf0, htrans⟩ := hRP κ A P hSub B i hi hiP
  haveI : (RingHom.ker ε₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hq := hRH κ B ε₀ htrans
  rw [hBrank, hcardB, hcard] at hq
  have hq' : Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) = p ^ f :=
    (Nat.eq_of_mul_eq_mul_right hd (hq.trans (mul_comm _ _))).symm
  obtain ⟨j, hj⟩ : InSub i' i := (hiP' _ i).mpr (hle _ i ((hiP _ i).mp ⟨𝟙 _, Category.id_comp _⟩))
  obtain ⟨π, hπ⟩ := Mod.pt_alg j
  haveI : Mono j := mono_of_mono_fac hj
  haveI := Over.mono_left_of_mono j
  have hπs : Function.Surjective π := Mod.surj_of_mono π (by rw [← hπ]; infer_instance)
  haveI := Over.mono_left_of_mono i'
  have hiL : i.left = spMap π.toRingHom ≫ i'.left := by rw [← hj, Over.comp_left, hπ]
  obtain ⟨ν', hν'⟩ := (inSub_iff_exists_algHom_factor i' g).mp ((hiP' _ g).mpr hP'g)
  have hInf0' : Inf (ε₀.comp π) i' := by
    unfold Inf at hInf0 ⊢
    rw [Mod.spMap_algComp, Category.assoc, ← hiL]
    exact hInf0
  have hεν : ε.comp ν' = ε₀.comp π := by
    apply exists_integer_mul_eq_of_valuation_le i'
    unfold Inf at hInf hInf0'
    rw [Mod.spMap_algComp, Category.assoc, ← hν', hInf, ← hInf0', Mod.spMap_algComp, Category.assoc]
  obtain ⟨v₀, hv₀P, hv₀I, hv₀⟩ := hTan
  obtain ⟨m₀, hm₀⟩ := (inSub_iff_exists_algHom_factor i' v₀).mp ((hiP' _ v₀).mpr hv₀P)
  have hcot := hCO κ B' (ε₀.comp π) m₀ (by
    intro v hv
    have hvI : Inf (TrivSqZeroExt.fstHom κ κ κ) (Mod.ptOf v ≫ i') := by
      unfold Inf at hInf0' ⊢
      rw [Over.comp_left]
      change spMap _ ≫ spMap v.toRingHom ≫ i'.left = _
      rw [← Category.assoc, ← Mod.spMap_algComp, hv]
      exact hInf0'
    obtain ⟨c, hc⟩ := hv₀ _ ((hiP' _ _).mp ⟨Mod.ptOf v, rfl⟩) hvI
    rw [hm₀, Over.comp_left, ← Category.assoc, Mod.spMap_comp'] at hc
    have hr := Mod.spMap_inj' ((cancel_mono i'.left).mp hc)
    refine ⟨c, fun x => ?_⟩
    have hx := RingHom.congr_fun hr x
    change v x = (epsScale c) (m₀ x) at hx
    rw [hx]
    simp [epsScale])
  have hch := hCR κ B' B Λ π ε₀ (p ^ f) hπs hq' hcot ε ν' hεν
  have hfr := hFR p f hp κ A B' Λ i' hi' (ε₀.comp π) hInf0' ν' g hν'
  rw [hfr, ← hiP]
  refine Iff.trans ?_ hch
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨m, hm⟩ := Mod.pt_alg y
    have hνm : ν' = m.comp π := exists_integer_mul_eq_of_valuation_le i' (by
      rw [← hν', ← hy, Over.comp_left, hm, hiL, Mod.spMap_algComp, Category.assoc])
    intro x hx
    rw [hνm, AlgHom.comp_apply, hx, map_zero]
  · intro hk
    let e := Ideal.quotientKerAlgEquivOfSurjective hπs
    let m : B →ₐ[κ] Λ := (Ideal.Quotient.liftₐ (RingHom.ker π) ν' (fun a ha => hk a ha)).comp e.symm.toAlgHom
    have hm : m.comp π = ν' := by
      ext x
      have he : e.symm (π x) = Ideal.Quotient.mk (RingHom.ker π) x := by
        rw [AlgEquiv.symm_apply_eq]
        rfl
      change (Ideal.Quotient.liftₐ (RingHom.ker π) ν' (fun a ha => hk a ha)) (e.symm (π x)) = ν' x
      rw [he]
      rfl
    refine ⟨Mod.ptOf m, Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left]
    change spMap m.toRingHom ≫ i.left = g.left
    rw [hν', hiL, ← Category.assoc, ← Mod.spMap_algComp, hm]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.algOf_of :
    AlgOf := by
  intro S K h hfin hflat V _ _ z
  let h' : pullback h z ⟶ Sp V := pullback.snd h z
  haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin
  haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat
  haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'
  let φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤) := (Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop
  letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra
  have hfinite : φ.hom.Finite := by
    have h1 : h'.appTop.hom.Finite := Scheme.Hom.finite_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hflat' : φ.hom.Flat := by
    have h1 : h'.appTop.hom.Flat := Scheme.Hom.flat_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)
    exact RingHom.Flat.comp h2 h1
  haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite
  haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'
  refine ⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf,
    Module.free_of_flat_of_isLocalRing, ?_⟩
  have key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩
  have := sq.paste_horiz (IsPullback.of_hasPullback h z)
  rwa [Category.id_comp] at this
end
