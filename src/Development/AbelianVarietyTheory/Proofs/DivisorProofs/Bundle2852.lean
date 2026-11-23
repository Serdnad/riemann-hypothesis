module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem genFibre_endo_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hU
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gA := isGrpPullback_pullback FinalForm.G M.pt
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    gA.congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  have gψ' : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) ρ.P.A (spMap S.R.val.toRingHom)
      (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := gψ.congr (FinalForm.u₀_gen x hx) rfl
  refine ⟨(Over.pullback M.pt).obj FinalForm.G, inferInstance, ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀,
    pullback.fst FinalForm.G.hom M.pt, gψ', gA, ?_, ?_⟩
  · intro e he
    haveI := he
    obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ' e
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    refine ⟨F, hF, fun e₀ he₀ => ?_⟩
    have hw'l : w'.left ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ e.left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    have he₀w : e₀ = w' := hom_ext_of_pullback gψ' (he₀.trans hw'l.symm)
    rw [he₀w, ← hFw]
    simp only [Over.pullback_map_left, pullback.lift_fst]
  · intro b
    have hb : (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (ρ.pt b)]; simp
    let w₀ := gψ'.1.lift _ _ hb
    have hw₁ : w₀ ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = spMap S.R.val.toRingHom ≫ (ρ.pt b).left :=
      gψ'.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ pullback.snd FinalForm.G.hom M.pt = 𝟙 _ := gψ'.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G := Over.homMk w₀ hw₂
    let V : Over.mk M.pt ⟶ Over.mk (𝟙 (Sp Ω) ≫ M.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk M.pt ⟶ FinalForm.G := V ≫ pushPt gA.1.w sec0
    have hgl : gγ.left = w₀ ≫ pullback.fst FinalForm.G.hom M.pt := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : ρ.pt 0 = 1 := by
        have := ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (ρ.pt b) ^ n = ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← ρ.pt_add, succ_nsmul]
      have hrN : (S.r * S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp Ω) ≫ spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) :=
        Over.homMk (spMap S.R.val.toRingHom) (by simp)
      have hs : pushPt gψ'.1.w sec0 = U ≫ ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (S.r * S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective gψ'
        have e1 : pushPt gψ'.1.w (sec0 ^ (S.r * S.N)) = (pushPt gψ'.1.w sec0) ^ (S.r * S.N) :=
          map_pow (pushHom gψ' _) sec0 _
        have e2 : pushPt gψ'.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
          map_one (pushHom gψ' _)
        have e3 : (U ≫ ρ.pt b) ^ (S.r * S.N) = U ≫ (ρ.pt b) ^ (S.r * S.N) :=
          (map_pow (preHom U) (ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp S.R) ⟶ ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (S.r * S.N) = V ≫ (pushPt gA.1.w sec0) ^ (S.r * S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gA.1.w sec0) ^ (S.r * S.N) = pushPt gA.1.w (sec0 ^ (S.r * S.N)) :=
        (map_pow (pushHom gA _) sec0 _).symm
      have f3 : pushPt gA.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
        map_one (pushHom gA _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp Ω) ≫ M.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := gψ'.1.hom_ext (by rw [h2, hw₁]) (by
        show w ≫ pullback.snd FinalForm.G.hom M.pt = w₀ ≫ pullback.snd FinalForm.G.hom M.pt
        rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro z hz
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec z b hz
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_, Category.assoc, hν₁]
      · rw [Category.assoc, ← Category.assoc ν, hν₁, pullback.condition, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc]; exact hw₁

end GlobalTheory.Poinc.FibLat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThickEndo

variable {S S' : Scheme.{0}}

theorem homEquiv_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Hom.mul_def,
    Hom.mul_def, Functor.obj.μ_def, ← comp_lift_assoc, ← Category.assoc (lift _ _),
    Functor.Monoidal.lift_μ, CategoryTheory.Functor.map_comp]

theorem homEquiv_symm_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : X ⟶ (Over.pullback φ).obj A) :
    ((Over.mapPullbackAdj φ).homEquiv X A).symm (a * b) =
      ((Over.mapPullbackAdj φ).homEquiv X A).symm a * ((Over.mapPullbackAdj φ).homEquiv X A).symm b := by
  apply ((Over.mapPullbackAdj φ).homEquiv X A).injective
  rw [homEquiv_mul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

theorem homEquiv_symm_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (q : Y ⟶ (Over.pullback t).obj A) :
    (((Over.mapPullbackAdj t).homEquiv Y A).symm q).left = q.left ≫ pullback.fst A.hom t := by
  have := homEquiv_left' t (((Over.mapPullbackAdj t).homEquiv Y A).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

variable {R : Type} [CommRing R] (I : Ideal R) {B : Type} [CommRing B] [IsLocalRing B]

theorem le_comap_of_mem_range {φ : CommRingCat.of R ⟶ CommRingCat.of B}
    (h : Spec.map φ (closedPoint B) ∈ Set.range (thick R I 0)) :
    I ≤ (maximalIdeal B).comap φ.hom := by
  obtain ⟨y, hy⟩ := h
  intro a ha
  have h1 : a ∈ ((thick R I 0) y).asIdeal := by
    show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)]
    exact zero_mem _
  rw [hy] at h1
  exact h1

def lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ.hom
    ((Ideal.pow_right_mono hI (e + 1)).trans (Ideal.le_comap_pow _ _))))

variable {I}

theorem lev_thick (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    lev I φ hI e ≫ thick R I e = thick B (maximalIdeal B) e ≫ Spec.map φ := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem adicLevelMap_lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom)
    (e : ℕ) : adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ lev I φ hI (e + 1) =
      lev I φ hI e ≫ thickTrans R I e := by
  rw [lev, lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact Ideal.Quotient.ringHom_ext rfl

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

section Main

variable {R : Type} [CommRing R] {I : Ideal R} {G : Over (Sp R)} [GrpObj G] {B : Type} [CommRing B]
  [IsLocalRing B] {φ : CommRingCat.of R ⟶ CommRingCat.of B} (hI : I ≤ (maximalIdeal B).comap φ.hom)

abbrev lvl (e : ℕ) : Over (Sp (R ⧸ I ^ (e + 1))) := Over.mk (lev I φ hI e)

def incl (e : ℕ) : (Over.map (thick R I e)).obj (lvl hI e) ⟶ Over.mk (Spec.map φ) :=
  Over.homMk (thick B (maximalIdeal B) e) (lev_thick φ hI e).symm

def red (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) : lvl hI e ⟶ thickObj R I e G :=
  (Over.mapPullbackAdj (thick R I e)).homEquiv (lvl hI e) G (incl hI e ≫ x)

theorem red_fst (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left :=
  homEquiv_left' _ _

theorem red_snd (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.snd G.hom (thick R I e) = lev I φ hI e :=
  Over.w (red hI e x)

omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [GrpObj G] in
theorem thickMap_snd (e : ℕ) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem red_succ (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ (red hI (e + 1) x).left =
      (red hI e x).left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · rw [Category.assoc, red_fst, Category.assoc, thickMap_fst, red_fst]
    exact adicLevelMap_ι_assoc (maximalIdeal B) (Nat.le_succ (e + 1)) x.left
  · rw [Category.assoc, red_snd, Category.assoc, thickMap_snd, ← Category.assoc, red_snd, adicLevelMap_lev]

variable (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G)

def fam (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ G.left :=
  (red hI e x ≫ b e).left ≫ pullback.fst G.hom (thick R I e)

variable {b}

theorem fam_adic (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : IsAdicFamily (maximalIdeal B) (fam hI b x) := fun e => by
  simp only [fam, Over.comp_left, Category.assoc]
  rw [← Category.assoc (adicLevelMap _ _), red_succ, Category.assoc, ← Category.assoc (thickMap R I e G),
    hb, Category.assoc, thickMap_fst]

variable (b) in
theorem fam_over (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    fam hI b x e ≫ G.hom = adicLevelι (maximalIdeal B) (e + 1) ≫ Spec.map φ := by
  have hw : (b e).left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w (b e)
  simp only [fam, Over.comp_left, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((b e).left), hw, ← Category.assoc, red_snd, lev_thick]

variable [IsAdicComplete (maximalIdeal B) B]

theorem exists_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : ∃ g : Sp B ⟶ G.left, g ≫ G.hom = Spec.map φ ∧
      ∀ e, adicLevelι (maximalIdeal B) (e + 1) ≫ g = fam hI b x e :=
  (existsUnique_over_of_isAdicFamily (Spec.map φ) G.hom (fam_adic hI hb x) (fam_over hI b x)).exists

def lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : Over.mk (Spec.map φ) ⟶ G :=
  Over.homMk (exists_lim hI hb x).choose (exists_lim hI hb x).choose_spec.1

theorem lim_level (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    thick B (maximalIdeal B) e ≫ (lim hI hb x).left = fam hI b x e :=
  (exists_lim hI hb x).choose_spec.2 e

theorem incl_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    incl hI e ≫ lim hI hb x = ((Over.mapPullbackAdj (thick R I e)).homEquiv _ G).symm (red hI e x ≫ b e) := by
  apply Over.OverMorphism.ext
  rw [homEquiv_symm_left', Over.comp_left]
  exact lim_level hI hb x e

theorem lim_mul (hmon : ∀ e, IsMonHom (b e))
    (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x y : Over.mk (Spec.map φ) ⟶ G) : lim hI hb (x * y) = lim hI hb x * lim hI hb y := by
  have he : ∀ e, incl hI e ≫ lim hI hb (x * y) = incl hI e ≫ (lim hI hb x * lim hI hb y) := by
    intro e
    have := hmon e
    rw [comp_mul, incl_lim, incl_lim, incl_lim, red, comp_mul, homEquiv_mul', mul_comp, homEquiv_symm_mul']
    rfl
  exact Over.OverMorphism.ext (hom_ext_of_isHausdorff (maximalIdeal B) fun e => congrArg (·.left) (he e))

end Main

end GlobalTheory.ThickEndo


open GlobalTheory.ThickEndo in
theorem GlobalTheory.exists_mul_map_points_of_thickEndo : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  intro R _ I G _ b hmon hb B _ _ _ s hs
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hI := le_comap_of_mem_range I hs
  refine ⟨lim hI hb, fun x y => lim_mul hI hmon hb x y, fun x e => ⟨(red hI e x).left, red_fst hI e x, ?_⟩⟩
  rw [lim_level hI hb x e]
  simp only [fam, Over.comp_left, Category.assoc]
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.MultPull

open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull

theorem isRatSec_pull_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) :
    IsRatSec (L.pull j) fun c => Units.map (fnMap j hη).toMonoidHom (r (c PUnit.unit)) := by
  intro c c' h
  have l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) := l h
  have h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    (genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁
  have e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  change fnMap j hη (r (c PUnit.unit) : X.functionField) =
    fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) *
      fnMap j hη (r (c' PUnit.unit) : X.functionField)
  rw [hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]
  first
    | exact congrArg (· * _) (fnOf_resG l h _)
    | exact congrArg (· * _) (fnOf_resG l h _).symm

theorem ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) (y : Y)
    [IsIso (j.stalkMap y)] (f : X.functionField) :
    Scheme.ord (fnMap j hη f) y = Scheme.ord f (j y) := by
  let e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a := rfl
  have hc : Order.coheight y = Order.coheight (j y) := by
    have := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this.symm
  by_cases hz : Order.coheight (j y) = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have hz' : Order.coheight y = 1 := hc.trans hz
  have key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) :
      Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y =
        Scheme.ord (algebraMap _ X.functionField a) (j y) := by
    have ha' : j.stalkMap y a ≠ 0 := by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha
    rw [fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb']
  have h₁ := Scheme.ord_mul (x := j y) hf hb'
  have hfm : fnMap j hη f ≠ 0 := (map_ne_zero_iff _ (fnMap j hη).injective).2 hf
  have hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0 :=
    (map_ne_zero_iff _ (fnMap j hη).injective).2 hb'
  have h₂ := Scheme.ord_mul (x := y) hfm hbm
  rw [← map_mul, hfb] at h₂
  rw [hfb] at h₁
  rw [key a ha0, key b hb0] at h₂
  omega

end GlobalTheory.MultPull

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.CompleteNormalDvr

theorem exists_dvr_isCN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  intro R _ _ _ hR
  obtain ⟨h1, h2, h3, h4⟩ := hR
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨g1, g2, g3⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  refine ⟨V, inferInstance, inferInstance, inferInstance, g1, φ, ?_, hφ, hloc⟩
  exact ⟨inferInstance, inferInstance, g2, g3⟩

end GlobalTheory.CompleteNormalDvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C), IsCN R → Function.Injective φ → φ.Finite → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  first | exact @GlobalTheory.LocExt.exists_isCN_cover_of_finite | exact GlobalTheory.LocExt.exists_isCN_cover_of_finite | (intros; apply GlobalTheory.LocExt.exists_isCN_cover_of_finite <;> assumption)
end
