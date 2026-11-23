module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle132
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointNthMultipleGaloisFixedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add (f := _)]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.low_eq_of_match : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  intro o _ ζ n L hn hζ hnu I _ ε V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂ hω hM he
    hco hlev
  have himg : ∀ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), QImg b φ p₁ p₂ → p₂.y = φ p₁.y →
      p₂.g.b.left = p₁.g.b.left ≫ b.left := by
    rintro p₁ p₂ ⟨p', hp'y, hact, heqv⟩ hy
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hτ₂ F n (by omega) p' p₂ (hp'y.trans hy.symm) heqv
    rw [← hg, hact.1, Over.comp_left]
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  set t₁ : Sp V ⟶ L.F.X := spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₁
  set t₂ : Sp V ⟶ L.F.X := spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₂
  let a₁ : D₁.P.A.left ⟶ L.F.univ.A.left := β₁ ≫ L.β
  let a₂ : D₁.P.A.left ⟶ L.F.univ.A.left := b.left ≫ β₂ ≫ L.β
  let bb : (G2 D₁.P.A).left ⟶ (G2 D₂.P.A).left :=
    (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left
  let aa₁ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := ββ₁ ≫ L.β₂
  let aa₂ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := bb ≫ ββ₂ ≫ L.β₂
  have hpb₁ : IsGrpPullback D₁.P.A L.F.univ.A t₁ a₁ := IsGrpPullback.comp hF₁.1 L.cart
  have hpb₂ : IsGrpPullback D₁.P.A L.F.univ.A t₂ a₂ :=
    (IsGrpPullback.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso (asIso b))
      (IsGrpPullback.comp hF₂.1 L.cart)).congr (Category.id_comp _) rfl
  have hbsq : IsSquare b.left bb :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hsq₁ : IsSquare a₁ aa₁ := GlobalTheory.PolDeg.isSquare_comp hF₁.2.1 L.sq
  have hsq₂ : IsSquare a₂ aa₂ := GlobalTheory.PolDeg.isSquare_comp hbsq (GlobalTheory.PolDeg.isSquare_comp hF₂.2.1 L.sq)
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ L.T.B L.T.M.L).IsLB := LB.isLB_linComb L.T.M.isLB _ _
  have hU := L.F.univ.isLB
  have hA₁ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₁) :=
    LBIso.trans (hLam D₁) (pull_isLB hLamT ββ₁) (pull_isLB hU _) ⟨w₁, hF₁.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₁ rfl)
  have hA₂' : LBIso (abelian₂ D₂.P.A D₂.P.L) (L.F.univ.P.pull (ββ₂ ≫ L.β₂)) :=
    LBIso.trans (hLam D₂) (pull_isLB hLamT ββ₂) (pull_isLB hU _) ⟨w₂, hF₂.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₂ rfl)
  have hA₂ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (hLam D₁) (pull_isLB (hLam D₂) bb) (pull_isLB hU _) hM.2.2.1
      (GlobalTheory.PolDeg.lbIso_pull_comp hA₂' bb rfl)
  have hP : LBIso (L.F.univ.P.pull aa₁) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (pull_isLB hU _) (hLam D₁) (pull_isLB hU _) hA₁.symm hA₂
  have hs : t₁ ≫ L.F.s = t₂ ≫ L.F.s := by
    have hb : spMap ω₁ ≫ spMap L.T.b = spMap ω₂ ≫ spMap L.T.b := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hω]
    have e : ∀ ω : L.W →+* V, (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom) ≫ L.F.s = spMap ω ≫ spMap L.T.b := by
      intro ω
      rw [Category.assoc, Category.assoc, ← L.u_base]
      rfl
    rw [ht₁, ht₂, e, e, hb]
  have hlev' : ∀ l, ∃ x : TF (R := V) F ⟶ D₁.P.A,
      x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (L.F.univ.lev l).left ∧
      x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (L.F.univ.lev l).left := by
    intro l
    obtain ⟨p₁, p₂, hy₁, hb₁, hy₂, hb₂, hQ⟩ := hlev l
    have h21 := himg p₁ p₂ hQ (by rw [hy₂, hy₁, map_zero])
    refine ⟨p₁.g.b, ?_, ?_⟩
    · simpa only [a₁, ht₁, Category.assoc] using hb₁
    · have : p₁.g.b.left ≫ a₂ = p₂.g.b.left ≫ β₂ ≫ L.β := by
        simp only [a₂, h21, Category.assoc]
      rw [this, hb₂]
      simp only [ht₂, Category.assoc]
  obtain ⟨ht, ha⟩ := GlobalTheory.T.eq_of_presentations_same_polarisation_level L.F hn hζ hnu V D₁.P.A t₁ t₂ a₁ a₂ aa₁ aa₂ hpb₁ hpb₂ hsq₁ hsq₂ hP hs F hlev'
  have hcoordEq : ∀ i, (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
      (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
    intro i
    obtain ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ⟩ := hco (Pi.single i 1)
    have hφ : p₂.y = φ p₁.y := by
      rw [hy₂, hy₁]
      apply e₂.injective
      rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have h21 := himg p₁ p₂ hQ hφ
    have c1 : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₁ := by
      simp only [a₁, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, hT₁.1]
      simp only [Category.assoc]
    have c2 : (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₂ := by
      simp only [a₂, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, ← h21, ← Category.assoc p₂.g.b.left, hT₂.1]
      simp only [Category.assoc]
    have hgen : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
        (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
      rw [c1, c2, ha]
    have : IsProper L.F.univ.A.hom := L.F.univ.ab.proper
    haveI : IsDominant (TF (R := V) F).hom := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated L.F.univ.A.hom ?_ (TF (R := V) F).hom hgen
    simp only [Category.assoc, Over.w]
    exact ht
  refine ⟨GlobalTheory.LowChart.hom_ext _ _ (by simpa only [Category.assoc] using ht) hcoordEq, ?_⟩
  rintro rfl
  apply L.cart.1.hom_ext
  · simpa only [a₁, a₂, Category.assoc] using ha.symm
  · rw [Category.assoc, hF₂.1.1.w, ← Category.assoc, Over.w b, hF₁.1.1.w]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleIso_of_action_compatible_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  first | exact @GlobalTheory.UCanon.MatchBundle.lbIso_of_match | exact GlobalTheory.UCanon.MatchBundle.lbIso_of_match | (intros; apply GlobalTheory.UCanon.MatchBundle.lbIso_of_match <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lattice_point_nth_multiple_galois_fixed_point : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ a : Q.X, ∃ h : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), (spMap σ.toAlgHom.toRingHom ≫ h.b.left = h.b.left ∧ ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (h.s χ) (LB.pullGen D'.toPre.P.L _ _ (h.s χ) (spMap σ.toAlgHom.toRingHom))) ∧ (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n h z ∧ GtPtF.IsIota (F.xi a) z) ∧ GtPtAct F.o F.e h h := by
  first | exact @GlobalTheory.Mum.EDiv.exists_fixed_root | exact GlobalTheory.Mum.EDiv.exists_fixed_root | (intros; apply GlobalTheory.Mum.EDiv.exists_fixed_root <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.TermsMove

theorem tors_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {g : GtPtF D F} {n : ℕ} (d : ℕ) (h : ∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) :
    ∃ o, GtPtF.IsNsmul (n * d) g o ∧ o.IsZero := by
  letI := @TorusExt.gtGroup
  obtain ⟨o, o₁, o₂⟩ := h
  rw [TorusExt.isNsmul_iff_eq] at o₁
  rw [TorusExt.isZero_iff_eq] at o₂
  refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
  rw [mul_nsmul, ← o₁, o₂, nsmul_zero]

theorem frExt_isGen {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {E : Type} (F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} (he : e.IsGen) : (frExt F e).IsGen :=
  pullGen_isGen A.L _ _ e he (TorsionExt.fieldMap (R := R) E F).left


open GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull in

theorem exists_witnesses : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab x fr th w₀ s g' w h1 h2 h3 h4 h5 h6
    V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen x₂ fr₂ h1' h2' ρ hρ
  have hG := GlobalTheory.globalFns_holds
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  haveI : IsScalarTower (FractionRing V) (FractionRing V) (FractionRing V') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hF : Compat io (FractionRing V') := hf
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := map_maximalIdeal_le io
  have hg₂ : jFK (R := V') (FractionRing V') ≫ spMap f = jFK (R := V) (FractionRing V') := (Spec.map_comp _ _).symm
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w₀₂, hw₀₂, Ω, hΩ₁, hΩ₂, hE⟩ := exists_expand hG hmon hU hF hg₂ hcart.1 hwψ hgen h4 hκ
  obtain ⟨t', s', E', ht', hs'⟩ := (hE 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing V') 𝔪.U.toUnifPre hG h5)
  have hx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = (fieldMap (R := V) (FractionRing V) (FractionRing V') ≫ x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · show _ = (spMap f ≫ (x b).left) ≫ 𝔪.φ
      rw [Category.assoc, ← hφ, ← Category.assoc, h1', Category.assoc, 𝔗.lam_pt, Category.assoc, h1, ← Category.assoc,
        ← Category.assoc, ← spMap_comp, ← spMap_comp, hyK]
    · rw [Category.assoc, hcart.1.w, ← Category.assoc, Over.w, Over.w]
      exact hg₂
  have hfr : ∀ b, FrUp wψ (fr₂ (𝔗.lam b)) (frExt (FractionRing V') (fr b)) (ρ b : FractionRing V') := fun b z J J' hJ hJ' => by
    have e : vS (frExt (FractionRing V') (fr b)) z J = val (fr b) (spMap f) z J :=
      (val_frExt (fr b) (𝟙 _) hJ).trans (congrArg (fun q => val (fr b) q z J) (Category.id_comp _))
    rw [e]
    exact hρ b z J J' hJ hJ'
  have hv : ∀ b, ValAt t' (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b))
      (f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) * ((ρ b)⁻¹ ^ 1).val) := fun b =>
    valAt_pull hΩ₁ hΩ₂ ht' (hx b) (hfr b) (valAt_ext (h3 b))
  have t0 : (show AbSec 𝔪₂.A (FractionRing V') 1 from t') ≠ 0 := fun e => by
    have h₀ := hv x₀
    rw [show t' = (0 : AbSec 𝔪₂.A (FractionRing V') 1) from e] at h₀
    exact mul_ne_zero ((map_ne_zero f).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv))
      (Units.ne_zero _) (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨x', fr', Θ, -, k1, k2, k3, -⟩ := IntTerm.exists_points_frames_theta _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m _ δ 𝔪₂
  obtain rfl : x' = x₂ := funext fun a => Over.OverMorphism.ext (𝔪₂.cart.1.hom_ext ((k1 a).trans (h1' a).symm)
    ((Over.w _).trans (Over.w _).symm))
  have hΘ : ∀ a, ValAt Θ (x' a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩) := fun a z J' hJ' => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' 𝔗.X₂.ρ.P.isLB z
    have e := mul_left_cancel (((k2 a).2 z J J' hJ hJ').trans ((h2' a).2 z J J' hJ hJ').symm)
    have b := k3 a z J' hJ'
    rw [FrameMove.val_powFrame] at b ⊢
    rwa [← e]
  obtain ⟨K, hK⟩ := exists_eq_smul t0 Θ
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') le_rfl w₀₂ hw₀₂
  choose g₁ w₁ a₁ a₂ a₃ a₄ using fun c => exists_ext (F := FractionRing V') hG 𝔪.U h4 (g' c) (h6 c).2.1
  choose g₂ w₂ b₁ b₂ b₃ b₄ using fun c => exists_point hG hI hF hκ hΩ₁ hΩ₂ (fun k hk => (hE k hk).2) (g₁ c) (a₁ c) (ρ (lab c))
  refine ⟨Θ, w₀₂, K • s', g₂, w₂, K, hΘ, hw₀₂, (he' _ _).2 ?_, fun c => ⟨?_, b₁ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e' hK).trans ((map_smul e' K _).trans (congrArg (K • ·) ((he' _ _).1 E')))
  · rw [𝔗.lev]
    exact tors_mul _ (b₂ c _ (a₂ c _ (h6 c).1))
  · exact b₄ c (x' (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c))) _ (frExt (FractionRing V') (fr (lab c)))
      (frExt_isGen _ (h2 (lab c)).1) (hx (lab c)) (hfr (lab c)) (a₄ c (x (lab c)) (fr (lab c)) (h2 (lab c)).1 (h6 c).2.2)
  · rw [coef_smul (b₁ c), _root_.mul_assoc, b₃ c _ _ hs', a₃, he₈]
    rfl
  · have h₀ := valAt_lin (hv b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at h₀
    rw [valAt_unique (hΘ _) h₀, pow_one, _root_.mul_assoc, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end GlobalTheory.TermsMove
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
open GlobalTheory.Poinc.Sep.BaseTerms


theorem _root_.GlobalTheory.T.frames_along_theta_tower_root_of_unity_power : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (m' : ℕ) (t' : Fin m' → V')
      (δ' : Fin m' → LinearMap.BilinForm ℤ X') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  first | exact @GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | exact GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | (intros; apply GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  first | exact @GlobalTheory.UCanon.quasiFinite_of_tautB | exact GlobalTheory.UCanon.quasiFinite_of_tautB | (intros; apply GlobalTheory.UCanon.quasiFinite_of_tautB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  first | exact @GlobalTheory.UCanon.MulDeg.mulDeg_laws | exact GlobalTheory.UCanon.MulDeg.mulDeg_laws | (intros; apply GlobalTheory.UCanon.MulDeg.mulDeg_laws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledLowerObject_group_identification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  first | exact @GlobalTheory.UCanon.pulled_lowObj_grp_ident | exact GlobalTheory.UCanon.pulled_lowObj_grp_ident | (intros; apply GlobalTheory.UCanon.pulled_lowObj_grp_ident <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.deeperThetaRing_regular_at_extension_point : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → RegAt 𝔗.X₂ z₂ ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.regAt | exact GlobalTheory.Poinc.Sep.Tower.regAt | (intros; apply GlobalTheory.Poinc.Sep.Tower.regAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.deeperTheta_value_galoisConjugate_extension : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  first | exact @GlobalTheory.Poinc.Sep.val_galois_conj | exact GlobalTheory.Poinc.Sep.val_galois_conj | (intros; apply GlobalTheory.Poinc.Sep.val_galois_conj <;> assumption)
end
