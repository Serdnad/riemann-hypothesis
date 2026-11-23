module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle101
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {q : Y ⟶ X} {q' : Y' ⟶ X'} {pm : Y' ⟶ Y}

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Half

end Half

variable {Xo : Moduli D l} {c : Coeff l}

section Cover

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a) (n : ℕ) (nab₂ : NabV C.Xo₂ C.c₂) (f : Rul C.Xo₂ C.c₂)
  (φ : (Fin n → LevQ D a.l₂) → c.F)

end Cover

section Rule

def fnRule (g : Γ(Xo.XF c, ⊤)) : Rul Xo c := fun _ y => fnAt (basePt y) g

theorem fnAt_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (y : Sp S ⟶ X) (g : Γ(X, ⊤)) :
    fnAt (spMap ψ ≫ y) g = ψ (fnAt y g) := by
  have e := congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem basePt_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {ψ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap ψ y z) : basePt z = spMap ψ.toRingHom ≫ basePt y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd,
      GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]
    exact congrArg spMap ψ.comp_algebraMap.symm

theorem fnRule_mem (g : Γ(Xo.XF c, ⊤)) : fnRule g ∈ sec Xo c 0 0 := by
  refine ⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩
  · change fnAt (basePt z) g = ψ (fnAt (basePt y) g)
    rw [basePt_frMap h, fnAt_comp]
    rfl
  · have e : basePt y' = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
      · rw [basePt, basePt, pullback.lift_snd, pullback.lift_snd]
    have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
    change fnAt (basePt y') g = _ * fnAt (basePt y) g
    rw [e, e', _root_.one_mul]

theorem evR_fnRule (g : Γ(Xo.XF c, ⊤)) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (fnRule g) y = fnAt (basePt y) g := by
  have h := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y
  unfold evR evalAt
  rw [dite_eq_left h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]
  rfl

end Rule

section Law

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

end Law

section Coefficients

open GlobalTheory.ShortDatumEq

variable {a : IsAuxiliarySplitSquarefreeLevel l}

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) {n : ℕ}

end Coefficients

theorem fnRule_injective : Function.Injective (fnRule (Xo := Xo) (c := c)) := by
  intro g g' h
  refine fn_ext fun z _ => ?_
  obtain ⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩ :=
    GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z
  have e : basePt y = j := pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])
  have e' : fnAt j g = fnAt j g' := e ▸ congrFun (congrFun h p) y
  have e'' : j.appTop.hom g = j.appTop.hom g' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'
  refine (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_
  refine (gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))
  rw [gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]
  exact congrArg _ e''

section Datum

open GlobalTheory.ShortDatumEq

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (n : ℕ)

variable {n}

end Datum

end GlobalTheory.LevelCoverCompare
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClassSumCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem exists_frUnder {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) (y₂ : FrPt d.Xo₂ d.c₂ S)
    (hx : (y₂.x ≫ d.r) ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF, hc]
  have e : y₂.x ≫ d.r = y₂.x ≫ d.r := rfl
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₂.x ≫ d.r, hx, fun τ i => y₂.u τ i ≫ d.m.φ, fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩,
    (frOver_iff d _ _).2 ⟨e, fun _ _ => rfl, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · obtain ⟨v₂, rfl, h₂⟩ := exists_lift d.m e hv.1
    refine (existsUnique_congr fun a => ?_).1
      (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))
    exact comb_iff d.m e (fun i => (y₂.tan τ i).1) a h₂
  · obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
    refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
    exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
        (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)

theorem rel_unique {A A₂ Y Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (hL₂ : L₂.IsLB)
    {w : LB.Iso L₂ (L.pull φ)} {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {k : Y ⟶ Y₂}
    (hk : k ≫ p = 𝟙 _) {s₂ : LB.Sec (LOne L₂ q₂)} {s s' : LB.Sec (LOne L q)} (H : Rel w p s₂ s)
    (H' : Rel w p s₂ s') : s = s' := by
  have : s.f = s'.f := funext fun i => by
    obtain ⟨i, rfl⟩ := exists_const i
    refine fn_ext fun z hz => ?_
    obtain ⟨j, hj⟩ := exists_chart hL₂ (q₂ (k z))
    have hi' : φ (q₂ (k z)) ∈ L.U i :=
      (congrArg (· ∈ L.U i) (pt_eq hp (k z))).mp ((congrArg (fun t => q t ∈ L.U i) (pt_eq hk z)).mpr (mem_ch.1 hz))
    have a := (H Y k z i j hi' hj).trans (H' Y k z i j hi' hj).symm
    rw [hk] at a
    exact a
  cases s; cases s'
  congr

theorem frUnder_unique {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {y₂ : FrPt d.Xo₂ d.c₂ S}
    {y z : FrPt Xo c S} (h : FrOver d y₂ y) (h' : FrOver d y₂ z) : y = z := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨x, xo, u, t, ei, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', ei', b', s', g'⟩ := z
  dsimp only at e e' hu hu' p p' p₁ p₂ p₁' p₂' H H'
  obtain rfl : x = x' := e.symm.trans e'
  obtain rfl : u = u' := funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e
  obtain rfl : p = q := pm_ext (p₁.trans q₁.symm) (p₂.trans q₂.symm)
  obtain rfl : s = s' := rel_unique d.Xo₂.univ.t.PP.isLB p₁ hk H H'
  rfl

end GlobalTheory.ClassSumCompare
end
end

section

theorem GlobalTheory.allClassesSt_of_landherr_of_hasseNorm :
    GlobalTheory.Published.LandherrSt → GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hL hN => GlobalTheory.all_classes_occur hL hN GlobalTheory.abelianSchemeLaws_all.1 (GlobalTheory.T.exists_heckeQuotient_principal_triple GlobalTheory.abelianSchemeLaws_all.1)

theorem GlobalTheory.allClassesSt_of_hasseNorm : GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hN => GlobalTheory.allClassesSt_of_landherr_of_hasseNorm
    (GlobalTheory.Published.landherrSt_of_landherr (GlobalTheory.LocalQuad.landherr_of_hasseNormSt hN)) hN
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem cuspForms_finiteDimensional_of_goodEmb :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ) → Formalism.L2.Pj.CuspFD Xo c U := by
  intro E _ _ _ H Dw l Xo c r U σ hσ hU
  exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ)
      ((Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 hU))

end GlobalTheory
end

section



noncomputable section

namespace GlobalTheory.AlgLawsCompare

open NumberField IsDedekindDomain IsLocalRing AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

section Valuations

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one_iff_isUnit (v : V) : valV V (algebraMap V K' v) = 1 ↔ IsUnit v := by
  rw [← notMem_maximalIdeal, ← valV_lt_one_iff (K' := K'), not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (valV_le_one v) h⟩

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

end Valuations

theorem exists_overLa {K : Type} [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr) (hT : T.FinRes) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la T.V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := T.V) (K := T.Fr)
      (IsIntegral.map_of_comp_eq (Int.castRingHom T.V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective T.V T.Fr
  let g : 𝓞 K →+* T.V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap T.V T.Fr (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal T.V).comap g ≠ ⊥ := by
    have : Finite (ResidueField T.V) := hT
    have hc : Nat.card (ResidueField T.V) ≠ 0 := Nat.card_pos.ne'
    intro h
    have h1 : ((Nat.card (ResidueField T.V) : ℕ) : 𝓞 K) ∈ (maximalIdeal T.V).comap g := by
      rw [Ideal.mem_comap, map_natCast, ← residue_eq_zero_iff, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    rw [h, Ideal.mem_bot] at h1
    exact hc (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal T.V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV T.V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg, valV_eq_one_iff_isUnit]
    exact notMem_maximalIdeal.1 ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV T.V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hpos : 0 < vV T.V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV T.V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

theorem exists_testRing_factor {K : Type} [Field K] (p : TRing K) {S : Type} [Field S] [Algebra K S]
    (φ : p.R →ₐ[K] S) {J : Type} [Fintype J] (g : J → S) :
    ∃ (r : TRing K) (α : p.R →ₐ[K] r.R) (χ : r.R →ₐ[K] S) (gr : J → r.R),
      Function.Injective χ ∧ χ.comp α = φ ∧ ∀ j, χ (gr j) = g j := by
  classical
  let e := Fintype.equivFin J
  let v : Fin (p.n + Fintype.card J) → S :=
    Fin.append (fun i => φ (Ideal.Quotient.mk p.I (MvPolynomial.X i))) (fun k => g (e.symm k))
  let Φ : MvPolynomial (Fin (p.n + Fintype.card J)) K →ₐ[K] S := MvPolynomial.aeval v
  let r : TRing K := ⟨p.n + Fintype.card J, RingHom.ker Φ, (RingHom.ker_isPrime Φ).isRadical⟩
  have hΦ : Φ.comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J))) =
      φ.comp (Ideal.Quotient.mkₐ K p.I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, v, Fin.append_left]
  let α₀ : MvPolynomial (Fin p.n) K →ₐ[K] r.R :=
    (Ideal.Quotient.mkₐ K (RingHom.ker Φ)).comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J)))
  have hα₀ : ∀ a ∈ p.I, α₀ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
    have h1 : Φ (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) a) = φ (Ideal.Quotient.mk p.I a) :=
      congrArg (fun F => F a) hΦ
    exact h1.trans (by rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
  let α : p.R →ₐ[K] r.R := Ideal.Quotient.liftₐ p.I α₀ hα₀
  let χ : r.R →ₐ[K] S := Ideal.kerLiftAlg Φ
  refine ⟨r, α, χ, fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Fin.natAdd p.n (e j))),
    Ideal.kerLiftAlg_injective Φ, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    rw [← hΦ]
    apply MvPolynomial.algHom_ext
    intro i
    rfl
  · intro j
    show Φ _ = g j
    simp [Φ, v, Fin.append_right]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z : FrPt Xo c T, FrMap φ y z :=
  FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem fromTest_of_same_point {S : Type} [Field S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' := by
  classical
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
  obtain ⟨r, α, χ, gr, hχ, hα, hgr⟩ := exists_testRing_factor p φ
    (J := (Σ τ : E →+* ℂ, Option (Fin (Dw.mult τ) × Fin (Dw.mult τ))) ⊕ Bool)
    (Sum.elim (fun q => q.2.elim (g q.1).det⁻¹ fun ij => g q.1 ij.1 ij.2) fun b => cond b (a : S) (a⁻¹ : Sˣ))
  let g₀ : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) r.R :=
    fun τ => Matrix.of fun i j => gr (.inl ⟨τ, some (i, j)⟩)
  have hg₀ : ∀ τ, (g₀ τ).map χ = g τ := fun τ => Matrix.ext fun i j => hgr (.inl ⟨τ, some (i, j)⟩)
  have hd : ∀ τ, IsUnit (g₀ τ).det := fun τ => by
    refine IsUnit.of_mul_eq_one (gr (.inl ⟨τ, none⟩)) (hχ ?_)
    rw [map_mul, map_one, hgr, AlgHom.map_det, AlgHom.mapMatrix_apply, hg₀]
    exact mul_inv_cancel₀ (hg τ).ne_zero
  have h1 : gr (.inr true) * gr (.inr false) = 1 := hχ (by rw [map_mul, map_one, hgr, hgr]; simp)
  let a₀ : r.Rˣ := ⟨gr (.inr true), gr (.inr false), h1, (mul_comm _ _).trans h1⟩
  obtain ⟨z, hz⟩ := exists_baseChange α y₀
  have hzy : FrMap χ z y := frMap_cancel (Xo := Xo) (c := c) _ _ _ α χ y₀ z y hz (hα ▸ h₀)
  obtain ⟨z', hz', -⟩ := existsUnique_frChg E H Dw l Xo c r.R z g₀ a₀ hd
  refine ⟨r, χ, z', (ChgBC.frChg_baseChange E H Dw l Xo c r.R S χ z z' y y' g₀ a₀ hz' hzy).2 ?_⟩
  have ha : χ (a₀ : r.R) = (a : S) := hgr (.inr true)
  simp only [hg₀, ha]
  exact hc

theorem reFrame : Formalism.L2.PjFree.ReFrame Xo c := by
  refine Formalism.L2.PjFree.reFrame_of
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw') ?_
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx k hk
  have hK : ∀ τ, IsUnit ((k τ).map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk τ).map _
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  simp only at hx
  subst hx
  obtain ⟨u0, hu0⟩ := IntRebase.gen_unit' (x := y0.1.x) zs y0.1.s zg y0.1.gen
  refine ⟨⟨IntRebase.rebase₂ y0.1 _ hK, fromTest_of_same_point (y := y0.1) rfl y0.2.1,
    IntRebase.integral_reb T io y0.1 y0.2.2 k hk hK⟩, u0, rfl, fun τ i => ?_,
    𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · exact (IntRebase.isCombAtG_iff Xo.univ.t y0.1.x
      (fun j => IntRebase.ovT (t := Xo.univ.t) (y0.1.tan τ j)) _ _).2 rfl
  · intro i h
    show ((𝟙 _ : Gx y0.1.x ⟶ Gx y0.1.x).appLE _ _ h).hom (scal y0.1.x (u0 : T.Fr) i * zs.f i) = y0.1.s.f i
    rw [← hu0 i]
    exact IntRebase.id_appLE_apply _ _ h _

variable (Xo c)

end GlobalTheory.AlgLawsCompare
end
end
