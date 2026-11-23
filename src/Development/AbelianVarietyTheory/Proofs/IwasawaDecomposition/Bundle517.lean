module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle405
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle436
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle513
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle503
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle485
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE



theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

def SeedW (K : Ctx) (P : Pre) (f : Fr P) (F F₀ : IntermediateField ℚ ℂ) (px : PreX P) (S : Set ℕ) (L : IntermediateField ℚ ℂ) :
    Prop :=
  ∃ (B₀ : Base) (f₀ : Fr B₀.toPre) (T₀ : TwDat B₀) (w₀ : ColW B₀ f₀ T₀) (Z₀ : w₀.Lt) (hX₀ : B₀.fields.Ok) (Wt₀ : Set B₀.places.Pl)
    (z₀ : Dat (w₀.st Z₀) w₀.I hX₀ T₀ Wt₀), B₀.toPre = P ∧ HEq f₀ f ∧ B₀.KsC = F ∧ B₀.fixedCoefficientFieldInComplex = F₀ ∧ HEq w₀.px px ∧
      Pinned K B₀ f₀ T₀ w₀ ∧ GrpTrue Z₀.N f₀ ∧ GrpAt (w₀.st Z₀) w₀.I ∧ Fine z₀ ∧ HoldsL z₀.R z₀.F ∧
      (∀ v ∈ z₀.W1 (fun _ _ => 0), B₀.places.resChar v ∈ S) ∧ B₀.LLC ≤ L

theorem SeedW.mono {K : Ctx} {P : Pre} {f : Fr P} {F F₀ : IntermediateField ℚ ℂ} {px : PreX P} {S S' : Set ℕ}
    {L L' : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ px S L) (hS : S ⊆ S') (hL : L ≤ L') : SeedW K P f F F₀ px S' L' := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => hS (a11 v hv), a12.trans hL⟩

end GlobalTheory.Mem.R3.Rw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem coreCharacter_fieldInclusion_eq_columnHeckeChar {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {h : B.fields.Ok} {W : Set B.places.Pl}
    (z : Dat (w.st Z) w.I h T W) (j : Fin B.R.m) :
    ChrEq (z.core.chiW ((j : ℕ) + 1) z.core.toCore.σ₀) (w.I.C.mu0 j) := by
  have e := Formalism.IndefR.FWT.chiTie_of_chiR z.core z.R.toRealDat z.geo.fw.alg_eq z.geo.fw.laws.pins.2.2.1 z.geo.fw.chiR j
  rw [e]
  have h1 := z.lev.is.mu0 j
  rw [z.lev.C] at h1
  exact h1

theorem embLL_chi {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : Fin B.R.m)
    (p : {p // p ∈ (B.primes w.px).vGs}) (c : (𝓞 B.fields.E ⧸ p.1.asIdeal)ˣ) (y : 𝓞 B.fields.E) (x : B.fields.Eˣ)
    (hx : (x : B.fields.E) = y) (hc : (c : 𝓞 B.fields.E ⧸ p.1.asIdeal) = Ideal.Quotient.mk p.1.asIdeal y) :
    B.embLL ((w.I.Ch.chi j p c : B.fields.Kˣ) : B.fields.K) = (((w.I.C.mu0 j).locK p.1 x : ℂˣ) : ℂ)⁻¹ := by
  have h1 := (w.ok.ch_tied.mu0 j).atg p x y c hx hc
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_chiW {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Type} [Monoid A]
    {H₁ H₂ : Host E} {l₁ : Level H₁} {l₂ : Level H₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    {χ₁ : ℕ → (c₁.F →+* ℂ) → A →* Circle} {χ₂ : ℕ → (c₂.F →+* ℂ) → A →* Circle}
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hχ : HEq χ₂ χ₁) (n : ℕ) :
    χ₂ n c₂.F.val.toRingHom = χ₁ n c₁.F.val.toRingHom := by
  cases hH; cases hl; cases hc; cases hχ; rfl

end GlobalTheory.Mem.R3.Rw.ChiTr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem embLL_chi_ext : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX j₁ j₂ hj p₁ p₂ hp c₁ c₂ hc
  have A₁ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₁ j₁
  have A₂ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₂ j₂
  have eH := hX.H
  have el := hX.l
  have ec := hX.c
  have eχ := hX.chiW
  obtain ⟨hP, -⟩ := hE
  clear hX
  rcases B₂ with ⟨P₂⟩
  change P₂ = B₁.toPre at hP
  subst hP
  have ec₀ := app_chiW eH el ec eχ ((j₁ : ℕ) + 1)
  rw [← hj] at A₂
  have A₂' : ChrEq (D := (w₁.st Z₁).toD7) (z₁.core.chiW ((j₁ : ℕ) + 1) z₁.core.Q.c.F.val.toRingHom) (w₂.I.C.mu0 j₂) := by
    rw [← ec₀]
    exact A₂
  have hχ : w₁.I.C.mu0 j₁ = w₂.I.C.mu0 j₂ := (GlobalTheory.ChrEqUnique.chrEq_unique _).1 _ _ _ A₁ A₂'
  rcases p₂ with ⟨q₂, hq₂⟩
  have eq : q₂ = p₁.1 := eq_of_heq hp
  subst eq
  have ecc : c₂ = c₁ := eq_of_heq hc
  subst ecc
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c₂ : 𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)
  have hy0 : ((y : 𝓞 B₁.fields.E) : B₁.fields.E) ≠ 0 := by
    intro h0
    have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
    rw [h0', map_zero] at hy
    exact c₂.ne_zero hy.symm
  rw [embLL_chi w₂ j₂ _ c₂ y (Units.mk0 _ hy0) rfl hy.symm, embLL_chi w₁ j₁ p₁ c₂ y (Units.mk0 _ hy0) rfl hy.symm, hχ]

end GlobalTheory.Mem.R3.Rw.ChiTr
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


open Classical in
noncomputable def wtPre (P : Pre) (j : ℕ) (aP : Tau P.R → Fin (P.R.sigW j).1 → ℕ) (aM : Tau P.R → Fin (P.R.sigW j).2 → ℕ)
    (x : (P.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : Tau P.R, ((if x.1 = P.host.emb t.1 then Formalism.L2.Pj.ext0 (aP t) x.2 else 0) +
    if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (P.host.emb t.1) then Formalism.L2.Pj.ext0 (aM t) x.2 else 0)

theorem cusp_type_congr {P₁ P₂ : Pre} (hP : P₂ = P₁)
    {H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₁.host.E} {H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₂.host.E}
    {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁} {c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {Xo₁ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₁ j) l₁} {Xo₂ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₂ j) l₂}
    {U₁ : ∀ j (σ : c₁.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₁ j) c₁ σ P₁.R.r}
    {U₂ : ∀ j (σ : c₂.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₂ j) c₂ σ P₂.R.r}
    {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    {aP₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).1 → ℕ} {aP₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).1 → ℕ}
    {aM₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).2 → ℕ} {aM₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).2 → ℕ}
    {n₁ n₂ : ℕ} (hn : n₂ = n₁)
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hDw : HEq Dw₂ Dw₁) (hXo : HEq Xo₂ Xo₁) (hU : HEq U₂ U₁)
    (haP : HEq aP₂ aP₁) (haM : HEq aM₂ aM₁) :
    ↥(Formalism.L2.Pj.cusp (Xo₂ j₂) c₂ (U₂ j₂) (wtPre P₂ j₂ aP₂ aM₂) n₂) =
      ↥(Formalism.L2.Pj.cusp (Xo₁ j₁) c₁ (U₁ j₁) (wtPre P₁ j₁ aP₁ aM₁) n₁) := by
  subst hP hj hn
  cases hH; cases hl; cases hc; cases hDw; cases hXo; cases hU; cases haP; cases haM
  rfl

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw



theorem Ext.cuspA_type_eq : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX i₁ i₂ hi
  have hk := hX.κ i₁ i₂ hi
  exact (cusp_type_congr hE.left (congrArg (fun x ↦ x + 1) hi) hk.right.right hX.H hX.l hX.c hX.Dw hX.Xo hX.U hk.left hk.right.left)

end GlobalTheory.Mem.R3.Rw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilTwist

variable {D : D7}

theorem exists_isDetRoot (V : HSp D) (g : GA D V) : ∃ x, IsDetRoot V g x := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V 1 (isHC_one D).1 (fun _ => rfl)
  exact aval.1 g

theorem twist_both {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D}
    (ha : AdmE V W χ χ') (hν : IsHC D ν) (rν : ResEta D ν 0) (hν' : IsHC D ν') (rν' : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ho : IsWeilOn ψ V W χ χ' om)
    (ho' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g : GA D V} {h : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((ν' x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) := by
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.Mem.HeckeExp.hecke_exp_laws D
  have hmul : ∀ a b : IdC D, IsHC D a → IsHC D b → IsHC D (a * b) := fun a b k l =>
    (hC _).1 (C.mul_mem ((hC _).2 k) ((hC _).2 l))
  have ha' : AdmE V W (χ * ν) (χ' * ν') :=
    ⟨ha.1, hmul _ _ ha.2.1 hν, hmul _ _ ha.2.2.1 hν', resEta_mul ha.2.2.2.1 rν, resEta_mul ha.2.2.2.2 rν'⟩
  obtain ⟨o, hd, ht⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha ho
  obtain ⟨o', hd', ht'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W _ _ om' ha' ho'
  obtain ⟨o'', hd'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o hd hν.1 hν'.1 rν rν'
  obtain ⟨e, -, -, he, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  have hΦ : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simp only [← he]
    exact (hth ψ _).2 (mem_ThS.1 Φ.2)
  have k := GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ V W _ _ o' o'' hd' hd'' (g, h) _ hΦ
  rw [ht', hv g h x y hx hy, LinearMap.smul_apply, ht] at k
  have k2 := congrFun k (e.symm w)
  simp only [← he, e.apply_symm_apply, Pi.smul_apply] at k2
  exact k2

theorem weilTwEq : ∀ D : D7, WeilTwEq D := by
  intro D ψ hψ V W χ χ' ν ha hν rν om ho
  have r1 : ResEta D 1 0 := ⟨rν.1, fun _ _ _ => by simp⟩
  refine ⟨fun om' ho' g h x hx => ?_, fun om' ho' g h x hx => ?_⟩
  · obtain ⟨y, hy⟩ := exists_isDetRoot W h
    have := twist_both hψ ha (isHC_one D) r1 hν rν ho (om' := om') (by rwa [mul_one]) hx hy
    rwa [MonoidHom.one_apply, mul_one] at this
  · obtain ⟨y, hy⟩ := exists_isDetRoot V g
    have := twist_both hψ ha hν rν (isHC_one D) r1 ho (om' := om') (by rwa [mul_one]) hy hx
    rwa [MonoidHom.one_apply, inv_one, one_mul] at this

end GlobalTheory.Mem.WeilTwist
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  first | exact @GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | exact GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | (intros; apply GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.toricTorsion_uniformisation_eq_restrictCharacters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  first | exact @GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | exact GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | (intros; apply GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.FrameFinPart

theorem finHom_eq_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  intro D V n hF P P' hP hP' g
  obtain ⟨hn, h⟩ := hP
  obtain ⟨hn', h'⟩ := hP'
  apply Subtype.ext
  apply Units.ext
  ext a b
  change finMat D.sp.cm.sig V.gram (P.ψ g) a b = finMat D.sp.cm.sig V.gram (P'.ψ g) a b
  rw [h, h']

end GlobalTheory.FrameFinPart
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId

variable {D : D7}

theorem idFrame_iff_unitFr {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank) :
    GlobalTheory.MtRead.IdFrame hF P ↔ GlobalTheory.MtIn.UnitFr P := by
  constructor
  · rintro ⟨hn, h⟩ κ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := (RingEquiv.eq_symm_apply _).1 (h κ a b)
    exact this
  · intro h
    refine ⟨rfl, fun κ a b => (RingEquiv.eq_symm_apply _).2 ?_⟩
    exact congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) (h κ)

def castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V V.rank) : principalLevelFrame.RowPsi V n := hn ▸ P

theorem idFrame_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : GlobalTheory.MtIn.UnitFr P) : GlobalTheory.MtRead.IdFrame hF (castFr hn P) := by
  subst hn
  exact (idFrame_iff_unitFr hF P).2 h

end GlobalTheory.MtId

end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.twistedTuple_reading_level_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  first | exact @GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | exact GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | (intros; apply GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevGe

theorem exists_put : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (κ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∃ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) ∧ bc (prV (E := E) v) x = bc (prV (E := E) v) κ := by
  intro F E _ _ _ _ _ σ n J v κ hκ
  classical
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ) 1,
    Formalism.UG.P.afsplitU_mem v σ J _ 1 (Formalism.UG.P.afsplit_bc_mem σ J v κ hκ) (one_mem _), fun w hw => ?_, ?_⟩
  · apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · exact Formalism.UG.P.afsplit_right1 v _ 1



theorem mem_uloc : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → (∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ LiftsInv I κ' P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ' P' 1) → bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ (K (chOf c)).lev.Uloc v := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hg hF hL
  obtain ⟨N, hN⟩ := GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime I hOk hPins l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv
  obtain ⟨x, hx, hxoff, hxv⟩ := exists_put _ _ v κ hκ
  obtain ⟨kk, hkk⟩ : ∃ kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), kk = k (chOf c) := ⟨_, rfl⟩
  obtain ⟨z, hz, hzoff, hzN, g', hg', hgg', hpt⟩ := GlobalTheory.T.deepElement_conj_rational_at_badPrime I hOk hPins l Z a i hi kk fb (hkk ▸ hfb) P v hv κ hκ g hg hF x hx hxv N
  obtain ⟨κ', hK, hLP, hLo⟩ := hL g' hg' hgg'
  have hxz : x * z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := mul_mem hx hz
  have hxzoff : ∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') (x * z) = 1 := fun v' hv' => by
    calc
      _ = bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') x * bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') z := map_mul _ _ _
      _ = 1 * 1 := congrArg₂ (· * ·) (hxoff v' hv') (hzoff v' hv')
      _ = 1 := one_mul 1
  have hpt' : ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := hpt
  have hq := GlobalTheory.T.representative_image_point_of_lift I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv (x * z) hxz hxzoff g' hg' hpt' κ' hK hLP hLo
  subst hkk
  have hxzU : x * z ∈ (K (chOf c)).lev.U := (hR.lev c (x * z) _ hq).2 ⟨κ', hK.1, rfl, hK.2⟩
  have hzU : z ∈ (K (chOf c)).lev.U := hN z hz hzoff hzN
  have hxU : x ∈ (K (chOf c)).lev.U := by
    have := mul_mem hxzU (inv_mem hzU)
    rwa [mul_inv_cancel_right] at this
  have := (((K (chOf c)).lev.U_eq x).1 hxU).2 v
  rwa [hxv] at this

end GlobalTheory.Mem.Col2.AdT.LevGe

end
end
