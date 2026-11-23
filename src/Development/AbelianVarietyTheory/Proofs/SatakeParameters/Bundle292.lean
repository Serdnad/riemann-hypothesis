module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitSatLoc

section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def rtHom (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun x := NG.rt L n x
  map_one' := LinearMap.ext fun f => funext fun g => by simp [NG.rt]
  map_mul' x y := LinearMap.ext fun f => funext fun g => by simp [NG.rt, mul_assoc]

theorem map_symm_map (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.symm.toRingHom
      (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem map_map_symm (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.w.adicCompletion L)) :
    Matrix.GeneralLinearGroup.map c.toRingHom
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem mem_Ov_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (a : s.v.adicCompletion L⁺) :
    c a ∈ Formalism.UG.Ov L s.w ↔ a ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  show c a ∈ s.w.adicCompletionIntegers L ↔ a ∈ s.v.adicCompletionIntegers L⁺
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]

theorem map_mem_KGL_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) {n : ℕ}
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.HeckeScalarSph.mem_GLint_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mem_Ov_iff hc hcL]

theorem isUnifV_map {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) : Formalism.UG.IsUnifV L s.w (c ϖ) := by
  show Valued.v (c ϖ) = _
  rw [GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]
  exact hϖ

theorem coe_glMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map f :=
  rfl

theorem diagJ_map {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (ϖ : A) (k : ℕ) :
    (Formalism.UG.diagJ n ϖ k).map f = Formalism.UG.diagJ n (f ϖ) k := by
  simp only [Formalism.UG.diagJ, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

end Local

section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def locAct (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) :
    Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → W) :=
  (rtHom n W).comp (e.comp (Matrix.GeneralLinearGroup.map c.symm.toRingHom))

theorem locAct_apply (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n)
    (g : GL (Fin n) (s.w.adicCompletion L)) (f : GAf L n → W) :
    locAct n W s c e g f = NG.rt L n (e (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)) f := rfl

theorem heckeD_eq_heckeVec {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) (he1 : ∀ g, TrivOutside {s.v} (e g))
    (he2 : ∀ g, s.loc n (e g) = g) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ)
    (k : ℕ) {F : GAf L n → W} (hF : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ F = F) :
    NG.heckeD J (tSet L n s ϖ k) F =
      GlobalTheory.LFun.heckeVec (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov L s.w) (c ϖ) k) F := by
  classical
  have hψφ : ∀ g : GL (Fin n) (s.v.adicCompletion L⁺),
      Matrix.GeneralLinearGroup.map c.symm.toRingHom
        (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g := map_symm_map s c
  have hφψ : ∀ g : GL (Fin n) (s.w.adicCompletion L),
      Matrix.GeneralLinearGroup.map c.toRingHom
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g := map_map_symm s c
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  rw [GlobalTheory.HeckeEigConj.heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hF]
  have hU := isUnifV_map hc hcL hϖ
  rw [GlobalTheory.SatHecke.Tj_eq_dosetInd hU k]
  have hK : ∀ x, TrivOutside {s.v} x →
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ x ∈ Umax L n) := fun x hx =>
    (map_mem_KGL_iff hc hcL _).trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hF _ ((hK _ (he1 _)).1 ?_) (he1 _)
    rw [he2, hφψ]; exact hA
  have hdiag : ∀ a b x : GL (Fin n) (s.v.adicCompletion L⁺),
      (x : Matrix (Fin n) (Fin n) _) = (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) _) →
      (Matrix.GeneralLinearGroup.map c.toRingHom x : GL (Fin n) (s.w.adicCompletion L)) =
        Matrix.GeneralLinearGroup.map c.toRingHom a *
          Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) *
            Matrix.GeneralLinearGroup.map c.toRingHom b := by
    intro a b x h
    refine Units.ext ?_
    simp only [Units.val_mul, coe_glMap, h, Matrix.map_mul, diagJ_map,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    rfl
  have hinj : Set.InjOn (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
      GL (Fin n) (s.w.adicCompletion L))) R := by
    intro γ hγ δ hδ h
    have h' : s.loc n γ = s.loc n δ := by
      have := congrArg (Matrix.GeneralLinearGroup.map c.symm.toRingHom) h
      simpa only [hψφ] using this
    exact GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s γ δ (hD γ (hR1' γ hγ)) (hD δ (hR1' δ hδ)) h'
  have hmem : ∀ γ ∈ R, (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) : GL (Fin n) (s.w.adicCompletion L)) ∈
      DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)) := by
    intro γ hγ
    obtain ⟨-, a, ha, b, hb, h⟩ := hR1' γ hγ
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, (map_mem_KGL_iff hc hcL a).2 ha, _, (map_mem_KGL_iff hc hcL b).2 hb,
      hdiag a b _ h⟩
  have huniq : ∀ g ∈ DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)),
      ∃! r, r ∈ R.image (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
        GL (Fin n) (s.w.adicCompletion L))) ∧ r⁻¹ * g ∈ GlobalTheory.LFun.KGL s.w (n := n) := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    obtain ⟨x, hx⟩ : ∃ x, x = e (Matrix.GeneralLinearGroup.map c.symm.toRingHom (y *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z)) :=
      ⟨_, rfl⟩
    have hxt : TrivOutside {s.v} x := hx ▸ he1 _
    have hxT : x ∈ tSet L n s ϖ k := by
      refine ⟨hxt, Matrix.GeneralLinearGroup.map c.symm.toRingHom y, ?_,
        Matrix.GeneralLinearGroup.map c.symm.toRingHom z, ?_, ?_⟩
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hy)
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hz)
      · rw [hx, he2, map_mul, map_mul, Units.val_mul, Units.val_mul]
        congr 2
        rw [coe_glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagJ_map]
        simp
    obtain ⟨γ, ⟨hγR, hγx⟩, hγu⟩ := hR2' x hxT
    have hkey : ∀ δ ∈ R, ((Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) :
        GL (Fin n) (s.w.adicCompletion L))⁻¹ * (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
          (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ δ⁻¹ * x ∈ Umax L n) := by
      intro δ hδ
      have e1 : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) : GL (Fin n) (s.w.adicCompletion L))⁻¹ *
          (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) =
          Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (δ⁻¹ * x)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx, he2, hφψ]
      rw [e1]
      exact hK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD δ (hR1' δ hδ))) hxt)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hγR, (hkey γ hγR).2 hγx⟩, ?_⟩
    rintro r ⟨hr, hr'⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hr
    rw [hγu δ ⟨hδ, (hkey δ hδ).1 hr'⟩]
  rw [GlobalTheory.LFun.heckeVec_dosetInd hFK (R := R.image fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
    GL (Fin n) (s.w.adicCompletion L))) (fun r hr => ?_) huniq, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [locAct_apply, hψφ, GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s (e (s.loc n γ)) γ (he1 _)
      (hD γ (hR1' γ hγ)) (he2 _)]
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hr
    exact hmem γ hγ

end Key
section Main


end Main

end GlobalTheory.SplitSatLoc

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SatChar

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem charPol_satWD (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (n : ℕ) (B : Multiset ℂˣ) (g : Weil h) :
    (satWD h n B).charPol g = (B.map fun b : ℂˣ =>
      X - C ((((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - n) / 2 : ℝ)) : ℂ)) ^ deg g * ((b : ℂ)⁻¹) ^ deg g)).prod := by
  classical
  have hs : ∀ {ι : Type} (c : ℂ) (d : ι → ℂ), c • _root_.GlobalTheory.WeilDeligne.diagEnd d = _root_.GlobalTheory.WeilDeligne.diagEnd (fun i => c * d i) := fun c d =>
    LinearMap.ext fun v => _root_.funext fun i => by simp [mul_assoc]
  rw [satWD, WD.lpUnr, WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hs, charpoly_diagEnd,
    ← Finset.prod_map_val]
  rw [Multiset.map_univ (B.map fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))
    (fun z : ℂ => X - C ((((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) ^ deg g * ((WD.unitOf z : ℂˣ) : ℂ) ^ deg g)),
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [WD.coe_unitOf (by simp), Units.val_inv_eq_inv_val]

def ordHom (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ord (w.adicCompletion E) x)) fun x y => by
    rw [ord_mul, ofAdd_add]

theorem unram_art {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : ∀ x : (w.adicCompletion E)ˣ, Valued.v (x : w.adicCompletion E) = 1 → χ x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (g : Weil h) :
    χ (a g) = χ ϖ ^ (-deg g) := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  have h2 : ord (w.adicCompletion E) (a g * ϖ ^ deg g) = 0 := by
    have := congrArg Multiplicative.toAdd (map_mul (ordHom w) (a g) (ϖ ^ deg g))
    rw [map_zpow] at this
    simp only [ordHom, MonoidHom.mk'_apply, toAdd_ofAdd, toAdd_mul, toAdd_zpow, smul_eq_mul] at this
    rw [this, ha.ord_eq, h1]; ring
  have h3 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [SphCompletion.ord_completion, neg_eq_zero] at h2
    have h0 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    rw [← WithZero.exp_log h0, h2, WithZero.exp_zero]
  have h4 : a g = (a g * ϖ ^ deg g) * ϖ ^ (-deg g) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h4, map_mul, hχ _ h3, one_mul, map_zpow]

theorem absPow_art {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (s : ℝ)
    (g : Weil h) :
    (absPow (w.adicCompletion E) (s : ℂ) (a g) : ℂ) = (((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    exact_mod_cast (zero_lt_one.trans this)
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq.le, ← Complex.ofReal_zpow,
    ← Complex.ofReal_cpow (zpow_pos hq _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, mul_comm]

theorem satWD_charPol_chars : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), ∀ (n : ℕ) (ξ ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, ξ' j = ξ j * absPow (w.adicCompletion E) ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := by
  intro Ω _ E _ _ _ _ w A h n ξ ξ' hξ' hun ϖ hϖ a ha g
  rw [charPol_satWD, Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rw [hξ' j, MonoidHom.mul_apply, Units.val_mul, unram_art ha (ξ j) (hun j) ϖ hϖ g, absPow_art ha]
  congr 2
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, inv_zpow, mul_comm]

end GlobalTheory.SatChar
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem wdOf_eq_satWD_of_frobEig : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  intro Ω _ E _ _ _ _ l _ ι n r _hr w hl A h B hF
  obtain ⟨hI, hFr⟩ := hF A h
  have ht := isTameChar_tameL h hl
  have hN : IsMonodromy (tameL h hl) r 0 :=
    (isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => hI σ σ.2)
  have hu1 : (wdOf h hl ι r).unr := (hN.unr_wdOf_iff hl ht ι).mpr hI
  have hm : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  have hs := WD.lpUnr_spec (h := h) _ hm
  have hu2 : (satWD h n B).unr := (WD.unr_tw _ _).mpr hs.1
  rw [WD.unr_eq_lpUnr _ hu1, WD.unr_eq_lpUnr _ hu2]
  congr 1
  rw [satWD, WD.frobEig_tw _ _ hs.1, hs.2.1, WD.frobEig, WD.eig, hN.charPol_wdOf hl ht ι (frob h)]
  have hσ : IsFrob A (normV w) ((frob h : Weil h) : _root_.Formalism.ConjugateSelfDual.G E Ω) := deg_eq_one_iff.mp deg_frob
  have hc := Formalism.L2.NR.charpoly_map_of_inv ι.toRingHom (r (frob h : _root_.Formalism.ConjugateSelfDual.G E Ω)) _
    (by rw [← map_inv]; exact hFr _ hσ)
  have e : ∀ s : Multiset ℂ, s.map (fun μ => X - C μ⁻¹) = (s.map (·⁻¹)).map (fun a => X - C a) := fun s => by
    rw [Multiset.map_map]; rfl
  rw [hc, e, roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.map_map]
  have hB : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map (Units.val : ℂˣ → ℂ) := by
    simp [Multiset.bind_singleton]
  rw [hB, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_inv_eq_inv_val]
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring,
    Real.rpow_neg hq, Complex.ofReal_inv, mul_inv, mul_comm]

end GlobalTheory.RoadU
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem unlinked_chars_comp_normU : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (c : ℝ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - c : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) → Unlinked (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j)) := by
  intro E M _ _ _ _ _ w u _ n c ξ hξ he
  letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
  have hf := GroundTheory.Global.continuous_adicCompletionMap w u
  haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := _root_.continuousSMul_of_algebraMap _ _ hf
  haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap w u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
  haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
  haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact isModuleTopologyOfFiniteDimensional
  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t :=
    fun t => GlobalTheory.LBCNu.absPow_comp_norm t
  have hval : ∀ (s : ℝ) (x : (u.adicCompletion M)ˣ), ‖((absPow (u.adicCompletion M) (s : ℂ) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ s := fun s x => by
    rw [val_absPow_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (nabs_pos' _ x).le _)]
  have key : ∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖(((ξ j).comp (GlobalTheory.BCChar.normU w u) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ (e - c) := by
    intro j
    obtain ⟨e, he1, he2⟩ := he j
    refine ⟨e, he1, fun x => ?_⟩
    rw [MonoidHom.comp_apply, he2, ← MonoidHom.comp_apply, hN, hval]
  intro y hy z hz hyz
  simp only [chars, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hy hz
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at hyz
  obtain ⟨a, ha, ha'⟩ := key i
  obtain ⟨b, hb, hb'⟩ := key j
  have h1 : absPow (u.adicCompletion M) ((a - b - 1 : ℝ) : ℂ) = 1 := by
    ext x
    have hx := congrArg (fun χ : (u.adicCompletion M)ˣ →* ℂˣ => ‖((χ x : ℂˣ) : ℂ)‖) hyz
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_mul] at hx
    have h1' : ‖((absPow (u.adicCompletion M) 1 x : ℂˣ) : ℂ)‖ = nabs (u.adicCompletion M) x ^ (1 : ℝ) := by
      rw [← hval]; simp
    rw [ha', hb', h1'] at hx
    have ht := nabs_pos' (u.adicCompletion M) x
    rw [val_absPow_ofReal, MonoidHom.one_apply, Units.val_one]
    have : nabs (u.adicCompletion M) x ^ (a - b - 1) = 1 := by
      rw [show a - b - 1 = (a - c) - ((b - c) + 1) by ring, Real.rpow_sub ht, Real.rpow_add ht, hx,
        div_self (by positivity)]
    rw [this, Complex.ofReal_one]
  have h2 := (absPow_ofReal_eq_one (k := u.adicCompletion M)).1 h1
  rw [abs_lt] at ha hb
  linarith [ha.1, ha.2, hb.1, hb.2]

end GlobalTheory.RoadU
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SatSupp.hasSupport_of_hasSatGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  intro E _ _ n _ w σ B hB
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  have hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := by
    simpa using GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  refine ⟨fun j => GlobalTheory.SmGL.unrChar _ (α j),
    fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)),
    GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩
  · let π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)) := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩
    exact (GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv
      (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro j x hx
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
    simp
  · rw [← hαB]
    congr 1
    funext j
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]
    simp
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem holds_csd_crys_of_holdsS (hC : SphericalLevelCondition .csd .crys) : Holds .csd .crys := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  have hc := GlobalTheory.Cong.satake_locComp E a π w σ hσ
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (hc.2.1 hsph)
  exact hC E Ω l ι a ha π χ hs r hr w hw B ((hc.1 B).2 hB) P AI hT A hAw O Bw hj σ hσ hsph

end GlobalTheory.RoadU

end
end
