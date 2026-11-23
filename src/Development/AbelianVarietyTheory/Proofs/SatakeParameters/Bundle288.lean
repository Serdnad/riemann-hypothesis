module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeSplitTopDegreeRecursion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_withEnt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw)
    (hE : EntOk E O) (hS : ∀ u w h, ThAtServed (ex.ker u w h) E)
    (t : KerEntTied ex) (ht : I.StdKerTie l Z t) (hO : t.O = O) (hTop : t.TopPinned) :
    ∃ t' : KerEntTied ex, I.StdKerTie l Z t' ∧ t'.O = O ∧ t'.ent = E ∧ t'.Adapted ∧ t'.TopPinned := by
  obtain ⟨⟨kf, kf_un⟩, hAd⟩ := hE
  subst hO
  refine ⟨{ t with ent := E, ent_lam := fun u w h => (hS u w h).1, kf := kf, kf_un := kf_un, served := hS },
    ?_, rfl, rfl, hAd, hTop⟩
  exact { X_eq := ht.X_eq, seam := ht.seam, Pr := ht.Pr, Ch := ht.Ch, sel := ht.sel, S := ht.S, word := ht.word, tup := ht.tup,
          cst := ht.cst, idx := ht.idx, m2 := ht.m2, glob := ht.glob, amb := ht.amb, δ := ht.δ, O := ht.O }

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

end GlobalTheory.RoadU.FinTwist

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

theorem isAlg_zero {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K} {m : ℕ} (hm : 0 < m)
    (h : κ ^ m = 1) : κ.IsAlg 0 := fun k => isAlgPos_zero_of_orderDvd hm h k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n) {κ : HChar K}
    (hκ : κ.IsAlg 0) (τ : K →+* ℂ) : (CG.mk (P.twist κ)).infChar τ = (CG.mk P).infChar τ := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 0 hκ τ]
  simp

end GlobalTheory.RoadU.FinTwist
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

theorem wdRel_trivWD {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' w') (φ : Ω ≃+* Ω') (a : ℕ) :
    WDRel φ (trivWD h a) (trivWD h' a) := by
  refine ⟨a, WDRep.diag h fun _ : Fin a => 1, WDRep.diag h' fun _ : Fin a => 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · intro σ σ' _
    ext v i
    simp [WDRep.diag, WDRep.ofChars, GlobalTheory.WeilDeligne.unrChar]

theorem charPol_eq {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' w'}
    {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

end GlobalTheory.RoadU.PhiDescent


end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocal

open GlobalTheory.PRep

theorem exists_trivOutside_map_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (h : GL (Fin n) (s.w.adicCompletion L)) :
    ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h := by
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  refine ⟨x, hx, ?_⟩
  rw [e]
  ext i j
  simp

theorem exists_eigen_of_sum {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V) (hf0 : ∑ i, T i (y i) ≠ 0)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v :=
  _root_.GlobalTheory.ExistsEigenvector.exists_eigenvector hρ hK hU h1 θ hθU hmul T y hf0 hinv


theorem exists_eigen_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ hK hKOne f hf hf0 hθ
  classical
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono (fun h hh => (hKOne h hh).1) GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  refine exists_eigen_of_sum σ.smooth hKc GlobalTheory.StepData.isOpen_KOne (one_mem _) θ
    (fun g hg _ => (hKOne g hg).2) hmul (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)))
    (fun j => y j.1) (by rw [hsum]; exact hf0) ?_
  intro k hk
  obtain ⟨x, hx, e, hfx⟩ := hrt k hk
  subst e
  have hj : ∀ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
      (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (y j.1)) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1)) := fun j => j.1.2.2 x hx (y j.1)

  rw [Finset.sum_congr rfl fun j _ => hj j, ← map_sum, hsum, hfx]

end GlobalTheory.EigLocal
end
end

section

noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (π : Representation ℂ G V) (w : V) : Subgroup G where
  carrier := {g | π g w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_eigen_of_sum {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Representation ℂ G V) (θ : G →* ℂˣ) (H : Subgroup G) [H.FiniteIndex] (hHθ : H ≤ θ.ker)
    {ι : Type} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, ∀ h ∈ H, π h (u i) = u i)
    (T : ι → V →ₗ[ℂ] M) (f : M) (hf0 : f ≠ 0)
    (hf : ∀ g, ∑ i ∈ s, T i (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, π g w = ((θ g : ℂˣ) : ℂ) • w := by
  classical
  haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let F : V → G → V := fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w
  have hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x) := by
    intro w g x
    simp only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]
    congr 1
    have : ((θ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y := by
    intro i hi x y hxy
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h := ⟨x⁻¹ * y, hm, by group⟩
    have hθh : θ h = 1 := hHθ hh
    simp only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]
  let e : V → V := fun w => ∑ q : G ⧸ H, F w q.out
  have heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i) := by
    intro i hi g

    simp only [e, map_sum, hFg, ← Finset.smul_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    apply hFH i hi
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f := by

    simp only [e, map_sum]
    rw [Finset.sum_comm]
    have : ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f := by
      intro q
      simp only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  by_contra hne
  push_neg at hne
  have hz : ∀ i ∈ s, e (u i) = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨g, hg⟩ := hne _ h0
    exact hg (heig i hi g)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])] at htot
  have hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)

end Algebra

section Topology

theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  open scoped Pointwise in
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  intro L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt
  classical
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hσ c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨φ, hφ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hφ i)
  let m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map c.toRingHom
  have hm : Continuous m := Units.continuous_map (continuous_id.matrix_map hc)
  let π : Representation ℂ K σ.V := σ.ρ.comp (m.comp K.subtype)
  have hπ : ∀ g : K, π g = σ.ρ (m g) := fun g => rfl
  have hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f := by
    rintro ⟨g, hg⟩
    obtain ⟨κ, hκ, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have : ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i) := by
      intro i _
      rw [hπ, ← hu i]
      exact i.2.2 κ hκ (u i)

    rw [Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]
    rw [← hsum]
    rfl
  let H : Subgroup K := θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)
  have hHo : IsOpen (H : Set K) := by
    rw [Subgroup.coe_inf]
    refine hθ.inter ?_
    simp only [Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)
  have hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :
      Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.SplitFlip.isCompact_KO
  haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_sum π θ H inf_le_left φ.support u
    (fun i hi h hh => by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)
      exact (Subgroup.mem_iInf.1 this hi))
    (fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF
  exact ⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩

end GlobalTheory.LocVec
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isotypic_local_component_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  first | exact @GlobalTheory.SepLoc.main | exact GlobalTheory.SepLoc.main | (intros; apply GlobalTheory.SepLoc.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.eigencharacter_of_summand_charZero : EigenCharTwist := by
  first | exact @GlobalTheory.eigenCharTwist_holds | exact GlobalTheory.eigenCharTwist_holds | (intros; apply GlobalTheory.eigenCharTwist_holds <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

theorem _root_.GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted → ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | exact GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | (intros; apply GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | exact GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | (intros; apply GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sphericalHecke_split_top_degree_recursion : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := by
  first | exact @GlobalTheory.SplitTopStep.top_step | exact GlobalTheory.SplitTopStep.top_step | (intros; apply GlobalTheory.SplitTopStep.top_step <;> assumption)
end
