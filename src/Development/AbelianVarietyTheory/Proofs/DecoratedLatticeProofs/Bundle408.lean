module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle383
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle384
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle386
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle382
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.besselFourierJacobi_contracted_isThetaFun_each_variable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧ ∀ p, (IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧ ∀ v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) * oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := by
  first | exact @GlobalTheory.ContrTheta.contr_isTheta | exact GlobalTheory.ContrTheta.contr_isTheta | (intros; apply GlobalTheory.ContrTheta.contr_isTheta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LastRow

theorem row_lt_of_smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M : Matrix (Fin n) (Fin n) k) (hb : b * b' = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hfix : g • Q = Q) (s : Fin n) :
    valuation k (M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, Q.fn x ≠ 0 := by
    by_contra h
    exact Q.fn_ne (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨y0, -, s0, hs0, ha0⟩ := (hQ x0.1 (Q.fn x0)).1 ⟨x0.2, rfl⟩
  have hu : residue 𝒪[k] s0 ≠ 0 := by
    intro h
    apply hx0
    rw [ha0, map_mul, h, zero_mul]
  let yE : Fin n → 𝒪[k] := Pi.single s 1
  have hyE : ∀ r, (yE r : k) = (Pi.single s 1 : Fin n → k) r := by
    intro r
    simp only [yE, Pi.single_apply]
    split_ifs <;> rfl
  have h1 : Q.HasVal (b' *ᵥ Pi.single s 1) (residue 𝒪[k] (s0 * yE r₀)) := by
    refine (hQ _ _).2 ⟨yE, fun r => ?_, s0, hs0, rfl⟩
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, hyE]
  have h2 : Q.HasVal (g • (b' *ᵥ (Pi.single s 1 : Fin n → k))) (residue 𝒪[k] (s0 * yE r₀)) := by
    rw [← hfix, GlobalTheory.LatPair.Pair.smul_hasVal, inv_smul_smul]
    exact h1
  obtain ⟨y1, hy1, s1, hs1, ha1⟩ := (hQ _ _).1 h2
  obtain rfl : s1 = s0 := Subtype.ext (hs1.trans hs0.symm)
  have hM : (y1 r₀ : k) = M r₀ s := by
    rw [hy1]
    change (b *ᵥ (g.val *ᵥ (b' *ᵥ (Pi.single s 1 : Fin n → k)))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg, Matrix.mulVec_single_one]
    rfl
  have h3 : residue 𝒪[k] (y1 r₀ - yE r₀) = 0 := by
    rw [map_mul, map_mul] at ha1
    rw [map_sub, mul_left_cancel₀ hu ha1, sub_self]
  have h4 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3))
  have h5 : ((y1 r₀ - yE r₀ : 𝒪[k]) : k) = M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s := by
    rw [AddSubgroupClass.coe_sub, hM, hyE, Pi.single_apply, Matrix.one_apply]
  rw [← h5]
  exact h4



theorem exists_gl {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {V : HSp D} (β : GlobalTheory.FinPl.Frame p V (Fin V.rank)) (κ : GA D V) :
    ∃ g : GL (Fin V.rank) k, (mt V κ).map p.pr = β.b * g.val * β.b' := by
  have hm : ∀ x y : GA D V, x * y = 1 → (mt V x).map p.pr * (mt V y).map p.pr = 1 := by
    intro x y h
    have e : mt V x * mt V y = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, h, map_one, Units.val_one]
    rw [← Matrix.map_mul, e]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ A A' : Matrix (Fin V.rank) (Fin V.rank) k, A * A' = 1 → (β.b' * A * β.b) * (β.b' * A' * β.b) = 1 := by
    intro A A' h
    calc (β.b' * A * β.b) * (β.b' * A' * β.b) = β.b' * (A * ((β.b * β.b') * A')) * β.b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [β.bb', Matrix.one_mul, h, Matrix.mul_one, β.b'b]
  refine ⟨⟨β.b' * (mt V κ).map p.pr * β.b, β.b' * (mt V κ⁻¹).map p.pr * β.b, hc _ _ (hm _ _ (mul_inv_cancel κ)),
    hc _ _ (hm _ _ (inv_mul_cancel κ))⟩, ?_⟩
  calc (mt V κ).map p.pr = (β.b * β.b') * (mt V κ).map p.pr * (β.b * β.b') := by rw [β.bb', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]



theorem entry_cong (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (T : ℕ)
    (t t' : 𝓞 D.host.E) (h1 : (t' : D.host.E) = star (t : D.host.E)) (h2 : t * t' = (T : 𝓞 D.host.E)) (h3 : IsCoprime t t')
    (h4 : t ∈ P.asIdeal) (h5 : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h6 : (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (r s : Fin n)
    (hi : Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E p.v)
    (hl : valuation k (((mt V κ).map p.pr) ((finCongr hn).symm r) ((finCongr hn).symm s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) k) ((finCongr hn).symm r) ((finCongr hn).symm s)) < 1) :
    ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  subst hn
  let y : AE D := mt V κ r s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s
  have hy : Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s := by
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h7 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← hy]
  refine GlobalTheory.LocMod.SplitUnif.eq_mul_of_val_lt_one D k p P hP T t t' h1 h2 h3 h4 h5 h6 y ?_ ?_
  · rw [hy]
    refine Subring.sub_mem _ hi ?_
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [y]
    rw [map_sub, h7]
    exact hl

end GlobalTheory.FamTrace.LastRow


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem _root_.GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n) (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k), (mt B.A κ).map p.pr = β.b * g.val * β.b' → (mt B.V₀ (B.o.emb (κ, 1))).map p.pr = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  first | exact @GlobalTheory.FinPl.CoreMat.coreMat | exact GlobalTheory.FinPl.CoreMat.coreMat | (intros; apply GlobalTheory.FinPl.CoreMat.coreMat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  first | exact @GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | exact GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | (intros; apply GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem _root_.GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n) (L : GlobalTheory.FinPl.Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → β.IsLat L Λ → ∀ (κ : GA D S) (g : GL n k), (mt S κ).map p.pr = β.b * g.val * β.b' → (GlobalTheory.FinPl.Moves S κ L L (· = p.v) ↔ g • Λ = Λ) := by
  first | exact @GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq | exact GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq | (intros; apply GlobalTheory.FinPl.FrameLat.moves_iff_smul_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_integralAdele_iff_both_components : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D), a ∈ GlobalTheory.FinPl.idAt D (· = q.v) → (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.SplitInt.intAt_iff_pr | exact GlobalTheory.SplitInt.intAt_iff_pr | (intros; apply GlobalTheory.SplitInt.intAt_iff_pr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  first | exact @GlobalTheory.LocMod.SplitCoord.coord_int_last | exact GlobalTheory.LocMod.SplitCoord.coord_int_last | (intros; apply GlobalTheory.LocMod.SplitCoord.coord_int_last <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.integral_finiteAdele_of_split_place_components : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IntPlaces.mem_intAf_of_split | exact GlobalTheory.IntPlaces.mem_intAf_of_split | (intros; apply GlobalTheory.IntPlaces.mem_intAf_of_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)), finM V hn g = k.1 → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det → finPart D (d : Formalism.L2.Theta.AE D) ∈ intAE D ∧ finPart D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := by
  first | exact @GlobalTheory.DetIntUnit.det_int_unit | exact GlobalTheory.DetIntUnit.det_int_unit | (intros; apply GlobalTheory.DetIntUnit.det_int_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

theorem isJ_smul {D : D7} {u : D.what₂.Word} {S : D.what₂.Tau → SPar} {M : Formalism.IndefR.Mult.DSModel D.sp.X' S}
    {j : SmT M →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)} (h : GlobalTheory.Core.Rk.Top.IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    GlobalTheory.Core.Rk.Top.IsJ u M (a • j) := by
  constructor
  · intro x y e
    exact h.inj (smul_right_injective (Formalism.L2.Forms.FrP D → ℂ) ha e)
  · exact (LinearMap.range_smul j a ha).trans h.range
  · intro τ g hg v w hw y y' hy
    exact congrArg (a * ·) (h.eqv τ g hg v w hw y y' hy)

theorem levG_one {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad} (K : Formalism.L2.Forms.ClassesAtPrimes M bad)
    {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (h1 : ∀ g, g ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1)
    (h2 : ∀ g (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → χ g = star ((K.lev.chi κ : ℂˣ) : ℂ)) : LevG K 1 J χ := by
  simp only [LevG, inv_one, one_mul, mul_one]
  exact ⟨h1, h2⟩


end GlobalTheory.TopVal
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevelP

theorem toMap_shift {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem toMap_eigen {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (f : Bridge.Gf V → c.W) (hy : ∀ h, (b • f) h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    a⁻¹ * c.toMap pr f v (h * κ) = b * c.toMap pr f v h :=
  (toMap_shift c hc pr κ hκ a ha f (b • f) hy v h).symm.trans
    (congrFun (LinearMap.congr_fun ((c.toMap pr).map_smul b f) v) h)

theorem mem_multT_withP {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (hu : u ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (hP : ∀ p : P.H, ∃ κ, IsLevelLift V β L p.1 κ ∧ ∀ v h,
      (levChi V β (flagL L) κ)⁻¹ * u v (h * κ) = ((P.chi p : ℂˣ) : ℂ) * u v h) :
    u ∈ MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hu)
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff]
  refine ⟨hm.aut, hm.cusp, fun v k hk g => ?_, hm.equiv, hm.cont⟩
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u v) := fun k hk g => hm.lev v k hk g
  refine IsPLevel.hasType (V := V) (β := β) (L := L) (P := P) ⟨hT, fun p => ?_⟩ k hk g
  obtain ⟨κ, hl, hκ⟩ := hP p
  funext h
  exact (level_action_spec hT ⟨κ, hl⟩ κ hl h).trans (hκ (PiTensorProduct.tprod ℂ v) h)

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_lift_eigen (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (a : D.what₂.LL) (hx : (A.fam.R t).r g x = a • x) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ v h,
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ)⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * κ) =
        D.what₂.embLL a * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v h := by
  refine (GlobalTheory.FormAction.act_eq_translate R hred hj t g x).imp fun κ hκ => ⟨hκ.1, ?_⟩
  have h3 : R.jX t ((A.fam.R t).r g x) = D.what₂.embLL a • R.jX t x :=
    (congrArg (R.jX t) hx).trans ((R.jX t).map_smulₛₗ a x)
  have h4 : (R.HX t).e (R.jX t ((A.fam.R t).r g x)) = D.what₂.embLL a • (R.HX t).e (R.jX t x) :=
    (congrArg (R.HX t).e h3).trans ((R.HX t).e.map_smul _ _)
  exact toMap_eigen R.cX hc R.prX κ hκ.1.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ) _ _
    fun h => (congrFun h4 h).symm.trans (hκ.2 h)

theorem mem_CXP_of_good (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (hirr : ∀ χ ∈ A.fam.X, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T0) (x : (A.fam.R t).S.Forms)
    (hx : x ∈ Formalism.IndefR.Cx.BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hu : R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈ CXP R (levPOf R.eG D.what₂.embLL P ψ) t := by
  rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hx
  refine mem_multT_withP R.θ R.MX R.βX (R.datXt t) (levPOf R.eG D.what₂.embLL P ψ) _ hu fun p => ?_
  have hq : R.eG.symm p.1 ∈ P := p.2
  have ha := Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type (A.fam.R t).r A.fam.X hirr P ψ ⟨_, hq⟩ x hx
  refine (exists_lift_eigen R hred hj hc t (R.eG.symm p.1) x _ ha).imp fun κ hκ => ⟨?_, hκ.2⟩
  exact ⟨hκ.1.1, hκ.1.2.1, hκ.1.2.2.trans (R.eG.apply_symm_apply p.1)⟩

end Package

end GlobalTheory.TopLevelP

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineIdeal

theorem e_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr c ∈ 𝒪[k]) := by

  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hsum hlat c
  have key : (fun r => p.e * (c * incA D (vecB o ζ r))) =
      fun r => p.sec ((α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r) := by
    funext r
    have hb : α₀.b r (Sum.inr 0) = p.pr (incA D (vecB o ζ r)) := by
      rw [hsum]; rfl
    have hv : (α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r = α₀.b r (Sum.inr 0) * p.pr c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, hb, ← map_mul, p.sec_pr, mul_comm (incA D _) c]
  rw [key, ← hlat, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
  have h1 : (Pi.single (Sum.inr 0) (p.pr c) : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j; simp
  simp [h1]

theorem mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by

  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr c hc
  have hyid : ∀ r, (fun r => c * incA D (vecB o ζ r)) r ∈ idAt D P := fun r => Ideal.mul_mem_right _ _ hc
  have hloc : (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ ∀ i,
      GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M (· = (p i).v) := by
    constructor
    · intro h i
      exact GlobalTheory.FinPlLoc.smul_latV _ (GlobalTheory.FinPlLoc.idem_mem_intAt _) h
    · intro h
      refine (GlobalTheory.FinPlLoc.part_lat P S₀ M _ hM.1).2 ⟨hyid, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
      have h1 : e • (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) =
          e • (fun r => c * incA D (vecB o ζ r)) := by
        rw [smul_smul, mul_comm, (GlobalTheory.FinPlLoc.mem_idAt_iff _ e).1 he.1]
      rw [← h1]
      exact GlobalTheory.FinPlLoc.smul_latV _ he (h i)
  rw [hloc]
  refine forall_congr' fun i => ?_
  have hεid : ∀ r, (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r ∈ idAt D (· = (p i).v) :=
    fun r => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_intAt _).1
  rw [GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts D k (p i) S₀ M _ hεid]
  have he : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * (p i).e = (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (FrameLat.e_mem_idAt (p i))
  have hce_id : cA D (p i).e ∈ idAt D (· = (p i).v) := by
    have := Ideal.sub_mem _ (FrameLat.sum_mem_idAt (p i)) (FrameLat.e_mem_idAt (p i))
    rwa [add_sub_cancel_left] at this
  have hce : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * cA D (p i).e = cA D (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hce_id
  have e1 : (fun r => (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (p i).e, he]
  have e2 : (fun r => cA D (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => cA D (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (cA D (p i).e), hce]
  rw [e1, e2, e_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) (hfr i).1 (hfr i).2 c,
    GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) hM (hfr i).1 (hfr i).2 c]

end GlobalTheory.LineIdeal

end
end
