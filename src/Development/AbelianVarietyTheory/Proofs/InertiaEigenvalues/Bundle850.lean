module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExists
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.algebraic_weight_dominant_iso_exists : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → L →+* ℂ), Function.Injective (emb) → (∀ t t', (emb) t ≠ ComplexEmbedding.conjugate ((emb) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (emb) t ∨ σ = ComplexEmbedding.conjugate ((emb) t)) → ∀ a : NG.AlgWt L n, ∃ (lam : ι → DomWeight n) (T : a.W ≃ₗ[ℂ] VV ℂ lam), ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (a.ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtClass.exists_equiv_VV | exact GlobalTheory.WtClass.exists_equiv_VV | (intros; apply GlobalTheory.WtClass.exists_equiv_VV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.SideTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fi
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fiOf (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) : FormsIso (R.FW i') (R.FW i) := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ => rfl, LinearEquiv.refl _ _, MulEquiv.refl _, fun _ => LinearIsometryEquiv.refl _ _,
    fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem fiOf_heq (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (x : Fin (R.nW i') → D.what₂.LL) :
    HEq ((fiOf R i' i h).e x) x := by
  subst h; rfl

theorem fiOf_eG (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (g : G) : (fiOf R i' i h).eG g = g := by
  subst h; rfl

end Fi

end GlobalTheory.TwInputs.SideTies
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlacesOver

theorem mem_placesOver : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ P ∈ Rl.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC P hP
  obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
  refine ⟨k, ?_⟩
  have h1 := Rl.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ P.asIdeal := h1
  simpa [placesOver] using h2

end GlobalTheory.TypePlacesOver
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOfReal

theorem exists_frame_real : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j
  have hBV := hC.models.BV j
  have hu : ∀ τ, IsUnit (Rl.BV j τ) := fun τ => by
    obtain ⟨ε, hε, h2, -⟩ := hBV τ
    have hd : (Matrix.diagonal fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rcases hε a with h | h <;> simp [h.1]
    refine IsUnit.of_mul_eq_one_right (Matrix.diagonal (fun a => (ε a : ℂ)) * (Matrix.conjTranspose (Rl.BV j τ) * gramAt D (Vc D j) τ)) ?_
    rw [Matrix.mul_assoc, h2, hd]
  have sdV := hC.lev.βV j
  have sdW := hC.lev.βW j
  have bV : Lev.IsBaseFrame (Vc D j) (Rl.βV j) (Rl.ΛV j) 1 := by
    obtain ⟨c, hc⟩ := sdV
    rwa [one_pow] at hc
  have bW : Lev.IsBaseFrame (Wc D j) (Rl.βW j) (Rl.ΛW j) 1 := by
    obtain ⟨c, hc⟩ := sdW
    rwa [one_pow] at hc
  have hv := (hC.thP.vP j A3.A.μ0).1
  have hstd := (hC.thP.ωP j A3.A.μ0).std
  refine ⟨⟨Rl.ψ, Rl.θ, cart (Rl.MW j (sg0 D A3.A)), fun τ => (hu τ).unit, onb (Rl.MW j (sg0 D A3.A)), Rl.ΛV j, Rl.ΛW j,
    Rl.βV j, Rl.βW j, Rl.vacP j⟩, ?_, hstd, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, bV, bW⟩
  exact
    { rank_le := (D.sp.W_rank _ (Nat.le_add_left _ _) j.2).le.trans (r_le_V j)
      onbS := hBV
      cartT := fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
      onbT := fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order j τ)
      sdS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdV
      sdT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdW
      frS := bV.1
      frT := bW.1
      vac := hv }

end GlobalTheory.FrameOfReal
end
