module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle011
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle673
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

theorem hasGram_norm_sum_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {N : (K →+* ℂ) → V → ℝ} (hN : GlobalTheory.AllWt.HasGram N) (σ : K →+* ℂ)
    (hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y) {ι : Type} (s : Finset ι) (y : ι → V) :
    N σ (∑ i ∈ s, y i) ≤ ∑ i ∈ s, N σ (y i) ∧ ∀ z, 0 ≤ N σ z := by
  obtain ⟨⟨n, ⟨b, X⟩, hbX⟩⟩ := hN
  letI : StarRing K := starRingOfComm
  let Φ : V →+ EuclideanSpace ℂ (Fin n) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X (InfinitePlace.mk σ) y)
      map_zero' := by rw [Formalism.HermitianLatticesTheory.fcoord_zero]; rfl
      map_add' := fun y z => by rw [Formalism.HermitianLatticesTheory.fcoord_add]; rfl }
  have hΦ : ∀ y, N σ y = ‖Φ y‖ := by
    intro y
    rw [← hτ, ← (hbX (InfinitePlace.mk σ)).2 y, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]
    rfl
  refine ⟨?_, fun z => (hΦ z).symm ▸ norm_nonneg _⟩

  rw [hΦ, map_sum]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun g _ => (hΦ _).symm))

theorem sum_sq_normW_cuspPh_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W) (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (B : ℝ), 0 ≤ B → GlobalTheory.AllWt.HasGram (GlobalTheory.AllWt.normW U x V dict (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g = GlobalTheory.AllWt.normW U x V dict (G + W) σ f) → (∀ (γ : LevelAut Dw l) (f : cuspW Xo c U G) (g : cuspW Xo c U (G + W)), (g : Rul Xo c) = f * pull Xo c γ u → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict G σ f) → ∀ (f : cuspW Xo c U G) (σ : c.F →+* ℂ), ∑ h : S, GlobalTheory.AllWt.normW U x V dict (G + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ^ 2 ≤ (Fintype.card S : ℝ) ^ 3 * B ^ 2 * GlobalTheory.AllWt.normW U x V dict G σ f ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hK hKW χ u B hB hGram hinv hbd f σ
  set N := GlobalTheory.AllWt.normW U x V dict (G + W) with hN
  have hconj : ∀ y, N ((starRingEnd ℂ).comp σ) y = N σ y := fun y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.petW, GlobalTheory.AllWt.petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y := by
    intro y
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      rw [h, e, hconj]
  have hnn : ∀ y, 0 ≤ N σ y := (hasGram_norm_sum_le hGram σ hτ (∅ : Finset S) (fun _ => 0)).2
  have hsum : ∀ (s : Finset S) (y : S → cuspW Xo c U (G + W)), N σ (∑ g ∈ s, y g) ≤ ∑ g ∈ s, N σ (y g) :=
    fun s y => (hasGram_norm_sum_le hGram σ hτ s y).1
  have hsmul : ∀ (a : c.F) (y : cuspW Xo c U (G + W)), N σ (a • y) = ‖σ a‖ * N σ y := fun a y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, Submodule.coe_smul, GlobalTheory.AllWt.petW_smul]
  have hunit : ∀ g : S, ‖σ (((χ g)⁻¹ : (c.F)ˣ) : c.F)‖ = 1 := by
    intro g
    have h1 : ((χ g)⁻¹) ^ (Fintype.card S) = 1 := by rw [← map_inv, ← map_pow, pow_card_eq_one, map_one]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card S) ?_ Fintype.card_ne_zero
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have hcomp : ∀ h : S, N σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
      (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ≤
        (Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f) := by
    intro h
    have hFm : (f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u ∈ cuspW Xo c U (G + W) :=
      GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW (h : LevelAut Dw l) _ u.2)
    have hP : ∀ g : S, pull Xo c (g : LevelAut Dw l) ((f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u) ∈
        cuspW Xo c U (G + W) := fun g => hK (g : LevelAut Dw l) _ hFm
    have he : ((GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
        (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h : cuspW Xo c U (G + W)) : Rul Xo c) =
          ((∑ g : S, (((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)) : cuspW Xo c U (G + W)) :
            Rul Xo c) := by
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      rfl
    rw [Subtype.ext he]
    refine (hsum _ _).trans ?_
    calc ∑ g : S, N σ ((((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)))
        ≤ ∑ _g : S, B * GlobalTheory.AllWt.normW U x V dict G σ f := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [hsmul, hunit, one_mul, hinv (g : LevelAut Dw l) ⟨_, hFm⟩ ⟨_, hP g⟩ rfl σ]
          exact hbd (h : LevelAut Dw l) f ⟨_, hFm⟩ rfl σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc _ ≤ ∑ _h : S, ((Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f)) ^ 2 :=
        Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (hnn _) (hcomp h) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GlobalTheory
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnCmp


open Classical in
theorem exists_baseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∃ ω φ, IsBaseKernel R i v (ownAt D v) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu
  obtain ⟨ψw, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hδ : R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = R.xiH (R.mu v) * ψw⁻¹ := by rw [hxi, mul_inv_cancel_right]
  have htame : ∀ P, (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TameAt P := by
    intro P
    unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
    intro x hx hle
    have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
        (a * b).loc P x = a.loc P x * b.loc P x := rfl
    have loc_inv (a : Formalism.L2.Host.HChar D.host.E) :
        (a⁻¹).loc P x = (a.loc P x)⁻¹ := rfl
    rw [hδ, loc_mul, loc_inv, hL.xi_tame (R.mu v) P x hx hle, hψ.tame P x hx hle,
      inv_one, mul_one]
  have htriv : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TrivOn D.host.F := by
    rw [hδ]; exact (hL.xi_triv (R.mu v)).mul hψ.triv.inv
  have hunit : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).IsUnitary := by
    obtain ⟨n, hn, hno⟩ := hL.xi_fin (R.mu v)
    obtain ⟨a, ha⟩ := hψ.ord
    refine Formalism.L2.Host.HChar.isUnitary_of_order (n := n * Formalism.EigenvalueLevelCeiling.plc v ^ a)
      (Nat.mul_pos hn (pow_pos (Formalism.EigenvalueLevelCeiling.plc_prime v).pos a)) ?_
    show _ ^ (n * _) = 1
    rw [hδ, mul_pow, inv_pow, pow_mul, hno, one_pow, one_mul, mul_comm n, pow_mul, ha, one_pow, inv_one]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CharTransport.exists_chrEq D _ hunit
  have hF : ∀ a, χ (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hχ htriv
  have hr0 : ResEta D χ 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ a => by rw [hF a, pow_zero]⟩
  have h0 := hC.thP.ωP i A.μ0
  obtain ⟨ω, hω, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D R.ψ h0.std _ _ _ _ χ χ _ h0 hχ.1 hχ.1 hr0 hr0
  have hx0 : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have hω' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
    convert hω using 2
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
      exact mul_right_comm _ _ _
  choose ξR hξR using fun PP => GlobalTheory.exists_isRes_of_tameAt D _ PP (htame PP)
  have hsub : placesOver R (R.mu v) (ownAt D v) ⊆ R.Q (R.mu v) := Finset.filter_subset _ _
  obtain ⟨e0, he0, -⟩ := (hC.thP.vP i (R.mu v)).2
  have hsub' : R.Pg ∪ placesOver R (R.mu v) (ownAt D v) ⊆ R.Pg ∪ R.Q (R.mu v) := Finset.union_subset_union le_rfl hsub
  have hnc : ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ P' ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v),
      ¬ Lev.IsConjPl P P' := fun P hP P' hP' =>
    GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0 P (hsub' hP) P' (hsub' hP')
  obtain ⟨cV, hcV⟩ := hL.βV i
  obtain ⟨cW, hcW⟩ := hL.βW i
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i)
    (R.ΛW i) (R.βV i) (R.βW i) R.Pg (placesOver R (R.mu v) (ownAt D v)) ξR (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcV)
    (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcW) hcV.1 hcW.1 ((Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL (R.mu v)).mono_right hsub)
    (Formalism.IndefR.Fin.idemSum_of_noConj _ hnc) (R.vacP i) (hC.thP.vP i (R.mu v)).1
  refine ⟨ω, φ, ?_⟩
  unfold IsBaseKernel IsKernel
  exact ⟨χ, ξR, hχ, fun PP _ => hξR PP, hω', hφ⟩

end GlobalTheory.OnCmp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)



theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallSpan

variable {D : D7} {m n : ℕ}


open GlobalTheory.ExportSeries.Onto in
theorem exists_harm (w : _root_.GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (F : VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n) := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle (Submodule.mem_map_of_mem F.2)


open GlobalTheory.ExportSeries.HarmLattice in
theorem harmLat_le_span {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 K, σ a ∈ O') (w : _root_.GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : Submodule.IsFullLattice D.host.E M) {P : PolF D m n} (hP : P ∈ harmLat σ (fun τ => f.comp (emb τ)) O' m w B M) :
    P ∈ Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n)) := by
  set N := Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n))
  have hN : N ≤ (harm m w B).restrictScalars O' := Submodule.span_le.2 fun Q hQ => hQ.1
  have hle : coefLatFn σ (fun τ => f.comp (emb τ)) O' w.lam M ≤ N.map ((harmFn m w B).restrictScalars O') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' := GlobalTheory.NabBC.nabBaseChange _ _ _ _ n f emb w.lam M hM hF
    rw [coefFn_eq, SetLike.mem_coe]
    clear hF
    induction hF' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, e⟩ := hy
      obtain ⟨Q, hQ, eQ⟩ := exists_harm w B hw hm (GlobalTheory.CoefModel.mapVV (σ.comp f) w.lam x)
      have e1 : harmFn m w B Q = coefFn (σ.comp f) w.lam (x : Pol K₀ D.what₂.Tau n) := eQ.trans (coefFn_eq _ _ x).symm
      refine ⟨Q, Submodule.subset_span ⟨hQ, ?_⟩, ?_⟩
      · exact Submodule.subset_span ⟨x, hx, e1⟩
      · refine eQ.trans (congrArg (cf w.lam) (Subtype.ext ?_))
        change MvPolynomial.map (σ.comp f) x.1 = MvPolynomial.map σ y.1
        rw [e, MvPolynomial.map_map]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hO' a⟩ : O') h1
  obtain ⟨Q, hQ, e⟩ := hle hP.2
  have h0 : P - Q = 0 := GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm _ (sub_mem hP.1 (hN hQ)) (by
    rw [map_sub, sub_eq_zero]
    exact e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem isLattice_latAt {S T : HSp D} {B : Base S T} (hF : B.F.Good) (h : Bridge.Gf S) :
    Submodule.IsFullLattice D.host.E (B.latAt h) :=
  by
  classical
  have hspan : Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E)) = ⊤ := by
    let W := Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E))
    change W = ⊤
    by_contra hW
    let g : (Fin S.rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
      { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * S.gram i j * y.1 j
                            map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                            map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
        map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin S.rank → D.host.E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let v : Fin S.rank → D.host.E := fun i => star (x i)
    have hv0 : v ≠ 0 := by
      intro hv
      apply hx0
      funext i
      have hi := congrFun hv i
      simpa [v] using congrArg star hi
    have hline (r : D.host.E) : r • v ∈ B.F.ΛS := by
      apply (hF.sdS.2 _).2
      intro y hy
      have hz : (∑ i, ∑ j, x i * S.gram i j * y j) = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hzy : (∑ i, ∑ j, star (y i) * S.gram i j * v j) = 0 := by
        have hg (i j : Fin S.rank) : star (S.gram i j) = S.gram j i := by
          exact S.herm.eq _ _
        have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * S.gram i j * y j) = 0 := by rw [hz, map_zero]
        simp only [map_sum, map_mul] at hs
        change (∑ i, ∑ j, star (x i) * star (S.gram i j) * star (y j)) = 0 at hs
        simp only [hg] at hs
        rw [Finset.sum_comm] at hs
        simpa [mul_comm, mul_left_comm, mul_assoc] using hs
      refine ⟨0, ?_⟩
      simp only [map_zero, Pi.smul_apply, smul_eq_mul]
      calc
        0 = r * (∑ i, ∑ j, star (y i) * S.gram i j * v j) := by rw [hzy, mul_zero]
        _ = ∑ i, ∑ j, star (y i) * S.gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      apply hv0
      funext i
      simpa using not_exists.mp hn i
    let coord := (LinearMap.proj i : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
    have htop : B.F.ΛS.map coord = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ hF.sdS.1.fg.map coord)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hspan _

end GlobalTheory.SmallSpan

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  first | exact @GlobalTheory.SUGenPairs.eq_prod_pairs | exact GlobalTheory.SUGenPairs.eq_prod_pairs | (intros; apply GlobalTheory.SUGenPairs.eq_prod_pairs <;> assumption)
end
