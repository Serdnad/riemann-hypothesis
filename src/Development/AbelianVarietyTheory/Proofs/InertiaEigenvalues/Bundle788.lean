module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle781
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.Automorphisms.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstOfCrys

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem mulV_crisIncl_comm {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (c : ↥(MaximalUnramifiedExtension l)) (x : P.R.B ⊗[ℚ_[l]] V) :
    mulV P LL V c (crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V x)) =
      crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c • x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul, crisIncl_tmul, crisIncl_tmul,
      mulV_tmul, Polynomial.algebraMap_apply, smul_eq_mul, C_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem isPst_of_isCrys (T : LocTied l P AI) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (hc : IsCrys (P.PD K) ρ) : IsPst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.Per.TiedRestrict.fracInv_of_tied T K
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  obtain ⟨hfin, -⟩ := GlobalTheory.RegularRing.finite_le₀ (P.PD K) hf ρ
  have hd := (GlobalTheory.RegularRing.isCrys_iff_finrank (P.PD K) ρ).1 hc
  let e := set_option synthInstance.maxHeartbeats 200000 in
    Module.finBasisOfFinrankEq ↥(K0 K) _ hd
  have hB := GlobalTheory.RegularRing.indepB (P.PD K) hf ρ e e.linearIndependent
  have hmem : ∀ i, crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V (e i : P.R.B ⊗[ℚ_[l]] V)) ∈ Dpst P ρ := by
    intro i
    refine (mem_Dpst P ρ).mpr ⟨K, fun g _ => ?_⟩
    rw [stRep_crisIncl]
    congr 1
    exact (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris (PD := P.PD K) ρ _).1 (e i).2 g
  let y : Fin (finrank ℚ_[l] V) → DpstUr P ρ := fun i => toUr P ρ ⟨_, hmem i⟩
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = 0 := by
      rw [hc]; rfl
    have h2 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
        crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V
          (∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V))) := by

      rw [map_sum, Submodule.coe_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulV_crisIncl_comm]
      rfl
    rw [h2] at h1
    have h3 : ∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V) = 0 :=
      (TensorProduct.comm ℚ_[l] P.R.B V).injective
        (crisIncl_injective P (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    have h4 := Fintype.linearIndependent_iff.1 hB (fun j => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j)) h3 i
    exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h4.trans (map_zero _).symm)
  have hlow : (finrank ℚ_[l] V : Cardinal) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
    have := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype, Fintype.card_fin] at this
  have hV : Module.rank ℚ_[l] V = (finrank ℚ_[l] V : Cardinal) := (Module.finrank_eq_rank ℚ_[l] V).symm
  rw [IsPst, hV]
  exact le_antisymm hup hlow

end GlobalTheory.PstOfCrys

namespace GlobalTheory.PstOfCrys

theorem pst_of_pc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  intro D i w hw K' h hN hF hS m r _ hpc
  let r' : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin m) ↥(D.nbr i w hw).LL.1 :=
    mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))
  have hmodel : IsModel (D.nbr i w hw)
      (resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) (D.nbr i w hw).LL r' := by
    refine ⟨le_rfl, ?_⟩
    ext g a b
    exact ((D.loc_tie i w hw).1 _).symm
  refine ⟨(D.nbr i w hw).LL, r', hmodel, ?_⟩
  have hc := ((GlobalTheory.PcRes.main _ (D.loc (D.nd.l i)) _ K' (D.nbr i w hw).LL h hN hF hS _ _).2).1 hpc
  have hp := isPst_of_isCrys (D.locT (D.nd.l i)) _ hc
  exact (GlobalTheory.PstLaws.isPst_resTo_iff (D.loc (D.nd.l i)) _ h).1 hp

end GlobalTheory.PstOfCrys
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.ConjDual

theorem valuation_lt_one_iff {Ω : Type} [Field Ω] {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω)
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) : A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hA, map_inv₀,
    EmbeddingLike.map_eq_zero_iff]

theorem tame_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {a : WDRep h V}
    (ha : a.Tame) : a.dual.Tame := by
  intro σ hσ
  have h1 : a.ρ σ⁻¹ = 1 := ha σ⁻¹ ((Wild E A).inv_mem hσ)
  rw [WDRep.dual_ρ, h1]
  ext
  simp

theorem transport_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'} (s : E → E) (c : Ω ≃+* Ω)
    (hc : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (x : WD h) (x' : WD h') (n : ℕ)
    (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ))
    (hb : WD.mk b = x.lpDual) (hb' : WD.mk b' = x') (hN : b.N = b'.N)
    (hρ : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ') :
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧ (x.tame → x'.tame) := by
  subst hb'
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpDual_mk] at hb
    refine ⟨fun h0 => ?_, ?_, fun h0 => ?_⟩
    · rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0 ⊢
      rw [← hN, ← WD.monodromyZero_ofWeilDeligneRepClass_iff, hb, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.dual_N, h0]
      ext
      simp
    · have h1 := congrArg WD.lpDim hb
      rw [WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq] at h1
      rw [WD.lpDim_mk, WD.lpDim_mk, h1]
    · rw [WD.tame_mk] at h0 ⊢
      have h1 : b.Tame := by
        rw [← WD.tame_mk, hb, WD.tame_mk]
        exact tame_dual h0
      intro τ' hτ'
      let σ : G E Ω :=
        { (c.trans ((τ' : G E Ω) : Ω ≃+* Ω)).trans c.symm with
          commutes' := fun r => by
            show c.symm ((τ' : G E Ω) (c (algebraMap E Ω r))) = _
            rw [hc, AlgEquiv.commutes, ← hc, RingEquiv.symm_apply_apply] }
      have hσ : ∀ z, c (σ z) = (τ' : G E Ω) (c z) := fun z => c.apply_symm_apply _
      have hw : σ ∈ Wild E A := fun y hy => by
        rw [valuation_lt_one_iff c hA, map_sub, map_div₀, map_one, hσ]
        exact hτ' _ ((_root_.map_ne_zero c).2 hy)
      rw [← hρ ⟨σ, Ine_le_Weil h (Wild_le_Ine hw)⟩ τ' hσ]
      exact h1 _ hw

theorem mono_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  intro D w w' c hc hA x x' n b b' hb hb' hN hρ
  obtain ⟨h1, h2, h3⟩ := transport_dual (fun y => D.host.conj y) c hc hA x x' n b b' hb hb' hN hρ
  refine ⟨h1, h2, fun H σ _ hσ => ?_⟩
  exact (WD.tame_iff_inePol x').mp (h3 ((WD.tame_iff_inePol x).mpr
    fun τ hτ => H τ (Wild_le_Ine hτ) hτ)) σ hσ

end GlobalTheory.WeilDeligne.ConjDual
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.LabTransport

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}

theorem val_lt_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A'.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc,
    map_eq_zero_iff _ c.injective]


omit [NumberField E] in
theorem normV_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') : normV w' = normV w := by
  let t : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv s
  have h1 : w.asIdeal = w'.asIdeal.comap t := by
    ext x
    rw [Ideal.mem_comap, ← h x, ← h' (t x), ← val_lt_iff c hc, hs]
    rfl
  have h2 : w'.asIdeal = w.asIdeal.map (t : 𝓞 E →+* 𝓞 E) := by
    rw [h1]
    exact (Ideal.map_comap_of_surjective (t : 𝓞 E →+* 𝓞 E) t.surjective _).symm
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal w'.asIdeal t h2).toEquiv).symm


open Pointwise in
theorem mem_Ine_of (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) (h : γ ∈ Ine (F := E) A) : γ' ∈ Ine (F := E) A' := by
  refine ⟨?_, fun x hx => ?_⟩
  · change γ' • A' = A'
    ext x
    obtain ⟨x, rfl⟩ := γ'.surjective x
    obtain ⟨x, rfl⟩ := c.surjective x
    rw [← AlgEquiv.smul_def, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, hγ,
      ← hc, ← hc, apply_mem_iff_of_mem_Dec h.1]
  · obtain ⟨x, rfl⟩ := c.surjective x
    rw [hγ, ← map_sub, val_lt_iff c hc]
    refine h.2 x ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hc x).mpr hx

theorem mem_Ine_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Ine (F := E) A' ↔ γ ∈ Ine (F := E) A :=
  ⟨mem_Ine_of c.symm (fun y => by rw [hc, c.apply_symm_apply])
    (fun y => by rw [eq_comm, c.symm_apply_eq, ← hγ, c.apply_symm_apply]), mem_Ine_of c hc hγ⟩


omit [NumberField E] in
theorem mem_Wild_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Wild E A' ↔ γ ∈ Wild E A := by
  rw [mem_Wild, mem_Wild, c.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [map_ne_zero_iff _ c.injective, hγ, ← val_lt_iff c hc, map_sub c,
    map_div₀ c, map_one c]


omit [NumberField E] in
theorem exists_conj (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ : G E Ω) :
    ∃ γ' : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (c.symm.trans γ.toRingEquiv).trans c) fun x => ?_,
    fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective x
    show c (γ (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, AlgEquiv.commutes]
  · show c (γ (c.symm _)) = _
    rw [c.symm_apply_apply]


omit [NumberField E] in
theorem exists_conj' (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ' : G E Ω) :
    ∃ γ : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  obtain ⟨γ, hγ⟩ := exists_conj s.symm c.symm
    (fun x => by rw [c.symm_apply_eq, hs, s.apply_symm_apply]) γ'
  refine ⟨γ, fun y => ?_⟩
  have := hγ (c y)
  rw [c.symm_apply_apply] at this
  rw [this, c.apply_symm_apply]

variable [IsAlgClosure E Ω]

theorem lab_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : WDRep h V) (b' : WDRep h' V)
    (hb : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ')
    {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) :
    WD.lab t γ' (WD.mk b') = WD.lab t γ (WD.mk b) := by
  have hiff : TeichmullerInertiaLabelCondition A' w' t γ' ↔ TeichmullerInertiaLabelCondition A w t γ := by
    unfold TeichmullerInertiaLabelCondition
    rw [normV_eq s c hs hc h h', mem_Ine_iff c hc hγ]
  by_cases H : TeichmullerInertiaLabelCondition A w t γ
  · have H' := hiff.mpr H
    have hsp : b.tameSpace = b'.tameSpace := by
      ext v
      rw [WDRep.mem_tameSpace, WDRep.mem_tameSpace]
      constructor
      · intro hv σ' hσ'
        obtain ⟨σ, hσ⟩ := exists_conj' s c hs (σ' : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mp hσ'
        rw [← hb ⟨σ, Ine_le_Weil h (Wild_le_Ine h1)⟩ σ' fun z => (hσ z).symm]
        exact hv _ h1
      · intro hv σ hσ1
        obtain ⟨σ', hσ⟩ := exists_conj s c hs (σ : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mpr hσ1
        rw [hb σ ⟨σ', Ine_le_Weil h' (Wild_le_Ine h1)⟩ fun z => (hσ z).symm]
        exact hv _ h1
    have he : WD.tameEig (WD.mk b') γ' = WD.tameEig (WD.mk b) γ := by
      rw [WD.tameEig_mk _ (Ine_le_Weil h' H'.2.1), WD.tameEig_mk _ (Ine_le_Weil h H.2.1),
        ← LinearEquiv.charpoly_conj (LinearEquiv.ofEq _ _ hsp)]
      congr 2
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact (LinearMap.congr_fun (hb ⟨γ, Ine_le_Weil h H.2.1⟩ ⟨γ', Ine_le_Weil h' H'.2.1⟩
        fun z => (hγ z).symm) v).symm
    rw [WD.lab_eq_iff H', he]
    exact ⟨WD.lab_monic _ _ _, WD.map_rootsBar_lab H _⟩
  · rw [WD.lab_of_not H, WD.lab_of_not (mt hiff.mp H)]

end General

theorem main : ∀ (D : D7) (k : Fin 2) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    ∀ γ γ' : GE D.nd, (∀ y, γ' (c y) = c (γ y)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') =
      (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by
  intro D k w w' c hs hc x x' n b b' hx hx' _ hb γ γ' hγ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  subst hx'
  rw [lab_eq D.host.conj.toRingEquiv c hs hc b b' hb (D.ntypes.teichC k) hγ, hx]
  exact LabDual.rootsBar_lab_lpDual _ _ _ _ _ _ _ _ x

end GlobalTheory.WeilDeligne.LabTransport
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.JacquetEmptyFirstBlock

theorem jacquet_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    π.IsIrreducible → ∀ (h : 0 + n = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  intro k _ _ _ _ n V _ _ π hπ h
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · exact Fin.elim0 y
    · rfl
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : IsSimpleOrder (Subrepresentation π) := hπ
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

end GlobalTheory.SmGL.JacquetEmptyFirstBlock
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

theorem _root_.GlobalTheory.T.petersson_integral_formula : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  first | exact @GlobalTheory.AdjUp.ip_eq_mul_integral_val | exact GlobalTheory.AdjUp.ip_eq_mul_integral_val | (intros; apply GlobalTheory.AdjUp.ip_eq_mul_integral_val <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.realLowestKType_of_extremalVectorCase : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → RealLow R i t := by
  first | exact @GlobalTheory.RawLift.RealLowRed.realLow_of_ext | exact GlobalTheory.RawLift.RealLowRed.realLow_of_ext | (intros; apply GlobalTheory.RawLift.RealLowRed.realLow_of_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf

namespace GlobalTheory.GoodFree

end GlobalTheory.GoodFree
end
