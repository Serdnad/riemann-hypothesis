module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResEqOneIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Formalism.LocalRingCardinality.SpanPowerMembership
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmLattice

theorem fg_span_comap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (O : Subring ℂ)
    (H : Submodule ℂ V) (f : V →ₗ[ℂ] W) (hinj : ∀ P ∈ H, f P = 0 → P = 0) (L : Submodule O W) (hfg : L.FG)
    (hsp : Submodule.span ℂ (L : Set W) = H.map f) :
    (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).FG ∧
      Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = H := by
  have him : f '' ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have : y ∈ H.map f := hsp ▸ Submodule.subset_span hy
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (f.restrictScalars O) ?_ ?_
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).map (f.restrictScalars O) = L :=
        SetLike.coe_injective him
      rw [this]
      exact hfg
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)) ⊓ LinearMap.ker (f.restrictScalars O) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hinj x hx.1.1 hx.2
      rw [this]
      exact Submodule.fg_bot
  · have hle : Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) ≤ H :=
      Submodule.span_le.2 fun x hx => hx.1
    refine le_antisymm hle fun x hx => ?_
    have : f x ∈ (Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V)).map f := by
      rw [Submodule.map_span, him, hsp]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, e⟩ := this
    have h0 : x - y = 0 := hinj _ (sub_mem hx (hle hy)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 h0]
    exact hy

variable {D : D7} {n : ℕ}

def cf (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add (f := _), Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem coefFn_eq {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cf lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

private theorem nabAtr_full (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.IsFullLattice K (nabAtr emb lam M) := by
  classical
  refine nb_lattice (nb_comm_nab lam) _ fun τ => ?_
  obtain ⟨m, x, ξ, hx, hξ, h⟩ := GlobalTheory.TauLat.exists_dual_family M hM
  let e (z : Fin n → D.host.E) (a : Fin n) : K := emb τ (z a)
  have hx' (i : Fin m) : e (x i) ∈ tauLat emb τ M :=
    Submodule.subset_span ⟨x i, hx i, rfl⟩
  have hξ' (i : Fin m) : e (ξ i) ∈ dualFr (tauLat emb τ M) := by
    intro y hy
    change y ∈ Submodule.span (𝓞 K) (e '' (M : Set (Fin n → D.host.E))) at hy
    induction hy using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      change (fun a => emb τ (ξ i a)) ⬝ᵥ (fun a => emb τ (z a)) ∈ _
      rw [← GlobalTheory.TauLat.map_dot]
      exact du_map_mem_one _ ((GlobalTheory.TauLat.mem_one_iff _).2 (hξ i z hz))
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add _ _ _ _ hy hz => rw [dotProduct_add]; exact add_mem hy hz
    | smul c _ _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy
  have hexpand (y : Fin n → K) :
      y = ∑ i, (y ⬝ᵥ e (x i)) • e (ξ i) := by
    simpa only [dotProduct_comm y, e] using GlobalTheory.TauLat.expand_left (emb τ) h y
  refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := ?_ }
  · refine ⟨Finset.univ.image (fun i => e (ξ i)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Submodule.span_le, Set.range_subset_iff]
      exact hξ'
    · intro y hy
      rw [hexpand y]
      exact Submodule.sum_mem _ fun i _ =>
        du_smul_of_mem_one _ (hy _ (hx' i)) (Submodule.subset_span (by simp))
  · rw [eq_top_iff]
    intro y _
    rw [hexpand y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hξ' i))

theorem coefLatFn_fg (hc : IsCoefRing σ emb O) (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    (coefLatFn σ emb O lam M).FG := by
  obtain ⟨s, hs, e⟩ := Submodule.fg_def.1 (nabAtr_full (emb := emb) lam hM).fg
  refine Submodule.fg_def.2 ⟨(fun F => cf lam (GlobalTheory.CoefModel.mapVV σ lam F)) '' s, hs.image _, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, e ▸ Submodule.subset_span hF, (coefFn_eq σ lam F).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    rw [coefFn_eq, SetLike.mem_coe]
    rw [← e] at hF
    induction hF using Submodule.span_induction with
    | mem F h => exact Submodule.subset_span ⟨F, h, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hc.int a⟩ : O) h1

theorem span_coefLatFn (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.span ℂ (coefLatFn σ emb O lam M : Set (GLR D n → ℂ)) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ lam, φ = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)} := by
  rw [coefLatFn, Submodule.span_span_of_tower]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨F, -, rfl⟩
    exact ⟨_, coefFn_eq σ lam F⟩
  · rintro _ ⟨F, rfl⟩
    have key : ∀ G : VV K lam, cf lam (GlobalTheory.CoefModel.mapVV σ lam G) ∈
        Submodule.span ℂ {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)} := by
      intro G
      have hG : G ∈ Submodule.span K (nabAtr emb lam M : Set (VV K lam)) := by
        rw [(nabAtr_full (emb := emb) lam hM).span_eq_top]
        exact Submodule.mem_top
      induction hG using Submodule.span_induction with
      | mem F h => exact Submodule.subset_span ⟨F, h, (coefFn_eq σ lam F).symm⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
      | smul a F _ h1 =>
        rw [LinearMap.map_smulₛₗ, map_smul]
        exact Submodule.smul_mem _ _ h1
    have hF : F ∈ Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) := by
      rw [GlobalTheory.CoefModel.span_mapVV]; trivial
    change cf lam F ∈ _
    have := Submodule.mem_map_of_mem (f := cf lam) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact key _

theorem harmLat_fg_span : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  exact fg_span_comap O (harm m w B) (harmFn m w B) (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm) _ (coefLatFn_fg hc w.lam hM)
    ((span_coefLatFn w.lam hM).trans (GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm).symm)

end GlobalTheory.ExportSeries.HarmLattice

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KUTransfer

theorem ku_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  intro L _ _ _ n w σ b hb p hp x
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  have hK : ∀ g : GL (Fin n) (w.adicCompletion L), g ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      g ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := by
    intro g
    show g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L w) ↔ _
    rw [hO]; rfl
  have h1 : p x ∈ Formalism.UG.KU σ n ↔ (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [hK]
    show (p x).val ∈ Formalism.UG.intPts (Formalism.UG.intL _).subtype (Formalism.UG.GU σ n) ↔ _
    exact ⟨fun h => h.2, fun h => ⟨(p x).2, h⟩⟩
  rw [h1, hp]
  have hbi : b⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hb
  constructor
  · intro h
    have := (GlobalTheory.LFun.KGL w (n := n)).mul_mem (( GlobalTheory.LFun.KGL w (n := n)).mul_mem hb h) hbi
    simpa [mul_assoc] using this
  · intro h
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem hbi h) hb

end GlobalTheory.KUTransfer
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertOfUnramInv

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 L)) (x : w.adicCompletion L) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 L, Valued.v (x - algebraMap L (w.adicCompletion L) (a : L)) < 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k
  have hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1} := by
    have h := (Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)
    simpa [Valuation.restrict_lt_one_iff] using h
  obtain ⟨y, hy⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩
  have hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1 := hy
  have hyv : w.valuation L y ≤ 1 := by
    rw [← hval]
    calc Valued.v (algebraMap L (w.adicCompletion L) y)
        = Valued.v ((algebraMap L (w.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (w.adicCompletion L) y - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy'.le hx
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1
  refine ⟨a, ?_⟩
  have e : x - algebraMap L (w.adicCompletion L) (a : L) =
      -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) -
        algebraMap L (w.adicCompletion L) y) := by ring
  rw [e]
  refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_
  rw [Valuation.map_neg, ← map_sub, hval]
  simpa using ha

theorem inert_of_isUnramInv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  intro L _ _ _ v w hvw s ϖ q hsc hU
  unfold Formalism.UG.IsUnramInv at hU
  obtain ⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩ := hU
  have hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal := hvw
  have hlo : w.asIdeal.LiesOver v.asIdeal := ⟨hvw'.symm⟩
  let φ : 𝓞 L →+* w.adicCompletion L := (algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)
  have hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b) :=
    fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)
  have hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal := by
    intro b
    rw [hφ]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b
  have hfix : ∀ a : 𝓞 (maximalRealSubfield L),
      s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) := by
    intro a
    show s (algebraMap L _ _) = algebraMap L _ _
    rw [hsc]
    congr 1
    exact (IsCMField.complexConj L).commutes (a : maximalRealSubfield L)
  have hxv : Valued.v x ≤ 1 := hxO

  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1 := by
    intro hf
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hn
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := hvw'.ge
    have hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle) :=
      Ideal.quotientMap_injective' hvw'.le
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩
    obtain ⟨b, hb⟩ := exists_int_approx w x hxv
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
    have hsz := hfix a
    set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz
    have h1 : Valued.v (x - z) < 1 := by
      have e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b)) := by
        rw [map_sub]; ring
      rw [e]
      refine Valuation.map_add_lt _ hb ?_
      rw [Valuation.map_neg, hval]
      exact ha
    have h2 : s x - x = s (x - z) + -(x - z) := by
      rw [map_sub, hsz]; ring
    have h3 : Valued.v (s x - x) < 1 := by
      rw [h2]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [hsv]; exact h1
      · rw [Valuation.map_neg]; exact h1
    exact absurd hx1 (ne_of_lt h3)
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))
  have hepos := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) w.asIdeal

  have hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hsum := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L)
    (G := L ≃ₐ[maximalRealSubfield L] L)
  let F : v.asIdeal.primesOver (𝓞 L) → ℕ := fun P =>
    P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))
  have hsum' : ∑ P, F P = 2 := by
    rw [← hG2, ← hsum]
  let W : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlo⟩
  have hW : F W ≤ 2 := by
    rw [← hsum']
    exact Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)
  have hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
      w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2 := hW
  have hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2 := by
    have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) := by omega
    nlinarith
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1 := by
    rw [hf2] at hW'
    omega
  refine ⟨?_, ?_, ?_⟩
  · have : (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal := by
      rw [← hlo.over]
      exact v.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mp he1
  · rintro ⟨u, hne, hu⟩
    have hlu : u.asIdeal.LiesOver v.asIdeal := ⟨by
      rw [hlo.over]
      exact (congrArg HeightOneSpectrum.asIdeal hu).symm⟩
    let U : v.asIdeal.primesOver (𝓞 L) := ⟨u.asIdeal, u.isPrime, hlu⟩
    have hWU : W ≠ U := fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)
    have h2 : F W + F U ≤ 2 := by
      rw [← hsum', ← Finset.sum_pair hWU]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 := Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hu2 := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) u.asIdeal
    have hFU : 1 ≤ F U := Nat.mul_pos hu2 hu1
    have hFW : F W = 2 := by
      show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
        w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2
      rw [he1, hf2]
    omega
  ·
    let O := (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring
    have hmemO : ∀ b : 𝓞 L, φ b ∈ O := by
      intro b
      show Valued.v (φ b) ≤ 1
      rw [hφ]
      exact HeightOneSpectrum.valuation_le_one (K := L) w b
    let g : 𝓞 L →+* O := φ.codRestrict O hmemO
    have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1 := by
      intro y
      have hle : Valued.v (y : w.adicCompletion L) ≤ 1 := y.2
      have hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1 :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    let G := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g
    have hGs : Function.Surjective G := by
      intro Y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
      obtain ⟨b, hb⟩ := exists_int_approx w (y : w.adicCompletion L) y.2
      refine ⟨b, ?_⟩
      show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq, hmax]
      show Valued.v (φ b - (y : w.adicCompletion L)) < 1
      rw [← Valuation.map_neg, neg_sub]
      exact hb
    have hker : RingHom.ker G = w.asIdeal := by
      ext b
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk _ (g b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hmax]
      exact hval b
    have hc := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv
    rw [hker] at hc
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard'] at hn
    show q = Ideal.absNorm v.asIdeal
    exact Nat.pow_left_injective (n := 2) (by norm_num) hn.symm

end GlobalTheory.InertOfUnramInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
namespace GlobalTheory.HWL.Assembly

theorem exists_wach (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (hF : FaithH AI) (hW : WachEx AI) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  obtain ⟨ht, hπ, -⟩ := GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI hT
  refine exists_of_layers P AI (fun K s LL g => ?_) ht hπ
  obtain ⟨Γ⟩ := GlobalTheory.HWL.GroupLayer.nonempty_gamS l P K s LL g
  obtain ⟨R⟩ := GlobalTheory.HWL.Ser.nonempty_wSer l P K s LL g Γ
  obtain ⟨I, hI⟩ := GlobalTheory.HWL.IoLayer.main l P AI K s LL g Γ R
  obtain ⟨E⟩ := GlobalTheory.HWL.EtMod.nonempty_wEt l P AI K s LL g Γ R I hI (GlobalTheory.EtaleBasis.exists_etBasis l P AI hF K s LL g Γ R I hI)
  obtain ⟨Mo⟩ := hW K s LL g Γ R I hI E
  obtain ⟨Cl⟩ := GlobalTheory.HerrClassMaps.exists_classMaps l P AI K s LL g Γ R I hI E
  obtain ⟨Cm⟩ := GlobalTheory.HWL.Cmp.nonempty_cmpS l P AI hT K s LL g Γ R I hI E Mo
  exact ⟨⟨Γ, R, I, hI, E, Mo, Cl, Cm⟩⟩

end GlobalTheory.HWL.Assembly
end

section

open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
end
