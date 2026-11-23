module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doublingVector_fockPair_isCompactFinite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsKFinVec omh (Khat A a) (delta A B Φ₁ Φ₂) := by
  first | exact @GlobalTheory.Core.Rk.IP.delta_isKFinVec | exact GlobalTheory.Core.Rk.IP.delta_isKFinVec | (intros; apply GlobalTheory.Core.Rk.IP.delta_isKFinVec <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic : GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.IP.localZetaOn_split | exact GlobalTheory.Core.Rk.IP.localZetaOn_split | (intros; apply GlobalTheory.Core.Rk.IP.localZetaOn_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VReal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem biTheta_add {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ} (hf : IsBiTheta ψ A S A' f)
    (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem biTheta_zero {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem biTheta_app (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} (o : BiOp A S A')
    (ho : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i)) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) :
    IsBiTheta ψ A S A' (o.app ψ C) := by
  unfold BiOp.app
  exact Finset.sum_induction _ (IsBiTheta ψ A S A') (fun f g hf hg => biTheta_add hf hg) biTheta_zero
    fun i _ => GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC (ho i).2) (ho i).1

theorem heisO_add {S T : HSp D} (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := by
  funext x; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_zero {S T : HSp D} (w : WO S T) : heisO ψ S T w 0 = 0 := by
  funext x; simp [heisO]

theorem latVac_add {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) :=
  ⟨fun u hu => by rw [heisO_add, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_add, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem latVac_zero {S T : HSp D} {Λ : AddSubgroup (WO S T)} : IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero _, fun _ _ u _ _ => heisO_zero u⟩

theorem latVac_sum {S T : HSp D} {Λ : AddSubgroup (WO S T)} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, IsLatVac (heisO ψ S T) Λ (F i)) : IsLatVac (heisO ψ S T) Λ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ hf hg => latVac_add hf hg) latVac_zero h

def combEnd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : Module.End ℂ (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext u; simp only [GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u
    simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem vac_of_true {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (h : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v hv => absurd trivial hv, rest⟩
  unfold Vac IsLatVac at h ⊢
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem vac_union (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (P : Pl D → Prop) (LS : Lat S) (LT : Lat T) (f : WO S T → ℂ)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (h1 : Vac ψ S T LS LT P f) (h2 : Vac ψ S T LS LT (fun p => ¬ P p) f) :
    Vac ψ S T LS LT (fun _ => True) f := by
  have H := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => P p ∨ ¬ P p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  have h3 := H.2 ⟨h1, h2⟩
  rwa [e] at h3

theorem real_of (hψ : IsStdChar D ψ (-1)) (P : Pl D → Prop)
    (hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt P e → IsFinComb e ∧
      ∀ LS LT f, Vac ψ S T LS LT (fun p => ¬ P p) f → Vac ψ S T LS LT (fun p => ¬ P p) (comb ψ S T e f))
    {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS)
    (hA' : IsSelfDualC A' LA') (o : BiOp A S A') (ho : ∀ i, CombAt P (o.u i) ∧ CombAt P (o.u' i))
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (hoff : BiVacAt ψ LA LS LA' (fun p => ¬ P p) C)
    (hon : BiVacAt ψ LA LS LA' P (o.app ψ C)) :
    IsBiTheta ψ A S A' (o.app ψ C) ∧ IsBiVac ψ A S A' LA LS LA' (o.app ψ C) ∧ IsBiSmooth (o.app ψ C) := by
  have hfin : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i) :=
    fun i => ⟨(hcomb _ _ _ (ho i).1).1, (hcomb _ _ _ (ho i).2).1⟩
  have hB := biTheta_app hψ o hfin hC
  have hoffApp : BiVacAt ψ LA LS LA' (fun p => ¬ P p) (o.app ψ C) := by
    refine ⟨fun v => ⟨GlobalTheory.FrComb.slice_left hB v, ?_⟩, fun u => ⟨GlobalTheory.FrComb.slice_right hB u, ?_⟩⟩
    · have e : (fun u => o.app ψ C u v) = ∑ i, fun u => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext u; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      have hR := GlobalTheory.FrComb.biTheta_combR hψ hC (hfin i).2
      have hg : Vac ψ A S LA LS (fun p => ¬ P p) (fun u' => comb ψ S A' (o.u' i) (C u') v) :=
        ⟨GlobalTheory.FrComb.slice_left hR v, GlobalTheory.FrComb.latVac_opR (fun v => (hoff.1 v).2) (combEnd ψ S A' (o.u' i)) v⟩
      exact ((hcomb _ _ _ (ho i).1).2 LA LS _ hg).2
    · have e : o.app ψ C u = ∑ i, fun v => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext v; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      exact GlobalTheory.FrComb.latVac_opL (K := fun u' => comb ψ S A' (o.u' i) (C u'))
        (fun u' => ((hcomb _ _ _ (ho i).2).2 LS LA' _ (hoff.2 u')).2) (combEnd ψ A S (o.u i)) u
  have hT : BiVacAt ψ LA LS LA' (fun _ => True) (o.app ψ C) :=
    ⟨fun v => vac_union hψ _ _ P _ _ _ hA hS (hon.1 v) (hoffApp.1 v),
      fun u => vac_union hψ _ _ P _ _ _ hS hA' (hon.2 u) (hoffApp.2 u)⟩
  exact ⟨hB, ⟨hB.cont, fun v => hT.1 v, fun u => hT.2 u⟩, hB.smooth⟩

theorem v_real : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc hv ht hV hT hF
  have hψ := hc.std
  have hfl := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF c.ψ
  have hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt (· ∈ v.tP) e → IsFinComb e ∧
      ∀ LS LT f, Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) f → Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) (comb c.ψ S T e f) :=
    fun S T e he => (GlobalTheory.DisjComb.main D c.ψ hψ S T (· ∈ v.tP) (fun p => ¬ p ∈ v.tP) (fun p hp hq => hq hp)).2.1 e he
  refine ⟨fun j σ h Ψ₁ Ψ₂ h1 h2 => ?_, fun j h Ψ₁ Ψ₂ hW h1 h2 => ?_⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) :=
      (GlobalTheory.ContrComb.contr_comb_main D c.ψ hψ (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂)
        (hfl.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) Ψ₁ h1.1)
        (hfl.2 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) Ψ₂ h2.1)).1
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) :=
      GlobalTheory.LastBiTheta.isBiTheta_lastBi D c.ψ hψ _ _ _ _ _ _ _ (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (hW.tau j h).2 (flatBF (t.sBF j 0 h) Ψ₁) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w))
        (hfl.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) Ψ₁ h1.1) ((GlobalTheory.WeilSrc.Zero.theta_iff (c.jac j 0 h).d Ψ₂).2 h2.1)
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩

end GlobalTheory.VReal

end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.placewise_to_adelicDecomposition_forall : ∀ D : D7, GlobalTheory.FinPl.PlacesToAdeles D := by
  first | exact @GlobalTheory.FinPl.placesToAdeles_all | exact GlobalTheory.FinPl.placesToAdeles_all | (intros; apply GlobalTheory.FinPl.placesToAdeles_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.ThetaMap

variable {D : D7}

theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T w g 0 = g w := by
  have h0 : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h0]

theorem thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  intro D ψ hψ θ hθ S T S₀ T₀ ι hιc hιf hιi A hA hint hrat f hf

  have key : ∀ w, A f w = A (heisO ψ S T (ι w) f) 0 := by
    intro w
    rw [hint f w hf, heisO_apply_zero]
  have hfun : A f = fun w => (fun g => A g 0) (heisO ψ S T (ι w) f) := funext key
  obtain ⟨hc, hs⟩ := GlobalTheory.T.sobolevBoundedThetaForm_matrixCoeff_smooth D ψ hψ θ hθ S T (fun g => A g 0) hA f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro γ w
    have h1 := hrat (heisO ψ S T (ι w) f) γ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (ι w))
    rw [hint f w hf, heisO_apply_zero] at h1
    simp only [heisO] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  ·
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap ι, hUo.preimage hιc, fun u hu hui => ?_⟩
    rw [← hint f u hf, hU (ι u) hu (hιi u hui)]
  ·
    rw [hfun]
    exact hc.comp hιc
  ·
    intro k L hL hLf w
    have h2 := hs k (ι.comp L) (hιc.comp hL) (fun t => hιf (L t) (hLf t)) (ι w)
    rw [hfun]
    simpa [map_add (f := _)] using h2

end GlobalTheory.ThetaMap
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.LastKerRep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂]

theorem hasVal_transport {Q : Pair k n} {R : Pair k n₂} (G : Matrix n₂ n k) (G' : Matrix n n₂ k) (hGG : G * G' = 1)
    {e : n₂ → k} (he : R.HasVal e 1) (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ R.ker) {s : 𝓀[k]ˣ}
    (hs : Q.HasVal (G' *ᵥ e) s) (y : n → k) (a : 𝓀[k]) :
    Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a) := by
  have hGe : ∀ (r : 𝒪[k]) (z : n → k), G *ᵥ (z - r • (G' *ᵥ e)) = G *ᵥ z - r • e := by
    intro r z
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  obtain ⟨r, hr⟩ := residue_surjective (R := 𝒪[k]) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)
  have hsr : residue 𝒪[k] r * (s : 𝓀[k]) = a := by
    rw [hr, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  constructor
  · intro hy
    have h1 := hy.sub (hs.smul r)
    rw [hsr, sub_self] at h1
    have h2 := Pair.mem_ker.1 ((hker _).1 (Pair.mem_ker.2 h1))
    rw [hGe] at h2
    have h3 := h2.add (he.smul r)
    rw [sub_add_cancel, zero_add, mul_one, hr] at h3
    exact h3
  · intro hy
    have h1 := hy.sub (he.smul r)
    rw [mul_one, hr, sub_self, ← hGe] at h1
    have h2 := Pair.mem_ker.1 ((hker _).2 (Pair.mem_ker.2 h1))
    have h3 := h2.add (hs.smul r)
    rw [sub_add_cancel, zero_add, hsr] at h3
    exact h3

theorem maps_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    Maps (s⁻¹ • P) R (G * x) ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal, inv_inv]
  constructor
  · intro H y a hy
    rw [hT, Matrix.mulVec_mulVec]
    apply H
    rwa [← mul_assoc, Units.mul_inv, one_mul]
  · intro H y a hy
    have := (hT _ _).1 (H y _ hy)
    rwa [← mul_assoc, Units.inv_mul, one_mul, Matrix.mulVec_mulVec] at this

theorem phiOne_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    phiOne (s⁻¹ • P) R (G * x) = phiOne P Q x := by
  classical
  unfold phiOne
  exact if_congr (maps_transport P G s hT x) rfl rfl

section Frames
variable {D : D7} {p : SplitPt D k} {S T : HSp D} {n' : Type} [Fintype n'] [DecidableEq n']

theorem extFun_eq_of (α : Frame p S n') (β : Frame p T n₂) (β' : Frame p T n) (Ψ : Matrix n₂ n' k → ℂ)
    (Ψ' : Matrix n n' k → ℂ) (hΨ : ∀ x, Ψ' ((β'.b' * β.b) * x) = Ψ x) : extFun α β Ψ = extFun α β' Ψ' := by
  funext t
  unfold extFun
  split_ifs
  · rw [← hΨ]
    congr 1
    unfold rd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
  · rfl

end Frames

section Lists
variable {D : D7} {ι : Type} {p : ι → SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem overAll_of_extFun_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n₂) (β' : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n₂ n' k → ℂ)
    (Ψ' : ι → Matrix n n' k → ℂ) (h : ∀ i, extFun (α i) (β i) (Ψ i) = extFun (α i) (β' i) (Ψ' i))
    (hSB : ∀ i, Ψ' i ∈ SB (Matrix n n' k)) :
    ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β' LS LT Ψ' l f f' := by
  intro l f f' hf
  induction l generalizing f' with
  | nil => exact hf
  | cons i l ih =>
    change ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' at hf
    change ∃ g, OverAll ψ α β' LS LT Ψ' l f g ∧ Over ψ (α i) (β' i) LS LT g (Ψ' i) f'
    obtain ⟨g, hg, hov⟩ := hf
    refine ⟨g, ih g hg, ?_⟩
    unfold Over at hov ⊢
    obtain ⟨h1, h2, h3, -, h5⟩ := hov
    refine ⟨h1, h2, h3, hSB i, ?_⟩
    rw [← h i]
    exact h5

end Lists

theorem isLattice_of_lastKer {m : Type} [Fintype m] [DecidableEq m] {Q : Pair k n₂} (G : Matrix (m ⊕ Fin 1) n₂ k)
    (G' : Matrix n₂ (m ⊕ Fin 1) k) (hGG : G * G' = 1) (L : Submodule 𝒪[k] (m → k))
    (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) :
    L.IsFullLattice k := by
  let e : (m → k) →ₗ[k] (m ⊕ Fin 1 → k) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext (i | i) <;> simp
      map_smul' := by intro c x; ext (i | i) <;> simp }
  let f : (m → k) →ₗ[k] (n₂ → k) := (Matrix.mulVecLin G').comp e
  have hGf : ∀ x, G *ᵥ f x = Sum.elim x 0 := by
    intro x
    simp only [f, e, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (G *ᵥ ·) hxy
    simp only [hGf] at this
    funext i
    exact congrFun this (Sum.inl i)
  have hL : L = Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hker, hGf, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    simp
  rw [hL]
  have := GlobalTheory.GoodLat.isLattice_comap Q.ker Q.ker_isLat.toIsLattice f hf
  refine ⟨?_⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : f x ∈ Submodule.span k (Q.ker : Set (n₂ → k)) := by
    rw [Submodule.IsFullLattice.span_eq_top]
    trivial
  obtain ⟨a, ha, hax⟩ := GlobalTheory.GoodLat.exists_smul_mem Q.ker hx
  have hmem : a • x ∈ Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    change (f.restrictScalars 𝒪[k]) (a • x) ∈ Q.ker
    rw [map_smul]
    exact hax
  have hspan := Submodule.subset_span (R := k) hmem
  have ha' : algebraMap 𝒪[k] k a ≠ 0 := by
    intro hzero
    exact ha (IsFractionRing.injective 𝒪[k] k (hzero.trans (map_zero _).symm))
  rw [← algebraMap_smul k a x] at hspan
  simpa only [inv_smul_smul₀ ha'] using
    (Submodule.span k (Q.ker.comap (f.restrictScalars 𝒪[k]) : Set (m → k))).smul_mem
      (algebraMap 𝒪[k] k a)⁻¹ hspan

end GlobalTheory.LastKerRep


open GlobalTheory.LastKerRep in
theorem GlobalTheory.SeeSaw.lastKernel_reps :
    ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
      c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
        (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧
        Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
          (fun i =>
            haveI := hΛ i
            phiOne (u i • o.Q (j + 1) i)
              (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i)))
          o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have htop := fun i => (hS.pre.topT (j + 1 + 1) h i).2
  choose Λ s hLat hKer hVal using htop
  have hGG : ∀ i, ((o.γ₀ (j + 1 + 1) h i).b' * (o.β (j + 1 + 1) i).b) * ((o.β (j + 1 + 1) i).b' * (o.γ₀ (j + 1 + 1) h i).b) = 1 := by
    intro i
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (o.β (j + 1 + 1) i).b, (o.β (j + 1 + 1) i).bb', Matrix.one_mul, (o.γ₀ (j + 1 + 1) h i).b'b]
  have hΛ : ∀ i, (Λ i).IsFullLattice k := fun i => isLattice_of_lastKer _ _ (hGG i) (Λ i) (hKer i)
  refine ⟨Λ, hΛ, fun i => (s i)⁻¹, hLat, (hv.atT (j + 1)).1, fun f hf => ?_⟩
  refine overAll_of_extFun_eq c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (o.γ₀ (j + 1 + 1) h) _ _ _ _ (fun i => ?_) (fun i => ?_)
    o.I f _ (hS.rep (j + 1) (by omega) f hf)
  · have := hΛ i
    apply extFun_eq_of
    intro x
    exact phiOne_transport _ _ _ (hasVal_transport _ _ (hGG i)
      (glue_hasVal (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last o.q (Λ i)))
      (fun y => (hKer i y).trans (by rw [glue_ker])) (hVal i)) x
  · have := hΛ i
    exact GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _

end
end
