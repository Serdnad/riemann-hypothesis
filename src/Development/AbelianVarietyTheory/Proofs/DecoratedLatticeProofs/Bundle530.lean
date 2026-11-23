module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle526
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle527
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam

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


theorem _root_.GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  first | exact @GlobalTheory.EisConvGrowth.eis_modGrowth | exact GlobalTheory.EisConvGrowth.eis_modGrowth | (intros; apply GlobalTheory.EisConvGrowth.eis_modGrowth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumRead

theorem reads_datum_eq_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT f₀ Φ f Ξ hV hSB hTh hΦ hΞ1 hΞ2
  classical
  obtain ⟨ΛS, hΛS, hΛS'⟩ := id hdS
  obtain ⟨ΛT, hΛT, hΛT'⟩ := id hdT
  obtain ⟨hRX, hRA, hRB⟩ := GlobalTheory.T.periodLatticeHalves_reps_finite_index D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa
  set SX := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSXd
  set SA := repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)
    (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSAd
  set SB := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSBd
  set MA := halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  set MB := halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  have hpx : ∀ x ∈ SX, ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x := fun x hx => by
    obtain ⟨x', hx', h⟩ := AddSubgroup.mem_map.1 (hRX.1 x hx)
    exact ⟨x', hx', h⟩
  have hpy : ∀ y ∈ SB, ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y := fun y hy => by
    obtain ⟨y', hy', h⟩ := AddSubgroup.mem_map.1 (hRB.1 y hy)
    exact ⟨y', hy', h⟩
  let px : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun x =>
    if h : ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x then h.choose else 0
  let py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun y =>
    if h : ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y then h.choose else 0
  have hpx' : ∀ x ∈ SX, px x ∈ MA ∧ embH (tauE D) δ (px x) = x := fun x hx => by
    simp only [px, dif_pos (hpx x hx)]; exact (hpx x hx).choose_spec
  have hpy' : ∀ y ∈ SB, py y ∈ MB ∧ embH (tauE D) δ (py y) = y := fun y hy => by
    simp only [py, dif_pos (hpy y hy)]; exact (hpy y hy).choose_spec
  let mt : Formalism.L2.Col.HomE D.host.E a b → Matrix (Fin T.rank) (Fin S.rank) D.host.E := fun x =>
    (LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)
  have hmt : ∀ x, toHom S T hS hT (mt x) = x := fun x => by
    simp only [mt]
    unfold toHom
    have h : ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)).reindex (finCongr hT) (finCongr hS) =
        LinearMap.toMatrix' x := by
      ext i j; simp [Matrix.reindex_apply]
    rw [h, Matrix.toLin'_toMatrix']
  let K : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - p.1) * (brk (HV sc) p.2 s)⁻¹
  have hF := GlobalTheory.T.finite_fourier_expansion_half_split_places D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx' hpy'
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hf1 : f = ∑ p ∈ SX ×ˢ SB, K p • heisO ψ S T ((mt (px p.1)).map fun r => e * incA D r)
      (heisO ψ S T ((mt (py p.2)).map fun r => cA D e * incA D r) f₀) := by
    refine GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates D ψ S T e _ f₀ Φ f _ (SX ×ˢ SB) K (fun p => (mt (px p.1)).map fun r => e * incA D r)
      (fun p => (mt (py p.2)).map fun r => cA D e * incA D r) c hc hTh ?_ ?_ ?_ ?_
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, hee]
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
    · intro p hp u hu
      exact GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT (py p.2) (hpy' _ (Finset.mem_product.1 hp).2).1 u hu
    · intro t
      rw [hF t, Finset.sum_product]

  have hV' := hV
  obtain ⟨hstd, hvac⟩ := hV'
  have h0 : IsThetaFunO ψ S T f₀ := hvac.theta
  have hψ : IsCharAF D.host.F ψ := hstd.1
  set G : VV D.what₂.Tau a b × VV D.what₂.Tau a b → WO S T := fun p =>
    GlobalTheory.VacUnique.finRat S T (mt (px p.1)) + GlobalTheory.VacUnique.finRat S T (mt (py p.2)) with hG
  set C : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    K p * (alV D.host.d sc p.1 * alV D.host.d sc p.2) with hC
  have hf2 : f = ∑ p ∈ SX ×ˢ SB, C p • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) := by
    rw [hf1]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
    rw [GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (py p.2) (hpy' _ h2').1,
      GlobalTheory.LatVac.heisO_smul,
      GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (px p.1) (hpx' _ h1).1 (py p.2) (hpy' _ h2').1,
      (hpx' _ h1).2, (hpy' _ h2').2, smul_smul, smul_smul, hC]
    congr 1
    ring
  have hf3 : f = ∑ p ∈ SX ×ˢ SB, (C p * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (GlobalTheory.VacUnique.finRat S T (mt (py p.2))))) • heisO ψ S T (G p) f₀ := by
    rw [hf2]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LatVac.heisO_heisO, smul_smul]
  have hGi : ∀ p ∈ SX ×ˢ SB, (G p).map (infPart D) = 0 := fun p _ => by
    simp only [hG, ← map_add (f := _)]
    exact GlobalTheory.VacUnique.finRat_inf S T _
  refine ⟨⟨?_, fun τ => ?_⟩, ?_⟩
  · rw [hf3]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ h0 _ _ G _ hGi
  · rw [hf3]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ hP.inf f₀ h0 τ _ (hvac.fock τ) _ _ G _ hGi
  · have hread : ∀ p ∈ SX ×ˢ SB, xiN θ S T hS hT δ sc (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) =
        Formalism.L2.Th1.H.opU (HV sc) p.1 (Formalism.L2.Th1.H.opU (HV sc) p.2 (xiN θ S T hS hT δ sc f₀)) := by
      intro p hp
      obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
      have hfin : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.VacUnique.finRat S T γ) := fun γ =>
        ⟨GlobalTheory.VacUnique.finRat_inf S T γ, GlobalTheory.VacUnique.finRat_fin S T γ⟩
      have ht1 : IsThetaFunO ψ S T (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) :=
        GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.VacUnique.finRat_inf S T _) h0
      rw [GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ ht1 _ _ (hfin _), GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ h0 _ _ (hfin _),
        hmt, hmt, (hpx' _ h1).2, (hpy' _ h2').2]
    funext z
    have hlin : xiN θ S T hS hT δ sc f z = ∑ p ∈ SX ×ˢ SB, C p * xiN θ S T hS hT δ sc
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
          (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) z := by
      rw [hf2]
      simp only [xiN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hlin]
    rw [Finset.sum_congr rfl fun p hp => by rw [hread p hp]]
    show _ = xiL (HV sc) (alV D.host.d sc) 1 SX SA SB (onV (tauE D) δ Ξ) (xiN θ S T hS hT δ sc f₀) z
    rw [GlobalTheory.ThetaCosetSum.xiL_eq_kernel, Finset.sum_product]
    simp only [hC, K, Formalism.L2.Th1.H.opU, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
    ring

end GlobalTheory.AdForm.DatumRead
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatLaw

theorem isHalf_actO {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

theorem law_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z
  obtain ⟨hsupp, k, hk, hper, -⟩ := hΦ
  set ez := z.map fun r => A.e * incA (I.rec7 l Z) r with hez
  by_cases hw : IsHalf A.e (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez)
  · obtain ⟨z', v, hv, hvh, hwe⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem k hk _ hw
    have hΦw : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = p * A.xi i hi α γ z' := by
      rw [hwe, hper v hv hvh, hp z']
    rw [hΦw, hp z]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hxi : ∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E)
          (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t →
          z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t →
          A.xi i hi α γ z₁ = A.xi i hi α γ z₂ := by
        intro z₁ z₂ t ht hth he
        have h1 := hp z₁
        rw [he, hper t ht hth, hp z₂] at h1
        exact (mul_left_cancel₀ hp0 h1).symm
      have hL := GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hwe
      linear_combination p * hL
  · have h1 : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = 0 := by
      by_contra h
      exact hw (hsupp _ h)
    have h2 : Φ ez = 0 := by
      by_contra h
      exact hw (GlobalTheory.AdForm.RatLaw.isHalf_actO _ _ (hsupp _ h))
    rw [h1, h2]
    simp

end GlobalTheory.AdForm.RatLaw
end

section


theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.LastOneLin.lin | exact GlobalTheory.LastOneLin.lin | (intros; apply GlobalTheory.LastOneLin.lin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainUpwardLift_heckeParam_transferred : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, LevFacts D → UpPar D := by
  first | exact @GlobalTheory.ChainOnto.upPar_of_transfer | exact GlobalTheory.ChainOnto.upPar_of_transfer | (intros; apply GlobalTheory.ChainOnto.upPar_of_transfer <;> assumption)
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


theorem _root_.GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, SphFactor D := by
  first | exact @GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | exact GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | (intros; apply GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair <;> assumption)
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


theorem _root_.GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  exact @GlobalTheory.SwSecMem.swSec_mem_degPS
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  first | exact @GlobalTheory.ChainTw.Peel.qPeel_holds | exact GlobalTheory.ChainTw.Peel.qPeel_holds | (intros; apply GlobalTheory.ChainTw.Peel.qPeel_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (VacFin)

noncomputable section

namespace GlobalTheory.ChainTw

theorem upParQ_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpParQ D := by
  intro hRD hHowe D hND c w hw k hk s s' hs hs' p hp u B φ hu v _ hne
  obtain ⟨hr, _, hfl⟩ := hs
  obtain ⟨hr', _, hfl'⟩ := hs'
  have hlat' : ∀ (f : GA D s'.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s'.V.gram s'.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s'.V c.S f B := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hw.com (k + 1) hk _ hfl').2
  have hlat : ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hw.com k hk.le _ hfl).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by
    have h1 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    have h2 : s.V.rank = D.R.rankY k := hfl.rank
    rw [h1, h2, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hfock := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hND c w hw k hk s s' ⟨hr, by assumption, hfl⟩ ⟨hr', by assumption, hfl'⟩ p hp
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w' h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil D.R.t hrank s.ν s.fd
    hfl.haar hfl.fund w0 (fun w'' hw'' => GlobalTheory.T.thetaChain_step_chars_unramified_off_S D c hw.com k hk w0 hw0' w'' hw'') w' h (p.pt φ)
    ((hfock.1 φ).2.2 w0 hw0') y (B w') hYA.1 hYA.2 (hyB w0 hw0 w' h) hne'

end GlobalTheory.ChainTw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.doubleMixedModel_valueAtZero_equivariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 = s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  first | exact @GlobalTheory.Unf.FB.evalAt_zero_equivariant | exact GlobalTheory.Unf.FB.evalAt_zero_equivariant | (intros; apply GlobalTheory.Unf.FB.evalAt_zero_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.doubleMixedModel_baseValue_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  first | exact @GlobalTheory.Unf.evalAt_xZero_yZero | exact GlobalTheory.Unf.evalAt_xZero_yZero | (intros; apply GlobalTheory.Unf.evalAt_xZero_yZero <;> assumption)
end
