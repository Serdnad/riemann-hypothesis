module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle371
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle374
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.mem_finite_part_of_lift : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescHf.descHf | exact GlobalTheory.UseLoc.DescHf.descHf | (intros; apply GlobalTheory.UseLoc.DescHf.descHf <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) (Br.LL D.nbr i w hw) :=
  GlobalTheory.TateDualX.dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) (Br.loc D.nbr i w hw M)

theorem dualMat_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    dualMat i w hw M g = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) • (Br.loc D.nbr i w hw M g⁻¹).transpose := rfl

theorem continuous_dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (dualMat i w hw M) := by
  haveI := isTopRing i w hw
  exact GlobalTheory.TateDualX.continuous_dualTw _ _ (GlobalTheory.TateDualX.continuous_cyc D i w hw)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

def Udual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (dualMat i w hw M) (continuous_dualMat i w hw M hM)

theorem cyc_mem (g : Br.G D.nbr i w hw) : ∃ c : Br.OLL D.nbr i w hw,
    algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  exact ⟨_, rfl⟩

theorem dualMat_integral {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    ∃ N : Matrix (Fin k) (Fin k) (Br.OLL D.nbr i w hw),
      dualMat i w hw M g = N.map (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  obtain ⟨c, hc⟩ := cyc_mem i w hw g
  refine ⟨c • (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)) g⁻¹).transpose, ?_⟩
  rw [dualMat_apply, ← hc, Matrix.map_smul' _ _ _ (map_mul _), Matrix.transpose_map]
  rfl

def latDual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    Lattice (O := Br.OLL D.nbr i w hw) (Udual i w hw M hM).ρ :=
  GlobalTheory.BKLatticeCochain.stdLattice Subtype.val_injective (Udual i w hw M hM).ρ fun g => by
    obtain ⟨N, hN⟩ := dualMat_integral i w hw M g
    exact ⟨N, fun x => by rw [← hN]; rfl⟩

end GlobalTheory.Pass.LocDirect

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.local_duality_finite_discrete_modules : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.DualPairFormula.greenbergWiles_dualPair | exact GlobalTheory.DualPairFormula.greenbergWiles_dualPair | (intros; apply GlobalTheory.DualPairFormula.greenbergWiles_dualPair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem tors_of_finite_local (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [show x = 0 from hx, zero_smul]

theorem bkOn_le_map_of_surjective : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (f : Y →ₗ[A] Y₂), Function.Surjective f → ∀ v, bkOn bkP i (Tgl i s) κ Y₂ v ≤ (bkOn bkP i (Tgl i s) κ Y v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  intro D N X bkP i s A _ _ _ _ κ Q hS _ Y _ _ _ _ Y₂ _ _ _ _ f hf v
  haveI := hS.2.1
  exact GlobalTheory.SelObstruction.bkOn_onto bkP i s κ hS.2.2.2.2.2.1 (tors_of_finite_local A Y) f hf v

end GlobalTheory.NewPrime
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.PairFormula

theorem perp_iff {n : ℕ} [NeZero n] {Λ : Type} [CommRing Λ]
    {M : Type} [AddCommGroup M] [Module Λ M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {M' : Type} [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M'] [DiscreteTopology M']
    {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → ZMod n)
    (hχ : ∀ g, χ g = ((μ (φ g) : (ZMod n)ˣ) : ZMod n))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (L : Submodule Λ (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = P x (y.1 g)) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupB χ (fun g m => ρ' g m) P x.1 y.1 := by
  let E := GlobalTheory.DualPairFormula.cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, P (x.1 (g * h)) (y.1 (g * h)) = P (x.1 g) (y.1 g) +
      P (x.1 g) (ρ' g (y.1 h)) + P (ρ g (x.1 h)) (y.1 g) + χ g * P (x.1 h) (y.1 h) :=
    fun x g h => by
    rw [x.2.2, y.2.2, ← hP]
    simp only [map_add (f := _), AddMonoidHom.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => P (x.1 g) (y.1 g) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => P p.1 p.2)).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ,
      cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        P (x.1 g) (ρ' g (y.1 h)) = χ g * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        χ g * c h - c (g * h) + c g = P (ρ g (x.1 h)) (y.1 g) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ, hχ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    obtain ⟨c, hc1, hc2⟩ := (hcup x).1 (H _ ((hL _ _ (hE _)).1 hx))
    exact ⟨c, (IsLocallyConstant.iff_continuous c).2 hc1, hc2⟩
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    exact (hcup x).2 ⟨f, hf1.continuous, hf2⟩


open GlobalTheory.DualPairFormula GlobalTheory.SelInf in
theorem greenbergWiles_pair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ n Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
    S A hS hur L hL C hC
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : ∀ (x : W) (y : W'), (l ^ n) • P x y = 0 := fun x y => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  haveI : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hk]
  haveI : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, hk]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ n) ρ) hρ (S : Set _)
    fun v hv B hB σ hσ => by
      ext x
      change ρ σ x = x
      rw [(hur v hv B hB σ hσ).1]
      rfl
  replace hd : ∀ (g : G F Ω) (x : W), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := n) hS
  have hμ' : ∀ g, ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) =
      ((μ (toGS Ω _ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := fun g => by rw [← hμ]; rfl
  have hfin : Finite (TDual (ZMod (l ^ n)) W) := GlobalTheory.DualSide.finite_TDual
  have hfin' : Finite (TDual (ZMod (l ^ n)) W') := GlobalTheory.DualSide.finite_TDual
  let f : W' →+ TDual (ZMod (l ^ n)) W := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap (l ^ n))) (fun y y' => by refine DFunLike.ext _ _ fun x => ?_; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod (l ^ n)) W) = Nat.card W := GlobalTheory.ZModDual.card_dual_eq _ W
  have c2 : Nat.card (TDual (ZMod (l ^ n)) W') = Nat.card W' := GlobalTheory.ZModDual.card_dual_eq _ W'
  have c3 : Nat.card W ≤ Nat.card W' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective
      (fun x => TDual.mk ((P x).toZModLinearMap (l ^ n))) fun x x' hxx' => ?_
    have : ∀ y, P x y = P x' y := fun y =>
      congrArg (fun φ : TDual (ZMod (l ^ n)) W' => φ y) hxx'
    exact sub_eq_zero.1 (h1 _ fun y => by rw [map_sub, AddMonoidHom.sub_apply, this, sub_self])
  let e : W' ≃+ TDual (ZMod (l ^ n)) W :=
    AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3))
  have he : ∀ y x, e y x = P x y := fun _ _ => rfl
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    refine DFunLike.ext _ _ fun x => ?_
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← hμ', ← hP, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl W) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l n W S
    ρS hn hS hρS μ hμ (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := selAll_equiv_sel F Ω Λ (ZMod (l ^ n)) W W S A ρ ρS (AddEquiv.refl W) hρ hd L LS
    hL hLS2

  have hv' : ∀ (z : Z1 (twDual μ ρS)) (v : S),
      resH1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v)
        (Submodule.Quotient.mk z) ∈ perpCond μ ρS (locFam S fun v => A.1 v.1)
          (fun v => hρS.comp' (continuous_locFam S _ v)) LS v ↔
      ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype), Submodule.Quotient.mk x ∈ L v.1 →
        CupB (fun g : Dec (F := F) (A.1 v.1) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
          (fun g m => ρ' g.1 m) P x.1 (fun g => (infZ e hee z).1 g.1) := fun z v => by
    rw [mem_perpCond]
    exact perp_iff (ρ.comp (Dec (F := F) (A.1 v.1)).subtype) (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype)
      P μ ρS (locFam S (fun v => A.1 v.1) v) (fun g x => hd g x) _
      (fun g => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g => hμ' g.1)
      (fun g => hP g.1) (L v.1) (LS v) (hLS2 v)
      (restrictCocycles1 ρ' (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e hee z))
      (restrictCocycles1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g x => by
        change z.1 (toGS Ω _ g.1) x = P x (e.symm (z.1 (toGS Ω _ g.1)))
        rw [← he, e.apply_symm_apply])
  have hmem : ∀ z : Z1 (twDual μ ρS),
      Submodule.Quotient.mk z ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      Submodule.Quotient.mk (infZ e hee z) ∈ C := fun z => by
    rw [mem_Sel, hC]
    constructor
    · intro h
      refine ⟨fun v hv σ hσ => ?_, fun v hv x hx => (hv' z ⟨v, hv⟩).1 (h ⟨v, hv⟩) x hx⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
        (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
      rw [infZ_apply, this, z_one, map_zero]
    · rintro ⟨-, h⟩ v
      exact (hv' z v).2 (h v.1 v.2)
  have hmem' : ∀ x : H1 (twDual μ ρS),
      x ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      infH e hee x ∈ C := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk]
    exact hmem z
  let T := Equiv.ofBijective (fun x : Sel (twDual μ ρS) (locFam S fun v => A.1 v.1)
      (continuous_locFam S _) (perpCond μ ρS (locFam S fun v => A.1 v.1)
        (fun v => hρS.comp' (continuous_locFam S _ v)) LS) =>
      (⟨infH e hee x.1, (hmem' _).1 x.2⟩ : C)) ⟨fun x y h => ?_, fun y => ?_⟩
  · have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.mk'_surjective _
    refine ⟨Finite.of_equiv _ T, ?_⟩
    rw [Nat.card_congr E1, ← Nat.card_congr T, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
      ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl W) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
    simp only [← hLS1]
    rw [← hmain]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
      (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl W)
      (fun g x => hd g x)).symm
  · exact Subtype.ext (infH_injective e hee (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z', rfl⟩ := exists_infZ e hee z (vanish_NS e hee A z ((hC z).1 hy).1)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem' _).2 (by rw [infH_mk]; exact hy)⟩,
      Subtype.ext (infH_mk e hee z')⟩

end GlobalTheory.PairFormula
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def vecLS (a : ℕ) :
    (Fin a → Fin D.R.nV → KK D.nd i) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) where
  toFun := vecL i w hw
  map_add' u v := by
    funext b j
    simp [vecL]
  map_smul' c v := by
    funext b j
    simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]
    rfl

theorem eO_surj : RingHomSurjective (D.nbr i w hw).eO.toRingHom :=
  ⟨(D.nbr i w hw).eO.surjective⟩

theorem latY_map {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    (latY i w hw Y).map ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) =
      Submodule.span (Br.OLL D.nbr i w hw) (vecL i w hw '' (Y : Set _)) := by
  rw [latY, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩, ⟨y, hy, rfl⟩, rfl⟩

theorem latY_fg {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    (latY i w hw Y).FG := by
  have hinj : Function.Injective ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) :=
    Subtype.val_injective
  apply Submodule.fg_of_fg_map_injective _ hinj
  rw [latY_map]
  haveI := eO_surj i w hw
  obtain ⟨S, rfl⟩ := hY
  have h : ∀ T : Set (Fin a → Fin D.R.nV → KK D.nd i), vecL i w hw '' T = (vecLS i w hw a) '' T :=
    fun _ => rfl
  rw [h, ← Submodule.map_coe, Submodule.span_eq, Submodule.map_span]
  classical
  exact ⟨(S.image (vecLS i w hw a)), by rw [Finset.coe_image]⟩

theorem span_stable_of_gen {R K M : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module K M]
    [Module R M] (hT : IsScalarTower R K M) (f : M →ₗ[K] M) (s : Set M) (h : ∀ v ∈ s, f v ∈ s) :
    ∀ v ∈ Submodule.span R s, f v ∈ Submodule.span R s := by
  intro v hv
  haveI := hT
  have key : Submodule.span R s ≤ (Submodule.span R s).comap (f.restrictScalars R) :=
    Submodule.span_le.2 fun u hu => Submodule.subset_span (h u hu)
  exact key hv

theorem latY_stable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ latY i w hw Y,
      subRho (sumG i w hw r Xs hr x) (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst) g u ∈ latY i w hw Y := by
  intro g
  apply span_stable_of_gen (K := Br.LL D.nbr i w hw)
  · exact ⟨fun c k u => Subtype.ext (smul_assoc c k (u.1 : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw))⟩
  rintro v ⟨y, hy, hv⟩
  refine ⟨actK i r Xs x (gl i w hw g) y, hst _ y hy, ?_⟩
  show _ = (sumG i w hw r Xs hr x).ρ g (v : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)
  rw [← hv, sumG_vecL]

theorem latY_span {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule.span (Br.LL D.nbr i w hw) ((latY i w hw Y : Set ↥(spanL i w hw Y))) = ⊤ := by
  apply Submodule.map_injective_of_injective (spanL i w hw Y).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩,
      Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩

theorem latY_free {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    Module.Free (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
  letI : CommRing (Br.OLL D.nbr i w hw) := inferInstance
  letI : AddCommGroup ↥(latY i w hw Y) := inferInstance
  letI : Module (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := inferInstance
  haveI : Module.Finite (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) :=
    Module.Finite.iff_fg.2 (latY_fg i w hw Y hY)
  haveI : NoZeroSMulDivisors (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
    constructor
    intro c u h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    have h1 : ((c • u : ↥(latY i w hw Y)) : ↥(spanL i w hw Y)) = 0 := by rw [h]; rfl
    have h2 : ((algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c) • (u : ↥(spanL i w hw Y))) = 0 := by
      rw [algebraMap_smul]; exact h1
    have hc' : algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c ≠ 0 := by
      intro h0; apply hc; exact Subtype.val_injective h0
    have := (smul_eq_zero.1 h2).resolve_left hc'
    exact Subtype.ext this
  haveI : IsPrincipalIdealRing (Br.OLL D.nbr i w hw) := inferInstance
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  haveI : IsTorsionFree (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := inferInstance
  exact @Module.free_of_finite_type_torsion_free' (Br.OLL D.nbr i w hw) inferInstance
    ↥(latY i w hw Y) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

theorem latY_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  intro D i w hw r Xs hr a x Y hst hY
  exact ⟨{ T := latY i w hw Y
           stable := latY_stable i w hw r Xs hr x Y hst
           fg := latY_fg i w hw Y hY
           free := latY_free i w hw Y hY
           span := latY_span i w hw Y }, rfl⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

section

open NumberField Matrix GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F → ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a, GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1))) (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | exact GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_blk_last_eq_zero <;> assumption)
end
