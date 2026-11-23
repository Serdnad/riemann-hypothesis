module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle348
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle349
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PushoutsMemSpanLocalSelmerPushouts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := GlobalTheory.T.exists_integral_retraction_localIntegers h
  obtain ⟨p, hp, hpr⟩ := GlobalTheory.T.exists_fieldExtension_of_integral_retraction h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2




theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a

    simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add (f := _), map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
end
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.liftC_main | exact GlobalTheory.UseLoc.Cases.liftC_main | (intros; apply GlobalTheory.UseLoc.Cases.liftC_main <;> assumption)
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  first | exact @GlobalTheory.UseLoc.Cases.readC_cob | exact GlobalTheory.UseLoc.Cases.readC_cob | (intros; apply GlobalTheory.UseLoc.Cases.readC_cob <;> assumption)
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  first | exact @GlobalTheory.UseLoc.Cases.readW_main | exact GlobalTheory.UseLoc.Cases.readW_main | (intros; apply GlobalTheory.UseLoc.Cases.readW_main <;> assumption)
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  first | exact @GlobalTheory.UseLoc.Cases.readU_unr | exact GlobalTheory.UseLoc.Cases.readU_unr | (intros; apply GlobalTheory.UseLoc.Cases.readU_unr <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.tensorLocalField_isCrystalline_over_familyField : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g), ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  first | exact @GlobalTheory.Pass.LocCrysU.main | exact GlobalTheory.Pass.LocCrysU.main | (intros; apply GlobalTheory.Pass.LocCrysU.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.pushouts_mem_span_localSelmerPushouts : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) → ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG → ∀ (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), ∀ c ∈ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE, c ∈ BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst) (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.Pass.LocPush.main | exact GlobalTheory.Pass.LocPush.main | (intros; apply GlobalTheory.Pass.LocPush.main <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.ResSel.Transfer

section Alg

variable {O Λ K : Type} [CommRing O] [CommRing Λ] [CommRing K] [Algebra O Λ] [Algebra O K] [Module Λ K]
  (φ : Λ →ₐ[O] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b)

def idVec (r : ℕ) : (Fin r → K) →ₛₗ[(φ : Λ →+* K)] (Fin r → K) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := funext fun a => hs c (m a)

include hs in
theorem matAct_eq {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : Fin n → K) :
    matAct (M := K) Φ x = (Φ.map φ).mulVec x := by
  funext a
  simp [matAct, hs, Matrix.mulVec, dotProduct]

include hs in
theorem repOn_eq {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn ρ κ K g m = φ ((κ g : Λˣ) : Λ) • ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, hs, Matrix.mulVec, dotProduct]

theorem idVec_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
    (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1) (g : Γ) (m : Fin r → K) :
    idVec φ hs r (repOn ρ κ K g m) = repOn ρ (1 : Γ →* Kˣ) K g (idVec φ hs r m) := by
  change repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m
  rw [repOn_eq φ hs, hκ]
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

variable [TopologicalSpace K] [DiscreteTopology K] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {r : ℕ}
  (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

def tau : H1 (repOn ρ κ K) →ₛₗ[(φ : Λ →+* K)] H1 (repOn ρ (1 : Γ →* Kˣ) K) :=
  slH1 _ _ (idVec φ hs r) continuous_of_discreteTopology (idVec_repOn φ hs ρ κ hκ)

theorem tau_injective : Function.Injective (tau φ hs ρ κ hκ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
      (idVec_repOn φ hs ρ κ hκ) z) : H1 (repOn ρ (1 : Γ →* Kˣ) K)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    have e : repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m := idVec_repOn φ hs ρ κ hκ g m
    rw [e]
    exact hm g

def kerIn {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : LinearMap.ker (Φ.map φ).mulVecLin) :
    LinearMap.ker (matAct (M := K) Φ) :=
  ⟨x.1, by rw [LinearMap.mem_ker, matAct_eq φ hs]; exact x.2⟩

theorem exists_linear (hsurj : Function.Surjective (algebraMap O K)) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ)
    (S : Submodule Λ (H1 (repOn ρ κ K))) (e : LinearMap.ker (matAct (M := K) Φ) ≃ₗ[Λ] S) :
    ∃ E : LinearMap.ker (Φ.map φ).mulVecLin →ₗ[K] H1 (repOn ρ (1 : Γ →* Kˣ) K), Function.Injective E ∧
      ∀ x, E x = tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1 := by
  refine ⟨{ toFun := fun x => tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun x y hxy => ?_, fun _ => rfl⟩
  · rw [show kerIn φ hs Φ (x + y) = kerIn φ hs Φ x + kerIn φ hs Φ y from rfl, map_add (f := _), Submodule.coe_add, map_add (f := _)]
  · obtain ⟨o, rfl⟩ := hsurj c
    have h1 : kerIn φ hs Φ (algebraMap O K o • x) = algebraMap O Λ o • kerIn φ hs Φ x := by
      apply Subtype.ext
      funext b
      change algebraMap O K o * x.1 b = algebraMap O Λ o • x.1 b
      rw [hs, AlgHom.commutes]
    rw [h1, map_smul, Submodule.coe_smul, map_smulₛₗ, RingHom.id_apply]
    congr 1
    exact φ.commutes o
  · have h1 := e.injective (Subtype.ext (tau_injective φ hs ρ κ hκ hxy))
    have h2 : (kerIn φ hs Φ x).1 = (kerIn φ hs Φ y).1 := congrArg Subtype.val h1
    exact Subtype.ext h2

end Alg

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ K : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing K] [Algebra (X.O0 i) K] [Module Λ K]
  [TopologicalSpace K] [DiscreteTopology K]
  (φ : Λ →ₐ[X.O0 i] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b) (κ : GE N →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

theorem tau_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ K v) :
    slH1 ((repOn ρ κ K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype)
      (idVec φ hs r) continuous_of_discreteTopology (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
        (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, hs, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem tau_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ K)) (hx : x ∈ selOn bkP i ρ κ K Q) :
    tau φ hs ρ κ hκ x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ κ K) (repOn ρ (1 : GE N →* Kˣ) K) (idVec φ hs r) continuous_of_discreteTopology
    (idVec_repOn φ hs ρ κ hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact tau_mem_bkOn bkP i ρ φ hs κ hκ v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem tors_of_cast_eq_zero {B : Type} [CommRing B] {l : ℕ} (h : (l : B) = 0) (b : B) : ∃ n : ℕ, (l ^ n) • b = 0 :=
  ⟨1, by rw [pow_one, nsmul_eq_mul, h, zero_mul]⟩

theorem computes_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  intro D N X bkP i s M ι d Q a Φ hC k _ _ _ _ hk hsurj aug haug
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) k := Module.compHom k (aug : abelian₂ X i M ι →+* k)
  have hs : ∀ (y : abelian₂ X i M ι) (b : k), y • b = aug y * b := fun _ _ => rfl
  have hκ : ∀ g, aug ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = 1 := fun g =>
    haug (delAll X i M d g)⁻¹
  have hkT := tors_of_cast_eq_zero hk
  obtain ⟨E, hEi, hE⟩ := exists_linear aug hs (Tgl i s) (delInv i M d) hκ hsurj Φ _ (e k hkT)
  refine ⟨E, hEi, fun x => ?_, ?_⟩
  · rw [hE]
    exact tau_mem_selOn bkP i _ aug hs _ hκ Q _ (e k hkT (kerIn aug hs Φ x)).2
  intro B _ _ th hB x hx
  letI : Module (abelian₂ X i M ι) B := Module.compHom B (th : abelian₂ X i M ι →+* B)
  have hsB : ∀ (y : abelian₂ X i M ι) (b : B), y • b = th y * b := fun _ _ => rfl
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hBT := tors_of_cast_eq_zero hB
  let xB : LinearMap.ker (matAct (M := B) Φ) := ⟨x, by rw [LinearMap.mem_ker, matAct_eq th hsB]; exact hx⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B hBT xB).1
  refine ⟨z.1, (IsLocallyConstant.iff_continuous _).2 z.2.1, fun g h => ?_, fun f hf => ?_⟩
  · rw [z.2.2 g h, repOn_eq th hsB, Tgl_coe]
  let fl : B →ₗ[abelian₂ X i M ι] k :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun y b => hf y b }
  have hx' : (Φ.map aug).mulVec (fun c => f (x c)) = 0 := by
    funext c
    have h1 := congrArg f (congrFun hx c)

    simpa [Matrix.mulVec, dotProduct, map_sum, hf] using h1
  let z₁ : Z1 (repOn (Tgl i s) (delInv i M d) k) :=
    cocycles1MapOfEquivariant _ _ (fl.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map (Tgl i s) (delInv i M d) fl) z
  refine ⟨⟨fun c => f (x c), hx'⟩, semilinearCoefficientMapCocycles _ _ (idVec aug hs D.R.r) continuous_of_discreteTopology
    (idVec_repOn aug hs (Tgl i s) (delInv i M d) hκ) z₁, fun _ => rfl, fun _ _ => rfl, ?_⟩
  rw [hE, he B k hBT hkT fl xB (kerIn aug hs Φ ⟨fun c => f (x c), hx'⟩) z z₁ (fun _ => rfl) (fun _ _ => rfl) hz.symm]
  rfl

end GlobalTheory.ResSel.Transfer

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDualDR




theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  intro D hFont hP i r hr Xs w hw n hPot X hX X' PX hD
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  obtain ⟨h1, h2, h3, h4⟩ := hD
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X'.V, ρ := X'.ρ.comp incl, cont := fun v => (X'.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW : IsCrys ((D.loc (D.nd.l i)).PD K') W.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W) (hA := hsub)).1
  have hcyc : ∀ g : ↥(GK K'),
      ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
        ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) (incl g) : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
    intro g
    have e1 := (D.loc (D.nd.l i)).PD_χ K' g
    have e2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (incl g)
    change algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((((D.loc (D.nd.l i)).PD K').χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (incl g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i])
    rw [e1, e2]
    rfl
  have hD' : IsDual1 ((D.loc (D.nd.l i)).PD K') W.ρ W'.ρ PX := by
    refine ⟨fun g v y => ?_, h2, h3, h4⟩
    rw [hcyc]
    exact h1 (incl g) v y
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (hFont (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1 W W' PX hD' hW
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X' hW'

end GlobalTheory.SummandDualDR

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nearPi_sep_complete_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧ ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.nearPi_sep_complete | exact GlobalTheory.Decompl.nearPi_sep_complete | (intros; apply GlobalTheory.Decompl.nearPi_sep_complete <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R), (∀ g h i j, ρ g (M h i j) = M h i j) → (∀ h i j, M h i j ^ p ^ m = M h i j) → (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧ ∀ g, M g * W.map (ρ g) = W := by
  first | exact @GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | exact GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | (intros; apply GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_wittVector_trace_one_finiteLevel : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  first | exact @GlobalTheory.UnramifiedCrys.exists_witt_trace_one | exact GlobalTheory.UnramifiedCrys.exists_witt_trace_one | (intros; apply GlobalTheory.UnramifiedCrys.exists_witt_trace_one <;> assumption)
end
