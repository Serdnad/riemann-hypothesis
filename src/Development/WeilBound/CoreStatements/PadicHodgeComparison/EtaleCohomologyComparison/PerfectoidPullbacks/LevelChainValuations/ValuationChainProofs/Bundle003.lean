module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoFirstChernLaw
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

theorem red_s_pf : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s s' 𝒱 h c lam hc r j x
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := lam) (redMor q s' d 𝒱 c lam hc r) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))) j x).1]
  refine CrystallineSemistableComparison.P.prism ((redMor q s' d 𝒱 c lam hc r).comp (σ'' := lam) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n)))) (redMor q s d 𝒱 c lam hc r) (𝟙 (redG q s d 𝒱)) (fun T y => ?_) j x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

theorem rHof_incl_pf (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (n j : ℕ) (x : M.Hc false n j) :
    inclHM M h n j (rHof (dOf S hS hC m) (hcOf S hS hC m) M s' n j x) = rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x :=
  red_s_pf _ M.p s s' {⊤} (ts_le _ M.p l h {⊤}) _ _ _ none j x

end CrystallineSemistableComparison.Pb.Kap
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

namespace LevelIdentityMorphisms

def idMor (M : Model l K) (n : ℕ) :
    GlobalTheory.LogCris.Mor (B.Lc (B.schFn M.p) (okToOC l K) false n) (B.Lc (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l false n) (b' := B.bs l false n) (ht := rfl) (ht' := rfl)
    (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism (𝟙 _) (fun _ _ _ => rfl)

abbrev idOm (M : Model l K) (n : ℕ) :
    CH.Mor (B.Oc (B.schFn M.p) (okToOC l K) false n) (B.Oc (B.schFn M.p) (okToOC l K) false n) (RingHom.id (Acris l)) :=
  B.omMor (idMor M n) (RingHom.id (Acris l)) (fun _ => rfl)

def idEta (M : Model l K) (n : ℕ) : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).G ⟶ (idOm M n).G where
  app T := LevelPullbackIdentities.thHom ⟨fun j => Empty.elim j⟩ rfl (RingHom.id T.B) (fun r => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _))
      (LevelPullbackIdentities.spec_qid _ (fun _ h => h) _)))
  naturality _ _ f := Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => Empty.elim j)

theorem idMor_pull (M : Model l K) (n j : ℕ) (x : M.Hc false n j) : (idOm M n).pull j x = x := by
  have h1 : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).pull j x = x :=
    (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) j x).2
  have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)) (idOm M n) (idEta M n)
    (fun T x => rfl) j x
  exact h2.symm.trans h1

end LevelIdentityMorphisms

theorem nmHM_nmLevA_rHof_succ (M : Model l K) (m s n j : ℕ) (x : M.Hc false n j) :
    nmHM (nmLevA S hS m M) l s none n j (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s n j x) =
      rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x := by
  have hρ : ∀ y, (dOf S hS hC m n).ρ (RingHom.id _ y) = lnMap (S.dA m) l le_rfl ((dOf S hS hC (m + 1) n).ρ y) := by
    intro y
    obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
    rw [RingHom.id_apply, hcOf, hcOf]
    exact congrArg (Ideal.Quotient.mk _) (hS.dlam m c).symm
  have e := red_nm (dOf S hS hC (m + 1) n) (dOf S hS hC m n) s (nmLevA S hS m M) (LevelIdentityMorphisms.idMor M n)
    ((PAlg.base l).cris n) ((PAlg.base l).cris n) (S.L (m + 1)).lam (S.L m).lam
    (hcOf S hS hC (m + 1) n) (hcOf S hS hC m n) (RingHom.id _) (fun _ => rfl) (fun _ _ => (Category.comp_id _).symm)
    hρ none j x
  exact (congrArg _ (LevelIdentityMorphisms.idMor_pull M n j x).symm).trans e |>.symm

end CrystallineSemistableComparison.Pb.Kap
end
end
