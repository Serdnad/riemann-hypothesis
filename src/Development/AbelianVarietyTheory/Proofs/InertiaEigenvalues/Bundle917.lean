module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRational
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle907
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle909
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle910
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS R cG S), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) → R.toRealDat.LIntegral → SupG D ∧ SupFull D := by
  first | exact @GlobalTheory.SupEq.supG_supFull_of_eq | exact GlobalTheory.SupEq.supG_supFull_of_eq | (intros; apply GlobalTheory.SupEq.supG_supFull_of_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.SeriesTie.Scale

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.MtLatConj

variable {D : D7}

theorem locC_conj {τ : ℂ ≃+* ℂ} {ν ν' : Twist D Circle} (h : ConjChar τ ν ν') (hν : ν.Good) (hν' : ν'.Good)
    (PP : Pl D.host.E) (u : (kP PP)ˣ) : τ ((ν.locC PP u : ℂˣ) : ℂ) = ((ν'.locC PP u : ℂˣ) : ℂ) := by
  classical
  unfold Twist.locC
  by_cases hP : PP ∈ ν.Q
  · have hP' : PP ∈ ν'.Q := by rw [h.1]; exact hP
    rw [if_pos hP, if_pos hP']
    exact (h.res hν hν' hP u).symm
  · have hP' : PP ∉ ν'.Q := by rw [h.1]; exact hP
    rw [if_neg hP, if_neg hP']
    simp

theorem levPOf_ext1_apply_eq_units_map_inv {r : ℕ} {Pg : Finset (Pl D.host.E)} (P : LevelP Pg r ℂ) {τ : ℂ ≃+* ℂ}
    (hP : ∀ p, τ ((P.chi p : ℂˣ) : ℂ) = ((P.chi p : ℂˣ) : ℂ)) (g : G0 Pg r) :
    τ ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) = ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact hP _
  · simp

theorem levFn_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (x : GL (Fin S.rank) (Lev.EAf D)) :
    τ ((levFn B.F.βS (B.levS ψ) x : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ') x : ℂˣ) : ℂ) := by
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rw [hcc.1]
  congr 1
  congr 1
  · exact levPOf_ext1_apply_eq_units_map_inv B.G.P hf.2.1 _
  · refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => ?_
    exact hf.2.2 PP hPP _
  · refine Finset.prod_congr rfl fun PP _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul,
      locC_conj hf.conjChar hB.de hB.de, locC_conj hcc hψ hψ']

theorem mem_levJ_of {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) {k : Bridge.Gf S}
    (hk : k ∈ B.levJ ψ') : k ∈ B.levJ ψ := by
  simp only [Base.levJ, Subgroup.mem_comap, Lev.toAfE, mem_lev, mem_parLev, Base.levS] at hk ⊢
  rw [hQ] at hk
  exact hk


theorem levelCharacter_apply_eq_levelFunction_swap {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (k : B.levJ ψ) :
    B.levLam ψ k = levFn B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1.1) := by
  unfold Base.levLam Lev.levCharAfE
  rfl

theorem levLam_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (k : B.levJ ψ') :
    ((B.levLam ψ' k : ℂˣ) : ℂ) = τ ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) := by
  rw [levelCharacter_apply_eq_levelFunction_swap, levelCharacter_apply_eq_levelFunction_swap]
  exact (levFn_conj hB hψ hψ' hcc hf _).symm

variable {n : ℕ}

def cmapGL (τ : ℂ ≃+* ℂ) : GLR D n →* GLR D n :=
  MonoidHom.pi fun t => (Units.map (RingHom.mapMatrix (τ : ℂ →+* ℂ) : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom).comp
    (Pi.evalMonoidHom (fun _ : D.what₂.Tau => GL (Fin n) ℂ) t)

theorem cmapGL_val (τ : ℂ ≃+* ℂ) (y : GLR D n) (t : D.what₂.Tau) (a b : Fin n) :
    ((cmapGL τ y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b = τ (((y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) := rfl

theorem coefFn_conj (τ : ℂ ≃+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Pol ℂ D.what₂.Tau n) (y : GLR D n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map (τ : ℂ →+* ℂ) F) y = τ (coefFn (RingHom.id ℂ) lam F (cmapGL τ.symm y)) := by
  simp only [coefFn, map_mul]
  congr 1
  · simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    have e := RingHom.map_det (τ : ℂ →+* ℂ) (((cmapGL τ.symm y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    refine Eq.trans ?_ e.symm
    congr 1
    ext a b
    simp [cmapGL_val]
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    have e := MvPolynomial.hom_eval₂ F (RingHom.id ℂ) (τ : ℂ →+* ℂ)
      (fun v : D.what₂.Tau × Fin n × Fin n => ((cmapGL τ.symm y v.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
    refine Eq.trans ?_ e.symm
    congr 1
    funext v
    simp [cmapGL_val]

theorem cmapGL_embGL (τ : ℂ ≃+* ℂ) (hτ : ∀ (t : D.what₂.Tau) (e : D.host.E), τ (tauE D t e) = tauE D t e)
    (g : GL (Fin n) D.host.E) : cmapGL τ (embGL (tauE D) g) = embGL (tauE D) g := by
  funext t
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [cmapGL_val]
  exact hτ t _

theorem hasLaw_conj {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    {Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank} {κ : ℂ} (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {τ : ℂ ≃+* ℂ} (hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e)
    {ψ ψ' : Twist D Circle} (hψ : ψ.Good) (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ)
    {x x' : Bridge.Gf (Vc D i) → VsV D i ℂ} (hxx : ∀ h, ConjVec i τ (x h) (x' h))
    (hlaw : B.HasLaw ψ (fun h => Φ (x h))) : B.HasLaw ψ' (fun h => Φ ((τ κ / κ) • x' h)) := by
  intro γ h k
  have hfn : ∀ (w : VsV D i ℂ) z, harmFn (Wc D i).rank B.w B.F.BS (Φ w) z = κ * coefLin (lamV D i) w z :=
    fun w z => congrFun (hκ w) z
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨y, -, hy⟩ := γ.2
    exact ⟨y, hy.symm⟩
  set u := realGL B.F.θ (Vc D i) γ with hu_def
  have hu : u = embGL (tauE D) γE := realGL_rat hB.frame.vac.2.inf hγ
  have hact : ∀ P z, harmFn (Wc D i).rank B.w B.F.BS (B.act γ P) z =
      harmFn (Wc D i).rank B.w B.F.BS P (u⁻¹ * z) := fun P z => harmFn_fockGL _ _ _ _ _
  have hfix : ∀ z, cmapGL τ.symm (u⁻¹ * z) = u⁻¹ * cmapGL τ.symm z := by
    intro z
    rw [map_mul, hu, ← map_inv, cmapGL_embGL τ.symm hτE]
  have hconj : ∀ w z, coefLin (lamV D i) (x' w) z = τ (coefLin (lamV D i) (x w) (cmapGL τ.symm z)) := fun w z => by
    change coefFn (RingHom.id ℂ) (lamV D i) (x' w : Pol ℂ D.what₂.Tau (Vc D i).rank) z =
      τ (coefFn (RingHom.id ℂ) (lamV D i) (x w : Pol ℂ D.what₂.Tau (Vc D i).rank) _)
    rw [hxx w]
    exact coefFn_conj τ _ _ z
  set g := Bridge.ratF (Vc D i) γ * h * (k : Bridge.Gf (Vc D i)) with hg
  set lam : ℂ := ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) with hlam
  have hL : Φ (x g) = lam • B.act γ (Φ (x h)) := hlaw γ h ⟨k.1, mem_levJ_of B hcc.1 k.2⟩
  have E1 : ∀ z, coefLin (lamV D i) (x g) z = lam * coefLin (lamV D i) (x h) (u⁻¹ * z) := by
    intro z
    have e1 : harmFn (Wc D i).rank B.w B.F.BS (Φ (x g)) z =
        lam * harmFn (Wc D i).rank B.w B.F.BS (B.act γ (Φ (x h))) z := by
      rw [hL, map_smul]
      rfl
    rw [hact, hfn, hfn] at e1
    apply mul_left_cancel₀ hκ0
    rw [e1]
    ring
  have hl' : ((B.levLam ψ' k : ℂˣ) : ℂ) = τ lam := levLam_conj hB hψ hψ' hcc hf k
  show Φ ((τ κ / κ) • x' g) = ((B.levLam ψ' k : ℂˣ) : ℂ) • B.act γ (Φ ((τ κ / κ) • x' h))
  rw [hl']
  refine sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (GlobalTheory.CoefLatConj.pq_le hB) _
    (sub_mem (hval _) (Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (hval _)))) ?_)
  funext z
  have e2 : ∀ (P Q : PolF D (Wc D i).rank (Vc D i).rank) (a : ℂ), harmFn (Wc D i).rank B.w B.F.BS (P - a • Q) z =
      harmFn (Wc D i).rank B.w B.F.BS P z - a * harmFn (Wc D i).rank B.w B.F.BS Q z := fun P Q a => by
    rw [map_sub, map_smul]
    rfl
  rw [e2, hact, hfn, hfn, map_smul, map_smul]
  change κ * ((τ κ / κ) * coefLin (lamV D i) (x' g) z) - τ lam * (κ * ((τ κ / κ) * coefLin (lamV D i) (x' h) (u⁻¹ * z))) = 0
  rw [hconj, hconj, hfix, E1, map_mul]
  ring

theorem mtLat_conj : ∀ (D : D7) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → B.w.lam = lamV D i → ∀ (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) → (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → ∀ (ψ ψ' : Twist D Circle), ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = Φ x ∧ f' h = Φ ((τ κ / κ) • x')) → f ∈ B.mtLat σ emb O ψ → f' ∈ B.mtLat σ emb (O.map (τ : ℂ →+* ℂ)) ψ' := by
  intro D i B hB hlam Φ κ hκ0 hval hκ K _ _ σ emb O hc τ hτ ψ ψ' hψ hψ' hcc hf f f' hff hfm
  choose x x' hxx hfx hfx' using hff
  have hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e := fun t e => by
    rw [← hc.emb t, RingHom.comp_apply, τ.symm_apply_eq, hτ]
  obtain ⟨hform, hlat⟩ := (Base.mem_mtLat B σ emb O).1 hfm
  have hlaw : B.HasLaw ψ (fun h => Φ (x h)) := by
    have e : f = fun h => Φ (x h) := funext hfx
    rw [← e]
    exact ((Base.mem_formsC B).1 hform).2
  have e' : f' = fun h => Φ ((τ κ / κ) • x' h) := funext hfx'
  refine (Base.mem_mtLat B σ emb (O.map (τ : ℂ →+* ℂ))).2 ⟨(Base.mem_formsC B).2 ⟨fun h => (hfx' h).symm ▸ hval _, ?_⟩, fun h => ?_⟩
  · rw [e']
    exact hasLaw_conj hB hκ0 hval hκ hτE hψ hψ' hcc hf hxx hlaw
  · rw [hfx' h]
    exact (GlobalTheory.CoefLatConj.conj_mem_iff Φ hlam hκ0 hval hκ σ emb O τ hτ h (hxx h)).1 (hfx h ▸ hlat h)

end GlobalTheory.MtLatConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.thetaFunction_mem_span_of_coefficientSpan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  first | exact @GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span | exact GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span | (intros; apply GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.JSW.NzSphRam

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.JSW.NzSph

variable {E : Type} [Field E] [NumberField E]

theorem diagPow_eq_tD {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    GlobalTheory.JSW.diagPow ϖ l = GlobalTheory.IwaCell.tD ϖ (fun i => ((l i : ℕ) : ℤ)) := by
  apply Units.ext
  unfold GlobalTheory.IwaCell.tD
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_apply]

variable [_root_.NumberField.IsTotallyComplex E]

theorem exists_whittaker_ne_zero_induction_bad_places (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ g : GA E (m + 1),
      (∀ w ∉ T, w ∉ R → GlobalTheory.CellDec.compV E (m + 1) w
        ((GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1)⁻¹ * g) ∈ KGL w (n := (m + 1))) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T,
          whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  classical
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1 with ht0
  induction R using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E (m + 1) T (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E (m + 1) φ (π.cusp φ hφV).1 T hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E (m + 1) k)⁻¹ * t0⁻¹, fun w hw => ?_, ?_⟩
    · simp only [map_mul, map_inv]
      rw [comp_finGL, hk1 w hw, map_pLoc_pFin]
      simp only [map_mul, map_inv]
      group
    · have e : g * (finGL E (m + 1) k)⁻¹ * t0⁻¹ * t0 = g * (finGL E (m + 1) k)⁻¹ := by group
      rw [e]
      have e2 : g = g * (finGL E (m + 1) k)⁻¹ * finGL E (m + 1) k := by group
      rw [e2, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w R hwR ih =>
    intro φ hφV hφ g hg hW
    by_cases hwT : w ∈ T
    · refine ih φ hφV hφ g (fun v hv hvR => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwT), hvR⟩
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E (m + 1) w (ϖ w) (hϖ w) gw
    let z := GlobalTheory.JSW.diagPow (ϖ w)⁻¹ (fun _ : Fin (m + 1) => N)
    let d := GlobalTheory.JSW.diagPow (ϖ w) l
    let F : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
    have hF : ∀ h, F h = finGL E (m + 1) (locGL E (m + 1) w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwT k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E (m + 1) w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ T, ∀ k' ∈ KGL v (n := (m + 1)), act (.fin (locGL E (m + 1) v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E (m + 1) v k' * locGL E (m + 1) w z = locGL E (m + 1) w z * locGL E (m + 1) v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E (m + 1) w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2

    let e0 : ℤ := GlobalTheory.RamShift.condExp ϖ w
    let d0 := GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)))
    let ν : Fin (m + 1) → ℤ := fun i => ((l i : ℕ) : ℤ) - e0 * ((m : ℤ) - ((i : ℕ) : ℤ))
    have hν : 0 ≤ ν (Fin.last m) := by simp [ν]
    have hloc := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π w (α ⟨w, hwT⟩) (hα ⟨w, hwT⟩) φ₁ hφ₁V (hφ₁ w hwT) (ϖ w) (hϖ w) e0
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ w (hϖ w)) y hyw ν hν
    have htD : GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i) = d := by
      simp only [d, diagPow_eq_tD]
      congr 1
      funext i
      dsimp [ν]
      ring
    have h4 : whit φ₁.1 (y * F d0) ≠ 0 := by
      have h3' : whit φ₁.1 (y * finGL E (m + 1) (locGL E (m + 1) w
          (GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) ≠ 0 := by
        rw [htD]; exact h3
      rw [hloc] at h3'
      exact right_ne_zero_of_mul h3'
    refine ih φ₁ hφ₁V hφ₁ (y * F d0) (fun v hv hvR => ?_) h4
    by_cases hvw : v = w
    · subst hvw
      have hc : GlobalTheory.CellDec.compV E (m + 1) v t0 = d0 := by
        rw [ht0, GlobalTheory.CellDec.compV_tl, GlobalTheory.RamShift.shift_apply_of_notMem m ϖ hv]
      have hy1 : GlobalTheory.CellDec.compV E (m + 1) v y = 1 := hyw
      rw [map_mul, map_inv, map_mul, hc, hy1, hF, GlobalTheory.CellDec.compV_finGL_locGL_same, one_mul, inv_mul_cancel]
      exact one_mem _
    · have hyv' : GlobalTheory.CellDec.compV E (m + 1) v y = GlobalTheory.CellDec.compV E (m + 1) v g := hyv v hvw
      have hgv := hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvR⟩)
      rw [map_mul, map_mul, hyv', hF, GlobalTheory.CellDec.compV_finGL_locGL_ne hvw, mul_one, ← map_mul]
      exact hgv

end GlobalTheory.JSW.NzSphRam

namespace GlobalTheory.JSW.NzSphRam

open GlobalTheory.JSW.NzSph

theorem exists_sph_whit_tl_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
      ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T,
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  intro E _ _ _ m T π α hα ϖ hϖ
  classical
  let B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ := fun w =>
    if h : w ∈ T then 0 else Finset.univ.val.map (α ⟨w, h⟩)
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π T B (fun w hw => by
    simp only [B, dif_neg hw]; exact hα ⟨w, hw⟩)
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
  refine exists_whittaker_ne_zero_induction_bad_places m T π α hα ϖ hϖ hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwR => ?_) hg
  by_contra h
  refine hwR (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g)) ∉ KGL w (n := (m + 1))
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSphRam
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) m ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  first | exact @GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | exact GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | (intros; apply GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
end
