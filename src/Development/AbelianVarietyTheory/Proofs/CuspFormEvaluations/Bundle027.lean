module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LBPull
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RawChartGermBC

section Alg

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem map_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.map ψ (psTrunc m f) = psTrunc m (MvPowerSeries.map ψ f) := by
  unfold psTrunc

  rw [map_sum]
  simp only [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem map_psIn (d : ℕ) {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    MvPolynomial.map ψ (psIn d m r f) = psIn d m r (MvPowerSeries.map ψ f) := by
  unfold psIn
  rw [MvPolynomial.map_rename, map_psTrunc]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem appTop_toΓ_spMap (a : S) : (spMap ψ).appTop.hom (toΓ S a) = toΓ S' (ψ a) := by
  unfold toΓ
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

end Alg

section Pull

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)


theorem isPullSec_whisker_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 :=
  (LBPull.isPullSec_congr A L a (MonoidalCategory.comp_whiskerRight h2 h1 A) _ _ s1 s3).2
    (LBPull.isPullSec_comp A L a e1 e2)

end Pull

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem subst_rjBC (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetSubstP m φ')).left ≫ (rjBC ψ x0 d m n).left =
      (rjBC ψ x0 d m n').left ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  have hφ : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  subst hφ
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_rjBC (m n : ℕ) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ (rjBC ψ x0 d m n).left =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ (Fin n × Fin d) m)

theorem base_rjBC (m n : ℕ) :
    rjBase (spMap ψ ≫ x0) d m n ≫ ptBC ψ x0 = rjBC ψ x0 d m n ≫ rjBase x0 d m n := by
  apply Over.OverMorphism.ext
  unfold rjBC ptBC rjBase
  simp only [Over.comp_left, Over.homMk_left]
  refine spMap_comp_eq _ _ _ _ (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply]
  rw [show algebraMap S (Jet S (Fin n × Fin d) m) a = Ideal.Quotient.mk _ (MvPolynomial.C a) from rfl,
    PullbackSections.jetBC_mk, MvPolynomial.map_C]
  rfl

theorem overAt_hom_bc :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  unfold overAt
  simp [spMap]

theorem val_genPow {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z) (J) :
    val (genPow φ ε g k) r z J = val g r z J ^ k := by
  unfold genPow val
  exact map_pow _ _ _

theorem val_reL_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m)
    (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m)
    (he : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
      (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
    (wP : PrimTy H Xo) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m 1).left) (z : Z) {J}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (reL x0 d x act e wP m) (r ≫ (rjBC ψ x0 d m 1).left) z J := by
  have hφ : ∀ p : Fin 2 × Fin d,
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (MvPowerSeries.map ψ (act H.w0 j))] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S') p.1 p.2 =
      MvPolynomial.map ψ ((![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [map_psIn]
  have hxl : (x' m).left = (rjBC ψ x0 d m 1).left ≫ (x m).left := by
    rw [hx m]
    rfl
  unfold reL rpe
  simp only [val_mul hJ, val_pull hJ]
  congr 1
  · rw [hxl, Category.assoc]
  · refine (val_pull hJ _ _ r).trans ?_
    refine (val_corr hJ (he m) _).trans ?_
    refine (val_pull hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    simp only [Category.assoc]
    rw [subst_rjBC ψ x0 d m 2 1 _ _ hφ]

end Geo

end GlobalTheory.RawChartGermBC

namespace GlobalTheory


open RawChartGermBC in
theorem rawChart_baseChange_rig_germ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d _ act x x' hx e e' hge hge' he wP hwP
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx
  refine ⟨fun hrig => ?_, fun k Fs Fs' f hpull hgerm => ?_⟩
  · refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP 0 _ y hJ).trans ?_
    rw [Category.assoc, aug_rjBC ψ x0 d 0 1, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ?_
    refine (val_corr hJ hrig _).trans ?_
    rw [GermB.val_rigT _ _ _ _ _ _ _ hJ, GermB.val_rigT _ _ _ _ _ _ _ hJ, overAt_hom_bc ψ x0]
    simp only [Category.id_comp]
  · intro m
    obtain ⟨F0, τ0, hF0, hτ0, hv0⟩ := hgerm m
    obtain ⟨F1, hF1⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBase (spMap ψ ≫ x0) d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs'
    obtain ⟨F2, hF2⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBC ψ x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F0
    have hA := isPullSec_whisker_comp _ _ (k : ℤ) (rjBase x0 d m 1) (rjBC ψ x0 d m 1) hF0 hF2
    have hB := isPullSec_whisker_comp _ _ (k : ℤ) (ptBC ψ x0) (rjBase (spMap ψ ≫ x0) d m 1) hpull hF1
    have hB' := (LBPull.isPullSec_congr Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (congrArg (· ▷ Xo.univ.t.G) (base_rjBC ψ x0 d m 1)) _ (whiskerRight_snd _ _) Fs F1).1 hB
    have h12 : F1 = F2 := LBPull.isPullSec_unique _ _ _ hB' hA
    subst h12
    have hv := LBPull.isValueAt_pull Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (rjBC ψ x0 d m 1) (x m) hF2 hv0
    have hvb : (rjBC ψ x0 d m 1).left.appTop.hom (toΓ _ (psJet m f)) =
        toΓ _ (psJet m (MvPowerSeries.map ψ f)) := by
      rw [← PullbackSections.jetBC_psJet]
      exact appTop_toΓ_spMap (jetBC ψ (Fin 1 × Fin d) m) (psJet m f)
    rw [hvb] at hv
    refine ⟨F1, LB.pullGen Xo.univ.t.PP.L _ _ τ0 (rjBC ψ x0 d m 1).left, hF1, ?_, hv⟩
    refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_corr hJ hτ0 _).trans ?_
    rw [val_genPow, val_genPow, val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP m _ y hJ]

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FramePartialLaw

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_copy (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (i : Fin n) :
    (jetRen (S := S) d m r).comp (jetCopy d m i) = jetCopy d m (r i) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem pt_law (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (F p.2))) ≫ x m =
      jptG t x0 d x m (r 0) * jptG t x0 d x m (r 1) := by
  have hk : ∀ i, homAt x0 (jetRen d m r) ≫ jptG t x0 d x m i = jptG t x0 d x m (r i) := fun i => by
    rw [jptG, jptG, ← Category.assoc, homAt_comp, ren_copy]
  rw [subst_psIn, ← homAt_comp, Category.assoc, hch.law m, MonObj.comp_mul, hk, hk]

theorem th_pt {T : Over X0} (a b c : T ⟶ t.G) (I : thK) :
    (lift a (lift b c)).left ≫ thφ t.G (x3 t.G) I = (psum t.G ![a, b, c] I.down).left := by
  simp only [thφ, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a (lift b c) ≫ fst t.G (t.G ⊗ t.G) = a
    exact lift_fst _ _
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ fst t.G t.G) = b
    rw [lift_snd_assoc, lift_fst]
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ snd t.G t.G) = c
    rw [lift_snd_assoc, lift_snd]

theorem jetPt_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

abbrev threePts (m : ℕ) (i j k : Fin 3) : jOG x0 d m 3 ⟶ t.G ⊗ t.G ⊗ t.G :=
  lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))

theorem threePts_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (threePts (x := x) (m + 1) i j k).left = 𝟙 _ ≫ (threePts (x := x) m i j k).left := by
  rw [← Over.comp_left, Category.id_comp, threePts, threePts, comp_lift, comp_lift, jetPt_trunc hch, jetPt_trunc hch, jetPt_trunc hch]

end Chart

end GlobalTheory.FramePartialLaw

namespace GlobalTheory


open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry GlobalTheory.FramePartialLaw in

theorem exists_firstPartialLaw_series_of_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph1 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch e heg htr _
  have hL := t.PP.isLB
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x e m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph, hph⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (threePts (x := x) m 0 1 2).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hpe m _) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _)) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _))))
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, th_pt, pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_law hch, zpow_neg, Finset.prod_inv_distrib]
      erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      rw [prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
        prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      have ha : jptG t x0 d x m (0 : Fin 3) * jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) =
          jptG t x0 d x m (0 : Fin 3) * (jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3)) := _root_.mul_assoc _ _ _
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      erw [ha]
      abel!)
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (threePts_trunc hch m 0 1 2)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.universal_symLift_mul_odd : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (a b : T ⟶ Xo.univ.t.G) (Ua Ub Uab : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T) (e : Γ(T.left, ⊤)ˣ), SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) a Ua → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) b Ub → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (a * b) Uab → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) a b e → ∃ r : Γ(T.left, ⊤)ˣ, r ^ 2 = e ∧ r ^ (N ^ 2) = 1 ∧ ∀ s s₁ s₂ s₃ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T), IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ub s s₁ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ua s₁ s₂ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Uab s s₃ → ∀ j, s₂.f j = liftFun Xo.univ.t.G _ (r : Γ(T.left, ⊤)) * s₃.f j := by
  first | exact @GlobalTheory.moduli_univ_symLift_mul | exact GlobalTheory.moduli_univ_symLift_mul | (intros; apply GlobalTheory.moduli_univ_symLift_mul <;> assumption)
end
