module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagWeil

theorem diag_psum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : Finset (Fin 2)) :
    lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I = psum A ![𝟙 A, 𝟙 A] I := by
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd, pzero, x2, List.finRange_succ]

theorem lbIso_lam_diag (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB) :
    LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) (cubeLB A ![𝟙 A, 𝟙 A] M) := by
  refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _ ?_
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [← Over.comp_left, diag_psum]

end GlobalTheory.DiagWeil


open GlobalTheory.TorusRM.DiagFrame in
theorem GlobalTheory.DiagWeil.weilIs_diag_lam : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  intro A _ _ g hA _ M u Hm χ hM hF N hN hNc hamp k a b c hk ha hb hc
  have : IsProper A.hom := hA.proper
  have hL : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hcube : (cubeLB A ![𝟙 A, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have hLN : LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) N :=
    LBIso.trans hL hcube hN (GlobalTheory.DiagWeil.lbIso_lam_diag A hM) hNc.symm
  have hampL : Out.RelAmple A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self hN hL hLN hamp
  have hF' := isFactorAH_diagUnif u hF
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hampL g (diagUnif u) _ _ hF'.1 hF'.2.1 hF'.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' hpos
  have hc' : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (((a ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star b)).im : ℝ) : ℂ) / k) := by
    rw [hc]
    congr 4
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
    simp [hermForm]
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hL g (diagUnif u) _ _ hAH k a b c hk ha hb hc'
  rw [diagUnif_ex] at hw
  exact GlobalTheory.PELFamily.weilIs_of_lbIso GlobalTheory.globalFns_holds hA hN hL
    (LBIso.trans hN hL (pull_isLB hL _) hLN.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL)) hw
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this


omit [GrpObj A] [GrpObj A'] in
theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieAt_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} {R' : Type} [CommRing R']
    {β : R →+* R'} {x : Sp R' ⟶ S} (h : LieHer b act β x) : LieAt b act β x := by
  have H := (h R' (RingHom.id R')).1
  have e : spMap (RingHom.id R') = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

theorem lieMult_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} (k : Type) [Field k]
    [IsAlgClosed k] {β : R →+* k} {x : Sp k ⟶ S} (h : LieHer b act β x) (i : Fin D.a) :
    LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  have H := (h k (RingHom.id k)).2 k (RingHom.id k) i
  have e : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

end GlobalTheory.HTMkObj

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem exists_obj_of_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  intro p _ D R _ b N _ _ h M B _ ζ S s₁ t c e he hc X πX AX _ _ φX φ₂X actX ηX hX sqX hRos hEta Z j hLie hGeom
  let A' := (Over.pullback (j ≫ πX)).obj c.A
  let φ := PullbackComparison.pφ (j ≫ πX) c.A
  let φ₂ := PullbackComparison.pφ₂ (j ≫ πX) c.A
  have pb : IsGrpPullback A' c.A (j ≫ πX) φ := PullbackComparison.isGrpPullback (j ≫ πX) c.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare (j ≫ πX) c.A
  have wψ : φ ≫ c.A.hom = (A'.hom ≫ j) ≫ πX := by
    rw [Category.assoc]; exact pb.1.w
  let ψ : A'.left ⟶ AX.left := hX.1.lift φ (A'.hom ≫ j) wψ
  have hψ : ψ ≫ φX = φ := hX.1.lift_fst _ _ _
  have hψh : ψ ≫ AX.hom = A'.hom ≫ j := hX.1.lift_snd _ _ _
  have pbj : IsGrpPullback A' AX j ψ := IsGrpPullback.cancel hX (by rw [hψ]; exact pb) hψh
  let ψ₂ : (G2 A').left ⟶ (G2 AX).left :=
    pullback.lift ((fst A' A').left ≫ ψ) ((snd A' A').left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hψh, ← Category.assoc, ← Category.assoc, Over.w (fst A' A'),
        Over.w (snd A' A')])
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hψ₂ : ψ₂ ≫ φ₂X = φ₂ := by
    refine pullback.hom_ext (f := c.A.hom) (g := c.A.hom) ?_ ?_
    · show (ψ₂ ≫ φ₂X) ≫ (fst c.A c.A).left = φ₂ ≫ (fst c.A c.A).left
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sq.1]
    · show (ψ₂ ≫ φ₂X) ≫ (snd c.A c.A).left = φ₂ ≫ (snd c.A c.A).left
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sq.2]
  have hab : IsAbelianScheme A' :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := GlobalTheory.ActPull.exists_act_pull X Z j AX A' ψ pbj D.Oᵐᵒᵖ
    (fun a => actX.act a.unop) (fun a => actX.hom _) (by simpa using actX.one)
    (fun a b => by simpa using actX.mul b.unop a.unop) (fun a b => by simpa using actX.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ ψ = ψ ≫ (actX.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := c.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB c.isLB φ₂
  have iso : LBIso P' (c.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have hPX : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso P' ((c.P.pull φ₂X).pull ψ₂) :=
    LBIso.chartPull (chartPullSame c.P (fun _ : PUnit => φ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => (Category.comp_id _).symm))
      (chartPullLinComb c.P φ₂X (fun _ : PUnit => ψ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => by rw [hψ₂, Category.comp_id]))
      (PullbackComparison.gen_refl _ (pull_isLB c.isLB _))
  have dgX := SiegelPull.diag_iso sqψ H
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 AX ⟶ AX), x'.left ≫ ψ = ψ₂ ≫ x.left → y'.left ≫ ψ = ψ₂ ≫ y.left →
      (lift x' y').left ≫ ψ₂ = ψ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sqψ (T := Over.mk (ψ₂ ≫ (G2 AX).hom)) (T' := G2 A') (𝟙 _)
      x' y' (Z := G2 AX) ψ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  have rosP : RosatiFor D actN ((c.P.pull φ₂X).pull ψ₂) := fun a => LBIso.chartPull
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.1, Category.assoc])
      (by rw [sqψ.2])))
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by rw [sqψ.1]) (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.2, Category.assoc])))
    (hRos a)
  obtain ⟨t₁, ht₁⟩ := c.rig₁
  obtain ⟨t₂, ht₂⟩ := c.rig₂
  let u : Obj b N ((j ≫ πX) ≫ t) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id (j ≫ πX) c.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one (j ≫ πX) c.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
        (chartPullLinComb c.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap (j ≫ πX) c.A)) c.symm
      ample := (pol_pull S Z c.A A' (j ≫ πX) φ _ _ (pull_isLB c.isLB _) (pull_isLB hP' _) c.ab pb dg).2.1 hc.1
      kerP := ⟨e, he, fun T x hx => kerBy_pull pb sq c.isLB hP' iso e hc.2 T x hx⟩
      rosati := RosatiFor.of_iso (pull_isLB hPX _) hP' (LBIso.symm H) rosP
      lie := fun R' _ β x hx v hv => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pbj (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ j)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := lieAt_of_lieHer b (hLie R' β x hx') (e v)
          ((HTPull.isTanScal_iff pbj actX actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (HTPull.isTanScal_iff pbj actX actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) X Z AX A' j ψ (actX.toF D) (actN.toF D) pbj
          (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (lieMult_of_lieHer b k (hLie k β x hx') i)
      eta := fun y => SiegelPull.secPull pbj (ηX y)
      eta_add := fun y z => SiegelPull.push_injective pbj _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', hEta.1, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pbj _ (by
        rw [HTPull.push_comp pbj (hact c), push_secPull', push_secPull', hEta.2.1, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pbj _ (by
        rw [push_secPull', hEta.2.2, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨I, hI⟩ := hGeom k x β hx'
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ j) ⟶ AX) := MulEquiv.ofBijective (pushHom pbj (Over.mk x))
          ⟨SiegelPull.push_injective pbj _, SiegelPull.push_surjective pbj _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ actX.act c := fun c g => HTPull.push_comp pbj (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ ψ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm X Z AX A' j ψ _ _ (pull_isLB hPX _)
                    (pull_isLB hP' _) pbj dgX (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pbj (ηX y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pbj (ηX y) (Over.mk x)).symm }
  exact ⟨u, ψ, φ₂, pbj, by rw [hψ]; exact sq, iso, hact, fun y => SiegelPull.secPull_left pbj _⟩

end GlobalTheory.HTMkObj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.DvrAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar
section
open GlobalTheory.UT.CoefUnit GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallPoint GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallZero GlobalTheory.UT.CoefBasic GlobalTheory.UT.SmallPoint

end
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar GlobalTheory.UT.MixedConv GlobalTheory.FieldBaseChange
section CoreAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end CoreAny
section FieldAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

end FieldAny

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

theorem qkToAkU_level_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN p q x hy hg hx
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
  have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
    (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
  obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk p x x₀ hx a
  exact (indAtTransl_any hL R I hI D A G hG U F N hN1 q x).1 (h₀ n N hn hN q hy hg)

end GlobalTheory.DvrAnyChar
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

abbrev KK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

def cmpφ (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) : KK → ((P₀.A ⊗ P₀.A).left ⟶ P₁.A.left ⨿ P₂.A.left) :=
  Sum.elim (fun I => (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] I.down).left ≫ coprod.inr)
    (fun I => (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] I.down).left ≫ coprod.inl)

def cmpε : KK → ℤ := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -((-1) ^ (2 - I.down.card)))

abbrev CmpL (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) : LB (P₀.A ⊗ P₀.A).left :=
  LB.LinComb (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) cmpε

end GlobalTheory.Mum.Two.WeilCmp
end
end

section

open IsLocalRing GlobalTheory.TorRef

theorem _root_.GlobalTheory.T.exists_completeDVR_valuation_completeNormalLocal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  first | exact @GlobalTheory.DivBound.exists_cdvr_valuation_le | exact GlobalTheory.DivBound.exists_cdvr_valuation_le | (intros; apply GlobalTheory.DivBound.exists_cdvr_valuation_le <;> assumption)
end
