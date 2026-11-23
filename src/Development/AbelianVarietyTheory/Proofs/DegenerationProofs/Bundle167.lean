module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle163
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle009
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ThetaData

theorem valR_eq_gs {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint R) ∈ U) (f : Γ(X, U)) :
    valR x U f = (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gs x (IsLocalRing.closedPoint R) U f) := by
  have h' := (CrdCalc.top_le_iff x U).2 h
  rw [CrdCalc.valR_eq x U h', gs_eq x _ U h]
  have e := germ_stalkClosedPointIso_hom (CommRingCat.of R)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE h').op).hom ((x.app U).hom f)) = _
  rw [← e]
  exact congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom
    (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') _ trivial _)

theorem crd_of_chartSec {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y}
    {h : Y' ⟶ Y} (a : ChartPull A' A h) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A' (fun j => chartSec a (s j)) x v) : Crd A s (x ≫ h) v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m := (CrdCalc.top_le_iff x _).1 hl
  have m' : (x ≫ h) (IsLocalRing.closedPoint R) ∈ A.U (a.idx l) := a.le l m
  refine ⟨a.idx l, c, (CrdCalc.top_le_iff _ _).2 m', fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m', gs_chartSec a (s j) x _ l m]

theorem crd_secPull {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A : LB Y}
    (h : Y' ⟶ Y) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A s (x ≫ h) v) : Crd (A.pull h) (fun j => secPull (s j) h) x v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m' := (CrdCalc.top_le_iff _ _).1 hl
  have m : x (IsLocalRing.closedPoint R) ∈ (A.pull h).U (fun _ => l) := mem_pull.2 m'
  refine ⟨fun _ => l, c, (CrdCalc.top_le_iff _ _).2 m, fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m']
  exact congrArg (fun q => (c : R) * (stalkClosedPointIso (CommRingCat.of R)).hom.hom q)
    (gs_chartSec (GlobalTheory.chartPullPull A h) (s j) x _ (fun _ => l) m).symm

theorem exists_twist_sections {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -1])} (hα : α.IsGen) {J : Type}
    (s : J → LB.Sec (LPow A L a T)) (th : LB.Sec (LPow A L 1 T)) (i₀ : J)
    (H : IsTwistPull A L ψ m hm a 1 α th (s i₀)) {Y : Scheme.{0}} (κ : Y ⟶ (T ⊗ A).left) (F : Y ⟶ A.left)
    (hF : κ ≫ (snd T A).left = F) (n : Y ⟶ Y) (hn : n ≫ κ = κ ≫ ψ.left) :
    ∃ (θ : (L.pull F).Sec) (t : J → ((L.pull F).pull n).Sec),
      (∀ (K : Type) [Field K] (x : Sp K ⟶ Y) (v : J → K), Crd _ t x v → Crd (LPow A L a T) s (x ≫ κ) v) ∧
      ∀ (y : Y) (j : (L.pull F).ι), n y ∈ (L.pull F).U j →
        gs (𝟙 Y) y _ ((t i₀).f (fun _ => j)) = gs n y _ (θ.f j) := by
  have e : κ ≫ m.left = n ≫ F := by
    rw [← hm, Over.comp_left, ← Category.assoc, ← hn, Category.assoc, hF]
  obtain ⟨θ, hθ⟩ := exists_sec hL (φ := fun _ : Fin 1 => F) (ε := fun _ => 1) (φ' := fun _ : PUnit => F)
    (ε' := fun _ => 1) (fun U _ h => by simp)
    (VVRank.pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => 1) th κ (fun _ => hF))
  have hu := LB.isGen_invGen L _ _ _ (LB.isGen_pullGen L _ _ α hα κ)
  have hσ : ∀ j, ∃ σ : (L.pull (n ≫ F)).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I), Good L z I →
      sval (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) σ r z I =
        VVRank.sv A (s j) (r ≫ κ) z I * ((val α (r ≫ κ) z I)⁻¹).val := by
    intro j
    obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := fun _ : PUnit => n ≫ F) (ε' := fun _ => 1)
      (fun U _ h => by simp [Fintype.prod_sum_type, e])
      (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s j) κ _ hu)
    refine ⟨σ, fun Z r z I hI => (hσ Z r z I hI).trans ((sval_pullMulSec _ κ _ hu r z hI).trans ?_)⟩
    rw [val_inv, val_pull hI]
  choose σ hσ using hσ
  let c := chartPullLinComb L F (fun _ : PUnit => n) (fun _ : PUnit => n ≫ F) (fun _ => 1) (𝟙 Y)
    (fun _ => (Category.id_comp _).symm)
  refine ⟨θ, fun j => chartSec c (σ j), fun K _ x v hv => ?_, fun y j hj => ?_⟩
  · obtain ⟨l, u, hl, hv⟩ := crd_of_chartSec c σ x v hv
    rw [Category.comp_id] at hl hv
    have m₁ := (CrdCalc.top_le_iff _ _).1 hl
    obtain ⟨I, hI, eI⟩ := exists_good L hL (IsLocalRing.closedPoint K : Sp K) (fun _ : PUnit => x ≫ n ≫ F) l
      (fun _ _ _ => rfl) (fun k => Set.mem_iInter.1 m₁ k)
    have m₂ := hI.mem (fun _ : Fin 1 => (snd T A).left) (x ≫ κ)
    refine ⟨fun _ => I ((x ≫ κ) ≫ (snd T A).left), u * Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom
      (val α (x ≫ κ) _ I)⁻¹, (CrdCalc.top_le_iff _ _).2 m₂, fun j => ?_⟩
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ j) x _ I l eI).symm.trans (hσ j _ x _ I hI)
    refine (hv j).trans ?_
    refine (congrArg (_ * ·) ((valR_eq_gs x _ m₁ _).trans ((congrArg _ e₁).trans (map_mul _ _ _)))).trans ?_
    rw [Units.val_mul, _root_.mul_assoc, _root_.mul_comm (Units.val (Units.map _ _))]
    exact congrArg (fun q => (u : K) * (q * _)) (valR_eq_gs (x ≫ κ) _ m₂ _).symm
  · have m₁ : (n ≫ F) y ∈ L.U (j PUnit.unit) := mem_pull (F := F).1 hj
    obtain ⟨I, hI, eI⟩ := exists_good L hL y (fun _ : PUnit => n ≫ F) j (fun _ _ _ => rfl) (fun k => m₁)
    refine (gs_chartSec c (σ i₀) (𝟙 Y) y (fun _ => j) (mem_pull (F := n).2 hj)).trans ?_
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ i₀) (𝟙 Y ≫ 𝟙 Y) y I j
      (fun k => by simpa using eI k)).symm.trans (hσ i₀ _ _ _ I hI)
    have e₂ := (sval_of (φ := fun _ : PUnit => F) (ε := fun _ => 1) θ n y I j eI).symm.trans
      ((hθ _ n y I hI).trans (VVRank.sval_pullTo _ _ _ _ _ hI))
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    rw [VVRank.sv_of_isTwistPull A H _ y hI, mul_right_comm, Units.mul_inv, _root_.one_mul, hn]
    simp only [Category.id_comp]

theorem mulN_eq_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (𝟙 G ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ 𝟙 G ^ n = pushHom h G' (𝟙 G') ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_id_pow] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_iso [ArithBase o Ω] (hLL : GlobalTheory.UT.LL) {S : ThetaSys o Ω} (ρ : S.Real) {B : Scheme.{0}} (A' : Over B)
    [GrpObj A'] [IsCommMonObj A'] [IsIntegral A'.left] {f : B ⟶ Sp S.R} {F : A'.left ⟶ ρ.P.A.left}
    (h : IsGrpPullback A' ρ.P.A f F) {Y : Scheme.{0}} (a : A'.left ⟶ Y) {O : LB Y} (hO : O.IsLB) (st : S.J → O.Sec)
    (hc : ∀ (K : Type) [Field K] (x : Sp K ⟶ A'.left) (v : S.J → K), ρ.Crd (x ≫ F) v → Crd O st (x ≫ a) v) :
    ∃ (θ : (ρ.P.L.pull F).Sec) (w : LB.Iso ((ρ.P.L.pull F).pull (mulN A' (ρ.n ^ ρ.k)).left) (O.pull a)), w.IsGen ∧
      ∀ (x : A'.left) (i : O.ι) (j : (ρ.P.L.pull F).ι), a x ∈ O.U i →
        (mulN A' (ρ.n ^ ρ.k)).left x ∈ (ρ.P.L.pull F).U j →
        gs a x _ ((st ρ.i₀).f i) = gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val *
          gs (mulN A' (ρ.n ^ ρ.k)).left x _ (θ.f j) := by
  have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
  let κ := F ≫ inv (snd (baseOver (Sp S.R)) ρ.P.A).left
  have hκ : κ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = F := by simp [κ]
  have hn : (mulN A' (ρ.n ^ ρ.k)).left ≫ κ = κ ≫ (mulT ρ.P.A (baseOver (Sp S.R)) (ρ.n ^ ρ.k)).left := by
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, Category.assoc, hκ, mulN_comp h, Category.assoc,
      ← Over.comp_left, mulT, lift_snd, ← hκ, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨θ, t, ht, hθ⟩ := exists_twist_sections ρ.P.A ρ.P.isLB ρ.α_gen ρ.s ρ.th₁ ρ.i₀ ρ.s_zero κ F hκ _ hn
  have hH := LB.isLB_pull (LB.isLB_pull ρ.P.isLB F) (mulN A' (ρ.n ^ ρ.k)).left
  have hcov : ⨆ j, nonzeroLocus (t j) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨K, _, p, hp⟩ := CrdIso.exists_pt y
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH t p
    have h₀ := (ThetaSys.Real.immBy_basis hLL o Ω S ρ).1
    have h₁ : (p ≫ κ) (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
      rw [h₀]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h₁
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have h₂ := (CrdCalc.crd_isUnit_iff i (ht K p v hv)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hp _).1 ((CrdCalc.crd_isUnit_iff i hv).1 h₂)⟩
  obtain ⟨w, hw, hs⟩ := CrdIso.exists_iso_of_crd _ _ (O.pull a) _ t (fun j => secPull (st j) a) hH
    (LB.isLB_pull hO a) hcov (fun K _ x v hv => crd_secPull a st x v
      (hc K x v ⟨x ≫ κ, by rw [Category.assoc, hκ], ht K x v hv⟩))
  refine ⟨θ, w, hw, fun x i j hi hj => ?_⟩
  have e := hs ρ.i₀ x (fun _ => j) (fun _ => i) (mem_pull.2 hj) (mem_pull.2 hi)
  rw [hθ x j hj] at e
  refine Eq.trans ?_ e
  have e' := gs_chartSec (GlobalTheory.chartPullPull O a) (st ρ.i₀) (𝟙 _) x (fun _ => i) (mem_pull.2 hi)
  rw [Category.id_comp] at e'
  exact e'.symm

theorem exists_theta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) := by
  intro hLL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  have := ex.ab.comm
  have hI : IsIntegral ex.core.A.left := by
    have := ex.core.isIntegral_G
    have := ex.core.isOpenImmersion_a
    have := ex.core.nonempty_A
    exact isIntegral_of_isOpenImmersion ex.core.a
  have : IsIntegral ((Over.pullback Q.u₀).obj ρ.P.A).left := hI
  have h := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨c⟩ := (hLL.1.cube _ ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  obtain ⟨hL, hr, ⟨c', -⟩, -⟩ := hLL.2.2.1.cubePull _ _ _ _ (cubeMapOf h) _ c
  obtain ⟨θ, w, hw, hs⟩ := exists_iso hLL ρ _ h ex.a (LB.isLB_pull Q.isLB Q.G.ι) (fun j => secPull (Q.st j) Q.G.ι)
    (fun K _ x v hv => crd_secPull _ _ _ _ (by
      have e := Q.crd K x v hv
      rw [← ex.a_eq] at e
      rw [Category.assoc]
      exact e))
  have hm : IsUnit ((ρ.n ^ ρ.k : ℕ) : Γ(M.Z, ⊤)) := by
    have h₁ : IsUnit ((ρ.n ^ ρ.k : ℕ) : o) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast (ρ.N_eq ▸ Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) S.r)) S.unit
    have h₂ := h₁.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at h₂
  refine ⟨⟨_, c', θ, ρ.n ^ ρ.k, hm, _, LB.isLB_pull Q.isLB Q.G.ι, secPull (Q.st ρ.i₀) Q.G.ι, w, hw, hs,
    fun z hz => ?_⟩, lbIso_refl hL⟩
  obtain ⟨x, hx, hG', e⟩ := GlobalTheory.T.exists_theta_pullback_nonzero_on_closed_fibre hLL o Ω S ρ M U₀ EE hB Q hS hG z hz
  refine ⟨⟨x, hG'⟩, ?_, e⟩
  erw [nonzeroLocus_secPull]
  exact hx

end GlobalTheory.ZH.ThetaData
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ModelBasis
open GlobalTheory.FieldBaseChange GlobalTheory.IntegralCombination GlobalTheory.ZH GlobalTheory.ZH.AdaptedSpan

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

theorem toGen_injective (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) : Function.Injective (toGen U k) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have h₁ : IsSchemeTheoreticallyDominant (jK V) := h.2
  have h₂ : QuasiCompact (jK V) := h.1
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) := inferInstance
  exact GlobalTheory.ConstFam.pullOver_injective_of_dominant _ _ _ _

theorem chart_sum {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of V)} {M : LB Y} {J : Type} [Fintype J]
    (c : J → V) (x : J → SecOver p M) (j : M.ι) :
    LB.Sec.f (∑ i, c i • x i : SecOver p M) j = ∑ i, resTop _ (scal p (c i)) * LB.Sec.f (x i) j :=
  map_sum (chartLin p M j) (fun i => c i • x i) _


open Classical in
theorem mem_maximalIdeal (hW : WeightIndepSt) (U : UnifPre (maximalIdeal V) D A G) {k : ℕ} {J : Type} [Fintype J]
    (σ : J → SecG U k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (hE : ∀ i, U.ExpandsAt 0 k (σ i) (f i)) (hz : ∀ i i₀, cls i ≠ cls i₀ → f i (cls i₀) = 0)
    (hB : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))) (c : J → V)
    (h : ∀ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (LB.Sec.f (∑ i, c i • σ i : SecG U k) j) = 0) (i₀ : J) :
    c i₀ ∈ maximalIdeal V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨g, hg⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 k (cls i₀) _).1
    (hW V _ D A G U 0 k _ _ h (expandsAt_sum U 0 k σ f hE c) (cls i₀))
  obtain ⟨a, ha, -⟩ := hB i₀ g
  let β : {i // cls i = cls i₀} → SecAb D.toPre k (cls i₀) := fun i => f i (cls i₀)
  have e₁ : (show SecAb D.toPre k (cls i₀) from g) = ∑ i, a i • β i :=
    SecOver.ext _ _ fun j => (ha j).trans (chart_sum a β j).symm
  have e₂ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) =
      ϖ ^ (0 + 1) • (show SecAb D.toPre k (cls i₀) from g) := SecOver.ext _ _ hg
  have e₃ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) = ∑ i : {i // cls i = cls i₀}, c i • β i := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
        (fun i _ => by rw [hz i i₀ i.2, smul_zero]), add_zero]
  have e₄ : (∑ i : {i // cls i = cls i₀}, c i • β i) = ∑ i, (ϖ ^ (0 + 1) * a i) • β i := by
    rw [← e₃, e₂, e₁, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have e₅ := (hB i₀ (∑ i : {i // cls i = cls i₀}, c i • β i : SecAb D.toPre k (cls i₀))).unique
    (y₁ := fun i => c i) (y₂ := fun i => ϖ ^ (0 + 1) * a i) (fun j => chart_sum _ β j)
    (fun j => by rw [e₄]; exact chart_sum _ β j)
  have e₆ : c i₀ = ϖ ^ (0 + 1) * a ⟨i₀, rfl⟩ := congrFun e₅ ⟨i₀, rfl⟩
  rw [e₆, zero_add, pow_one]
  exact Ideal.mul_mem_right _ _ hϖ.not_isUnit

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f → ∃ σ : Fin r → H0 U.LG.L k, (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧ IsBasisH σ := by
  intro hL V _ _ _ D Q A G _ _ U k hk r cls mu f ⟨⟨_, h₂, h₃, _⟩, h₅, h₆, h₇⟩
  have ex : ∀ i, ∃ σ : SecG U.toUnifPre k, ∀ e, U.ExpandsAt e k σ (f i) := fun i => by
    obtain ⟨s, hs⟩ := h₅ i
    exact GlobalTheory.IntegralExpansion.main hL.1 V D A G U k hk s (f i) hs
  choose σ hσ using ex
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨a, ha⟩ := AdaptedSpan.exists_comb hL.1.globalFns U hk σ cls f h₂ h₃ hσ h₅ h₆ h₇ (toGen U.toUnifPre k s)
  obtain ⟨d, b, hd, hb⟩ := exists_denom a
  have e : (d • (show SecG U.toUnifPre k from s)) = ∑ i, b i • σ i := toGen_injective U.toUnifPre k (by

    rw [map_smulₛₗ, map_sum, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul, hb])
  refine GlobalTheory.SaturatedSections.existsUnique_comb
    (A := fun j => Γ(G.left, (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))).U j))
    (fun j => GlobalTheory.SaturatedSections.cst G.hom _) hϖ
    (fun j x hx => GlobalTheory.SaturatedSections.eq_zero_of_cst_mul G.hom _ hϖ.ne_zero x hx) (fun i j => LB.Sec.f (σ i) j)
    (fun c y hy => mem_maximalIdeal hL.2.2.2.1.weightIndep U.toUnifPre σ cls f (fun i => hσ i 0)
      (fun i i₀ h => SecOver.ext _ _ fun j => h₆ i (cls i₀) (fun m hm => h (h₂ i₀ i ⟨m, hm⟩).symm) j) h₇ c
      fun j => ?_) s.f d b hd fun j => ?_
  · refine (GlobalTheory.ThickDiv.app_eq_zero_iff hϖ G 0 _ _).2 ⟨y j, ?_⟩
    rw [zero_add, pow_one]
    exact (chart_sum c σ j).trans (hy j).symm
  · exact (congrArg (fun t : SecG U.toUnifPre k => LB.Sec.f t j) e).trans (chart_sum b σ j)

end GlobalTheory.OneBasis.ModelBasis
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section

namespace GlobalTheory.DescendIso

theorem isCoordPt_cart (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact FullExtend.isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) hp hw σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (FullExtend.isGenSec_base hS P₀ t) hx hk hz H

theorem exists_unit_smul {K C : Type} [Field K] [Field C] (f : K →+* C) {I : Type} (v₀ v : I → K) (c : Cˣ)
    (h : ∀ x, f (v x) = c * f (v₀ x)) : ∃ d : Kˣ, v = (d : K) • v₀ := by
  by_cases h₀ : ∀ x, v₀ x = 0
  · refine ⟨1, funext fun x => f.injective ?_⟩
    simp [h x, h₀ x]
  · push Not at h₀
    obtain ⟨y, hy⟩ := h₀
    have hy' : f (v₀ y) ≠ 0 := (map_ne_zero f).2 hy
    have e : f (v y / v₀ y) = c := by rw [map_div₀, h y, mul_div_assoc, div_self hy', _root_.mul_one]
    have hd : v y / v₀ y ≠ 0 := fun q => c.ne_zero (by rw [← e, q, map_zero])
    refine ⟨Units.mk0 _ hd, funext fun x => f.injective ?_⟩
    rw [h x, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mk0, e]

theorem isCoordPt_descend (hL : Laws) {K C : Type} [Field K] [IsAlgClosed K] [Field C] [IsAlgClosed C] {f : K →+* C}
    {P₀ : PolAV (Sp K)} {P : PolAV (Sp C)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {m : ℕ} (hm : Odd m) (hK : (m : K) ≠ 0) {I : Type}
    {x : I → (baseOver (Sp C) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (m ^ 2) = 1)
    (hk₀ : ∀ i, x₀ i ^ (m ^ 2) = 1)
    {z : baseOver (Sp C) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    (v : I → K) (v' : I → C) (s : Cˣ) (hv : ∀ i, f (v i) = s * v' i)
    (H : IsCoordPt P m x z fun i => fnOf (v' i)) : IsCoordPt P₀ m x₀ z₀ fun i => fnOf (v i) := by
  have hC : (m : C) ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hK
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) P₀ (𝟙 _) m hm hK I x₀ hk₀
  obtain ⟨-, b₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) P (𝟙 _) m hm hC I x hk
  obtain ⟨v₀, h₀⟩ := a₁ z₀
  have q := isCoordPt_cart hL.secBaseChange hp hw hx hk hz h₀
  simp only [← FullExtend.fnOf_map] at q
  obtain ⟨c, hc⟩ := (b₂ z (fun i => f (v₀ i)) v' q).1 H
  refine (a₂ z₀ v₀ v h₀).2 (exists_unit_smul f v₀ v (s * c) fun i => ?_)
  rw [hv, hc, Pi.smul_apply, smul_eq_mul, Units.val_mul, _root_.mul_assoc]

theorem exists_descend : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  intro hL E _ _ _ H D K C _ _ f o o' hext I' ζ hζ
  obtain ⟨-, hz, φ, hp, hw, -, hev⟩ := hext
  haveI := o.closed
  haveI := o'.closed
  haveI := o.charZero
  haveI := o'.charZero
  obtain ⟨g, hg⟩ := tateIso_differ_by_similitude E H D C _ _ _
    (fun n x y c c' _ _ _ => weilIs_unique_fieldPoint _ _ _ o'.P.isLB C (𝟙 _) n x y c c') o'.I I'
  obtain ⟨ν, h₀, h₁, h₂⟩ := ReZeta.exists_exponent o'.I.ζ I'.ζ o'.I.ζ_prim o'.I.ζ_pow I'.ζ_prim I'.ζ_pow
  have hd : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n - ν n := fun n hn => by
    rw [← (o'.I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, ← (hg n hn).2, h₀ n hn, mul_inv_cancel]
  have hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ) :=
    fun n m hn hm => by
      obtain ⟨a, ha⟩ := hd n hn
      obtain ⟨b, hb⟩ := hd (n * m) (Nat.mul_pos hn hm)
      obtain ⟨c, hc⟩ := h₂ n m hn hm
      obtain ⟨u, w, huw⟩ := h₁ n hn
      push_cast at hb
      exact ⟨⟨m * b + c - a, by linear_combination hb + hc - ha⟩, u, w - u * a, by linear_combination huw + u * ha⟩
  let I : FullI o := LevelTwist.twist o.I g hν
  have hI : ∀ n, 0 < n → ∀ a, spMap f ≫ (I.ev n a).left = (I'.ev n a).left ≫ φ := fun n hn a => by
    rw [(hg n hn).1 a]
    exact (hev n _ hn).symm
  have key : ∀ m, Odd m → ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) →
      (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := fun m hm j hj z v v' s hv Q =>
    isCoordPt_descend hL hp hw hm (Nat.cast_ne_zero.2 hm.pos.ne') (hI _ (pow_pos hm.pos 2))
      (tateIso_ev_pow I' (pow_pos hm.pos 2)) (tateIso_ev_pow I (pow_pos hm.pos 2)) (hI j hj z) v v' s hv Q
  refine ⟨I, fun n hn => Units.ext (f.injective ?_), fun m hm => ⟨fun v v' s hv Q => ?_, key m hm⟩⟩
  · rw [← hζ n hn, (hg n hn).2, Units.val_zpow_eq_zpow_val, hz n hn, ← map_zpow₀, ← Units.val_zpow_eq_zpow_val]
    rfl
  · have e : I.ev 1 0 = 1 := (I.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have e' : I'.ev 1 0 = 1 := (I'.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have k := key m hm 1 one_pos 0 v v' s hv
    rw [e, e'] at k
    obtain ⟨-, -, a₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I.ev (m ^ 2)) (tateIso_ev_pow I (pow_pos hm.pos 2))
    obtain ⟨-, -, b₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) o'.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I'.ev (m ^ 2)) (tateIso_ev_pow I' (pow_pos hm.pos 2))
    exact (a₃ v).2 (k ((b₃ v').1 Q))

end GlobalTheory.DescendIso

end
end
