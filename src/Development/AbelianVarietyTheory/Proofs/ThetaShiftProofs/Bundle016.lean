module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Forms

variable (O : Type) [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X] {U U' : Type} [CommGroup U]
  [CommGroup U']

structure IsScalarForm (t : X → X → U) : Prop where
  add_right : ∀ y x x', t y (x + x') = t y x * t y x'
  symm : ∀ y x, t y x = t x y
  bal : ∀ (a : O) y x, t (a • y) x = t y (star a • x)

variable {O}

namespace IsScalarForm

variable {t s : X → X → U} (ht : IsScalarForm O t)
include ht

theorem add_left (y y' x : X) : t (y + y') x = t y x * t y' x := by
  rw [ht.symm, ht.add_right, ht.symm x, ht.symm x]

theorem zero_right (y : X) : t y 0 = 1 := by
  have := ht.add_right y 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem neg_right (y x : X) : t y (-x) = (t y x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ht.add_right, neg_add_cancel, ht.zero_right]

theorem neg_left (y x : X) : t (-y) x = (t y x)⁻¹ := by rw [ht.symm, ht.neg_right, ht.symm]

theorem nsmul_right (n : ℕ) (y x : X) : t y (n • x) = t y x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, ht.zero_right]
  | succ n ih => rw [succ_nsmul, pow_succ, ht.add_right, ih]

theorem nsmul_left (n : ℕ) (y x : X) : t (n • y) x = t y x ^ n := by rw [ht.symm, ht.nsmul_right, ht.symm]

theorem map (f : U →* U') : IsScalarForm O fun y x => f (t y x) :=
  ⟨fun y x x' => by rw [ht.add_right, map_mul], fun y x => by rw [ht.symm], fun a y x => by rw [ht.bal]⟩

theorem inv : IsScalarForm O fun y x => (t y x)⁻¹ := ht.map invMonoidHom

theorem pow (n : ℕ) : IsScalarForm O fun y x => t y x ^ n := ht.map (powMonoidHom n)

theorem mem_balForms : Forms.bilOfMul t ht.add_left ht.add_right ∈ Forms.balForms ℤ O X (Additive U) :=
  ⟨ht.symm, ht.bal⟩

theorem refine_add {w : O} (hw : w + star w = 1) (a b : X) :
    t (a + b) (w • (a + b)) = t a (w • a) * t b (w • b) * t a b := by
  have h : t a (w • b) * t b (w • a) = t a b := by
    rw [ht.symm b, ht.bal, ← ht.add_right, ← add_smul, hw, one_smul]
  rw [smul_add, ht.add_left, ht.add_right, ht.add_right, ← h]
  ac_rfl

theorem refine_neg (w : O) (a : X) : t (-a) (w • -a) = t a (w • a) := by
  rw [smul_neg, ht.neg_left, ht.neg_right, inv_inv]

end IsScalarForm

end Forms

section Constants

variable {A A' : Type} [CommRing A] [CommRing A'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K]
  [Fintype K']

def unitAt (q : Z ⟶ Sp A) (z : Z) : Aˣ →* (Z.presheaf.stalk z)ˣ :=
  (gm q z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem unitAt_apply (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : unitAt q z u = gm q z ⊤ (unitOn u) := rfl

theorem unitAt_val (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : (unitAt q z u).val = gs q z ⊤ (unitOn u).val :=
  (gs_unit q z ⊤ trivial (unitOn u)).symm

theorem unitAt_spMap (q : Z ⟶ Sp A') (f : A →+* A') (z : Z) (u : Aˣ) :
    unitAt (q ≫ spMap f) z u = unitAt q z (Units.map f.toMonoidHom u) := by
  refine (gm_pull q (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm q z ⊤) (Units.ext ?_))
  exact (congrArg (fun e => e.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem unitAt_injective {F : Type} [Field F] (y : Sp F) : Function.Injective (unitAt (𝟙 (Sp F)) y) :=
  fun u v h => (stalkUnits y).injective ((gm_unitOn y u).symm.trans (h.trans (gm_unitOn y v)))

theorem val_scale {φ : K → (Sp A ⟶ X)} {ε : K → ℤ} (u : Aˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Sp A) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (scaleGen (unitOn u) t) r z J = unitAt r z u * val t r z J :=
  val_scaleGen _ t r hJ

theorem val_powGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) : val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

end Constants

variable {R : Type} [CommRing R] [IsDomain R]

abbrev PsiFam (D : DegPre R) : Type :=
  ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))

@[reducible] def withPsi (D : DegPre R) (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) : DegPre R :=
  { D with psi := ψ, psi_gen := hψ }

@[reducible] def rescale (D : DegPre R) (q : D.X → (FractionRing R)ˣ) : DegPre R :=
  withPsi D (fun χ => scaleGen (unitOn (q χ)) (D.psi χ)) fun χ => scaleGen_isGen _ _ (D.psi_gen χ)

variable {O : Type} [CommRing O] [StarRing O]

@[reducible] def twist (D : DegPre R) [Module O D.X] (w : O) (t : D.X → D.X → (FractionRing R)ˣ) : DegPre R :=
  rescale D fun y => t y (w • y)

variable {D : DegPre R}

theorem val_tau (D : DegPre R) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) r z J = val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ *
      (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (q : D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((rescale D q).psi a) r z J = unitAt r z (q a) * val (D.psi a) r z J :=
  val_scale (q a) (D.psi a) r hJ

theorem val_tau_rescale (q : D.X → (FractionRing R)ˣ) {a b : D.X} {x : (FractionRing R)ˣ}
    (hx : q (a + b) = q a * q b * x) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((rescale D q).tau a b) r z J = unitAt r z x * val (D.tau a b) r z J := by
  have e := val_tau (rescale D q) a b r hJ
  have e₁ := val_psi_rescale q (a + b) r hJ
  have e₂ := val_psi_rescale q a r hJ
  have e₃ := val_psi_rescale q b r hJ
  have e₄ := val_tau D a b r hJ
  rw [hx, map_mul, map_mul] at e₁
  have e₅ : val (rescale D q).rigK r z J = val D.rigK r z J := rfl
  rw [e₁, e₂, e₃, e₅] at e
  rw [e, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Twist

variable [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ}

theorem val_psi_twist (w : O) (t : D.X → D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left)
    {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).psi a) r z J = unitAt r z (t a (w • a)) * val (D.psi a) r z J :=
  val_psi_rescale (fun y => t y (w • y)) a r hJ

variable (hw : w + star w = 1) (ht : IsScalarForm O t)
include ht

theorem psiEven_twist (w : O) (h : D.PsiEven) : (twist D w t).PsiEven := fun χ =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (h χ) (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_psi_twist w t (-χ) _ hJ) rfl).trans
      (Eq.trans ?_ (val_psi_twist w t χ _ hJ).symm))
    rw [ht.refine_neg, ← e, _root_.mul_assoc]

include hw

theorem val_tau_twist (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).tau a b) r z J = unitAt r z (t a b) * val (D.tau a b) r z J :=
  val_tau_rescale (fun y => t y (w • y)) (ht.refine_add hw a b) r hJ

theorem tauBimult_twist (h : D.TauBimult) : (twist D w t).TauBimult := fun a a' b =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a + a') b _ hJ) rfl).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_tau_twist hw ht a b _ hJ)
        (val_tau_twist hw ht a' b _ hJ))).symm))
    rw [ht.add_left, map_mul, _root_.mul_mul_mul_comm, ← e, _root_.mul_assoc]
    rfl

def twistAct (oa : D.OAct O) : (twist D w t).OAct O where
  onB := oa.onB
  c_lin := oa.c_lin
  tau_bal a u hu u₀ x x' := corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal a u hu u₀ x x') (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a • x) x' _ hJ) rfl).trans
      (Eq.trans ?_ (val_tau_twist hw ht x (star a • x') _ hJ).symm))
    rw [ht.bal, ← e, _root_.mul_assoc]
    rfl

theorem psi_weight_zero_twist {oa : D.OAct O} (h : TraceFormTwistIso D oa w) : TraceFormTwistIso (twist D w t) (twistAct hw ht oa) w := by
  obtain ⟨u, hu, u₀, h⟩ := h
  refine ⟨u, hu, u₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h x) (𝟙 _)).trans (val_mul hJ _ _ _))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht x (w • x) _ hJ) rfl).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_psi_twist w t x _ hJ) rfl)).symm))
  rw [_root_.mul_assoc, _root_.mul_assoc]
  exact congrArg _ e


end Twist

end GlobalTheory.TauTwist
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpanFrame

open GlobalTheory.AmpleSpan

theorem secScal_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (a : ℤ)
    {T T' : Over S} (k : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (k ▷ A) (whiskerRight_snd k A) s s') :
    GeneratorPullback.SecScal L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) s' (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s
      (k ▷ A).left 1 := by
  have e : (k ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  apply (secScal_const_iff hL e).2
  intro i Z r z hz
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
  have le := chart_le_res A L (k ▷ A) (whiskerRight_snd k A) a (fun _ => i)
  refine Eq.symm ((congrArg (gs r z _) (H fun _ => i)).trans ?_)
  exact (gs_res r z le hm _).trans (gs_pull r (k ▷ A).left z _ (le (x := r z) hm) _)

theorem valR_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}
    {ε' : K' → ℤ} {χ : Y ⟶ X} {χ' : Y' ⟶ X} {h : Y' ⟶ Y} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)}
    (H : GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1) {R : Type} [CommRing R] (x : Sp R ⟶ Y') (j : L.ι)
    (hx : ⊤ ≤ (x ≫ χ') ⁻¹ᵁ L.U j) :
    valR (x ≫ h) (LB.wchart L (fun _ : K => χ) (fun _ => j)) (s.f fun _ => j) =
      valR x (LB.wchart L (fun _ : K' => χ') (fun _ => j)) (s'.f fun _ => j) := by
  subst e
  have E := H (fun _ => j) (fun _ => j) (by rintro (a | a) (b | b) _ <;> rfl)
  have hm : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K' => h ≫ χ) (fun _ => j) ⊓ LB.wchart L (fun _ : K => h ≫ χ) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hx hz, Set.mem_iInter.2 fun _ => hx hz⟩
  have E' := congrArg (valR x _) E
  rw [HolHom.valR_res _ _ _ hm, resTop, map_one, one_mul] at E'
  exact (HolHom.valR_comp _ _ _ _).trans (E'.trans (HolHom.valR_res _ _ _ hm))

theorem exists_span_powOver (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ}
    (hN : 1 ≤ N) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ (m : ℕ) (b : Fin m → LB.Sec (powOver P.A P.L U N)), ∀ (X' Y' : Scheme.{0}) [IsAffine Y']
      (h : X' ⟶ (P.A.hom ⁻¹ᵁ U).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ U.toScheme), IsPullback h f' (P.A.hom ∣_ U) g →
      ∀ (K : Type) [Fintype K] (ε : K → ℤ) (φ : X' ⟶ P.A.left), h ≫ (P.A.hom ⁻¹ᵁ U).ι = φ → ∑ k, ε k = N →
      ∀ b' : Fin m → LB.Sec (LB.LinComb P.L (fun _ : K => φ) ε),
        (∀ i, GeneratorPullback.SecScal P.L _ _ (b' i) (fun _ : Fin N => (P.A.hom ⁻¹ᵁ U).ι) (fun _ => 1) (b i) h 1) →
        ∀ s, InSpan f' b' s := by
  obtain ⟨m, b₀, hb₀⟩ := exists_sections_span_affine hS S P N hN U hU
  obtain ⟨h₀, e₀, -, -, hE⟩ := translate_powOver_LPow P.A P.isLB N (U := U) (overRes (T := baseOver S) U)
    (𝟙 U.toScheme) (by simp)
  obtain ⟨E, hE⟩ := hE (IsIso.id _)
  refine ⟨m + 1, fun i => E.symm (b₀ i), fun X' Y' _ h f' g sq K _ ε φ e hε b' hb' s => ?_⟩
  let T' : Over S := Over.mk (g ≫ U.ι)
  have : IsAffine T'.left := ‹IsAffine Y'›
  let k : T' ⟶ overRes (T := baseOver S) U := Over.homMk g (by simp [T'])
  obtain ⟨h', e', sq', -, -⟩ := translate_powOver_LPow P.A P.isLB N (U := U) T' g rfl
  let b'' : Fin (m + 1) → LB.Sec (LPow P.A P.L N T') := fun i =>
    SecM.toSec P.A (SecAff.pull P.A P.L N k (SecM.ofSec P.A (b₀ i)))
  have hb'' : ∀ i, IsPullSec P.A P.L N (k ▷ P.A) (whiskerRight_snd k P.A) (b₀ i) (b'' i) := fun i =>
    (SecAff.isPullSec_iff P.A P.L N _ _ _).2 rfl
  have hsp := hb₀ T' k b'' hb''
  let θ := sq.isoIsPullback _ _ sq'
  have θ₁ : θ.hom ≫ h' = h := sq.isoIsPullback_hom_fst _ _ sq'
  have θ₂ : θ.hom ≫ (fst T' P.A).left = f' := sq.isoIsPullback_hom_snd _ _ sq'
  have θ₃ : θ.hom ≫ (snd T' P.A).left = φ := by rw [← e', ← Category.assoc, θ₁, e]
  obtain ⟨F, hF⟩ := exists_equiv_secScal P.isLB (h := θ.hom) (formEq_const (K := Fin 1) (K' := K)
    (ε := fun _ => (N : ℤ)) (ε' := ε) θ₃ (by simp [hε]))
  have θ₄ : θ.hom ≫ (k ▷ P.A).left ≫ h₀ = h := by
    rw [← cancel_mono (P.A.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, e₀, ← Over.comp_left, whiskerRight_snd, θ₃, e]
  refine InSpan.secScal P.isLB (h := θ.hom) (f := (fst T' P.A).left) (g := 𝟙 Y') (θ₂.trans (Category.comp_id _).symm)
    (t := b'') (s := F.symm s) ((inSpan_iff_mem_span P.A b'' _).2 (by rw [hsp]; trivial)) (fun i => ?_)
    ((hF _ _).2 (F.apply_symm_apply s))
  apply (secScal_iff_sval P.isLB).2
  intro Z r z J hJ
  rw [← SectionScalarValuation.secScal_sval (hb' i) r z hJ, ← SectionScalarValuation.secScal_sval (secScal_of_isPullSec P.A P.isLB N k (hb'' i)) _ z hJ,
    ← SectionScalarValuation.secScal_sval ((hE _ _).2 (E.apply_symm_apply (b₀ i))) _ z hJ, Category.assoc, Category.assoc, θ₄]

end GlobalTheory.SpanFrame
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have face (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J 1 x x' = 1 := by
    have q := val_corr hJ (D₀.cub.face 0) (lift x x').left
    rw [val_one] at q
    refine (Eq.trans ?_ (val_cub D₀.cub (lift x x') hJ (pzero D₀.P.A _) (x2 D₀.P.A 0) (x2 D₀.P.A 1)).symm).trans q
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have swap01 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x' x w := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_first (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have swap12 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x w x' := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_last (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have face3 (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' 1 = 1 :=
    (swap12 _ _ _).trans ((swap01 _ _ _).trans (face _ _))
  rw [hb1] at e
  change cv g χ y J * cubV D₀.cub y J (DVR.cP D₀ T χ) 1 1 = _ at e
  rw [face3, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
end
end
