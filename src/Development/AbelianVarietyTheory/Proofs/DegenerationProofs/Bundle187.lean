module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitOverOfHasArcData
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Ideal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.LabelsAllLevels

section Values
variable {O : Type} [CommRing O] {N N' : NumD O}

def lower {k m : ℕ} (p : N.QT (k * m)) : N.QT k :=
  ⟨(p.1.1, p.1.2 ^ m), (pow_mul' _ k m).symm.trans p.2⟩

private theorem twist_theta' {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).θ = N.θ := rfl

private theorem twist_c {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).c = N.c := rfl

theorem qEq_twist {j k m : ℕ} (β : N.Form j) {u r r' : Oˣ} (h₁ : r' ^ m = r) (h₂ : r ^ k = u)
    {q' : N.QT (k * m)} {q : N.QT k} {p' : (N.twist β u).QT (k * m)} {p : (N.twist β u).QT k}
    (t' : TwRel β u r' q' p') (t : TwRel β u r q p) (e : N.QEq (lower q') q) :
    (N.twist β u).QEq (lower p') p := by
  obtain ⟨z, hy, hg⟩ := e
  obtain ⟨ty', tb', ts'⟩ := t'
  obtain ⟨ty, tb, ts⟩ := t
  refine ⟨z, ?_, ?_⟩
  · have e1 : (lower p').1.1 = (lower q').1.1 := ty'
    rw [ty, e1]
    exact hy
  · show p.1.2 = p'.1.2 ^ m * (N.twist β u).io z
    have hg' : q.1.2 = q'.1.2 ^ m * N.io z := hg
    apply NumD.Gt.ext
    · rw [tb, hg', NumD.Gt.mul_b, NumD.Gt.mul_b, NumD.Gt.pow_b, NumD.Gt.pow_b, tb', NumD.io_b]
      rfl
    · refine funext fun (χ : N.X) => ?_
      have A1 := ts χ
      have A2 := NumD.Gt.mul_s (q'.1.2 ^ m) (N.io z) χ
      rw [NumD.io_s, NumD.io_b, ← hg'] at A2
      have A3 := NumD.Gt.pow_s q'.1.2 m χ
      have A4 : (p'.1.2 ^ m).s χ * cubN N.θ m 1 q'.1.2.b (N.c χ) = p'.1.2.s χ ^ m := by
        have A4' := NumD.Gt.pow_s p'.1.2 m χ
        rw [tb'] at A4'
        exact A4'
      have Bq : (p'.1.2 ^ m).b = (q'.1.2 ^ m).b := by
        rw [NumD.Gt.pow_b, NumD.Gt.pow_b, tb'] <;> rfl
      have A5 := ts' χ
      have A6 := N.twist_τ β u z χ
      have hy' : β.be q.1.1.toAdd χ = β.be q'.1.1.toAdd χ + k * β.be z χ := by
        rw [show q.1.1.toAdd = q'.1.1.toAdd + k • z from hy, map_add (f := _), map_nsmul, LinearMap.add_apply,
          LinearMap.smul_apply, nsmul_eq_mul]
      rw [hy'] at A1
      rw [NumD.Gt.mul_s (p'.1.2 ^ m) ((N.twist β u).io z) χ, NumD.io_s (N.twist β u) z χ,
        NumD.io_b (N.twist β u) z, Bq, twist_theta' β u, twist_c β u, A6]
      subst h₁ h₂
      apply Additive.ofMul.injective
      replace A1 := congrArg Additive.ofMul A1
      replace A2 := congrArg Additive.ofMul A2
      replace A3 := congrArg Additive.ofMul A3
      replace A4 := congrArg Additive.ofMul A4
      replace A5 := congrArg Additive.ofMul A5
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_pow] at A1 A2 A3 A4 A5 ⊢
      rw [A1, A2, eq_sub_of_add_eq A3, eq_sub_of_add_eq A4, A5]
      clear hy hg hg' hy' ty ty' tb tb' ts ts' A6 A1 A2 A3 A4 A5
      module

theorem exists_image (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hid (u : Oˣ) : (Units.map (RingHom.id O).toMonoidHom) u = u := by
    ext
    rfl
  let g : N'.Gt :=
    ⟨I.φ p.1.2.b, fun χ => p.1.2.s (I.e.symm χ) * I.h (N.c (I.e.symm χ)) * I.h p.1.2.b / I.h (N.c (I.e.symm χ) * p.1.2.b),
      fun χ χ' => by
        obtain ⟨χ, rfl⟩ := I.e.surjective χ
        obtain ⟨χ', rfl⟩ := I.e.surjective χ'
        rw [← map_add (f := _)]
        simp only [AddEquiv.symm_apply_apply]
        rw [I.c_eq, I.c_eq, N.c_add]
        have a := I.θ_eq (N.c χ) (N.c χ') p.1.2.b
        simp only [hid] at a
        have b := p.1.2.mult χ χ'
        apply Additive.ofMul.injective
        replace a := congrArg Additive.ofMul a
        replace b := congrArg Additive.ofMul b
        simp only [ofMul_mul, ofMul_div] at a b ⊢
        linear_combination (norm := abel) a + b⟩
  have hg : I.Rel p.1.2 g := ⟨rfl, fun χ => by simp only [g, AddEquiv.symm_apply_apply, div_mul_cancel, hid]⟩
  have h1 : I.Rel (p.1.2 ^ k) (g ^ k) := hg.pow k
  rw [N.mem_QT.1 p.2] at h1
  have h2 := I.rel_io p.1.1.toAdd
  have h3 : g ^ k = N'.io (J.e p.1.1.toAdd) :=
    NumD.Gt.ext (h1.1.trans h2.1.symm) (funext fun χ => by
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      exact mul_right_cancel ((h1.2 χ).trans (h2.2 χ).symm))
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), N'.mem_QT.2 h3⟩, rfl,
    (NumD.Hom.ofIso_rel J _ _).1 hg⟩

theorem qEq_image (J : NumD.Iso N N') {k m : ℕ} {p' : N.QT (k * m)} {p : N.QT k} {q' : N'.QT (k * m)} {q : N'.QT k}
    (a' : q'.1.1.toAdd = J.e p'.1.1.toAdd) (b' : J.Rel p'.1.2 q'.1.2) (a : q.1.1.toAdd = J.e p.1.1.toAdd)
    (b : J.Rel p.1.2 q.1.2) (e : N.QEq (lower p') p) : N'.QEq (lower q') q := by
  obtain ⟨z, hy, hg⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, ?_, ?_⟩
  · show q.1.1.toAdd = q'.1.1.toAdd + k • J.e z
    have hy' : p.1.1.toAdd = p'.1.1.toAdd + k • z := hy
    rw [a, a', hy', map_add (f := _), map_nsmul]
  · show q.1.2 = q'.1.2 ^ m * N'.io (J.e z)
    have hg' : p.1.2 = p'.1.2 ^ m * N.io z := hg
    have r1 : I.Rel p.1.2 q.1.2 := (NumD.Hom.ofIso_rel J _ _).2 b
    have r2 : I.Rel p.1.2 (q'.1.2 ^ m * N'.io (J.e z)) := by
      rw [hg']
      have rb : I.Rel p'.1.2 q'.1.2 := (NumD.Hom.ofIso_rel J _ _).2 b'
      exact (rb.pow m).mul (I.rel_io z)
    apply NumD.Gt.ext (r1.1.trans r2.1.symm)
    refine funext fun χ => ?_
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    exact mul_right_cancel ((r1.2 χ).trans (r2.2 χ).symm)

private theorem pow_left_of_isGrpPullback' {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (z : Over.mk (T.hom ≫ f) ⟶ G) (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero =>
    let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w])
    have ho : o * o = o := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 o o rfl rfl, _root_.mul_one]
      rfl
    have h1 : o = 1 := mul_left_cancel (a := o) (by rw [_root_.mul_one]; exact ho)
    rw [pow_zero, pow_zero, ← h1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih e
end Values

theorem pow_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x : baseOver S' ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  let w : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') (by simp)
  have h1 : (w ≫ z).left = x.left ≫ φ := by
    rw [Over.comp_left, e]
    simp [w]
  have h2 := pow_left_of_isGrpPullback' h x (w ≫ z) h1 n
  rw [← comp_pow, Over.comp_left] at h2
  simpa [w] using h2

theorem labels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  intro hL hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hR _ hT h4 k hk
  intro x p q' p' z hTw hqy hqg hQ hz
  have hK : 0 < k * 4 := by omega
  obtain ⟨p₁, hp₁, -⟩ := existsUnique_twRel A.be u (r (k * 4)) (hR.pow hK) (A.q (k * 4) x)
  obtain ⟨q₁, hq₁y, hq₁g⟩ := exists_image J p₁
  obtain ⟨-, -, -, -, hQk⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨p₁', hp₁'⟩ := (hQk (k * 4)).2.1 q₁
  have hw : ((o.I.ev (k * 4) x).left ≫ M.φ) ≫ M.P.A.A.hom = (Out.TFK (R := M.W) C).hom := by
    rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
    simp
  let z₁ : Out.TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev (k * 4) x).left ≫ M.φ) hw
  have t₁ : M.P.ToA C (k * 4) p₁' z₁ := h4 (k * 4) (by omega) x p₁ q₁ p₁' z₁ hp₁ hq₁y hq₁g hp₁' rfl
  obtain ⟨p₂, hp₂⟩ := (hQk k).2.1 (lower q₁)
  have hy₂ : p₂.y = p₁'.y := hp₂.1.symm.trans hp₁'.1
  have hn₂ : GtPtF.IsNsmul 4 p₁'.g p₂.g := (GtValues.isNsmul_val ν' 4 hp₁'.2 hp₂.2).2 rfl
  haveI := M.admissible_base_of_complete_dvr.2
  have t₂ : M.P.ToA C k p₂ (z₁ ^ 4) :=
    (GlobalTheory.LevelCompat.qkToAkU_level hL M.W (IsLocalRing.maximalIdeal M.W) M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi
      M.P.U C k 4 (k * 4) hk (by norm_num) rfl p₂ p₁' z₁).2 hy₂ hn₂ t₁
  obtain ⟨hgA, -, -, -, hQA⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₀, hq₀y, hq₀n, hq₀e⟩ := A.I.tower k 4 hk (by norm_num) x
  have hqA := A.hq (k * 4) x
  obtain ⟨c₀, hc₀, -⟩ := hgA q₀.g
  have hc : c₀ = (A.q (k * 4) x).1.2 ^ 4 := (GtValues.isNsmul_val A.ν 4 hqA.2 hc₀).1 hq₀n
  have hQP : A.ν.QPt q₀ (lower (A.q (k * 4) x)) := by
    refine ⟨hqA.1.trans hq₀y.symm, ?_⟩
    show A.ν.Pt q₀.g ((A.q (k * 4) x).1.2 ^ 4)
    rw [← hc]
    exact hc₀
  have hE1 : A.N.QEq (lower (A.q (k * 4) x)) (A.q k x) :=
    ((hQA k).2.2 q₀ (A.I.ev k x) _ _ hQP (A.hq k x)).1 hq₀e
  have hE0 := qEq_twist A.be (hR.2 k 4 hk (by norm_num)) (hR.pow hk) hp₁ hTw hE1
  have hE : Out.QkPt.Equiv M.P.D.toPre C p₂ p' :=
    ((hQk k).2.2 p₂ p' _ _ hp₂ hQ).2 (qEq_image J hq₁y hq₁g hqy hqg hE0)
  obtain ⟨F, hF1, -, hF3, -, -, -⟩ := hT C k hk
  have e3 : z = z₁ ^ 4 := by
    apply Over.OverMorphism.ext
    rw [hz, pow_left M.cart (o.I.ev (k * 4) x) z₁ rfl 4, o.I.tower k 4 hk (by norm_num) x]
  exact (hF1 p' z).2 (e3.trans (((hF1 p₂ _).1 t₂).trans ((hF3 p₂ p').2 hE)))

end GlobalTheory.Ex.LabelsAllLevels
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem polAt_of_point {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem admissible_maximal_ideal_of_complete_dvr_char_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) :
    admitted V (IsLocalRing.maximalIdeal V) ∧ IsPrincipalIdealRing (V ⧸ IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  exact ⟨⟨⟨inferInstance, inferInstance, inferInstance, h₂⟩, h₂, h₃, inferInstance, inferInstance⟩, inferInstance⟩

theorem cdvr_powerSeries (K : Type) [Field K] [CharZero K] : CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

theorem powerSeries_dvr_admissible_X_ideal (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal O) O) :
    admitted (PowerSeries O) (Ideal.span {PowerSeries.X}) ∧
      IsPrincipalIdealRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) := by
  have hk : Ideal.span {(PowerSeries.X : PowerSeries O)} = RingHom.ker (PowerSeries.constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) ≃+* O :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
  refine ⟨⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := O)), hk ▸ RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv e.symm⟩, IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective⟩
  infer_instance

theorem hasArcData_trait (h₁ : Laws) (h₂ : Laws2) (h₃ : Laws3) (h₄ : Laws4) (h₅ : Laws5) (h₆ : Laws6) (hE : Ega)
    (hU : USt) (hP : PelSt) (hH : HomExtSt) {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    {b : c.V W₀ →+* O'} (a : ArcIn D l (c.V W₀).subtype O' b) (hp : PushInvertible Y.t.G Y.t.PP.L)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X) (hχ : jK _ ≫ χ = y ≫ Y.j)
    (hT : TraitData Y a (RingHom.id _) y) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (φ : PowerSeries O' →+* V) (hφ : Function.Injective φ) (hX : ¬ IsUnit (φ PowerSeries.X))
    (hC : ∀ x, x ≠ 0 → IsUnit (φ (PowerSeries.C x))) :
    Y.HasArcData a (IsLocalRing.maximalIdeal V) (φ.comp (PowerSeries.C (R := O'))) (φ PowerSeries.X) (spMap φ ≫ χ) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp φ) := (IsFractionRing.injective V _).comp hφ
  let gam : FractionRing (PowerSeries O') →+* FractionRing V := IsFractionRing.lift hinj
  have hg : ∀ r, gam (algebraMap _ _ r) = algebraMap V _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ y ≫ Y.j = jK V ≫ spMap φ ≫ χ := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hg r
  obtain ⟨W, _, _, _, io, hW, hio, hfin, hA⟩ := (hT.2 V hV φ gam hg _ hsq).2 hX
  have hA' : Y.HasArcData a (IsLocalRing.maximalIdeal W) (io.comp (φ.comp (PowerSeries.C (R := O'))))
    (io (φ PowerSeries.X)) (spMap io ≫ spMap φ ≫ χ) := hA
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap φ ≫ χ) Y.t
  have hsq' : (spMap gam ≫ y) ≫ Y.j = jK V ≫ spMap φ ≫ χ := (Category.assoc _ _ _).trans hsq
  have hS := GlobalTheory.T.closedFibre_split_of_arcData_finite_extension h₁ h₂ h₃ h₄ h₅ h₆ E H D l Xo c W₀ Y O' b a V hV _ _ hC hX _ _ hsq' t m W hW io hio hfin hA'
  obtain ⟨hadm, hpid⟩ := admissible_maximal_ideal_of_complete_dvr_char_zero hV
  obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H V _ hadm hpid t (polAt_of_point Y m _ _ hsq') hS
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp V _ t m)
  have := hV.2.2
  have hloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  exact GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a V _ _ _ hadm.1
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (hφ.comp PowerSeries.C_injective) _ _ hsq' t m P hPt W hW io hio
    (IsLocalRing.map_maximalIdeal_le io) (fun h => hX (isUnit_of_map_unit io _ h)) (fun x hx => (hC x hx).map io) hA'

theorem hasArcData_of_traitData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb hp y χ hχ hT
  rcases hb with ⟨hf, -⟩ | ⟨hd, hϖ, hc⟩
  · letI := hf.toField
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT (cdvr_powerSeries O') (RingHom.id _)
      Function.injective_id PowerSeries.X_prime.not_unit (fun x hx => (IsUnit.mk0 x hx).map (PowerSeries.C (R := O')))
    have e : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp, PowerSeries.maximalIdeal_eq_span_X] at h
    exact h
  · have hi := IsFractionRing.injective O' (FractionRing O')
    have hX : ¬ IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) PowerSeries.X) := by
      rw [PowerSeries.map_X]
      exact PowerSeries.X_prime.not_unit
    have hC : ∀ x, x ≠ 0 → IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) (PowerSeries.C x)) := fun x hx => by
      rw [PowerSeries.map_C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 hx)).map _
    have hV := cdvr_powerSeries (FractionRing O')
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT hV _
      (PowerSeries.map_injective _ hi) hX hC
    obtain ⟨t, ⟨m⟩⟩ := exists_sab χ Y.t
    have hS := GlobalTheory.splitOver_of_hasArcData h₁ h₂ h₃ hH E H D l Xo c W₀ Y O' b a hd χ t m (by
      have e : (PowerSeries.map (algebraMap O' (FractionRing O'))).comp (PowerSeries.C (R := O')) =
          (PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _) := RingHom.ext fun x => PowerSeries.map_C (algebraMap O' (FractionRing O')) x
      rw [e, PowerSeries.map_X] at h
      exact h)
    obtain ⟨hadm, hpid⟩ := powerSeries_dvr_admissible_X_ideal O' (hϖ.maximalIdeal_eq ▸ hc)
    obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H _ _ hadm hpid t (polAt_of_point Y m _ _ hχ.symm) hS
      (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp _ _ t m)
    have := hadm.2.2.1
    refine GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a _ _ _ _ hadm.1 hadm.2.2.2.1.ne_top
      PowerSeries.C_injective _ _ hχ.symm t m P hPt _ hV _ (PowerSeries.map_injective _ hi) ?_ hX hC h
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hX

end GlobalTheory.ArcData
end
end
