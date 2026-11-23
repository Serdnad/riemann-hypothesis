module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle138
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle140
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait.LevelClause

theorem qEq_twist {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {u r : Oˣ} {j : ℕ} (h : r ^ j = u)
    {p q : N.QT j} {p' q' : (N.twist β u).QT j} (e : N.QEq p q) (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩
  · rw [hp.1, hq.1]; exact h1
  · rw [hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]; rfl
  · have e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ := N.twist_τ β u z χ
    have e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ := by
      rw [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul,
        zpow_natCast, h]
    have e₃ : (p'.1.2 * (N.twist β u).io z).s χ =
        p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z) := rfl
    refine (hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)
    rw [h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem exists_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩
  have a := (I.rel_img p.1.2).pow k
  rw [hp] at a
  exact (I.rel_existsUnique _).unique a (I.rel_io _)

theorem qEq_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (e : N.QEq p q) (hp : p'.1.1.toAdd = J.e p.1.1.toAdd) (hp' : J.Rel p.1.2 p'.1.2)
    (hq : q'.1.1.toAdd = J.e q.1.1.toAdd) (hq' : J.Rel q.1.2 q'.1.2) : N'.QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, by rw [hq, hp, h1, map_add (f := _), map_nsmul], ?_⟩
  have a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z)) := NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)
  rw [← h2] at a
  exact (I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a

theorem genRel_of_gauge {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (ht₀ : t₀.IsGen) (x : F) (hpt : ∀ k, pt k ≫ φ = pt₀ k)
    (J : (Sp F ⟶ B₀) → M₀.ι) (J' : (Sp F ⟶ B) → M.ι) (gJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M₀.U (J ψ)) (gJ' : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M.U (J' ψ))
    (hv : (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) * vF t (𝟙 _) J' = x * vF t₀ (𝟙 _) J) :
    GenRel w t t₀ x := by
  obtain rfl : pt₀ = fun k => pt k ≫ φ := funext fun k => (hpt k).symm
  have z : Sp F := (default : PrimeSpectrum F)
  rw [genRel_iff w t t₀ x z]
  refine ⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩
  have hJ := fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)
  have hJ' := fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)
  have hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ _
  have hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k)) := Set.mem_iInter.2 fun k => hJ' _
  have P1 := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'
  have G1 := gen_trans ht (𝟙 _) z hq hq'
  have G0 := gen_trans ht₀ (𝟙 _) z hp hp'
  have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) =
      (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val := fun k =>
    toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _
  have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) =
      (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val := by
    simp only [pw, Category.id_comp]
    rw [map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0 := fun h0 => by
      have := a₃ k
      rw [h0, map_zero] at this
      exact Units.ne_zero _ this.symm
    have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _ := Units.ext (a₃ k)
    rw [← e, ← map_zpow]
    show _ = toStk z _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e' := congrArg (toStk z) hv
  rw [map_mul, map_mul, a₄] at e'
  have b₁ : toStk z (vF t (𝟙 _) J') = _ := toStk_valF _ _ z hq' _
  have b₀ : toStk z (vF t₀ (𝟙 _) J) = _ := toStk_valF _ _ z hp' _
  rw [b₁, b₀, ← Units.val_mul] at e'
  have hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j := by
    simp only [pw, Category.id_comp]
  have step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d) := fun a b c d => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]
  exact mul_left_comm _ _ _

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) (b : N.A) (χ : N.X) (i : Fin 4) :
    DegPre.gtφ D F (ν.eA b) (ν.eX χ) i = (ν.eA (![N.c χ * b, N.c χ, b, 1] i)).left := by
  fin_cases i
  · show _ = (ν.eA (N.c χ * b)).left
    rw [map_mul, ν.c_eq]; rfl
  · show _ = (ν.eA (N.c χ)).left
    rw [ν.c_eq]; rfl
  · rfl
  · show _ = (ν.eA 1).left
    rw [map_one]; rfl

theorem level_clause : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  intro _ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz
  obtain ⟨-, hw, hA, hX, hne, hh⟩ := hF
  have hrk := hr.pow hk
  obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C)
    (RingHom.ext fun _ => rfl) p₀
  obtain ⟨-, -, -, -, B₀⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B₁⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨v₀, hv₀, -⟩ := (B₀ k).1 q₀
  have e₀ := ((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_twRel A.be u (r k) hrk v₀
  obtain ⟨t₁, ht₁, -⟩ := existsUnique_twRel A.be u (r k) hrk (A.q k v)
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_image J t₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_image J t₁
  obtain ⟨q, hq⟩ := (B₁ k).2.1 s₀
  obtain ⟨p', hp'⟩ := (B₁ k).2.1 s₁
  have e₁ := ((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')
  refine ⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩
  · rw [← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]
    rfl
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective χ
    have hb : q.g.b = ν'.eA (J.φ v₀.1.2.b) := by rw [← hq.2.1, hs₀'.1, ht₀.2.1]
    have hc : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
    have g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i =
        (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left := fun i => by
      rw [hb, hX, gtφ_eq, hc]
      fin_cases i
      · exact congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm
      · rfl
      · rfl
      · exact congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm
    refine genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_
    · rw [g₁, hA, ← hv₀.2.1, gtφ_eq]
    · have g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _
          (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ),
            ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val =
          wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i)) := fun i =>
        congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)
      have g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C) :=
        (congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm
      have g₄ := (hv₀.2.2 χ).symm
      have g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ) := by
        rw [← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
          mul_comm, A.be.div_mul hkM]
      have g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) =
          v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b := by
        have := hs₀'.2 χ
        rw [ht₀.2.1, ht₀.2.2] at this
        exact this
      have g₇ := congrArg Units.val g₆
      simp only [Units.val_mul] at g₇
      refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)
      rw [Fin.prod_univ_four]
      have alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W →
          w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ →
          w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀ := by
        intro S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄
        subst a₃
        simp only [zpow_neg, zpow_one]
        field_simp
        refine mul_left_cancel₀ nW ?_
        linear_combination (-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ +
          (S₀ * ρ * w₀ * w₃) * a₂
      exact alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _)
        (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇
  · obtain ⟨g, hg, -, hge, -⟩ := hTI C k hk
    exact (hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)

end GlobalTheory.Ex.Trait.LevelClause
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem existsUnique_smul_of_basis {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton κ]
    (c : Module.Basis κ R M) (k : κ) (s : M) : ∃! r : R, s = r • c k := by
  have := uniqueOfSubsingleton k
  obtain rfl : k = default := Subsingleton.elim _ _
  refine ⟨c.repr s default, ?_, fun r hr => ?_⟩
  · have e := c.sum_repr s
    rw [Fintype.sum_unique] at e
    exact e.symm
  · rw [hr]; simp

theorem exists_univBasis_field (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    (y : Sp K ⟶ S) : ∃ b : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk y), ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ Over.mk y)
      (s : SecM P.A P.L ((1 : ℕ) : ℤ) T), ∃! c : Γ(T.left, ⊤), s = c • VVRank.pullM P.A P.L _ h b := by
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl (y (closedPoint K))
  have hr : Set.range y ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim q (closedPoint K)]
    exact ⟨⟨_, hV⟩, rfl⟩
  let u : Over.mk y ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι y hr)
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac V.ι y hr))
  have h1 : 1 ^ P.g = 1 := one_pow _
  let k₀ : Fin (1 ^ P.g) := Fin.cast h1.symm 0
  have : Subsingleton (Fin (1 ^ P.g)) := ⟨fun a a' => Fin.ext (by have := a.2; have := a'.2; omega)⟩
  refine ⟨VVRank.pullM P.A P.L _ u (b k₀), fun T _ h s => ?_⟩
  obtain ⟨c, hc⟩ := hb T (h ≫ u)
  rw [VVRank.pullM_comp _ P.isLB, ← hc]
  exact existsUnique_smul_of_basis c k₀ s

theorem exists_univBasis_of_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) →
    ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  intro hL S S' G _ L hL₀ P f φ hp hw K _ y x hx
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := exists_univBasis_field hL.secBaseChangeAny P y
  have hτ : (𝟙 (Sp K) : (Over.mk y).left ⟶ (Over.mk x).left) ≫ (Over.mk x).hom = (Over.mk y).hom ≫ f :=
    (Category.id_comp _).trans hx.symm
  have : IsIso (C := Scheme.{0}) (X := (Over.mk y).left) (Y := (Over.mk x).left) (𝟙 (Sp K)) := IsIso.id _
  obtain ⟨e, he⟩ := UnivBasisMove.exists_rel_up hp (T := Over.mk y) (T₀ := Over.mk x) (𝟙 (Sp K)) hτ hw hL₀ P.isLB b
  refine ⟨SecM.toSec G e, fun K' _ i x' h s => ?_⟩
  obtain rfl : (spMap i ≫ y) ≫ f = x' := by rw [Category.assoc, hx, h]
  let T : Over S' := Over.mk (spMap i ≫ y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨E, hE⟩ := UnivBasisMove.exists_linearEquiv hp hw hL₀ P.isLB ((1 : ℕ) : ℤ) T
  let u : T ⟶ Over.mk y := Over.homMk (spMap i) rfl
  let u₀ : Over.mk (T.hom ≫ f) ⟶ Over.mk x := Over.homMk (spMap i) h
  have key : E (VVRank.pullM G L _ u₀ e) = VVRank.pullM P.A P.L _ u b :=
    (hE _).unique_down hL₀ P.isLB (he.pull _ _ u u₀ ((Category.id_comp _).trans (Category.comp_id _).symm))
  obtain ⟨c, hc, hu⟩ := hb T u (E s)
  refine ⟨c, E.injective (hc.trans ?_), fun r hr => hu r ?_⟩
  · rw [← key]
    exact (E.map_smul c _).symm
  · rw [← key]
    exact (congrArg E hr).trans (E.map_smul r _)

end GlobalTheory.Ex.OneGen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGenBasis

theorem pullTo_injective {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (p : Y' ⟶ Y) (e : ∀ k, p ≫ φ k = φ' k) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, (VVRank.pullTo s p e).f j = (VVRank.pullTo t p e).f j) (j) :
    s.f j = t.f j := by
  obtain rfl : (fun k => p ≫ φ k) = φ' := funext e
  refine p.app_injective _ (fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L (fun k => p ≫ φ k) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact (gs_res _ y _ hy' _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j)).trans (gs_res _ y _ hy' _))

theorem pullM_injective {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) [IsSchemeTheoreticallyDominant h.left] [QuasiCompact h.left] :
    Function.Injective (VVRank.pullM G L a h) := by
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w]
      exact (IsPullback.of_hasPullback T'.hom G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have : Flat (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have : IsSchemeTheoreticallyDominant (h ▷ G).left := .of_isPullback hp.flip
  have : QuasiCompact (h ▷ G).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  intro s t e
  exact Subtype.ext (funext (pullTo_injective (s := SecM.toSec G s) (t := SecM.toSec G t) (h ▷ G).left
    (fun _ => VVRank.whisker_snd_left G h) fun j => congrFun (congrArg Subtype.val e) j))

theorem exists_eq_mul {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : FractionRing W} (ha : a ≠ 0) {r : W'}
    (h : i' b = algebraMap W' _ r * i' a) : ∃ r₀ : W, b = algebraMap W _ r₀ * a := by
  have h₁ : i' (b / a) = algebraMap W' _ r := by
    rw [map_div₀, h, mul_div_cancel_right₀ _ ((map_ne_zero i').2 ha)]
  obtain ⟨p, hp, h₂⟩ := hf.to_isIntegral r
  have h₃ : IsIntegral W (b / a) := ⟨p, hp, i'.injective (by
    rw [Polynomial.hom_eval₂, hi, h₁, ← Polynomial.hom_eval₂, h₂, map_zero, map_zero])⟩
  obtain ⟨r₀, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h₃
  exact ⟨r₀, by rw [hr, div_mul_cancel₀ _ ha]⟩

theorem exists_fractionMap {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] (i : W →+* W')
    (hi : Function.Injective i) : ∃ i' : FractionRing W →+* FractionRing W',
      i'.comp (algebraMap W _) = (algebraMap W' _).comp i := by
  have hg : Function.Injective ((algebraMap W' (FractionRing W')).comp i) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W' (FractionRing W')).comp hi
  refine ⟨IsFractionRing.lift (K := FractionRing W) hg, RingHom.ext fun x => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

theorem appTop_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem inv_bijective (R : Type) [CommRing R] :
    Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

theorem exists_eq_mul_fn {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : Γ(Sp (FractionRing W), ⊤)} (ha : a ≠ 0)
    {r : Γ(Sp W', ⊤)} (h : (spMap i').appTop.hom b = (jK W').appTop.hom r * (spMap i').appTop.hom a) :
    ∃ r₀ : Γ(Sp W, ⊤), b = (jK W).appTop.hom r₀ * a := by
  obtain ⟨a, rfl⟩ := (inv_bijective _).2 a
  obtain ⟨b, rfl⟩ := (inv_bijective _).2 b
  obtain ⟨r, rfl⟩ := (inv_bijective _).2 r
  rw [appTop_inv, appTop_inv, appTop_inv, ← map_mul] at h
  obtain ⟨r₀, hr⟩ := exists_eq_mul i hf i' hi (a := a) (fun e => ha (by rw [e, map_zero]))
    ((inv_bijective (FractionRing W')).1 h)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r₀, by
    rw [appTop_inv (algebraMap W (FractionRing W)), ← map_mul, ← hr]⟩

theorem basis_of_square {A A' K K' M M' N N' : Type} [CommRing A] [CommRing A'] [CommRing K] [CommRing K'] [IsDomain K]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module A M] [Module A' M'] [Module K N]
    [Module K' N'] {f : A →+* K} {g : A →+* A'} {f' : A' →+* K'} {g' : K →+* K'} (p : M →ₛₗ[f] N) (q : M →ₛₗ[g] M')
    (p' : M' →ₛₗ[f'] N') (q' : N →ₛₗ[g'] N') (hsq : ∀ x, q' (p x) = p' (q x)) (hp : Function.Injective p)
    (hf : Function.Injective f) (e : N) (h₀ : ∀ s, ∃! c : K, s = c • e) (h₁ : ∀ s, ∃! c : K', s = c • q' e) (σ : M)
    (hne : p σ ≠ 0) (hgen : ∀ s, ∃ r : A', q s = r • q σ)
    (hint : ∀ a b r, a ≠ 0 → g' b = f' r * g' a → ∃ r₀, b = f r₀ * a) :
    LinearIndependent A (fun _ : Fin 1 => σ) ∧ Submodule.span A (Set.range fun _ : Fin 1 => σ) = ⊤ := by
  obtain ⟨a, ha, -⟩ := h₀ (p σ)
  have ha0 : a ≠ 0 := fun h => hne (ha.trans (by rw [h, zero_smul]))
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc k => ?_, eq_top_iff.2 fun s _ => ?_⟩
  · rw [Fin.sum_univ_one] at hc
    rw [Subsingleton.elim k 0]
    have t := congrArg p hc
    rw [map_smulₛₗ, ha, smul_smul, map_zero] at t
    have t' := (h₀ 0).unique t.symm (zero_smul _ _).symm
    exact hf (((mul_eq_zero.1 t').resolve_right ha0).trans (map_zero _).symm)
  · obtain ⟨b, hb, -⟩ := h₀ (p s)
    obtain ⟨r, hr⟩ := hgen s
    have t := congrArg p' hr
    rw [map_smulₛₗ, ← hsq, ← hsq, ha, hb, map_smulₛₗ, map_smulₛₗ, smul_smul] at t
    obtain ⟨r₀, hr₀⟩ := hint a b r ha0 ((h₁ _).unique rfl t)
    have : s = r₀ • σ := hp (by rw [map_smulₛₗ, ha, hb, smul_smul, hr₀])
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

theorem basisAlong_of_isGenSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  intro S G _ _ L hL W W' _ _ _ _ _ i hinj hf χ σ hgen ⟨e, he⟩ hne
  obtain ⟨i', hi⟩ := exists_fractionMap i hinj
  have hsq : spMap i' ≫ jK W = jK W' ≫ spMap i := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  let hK : Over.mk (jK W ≫ χ) ⟶ Over.mk χ := Over.homMk (jK W) rfl
  let hI : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let hI' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ) := Over.homMk (spMap i') rfl
  let hK' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (jK W') (by
    change jK W' ≫ spMap i ≫ χ = spMap i' ≫ jK W ≫ χ
    rw [← Category.assoc, ← hsq, Category.assoc])
  have hsq' : hI' ≫ hK = hK' ≫ hI := Over.OverMorphism.ext hsq
  have : IsSchemeTheoreticallyDominant hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).2
  have : QuasiCompact hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).1
  have hρ := pullM_injective G L ((1 : ℕ) : ℤ) hK
  have hid : spMap (RingHom.id (FractionRing W)) = 𝟙 _ := Spec.map_id _
  have h₀ : ∀ s : SecM G L ((1 : ℕ) : ℤ) (Over.mk (jK W ≫ χ)), ∃! c : Γ((Over.mk (jK W ≫ χ)).left, ⊤),
      s = c • SecM.ofSec G e := fun s => by
    have q := he _ (RingHom.id _) _ (by rw [hid, Category.id_comp]) s
    rwa [← VVRank.pullM_ofSec, show (Over.homMk (spMap (RingHom.id (FractionRing W))) _ :
      Over.mk (jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)) = 𝟙 _ from Over.OverMorphism.ext hid, VVRank.pullM_id G hL] at q
  have h₁ : ∀ s, ∃! c : Γ((Over.mk (spMap i' ≫ jK W ≫ χ)).left, ⊤),
      s = c • VVRank.pullM G L ((1 : ℕ) : ℤ) hI' (SecM.ofSec G e) := he _ i' _ rfl
  have hdom : IsDomain Γ((Over.mk (jK W ≫ χ)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := basis_of_square (VVRank.pullM G L ((1 : ℕ) : ℤ) hK) (VVRank.pullM G L _ hI) (VVRank.pullM G L _ hK')
    (VVRank.pullM G L _ hI') (fun x => by rw [VVRank.pullM_comp G hL, VVRank.pullM_comp G hL, hsq']) hρ
    (hK.left.app_injective ⊤) _ h₀ h₁ (SecM.ofSec G σ) hne
    (fun s => (hgen (SecM.toSec G (VVRank.pullM G L _ hI s))).imp fun _ hr => Subtype.ext (funext hr))
    fun a b r ha h => exists_eq_mul_fn i hf i' hi ha h
  rw [← VVRank.pullM_id G hL _ (SecM.ofSec G σ)] at key
  exact (GlobalTheory.LN.PolFrames.basisAlong_iff G L 1 (𝟙 _) hL
    (b' := fun _ => VVRank.pullS G _ (𝟙 _) σ) fun _ => VVRank.isPullSec_pullS G _ _ σ).2 key

end GlobalTheory.Ex.OneGenBasis
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension : ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries | exact GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_torsionPair_descent_algClosed_subfield : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  first | exact @GlobalTheory.QkDescent.exists_qkExt_of_isAlgClosed | exact GlobalTheory.QkDescent.exists_qkExt_of_isAlgClosed | (intros; apply GlobalTheory.QkDescent.exists_qkExt_of_isAlgClosed <;> assumption)
end
