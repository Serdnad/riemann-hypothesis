module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel
open GlobalTheory.TorusExt

theorem b_eq_of_equiv {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {j : ℕ} (hj : 0 < j) {p p' : QkPt D F j}
    (h : QkPt.Equiv D F p p') (hy : p.y = 0) (hy' : p'.y = 0) : p'.g.b = p.g.b := by
  letI := gtGroup D F
  obtain ⟨z, h₁, t, ht, h₂⟩ := h
  rw [hy, hy', zero_add] at h₁
  have hz : z = 0 := by
    have : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h₁.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hj.ne')
  obtain ⟨z₀, hz₀, t₀, ht₀, ht₁⟩ := qk_equiv_refl hB p
  have hz₀' : z₀ = 0 := by
    have h : j • z₀ = 0 := add_left_cancel (hz₀.symm.trans (add_zero _).symm)
    have h' : (j : ℤ) • z₀ = 0 := by rw [natCast_zsmul]; exact h
    exact (smul_eq_zero.1 h').resolve_left (by exact_mod_cast hj.ne')
  have htzero : t = 0 := by
    have he := (isAdd_iff_eq _ _ _).1 ht₁
    have hz0 : t₀ = 0 := add_left_cancel (he.symm.trans (add_zero _).symm)
    exact (isIota_unique (hz ▸ ht) (hz₀' ▸ ht₀)).trans hz0
  have he := (isAdd_iff_eq _ _ _).1 h₂
  rw [he, htzero, add_zero]

theorem act_compat_on_torsion : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  intro hL hBr E _ _ _ H D R _ _ C _ _ _ A o M hT N' ν' k β u r J j hj hr hlab x b hb
  letI := H.starRing
  have hG := hL.globalFns
  have hB := A.bimult
  have hB' : M.P.D.toPre.TauBimult := M.P.D.tau_bimult
  obtain ⟨-, -, -, -, br⟩ := hBr R A.D₀ A.even A.bimult C A.N A.ν
  obtain ⟨-, -, -, -, br'⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even hB' C N' ν'
  obtain ⟨e1, -, e3⟩ := br j
  obtain ⟨-, e2', e3'⟩ := br' j
  obtain ⟨τ, hτ, hQ, -⟩ := (twJ_mulEquiv C A.N N' k β u J).1 r j hr
  obtain ⟨f, f1, -, f3, -, f5, -⟩ := hT C j hj

  have actzero : ∀ {V : Type} [CommRing V] [IsDomain V] {D₁ : DegPre V}
      {O : Type} [CommRing O] [StarRing O] [Module O D₁.X]
      [Algebra (FractionRing V) C] (hB₁ : D₁.TauBimult) (oa : D₁.OAct O)
      (a : O) (p : QkPt D₁ C j), p.y = 0 →
      ∃ q : QkPt D₁ C j, q.y = 0 ∧ q.g.b = p.g.b ≫ oa.onB.act a ∧ QkAct oa a p q := by
    intro V _ _ D₁ O _ _ _ _ hB₁ oa a p hy
    letI := gtGroup D₁ C
    obtain ⟨z, hz, t, ht, ha⟩ := qk_equiv_refl hB₁ p
    have hz' : z = 0 := by
      have h : j • z = 0 := add_left_cancel (hz.symm.trans (add_zero _).symm)
      have h' : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h
      exact (smul_eq_zero.1 h').resolve_left (by exact_mod_cast hj.ne')
    have ht' : t = 0 := by
      have he := (isAdd_iff_eq _ _ _).1 ha
      exact add_left_cancel (he.symm.trans (add_zero _).symm)
    have iz : GtPtF.IsIota (D := D₁) (F := C) 0 0 := by simpa [hz', ht'] using ht
    obtain ⟨g, hg, hi⟩ := p.eq
    have hp : j • p.g = 0 := by
      have hg' := (isNsmul_iff_eq _ _ _).1 hg
      have hi' : g = 0 := isIota_unique (hy ▸ hi) iz
      exact hg'.symm.trans hi'
    have hq : j • gtSmul hG oa a p.g = 0 := by
      change j • (gtSmulHom hG oa C a) p.g = 0
      rw [← map_nsmul (gtSmulHom hG oa C a), hp, map_zero]
    let q : QkPt D₁ C j := ⟨0, gtSmul hG oa a p.g, 0,
      (isNsmul_iff_eq _ _ _).2 hq.symm, iz⟩
    exact ⟨q, rfl, gtSmul_b hG oa a p.g, ⟨q, by simp [q, hy], gtAct_gtSmul hG oa a p.g, qk_equiv_refl hB₁ q⟩⟩

  have key : ∀ (v : D.La) (p : QkPt A.D₀ C j), QkPt.Equiv A.D₀ C (A.I.ev j v) p → p.y = 0 →
      ∃ p' : QkPt M.P.D.toPre C j, p'.y = 0 ∧ p'.g.b = ν'.eA (J.φ (A.ν.eA.symm p.g.b)) ∧
        (f p').left = (o.I.ev j v).left ≫ M.φ := by
    intro v p hp hy
    obtain ⟨q, hq, -⟩ := e1 p
    obtain ⟨p', hp'⟩ := e2' (τ q)
    obtain ⟨pv, hpv⟩ := e2' (τ (A.q j v))
    have hE : QkPt.Equiv _ C pv p' := (e3' _ _ _ _ hpv hp').2 ((hQ _ _).1 ((e3 _ _ _ _ (A.hq j v) hq).1 hp))
    obtain ⟨t, t1, t2, t3⟩ := (hτ q _).1 rfl
    obtain ⟨s, s1, s2, s3⟩ := (hτ (A.q j v) _).1 rfl
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev j v).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (f1 _ _).1 (hlab v s _ pv z s1 s2 s3 hpv rfl)
    refine ⟨p', ?_, ?_, ?_⟩
    · have h0 : q.1.1.toAdd = 0 := A.ν.eX.injective (hq.1.trans (hy.trans (map_zero _).symm))
      rw [← hp'.1, t2, t1.1]
      erw [h0, map_zero, map_zero]
    · rw [← hp'.2.1, t3.1, t1.2.1, ← hq.2.1, MulEquiv.symm_apply_apply]
    · rw [← (f3 _ _).2 hE, ← hz]
      rfl
  obtain ⟨p₀, y₀, b₀⟩ := exists_qkPt_of_torsion (F := C) hB hj.ne' (b := A.ν.eA b) (by rw [← map_pow, hb, map_one])
  obtain ⟨v, hv⟩ := A.I.onto j hj p₀
  obtain ⟨p₁, y₁, a₀, hact₀⟩ := actzero hB A.oa x p₀ y₀
  have hv₁ : QkPt.Equiv A.D₀ C (A.I.ev j (x • v)) p₁ :=
    (qkAct_iff_of_equiv hB hG A.oa hv (A.I.lin j hj x v)).1 hact₀
  obtain ⟨p₀', c₀, d₀, g₀⟩ := key v p₀ hv y₀
  obtain ⟨p₁', c₁, d₁, g₁⟩ := key (x • v) p₁ hv₁ y₁
  obtain ⟨p₂', c₂, a₁, hact₁⟩ := actzero hB' M.P.oD x p₀' c₀
  have hf : f p₂' = f p₁' := by
    rw [f5 x _ _ hact₁]
    refine Over.OverMorphism.ext ?_
    rw [g₁, Over.comp_left, g₀, o.I.lin, Over.comp_left, Category.assoc, Category.assoc, M.act]
  have hb' := b_eq_of_equiv hB' hj ((f3 _ _).1 hf) c₂ c₁
  rw [d₁, a₁, a₀, d₀, b₀, MulEquiv.symm_apply_apply] at hb'
  unfold actV
  rw [← hb', MulEquiv.symm_apply_apply]

end GlobalTheory.Relabel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.RosMove

def rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) : Fin 6 → (A ⊗ A ⟶ A) :=
  ![(fst A A ≫ f) * snd A A, fst A A ≫ f, snd A A, fst A A * (snd A A ≫ g), fst A A, snd A A ≫ g]

theorem rosO_left {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) (k : Fin 6) :
    (rosO A f g k).left = rosatiφ A f g k := by
  fin_cases k <;> rfl

theorem lift_rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A)
    (k : Fin 6) : lift x y ≫ rosO A f g k = ![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] k := by
  fin_cases k <;> simp [rosO, MonObj.comp_mul]

theorem val_origin {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {f g : A ⟶ A}
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem val_move (hG : GlobalFnsSt) {F : Type} [Field F] [IsAlgClosed F] {S S' : Scheme.{0}} (t : Sp F ⟶ S) (t' : Sp F ⟶ S')
    {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] (hA : IsAbelianScheme A)
    (hA' : IsAbelianScheme A') {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (Φ : (Over.mk t ⊗ A).left ⟶ A'.left) (w : LB.Iso (L.pull (snd (Over.mk t) A).left) (L'.pull Φ)) (hw : w.IsGen)
    (hΦ : Φ ≫ A'.hom = (fst (Over.mk t) A).left ≫ t') (ψ : (Over.mk t ⟶ A) →* (Over.mk t' ⟶ A'))
    (hψ : ∀ x, (lift (𝟙 (Over.mk t)) x).left ≫ Φ = (ψ x).left) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (f' g' : A' ⟶ A')
    (hf : ∀ x, ψ (x ≫ f) = ψ x ≫ f') (hg : ∀ x, ψ (x ≫ g) = ψ x ≫ g')
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {u' : LB.Gen (LB.LinComb L' (rosatiφ A' f' g') rosatiε)} (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 A')) (LB.oneGen L'))
    (z : Sp F) (N) (J) (hN : Good L z N) (hJ : Good L' z J) (b b' : Over.mk t ⟶ A) :
    val u' (lift (ψ b) (ψ b')).left z J =
      (∏ k, gw w (lift (𝟙 (Over.mk t)) (lift b b' ≫ rosO A f g k)).left z (J (ψ (lift b b' ≫ rosO A f g k)).left)
        (fun _ => N (lift b b' ≫ rosO A f g k).left) ^ rosatiε k) * val u (lift b b').left z N := by
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  let Y : Over S := T ⊗ (A ⊗ A)
  let p : Y.left ⟶ Sp F := (fst T (A ⊗ A)).left
  let Y' : Over S' := Over.mk (p ≫ t')
  let Θ : (Y ⟶ A) → (Y' ⟶ A') := fun x => Over.homMk ((lift (fst T (A ⊗ A)) x).left ≫ Φ) (by
    show ((lift (fst T (A ⊗ A)) x).left ≫ Φ) ≫ A'.hom = p ≫ t'
    rw [Category.assoc, hΦ, ← Category.assoc, ← Over.comp_left, lift_fst])
  let pt : (T ⟶ A ⊗ A) → (T' ⟶ Y') := fun c => Over.homMk (lift (𝟙 T) c).left (by
    show (lift (𝟙 T) c).left ≫ (fst T (A ⊗ A)).left ≫ t' = t'
    rw [← Category.assoc, ← Over.comp_left, lift_fst]; exact Category.id_comp _)
  have hΘ : ∀ c x, pt c ≫ Θ (snd _ _ ≫ x) = ψ (c ≫ x) := fun c x => by
    ext
    show (lift (𝟙 T) c).left ≫ (lift (fst T (A ⊗ A)) (snd _ _ ≫ x)).left ≫ Φ = _
    rw [← Category.assoc, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hψ]
  let H : Y' ⟶ A' ⊗ A' := lift (Θ (snd _ _ ≫ fst A A)) (Θ (snd _ _ ≫ snd A A))
  have hH : ∀ x y, pt (lift x y) ≫ H = lift (ψ x) (ψ y) := fun x y => by
    rw [comp_lift, hΘ, hΘ, lift_fst, lift_snd]
  have hr : ∀ x y k, lift (ψ x) (ψ y) ≫ rosO A' f' g' k = ψ (lift x y ≫ rosO A f g k) := fun x y k => by
    rw [lift_rosO, lift_rosO]
    fin_cases k <;> simp [hf, hg]
  have := hA.smooth
  have := hA'.proper
  have sm : Smooth (A ⊗ A).hom := by
    show Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have sp : Smooth p := by
    show Smooth (pullback.fst t (A ⊗ A).hom); infer_instance
  have rd : IsReduced Y.left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hE : ∀ k, (Θ (snd _ _ ≫ rosO A f g k)).left = H.left ≫ rosatiφ A' f' g' k := fun k => by
    rw [← rosO_left, ← Over.comp_left]
    refine ComplexPoints.hom_ext_of_points (X := Y.left) p A'.hom ((Over.w _).trans (Over.w _).symm) fun x hx => ?_
    let x₀ : T ⟶ Y := Over.homMk x (by
      show x ≫ Y.hom = t
      rw [← Over.w (fst T (A ⊗ A)), ← Category.assoc]
      exact (congrArg (· ≫ t) hx).trans (Category.id_comp _))
    have e : x₀ = lift (𝟙 T) (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst]; ext; exact hx
      · rw [lift_snd, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e' : x = (pt (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A))).left := congrArg (·.left) e
    rw [e', ← Over.comp_left, ← Over.comp_left, hΘ, ← Category.assoc (pt _), hH, hr]
  let φ : Fin 6 → (Y.left ⟶ (T ⊗ A).left) := fun k => (lift (fst T (A ⊗ A)) (snd _ _ ≫ rosO A f g k)).left
  have hφ : ∀ k, φ k ≫ (snd T A).left = (snd T (A ⊗ A)).left ≫ rosatiφ A f g k := fun k => by
    rw [← rosO_left, ← Over.comp_left, ← Over.comp_left, lift_snd]
  have hφc : ∀ c k, (lift (𝟙 T) c).left ≫ φ k = (lift (𝟙 T) (c ≫ rosO A f g k)).left := fun c k => by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨a, ha, va⟩ := exists_gen hL (φ' := fun k => φ k ≫ (snd T A).left) (ε' := rosatiε)
    (fun U _ h => by simp only [hφ]) (LB.pullGen L _ _ u (snd T (A ⊗ A)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨s, hs, vs⟩ := GlobalTheory.EndRosati.exists_gen_through hL hL' w hw φ rosatiε a ha
  have ev : ∀ (c : T ⟶ A ⊗ A) (y : Sp F) N J, Good L y N → Good L' y J → val s (lift (𝟙 T) c).left y J =
      (∏ k, gw w (lift (𝟙 T) (c ≫ rosO A f g k)).left y (J (ψ (c ≫ rosO A f g k)).left)
        (fun _ => N (c ≫ rosO A f g k).left) ^ rosatiε k) * val u c.left y N := fun c y N J hN hJ => by
    rw [vs _ _ y J N hJ hN, va _ _ y N hN, val_pull hN, ← Over.comp_left, lift_snd]
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    rw [hφc, hψ, ← Over.comp_left, lift_snd]
  have ev' : ∀ (x x' : T ⟶ A) (y : Sp F) J, Good L' y J →
      val (LB.pullGen L' _ _ u' H.left) (lift (𝟙 T) (lift x x')).left y J = val u' (lift (ψ x) (ψ x')).left y J :=
    fun x x' y J hJ => by rw [val_pull hJ, ← hH]; rfl
  have hp : Function.Surjective p.appTop.hom := by
    let β : Y ≅ A ⊗ (A ⊗ T) := β_ _ _ ≪≫ α_ _ _ _
    have e : p = β.hom.left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left := by
      have : fst T (A ⊗ A) = β.hom ≫ snd A (A ⊗ T) ≫ snd A T := by simp [β, Y]
      exact congrArg (·.left) this
    rw [e]
    refine surj_comp ?_ (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
    have : IsIso β.hom.left.appTop := inferInstanceAs (IsIso (β.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso β.hom.left.appTop).2
  refine (ev' b b' z J hJ).symm.trans (Eq.trans ?_ (ev _ z N J hN hJ))
  refine gen_unique' hL' (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (hE k)) p
    (lift (𝟙 T) (lift 1 1)).left (by rw [← Over.comp_left, lift_fst]; rfl) hp
    (DVR.pullGen_isGen _ _ _ _ hu' _) hs (fun y I hI => ?_) _ _ z J hJ
  choose M hM using fun χ : Sp F ⟶ A.left => exists_chart hL (χ y)
  have o : ∀ k, lift (1 : T ⟶ A) 1 ≫ rosO A f g k = 1 := fun k => by
    rw [lift_rosO]; fin_cases k <;> simp [MonObj.one_comp]
  refine (ev' _ _ y I hI).trans (Eq.trans ?_ (ev _ y M I hM hI).symm)
  rw [map_one, val_origin u₀' (T := T') hI, val_origin u₀ (T := T) hM]
  simp [o, rosatiε, Fin.prod_univ_succ]

theorem rosV_move : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  intro hL R R' _ _ _ _ D D' F _ _ _ _ N N' ν ν' O _ _ oa oa' Φ w φ wv hw hΦ hφ hwv hact a ρ ρ' ⟨u, hu, u₀, hρ⟩
    ⟨u', hu', u₀', hρ'⟩ b b'
  have := oa.hom a
  have := oa.hom (star a)
  let ψ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R') F ⟶ D'.P.A) :=
    (ν'.eA.toMonoidHom.comp φ).comp ν.eA.symm.toMonoidHom
  have e : ∀ x, ψ (ν.eA x) = ν'.eA (φ x) := fun x => by simp [ψ]
  have ea : ∀ y x, ν.eA (actV ν oa y x) = ν.eA x ≫ oa.act y := fun y x => ν.eA.apply_symm_apply _
  have hf : ∀ y x, ψ (x ≫ oa.act y) = ψ x ≫ oa'.act y := fun y x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [← ea, e, e, hact]; exact ν'.eA.apply_symm_apply _
  have hψ : ∀ x, (lift (𝟙 (TF (R := R) F)) x).left ≫ Φ = (ψ x).left := fun x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [e, hφ]
  let z : Sp F := IsLocalRing.closedPoint F
  have hN : Good D.P.L z ν.J := fun q => ν.good q trivial
  have hJ : Good D'.P.L z ν'.J := fun q => ν'.good q trivial
  have H := val_move hL.globalFns _ _ D.P.isAb D'.P.isAb D.P.isLB D'.P.isLB Φ w hw hΦ ψ hψ _ _ _ _ (hf (star a)) (hf a)
    hu u₀ hu' u₀' z ν.J ν'.J hN hJ (ν.eA b) (ν.eA b')
  let W : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x =>
    gw w (lift (𝟙 (TF (R := R) F)) x).left z (ν'.J (ψ x).left) (fun _ => ν.J x.left)
  have hW : ∀ x, toStk z (wv x) = (W (ν.eA x)).val := fun x => by
    rw [hwv, ← e]
    have m₁ : Φ ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left) :=
      (congrArg (fun q : Sp F ⟶ _ => q z ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left)) (hψ (ν.eA x))).mpr (hJ _)
    have m₂ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : TF (R := R) F ⟶ _ => q.left z ∈ D.P.L.U (ν.J (ν.eA x).left))
        (lift_snd (𝟙 (TF (R := R) F)) (ν.eA x))).mpr (hN _)
    exact toStk_valF _ (_ ⊓ _) z ⟨mem_pull.2 m₁, mem_pull.2 m₂⟩ _
  have H' : val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J =
      (∏ k, W (lift (ν.eA b) (ν.eA b') ≫ rosO _ (oa.act (star a)) (oa.act a) k) ^ rosatiε k) * val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J := by
    rw [← e, ← e]; exact H
  have v : toStk z (ρ b b') = (val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J).val := by
    rw [hρ]; exact toStk_valF _ _ z (hN.mem _ _) _
  have v' : toStk z (ρ' (φ b) (φ b')) = (val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J).val := by
    rw [hρ']; exact toStk_valF _ _ z (hJ.mem _ _) _
  apply (toStk z).injective
  simp only [map_mul, hW, v, v', ea, ← Units.val_mul, H', lift_rosO]
  congr 1
  clear_value W
  apply Additive.ofMul.injective
  simp [rosatiε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.RosMove
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.exists_abelianPartIso_theta_section_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  first | exact @GlobalTheory.Ex.AbPartIso.exists_th_scale | exact GlobalTheory.Ex.AbPartIso.exists_th_scale | (intros; apply GlobalTheory.Ex.AbPartIso.exists_th_scale <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.exists_torsion_map_of_theta_matching : AllMatch fun {_} _ {N} {N'} {n} mt _ _ => mt.A → ∀ e, mt.Term e → ∀ j : ℕ, ∃ ρ : N.A → N'.A, TorsMap N.toNumB N'.toNumB (n ^ j) mt.c₀ ρ ∧ (∀ i, i ≤ 2 * j → ∀ p p', mt.r (n ^ i) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b) ∧ ∀ b : N.A, b ^ (n ^ j) ^ 2 = 1 → ∃ p p', mt.r (n ^ (2 * j)) p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  first | exact @GlobalTheory.Ex.TorsMatch.exists_torsMap | exact GlobalTheory.Ex.TorsMatch.exists_torsMap | (intros; apply GlobalTheory.Ex.TorsMatch.exists_torsMap <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.AbPartSym

theorem exists_move {X₁ X₂ B Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ B)) {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ f₁ = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L₁ φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J₂ J₁,
      Good L₂ z J₂ → Good L₁ z J₁ → val u r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t (r ≫ h) z J₁ := by
  let c := chartPullLinComb L₁ f₁ φ' φ ε h hc
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (c.le j) (pullU h _ (t.s (c.idx j)))⟩
  have va : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) j, r z ∈ LB.wchart (L₁.pull f₁) φ' j →
      gm r z (LB.wchart (L₁.pull f₁) φ' j) (a.s j) =
        gm (r ≫ h) z (LB.wchart L₁ φ fun k => j k PUnit.unit) (t.s fun k => j k PUnit.unit) := fun Z r z j hj =>
    (gm_res r z (c.le j) hj _).trans (gm_pull r h z _ (c.le j hj) _)
  have ha : a.IsGen := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm a fun y j j' hj hj' => by
    rw [va _ _ y j hj, va _ _ y j' hj', Category.id_comp]
    refine (gen_trans ht h y (c.le j hj) (c.le j' hj')).trans (congrArg (· * _) ?_)
    exact ((gm_linComb L₁ φ ε h y _ _ (c.le j hj) (c.le j' hj')).symm.trans (c.g y j j' hj hj').symm).trans
      (gm_linComb (L₁.pull f₁) φ' ε (𝟙 Y') y j j' hj hj')
  obtain ⟨u, hu, hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨u, hu, fun Z r z J₂ J₁ g₂ g₁ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' fun k _ => J₁ ((r ≫ φ' k) ≫ f₁) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (g₁ ((r ≫ φ' k) ≫ f₁))
  refine (hv Z r z _ _ (g₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_)
  · rw [Category.assoc]
  · exact (va Z r z _ m).trans (val_of t (r ≫ h) z J₁ _ fun k => by
      rw [Category.assoc, Category.assoc, hc]).symm

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem sym_one (D : DegPre R) {Z : Over (Sp R)} {z : Z.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : Z ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ D.sym (eSec D.P.A) Z.hom).symm.trans ((val_corr hJ D.sym_rig Z.hom).trans (val_one _))

theorem val_sym_move (hG : GlobalFnsSt) {T : Over (Sp R)} (g : T ⊗ D.P.A ⟶ D'.P.A)
    (hg : ∀ (Z : Over (Sp R)) (t : Z ⟶ T) (x y : Z ⟶ D.P.A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (D.P.L.pull (snd T D.P.A).left) (D'.P.L.pull g.left)) (hw : w.IsGen) {Z : Over (Sp R)} (t : Z ⟶ T)
    (x : Z ⟶ D.P.A) {z : Z.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D'.sym (lift t x ≫ g).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J := by
  let ρ : ∀ {Z : Over (Sp R)} (t : Z ⟶ T), (Z ⟶ D.P.A) →* (Z ⟶ D'.P.A) := fun t =>
    MonoidHom.mk' (fun x => lift t x ≫ g) (hg _ t)
  let n : T ⊗ D.P.A ⟶ T ⊗ D.P.A := lift (fst _ _) (snd _ _)⁻¹
  have hn : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A), (lift t x).left ≫ n.left = (lift t x⁻¹).left :=
    fun t x => by rw [← Over.comp_left, comp_lift, lift_fst, GrpObj.comp_inv, lift_snd]
  have ng : n.left ≫ g.left = g.left ≫ (ι[D'.P.A]).left := by
    have e : n ≫ g = (lift (fst T D.P.A) (snd T D.P.A) ≫ g)⁻¹ := map_inv (ρ (fst T D.P.A)) (snd T D.P.A)
    rw [lift_fst_snd, Category.id_comp] at e
    exact congrArg (fun q => q.left) e
  obtain ⟨u, hu, hv⟩ := exists_move w hw D.P.isLB D'.P.isLB (K := Fin 2) ![n.left, 𝟙 _] (snd T D.P.A).left
    (fun k => by
      fin_cases k
      · exact congrArg (fun q => q.left) (lift_snd (fst T D.P.A) (snd T D.P.A)⁻¹)
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) D.sym D.sym_gen
  have hv' : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A) (z : Z.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val u (lift t x).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J :=
    fun t x z J J' hJ hJ' => by
      refine (hv _ _ z J' J hJ' hJ).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hn, Category.comp_id, zpow_one, zpow_neg_one]
      simp only [← Over.comp_left, lift_snd]
  have key := gen_unique' D'.P.isLB
    (φ := fun k => g.left ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ng, Category.id_comp, Category.comp_id])
    (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left])
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst hG D.P.isAb T)
    (DVR.pullGen_isGen _ _ _ _ D'.sym_gen g.left) hu (fun y I' hI' => by
      choose I hI using fun χ : T.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
      have o : lift (𝟙 T) (1 : T ⟶ D.P.A) ≫ g = 1 := map_one (ρ (𝟙 T))
      rw [val_pull hI', hv' _ _ y I I' hI hI', ← Over.comp_left, inv_one, o, sym_one D hI, sym_one D' hI',
        mul_inv_cancel, _root_.one_mul]) _ (lift t x).left z J' hJ'
  exact (val_pull hJ' _ _ _).symm.trans (key.trans (hv' t x z J J' hJ hJ'))


open GlobalTheory.ThetaInValues in
theorem sym_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have c : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  have v : ∀ a, sR y (wVal ν ν' w f a) = (gw w (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left y
      (ν'.J (ν'.eA (f a)).left) (fun _ => ν.J (ν.eA a).left)).val := fun a => by
    refine toStk_valF _ _ y ?_ _
    refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
    · have := good ν' y (ν'.eA (f a)).left
      conv at this => enter [2]; rw [← c a]
      exact this
    · have := good ν y (ν.eA a).left
      conv at this => enter [2]; rw [← lift_snd (𝟙 (TF (R := R) F)) (ν.eA a)]
      exact this
  have key := val_sym_move hG (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 _) (ν.eA x) (good ν y) (good ν' y)
  rw [← map_inv ν.eA, c, c, sym_eq, sym_eq] at key
  refine (sR (R := R) y).injective ?_
  rw [map_mul, map_mul, v, v, ← sU_val, ← sU_val, key, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel_right, mul_comm]

end GlobalTheory.AbPartSym
end
end
