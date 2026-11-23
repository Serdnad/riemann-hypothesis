module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValFeTranslate
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle027
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

open ConstFam FormalValue

theorem exists_vals_fsum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ α th hth
  have hj : 1 ≤ j := NeZero.one_le
  obtain ⟨s₀, hs₀, -⟩ := ((ArcThetaSpaces.sections_theta hL hL₂ E H D l c O β b a Λ).1 j α hj).2 th hth
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hE⟩ := hm m le_rfl
  have ex : ∀ mu, expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := fun mu => by
    rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]
  have hpos : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => ex mu ▸ (hf.1 (Λ.ε mu)).1
  have comp : ∀ mu, ∃ t : SecBMod a.D₀ j (Λ.ε (α + j • mu)), f (W.e (Λ.ε (α + j • mu))) =
      (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
      ∀ z, Λ.fn j (α + j • mu) t z = Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := fun mu => by
    have cast : ∀ x, Λ.ε α + j • Λ.ε mu = x → ∃ t : SecBMod a.D₀ j x, f (W.e x) =
        (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
        ∀ z, FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left
          ![z, z + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] =
            Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := by
      rintro _ rfl
      refine ⟨_, ex mu ▸ (hf.1 (Λ.ε mu)).2, fun z => ?_⟩
      have es := Λ.psi (mu + α)
      rw [map_add Λ.ε, map_add Λ.A.ct] at es
      refine (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu) es s₀ z).trans ?_
      refine (congrArg (· * _) (congrFun hs₀ (z + Λ.A.ct mu))).trans ?_
      have := (Λ.A.psi mu).ne_zero
      have := (Λ.A.psi α).ne_zero
      push_cast
      rw [Λ.A.psi_add]
      field_simp
    obtain ⟨t, h₁, h₂⟩ := cast (Λ.ε (α + j • mu)) (by rw [map_add (f := _), map_nsmul])
    refine ⟨t, h₁, fun z => Eq.trans ?_ (h₂ z)⟩
    exact congrArg (fun q => FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left ![z, z + q, q, 0])
      ((map_add Λ.A.ct _ _).trans (congrArg _ (map_nsmul Λ.A.ct _ _)))
  refine ⟨m, σ, fun v jL hjL => ?_⟩
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB (W.φ (basePt (Ξ.g v) (cpt ℂ⟦X⟧)))
  have hM' := (top_le_iff_cpt _ _).2 hM
  have hw : ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 ⟨mem_pull.2 h₀, hM⟩
  choose jf jt hc using exists_cohCharts (Ξ.g v) jM hM'
  obtain ⟨w, hw'⟩ := isUnit_valR (A := ℂ⟦X⟧) _ _ hw (W.w.s (fun _ => j₀, jM))
  have hτ := Ξ.τ_eq v jL jM j₀ hjL hw
  have hI : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have hx := Ξ.x_fm v
  rw [hI, ← hw'] at hτ
  rw [hI] at hx
  let i : Λ.A.X → W.P.D.toPre.X := fun mu => W.e (Λ.ε (α + j • mu))
  have hi : Function.Injective i := fun mu mu' h =>
    smul_right_injective Λ.A.X (Int.natCast_ne_zero.2 (NeZero.ne j)) ((natCast_zsmul mu j).trans
      ((add_left_cancel (Λ.ε.injective (W.e.injective h))).trans (natCast_zsmul mu' j).symm))
  let h : W.P.D.toPre.X → ℂ⟦X⟧ := fun x => w.val ^ j * (famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x))
  have h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat *
      PowerSeries.C (Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) := fun mu => by
    obtain ⟨t, e₁, e₂⟩ := comp mu
    have := GlobalTheory.ConstTerm.main hL hL₂ E H D l Xo c O β Y b a χ W Λ Ξ j (α + j • mu) t (f (i mu)) _
      (fun Z _ _ p κ jf j₀ hp hi => by
        rw [show f (i mu) = _ from e₁]
        exact valR_smul_pullB hW j _ t _ Z p κ jf j₀ hp hi) v jM j₀ _ _ (hc (i mu)) hw
    rw [← hw', e₂] at this
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [AnArc.term]; ring
  have h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0 := fun x hx => by
    have e₁ : f x = 0 := hf.2 x fun y e => hx (Λ.ε.symm (W.e.symm y)) (by
      rw [← e]
      show W.e (Λ.ε _) = _
      rw [map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, Λ.ε.apply_symm_apply, W.e.apply_symm_apply])
    have e₂ : famVal (Ξ.g v) (f x) (jf x) = 0 := by
      rw [e₁]
      exact (dif_pos (hc x).1).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    show _ * (_ * _) = _
    rw [e₂, zero_mul, mul_zero]
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α th v hpos, ← map_pow, ← map_mul]
  refine congrArg _ ((Units.mul_right_inj (w ^ j)).1 (eq_of_forall_mk_eq (Ideal.span {PowerSeries.X}) fun e => ?_))
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)})) e
  obtain ⟨F, hF⟩ := map_secVal_eq W.P.U.toUnifPre (hE e)
  obtain ⟨F', hF', hd⟩ := exists_sum_sub_mem hi h₁ h₂ (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
    have := hpos mu
    rw [Λ.A.mem_level]
    omega) (e + 1) F
  have H := (hF _ _ _ _ _ hx _ (Ideal.Quotient.mk (Ideal.span {PowerSeries.X} ^ (e + 1))) Ideal.mk_ker.ge).2
    F' jL jM jf jt hF' hjL hM' fun x _ => hc x
  rw [map_mul, H, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, show ∑ x ∈ F', h x = w.val ^ j * ∑ x ∈ F', famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x) from
    (Finset.mul_sum _ _ _).symm] at hd
  refine (congrArg (_ ∣ ·) ?_).mp (hd.mul_left ((tau W.P.U.toUnifPre (Ideal.span {PowerSeries.X}) (Ξ.x v).left jL jM).val ^ j))
  rw [Units.val_pow_eq_pow_val]
  have := congrArg (· ^ j) hτ
  simp only [mul_pow] at this
  linear_combination (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) * this

end GlobalTheory.ConstThetaSections
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFamValues

open ConstThetaSections ConstFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}


omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem ex_add_nsmul (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (j : ℕ) (α mu : Λ.A.X) :
    Λ.u.ex (Λ.A.ct α + j • Λ.A.ct mu) = a.D₀.c (Λ.ε α + j • Λ.ε mu) := by
  rw [← map_nsmul, ← map_add (f := _), ← map_nsmul, ← map_add (f := _), Λ.ct]


omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem expo_eq (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (j : ℕ) (α mu : Λ.A.X) : expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := by
  rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]

theorem secVal_mul_genVal (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (j : ℕ) (α mu : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (v : Λ.A.V) :
    FrameValue.secVal Λ.u a.D₀.P.isLB (feTranslate a.D₀ j (Λ.ε mu) (Λ.ε α) s₀) (Λ.u.ex v.2).left
        ![v.2, v.2 + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] *
      FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε α + j • Λ.ε mu)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![(Λ.A.ct α + j • Λ.A.ct mu) + v.2, Λ.A.ct α + j • Λ.A.ct mu, v.2, 0] =
      Λ.A.term j α (Λ.fn j α s₀) mu v := by
  have h₁ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![z + v.2, z, v.2, 0] = eTwoPi (v.1 y) := by
    rintro y _ _ rfl rfl
    exact Λ.arcDict_expZero_section v y
  have h₂ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB (a.D₀.psi x)
      (Out.jFK (R := ℂ) ℂ) (fun _ => z) = Λ.A.psi y := by
    rintro y _ _ rfl rfl
    exact Λ.psi y
  refine (congrArg₂ (· * ·) (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu)
    (h₂ (mu + α) _ _ (map_add _ _ _).symm (map_add _ _ _).symm) s₀ v.2)
    (h₁ (α + j • mu) _ _ (by rw [map_add (f := _), map_nsmul]) (by rw [map_add (f := _), map_nsmul]))).trans ?_
  change Λ.fn j α s₀ (v.2 + Λ.A.ct mu) * _ * _ = _
  have n₁ := (Λ.A.psi mu).ne_zero
  have n₂ := (Λ.A.psi α).ne_zero
  simp only [AnArc.term, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Λ.A.psi_add]
  field_simp

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (j : ℕ) [NeZero j] (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (m : ℕ) (f : ∀ x, ConstFam.SecBMod W.P.D.toPre j x) (σ : Out.H0 W.P.U.LG.L j), ConstFam.IsIntegralForm hW j (Λ.ε α) s₀ m f → (∀ n, W.P.U.toUnifPre.ExpandsAt n j σ f) → Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α (Λ.fn j α s₀) v) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ hW j _ α s₀ m f σ hf hE v jL hL
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hm : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => expo_eq Λ j α mu ▸ (hf.1 (Λ.ε mu)).1
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ :=
    hJ.symm ▸ (admissibleBase_powerSeries ℂ).2.2.2
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  replace hM := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) _).2 hM
  obtain ⟨j₀, h₀⟩ : ∃ j₀, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := ⟨_, FrameValue.le_chartAt a.D₀.P.isLB _⟩
  have hd := ConstTerm.le_div (M := W.P.D.toPre.P.L) (φ := W.φ) (k := j₀) (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left)
    (hb ▸ FormalValue.top_le_comp h₀ _) hM
  have hτ := Ξ.τ_eq v jL jM j₀ hL hd
  have hu := FormalValue.isUnit_valR _ _ hd (W.w.s (fun _ => j₀, jM))
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g v) jM hM
  have hs := exists_sum_sub_mem (i := fun mu => W.e (Λ.ε α + j • Λ.ε mu))
    (fun _ _ h => Λ.ε.injective (FamFree.add_nsmul_inj hj _ _ _ (W.e.injective h)))
    (n := fun mu => ((m : ℤ) + Λ.A.exponent j α mu).toNat)
    (c := fun mu => Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j)
    (h := fun x => valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j *
      (FormalValue.famVal (Ξ.g v) (f x) (jf x) * FormalValue.coordVal (Ξ.g v) x (jt x)))
    (fun mu => by
      rw [(hf.1 (Λ.ε mu)).2, ← secVal_mul_genVal, ← expo_eq]
      exact ConstTerm.core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v)
        (ex_add_nsmul Λ j α mu) (Λ.ex0_b v) (Ξ.g_rel v _) _ _ _
        (fun p => valR_smul_pullB hW j _ _ _ _ p _) jM j₀ _ _ (hc _) hd)
    (fun x hx => by
      have e : f x = 0 := hf.2 x fun mu h => hx (Λ.ε.symm (W.e.symm mu)) (by
        rw [Λ.ε.apply_symm_apply, map_add_nsmul, W.e.apply_symm_apply, h])
      have e' : FormalValue.famVal (Ξ.g v) (f x) (jf x) = 0 := by
        rw [e]
        exact (HolHom.valR_eq _ _ (hc x).1 _).trans (map_zero _)
      rw [e', zero_mul, mul_zero])
    (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
      have := hm mu
      rw [AnArc.mem_level]
      omega)
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α _ v hm, ← map_pow, ← map_mul]
  refine congrArg _ ((hu.pow j).mul_left_cancel (FormalValue.eq_of_forall_mk_eq
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => Ideal.Quotient.eq.2 ?_))
  obtain ⟨F, -, hF⟩ := ((FormalValue.value_eq_sum_expansion (admissibleBase_powerSeries ℂ) W.P.U (Ξ.g v) (Ξ.x v).left
    (Ξ.x_fm v)).2 j σ f hE).1 e
  obtain ⟨F', hFF, h₂⟩ := hs (e + 1) F
  have h₁ := hF F' jL jM jf jt hFF hL hM fun x _ => hc x
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
      Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α (Λ.fn j α s₀) mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, ← Finset.mul_sum, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow] at h₂
  replace h₂ := Ideal.pow_right_mono hJ.ge (e + 1) h₂
  have h₃ := congrArg (· ^ j) hτ
  simp only [mul_pow] at h₃
  convert add_mem (Ideal.mul_mem_left _ (valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j) h₁)
    (Ideal.mul_mem_left _ ((FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map
      (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (Ξ.x v).left jL jM).val ^ j) h₂) using 1
  linear_combination (-(PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
    Λ.A.term j α (Λ.fn j α s₀) mu v)) * h₃

end GlobalTheory.ConstFamValues
end
end
