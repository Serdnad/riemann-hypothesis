module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowers
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3170
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3342
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.thetaSystem_universalUnitary_deep_towers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → GlobalTheory.GSep.Deep X₁ act := by
  first | exact @GlobalTheory.GSep.UTower.deep_of_uLink | exact GlobalTheory.GSep.UTower.deep_of_uLink | (intros; apply GlobalTheory.GSep.UTower.deep_of_uLink <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  obtain ⟨z⟩ : Nonempty (TFK (R := R) K).left := exists_pt (R := R) (F := K)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj (R := R) (F := K) z (val e' (𝟙 _) z J' * (val e (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl : z = z' := pt_eq (R := R) (F := K) z z'
    rw [hc, val_tr he (𝟙 _) hJ hJ', val_tr he' (𝟙 _) hJ hJ']
    refine Eq.trans ?_ (Units.val_mul _ _)
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem over_scale {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' _ s s' v hs hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  have pf : ∀ (e : FrAt x) z J, val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = val e (𝟙 _) z J ^ k :=
    fun e z J => (map_zpow _ _ _).trans (zpow_natCast _ _)
  have hval' : ValAt s x e (c ^ k * v) := fun z J hJ => by
    have cm : @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z (c ^ k * v)) =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) ^ k *
          @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z v) :=
      (cst_eq (R := V) z _).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (map_pow _ _ _) (cst_eq (R := V) z _).symm))
    rw [hval z J hJ, pf, pf, cm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    ring
  have S := sumF_const_mul (c⁻¹ ^ k) (h k hk wk hwkv hwk s s' _ hs hval')
  have sc := coef_scale (w' := wk') hwk (c := c⁻¹ ^ k) (fun z J hJ => by
    rw [hwk' z J hJ, hwkv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      cst_eq, cst_eq, map_pow]) s'
  rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul] at S
  simpa only [← sc] using S


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_terms_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro I X₁ z₁ act x₀ _ V _ _ _ ev X _ t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨χ, hχ, hyp⟩ := GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.GSep.TwistTranslate.over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (lab c + τ)).2.1
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu1 : u ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J, hJ⟩ := exists_good' 𝔪.A.isLB z
    have q := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (htors (lab c + τ)) he₂ hJ
    rw [div_self', one_pow] at q
    have q' := congrArg Units.val q
    have e : (val (fr (lab c + τ)) (𝟙 _) z J / val e₂ (𝟙 _) z J).val =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z u) := by
      rw [div_eq_mul_inv, Units.val_mul, huv z J hJ, Units.mul_inv_cancel_right]
    rw [Units.val_pow_eq_pow_val, e] at q'
    exact cstH_inj (R := V) z ((map_pow _ _ _).trans (q'.trans (map_one _).symm))
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hov' := over_scale 𝔪 hw''g hu huv hw₃v hov
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w₃ χ' =
      u⁻¹ * ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' =>
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]) s χ'
  haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
  have hint : ∀ mu : X, ∃ a : V, algebraMap V (FractionRing V) a =
      u⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
    · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
      rw [inv_pow, hu1, inv_one]
      exact isIntegral_one
    · refine IsIntegral.of_pow hk ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one]
      exact isIntegral_one
  choose a ha using hint
  refine ⟨fun mu _ => a mu * T mu c, x, fr, th, w₀, s, fun _ => _, fun _ => w₃, hx, hfr, hth, hw₀, hs,
    fun _ => ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, hov'⟩,
    fun mu _ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := (hc c).1
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]
  · rw [hco, map_mul, ha, ← hTc, _root_.mul_assoc]

end GlobalTheory.GSep.TermsExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono (le_refl (I ^ 1)) (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1
  ring

private theorem sum_terms_universal_member {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X]
    {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)
    {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam} {T : (Fin 8 → X) → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

theorem UMem.const_term_sub_mem : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hd V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c r hr
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ := UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, TwistSum₂.val_stalkHom] at e
  have e' : 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
      algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    exact e
  have hS := sum_terms_universal_member 𝔪 hT c
  rw [e'] at hS
  have hI := TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _ hθ hS
  have := sub_mem_of_sumI hI 0 fun j hj =>
    GlobalTheory.T.thetaModelMember_term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c _ (𝔪.e₈.symm.map_ne_zero_iff.2 hj)
  simpa only [map_zero] using this

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_terms_dividing_label_group_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : (Fin 8 → Y1) → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  first | exact @GlobalTheory.Poinc.Sep.exists_terms_single | exact GlobalTheory.Poinc.Sep.exists_terms_single | (intros; apply GlobalTheory.Poinc.Sep.exists_terms_single <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_thetaTerms_torusTranslate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : (Fin 8 → X) → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  first | exact @GlobalTheory.Poinc.Sep.TermsExt.exists_terms_translate | exact GlobalTheory.Poinc.Sep.TermsExt.exists_terms_translate | (intros; apply GlobalTheory.Poinc.Sep.TermsExt.exists_terms_translate <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LocAcycDegOne

open scoped TensorProduct

theorem unitsL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.henselian_directed_union_subalgebras q T hT hq O hO A π hπ

theorem picL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt q T hT hq O hO A π hπ

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (T B : Type) [CommRing T] [Nontrivial T] [CommRing B] [Algebra T B] (hT : AIC T) :
    ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  have hcyc : (Polynomial.cyclotomic q T).Monic := Polynomial.cyclotomic.monic q T
  have hdeg : 0 < (Polynomial.cyclotomic q T).natDegree := by
    rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨ζ, hζ⟩ := hT _ hcyc hdeg
  refine ⟨algebraMap T B ζ, ?_⟩
  have h0 := congrArg (algebraMap T B) hζ
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, Polynomial.hom_eval₂, map_zero] at h0
  rw [Polynomial.aeval_def, algebraMap_int_eq]
  rwa [show (algebraMap T B).comp (Int.castRingHom T) = Int.castRingHom B from RingHom.ext_int _ _] at h0

theorem tateTwistCohomology_genericFibre_henselLine_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ i : ℤ, Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 i) := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA i
  have hqB : IsUnit (q : TensorProduct T (FractionRing T) A) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  have hz := exists_cyclotomic_root q T (TensorProduct T (FractionRing T) A) hT
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (TensorProduct T (FractionRing T) A) hqB hz 1 i 1
  have h1 : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 1) :=
    GlobalTheory.T.kummer_etale_vanishing q _ hqB (fun u => (unitsL q T hT hq A hSH hA u).imp fun _ h => h.symm) (picL q T hT hq A hSH hA)
  refine ⟨fun x y => e.injective ?_⟩
  exact Subsingleton.elim _ _

end GlobalTheory.LocAcycDegOne
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes : ∀ (σ : Setup) (u : σ.A.left.functionField), (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  first | exact @GlobalTheory.Desc.Setup.forall_mem_W_iff | exact GlobalTheory.Desc.Setup.forall_mem_W_iff | (intros; apply GlobalTheory.Desc.Setup.forall_mem_W_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  first | exact @GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper | exact GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper | (intros; apply GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  first | exact @GlobalTheory.Mum.PowData.adjCls_abelianPart | exact GlobalTheory.Mum.PowData.adjCls_abelianPart | (intros; apply GlobalTheory.Mum.PowData.adjCls_abelianPart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  first | exact @GlobalTheory.Mum.PowData.periodRel_of_adj | exact GlobalTheory.Mum.PowData.periodRel_of_adj | (intros; apply GlobalTheory.Mum.PowData.periodRel_of_adj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_carried_section_off_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.exists_carried_sec_off_closed | exact GlobalTheory.Mum.exists_carried_sec_off_closed | (intros; apply GlobalTheory.Mum.exists_carried_sec_off_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  first | exact @GlobalTheory.Poinc.Sep.twistAtEach_exists | exact GlobalTheory.Poinc.Sep.twistAtEach_exists | (intros; apply GlobalTheory.Poinc.Sep.twistAtEach_exists <;> assumption)
end
