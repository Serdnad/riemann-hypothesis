module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle982
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationAtUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatTrivSec

variable {X Y : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

def pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) : LB.Sec (L.pull F) where
  f := fun I => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => F) I PUnit.unit)).op).hom
    ((F.app _).hom (θ.f (I PUnit.unit)))
  compat := fun I J => fn_ext fun y hy => by
    have hI : F y ∈ L.U (I PUnit.unit) := mem_pull.1 hy.1
    have hJ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.2
    have hm : (𝟙 Y ≫ F) y ∈ L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit) := ⟨hI, hJ⟩
    refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.1 _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_))
    refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 Y) y I J hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.2 _).trans (gs_pull (𝟙 Y) F y _ hJ _))))).symm
    exact (gs_res _ y inf_le_left hm _).symm.trans ((congrArg (gs _ y _) (θ.compat _ _)).trans
      ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

theorem gs_pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) (y : Y) (J : PUnit → L.ι) (hy : y ∈ (L.pull F).U J) :
    gs (𝟙 Y) y _ ((pullSec L θ F).f J) = gs F y (L.U (J PUnit.unit)) (θ.f (J PUnit.unit)) := by
  have hI : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy
  refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_)
  rw [Category.id_comp]

theorem cst_bijective_of {C : Type} [CommRing C] (V : (Sp C).Opens)
    (hV : Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :
    Function.Bijective (cst V.ι ⊤) := by
  have key : ∀ (V' : (Sp C).Opens) (h : V' ≤ ⊤), V' = V →
      Function.Bijective ((Sp C).presheaf.map (homOfLE h).op).hom := by
    rintro V' h rfl
    exact hV
  have h₁ : Function.Bijective V.ι.appTop.hom := by
    rw [Scheme.Opens.ι_appTop]
    exact key _ _ V.ι_image_top
  have h₀ : Function.Bijective (rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) := by
    have : ⇑(rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  exact h₀.comp (h₁.comp h₃)

theorem gs_cst_top {C : Type} [CommRing C] {Z : Scheme.{0}} (f : Z ⟶ Sp C) (z : Z) (x : C) :
    gs (𝟙 Z) z ⊤ (cst f ⊤ x) = gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom x) := by
  refine (gs_res (𝟙 Z) z (U := f ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 Z) f z ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

theorem exists_sec_near : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  intro B C _ _ _ g hg W hbij M hM hT y
  classical
  haveI : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Sp B)))
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, c, u, hcomb⟩ := FlatSec.exists_comb_of_flat B C g hg W.toScheme W.ι _ (spMap g ∣_ W)
    (spMap g ⁻¹ᵁ W).ι (isPullback_morphismRestrict (spMap g) W) M hM (genSec t ht)
  choose a ha using fun i => DVR.ValuationAtUnit.exists_glue_ratio
    (DVR.linComb_cover M hM (fun _ : PUnit => spMap g ∣_ W) (fun _ => 1)) (pullSec M (u i) (spMap g ∣_ W)) t ht
  have hb := cst_bijective_of _ hbij
  choose e he using fun i => hb.2 (a i)
  have chart : ∀ z : (spMap g ⁻¹ᵁ W).toScheme, ∃ k, (spMap g ∣_ W) z ∈ M.U k := fun z => by
    have hz : (spMap g ∣_ W) z ∈ ⨆ k, M.U k := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hz
  have key : ∀ (z : (spMap g ⁻¹ᵁ W).toScheme) (k : M.ι), (spMap g ∣_ W) z ∈ M.U k → ∀ i,
      gs (spMap g ∣_ W) z _ ((u i).f k) = gs (𝟙 _) z ⊤ (a i) * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
    intro z k hk i
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    refine (gs_pullSec M (u i) _ z (fun _ => k) hz).symm.trans ?_
    refine (congrArg (gs (𝟙 _) z _) (ha i (fun _ => k))).trans ?_
    rw [gs_mul (𝟙 _) z _ hz, gs_res (𝟙 _) z _ hz, gs_unit (𝟙 _) z _ hz]
  have hsum : ∑ i, c i * e i = 1 := by
    apply hb.1

    rw [map_sum, map_one]
    refine fn_ext fun z _ => ?_
    obtain ⟨k, hk⟩ := chart z
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    have h1 := hcomb z k hk
    simp only [key z k hk] at h1
    have h2 : gs (𝟙 _) z _ ((genSec t ht).f (fun _ => k)) = (gm (𝟙 _) z _ (t.s (fun _ => k))).val :=
      gs_unit (𝟙 _) z _ hz _
    rw [h2] at h1
    simp only [map_mul, he]
    rw [FlatSec.gs_sum (𝟙 _) z ⊤ trivial, gs_eq (𝟙 _) z ⊤ trivial 1, map_one, map_one]
    simp only [gs_mul (𝟙 _) z ⊤ trivial]
    have h3 : (∑ i, gs (𝟙 _) z ⊤ (cst (spMap g ⁻¹ᵁ W).ι ⊤ (c i)) * gs (𝟙 _) z ⊤ (a i)) *
        (gm (𝟙 _) z _ (t.s (fun _ => k))).val = 1 * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_assoc _ _ _) h1.symm
    exact (Units.mul_left_inj _).1 h3
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ y.asIdeal := by
    by_contra hne
    push_neg at hne
    apply y.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hne i)
  refine ⟨u i, PrimeSpectrum.basicOpen (e i), hi, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := chart z
  have hu1 : IsUnit (gs (𝟙 _) z ⊤ (a i)) := by
    rw [← he i, gs_cst_top, isUnit_gs_iff _ z ⊤ trivial, basicOpen_eq_of_affine]
    exact hz
  have hu2 : IsUnit (gs (spMap g ∣_ W) z _ ((u i).f k)) := by
    rw [key z k hk i]
    exact hu1.mul (Units.isUnit _)
  rw [isUnit_gs_iff _ z _ hk] at hu2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hu2⟩

end GlobalTheory.FlatTrivSec
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_cusp_kills_of_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hnd hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
  set K := k * ∑ i ∈ Finset.range l, q ^ (n * i) with hK_def
  obtain ⟨hregK, a, ha⟩ := GlobalTheory.T.regular_pair_lift_to_prime_power_field q l n k hq2 hl hn hnd hreg
  have hregK' : Reg (Nat.card F') n K := by rw [hcard']; exact hregK
  obtain ⟨hYchar, -⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F' θ hθ n K hn hregK'
  have hYs : ∀ g, cusp θ n K (galAct F F' n s g) = cusp θ n K g := by
    intro g
    obtain ⟨⟨i, hi⟩, hi'⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 s
    simp only at hi'
    obtain ⟨r, hp, hr⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
    have hsx : ∀ x, s.toRingEquiv x = x ^ (ringChar F' ^ ((r : ℕ) * i)) := by
      intro x
      change s x = _
      rw [← hi', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr, hchar, pow_mul]
    have h1 := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ s.toRingEquiv ((r : ℕ) * i) hsx n K g
    have hpq : ringChar F' ^ ((r : ℕ) * i) = q ^ i := by
      rw [hchar, pow_mul, ← hr, hq_def, Nat.card_eq_fintype_card]
    rw [hpq] at h1
    have hpow : ∀ j, K * q ^ j ≡ K * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
      intro j
      induction j with
      | zero => simp only [pow_zero, mul_zero, mul_one]; exact Nat.ModEq.refl _
      | succ j ih =>
        have e1 : K * q ^ (j + 1) = (K * q ^ j) * q := by ring
        have e2 : K * Nat.card F' ^ (a * (j + 1)) = (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) := by
          rw [hcard']; ring
        rw [e1, e2]
        calc K * q ^ j * q ≡ K * Nat.card F' ^ (a * j) * q [MOD Nat.card F' ^ n - 1] := ih.mul_right _
          _ = (K * q) * Nat.card F' ^ (a * j) := by ring
          _ ≡ (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
            apply Nat.ModEq.mul_right
            rw [hcard']; exact ha
    have h2 := GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq F' θ hθ n K (K * q ^ i) (a * i) hn (hpow i)
    rw [galAct_apply]
    exact h1.trans (congrFun h2 g)
  obtain ⟨X0, hX0, hX0a, hX0b⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; simp
  have hcstar : star c = c := by rw [hc_def]; simp
  set X : GHat F F' n → ℂ := fun x => c * X0 x with hX_def
  have hX : X ∈ Virt ℂ ℂ (GHat F F' n) := by
    have e : X = ((-1 : ℤ) ^ (n - 1)) • X0 := by
      funext x
      simp only [hX_def, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hc_def]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hX0 _
  have hfun : (fun δ => X (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := by
    funext δ
    simp only [hX_def, hX0b]
    by_cases h : ∃ γ, IsNorm s δ γ <;> simp [shLift, cusp, h, hc_def]
  have hcl : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    have := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y
    simp only [cusp]
    rw [this]
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy h
    apply hinj
    refine hθ _ _ ?_ ?_ h
    · exact fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    · exact fun h0 => hy (hinj (h0.trans (map_zero ι).symm))
  obtain ⟨-, hnormF⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hΓ : Nat.card (F' ≃ₐ[F] F') = l := IsGalois.card_aut_eq_finrank F F'
  have htop : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := fun t => by
    rw [zpowers_eq_top_of_prime_card hΓ hs]; trivial
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s htop n _ _ hcl hcl
  rw [hnormF] at hiso
  have hnorm : ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    have e : ∀ g, X (inl g * inr s) * star (X (inl g * inr s)) =
        shLift s (cusp (pullθ ι θ) n k) g * star (shLift s (cusp (pullθ ι θ) n k) g) := fun g => by
      rw [← congrFun hfun g]
    rw [finsum_congr e]
    have hpos : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    apply mul_left_cancel₀ hpos
    rw [hiso, mul_comm]
  set S : F'[X] → ℂ := fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) with hS_def
  have hS1 : S 1 = 0 := by
    simp only [hS_def, Polynomial.map_one]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rootSum]
  have hSprod : S = fun P => ∏ j : Fin l, rootSum θ (k * q ^ (j : ℕ)) P := by
    funext P
    simp only [hS_def]
    rw [GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k P, Fin.prod_univ_eq_prod_range (fun j => rootSum θ (k * q ^ j) P) l]
  have hprim := GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form F' θ S n K hS1
  have hprod := GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum F' θ hθ n K l (fun j => k * q ^ (j : ℕ)) hn
  rw [hcard'] at hprod
  set cnt := (Finset.univ.filter fun a : Fin l → Fin n =>
    K ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ n - 1]).card with hcnt_def
  have hcnt : cnt ≡ 1 [MOD l] := GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd q l n k hq2 hl hn hnd hreg
  have hz : ∑ᶠ g, X (inl g) * star (cusp θ n K g) = ((cnt : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [finsum_eq_sum_of_fintype] at hprim hprod ⊢
    have e1 : ∀ g, X (inl g) * star (cusp θ n K g) = c * (psiG S n g * star (cusp θ n K g)) := fun g => by
      simp only [hX_def, hX0a]; ring
    rw [Finset.sum_congr rfl (fun g _ => e1 g), ← Finset.mul_sum, hprim]
    have e2 : ∀ g, chG S n g * star (cusp θ n K g) = star (cusp θ n K g * star (chG S n g)) := fun g => by
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun g _ => e2 g), ← star_sum]
    have e3 : ∀ g, cusp θ n K g * star (chG S n g) = c * (psiG (rootSum θ K) n g * star (chG S n g)) :=
      fun g => by simp only [cusp, hc_def]; ring
    rw [Finset.sum_congr rfl (fun g _ => e3 g), ← Finset.mul_sum, hSprod, hprod, star_mul', hcstar, ← mul_assoc, hc2,
      one_mul, star_mul', star_natCast, star_natCast]
    push_cast
    ring
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (cnt : ℤ)) := by
    rw [hΓ, Int.natCast_dvd_natCast]
    intro h
    have h1 : cnt % l = 1 % l := hcnt
    rw [(Nat.dvd_iff_mod_eq_zero).1 h, Nat.mod_eq_of_lt hl.one_lt] at h1
    exact zero_ne_one h1
  have key := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X hX hnorm (cusp θ n K)
    hYchar hYs (cnt : ℤ) hz hndvd
  rw [hfun] at key
  exact key

end GlobalTheory.Shin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.RingContH.main
  | exact GlobalTheory.EtC.RingContH.main
  | (intros; apply GlobalTheory.EtC.RingContH.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    resG X h2 (resG X h1 z) = resG X (h2.trans h1) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_elim {X : Scheme.{0}} {U W : X.Opens} (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (o : Option (Fin d)) : resG X h (o.elim 1 t) = o.elim 1 (fun a => resG X h (t a)) := by
  cases o <;> simp

theorem relSnc_of_sameDiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ)
    (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec),
    RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  intro R _ X f d s L σ L' σ' hR hL' hS
  refine ⟨hL', fun x => ?_⟩
  obtain ⟨C, hxC⟩ := hR.chart x
  choose U a b ha hb v hxU hv using fun i => hS i x
  let V : X.Opens := C.U ⊓ ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hxV : x ∈ V := ⟨hxC, Set.mem_iInter.2 hxU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWC : W ≤ C.U := fun y hy => (hWV hy).1
  have hWU : ∀ i, W ≤ U i := fun i y hy => Set.mem_iInter.1 (hWV hy).2 i
  have hWca : ∀ i, W ≤ (L i).U (C.c i) ⊓ (L i).U (a i) := fun i => le_inf (hWC.trans (C.le i)) ((hWU i).trans (ha i))
  let G : ∀ i, Γ(X, W)ˣ := fun i => Units.map (resG X (hWca i)).toMonoidHom ((L i).g (C.c i) (a i)) *
    Units.map (resG X (hWU i)).toMonoidHom (v i)
  refine ⟨{
    U := W
    affine := hW
    t := fun j => resG X hWC (C.t j)
    etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f C.U W hWC d C.t C.affine hW C.etale
    c := b
    le := fun i => (hWU i).trans (hb i)
    e := C.e
    inj := C.inj
    u := fun i => Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹
    eq := fun i => ?_ }, hxW⟩

  have h1 := congrArg (resG X hWC) (C.eq i)
  rw [resG_resG', map_mul, resG_elim] at h1

  have h2 := congrArg (resG X (hWca i)) ((σ i).compat (C.c i) (a i))
  simp only [resG_resG', map_mul] at h2

  have h3 := congrArg (resG X (hWU i)) (hv i)
  simp only [resG_resG', map_mul] at h3
  have hG : (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * (G i : Γ(X, W)) = 1 := Units.inv_mul _
  have hG' : (G i : Γ(X, W)) = resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) *
      resG X (hWU i) (v i : Γ(X, U i)) := by
    simp only [G, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  show _ = ((Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * _
  rw [Units.val_mul, Units.coe_map]
  rw [hG'] at hG
  linear_combination (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h1 - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h2
    - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) * h3
    - resG X (le_trans (hWU i) (hb i)) ((σ' i).f (b i)) * hG

end GlobalTheory.LogPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_baseChange | exact GlobalTheory.LogPair.isEtCoord_baseChange | (intros; apply GlobalTheory.LogPair.isEtCoord_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.homFixedPullback_representable_glue : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (Ix : Type) (V : Ix → Scheme.{0}) (j : ∀ i, V i ⟶ S), (∀ i, IsOpenImmersion (j i)) → (∀ s : S, ∃ i, s ∈ Set.range (j i)) → (∀ i, ∃ (A' B' : Over (V i)) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A (j i) φA ∧ IsGrpPullback B' B (j i) φB ∧ QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | exact @GlobalTheory.EndLoc.HomGlue.homFixRep_glue | exact GlobalTheory.EndLoc.HomGlue.homFixRep_glue | (intros; apply GlobalTheory.EndLoc.HomGlue.homFixRep_glue <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechPer.isPer_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  intro A _ g L u x q q' hq hq'
  have h := ((GlobalTheory.T.cechDeRhamPeriods_linear A g L u).1 x x q q' hq hq').2
  rw [sub_self] at h
  exact sub_eq_zero.mp (GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero A g L u _ h)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_harrisTaylorModuliObject_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ o : Obj b N s, ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.HTPullEvery.exists_objMap | exact GlobalTheory.HTPullEvery.exists_objMap | (intros; apply GlobalTheory.HTPullEvery.exists_objMap <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.artinian_lift_axes_wedge_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.StepPrim.main | exact GlobalTheory.AbCoh.StepPrim.main | (intros; apply GlobalTheory.AbCoh.StepPrim.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.closed_fibre_pull_h1_abelian : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  first | exact @GlobalTheory.AbCohWedgeLift.wedgeO_fibre | exact GlobalTheory.AbCohWedgeLift.wedgeO_fibre | (intros; apply GlobalTheory.AbCohWedgeLift.wedgeO_fibre <;> assumption)
end
