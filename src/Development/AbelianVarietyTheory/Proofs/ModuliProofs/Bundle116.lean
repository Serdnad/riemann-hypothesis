module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaUniq

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_unit_of_local {R I : Type} [CommRing R] {v v' : I → R} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ, ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a)) :
    ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 ((Ideal.eq_top_iff_one _).1 hv)
  have key : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ,
      algebraMap R (Localization.AtPrime q) (c.sum fun i a => a * v' i) = u ∧ ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a) := fun q _ => by
    obtain ⟨u, hu⟩ := h q
    refine ⟨u, ?_, hu⟩
    have e := congrArg (algebraMap R (Localization.AtPrime q)) hc

    simp only [Finsupp.sum, map_sum, map_mul, map_one] at e ⊢
    simp only [hu, mul_left_comm _ (u : Localization.AtPrime q)]
    rw [← Finset.mul_sum, e, _root_.mul_one]
  have hu : IsUnit (c.sum fun i a => a * v' i) := by
    by_contra hn
    obtain ⟨q, hq, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
    obtain ⟨u, e, -⟩ := key q
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).1 (e ▸ u.isUnit) hm
  refine ⟨hu.unit, fun a => Module.eq_of_localization_maximal (R := R) (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap R (Localization.AtPrime q)) _ _ fun q _ => ?_⟩
  obtain ⟨u, e, e'⟩ := key q
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_mul, IsUnit.unit_spec, e, e']

theorem exists_ratio_base {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun Z r z J hJ => ?_⟩
  rw [← hc Z r z J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

variable {S : Scheme.{0}} {T : Over S}

theorem exists_unit_of_isGenSec_local {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} [IsLocalRing Γ(T.left, ⊤)]
    {th th' : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') :=
    (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu (isUnit_of_mul_isUnit_left h)
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩

theorem exists_unit_over (hG : GlobalFnsSt) (P : PolAV S) [IsLocalRing Γ(T.left, ⊤)] {k : ℕ} (hk : Odd k) {I : Type}
    {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) (H' : IsThetaPtOver P k x v') :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ i, v' i = u * v i := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨th', s₁', α', τ', U', s₂', w', u', hth', hα', hτ', hs₁', hU', hs₂', hw', hv'⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec_local hth' hth
  obtain ⟨c, hc⟩ := exists_ratio_base hL (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst hG P.isAb T) hα' hα
  obtain ⟨d, hd⟩ := exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun a => ⟨a, rfl⟩) hτ hτ'
  have key : ∀ i, w' i = (ρ * c * d : Γ(T.left, ⊤)ˣ) * w i := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    replace hJ : Good P.L z J := hJ
    have a₀ : tval (U' i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J = tval (U i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique hG P.isAb hL hk.pow _ _ (hU' i) (hU i)) _
    have a₁ : bval (b := 1) α' (lift (𝟙 T) (x i)).left z J =
        bval (b := 1) α (lift (𝟙 T) (x i)).left z J * gm (𝟙 T.left) z ⊤ c := by
      have := hc _ (lift (𝟙 T) (x i)).left z J hJ
      rw [lift_fst_left] at this
      exact this
    have a₂ := hd _ (𝟙 _) z J hJ
    have a₃ : sv P.A th' (lift (𝟙 T) (x i ^ k)).left z J =
        gs (𝟙 T.left) z ⊤ ρ * sv P.A th (lift (𝟙 T) (x i ^ k)).left z J := by
      have := ThetaAct.sv_smul (ρ : Γ(T.left, ⊤)) (SecM.ofSec P.A th) (lift (𝟙 T) (x i ^ k)).left z hJ
      rw [← hρ, lift_fst_left] at this
      exact this
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_mulPull hs₁ (𝟙 T) hJ (x i)
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    have c₁ := sv_act (hU' i).pt_eq (hs₂' i) (𝟙 T) hJ 1
    have c₂ := sv_mulPull hs₁' (𝟙 T) hJ (x i)
    have c₃ := sv_of_isValueAt (hw' i) (𝟙 T) hJ
    rw [Category.id_comp, _root_.mul_one] at b₁ c₁
    rw [Category.id_comp] at b₃ c₃ a₂
    rw [b₃, b₂] at b₁
    rw [c₃, c₂, a₀, a₁, a₃] at c₁
    simp only [Over.id_left] at b₁ c₁
    rw [a₂] at b₁
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    rw [c₁, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, map_mul, map_mul]
    simp only [Units.val_mul] at b₁ ⊢
    linear_combination (-(gm (𝟙 T.left) z ⊤ ρ).val * (gm (𝟙 T.left) z ⊤ c).val) * b₁
  refine ⟨u' * (ρ * c * d) * u⁻¹, fun i => ?_⟩
  rw [hv', hv, key, Units.val_mul _ u⁻¹, _root_.mul_assoc _ _ (u * w i), Units.inv_mul_cancel_left, Units.val_mul u',
    _root_.mul_assoc (u' : Γ(T.left, ⊤))]

theorem isThetaPtOver_of_local (P : PolAV S) {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S) {n : ℕ} {I : Type}
    {x : I → (Over.mk y ⟶ P.A)} {v : I → Γ((Over.mk y).left, ⊤)} (H : IsThetaPt P n x v) : IsThetaPtOver P n x v := by
  obtain ⟨V, hp, H'⟩ := H.2.2 (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  let h : Over.mk y ⟶ overRes (T := Over.mk y) ⊤ := Over.homMk (Sp R).topIso.inv (by
    show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ y = y
    rw [Scheme.toIso_inv_ι_assoc])
  have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
  have := isThetaPtOver_pull P H' h (overResι ⊤) hh
  convert this using 2 with a a
  · rw [← Category.assoc, hh, Category.id_comp]
  · have q := congrArg (fun q => q.left.appTop.hom (v a)) hh
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
    exact q.symm

theorem exists_unit_local (hG : GlobalFnsSt) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S)
    {v v' : Ix g (N' ^ 2) → R} (H : t.HasTh x v) (H' : t.HasTh x v') : ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  let e : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := e.symm.isLocalRing
  obtain ⟨u, hu⟩ := exists_unit_over hG t.pol H.1 (isThetaPtOver_of_local _ x H) (isThetaPtOver_of_local _ x H')
  refine ⟨Units.map e.toMonoidHom u, fun a => ?_⟩
  have q := (congrArg e (hu a)).trans (map_mul e _ _)
  exact (e.apply_symm_apply (v' a)).symm.trans (q.trans (congrArg (_ * ·) (e.apply_symm_apply (v a))))

end GlobalTheory.ThetaUniq

namespace GlobalTheory

theorem hasTh_unique_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a :=
  fun h₁ h₂ o _ g N' J b S s t R _ x v v' H H' hv => ThetaUniq.exists_unit_of_local hv fun q _ =>
    ThetaUniq.exists_unit_local h₁.globalFns t _
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v H)
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v' H')

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCoset

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_eq_smul {N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) {c : ZMod (N ^ 2)} (hc : n • c = 0) :
    ∃ d : ZMod (N ^ 2), N • (N / n) • d = c := by
  obtain ⟨m, rfl⟩ := hn
  have h₀ : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul hN)
  have : NeZero ((n * m) ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨e, rfl⟩ := ZMod.natCast_zmod_surjective c
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    show (n * m) ^ 2 = n * (n * m * m) by ring] at hc
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left h₀ hc
  refine ⟨d, ?_⟩
  rw [Nat.mul_div_cancel_left _ h₀, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem exists_label {G : Type} [CommGroup G] {r N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) (p : Fin r → G)
    (hp : ∀ i, p i ^ (N ^ 2) = 1)
    (hb : ∀ y : G, y ^ (N ^ 2) = 1 → ∃! c : Fin r → ZMod (N ^ 2), ∏ i, p i ^ (c i).val = y)
    (a : Fin r → ZMod (N ^ 2)) {z : G} (hz : z ^ n = 1) :
    ∃ c : Fin r → ZMod (N ^ 2), (∏ i, p i ^ ((a + (N / n) • c) i).val) ^ N = (∏ i, p i ^ (a i).val) ^ N * z := by
  have : NeZero (N ^ 2) := ⟨pow_ne_zero _ hN⟩
  let f : (Fin r → ZMod (N ^ 2)) → G := fun c => ∏ i, p i ^ (c i).val
  have f₀ : f 0 = 1 := Finset.prod_eq_one fun i _ => by rw [Pi.zero_apply, ZMod.val_zero, pow_zero]
  have fa : ∀ c d, f (c + d) = f c * f d := fun c d => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hp i), pow_add]
  have fs : ∀ (m : ℕ) c, f (m • c) = f c ^ m := fun m c => by
    induction m with
    | zero => rw [zero_smul, f₀, pow_zero]
    | succ m ih => rw [succ_nsmul, fa, ih, pow_succ]
  obtain ⟨c₀, hc₀, -⟩ := hb z (by
    obtain ⟨m, hm⟩ := hn.trans (dvd_pow_self N two_ne_zero)
    rw [hm, pow_mul, hz, one_pow])
  replace hc₀ : f c₀ = z := hc₀
  have h₁ : n • c₀ = 0 := (hb 1 (one_pow _)).unique ((fs n c₀).trans (by rw [hc₀, hz])) f₀
  choose d hd using fun i => exists_eq_smul hN hn (congrFun h₁ i)
  refine ⟨d, ?_⟩
  change f _ ^ N = f a ^ N * z
  rw [fa, mul_pow, ← fs N (_ • d), ← hc₀]
  exact congrArg (fun c => _ * f c) (funext hd)

variable {S : Scheme.{0}}

theorem ne_zero_of_isGenSec (hB : SecBaseChangeAnySt) (P : PolAV S) {K : Type} [Field K] (x : Sp K ⟶ S)
    {th : LB.Sec (LPow P.A P.L 1 (Over.mk x))} (H : IsGenSec P.A P.L 1 th) : SecM.ofSec P.A th ≠ 0 := by
  obtain ⟨V, hV, b, hb⟩ := hB S P 1 le_rfl (x (IsLocalRing.closedPoint K))
  obtain ⟨t, rfl⟩ : ∃ t : Sp K ⟶ (overRes (T := baseOver S) V).left, t ≫ (overRes (T := baseOver S) V).hom = x :=
    ⟨IsOpenImmersion.lift V.ι x (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨hli, -⟩ := hb K t (fun i => pullS P.A _ (homAt t) (b i)) fun i => isPullSec_pullS _ _ _ _
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have i : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact one_pos⟩
  intro h₀
  obtain ⟨r, hr⟩ := H (pullS P.A _ (homAt t) (b i))
  have e : SecM.ofSec P.A (pullS P.A _ (homAt t) (b i)) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  rw [h₀, smul_zero] at e
  exact hli.ne_zero i e

theorem exists_ne_zero_over (h₁ : Laws) (h₂ : Laws2) (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0) {I : Type} {y : I → (Over.mk x ⟶ P.A)}
    {v : I → Γ((Over.mk x).left, ⊤)} (H : IsThetaPtOver P k y v) (a : Over.mk x ⟶ P.A) :
    ∃ z : Over.mk x ⟶ P.A, z ^ n = 1 ∧ ∀ i, y i ^ k = a * z → v i ≠ 0 := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point h₁.goodPt h₁.polBaseChange P x hn hK th
    (ne_zero_of_isGenSec h₂.secBaseChangeAny P x hth) a
  refine ⟨z, hz, fun i hi h₀ => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk x).left ⟶ P.A.left => exists_chart hL (χ p)
  replace hJ : Good P.L p J := hJ
  have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ (y i)
  have b₃ := sv_of_isValueAt (hw i) (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [hv, Units.mul_right_eq_zero] at h₀
  rw [b₃, b₂, hi, h₀, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu p J hJ))).ne_zero b₁.symm

theorem coset_bot (h₁ : Laws) (h₂ : Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {v : Ix g (N' ^ 2) → K} (H : t.HasTh x v) (a : Ix g (N' ^ 2)) :
    ∃ c, v (a + (N' / n) • c) ≠ 0 := by
  have := t.ab.comm
  let π : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have hK : (n : K) ≠ 0 := by
    have := H.2.1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    rw [map_natCast] at this
    exact (isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) this).ne_zero
  have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨z, hz, hv⟩ := exists_ne_zero_over h₁ h₂ t.pol x hn hK (isThetaPtOver_of_subsingleton t.pol H)
    ((π ≫ t.lab a) ^ N')
  have e : ∀ c, π ≫ t.lab c = ∏ i, (π ≫ t.pt i) ^ (c i).val := fun c => by
    rw [TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
  obtain ⟨c, hc⟩ := exists_label (G := Over.mk x ⟶ t.A) H.1.pos.ne' hd (fun i => π ≫ t.pt i)
    (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
    (fun y hy => by simpa only [linComb, List.prod_ofFn] using t.bij K x y hy) a hz
  rw [← e, ← e] at hc
  refine ⟨c, fun h₀ => hv _ hc ?_⟩
  rw [h₀, map_zero]

end GlobalTheory.ThetaCoset

namespace GlobalTheory

theorem coset_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  intro h₁ h₂ o _ g N' J b S s t n R _ x v q hn hd H hq a
  let φ : R →+* AlgebraicClosure q.ResidueField :=
    (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)).comp (algebraMap R q.ResidueField)
  obtain ⟨c, hc⟩ := ThetaCoset.coset_bot h₁ h₂ t hn hd _ (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ φ x v H) a
  refine ⟨c, fun hm => hc ?_⟩
  rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.2 hm, map_zero]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaLevelAbelianScheme_const_over_dualNumbers : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  first | exact @GlobalTheory.ConstTheta.tMap_of_const | exact GlobalTheory.ConstTheta.tMap_of_const | (intros; apply GlobalTheory.ConstTheta.tMap_of_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormTorsion

theorem rel_prod {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hm : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) :
    ∀ (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ), (∀ i, R (y i) (c i)) →
      R (List.ofFn fun i => y i ^ a i).prod (∏ i, c i ^ a i) := by
  first
  | exact @_root_.GlobalTheory.RelationPowers.rel_prod_pow
  | exact _root_.GlobalTheory.RelationPowers.rel_prod_pow
  | (apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationPowers.rel_prod_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationPowers.rel_prod_pow ..)

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_linComb (hW : Out.WeilSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ) {n : ℕ}
    (y : Fin n → (Out.baseOver (Sp K) ⟶ P.A)) (z : Out.baseOver (Sp K) ⟶ P.A) (hz : z ^ k = 1)
    (e : Fin n → ℤ) (a : Fin n → ℕ) (h : ∀ i, Out.WeilIs P.A P.L k (y i) z (unitOn (ζ ^ e i))) :
    Out.WeilIs P.A P.L k (Out.linComb y a) z (unitOn (ζ ^ ∑ i, (a i : ℤ) * e i)) := by
  obtain ⟨hu, hm, -, -⟩ := hW (Sp K) P k (Out.baseOver (Sp K))
  have h1 : Out.WeilIs P.A P.L k 1 z 1 := by
    obtain ⟨c, hc, hc'⟩ := hu 1 z (one_pow k) hz
    have h2 := hm _ _ _ _ _ hc hc
    rw [_root_.mul_one] at h2
    have : c = 1 := mul_eq_left.1 (hc' _ h2)
    exact this ▸ hc
  have H := rel_prod (fun x (c : Kˣ) => Out.WeilIs P.A P.L k x z (unitOn c))
    (by
      have : unitOn (1 : Kˣ) = 1 := map_one _
      show Out.WeilIs P.A P.L k 1 z (unitOn 1)
      rw [this]; exact h1)
    (fun x x' c c' hx hx' => by
      have : unitOn (c * c') = unitOn c * unitOn c' := map_mul _ _ _
      show Out.WeilIs P.A P.L k (x * x') z (unitOn (c * c'))
      rw [this]; exact hm _ _ _ _ _ hx hx') n y (fun i => ζ ^ e i) a h
  have e' : ∏ i, (ζ ^ e i) ^ a i = ζ ^ ∑ i, (a i : ℤ) * e i := by
    have key : ∀ t : Finset (Fin n), ∏ i ∈ t, (ζ ^ e i) ^ a i = ζ ^ ∑ i ∈ t, (a i : ℤ) * e i := fun t => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add, ← zpow_natCast, ← zpow_mul,
          _root_.mul_comm (e b)]
    exact key _
  rw [← e']
  exact H

theorem weilIs_symm_zpow {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ)
    {x y : Out.baseOver (Sp K) ⟶ P.A} {e : ℤ} (h : Out.WeilIs P.A P.L k x y (unitOn (ζ ^ e))) :
    Out.WeilIs P.A P.L k y x (unitOn (ζ ^ (-e))) := by
  have : unitOn (ζ ^ (-e)) = (unitOn (ζ ^ e))⁻¹ := by
    rw [zpow_neg]; exact map_inv _ _
  rw [this]
  exact GlobalTheory.CommPairing.weilIs_symm P.isLB h

theorem injective_stdSymp (g k : ℕ) :
    Function.Injective (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k)) := by
  intro x x' h
  apply GlobalTheory.injective_toBilin'_stdSymp (R := ZMod k) g
  ext a
  have := congrFun h a
  simpa [Matrix.toBilin'_apply, Pi.single_apply] using this

theorem exists_matrix_form : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  intro hL hL2 g N k Mat
  classical
  refine ⟨fun i j => Function.invFun
    (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k))
    (fun a => -(((Out.stdSymp g a j : ℤ) : ZMod k) * N +
      (∑ i, Mat i a * -(∑ l, Mat l j * ((Out.stdSymp g l i : ℤ) : ZMod k))) * N)) i, ?_⟩
  intro K _ _ P pt ζ f s hk hζ hB hpt hf hM hs
  refine ⟨hB.pos, fun j => ?_⟩
  haveI : NeZero k := ⟨fun e => hk (by simp [e])⟩
  haveI := hs.isMonHom
  have tors : ∀ (u : P.A ⟶ P.A) [IsMonHom u] i, (pt i ≫ u) ^ k = 1 := fun u _ i => by
    have := congrArg (IsMonHom.monoidHom u _) (hB.pow_eq_one i)
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨c, hc, -⟩ := hB.existsUnique (tors s j)
  rw [← hc]
  congr 1
  funext i
  congr 1
  refine congrFun (?_ : c = _) i
  rw [← Function.leftInverse_invFun (injective_stdSymp g k) c]
  congr 1
  funext a
  have w₁ := weilIs_linComb hL.weil P k ζ pt (pt a) (hB.pow_eq_one a) _ (fun i => (c i).val) (fun i => hpt i a)
  rw [hc] at w₁
  have w₂ : ∀ i, Out.WeilIs P.A P.L k (pt i) (pt j ≫ f)
      (unitOn (ζ ^ (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i))) := fun i => by
    rw [hM.comp_eq j]
    exact weilIs_symm_zpow P k ζ (weilIs_linComb hL.weil P k ζ pt (pt i) (hB.pow_eq_one i) _ _ (fun l => hpt l i))
  have w₃ := weilIs_linComb hL.weil P k ζ pt _ (tors f j) _ (fun i => (Mat i a).val) w₂
  rw [← hM.comp_eq a] at w₃
  have eφ : (fun i : Fin 2 => ((![𝟙 P.A, f] : Fin 2 → (P.A ⟶ P.A)) i).left) = ![𝟙 P.A.left, f.left] := by
    funext i; fin_cases i <;> rfl
  have w₄ := GlobalTheory.T.weilPairing_of_polarisationForm_linComb hL hL2 K P (Fin 2) ![𝟙 P.A, f] ![(N : ℤ), (N : ℤ)] s k (pt a) (pt j)
    ![ζ ^ Out.stdSymp g a j, ζ ^ ∑ i, ((Mat i a).val : ℤ) * (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i)] hk
    (fun i => by
      fin_cases i
      · exact (inferInstance : IsMonHom (𝟙 P.A))
      · exact hf)
    (by rw [eφ]; exact hs) (hB.pow_eq_one a) (hB.pow_eq_one j)
    (fun i => by
      fin_cases i
      · show Out.WeilIs P.A P.L k (pt a ≫ 𝟙 _) (pt j ≫ 𝟙 _) _
        rw [Category.comp_id, Category.comp_id]
        exact hpt a j
      · exact w₃)
  rw [Fin.prod_univ_two] at w₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at w₄
  rw [← zpow_mul, ← zpow_mul, ← zpow_add] at w₄
  have w₅ := weilIs_symm_zpow P k ζ w₄
  have e := unitOn_inj (((hL.weil (Sp K) P k _).1 _ _ (tors s j) (hB.pow_eq_one a)).unique w₁ w₅)
  rw [← mul_inv_eq_one, ← zpow_sub, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at e
  push_cast at e
  simp only [ZMod.natCast_zmod_val] at e
  exact sub_eq_zero.1 e

end GlobalTheory.FormTorsion
end
