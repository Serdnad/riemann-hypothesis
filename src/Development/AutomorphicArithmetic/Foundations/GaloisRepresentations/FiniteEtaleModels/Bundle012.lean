module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle047
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle050
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle049
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle052
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ODownEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O


private theorem stepF_of (hGen : GenEx) (hComp : QComp) (hIso : QIso) (hCls : ClsEx) (hEta : TrEta) (hUnit : TrUnit)
    (hEps : EpsEx) (hDown : DownEx) : UpperTheory.Gal.FiniteEtaleModels.StepF := by
  intro p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle M₁ M₂ c₁ c₂ a₁ a₂ hN₁ hN₂ hM C₁ C₂ W
  obtain ⟨hM₁, hg₁⟩ := hN₁
  obtain ⟨hM₂, hg₂⟩ := hN₂
  obtain ⟨t, ht⟩ := hM
  have hM₁' : (M₁ : ℕ) = N₀ * κ * c₁ := hM₁
  have hM₂' : (M₂ : ℕ) = N₀ * c₂ := hM₂
  have hpos : 0 < (M₁ : ℕ) := by have := M₁.2.1; omega
  obtain ⟨h3, hcq₂, -, -, -⟩ := X₂.lev
  obtain ⟨-, hcq₁, -, -, -⟩ := X₁.lev
  have hN₀pos : 0 < N₀ := by omega
  have hd : N₀ ∣ N₀ * κ := dvd_mul_right N₀ κ
  obtain ⟨ε, hdvd, hεid⟩ := hEps (𝓞 D.F) 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos ht hle hg₁ hg₂
  obtain ⟨τ, m, hτ, hfin, het, hml⟩ :=
    hDown p D hSc.m1 hSc.a1 E gb w q r 𝔴 𝔫 S N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ ε hεid
  have hcart : IsGrpPullback (T.M M₁).univ.A (X₁.Y.univ.forget N₀ hd hcq₁).A C₁.j C₁.m.φ := C₁.m.cart
  have hsq : Geo.Tor.IsSquare C₁.m.φ C₁.m.φ₂ := C₁.m.sq
  have hact : ∀ x, Over.Hom.left ((T.M M₁).univ.act.act x) ≫ C₁.m.φ =
      C₁.m.φ ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).act.act x) := C₁.m.act
  have hpol : LBIso (T.M M₁).univ.P ((X₁.Y.univ.forget N₀ hd hcq₁).P.pull C₁.m.φ₂) := C₁.m.pol
  have heF : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((c₁ * κ) • y)) ≫ C₁.m.φ =
      C₁.j ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).eta y) := by
    intro y
    rw [Obj.forget_eta, Nat.mul_div_cancel_left κ hN₀pos, mul_smul]
    exact C₁.m.eta (κ • y)
  obtain ⟨nF, hnFφ⟩ : ∃ n : @QMap q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb _ _ X₁.Y.s (T.M M₁).s _ _
      (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) C₁.j (c₁ * κ), n.φ = C₁.m.φ :=
    ⟨⟨C₁.m.φ, C₁.m.φ₂, hcart, hsq, hact, hpol, heF⟩, rfl⟩
  obtain ⟨nA, hnA⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₁ : ℕ) N₀ (c₁ * κ) (T.M M₁).X X₁.Y.X
    X₂.Y.X (T.M M₁).s X₁.Y.s X₂.Y.s (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) X₂.Y.univ C₁.j τ).1 nF m
  obtain ⟨n₂, hn₂⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) N₀ c₂ (T.M M₂).X X₂.Y.X
    X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    (T.M M₁).X (T.M M₁).s W.o W.π W.φ C₂.m
  obtain ⟨hiso, hpol'⟩ :=
    hUnit p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans (one_mem _)
  have hex : ∀ (n : ℕ) (x : D.La), ∃ v ∈ LaHat D, (L.actG 1) (inAf D x) = inAf D x + n • v :=
    fun n x => ⟨0, zero_mem _, by simp⟩
  have heta₁ : ∀ y : D.La, (T.M M₁).univ.eta ((c₁ * κ) • y) ≫ W.ψ = W.o.eta (c₂ • y) :=
    fun y => hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans N₀ (c₁ * κ) c₂
      (by rw [hM₁']; ring) hM₂' y y (hex N₀ y)
  obtain ⟨nB, hnB⟩ := hIso q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) (M₁ : ℕ) N₀ c₂ (c₁ * κ) (T.M M₁).X
    X₂.Y.X (T.M M₁).s X₂.Y.s (T.M M₁).univ W.o X₂.Y.univ (W.π ≫ C₂.j) W.ψ hiso W.trans.1 W.trans.2.1 hpol'
    heta₁ n₂
  have heq : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) =
      (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y) := by
    intro y
    obtain ⟨z, hz⟩ := hdvd
    have e1 : (algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y = (algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y +
        (M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y) := by
      have h' : a₁ * ε = (t : 𝓞 D.F) * a₂ + ((M₁ : ℕ) : 𝓞 D.F) * z := by linear_combination hz
      rw [h', map_add (f := _), add_smul, map_mul (algebraMap (𝓞 D.F) D.O) ((M₁ : ℕ) : 𝓞 D.F) z, mul_smul,
        map_natCast, Nat.cast_smul_eq_nsmul]
    have h1 := (T.M M₁).univ.eta_add ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)
      ((M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y))
    have h2 := (T.M M₁).univ.eta_ker ((algebraMap (𝓞 D.F) D.O) z • y)
    rw [e1]
    refine (h1.trans ?_).symm
    exact (congrArg (_ * ·) h2).trans (_root_.mul_one _)
  have hkey : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) ≫ W.ψ =
      W.o.eta ((algebraMap (𝓞 D.F) D.O) a₂ • y) := by
    intro y
    have h' := hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans M₂ t 1 ht
      (_root_.mul_one _).symm ((algebraMap (𝓞 D.F) D.O) a₂ • y) ((algebraMap (𝓞 D.F) D.O) a₂ • y) (hex _ _)
    rw [map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul, h', one_smul]
  have lvA : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nA.φ =
      (C₁.j ≫ τ) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [heq, hnA, hnFφ, map_mul, mul_smul]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m.φ) (C₁.lv _))).trans
      ((Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) (hml y)).trans (Category.assoc _ _ _).symm))
  have lvB : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nB.φ =
      (W.π ≫ C₂.j) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [hnB, hn₂, ← Category.assoc, ← Over.comp_left, hkey, ← Category.assoc]
    exact (congrArg (· ≫ C₂.m.φ) (W.φ.eta _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (W.π ≫ ·) (C₂.lv y)).trans (Category.assoc _ _ _).symm))
  obtain ⟨CA, hCAj, hCAm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = C₁.j ≫ τ ∧ C.m.φ = nA.φ :=
    ⟨⟨C₁.j ≫ τ, (Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) hτ).trans C₁.ov), nA, lvA⟩, rfl, rfl⟩
  obtain ⟨CB, hCBj, hCBm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = W.π ≫ C₂.j ∧ C.m.φ = nB.φ :=
    ⟨⟨W.π ≫ C₂.j, (Category.assoc _ _ _).trans ((congrArg (W.π ≫ ·) C₂.ov).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap _) W.ov))), nB, lvB⟩, rfl, rfl⟩
  have hgen : IsGen ((t : 𝓞 D.F) * a₂) (M₁ : ℕ) 𝔟₂ := by
    rw [ht]
    exact (hGen (𝓞 D.F) 𝔟₂ M₂ (by have := M₂.2.1; omega)).2 a₂ t hg₂
  obtain ⟨hj, hφ⟩ := (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat (M₁ : ℕ) N₀
    (c₁ * κ) ((t : 𝓞 D.F) * a₂) 𝔟₂ (by rw [hM₁']; ring) hpos h3 hcq₂ hgen X₂.Y (T.M M₁).X (T.M M₁).s
    (T.M M₁).univ).2 CA CB
  rw [hCAj, hCBj] at hj
  rw [hCAm, hCBm, hnA, hnB, hn₂, hnFφ] at hφ
  exact ⟨⟨τ, hτ, m.φ, m.cart.1.w⟩, ⟨hj, hφ⟩, hfin, het, m.cart.1⟩

theorem stepF : UpperTheory.Gal.FiniteEtaleModels.StepF :=
  stepF_of UpperTheory.exists_generic_moduli_point UpperTheory.quotient_map_comp UpperTheory.quotient_moduli_iso
    (UpperTheory.isogeny_class_exists_of_quotient UpperTheory.quotient_moduli_object_exists UpperTheory.quotient_map_comp (UpperTheory.quotient_unique_of_comp UpperTheory.quotient_map_comp) (UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation))
    UpperTheory.trace_eta_identity (UpperTheory.trace_unit_of_pullback_multiplier UpperTheory.trace_pullback_identity UpperTheory.multiplier_is_unit) epsEx downEx

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.trEtaK_holds :
    TrEtaK := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ c₂ hM1 hM2 x y hxy
  obtain ⟨v, hv, hxv⟩ := hxy
  haveI : IsMonHom ψ := hT.1
  obtain ⟨hM13, hM1c⟩ := M₁.2
  obtain ⟨hM23, hM2c⟩ := M₂.2
  have hne1 : (M₁ : ℕ) ≠ 0 := by omega
  have hne2 : (M₂ : ℕ) ≠ 0 := by omega
  have hne1' := hne1
  have hne2' := hne2
  rw [hM1] at hne1 hM1c
  rw [hM2] at hne2 hM2c
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc10 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc20 : 0 < c₂ := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₂, rfl⟩ hM2c
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hM1c
  have hpc : ∀ (f : 𝟙_ (Over X) ⟶ o'.A) (k : ℕ), (f ^ k) ≫ ψ = (f ≫ ψ) ^ k := by
    intro f k
    induction k with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.one_comp]
    | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.mul_comp, ih]
  set a := o'.eta (c₁ • x) ≫ ψ with ha
  set b := o.eta (c₂ • y) with hb
  have haN : a ^ (M₁ : ℕ) = 1 := by
    rw [ha, ← hpc]
    exact (congrArg (· ≫ ψ) ((GObj.eta_nsmul o' _ _).symm.trans (GObj.eta_ker o' _))).trans
      (MonObj.one_comp ψ)
  have hbN : b ^ (M₂ : ℕ) = 1 := (GObj.eta_nsmul o _ _).symm.trans (GObj.eta_ker o _)
  have hunit : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : Γ(X, ⊤)) := by
    have hR : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : R) := by
      rw [← map_natCast (algebraMap ℚ R)]
      refine IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 _ ?_)
      exact_mod_cast Nat.mul_ne_zero hne1' hne2'
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  rw [← _root_.mul_inv_eq_one]
  have hpow : (a * b⁻¹) ^ ((M₁ : ℕ) * (M₂ : ℕ)) = 1 := by
    rw [mul_pow, _root_.inv_pow, _root_.pow_mul, haN, _root_.mul_comm (M₁ : ℕ), _root_.pow_mul, hbN,
      _root_.one_pow, _root_.one_pow, inv_one, _root_.mul_one]
  have := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points X o.A o.ab _ hunit _ (a * b⁻¹) hpow 1 ?_
  · simpa using this
  intro k _ _ ξ
  rw [_root_.pow_one, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_inv_eq_one]
  rw [show Over.homMk ξ _ = toUnit (Over.mk (ξ ≫ (𝟙_ (Over X)).hom)) from Subsingleton.elim _ _]
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap ((ξ ≫ (𝟙_ (Over X)).hom) ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 k (ξ ≫ (𝟙_ (Over X)).hom) β hβ
  have e1 : I'.ev (M₁ : ℕ) (c₁ • x) = I'.ev (n * κ) x :=
    (KerBy.ev_nsmul _ (I'.add _) c₁ x).trans
      ((congrArg (fun m => I'.ev m x ^ c₁) hM1).trans (I'.tower (n * κ) c₁ (Nat.mul_pos hn0 hκ0) hc10 x))
  have e2 : I''.ev (M₂ : ℕ) (c₂ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) c₂ y).trans
      ((congrArg (fun m => I''.ev m y ^ c₂) hM2).trans (I''.tower n c₂ hn0 hc20 y))
  have e3 : I''.ev (n * κ) (κ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) κ y).trans (I''.tower n κ hn0 hκ0 y)
  have e4 : I'.ev (n * κ) x ≫ ψ = I''.ev (n * κ) (κ • y) :=
    (hev (n * κ) (Nat.mul_pos hn0 hκ0) hnκc x (κ • y)).mpr
      ⟨v, hv, by rw [GlobalTheory.HeckeApprox.inAf_nsmul]; exact hxv⟩
  rw [ha, hb, ← Category.assoc]
  exact (congrArg (· ≫ ψ) ((h1 _).trans e1)).trans (e4.trans (e3.trans (e2.symm.trans (h2 _).symm)))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem natCast_gcd_mem {A : Type} [CommRing A] {I : Ideal A} {x y : ℕ} (hx : (x : A) ∈ I) (hy : (y : A) ∈ I) :
    ((Nat.gcd x y : ℕ) : A) ∈ I := by
  have h : ((Nat.gcd x y : ℕ) : A) = (x : A) * (Nat.gcdA x y : A) + (y : A) * (Nat.gcdB x y : A) := by
    have := congrArg (Int.cast : ℤ → A) (Nat.gcd_eq_gcd_ab x y)
    push_cast at this
    exact this
  rw [h]
  exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_right _ hy)

private theorem natCast_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) :
    (N : A) ∈ 𝔞 := by
  unfold IsGen at h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h] at hN
  have hle : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞 := Ideal.mul_le_right
  exact hle hN

theorem UpperTheory.Gal.FiniteEtaleModels.numSplit_holds :
    NumSplit := by
  intro A _ _ _ 𝔟₁ 𝔟₂ M₁ M₂ Q a₁ a₂ hM₁ hM₂ hle h₁ h₂ hQ
  have hgM₁ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgM₂ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₂ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgQ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ Q := Nat.gcd_dvd_left _ _
  have hg_mem : ((Nat.gcd Q (Nat.gcd M₁ M₂) : ℕ) : A) ∈ 𝔟₂ :=
    natCast_gcd_mem (hle hQ) (natCast_gcd_mem (hle (natCast_mem_of_isGen h₁)) (natCast_mem_of_isGen h₂))
  have hgpos : 0 < Nat.gcd Q (Nat.gcd M₁ M₂) := Nat.pos_of_dvd_of_pos hgM₂ hM₂
  generalize Nat.gcd Q (Nat.gcd M₁ M₂) = g at hgM₁ hgM₂ hgQ hg_mem hgpos
  obtain ⟨m₁, hm₁⟩ := hgM₁
  obtain ⟨m₂, hm₂⟩ := hgM₂
  have h1 : a₂ * (g : A) ∈ Ideal.span {(M₂ : A)} := by
    rw [← h₂]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a₂)) hg_mem
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hg0 : (g : A) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hm₂pos : 0 < m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · subst h; omega
    · exact h
  have hm₂0 : (m₂ : A) ≠ 0 := by exact_mod_cast hm₂pos.ne'
  have hM₂c : (M₂ : A) = (g : A) * (m₂ : A) := by rw [hm₂]; push_cast; ring
  have ha : a₂ = (m₂ : A) * c := by
    apply mul_right_cancel₀ hg0
    rw [hc, hM₂c]; ring
  refine ⟨g, m₁, m₂, c, hgQ, hm₁, hm₂, ha, ?_⟩
  unfold IsGen at h₂ ⊢
  have hs : Ideal.span {(m₂ : A)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm₂0
  apply mul_left_cancel₀ hs
  calc Ideal.span {(m₂ : A)} * ((Ideal.span {c} ⊔ Ideal.span {(g : A)}) * 𝔟₂)
      = (Ideal.span {(m₂ : A)} * Ideal.span {c} ⊔ Ideal.span {(m₂ : A)} * Ideal.span {(g : A)}) * 𝔟₂ := by
        rw [← _root_.mul_assoc, Ideal.mul_sup]
    _ = (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) * 𝔟₂ := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, ← ha, hM₂c,
          _root_.mul_comm (m₂ : A)]
    _ = Ideal.span {(M₂ : A)} := h₂
    _ = Ideal.span {(m₂ : A)} * Ideal.span {(g : A)} := by
        rw [Ideal.span_singleton_mul_span_singleton, hM₂c, _root_.mul_comm]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
end

section

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open GlobalTheory.HeckeApprox (inAf_sub inAf_nsmul inAf_mem inAfH)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem betaH_holds : BetaH := by
  intro p _ D G L h κ n hn hnp hnκ hI hκ
  set u := L.actG h with hu
  set ui := L.actG h⁻¹ with hui
  have hinv : ∀ v, ui (u v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, u (ui v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hIu : ∀ v ∈ LaHat D, u v ∈ LaHat D := hI
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • ui with hh₀
  have h₀app : ∀ v, h₀ v = κ • ui v := fun v => rfl
  have h₀mem : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', e⟩ := hκ v hv
    rw [h₀app, ← map_nsmul, ← e, hinv]
    exact hv'
  have h₀u : ∀ v, u (h₀ v) = κ • v := by
    intro v
    rw [h₀app, map_nsmul, hinv']
  have h₀c : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := by
    intro c v
    rw [h₀app, h₀app, hui, actG_actAf, map_nsmul]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ h₀mem
  obtain ⟨k, m, hkm⟩ : ∃ k : ℕ, ∃ m : ℤ, (κ : ℤ) * k = 1 + n * m := by
    have hc : Nat.Coprime κ n := hnκ.symm
    have e := Nat.gcd_eq_gcd_ab κ n
    rw [hc.gcd_eq_one] at e
    have hn' : (0:ℤ) < n := by exact_mod_cast hn
    refine ⟨(Nat.gcdA κ n % n).toNat, -(Nat.gcdB κ n) - κ * (Nat.gcdA κ n / n), ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne'), Int.emod_def]
    push_cast at e
    linear_combination -e
  have hsm : ∀ {M : Type} [AddCommGroup M] (y : M), (κ * k) • y = y + n • (m • y) := by
    intro M _ y
    have : (((κ * k : ℕ) : ℤ)) • y = ((1:ℤ) + n * m) • y := by push_cast; rw [hkm]
    rw [natCast_zsmul] at this
    rw [this, add_smul, one_smul, mul_smul, natCast_zsmul]
  have key : ∀ x, ∃ v ∈ LaHat D, u (inAf D (k • φ n x)) = inAf D x + n • v := by
    intro x
    obtain ⟨w, hw, e⟩ := hφ n hn hnp x
    refine ⟨m • inAf D x - k • u w, ?_, ?_⟩
    · exact sub_mem (zsmul_mem (inAf_mem D x) _) (nsmul_mem (hIu w hw) _)
    · have e2 : inAf D (φ n x) = h₀ (inAf D x) - n • w := by rw [e]; abel
      rw [inAf_nsmul, e2, map_nsmul, map_sub, h₀u, map_nsmul, smul_sub, smul_smul, mul_comm k κ, hsm,
        smul_sub n, smul_comm n k (u w)]
      abel
  have hg : ∀ x, (k • φ n) x = k • φ n x := fun x => rfl
  refine ⟨k • φ n, ?_, ?_, ?_, ?_⟩
  · intro c x
    rw [hg, hg]
    obtain ⟨w1, hw1, e1⟩ := hφ n hn hnp (c • x)
    obtain ⟨w2, hw2, e2⟩ := hφ n hn hnp x
    have a1 : inAf D (φ n (c • x)) = h₀ (inAf D (c • x)) - n • w1 := by rw [e1]; abel
    have a2 : inAf D (φ n x) = h₀ (inAf D x) - n • w2 := by rw [e2]; abel
    have hE : inAf D (k • φ n (c • x) - c • (k • φ n x)) = n • (k • (actAf D c w2 - w1)) := by
      rw [inAf_sub, inAf_nsmul, ← actAf_inAf, inAf_nsmul, map_nsmul, a1, a2, ← actAf_inAf, h₀c, map_sub,
        map_nsmul, smul_sub, smul_sub, smul_sub, smul_sub, smul_comm k n w1, smul_comm k n (actAf D c w2)]
      abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _
      (nsmul_mem (sub_mem (actAf_mem_laHat D c hw2) hw1) k) hE
    exact ⟨z, by rw [← hz]; abel⟩
  · intro x z hxz
    rw [hg] at hxz
    obtain ⟨v, hv, e⟩ := key x
    rw [hxz, inAf_nsmul, map_nsmul] at e
    have hx : inAf D x = n • (u (inAf D z) - v) := by rw [smul_sub, e]; abel
    exact LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x n hn hnp _ (sub_mem (hIu _ (inAf_mem D z)) hv) hx
  · intro x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (u (inAf D x)) (hIu _ (inAf_mem D x))
    obtain ⟨v, hv, ev⟩ := key y
    have hd : inAf D (k • φ n y) - inAf D x = ui (n • (v - w)) := by
      rw [← hinv (inAf D (k • φ n y) - inAf D x), map_sub, ev, e]
      congr 1
      rw [smul_sub]
      abel
    have h1 : inAf D (κ • (k • φ n y - x)) = n • h₀ (v - w) := by
      rw [inAf_nsmul, inAf_sub, hd, map_nsmul, h₀app, smul_comm κ n]
    obtain ⟨z1, hz1⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ (h₀mem _ (sub_mem hv hw)) h1
    refine ⟨y, k • z1 - m • (k • φ n y - x), ?_⟩
    have ht := hsm (k • φ n y - x)
    rw [mul_comm κ k, ← smul_smul, hz1] at ht
    rw [hg, smul_sub, smul_comm n k z1, ht]
    abel
  · intro x
    rw [hg]
    exact key x

end UpperTheory.Gal.FiniteEtaleModels
end
end
