module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GDeep

theorem big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem exists_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s →
    ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ →
      ∀ m₀ : ℕ, ∃ D : Deep X₁ ε₁, m₀ ≤ D.m := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ hε₁ m₀
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j, hk, hB, hj, big⟩ :=
    big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 ((X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1) ^ 2)
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  have hunK : IsUnit ((((X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 : ℕ)) : X₁.o₁) := by
    push_cast
    exact ((hun1.pow _).mul ((hun1.pow _).pow _)).pow _
  obtain ⟨o₂, Ω₂, _, _, _, _, _, κ, fd, gal, hκ, hc, R, h, P, ψ, ze, hfg, hfr, hh, hPg, hpb, hlb, ⟨lev⟩⟩ :=
    GlobalTheory.T.exists_symplectic_level_eighth_power_galois_ext X₁ _ (by have := hℓp.pos; positivity) hunK
  have hS := GlobalTheory.T.lineBundleSymmetryHypothesis_of_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  obtain ⟨S₂, ρ₂, hR, φ, -, hN₂, hr₂, hg₂, hpb₂, hlb₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk hj hun2 hS lev
  set h' : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hh'
  have hval : ∀ a, ((h' a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hpb' : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap h') (φ ≫ ψ) := by
    rw [hh', ← spMap_comp']
    exact hpb₂.comp hpb
  have hlb' : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp' hlb φ rfl)
  obtain ⟨ε₂, hε₂, hεc⟩ := GlobalTheory.T.diagonalEndOfEighthPower_of_polAV_pullback F W X₁.ρ.P ρ₂.P X₁.u (spMap h') (φ ≫ ψ) ε₁ hε₁ hpb' hlb'
  have hsharp : SharpOver F W ρ₂.P (spMap h' ≫ X₁.u) := by
    obtain ⟨c, hc₁, pr, hpr, hun, hLc, -⟩ := hε₂
    exact ⟨c, hc₁, pr, hpr, hun, hLc⟩
  have key : spMap S₂.R.val.toRingHom ≫ spMap h' = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [spMap_comp', spMap_comp']
    congr 1
    ext a
    exact hval a
  have hgen : ∀ w, (spMap S₂.R.val.toRingHom ≫ spMap h' ≫ X₁.u) w ∈ genericPoints F.X := by
    intro w
    rw [← Category.assoc, key, Category.assoc, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.T.exists_normalisation_model_finite_extension X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap S₂.R.val.toRingHom ≫ (spMap h' ≫ X₁.u) ≫ i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, Category.assoc, ← Category.assoc (spMap S₂.R.val.toRingHom),
      key, Category.assoc]
  have hbase : spMap S₂.R.val.toRingHom ≫ (spMap h' ≫ X₁.u) ≫ F.s =
      spMap ((algebraMap o₂ Ω₂).comp (κ.comp X₁.κ)) := by
    rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, X₁.base, spMap_comp', ← RingHom.comp_assoc, ← hc]
  have hbig : S₂.Big := big j le_rfl o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : Setup F W i := Setup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap h' ≫ X₁.u) hsharp hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
    X₁.one_le X₁.three_le X₁.odd X₁.z X₁.proj X₁.normalZ X₁.imm X₁.thetaSetup_structureMap_comp X₁.dense X₁.e8 X₁.thetaInt (κ.comp X₁.κ) hbase
  have hle : X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1 ≤ X₁.ρ.n ^ k :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 hB
  have hpos : 1 ≤ X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := Nat.one_le_pow _ _ (by omega)
  have hm₁ : 1 ≤ max m₀ 1 := le_max_right _ _
  have hm₀ : m₀ ≤ X₁.ρ.n ^ k :=
    (le_max_left m₀ 1).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans hle)
  have hdm : X₁.S.r * X₁.S.N ∣ X₁.ρ.n ^ k := by
    rw [hL₁]
    refine pow_dvd_pow _ ((Nat.pow_le_pow_iff_right hℓ2).1 ?_)
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans hle
  have hd₂ : X₁.S.r * X₁.S.N ∣ S₂.r * S₂.N := by
    rw [hN₂]
    exact (hdm.trans (dvd_pow_self _ two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨lab, hsame, hrange⟩ :=
    GlobalTheory.T.exists_thetaLabel_common_generic_fibre_pullback X₁.S S₂ X₁.ρ ρ₂ ε₁ ε₂ (algebraMap X₁.Ω₁ Ω₂) h' (φ ≫ ψ) hval hpb' hlb' hεc hd₂
  exact ⟨Deep.mk X₂ ε₂ hε₂ fd gal X₂.projM q hq hqgen rfl (X₁.ρ.n ^ k) hN₂ hdm lab hsame hrange, hm₀⟩

end GlobalTheory.Poinc.GDeep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GeomCore

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in
theorem core : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x ν, yy x = QuotientAddGroup.mk ν → yy' x = QuotientAddGroup.mk (θ ν)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  intro g n F W Z i X ε hd p _ z c yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩ := GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → (∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have ord : ∀ m pk (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
      x ^ m = 1 := fun m pk x h => by
    obtain ⟨w, hw⟩ := u.U.ext
    exact (h w hw).1
  have hqe : ∀ χ, l'.q (e χ) = l.q χ := fun χ => by
    have h2 := (hψ χ _).1 (l.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ →
      l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := (tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := (tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')
    have e1 := l.yy_eq b pk x hpk hx
    have e2 := l'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  have hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X,
      CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ))) := fun m hm E χ => by
    obtain ⟨pk, rfl⟩ := GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ
    obtain ⟨x, hQ⟩ := (tors m hm).2 pk
    obtain ⟨w, x', hw, hwa, hwa', hx'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)
    obtain ⟨pk', hQ'⟩ := (tors' m hm).1 x' hx'
    have hmon := GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E
    obtain ⟨x₂, hx₂φ, hx₂⟩ := GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)
    obtain ⟨pk₂, hQ₂⟩ := (tors m hm).1 x₂ hx₂
    obtain ⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂
    obtain ⟨pk₂', hQ₂'⟩ := (tors' m hm).1 x₂' hx₂'
    have hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left := by
      have := hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])
      rw [← hw₂a', ← hwa']
      simpa only [Category.assoc] using this
    have c1 := hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ
    have c2 := hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂
    have t1 := htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'
    have t2 := htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'
    refine ⟨pk₂.y, c1, ?_⟩
    exact cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2))
      (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have h1 := hq χ
    have h2 := hq' (e χ)
    rw [hqe] at h2
    have hs := c.scale_pos
    have h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hs.ne' (h2.symm.trans h1)
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (l'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))
  · intro m hm E v
    obtain ⟨χ, rfl⟩ := j.surjective v
    obtain ⟨χ₂, c1, c2⟩ := hcom m hm E χ
    have c3 : CongMod m (j.symm (matAct E (j χ))) χ₂ := by
      simpa using cm_symm (cm_map j.symm.toAddMonoidHom c1)
    have c4 := cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2
    simpa [matAct] using c4

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := core

end GlobalTheory.GeomCore
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_uCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  intro R _ _ _ hR A hA
  obtain ⟨n, hn, hno, hnu⟩ := GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase R hR
  obtain ⟨k, j, hk, hj, hbig⟩ := GlobalTheory.T.exists_exponents_thetaSystem_big_odd_prime A.g n hn hno
  have hmu : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : R) := by
    push_cast; exact ((hnu.pow _).mul ((hnu.pow _).pow _)).pow _
  obtain ⟨R₁, _, _, _, ρ, A₁, a, ζ, lev, hfin, hfib, hg, hS⟩ :=
    GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base R hR A hA _ (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hn.ne_zero) (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))))) hmu
  haveI : CharZero R₁ := ⟨fun x y h => by
    have := hR.2
    exact Nat.cast_injective (hfin.2.1 (by simpa using h))⟩
  have hnu₁ : IsUnit (n : R₁) := by simpa using hnu.map ρ
  obtain ⟨o, Ω, _, _, _, _, S, ρS, b, e, φ, hSg, hSN, hSr, hb, hcart, hlb⟩ :=
    GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField R₁ A₁ hS n k j hn hno hk hj hnu₁ ζ lev
  have hB : S.Big := hbig o Ω S (hSg.trans hg) hSN hSr
  obtain ⟨J₀, _, t₀, ht₀, hfin'⟩ := GlobalTheory.T.exists_tuple_thetaConstant_ratios_generate_field o Ω S
  obtain ⟨M, U₀, EE, hO, -, -, ⟨Z⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρS hB J₀ t₀ ht₀ hfin'
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_uniformised_cover_pullback_semiAbelian_model R₁ o Ω S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  subst hC
  exact ⟨R₁, _, _, _, ρ, C, a, hfin, hfib⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.exists_rechart_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ w : X₁.M.Z, X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ X₁.M.ringOn U) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ X₁.M.ringOn U) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε' ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u' = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ _hg1 _hn3 _hodd _himm he8 _hti _hproj ε₁ hε₁ w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hU₀i, hu₀⟩ := GlobalTheory.T.exists_affineChart_lift_to_moduli_scheme g n F W Z i X₁ w hw
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain g n F W he8 (X₁.M.ringOn U₀) u₀
  have hN : 1 ≤ X₁.S.N := by have := X₁.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₀, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart X₁.o₁ X₁.Ω₁ X₁.M U₀ w hU₀a hwU₀ P₁ X₁.S.N hN
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hsh : SharpOver F W P' (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) :=
    GlobalTheory.T.sharpOver_of_polarized_pullback g n F W _ _ P₁ P' u₀ _ φ hP₁ hφ hφL
  have hsp : spMap (X₁.M.ringOn U).val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom =
      spMap (X₁.M.ringOn U₀).val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have hcomp : spMap X₁.S.R.val.toRingHom ≫ X₁.u =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) := by
    rw [← Category.assoc, hsp, hu₀]
  obtain ⟨ε', hε', P₀, a, a', ε₀, ha, ha', hL, hL', hε₀⟩ :=
    GlobalTheory.T.exists_common_genericFibre_diagonalEnd_eighthPower g n F W X₁.S.R (X₁.M.ringOn U) X₁.Ω₁ X₁.S.R.val.toRingHom (X₁.M.ringOn U).val.toRingHom X₁.ρ.P X₁.u ε₁ P' _
      hε₁ hsh hcomp
  have hg' : P'.g = X₁.S.g :=
    (GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ P' P₀ _ a' ha').symm.trans ((GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ X₁.ρ.P P₀ _ a ha).trans X₁.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart X₁.o₁ X₁.Ω₁ X₁.M U hUa hne X₁.normal X₁.S.R X₁.ρ.P P' P₀ _ a a' ha ha' hL hL' X₁.ρ.hypS
  obtain ⟨pt', hadd, hbij, hweil, hmatch⟩ := GlobalTheory.T.polarized_abelian_variety_pullback_affine_open g n F W Z i X₁ U P' P₀ a a' hUa hne ha ha' hL hL'
  have fg : (X₁.M.ringOn U).FG := GlobalTheory.T.ringOn_affineOpen_finitelyGenerated X₁.o₁ X₁.Ω₁ X₁.M U hUa hne
  have frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ε'', hSame, hi₀, hD⟩ :=
    GlobalTheory.T.thetaSetup_extends_normal_affineChart_after_rescaling g n F W Z i X₁ U ε₁ fg frac _ P' ε' P₀ a a' ε₀ pt' th b hUa hne hε₁ hε' ha ha' hL hL' hε₀ hg' hyp hadd hbij
      hweil hmatch hth hb
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', ε'', _, hUa, hwU, fun w' hw' => hU₀i w' (hUU₀ hw'), hSame, hi₀, hD,
    hcomp.symm⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_labels_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  intro R _ _ _ hB D A lab n hOne hGal R₁ _ _ _ ρ hρ D₁ hD A₁ a hfib hn
  obtain ⟨hD⟩ := hD
  obtain ⟨_, em, lab₁, hc, hOne₁, hrel⟩ :=
    exists_labels_finExt_emb R hB D A lab hOne R₁ ρ hρ D₁ hD A₁ a hfib
  exact ⟨lab₁, hOne₁, LabBC.galEqN_of_rel ρ hρ D D₁ hD A A₁ a hfib lab n hn hGal em lab₁ hc hrel⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorData_tau_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  first | exact @GlobalTheory.TensBimult.main | exact GlobalTheory.TensBimult.main | (intros; apply GlobalTheory.TensBimult.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.GLift.transport | exact GlobalTheory.Poinc.GLift.transport | (intros; apply GlobalTheory.Poinc.GLift.transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_principally_polarised_power_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  first | exact @GlobalTheory.Mum.TensPow.exists_pow_data_polAV | exact GlobalTheory.Mum.TensPow.exists_pow_data_polAV | (intros; apply GlobalTheory.Mum.TensPow.exists_pow_data_polAV <;> assumption)
end
