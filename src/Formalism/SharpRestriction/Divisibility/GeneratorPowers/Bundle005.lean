module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Mathlib.Tactic.ENatToNat
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Nakayama
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  apply GlobalTheory.RigNorm.glue_units <;> assumption

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem etSpan_holds : ETSpanStatement := by
  intro E _ _ Y _ _ _ R' hR' r y z hgen a
  set X : Submodule (𝓞 E) Y := Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b) with hX

  have hdec : ∀ a : Y, ∃ x ∈ X, ∃ t : Y, a = x + R' • t := by
    intro a
    obtain ⟨u, hu, t, rfl⟩ := hgen a
    have hspan : Submodule.span (𝓞 E) (Set.range y) ≤
        X ⊔ LinearMap.range (R' • LinearMap.id : Y →ₗ[𝓞 E] Y) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_sup]
      refine ⟨y b + R' • z b, Submodule.subset_span ⟨b, rfl⟩, R' • (-z b), ⟨-z b, rfl⟩, ?_⟩
      rw [smul_neg, add_neg_cancel_right]
    obtain ⟨x, hx, w, ⟨t', rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hspan hu)
    refine ⟨x, hx, t' + t, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add, add_assoc]

  let Xz : Submodule ℤ Y := X.restrictScalars ℤ
  let I : Ideal ℤ := Ideal.span {(R' : ℤ)}
  have hfg : (⊤ : Submodule ℤ (Y ⧸ Xz)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule ℤ (Y ⧸ Xz)) ≤ I • ⊤ := by
    intro m _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective Xz m
    obtain ⟨x, hx, t, rfl⟩ := hdec b
    have hx' : Submodule.Quotient.mk (p := Xz) x = 0 :=
      (Submodule.Quotient.mk_eq_zero Xz).2 ((Submodule.restrictScalars_mem ℤ X x).2 hx)
    rw [Submodule.Quotient.mk_add, hx', zero_add, Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul ℤ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hfg hle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton, zero_sub, dvd_neg] at hs1
    have h1 : ((R' : ℤ)) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg R') hs1
    omega
  have hsa : s • a ∈ X := by
    have h0 : s • Submodule.Quotient.mk (p := Xz) a = 0 := hs _ Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.restrictScalars_mem ℤ X _).1 h0
  refine ⟨s.natAbs, Int.natAbs_pos.2 hs0, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rcases Int.natAbs_eq s with h | h
  · rw [← h]
    exact hsa
  · have : ((s.natAbs : ℤ)) = -s := by omega
    rw [this, neg_smul]
    exact X.neg_mem hsa

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Jet

variable {S ι : Type} [CommRing S]

theorem jet_exists_nil (m : ℕ) (a : Jet S ι m) : ∃ c : S, IsNilpotent (a - algebraMap S (Jet S ι m) c) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.constantCoeff p, m + 1, ?_⟩
  have h : Ideal.Quotient.mk (orig S ι ^ (m + 1)) p - algebraMap S (Jet S ι m) (MvPolynomial.constantCoeff p) =
      Ideal.Quotient.mk _ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
    rw [map_sub]
    rfl
  rw [h, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_const_mem_orig p) _

instance jet_isLocalRing [IsLocalRing S] (m : ℕ) : IsLocalRing (Jet S ι m) := by
  have : Nontrivial (Jet S ι m) := (jetAug : Jet S ι m →ₐ[S] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨c, hc⟩ := jet_exists_nil (ι := ι) m a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
  · left
    have := hc.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    simpa using this
  · right
    have := hc.neg.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    convert this using 1
    rw [map_sub, map_one]
    ring

end Jet

section Gen

variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

def cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res (le_inf le_rfl (by rw [h0]; exact le_top) : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j0)
    ((LB.LinComb L φ ε).g j j0)⟩

theorem cgen_isGen (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) :
    (cgen L φ ε j0 h0).IsGen := fun i j => unit_ext fun y hy => by
  have h0y : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j0 := by rw [h0]; trivial
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((gm_linComb L φ ε (𝟙 _) y i j0 hy.1 h0y).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.2 _).trans (gm_linComb L φ ε (𝟙 _) y j j0 hy.2 h0y))))).symm
  exact (trF_trans hL φ ε (𝟙 _) y hy.1 hy.2 h0y).symm

def cv {Z : Scheme.{0}} (i0 : L.ι) (z : Z) (J : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U i0) (L.g (J ψ) i0)

theorem val_cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i0 : L.ι) (h0 : LB.wchart L φ (fun _ => i0) = ⊤) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val (cgen L φ ε (fun _ => i0) h0) r z J = ∏ k, cv L i0 z J (r ≫ φ k) ^ ε k :=
  (gm_res r z _ (hJ.mem φ r) _).trans (gm_linComb L φ ε r z _ _ (hJ.mem φ r) (by rw [h0]; trivial))

theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ u * val t' r z J := by
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ hU => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [h U hU]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ ht
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (s.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e1 := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of s r z J PEmpty.elim (fun k => k.elim)] at e1
  have e2 := (gm_res r z le trivial (s.s PEmpty.elim)).trans e1
  exact mul_inv_eq_iff_eq_mul.1 e2.symm

def divLin (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) :
    LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε fun k => -ε' k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩ :
    LB.wchart L (Sum.elim φ φ') j ≤ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr))
    (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem gm_divLC (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (p q : (K → L.ι) × (K' → L.ι)) (y : Y) (hp : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p)
    (hq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q) :
    gm (𝟙 Y) y _ ((LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).g p q) =
      trF φ ε (𝟙 Y) y p.1 q.1 * (trF φ' ε' (𝟙 Y) y p.2 q.2)⁻¹ := by
  have hpq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q := ⟨hp, hq⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hpq _).trans
    (gm_linComb L φ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)) ((map_inv _ _).trans (congrArg _ ((gm_res _ y _ hpq _).trans
      (gm_linComb L φ' ε' (𝟙 _) y p.2 q.2 hp.2 hq.2)))))

theorem divLin_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) (hw : w.IsGen) :
    (divLin L φ ε φ' ε' w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (i ∘ Sum.inl, i ∘ Sum.inr) ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 Y) y _ hij _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (i ∘ Sum.inl, i ∘ Sum.inr)
    (j ∘ Sum.inl, j ∘ Sum.inr))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hij _))))
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (hw'.trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm
  refine congrArg₂ (· * ·) ((gm_divLC L φ ε φ' ε' _ _ y hi hj).trans ?_) rfl
  refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2).symm
  rw [Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Gen

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem exists_pullSec (a : ℤ) {T T' : Over S0} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s', IsPullSec A L a h hh s s' := by
  have hl : ∀ j, (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := fun j => chart_le_res A L h hh a j
  have hc : h.left ≫ (snd T A).left = (snd T' A).left := by
    rw [← Over.comp_left, hh]
  refine ⟨⟨fun j => ((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j)), ?_⟩,
    fun j => rfl⟩
  intro j j'
  apply fn_ext
  intro y hy
  have v : ∀ j, y ∈ (LPow A L a T').U j →
      gs (𝟙 _) y _ (((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ h.left) y ((LPow A L a T).U j) (s.f j) :=
    fun j hj => (gs_res _ y _ hj _).trans (gs_pull _ h.left y _ (hl j hj) _)
  refine ((gs_res (𝟙 _) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y j j' hy.1 hy.2))) ((gs_res (𝟙 _) y _ hy _).trans (v j' hy.2)))).symm)
  refine (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ h.left) y
    (hl j hy.1) (hl j' hy.2)).trans ?_
  simp only [trF, Category.assoc, hc]
  try rfl

theorem exists_value (hL : L.IsLB) (a : ℤ) {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))) (hτ : τ.IsGen) :
    ∃ v, IsValueAt A L a s z τ v := by
  have hpz : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left]
    simp [ptSecT]
  obtain ⟨w, hw⟩ : ∃ w : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j),
      ∀ j, w j = (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) *
        (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from ((τ.s j)⁻¹).val) := ⟨_, fun _ => rfl⟩
  have loc : ∀ j x, x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      gs (𝟙 _) x _ (w j) = gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) * ((gm (𝟙 _) x _ (τ.s j))⁻¹).val := by
    intro j x hx
    rw [hw j]
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) x (val_le A L z j) hx _).trans
      (gs_pull (𝟙 _) (ptSecT A z).left x _ (val_le A L z j hx) _)) ?_)
    exact (gs_unit (𝟙 _) x _ hx ((τ.s j)⁻¹)).trans (congrArg Units.val (map_inv _ _))
  have hcompat : TopCat.Presheaf.IsCompatible T.left.sheaf.obj (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) w := by
    intro j j'
    apply fn_ext
    intro x hx
    change gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_left).op).hom (w j)) =
      gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_right).op).hom (w j'))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, loc j x hx.1, loc j' x hx.2]
    rw [show gs (𝟙 _ ≫ (ptSecT A z).left) x ((LPow A L a T).U j) (s.f j) = _ from
      sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ x
        (val_le A L z j hx.1) (val_le A L z j' hx.2)]
    rw [show gm (𝟙 _) x ((LB.LinComb L (fun _ : Fin 1 => z.left) fun _ => a).U j) (τ.s j) = _ from
      gen_trans hτ (𝟙 _) x hx.1 hx.2]
    have ht : trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _ ≫ (ptSecT A z).left) x j j' =
        trF (L := L) (fun _ : Fin 1 => z.left) (fun _ => a) (𝟙 _) x j j' := by
      simp only [trF, Category.assoc, hpz]
    rw [ht, mul_inv_rev, Units.val_mul]
    have key : ∀ (t G : (T.left.presheaf.stalk x)ˣ) (P : T.left.presheaf.stalk x),
        (t : T.left.presheaf.stalk x) * P * (((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) *
          ((t⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) =
          P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) := by
      intro t G P
      linear_combination (P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) * Units.mul_inv t
    exact key _ _ _
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => z.left) j := by
    intro x _
    have hx : z.left x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨v, hv, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.left.sheaf
    (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) ⊤ (fun j => homOfLE le_top) hcov w hcompat
  refine ⟨v, fun j => ?_⟩
  have e : (T.left.presheaf.map (homOfLE le_top).op).hom v = w j := hv j
  have key : ∀ (R : Type) [CommRing R] (p : R) (t : Rˣ), p = p * ((t⁻¹ : Rˣ) : R) * (t : R) := by
    intro R _ p t
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [e, hw j]
  exact key _ _ (τ.s j)

theorem value_stalk (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by
  have h1 := congrArg (gs r y (LB.wchart L (fun _ : Fin 1 => z.left) j)) (hv j)
  refine ((gs_pull r (ptSecT A z).left y _ (val_le A L z j hy) _).symm.trans
    ((gs_res r y (val_le A L z j) hy _).symm.trans h1)).trans ?_
  exact (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y le_top hy v) (gs_unit r y _ hy _))

theorem pullSec_stalk (a : ℤ) {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a h hh s s') {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (y : Z) (j : Fin 1 → L.ι) (hy : r y ∈ (LPow A L a T').U j) :
    gs r y _ (s'.f j) = gs (r ≫ h.left) y _ (s.f j) := by
  rw [hs j]
  exact (gs_res r y (chart_le_res A L h hh a j) hy _).trans (gs_pull r h.left y _ (chart_le_res A L h hh a j hy) _)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end
