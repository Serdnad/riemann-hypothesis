module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.galOfKer_holds :
    GalOfKer := by
  intro S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj
  haveI := hA
  haveI := hB
  obtain ⟨-, haF, haE, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ
  obtain ⟨-, -, hbE, hbS⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : IsProper B.hom := IsAbelianScheme.proper
  haveI : Smooth B.hom := IsAbelianScheme.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom
  haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF
  haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE
  haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE
  haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS
  haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left
  refine ⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left,
    Surjective.of_comp ψ'.left ψ.left, ?_⟩
  · simp [Hecke.PullHecke.transl_one]
  · intro a c
    simp [Hecke.PullHecke.transl_mul]
  · intro a
    have ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ := by
      have e := Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)
      rw [Category.id_comp] at e
      rw [e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]
    rw [← Over.comp_left, ht]
  · intro K _ _ y y' hyy
    have hz : y' ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ]
      simp only [← Category.assoc, hyy]
    let Y0 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    let Y1 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y' hz
    have hY : Y1 ≫ ψ = Y0 ≫ ψ := by
      ext
      simp [Y0, Y1, hyy]
    have hg : (Y1 * Y0⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]
    obtain ⟨g₀, hg₀H, hgg₀⟩ := hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg
    have key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔
        toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹) := by
      intro h
      have e := Hecke.Comp.comp_transl Y0 h
      constructor
      · intro hh
        have e' : Y0 ≫ Hecke.transl h = Y1 := by
          ext
          simpa [Y0, Y1] using hh
        rw [e'] at e
        rw [e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
      · intro hh
        rw [hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul] at e
        have := congrArg Over.Hom.left e
        simpa [Y0, Y1] using this
    refine ⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩
    rintro ⟨h, hH⟩ hh
    have h3 := (key h).mp hh
    apply Subtype.ext
    have h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_of (hD : DictP) (hX : SysExt) (hE : TrEtaK) (hK : TrKer) (hG : GalOfKer) (hH : BetaH) (hB : BetaLat) (hN : NumSplit)
    (hC : CoreA) (hE' : TrEta) (hBk : TrBack) (hQ : QComp) : StepA := by
  intro p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle h hI hκ M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W
  obtain ⟨e₁, g₁⟩ : M₁.1 = N₀ * κ * c₁ ∧ IsGen a₁ M₁.1 𝔟₁ := hn₁
  obtain ⟨e₂, g₂⟩ : M₂.1 = N₀ * c₂ ∧ IsGen a₂ M₂.1 𝔟₂ := hn₂
  obtain ⟨l3, lq, lp, -, e, he⟩ := X₁.lev
  obtain ⟨l3', lq', -, -, -⟩ := X₂.lev
  have h₁ : 0 < M₁.1 := lt_of_lt_of_le (by norm_num) M₁.2.1
  have h₂ : 0 < M₂.1 := lt_of_lt_of_le (by norm_num) M₂.2.1
  have hNκ : 0 < N₀ * κ := by omega
  have hκ0 : 0 < κ := Nat.pos_of_mul_pos_left hNκ
  have hκp : κ.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lp
  have hκq : κ.Coprime q := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lq
  have hqe : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟₁ := by
    rw [Nat.cast_pow]
    exact he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  obtain ⟨hmon, hlin, -, ⟨c', hc'p, hpol, hmult⟩, -⟩ := id W.trans
  obtain ⟨f, u, c, hcc, hsys, hrel⟩ := hD p D G L h κ c' hκ0 hκp hc'p hI hκ hmult
  obtain ⟨f', u', hsys', hff⟩ := hX D.toG p Fact.out f u c c' κ hcc hc'p hsys
  let F : D.La →+ D.La := f' (N₀ * κ)
  have hF : ∀ x, ∃ v ∈ LaHat D, κ • L.actG h⁻¹ (inAf D x) = inAf D (F x) + (N₀ * κ) • v := fun x => by
    obtain ⟨v, hv, ev⟩ := hrel _ hNκ lp x
    obtain ⟨z, hz⟩ : ∃ z : D.La, F x = f (N₀ * κ) x + (N₀ * κ) • z := hff _ hNκ lp x
    refine ⟨v - inAf D z, sub_mem hv (GlobalTheory.HeckeApprox.inAf_mem D z), ?_⟩
    rw [ev, hz, GlobalTheory.HeckeApprox.inAf_add, GlobalTheory.HeckeApprox.inAf_nsmul, smul_sub]
    abel
  have heta : ∀ y : D.La, (T.M M₁).univ.eta (c₁ • F y) ≫ W.ψ = W.o.eta (c₂ • y) := fun y => by
    refine hE p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ c₂ e₁ e₂ (F y) y ?_
    obtain ⟨v, hv, ev⟩ := hF y
    refine ⟨-L.actG h v, neg_mem (hI v hv), ?_⟩
    have := congrArg (L.actG h) ev
    rw [map_nsmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_add (f := _), map_nsmul] at this
    rw [this, smul_neg]
    abel
  obtain ⟨n, m₁, m₂, a, hnQ, en₁, en₂, ea, ga⟩ := hN (𝓞 D.F) 𝔟₁ 𝔟₂ M₁.1 M₂.1 (q ^ e) a₁ a₂ h₁ h₂ hle g₁ g₂ hqe
  have hn0 : 0 < n := Nat.pos_of_mul_pos_right (en₁ ▸ h₁)
  have hm0 : 0 < m₁ := Nat.pos_of_mul_pos_left (en₁ ▸ h₁)
  obtain ⟨g, gl, gi, gs, gr⟩ := hH p D G L h κ n hn0 (Nat.Coprime.coprime_dvd_left ⟨m₁, en₁⟩ M₁.2.2)
    (Nat.Coprime.coprime_dvd_left hnQ (hκq.symm.pow_left e)) hI hκ
  obtain ⟨ρ, hρ, hρe⟩ := hB q (datAt S.atq S.sp) 𝔟₁ 𝔟₂ n m₁ a₁ a hn0 hm0 hle (en₁ ▸ g₁) ga g gl gi gs
  have hlv : ∀ y : D.La, (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) ≫ W.ψ =
      W.o.eta (algebraMap (𝓞 D.F) D.O a₂ • y) := fun y => by
    obtain ⟨z, hz⟩ : ∃ z : D.La, m₁ • g (algebraMap (𝓞 D.F) D.O a • y) = algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + (n * m₁) • z := hρe y
    have t₁ := hE' p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans n m₁ m₂ en₁ en₂ _ _ (gr (algebraMap (𝓞 D.F) D.O a • y))
    have t₂ : (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + M₁.1 • z) =
        (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) :=
      ((T.M M₁).univ.eta_add _ _).trans (by
        rw [show (T.M M₁).univ.eta (M₁.1 • z : D.La) = 1 from (T.M M₁).univ.eta_ker z, _root_.mul_one])
    have t₃ : algebraMap (𝓞 D.F) D.O a₂ • y = m₂ • algebraMap (𝓞 D.F) D.O a • y := by
      rw [ea, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [hz, ← en₁] at t₁
    rw [t₃, ← t₂]
    exact t₁
  obtain ⟨ψ', hm', b₁, b₂⟩ := hBk p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans κ hκp hκ
  have hdiv : κ ^ 2 / c = c' := by
    have hc0 : 0 < c := Nat.pos_of_mul_pos_right (hcc ▸ pow_pos hκ0 2)
    rw [← hcc, Nat.mul_div_cancel_left _ hc0]
  let o₁ := ob (D := datAt S.atq S.sp) (gb := gb) S.mat (T.M M₁).univ (N₀ * κ) c₁ e₁ h₁
  have hA : IsTranslA (D := datAt S.atq S.sp) F c κ N₀ o₁ (ob (D := datAt S.atq S.sp) (gb := gb) S.mat W.o N₀ c₂ e₂ h₂) W.ψ := by
    obtain ⟨hfin, hfree⟩ := HeckeAd.heckeSubA_finite_free S.b F κ N₀ hκ0 (by omega) hκq lq' _ o₁
    refine ⟨hmon, hlin, fun y => (heta y).symm, ?_, hdiv ▸ hpol, ⟨c', hcc.symm⟩⟩
    haveI := hmon
    refine hG _ _ _ (T.M M₁).univ.ab W.o.ab W.ψ ψ' κ hmon hm' b₁ b₂ (Hecke.Comp.isUnit_natCast S.b ((T.M M₁).s ≫ spMap (algebraMap (Ow w) E)) κ hκq) _ hfin ?_ hfree ?_
    · rintro _ ⟨x, rfl⟩
      show (T.M M₁).univ.eta (c₁ • N₀ • F x) ≫ W.ψ = 1
      rw [← map_nsmul, heta, smul_smul, mul_comm c₂, ← e₂]
      exact W.o.eta_ker x
    · intro Ω _ _ z y₀ hy₀
      obtain ⟨x, hx⟩ := hK p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ e₁ hκ F hF Ω z y₀ hy₀ (by
        haveI := hm'
        rw [← Category.comp_id y₀, ← MonObj.comp_pow, ← b₁, ← Category.assoc, hy₀, MonObj.one_comp])
      exact ⟨_, HeckeAd.mem_heckeSubA o₁ F N₀ x, hx⟩
  obtain ⟨n', hn'⟩ := (hQ q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ _ _ _ _ _ _ (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C₂.m
  let C₂' : Cls (D := datAt S.atq S.sp) (gb := gb) X₂.Y (algebraMap (Ow w) E) W.o c₂ a₂ :=
    { j := W.π ≫ C₂.j
      ov := by rw [Category.assoc, C₂.ov, ← Category.assoc, W.ov]
      m := n'
      lv := fun y => by
        rw [hn', ← Category.assoc]
        erw [W.φ.eta]
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (C₂.lv y) }
  haveI : Smooth X₁.M.s := X₁.M.smooth.smooth
  haveI := X₁.et
  haveI : IsLocallyNoetherian X₁.Y.X := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ X₁.M.s)
  obtain ⟨t, Φ, ht, hΦ, j₁, j₂⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat N₀ κ c 𝔟₁ 𝔟₂ X₁.Y X₂.Y this l3' lq' hκq ⟨c', hcc.symm⟩ hle
    ⟨e, hqe⟩ f' u' (hsys'.mono q) ρ hρ _ _ M₁.1 M₂.1 c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ g₂ (T.M M₁).univ W.o W.ψ hA hlv C₁ C₂'
  exact ⟨⟨t, ht, Φ, hΦ⟩, j₁, j₂.trans (by rw [← hn'])⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem keyC {A B V U E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {χ : B ⟶ V} {mv : V ⟶ U} {m : U ⟶ E₂} {ψ₂ : A ⟶ V} {c : A ⟶ E₁}
    {ψ₁ : E₁ ⟶ U} {n₁ : B ⟶ U} {n₂ : B ⟶ E₂} (h₁ : n₁ = χ ≫ mv) (h₂ : n₂ = n₁ ≫ m) (h₃ : ψ ≫ χ = ψ₂) (h₄ : ψ₂ ≫ mv = c ≫ ψ₁) :
    ψ ≫ n₂ = c ≫ ψ₁ ≫ m := by
  rw [h₂, h₁, ← Category.assoc, ← Category.assoc, h₃, h₄, Category.assoc]

private theorem keyL {X A B U Y₁ Y₂ E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {n : B ⟶ E₂} {c : A ⟶ E₁} {ψ₁ : E₁ ⟶ U} {m : U ⟶ E₂}
    {x : X ⟶ A} {j : X ⟶ Y₁} {t : Y₁ ⟶ Y₂} {l₁ : Y₁ ⟶ E₁} {l₂ : Y₂ ⟶ E₂} (h₁ : ψ ≫ n = c ≫ ψ₁ ≫ m) (h₂ : x ≫ c = j ≫ l₁)
    (h₃ : (l₁ ≫ ψ₁) ≫ m = t ≫ l₂) : (x ≫ ψ) ≫ n = ((𝟙 X ≫ j) ≫ t) ≫ l₂ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.id_comp, Category.assoc, Category.assoc, ← h₃, Category.assoc]

theorem coreA_of (hP : TrPull) (hS : TrSame) (hL : LevTr) (hR : LevRe) (hC : ClsEx) : CoreA := by
  intro q _ D R R' _ _ _ b gb β hm N κ c 𝔟₁ 𝔟₂ E₁ E₂ hno hN hNq hκ hck hle hq f u hs ρ hρ X s M₁ M₂ c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ hg o₁ o₂ ψ
    hA hlv C₁ C₂
  have hc : c.Coprime q := Nat.Coprime.coprime_dvd_left hck (hκ.pow_left 2)
  obtain ⟨u', ψ₁, hT⟩ := GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base q D R b f u c κ N hN hNq hc hκ hck hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 E₁.X E₁.s E₁.univ
  have hl := hR q D R b N 𝔟₁ 𝔟₂ ρ hle hρ _ _ u' _ (hL q D R b _ c κ N 𝔟₁ hκ hq _ _ E₁.univ u' ψ₁ E₁.lv hT E₁.isLev)
  obtain ⟨t, ⟨ht, m, hmlv⟩, -⟩ := E₂.rep E₁.X E₁.s u' _ hl
  let m₁ : ObjMap (ob hm o₁ (N * κ) c₁ e₁ h₁) E₁.univ C₁.j :=
    ⟨C₁.m.φ, C₁.m.φ₂, C₁.m.cart, C₁.m.sq, C₁.m.act, C₁.m.pol, C₁.m.eta⟩
  have hv : ∃ v : Obj b N (s ≫ spMap β), Nonempty (ObjMap v u' C₁.j) := by
    rw [← C₁.ov]; exact GlobalTheory.HTPull.exists_objMap_pull q D R b N _ _ E₁.s C₁.j u'
  obtain ⟨v, ⟨mv⟩⟩ := hv
  obtain ⟨ψ₂, hT₂, hψ₂⟩ := hP q D R b _ c κ N _ _ _ _ C₁.j E₁.univ u' ψ₁ _ v m₁ mv hT
  obtain ⟨χ, hχ⟩ := hS q D R b _ c κ N _ _ (ob hm o₁ (N * κ) c₁ e₁ h₁) (ob hm o₂ N c₂ e₂ h₂) v ψ ψ₂ hA hT₂
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ χ mv
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ n₁ m
  have key : ψ.left ≫ n₂.φ = C₁.m.φ ≫ ψ₁.left ≫ m.φ := keyC hn₁ hn₂ hχ hψ₂
  let B : Cls E₂ β o₂ c₂ a₂ :=
    { j := (𝟙 X ≫ C₁.j) ≫ t
      ov := by rw [Category.assoc, ht, Category.id_comp, C₁.ov]
      m := ⟨n₂.φ, n₂.φ₂, n₂.cart, n₂.sq, n₂.act, n₂.pol, n₂.eta⟩
      lv := fun y => by
        show (o₂.eta _).left ≫ n₂.φ = _
        rw [← hlv y]
        exact keyL key (C₁.lv (ρ y)) (hmlv y) }
  obtain ⟨ej, eφ⟩ := (hC q D R R' b gb β hm M₂ N c₂ a₂ 𝔟₂ e₂ h₂ hN hNq hg E₂ X s o₂).2 B C₂
  refine ⟨t, ψ₁.left ≫ m.φ, ht, ?_, ?_, ?_⟩
  · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]
  · rw [← ej]; show _ = (𝟙 X ≫ C₁.j) ≫ t; rw [Category.id_comp]
  · rw [← eφ]; exact key.symm

end UpperTheory.Gal.FiniteEtaleModels
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

private theorem gen_facts {A : Type} [CommRing A] {a : A} {n : ℕ} {𝔟 : Ideal A} (G : IsGen a n 𝔟) :
    (n : A) ∈ 𝔟 ∧ ∀ c ∈ 𝔟, ∃ d, c * a = (n : A) * d := by
  have G' : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 = Ideal.span {(n : A)} := G
  have hle : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 ≤ 𝔟 :=
    Ideal.mul_le.mpr fun x _ y hy => 𝔟.mul_mem_left x hy
  have hN : (n : A) ∈ 𝔟 := by
    apply hle
    rw [G']
    exact Ideal.mem_span_singleton_self _
  refine ⟨hN, fun c hc => ?_⟩
  have hmem : a * c ∈ (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 :=
    Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
  rw [G', Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [mul_comm]; exact hd⟩

private theorem reindex_lattice_of_ideals {A O L : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup L] [Module O L]
    (cancel : ∀ k : ℕ, 0 < k → ∀ x y : L, k • x = k • y → x = y)
    (𝔟₁ 𝔟₂ : Ideal A) (W₁ W₂ : Submodule O L) (n m₁ : ℕ) (a₁ a₂ : A) (hn : 0 < n) (hm : 0 < m₁) (hle : 𝔟₁ ≤ 𝔟₂)
    (hn2 : (n : A) ∈ 𝔟₂) (hc2 : ∀ c ∈ 𝔟₂, ∃ d, c * a₂ = n * d)
    (BaseTypeSubspacesMapOntoBothSides : ∀ y : L, (∃ z, algebraMap A O a₁ • y = (n * m₁) • z) ↔ y ∈ W₁)
    (PairingFactorsThroughPeriods : ∀ x : L, (∀ c ∈ 𝔟₁, ∃ z, algebraMap A O c • x = (n * m₁) • z) →
      ∃ y z, x = algebraMap A O a₁ • y + (n * m₁) • z)
    (ProjectionSandwichLength : ∀ y : L, (∃ z, algebraMap A O a₂ • y = n • z) ↔ y ∈ W₂)
    (DegreeKernelLowerBound : ∀ x : L, (∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • x = n • z) → ∃ y z, x = algebraMap A O a₂ • y + n • z)
    (g : L →+ L) (h1 : ∀ (a : O) x, ∃ z, g (a • x) = a • g x + n • z)
    (h2 : ∀ x z, g x = n • z → ∃ v, x = n • v) (h3 : ∀ x, ∃ y z, g y = x + n • z) :
    ∃ β : L → L, (∀ x y, β (x + y) - (β x + β y) ∈ W₁) ∧ (∀ (c : O) x, β (c • x) - c • β x ∈ W₁) ∧
      (∀ y, β y ∈ W₁ ↔ y ∈ W₂) ∧
      (∀ x, (∀ c ∈ 𝔟₂, algebraMap A O c • x ∈ W₁) → ∃ y, x - β y ∈ W₁) ∧
      ∀ y, ∃ z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • β y + (n * m₁) • z := by
  have hnm : ∀ v : L, m₁ • (n • v) = (n * m₁) • v := by
    intro v
    rw [mul_comm, mul_smul]
  have memW1 : ∀ v : L, (∃ z, algebraMap A O a₁ • v = (n * m₁) • z) → v ∈ W₁ := fun v h => (BaseTypeSubspacesMapOntoBothSides v).mp h
  have ex : ∀ y : L, ∃ y' z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • y' + (n * m₁) • z := by
    intro y
    apply PairingFactorsThroughPeriods
    intro c hc
    obtain ⟨d, hd⟩ := hc2 c (hle hc)
    obtain ⟨z, hz⟩ := h1 (algebraMap A O c) (algebraMap A O a₂ • y)
    have e1 : algebraMap A O c • algebraMap A O a₂ • y = n • (algebraMap A O d • y) := by
      rw [smul_smul, ← map_mul, hd, map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]
    refine ⟨g (algebraMap A O d • y) - z, ?_⟩
    rw [e1, map_nsmul] at hz
    rw [smul_comm (algebraMap A O c) m₁, eq_sub_of_add_eq hz.symm, mul_comm n m₁, mul_smul]
    simp only [smul_sub]
  choose β z0 hβ using ex
  refine ⟨β, ?_, ?_, ?_, ?_, fun y => ⟨z0 y, hβ y⟩⟩
  · intro x y
    apply memW1
    refine ⟨z0 x + z0 y - z0 (x + y), ?_⟩
    have h := hβ (x + y)
    rw [smul_add, map_add (f := _), smul_add, hβ x, hβ y] at h
    rw [smul_sub, smul_add, eq_sub_of_add_eq h.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro c x
    apply memW1
    obtain ⟨w, hw⟩ := h1 c (algebraMap A O a₂ • x)
    have hc := hβ (c • x)
    have comm1 : algebraMap A O a₂ • c • x = c • algebraMap A O a₂ • x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    have comm2 : algebraMap A O a₁ • c • β x = c • algebraMap A O a₁ • β x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    refine ⟨w - z0 (c • x) + c • z0 x, ?_⟩
    rw [comm1, hw, smul_add, hnm] at hc
    have hx' : c • (m₁ • g (algebraMap A O a₂ • x)) = c • (algebraMap A O a₁ • β x + (n * m₁) • z0 x) := by
      rw [hβ x]
    rw [smul_add, smul_comm c m₁, smul_comm c (n * m₁)] at hx'
    rw [hx'] at hc
    rw [smul_sub, comm2, eq_sub_of_add_eq hc.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides (β y)).mpr hy
      have h := hβ y
      rw [hz, ← smul_add, ← hnm] at h
      have e := cancel m₁ hm _ _ h
      obtain ⟨v, hv⟩ := h2 _ _ e
      exact (ProjectionSandwichLength y).mp ⟨v, hv⟩
    · intro hy
      obtain ⟨v, hv⟩ := (ProjectionSandwichLength y).mpr hy
      apply memW1
      refine ⟨g v - z0 y, ?_⟩
      have h := hβ y
      rw [hv, map_nsmul, hnm] at h
      rw [smul_sub, eq_sub_of_add_eq h.symm]
  · intro x hx
    have hu : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • (algebraMap A O a₁ • x) = (n * m₁) • z := by
      intro c hc
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides _).mpr (hx c hc)
      exact ⟨z, by rw [smul_smul, ← Algebra.commutes a₁, ← smul_smul, hz]⟩
    obtain ⟨w, hw⟩ := hu _ hn2
    rw [map_natCast, Nat.cast_smul_eq_nsmul, mul_smul] at hw
    have hu1 := cancel n hn _ _ hw
    have hw2 : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • w = n • z := by
      intro c hc
      obtain ⟨z, hz⟩ := hu c hc
      rw [hu1, smul_comm (algebraMap A O c) m₁ w, ← hnm] at hz
      exact ⟨z, cancel m₁ hm _ _ hz⟩
    obtain ⟨y0, z0', hy0⟩ := DegreeKernelLowerBound w hw2
    obtain ⟨y1, z1, hy1⟩ := h3 y0
    obtain ⟨z2, hz2⟩ := h1 (algebraMap A O a₂) y1
    refine ⟨y1, memW1 _ ⟨z0' - algebraMap A O a₂ • z1 - z2 + z0 y1, ?_⟩⟩
    have hb := hβ y1
    rw [hz2, hy1] at hb
    simp only [smul_add] at hb
    rw [smul_comm (algebraMap A O a₂) n z1] at hb
    simp only [hnm] at hb
    rw [smul_sub, hu1, hy0, smul_add, hnm, eq_sub_of_add_eq hb.symm]
    simp only [smul_add, smul_sub]
    abel

theorem UpperTheory.Gal.FiniteEtaleModels.betaLat_holds :
    LatGen → BetaLat := by
  intro hL q _ D 𝔟₁ 𝔟₂ n m₁ a₁ a₂ hn hm hle G1 G2 g h1 h2 h3
  have cancel : ∀ k : ℕ, 0 < k → ∀ x y : D.La, k • x = k • y → x = y := by
    intro k hk x y h
    haveI := D.freeLa
    have h' : (k : ℤ) • (x - y) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (by exact_mod_cast hk.ne')
    · exact sub_eq_zero.mp h0
  obtain ⟨BaseTypeSubspacesMapOntoBothSides, PairingFactorsThroughPeriods⟩ := hL q D a₁ (n * m₁) 𝔟₁ (Nat.mul_pos hn hm) G1
  obtain ⟨ProjectionSandwichLength, DegreeKernelLowerBound⟩ := hL q D a₂ n 𝔟₂ hn G2
  obtain ⟨hn2, hc2⟩ := gen_facts G2
  obtain ⟨β, hadd, hlin, hker, honto, hmain⟩ :=
    reindex_lattice_of_ideals cancel 𝔟₁ 𝔟₂ (wSub D 𝔟₁ 1) (wSub D 𝔟₂ 1) n m₁ a₁ a₂ hn hm hle hn2 hc2
      BaseTypeSubspacesMapOntoBothSides PairingFactorsThroughPeriods ProjectionSandwichLength DegreeKernelLowerBound g h1 h2 h3
  exact ⟨β, ⟨hadd, hlin, hker, honto⟩, hmain⟩
end
