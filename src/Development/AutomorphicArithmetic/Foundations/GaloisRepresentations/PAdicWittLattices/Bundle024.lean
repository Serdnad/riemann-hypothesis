module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

theorem pTatePull : TatePull := by
  unfold TatePull
  intro p _ D R _ _ gb S S' s s' f N o o' m k _ t
  have hT := HeckeRestrict.tate_pullback D.toG o.A o'.A o.act o'.act o.P o'.P o.isLB o'.isLB f m.φ m.φ₂
    m.cart m.sq m.act m.pol k t
  have hpt : ∀ y, (toUnit (Over.mk (t ≫ f)) ≫ o.eta y).left = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left, m.eta y]
    exact Category.assoc _ _ _
  have hpt' : ∀ y, (toUnit (Over.mk t) ≫ o'.eta y).left ≫ m.φ = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left]
    exact Category.assoc _ _ _
  refine ⟨fun I => ?_, fun I' => ?_⟩
  · obtain ⟨I', hI'⟩ := hT.2 I
    refine ⟨I', fun hI y => ?_, fun n x => (hI' n x).symm⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hpt', ← hpt, hI y, hI' N y]
    · rw [Over.w, Over.w]
  · obtain ⟨I, hI⟩ := hT.1 I'
    refine ⟨I, fun hI' y => ?_, fun n x => (hI n x).symm⟩
    apply Over.OverMorphism.ext
    rw [hpt, hI N y, ← hI' y, hpt']

end UpperTheory.Gal.G3
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem comp_pow_overScheme_grpObj {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    f ≫ x ^ n = (f ≫ x) ^ n := MonObj.comp_pow x n f

private theorem pow_comp_monHom_overScheme_grpObj {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem pt_transfer {N' N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {o : GObj gb N' s} {o₁ o₂ : GObj gb N s}
    {ψ₁ : o.A ⟶ o₁.A} {ψ₂ : o.A ⟶ o₂.A} {ψ' : o₁.A ⟶ o.A} {d : ℕ} (hψ' : IsMonHom ψ')
    (hd : ψ₁ ≫ ψ' = (𝟙 o.A) ^ d) (hdp : d.Coprime p) {h : G.GAf} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (J₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t) (J₂ : UpperTheory.Gal.Int.Geo.TIso o₂ t)
    (H₁ : Rel L I J₁ ψ₁ h) (H₂ : Rel L I J₂ ψ₂ h) (a : Over.mk t ⟶ o.A) (y : D.La)
    (ha : a ≫ ψ₁ = J₁.ev N y) : a ≫ ψ₂ = J₂.ev N y := by
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hn : 0 < N * d := Nat.mul_pos hN hd0
  have hnp : (N * d).Coprime p := Nat.Coprime.mul_left hNp hdp
  have h1 : (a ≫ ψ₁) ^ N = 1 := by
    rw [ha]
    exact (J₁.onto N hN _).mpr ⟨y, rfl⟩
  have h2 : a ^ d = (a ≫ ψ₁) ≫ ψ' := by
    rw [Category.assoc, hd, comp_pow_overScheme_grpObj, Category.comp_id]
  have h3 : a ^ (N * d) = 1 := by
    rw [mul_comm, pow_mul, h2, ← pow_comp_monHom_overScheme_grpObj, h1, MonObj.one_comp]
  obtain ⟨x, hx⟩ := (I.onto (N * d) hn a).mp h3
  let y' : D.toG.La := y
  have hJ₁ : J₁.ev N y' = J₁.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₁.tower N d hN hd0]
  have hJ₂ : J₂.ev N y' = J₂.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₂.tower N d hN hd0]
  change a ≫ ψ₁ = J₁.ev N y' at ha
  change a ≫ ψ₂ = J₂.ev N y'
  rw [← hx] at ha ⊢
  rw [hJ₂]
  rw [hJ₁] at ha
  exact (H₂ (N * d) hn hnp x (d • y')).mpr ((H₁ (N * d) hn hnp x (d • y')).mp ha)

end

theorem UpperTheory.Gal.G3.pTransKer :
    RelComp → TateDiff → TateTwist → TransKer := by
  intro RC TD TT p _ D G L R _ _ gb S s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm T₁ T₂ k _ _ t
  let β : R →+* k := (Spec.preimage (t ≫ s)).hom
  have hβ : t ≫ s = spMap β := by
    simp [β, spMap, Spec.map_preimage]
  have key : ∀ (q₁ q₂ : GObj gb (↑N) s) (φ₁ : o.A ⟶ q₁.A) (φ₂ : o.A ⟶ q₂.A),
      IsTrans L h o q₁ φ₁ → IsTrans L h o q₂ φ₂ → ∀ (a : Over.mk t ⟶ o.A) (y : D.La),
      a ≫ φ₁ = toUnit (Over.mk t) ≫ q₁.eta y → a ≫ φ₂ = toUnit (Over.mk t) ≫ q₂.eta y := by
    intro q₁ q₂ φ₁ φ₂ U₁ U₂ a y ha
    obtain ⟨-, -, ⟨φ', d, hφ', -, hd, -, hdp⟩, -, tate₁⟩ := U₁
    obtain ⟨hmon₂, -, -, -, tate₂⟩ := U₂
    obtain ⟨I₁, J₁, hI₁, hJ₁, R₁⟩ := tate₁ k t β hβ
    obtain ⟨I₂, J₂, hI₂, hJ₂, R₂⟩ := tate₂ k t β hβ
    obtain ⟨u, hu, hR⟩ := TD p D G L R gb S s N' o k t I₁ I₂ hI₁ hI₂
    have hc₁ := (RC p D G L R gb S s (↑N') (↑N') (↑N) o o q₂ k t I₁ I₂ J₂ (𝟙 _) φ₂ u h
      inferInstance hmon₂ hint).2 hR R₂
    have hw : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hadm _ (Subgroup.inv_mem _ hu)
    obtain ⟨J₃, hJ₃, hR₃⟩ := TT p D G L R gb S s N q₂ k t J₂ hJ₂ _ hw
    have hwi : Integ L (h * u⁻¹ * h⁻¹) :=
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hw)
    have hc₂ := (RC p D G L R gb S s (↑N') (↑N) (↑N) o q₂ q₂ k t I₁ J₂ J₃ (𝟙 _ ≫ φ₂) (𝟙 _) (h * u) _
      inferInstance inferInstance hwi).2 hc₁ hR₃
    have hg : h * u⁻¹ * h⁻¹ * (h * u) = h := by group
    rw [hg, Category.id_comp, Category.comp_id] at hc₂
    have hN : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    rw [hJ₁ y] at ha
    rw [hJ₃ y]
    exact pt_transfer hN N.2.2 hφ' hd hdp I₁ J₁ J₃ R₁ hc₂ a y ha
  have hz : ∀ q : GObj gb (↑N) s, toUnit (Over.mk t) ≫ q.eta (0 : D.La) = 1 := by
    intro q
    rw [show q.eta (0 : D.La) = 1 from q.eta_zero, MonObj.comp_one]
  refine ⟨fun a => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun a y => ⟨key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a y, key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a y⟩⟩
  · have := key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a 0 (by rw [h1, hz])
    rwa [hz] at this
  · have := key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a 0 (by rw [h2, hz])
    rwa [hz] at this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateTwist :
    GSimOf → TateTwist := by
  unfold GSimOf TateTwist
  intro hG p _ D G L R _ _ gb S s N o k _ t I hI u hu
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hNcop : (N : ℕ).Coprime p := N.2.2
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have hui1 : u⁻¹ ∈ L.KN 1 := inv_mem hu1
  obtain ⟨g, hg⟩ := hG p D G L u⁻¹ hui1
  obtain ⟨J, hJ⟩ := UpperTheory.exists_gTateIso_twist_of_similitude I g
  have intU := UpperTheory.Gal.Int.Geo.integ_of_mem hu1
  have intUi := UpperTheory.Gal.Int.Geo.integ_of_mem hui1
  unfold UpperTheory.Gal.Int.Geo.Integ at intU intUi
  have hcong : L.CongOne (N : ℕ) u⁻¹ := by
    unfold GlobalTheory.LKGeo.Link.KN at hu
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
    exact hu.2
  unfold GlobalTheory.LKGeo.Link.CongOne at hcong
  have inv_act : ∀ v, L.actG u⁻¹ (L.actG u v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have act_inv : ∀ v, L.actG u (L.actG u⁻¹ v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  refine ⟨J, ?_, ?_⟩
  · unfold UpperTheory.Gal.G3.Ind at hI ⊢
    intro y
    rw [hI y, hJ _ hNpos y]
    symm
    refine (HeckeRestrict.ev_eq_iff I _ hNpos (g.f N y) y).mpr ?_
    obtain ⟨w, hw, hgw⟩ := hg N hNpos hNcop y
    obtain ⟨w', hw', hcw⟩ := hcong (inAf D y) (GlobalTheory.HeckeApprox.inAf_mem D y)
    apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ N hNpos hNcop (w' - w) (sub_mem hw' hw)
    have e := hgw.symm.trans hcw
    rw [show inAf D (g.f N y - y) = inAf D (g.f N y) - inAf D y from GlobalTheory.HeckeApprox.inAf_sub D _ _, smul_sub]
    calc inAf D (g.f N y) - inAf D y = (inAf D (g.f N y) + (N : ℕ) • w) - (N : ℕ) • w - inAf D y := by abel
      _ = (inAf D y + (N : ℕ) • w') - (N : ℕ) • w - inAf D y := by rw [e]
      _ = (N : ℕ) • w' - (N : ℕ) • w := by abel
  · unfold UpperTheory.Gal.G3.Rel
    intro n hn hnp x y
    rw [Category.comp_id, hJ n hn y]
    refine (HeckeRestrict.ev_eq_iff I n hn x (g.f n y)).trans ?_
    obtain ⟨w, hw, hgw⟩ := hg n hn hnp y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨L.actG u (inAf D z - w), intU _ (sub_mem (GlobalTheory.HeckeApprox.inAf_mem D z) hw), ?_⟩
      have h1 := GlobalTheory.HeckeApprox.inAf_add D (g.f n y) (n • z)
      have h2 := GlobalTheory.HeckeApprox.inAf_nsmul D n z
      have hx : inAf D x = inAf D (g.f n y) + n • inAf D z :=
        (congrArg (inAf D) (sub_eq_iff_eq_add'.mp hz)).trans (h1.trans (congrArg (inAf D (g.f n y) + ·) h2))
      have e1 : inAf D (g.f n y) = L.actG u⁻¹ (inAf D y) - n • w := by
        rw [hgw]
        abel
      rw [hx, e1, map_add (f := _), map_sub, map_nsmul, map_nsmul, act_inv, map_sub, smul_sub]
      abel
    · rintro ⟨v, hv, hxv⟩
      apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp (w + L.actG u⁻¹ v) (add_mem hw (intUi _ hv))
      have hx : inAf D x = L.actG u⁻¹ (inAf D y) + n • L.actG u⁻¹ v := by
        rw [← map_nsmul, ← map_add (f := _), ← hxv, inv_act]
      refine (GlobalTheory.HeckeApprox.inAf_sub D x (g.f n y)).trans ?_
      rw [hx, hgw, smul_add]
      abel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pRelComp :
    RelComp := by
  unfold UpperTheory.Gal.G3.RelComp
  intro p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ k _ t I₁ I₂ I₃ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂ hint
  unfold UpperTheory.Gal.G3.Rel
  refine ⟨?_, ?_⟩
  · intro n hn hcop x y
    rw [Category.comp_id]
    refine (HeckeRestrict.ev_eq_iff I₁ n hn x y).trans
      ((ForgetHecke.acts_one_iff L n hn hcop x y).symm.trans ?_)
    simp
  · intro r₁ r₂ n hn hcop x z
    have htor : (I₁.ev n x ≫ ψ₁) ^ n = 1 := by
      haveI := hψ₁
      have e := map_pow (IsMonHom.monoidHom ψ₁ (Over.mk t)) (I₁.ev n x) n
      simp only [IsMonHom.monoidHom_apply] at e
      rw [← e, (I₁.onto n hn (I₁.ev n x)).2 ⟨x, rfl⟩]
      exact (IsMonHom.monoidHom ψ₁ (Over.mk t)).map_one
    obtain ⟨y, hy⟩ := (I₂.onto n hn _).1 htor
    obtain ⟨v₁, hv₁, e₁⟩ := (r₁ n hn hcop x y).1 hy.symm
    rw [← Category.assoc, ← hy, r₂ n hn hcop y z, map_mul, Module.End.mul_apply, e₁, map_add (f := _),
      map_nsmul]
    have hw := hint v₁ hv₁
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v + L.actG h₂ v₁, add_mem hv hw, ?_⟩
      rw [e, smul_add, add_assoc]
    · rintro ⟨v, hv, e⟩
      refine ⟨v - L.actG h₂ v₁, sub_mem hv hw, ?_⟩
      rw [smul_sub, ← add_sub_assoc, ← e, add_sub_cancel_right]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransIso :
    IsoPts → IsogFEt → TransIso := by
  intro IP IF p _ D G L R _ _ gb S s N' N o' o ψ u hu T
  obtain ⟨hmon, -, ⟨ψ', d, hψ', -, hd, hd', hdp⟩, -, tate⟩ := T
  haveI := hmon
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  obtain ⟨hfin, het, hsurj⟩ := IF R S s o'.A o.A o'.ab o.ab ψ ψ' d hd0 hmon hψ' hd hd'
  haveI := het
  haveI := hfin
  have hiso : IsIso ψ.left := by
    apply IP ψ.left
    intro Ω _ _ z
    obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
    obtain ⟨y, hy, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ.left Ω z v hv
    refine ⟨y, hy, fun y₂ hy₂ => ?_⟩
    let t : sp Ω ⟶ S := y ≫ o'.A.hom
    have ht2 : y₂ ≫ o'.A.hom = t := by
      rw [← Over.w ψ, ← Category.assoc, hy₂, ← hy, Category.assoc, Over.w ψ]
    let a₁ : Over.mk t ⟶ o'.A := Over.homMk y rfl
    let a₂ : Over.mk t ⟶ o'.A := Over.homMk y₂ ht2
    have hc : a₁ ≫ ψ = a₂ ≫ ψ := by
      ext
      simp [a₁, a₂, hy, hy₂]
    have ha : (a₂ * a₁⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← hc, mul_inv_cancel]
    have had : (a₂ * a₁⁻¹) ^ d = 1 := by
      have e : (a₂ * a₁⁻¹) ^ d = (a₂ * a₁⁻¹) ≫ ψ ≫ ψ' := by
        rw [hd, MonObj.comp_pow, Category.comp_id]
      rw [e, ← Category.assoc, ha, MonObj.one_comp]
    let β : R →+* Ω := (Spec.preimage (t ≫ s)).hom
    have hβ : t ≫ s = spMap β := by
      simp [β, spMap, Spec.map_preimage]
    obtain ⟨I', I'', -, -, hrel⟩ := tate Ω t β hβ
    obtain ⟨x, hx⟩ := (I'.onto d hd0 _).mp had
    have h0 : I'.ev d x ≫ ψ = I''.ev d 0 := by
      rw [hx, ha, HeckeRestrict.ev_zero]
    obtain ⟨w, hw, hxw⟩ := (hrel d hd0 hdp x 0).mp h0
    have hinv : u⁻¹ ∈ L.KN 1 := Subgroup.inv_mem _ hu
    have hdw : d • w = L.actG u (inAf D x) := by
      rw [hxw]
      simp [inAf]
    have hxa : inAf D x = d • L.actG u⁻¹ w := by
      rw [← map_nsmul, hdw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    obtain ⟨z', hz'⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x d hd0 hdp _
      (UpperTheory.Gal.Int.Geo.integ_of_mem hinv w hw) hxa
    have h1 : a₂ * a₁⁻¹ = 1 := by
      rw [← hx]
      exact (I'.ker d hd0 x).mpr ⟨z', hz'⟩
    have h2 : a₂ = a₁ := mul_inv_eq_one.mp h1
    exact congrArg Over.Hom.left h2
  have : IsIso ((Over.forget S).map ψ) := hiso
  exact isIso_of_reflects_iso ψ (Over.forget S)
end
