module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open GlobalTheory GlobalTheory.LKMid GlobalTheory.LKRes GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pSysOf :
    NuInt → SysOf := by
  intro hNu p _ D G L g hI
  classical
  set A := L.actG g with hA
  set B := L.actG g⁻¹ with hB
  have hBA : ∀ v, B (A v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hAB : ∀ v, A (B v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hAint : ∀ v ∈ LaHat D, A v ∈ LaHat D := hI
  obtain ⟨j₁, hj₁, hj₁p, hj₁B⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D B
  set ν : AfP p := UpperTheory.Gal.G3.mul g with hν
  set ν' : AfP p := ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) with hν'
  have hνν' : ν * ν' = 1 := Units.mul_inv _
  have hνint : IsIntAf ν := hNu p D G L g hI
  obtain ⟨j₃, hj₃, hj₃p, hj₃ν⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p ν'
  set k := j₁ * j₃ with hk
  have hkp : k.Coprime p := Nat.Coprime.mul_left hj₁p hj₃p
  have hk0 : 0 < k := Nat.mul_pos hj₁ hj₃
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := k • B with hh₀
  have hh₀v : ∀ v, h₀ v = k • B v := fun v => rfl
  have hh₀int : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := fun v hv => by
    rw [hh₀v, hk, mul_comm, mul_smul]; exact nsmul_mem (hj₁B v hv) _
  have hh₀A : ∀ v, h₀ (A v) = k • v := fun v => by
    rw [hh₀v, hBA]
  have hAh₀ : ∀ v, A (h₀ v) = k • v := fun v => by
    rw [hh₀v, map_nsmul, hAB]
  have hh₀O : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := fun c v => by
    rw [hh₀v, hh₀v, hB, actG_actAf, map_nsmul]
  set mu : AfP p := (k : AfP p) ^ 2 * ν' with hmu
  have hh₀sim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := fun v w => by
    simp only [hh₀v, map_nsmul, LinearMap.smul_apply]
    rw [hB, GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L g⁻¹ v w]
    simp only [nsmul_eq_mul, hmu, hν']
    rw [show (((g⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) =
      ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) from rfl]
    ring
  have hmuint : IsIntAf mu := by
    have e : mu = ((j₁ : AfP p) ^ 2 * j₃) * ((j₃ : AfP p) * ν') := by rw [hmu, hk]; push_cast; ring
    rw [e]; exact isInt_mul (isInt_mul (by rw [sq]; exact isInt_mul (isInt_natCast _) (isInt_natCast _))
      (isInt_natCast _)) hj₃ν
  have hmuν : mu * ν = ((k ^ 2 : ℕ) : AfP p) := by
    rw [hmu]; push_cast; linear_combination ((k : AfP p) ^ 2) * hνν'
  obtain ⟨c, ε, ε', hcp, hck, hε, hε', hεε', hmuε⟩ :=
    GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ν (k ^ 2) (pow_pos hk0 2) (Nat.Coprime.pow_left 2 hkp) hmuint hνint hmuν
  obtain ⟨u, hut, hu⟩ := GlobalTheory.T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε'
  obtain ⟨f, hf⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ hh₀int
  have hfe : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, inAf D (f n x) = h₀ (inAf D x) - n • w :=
    fun n hn hnp x => by
      obtain ⟨w, hw, e⟩ := hf n hn hnp x
      exact ⟨w, hw, by rw [e]; abel⟩
  have hmult : IsMult ν (k ^ 2 / c) := by
    refine ⟨ε', ε, hε', hε, by rw [mul_comm]; exact hεε', ?_⟩
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hck
      exact (pow_pos hk0 2).ne' hck
    have hcu : IsUnit (c : AfP p) := by
      have : IsUnit (algebraMap ℚ (AfP p) (c : ℚ)) :=
        (IsUnit.mk0 (c : ℚ) (Nat.cast_ne_zero.mpr hc0)).map _
      simpa using this
    have e1 : ((k ^ 2 : ℕ) : AfP p) = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hck]
    apply hcu.mul_left_cancel
    have e2 : (c : AfP p) * ε * ν = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← hmuε, hmuν, e1]
    linear_combination ε' * e2 - ((c : AfP p) * ν) * hεε'
  refine ⟨f, u, c, k, ⟨hcp, hkp, hck, ?_, ?_, ?_, ?_⟩, hmult, fun v hv => hh₀int v hv, ?_⟩
  ·
    intro n hn hnp a x
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp (a • x)
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n (a • x) - a • f n x) n hn hnp
      (actAf D a w₂ - w₁) (sub_mem (actAf_mem_laHat D a hw₂) hw₁) (by
        rw [inAf_sub, ← actAf_inAf, e₁, e₂, ← actAf_inAf, hh₀O, map_sub, map_nsmul, smul_sub]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    refine ⟨fun x => ?_, hut n m hn hm hnm⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe (n * m) (Nat.mul_pos hn hm) hnm x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f (n * m) x - f n x) n hn hnp
      (w₂ - m • w₁) (sub_mem hw₂ (nsmul_mem hw₁ m)) (by
        rw [inAf_sub, e₁, e₂, smul_sub, smul_smul]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp
    obtain ⟨hco, β, hβ, hεβ⟩ := hu n hn hnp
    refine ⟨hco, fun x y => ?_⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp y
    have hX := hh₀int _ (inAf_mem D x)
    have hY := hh₀int _ (inAf_mem D y)
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w₂ - fAf D w₁ (h₀ (inAf D y)) +
        (n : AfP p) * fAf D w₁ w₂)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _))
        (formInt_laHat p D _ _ hX hw₂)) (formInt_laHat p D _ _ hw₁ hY))
        (isInt_mul (isInt_natCast n) (formInt_laHat p D _ _ hw₁ hw₂))) ?_
    have e : ((D.EF (f n x) (f n y) : ℤ) : AfP p) = fAf D (inAf D (f n x)) (inAf D (f n y)) :=
      (form_inAf D _ _).symm
    push_cast
    rw [e, e₁, e₂]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hh₀sim, hmuε, hεβ, form_inAf]
    ring
  ·
    intro n hn hnp x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (A (inAf D x))
      (hAint _ (inAf_mem D x))
    obtain ⟨w', hw', e'⟩ := hfe n hn hnp y
    have e2 : h₀ (inAf D y) = k • inAf D x - n • h₀ w := by
      rw [← hh₀A, e, map_add (f := _), map_nsmul]; abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n y - k • x) n hn hnp
      (-(w' + h₀ w)) (neg_mem (add_mem hw' (hh₀int w hw))) (by
        rw [inAf_sub, e', e2, inAf_nsmul, smul_neg, smul_add]; abel)
    exact ⟨y, z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp x
    obtain ⟨w, hw, e⟩ := hfe n hn hnp x
    refine ⟨-(A w), neg_mem (hAint w hw), ?_⟩
    rw [e, map_sub, map_nsmul, hAh₀, smul_neg]
    abel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.UPel.HT.Hecke in
private theorem gObjMap_comp_keep {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) :
    ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have e₁ : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have e₂ : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ => h₂.φ₂) (fun _ => 1) h₁.φ₂) e₁
  refine ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, ?_, ?_,
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol e₂, ?_⟩, rfl⟩
  · exact ⟨by simp only [Category.assoc, h₂.sq.1, reassoc_of% h₁.sq.1],
      by simp only [Category.assoc, h₂.sq.2, reassoc_of% h₁.sq.2]⟩
  · intro c
    simp only [← Category.assoc, h₁.act c]
    simp only [Category.assoc, h₂.act c]
  · intro y
    simp only [reassoc_of% h₁.eta y, h₂.eta y, Category.assoc]

theorem UpperTheory.Gal.G3.pWitEx :
    KNBasic → GenSm → Rigid → WitForget → WitDeep → DescMap → TransIso → TransCancel → TransDesc → WitEx := by
  intro _ hSm hRig hWF hWD hDM hTI hTC hTD p _ D G L R _ _ gb X N' N h hI hA
  obtain ⟨M, hdiv, hAM, π₁, Φ₁, hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩ := hWD p D G L R gb X N' N h hI
  obtain ⟨c, Φc, hw, hfin, het, hsur⟩ := hWF p D G L R gb N' M hdiv (X N') (X M)
  have hA1 : AdmK L (↑M) (↑N') 1 := by
    intro u hu
    simpa using UpperTheory.Gal.Int.Geo.KN_anti hdiv hu
  obtain ⟨π, Φ, hcπ, hΦ, hπs, hΦw⟩ :=
    hDM p D G L R gb M N' N (X M) (X N') (X N) h hI hA hA1 c Φc π₁ Φ₁ hw hfin het hsur
      ⟨hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩
  subst hcπ
  obtain ⟨hsc, oc, ψc, φc, htc, hΦc⟩ := hw
  obtain ⟨o, ⟨φ⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (X N').s π hπs (X N).univ
  let ψl : (X N').univ.A.left ⟶ o.A.left :=
    φ.cart.1.lift Φ (X N').univ.A.hom hΦw
  have hψ₁ : ψl ≫ φ.φ = Φ := φ.cart.1.lift_fst _ _ _
  have hψ₂ : ψl ≫ o.A.hom = (X N').univ.A.hom := φ.cart.1.lift_snd _ _ _
  let ψ : (X N').univ.A ⟶ o.A := Over.homMk ψl hψ₂
  refine ⟨π, Φ, hπs, o, ψ, φ, ?_, hψ₁.symm⟩
  obtain ⟨m₂⟩ := BaseChange.gObjMap_cancel φ₁ φ
  haveI := hTI p D G L R gb (X M).X (X M).s M N' (X M).univ oc ψc 1 (one_mem _) htc
  have htr : IsTrans L h oc o₁ (inv ψc ≫ ψ₁) :=
    hTC p D G L R gb (X M).X (X M).s M N' N (X M).univ oc o₁ ψc (inv ψc ≫ ψ₁) h hI hAM htc
      (by simpa using ht₁)
  haveI : Smooth (X M).s := (hSm p D R gb M (X M)).1
  haveI : AlgebraicGeometry.IsReduced (X M).X := GlobalTheory.isReduced_of_smooth_of_isReduced (X M).s
  have hcomp : m₂.φ ≫ φ.φ = φ₁.φ := by
    obtain ⟨m, hm⟩ := gObjMap_comp_keep m₂ φ
    rw [← hm]
    exact hRig p D R gb (X N).X (X M).X (X N).s (X M).s (c ≫ π)
      (by rw [Category.assoc, hπs, hsc]) N (X N).univ o₁ m φ₁
  refine hTD p D G L R gb (X N').X (X M).X (X N').s (X M).s c hsc N' N (X N').univ o oc o₁ φc m₂ ψ
    (inv ψc ≫ ψ₁) h ?_ htr
  have key : ψc.left ≫ φc.φ ≫ Φ = ψ₁.left ≫ φ₁.φ := by
    rw [← Category.assoc, ← hΦc, hΦ, hΦ₁]
  apply φ.cart.1.hom_ext
  · simp only [Category.assoc, hcomp, ψ, Over.homMk_left, hψ₁, Over.comp_left]
    rw [← key, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.id_comp]
  · simp only [Category.assoc, ψ, Over.homMk_left, hψ₂, Over.comp_left]
    rw [m₂.cart.1.w, φc.cart.1.w, ← Over.comp_left_assoc, Over.w_assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransComp :
    MultBasic → RelComp → TateDiff → TateTwist → TransComp := by
  intro hMB hRC hTD hTT p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ ψ₁ ψ₂ h₁ h₂ hI hA t1 t2
  obtain ⟨m1, a1, ⟨ψ₁', d₁, m1', a1', e1, e1', cp1⟩, ⟨c₁, cc1, ⟨iso1⟩, hm1⟩, g1⟩ := t1
  obtain ⟨m2, a2, ⟨ψ₂', d₂, m2', a2', e2, e2', cp2⟩, ⟨c₂, cc2, ⟨iso2⟩, hm2⟩, g2⟩ := t2
  haveI := m1
  haveI := m2
  haveI := m1'
  haveI := m2'
  refine ⟨inferInstance, ?_, ⟨ψ₂' ≫ ψ₁', d₁ * d₂, inferInstance, ?_, ?_, ?_, Nat.Coprime.mul_left cp1 cp2⟩,
    ⟨c₂ * c₁, Nat.Coprime.mul_left cc2 cc1, ⟨?_⟩, ?_⟩, ?_⟩
  · intro c
    rw [← Category.assoc, a1 c, Category.assoc, a2 c, Category.assoc]
  · intro c
    rw [← Category.assoc, a2' c, Category.assoc, a1' c, Category.assoc]
  · rw [Category.assoc, ← Category.assoc ψ₂, e2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e1, pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ₁', e1', MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e2', mul_comm, pow_mul]
  · have hlb : (Hecke.lbPow o₁.P (c₂ * c₁)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpl : (o₃.P.pull (Hecke.sq2 (ψ₁ ≫ ψ₂))).IsLB := pull_isLB o₃.isLB _
    have hl1 : (Hecke.lbPow o₁.P c₁).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hl2 : (Hecke.lbPow o₂.P c₂).IsLB := LB.isLB_linComb o₂.isLB _ _
    have k1 := (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB o₂.isLB (Hecke.sq2 ψ₁))).2 iso1
    have k2 := (GlobalTheory.CechPic.cls_eq_iff hl2 (pull_isLB o₃.isLB (Hecke.sq2 ψ₂))).2 iso2
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at k1
    rw [Hecke.Comp.cls_lbPow' o₂.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB] at k2
    apply (GlobalTheory.CechPic.cls_eq_iff hlb hpl).1
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB, Hecke.Comp.grpSchemeSquareProductMap_comp,
      GlobalTheory.CechPic.pull_comp, ← k2, map_nsmul, ← k1, smul_smul]
  · exact (hMB p).2.1 _ _ _ _ hm2 hm1
  · intro k _ _ t β hts
    obtain ⟨I1', I1'', ind1', ind1'', rel1⟩ := g1 k t β hts
    obtain ⟨I2', I2'', ind2', ind2'', rel2⟩ := g2 k t β hts
    obtain ⟨u, hu, ru⟩ := hTD p D G L R gb S s N₂ o₂ k t I1'' I2' ind1'' ind2'
    have hint : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → Integ L g := fun hg =>
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg)
    have rA := (hRC p D G L R gb S s N₁ N₂ N₂ o₁ o₂ o₂ k t I1' I1'' I2' ψ₁ (𝟙 _) h₁ u
      inferInstance inferInstance (hint hu)).2 rel1 ru
    have rB := (hRC p D G L R gb S s N₁ N₂ N₃ o₁ o₂ o₃ k t I1' I2' I2'' (ψ₁ ≫ 𝟙 _) ψ₂ (u * h₁) h₂
      inferInstance inferInstance hI).2 rA rel2
    have hu' : (h₂ * u * h₂⁻¹)⁻¹ ∈ L.KN N₃ := inv_mem (hA u hu)
    obtain ⟨J, indJ, rJ⟩ := hTT p D G L R gb S s N₃ o₃ k t I2'' ind2'' _ hu'
    have rC := (hRC p D G L R gb S s N₁ N₃ N₃ o₁ o₃ o₃ k t I1' I2'' J ((ψ₁ ≫ 𝟙 _) ≫ ψ₂) (𝟙 _)
      (h₂ * (u * h₁)) _ inferInstance inferInstance (hint hu')).2 rB rJ
    have hg : (h₂ * u * h₂⁻¹)⁻¹ * (h₂ * (u * h₁)) = h₂ * h₁ := by group
    rw [hg] at rC
    simp only [Category.comp_id] at rC
    exact ⟨I1', J, ind1', indJ, rC⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pDescMap :
    GenSm → EtDesc → PtEq → PtOrbit → WitCart → DescMap := by
  intro hSm hEt hEq hOrb hCart p _ D G L R _ _ gb M N' N XM X' X h hI hA' hA1 c Φc π₁ Φ₁ hWc hFin hEtc hSurj hW1
  have hAd : AdmK L (↑M) (↑N) h := by
    intro v hv
    have h1 := hA1 v hv
    have h2 : v ∈ L.KN ↑N' := by simpa using h1
    exact hA' v h2
  haveI hred : IsReduced XM.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field R XM.X XM.s
      (hSm p D R gb M XM).1).1
  haveI hsep : IsSeparated X.s := (hSm p D R gb N X).2.1
  haveI := hFin
  haveI := hEtc
  haveI := hSurj
  have hsq : π₁ ≫ X.s = c ≫ X'.s := hW1.1.trans hWc.1.symm
  obtain ⟨hepi, π, hπ⟩ := hEt c X'.s X.s π₁ hsq (by
    intro Ω _ _ x y hxy
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, _⟩ := hOrb p D G L R gb M N' XM X' c Φc hWc Ω x y hxy
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    exact (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω (x ≫ XM.s) x y rfl hys ox oy mx my θ hθ).1)
  have hπs : π ≫ X.s = X'.s := by
    rw [← cancel_epi c, ← Category.assoc, hπ, hW1.1, hWc.1]
  have wsq : ∀ {NN NN' : ℕ} (Y' : GenModel gb NN') (Y : GenModel gb NN) (g : G.GAf) (ρ : Y'.X ⟶ Y.X)
      (Ψ : Y'.univ.A.left ⟶ Y.univ.A.left), Wit L g Y' Y ρ Ψ → Ψ ≫ Y.univ.A.hom = Y'.univ.A.hom ≫ ρ := by
    rintro _ _ Y' Y g ρ Ψ ⟨_, o, ψ, φ, _, rfl⟩
    rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w ψ]
  have hC : IsPullback Φc XM.univ.A.hom X'.univ.A.hom c :=
    hCart p D G L R gb (↑M) (↑N') XM X' 1 (one_mem _) c Φc hWc
  haveI : IsReduced XM.univ.A.left := by
    haveI := XM.univ.ab.smooth
    exact GlobalTheory.isReduced_of_smooth_of_isReduced XM.univ.A.hom
  haveI : IsSeparated X.univ.A.hom := by
    haveI := X.univ.ab.proper
    infer_instance
  haveI : IsFinite Φc := MorphismProperty.of_isPullback (P := @IsFinite) hC.flip hFin
  haveI : Etale Φc := MorphismProperty.of_isPullback (P := @Etale) hC.flip hEtc
  haveI : Surjective Φc := MorphismProperty.of_isPullback (P := @Surjective) hC.flip hSurj
  have hsq2 : Φ₁ ≫ X.univ.A.hom = Φc ≫ X'.univ.A.hom ≫ π := by
    rw [wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  obtain ⟨hepi2, Φ, hΦ⟩ := hEt Φc (X'.univ.A.hom ≫ π) X.univ.A.hom Φ₁ hsq2 (by
    intro Ω _ _ x y hxy
    have hab : (x ≫ XM.univ.A.hom) ≫ c = (y ≫ XM.univ.A.hom) ≫ c := by
      have e := congrArg (· ≫ X'.univ.A.hom) hxy
      simpa [hC.w] using e
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθeq⟩ :=
      hOrb p D G L R gb M N' XM X' c Φc hWc Ω _ _ hab
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    have key := (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω ((x ≫ XM.univ.A.hom) ≫ XM.s) _ _ rfl hys ox oy mx my θ hθ).2
    obtain ⟨x', hx1, hx2⟩ : ∃ x' : sp Ω ⟶ ox.A.left, x' ≫ mx.φ = x ∧ x' ≫ ox.A.hom = 𝟙 _ :=
      ⟨mx.cart.1.lift x (𝟙 _) (by simp), mx.cart.1.lift_fst _ _ _, mx.cart.1.lift_snd _ _ _⟩
    obtain ⟨y', hy1, hy2⟩ : ∃ y' : sp Ω ⟶ oy.A.left, y' ≫ my.φ = y ∧ y' ≫ oy.A.hom = 𝟙 _ :=
      ⟨my.cart.1.lift y (𝟙 _) (by simp), my.cart.1.lift_fst _ _ _, my.cart.1.lift_snd _ _ _⟩
    have hP := my.cart.1.paste_horiz hC
    have hxy' : x' ≫ θ.left = y' := by
      apply hP.hom_ext
      · rw [Category.assoc, hθeq, ← Category.assoc, hx1, hxy, ← Category.assoc, hy1]
      · rw [Category.assoc, Over.w θ, hx2, hy2]
    calc x ≫ Φ₁ = x' ≫ mx.φ ≫ Φ₁ := by rw [← Category.assoc, hx1]
      _ = x' ≫ θ.left ≫ my.φ ≫ Φ₁ := by rw [key]
      _ = y' ≫ my.φ ≫ Φ₁ := by rw [← Category.assoc x', hxy']
      _ = y ≫ Φ₁ := by rw [← Category.assoc, hy1])
  have hΦs : Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
    rw [← cancel_epi Φc, ← Category.assoc, hΦ, wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  exact ⟨π, Φ, hπ, hΦ, hπs, hΦs⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_one {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]
    {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    Nonempty (LBIso (Hecke.lbPow o.P 1) (o.P.pull (Hecke.sq2 (𝟙 o.A)))) := by
  have h : Hecke.sq2 (𝟙 o.A) = 𝟙 _ := by simp [Hecke.sq2]
  refine ⟨?_⟩
  rw [h]
  unfold Hecke.lbPow LB.pull
  exact (GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 rfl

private theorem gTateIso_ev_nsmul' {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ)
    (y : G.La) : I.ev n (c • y) = I.ev n y ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    have h1 : I.ev n 0 = 1 :=
      mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
    rw [zero_smul, pow_zero, h1]
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.G3.pTransSelf :
    MultBasic → RelComp → TateTwist → TransSelf := by
  intro hM hR hT p _ D G L R _ _ gb S s N
  refine ⟨fun o u hu => ?_, fun c hN hc o => ?_⟩
  · have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L u hu1
    refine ⟨⟨by simp, by simp⟩, fun _ => by simp, ⟨𝟙 _, 1, ⟨by simp, by simp⟩, fun _ => by simp,
      by simp, by simp, Nat.coprime_one_left _⟩, ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha,
      ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    obtain ⟨J, hJ, hRel⟩ := hT p D G L R gb S s N o k x I hI u hu
    exact ⟨I, J, hI, hJ, hRel⟩
  · obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L 1 (one_mem _)
    have hmon : IsMonHom (𝟙 o.A) := ⟨by simp, by simp⟩
    refine ⟨show IsMonHom (𝟙 o.A) from hmon, fun _ => by simp [GObj.forgetMul],
      ⟨𝟙 _, 1, show IsMonHom (𝟙 o.A) from hmon,
      fun _ => by simp [GObj.forgetMul], by simp; exact Category.comp_id _,
      by simp; exact Category.comp_id _, Nat.coprime_one_left _⟩,
      ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha, ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    have hInt : UpperTheory.Gal.Int.Geo.Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
    refine ⟨I, I, hI, fun y => ?_, ?_⟩
    · show toUnit _ ≫ o.eta (c • y) = _
      rw [hI, gTateIso_ev_nsmul', I.tower _ _ hN hc]
    · exact (hR p D G L R gb S s _ _ _ o o o k x I I I (𝟙 _) (𝟙 _) 1 1 hmon hmon hInt).1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pEtDesc :
    ExtPts → EtDesc := by
  intro hE W Z Y B _ c _ _ _ pZ pY _ f hf hpts
  haveI : Flat c := inferInstance
  haveI : EffectiveEpi c := inferInstance
  haveI : IsReduced (pullback c c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst c c)
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hE pY _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      refine hpts Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) ?_ |>.trans ?_ <;> simp [pullback.condition]
  refine ⟨inferInstance, EffectiveEpi.desc c f (fun {T} g₁ g₂ h => ?_), EffectiveEpi.fac _ _ _⟩
  have e₁ : pullback.lift g₁ g₂ h ≫ pullback.fst c c = g₁ := pullback.lift_fst _ _ _
  have e₂ : pullback.lift g₁ g₂ h ≫ pullback.snd c c = g₂ := pullback.lift_snd _ _ _
  calc g₁ ≫ f = pullback.lift g₁ g₂ h ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, e₁]
    _ = pullback.lift g₁ g₂ h ≫ pullback.snd c c ≫ f := by rw [key]
    _ = g₂ ≫ f := by rw [← Category.assoc, e₂]
end
