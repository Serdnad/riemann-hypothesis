module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqTwist

theorem twist_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hvT hvS s z hf
  classical
  set τ := Bs.τ v with hτ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hunder : w.under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under τ
  have hloc : w ∈ locPl G t := hB.2.2.2 v hvT
  have hW0 : w ∉ G.pl.W0 := by
    intro h
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h
    apply hvS
    have := G.pl.under_w hu
    rw [hu'] at this
    rw [← hunder, this]
    exact hu
  have htw : w ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  have hQ : w ∈ Lc.Q t := by
    rcases Finset.mem_union.1 hloc with h | h
    · exact absurd h hW0
    · exact h
  have hq : Ideal.absNorm w.asIdeal = Ideal.absNorm v.1.asIdeal := GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ
  have hQn : 0 < Qn G t := by
    unfold Qn
    refine Finset.prod_pos fun u _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hqd : Ideal.absNorm v.1.asIdeal ∣ Qn G t := hq ▸ Finset.dvd_prod_of_mem _ htw
  obtain ⟨hmu, hchi⟩ := GlobalTheory.T.mu0_and_chiH_unrAt_outside_S0 G hL i j t w hQ (by rw [hunder]; exact hvS)
  have hc := GlobalTheory.T.twistPlace_stepCharacter_conductorExponent_one G hL i j t τ hmu hchi hQ
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.gaussSum_stepCharacter_twistPlace_dvd G W S hL hN i j t τ Bs.ψ (hB.2.2.1 v.1 v.2) hloc hc
  obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist G W S hL hN i j t τ hmu hchi htw
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  set s' : (Fv D.host.F v.1)ˣ := Units.map (Int.castRingHom _).toMonoidHom s with hs'

  have hs2 : s' ^ 2 = 1 := by
    rw [hs', ← map_pow, Int.units_sq, map_one]
  have hsgn : ((ν s' : ℂˣ) : ℂ) = 1 ∨ ((ν s' : ℂˣ) : ℂ) = -1 := by
    have h2 : ((ν s' : ℂˣ) : ℂ) * ((ν s' : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← sq, hs2, map_one, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  obtain ⟨e, he, hea⟩ : ∃ e : D.what₂.LL, D.what₂.embLL e = ((ν s' : ℂˣ) : ℂ) ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) e := by
    rcases hsgn with h | h
    · exact ⟨1, by rw [map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ one_pos (one_pow 1)⟩
    · exact ⟨-1, by rw [map_neg, map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ two_pos (by norm_num)⟩

  set q : ℕ := Ideal.absNorm v.1.asIdeal with hqdef
  have hqa : GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ (-z)) := by
    have hn : ∀ n : ℕ, GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ n) := by
      intro n
      have h1 : (((q : 𝓞 D.what₂.LL) ^ n : 𝓞 D.what₂.LL) : D.what₂.LL) = (q : D.what₂.LL) ^ n := by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
      rw [← h1]
      apply GlobalTheory.Square.AwayClosure.of_dvd (k := n)
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hqd) n
    rcases Int.eq_nat_or_neg (-z) with ⟨n, hn' | hn'⟩
    · rw [hn', zpow_natCast]; exact hn n
    · rw [hn', zpow_neg, zpow_natCast]; exact GlobalTheory.Square.AwayClosure.inv hQn (hn n)
  have hga : GlobalTheory.Square.IsAwayUnit (Qn G t) (g : D.what₂.LL) :=
    GlobalTheory.Square.AwayClosure.of_dvd (k := 1) (by rw [pow_one]; exact hgd.trans (Nat.cast_dvd_cast hqd))
  set a : D.what₂.LL := e * ((q : D.what₂.LL) ^ (-z) * (g : D.what₂.LL) * x) with ha
  have haA : GlobalTheory.Square.IsAwayUnit (Qn G t) a :=
    GlobalTheory.Square.AwayClosure.mul hea (GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul hqa hga) hxa)
  have hfa : D.what₂.embLL a = ((ν s' : ℂˣ) : ℂ) * eps Bs.ψ ν z := by
    rw [ha]
    unfold eps
    rw [hc]
    simp only [map_mul, map_zpow₀, map_natCast, he, hg, hx, Nat.cast_one, pow_one]
    congr 1
    rw [neg_one_mul]
  refine ⟨a⁻¹, GlobalTheory.Square.AwayClosure.inv hQn haA, ?_⟩
  rw [map_inv₀, ← hfa]
  rw [← hfa] at hf
  exact inv_mul_cancel₀ hf

end GlobalTheory.SqTwist
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar
variable {D : D7}

theorem coe_chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) (x : (AE D)ˣ) :
    ((chi c θ e x : Circle) : ℂ) = (((c.f (finY D x) : ℂˣ) : ℂ) *
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ c.n τ) ^ e := by
  rw [chi, MonoidHom.zpow_apply, Circle.coe_zpow, MonoidHom.mul_apply, Circle.coe_mul, coe_finChar, coe_infChar]

theorem exists_hecke_of_heckeU : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ), (e = 1 ∨ e = -1) →
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ N ∧ HasFinPart χ c e := by
  intro D N c e he
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : Continuous (chi c θ e) := by
    have h : ((chi c θ e : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (finChar c x * infChar θ c.n x) ^ e := by
      funext x; rw [chi, MonoidHom.zpow_apply, MonoidHom.mul_apply]
    rw [h]
    exact ((GlobalTheory.T.continuous_heckeCharacterFinitePart c).mul (continuous_infChar hθ c.n)).zpow e
  have haut : ∀ a : D.host.Eˣ, chi c θ e (Units.map (incA D).toMonoidHom a) = 1 := by
    intro a
    refine Circle.ext ?_
    rw [coe_chi, finY_incA]
    have h1 : ∀ τ, θ τ (infPart D ((Units.map (incA D).toMonoidHom a : (AE D)ˣ) : AE D)) = embT D τ (a : D.host.E) :=
      fun τ => GlobalTheory.FockCompare.comp_incA hθ τ _
    simp only [h1]
    rw [c.aut a, one_zpow, Circle.coe_one]
  refine ⟨chi c θ e, ⟨hcont, haut⟩, ?_, fun x y hxy => ?_⟩
  · refine GlobalTheory.T.heckeChar_restricts_eta_pow_of_sign D _ N ⟨hcont, haut⟩ (fun x y hy => Circle.ext ?_) θ hθ fun τ x h1 h2 h3 => ?_
    · rw [coe_chi, finY_mul_conj x y hy, c.norm, Units.val_one, one_mul, Circle.coe_one]
      have h4 : ∀ τ, θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ) = 1 := by
        intro τ
        have e1 : θ τ (infPart D (y : AE D)) = (Complex.normSq (θ τ (infPart D (x : AE D))) : ℂ) := by
          rw [hy, RingHom.map_mul, map_mul, GlobalTheory.FockCompare.comp_cA hθ, Complex.mul_conj]
        have hne : θ τ (infPart D (x : AE D)) ≠ 0 := by
          intro h0
          have := congrArg (fun z => θ τ (infPart D z)) (Units.mul_inv x)
          simp only [RingHom.map_mul, map_mul, h0, zero_mul, RingHom.map_one, map_one] at this
          exact zero_ne_one this
        have hp : 0 < Complex.normSq (θ τ (infPart D (x : AE D))) := Complex.normSq_pos.2 hne
        rw [e1, Complex.norm_real, Real.norm_of_nonneg hp.le]
        exact div_self (by exact_mod_cast hp.ne')
      simp only [h4, one_zpow, Finset.prod_const_one, one_zpow]
    · have hf : finY D x = 1 := Units.ext (by
        rw [coe_finY, h1, map_one, map_one, Units.val_one])
      rw [coe_chi, hf, map_one, Units.val_one, one_mul, Finset.prod_eq_single τ (fun τ' _ hτ' => by
        rw [h3 τ' hτ']; simp) (fun h => absurd (Finset.mem_univ τ) h), h2]
      have hn : (-1 : ℂ) / (‖(-1 : ℂ)‖ : ℂ) = -1 := by simp
      rw [hn, ← zpow_mul]
      obtain ⟨k, hk⟩ := c.par τ
      have hodd : Odd e := by rcases he with rfl | rfl <;> decide
      obtain ⟨j, hj⟩ := hodd
      have : c.n τ * e = (N : ℤ) + 2 * (k * e + j * (N : ℤ) - (N : ℤ) * 0) := by
        have : c.n τ = k + k + N := by linarith
        rw [this, hj]; ring
      rw [this, zpow_add₀ (by norm_num), zpow_mul, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, mul_one,
        zpow_natCast]
  · obtain ⟨h1, h2⟩ := hxy
    have hy : finY D x = y := Units.ext (by rw [coe_finY, h2, RingEquiv.symm_apply_apply])
    rw [coe_chi, hy, h1]
    simp only [map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one, mul_one]
    rw [Units.val_zpow_eq_zpow_val]

end GlobalTheory.HeckeUChar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.LieEigenspaceFinrank

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem isLieEigen_iff (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (w : Fin g → ℂ) :
    IsLieEigen act y τ' (expDer he w) ↔ w ∈ eigSp φ τ := by
  rw [mem_eigSp]
  constructor
  · intro h c
    rw [hτ]
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).1 (h.2 c)
  · intro h
    refine ⟨expDer_base he w, fun c => ?_⟩
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).2 (by rw [← hτ]; exact h c)

theorem comb_iff (he : IsExp y e) {n : ℕ} (w : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (z : Fin g → ℂ) :
    (∃ u : Fin n → (epsPt y ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (expDer he (w i)).left) ∧
      expDer he z = (List.ofFn u).prod) ↔ z = ∑ i, c i • w i := by
  constructor
  · rintro ⟨u, hu, hz⟩
    have hu' : u = fun i => expDer he (c i • w i) := by
      funext i
      exact Over.OverMorphism.ext (by rw [hu i, expDer_smul he])
    rw [hu', expDer_prod he (fun i => c i • w i)] at hz
    exact expDer_injective he hz
  · intro hz
    refine ⟨fun i => expDer he (c i • w i), fun i => expDer_smul he _ _, ?_⟩
    rw [expDer_prod he (fun i => c i • w i), hz]

theorem finrank_eigSp (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (n : ℕ) (h : LieMult act y τ' n) :
    Module.finrank ℂ (eigSp φ τ) = n := by
  obtain ⟨v, hv, hb⟩ := h
  choose w hw using fun i => expDer_surj he (v i) (hv i).1
  obtain rfl : v = fun i => expDer he (w i) := funext fun i => (hw i).symm
  have hwm : ∀ i, w i ∈ eigSp φ τ := fun i => (isLieEigen_iff he φ act hM τ τ' hτ _).1 (hv i)
  have key : ∀ z ∈ eigSp φ τ, ∃! c : Fin n → ℂ, z = ∑ i, c i • w i := by
    intro z hz
    have := hb _ ((isLieEigen_iff he φ act hM τ τ' hτ z).2 hz)
    simpa only [comb_iff he w] using this
  let L : (Fin n → ℂ) →ₗ[ℂ] eigSp φ τ := Fintype.linearCombination ℂ (fun i => (⟨w i, hwm i⟩ : eigSp φ τ))
  have hL : ∀ c, (L c : Fin g → ℂ) = ∑ i, c i • w i := by
    intro c
    simp [L, Fintype.linearCombination_apply]
  have hbij : Function.Bijective L := by
    rw [Function.bijective_iff_existsUnique]
    intro z
    obtain ⟨c, hc, hu⟩ := key z.1 z.2
    refine ⟨c, Subtype.ext (by rw [hL]; exact hc.symm), fun c' hc' => hu c' ?_⟩
    exact (congrArg Subtype.val hc').symm.trans (hL c')
  rw [← (LinearEquiv.ofBijective L hbij).finrank_eq]
  simp

theorem lie_type_of_unif (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ))
    (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ))
    (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ (o.fam h hL).A))
    (hU : UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 (Sp ℂ)) e) (τ : Fin D.a → D.F →+* ℂ)
    (hτ : ∀ (i : Fin D.a) (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) :
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
      ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
        u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  have he : IsExp (G := o.A) (𝟙 (Sp ℂ)) e := hU.2.2.1
  have hM : ∀ (a : D.O) z, e (ρ a *ᵥ z) = e z ≫ o.act.act a := hU.2.2.2.2.1
  have hx : 𝟙 (Sp ℂ) ≫ spMap σ = spMap σ := Category.id_comp _
  have hM' : ∀ (c : 𝓞 D.F) z, e ((ρ.comp (algebraMap (𝓞 D.F) D.O)) c *ᵥ z) = e z ≫ (o.act.toF D).act c :=
    fun c z => hM _ z
  refine ⟨fun i => ?_, fun u hu => ?_⟩
  · exact finrank_eigSp (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _
      (o.lieRank ℂ (𝟙 _) σ hx i)
  · obtain ⟨v, hv, hprod⟩ := o.lie ℂ σ (𝟙 _) hx (expDer (G := o.A) he u)
      ⟨expDer_base he u, (expDer_eigen_iff (G := o.A) he _ _ (hM _) (σ b.ρ) u).2 hu⟩
    choose w hw using fun i => expDer_surj (G := o.A) he (v i) (hv i 0).1
    obtain rfl : v = fun i => expDer (G := o.A) he (w i) := funext fun i => (hw i).symm
    have hu' : u = ∑ i, w i := expDer_injective he (hprod.trans (expDer_prod he w))
    rw [hu']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact (isLieEigen_iff (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _).1
      ⟨(hv i 0).1, fun c => (hv i c).2⟩

end GlobalTheory.LieEigenspaceFinrank
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_eInf (w : InfinitePlace F) : evInf F w (eInf F) = 1 := by
  show GlobalTheory.AutFunCompare.evW w ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1
  rw [map_one, map_one, map_one]

theorem compInf_unitArch (w : InfinitePlace F) (l : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    compInf F E w (unitArch F E l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = compInf F E w l := by
  change compInf F E w (eInf F • (l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) + (1 - eInf F) • 1) = _
  rw [map_add (f := _), compInf_smul, compInf_smul, evInf_eInf, map_sub, map_one, evInf_eInf, sub_self, zero_smul, one_smul,
    add_zero]

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

theorem isCompact_restrictedProduct_forall_mem {ι : Type} (R : ι → Type) [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (C : ∀ i, Set (R i)) (hC : ∀ i, IsCompact (C i)) (hCA : ∀ᶠ i in Filter.cofinite, C i ⊆ A i) :
    IsCompact {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ C i} := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : (Filter.cofinite : Filter ι) ≤ Filter.principal S := Filter.le_principal_iff.2 hCA
  have h1 : IsCompact (((↑) : RestrictedProduct R A (Filter.principal S) → ∀ i, R i) ⁻¹' Set.univ.pi C) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr (isCompact_univ_pi hC)
    rintro f hf
    refine ⟨⟨f, Filter.eventually_principal.2 fun i hi => hi (hf i trivial)⟩, rfl⟩
  convert h1.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

theorem repr_tmul_basis {n : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin n) F E) (a : R) (x : E) (j : Fin n) :
    (Algebra.TensorProduct.basis R b).repr (a ⊗ₜ[F] x) j = a * algebraMap F R (b.repr x j) := by
  simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem eventually_repr_mem_of_mem_intLoc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Module.Finite F E] (j : Fin (Module.finrank F E)) : ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  classical
  let b := Module.finBasis F E
  let β := RingOfIntegers.basis E
  have hfin : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr (β k : E) j) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (β k : E) j)).2
  refine hfin.mono fun v hv y hy => ?_
  have hx : ∀ x : 𝓞 E, algebraMap F (Fv F v) (b.repr (x : E) j) ∈ v.adicCompletionIntegers F := by
    intro x
    have e : (x : E) = ∑ k, (β.repr x k : ℤ) • (β k : E) := by
      conv_lhs => rw [← β.sum_repr x]
      simp

    rw [e, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine Subring.sum_mem (v.adicCompletionIntegers F).toSubring fun k _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem (v.adicCompletionIntegers F).toSubring (hv k) _
  refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)))
    (fun a ha x => ?_) (by simp) (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · rw [repr_tmul_basis]
    exact mul_mem ha (hx x)
  · rw [map_add (f := _), Finsupp.add_apply]; exact add_mem hy hz
  · rw [map_neg, Finsupp.neg_apply]; exact neg_mem hy

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

theorem repr_map_tens {n : ℕ} {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (b : Module.Basis (Fin n) F E) (φ : R →ₐ[F] R') (z : R ⊗[F] E) (j : Fin n) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) j =
      φ ((Algebra.TensorProduct.basis R b).repr z j) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end GlobalTheory.IdeleCyl


open GlobalTheory.IdeleCyl in
theorem GlobalTheory.IdeleCyl.exists_isCompact_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (M : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E)) (L : ∀ v : Pl (F := F), Set (Fv F v ⊗[F] E)),
    (∀ w, IsCompact (M w)) → (∀ v, IsCompact (L v)) → (∀ᶠ v in Filter.cofinite, L v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E))) →
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ z : AE F E, (∀ w, compInf F E w z ∈ M w) → (∀ v, compFin F E v z ∈ L v) → z ∈ K := by
  intro F E _ _ _ _ _ M L hM hL hLc
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let Mc : Fin (Module.finrank F E) → ∀ w : InfinitePlace F, Set w.Completion := fun j w =>
    (fun y => (Algebra.TensorProduct.basis w.Completion b).repr y j) '' M w
  let Lc : Fin (Module.finrank F E) → ∀ v : Pl (F := F), Set (Fv F v) := fun j v =>
    (fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j) '' L v
  have hMc : ∀ j w, IsCompact (Mc j w) := fun j w => by
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
    exact (hM w).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis w.Completion b).coord j))
  have hLc' : ∀ j v, IsCompact (Lc j v) := fun j v => by
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (hL v).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (Fv F v) b).coord j))
  let Q : Fin (Module.finrank F E) → Set (AF F) := fun j =>
    (Set.univ.pi (Mc j)) ×ˢ {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ Lc j v}
  have hQ : ∀ j, IsCompact (Q j) := fun j => by
    refine (isCompact_univ_pi (hMc j)).prod ?_
    have := isCompact_restrictedProduct_forall_mem (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (Lc j) (hLc' j) ((hLc.and (eventually_repr_mem_of_mem_intLoc F E j)).mono fun v ⟨h1, h2⟩ => by
        rintro _ ⟨y, hy, rfl⟩
        exact h2 y (h1 hy))
    exact this
  refine ⟨e.symm '' Set.univ.pi Q, (isCompact_univ_pi hQ).image he, fun z hz1 hz2 => ⟨e z, fun j _ => ⟨fun w _ => ?_, fun v => ?_⟩, e.symm_apply_apply z⟩⟩
  · refine ⟨compInf F E w z, hz1 w, ?_⟩
    exact repr_map_tens b (evInf F w) z j
  · refine ⟨compFin F E v z, hz2 v, ?_⟩
    exact repr_map_tens b (evFin F v) z j

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.IdeleCyl

end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  first | exact @GlobalTheory.ThetaTransformF.isThetaFunOF_thV | exact GlobalTheory.ThetaTransformF.isThetaFunOF_thV | (intros; apply GlobalTheory.ThetaTransformF.isThetaFunOF_thV <;> assumption)
end
