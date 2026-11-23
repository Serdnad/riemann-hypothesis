module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomCusp

theorem isAniso_neg {D : D7} {A : HSp D} (h : IsAniso A) : IsAniso (GlobalTheory.Grid.neg A) := by
  rintro r C ⟨hr, hC, h0⟩
  refine h r C ⟨hr, hC, ?_⟩
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [e, Matrix.mul_neg, Matrix.neg_mul] at h0
  exact neg_eq_zero.1 h0

theorem const_one_mem_cuspForms_of_anisotropic {D : D7} {V : HSp D} (h : IsAniso V) (θ : GlobalTheory.Mem.Th.InfF D) (A : CptF V) :
    (fun _ => (1 : ℂ)) ∈ A0 θ V A :=
  GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem one_mem_A0_of_isBottomTri : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t cA _
  exact const_one_mem_cuspForms_of_anisotropic (isAniso_neg (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.std.1)) W.θ cA

end GlobalTheory.BottomCusp
end
end

section

open NumberField IsDedekindDomain
open Classical

noncomputable section

namespace GlobalTheory.SqTop.TwVal

open Formalism.BasicNotions Formalism.IndefR.Links
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

variable {D : D7}

theorem under_eq_of_conj {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem expAt_mul_unr {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.UnrAt P) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  have hm : ξ.LevelLe P m := hξ.levelLe m
  refine ⟨fun hx => (h m).1 ?_, fun hn => ((h m).2 hn).mul hm⟩
  have := hx.mul hm.inv
  rwa [mul_inv_cancel_right] at this

theorem expAt_mul_low {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n k : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.LevelLe P k) (hk : k < n) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  refine ⟨fun hx => ?_, fun hn => ((h m).2 hn).mul (Model.levelLe_mono hξ (by omega))⟩
  by_contra c
  have a := Model.levelLe_mono hx (le_max_left m k)
  have b := Model.levelLe_mono hξ (le_max_right m k)
  have := a.mul b.inv
  rw [mul_inv_cancel_right] at this
  have := (h _).1 this
  omega

theorem isValChar_nu_twist {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    rw [div_mul_eq_mul_div]
  obtain ⟨n, hn, hf⟩ := hL.xi_fin t
  obtain ⟨hu0, htr0, hinf0, hloc0⟩ := (Model.isValChar_nu hL G i j hs).1
  have unipotent_character_trivial_off_S0 : ∀ PP ∈ GlobalTheory.SqTop.twPl G t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ G.pl.S0 := fun PP hPP hS => by
    simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    have hQ : PP ∈ L.Q t := hPP.1.resolve_left hPP.2
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h | h
    · exact G.pl.levelPlace_ne_basePlace t PP hQ h
    · exact hPP.2 (by rw [G.pl.w_Q t PP hQ h]; exact Finset.mem_image_of_mem _ hS)
  have ram : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), ¬ (L.xiH t).UnrAt PP →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D ∨
        (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := by
    intro PP hPP
    obtain ⟨P', hP', hu⟩ : ∃ P' ∈ L.Q t, P'.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
      rcases (hL.Q_ram t PP).1 hPP with h | ⟨P', h, hc⟩
      · exact ⟨PP, h, rfl⟩
      · exact ⟨P', h, under_eq_of_conj hc⟩
    by_cases hW : P' ∈ G.pl.W0
    · left
      obtain ⟨u, hu', rfl⟩ := Finset.mem_image.1 hW
      rw [← hu, G.pl.under_w hu']
      exact (G.pl.mem_S0_of_sum_eq.1 hu').resolve_left fun h => G.pl.levelPlace_ne_basePlace t _ hP' ((G.pl.under_w hu').trans h)
    · right
      exact Finset.mem_image.2 ⟨P', by
        simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union]; exact ⟨Or.inr hP', hW⟩, hu⟩
  rw [e]
  refine ⟨hu0.mul (HChar.isUnitary_of_order hn hf), htr0.mul (hL.xi_triv t), fun k => ?_,
    fun v P hP => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (L.xiH t) hn hf k, mul_one]
    exact hinf0 k
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    obtain ⟨PP, hPP, hu⟩ := Finset.mem_image.1 hv
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    rw [Model.expIn_condF, if_neg (hu ▸ unipotent_character_trivial_off_S0 PP hPP)] at h0
    exact (Model.levelLe_mono ((h0 0).2 le_rfl) (Nat.zero_le 1)).mul (hL.xi_tame t P)
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    by_cases hr : (L.xiH t).UnrAt P
    · exact expAt_mul_unr h0 hr
    · have hS1 := (ram P hr).resolve_right hv
      refine expAt_mul_low h0 (hL.xi_tame t P) ?_
      rw [Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)), condExp,
        if_neg fun (e : P.under (𝓞 D.host.F) = G.pl.v0) => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ hS1)]
      norm_num

end GlobalTheory.SqTop.TwVal
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

theorem auxiliaryProduct_mem_place_of_exceptionalSet (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hp := v.isPrime
  simp only [Nat.cast_mul, hp.mul_mem_iff_mem_or_mem]
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h
  · exact Or.inr P.basePlace_over_qZero
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

theorem levQ_le (P : Places L) :
    levQ P ≤ ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D) ^ Module.finrank ℤ (𝓞 D.host.F)) ^ 2 := by
  classical
  set M := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D with hM
  have hmem : ((M : ℕ) : 𝓞 D.host.F) ∈ ∏ v ∈ P.S0, v.asIdeal := by
    rw [← Ideal.dvd_span_singleton]
    exact Finset.prod_dvd_of_coprime (fun v _ w _ hne => HeightOneSpectrum.isCoprime_of_ne v w hne)
      fun v hv => Ideal.dvd_span_singleton.2 (auxiliaryProduct_mem_place_of_exceptionalSet P hv)
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast, map_prod] at hdvd
  have hM0 : 0 < M := by
    have := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  have hle := Nat.le_of_dvd (pow_pos hM0 _) hdvd
  calc levQ P = ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ condExp P v := rfl
    _ ≤ ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ 2 := by
      refine Finset.prod_le_prod' fun v _ => Nat.pow_le_pow_right ?_ ?_
      · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
      · unfold condExp; split_ifs <;> norm_num
    _ = (∏ v ∈ P.S0, Ideal.absNorm v.asIdeal) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hle 2

theorem kap_add_le (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) {s : ℕ}
    (hs : s ≤ halfRank D i j) (τ : D.what₂.Tau) : (kap D 1 i j s τ : ℝ) + s ≤ 5 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hhc, -⟩ := h
  have e := (Model.kap_add D 1 i j τ hs).1
  have e' := congrArg (Int.cast : ℤ → ℝ) e
  push_cast at e'
  rw [e']

  have he : (((num D 1 τ).e (j + 1) : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    have s1 := ((GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 j)
    have s2 : (((D.hc τ).e j : ℚ) : ℝ) = (((num D 1 τ).e (j + 1) : ℤ) : ℝ) := by
      rw [s1]; push_cast; rfl
    rw [← s2]; exact (hhc τ j).2

  set G0 := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have hv0 : 0 < D.R.k - 1 := by omega
  have hv : (G0.v 2 : ℚ) ≤ large₂.Sc := by
    have s1 := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, hv0⟩
    have := (large₂.cloud_v τ ⟨0, hv0⟩).2
    rw [s1] at this
    exact_mod_cast this
  have hmid : ((G0.mid (D.R.m - i) : ℚ) : ℝ) ≤ large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 := by
    have hi := i.2
    have hm : G0.m = D.R.m := rfl
    have hg : G0.ga = gap D 1 := rfl
    simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a, hm, hg]
    have hg0 : (0 : ℝ) ≤ gap D 1 := by positivity
    have hi' : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
    have hv' : ((G0.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    have c1 : ((D.R.m - (i : ℕ) - 1 : ℕ) : ℝ) = D.R.m - (i : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have c2 : ((D.R.m - (i : ℕ) : ℕ) : ℝ) = D.R.m - (i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
    push_cast
    rw [c1, c2]
    have hv'' : ((G0.v 2 : ℤ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    nlinarith [mul_le_mul_of_nonneg_right hi' hg0]
  have hc : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ large₂.sc.b := by
    have h1 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℚ) ≤ G0.mid (D.R.m - i) := Int.floor_le _
    have h2 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ ((G0.mid (D.R.m - i) : ℚ) : ℝ) := by exact_mod_cast h1
    linarith
  linarith

end GlobalTheory.SqTop.SizesBound

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizes (c : ℝ) : GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  refine ⟨0, fun ε CF _ => ⟨2 * |c| + 100, 3, fun C hC D large₂ _ hx hR T Lc μ₀ _ G i j s _ hs => ?_⟩⟩
  have hS := hR.size
  obtain ⟨-, hSA, -, -, -, -, -, hgL, hqL, hrd, hcd, -, -, -⟩ := hR.size
  have hpde : Real.log (D.host.pde : ℝ) ≤ large₂.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ large₂.sc.L :=
    hSA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

  have hx1 : 1 < large₂.sc.x := by linarith
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp hLpos.le
  have hlx : 1 ≤ Real.log large₂.sc.x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _

  have h1 : c * (Module.finrank ℚ D.host.E : ℝ) ≤ 2 * |c| * D.R.f := by
    rw [Formalism.L2.Pj.hostSize_finrank D]; push_cast
    nlinarith [le_abs_self c]

  have h2 : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * large₂.sc.L := by
    have e : Real.log |((discr D.host.E : ℤ) : ℝ)| = logdE D := rfl
    rw [e, Formalism.BasicNotions.logdE_eq_rd]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    nlinarith

  have h3 : Real.log (levQ G.pl) ≤ 2 * D.R.f * (21 * large₂.sc.L + 2) := by
    have hle := levQ_le G.pl
    rw [NumberField.RingOfIntegers.rank, GlobalTheory.ColClassCompare.finrank_F] at hle
    have hpos : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
      pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
    have hle' : (levQ G.pl : ℝ) ≤ ((((D.host.g 0 : ℕ) : ℝ) * (D.host.g 1 : ℕ) * (D.host.pde : ℕ) * (D.host.pde' : ℕ) *
        (q0 D : ℕ)) ^ D.R.f) ^ 2 := by exact_mod_cast hle
    have hl := Real.log_le_log (by exact_mod_cast hpos) hle'
    have p0 := (D.host.g_prime 0).pos
    have p1 := (D.host.g_prime 1).pos
    have p2 := D.host.pde_prime.pos
    have p3 := D.host.pde'_prime.pos
    have p4 := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    push_cast at hl
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hl
    have g0 := hgL 0
    have g1 := hgL 1
    push_cast at hl
    nlinarith

  have h4 : ∑ τ, Real.log (1 + ((kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s τ : ℝ) + s)) ≤
      D.R.f * (5 + large₂.sc.L) := by
    have hk : ∀ τ, Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ 5 + large₂.sc.L := by
      intro τ
      have k1 := kap_add_le large₂ hS i j hs τ
      have k0 : (0 : ℝ) ≤ (kap D 1 i j s τ : ℝ) + s := by positivity
      calc Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ Real.log (6 * large₂.sc.b) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 6 + large₂.sc.L := by rw [Real.log_mul (by norm_num) (by linarith), hlogb]
        _ ≤ 5 + large₂.sc.L := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
          linarith
    calc _ ≤ ∑ _τ : D.what₂.Tau, (5 + large₂.sc.L) := Finset.sum_le_sum fun τ _ => hk τ
      _ = D.R.f * (5 + large₂.sc.L) := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

  show _ ≤ C * D.R.f * large₂.sc.b * (Real.log large₂.sc.b + Real.log large₂.sc.x)
  rw [hlogb]
  have hC0 : 0 ≤ C := by have := abs_nonneg c; linarith
  have t1 : (2 * |c| + 100) * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.L + 1) := by
    have : 0 ≤ (D.R.f : ℝ) * (large₂.sc.L + 1) := by positivity
    nlinarith
  have t2 : large₂.sc.L + 1 ≤ large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) := by nlinarith
  have t3 : C * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) :=
    mul_le_mul_of_nonneg_left t2 (by positivity)
  have t4 : 0 ≤ (D.R.f : ℝ) * large₂.sc.L := by positivity
  have t5 : 0 ≤ |c| * D.R.f := by positivity
  nlinarith

end GlobalTheory.SqTop.SizesBound

end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_quot_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    Nat.card (𝓞 D.host.E ⧸ P'.asIdeal) = Nat.card (𝓞 D.host.E ⧸ P.asIdeal) := by
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)
  have hle : P.asIdeal.map σ ≤ P'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : σ c = c' := RingOfIntegers.ext h2.symm
    show σ c ∈ P'.asIdeal
    rw [e]; exact h1
  have hmax : (P.asIdeal.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ (hp := P.isMaximal)
  have e : P'.asIdeal = P.asIdeal.map σ := (hmax.eq_of_le P'.isPrime.ne_top hle).symm
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal P'.asIdeal σ e).toEquiv).symm

theorem twist_ram_prime_dvd_Qn : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  classical
  intro D T Lc sc G μ₀ hL i j t w hxi hnu

  have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro hS
    have hv := (Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1
    have hE := hv.2.2.2 (w.under (𝓞 D.host.F)) w rfl
    have hexp := (hE.2 (Finset.notMem_empty _) 0).1 ((Formalism.L2.Host.HChar.unrAt_iff _ _).1 hnu)
    rw [Model.expIn_condF, if_pos hS, condExp] at hexp
    split_ifs at hexp <;> omega

  obtain ⟨PP, hPP, hw⟩ : ∃ PP ∈ Lc.Q t, w = PP ∨ Formalism.IndefR.Lev.IsConjPl PP w := by
    rcases (hL.Q_ram t w).1 hxi with h | ⟨PP, h, hc⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨PP, h, Or.inr hc⟩
  have hunder : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = w.under (𝓞 D.host.F) := by
    rcases hw with rfl | hc
    · rfl
    · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
  have hW0 : PP ∉ G.pl.W0 := by
    intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    apply hS0
    rw [← hunder, G.pl.under_w hv]
    exact hv
  have hloc : PP ∈ GlobalTheory.FunObj.locPl G t := Finset.mem_union_right _ hPP
  have htw : PP ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t PP hPP
  have hnorm : Ideal.absNorm PP.asIdeal = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hcard]
  refine ⟨q, hq, ?_, ?_, PP, hloc, hnorm⟩
  · rcases hw with rfl | hc
    · exact hcard
    · rw [card_quot_of_isConjPl hc]; exact hcard
  · rw [← hnorm]
    exact Finset.dvd_prod_of_mem _ htw

end GlobalTheory.SqTop
end

section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.KummerTwistLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_places_under_split_coprime_conductor : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL t q hq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP
    rcases Finset.mem_union.1 hP.1 with h | h
    · exact absurd h hP.2
    · exact ⟨h, hP.2⟩
  refine ⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩
  · apply (hL.Q_pl t P hP'.1).2 P hP'.1
    intro c hc
    refine ⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩
    have h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [← e] at h
  · exact congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)
  · have hS : P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
      intro h
      rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
      · exact G.pl.levelPlace_ne_basePlace t P hP'.1 h0
      · apply hP'.2
        rw [G.pl.w_Q t P hP'.1 h1]
        exact Finset.mem_image_of_mem _ h
    have h0 := GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))
    rw [if_neg hS] at h0
    have hne : GlobalTheory.FunObj.SqNum.condF G.pl ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    exact (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left (P.under (𝓞 D.host.F)).prime hne)).1 h0

end GlobalTheory.KummerTwistLemmas
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, (∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) → γ = 1 := by
  first | exact @GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | exact GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | (intros; apply GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ <;> assumption)
end
