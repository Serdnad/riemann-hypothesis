module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle535
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle536
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle537
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.OnePart

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (S : M → Prop)
    (h : ∀ x ∈ s, ∃ l : ℂ, ∀ u, S u → x u = l • u) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, ∀ u, S u → a u = l • u := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
    refine ⟨r, fun u _ => ?_⟩
    simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨l + m, fun u hu => by rw [LinearMap.add_apply, hl u hu, hm u hu, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨m * l, fun u hu => by rw [Module.End.mul_apply, hm u hu, map_smul, hl u hu, smul_smul]⟩

variable {D : D7}

theorem scalar_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ hyp V P, π k u = u) (a b : List ℤ → ℂ)
    (ha : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π P (Finsupp.single (splitLab V.rank k) 1) u = a (splitLab V.rank k) • u)
    (hb : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = b (splitLab V.rank k) • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨z, hz, hzu⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  have gen : ∀ x ∈ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
      x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∃ l : ℂ, ∀ u, S u → x u = l • u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · exact ⟨a (splitLab V.rank k), fun u hu => ha u hu k hk⟩
    · refine ⟨b (splitLab V.rank k), fun u hu => ?_⟩
      have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π u (fu u hu)
      rw [GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single] at hc
      rw [← hc]
      exact hb u hu k hk
  obtain ⟨l, hl⟩ := adjoin_scalar _ S gen z hz
  exact ⟨l, fun u hu => by rw [← hzu u (fu u hu), hl u hu]⟩

theorem postOn_hk_single {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = opOf (rRep M) P (Finsupp.single d 1) U := by
  unfold rRep
  simp only [hk, opOf, Finsupp.sum_single_index, one_smul, zero_smul]
  ext v g
  simp [postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply, Finset.sum_apply]

private theorem star_algebraMap_eq (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c := by
  have hm : (algebraMap D.host.F D.host.E c) ∈ NumberField.maximalRealSubfield D.host.E :=
    NumberField.IsTotallyReal.le_maximalRealSubfield D.host.F c.2
  exact (NumberField.IsCMField.complexConj_eq_self_iff _ _).mpr hm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem good_conj (R : RealDat D A Ks) (t : T0) (P : Pl D.host.E) (hP : Good R t P) : Good R t (Formalism.DivisionValues.conjPl P) := by
  intro PP hPP
  obtain ⟨h1, h2⟩ := hP PP hPP
  rw [GlobalTheory.GoodPrimes.isConjPl_iff] at h2 ⊢
  refine ⟨fun e => h2 ?_, fun e => h1 ?_⟩
  · rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  · have e' := congrArg Formalism.DivisionValues.conjPl e
    rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at e'
    exact e'.symm

theorem good_of_offS (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (P : Pl D.host.E)
    (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P) : Good R A.μ0 P := by
  classical
  intro PP hPP
  have hPg : PP ∈ R.Pg := by
    rcases hPP with h1 | h1
    · exact h1
    · rw [GlobalTheory.LiftLower.Q_base hL] at h1
      simp at h1
  obtain ⟨x, hx, hy⟩ := h ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (Finset.mem_image_of_mem _ hPg)
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (x : D.host.F) := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E,
          IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]; rfl)
  have hnot := hy _ hcoe
  refine ⟨fun e => hnot (by rw [← e]; exact hx'), fun hc => ?_⟩
  obtain ⟨c', hc'P, hc'eq⟩ := hc _ hx'
  exact hy c' (by rw [hc'eq, hcoe, star_algebraMap_eq]) hc'P

private theorem primeIdem_and_sphOp_of_isHeckeOpFull {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E} {d : List ℤ} {Rp : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d Rp) :
    (∃ e f, IsPrimeIdem P e f ∧ OffS D Sb P ∧ (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
      (∀ g ∈ J, SuppF V f g → χ g = 1)) ∧ SphOp V P d Rp := by
  unfold Hecke₂ at h
  obtain ⟨e, f, ϖ, α, hS, hPf, h1, h2, h3, hJ, hχ, hα, hd, hR, hc⟩ := h
  refine ⟨⟨e, f, hPf, hS, hJ, hχ⟩, ?_⟩
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun hk => ⟨(hJ k hk.2).1 hk.1, hk.2⟩, fun hk => ⟨(hJ k hk.2).2 hk.1, hk.2⟩⟩
  unfold SphOp Hecke₂
  refine ⟨e, f, ϖ, α, GlobalTheory.LevOp.offS_empty, hPf, h1, h2, h3, fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hd, hR, ?_⟩
  rw [← hset]
  exact hc

private theorem mult_map_mul_right_eq_of_chi_eq_one {θ} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J) (hχ : χ k = 1) :
    ∀ v g, U v (g * k) = U v g := by
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v g
    rw [hT.lev v k hk g, hχ, one_mul]
  | zero => intro v g; rfl
  | add T T' _ _ h1 h2 =>
    intro v g
    simp only [MultilinearMap.add_apply, Pi.add_apply, h1 v g, h2 v g]
  | smul c T _ h1 =>
    intro v g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1 v g]

theorem mem_one_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hM i σ b
  classical
  obtain ⟨Sw, hSw⟩ : ∃ Sw : MMap (R.MW i σ) → Prop, ∀ u, Sw u ↔ ∃ w : (R.HW i σ).H,
      (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d →
        postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) ∧
      u = (R.HW i σ).e w := ⟨_, fun _ => Iff.rfl⟩
  refine ⟨fun P d => if h : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u
    then h.choose else 0, ?_⟩
  intro w hw
  have hW : ∀ w' : (R.HW i σ).H, (R.HW i σ).e w' ∈ R.Wall i σ := by
    intro w'
    rw [← (hM i σ).2.1]
    exact LinearMap.mem_range_self _ w'
  simp only [GlobalTheory.LiftLower.partH, Submodule.mem_comap, partFull, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨hW w, ?_⟩
  intro P d Rp hfull
  obtain ⟨⟨e, f, hPf, hS, hJ, hχ⟩, hsph⟩ := primeIdem_and_sphOp_of_isHeckeOpFull hfull
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := good_of_offS R hL P hS
  have hfix : ∀ w' : (R.HW i σ).H, ∀ k ∈ hyp (Wc D i) P,
      rRep (R.MW i σ) k ((R.HW i σ).e w') = (R.HW i σ).e w' := by
    intro w' k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.LevOp.mem_hyp hPf).1 hk
    have hkJ := (hJ k hk2).2 hk1
    have hinv := mult_map_mul_right_eq_of_chi_eq_one (hW w') k hkJ (hχ k hkJ hk2)
    unfold rRep
    ext v g
    simp [postOn, rLin, LinearMap.compMultilinearMap_apply, hinv]
  have hSfix : ∀ u, Sw u → ∀ k ∈ hyp (Wc D i) P, rRep (R.MW i σ) k u = u := by
    intro u hu k hk
    obtain ⟨w', -, rfl⟩ := (hSw u).1 hu
    exact hfix w' k hk
  have hex : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u := by
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · refine ⟨b P d, fun u hu => ?_⟩
      obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
      rw [← postOn_hk_single]
      exact hw' P d hG (Or.inr ⟨hc, Rp, hsph⟩)
    · refine scalar_of_split (rRep (R.MW i σ)) P hc Sw hSfix (b P) (b (Formalism.DivisionValues.conjPl P)) ?_ ?_ d
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        exact hw' P _ hG (Or.inl ⟨hc, k, hk, rfl⟩)
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        refine hw' (Formalism.DivisionValues.conjPl P) _ (good_conj R A.μ0 P hG) (Or.inl ⟨?_, k, hk, rfl⟩)
        rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
        exact fun h => hc h.symm
  have hsum : heckeOn (R.MW i σ) Rp ((R.HW i σ).e w) = ∑ γ ∈ Rp, rRep (R.MW i σ) γ ((R.HW i σ).e w) := by
    unfold rRep
    ext v g
    simp [heckeOn, postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply]
  rw [hsum, ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors (Wc D i) P).1 d Rp hsph).2 _ (rRep (R.MW i σ)) _ (hfix w), dite_eq_left hex]
  exact hex.choose_spec _ ((hSw _).2 ⟨w, hw, rfl⟩)

end GlobalTheory.ConjScalar.OnePart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.halfLattice_iff_frameAdjoint_isIntegralMatrix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x →
  (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) := by
  first | exact @GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | exact GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | (intros; apply GlobalTheory.HalfLatFrames.halfLat_iff_isIntM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  first | exact @GlobalTheory.InjEigen.inj_eig | exact GlobalTheory.InjEigen.inj_eig | (intros; apply GlobalTheory.InjEigen.inj_eig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  first | exact @GlobalTheory.EvenOnto.parBound_of_rapidDecay | exact GlobalTheory.EvenOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.EvenOnto.parBound_of_rapidDecay <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.heckeKernel_sum_eq_card_torsion_mul_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  first | exact @GlobalTheory.KernelSum.sum_ker_eq_card_mul | exact GlobalTheory.KernelSum.sum_ker_eq_card_mul | (intros; apply GlobalTheory.KernelSum.sum_ker_eq_card_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ θ : InfFam D, IsInfFam θ → ∀ d : ℕ, ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d (ω (g, h) f) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  first | exact @GlobalTheory.WeilWordGrowth.sup_words_growth | exact GlobalTheory.WeilWordGrowth.sup_words_growth | (intros; apply GlobalTheory.WeilWordGrowth.sup_words_growth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselLevel_unfolding_character_and_flatMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  first | exact @GlobalTheory.Asc.FromBes.isTh_and_fl | exact GlobalTheory.Asc.FromBes.isTh_and_fl | (intros; apply GlobalTheory.Asc.FromBes.isTh_and_fl <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrTheta

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem placeModel_induction (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁)
    (p : (WO S T → ℂ) → Prop) (p0 : p 0) (padd : ∀ f g, p f → p g → p (f + g)) (psmul : ∀ (c : ℂ) f, p f → p (c • f))
    (px : ∀ x ∈ half S T e, ∀ f, p f → p (heisO ψ S T x f))
    (py : ∀ y ∈ half S T (cA D e), ∀ f, p f → p (heisO ψ S T y f)) (pf : p f₀)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : p (T₁ Φ) := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e Λ
    have s1 : IsSBHalf e Λ fun t => ψ (symplO S T t y) * halfInd e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h₁.vac
    rw [one_smul] at v1
    rw [e1, h₁.trans _ s1 x ((isHalf_iff S T).2 hx), h₁.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    exact px x hx _ (py y hy _ pf)
  | zero => rw [LinearMap.map_zero]; exact p0
  | add f g _ _ hf hg => rw [LinearMap.map_add (f := _)]; exact padd _ _ hf hg
  | smul c f _ hf => rw [LinearMap.map_smul]; exact psmul _ _ hf

theorem isTheta_heis_fin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {a : WO S T} (ha : a.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
  have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf Unit {()} (fun _ => a) (fun _ => 1)
    fun _ _ => ha
  rwa [Finset.sum_singleton, one_smul] at this

theorem isTheta_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → infPart D e = 0 → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ Φ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm Φ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hz : IsThetaFunO ψ S T 0 := by
    refine ⟨?_, ?_, continuous_const, ?_⟩
    · intro γ w; simp only [Pi.zero_apply, mul_zero]
    · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    · intro k L _ _ w; exact contDiff_const
  have hadd : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := by
    intro f g hf hg
    refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
    · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
  have hsmul : ∀ (c : ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := by
    intro c f hf
    refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
    · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
  refine placeModel_induction ψ _ (fun u hu y hy => ?_) (fun x hx h => ?_)
    (fun k hk => ?_) (fun y hy => ?_) hTm (IsThetaFunO ψ S T) hz
    hadd hsmul
    (fun x hx f hf => isTheta_heis_fin hψ hf (infPart_of_half hinf ((isHalf_iff S T).2 hx)))
    (fun y hy f hf => isTheta_heis_fin hψ hf (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))) hf₀ hΦ
  · exact (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  · refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · exact exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))

end GlobalTheory.SchrTheta

end
end

section

open NumberField

theorem _root_.GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  first | exact @GlobalTheory.LatCountGauss.card_latCount | exact GlobalTheory.LatCountGauss.card_latCount | (intros; apply GlobalTheory.LatCountGauss.card_latCount <;> assumption)
end
