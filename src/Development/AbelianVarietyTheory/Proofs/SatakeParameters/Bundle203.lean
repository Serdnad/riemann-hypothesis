module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open GlobalTheory.DefU

namespace GlobalTheory.AlgMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RU_mul (x : UA E n) (a b : UA E n → ℂ) : RU E n x (a * b) = RU E n x a * RU E n x b := rfl

theorem isOpen_fix_of {ψ : UA E n → ℂ} (U : Set (finU (E := E) (n := n))) (hU : IsOpen U) (h1 : (1 : finU (E := E) (n := n)) ∈ U)
    (hs : ∀ k ∈ U, RU E n k ψ = ψ) : IsOpen {k : finU (E := E) (n := n) | RU E n k ψ = ψ} := by
  let St : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | RU E n k ψ = ψ}
      mul_mem' := fun {a b} ha hb => by
        change RU E n ((a : UA E n) * b) ψ = ψ
        rw [← RU_RU]
        change RU E n a (RU E n b ψ) = ψ
        rw [hb]; exact ha
      one_mem' := by
        change RU E n ((1 : finU (E := E) (n := n)) : UA E n) ψ = ψ
        simp
      inv_mem' := fun {a} ha => by
        change RU E n ((a : UA E n)⁻¹) ψ = ψ
        conv_lhs => rw [← (show RU E n (a : UA E n) ψ = ψ from ha)]
        rw [RU_RU, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : (St : Set (finU (E := E) (n := n))) ∈ nhds (1 : finU (E := E) (n := n)) :=
    Filter.mem_of_superset (hU.mem_nhds h1) hs
  exact Subgroup.isOpen_of_mem_nhds St this

theorem isAutFormU_mul {e φ : UA E n → ℂ} (he : IsAutFormU e) (hinv : ∀ g, ∀ x ∈ infU E n, e (g * x) = e g)
    (hφ : IsAutFormU φ) : IsAutFormU (e * φ) := by
  refine ⟨he.cont.mul hφ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, he.left γ hγ g, hφ.left γ hγ g]
  · refine isOpen_fix_of _ (he.level.inter hφ.level) ⟨by simp, by simp⟩ ?_
    rintro k ⟨hk1, hk2⟩
    rw [RU_mul, show RU E n k e = e from hk1, show RU E n k φ = φ from hk2]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (LinearMap.mulLeft ℂ e))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨RU E n k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    show e * RU E n k φ = RU E n k (e * φ)
    rw [RU_mul]
    congr 1
    funext g
    exact (hinv g k k.2).symm

end GlobalTheory.AlgMul

theorem GlobalTheory.AlgMul.exists_mul_algForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  intro E _ _ _ n W f e he hinv
  have hmem : (LinearMap.mulLeft ℂ e).comp f.1 ∈ algForms W := by
    refine ⟨fun v => GlobalTheory.AlgMul.isAutFormU_mul he hinv (f.2.1 v), fun x v => ?_⟩
    change e * f.1 (W.rep x v) = RU E n x (e * f.1 v)
    rw [f.2.2 x v, GlobalTheory.AlgMul.RU_mul]
    congr 1
    funext g
    exact (hinv g x x.2).symm
  exact ⟨⟨_, hmem⟩, fun v g => rfl⟩
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory


open Polynomial in
theorem trace_Eop_of_hasInfChar (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) (h : π.HasInfChar τ m) :
    ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hcard, hcap⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.card_eq_zero.1 hcard]; simp
  set c : ℂ := ((a : ℂ) - 1) / 2 with hc
  set P := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (GlobalTheory.CuspRep.Eop (a := a) τ) with hPdef
  have hP : P.coeff (a - 1) = ∑ i, GlobalTheory.CuspRep.Eop τ i i -
      algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) (((a : ℂ) * ((a : ℂ) - 1)) / 2) := by
    obtain ⟨-, -, hsub⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear a fun k =>
      GlobalTheory.CuspRep.Eop (a := a) τ k k - algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) ((k : ℕ) : ℂ)

    rw [hPdef, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.coeff_qdetPoly_top _ (a - 1) (by omega), hsub (a - 1) (by omega),
    Finset.sum_sub_distrib, ← map_sum, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.sum_fin_cast]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let Q : ℂ[X] := ∑ j ∈ Finset.range (a + 1), C (ℓ (P.coeff j φ)) * X ^ j
  let R : ℂ[X] := C (ℓ φ) * (m.map fun z => X + C (z - c)).prod
  have hdeg : P.natDegree < a + 1 :=
    Nat.lt_succ_of_le (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_qdetPoly_le _)
  have hQ : ∀ v : ℂ, Q.eval v = ℓ ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU v P) φ) := by
    intro v

    rw [GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum_range' _ hdeg, LinearMap.sum_apply, map_sum,
    eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, RingHom.id_apply, Module.End.mul_apply, ← map_pow,
      Module.algebraMap_end_apply, map_smul, map_smul, smul_eq_mul, mul_comm]
  have hQR : Q = R := by
    refine Polynomial.funext fun v => ?_
    rw [hQ, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly]
    have e := hcap (v - c) φ hφ
    rw [GlobalTheory.CuspRep.cap, show v - c + ((a : ℂ) - 1) / 2 = v by rw [hc]; ring] at e
    rw [e, map_smul, smul_eq_mul]
    simp only [R, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X]
    rw [mul_comm]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hco := congrArg (fun p : ℂ[X] => p.coeff (a - 1)) hQR
  have hlt : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  simp only [Q, R, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hlt] at hco
  have hm : (m.map fun z => X + C (z - c)).prod =
      ((m.map fun z => z - c).map fun r => X + C r).prod := by rw [Multiset.map_map]; rfl
  rw [hm, Multiset.prod_X_add_C_coeff _ (by simp [hcard]), Multiset.card_map, hcard,
    show a - (a - 1) = 1 by omega, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map] at hco
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', Multiset.sum_map_sub,
    Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at hco
  rw [hP] at hco
  simp only [LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at hco ⊢
  rw [hc] at hco
  linear_combination hco

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem norm_natCast_om_lt_one : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one


omit [NumberField E] [IsAlgClosure E Ω] [IsCMField E] in
theorem valuation_natCast_lt_one_of_induces {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    A.valuation ((l : ℕ) : Ω) < 1 := by
  have hn : ‖Bw.j ((l : ℕ) : Ω)‖ < 1 := by rw [map_natCast]; exact norm_natCast_om_lt_one
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    have h1 := congrArg Bw.j h0
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hmem : ((l : ℕ) : Ω) ∈ A := (hj _).2 hn.le
  have hinv : ((l : ℕ) : Ω)⁻¹ ∉ A := by
    intro hm
    have h1 := (hj _).1 hm
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖Bw.j ((l : ℕ) : Ω)‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hl0)
    have := (one_lt_inv₀ hpos).2 hn
    linarith
  refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 hmem) fun h1 => hinv ?_
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem mem_of_induces {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  refine (hA _).1 ?_
  have h := valuation_natCast_lt_one_of_induces Bw hj
  simpa [map_natCast] using h

end GlobalTheory.GalCut
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

section Res

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω]

def decRes (A : ValuationSubring Ω) : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) where
  toFun g := ⟨AlgEquiv.restrictScalars K (g : _root_.Formalism.ConjugateSelfDual.G L Ω), by
    have hg := mem_Dec.mp g.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Res

end GlobalTheory.AboveLRes

noncomputable section

namespace GlobalTheory.AboveLRes

section Bridge

variable {l : ℕ} [Fact l.Prime] {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem exists_bridge (Bw : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O) (hj : Induces Bw) (S : FinExt l) :
    ∃ (LL' : FinExt l) (Bw' : LocBridge l L Ω (_root_.ReciprocityTheory.Gal.Dec (F := L) A) ↥(OL LL')), Bw'.j = Bw.j ∧ S.1 ≤ Bw'.LL.1 ∧ Bw.Kw.1 ≤ Bw'.Kw.1 := by
  let jL := Bw.j.comp (algebraMap L Ω)
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range jL),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range jL⟩
  have := K'.2
  let N : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] ↥K'.1 (PadicAlgCl l),
    normalClosure.is_finiteDimensional ℚ_[l] ↥K'.1 (PadicAlgCl l)⟩
  let LL' : FinExt l := supExt S N
  have hN : N.1 ≤ LL'.1 := le_sup_right
  have hS : S.1 ≤ LL'.1 := le_sup_left
  obtain ⟨e, he, he', hec⟩ :=
    GlobalTheory.PlaceBridge.exists_mulEquiv (E := L) (j := Bw.j) hj K' rfl
  let B : LocBridge l L Ω (_root_.ReciprocityTheory.Gal.Dec (F := L) A) ↥(OL LL') := {
    Kw := K'
    j := Bw.j
    j_E := fun x => IntermediateField.subset_adjoin ℚ_[l] (Set.range jL) (Set.mem_range_self x)
    j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure jL
    e := e
    e_cont := he
    e_symm_cont := he'
    e_comm := hec
    LL := LL'
    LL_split := fun τ x => hN (τ.fieldRange_le_normalClosure ⟨x, rfl⟩)
    eO := RingEquiv.refl ↥(OL LL')
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }
  refine ⟨LL', B, rfl, hS, ?_⟩
  show Bw.Kw.1 ≤ K'.1
  rw [BridgeInd.kw_eq_adjoin Bw, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
  show Bw.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
  rw [← IsScalarTower.algebraMap_apply]

variable {O' : Type} [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (Bw : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O) (Bw' : LocBridge l L Ω (_root_.ReciprocityTheory.Gal.Dec (F := L) A) O')
  (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
include hjj hle

theorem decRes_e_symm (g' : ↥(GK Bw'.Kw)) :
    decRes (K := K) A (Bw'.e.symm g') = Bw.e.symm ⟨g', GK_le hle g'.2⟩ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply Bw.j.injective
  have h1 := Bw'.e_comm (Bw'.e.symm g') x
  have h2 := Bw.e_comm (Bw.e.symm ⟨g', GK_le hle g'.2⟩) x
  rw [MulEquiv.apply_symm_apply] at h1 h2
  rw [hjj] at h1
  exact h1.symm.trans h2

theorem repE_decRes (T : FinExt l) {m : ℕ} (t : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin m) ↥T.1) :
    Bw'.repE T (t.comp (decRes A)) = GlobalTheory.Pst.resTo (Bw.repE T t) hle := by
  ext g' v i
  simp only [LocBridge.repE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.Pst.resTo]
  rw [decRes_e_symm Bw Bw' hjj hle]
  rfl

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v')

theorem weilToGK_eq (σ : Weil h) (σ' : Weil h') (hσ : ∀ z : Ω, (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) z = (σ' : _root_.Formalism.ConjugateSelfDual.G L Ω) z) :
    (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l) := by
  have e1 := decRes_e_symm Bw Bw' hjj hle (weilToGK Bw' h' σ')
  have e2 : decRes (K := K) A (Bw'.e.symm (weilToGK Bw' h' σ')) = Subgroup.inclusion (Weil_le_Dec h) σ := by
    rw [weilToGK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subtype.ext (AlgEquiv.ext fun z => (hσ z).symm)
  rw [e2, MulEquiv.eq_symm_apply] at e1
  exact (congrArg Subtype.val e1).symm

end Bridge

end GlobalTheory.AboveLRes
end
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory GlobalTheory.Cong GlobalTheory.UnitaryBC

namespace GlobalTheory.CrysNoMono

theorem crystalline_decompositionGroup_no_monodromy : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw) (ρ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) (Qbar l)),
    IsCrysAt P Bw ρ → (GlobalTheory.Pst.wdAt P ι Bw h hj ρ).mono0 := by
  intro E Ω _ _ _ _ _ l _ ι a P w A h O _ _ _ Bw hj ρ hc
  by_cases hr : IsPstAt P Bw ρ
  · exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι ρ hr).2 hc.isPotCrysAt
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, trivWD]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))

end GlobalTheory.CrysNoMono
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.WeakTheRep

theorem eq_of_mono0_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} (x y : WD h)
    (hx : x.mono0) (hy : y.mono0) (hc : ∀ g, x.charPol g = y.charPol g) : x = y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hx hy
  obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b
    (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
  exact WD.sound ⟨e, he, fun v => by rw [hx, hy]; simp⟩

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') {K : Subgroup G}
    (h : GlobalTheory.PRep.fixed ρ K ≠ ⊥) : GlobalTheory.PRep.fixed ρ' K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e v, ?_, fun h0 => hv0 ?_⟩
  · refine GlobalTheory.ContraRefl.mem_fix.2 fun g hg => ?_
    have h1 := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h1
    rw [GlobalTheory.ContraRefl.mem_fix.1 hv g hg] at h1
    exact h1.symm
  · exact e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm)

end GlobalTheory.WeakTheRep

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut.SsTwist

open Polynomial

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}

theorem charPol_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (x.charPol g).scaleRoots (ξ g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_end _ (Units.ne_zero _)]

theorem scaleRoots_cancel {p q : ℂ[X]} {c : ℂ} (hc : c ≠ 0) (H : p.scaleRoots c = q.scaleRoots c) : p = q := by
  have := congrArg (fun P : ℂ[X] => P.scaleRoots c⁻¹) H
  simpa only [← scaleRoots_mul, mul_inv_cancel₀ hc, scaleRoots_one] using this

end GlobalTheory.GalCut.SsTwist
end
