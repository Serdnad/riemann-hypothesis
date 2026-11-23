module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle575
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle432
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.MovedTwist

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (hinf : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq : (q : 𝓞 L) ∈ v.asIdeal) (x : (v.adicCompletion L)ˣ) :
    UnitOff q ((χ.loc v x : ℂˣ) : ℂ) := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt L χ
  have hinf' : (χ ^ N).HasInf φ fun i => n i * N := fun k => by
    have e : (χ ^ N).inf k = χ.inf k ^ N := rfl
    rw [e, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_mul, zpow_natCast]
  have hv := GlobalTheory.ValUnit.unitOff_val L (χ ^ N) I φ _ v q hinf' (by simp [hu]) (fun w x hx _ => hu w x hx) (hu v) hq
  refine unitOff_of_pow hN ?_
  have e : ((χ.loc v x : ℂˣ) : ℂ) ^ N = (((χ ^ N).loc v x : ℂˣ) : ℂ) := by
    rw [← Units.val_pow_eq_pow_val]; rfl
  rw [e]
  set u : (v.adicCompletion L)ˣ := atFin v (unif v) with hudef
  have h0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  have hu1 : Valued.v (u : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) = WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion L))) :=
    (WithZero.exp_log h0).symm
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((x * u ^ m : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1 := by
    refine ⟨WithZero.log (Valued.v (x : v.adicCompletion L)), ?_⟩
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hx' : x = (x * u ^ m) * u ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx', map_mul, hu v _ hm, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  exact unitOff_zpow hv _

theorem unitOff_sqrt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq0 : q ≠ 0)
    (hq : (q : 𝓞 L) ∈ v.asIdeal) : UnitOff q ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) := by
  refine unitOff_of_pow two_pos ?_
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hq)
  rw [Ideal.absNorm_span_natCast] at h
  obtain ⟨b, hb⟩ := h
  have hi : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine unitOff_of_mul_eq (m := Module.finrank ℤ (𝓞 L)) (hi _) (hi b) ?_ hq0
  rw [← Nat.cast_mul, ← hb, Nat.cast_pow]

variable {D : D7}

theorem unitOff_apow_half {P : Pl D.host.E} {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (x : (Kw P)ˣ) (z : ℤ) :
    UnitOff q (apow x ((z : ℂ) / 2)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.MovedField.exists_zpow_unit P x
  have h1 : valuation (Kw P) (((x * unifAt P ^ n : (Kw P)ˣ)) : Kw P) = 1 := (Good.isEquiv_Kw P).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt P ^ n) * unifAt P ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt P).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, GlobalTheory.MovedField.natCast_cpow_half]
  exact unitOff_zpow (unitOff_sqrt_absNorm P hq0 hq) _

theorem lossLe_unit_mul {w : PlL D} {q : ℕ} (hw : (q : 𝓞 D.what₂.LL) ∉ w.asIdeal) {u z : ℂ} {c : ℝ}
    (hu : u ∈ D.what₂.embLL.fieldRange) (hq : UnitOff q u) (hz : LossLe w z c) : LossLe w (u * z) c := by
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨y', rfl, h'⟩ := hz
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y' = 0
  · exact Or.inl (by rw [h0, mul_zero])
  have h' := h'.resolve_left h0
  obtain ⟨hy, k, hk, -⟩ := hq
  have hy0 : y ≠ 0 := fun e => hy (by rw [e, map_zero])
  have hq0 : (q : D.what₂.LL) ≠ 0 := by
    have : q ≠ 0 := fun e => hw (by rw [e, Nat.cast_zero]; exact zero_mem _)
    exact_mod_cast this
  have hint : IsIntegral ℤ ((q : D.what₂.LL) ^ k * y) := by
    rw [← isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective]
    simpa using hk
  have hqk : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hw (w.isPrime.mem_of_pow_mem k (by simpa using h))
  have h1 : vw w ((q ^ k : ℕ) : D.what₂.LL) = 0 := by
    have h0 : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := fun e => hqk (e ▸ zero_mem _)
    have h1 := Formalism.EigenvalueLevelCeiling.intValuation_eq_exp' w _ h0
    rw [(w.intValuation_eq_one_iff).2 hqk, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_injective h1
    have h3 : (((q ^ k : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((q ^ k : ℕ) : D.what₂.LL) := by simp
    rw [h3] at h2
    omega
  have h2 : 0 ≤ vw w ((q : D.what₂.LL) ^ k * y) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (⟨_, hint⟩ : 𝓞 D.what₂.LL)
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hq0) hy0, ← Nat.cast_pow, h1, zero_add] at h2
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hy0 h0, Int.cast_add]
  have h3 : (0 : ℝ) ≤ (vw w y : ℝ) := by exact_mod_cast h2
  linarith

def UnitIn (K : Subfield ℂ) (q : ℕ) (u : ℂ) : Prop := u ∈ K ∧ UnitOff q u

theorem UnitIn.mul {K : Subfield ℂ} {q : ℕ} {u v : ℂ} (h : UnitIn K q u) (h' : UnitIn K q v) : UnitIn K q (u * v) :=
  ⟨mul_mem h.1 h'.1, unitOff_mul h.2 h'.2⟩

theorem UnitIn.inv {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) : UnitIn K q u⁻¹ := ⟨inv_mem h.1, unitOff_inv h.2⟩

theorem UnitIn.pow {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) (n : ℕ) : UnitIn K q (u ^ n) :=
  ⟨pow_mem h.1 n, unitOff_pow h.2 n⟩

theorem unitIn_one (K : Subfield ℂ) (q : ℕ) : UnitIn K q 1 := ⟨one_mem K, unitOff_one q⟩

theorem unitIn_prod {α : Type*} {K : Subfield ℂ} {q : ℕ} (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, UnitIn K q (f a)) → UnitIn K q (l.map f).prod
  | [], _ => by simpa using unitIn_one K q
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (unitIn_prod f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedTwist


open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
theorem GlobalTheory.MovedTwist.moved_lossLe : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    show UnitIn K q ((((GlobalTheory.FunObj.muBase _ j * _).loc _) x : ℂˣ) : ℂ)
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x * (R.xiH t).loc P.1 x : ℂˣ) : ℂ)
    rw [Units.val_mul]
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · simpa [GlobalTheory.FunObj.muBase, HChar.loc] using unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · simpa [HChar.loc] using unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, if_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)

end
end

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

theorem _root_.GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  first | exact @GlobalTheory.BottomWitt.wittIndex_eq_zero | exact GlobalTheory.BottomWitt.wittIndex_eq_zero | (intros; apply GlobalTheory.BottomWitt.wittIndex_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end
end

section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  first | exact @GlobalTheory.SqTop.nuH_not_unrAt_twPl | exact GlobalTheory.SqTop.nuH_not_unrAt_twPl | (intros; apply GlobalTheory.SqTop.nuH_not_unrAt_twPl <;> assumption)
end

section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.twist_places_under_prime_not_mem_of_norm_coprime : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL}, (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal → ∀ q ∈ ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal := by
  first | exact @GlobalTheory.twPl_under_not_mem_prime | exact GlobalTheory.twPl_under_not_mem_prime | (intros; apply GlobalTheory.twPl_under_not_mem_prime <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottomRanks_arithmetic_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  first | exact @GlobalTheory.BotRankSize.bottom_ranks | exact GlobalTheory.BotRankSize.bottom_ranks | (intros; apply GlobalTheory.BotRankSize.bottom_ranks <;> assumption)
end

section

open NumberField GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

theorem _root_.GlobalTheory.T.gridSizes_log_bound : ∀ c : ℝ, GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  first | exact @GlobalTheory.SqTop.SizesBound.sizes | exact GlobalTheory.SqTop.SizesBound.sizes | (intros; apply GlobalTheory.SqTop.SizesBound.sizes <;> assumption)
end

section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m) {s : ℕ}, s ≤ GlobalTheory.FunObj.SqNum.halfRank D i j → GlobalTheory.CMVal.IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D sc.cGap i j s) (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (GlobalTheory.FunObj.SqNum.nuH G t i j) := by
  first | exact @GlobalTheory.SqTop.TwVal.isValChar_nu_twist | exact GlobalTheory.SqTop.TwVal.isValChar_nu_twist | (intros; apply GlobalTheory.SqTop.TwVal.isValChar_nu_twist <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.twist_only_ramified_place_prime_residue_dvd_norm : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  first | exact @GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | exact GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | (intros; apply GlobalTheory.SqTop.twist_ram_prime_dvd_Qn <;> assumption)
end

section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | exact GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | (intros; apply GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor <;> assumption)
end

section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  first | exact @GlobalTheory.SqTop.thbSt_of_inputs | exact GlobalTheory.SqTop.thbSt_of_inputs | (intros; apply GlobalTheory.SqTop.thbSt_of_inputs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.large_place_not_dvd_different : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DiffSOne.not_dvd_differentIdeal | exact GlobalTheory.DiffSOne.not_dvd_differentIdeal | (intros; apply GlobalTheory.DiffSOne.not_dvd_differentIdeal <;> assumption)
end
