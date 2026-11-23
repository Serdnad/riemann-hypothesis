module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfPrecomplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle506
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKs
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E]

open Classical

def idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

theorem pLoc_idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    pLoc E v (idemOff S) = if v ∈ S then 0 else 1 := rfl

theorem idemOff_mul_self (S : Finset (HeightOneSpectrum (𝓞 E))) : idemOff S * idemOff S = idemOff S :=
  FiniteAdeleRing.ext _ fun v => by
    change pLoc E v (idemOff S) * pLoc E v (idemOff S) = pLoc E v (idemOff S)
    rw [pLoc_idemOff]; split_ifs <;> simp

def cutS (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E →ₙ+* Af E where
  toFun x := idemOff S * x
  map_mul' x y := by
    calc idemOff S * (x * y) = (idemOff S * idemOff S) * (x * y) := by rw [idemOff_mul_self]
      _ = idemOff S * x * (idemOff S * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pLoc_cutS (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) (x : Af E) :
    pLoc E v (cutS S x) = (if v ∈ S then 0 else 1) * pLoc E v x := by
  change pLoc E v (idemOff S * x) = _
  rw [map_mul, pLoc_idemOff]

theorem map_pLoc_pFin_finGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a k) = Matrix.GeneralLinearGroup.map (pLoc E v) k := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun x : GL (Fin a) (Af E) => pLoc E v (x i j)) (pFin_finGL k)

theorem exists_mul_supS_finGL : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a),
    g ∈ GlobalTheory.CellDec.C0 E a S →
    ∃ u ∈ GlobalTheory.CellDec.NA E a, ∃ h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, ∃ k : GL (Fin a) (Af E),
      (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := a)) ∧ (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) ∧
      g = u * h * finGL E a k := by
  intro E _ _ a S g hg
  obtain ⟨u, hu, k₁, hk₁, rfl⟩ := hg
  set k : GL (Fin a) (Af E) := cornerGL a (cutS S) (Matrix.GeneralLinearGroup.map (pFin E) k₁) with hk
  have hkv : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map (pLoc E v) k =
      Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ := by
    intro v hv
    rw [hk, map_cornerGL_of_hom _ _ (pLoc E v) (fun x => by rw [pLoc_cutS, if_neg hv, one_mul])]
    exact Units.ext (Matrix.ext fun i j => rfl)
  have hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1 := fun v hv =>
    map_cornerGL_of_zero _ _ (fun x => by rw [pLoc_cutS, if_pos hv, zero_mul]) _
  have hK : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ ∈ KGL v (n := a) := by
    intro v hv
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk₁ v) hv
  refine ⟨u, hu, k₁ * (finGL E a k)⁻¹, ?_, k, fun v => ?_, hkS, ?_⟩
  · intro w hw
    rw [map_mul, map_inv, map_pLoc_pFin_finGL, hkv w hw, mul_inv_cancel]
  · by_cases hv : v ∈ S
    · rw [hkS v hv]; exact one_mem _
    · rw [hkv v hv]; exact hK v hv
  · group

end GlobalTheory.CellDec
end
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisRegular
variable {l : ℕ} [Fact l.Prime] (C : Core l)

theorem exists_frob (C : Core l) :
    ∃ F : GQ l, ∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l := by
  obtain ⟨g, hg⟩ := FrobLaws.exists_ext C.σ
  refine ⟨g, fun ζ m hm hlm hζ => ?_⟩
  let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
  have := C.σ_root c m hm hlm (Subtype.ext hζ)
  rw [show ζ = (c : Om l) from rfl, hg, this]; rfl

theorem qB_coe (z : ℤ_[l]) : C.qB (z : ℚ_[l]) = Per.zB l z := (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z

theorem ι_aB (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, C.ι_j, GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap]
  simp only [aDp, RingHom.comp_apply]

theorem theta_eig {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) {g : GQ l} {x : ℚ_[l]}
    (hx : Per.σB g b = C.qB x * b) :
    Per.σC g (Per.θD l y) = algebraMap ℚ_[l] ℂ_[l] x * Per.θD l y := by
  have h1 := congrArg C.ι hx
  rw [(GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.1, map_mul, h, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1,
    show C.ι (C.qB x) = _ from C.ι_u _, ← map_mul] at h1
  have h2 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h1)
  rw [(thetaD_props l).2.2.2.2, map_mul, C.o_sec.th] at h2
  exact h2

theorem σB_tB (g : GQ l) : Per.σB g C.tB = C.qB ((C.χ g : ℤ_[l]) : ℚ_[l]) * C.tB := by
  rw [qB_coe, Core.tB, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, TAct.t_act l C g, map_mul,
    GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg]

theorem isUnit_of_theta {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) (hy : Per.θD l y ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate l _ hy fun g => (hb g).imp fun x hx => theta_eig C h hx
  obtain ⟨N, hN, hI⟩ := GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector l η _ hy hη
  obtain ⟨F, hF⟩ := exists_frob C
  obtain ⟨w, hw, hwI, hwF, hwφ⟩ := GlobalTheory.T.exists_unramified_period_ainf_unit l F hF (η F ^ N)⁻¹
  have h2 : C.ι (b ^ N * Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (y ^ N * aDp l w) := by
    rw [map_mul, map_pow, h, ι_aB, map_mul, map_pow]
  have hθ : Per.θD l (y ^ N * aDp l w) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hy) ((hw.map _).map _).ne_zero
  have hact : ∀ g : GQ l, Per.σC g (Per.θD l (y ^ N * aDp l w)) =
      algebraMap ℚ_[l] ℂ_[l] (((η g ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * Per.θD l y ^ N *
        Per.θD l (aDp l (Per.σA g w)) := by
    intro g
    rw [map_mul, map_mul, map_pow, map_pow, hη, ← (thetaD_props l).2.2.2.2,
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, mul_pow, ← map_pow, Units.val_pow_eq_pow_val,
      PadicInt.coe_pow]
  have hfix := GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius l F hF (Per.θD l (y ^ N * aDp l w))
    (fun g hg => by rw [hact, hI g hg, hwI g hg]; simp)
    (by
      rw [hact, hwF, map_mul, map_mul, ← C.o_sec.z, C.o_sec.th, map_mul, map_pow]
      have e : algebraMap ℚ_[l] ℂ_[l] (((η F ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
          algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
        rw [← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
      have e' : ((algebraMap ℚ_[l] (Om l) ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) : Om l) : ℂ_[l]) =
        algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
      rw [e']
      linear_combination (Per.θD l y ^ N * Per.θD l (aDp l w)) * e)
  have hinv : ∀ g : GQ l, Per.σB g (b ^ N * Per.aB l w) = b ^ N * Per.aB l w := by
    intro g
    obtain ⟨x, hx⟩ := hb g
    obtain ⟨z, hz⟩ := GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line l w _ hw hwφ g
    have e : Per.σB g (b ^ N * Per.aB l w) = C.qB (x ^ N * z) * (b ^ N * Per.aB l w) := by
      rw [map_mul, map_pow, hx, hz, map_mul, map_pow, qB_coe]
      ring
    have e2 := theta_eig C h2 e
    rw [hfix] at e2
    have e3 : algebraMap ℚ_[l] ℂ_[l] (x ^ N * z) = 1 := mul_right_cancel₀ hθ (by rw [one_mul, ← e2])
    have e4 : x ^ N * (z : ℚ_[l]) = 1 := (algebraMap ℚ_[l] ℂ_[l]).injective (by rw [e3, map_one])
    rw [e, e4, map_one, one_mul]
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified l C ⟨⊥, inferInstance⟩ _ fun g _ => hinv g
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, map_zero] at h2
    apply hθ
    rw [(BdRField.bdR_isField l).2.1 (h2.symm.trans (map_zero _).symm), map_zero]
  have hu : IsUnit (b ^ N * Per.aB l w) := hc ▸ (Ne.isUnit hc0).map C.u
  exact (isUnit_pow_iff hN.ne').1 (isUnit_of_mul_isUnit_left hu)

theorem isUnit_of_line (b : Per.Bcris l) (h0 : b ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨m, n, b', y, e, hy, hθ⟩ := GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero l C b h0
  have ht : IsUnit C.tB := (core_t_unit_fil l C).1
  have hu : IsUnit b' := isUnit_of_theta C hy hθ fun g => by
    obtain ⟨x, hx⟩ := hb g
    set a : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact PadicInt.coe_ne_zero.2 (C.χ g).ne_zero
    refine ⟨x * a ^ m * (a ^ n)⁻¹, ?_⟩
    have e1 := congrArg (Per.σB g) e
    rw [map_mul, map_mul, map_pow, map_pow, hx, σB_tB, ← ha] at e1
    have e2 : C.qB a ^ n * C.qB (a ^ n)⁻¹ = 1 := by
      rw [← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ ha0), map_one]
    apply (ht.pow n).mul_left_cancel
    rw [map_mul, map_mul, map_pow]
    linear_combination (-C.qB (a ^ n)⁻¹) * e1 + (C.qB x * C.qB a ^ m * C.qB (a ^ n)⁻¹) * e -
      (C.tB ^ n * Per.σB g b') * e2
  exact isUnit_of_mul_isUnit_left (e ▸ (ht.pow n).mul hu)

end GlobalTheory.MemLoc.CrisRegular

namespace GlobalTheory.MemLoc

theorem core_regular (l : ℕ) [Fact l.Prime] (C : Core l) : C.Regular :=
  GlobalTheory.T.bcris_regular_of_full_galois_line_units l C (CrisRegular.isUnit_of_line C)

theorem regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular :=
  fun l _ C _ => core_regular l C

end GlobalTheory.MemLoc
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CocycleInj



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  intro D HW F l _ K s LL h W E T hT M m hy hz
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius D HW F l K s LL h T hT M m hy
  exact GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma D HW F l K s LL h T hT M a m hy hz ha

end GlobalTheory.NL.CocycleInj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl GlobalTheory.FrobDescent

noncomputable section

namespace GlobalTheory.HWL.MatDecompl

section Concrete

open GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
  {LL : FinExt l} {Γ : GamS P K s LL} {R : WSer Γ}

theorem res_eq_one (Γ : GamS P K s LL) (g : ↥(GK K)) (h1 : P.χQ (g : GQ l) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply Subtype.ext
  have := Γ.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at this
  exact this

theorem chi_eq_one (P : LocPrime l) (h : Good K s LL) {g : GQ l} (hg : g ∈ Hinf K) :
    P.χQ g = 1 :=
  ((cyc_basic l P.χQ P.χQ_cyc).2.2 K g
    (IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) (Hinf_le_GK h hg))).2.1 hg

theorem fixH_io (I : IoS AI R) (e : R.EE) : FixH AI K (I.ioE e) :=
  fun g hg h1 => io_fixed I ⟨g, hg⟩ (res_eq_one Γ ⟨g, hg⟩ h1) e

theorem fixH_pi (I : IoS AI R) : FixH AI K (piR AI LL s) := by
  have h := fixH_io I (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) R.EE letπ)
  set_option synthInstance.maxHeartbeats 400000 in
    rw [io_pi I] at h
  exact h

theorem exists_pole_RW (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (x : RW LL) :
    ∃ k, NearPi AI LL s 0 (piR AI LL s ^ k * x) := by
  choose k hk using fun i => exists_pow_mul AI s ((crd (basisO LL) i x).coeff 0)
  refine ⟨Finset.univ.sup k, (nearPi_iff_crd AI LL s _ _).2 fun i => ?_⟩
  obtain ⟨z, hz⟩ := hk i _ (Finset.le_sup (f := k) (Finset.mem_univ i))
  exact ⟨z, by rw [crd_piR_pow, hz, pow_zero, one_mul]⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_near_perfI (h : Good K s LL) (I : IoS AI R) (hI : IoW I) (x : RW LL)
    (hx : FixH AI K x) (m : ℕ) : ∃ u ∈ perfI I l, NearPi AI LL s m (x - u) := by
  obtain ⟨u, hu, hu'⟩ := exists_inv_perfI I l
  refine exists_near AI K LL s _ (algebraMap_mem_perfI I l) u hu hu' (lift_closure _ _ ?_)
    (fun g hg => fixH_pi I g (Hinf_le_GK h hg) (chi_eq_one P h hg))
    x (fun g hg => hx g (Hinf_le_GK h hg) (chi_eq_one P h hg)) m
  rintro y (⟨j, rfl⟩ | ⟨z, hz, k, hk, hl, hzk, hy⟩)
  · refine mem_perfI_of_iterate I l j (l ^ s) _ ?_
    refine (GlobalTheory.TorsionBoundCompare.tmul_iter LL j _).trans ?_
    rw [frob_iter_teich, _root_.GlobalTheory.FrobDescent.εroot_pow]
    exact piR_add_one_pow AI LL s
  · have hint : ∀ i, Γ.emb i ⟨z, hz⟩ ∈ OL LL := fun i => by
      refine IsIntegral.of_pow hk ?_
      have : (⟨z, hz⟩ : ↥(K0 K)) ^ k = 1 := Subtype.ext hzk
      rw [← map_pow, this, map_one]
      exact isIntegral_one
    exact mem_perfI_of_io I l (hI ⟨z, hz⟩ k hk hl hzk y hy (fun i => ⟨_, hint i⟩) fun _ => rfl)

theorem mem_fixSub_iff (AI : LocAinf l P) (K : FinExt l) (x : RW LL) :
    x ∈ fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1} ↔ FixH AI K x :=
  mem_fixSub.trans ⟨fun h g h1 h2 => h g ⟨h1, h2⟩, fun h g hg => h g hg.1 hg.2⟩

theorem isUnit_one_add_RW (LL : FinExt l) (x : RW LL) : IsUnit (1 + (l : RW LL) * x) :=
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).1
  isUnit_one_add x

end Concrete

theorem conj_io' {O E A R : Type} [CommRing O] [CommRing E] [CommRing A] [CommRing R]
    [Algebra O E] [Algebra O A] [Algebra O R] {n : Type} [Fintype n] [DecidableEq n]
    (ι : A →ₐ[O] R) (p : ℕ) (τ : A) (φ : R →ₐ[O] R) (io : E →ₐ[O] R) (S : Subring R)
    (ht : IsUnit (ι τ)) (hp : 2 ≤ p)
    (h3 : ∀ m x, Near (ι : A →+* R) p (ι τ) m x → Near (ι : A →+* R) p (ι τ) (p * m) (φ x))
    (meet : ∀ x, (∀ m, Near (ι : A →+* R) p (ι τ) m x) → ∃ r, x = (p : R) * r)
    (comp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) →
      (∀ i, Near (ι : A →+* R) p (ι τ) (i + k) (f i)) →
      ∃ x ∈ S, ∀ m, Near (ι : A →+* R) p (ι τ) (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hφS : ∀ x ∈ S, φ x ∈ S) (hioS : ∀ e, io e ∈ S)
    (hD : ∀ x ∈ modSub (io : E →+* R) p, (φ : R →+* R) x ∈ modSub (io : E →+* R) p)
    (hpole : ∀ x, ∃ k, Near (ι : A →+* R) p (ι τ) 0 ((ι τ) ^ k * x))
    (h2 : ∀ x ∈ S, ∀ m, ∃ u ∈ perfSub (φ : R →+* R) (modSub (io : E →+* R) p) hD,
      Near (ι : A →+* R) p (ι τ) m (x - u))
    (hφt : (p : R) ∣ (ι τ) ^ p - φ (ι τ)) (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    {H : Type} (Q : H → Prop) (g : H → (R →ₐ[O] R)) (hS : ∀ x, x ∈ S ↔ ∀ h, Q h → g h x = x)
    (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (compS : ∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ y ∈ S, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r)
    (compE : ∀ x : ℕ → E, ∃ y, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r)
    (hrefl : ∀ e, IsUnit (io e) → IsUnit e)
    (F : Matrix n n R) (hF : ∀ i j, F i j ∈ S) (hu : IsUnit F) :
    ∃ (V : Matrix n n R) (e : Matrix n n E), IsUnit V ∧ (∀ i j, V i j ∈ S) ∧
      F * V.map φ = V * e.map io := by
  obtain ⟨e, V, h1, h2, h3⟩ := conj_io (ι := (ι : A →+* R)) (φ := (φ : R →+* R))
    (io := (io : E →+* R)) (τ := τ) rfl ht hp h3 meet comp hφS hioS hD hpole h2 hφt hJ
    (fun X Y hX hXY i j => (hS _).2 fun h hh => map_eq_of_mul_eq_one
      (g h : R →+* R) (fun i j => (hS _).1 (hX i j) h hh) hXY i j)
    hsat sep compS compE hrefl F hF hu
  exact ⟨V, e, h2, h1, h3⟩



theorem decompletion : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (r : ℕ) (F : Matrix (Fin r) (Fin r) (RW LL)), IsUnit F → (∀ i j, FixH AI K (F i j)) → ∃ (V : Matrix (Fin r) (Fin r) (RW LL)) (F' : Matrix (Fin r) (Fin r) R.EE), IsUnit V ∧ (∀ i j, FixH AI K (V i j)) ∧ F * V.map (φRW LL) = V * F'.map I.ioE := by
  intro l _ P AI K s LL h Γ R I hI r F hu hF
  have hl := GlobalTheory.Decompl.FixL.fixSub_ladic l P AI LL {g | g ∈ GK K ∧ P.χQ g = 1}
  obtain ⟨V, e, h1, h2, h3⟩ := conj_io' (inclR LL) l ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) (φRW LL)
    I.ioE (fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1})
    (isUnit_pi I)
    (Fact.out : l.Prime).two_le
    (near_φ AI LL s)
    (meet_RW AI LL s)
    (GlobalTheory.Decompl.fixSub_nearPi_complete l P AI LL s _ ((mem_fixSub_iff AI K _).2 (fixH_pi I)))
    hl.2.1
    (fun e => (mem_fixSub_iff AI K _).2 (fixH_io I e))
    (stable_io I l)
    (exists_pole_RW AI LL s)
    (fun x hx => exists_near_perfI h I hI x ((mem_fixSub_iff AI K _).1 hx))
    (dvd_pow_sub Fact.out (frob_pi I (P.PD_p K)))
    (isUnit_one_add_RW LL)
    (· ∈ {g | g ∈ GK K ∧ P.χQ g = 1}) (AI.gRW LL)
    (fun _ => mem_fixSub)
    hl.1
    (GlobalTheory.EtaleExact.sep_RW LL)
    hl.2.2
    (series_EE R (P.PD_p K))
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l P AI K s LL h Γ R I hI).2.1
    F
    (fun i j => (mem_fixSub_iff AI K _).2 (hF i j))
    hu
  exact ⟨V, e, h1, fun i j => (mem_fixSub_iff AI K _).1 (h2 i j), h3⟩

end GlobalTheory.HWL.MatDecompl
end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  first | exact @GlobalTheory.PSer.row_lam_sub_untilt_rowT | exact GlobalTheory.PSer.row_lam_sub_untilt_rowT | (intros; apply GlobalTheory.PSer.row_lam_sub_untilt_rowT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.series_residues | exact GlobalTheory.PSer.series_residues | (intros; apply GlobalTheory.PSer.series_residues <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | exact GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_sub_unit_le_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  first | exact @GlobalTheory.PMon.Gauss.one_digit | exact GlobalTheory.PMon.Gauss.one_digit | (intros; apply GlobalTheory.PMon.Gauss.one_digit <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  first | exact @GlobalTheory.HTBasisEx.exists_htBasis | exact GlobalTheory.HTBasisEx.exists_htBasis | (intros; apply GlobalTheory.HTBasisEx.exists_htBasis <;> assumption)
end
