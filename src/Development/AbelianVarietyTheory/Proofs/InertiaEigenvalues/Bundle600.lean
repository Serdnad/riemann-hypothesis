module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle575
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

private theorem padicInt_hom_ext {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [← hy]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

private theorem zA_eq_alg (z : ℤ_[l]) : _root_.Formalism.Per.zA l z = algebraMap ℤ_[l] (Ainf l) z :=
  haveI : IsHausdorff (Ideal.span {(l : Ainf l)}) (Ainf l) :=
    (WittVector.isAdicCompleteIdealSpanP (p := l) (k := _root_.Formalism.Per.Fl l)).toIsHausdorff
  padicInt_hom_ext (R := Ainf l) (_root_.Formalism.Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z

private theorem j_alg (C : Core l) (a : Ainf l) : C.j (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.MemLoc.ULaws.alg_acris, C.j_cris.on0]
  rfl

private theorem alg_alg_eq_aB (C : Core l) (a : Ainf l) :
    algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) a) = _root_.Formalism.Per.aB l a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [C.ι_j, j_alg, GlobalTheory.MemLoc.ULaws.iota_aB]

private theorem aB_zA (C : Core l) (z : ℤ_[l]) : _root_.Formalism.Per.aB l (_root_.Formalism.Per.zA l z) = _root_.Formalism.Per.zB l z := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [← GlobalTheory.MemLoc.ULaws.u_padicInt C, GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

theorem kap_map (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) (hn : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) :
    (GlobalTheory.SstPer.kap C bk k₀ k Mn z).map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) =
      (l : _root_.Formalism.Per.Bcris l) ^ k₀ • ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (_root_.Formalism.Per.zB l z * C.tB) ^ i) • (Mn.map ((_root_.Formalism.Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  have hz : ∀ w : ℤ_[l], algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.zA l w)) =
      _root_.Formalism.Per.zB l w := fun w => (alg_alg_eq_aB C _).trans (aB_zA C w)
  have hM : (Mn.map (((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
      (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) = Mn.map ((_root_.Formalism.Per.aB l).comp (wA l bk.a).toRingHom) := by
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
    exact alg_alg_eq_aB C _
  have he : ∀ i ∈ Finset.range d, _root_.Formalism.Per.zB l (GlobalTheory.SstPer.ecoef l k₀ k i) =
      (l : _root_.Formalism.Per.Bcris l) ^ k₀ * C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) := by
    intro i hi
    rw [← (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.1, GlobalTheory.SstPer.ecoef_val (hn i (Finset.mem_range.1 hi))]
    show C.qB _ = _
    rw [GlobalTheory.SstPer.ecoefQ, map_mul, map_pow, map_natCast]
  unfold GlobalTheory.SstPer.kap

  rw [← RingHom.mapMatrix_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [RingHom.mapMatrix_apply, map_smul_ring, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hM,
    smul_smul]
  congr 1
  rw [map_mul, map_pow, map_mul, hz, hz, he i hi, Core.tB]
  ring

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

theorem periods_over_Acris_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : _root_.Formalism.Per.Bcris l) ^ c₁ • U.map (_root_.Formalism.Per.φB l) = U * F.map ((_root_.Formalism.Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (_root_.Formalism.Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((_root_.Formalism.Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Acris l)) ∧ (C.t ^ N * (l : _root_.Formalism.Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : _root_.Formalism.Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)) i j) ∈ _root_.Formalism.Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev) * Z') i j) ∈ _root_.Formalism.Per.FilP l (2 * N)) := by
  intro l _ K bk P AI T C _hFits d ρ U U' hUU' c₁ F hφ k k₀ Mn c hn hgal
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Acris l) => M.map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)).map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact j_alg C _
  have htN : C.ι (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) =
        (Z.map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))).map (_root_.Formalism.Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) = F.map ((_root_.Formalism.Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact alg_alg_eq_aB C _
    have ht : algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) (phiA l C.t) =
        _root_.Formalism.Per.φB l (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) =
        (Z.map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))).map (_root_.Formalism.Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) = (ρ g).map (_root_.Formalism.Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [alg_alg_eq_aB C, ← zA_eq_alg, aB_zA C]
    have ht : algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) (sigA (g : GQ l) C.t) =
        _root_.Formalism.Per.σB (g : GQ l) (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hZ,
      kap_map C bk k₀ k Mn (c g) hn]
    simp only [map_pow, map_mul, map_natCast, ht]
    rw [Matrix.mul_smul, hgal g, Matrix.smul_mul, Matrix.mul_smul]
    simp only [smul_smul, Core.tB]
    congr 1
    ring
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)).map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)).map
        (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev) * Z').map (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)).comp bk.ev)).map
        (algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods
end
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.WachKernel



theorem kernel_freeA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hexact : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) :=
    GlobalTheory.EtaleExact.DD_exact D HW F
      (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  obtain ⟨hinj, hex, -⟩ := hexact
  obtain ⟨hDVR, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := (HW l).W_proj K s LL h T₁
  set N₀ := (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) with hN₀
  haveI : Module.Free W.EE (W.DD T₀) := (W.DD_free T₀).1
  haveI : IsNoetherianRing ↥(OL LL) :=
    @PrincipalIdealRing.isNoetherianRing ↥(OL LL) _ hDVR.toIsPrincipalIdealRing
  haveI : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI : Module.Finite (AA K LL) ↥(W.N T₁) := Module.Finite.iff_fg.mpr (W.N_fg T₁)
  have hfin : Module.Finite (AA K LL) ↥N₀ := by
    let g : ↥N₀ →ₗ[AA K LL] ↥(W.N T₁) :=
      ((W.map ι).restrictScalars (AA K LL)).restrict (fun x hx => hx)
    haveI : IsNoetherian (AA K LL) ↥(W.N T₁) := isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective g fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab))
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hX : IsSMulRegular ↥N₀ (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) := by
    intro x y hxy
    have h1 : (letπ : AA K LL) • (x : W.DD T₀) = (letπ : AA K LL) • (y : W.DD T₀) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T₀)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  have hreg : ∀ x y : ↥N₀,
      (fun _ => C ((l : ℕ) : ↥(OL LL)) : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • x =
        (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • y →
      ∃ z : ↥N₀, x = (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • z := by
    intro x y hxy
    have hinj : Function.Injective (W.map ι) := hinj
    have hex : Function.Exact (W.map ι) (W.map π) := hex
    let mA := (W.map ι).restrictScalars (AA K LL)
    let x' : ↥(W.N T₁) := ⟨mA x, x.2⟩
    let y' : ↥(W.N T₁) := ⟨mA y, y.2⟩
    have hxy' : (fun _ => C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' = (fun _ => X : AA K LL) • y' := by
      apply Subtype.ext
      have := congrArg (fun w : ↥N₀ => mA (w : W.DD T₀)) hxy
      simpa only [Submodule.coe_smul, map_smul] using this
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @GlobalTheory.WachFree.mem_X_smul_of_projective ℤ_[l] ↥(W.N T₁) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x' y' (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x' =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y'
        rw [e1, e2]
        exact hxy')
    change x' = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    have hz' : mA x = (fun _ => X : AA K LL) • (z : W.DD T₁) := congrArg Subtype.val hz
    have hπz : W.map π (z : W.DD T₁) = 0 := by
      have h0 : W.map π (mA x) = 0 := (hex _).mpr ⟨(x : W.DD T₀), rfl⟩
      rw [hz'] at h0
      have h0' : (letπ : AA K LL) • W.map π (z : W.DD T₁) = (letπ : AA K LL) • 0 := by
        rw [smul_zero]
        have : W.map π ((letπ : AA K LL) • (z : W.DD T₁)) = (letπ : AA K LL) • W.map π (z : W.DD T₁) :=
          ((W.map π).restrictScalars (AA K LL)).map_smul _ _
        rw [← this]
        exact h0
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (0 : W.DD T₂)] at h0'
      exact W.EE_π.smul_left_cancel.mp h0'
    obtain ⟨w, hw⟩ := (hex (z : W.DD T₁)).mp hπz
    have hwN : w ∈ N₀ := by
      show W.map ι w ∈ W.N T₁
      rw [hw]
      exact z.2
    refine ⟨⟨w, hwN⟩, Subtype.ext (hinj ?_)⟩
    change mA x = W.map ι ((fun _ => X : AA K LL) • w)
    rw [hz', ← hw]
    exact (mA.map_smul _ _).symm
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥N₀) (E := W.EE) (D := W.DD T₀) W.EE_inj N₀.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hreg
  refine ⟨Module.finrank W.EE (W.DD T₀), fun j => (b j : W.DD T₀), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_, ?_⟩
  · have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  · intro a ha
    have hx' : (⟨x, hx⟩ : ↥N₀) = ∑ j, a j • b j :=
      Subtype.ext (by simpa only [Submodule.coe_sum, Submodule.coe_smul] using ha)
    funext j
    rw [hx', b.repr_sum_self]

end GlobalTheory.WachKernel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_pow_growth : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_pow_growth | exact GlobalTheory.PMon.Ram.jumpSum_pow_growth | (intros; apply GlobalTheory.PMon.Ram.jumpSum_pow_growth <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem five_le_typePrime (D : Formalism.BasicNotions.D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        (((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _), hc]
  have := (D.host.g_prime k).two_le
  omega

theorem rank_eq_k_add_two_mul (R : Formalism.BasicNotions.Ranks) : R.r = R.k + 2 * (R.m / 2 - 1) + 1 := by
  obtain ⟨a, ha⟩ := R.m_even
  have := R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem lemmaL_series_weights_of_greenCuspidalParametrisation : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → admLq D := by
  intro hG D hT k ψ hψ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hL⟩ := hT k
  have hw : ∀ a f, wtOf D k a f = wtC L a f := by
    intro a f
    unfold wtOf wtC
    rw [hL f]
  have h5 := five_le_typePrime D k
  have hr := rank_eq_k_add_two_mul D.R
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨hU, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ
  obtain ⟨hJ, hJ1⟩ := hJ hr
  simp only [hw]
  refine ⟨fun f => ⟨?_, ?_⟩, fun f hf hs => ?_, fun f _ => ?_, fun f hf hs => ?_⟩
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hU ?_ f
    change 0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re
    rw [hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hJ ?_ f
    change 0 ≤ ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ).coeff 1).re
    rw [hJ1, ← Nat.cast_pow, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · exact GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev _ L h5 hG ψ hψ _ f hf.1 hf.2.1 hf.2.2 hs
  · exact GlobalTheory.T.harishChandraSeriesWeight_lower_comparison _ L ψ hψ _ _ _ hr hk f
  · exact GlobalTheory.T.harishChandraSeriesWeight_le_squarefree _ L h5 hG ψ hψ _ _ _ hr hk f hf.1 hf.2.1 hf.2.2 hs

end GlobalTheory.GLq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_lubinTate_character_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  first | exact @GlobalTheory.LTChar.main | exact GlobalTheory.LTChar.main | (intros; apply GlobalTheory.LTChar.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
theorem GlobalTheory.PMon.exI_of_ser_core (hser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y) (hcore : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Formalism.Per.Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0) : ExI := by
  intro l _ P AI T h hh μ hμ hne
  obtain ⟨S, θ, hS, hker, hq, hb⟩ := hser l P AI T
  let μ' : Fin h → ℂ_[l] := fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩
  have hμ' : μ' ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    exact hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))
  obtain ⟨y, hy, hz, hind⟩ := hcore l h μ' hh hμ'
  choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)
  choose hm hev using hev
  choose hq0 hq using hq
  refine ⟨b, hplus, hφ, ?_, fun a => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have : c = 0 := by
      refine hind c fun j _ => ?_
      have e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x) := fun x => by
        simp only [ev, AlgHom.coe_pow]
      have h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0 := by
        apply Subtype.ext
        have := congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc

        simp only [map_sum, map_smul, map_zero] at this
        simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, e, ZeroMemClass.coe_zero]
        simpa only [Algebra.smul_def] using this
      have h2 := congrArg θ h1

      rw [map_sum, map_zero] at h2
      simpa only [map_mul, hq, hev] using h2
    exact fun i => congrFun this i
  · have h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0 := by

      rw [map_sum]
      simpa only [map_mul, hev] using hz a
    have := (hker _).1 h2
    simpa only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul] using this

theorem GlobalTheory.PMon.exI_main : ExI := GlobalTheory.PMon.exI_of_ser_core GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic : Ratio := by
  first | exact @GlobalTheory.PMon.ratio_holds | exact GlobalTheory.PMon.ratio_holds | (intros; apply GlobalTheory.PMon.ratio_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_nonzero_frobVector_residue_zero : ExII := by
  first | exact @GlobalTheory.PMonII.exII | exact GlobalTheory.PMonII.exII | (intros; apply GlobalTheory.PMonII.exII <;> assumption)
end
