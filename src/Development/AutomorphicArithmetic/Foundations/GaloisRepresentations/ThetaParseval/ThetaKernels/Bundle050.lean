module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.MemLpSchM
import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.FrameLin
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem memLp_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : MemLp f 2 ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    exact memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'
  have h2 := (e.memLp_map_measure_iff).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def TL_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d
  map_smul' a Φ := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k d a Φ
theorem rho_smul_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
theorem B_rel'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  have hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    intro i
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp
  set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef
  have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
    intro i
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    have h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ := by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, _root_.PositivityTheory.SiegelWeilFormula.KFP.rho_smul_k]
    rw [h2, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
    unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
    rw [← h1]
    have e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
        star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) := by
      intro X
      rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]
      ring
    simp_rw [e3]
    erw [integral_const_mul]
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]
  have hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν := by
    intro i
    have hA := _root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))
    have hB := (_root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star
    exact hA.integrable_mul hB
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp_rw [integral_const_mul] <;> rfl
    _ = ∫ X, _root_.PositivityTheory.SiegelWeilFormula.KFP.TL_k d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1
        funext X

        rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rfl
    _ = 0 := by
        rw [hq, map_zero]
        simp
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COne
theorem om_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have := d.ok.dbl.kill 0 Φ h
  have e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0 := Matrix.zero_mul _
  have e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0 := Matrix.zero_mul _
  erw [e2] at this
  show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _
  rw [e3]
  exact this
theorem constantTerm_eq_fourierAtZero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T (d.om x Φ) 0 :=
  (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d x h)).symm
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]
theorem orb_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
theorem Ln_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega
theorem fcVal_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d' : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R'' : _root_.PositivityTheory.SiegelWeilFormula.RD_k d') (hMV : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d' hc T g
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g' := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]
end COne
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hIH hΦ hv in
theorem cOneVal_pf_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk : d.om k Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d k hΦ
  have hvk : d.T (d.om k Φ) ∈ R.vac := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d _ hΦk
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero d hΦ, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.Ln_k L]; push_cast; ring
  have hid : ∀ z, _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.fcVal_k H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.orb_smul_k]
    · exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k L.sd g₀ hΦ')
    · intro X hX
      rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, Module.End.one_apply] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_add_k (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add (f := _), Finsupp.coe_add, Pi.add_apply]
theorem crd_fin_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) : (d.crd Z k).2 = 0 := by
  have h := congrArg (fun M => d.crd M k) hZ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, Matrix.zero_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul] at h
  have h2 := congrArg Prod.snd h
  have e : ∀ c : AF F, (finOne F * c).2 = c.2 := fun c => by
    show (1 : Af F) * c.2 = c.2
    exact one_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [← e]
  exact h2
theorem loc_add_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {Z : Mx F E d.m d.n} (hZ : d.cw w Z = 0) (X : Mx F E d.m d.n) :
    R.loc w (X + Z) = R.loc w X := by
  have : d.cw w (X + Z) = d.cw w X := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at hZ ⊢
    rw [Matrix.map_add _ (map_add _), hZ, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [this]
def psiW_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2
theorem vg_tens_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g = R.tens w (fP 1) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  ring
theorem psiW_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w X := by
  intro X Z h1 h2
  have e1 : (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' (X + Z))) = ∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X) :=
    Finset.prod_congr rfl fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w' (h1 w' (Finset.ne_of_mem_erase hw'))]
  have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
    funext k
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_add_k]
    show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_fin_k h2, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k
  rw [e1, e2]
theorem gauss_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ X Z, (∀ w, d.cw w Z = 0) → (∏ w, fP 1 (R.loc w (X + Z))) = ∏ w, fP 1 (R.loc w X) := by
  intro X Z h
  exact Finset.prod_congr rfl fun w _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w (h w)]
theorem fP_smul_one_k (c : ℂ) (u : Fin d.m → Fin d.n → ℂ) : fP (c • (1 : PX d.m d.n)) u = c * fP 1 u := by
  simp only [fP, evX, MvPolynomial.smul_eq_C_mul, mul_one, MvPolynomial.eval_C, map_one, one_mul]
theorem isSchwartz_fourierProjection_one : IsSw (fP (1 : PX d.m d.n)) := by
  obtain ⟨φ, hφ⟩ := KMain.schwartz_polyGauss (m := d.m) (n := d.n) (2 * Real.pi) (by positivity) 1
  exact ⟨φ, hφ⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
def ext_k (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
theorem choose_em_k (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec
theorem ext_sub_k (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_neg h]
    rw [this, hX]
theorem crd_ext_k (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') k).2 = _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
theorem continuous_ins_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]; exact continuous_apply _
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h]; exact continuous_const
def prj_k (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
theorem prj_ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L k.2.1 h]
theorem SB_ins_k {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L), ?_⟩
  have hc : IsCompact (_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L)).trans fun z hz => ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z, hz, _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_ins_k L z⟩
theorem sum_loc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply, norm_star]
  rfl
theorem hζ'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
theorem gauss_ext_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b i) = 0 := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R')
      (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R) (R'.hfr w) (R.hfr w) _
theorem res_vg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := by
  funext X'
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => _root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_ext_k L R R' w X'
  · congr 1
    funext k
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.crd_ext_k L X' k
def resL_k : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L)
theorem res_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (_root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) ∈ R'.vac
    have e : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vg_k L R R' g
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R' (_root_.PositivityTheory.SiegelWeilFormula.Avac.SB_ins_k L hg)
  exact this hf
theorem vac_res'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ R'.vac := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vac_k L R R' hv
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em)) = d.T Φ X
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_sub_k L X hX]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end
