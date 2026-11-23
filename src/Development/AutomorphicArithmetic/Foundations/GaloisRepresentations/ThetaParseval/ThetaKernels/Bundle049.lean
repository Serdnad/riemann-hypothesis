module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacDataOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ident_lincomb_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) {k : ℕ} (a : Fin k → ℂ)
    (Ψ : Fin k → d.Fn) (hK : ∀ i, d.KFin (Ψ i))
    (hI : ∀ i x, HolValueAt (fun z => d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (Ψ i) x))
    (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (∑ i, a i • Ψ i) x) := by
  have hsch : ∀ i, a i • Ψ i ∈ d.sch := fun i => d.sch.smul_mem _ (hK i).1
  have hv : d.I (∑ i, a i • Ψ i) x = ∑ i, a i * d.I (Ψ i) x := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hT.2.2.2.1 (a i) (hK i).1]
    rfl
  have key : ∀ i, HolValueAt (fun z => a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (a i * (c * d.I (Ψ i) x)) := fun i => (holValueAt_const (a i) _).mul (hI i x)
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Atop.eisAll_of_k hSK hEW d _ (hK i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 (∑ i, a i • Ψ i) = fun y => ∑ i, a i * d.sec0 (Ψ i) y := by
    funext y

    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have heq : EqRight (fun z => ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have hc' : ∀ i ∈ Finset.univ, GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
        (fun y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x := fun i _ =>
      (htt i z (hz' i)).of_norm_le (C := ‖a i‖) fun y => (norm_mul _ _).le
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x hc'
    show ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x = d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    have e2 : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * ∑ i, a i * d.sec0 (Ψ i) y) =
        fun y => ∑ i, a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) := by
      funext y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2, this]
    exact Finset.sum_congr rfl fun i _ => (cosetSum_const_mul _ _ _ _ _).symm
  have hval : c * d.I (∑ i, a i • Ψ i) x = ∑ i, a i * (c * d.I (Ψ i) x) := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
end PositivityTheory.SiegelWeilFormula.Atop
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem genAt_k (hG : AbsSt.GenCore) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w)
    {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ)
    (hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x))
    (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  have hEA := _root_.PositivityTheory.SiegelWeilFormula.Atop.eisAll_of_k hSK hEW d
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hCore : AbsSt.GlobCore (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n)
      d.Ht sl Il :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := by
        show Continuous (c • d.I (φ 1))
        exact ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := by
        intro γ hγ g
        show c * d.I (φ 1) (γ * g) = c * d.I (φ 1) g
        rw [((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g]
      Ik := by
        intro P g k hk
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := by
        intro g a b P
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := by
        intro g X a ha
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc,
          fun y => ⟨(hH y).1.const_mul c, fun t => ?_, fun r => ?_⟩⟩
        · show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t))
          rw [(hH y).2.1 t]
        · show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
          rw [iteratedDeriv_const_mul' c r (H y)]
          show c * iteratedDeriv r (H y) 0 = _
          rw [(hH y).2.2 r]
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ }
  have hVac : AbsSt.VacData (par2 σ d.Y) (rat2 σ d.Y) (s0 d.m d.n) d.Ht sl Il := by
    obtain ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ := vacData_of (fun z g => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z g)
      (s0 d.m d.n) (fun g => c * d.I (φ 1) g) U pp Ê t hUo hRD hs0 hp hhol hcont (fun z hz g => (hconv z hz).2 g)
      hvac
    exact ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩
  exact hG d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il hCore hVac P x
end PositivityTheory.SiegelWeilFormula.Atop
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix : Type := Fin d.m × Fin d.n × Fin 2
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.crd (d.cmb c) = c := by
  funext ⟨i, j, k⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb]
  have h : ∑ k', c (i, j, k') ⊗ₜ[F] d.bs k' = ∑ k', c (i, j, k') • (Algebra.TensorProduct.basis (AF F) d.bs) k' := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact congrFun (Module.Basis.repr_sum_self _ (fun k' => c (i, j, k'))) k
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add (X X' : Mx F E d.m d.n) : d.crd (X + X') = d.crd X + d.crd X' := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul (a : AF F) (X : Mx F E d.m d.n) : d.crd (a • X) = a • d.crd X := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) →ₗ[AF F] Mx F E d.m d.n where
  toFun := d.cmb
  map_add' c c' := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' a c := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Finset.smul_sum, TensorProduct.smul_tmul']
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n := d.cmb fun j => if k = j then 1 else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.cmb c = ∑ k, c k • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k :=
  LinearMap.pi_apply_eq_sum_univ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d) c
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : ∃ M : Matrix (Fin d.m) (Fin d.n) E, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k = incM F M := by
  refine ⟨Matrix.of fun i j => (∑ k', (if k = (i, j, k') then (1 : F) else 0) • d.bs k' : E), ?_⟩
  ext i j

  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, incM, Matrix.map_apply, Matrix.of_apply, map_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  show _ = (1 : AF F) ⊗ₜ[F] _
  split_ifs <;> simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM (M : Matrix (Fin d.m) (Fin d.n) E) (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    d.crd (incM F M) k = algebraMap F (AF F) (d.bs.repr (M k.1 k.2.1) k.2.2) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, incM, Matrix.map_apply]
  rw [show inclR (F := F) (AF F) (M k.1 k.2.1) = (1 : AF F) ⊗ₜ[F] M k.1 k.2.1 from rfl,
    Algebra.TensorProduct.basis_repr_tmul]
  simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (incM F x) = incM F ((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, ← incM_transpose, ← incM_mul]
  rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n)
    (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (fun k => d.crd X (τ k)) ⬝ᵥ (fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  rw [dotProduct, Equiv.sum_comp τ (fun i => d.crd X i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d i * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w), ← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left]
  congr 1
  conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum, Matrix.sum_mul]
  simp only [Matrix.smul_mul]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F) where
  toFun w := (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w)
  map_add' w w' := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right]
  map_smul' a w := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) := rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    om (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, om, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv]
  exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split d w w').symm
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = (fun k => d.crd X (τ k), 0) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame]
  refine Prod.ext rfl (funext fun k => ?_)
  exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame d _ _
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w).1 = 0) : ∃ Z : Mx F E d.m d.n, w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ := by
  have h1 : d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) = 0 := by
    funext i
    have := congrFun h (τ.symm i)
    simpa [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply] using this
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w), h1]
    exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d).map_zero
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  exact ⟨Z, by rw [hZ, h2, Matrix.zero_mul, add_zero]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    ∃ y z : κ → F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F x) = ratV y z := by
  have hs : ∀ k, ∃ r : F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (incM F x) = algebraMap F (AF F) r := by
    intro k
    obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat d (τ k)
    rw [hM, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_transpose, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]
    obtain ⟨y, z, h⟩ := d.ok.dbl.rat (M * (d.b.1.toCols₂)ᵀ)
    obtain ⟨y', z', h'⟩ := d.ok.dbl.rat x
    exact ⟨om (y, z) (y', z'), by rw [h, h']; exact om_ratV y z y' z'⟩
  choose r hr using hs
  refine ⟨fun k => d.bs.repr (((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) (τ k).1 (τ k).2.1) (τ k).2.2, r, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ (τ k)
  · exact hr k
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
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
namespace COneB
theorem fcBd'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) :
    ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      ∀ y : d.G, (∀ β ∈ K, ‖f (nb β * y)‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T y‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  refine ⟨K, hK, fun f M hf y hM => ?_⟩
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hbd : ∀ β, ‖f (nb β * y) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))‖ ≤ M := by
    intro β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hψ.2.1 _, mul_one]
    have e : f (nb β * y) = f (nb (γ + β) * y) := by
      rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
    rw [e]
    exact hM _ hk
  have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd β)
  have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
  rw [hr, mul_one] at h1
  exact h1
end COneB
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hE in
theorem avgHol_pf_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x := by
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb := d.ok.frame
  have hnbc := kfour.nb_continuous hσ hb hc.1
  obtain ⟨iTG, -, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨KN, hKN, hKNb⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.fcBd'_k d hc T
  obtain ⟨KU, hKU, hKUc⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.ratV_cocompact_k L
  have huc := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_cont_k L hu
  let C : Set d.G := (fun q : nA σ d.Y d.b × (Fin L.n → AE F E) => nb q.1 * uM q.2 * x) '' (KN ×ˢ KU)
  have hCc : IsCompact C :=
    (hKN.prod hKU).image (((hnbc.comp continuous_fst).mul (huc.comp continuous_snd)).mul continuous_const)
  have hper : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) → ∀ u, ∃ k ∈ KU,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T (uM k * x) := by
    intro φ hφ hi u
    obtain ⟨r, hr, hk⟩ := hKUc u
    refine ⟨r + u, hk, ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu, mul_assoc, (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT φ hφ hi r hr]
  have hbound : ∀ (φ : d.G → ℂ) (M : ℝ), Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      (∀ y ∈ C, ‖φ y‖ ≤ M) → ∀ u, ‖fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)‖ ≤ M := by
    intro φ M hφ hi hM u
    obtain ⟨k, hk, e⟩ := hper φ hφ hi u
    rw [e]
    refine hKNb φ M hi _ fun β hβ => hM _ ⟨(β, k), ⟨hβ, hk⟩, ?_⟩
    simp only [mul_assoc]
  have hmeas : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      AEStronglyMeasurable (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) ν := by
    intro φ hφ hi
    exact ((_root_.PositivityTheory.SiegelWeilFormula.AStep.fcCont_k d hc T φ hφ hi).comp (huc.mul continuous_const)).aestronglyMeasurable
  have hfin : ν 𝓤 < ⊤ := by rw [hu.2.2.2]; exact ENNReal.one_lt_top
  have hint : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      IntegrableOn (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) 𝓤 ν := by
    intro φ hφ hi
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne (hmeas φ hφ hi)
      (Filter.Eventually.of_forall fun u => hbound φ M hφ hi hM u)
  have hadd : ∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (a • f + f') T x =
        a * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f T x + _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f' T x := by
    intro a f f' hf hf' hi hi'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k]
    have e : (fun u => fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T (uM u * x)) =
        fun u => a * fc d.B.ψ d.b nb lam 𝓖 f T (uM u * x) + fc d.B.ψ d.b nb lam 𝓖 f' T (uM u * x) :=
      funext fun u => (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T (uM u * x)).1 a f f' hf hf' hi hi'
    rw [e, integral_add ((hint f hf hi).const_mul a) (hint f' hf' hi'), integral_const_mul]
  have hbd : ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ C, ‖f y‖ ≤ M) → ‖_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f T x‖ ≤ M := by
    refine ⟨C, hCc, fun f M hf hi hM => ?_⟩
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun u _ => hbound f M hf hi hM u)
    have hr : ν.real 𝓤 = 1 := by simp [Measure.real, hu.2.2.2]
    rw [hr, mul_one] at h1
    exact h1
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) (fun φ => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x) hadd hbd U Ê hUo hd hcont hinv
  exact ⟨hDiff, fun i => hComm _ hs i⟩
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem continuous_phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  have ha := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_a'_k d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [_root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x))
  exact h1.mul hf
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end
