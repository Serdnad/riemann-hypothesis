module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle276
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section



namespace GlobalTheory.SelfDualAt

variable {D : D7}


open Classical in
def indP (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_indP (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (indP P) = if P v then 1 else 0 := rfl

def cP (P : Pl D → Prop) : AF D.host.F := pairA D.host.F 0 (indP P)

theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

theorem hO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = hO S T (c • x) y := by
  unfold hO
  simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring

theorem symplO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = symplO S T (c • x) y := by
  unfold symplO
  rw [hO_smul_swap]



theorem compFin_repr (w : Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
        (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y) k =
      evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e := rfl
    rw [h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [RingHom.map_add (f := _), LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy]
    exact (RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm

theorem eq_zero_of_compFin (y : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y = 0) :
    y = 0 := by
  have hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0 := by
    refine Finsupp.ext fun k => ?_
    have hk : ∀ w : Pl D, evalV D.host.F w
        ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := fun w => by
      rw [← compFin_repr, h w, map_zero]; rfl
    rw [Finsupp.zero_apply]
    refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
    exact hk w
  simpa using hr


theorem compFin_alg_cP (P : Pl D → Prop) (w : Pl D) (hw : P w) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) (cP P))) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rfl
  rw [h, evalV_indP, if_pos hw]
  exact Algebra.TensorProduct.one_def.symm



theorem algebraMap_placeIdempotent_mul (P : Pl D → Prop) (z : AE D) (hz : z ∈ idAt D P) :
    algebraMap (AF D.host.F) (AE D) (cP P) * z = z := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at hz
  obtain ⟨hinf, hfin⟩ := hz
  rw [RingHom.mem_ker] at hinf
  have h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0 := by
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · rw [RingHom.map_mul, hinf, mul_zero]
    · apply eq_zero_of_compFin
      intro w
      rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hw : P w
      · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]
      · have h1 := hfin ⟨w, hw⟩
        rw [RingHom.mem_ker] at h1
        rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at h0
  exact h0.symm

theorem smul_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (y : WO S T) (hy : y ∈ latO S T LS LT fun _ => True) : cP P • y ∈ latO S T LS LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩
    · intro v
      rw [map_mul]
      refine mul_mem ?_ (hα v)
      rw [evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro v hv
      rw [map_mul, evalV_indP, if_neg hv, zero_mul]
    · ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem latO_ann_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  intro D ψ hψ S T LS LT hS hT P u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hinf : u.map (infPart D) = 0 := by
    ext i j
    have h := (Ideal.mem_inf.1 (hu i j)).1
    rw [RingHom.mem_ker] at h
    simpa using h
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩
  have hfix : cP P • u = u := by
    ext i j
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact algebraMap_placeIdempotent_mul P _ (hu i j)
  constructor
  · intro hm u' hu'
    exact (key u hinf).1 (hle hm) u' (hle hu')
  · intro hann
    have h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1 := by
      intro y hy
      have h := hann _ (smul_mem_latO S T _ _ P y hy)
      rwa [symplO_smul_swap, hfix] at h
    rw [← hfix]
    exact smul_mem_latO S T _ _ P u ((key u hinf).2 h2)

end GlobalTheory.SelfDualAt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem contAut_rapidDec_bounded_integrable : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ φ : GA D V → ℂ, IsContAut V φ → RapidDec V φ ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ v : Vol V, IntegrableOn φ v.𝓕 v.μ := by
  intro D V hV φ hφ
  obtain ⟨K, hK, hS⟩ := hV
  have hr : RapidDec V φ := RapidDec.of_isCompact hφ.1 hφ.2 hK hS
  exact ⟨hr, hr.bounded, fun v => hr.integrableOn_fundamentalDomain v.haar v.fund⟩

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.BotPin

variable {D : D7}

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.Core.Mi.BotPin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem gramQ_unitri : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  intro D W ρ x₀ hb u hd hl
  have htri : (rat u : Mx D ρ ρ).BlockTriangular id := fun i j (h : j < i) => by
    show incA D (u i j) = 0
    rw [hl i j h, map_zero]
  have hdiag : ∀ i, (rat u : Mx D ρ ρ) i i = 1 := fun i => by
    show incA D (u i i) = 1
    rw [hd i, map_one]
  have hu : IsUnit (rat u : Mx D ρ ρ) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => ⟨fun h => htri h, hdiag i⟩
  have h := hb.2 _ hmem
  rw [IsUnit.unit_spec] at h
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, Matrix.mul_assoc]
  exact h

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.RatBlock

variable {D : D7}

theorem blockX_mem_UX {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_col_of_fix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {g : GA D V} (k : Fin ρ)
    (h : g ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k)) (i : Fin ρ) :
    blockX d g i k = (1 : Mx D ρ ρ) i k := by
  have hcol : ∀ l, (mt V g ⬝ d.jX) l k = d.jX l k := fun l => by
    have := congrFun (congrFun (mem_fixer.1 h) l) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
  rw [← d.pX_jX, blockX, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [hcol l]

end GlobalTheory.Unf.RatBlock


open GlobalTheory.Unf.RatBlock in
theorem GlobalTheory.Unf.ratBlock_unitri : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  intro D V V₀ ρ d γ hq hn
  obtain ⟨M, hM⟩ := (mem_GQ_iff V γ).1 hq
  have hM' : rat M = mt V γ := hM
  have hb : (rat (d.qX * (M * d.e)) : Mx D ρ ρ) = blockX d γ := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  obtain ⟨v, hv, hvb⟩ := blockX_mem_UX d hn
  have hent : ∀ i k, incA D ((d.qX * (M * d.e)) i k) = v.1 i k := fun i k => by
    have := congrFun (congrFun (hb.trans hvb) i) k
    exact this
  have hdiag : ∀ i, (d.qX * (M * d.e)) i i = 1 := fun i =>
    incA_injective (by rw [map_one, hent]; exact ((mem_UX.1 hv) i i).2)
  have hlow : ∀ i k, k < i → (d.qX * (M * d.e)) i k = 0 := fun i k hki =>
    incA_injective (by rw [map_zero, hent]; exact ((mem_UX.1 hv) i k).1 hki)
  have hdet : (d.qX * (M * d.e)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k (hki : k < i) => hlow i k hki)]
    simp [hdiag]
  have hu : IsUnit (d.qX * (M * d.e)).det := by rw [hdet]; exact isUnit_one
  refine ⟨d.qX * (M * d.e), (d.qX * (M * d.e))⁻¹, hb, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
    hdiag, hlow, fun j hj i k hkj => ?_⟩
  have hfix : γ ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k) := by
    have h2 := (Subgroup.mem_inf.1 hj).2
    exact (Subgroup.mem_iInf.1 h2) ⟨k, hkj⟩
  apply incA_injective
  have e1 := blockX_col_of_fix d k hfix i
  rw [← hb] at e1
  change incA D _ = _ at e1
  rw [e1, Matrix.one_apply]
  split_ifs <;> simp
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem hd_numbers : ∀ (D : D7) (u : D.what₂.Word) (L C' Cl Cg cb Cu cT CT : ℝ), HD D L C' Cl Cg cb Cu cT CT →
    5 ≤ mfL D L ∧ 4 * D.R.f + 1 ≤ (D.mem u).A.T ∧ 0 < d0 D u ∧ 5 ≤ (D.R.f : ℝ) * D.R.k * L := by
  intro D u L C' Cl Cg cb Cu cT CT h
  obtain ⟨-, -, hH, hN, -⟩ := h
  obtain ⟨hL1, -, hmf, hfk, -, -, -, -, -, -, -, hg0, -, hg1, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, hT, hdu, -⟩ := hN
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hm4 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf16 : 16 ≤ D.R.f := le_trans hm4 hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hfR : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hkR : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hL : (1 : ℝ) ≤ L := hL1.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hmR 5
    unfold mfL
    calc (5 : ℝ) ≤ 32 * 16 * 1 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by
        apply mul_le_mul (mul_le_mul hm5 hfR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)
  · have hb : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hkg : ∀ g : ℝ, ((D.R.k : ℝ) * Real.exp L) ^ 8 ≤ g → (D.R.k : ℝ) ^ 8 ≤ g := fun g hg =>
      le_trans (pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hb) 8) hg
    have h0 : D.R.k ^ 8 ≤ D.host.g 0 := by exact_mod_cast hkg _ hg0
    have h1 : D.R.k ^ 8 ≤ D.host.g 1 := by exact_mod_cast hkg _ hg1
    set N := (D.host.g 0 * D.host.g 1) ^ 2 with hNdef
    have hk8 : 4 * D.R.f ≤ D.R.k ^ 8 := by
      calc 4 * D.R.f ≤ D.R.k * D.R.k := Nat.mul_le_mul (by omega) hfk
        _ = D.R.k ^ 2 := (sq _).symm
        _ ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkpos : 1 ≤ D.R.k ^ 8 := Nat.one_le_pow _ _ (by omega)
    have hgg : D.R.k ^ 8 ≤ D.host.g 0 * D.host.g 1 :=
      le_trans h0 (Nat.le_mul_of_pos_right _ (by omega))
    have hNge : D.host.g 0 * D.host.g 1 ≤ N := by
      rw [hNdef, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN4 : 4 * D.R.f ≤ N := le_trans hk8 (le_trans hgg hNge)
    have hN2 : 2 ≤ N := by omega
    obtain ⟨-, hmod⟩ := hT u
    rw [Nat.one_mod_eq_one.mpr (by omega)] at hmod
    have hTp := (D.mem u).A.T_prime
    have h2 := hTp.two_le
    have hdiv := Nat.div_add_mod ((D.mem u).A.T) N
    rw [hmod] at hdiv
    have hq : (D.mem u).A.T / N ≠ 0 := by
      intro hq0; rw [hq0] at hdiv; omega
    have : N ≤ N * ((D.mem u).A.T / N) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)
    omega
  · rw [d0_eq]; exact hdu u
  · calc (5 : ℝ) ≤ 16 * 16 * 1 := by norm_num
      _ ≤ (D.R.f : ℝ) * D.R.k * L :=
        mul_le_mul (mul_le_mul hfR hkR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)

end GlobalTheory.Core.Rk

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.CoreHt.sizes_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  intro B X I h l Z L CY hR hX' hx hT
  have hW := (GlobalTheory.Mem.wts_ok_and_sizes B X).2
  have hF := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  obtain ⟨P⟩ := hR.1
  have hfN := GlobalTheory.ColumnNormCompare.SizeRows.f_mul_N_le_b P hR.2.2.2.1.1
  have hb1 := GlobalTheory.ColumnNormCompare.SizeRows.one_le_b L.sc
  refine ⟨hW.g_big, fun u => hT u, ?_, GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale I h l Z L CY hR hX' hx⟩
  have hab : 2 * L.sc.b ≤ L.sc.a := by
    show 2 * L.sc.b ≤ L.sc.x * L.sc.b
    nlinarith
  have hfN' : ((B.fields.f : ℝ)) * (B.R.N B.R.m : ℝ) ≤ L.sc.b := by
    rw [hF]; exact hfN
  push_cast
  linarith
end
