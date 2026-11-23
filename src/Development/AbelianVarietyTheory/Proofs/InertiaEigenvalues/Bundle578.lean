module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
namespace GlobalTheory.CellEvalDet

open Matrix

variable {E : Type} [Field E] [NumberField E]

theorem detPow_eq_rpow {n : ℕ} (x : ℝ) (g : GA E n) :
    GlobalTheory.RSJ.detPow E n x g =
      ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem det_diagT {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.diagT R (Fin n) t) = ∏ i, t i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, det_diagonal, Units.coe_prod]

def posVal : {r : ℝ // 0 < r} →* ℝ where
  toFun r := r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem qV_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < qV E v :=
  lt_of_le_of_ne (Nat.cast_nonneg _) (GlobalTheory.AdeleScale.qV_ne_zero v).symm

end GlobalTheory.CellEvalDet


open GlobalTheory.CellEvalDet Matrix in
theorem GlobalTheory.CellEvalDet.detPow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  intro E _ _ _ n ϖ hϖ l x g
  rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_eq_rpow x (GlobalTheory.CellDec.tl n ϖ l)]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l) =
      ∏ i, finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin n → ℤ => y i) rfl l)) := by
    unfold GlobalTheory.CellDec.tl
    rw [det_finGL, det_diagT, map_prod]
  have hmod : ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l)) : ℝ)) =
      ∏ i, ∏ v ∈ l.support, ((qV E v : ℝ) ^ (l v i))⁻¹ := by
    rw [hdet, map_prod]
    change posVal (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
    rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support (fun v hv => by
      rw [Finsupp.notMem_support_iff] at hv; simp [hv])]
    simp
  rw [hmod, Finset.prod_comm, ← Real.finsetProd_rpow _ _ (fun v _ =>
    Finset.prod_nonneg fun i _ => inv_nonneg.2 (zpow_nonneg (Nat.cast_nonneg _) _)) x]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hq := qV_pos (E := E) v
  have e : ∀ i, ((qV E v : ℝ) ^ (l v i))⁻¹ = (qV E v : ℝ) ^ (-(l v i : ℝ)) := fun i => by
    rw [Real.rpow_neg hq.le, Real.rpow_intCast]
  simp_rw [e]
  rw [← Real.rpow_sum_of_pos hq, ← Real.rpow_mul hq.le]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | exact GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | (intros; apply GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conj_fourierCoefficients_conjugate_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ) (w' : M.Cl' a → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (M.dδ a).l₂) → M.c'.F), (u : ℂ) = ((R.xi (tup b) s : Circle) : ℂ) ∧ (∀ k, HEq (w' k) (M.w b (e k))) ∧ ∀ k q, ta (M.w a k q) = u * w' k q := by
  first | exact @GlobalTheory.ConjDatum.conj_coeff | exact GlobalTheory.ConjDatum.conj_coeff | (intros; apply GlobalTheory.ConjDatum.conj_coeff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



namespace GlobalTheory.FlatForm

open GlobalTheory.FlatConj

theorem gaussGL_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) :
    gaussGL ψ⁻¹ ξ⁻¹ r = (starRingEnd ℂ) (gaussGL ψ ξ r) := by
  unfold gaussGL

  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj]
  congr 1
  set u := Matrix.GeneralLinearGroup.det x
  have h1 : ((ξ u : ℂˣ) : ℂ) ^ Fintype.card kˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((ξ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  rw [MonoidHom.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]

theorem gaussGL_mul_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) :
    gaussGL ψ ξ r * gaussGL ψ⁻¹ ξ⁻¹ r = (Fintype.card k : ℂ) ^ (r ^ 2) := by
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ ξ r hψ hξ (gaussGL ψ ξ r) rfl
  rw [gaussGL_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  push_cast
  rfl

theorem gaussGL_ne_zero {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussGL ψ ξ r ≠ 0 := fun h => by
  have := gaussGL_mul_inv ψ ξ r hψ hξ
  rw [h, zero_mul] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) this.symm

theorem fourier_flat (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r t : ℕ) (hψ : ψ.IsPrimitive)
    (hξ : ξ ≠ 1) (u : Matrix (Fin (r + t)) (Fin r) k) :
    (∑ y : Matrix (Fin r) (Fin (r + t)) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
      ψ (Matrix.trace (y * u))) = ((Fintype.card k : ℂ) ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹) *
      (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  have hmul := gaussGL_mul_inv ψ ξ r hψ hξ
  have hne := gaussGL_ne_zero ψ ξ r hψ hξ
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hC : q ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹ = q ^ (r * t) * G := by
    have hG' : gaussGL ψ⁻¹ ξ⁻¹ r = G := rfl
    rw [hG'] at hmul
    rw [show (r + t) * r = r * t + r ^ 2 by ring, pow_add, ← hmul]
    field_simp
  rw [hC]
  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

theorem gaussP_ne_zero {E : Type} [Field E] [NumberField E] (PP : Pl E) (ψ : AddChar (kP PP) ℂ) (ξ : (kP PP)ˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussP PP ψ ξ r ≠ 0 :=
  @gaussGL_ne_zero (kP PP) (resField PP) (resFintype PP) ψ ξ r hψ hξ

theorem omegaQ_eq_gauss_mul_flat_transform (D : D7) [inst : ∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n : ℕ) (hrn : r ≤ n)
    (hQ : ∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1) (ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) ub = (∏ PP ∈ Q, ((Nat.card (kP PP) : ℂ) ^ (n * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹))⁻¹ *
      ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) *
          ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain rfl : inst = fun PP => resFintype PP := Subsingleton.elim _ _
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => resFintype PP
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin (r + t)) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let C : Pl D.host.E → ℂ := fun PP => (Nat.card (kP PP) : ℂ) ^ ((r + t) * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹
  have hC0 : ∀ PP : ↥Q, C PP ≠ 0 := fun PP =>
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hQ _ PP.2).1 (hQ _ PP.2).2))
  have hCe : ∀ (PP : ↥Q) (u : Matrix (Fin (r + t)) (Fin r) (kP PP.1)),
      (∑ y : Matrix (Fin r) (Fin (r + t)) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C PP * fq PP.1 u := by
    intro PP u
    have := @fourier_flat (kP PP.1) (resField PP.1) (resFintype PP.1) (ψP PP.1) (ξ PP.1) r t (hQ _ PP.2).1 (hQ _ PP.2).2 u
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
    rw [← Finset.attach_eq_univ]
    unfold omegaQ
    convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
      (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
  have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin (r + t)) (kP PP.1)),
      omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
    intro y
    have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP),
        omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
      intro Y
      unfold omegaFlat
      convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [e0, Finset.attach_eq_univ]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [dif_pos PP.2, Subtype.coe_eta]
  have hprod : (∏ PP ∈ Q, C PP) = ∏ PP : ↥Q, C PP := (Finset.prod_coe_sort Q C).symm
  show _ = (∏ PP ∈ Q, C PP)⁻¹ * _
  simp only [hf, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin (r + t)) (kP PP.1))))
    (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin (r + t)) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  simp only [hCe]
  rw [hprod, Finset.prod_mul_distrib (f := fun PP : ↥Q => C PP) (g := fun PP : ↥Q => fq PP.1 (ub PP.1)), hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatForm
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.residueTwistFactor_eq_unit_mul_flat_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  first | exact @GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform | exact GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform | (intros; apply GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E), FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) = (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ConjFix.fixBase_split_conj | exact GlobalTheory.ConjFix.fixBase_split_conj | (intros; apply GlobalTheory.ConjFix.fixBase_split_conj <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {B C D : Obj l R} (h : Hom B C) (h₂ : Hom C D) (m : ℕ) :
    qmap (h₂.comp h) m = (qmap h₂ m).comp (qmap h m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem stable_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C)
    (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  intro l _ R _ B C D h h₂ s s₂
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · rw [qmap_comp]
    exact RingHom.Flat.comp (s.flat m) (s₂.flat m)
  · obtain ⟨C', k', h', p⟩ := s.po B' k
    obtain ⟨D', k'', h₂', p₂⟩ := s₂.po C' k'
    refine ⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩
    · apply Hom.ext'
      have e1 := congrArg Hom.f p.comm
      have e2 := congrArg Hom.f p₂.comm
      change k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f
      change k'.f.comp h.f = h'.f.comp k.f at e1
      change k''.f.comp h₂.f = h₂'.f.comp k'.f at e2
      rw [← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]
    · have := (p.po m).paste_horiz (p₂.po m)
      rw [qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      exact this

end GlobalTheory.BSP
end
