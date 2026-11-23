module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.QE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.RpSmulLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle051
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem blockH_form_k {ε : ℤˣ} {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L))ᵀ * QE L.n ε * (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L)).map σ = QE L.n ε := by
  have hQx : ∀ r, r ≠ Sum.inr L.i₀ → QE (E := E) d.n ε r (Sum.inl L.i₀) = 0 := by
    intro r hr
    rcases r with i | i
    · simp [QE]
    · have hi : i ≠ L.i₀ := fun h => hr (by rw [h])
      simp [QE, Matrix.one_apply, hi]
  have hQx' : ∀ a', QE (E := E) d.n ε (Sum.inl L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = 0 := by
    intro a'
    rcases a' with k | k
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k)]
  have hne : ∀ a', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' ≠ Sum.inr L.i₀ := by
    intro a'
    rcases a' with k | k
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k]
  have hQQ : ∀ a' c', QE (E := E) d.n ε (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = QE L.n ε a' c' := by
    intro a' c'
    rcases a' with k | k <;> rcases c' with k' | k' <;> simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, L.inj.eq_iff]
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hM (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c)
  rw [← hQQ, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Finset.sum_mul]
  symm
  rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
    · exact Finset.sum_congr rfl fun a' _ => by rw [hQQ]
    · intro r hr
      have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rw [hQx', mul_zero, zero_mul]
      · rw [hy _ (hne a), zero_mul, zero_mul]
  · intro s hs
    have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = Sum.inr L.i₀
      · subst hr
        rw [hy _ (hne a), zero_mul, zero_mul]
      · rw [hQx r hr, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [hy _ (hne c), map_zero, mul_zero]
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
open Matrix
theorem padE_emS_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = N a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padE_out_row_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padE_out_col_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem nq_E_k {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0)
    {H' : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E} (hH : M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * H' = 1) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
  have hxo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L L.i₀ rfl
  have hyo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L L.i₀ rfl
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · have : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (Sum.inl L.i₀) = (M * (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) k (Sum.inl L.i₀) := by
      simp only [Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_col_k L H' _ hxo]
    rw [Matrix.sub_apply, this, Matrix.mul_one, hx k, sub_self]
  · have hl : ∃ c', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c' = l := by
      by_contra hc
      rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hc with h | h
      · exact hlx h
      · exact hly h
    obtain ⟨c', rfl⟩ := hl
    have hsum : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = ∑ a', M k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') * H' a' c' := by
      rw [Matrix.mul_apply, sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
      · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_emS_k]
      · intro m hm
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_row_k L H' (fun h => hm (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)), Matrix.one_apply_ne, mul_zero]
        rintro rfl
        exact hm ⟨c', rfl⟩
    rw [Matrix.sub_apply, hsum]
    by_cases hk : ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = k
    · obtain ⟨a, rfl⟩ := hk
      have := congrFun (congrFun hH a) c'
      rw [Matrix.mul_apply] at this
      simp only [Matrix.submatrix_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp [(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L).eq_iff]
    · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hk with h | h
      · exact (hkx h).elim
      · have h' : k = Sum.inr L.i₀ := h
        subst h'
        rw [Finset.sum_eq_zero fun a' _ => by rw [hy _ (fun he => hyo ⟨a', he⟩), zero_mul], Matrix.one_apply_ne, sub_self]
        intro he
        exact hyo ⟨c', he.symm⟩
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KTunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : κ → AF F := fun k => d.crd X (τ k)
def cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : Mx F E d.m d.n := d.cmb fun k => c (τ.symm k)
theorem cinv_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) = X := by
  have : (fun k => _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X (τ.symm k)) = d.crd X := funext fun k => by simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, this, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
theorem cmap_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c) = c := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
theorem cmap_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X Y : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X + _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ Y := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, map_add (f := _)]
theorem cont_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  refine continuous_pi fun k => ?_
  exact (continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))
theorem cont_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  set h := hr.homeomorph with hh
  have e : ∀ c i j, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c i j = h.symm (fun l => c (τ.symm (i, j, l))) := fun c i j => by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    funext l
    exact congrFun (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb d (fun k => c (τ.symm k))) (i, j, l)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [e]
  exact h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)
def cEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n ≃ₜ+ (κ → AF F) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_cmap_k d τ
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_cinv_k d τ
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_add_k d τ
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cmap_k d τ
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cinv_k d τ
theorem map_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (ν : Measure (Mx F E d.m d.n))
    (hν : ν.IsAddHaarMeasure) :
    (ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)).IsAddHaarMeasure ∧
      ∀ f : (κ → AF F) → ℂ, ∫ X, f (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) ∂ν = ∫ y, f y ∂(ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have P := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  haveI : IsTopologicalRing (AE F E) := P.1
  haveI : BorelSpace (Mx F E d.m d.n) := P.2.2.2.2.2.2.2.1 d.m d.n
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstance
  refine ⟨?_, fun f => ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ)
  · have h := integral_map_equiv (μ := ν) (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ).toHomeomorph.toMeasurableEquiv f
    exact h.symm
end PositivityTheory.SiegelWeilFormula.KTunit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def rp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) : F := Algebra.trace F E (Yᵀ * d.A.J * W.map σ).trace
def eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => if (i, j) = (q.1, q.2.1) then d.bs q.2.2 else 0
def rc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Matrix (Fin d.m) (Fin d.n) E ≃ₗ[F] (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) where
  toFun Y k := d.bs.repr (Y k.1 k.2.1) k.2.2
  invFun a := Matrix.of fun i j => ∑ k, a (i, j, k) • d.bs k
  left_inv Y := by
    ext i j
    simp only [Matrix.of_apply]
    exact d.bs.sum_repr (Y i j)
  right_inv a := by
    funext ⟨i, j, k⟩
    simp only [Matrix.of_apply]
    exact congrFun (d.bs.repr_sum_self fun k' => a (i, j, k')) k
  map_add' Y Y' := by funext k; simp
  map_smul' c Y := by funext k; simp
theorem rp_add_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y Y' W : Matrix (Fin d.m) (Fin d.n) E) : _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d (Y + Y') W = _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W + _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y' W := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _)]
theorem rp_smul_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : F) (Y W : Matrix (Fin d.m) (Fin d.n) E) : _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d (c • Y) W = c * _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]
def Lm_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) →ₗ[F] (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) where
  toFun a q := ((ε : ℤ) : F) * _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).symm a) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q)
  map_add' a b := by
    funext q
    simp only [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_add_left_k, Pi.add_apply]
    ring
  map_smul' c a := by
    funext q
    simp only [map_smul, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_smul_left_k, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem ek_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d q = incM F (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) := by
  obtain ⟨i0, j0, k0⟩ := q
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, incM, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, Matrix.of_apply]
  show _ = (1 : AF F) ⊗ₜ[F] _
  by_cases h : (i, j) = (i0, j0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [if_pos rfl, Finset.sum_eq_single k0]
    · simp
    · intro b _ hb
      have : ((i, j, k0) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) ≠ (i, j, b) := fun e => hb (by simp at e; exact e.symm)
      simp [this]
    · simp
  · rw [if_neg h, TensorProduct.tmul_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ((i0, j0, k0) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) ≠ (i, j, k) := fun e => h (by simp at e; rw [e.1, e.2.1])
    simp [this]
theorem crd_eq_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) : Z = ∑ q, d.crd Z q • incM F (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) := by
  conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d Z, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ek_eq_k]
def ttL_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) : Mx F E d.m d.n →ₗ[AF F] AF F where
  toFun Z := d.tt (d.gram X Z)
  map_add' Z Z' := by
    have e : (Z + Z').map (cA σ) = Z.map (cA σ) + Z'.map (cA σ) := Matrix.map_add _ (map_add _) _ _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, e, Matrix.mul_add, Matrix.trace_add, map_add (f := _)]
  map_smul' a Z := by
    have e : (a • Z).map (cA σ) = a • Z.map (cA σ) := Matrix.map_smul _ a (fun x => map_smul (cA σ) a x) _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, e, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]
theorem tt_gram_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) (W : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → Mx F E d.m d.n) :
    d.tt (d.gram X (∑ q, c q • W q)) = ∑ q, c q * d.tt (d.gram X (W q)) := by
  have h := map_sum (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ttL_k d X) (fun q => c q • W q) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
theorem tt_gram_inc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) :
    d.tt (d.gram (incM F Y) (incM F W)) = algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W) := by
  have e : d.gram (incM F Y) (incM F W) = incM F (Yᵀ * d.A.J * W.map σ) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, PositivityTheory.SiegelWeilFormula.TBij.cA_incM, ← PositivityTheory.SiegelWeilFormula.TBij.incM_transpose, ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul,
      ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k]
  have h2 : (incM F (Yᵀ * d.A.J * W.map σ)).trace = (1 : AF F) ⊗ₜ[F] (Yᵀ * d.A.J * W.map σ).trace := by
    simp only [Matrix.trace, incM, Matrix.diag_apply, Matrix.map_apply, TensorProduct.tmul_sum]
    rfl
  rw [h2, trace_tmul', one_mul]
theorem pair_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (Y : Matrix (Fin d.m) (Fin d.n) E) (Z : Mx F E d.m d.n) :
    ((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z) = ∑ q, d.crd Z q * algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d Y) q) := by
  conv_lhs => rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.crd_eq_sum_k d Z]
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tt_gram_sum_k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tt_gram_inc_k]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, map_mul, map_intCast]
  ring
theorem tr_single_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : Matrix (Fin d.n) (Fin d.m) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    (M * (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d (i, j, k)).map σ).trace = M j i * σ (d.bs k) := by
  rw [Matrix.trace, Finset.sum_eq_single j]
  · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k]
    · intro b _ hb; simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, hb]
    · simp
  · intro b _ hb
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, hb]
  · simp
theorem rp_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d (i, j, k)) = Algebra.trace F E ((Yᵀ * d.A.J) j i * σ (d.bs k)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tr_single_k]
theorem rp_nondeg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ q, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) = 0) : Y = 0 := by
  have hσ : Function.Surjective σ := (AlgHom.bijective σ).2
  have key : ∀ (i : Fin d.m) (j : Fin d.n), (Yᵀ * d.A.J) j i = 0 := by
    intro i j
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    obtain ⟨e, rfl⟩ := hσ z

    rw [Algebra.traceForm_apply, ← d.bs.sum_repr e, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [AlgHom.map_smul_of_tower, mul_smul_comm, map_smul, ← _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_eq_k, h, smul_zero]
  have hdet : IsUnit d.A.J.det := isUnit_iff_ne_zero.2 (_root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_detA_k d)
  have h0 : Yᵀ * d.A.J = 0 := by ext j i; exact key i j
  have h1 : Yᵀ = 0 := by
    have := congrArg (· * d.A.J⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.zero_mul] at this
    exact this
  rw [← Matrix.transpose_transpose Y, h1, Matrix.transpose_zero]
theorem Lm_inj_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hε : ((ε : ℤ) : F) ≠ 0 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hY : (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).symm a = 0 := by
    refine _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_nondeg_k d _ fun q => ?_
    have := congrFun ha q
    simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hε
  simpa using congrArg (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d) hY
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact th_cA_incl _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, h1]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]
theorem th_gramE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (X : Matrix (Fin d.m) (Fin d.n) E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
  ext a b
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
theorem th_gram_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = Td η T₀ := by
  have hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀) := by
    ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_incM_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gramE_k, Td, hs]
  constructor
  · intro h
    rw [th_incM_injective h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply]
    simp only [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
  · intro h
    congr 1
    ext i j
    have := congrFun (congrFun h j) i
    simp only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢
    simp only [zsmul_eq_mul, smul_eq_mul] at this ⊢
    push_cast at this ⊢
    apply mul_left_cancel₀ hη
    rw [this]; ring
theorem th_toMx_act_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : GL (Fin d.m) (AE F E)) (X : Matrix (Fin d.m) (Fin d.n) E) :
    toMx (HeckeCharacterZeroLocus.SiegelWeilU.actTup (AF F) M (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF F) Xᵀ)) =
      (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
  ext a j
  simp only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]
theorem thetaDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k := by
  intro F E _ _ _ _ _ σ d η hη _
  refine ⟨d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη), _root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_haar_k d hη, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_fd_k d hη, ?_⟩
  intro T T₀ hT Φ _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image,
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).restrict_map, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image, integral_map_equiv, measureReal_def]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]
  let e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀} :=
    { toFun := fun X => ⟨X.1ᵀ, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ X.1).1 (hT ▸ X.2)⟩
      invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by
        rw [hT]; exact (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ _).2 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }
  rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_toMx_act_k]
  rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
