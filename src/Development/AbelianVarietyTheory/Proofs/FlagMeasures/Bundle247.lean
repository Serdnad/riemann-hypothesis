module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle069
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle240
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
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
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PerpSort

theorem herm_comp {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (x y : Fin n → ℂ) : herm (x ∘ f) (y ∘ f) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  obtain ⟨h1, h2⟩ := hf
  rw [dotProduct, ← Equiv.sum_comp f, Fintype.sum_sum_type, herm]
  simp only [Function.comp_apply, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, h1, h2, if_true,
    Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem form_self {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (GlobalTheory.GaussMean.qEps ε x : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, GlobalTheory.GaussMean.qEps]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [mul_left_comm, hx]
  split_ifs <;> push_cast <;> ring

theorem mat_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : (hf.equiv.symm k).mat = (Formalism.MainNotions.S.uMat k).submatrix f f := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  ext i j
  have e := congrFun (congrFun h (f i)) (f j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at e
  exact e.symm

theorem act_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) (x : Fin n → ℂ) :
    act (hf.equiv.symm k) (x ∘ f) = (Formalism.MainNotions.S.uMat k *ᵥ x) ∘ f := by
  rw [act, mat_symm hf, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, f.self_comp_symm,
    Function.comp_id]

private theorem of_fin_cases_mulVec {n : ℕ} (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (w : Fin (n + 1) → ℂ) :
    (Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j) *ᵥ w =
      w 0 • x₀ + B *ᵥ fun k => w k.succ := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_mulVec_eq {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (h0 : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0) (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') (y : Fin (n + 1) → ℂ)
    (hy : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) : ∃ u, B *ᵥ u = y := by
  set J := Formalism.REAL.Jm ε
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j with hM
  have hMv : ∀ w, M *ᵥ w = w 0 • x₀ + B *ᵥ fun k : Fin n => w k.succ := fun w => of_fin_cases_mulVec x₀ B w
  have key : ∀ t : Fin n → ℂ, star x₀ ⬝ᵥ (J *ᵥ (B *ᵥ t)) = 0 := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1, zero_dotProduct]
  have hval : ∀ w, star x₀ ⬝ᵥ (J *ᵥ (M *ᵥ w)) = w 0 * (star x₀ ⬝ᵥ (J *ᵥ x₀)) := by
    intro w
    rw [hMv, Matrix.mulVec_add, dotProduct_add, key, add_zero, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have hz : M *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hab
    have hw0 : (a - b) 0 = 0 := by
      have e := hval (a - b)
      rw [hz, Matrix.mulVec_zero, dotProduct_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_right h0
    have hBt : B *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
      have e := hMv (a - b)
      rw [hz, hw0, zero_smul, zero_add] at e
      exact e.symm
    have ht : (fun k : Fin n => (a - b) k.succ) = 0 := by
      have hJ' : Formalism.REAL.Jm ε' *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
        rw [← h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      rw [← Matrix.one_mulVec (fun k : Fin n => (a - b) k.succ), ← Formalism.REAL.Jm_mul_self ε',
        ← Matrix.mulVec_mulVec, hJ', Matrix.mulVec_zero]
    rw [← sub_eq_zero]
    funext i
    refine Fin.cases hw0 (fun k => ?_) i
    exact congrFun ht k
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨w, hw⟩ := hsurj y
  have hw0 : w 0 = 0 := by
    have e := hval w
    rw [hw, hy] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  refine ⟨fun k : Fin n => w k.succ, ?_⟩
  rw [← hw, hMv, hw0, zero_smul, zero_add]

theorem isPerpEmb_of_sorts : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  intro n ε ε' s x₀ B j hq h1 h2 hj P Q P' Q' f f' hf hf'
  change IsPerpEmb (x₀ ∘ f) _ _
  have hsub : ∀ u : Fin P' ⊕ Fin Q' → ℂ, B.submatrix f f' *ᵥ u = (B *ᵥ (u ∘ f'.symm)) ∘ f :=
    fun u => Matrix.submatrix_mulVec_equiv _ _ _ _
  have hc : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [form_self, hq]
    cases s <;> simp [GlobalTheory.GaussMean.sgn]
  refine ⟨fun u v => ?_, fun y => ⟨fun h0 => ?_, ?_⟩, fun g => ?_⟩
  · have e := herm_comp hf' (u ∘ f'.symm) (v ∘ f'.symm)
    rw [Function.comp_assoc, f'.symm_comp_self, Function.comp_id, Function.comp_assoc,
      f'.symm_comp_self, Function.comp_id] at e
    rw [e, hsub, hsub, herm_comp hf, ← h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have e := herm_comp hf (y ∘ f.symm) x₀
    rw [Function.comp_assoc, f.symm_comp_self, Function.comp_id] at e
    rw [e] at h0
    obtain ⟨u, hu⟩ := exists_mulVec_eq ε ε' x₀ B hc h1 h2 _ h0
    refine ⟨u ∘ f', ?_⟩
    rw [hsub, Function.comp_assoc, f'.self_comp_symm, Function.comp_id, hu, Function.comp_assoc,
      f.symm_comp_self, Function.comp_id]
  · rintro ⟨u, rfl⟩
    rw [hsub, herm_comp hf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
      zero_dotProduct]
  · obtain ⟨hfix, hcomm⟩ := hj (hf'.equiv g)
    refine ⟨?_, fun u => ?_⟩
    · show act (hf.equiv.symm (j (hf'.equiv g))) (x₀ ∘ f) = x₀ ∘ f
      rw [act_symm hf, hfix]
    · show act (hf.equiv.symm (j (hf'.equiv g))) _ = _
      have e := act_symm hf' (hf'.equiv g) (u ∘ f'.symm)
      rw [ContinuousMulEquiv.symm_apply_apply, Function.comp_assoc, f'.symm_comp_self,
        Function.comp_id] at e
      rw [hsub, hsub, act_symm hf, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, e,
        Function.comp_assoc, f'.self_comp_symm, Function.comp_id]

end GlobalTheory.PerpSort
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.GlobIdx

theorem prod_relIndex_dvd {G ι : Type} [AddCommGroup G] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    (B A : AddSubgroup G) (H K : ∀ i, AddSubgroup (M i)) (φ : ∀ i, G →+ M i) (S : Finset ι)
    (hA : ∀ i, ∀ x ∈ A, φ i x ∈ K i) (hB : ∀ i, ∀ x ∈ B, φ i x ∈ H i)
    (hs : ∀ y : ∀ i, M i, (∀ i, y i ∈ K i) → ∃ x ∈ A, ∀ i ∈ S, φ i x - y i ∈ H i) :
    ∏ i ∈ S, (H i).relIndex (K i) ∣ B.relIndex A := by
  classical
  let ψ : A →+ (∀ i : S, K i ⧸ (H i).addSubgroupOf (K i)) :=
    AddMonoidHom.pi fun i : S => (QuotientAddGroup.mk' ((H i).addSubgroupOf (K i))).comp
      (((φ i).comp A.subtype).codRestrict (K i) fun x => hA i x x.2)
  have hψ : Function.Surjective ψ := by
    intro q
    choose r hr using fun i : S => QuotientAddGroup.mk_surjective (q i)
    obtain ⟨x, hx, h⟩ := hs (fun i => if hi : i ∈ S then (r ⟨i, hi⟩ : M i) else 0) (fun i => by
      by_cases hi : i ∈ S
      · simp only [hi, dif_pos]; exact (r ⟨i, hi⟩).2
      · simp only [hi, dif_neg, not_false_eq_true]; exact zero_mem _)
    refine ⟨⟨x, hx⟩, funext fun i => ?_⟩
    rw [← hr i]
    have h1 := h i i.2
    simp only [i.2, dif_pos] at h1
    show (QuotientAddGroup.mk (⟨φ i x, hA i x hx⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = _
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
    exact h1
  have hker : B.addSubgroupOf A ≤ ψ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    funext i
    show (QuotientAddGroup.mk (⟨φ i x, hA i x x.2⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hB i x hx
  have h1 : ψ.ker.index ∣ B.relIndex A := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hψ, AddSubgroup.card_top, Nat.card_pi] at h1
  rw [← Finset.prod_coe_sort S]
  exact h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L D : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ D, T • y ∈ L) : ∀ z ∈ loc v D, T • z ∈ loc v L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨T • y, h y hy, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prod_loc_relIndex_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL S _
  obtain ⟨hlat, -, hTL, -, -⟩ := hL
  have hfin := (GlobalTheory.St.G.dualL_local_adelic F E cm n J hJ hdet L hlat).1.1
  have hTD : ∀ y ∈ dualL cm.sig J L, T • y ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact hTL x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  refine prod_relIndex_dvd (M := fun v : HeightOneSpectrum (𝓞 F) => Fin n → E ⊗[F] v.adicCompletion F)
    L.toAddSubgroup (dualL cm.sig J L).toAddSubgroup (fun v => (loc v L).toAddSubgroup)
    (fun v => (loc v (dualL cm.sig J L)).toAddSubgroup)
    (fun v => AddMonoidHom.compLeft (inclE (F := F) (E := E) (v.adicCompletion F)).toAddMonoidHom (Fin n)) S
    (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) ?_
  intro y hy
  obtain ⟨x, hx, h⟩ := GlobalTheory.OverCompare.exists_lattice_approx_all F E n (dualL cm.sig J L) hfin T hT.ne_zero y hy
  refine ⟨x, hx, fun v _ => ?_⟩
  obtain ⟨z, hz, e⟩ := h v
  have h1 := nsmul_mem_loc v T L _ hTD z hz
  have e2 : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v = -(T • z) := by
    rw [e]; abel
  show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v ∈ loc v L
  rw [e2]
  exact neg_mem h1

end GlobalTheory.St.G.GlobIdx
end

section

open NumberField Formalism.BasicNotions

namespace GlobalTheory.SA.AmbSig

open Matrix Module

theorem card_le_of_diag {p q d : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin d) ℂ) (δ : Fin d → ℂ)
    (hδ : ∀ j, (δ j).re ≤ 0) (hN : Nᴴ * Formalism.UG.Jpq p q * N = diagonal δ)
    (hinj : ∀ c, N *ᵥ c = 0 → c = 0) : d ≤ q := by
  classical

  let f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun c hc => ?_
    set w := N *ᵥ c with hw
    have hr : ∀ i, w (Sum.inr i) = 0 := fun i => congrFun hc i

    have hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c) := by
      rw [← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i)) := by
      unfold Formalism.UG.Jpq
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]
    have hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    have hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i)) := fun i => Complex.normSq_nonneg _
    have hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0 := by
      rw [← hleft, hform, hright]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)
    have hl : ∀ i, w (Sum.inl i) = 0 := fun i =>
      Complex.normSq_eq_zero.1 (le_antisymm
        ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))
    apply hinj
    funext x
    cases x with
    | inl i => exact hl i
    | inr i => exact hr i
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem hT_eq_sum {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ b, (∑ a, star (S.frame.repr x a) * S.gram a b) * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
  smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [HSpace.gram]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem amb_of_sig : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (k r : ℕ),
    GlobalTheory.SA.CMStar E → S.SigOK → (∀ τ : E →+* ℂ, S.sig τ = (k + r, r + 1)) → GlobalTheory.SA.Amb S k r := by
  intro E _ _ _ S k r hcm hok hsig

  have hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧
      ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ,
        Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧
        ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1 := by
    intro τ
    have h := hok τ
    rw [hsig τ] at h
    obtain ⟨h1, ⟨A, hA⟩, h3⟩ :=
      GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h
    obtain ⟨B, -, hBA⟩ := h3 A hA
    exact ⟨h1.symm, A, hA, B, hBA⟩
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨hcm, ?_, ?_⟩
  · rw [S.rank_eq, (hfac τ₀).1]
    ring
  · intro τ U hU
    classical
    obtain ⟨-, A, hA, B, hBA⟩ := hfac τ

    let F : U →ₗ[E] U →ₛₗ[starRingEnd E] E := S.hT.flip.domRestrict₁₂ U U
    have hF : ∀ x y, starRingEnd E (F x y) = F y x := fun x y => S.herm.eq (y : S.V) (x : S.V)
    obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E)
      two_ne_zero (Module.finrank E U) F hF rfl

    let v : Fin (Module.finrank E U) → Fin S.rank → E := fun j => S.frame.repr (u j : S.V)
    have hv : LinearIndependent E v := by
      have hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)
      exact u.linearIndependent.map' _ hker
    letI : Algebra E ℂ := τ.toAlgebra
    haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective
    have hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j) :=
      linearIndependent_algebraMap_comp_iff.2 hv
    let C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ := Matrix.of fun a j => τ (v j a)
    refine card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V)))
      (fun j => hU _ (u j).2) ?_ ?_
    · have hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) =
          Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hsplit, hA]
      ext i j
      have hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j := by

        rw [hT_eq_sum, map_sum, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_

        rw [map_mul, map_sum, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [C, v, hcm τ]
      rw [← hij, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · have h0 : F (u j) (u i) = 0 := hu j i (Ne.symm h)
        simp only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0
        rw [h0, map_zero]
    · intro c hc
      have hCc : C *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec] at hc
        rw [← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
      have hlin := Fintype.linearIndependent_iff.1 hvC c (by
        rw [← hCc]
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])
      funext j
      exact hlin j

end GlobalTheory.SA.AmbSig
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_exists_conj_near_reference : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.NormalPos.exists_near | exact GlobalTheory.DegCnt.NormalPos.exists_near | (intros; apply GlobalTheory.DegCnt.NormalPos.exists_near <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub {g | uMat g - 1 ∈ A} d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ (∀ μ', IsGaugeSub {g | uMat g - 1 ∈ A} d μ' → μ' = μ) ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ r₀ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | Formalism.REAL.hs (uMat g - 1) < r₁}, φ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re / r) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t)) := by
  first | exact @GlobalTheory.GaugeSubLoc.gauge_local_asymptotics | exact GlobalTheory.GaugeSubLoc.gauge_local_asymptotics | (intros; apply GlobalTheory.GaugeSubLoc.gauge_local_asymptotics <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ n, f n ∂(lebN k r) = ∫⁻ q : PSec k r j × (UToff β → ℂ), ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) := by
  first | exact @GlobalTheory.Amp.RadConj.lebN_split | exact GlobalTheory.Amp.RadConj.lebN_split | (intros; apply GlobalTheory.Amp.RadConj.lebN_split <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isPair_move_by_integralUnipotent : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  first | exact @GlobalTheory.LoopC.PairMove.pair_move | exact GlobalTheory.LoopC.PairMove.pair_move | (intros; apply GlobalTheory.LoopC.PairMove.pair_move <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by
  first | exact @GlobalTheory.HL.sumData_nT_eq_mass | exact GlobalTheory.HL.sumData_nT_eq_mass | (intros; apply GlobalTheory.HL.sumData_nT_eq_mass <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDefectClass_mem_trace_firstFrameSpan : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  first | exact @GlobalTheory.HL.TraceRep.class_from_trace | exact GlobalTheory.HL.TraceRep.class_from_trace | (intros; apply GlobalTheory.HL.TraceRep.class_from_trace <;> assumption)
end
