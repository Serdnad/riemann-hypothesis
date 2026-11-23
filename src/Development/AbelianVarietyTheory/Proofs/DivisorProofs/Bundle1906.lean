module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny



namespace GlobalTheory.LatVacBdd

theorem exists_ne_zero_mul_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (S : Finset (v.adicCompletion F)) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∀ a ∈ S, c * a ∈ v.adicCompletionIntegers F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert b S hb ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    by_cases hcb : c * b ∈ v.adicCompletionIntegers F
    · refine ⟨c, hc0, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hcb
      · exact hc a ha
    · have hinv : (c * b)⁻¹ ∈ v.adicCompletionIntegers F :=
        ((v.adicCompletionIntegers F).mem_or_inv_mem (c * b)).resolve_left hcb
      have hcb0 : c * b ≠ 0 := fun h => hcb (h ▸ zero_mem _)
      refine ⟨c * (c * b)⁻¹, mul_ne_zero hc0 (inv_ne_zero hcb0), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [mul_assoc, mul_comm _ a, ← mul_assoc, mul_inv_cancel₀ hcb0]; exact one_mem _
      · rw [mul_comm c, mul_assoc]; exact mul_mem hinv (hc a ha)

end GlobalTheory.LatVacBdd

theorem GlobalTheory.LatVacBdd.locCo_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  classical
  choose yf zf hyz using hT.geo.hM.rat
  obtain ⟨sX, hsX⟩ := hT.geo.hV.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hT.geo.hW.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin a → E) →ₗ[ℤ] (Fin (a + a') → E) →ₗ[ℤ] Matrix (Fin a) (Fin (a + a')) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  let T₀ : Finset (Matrix (Fin a) (Fin (a + a')) E) := Finset.image₂ (fun x y => f x y) sX sY
  have hmem : ∀ x ∈ G.V.L, ∀ y ∈ G.W.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ (T₀ : Set _) := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin a → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin (a + a') → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rw [Submodule.map₂_span_span] at this
    rw [Finset.coe_image₂]; exact this
  have hgen : latAtV G.V G.W v ≤ AddSubgroup.closure {z | ∃ b : AF F,
      At (evFin F v) b ∧ evFin F v b ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = b • incM F t} := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨b, hb, hbv, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin a) (Fin (a + a')) E →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ b).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure (T₀ : Set _) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure (T₀ : Set _)).map g :=
      AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b, hb, hbv, t, ht, rfl⟩
  let S : Finset (Fv F v) :=
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (yf p.1 p.2)) ∪
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (zf p.1 p.2))
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatVacBdd.exists_ne_zero_mul_mem v S
  have hcy : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hcz : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hev : ∀ y : F, evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := fun y => AlgHom.commutes _ _
  refine ⟨c, hc0, fun γ hγ => ?_⟩
  clear_value T₀
  revert hγ
  intro hγ
  have hγ' := hgen hγ
  clear hγ
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, -, hbv, t, ht, rfl⟩ := hz
    intro k
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, hyz,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, hev]
    exact ⟨by rw [mul_left_comm]; exact mul_mem hbv (hcy t ht k),
      by rw [mul_left_comm]; exact mul_mem hbv (hcz t ht k)⟩
  | zero => intro k; simp
  | add x y _ _ hx hy =>
    intro k
    rw [map_add (f := _)]
    exact ⟨by rw [Prod.fst_add, Pi.add_apply, mul_add]; exact add_mem (hx k).1 (hy k).1,
      by rw [Prod.snd_add, Pi.add_apply, mul_add]; exact add_mem (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨by rw [Prod.fst_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).1,
      by rw [Prod.snd_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).2⟩
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

open Matrix

theorem swap_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  intro F E _ _ _ _ _ σ n J v f hQf hff hfc
  set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef
  have hQQ : Q * Q = Q := by
    have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q)
      (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef
  set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef
  have hp : p = 1 - q := by rw [hpdef, map_sub, map_one]
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQQ]
  have hqf : q * f = f := by rw [hqdef, ← Algebra.smul_def]; exact hQf
  have hcp : cA σ p = p := AlgHom.commutes _ _
  have hpp : p * p = p := by rw [hp]; linear_combination hqq
  have hpf : p * f = 0 := by rw [hp]; linear_combination -hqf
  have hpcf : p * cA σ f = 0 := by rw [← hcp, ← map_mul, hpf, map_zero]
  have hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N :=
    fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm
  have hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1 := by
    intro a; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
      ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef
  have hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1) := by
    rw [hMdef, ← hQdef, hsm]

  have hMM : M * M = 1 := by
    rw [hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
  have hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J) := by
    rw [hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul, smul_neg]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
    all_goals
      first
        | linear_combination incM F J i j * (hpp - hfc + hp)
        | linear_combination incM F J i j * (hfc - hpp - hp)
        | linear_combination incM F J i j * (hpcf - hpf)
        | linear_combination incM F J i j * (hpf - hpcf)
        | linear_combination incM F J i j * (hpcf + hpf)
        | linear_combination incM F J i j * (-hpcf - hpf)

  refine ⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩
  · intro u hu
    show u • (M - 1) = 0
    have hQu : u * Q = 0 := by
      have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
      rwa [← hQdef, smul_eq_mul] at h
    set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef
    have huq : ua * q = 0 := by rw [huadef, hqdef, ← map_mul, hQu, map_zero]
    have huf : ua * f = 0 := by rw [← hqf]; linear_combination f * huq
    rw [← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>
      first
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)
          | linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))
          | linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
  · intro k hk gd gd' hgd hgd'
    apply Subtype.ext
    apply Units.ext
    show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M =
      ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    have hK : p • (mat k - 1) = 0 := by
      rw [← hsm]
      exact hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    have hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
      intro i j
      have h := congrFun (congrFun hK i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h
      linear_combination h
    rw [hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul, smul_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    all_goals
      first
        | linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)
        | linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)
        | linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)

end GlobalTheory.DblDiag
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

theorem smul_eq_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m n : Type}
    {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (h1 : ∀ i j, piW t g * piW t (u i j) = 0) (h2 : ∀ i j, piW (t.comp σ) g * piW (t.comp σ) (u i j) = 0) :
    g • u = 0 := by
  have h0 := one_sub_smul hu
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  ext i j
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u i j = u i j := (congrFun (congrFun h0 i) j).symm
  refine eq_zero_of_piW h t ?_ ?_ ?_
  · rw [Matrix.smul_apply, smul_comm, h3]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h2]

theorem swap_at_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  intro F E _ _ _ _ _ σ h a' d J v t f hf _ _ ht htσ w hw
  refine ⟨?_, ?_⟩
  · intro r hr
    have h1 : r * GlobalTheory.LatVac.liftV v (1 : Fv F v) = 0 := GlobalTheory.LatVac.at_liftV v 1 r hr
    have h2 : r • f = 0 := by rw [← hf, smul_smul, h1, zero_smul]
    have h3 : r * (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = r := by rw [mul_sub, h1, mul_one, sub_zero]
    rw [hw, smul_sub, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, smul_smul, h3,
      ← smul_assoc, h2, zero_smul, smul_zero, sub_self]
  · intro u₁ u₂ hu₁ hu₂
    have hact : actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (f • u₂) (f • u₁) := by
      unfold actB
      rw [hw, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, one_sub_smul hu₁,
        one_sub_smul hu₂, zero_add, add_zero]
    have hneg : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW t) = 0 → f • u = -u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f + 1)
        (fun i j => by rw [show piW t (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
        (fun i j => by rw [map_add (f := _), htσ, map_one, neg_add_cancel, zero_mul])
      rwa [add_smul, one_smul, add_eq_zero_iff_eq_neg] at this
    have hpos : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → f • u = u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f - 1)
        (fun i j => by rw [map_sub, ht, map_one, sub_self, zero_mul])
        (fun i j => by rw [show piW (t.comp σ) (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    exact ⟨fun h1 h2 => by rw [hact, hneg _ hu₁ h1, hneg _ hu₂ h2],
      fun h1 h2 => by rw [hact, hpos _ hu₁ h1, hpos _ hu₂ h2]⟩

end GlobalTheory.SwapAtPlace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem sum_integral_translates_outer_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G μ₀ hL W t i j M hM Θ' F hB g₁ z hI hJ
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid i j) ⟨i.2.le, j.2.le⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i (j + 1)) =
      Θ'.sum fun d c => c * translates z (outer W M d F g₁) u := by
    intro u
    have hint : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun g => W.kerA (.down t i j) d.1.2 g (u * k) * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd k => (hB d hd).1.2 (u * k)
    have e : ∀ g, F g * translates z (kerSmall W Θ' g g₁) u = ∑ k ∈ z.support, ∑ d ∈ Θ'.support,
        z k * (Θ' d * (W.kerA (.right i j) d.2 (u * k) g₁ * (W.kerA (.down t i j) d.1.2 g (u * k) * F g))) := by
      intro g
      simp only [translates, kerSmall, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun d hd =>
      (((hint d hd k).const_mul _).const_mul _).const_mul _]
    simp_rw [integral_finsetSum _ fun d hd => (((hint d hd _).const_mul _).const_mul _).const_mul _]
    simp only [integral_const_mul, translates, outer, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by ring
  have hint2 : ∀ d ∈ Θ'.support, Integrable (translates z (outer W M d F g₁))
      ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) := fun d hd =>
    integrable_finsetSum _ fun k _ => (hI d hd k).const_mul _
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j), translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid i j), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid i j), ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid i j) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid i j), (Θ'.sum fun d c => c * translates z (outer W M d F g₁) u) ∂M.ν (.grid i j) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]

end GlobalTheory.SmallRoute

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  first | exact @GlobalTheory.PointTranslate.exists_point_cls_eq_lam | exact GlobalTheory.PointTranslate.exists_point_cls_eq_lam | (intros; apply GlobalTheory.PointTranslate.exists_point_cls_eq_lam <;> assumption)
end
