module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LatIdem

theorem exists_iterate_idem {X : Type*} [Finite X] (u : X → X) : ∃ N : ℕ, 0 < N ∧ u^[2 * N] = u^[N] := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ u^[i] = u^[j] := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => u^[n])
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact ⟨i, j, h1, h⟩
    · exact ⟨j, i, h1, h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have key : ∀ m : ℕ, u^[i + m * (k + 1)] = u^[i] := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : i + (m + 1) * (k + 1) = (i + m * (k + 1)) + (k + 1) := by ring
      rw [this, Function.iterate_add, ih, ← Function.iterate_add, ← add_assoc, ← h]
  refine ⟨(i + 1) * (k + 1), by positivity, ?_⟩
  have e1 : 2 * ((i + 1) * (k + 1)) = (i + (i + 1) * (k + 1)) + (i * k + k + 1) := by ring
  have e2 : (i + 1) * (k + 1) = i + (i * k + k + 1) := by ring
  rw [e1, Function.iterate_add, key, ← Function.iterate_add, ← e2]

theorem exists_idem_mod {M : Type*} [AddCommGroup M] (Λ P : AddSubgroup M) (g : M →+ M)
    (hΛ : ∀ z ∈ Λ, g z ∈ Λ) (hP : ∀ z ∈ P, g z ∈ P) [Finite (Λ.map (QuotientAddGroup.mk' P))] :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Λ, g^[2 * N] z - g^[N] z ∈ P := by
  let gb : M ⧸ P →+ M ⧸ P := QuotientAddGroup.map P P g hP
  let u : Λ.map (QuotientAddGroup.mk' P) → Λ.map (QuotientAddGroup.mk' P) := fun x => ⟨gb x, by
    obtain ⟨_, z, hz, rfl⟩ := x
    exact ⟨g z, hΛ z hz, rfl⟩⟩
  have hu : ∀ (n : ℕ) (z : M) (hz : z ∈ Λ), (u^[n] ⟨QuotientAddGroup.mk' P z, z, hz, rfl⟩ : M ⧸ P) =
      QuotientAddGroup.mk' P (g^[n] z) := by
    intro n
    induction n with
    | zero => intro z hz; rfl
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show gb _ = _
      rw [ih z hz]; rfl
  obtain ⟨N, hN, h⟩ := exists_iterate_idem u
  refine ⟨N, hN, fun z hz => ?_⟩
  have := hu (2 * N) z hz
  rw [h, hu N z hz] at this
  exact QuotientAddGroup.eq_iff_sub_mem.1 this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.EmbChart GlobalTheory.InertSph

theorem at_atPlace (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (atPlace v a) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem eq_atPlace (v : Pl (F := F)) (a : AF F) (ha : At (evFin F v) a) : a = atPlace v (evFin F v a) := by
  have h := ha (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, atPlace_mul_right, one_mul, sub_eq_zero] at h
  exact h

omit [NumberField E] in
theorem gen_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (c : v.adicCompletionIntegers F) (y : Fin d → E) (hy : y ∈ W.L) :
    (atPlace v (c : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
  AddSubgroup.subset_closure ⟨_, at_atPlace v _, by rw [evFin_atPlace]; exact c.2, y, hy, rfl⟩

theorem finite_mod {d : ℕ} (W : Spc F E d) (hW : W.L.FG) (v : Pl (F := F)) (p : ℕ) (hp : 0 < p) :
    Finite ((latAt W v).map (QuotientAddGroup.mk' ((latAt W v).map (nsmulAddMonoidHom p)))) := by
  set P := (latAt W v).map (nsmulAddMonoidHom p) with hPdef
  have hp0 : (p : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    have h1 : ((p : v.adicCompletionIntegers F) : Fv F v) = 0 := congrArg Subtype.val h
    have h2 : (p : Fv F v) = 0 := by simpa using h1
    rw [← map_natCast (algebraMap F (Fv F v)), map_eq_zero] at h2
    exact (Nat.cast_ne_zero.2 hp.ne') h2
  have hfin : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨T, hT⟩ : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hW
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 this
  have hTL : ∀ t ∈ T, t ∈ W.L := fun t ht => by
    have : t ∈ W.L.restrictScalars ℤ := hT ▸ Submodule.subset_span ht
    exact this
  let s : (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) × T → (Fin d → AE F E) ⧸ P :=
    fun x => QuotientAddGroup.mk' P
      (atPlace v ((x.1.out : v.adicCompletionIntegers F) : Fv F v) • fun i => inclR (F := F) (AF F) (x.2.1 i))
  have heq : (latAt W v).map (QuotientAddGroup.mk' P) = AddSubgroup.closure (Set.range s) := by
    apply le_antisymm
    · rw [AddSubgroup.map_le_iff_le_comap, InertSph.latAt, AddSubgroup.closure_le]
      rintro _ ⟨a, ha, hav, y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (T : Set (Fin d → E)) := hT ▸ hy
      clear hy
      rw [SetLike.mem_coe]
      induction hy' using Submodule.span_induction with
      | mem t ht =>
        let x : v.adicCompletionIntegers F := ⟨_, hav⟩
        let q := Ideal.Quotient.mk (Ideal.span {(p : v.adicCompletionIntegers F)}) x
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out q).symm)
        have hc' : evFin F v a - ((q.out : v.adicCompletionIntegers F) : Fv F v) = p • (c : Fv F v) := by
          have := congrArg Subtype.val hc
          simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, AddSubgroupClass.coe_sub] at this
          rw [nsmul_eq_mul, mul_comm]; exact this.symm
        rw [AddSubgroup.mem_comap]
        refine AddSubgroup.subset_closure ⟨(q, ⟨t, ht⟩), ?_⟩
        refine (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm
        refine ⟨_, gen_mem W v c t (hTL t ht), ?_⟩
        rw [← sub_smul, eq_atPlace v a ha, ← map_sub, hc', map_nsmul, smul_assoc]
        rfl
      | zero =>
        have : (a • fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := by
          funext i; simp
        rw [this]; exact zero_mem _
      | add x y _ _ hx hy =>
        have : (a • fun i => inclR (F := F) (AF F) ((x + y) i)) =
            (a • fun i => inclR (F := F) (AF F) (x i)) + (a • fun i => inclR (F := F) (AF F) (y i)) := by
          funext i; simp
        rw [this]; exact add_mem hx hy
      | smul n x _ hx =>
        have : (a • fun i => inclR (F := F) (AF F) ((n • x) i)) =
            n • (a • fun i => inclR (F := F) (AF F) (x i)) := by
          funext i
          simp only [Pi.smul_apply, map_zsmul]
          rw [smul_comm]
        rw [this]; exact zsmul_mem hx n
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, gen_mem W v _ _ (hTL _ x.2.2), rfl⟩
  have hfg : ((latAt W v).map (QuotientAddGroup.mk' P)).FG :=
    (AddSubgroup.fg_iff _).2 ⟨_, heq.symm, Set.finite_range s⟩
  have : AddGroup.FG ((latAt W v).map (QuotientAddGroup.mk' P)) := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine AddCommGroup.finite_of_fg_isAddTorsion _ ?_
  rintro ⟨_, z, hz, rfl⟩
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp, Subtype.ext ?_⟩
  show p • QuotientAddGroup.mk' P z = 0
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz, rfl⟩

theorem exists_pow_idem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  intro F E _ _ _ _ _ d W hW v p hp _ f hf
  have := finite_mod W hW.fg v p hp
  let g : (Fin d → AE F E) →+ (Fin d → AE F E) := (Matrix.mulVecLin f).toAddMonoidHom
  have hg : ∀ (n : ℕ) (z : Fin d → AE F E), g^[n] z = (f ^ n) *ᵥ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, pow_succ', ← Matrix.mulVec_mulVec]; rfl
  obtain ⟨N, hN, h⟩ := exists_idem_mod (latAt W v) ((latAt W v).map (nsmulAddMonoidHom p)) g hf (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨g z, hf z hz, (map_nsmul g p z).symm⟩)
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨y, hy, e⟩ := h z hz
  rw [hg, hg] at e
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.LatIdem
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvN.LagrangianNormalForm

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_ginv_form (X : Matrix κ κ F) :
    ∃ G C : Matrix κ κ F, X * G * X = X ∧ Cᵀ = C ∧ ∀ v, (Xᵀ * C * X) *ᵥ v = 0 → X *ᵥ v = 0 := by
  obtain ⟨L, L', d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal X
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have dP : IsUnit P.det := by rw [hP, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have dQ : IsUnit Q.det := by rw [hQ, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have hX : X = P⁻¹ * Matrix.diagonal d * Q⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ dP]
  have hPX : P * X = Matrix.diagonal d * Q⁻¹ := by
    rw [← h]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one]
  refine ⟨Q * Matrix.diagonal (fun i => (d i)⁻¹) * P, Pᵀ * P, ?_, ?_, ?_⟩
  · have e : Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) = Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      by_cases hi : d i = 0
      · simp [hi]
      · simp [hi]
    conv_lhs => rw [hX]
    conv_rhs => rw [hX, ← e]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ dQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ dP]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro v hv
    have e : Xᵀ * (Pᵀ * P) * X = (Q⁻¹)ᵀ * (Matrix.diagonal d * (Matrix.diagonal d * Q⁻¹)) := by
      have : Xᵀ * (Pᵀ * P) * X = (P * X)ᵀ * (P * X) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, hPX, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e] at hv
    have h2 := congrArg (fun w => Qᵀ *ᵥ w) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ dQ, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h2
    have h3 : Matrix.diagonal d *ᵥ (Q⁻¹ *ᵥ v) = 0 := by
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
      rcases mul_eq_zero.mp this with h0 | h0
      · simp [h0]
      · exact h0
    rw [hX, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

theorem exists_symm_isUnit (X Y : Matrix κ κ F) (hs : Xᵀ * Y = Yᵀ * X)
    (hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0) :
    ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (Y + C * X).det := by
  obtain ⟨G, C, hG, hC, hv⟩ := exists_ginv_form X
  refine ⟨C - Gᵀ * (Xᵀ * Y) * G, ?_, ?_⟩
  · rw [Matrix.transpose_sub, hC]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᵀ, ← hs, Matrix.mul_assoc]
  · have e : Xᵀ * (Y + (C - Gᵀ * (Xᵀ * Y) * G) * X) = Xᵀ * C * X := by
      have e1 : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = Xᵀ * Y := by
        have : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = (X * G * X)ᵀ * Y * G * X := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this, hG, hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc X, hG]
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, e1, Matrix.mul_assoc]
      abel
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv1⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hX : X *ᵥ v = 0 := by
      apply hv
      rw [← e, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]
    apply hv0
    apply hi v hX
    rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, add_zero] at hv1

theorem upper_mem (S : Matrix κ κ F) (hS : Sᵀ = S) :
    Matrix.fromBlocks 1 S 0 1 ∈ Submonoid.closure (gens F κ) := by
  have hJ : Matrix.fromBlocks (0 : Matrix κ κ F) (1 : Matrix κ κ F) (-1 : Matrix κ κ F) (0 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inr rfl)
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-S) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨S, hS, rfl⟩))
  have := mul_mem (mul_mem (mul_mem (mul_mem hJ hn) hJ) hJ) hJ
  simpa [Matrix.fromBlocks_multiply] using this

theorem exists_mem_closure (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hd : Module.finrank F L = Fintype.card κ) :
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  let b : Module.Basis κ F L := (Module.finBasisOfFinrankEq F L hd).reindex (Fintype.equivFin κ).symm
  let X : Matrix κ κ F := Matrix.of fun i j => (b j).1.1 i
  let Y : Matrix κ κ F := Matrix.of fun i j => (b j).1.2 i
  have key : ∀ v : κ → F, (X *ᵥ v, Y *ᵥ v) = ((∑ j, v j • b j : L) : (κ → F) × (κ → F)) := by
    intro v
    ext i
    · simp [X, Matrix.mulVec, dotProduct, Prod.fst_sum, mul_comm]
    · simp [Y, Matrix.mulVec, dotProduct, Prod.snd_sum, mul_comm]
  have hs : Xᵀ * Y = Yᵀ * X := by
    ext i j
    have := hL _ (b i).2 _ (b j).2
    simp only [dotProduct] at this
    simp only [Matrix.mul_apply, X, Y, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0 := by
    intro v h1 h2
    have h3 := key v
    rw [h1, h2] at h3
    have h4 : ∑ j, v j • b j = 0 := Subtype.ext h3.symm
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v h4 j
  obtain ⟨C, hC, hM⟩ := exists_symm_isUnit X Y hs hi
  set M := Y + C * X with hMdef
  have hXM : Xᵀ * M = Mᵀ * X := by
    rw [hMdef, Matrix.transpose_add, Matrix.transpose_mul, hC, Matrix.mul_add, Matrix.add_mul, hs,
      Matrix.mul_assoc]
  have hS : (X * M⁻¹)ᵀ = X * M⁻¹ := by
    have h1 : (M⁻¹)ᵀ * Mᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]
    calc (X * M⁻¹)ᵀ = (M⁻¹)ᵀ * (Xᵀ * M) * M⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = X * M⁻¹ := by rw [hXM, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-C) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  refine ⟨_, mul_mem hn (upper_mem _ hS), fun y => ?_⟩
  have hy : Y *ᵥ (M⁻¹ *ᵥ y) = -(C *ᵥ (X *ᵥ (M⁻¹ *ᵥ y))) + y := by
    have : M *ᵥ (M⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
    generalize M⁻¹ *ᵥ y = v at this ⊢
    rw [← this, hMdef, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hmem : (X *ᵥ (M⁻¹ *ᵥ y), Y *ᵥ (M⁻¹ *ᵥ y)) ∈ L := by rw [key]; exact Subtype.property _
  rw [hy] at hmem
  simpa [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hmem

end GlobalTheory.AdelicSvN.LagrangianNormalForm
end

section

noncomputable section

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.PolynomialMatching

section Extend

variable {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def padFam (T S : Finset ι) (c : ∀ i, M i) (x : ∀ u : T, M u) : ∀ u : S, M u :=
  fun u => if h : u.1 ∈ T then x ⟨u.1, h⟩ else c u.1

theorem padFam_update (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) [DecidableEq T] [DecidableEq S]
    (x : ∀ u : T, M u) (i : T) (y : M i) :
    padFam T S c (Function.update x i y) = Function.update (padFam T S c x) ⟨i.1, hTS i.2⟩ y := by
  funext u
  by_cases h : u.1 ∈ T
  · by_cases hu : u.1 = i.1
    · obtain ⟨u, hu'⟩ := u
      obtain ⟨i, hi⟩ := i
      simp only at hu
      subst hu
      simp [padFam, h]
    · have h1 : (⟨u.1, h⟩ : T) ≠ i := fun e => hu (by rw [← e])
      have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => hu (by rw [e])
      simp only [padFam, h, dif_pos, Function.update_of_ne h1, Function.update_of_ne h2]
  · have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => h (by rw [e]; exact i.2)
    simp only [padFam, h, dif_neg, not_false_eq_true, Function.update_of_ne h2]

def padMultilinear (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (∀ u : T, M u) →ₘₗ[ℂ] (⨂[ℂ] u : S, M u) where
  toFun x := PiTensorProduct.tprod ℂ (padFam T S c x)
  map_update_add' x i y z := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i r y := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

def padTensor (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (⨂[ℂ] u : T, M u) →ₗ[ℂ] ⨂[ℂ] u : S, M u :=
  PiTensorProduct.lift (padMultilinear T S hTS c)

theorem padTensor_tprod (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) (x : ∀ u : T, M u) :
    padTensor T S hTS c (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (padFam T S c x) := by
  simp [padTensor, padMultilinear]

end Extend

theorem polMatchOn_insert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (v : Pl (F := F)),
    Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v) → ∀ (T : Finset (Pl (F := F))) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' →
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf (insert v T) Φ Φ' := by
  intro F E _ _ _ _ _ σ B a a' G X R Rf v hv T Φ Φ' hM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hM
  refine ⟨m, m', f, φ, f', φ',
    fun i => ⟨(hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(hφ' j).1, (hφ' j).2.1, fun w hw => (hφ' j).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    hΦ, hΦ', ?_⟩
  let c : ∀ u, Rf.Pi u := fun u => Rf.p u (G.M.vac u)
  have key := congrArg (LinearMap.lTensor R.Pi (padTensor T (insert v T) (Finset.subset_insert _ _) c)) hsum

  simp only [map_sum, LinearMap.lTensor_tmul, padTensor_tprod] at key
  have e1 : ∀ i, padFam T (insert v T) c (fun u : T => Rf.p u (φ i u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p u (φ i u) := by
    intro i
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · simp [padFam, h, c, (hφ i).2.2 u.1 h]
  have e2 : ∀ j, padFam T (insert v T) c (fun u : T => Rf.p' u (φ' j u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p' u (φ' j u) := by
    intro j
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · obtain ⟨u, hu⟩ := u
      have huv : u = v := by
        rcases Finset.mem_insert.1 hu with h' | h'
        · exact h'
        · exact absurd h' h
      subst huv
      simp [padFam, h, c, (hφ' j).2.2 u h, hv]
  simp only [e1, e2] at key
  exact key

end GlobalTheory.ThK.PolynomialMatching
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertLocFrame.xm_bij_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (L : Type) [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        At (evFin F v) z ↔ ∃ x, GlobalTheory.InertLocFrame.xm ι PV PW x = z := by
  intro F E _ _ _ _ _ v n d L _ ι _ him _ PV PW z
  constructor
  · intro hz
    have hent : ∀ i j, ∃ y, ι y = z i j := fun i j => (him (z i j)).1 (fun u hu => by
        have := congrFun (congrFun (hz u hu) i) j
        simpa using this)
    choose y hy using hent
    refine ⟨(((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y * ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ)ᵀ, ?_⟩
    rw [GlobalTheory.InertLocFrame.xm_apply, Matrix.transpose_transpose]
    have h1 : (PV : Matrix (Fin n) (Fin n) L) * ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv PV
    have h2 : (((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h3 : (PV : Matrix (Fin n) (Fin n) L) * (((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y *
        ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ) * (PW : Matrix (Fin d) (Fin d) L)ᵀ = Matrix.of y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [h3]
    ext i j
    simp [hy]
  · rintro ⟨x, rfl⟩ u hu
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.InertLocFrame.xm_apply, Matrix.map_apply]
    exact (him _).2 ⟨_, rfl⟩ u hu
end
