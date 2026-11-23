module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem indexTwo_unitary (y : L) (hy : σ y + y = 0) :
    cT σ !![1, y; 0, 1] * antiJ L 2 * !![1, y; 0, 1] = antiJ L 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [add_comm]; exact hy

theorem indexTwo_exists_hom (σ : L →+* L) (T : AddSubgroup L) (hT : ∀ y, y ∈ T ↔ σ y + y = 0) :
    ∃ ψ : Multiplicative T →* GU σ 2,
      ∀ y, mat (ψ y) = !![1, (y.toAdd : L); 0, 1] := by
  have h : ∀ y : Multiplicative T,
      ∃ g : GU σ 2, mat g = !![1, (y.toAdd : L); 0, 1] := fun y =>
    exists_mat _ (indexTwo_unitary _ ((hT _).1 y.toAdd.2))
  choose f hf using h
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, hf⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, AddSubgroup.coe_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem indexTwo_mem_root (g : GU σ 2) :
    g ∈ rootU σ ![0, 0] ↔ mat g = !![1, mat g 0 1; 0, 1] := by
  constructor
  · intro h
    have h1 : ∀ i j : Fin 2, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 2) (Fin 2) L) i j := h.1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1 0 0 (by simp)
    · simp
    · simpa using h1 1 0 (by simp)
    · simpa using h1 1 1 (by simp)
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [h]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp at hij

theorem indexTwo_trace (g : GU σ 2) (y : L) (h : mat g = !![1, y; 0, 1]) : σ y + y = 0 := by
  have h1 : cT σ (mat g) * antiJ L 2 * mat g = antiJ L 2 := g.2
  rw [h] at h1
  have := congrFun (congrFun h1 1) 1
  simpa [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using this

theorem indexTwo_conj {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by
  have e : mat s * mat g = !![1, ϖ * (ϖ * y); 0, 1] * mat s := by
    rw [hs, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [mat_mul, mat_mul, e, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

end

theorem indexTwo_of_traceZeroIndex (H : TraceZeroIndex) : IndexTwo := by
  intro L _ _ ϖ σ q hU s hs
  have hq := H L ϖ σ q hU
  have h0 : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  have memT : ∀ y, y ∈ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔ σ y + y = 0 := fun y => Iff.rfl
  generalize (σ.toAddMonoidHom + AddMonoidHom.id L).ker = T at hq memT
  obtain ⟨ψ, hψ⟩ := indexTwo_exists_hom σ T memT
  set U := (intL L).toAddSubgroup ⊓ T with hUdef
  set m : L →+ L := AddMonoidHom.mulLeft ϖ with hm
  have hmT : ∀ y, y ∈ T → ϖ * y ∈ T := fun y hy => by
    rw [memT] at hy ⊢
    rw [map_mul, hU.2.2.1, ← mul_add, hy, mul_zero]
  have hminj : Function.Injective m := mul_right_injective₀ h0
  have hle : U.map m ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(intL L).mul_mem hϖ hy.1, hmT y hy.2⟩
  have h2 : ((U.map m).map m).relIndex U = q ^ 2 := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ (U.map m) _ (AddSubgroup.map_mono hle) hle,
      AddSubgroup.relIndex_map_map_of_injective _ _ hminj, hq, sq]
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := congrFun (congrFun ((hψ a).symm.trans ((congrArg mat hab).trans (hψ b))) 0) 1
    exact Multiplicative.toAdd.injective (Subtype.ext (by simpa using this))
  have e1 : KU σ 2 ⊓ rootU σ ![0, 0] = (AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨hK, hr⟩
      have hr' := (indexTwo_mem_root g).1 hr
      have ht := (memT _).2 (indexTwo_trace g _ hr')
      refine ⟨Multiplicative.ofAdd ⟨mat g 0 1, ht⟩, ⟨(mem_KU_iff hU.2.1 g).1 hK 0 1, ht⟩, mat_injective ?_⟩
      rw [hψ]; exact hr'.symm
    · rintro ⟨y, hy, rfl⟩
      have hy1 : (y.toAdd : L) ∈ intL L := hy.1
      refine ⟨(mem_KU_iff hU.2.1 _).2 fun i j => ?_, (indexTwo_mem_root _).2 ?_⟩
      · rw [hψ]
        fin_cases i <;> fin_cases j
        · exact one_mem _
        · exact hy1
        · exact zero_mem _
        · exact one_mem _
      · rw [hψ]; rfl
  have e2 : ((AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ).map (MulAut.conj s).toMonoidHom =
      (AddSubgroup.toSubgroup (((U.map m).map m).addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨ϖ * (ϖ * (y.toAdd : L)), hmT _ (hmT _ y.toAdd.2)⟩,
        ⟨_, ⟨_, hy, rfl⟩, rfl⟩, mat_injective ?_⟩
      rw [hψ]
      exact (indexTwo_conj h0 s _ hs _ (hψ y)).symm
    · rintro ⟨z, ⟨_, ⟨y, hy, rfl⟩, hz⟩, rfl⟩
      refine ⟨ψ (Multiplicative.ofAdd ⟨y, hy.2⟩), ⟨Multiplicative.ofAdd ⟨y, hy.2⟩, hy, rfl⟩, mat_injective ?_⟩
      refine (indexTwo_conj h0 s _ hs _ (hψ _)).trans ?_
      rw [hψ]
      exact congrArg (fun w => !![1, w; 0, 1]) hz
  rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup,
    AddSubgroup.relIndex_addSubgroupOf inf_le_right, h2]

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

noncomputable section

namespace GlobalTheory.SatakeWeyl.ContractProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) :
    mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-c i)) := by
  have h1 : mat s * Matrix.diagonal (fun i => ϖ ^ (-c i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; simp
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-c i))) := by rw [h1, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (i l : Fin r) :
    mat (s * g * s⁻¹) i l = ϖ ^ (c i - c l) * mat g i l := by
  rw [mat_mul, mat_mul, mat_inv_diag h0 c s hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ h0]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_pow_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by
  induction j with
  | zero => simp [mat_one]
  | succ j ih =>
    rw [pow_succ, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; congr 1; push_cast; ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem conj_mem_root {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by
  refine ⟨fun i l h => ?_, fun i l h => ?_⟩
  · rw [mat_conj h0 c s g hs, hg.1 i l h]
    by_cases e : i = l
    · subst e; simp
    · rw [Matrix.one_apply_ne e, mul_zero]
  · rw [mat_conj h0 c s g hs, hg.2 i l h, mul_zero]

theorem conj_mem_K {ϖ : L} (h0 : ϖ ≠ 0) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (γ : Fin r → ℕ) (c : Fin r → ℤ)
    (s g : GU σ r) (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ)
    (H : ∀ i l, i < l → γ i = γ l → ϖ ^ (c i - c l) * mat g i l ∈ intL L) : s * g * s⁻¹ ∈ KU σ r := by
  rw [mem_KU_iff hσ]
  intro i l
  have hr := conj_mem_root h0 γ c s g hs hg
  by_cases h1 : i < l
  · by_cases h2 : γ i = γ l
    · rw [mat_conj h0 c s g hs]; exact H i l h1 h2
    · rw [hr.2 i l h2]; exact zero_mem _
  · rw [hr.1 i l (not_lt.1 h1), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem zpow_mul_int {ϖ : L} (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ϖ ^ m * x ∈ intL L := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hx' : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := by simpa using hx
  refine ⟨(WithZero.log (Valued.v x : WithZero (Multiplicative ℤ))).toNat, fun m hm => ?_⟩
  show Valued.v (ϖ ^ m * x) ≤ (1 : WithZero (Multiplicative ℤ))
  rw [map_mul, map_zpow₀, hv, ← WithZero.exp_log hx', ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat (WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)))
  simp only [smul_eq_mul]
  omega

theorem contract : GlobalTheory.SatakeWeyl.Contract := by
  intro L _ _ ϖ σ q r γ b s g hU hb hs hg
  obtain ⟨-, hσ, -, hv, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  refine ⟨conj_mem_root h0 γ b s g hs hg, ?_, fun hK => ?_, ?_⟩
  · have := conj_mem_root h0 γ _ s⁻¹ g (mat_inv_diag h0 b s hs) hg
    rwa [inv_inv] at this
  · refine conj_mem_K h0 hσ γ b s g hs hg fun i l h1 h2 => ?_
    refine mul_mem ?_ ((mem_KU_iff hσ g).1 hK i l)
    show Valued.v (ϖ ^ (b i - b l)) ≤ (1 : WithZero (Multiplicative ℤ))
    have := hb i l h1 h2
    rw [map_zpow₀, hv', ← WithZero.exp_zsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    omega
  · choose N hN using fun p : Fin r × Fin r => zpow_mul_int hv' (mat g p.1 p.2)
    refine ⟨Finset.univ.sup N, conj_mem_K h0 hσ γ _ _ g (mat_pow_diag h0 b s hs _) hg fun i l h1 h2 => ?_⟩
    refine hN (i, l) _ ?_
    have h3 := hb i l h1 h2
    have h4 : (N (i, l) : ℤ) ≤ (Finset.univ.sup N : ℕ) := by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ _)
    have h5 : (0 : ℤ) ≤ (Finset.univ.sup N : ℕ) := Int.natCast_nonneg _
    nlinarith

end GlobalTheory.SatakeWeyl.ContractProof

end
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem traceZeroIndex_of_intIndex : IntIndex → TraceZeroIndex := by
  intro hI L _ _ ϖ σ q hU
  have hq := hI L ϖ σ q hU
  obtain ⟨hσσ, hv, hϖ, -, ⟨x, hx, hδ⟩, -, -⟩ := hU
  have hσO : ∀ y ∈ intL L, σ y ∈ intL L := fun y hy => by
    show Valued.v (σ y) ≤ 1
    rw [hv]; exact hy
  have hδ0 : σ x - x ≠ 0 := fun h => by rw [h, map_zero] at hδ; exact zero_ne_one hδ
  have hδ1 : x - σ x ≠ 0 := fun h => hδ0 (by linear_combination -h)
  have hδi : (σ x - x)⁻¹ ∈ intL L := by
    show Valued.v (σ x - x)⁻¹ ≤ 1
    rw [map_inv₀, hδ, inv_one]
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y = -y := fun y => by
    rw [hT, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, ← add_eq_zero_iff_eq_neg]
    rfl
  have hw : ∀ y ∈ intL L, σ y - y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (hσO y hy) hy, by rw [map_sub, hσσ]; ring⟩
  have hu : ∀ y ∈ intL L, σ x * y - x * σ y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (mul_mem (hσO x hx) hy) (mul_mem hx (hσO y hy)), by
      rw [map_sub, map_mul, map_mul, hσσ, hσσ]; ring⟩
  let f : T × T →+ (intL L).toAddSubgroup :=
    { toFun := fun p => ⟨(σ x - x)⁻¹ * (p.1.1 + x * p.2.1),
        (intL L).mul_mem hδi ((intL L).add_mem ((memT _).1 p.1.2).1 ((intL L).mul_mem hx ((memT _).1 p.2.2).1))⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp; ring) }
  have hf : ∀ p, (f p : L) = (σ x - x)⁻¹ * (p.1.1 + x * p.2.1) := fun _ => rfl
  have hsurj : Function.Surjective f := fun y =>
    ⟨(⟨_, hu y.1 y.2⟩, ⟨_, hw y.1 y.2⟩), Subtype.ext (by rw [hf]; field_simp; ring)⟩
  have hc : (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup).comap f =
      ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T).prod ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T) := by
    ext ⟨u, w⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map,
      hf, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨y, hy, e⟩
      have e1 : (σ x - x) * (ϖ * y) = u.1 + x * w.1 := by rw [e]; field_simp
      have e2 := congrArg σ e1
      rw [map_mul, map_sub, hσσ, map_mul, hϖ, map_add (f := _), map_mul, ((memT _).1 u.2).2, ((memT _).1 w.2).2] at e2
      have e3 : ϖ * (σ y - y) = w.1 := mul_left_cancel₀ hδ0 (by linear_combination -e1 - e2)
      exact ⟨⟨_, hu y hy, by linear_combination e1 - x * e3⟩, _, hw y hy, e3⟩
    · rintro ⟨⟨a, ha, e1⟩, b, hb, e2⟩
      refine ⟨_, (f (⟨a, ha⟩, ⟨b, hb⟩)).2, ?_⟩
      rw [hf, ← e1, ← e2]; ring
  have h2 := AddSubgroup.index_comap_of_surjective
    (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup) hsurj
  rw [hc, AddSubgroup.index_prod, ← pow_two] at h2
  exact Nat.pow_left_injective two_ne_zero (h2.trans hq)

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_out_inv_congr {A : Type} [Group A] (U V : Subgroup A) (e : MulAut A) (f : A → ℂ)
    (he : ∀ a, a ∈ U ↔ e a ∈ V) (hV : ∀ v ∈ V, ∀ a, f (v * a) = f a) :
    ∑ᶠ y : A ⧸ U, f (e y.out)⁻¹ = ∑ᶠ y : A ⧸ V, f y.out⁻¹ := by
  let E : A ⧸ U ≃ A ⧸ V := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he, map_mul, map_inv]
    rfl)
  have hE : ∀ a : A, E (QuotientGroup.mk a) = QuotientGroup.mk (e a) := fun a => rfl
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun y => ?_
  have h1 : E y = QuotientGroup.mk (e y.out) := by
    rw [← hE, QuotientGroup.out_eq']
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V (e y.out)
  rw [h1, hv, mul_inv_rev, hV _ (V.inv_mem v.2)]

theorem chainSum_of_unimod : Unimod → ChainIndex → ChainSum := by
  classical
  intro hUn hCh A _ U c Q d f hc hQ hind hex hV hU hfin
  have hchain := hCh A U c Q hc hind
  have hmem : ∀ (j : ℤ) (a : A), a ∈ U.comap (c ^ j).toMonoidHom ↔ (c ^ j) a ∈ U := fun j a => Iff.rfl
  have hmono : ∀ j j' : ℤ, j ≤ j' → U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ j').toMonoidHom := by
    intro j j' h
    have := (hchain j (j' - j).toNat).1
    rwa [show j + ((j' - j).toNat : ℤ) = j' by omega] at this
  have h0 : U.comap (c ^ (0 : ℤ)).toMonoidHom = U := by
    ext a
    rw [hmem, zpow_zero, MulAut.one_apply]
  choose J hJ using hex
  obtain ⟨k, hkd, hk⟩ : ∃ k : ℕ, d ≤ k ∧ ∀ y : A ⧸ U, f y.out ≠ 0 → J y.out ≤ k := by
    refine ⟨hfin.toFinset.sup (fun y => J y.out) + d.toNat, by omega, fun y hy => ?_⟩
    exact le_trans (Finset.le_sup (f := fun y : A ⧸ U => J y.out) (hfin.mem_toFinset.2 hy)) (Nat.le_add_right _ _)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, d + l = k := ⟨(k - d).toNat, by omega⟩
  have hUΓ : U ≤ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    have := hmono 0 k (by omega)
    rwa [h0] at this
  have iU : U.relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ k := by
    have := (hchain 0 k).2
    rwa [h0, zero_add] at this
  have iV : (U.comap (c ^ d).toMonoidHom).relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ l := by
    have := (hchain d l).2
    rwa [hl] at this
  have hsupp : ∀ a, f a ≠ 0 → a ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    intro a ha
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U a
    have h1 : f (QuotientGroup.mk a : A ⧸ U).out ≠ 0 := by rwa [hu, hU _ u.2]
    have h2 : (QuotientGroup.mk a : A ⧸ U).out ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
      refine hmono (J (QuotientGroup.mk a : A ⧸ U).out : ℕ) k (by exact_mod_cast hk _ h1) ?_
      rw [hmem, zpow_natCast]
      exact hJ _
    rw [hu] at h2
    exact (Subgroup.mul_mem_cancel_right _ (hUΓ u.2)).1 h2
  have key := hUn A _ U (U.comap (c ^ d).toMonoidHom) f hUΓ (hmono d k hkd)
    (by rw [iU]; exact pow_ne_zero _ hQ) (by rw [iV]; exact pow_ne_zero _ hQ) hsupp
    (fun v hv => hV v hv) hU
  rw [finsum_out_inv_congr U (U.comap (c ^ d).toMonoidHom) (c ^ (-d)) f (fun a => by
    rw [hmem, ← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply])
    (fun v hv => hV v hv)]
  rw [iU, iV] at key
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hpow : (Q : ℂ) ^ l = (Q : ℂ) ^ k * (Q : ℂ) ^ (-d) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hQ']
    congr 1
    omega
  push_cast at key
  rw [hpow, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ hQ') key

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem rankOne_of_steps : Descent → CellInv → ChainSum → RankOne := by
  intro hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc
  obtain ⟨-, e1⟩ := hD G A K N N' ι h t hfin hle hι hsplit hK hnorm
  obtain ⟨f2, e2⟩ := hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm
  have hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t' := fun a => by
    rw [← hconj a]; group
  have key := hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex
    (by
      intro v hv a
      have := hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)
      show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])
    (by
      intro u hu a
      have := hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u)
        (fun w hw => by simpa using hnorm u⁻¹ w hw)
      show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, one_mul, mul_assoc])
    f2
  rw [e1, e2, ← key]
  refine finsum_congr fun y => ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩ := hdc y.out
  have hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out := by
    rw [← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]
  rw [hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem cellInv_holds : CellInv := by
  classical
  intro G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'
  unfold cellSum
  rw [← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by
    rw [← MulAction.Quotient.mk_smul_out]
    exact QuotientGroup.mk_out_eq_mul K _
  rw [MulAction.toPerm_apply, hk]
  have e : h (k₁ * x.out * k) = h x.out := hh ⟨k₁, hk₁⟩ k _
  rw [e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩
    have : x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹ := by group
    rw [this, e']; group
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩
    rw [e']; group

end GlobalTheory.SatakeWeyl
end
