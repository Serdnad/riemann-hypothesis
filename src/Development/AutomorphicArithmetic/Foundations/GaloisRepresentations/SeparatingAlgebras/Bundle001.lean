module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

section

open UpperTheory.Gal.Gen

open Classical in
private noncomputable def rho0 (H : Type) [Group H] [Fintype H] : H →* Matrix H H ℤ where
  toFun u := Matrix.of fun h g => if h = u * g then 1 else 0
  map_one' := by
    ext h g
    simp [Matrix.one_apply]
  map_mul' u v := by
    ext h g
    have e : ∀ x, (if h = u * x then (1 : ℤ) else 0) * (if x = v * g then 1 else 0)
        = if x = v * g then (if h = u * x then 1 else 0) else 0 := by
      intro x
      split_ifs <;> simp
    simp only [Matrix.mul_apply, Matrix.of_apply, e, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_assoc]

theorem UpperTheory.Gal.Gen.groupDet_pf :
    UpperTheory.Gal.Gen.TriMat → UpperTheory.Gal.Gen.DetLow → UpperTheory.Gal.Gen.GroupDet := by
  classical
  intro hT hD k _ _ l _ H _ _ hp a ρ ha hrank
  obtain ⟨Q, P, hQP⟩ := hT l H hp H (rho0 H)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix H H k, A = Matrix.of fun h g : H => a (h * g⁻¹) := ⟨_, rfl⟩
  rw [← hAdef] at hrank
  obtain ⟨R, hR⟩ : ∃ R : H → Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) ℤ,
      R = fun u => Q * rho0 H u * P := ⟨_, rfl⟩
  have hm : ∀ u i j, ∃ m : ℤ, j ≤ i → R u i j - (if i = j then 1 else 0) = (l : ℤ) * m := by
    intro u i j
    by_cases h : j ≤ i
    · obtain ⟨m, hm⟩ := hQP u i j h
      exact ⟨m, fun _ => by rw [hR]; exact hm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hm
  have hAsum : A = ∑ u, a u • (rho0 H u).map (Int.castRingHom k) := by
    ext h g
    have e : ∀ u : H, h = u * g ↔ u = h * g⁻¹ := fun u => by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp [hAdef, Matrix.sum_apply, rho0, e]
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      A' = Q.map (Int.castRingHom k) * A * P.map (Int.castRingHom k) := ⟨_, rfl⟩
  have hA'sum : A' = ∑ u, a u • (R u).map (Int.castRingHom k) := by
    rw [hA'def, hAsum, hR]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]
  have hA' : ∀ i j, A' i j = ∑ u, a u * ((R u i j : ℤ) : k) := by
    intro i j
    rw [hA'sum]
    simp [Matrix.sum_apply]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      B = Matrix.of fun i j => - ∑ u, a u * ((m u i j : ℤ) : k) := ⟨_, rfl⟩
  have hTe : ∀ i j, j ≤ i → (A' + (l : k) • B) i j = (∑ u, a u) * (if i = j then 1 else 0) := by
    intro i j hij
    have e : ∀ u, ((R u i j : ℤ) : k) = (if i = j then 1 else 0) + (l : k) * ((m u i j : ℤ) : k) := by
      intro u
      have := hm u i j hij
      have h2 : R u i j = (if i = j then 1 else 0) + (l : ℤ) * m u i j := by linarith
      rw [h2]
      push_cast
      rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA', hB, Matrix.of_apply, e,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    have : ∀ u, a u * ((l : k) * ((m u i j : ℤ) : k)) = (l : k) * (a u * ((m u i j : ℤ) : k)) :=
      fun u => by ring
    simp only [this]
    simp
  have hdet : (A' + (l : k) • B).det = (∑ u, a u) ^ Fintype.card H := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hTe]
    · intro i j hij
      have hji : j < i := hij
      rw [hTe i j hji.le, if_neg hji.ne', mul_zero]
  have hnA : ∀ i j, ‖A' i j‖ ≤ 1 := by
    intro i j
    rw [hA']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnB : ∀ i j, ‖B i j‖ ≤ 1 := by
    intro i j
    rw [hB, Matrix.of_apply, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnl : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hr : A'.rank ≤ ρ := by
    rw [hA'def]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrank)
  have := hD k (Fintype.card H) A' B (l : k) ρ hnA hnB hnl hr
  rw [hdet, norm_pow] at this
  exact this
end

section

open UpperTheory.Gal.Gen

private lemma repr_sum_mul {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X]
    (b : Module.Basis ι k (X → k)) (v : X → k) (i : ι) :
    ∑ x, b.repr (Pi.single x 1) i * v x = b.repr v i := by
  have hv : v = ∑ x, v x • (Pi.single x 1 : X → k) := by
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]

  simp [map_sum, Finsupp.finsetSum_apply, mul_comm]

private lemma conj_apply {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X] [Fintype ι]
    (b : Module.Basis ι k (X → k)) (M : Matrix X X k) (i j : ι) :
    ((Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix ι X k) * M *
      (Matrix.of fun x j => b j x : Matrix X ι k)) i j = b.repr (M.mulVec (b j)) i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← repr_sum_mul b]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem UpperTheory.Gal.Gen.triMat_pf :
    UpperTheory.Gal.Gen.Flag → UpperTheory.Gal.Gen.TriMat := by
  intro hF l _ H _ hH X _ _ ρ
  let ρ' : Representation (ZMod l) H (X → ZMod l) :=
    ((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp
      (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)
  have hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v := by
    intro h v
    rfl
  obtain ⟨b₀, hb₀⟩ := hF l H hH (X → ZMod l) ρ'
  have hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X :=
    Module.finrank_fintype_fun_eq_card _
  let e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X) := finCongr hcard
  let b := b₀.reindex e
  have hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0 := by
    intro h i j hij
    have := hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)
    simpa [b] using this
  let Q : Matrix (Fin (Fintype.card X)) X ℤ := fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)
  let P : Matrix X (Fin (Fintype.card X)) ℤ := fun x j => ((b j x).val : ℤ)
  refine ⟨Q, P, fun h i j hij => ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1
  have hQ : Q.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix _ X (ZMod l)) := by
    ext i x
    change ((((b.repr (Pi.single x 1) i).val : ℤ)) : ZMod l) = b.repr (Pi.single x 1) i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hP : P.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun x j => b j x : Matrix X _ (ZMod l)) := by
    ext x j
    change ((((b j x).val : ℤ)) : ZMod l) = b j x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i := by
    have h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) =
        ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j := rfl
    rw [h1, Matrix.map_mul, Matrix.map_mul, hQ, hP, conj_apply, hρ']
  have hd := hb h i j hij
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply] at hd
  rw [Int.cast_sub, hc, hd]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij', Ne.symm hij']
end

section

noncomputable section

namespace UpperTheory.Gal.Gen

private lemma det_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) k) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  classical
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)

private lemma det_zero_of_card {k : Type} [Field k] {N ρ : ℕ}
    (A M : Matrix (Fin N) (Fin N) k) (s : Finset (Fin N)) (hr : A.rank ≤ ρ) (hs : ρ < s.card)
    (hM : ∀ i ∈ s, M i = A i) : M.det = 0 := by
  classical
  by_contra hne
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hne
  have heq : (fun i : s => A i) = (fun i => M i) ∘ (fun i : s => (i : Fin N)) := by
    funext i
    exact (hM i i.2).symm
  have hli' : LinearIndependent k (fun i : s => A i) := by
    rw [heq]
    exact hli.comp _ Subtype.val_injective
  have hle : Module.finrank k (Submodule.span k (Set.range (fun i : s => A i))) ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  rw [finrank_span_eq_card hli', Fintype.card_coe] at hle
  omega

private theorem det_add_smul_eq_sum_powerset_pow_card_mul_det {k : Type} [Field k] {N : ℕ} (A B : Matrix (Fin N) (Fin N) k)
    (c : k) :
    (A + c • B).det = ∑ t ∈ (Finset.univ : Finset (Fin N)).powerset,
      c ^ t.card * (Matrix.of fun r j => if r ∈ t then B r j else A r j).det := by
  classical
  rw [← Matrix.det_transpose]
  simp_rw [← Matrix.det_transpose (Matrix.of _)]
  simp only [Matrix.det_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [add_comm (A _ _)]
  rw [Finset.prod_add, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter,
    Finset.prod_mul_distrib, Finset.prod_const, mul_assoc, mul_smul_comm]

theorem detLow_pf : DetLow := by
  intro k _ _ N A B c ρ hA hB hc hr
  classical
  rw [det_add_smul_eq_sum_powerset_pow_card_mul_det]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t _ => ?_
  rw [norm_mul, norm_pow]
  by_cases ht : N - ρ ≤ t.card
  · have h1 := det_norm_le_one (Matrix.of fun r j => if r ∈ t then B r j else A r j) (by
      intro i j
      simp only [Matrix.of_apply]
      split_ifs
      · exact hB i j
      · exact hA i j)
    calc ‖c‖ ^ t.card * ‖(Matrix.of fun r j => if r ∈ t then B r j else A r j).det‖
        ≤ ‖c‖ ^ t.card * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ‖c‖ ^ (N - ρ) := by
        rw [mul_one]
        exact pow_le_pow_of_le_one (norm_nonneg _) hc ht
  · have h0 : (Matrix.of fun r j => if r ∈ t then B r j else A r j).det = 0 := by
      refine det_zero_of_card A _ tᶜ hr ?_ ?_
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · intro i hi
        funext j
        simp only [Matrix.of_apply, if_neg (Finset.mem_compl.mp hi)]
    rw [h0, norm_zero, mul_zero]
    positivity

end UpperTheory.Gal.Gen

end
end

section

namespace UpperTheory.Gal.Gen

theorem codim_pf : Codim := by
  intro k V M _ _ _ _ _ _ Ψ A B _ h
  let f : V →ₗ[k] M ⧸ A := A.mkQ ∘ₗ Ψ
  have hker : LinearMap.ker f = A.comap Ψ := by
    ext v
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f ≤ B.map A.mkQ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h v)
    refine ⟨b, hb, ?_⟩
    have hz : A.mkQ a = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ha
    simp only [f, LinearMap.comp_apply, ← hab, map_add (f := _), hz, zero_add]
  haveI : FiniteDimensional k (B.map A.mkQ) :=
    Module.Finite.map B A.mkQ
  have h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B :=
    Submodule.finrank_map_le A.mkQ B
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h3
  omega

end UpperTheory.Gal.Gen
end

section

namespace UpperTheory.Gal.Gen

theorem fixVec_pf : FixVec := by
  intro l _ H _ hH V _ _ _ ρ U hU hne
  classical
  let act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U) :=
    fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)
  have act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v) := fun h v => rfl
  letI : MulAction H (V ⧸ U) :=
    { smul := fun h x => act h x
      one_smul := by
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act 1 (U.mkQ v) = U.mkQ v
        rw [act_mk]
        simp
      mul_smul := by
        intro g h x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))
        rw [act_mk, act_mk, act_mk]
        simp }
  have smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x := fun h x => rfl
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : l ∣ Nat.card (V ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]
    exact dvd_pow_self l Module.finrank_pos.ne'
  have h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U) := by
    intro h
    rw [smul_def, map_zero]
  obtain ⟨x, hx, hx0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx0
    rw [eq_comm]
    simpa using hv
  · intro h
    have hfix := hx h
    rw [smul_def, act_mk] at hfix
    exact (Submodule.Quotient.eq U).1 hfix

end UpperTheory.Gal.Gen
end
