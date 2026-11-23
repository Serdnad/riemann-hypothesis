module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}

noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ

theorem UpperTheory.Reformulated.B.Yha8.main :
    ∀ {n : ℕ} (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ),
      (∀ (a b : Fin n), Q a b ≠ (0 : ℂ) → b ∈ UpperTheory.Reformulated.B.Yha8.blkA j) →
        (∀ (a b : Fin n), S a b ≠ (0 : ℂ) → a ∈ UpperTheory.Reformulated.B.Yha8.blkB j) → Q * S = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro n j Q S hQ hS
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hq : Q a b = 0
  · simp [hq]
  by_cases hs : S b c = 0
  · simp [hs]
  exfalso
  have h1 := hQ a b hq
  have h2 := hS b c hs
  unfold UpperTheory.Reformulated.B.Yha8.blkB at h2
  rw [Finset.mem_compl] at h2
  exact h2 h1
end

section

theorem UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by
  intro m y v h
  have key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : v j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj i, Matrix.one_apply]
  rw [key, Matrix.one_mulVec]
end

section

noncomputable def UpperTheory.Reformulated.B.ProjectionCompact.piK :
    {T κ : Type} →
      [inst : Fintype T] →
        [inst_1 : DecidableEq T] →
          [inst_2 : Fintype κ] → [inst_3 : DecidableEq κ] → (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ :=
  fun {T κ} _ _ _ _ =>
    { toFun := fun M => Matrix.of fun f g => ∏ t, M t (f t) (g t)
      map_one' := by
        ext f g
        simp only [Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
        by_cases h : f = g
        · subst h
          simp
        · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
          rw [if_neg h]
          exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
      map_mul' := fun M N => by
        ext f g
        simp only [Matrix.of_apply, Pi.mul_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun h _ => Finset.prod_mul_distrib }
end

section

theorem UpperTheory.Reformulated.B.PairCases.pair_cases :
    ∀ {a b c d : @Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)},
      @Eq (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) a
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) b))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) c
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) d)) →
        Or
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a c)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b d))
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a d)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b c)) := by
  intro a b c d h
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
  rcases Multiset.cons_eq_cons.mp h with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · exact Or.inl ⟨h1, Multiset.singleton_inj.mp h2⟩
  · exact Or.inr ⟨(Multiset.singleton_eq_cons_iff _ |>.mp h3).1.symm,
      (Multiset.singleton_eq_cons_iff _ |>.mp h2).1⟩
end

section

noncomputable def UpperTheory.Reformulated.B.SpecialLinearTensor.sl :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v :=
  fun {I} _ dI {W} _ _ v f => by
    have prod_update_self (m : (i : I) → W i) (x : W v) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m v x j) =
          ∏ j ∈ Finset.univ.erase v, f j (m j) := by
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have prod_update_ne {i : I} (h : i ≠ v) (m : (j : I) → W j) (x : W i) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m i x j) =
          f i x * ∏ j ∈ (Finset.univ.erase v).erase i, f j (m j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    exact PiTensorProduct.lift
      { toFun := fun m => (∏ j ∈ Finset.univ.erase v, f j (m j)) • m v
        map_update_add' := by
          intro d m i x y
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, smul_add]
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              map_add, add_mul, add_smul]
        map_update_smul' := by
          intro d m i c x
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, RingHom.id_apply]
            exact smul_comm _ _ _
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              RingHom.id_apply, map_smul, smul_eq_mul, mul_assoc, mul_smul] }

theorem UpperTheory.Reformulated.B.SpecialLinearTensor.sl_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.SpecialLinearTensor.sl v f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → W v)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        (∏ i ∈ Finset.univ.erase v, (f i : W i → ℂ) (m i)) • m v := by
  intro I _ _ W _ _ v f m
  rw [UpperTheory.Reformulated.B.SpecialLinearTensor.sl, PiTensorProduct.lift.tprod]
  rfl
end

section

noncomputable def UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev :
    {I : Type} →
      [Fintype I] →
        {W : I → Type} →
          [inst : (i : I) → AddCommGroup (W i)] →
            [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
              ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ :=
    fun {I : Type} [Fintype I] {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
        (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : ((∀ i, W i) →ₘₗ[ℂ] ℂ) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ)
        ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap f)

theorem UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → ℂ)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        ∏ i : I, (f i : W i → ℂ) (m i) := by
  intro I _ _ W _ _ f m
  simp [UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev]
end

section

private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    (v : I) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W v) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x v y j)
      = ∏ j ∈ Finset.univ.erase v, a j (x j) :=
  Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    {v i : I} (h : i ≠ v) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W i) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x i y j)
      = a i y * ∏ j ∈ (Finset.univ.erase v).erase i, a j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
    Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

noncomputable def UpperTheory.Reformulated.B.SpecialLinearMap.slM :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → MultilinearMap (RingHom.id ℂ) W (W v) :=
  fun {I} _ dI {_} _ _ v a =>
    { toFun := fun x => (∏ j ∈ Finset.univ.erase v, a j (x j)) • x v
      map_update_add' := fun {d} x i y z => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self, smul_add]
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_add, add_mul, add_smul]
      map_update_smul' := fun {d} x i c y => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self,
            RingHom.id_apply]
          exact smul_comm _ _ _
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul] }
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe48.DR :
    (R B : Type) → [inst : CommRing R] → [inst_1 : CommRing B] → [Algebra R B] → Type :=
    fun (R B : Type) [CommRing R] [CommRing B] [Algebra R B] ↦ ExteriorAlgebra B Ω[B⁄R]

noncomputable def UpperTheory.Reformulated.B.Qe48.omB :
    (k : Type) →
      [inst : Field k] →
        (K : Type) →
          [inst_1 : Field K] → [inst_2 : Algebra k K] → Subalgebra k K → ℕ → Submodule k (UpperTheory.Reformulated.B.Qe48.DR k K) :=
    fun (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ) ↦
      Submodule.span k
        {y : UpperTheory.Reformulated.B.Qe48.DR k K |
          ∃ b ∈ B,
            ∃ (v : Fin q → K),
              (∀ (j : Fin q), v j ∈ B) ∧
                y =
                  b •
                    (ExteriorAlgebra.ιMulti K q : (Fin q → Ω[K⁄k]) → ExteriorAlgebra K Ω[K⁄k]) fun (j : Fin q) ↦
                      (KaehlerDifferential.D k K : K → Ω[K⁄k]) (v j)}

theorem UpperTheory.Reformulated.B.Qe48.om_mul :
    ∀ {L : Type} [inst : Field L] [inst_1 : Algebra ℂ L] (B : Subalgebra ℂ L) {p q : ℕ} {u w : UpperTheory.Reformulated.B.Qe48.DR ℂ L},
      u ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B p → w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B q → u * w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B (p + q) := by
  intro L _ _ B p q u w hu hw
  unfold UpperTheory.Reformulated.B.Qe48.omB at hu hw ⊢
  have h := Submodule.mul_mem_mul hu hw
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨b, hb, v, hv, rfl⟩, _, ⟨c, hc, v', hv', rfl⟩, rfl⟩
  refine ⟨b * c, B.mul_mem hb hc, Fin.append v v', ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hv i
    · rw [Fin.append_right]; exact hv' i
  · show _ * _ = _
    rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
end

section

theorem UpperTheory.exists_invariant_subspace :
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (G ι : Type) [Fintype ι] (K : Set G)
        (σ : G → H →ₗ[ℂ] H) (S : Submodule ℂ H) (E : ι → Module.End ℂ S) (c : G → ι → ι → ℂ),
        (∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S) →
        (∀ g ∈ K, ∀ (i : ι) (v w : S), (w : H) = σ g (v : H) →
          σ g ((E i v : S) : H) = ∑ j, c g i j • ((E j w : S) : H)) →
        ∃ V₀ : Submodule ℂ S,
          (∀ x : S, x ∈ V₀ ↔ ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
            ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T) ∧
          ∀ i, ∀ x ∈ V₀, E i x ∈ V₀ := by
  intro H _ _ G ι _ K σ S E c hS hE
  refine ⟨{ carrier := {x : S | ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
              ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨T₁, f₁, ha, h₁⟩ ⟨T₂, f₂, hb, h₂⟩
    refine ⟨T₁ ⊔ T₂, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h₁ g hg y hy) (h₂ g hg z hz)
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ v hv
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
    exact Submodule.zero_mem _
  · rintro r x ⟨T, f, hx, h⟩
    exact ⟨T, f, T.smul_mem r hx, h⟩
  · rintro i x ⟨T, f, hx, h⟩
    have fU : FiniteDimensional ℂ (T.comap S.subtype) :=
      FiniteDimensional.of_injective (S.subtype.submoduleComap T) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H)) hab)
    have hmem : ∀ (j : ι) (u : S), (u : H) ∈ T →
        ((E j u : S) : H) ∈ ⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k) := fun j u hu =>
      Submodule.mem_iSup_of_mem j ⟨u, hu, rfl⟩
    refine ⟨⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k), inferInstance, hmem i x hx, ?_⟩
    intro g hg v hv
    have hle : (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)) ≤
        (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)).comap (σ g) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hE g hg j u ⟨σ g u, hS g hg u u.2⟩ rfl]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hmem k _ (h g hg u hu))
    exact hle hv
end

section

private theorem UpperTheory.Reformulated.B.Qp2.aux {X : Type} (n : ℕ) :
    ∀ (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V], Module.finrank ℂ V = n →
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn
    by_cases hV : ∀ v ∈ V, v = 0
    · exact ⟨∅, fun v hv _ => hV v hv⟩
    · obtain ⟨w, hw⟩ := not_forall.mp hV
      obtain ⟨hwV, hw0⟩ := Classical.not_imp.mp hw
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
      let U : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
      have hle : U ≤ V := inf_le_left
      have hlt : U < V := by
        refine lt_of_le_of_ne hle ?_
        intro h
        have hwU : w ∈ U := h ▸ hwV
        exact hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)
      haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle
      have hr : Module.finrank ℂ U < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT⟩ := ih _ hr U rfl
      refine ⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩

theorem UpperTheory.Reformulated.B.Qp2.exists_finset_separating :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  intro X V _
  exact UpperTheory.Reformulated.B.Qp2.aux _ V rfl
end

section

theorem UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by
  intro Y E _ φ
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro x hx
  have h0 : x = 0 := by
    apply Subtype.ext
    funext y
    exact (Submodule.mem_iInf _).1 hx y
  rw [h0]
  exact Submodule.zero_mem _
end

section

theorem UpperTheory.finite_span_add_smul :
    ∀ {ι V : Type} [AddCommGroup V] [Module ℂ V] (T : ι → V →ₗ[ℂ] V) (S : Set ι) (a b : V) (z : ℂ),
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i a) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i b) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i (a + z • b)) '' S)) := by
  intro ι V _ _ T S a b z ha hb
  have hle : Submodule.span ℂ ((fun i => T i (a + z • b)) '' S) ≤
      Submodule.span ℂ ((fun i => T i a) '' S) ⊔ Submodule.span ℂ ((fun i => T i b) '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [map_add (f := _), map_smul, SetLike.mem_coe]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.smul_mem _ z (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle
end
