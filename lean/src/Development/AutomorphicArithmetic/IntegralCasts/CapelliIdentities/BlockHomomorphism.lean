import Mathlib

noncomputable section

namespace UpperTheory.Reformulated.B.BlockHomomorphism

open Matrix

def IsSmooth {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [TopologicalSpace G]
    (ρ : Representation k G V) : Prop :=
  ∀ v, IsOpen {g : G | ρ g v = v}

def glCongr (k : Type) [inst : Field k] {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k :=
  Units.map (reindexAlgEquiv k k (finCongr h)).toMonoidHom

theorem aux3 (k : Type) [inst : Field k] (n r : ℕ) :
    fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (1 : Matrix (Fin r) (Fin r) k) = 1 := by
  rw [← fromBlocks_one]

theorem aux4 (k : Type) [inst : Field k] (n r : ℕ) (A B : Matrix (Fin n) (Fin n) k) :
    fromBlocks (A * B) 0 0 (1 : Matrix (Fin r) (Fin r) k) = fromBlocks A 0 0 1 * fromBlocks B 0 0 1 := by
  rw [fromBlocks_multiply]
  simp

def blkHom (k : Type) [inst : Field k] (n r : ℕ) :
    Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k where
  toFun A := fromBlocks A 0 0 1
  map_one' := aux3 k n r
  map_mul' := aux4 k n r

def blkGL (k : Type) [inst : Field k] (n r : ℕ) : GL (Fin n) k →* GL (Fin (n + r)) k :=
  Units.map ((reindexAlgEquiv k k finSumFinEquiv).toMonoidHom.comp (blkHom k n r))

def blkAt (k : Type) [inst : Field k] (n N : ℕ) (h : n ≤ N) : GL (Fin n) k →* GL (Fin N) k :=
  (glCongr k (Nat.add_sub_cancel' h)).comp (blkGL k n (N - n))

def FixK {k : Type} [inst : Field k] {m N : ℕ} (h : m + 1 ≤ N) {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin (m + 1)) k)) (v : V) : Prop :=
  ∀ g ∈ K, π (blkAt k (m + 1) N h g) v = v

theorem aux9 {m N : ℕ} {h : m + 2 ≤ N} : ¬m + 1 ≤ N → False := by omega

private theorem continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    unfold blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (glCongr k e) := by
    intro a b e
    unfold glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_fixK {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (v w : V) :
    ∃ K : Subgroup (GL (Fin (m + 1)) k), IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
      FixK (by omega : m + 1 ≤ N) π K v ∧ FixK (by omega : m + 1 ≤ N) π K w := by
  have hle : m + 1 ≤ N := by omega
  refine ⟨(fixer π v ⊓ fixer π w).comap
    (blkAt k (m + 1) N hle), ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (continuous_blkAt (m + 1) N hle)

end UpperTheory.Reformulated.B.BlockHomomorphism
