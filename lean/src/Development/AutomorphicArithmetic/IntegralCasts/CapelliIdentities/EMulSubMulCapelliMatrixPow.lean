import Mathlib

namespace UpperTheory.Reformulated.B.Qk36

noncomputable section

@[reducible] def gl (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

@[reducible] def U (n : ℕ) : Type :=
  @UniversalEnvelopingAlgebra ℂ (gl n) _ LieRing.ofAssociativeRing _

def E {n : ℕ} (a : Fin n × Fin n) : gl n := Matrix.single a.1 a.2 1

def e {n : ℕ} (a : Fin n × Fin n) : U n :=
  (@UniversalEnvelopingAlgebra.ι ℂ (gl n) _ LieRing.ofAssociativeRing _) (E a)

def capelliMatrix {n : ℕ} : Matrix (Fin n) (Fin n) (U n) := fun i j => e (i, j)

/-- A matrix-unit commutator identity for the entries of a matrix extends to all its powers. -/
theorem commutator_matrix_pow {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (x : R) (a b : ι)
    (h : ∀ c d, x * M c d - M c d * x
      = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : Nat) (c d : ι) :
    x * (M ^ k) c d - (M ^ k) c d * x
      = (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  let D := Matrix.diagonal (fun _ : ι => x) - Matrix.single b a (1 : R)
  have entry (N : Matrix ι ι R) (i j : ι) :
      (D * N) i j = (N * D) i j ↔
        x * N i j - N i j * x = (if b = i then N a j else 0) - (if j = a then N i b else 0) := by
    simp only [D, sub_mul, mul_sub, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have leftEntry : (Matrix.single b a (1 : R) * N) i j = if b = i then N a j else 0 := by
      by_cases hi : i = b
      · subst i; simp
      · simp [hi, Ne.symm hi]
    have rightEntry : (N * Matrix.single b a (1 : R)) i j = if j = a then N i b else 0 := by
      by_cases hj : j = a
      · subst j; simp
      · simp [hj]
    rw [leftEntry, rightEntry, sub_eq_sub_iff_add_eq_add, sub_eq_sub_iff_add_eq_add]
    simp only [add_comm]
  have comm : Commute D M := Matrix.ext fun i j => (entry M i j).2 (h i j)
  exact (entry (M ^ k) c d).1 (congrArg (fun A : Matrix ι ι R => A c d) (comm.pow_right k).eq)

private theorem E_comm {n : Nat} (a b c d : Fin n) :
    E (a, b) * E (c, d)
        - E (c, d) * E (a, b)
      = (if b = c then E (a, d) else 0)
        - (if d = a then E (c, b) else 0) := by
  have h : ∀ p q r s : Fin n, E (p, q) * E (r, s)
      = if q = r then E (p, s) else 0 := by
    intro p q r s
    unfold E
    split_ifs with hqr
    · subst hqr
      simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [h, h]

private theorem e_comm {n : Nat} (a b c d : Fin n) :
    e (a, b) * e (c, d)
        - e (c, d) * e (a, b)
      = (if b = c then e (a, d) else 0)
        - (if d = a then e (c, b) else 0) := by
  letI : LieRing (gl n) := LieRing.ofAssociativeRing
  letI : LieRing (U n) := LieRing.ofAssociativeRing
  unfold e
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, E_comm, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _

theorem e_mul_sub_mul_capelliMatrix_pow {n : ℕ} (a b : Fin n) (k : ℕ) (c d : Fin n) :
    e (a, b) * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * e (a, b) =
      (if b = c then (capelliMatrix ^ k) a d else 0) - (if d = a then (capelliMatrix ^ k) c b else 0) :=
  commutator_matrix_pow capelliMatrix _ a b (e_comm a b) k c d

end
end UpperTheory.Reformulated.B.Qk36
