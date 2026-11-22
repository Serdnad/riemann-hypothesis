import Mathlib

open Matrix

noncomputable section

namespace UpperTheory.Reformulated.B.Qj20

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def inLie (k r : ℕ) (X : Mat k r) : Prop := Xᴴ * Hpk k r + Hpk k r * X = 0

theorem aux4 (n : ℕ) : IsTopologicalRing (Matrix (Fin n) (Fin n) ℂ) := inferInstance

def RdV {n : ℕ} {E : Type*} [inst : NormedAddCommGroup E] [NormedSpace ℂ E] (X : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

def herm {ι : Type*} [inst : Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

theorem aux8 (k r : ℕ) (a : Fin r) : a.val < 2 * r + k + 1 := by omega

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, aux8 k r a⟩

section Operators

variable {n : ℕ} {E : Type*} [inst : NormedAddCommGroup E] [NormedSpace ℂ E]

def Top (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminorOp {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

theorem aux12 : (1 + 1).AtLeastTwo := ⟨by decide⟩

def hpart1 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Zᴴ * H)

def hpart2 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Zᴴ * H)

def EabH (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H (Matrix.single a b 1)) f g + Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

end Operators

def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) := eI k r (Fin.castLE h l)

open scoped Classical in
def AAop {E : Type*} [inst : NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (u : ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E := fun g =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det •
        qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0

private theorem Hpk_herm (k r : ℕ) : (Hpk k r).conjTranspose = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      (s : ℕ) = if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i :=
    ⟨⟨if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i,
      by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs <;> split_ifs <;> first | omega | simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ s := fun h => hb (Fin.ext h)
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hs <;> split_ifs <;> first | omega | rfl
    rw [h0, zero_mul]
  · simp

private theorem Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_right_inv (Hpk_sq k r)

private theorem inLie_hpart1 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [inLie, hpart1, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, ← smul_add]
  simp

private theorem inLie_hpart2 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  simp only [inLie, hpart2, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, neg_smul,
    add_comm (Hpk k r * Z), neg_add_cancel]

private theorem contDiff_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  contDiff_apply_apply ℝ ℂ i j

private theorem contDiff_cst {n : ℕ} (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  contDiff_const

private theorem contDiff_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : Matrix (Fin n) (Fin n) ℂ => herm H (g.mulVec v) w) := by
  simp only [herm, dotProduct, Matrix.mulVec]
  refine ContDiff.sum fun a _ => contDiff_const.mul ?_
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact ContDiff.sum fun c _ => (contDiff_entry b c).mul contDiff_const

private theorem contDiff_det {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ → Fin m → Fin m → ℂ)
    (hA : ∀ a l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => A g a l)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (Matrix.of (A g)).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun l _ => hA _ _)

private theorem closed_sum {X E ι : Type*} [AddCommMonoid E] (P : (X → E) → Prop)
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x) (h0 : P fun _ => 0)
    (s : Finset ι) (F : ι → X → E) (hF : ∀ i, P (F i)) : P fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ (hF a) ih

private theorem closed_foldr {Y : Type*} (P : Y → Prop) (f : Y) (hf : P f) (L : List (Y → Y))
    (hL : ∀ T ∈ L, ∀ y, P y → P (T y)) : P (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact hL T (List.mem_cons_self ..) _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

theorem aa_closed {k r : ℕ} {E : Type*} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E]
    (P : (Mat k r → E) → Prop)
    (hR : ∀ X f, inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x)
    (hmul : ∀ φ : Mat k r → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ f, P f → P fun x => φ x • f x)
    (h0 : P fun _ => 0) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (AAop k r m hm u f) := by
  have hc : ∀ (c : ℂ) (f : Mat k r → E), P f → P fun x => c • f x :=
    fun c f hf => hmul (fun _ => c) (contDiff_cst c) f hf
  have hE : ∀ a b (f : Mat k r → E), P f →
      P (EabH (Hpk k r) a b f) := fun a b f hf =>
    hadd _ _ (hR _ f (inLie_hpart1 k r _) hf)
      (hc _ _ (hR _ f (inLie_hpart2 k r _) hf))
  have hT : ∀ (v : ℂ) a b (f : Mat k r → E), P f →
      P (Top (EabH (Hpk k r)) v a b f) := by
    intro v a b f hf
    refine hadd (fun g => if a = b then v • f g else 0) _ ?_ (hE a b f hf)
    by_cases hab : a = b
    · simp only [if_pos hab]
      exact hc v f hf
    · simp only [if_neg hab]
      exact h0
  have hQ : ∀ (a b : Fin m → Fin (2 * r + k + 1)),
      P (qminorOp (EabH (Hpk k r)) a b u f) := by
    intro a b
    unfold qminorOp
    rw [Finset.sum_fn]
    refine closed_sum P hadd h0 _ _ fun σ => ?_
    refine hc _ _ (closed_foldr P f hf _ fun T hTm => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hTm
    exact hT _ _ _
  unfold AAop
  refine closed_sum P hadd h0 _ _ fun c => ?_
  by_cases hcm : StrictMono c
  · simp only [if_pos hcm]
    exact hmul _ (contDiff_det _ fun a l => contDiff_herm _ _ _) _
      (hQ _ c)
  · simp only [if_neg hcm]
    exact h0

end UpperTheory.Reformulated.B.Qj20
