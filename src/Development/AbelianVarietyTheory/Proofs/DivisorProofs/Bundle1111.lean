module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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

noncomputable section

namespace GlobalTheory.DoubleCosetDivisors

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem zpow_mem_of_val_one {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (k : ℤ) : u ^ k ∈ O := by
  apply hO
  rw [map_zpow₀, hu, _root_.one_zpow]

theorem diag_mem {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (e : Fin n → ℤ) :
    ∃ U ∈ Formalism.UG.GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => u ^ e i) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  let Uo : GL (Fin n) O :=
    { val := Matrix.diagonal (fun i => ⟨u ^ e i, zpow_mem_of_val_one hO hu (e i)⟩)
      inv := Matrix.diagonal (fun i => ⟨u ^ (-e i), zpow_mem_of_val_one hO hu (-e i)⟩)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [mul_inv_cancel₀ (zpow_ne_zero _ hu0)]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [inv_mul_cancel₀ (zpow_ne_zero _ hu0)] }
  refine ⟨Formalism.UG.bc (n := Fin n) O.subtype Uo, ⟨Uo, rfl⟩, ?_⟩
  ext i j
  simp [Formalism.UG.bc, Uo, Matrix.diagonal_apply]

theorem sameDiv_doubleCoset {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O) {d : List ℤ} {g s : GL (Fin n) L}
    (hg : GlobalTheory.SphPar.HasDiv O d g) (hs : GlobalTheory.SphPar.HasDiv O d s) :
    ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)),
      g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) := by
  obtain ⟨ϖ, hϖ, a1, ha1, b1, hb1, hg⟩ := hg
  obtain ⟨ϖ', hϖ', a2, ha2, b2, hb2, hs⟩ := hs
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  have h0' : ϖ' ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact hne hϖ'.symm
  have hu : (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ / ϖ') = 1 := by
    rw [map_div₀, hϖ, hϖ', div_self hne]
  obtain ⟨U, hU, hUe⟩ := diag_mem hO hu (fun i : Fin n => d.getD i 0)
  have hD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) =
      (U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) := by
    rw [hUe, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← mul_zpow, div_mul_cancel₀ _ h0']
  refine ⟨⟨a1 * U * a2⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hU) (Subgroup.inv_mem _ ha2)⟩,
    ⟨b2⁻¹ * b1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) hb1⟩, ?_⟩
  apply Units.ext
  have e1 : ((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul a2
  have e2 : (b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv b2
  simp only [Units.val_mul]
  rw [hg, hs, hD]
  calc (a1 : Matrix (Fin n) (Fin n) L) * ((U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0)) * (b1 : Matrix (Fin n) (Fin n) L)
      = (a1 : Matrix (Fin n) (Fin n) L) * (U : Matrix (Fin n) (Fin n) L) * (((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L))
          * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) * ((b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * (b1 : Matrix (Fin n) (Fin n) L) := by
        rw [e1, e2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {O : Subring L}, (∀ (x : L), (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ (1 : WithZero (Multiplicative ℤ)) → x ∈ O) → ∀ {d : List ℤ} {g s : GL (Fin n) L}, GlobalTheory.SphPar.HasDiv O d g → GlobalTheory.SphPar.HasDiv O d s → ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)), g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) :=
  fun hO _ _ _ hg hs => sameDiv_doubleCoset hO hg hs

end GlobalTheory.DoubleCosetDivisors
end
end

section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.DualDivU

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem exists_glint (O : Subring L) (A B : Matrix (Fin n) (Fin n) L) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∃ U ∈ GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = A := by
  let A0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have eA : RingHom.mapMatrix (m := Fin n) O.subtype A0 = A := by ext i j; rfl
  have eB : RingHom.mapMatrix (m := Fin n) O.subtype B0 = B := by ext i j; rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have h1 : A0 * B0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hAB])
  have h2 : B0 * A0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hBA])
  exact ⟨bc (n := Fin n) O.subtype ⟨A0, B0, h1, h2⟩, ⟨_, rfl⟩, eA⟩

theorem entry_mem (O : Subring L) {U : GL (Fin n) L} (hU : U ∈ GLint (Fin n) O) (i j : Fin n) :
    (U : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨U0, rfl⟩ := hU
  exact ((U0 : Matrix (Fin n) (Fin n) O) i j).2

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if j = i.rev then 1 else 0 := by
  unfold antiJ
  congr 1
  have := i.2
  have := j.2
  simp only [Fin.ext_iff, Fin.val_rev, eq_iff_iff]
  omega

theorem antiJ_mul (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, antiJ_apply]

theorem mul_antiJ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  have : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff, eq_comm, Fin.rev_eq_iff]
  simp [Matrix.mul_apply, antiJ_apply, this]

theorem antiJ_sq : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul, antiJ_apply, Fin.rev_rev, Matrix.one_apply]
  simp [eq_comm]

theorem dual_mul (σ : L →+* L) (A B : Matrix (Fin n) (Fin n) L) (h : A * B = 1) :
    antiJ L n * cT σ B * antiJ L n * (antiJ L n * cT σ A * antiJ L n) = 1 := by
  calc _ = antiJ L n * cT σ B * (antiJ L n * antiJ L n) * cT σ A * antiJ L n := by simp only [Matrix.mul_assoc]
    _ = antiJ L n * cT σ (A * B) * antiJ L n := by
      rw [antiJ_sq, Matrix.mul_one, cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, cT_one, Matrix.mul_one, antiJ_sq]

theorem getD_dualLab (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i 0 = -(d.getD i.rev 0) := by
  subst hd
  have hi := i.2
  have h1 : (i : ℕ) < (dualLab d).length := by simp [dualLab]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

end Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem exists_dual (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) (intL L)) :
    ∃ U ∈ GLint (Fin n) (intL L), (U : Matrix (Fin n) (Fin n) L) =
      antiJ L n * cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n := by
  have key : ∀ b ∈ GLint (Fin n) (intL L), ∀ i j,
      (antiJ L n * cT σ ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n) i j ∈ intL L := by
    intro b hb i j
    rw [mul_antiJ, antiJ_mul]
    have := entry_mem (intL L) hb j.rev i.rev
    show Valued.v (σ _) ≤ 1
    rw [hσ]
    exact this
  exact exists_glint (intL L) _ (antiJ L n * cT σ (a : Matrix (Fin n) (Fin n) L) * antiJ L n)
    (dual_mul σ _ _ (Units.mul_inv a)) (dual_mul σ _ _ (Units.inv_mul a)) (key _ (inv_mem ha)) (key _ ha)

theorem hasDiv_dualLab : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  intro L _ _ σ n d g hσ hd hg ⟨ϖ, hϖ, a, ha, b, hb, hab⟩
  obtain ⟨a', ha', ea⟩ := exists_dual σ hσ ha
  obtain ⟨b', hb', eb⟩ := exists_dual σ hσ hb
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨σ ϖ, by rw [hσ, hϖ], a', ha', b', hb', ?_⟩
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n := hg
  have eD : Matrix.diagonal (fun i : Fin n => σ ϖ ^ (dualLab d).getD i 0) =
      antiJ L n * cT σ (Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) * antiJ L n := by
    ext i j
    rw [mul_antiJ, antiJ_mul]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.rev_inj]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [getD_dualLab d hd, map_zpow₀]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hDD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (g : Matrix (Fin n) (Fin n) L) * (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    rw [hab]
    calc _ = (a : Matrix (Fin n) (Fin n) L) * (Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
        ((b : Matrix (Fin n) (Fin n) L) * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) *
        ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hDD, Matrix.mul_one, Units.mul_inv]
  have h1 := dual_mul σ _ _ hinv
  have h2 : antiJ L n * cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hg', antiJ_sq]
  have h3 : (g : Matrix (Fin n) (Fin n) L) = antiJ L n * cT σ (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
      antiJ L n := by
    conv_rhs => rw [← Matrix.mul_one (_ * antiJ L n), ← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h3, ea, eb, eD, cT_mul, cT_mul]
  have hJ : ∀ X : Matrix (Fin n) (Fin n) L, antiJ L n * (antiJ L n * X) = X := fun X => by
    rw [← Matrix.mul_assoc, antiJ_sq, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hJ]

end GlobalTheory.DualDivU
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LaurentNoeth

def lmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : S →+* LaurentPolynomial S).comp f) (laurentVarUnit S)

theorem laurentVarUnit_zpow (S : Type) [CommRing S] (n : ℤ) :
    ((laurentVarUnit S ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]; rfl
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl

theorem laurentMap_C_mul_T {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (n : ℤ) :
    lmap f (LaurentPolynomial.C a * LaurentPolynomial.T n) = LaurentPolynomial.C (f a) * LaurentPolynomial.T n := by
  simp [lmap, laurentVarUnit_zpow]

theorem lext {R : Type} [CommRing R] {p p' : LaurentPolynomial R} (h : ∀ n, p.coeff n = p'.coeff n) : p = p' :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem lmap_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (lmap f p).coeff n = f (p.coeff n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      map_add]
  | C_mul_T k a =>
    rw [laurentMap_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

theorem lmap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lmap f) := by
  intro p p' h
  refine lext fun n => ?_
  apply hf
  rw [← lmap_apply, ← lmap_apply, h]

theorem lmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    lmap (g.comp f) = (lmap g).comp (lmap f) := by
  refine RingHom.ext fun p => lext fun n => ?_
  rw [RingHom.comp_apply, lmap_apply, lmap_apply, lmap_apply, RingHom.comp_apply]

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (F : R →+* S) (G : S →+* T) :
    spMap (G.comp F) = spMap G ≫ spMap F := by
  show sch.map (Spec.map (CommRingCat.ofHom (G.comp F))) = sch.map (Spec.map (CommRingCat.ofHom G)) ≫ sch.map (Spec.map (CommRingCat.ofHom F))
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

attribute [local instance] Classical.propDecidable

variable {A : Type} [CommRing A]

def sub (u : A) (s : Finset A) : Subalgebra ℤ A := Algebra.adjoin ℤ (↑(insert u s) : Set A)

theorem sub_mono (u : A) : Monotone (sub u) := fun _ _ h =>
  Algebra.adjoin_mono (Finset.coe_subset.2 (Finset.insert_subset_insert u h))

theorem mem_sub (u : A) (s : Finset A) {a : A} (ha : a ∈ insert u s) : a ∈ sub u s :=
  Algebra.subset_adjoin (Finset.mem_coe.2 ha)

theorem lmap_val_comp (u : A) {s t : Finset A} (hst : s ≤ t) :
    (lmap (sub u t).val.toRingHom).comp (lmap (Subalgebra.inclusion (sub_mono u hst)).toRingHom) =
      lmap (sub u s).val.toRingHom := by
  rw [← lmap_comp]; rfl

def diag (u : A) : Finset A ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (LaurentPolynomial (sub u s))
  map {s t} h := CommRingCat.ofHom (lmap (Subalgebra.inclusion (sub_mono u (leOfHom h))).toRingHom)
  map_id s := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply, lmap_apply]; rfl)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, lmap_apply]; rfl)

def cocone (u : A) : Cocone (diag u) where
  pt := CommRingCat.of (LaurentPolynomial A)
  ι := { app := fun s => CommRingCat.ofHom (lmap (sub u s).val.toRingHom)
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact CommRingCat.hom_ext (lmap_val_comp u (leOfHom h)) }

theorem exists_preimage (u : A) (x : LaurentPolynomial A) : ∃ s y, lmap (sub u s).val.toRingHom y = x := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s, y, rfl⟩ := hp
    obtain ⟨t, z, rfl⟩ := hq
    refine ⟨s ∪ t, lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_left)).toRingHom y +
      lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_right)).toRingHom z, ?_⟩
    rw [map_add (f := _), ← RingHom.comp_apply, ← RingHom.comp_apply, ← lmap_comp, ← lmap_comp]
    rfl
  | C_mul_T k a =>
    refine ⟨{a}, LaurentPolynomial.C ⟨a, mem_sub u _ (by simp)⟩ * LaurentPolynomial.T k, ?_⟩
    rw [laurentMap_C_mul_T]
    rfl

theorem cocone_isColimit (u : A) : Nonempty (IsColimit (cocone u)) := by
  haveI : ReflectsColimitsOfShape (Finset A) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change LaurentPolynomial A at x
    obtain ⟨s, y, hy⟩ := exists_preimage u x
    exact ⟨s, y, hy.symm⟩
  · intro s t xs xt h
    refine ⟨s ∪ t, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
    apply lmap_injective (sub u (s ∪ t)).val.toRingHom (fun a b hab => Subtype.ext hab)
    · change (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xs = (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xt
      rw [← lmap_comp, ← lmap_comp]
      exact h

theorem sub_fg (u : A) (s : Finset A) : (sub u s).FG := ⟨insert u s, rfl⟩

end GlobalTheory.EtC.LaurentNoeth


open GlobalTheory.EtC.LaurentNoeth in
theorem GlobalTheory.EtC.laurent_vanishing_of_noetherian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  classical
  intro q _ hN A _ hA hq n i hn
  refine ⟨fun x y => ?_⟩
  suffices key : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 by rw [key x, key y]
  intro x
  set u : A := ((hq.unit⁻¹ : Aˣ) : A)
  obtain ⟨hc⟩ := cocone_isColimit u
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    have := hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A); simpa using this
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag u) (cocone u) hc n i).1 x hqL
  haveI : Algebra.FiniteType ℤ (sub u j) := (Subalgebra.fg_iff_finiteType _).1 (sub_fg u j)
  haveI : IsNoetherianRing (sub u j) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨C, _, hCn, hCsh, f, g, hfg⟩ := GlobalTheory.T.exists_noetherian_sh_factorization (sub u j) A hA (sub u j).val.toRingHom
  haveI := hCn
  have hqS : IsUnit (q : sub u j) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨u, mem_sub u j (Finset.mem_insert_self u j)⟩, ?_⟩
    apply Subtype.ext
    simp [u]
  have hqC : IsUnit (q : C) := by have := hqS.map f; simpa using this
  haveI := hN C hCsh hqC n i hn
  have e : (cocone u).ι.app j = CommRingCat.ofHom ((lmap g).comp (lmap f)) := by
    rw [← lmap_comp, hfg]; rfl
  rw [← hy, e]
  change pull _ (spMap ((lmap g).comp (lmap f))) _ _ y = 0
  rw [spMap_comp']
  refine (pull_comp (ZMod q) (spMap (lmap g)) (spMap (lmap f)) (tw q i) n y).trans ?_
  have : pull _ (spMap (lmap f)) (tw q i) n y = 0 := Subsingleton.elim _ _
  rw [this, map_zero]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) → (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  first | (exact @GlobalTheory.EtC.hInv_of_filtered_colimit) | (exact GlobalTheory.EtC.hInv_of_filtered_colimit) | (intros; apply GlobalTheory.EtC.hInv_of_filtered_colimit  <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.etale_enlarge_by_uniformiser_roots : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (exact GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (intros; apply GlobalTheory.KeyOriginEnlarge.etale_enlarge  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normChartLineBundle_baseChange_field_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ → NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A) (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  first | exact @GlobalTheory.ProjField.normChart_baseChange | exact GlobalTheory.ProjField.normChart_baseChange | (intros; apply GlobalTheory.ProjField.normChart_baseChange <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ d : ℤ, ∃ N : ℕ, ∀ a b : ℕ, N ≤ a + b → (a : ℤ) - b = d → ∀ j : ℕ, ¬ NV A (mix A L a b) (j + 1) := by
  first | exact @GlobalTheory.AmpleGen.exists_not_NV_mix | exact GlobalTheory.AmpleGen.exists_not_NV_mix | (intros; apply GlobalTheory.AmpleGen.exists_not_NV_mix <;> assumption)
end
