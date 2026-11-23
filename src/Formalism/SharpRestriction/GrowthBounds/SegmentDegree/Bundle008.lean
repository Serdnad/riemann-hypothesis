module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

variable (D : Formalism.BasicNotions.D7) (hV : admB2 D) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem mem_vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  have h := ((hV R ℤ n LZ S).1 P Q).1
  rw [h, WithTop.coe_add]
  exact add_le_add hP hQ

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have h := sDegs_C (R := R) LZ S (lastIdx n) c k hk
  rw [Set.mem_singleton_iff] at h
  subst h
  exact le_rfl

theorem mem_vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using mem_vg_C (R := R) (n := n) S 1
  | succ k ih =>
    have e : (((k + 1 : ℕ) : ℤ) * a : ℤ) = (k : ℤ) * a + a := by push_cast; ring
    rw [e, pow_succ]
    exact mem_vg_mul D hV S ih hP

theorem mem_vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using mem_vg_C (R := R) (n := n) S 1
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mem_vg_mul D hV S (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_X (v : ℤ × Fin n) (he : Even v.1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have hk0 : (0 : ℤ) ≤ k := by
    by_cases hS : v.1 ∈ S
    · have hv : LZ.vec v.1 = true := by simp [LZ, he]
      have h := sDegs_X_vec (R := R) LZ S (lastIdx n) v.1 v.2 hS hv k hk
      have h01 : k = 0 ∨ k = 1 := by simpa using h
      rcases h01 with h | h <;> simp [h]
    · have h := sDegs_X_out (R := R) LZ S (lastIdx n) v hS k hk
      rw [Set.mem_singleton_iff] at h
      simp [h]
  exact WithTop.coe_le_coe.mpr hk0

theorem mem_vg_monom {κ : Type} (s : Finset κ) (v : κ → ℤ × Fin n) (e : κ → ℕ) (he : ∀ i ∈ s, Even (v i).1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
  have h0 : ∀ i ∈ s, (((fun _ => (0 : ℤ)) i : ℤ) : WithTop ℤ) ≤
      valS LZ S ((X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
    intro i hi
    simpa using mem_vg_pow D hV S (mem_vg_X (R := R) S (v i) (he i hi)) (e i)
  simpa using mem_vg_prod D hV S s (fun i => (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) (fun _ => 0) h0

end Kit

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerTimesMonomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat)


omit [NeZero n'] [NeZero r] in
def memMu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ u v

def memPl (O : Type) [CommRing O] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) :
    MvPolynomial (ℤ × Fin r) O :=
  segRen X.F j O r (Psi O (plPart μ) (Ican (plPart μ)))

def memA (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin r) O :=
  X.discPowerTimesMonomial p K O j b * X.memMu O j q.2.2 * X.memPl K O j q.1

def memG (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin K) O :=
  segRen X.F j O K (Psi O (tanPart q.1) q.2.1)

def memM [NeZero K] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => if Even (segE X.F j i) then tanPart μ i.succ 0 else tanPart μ i.castSucc 0) 0

theorem famEl_eq (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    X.famEl p K O j b q = plEmb O r K (X.memA p K O j b q) * nmEmb O r K (X.memG K O j q) := by
  first
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def, plVar, tanVar]
     ring)
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def]
     ring_nf)

end Dat

def RestMemA (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      X.memA p K O j b q.1 ∈ supported O {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
      X.memG K O j q.1 ∈ supported O {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} ∧
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.memA p K O j b q.1)) ∧
        (¬ Even x → lam1S LZ {y | y < x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.memA p K O j b q.1)) ∧
        geR (valS LZ {y | y < x} (X.memA p K O j b q.1)) (X.thc p K j b x)

def RestMemB (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      ∀ mm ∈ (plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1)).support,
        ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.oc p K j x

def RestMemC (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ Pol O (r + K) b

def RestMemD (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ restrictSupport O (X.resSet p K j)

theorem restMem_of_rests (C₀ : ℝ) (hA : RestMemA C₀) (hB : RestMemB C₀) (hC : RestMemC C₀) (hD : RestMemD C₀) :
    RestMem C₀ := by
  intro p n' r K _ _ _ X O _ _ _ hS hX hCLa hCk j b hb q
  have hA' := hA p n' r K X O hS hX hCLa hCk j b hb q
  have hB' := hB p n' r K X O hS hX hCLa hCk j b hb q
  have hC' := hC p n' r K X O hS hX hCLa hCk j b hb q
  have hD' := hD p n' r K X O hS hX hCLa hCk j b hb q
  rw [X.famEl_eq p K O j b q.1]
  simp only [Dat.Mj, XX', Submodule.mem_inf]
  refine ⟨⟨⟨Submodule.subset_span ⟨X.memA p K O j b q.1, X.memG K O j q.1, X.memM K j q.1.1,
    hA'.1, hA'.2.1, hA'.2.2, rfl⟩, ?_⟩, hC'⟩, hD'⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact hB' mm hmm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def ellP (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin r) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin r, MvPolynomial.X (x, c) ^ e (x, Fin.castAdd K c)

def ellN (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin K) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin K, MvPolynomial.X (x, c) ^ e (x, Fin.natAdd r c)

def dS (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)

def dV (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0

def Aw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (nu : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I' : ℤ → Finset (Fin r)) : MvPolynomial (ℤ × Fin r) R :=
  (segRen X.F j R r (Psi R nu I')) ^ (p ^ X.Rj p K j) * X.ellP K R j e * X.DlSeg p K R j

def Gw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I'' : ℤ → Finset (Fin K)) : MvPolynomial (ℤ × Fin K) R :=
  (segRen X.F j R K (Psi R ka I'')) ^ (p ^ X.Rj p K j) * X.ellN K R j e

def Mw [NeZero K] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => ((p ^ X.Rj p K j : ℕ) : ℤ) * (if Even (segE X.F j i) then ka i.succ 0 else ka i.castSucc 0) +
      (X.dV K j e : ℤ)) 0

end Dat

structure WCtx (C₀ : ℝ) (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r)
    (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ)
    (q : (Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ))
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) : Prop where
  hX : X.Hyp p K
  hLa : C₀ ≤ X.CLa
  hk : C₀ ≤ X.Ck
  he : X.IsEll p K j e
  h2 : X.Step2 p K j b
  hq : q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j)
  hI' : IsSt q.1 I'
  hI'' : IsSt q.2 I''

def FrobeniusReductionProduct (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    MvPolynomial.map (IsLocalRing.residue O)
        (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e) =
      plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')

def ProductAllowedLetters (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    X.Aw p K (FF O) j e q.1 I' ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
    X.Gw p K (FF O) j e q.2 I'' ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1}

def ColumnConditionsWithMargin (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) ∧
      (¬ Even x → lam1S LZ {y | y < x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.Aw p K (FF O) j e q.1 I')) ∧
      geR (valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) (X.th p j x)

def ProductOrdersBounded (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ mm ∈ (plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')).support,
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.o p K j x

theorem column_word_reduction_of_four (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (h1 : FrobeniusReductionProduct C₀) (h2 : ProductAllowedLetters C₀)
    (h3 : ColumnConditionsWithMargin C₀) (h4 : ProductOrdersBounded C₀) : ColumnWordReductionLifts C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b e he hs2 q hq I' I'' hI' hI''
  have : Fact p.Prime := ⟨hX.prime⟩
  have hc : WCtx C₀ p n' r K X j b e q I' I'' := ⟨hX, hLa, hk, he, hs2, hq, hI', hI''⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h6 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (X.mg p K j) (X.th p j) (X.o p K j) hX.valid hseg
    (fun x => by unfold Dat.mg; positivity)).2.2.2.2.2
  obtain ⟨P, hP, hPe⟩ := h6 (X.Aw p K (FF O) j e q.1 I') (X.Gw p K (FF O) j e q.2 I'') (X.Mw p K j e q.2)
    (h2 p n' r K X O S j b e q I' I'' hc).1 (h2 p n' r K X O S j b e q I' I'' hc).2
    (h3 p n' r K X O S j b e q I' I'' hc) (h4 p n' r K X O S j b e q I' I'' hc)
  exact ⟨P, hP, hPe.trans (h1 p n' r K X O S j b e q I' I'' hc).symm⟩

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
