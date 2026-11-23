module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle015
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def pq (a : Fin 3) : ZMod 2 := ((w 3 a : ℤ) : ZMod 2)

theorem pw_eq (a b : Fin 3) : pw a b = pq a - pq b := Int.cast_sub _ _

def GrM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (α β : Fin 3 → ZMod 2)
    (M : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, M a b ∈ evp σ (α a - β b)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

namespace Box

structure Gr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (B : Box F 3 R) (σ : R →ₐ[O] R)
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ pq pq (B.r s).mat
  g : ∀ v, GrM σ (π v) pq (B.g v : Matrix (Fin 3) (Fin 3) R)

variable {K : Type} [CommRing K]

structure Ev (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, (B.r s).mat ∈ adp K 0
  g : ∀ v a b, π v a ≠ pq b → (B.g v : Matrix (Fin 3) (Fin 3) K) a b = 0
  stab : ∀ j s, adp K j ≤ (adp K j).comap (B.ad s)

variable {B : Box F 3 K} {π : F.V → Fin 3 → ZMod 2}

def Ev.ad (h : B.Ev π) (j : ZMod 2) : Representation K F.Γ (adp K j) := B.ad.subrepresentation (adp K j) (h.stab j)

@[simp] theorem Ev.ad_apply (h : B.Ev π) (j : ZMod 2) (s : F.Γ) (X : adp K j) :
    ((h.ad j s X : adp K j) : Matrix (Fin 3) (Fin 3) K) = B.ad s X := rfl


variable (B) in
def bp (j : ZMod 2) (v : F.V) : Submodule K (adp K j) := (B.b v).comap (adp K j).subtype

end Box

section CO

variable {O : Type} [CommRing O] [IsLocalRing O] {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C]
  [Algebra O C]

structure SetLift.Gr {p : C' →ₐ[O] C} {B : Box F 3 C} (D : SetLift p B) (σ' : C' →ₐ[O] C')
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ' pq pq (D.r s : Matrix (Fin 3) (Fin 3) C')
  g : ∀ v, GrM σ' (π v) pq (D.g v : Matrix (Fin 3) (Fin 3) C')
  t : ∀ v s, GrM σ' (π v) (π v) (D.t v s : Matrix (Fin 3) (Fin 3) C')

def formp (σ' : C' →ₐ[O] C') (K : Ideal C') (j : ZMod 2) :
    Submodule (ResidueField O) (K →ₗ[O] ResidueField O) where
  carrier := {u | ∀ i, i ≠ j → ∀ y : K, (y : C') ∈ evp σ' i → u y = 0}
  add_mem' h h' i e y hy := by simp [h i e y hy, h' i e y hy]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c u h i e y hy := by simp [h i e y hy]


variable (O) in
def HasObsG {R : Type} [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) (H : Type) [AddCommGroup H]
    [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (σ' : C' →ₐ[O] C'), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ → (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) →
    ∃ ob : formp σ' (RingHom.ker p) j →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u.1 y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

end CO

end UpperTheory.V.Fr
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prod_single {K α : Type} [CommRing K] (d : α → ℤ) (a : α → K) (L : List α) :
    (L.map fun s => AddMonoidAlgebra.single (d s) (a s)).prod =
      AddMonoidAlgebra.single (L.map d).sum (L.map a).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih, AddMonoidAlgebra.single_mul_single, List.map_cons,
      List.map_cons, List.sum_cons, List.prod_cons]

private theorem alg_val {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K)
    [SetLike.GradedMonoid P] (c : C) :
    (algebraMap C (lauSub P) c).1 = AddMonoidAlgebra.single 0 (algebraMap C K c) := by
  rfl

private theorem w_ne_w_of_ne (n : ℕ) {i j : Fin n} (hij : i ≠ j) : w n i ≠ w n j := by
  intro h
  apply hij
  unfold w at h
  split_ifs at h <;> exact Fin.ext (by omega)

theorem UpperTheory.V.Fr.alg_model :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → IsModel O C (vertex h) ρD := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  have key : ∀ (c : C) (y : K), algebraMap C K c = y → ∀ p : lauSub (ρ.part C),
      p.1 = AddMonoidAlgebra.single 0 y → algebraMap C (lauSub (ρ.part C)) c = p := by
    intro c y hcy p hp
    apply Subtype.ext
    rw [alg_val, hp, hcy]
  refine ⟨alg_cont C ρ hc h ρD hr hψ, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [mem_vertex]
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [hr, map_zero]
    have hne : (0 : ℤ) ≠ w n i - w n j := by
      intro h0
      exact w_ne_w_of_ne n hij (by omega)
    exact (Finsupp.single_eq_of_ne hne).symm
  · intro g i
    obtain ⟨c, hc1, hc2⟩ := hc.dg g i
    refine ⟨c, key c _ hc1 _ ?_, hc2⟩
    rw [hr, sub_self]
  · intro v i g
    obtain ⟨χ, hχ, hχψ⟩ := hc.psi
    exact ⟨χ v i g, key _ _ (hχψ v i g) _ (hψ v i g), (hχ v i).2 g⟩
  · intro x hx
    obtain ⟨L, hL, rfl⟩ := hx
    have hmem : (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ ρ.part C 0 :=
      Submodule.subset_span ⟨L, hL, rfl⟩
    obtain ⟨c, hc'⟩ := h.zero _ hmem
    refine ⟨c, key c _ hc' _ ?_⟩
    have e1 : ∀ L' : List (F.G0 × Fin n × Fin n),
        ((L'.map fun s => ρD.r s.1 s.2.1 s.2.2).prod : lauSub (ρ.part C)).1 =
          (L'.map fun s => AddMonoidAlgebra.single (w n s.2.1 - w n s.2.2) (ρ.r s.1 s.2.1 s.2.2)).prod := by
      intro L'
      induction L' with
      | nil => rfl
      | cons s L' ih =>
        rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, hr, List.map_cons, List.prod_cons]
    rw [e1, prod_single (fun s : F.G0 × Fin n × Fin n => w n s.2.1 - w n s.2.2)
      (fun s => ρ.r s.1 s.2.1 s.2.2) L, hL]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj {K : Type} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Mᵀ * Jmat (R := K) n) i j = M j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat]
  simp [Fin.rev_eq_iff]
  simp [eq_comm (a := j), Fin.rev_eq_iff]

private theorem ord3 {K : Type} [CommRing K] (α β γ p₀ q₀ p₁ q₁ p₂ q₂ : K) :
    (!![p₀, 0, 0; (p₀ - 1) * α, 1, 0; (p₀ - q₀) * γ - (1 - q₀) * (α * β), (1 - q₀) * β, q₀] -
        p₀ • (1 : Matrix (Fin 3) (Fin 3) K)) *
      ((!![p₁, 0, 0; (p₁ - 1) * α, 1, 0; (p₁ - q₁) * γ - (1 - q₁) * (α * β), (1 - q₁) * β, q₁] -
        (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (!![p₂, 0, 0; (p₂ - 1) * α, 1, 0; (p₂ - q₂) * γ - (1 - q₂) * (α * β), (1 - q₂) * β, q₂] -
        q₂ • (1 : Matrix (Fin 3) (Fin 3) K))) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

private theorem low_pol {K : Type} [CommRing K] (p q y z a : K) :
    !![q, 0, 0; z, 1, 0; a, y, p] =
      Jmat (R := K) 3 * (!![p, 0, 0; y, 1, 0; a, z, q])ᵀ * Jmat (R := K) 3 := by
  ext i j
  rw [jconj]
  fin_cases i <;> fin_cases j <;> rfl

private theorem low_mul {K : Type} [CommRing K] (p q y z a p' q' y' z' a' : K) :
    !![p * p', 0, 0; y * p' + y', 1, 0; a * p' + z * y' + q * a', z + q * z', q * q'] =
      !![p, 0, 0; y, 1, 0; a, z, q] * !![p', 0, 0; y', 1, 0; a', z', q'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem low_diag {K : Type} [CommRing K] (p q p' q' y a : K) (i j : Fin 3) (h : i ≠ j) :
    (!![p, 0, 0; y, 1, 0; a, y, q] - !![p', 0, 0; y, 1, 0; a, y, q'] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_up {K : Type} [CommRing K] (p q y z a : K) (i j : Fin 3) (h : i < j) :
    (!![p, 0, 0; y, 1, 0; a, z, q] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

theorem UpperTheory.lowerTriangular_conj_antidiag :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (y a : F.G0 → Q), F.Low Q y a → ∃ ρ : NRep F 3 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧ (∀ g, ρ.r g 1 0 = y g) ∧ ∀ g, ρ.r g 2 0 = a g := by
  intro l _ k _ _ F C₀ hF Q _ _ y a h
  obtain ⟨s1, s2, s3, s4, -⟩ := UpperTheory.V.Fr.star hF
  have y1 : y 1 = 0 := by
    have := h.muly 1 1
    simpa using this
  have st1 : F.star 1 = 1 := by simp [Frame.star]
  have a1 : a 1 = 0 := by
    have := h.mula 1 1
    simpa [y1] using this
  let p : F.G0 → Q := fun g => algebraMap k Q (F.Ψ g : k)
  let q : F.G0 → Q := fun g => algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k)
  have pm : ∀ g g', p (g * g') = p g * p g' := fun g g' => by simp [p]
  have qm : ∀ g g', q (g * g') = q g * q g' := fun g g' => by simp [q, mul_comm]
  have ps : ∀ g, p (F.star g) = q g := fun g => by simp only [p, q, s3]
  have qs : ∀ g, q (F.star g) = p g := fun g => by simp only [p, q, s3, inv_inv]
  have ym : ∀ g g', y (g * g') = y g * p g' + y g' := fun g g' => by
    rw [h.muly, Algebra.smul_def, mul_comm]
  have am : ∀ g g', a (g * g') = a g * p g' + y (F.star g) * y g' + q g * a g' := fun g g' => by
    rw [h.mula, Algebra.smul_def, Algebra.smul_def, mul_comm _ (a g)]
  have zm : ∀ g g', y (F.star (g * g')) = y (F.star g) + q g * y (F.star g') := fun g g' => by
    rw [s2, ym, ps]; ring
  let r : F.G0 →* Matrix (Fin 3) (Fin 3) Q :=
    { toFun := fun g => !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [p, q, y1, a1, st1]
      map_mul' := fun g g' => by
        rw [zm, pm, qm, ym, am, low_mul] }
  have hr : ∀ g, r g = !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g] := fun _ => rfl
  have w0 : w 3 0 = 1 := rfl
  have w1 : w 3 1 = 0 := rfl
  have w2 : w 3 2 = -1 := rfl
  let ψ : ∀ v, Fin 3 → F.Gv v →* Qˣ := fun v i =>
    (Units.map (algebraMap k Q).toMonoidHom).comp ((zpowGroupHom (w 3 i)).comp (F.Ψ.comp (F.loc v)))
  have hψ : ∀ v i g, (ψ v i g : Q) = algebraMap k Q ((F.Ψ (F.loc v g) ^ w 3 i : kˣ) : k) := fun _ _ _ => rfl
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have hc : Continuous fun x : F.G0 => (g : F.Γ)⁻¹ * (x : F.Γ) := by fun_prop
    have : ∀ᶠ x : F.G0 in nhds g, (g : F.Γ)⁻¹ * (x : F.Γ) ∈ (F.Ψ.ker : Set F.Γ) :=
      (hF.Ψ_open.preimage hc).mem_nhds (by simp)
    refine this.mono fun x hx => ?_
    have hx' : F.Ψ ((g : F.Γ)⁻¹ * (x : F.Γ)) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    exact hx'.symm
  have lp : IsLocallyConstant p := hΨ.comp fun u : kˣ => algebraMap k Q (u : k)
  have lq : IsLocallyConstant q := hΨ.comp fun u : kˣ => algebraMap k Q ((u⁻¹ : kˣ) : k)
  have lz : IsLocallyConstant fun g => y (F.star g) := h.lcy.comp_continuous s4
  refine ⟨⟨r, ψ, fun g => ?_, fun i j hij => ?_, fun v g => ?_⟩, ⟨fun g i => ?_, hψ⟩, ?_, fun i j => ?_,
    fun g => rfl, fun g => rfl⟩
  · rw [hr, hr, ps, qs, s1, h.pol, ← low_pol]
  · rw [hr, hr, s1, h.pol, ← h.nor]
    exact low_diag _ _ _ _ _ _ i j hij
  · obtain ⟨α, β, γ, H⟩ := h.loc v
    have e : ∀ s, r (F.loc0 v s) = !![p (F.loc0 v s), 0, 0; (p (F.loc0 v s) - 1) * α, 1, 0;
        (p (F.loc0 v s) - q (F.loc0 v s)) * γ - (1 - q (F.loc0 v s)) * (α * β), (1 - q (F.loc0 v s)) * β,
        q (F.loc0 v s)] := fun s => by
      obtain ⟨h1, h2, h3⟩ := H s
      rw [hr, h1, h2, h3]
      simp only [Algebra.smul_def, map_sub, map_one]
      rfl
    have e0 : ∀ s, (ψ v 0 s : Q) = p (F.loc0 v s) := fun s => by rw [hψ, w0, zpow_one]; rfl
    have e1 : ∀ s, (ψ v 1 s : Q) = 1 := fun s => by rw [hψ, w1, zpow_zero]; simp
    have e2 : ∀ s, (ψ v 2 s : Q) = q (F.loc0 v s) := fun s => by rw [hψ, w2, _root_.zpow_neg_one]; rfl
    have := ord3 α β γ (p (F.loc0 v (g 0))) (q (F.loc0 v (g 0))) (p (F.loc0 v (g 1))) (q (F.loc0 v (g 1)))
      (p (F.loc0 v (g 2))) (q (F.loc0 v (g 2)))
    rw [← e, ← e, ← e] at this
    rw [ordProd, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_cons, List.prod_nil, mul_one]
    show (r _ - (ψ v 0 (g 0) : Q) • 1) * ((r _ - (ψ v 1 (g 1) : Q) • 1) * (r _ - (ψ v 2 (g 2) : Q) • 1)) = 0
    rw [e0, e1, e2]
    exact this
  · show r g i i = _
    rw [hr]
    fin_cases i
    · simp [w0, p]
    · simp [w1]
    · simp [w2, q]
  · refine Ideal.span_eq_bot.2 ?_
    rintro x ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    exact low_up _ _ _ _ _ i j hij
  · show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    exacts [lp, IsLocallyConstant.const 0, IsLocallyConstant.const 0, h.lcy, IsLocallyConstant.const 1,
      IsLocallyConstant.const 0, h.lca, lz, lq]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem unit_sub {k : Type} [Field k] (u : kˣ) (hu : u ^ 2 ≠ 1) (i j : Fin 3) (hij : i ≠ j) :
    ((u ^ w 3 i : kˣ) : k) - ((u ^ w 3 j : kˣ) : k) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have h' : u ^ w 3 i = u ^ w 3 j := Units.ext h
  have a : u ≠ 1 := fun e => hu (by rw [e, one_pow])
  have b : u ≠ u⁻¹ := fun e => hu (by rw [sq]; exact mul_eq_one_iff_eq_inv.2 e)
  have w0 : w 3 0 = 1 := by decide
  have w1 : w 3 1 = 0 := by decide
  have w2 : w 3 2 = -1 := by decide
  fin_cases i <;> fin_cases j <;>
    first
    | exact hij rfl
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg] at h'
       first
       | exact a h'
       | exact a h'.symm
       | exact b h'
       | exact b h'.symm
       | exact a (inv_eq_one.1 h')
       | exact a (inv_eq_one.1 h'.symm))

theorem UpperTheory.one_add_maximalIdeal_subset_units :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → F.Low Q (fun g => ρ.r g 1 0) (fun g => ρ.r g 2 0) := by
  intro l _ k _ _ F C₀ h Q _ _ ρ hb ht hc
  have w0 : w 3 0 = 1 := by decide
  have w1 : w 3 1 = 0 := by decide
  have w2 : w 3 2 = -1 := by decide
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij => by
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    exact (Submodule.eq_bot_iff _).1 ht _ hm
  have hs := (UpperTheory.V.Fr.star h).2.2.2.2 ρ
  have s1 : ∀ g, ρ.r (F.star g) 1 0 = ρ.r g 2 1 := fun g => hs g 1 0
  have s2 : ∀ g, ρ.r (F.star g) 2 0 = ρ.r g 2 0 := fun g => hs g 2 0
  have d0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q (F.Ψ g : k) := fun g => by rw [hb.1, w0, zpow_one]
  have d1 : ∀ g : F.G0, ρ.r g 1 1 = 1 := fun g => by rw [hb.1, w1, zpow_zero, Units.val_one, map_one]
  have d2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k) := fun g => by
    rw [hb.1, w2, _root_.zpow_neg, zpow_one]
  refine ⟨hc 1 0, hc 2 0, fun g g' => ?_, fun g g' => ?_, s2, sub_eq_zero.1 (ρ.diag 1 0 (by decide)), fun v => ?_⟩
  · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d1, hz g 1 2 (by decide), Algebra.smul_def]
    ring
  · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d2, s1, Algebra.smul_def, Algebra.smul_def]
    ring
  · obtain ⟨s₀, h₀⟩ := h.f3 v
    obtain ⟨α, β, γ, H⟩ := UpperTheory.iwahori_factorization_lower_diag_upper (fun s => ρ.r (F.loc0 v s)) (fun i s => (ρ.ψ v i s : Q)) s₀
      (fun i j hij => by
        rw [hb.2, hb.2, ← map_sub]
        exact (IsUnit.mk0 _ (unit_sub _ h₀ i j hij)).map _)
      (fun s => hz _) (fun s i => (hb.1 _ i).trans (hb.2 v i s).symm) (ρ.ord v)
    refine ⟨α, β, γ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    simp only [hb.2, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg, Units.val_one, map_one] at h1 h2 h3
    simp only [Algebra.smul_def, map_sub, map_one, s1]
    exact ⟨h1, h2, h3⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_padded_family {κ M : Type} [Finite κ] [Zero M] (q : κ → Prop) (f : κ → M) (n : ℕ)
    (h : Nat.card {u // q u} ≤ n) :
    ∃ G : Fin n → M, (∀ i, G i = 0 ∨ ∃ u, q u ∧ G i = f u) ∧ ∀ u, q u → ∃ i, G i = f u := by
  classical
  haveI := Fintype.ofFinite κ
  have hc : Fintype.card {u // q u} ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨Function.extend e (fun u => f u.1) 0, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ u, e u = i
    · obtain ⟨u, rfl⟩ := hi
      right
      exact ⟨u.1, u.2, by rw [e.injective.extend_apply]⟩
    · left
      rw [Function.extend_apply' _ _ _ hi]
      rfl
  · intro u hu
    exact ⟨e ⟨u, hu⟩, by rw [e.injective.extend_apply]⟩

theorem UpperTheory.V.Fr.ep_pad :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (S : Space O F 3) (x : Ideal S.A) (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R), L.IsInv σ → ∀ P : GPres L.O' σ, Nat.card {u // P.wf u = 0} + (3 * F.d + 1) ≤ P.a → Nat.card {u // P.wf u = 1} ≤ P.g → L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) → Nonempty L.EPres := by
  intro l _ O _ _ F S x L σ hσ P h0 h1 hee
  obtain ⟨Fe, hF, hF'⟩ := exists_padded_family (fun u => P.wf u = 0) P.f (P.a - (3 * F.d + 1)) (by omega)
  obtain ⟨Go, hG, hG'⟩ := exists_padded_family (fun u => P.wf u = 1) P.f P.g h1
  have two : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  refine ⟨{ a := P.a, b := P.a - (3 * F.d + 1), g := P.g, p := P.p, Fe := Fe, Go := Go,
            num := by omega, surj := P.surj, ker := ?_, even := ?_, odd := ?_, min := P.min,
            ent := ?_, base := ?_, ee := hee }⟩
  · rw [P.ker]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro _ ⟨u, rfl⟩
      rcases two (P.wf u) with h | h
      · exact Or.inl (hF' u h)
      · exact Or.inr (hG' u h)
    · rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rcases hF i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
      · rcases hG i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
  · intro i
    rcases hF i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro i
    rcases hG i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro s i j
    rw [P.part]
    exact hσ.ent s i j
  · intro y
    rw [P.part]
    exact hσ.base y
end
