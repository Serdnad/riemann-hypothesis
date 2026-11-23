module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle038
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add (f := _)]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SUGenPairs

open GlobalTheory.UnRep Matrix

section Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem refl_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E) :
    k * refl c G x u = refl c G (k *ᵥ x) u * k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ReflLaws.refl_mulVec, ReflLaws.refl_mulVec, hk, hk, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem refl_conj' {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E)
    (X : Matrix (Fin n) (Fin n) E) : k * (refl c G x u * X) = refl c G (k *ᵥ x) u * (k * X) := by
  rw [← mul_assoc, refl_conj hk, mul_assoc]

theorem det_refl (x : Fin n → E) (u : E) (hx : hermE c G x x ≠ 0) : (refl c G x u).det = u := by
  rw [GlobalTheory.UnRep.refl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, ← ReflLaws.hermE_eq_dot, div_mul_cancel₀ _ hx]
  ring

theorem det_prod (l : List ((Fin n → E) × E)) (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0) :
    (l.map fun p => refl c G p.1 p.2).prod.det = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.det_mul]
    rw [det_refl _ _ (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

theorem prod_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (P : List ((Fin n → E) × (Fin n → E) × E)) :
    k * (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod =
      ((P.map fun p => (k *ᵥ p.1, k *ᵥ p.2.1, p.2.2)).map
        fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * k := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc, refl_conj' hk, ih]

theorem tele (hG : IsHermForm c G) (x₀ : Fin n → E) (h₀ : hermE c G x₀ x₀ ≠ 0) :
    ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
    ∃ P : List ((Fin n → E) × (Fin n → E) × E),
      (∀ p ∈ P, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * c p.2.2 = 1) ∧
      (l.map fun p => refl c G p.1 p.2).prod =
        (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * refl c G x₀ (l.map Prod.snd).prod := by
  have L := ReflLaws.refl_laws F E c n G hG x₀ h₀
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp, by simp [L.2.1]⟩
  | cons q l ih =>
    intro hl
    obtain ⟨P, hP, e⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    have hk : IsUnE c G (refl c G x₀ q.2) := L.2.2.2 q.2 hq2
    refine ⟨(q.1, x₀, q.2) :: P.map (fun p => (refl c G x₀ q.2 *ᵥ p.1, refl c G x₀ q.2 *ᵥ p.2.1, p.2.2)), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hq1, h₀, hq2⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨a1, a2, a3⟩ := hP p' hp'
        exact ⟨by rw [hk]; exact a1, by rw [hk]; exact a2, a3⟩
    · have hcu : refl c G x₀ (c q.2) * refl c G x₀ q.2 = 1 := by
        rw [L.2.2.1, mul_comm, hq2, L.2.1]
      have hc := prod_conj hk P
      simp only [List.map_cons, List.prod_cons]
      rw [e, ← L.2.2.1 q.2]
      calc refl c G q.1 q.2 * ((P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod *
              refl c G x₀ (l.map Prod.snd).prod)
          = refl c G q.1 q.2 * ((refl c G x₀ (c q.2) * refl c G x₀ q.2) *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by rw [hcu, one_mul, mul_assoc]
        _ = refl c G q.1 q.2 * refl c G x₀ (c q.2) * (refl c G x₀ q.2 *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]

end Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjE_apply (hcm : IsCMExt F E σ) (x : E) : GlobalTheory.WeilTwistF.conjE hcm x = σ x := rfl

theorem hermE_transpose (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = (fun b => σ (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [hermE, conjE_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermE_eq_hE (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = hE σ J y x := by
  rw [hermE_transpose]
  simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem isUnE_of (hcm : IsCMExt F E σ) {n : ℕ} (J m : Matrix (Fin n) (Fin n) E) (h : (m.map σ)ᵀ * J * m = J) :
    IsUnE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ m := by
  have e1 : ∀ y : Fin n → E, (fun b => σ ((m *ᵥ y) b)) = m.map σ *ᵥ (fun b => σ (y b)) := fun y => by
    funext i

    simp [mulVec, dotProduct, map_sum, map_mul]
  intro x y
  have e : (fun b => σ ((m *ᵥ y) b)) ⬝ᵥ J *ᵥ (m *ᵥ x) = (fun b => σ (y b)) ⬝ᵥ ((m.map σ)ᵀ * J * m) *ᵥ x := by
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [hermE_transpose, hermE_transpose, e, h]

theorem qr_eq_refl (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = GlobalTheory.UnRep.refl (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x u := by
  rw [GlobalTheory.SUAssemble.qr, GlobalTheory.UnRep.refl, hermE_eq_hE, Matrix.mulVec_transpose]
  rfl

end GlobalTheory.SUGenPairs


open GlobalTheory.UnRep GlobalTheory.SUGenPairs in
theorem GlobalTheory.SUGenPairs.eq_prod_pairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  intro F E _ _ _ _ _ σ hcm M J hJ g hg hdet
  have hG : IsHermForm (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ :=
    ⟨fun x => (GlobalTheory.WeilTwistF.conjE hcm).apply_symm_apply x, GlobalTheory.WeilTwistF.conjE_ne hcm, fun a b => hJ.1 a b,
      by rw [Matrix.det_transpose]; exact hJ.2⟩
  have hu : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  obtain ⟨l, hl, hgl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl F E _ M Jᵀ hG _ (isUnE_of hcm J _ hu)
  have hne : ∀ x : Fin M → E, hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x x ≠ 0 → hE σ J x x ≠ 0 := fun x hx => by
    rwa [← hermE_eq_hE hcm]
  cases l with
  | nil => exact ⟨[], by simp, by simpa using hgl⟩
  | cons q l' =>
    obtain ⟨P, hP, e⟩ := tele hG q.1 (hl q List.mem_cons_self).1 (q :: l') hl
    have ha : ((q :: l').map Prod.snd).prod = 1 := by
      rw [← det_prod _ (fun p hp => (hl p hp).1), ← hgl, hdet]
    rw [ha, (ReflLaws.refl_laws F E _ M Jᵀ hG q.1 (hl q List.mem_cons_self).1).2.1, mul_one] at e
    refine ⟨P, fun p hp => ⟨hne _ (hP p hp).1, hne _ (hP p hp).2.1, (hP p hp).2.2⟩, ?_⟩
    rw [hgl, e]
    congr 2
    funext p
    rw [qr_eq_refl hcm, qr_eq_refl hcm]
    rfl
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem exists_nat_denom {ι : Type} [Fintype ι] (a : ι → Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (k : ι) (w : Pl E),
      (d : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
  choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)
  refine ⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩
  have h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
    have := h k w
    rwa [show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast] at this
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) h'

theorem cLoc_val (k : finU (E := E) (n := n)) (w : Pl E) (i j : Fin n) :
    (cLoc w (k : UA E n)).val i j = pLoc E w ((FinPart.pU k).val i j) := rfl

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU (E := E) (n := n), ∃ d : ℕ, 0 < d ∧ ∀ g : finU (E := E) (n := n), (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ _ n S hS x
  obtain ⟨D₁, hD₁, h₁⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2
  obtain ⟨D₂, hD₂, h₂⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2
  have key : ∀ (h : finU (E := E) (n := n)) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) →
      ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
    intro h w hk i j
    have e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) * ((x⁻¹ : finU (E := E) (n := n)) : UA E n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₁ (i, a) w
    have e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₂ (b, j) w
    have e3 := GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b
    have e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a *
        (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) =
        ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b *
        ((D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) := by
      push_cast; ring
    rw [e4]
    exact mul_mem (mul_mem e1 e3) e2
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩
  rcases GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw
  · exact key g w (hg w hw) i j
  · have hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) : UA E n) ∈
        GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) (n := n) := by
      have : (x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) = (x⁻¹ * g * x)⁻¹ := by group
      rw [this, Subgroup.coe_inv, map_inv]
      exact (GlobalTheory.LFun.KGL _ (n := n)).inv_mem (hg _ hw)
    have h1 := key g⁻¹ _ hinv j i
    have e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w
        ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU (E := E) (n := n)) : UA E n)).val j i) := by
      rw [GlobalTheory.BCT.LocCpt.cLoc_eq_invT]
      show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
        (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _
      rw [← map_inv, ← map_inv, Subgroup.coe_inv]
      rfl
    rw [e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1

end GlobalTheory.BCT.StabDenom
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem hasOp_one (ψ : AddChar (AF F) ℂ) : HasOp (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl⟩

theorem hasOp_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOp ψ G) (hG' : HasOp ψ G') :
    HasOp ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul]
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul]
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]

theorem hasOp_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOp ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOp ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOp_one ψ) (fun _ _ _ _ hx hy => hasOp_mul hx hy) hG

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl (F := F)) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl (F := F)) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange

open GlobalTheory.SympChange in
theorem GlobalTheory.SympChange.change_of_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOp B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact GlobalTheory.T.weil_operator_for_levi_matrix F B.ψ hB.std hunr hnt _ A hA
    · exact GlobalTheory.T.weil_operator_for_unipotent_matrix F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weil_operator_for_weyl_element F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure⟩ :=
    hasOp_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    have hcoord : GlobalTheory.LatVac.locCo co v γ = spAct G (GlobalTheory.LatVac.locCo M.co v γ) :=
      locCo_eq M.co co G hGe v γ
    rw [hcoord, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
end
end
