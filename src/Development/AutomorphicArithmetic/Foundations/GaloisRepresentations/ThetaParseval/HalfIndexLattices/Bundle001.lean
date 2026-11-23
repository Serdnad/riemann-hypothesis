module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight

@[expose] public section

section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem card_quot_span_mul {R : Type} [CommRing R] [IsDomain R] {a b : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  let f : R →+ R := AddMonoidHom.mulLeft a
  have hle : (Ideal.span {a * b}).toAddSubgroup ≤ (Ideal.span {a}).toAddSubgroup := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨y * b, by ring⟩
  have hcomap : (Ideal.span {a * b}).toAddSubgroup.comap f = (Ideal.span {b}).toAddSubgroup := by
    ext x
    change a * x ∈ Ideal.span {a * b} ↔ x ∈ Ideal.span {b}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact mul_dvd_mul_iff_left ha
  have hmap : (⊤ : AddSubgroup R).map f = (Ideal.span {a}).toAddSubgroup := by
    ext x
    change x ∈ (⊤ : AddSubgroup R).map f ↔ x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hrel : (Ideal.span {a * b}).toAddSubgroup.relIndex (Ideal.span {a}).toAddSubgroup =
      (Ideal.span {b}).toAddSubgroup.index := by
    rw [← hmap, ← AddSubgroup.relIndex_comap, hcomap, AddSubgroup.relIndex_top_right]
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hrel] at hmul
  change (Ideal.span {a * b}).toAddSubgroup.index =
    (Ideal.span {a}).toAddSubgroup.index * (Ideal.span {b}).toAddSubgroup.index
  rw [← hmul, Nat.mul_comm]

private theorem card_quot_span_prod {R ι : Type} [CommRing R] [IsDomain R] (s : Finset ι) (c : ι → R)
    (hc : ∀ i ∈ s, c i ≠ 0) :
    Nat.card (R ⧸ Ideal.span {∏ i ∈ s, c i}) = ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {c i}) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : Ideal.span {(1 : R)} = ⊤ := Ideal.span_singleton_one
    simp only [Finset.prod_empty]
    rw [h]
    exact Nat.card_unique
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      card_quot_span_mul (hc i (Finset.mem_insert_self i s)),
      ih fun j hj => hc j (Finset.mem_insert_of_mem hj)]

theorem UpperTheory.TP.W.cardDet :
    CardDet := by
  intro R M _ _ _ _ _ _ _ f hinj
  set N := LinearMap.range f with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv cb (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hg : ∀ i, g (b' i) = c i • b' i := by
    intro i
    have : g (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' g = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hg, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : M →ₗ[R] N) = f := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det g = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det f) (LinearMap.det g) at hass
  rw [h1] at hass
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i hi
    apply cb.ne_zero i
    apply Subtype.ext
    rw [cb_eq i]
    change c i • b' i = 0
    rw [hi, zero_smul]
  have hcq : Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  rw [hcq, Ideal.span_singleton_eq_span_singleton.2 hass,
    card_quot_span_prod _ c fun i _ => hc0 i]
end

section

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem resEta_mul (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) : ResEtaF (η * κ) 1 :=
  ⟨h2.1, fun e he a => by rw [MonoidHom.mul_apply, hκ.base a, mul_one]; exact h2.2 e he a⟩

end UpperTheory.TP.W

end
end

section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem idxHalf_half {X : Type} [AddCommGroup X] (γ : X → X → ℂ)
    (al : ∀ x y z, γ (x + y) z = γ x z * γ y z) (ar : ∀ x y z, γ x (y + z) = γ x y * γ x z)
    (nz : ∀ x y, γ x y ≠ 0) (P P0 Q Q0 : AddSubgroup X)
    (h1 : ∀ p ∈ P, ∀ q ∈ Q, q ∈ Q0 → γ p q = 1)
    (h3 : ∀ p ∈ P, (∀ q ∈ Q, γ p q = 1) → p ∈ P0)
    (hfin : Q0.relIndex Q ≠ 0) :
    P0.relIndex P ≠ 0 ∧ P0.relIndex P ≤ Q0.relIndex Q := by
  classical
  have g0 : ∀ x, γ x 0 = 1 := fun x => by
    have h := ar x 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz x 0) (h.symm.trans (mul_one _).symm)
  have g0' : ∀ y, γ 0 y = 1 := fun y => by
    have h := al 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz 0 y) (h.symm.trans (mul_one _).symm)
  have hfinQ : Finite (↥Q ⧸ Q0.addSubgroupOf Q) := Nat.finite_of_card_ne_zero hfin
  letI : Fintype (↥Q ⧸ Q0.addSubgroupOf Q) := Fintype.ofFinite _
  let f : ↥P → ↥Q →+ Additive ℂˣ := fun p =>
    { toFun := fun q => Additive.ofMul (Units.mk0 (γ p q) (nz p q))
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext
        simp [g0]
      map_add' := fun q1 q2 => by
        rw [← ofMul_mul]
        congr 1
        ext
        simp [ar] }
  have hker : ∀ p, Q0.addSubgroupOf Q ≤ (f p).ker := by
    intro p q hq
    rw [AddSubgroup.mem_addSubgroupOf] at hq
    rw [AddMonoidHom.mem_ker]
    show Additive.ofMul _ = Additive.ofMul 1
    congr 1
    ext
    simp [h1 p p.2 q q.2 hq]
  let χ : ↥P → AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ := fun p =>
    { toFun := fun g => ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) g) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp }
  have hχ : ∀ p (q : ↥Q), χ p (q : ↥Q ⧸ Q0.addSubgroupOf Q) = γ p q := by
    intro p q
    show ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) (q : ↥Q ⧸ Q0.addSubgroupOf Q)) : ℂˣ) : ℂ) = _
    rw [QuotientAddGroup.lift_mk]
    rfl
  let Φ : ↥P →+ Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) :=
    { toFun := fun p => Additive.ofMul (χ p)
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [hχ, AddChar.one_apply]
        simp [g0']
      map_add' := fun p1 p2 => by
        rw [← ofMul_mul]
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [AddChar.mul_apply, hχ, hχ, hχ]
        simp [al] }
  have hkerΦ : Φ.ker ≤ P0.addSubgroupOf P := by
    intro p hp
    rw [AddMonoidHom.mem_ker] at hp
    have hp' : χ p = 1 := hp
    rw [AddSubgroup.mem_addSubgroupOf]
    apply h3 p p.2
    intro q hq
    have h4 := congrArg (fun c : AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ => c ((⟨q, hq⟩ : ↥Q) : ↥Q ⧸ Q0.addSubgroupOf Q)) hp'
    rw [hχ, AddChar.one_apply] at h4
    exact h4
  haveI : Finite (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
    inferInstanceAs (Finite (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ))
  have hΦfin : Nat.card Φ.range ≤ Q0.relIndex Q := by
    calc Nat.card Φ.range ≤ Nat.card (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := rfl
      _ = Fintype.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := Nat.card_eq_fintype_card
      _ ≤ Fintype.card (↥Q ⧸ Q0.addSubgroupOf Q) := AddChar.card_addChar_le _ _
      _ = Q0.relIndex Q := Nat.card_eq_fintype_card.symm
  haveI : Finite Φ.range := Finite.of_injective _ Subtype.val_injective
  have hkpos : Φ.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  have hdvd := AddSubgroup.index_dvd_of_le hkerΦ
  have hne : (P0.addSubgroupOf P).index ≠ 0 := fun h => hkpos (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  refine ⟨hne, ?_⟩
  calc P0.relIndex P = (P0.addSubgroupOf P).index := rfl
    _ ≤ Φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hkpos) hdvd
    _ = Nat.card Φ.range := AddSubgroup.index_ker Φ
    _ ≤ Q0.relIndex Q := hΦfin

theorem UpperTheory.TP.W.idxHalf :
    IdxHalf := by
  intro R X M _ _ _ _ _ σ w γ W hH A B hA hB hidx e e' he he' hee' he'e hadj hAe hBe hf
  have memE : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e S ↔ x ∈ S ∧ e x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).1, he y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have memE' : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e' S ↔ x ∈ S ∧ e' x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).2, he' y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have prodF : idx A B = idx (Submodule.map e A) (Submodule.map e B) *
      idx (Submodule.map e' A) (Submodule.map e' B) := by
    let φ : ↥B.toAddSubgroup →+ ↥(Submodule.map e B).toAddSubgroup × ↥(Submodule.map e' B).toAddSubgroup :=
      { toFun := fun b => (⟨e b, Submodule.mem_map_of_mem b.2⟩, ⟨e' b, Submodule.mem_map_of_mem b.2⟩)
        map_zero' := by ext <;> simp
        map_add' := fun x y => by ext <;> simp }
    have hφs : Function.Surjective φ := by
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx' := (memE B hBe x).1 hx
      have hy' := (memE' B hBe y).1 hy
      refine ⟨⟨x + y, B.add_mem hx'.1 hy'.1⟩, ?_⟩
      have h1 : e y = 0 := by rw [← hy'.2, hee']
      have h2 : e' x = 0 := by rw [← hx'.2, he'e]
      ext <;> simp [φ, map_add (f := _), hx'.2, hy'.2, h1, h2]
    have hcomap : A.toAddSubgroup.addSubgroupOf B.toAddSubgroup =
        AddSubgroup.comap φ (((Submodule.map e A).toAddSubgroup.addSubgroupOf
          (Submodule.map e B).toAddSubgroup).prod
          ((Submodule.map e' A).toAddSubgroup.addSubgroupOf (Submodule.map e' B).toAddSubgroup)) := by
      ext b
      simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf,
        Submodule.mem_toAddSubgroup]
      constructor
      · intro hb
        exact ⟨Submodule.mem_map_of_mem hb, Submodule.mem_map_of_mem hb⟩
      · rintro ⟨h1, h2⟩
        have h1' : e b ∈ A := ((memE A hAe _).1 h1).1
        have h2' : e' b ∈ A := ((memE' A hAe _).1 h2).1
        have hbB : (b : X) ∈ B := b.2
        have h3 : (b : X) - e b - e' b ∈ A :=
          (hf b).2 (B.sub_mem (B.sub_mem hbB (hBe _ hbB).1) (hBe _ hbB).2)
        convert A.add_mem (A.add_mem h3 h1') h2' using 1
        abel
    show (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).index = _
    rw [hcomap, AddSubgroup.index_comap_of_surjective _ hφs, AddSubgroup.index_prod]
    rfl
  have hfin2 : idx (Submodule.map e' A) (Submodule.map e' B) ≠ 0 := fun h => hidx (by rw [prodF, h, mul_zero])
  have s1h1 : ∀ p ∈ (Submodule.map e A).toAddSubgroup, ∀ q ∈ (Submodule.map e' B).toAddSubgroup,
      q ∈ (Submodule.map e' A).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hA ((memE A hAe p).1 hp).1 ((memE' A hAe q).1 hq).1
  have s1h3 : ∀ p ∈ (Submodule.map e A).toAddSubgroup,
      (∀ q ∈ (Submodule.map e' B).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e B).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE A hAe p).1 hp
    have hpB : p ∈ B := by
      refine (hB p).2 (fun b hb => ?_)
      rw [← hp'.2, hadj]
      exact hq _ ((memE' B hBe _).2 ⟨(hBe b hb).2, he' b⟩)
    exact (memE B hBe p).2 ⟨hpB, hp'.2⟩
  have st1 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s1h1 s1h3 hfin2
  have s2h1 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup, ∀ q ∈ (Submodule.map e A).toAddSubgroup,
      q ∈ (Submodule.map e B).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hB ((memE' B hBe p).1 hp).1 ((memE B hBe q).1 hq).1
  have s2h3 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup,
      (∀ q ∈ (Submodule.map e A).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e' A).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE' B hBe p).1 hp
    have hpA : p ∈ A := by
      refine (hA p).2 (fun a ha => hH.swap_eq_one ?_)
      rw [← hp'.2, ← hadj]
      exact hH.swap_eq_one (hq _ ((memE A hAe _).2 ⟨(hAe a ha).1, he a⟩))
    exact (memE' A hAe p).2 ⟨hpA, hp'.2⟩
  have st2 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s2h1 s2h3 st1.1
  rw [prodF]
  congr 1
  exact le_antisymm st2.2 st1.2
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

namespace UpperTheory.TP

def TLiftK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), W.GoodK (cj E) B →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'

end UpperTheory.TP

end
end
