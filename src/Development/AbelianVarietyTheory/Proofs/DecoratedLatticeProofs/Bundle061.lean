module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

variable {E : Type} [Field E] {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}

def autOf (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g.val.submatrix e.symm e.symm)) (Matrix.toLin' ((g⁻¹).val.submatrix e.symm e.symm))
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv, Matrix.toLin'_one])

theorem autOf_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    autOf e g v = (g.val.submatrix e.symm e.symm).mulVec v := rfl

theorem autOf_inv_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    (autOf e g)⁻¹ v = ((g⁻¹).val.submatrix e.symm e.symm).mulVec v := rfl

theorem lev_symm (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (l : Fin (M + c')) : lev (n := A) (c := c) 1 (e.symm l) = if l.val < M then 1 else l.val - M + 1 := by
  rcases hm : e.symm l with a | i
  · have h1 : l = e (Sum.inl a) := by rw [← hm]; simp
    have := eX_lt e hcc he a
    rw [← h1] at this
    simp [lev, this]
  · have h1 : l = e (Sum.inr i) := by rw [← hm]; simp
    have := he i
    rw [← h1] at this
    simp [lev, this]

theorem mulVec_fix (e : A ⊕ Fin c ≃ Fin (M + c')) (m : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E)
    (hm : ∀ r s, lev 1 s ≤ lev 1 r → m r s = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E) r s) (v : Fin (M + c') → E)
    (l : Fin (M + c')) (hv : ∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) :
    (m.submatrix e.symm e.symm).mulVec v l = v l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single l]
  · rw [hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    by_cases h0 : v j = 0
    · rw [h0, mul_zero]
    · rw [hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]
  · simp

theorem mem_normOneIdeles (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (g : GL (A ⊕ Fin c) E) (hg : g ∈ N E A c 1) : autOf e g ∈ Loc.N1 E M c' := by
  have hL := lev_symm e hcc he
  have key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')),
      (∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) →
      (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv =>
    mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv
  have hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E),
      (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r := by
    intro g hg r hr
    refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [hr, key g hg v l ?_]
      · exact hv l (by simpa using hl)
      · intro j hj
        have : j.val < M + i := by
          by_contra h
          exact hj (hv j (by simpa using h))
        rw [hL, hL]; split_ifs <;> omega
    · funext l
      rw [hr, key g hg _ l]
      intro j hj
      have : j.val = M := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [Pi.sub_apply, hr, key g hg _ l, sub_self]
      intro j hj
      have : j.val = M + i := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
  refine ⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩
  funext l
  rw [autOf_apply, key g hg _ l]
  intro j hj
  have : j.val < M := by
    by_contra h
    exact hj (by simp [Loc.inX, h])
  rw [hL, hL]; split_ifs <;> omega

theorem locHom_autOf {k : Type} [Field k] (ι : E →+* k) (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) :
    (locHom ι e (autOf e g)).val = g.val.map ι := by
  rw [locHom_val]
  ext i j
  simp [GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]

end GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

namespace GlobalTheory.VolBridge
open NormOneIdeleAutomorphisms

theorem exists_N1_local_hom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV
  let f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k := fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)
  have hf : Continuous f := continuous_subtype_val.comp (VolN.continuous_mkNel 1)
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V := by
    show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V
    rw [VolN.mkNel_co]; exact huV
  have hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨b, hb⟩ := hD.exists_mem_open hW ⟨_, h0⟩
  refine ⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩
  have : locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b) := by
    apply Units.ext
    rw [locHom_autOf]
    show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val
    rw [VolN.val_mkNel, VolN.val_mkNel]
    ext r s
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), VolN.ext0, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]; exact hb

end GlobalTheory.VolBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.VolBridge

section PrXIff
variable {E : Type} [Field E] {M c' : ℕ}

theorem inX_castAdd (v : Sp E M) (i : Fin M) : Loc.inX E M c' v (Fin.castAdd c' i) = v i := by
  simp [Loc.inX]

theorem inX_natAdd (v : Sp E M) (i : Fin c') : Loc.inX E M c' v (Fin.natAdd M i) = 0 := by
  simp [Loc.inX]

theorem extX_inX (y : Sp E M ≃ₗ[E] Sp E M) (v : Sp E M) :
    extX c' y (Loc.inX E M c' v) = Loc.inX E M c' (y v) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [extX_castAdd, inX_castAdd]
    have h : (fun j => Loc.inX E M c' v (Fin.castAdd c' j)) = v := funext fun j => inX_castAdd v j
    rw [h]
  · rw [extX_natAdd, inX_natAdd, inX_natAdd]

variable {A : Type} {c : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem e_inl (a : A) : e (Sum.inl a) = Fin.castAdd c' (eX e hcc he a) := Fin.ext (by simp [eX_val])

include he in
theorem e_inr (i : Fin c) : e (Sum.inr i) = Fin.natAdd M (⟨i.val, hcc ▸ i.isLt⟩ : Fin c') := Fin.ext (by simp [he])

theorem single_inl (a : A) :
    (Pi.single (e (Sum.inl a)) 1 : Sp E (M + c')) = Loc.inX E M c' (Pi.single (eX e hcc he a) 1) := by
  rw [e_inl e hcc he]
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [inX_castAdd]
    by_cases h : i = eX e hcc he a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_injective _ _ h')), Pi.single_eq_of_ne h]
  · rw [inX_natAdd, Pi.single_eq_of_ne]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end PrXIff

section Blocks
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
  (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

theorem locHom_inl_inl (r : Sp E (M + c') ≃ₗ[E] Sp E (M + c')) (y : Sp E M ≃ₗ[E] Sp E M)
    (hr : ∀ v, r (Loc.inX E M c' v) = Loc.inX E M c' (y v)) (a b : A) :
    (locHom ι e r).val (Sum.inl a) (Sum.inl b) = (locHom ι (eX e hcc he) y).val a b := by
  show ι (r (Pi.single (e (Sum.inl b)) 1) (e (Sum.inl a))) = ι (y (Pi.single (eX e hcc he b) 1) (eX e hcc he a))
  rw [single_inl e hcc he, hr, e_inl e hcc he, inX_castAdd]

theorem locHom_extX (y : Sp E M ≃ₗ[E] Sp E M) :
    locHom ι e (extX c' y) = embX c (locHom ι (eX e hcc he) y) := by
  ext i j
  rw [GlobalTheory.RootEx.VolN.val_embX]
  show ι (extX c' y (Pi.single (e j) 1) (e i)) = _
  rcases i with a | s
  · rw [e_inl e hcc he, extX_castAdd]
    rcases j with b | t
    · rw [single_inl e hcc he]
      have h : (fun l => Loc.inX E M c' (Pi.single (eX e hcc he b) (1 : E)) (Fin.castAdd c' l)) = Pi.single (eX e hcc he b) 1 :=
        funext fun l => inX_castAdd _ l
      rw [h]
      rfl
    · have h : (fun l => (Pi.single (e (Sum.inr t)) (1 : E) : Sp E (M + c')) (Fin.castAdd c' l)) = 0 := by
        funext l
        rw [Pi.single_eq_of_ne]
        · rfl
        intro h'
        have := congrArg Fin.val h'
        simp [he] at this
        omega
      rw [h, map_zero]
      simp
  · rw [e_inr e hcc he, extX_natAdd]
    rcases j with b | t
    · rw [Pi.single_eq_of_ne]
      · simp
      intro h'
      have := congrArg Fin.val h'
      simp [eX_val] at this
      have := eX_lt e hcc he b
      omega
    · rw [e_inr e hcc he]
      by_cases h : s = t
      · subst h; simp
      · rw [Pi.single_eq_of_ne]
        · simp [Matrix.one_apply, h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        exact h (Fin.ext this)

end Blocks

theorem prX_iff_locHom : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  intro E k _ _ _ _ _ ι A _ _ M c c' e hcc he hN hdense CE Ck O hO hCkO hCkR hCE y
  constructor
  · rintro ⟨r, hr, hry⟩
    have hg : locHom ι e r ∈ Ck := (hCE r).1 hr
    obtain ⟨x', u, hu, hxu⟩ := GlobalTheory.RootEx.VolN.exists_of_mem_R (hCkR hg)
    have hu' := GlobalTheory.RootEx.Model.mem_N_iff.1 hu
    have hx' : x' = locHom ι (eX e hcc he) y := by
      ext a b
      rw [← locHom_inl_inl ι e hcc he r y hry a b, hxu, Units.val_mul, GlobalTheory.RootEx.VolN.val_embX, Matrix.mul_apply,
        Fintype.sum_sum_type]
      have h1 : ∀ a', u.val (Sum.inl a') (Sum.inl b) = if a' = b then 1 else 0 := fun a' => by
        rw [hu' (Sum.inl a') (Sum.inl b) le_rfl]
        simp [Matrix.one_apply]
      simp [h1]
    refine ⟨embX c x' * u * (embX c x')⁻¹, ?_, ?_⟩
    · have := GlobalTheory.RootEx.Model.conj_mem hu x'⁻¹
      simpa [map_inv, inv_inv] using this
    · rw [← hx']
      simpa [mul_assoc, ← hxu] using hg
  · rintro ⟨u, hu, huC⟩
    set x := locHom ι (eX e hcc he) y with hx
    have huO : u * embX c x ∈ O := (hCkO _ (hCkR huC)).1 huC
    have hV : IsOpen {v : GL (A ⊕ Fin c) k | v * embX c x ∈ O} := hO.preimage (continuous_mul_const _)
    obtain ⟨x₀, hx₀, hx₀V⟩ := hdense u hu _ hV huO
    refine ⟨x₀ * extX c' y, ?_, fun v => ?_⟩
    · rw [hCE, map_mul, locHom_extX ι e hcc he]
      have hR : locHom ι e x₀ * embX c x ∈ R k A c 1 :=
        mul_mem (Subgroup.mem_sup_right ((hN x₀).1 hx₀)) (Subgroup.mem_sup_left ⟨x, rfl⟩)
      exact (hCkO _ hR).2 hx₀V
    · show x₀ (extX c' y (Loc.inX E M c' v)) = _
      rw [extX_inX]
      exact (Subgroup.mem_inf.1 hx₀).2 (y v)

end GlobalTheory.VolBridge
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoverDS.TwistTypes

variable {p q : ℕ}

theorem sum_rhoNC (lam : Ix p q → ℚ) : ∑ a, rhoNC lam a = 0 := by
  have symm : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have k1 : ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  have k2 : ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  simp only [rhoNC, Finset.sum_sub_distrib, ← Finset.sum_div, k1, k2, sub_self, zero_div]

theorem normSq_add_half (lam : Ix p q → ℚ) :
    normSq (fun a => lam a + 1 / 2) =
      normSq lam + ∑ a, (lam a + 1 / 2) - (Fintype.card (Ix p q) : ℚ) / 4 := by
  have e : ∀ a, (lam a + 1 / 2) ^ 2 = lam a ^ 2 + (lam a + 1 / 2) - 1 / 4 := fun a => by ring
  simp only [normSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casimir_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) :
    casimir (Cover.twAct act) v = casimir act v - act 1 v + ((Fintype.card (Ix p q) : ℂ) / 4) • v := by
  have hterm : ∀ a b, Cover.twAct act (Eab a b) (Cover.twAct act (Eab b a) v) =
      act (Eab a b) (act (Eab b a) v) - if a = b then act (Eab a a) v - (1 / 4 : ℂ) • v else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [Cover.twAct_apply, if_true, Eab, Matrix.trace_single_eq_same, map_sub, map_smul]
      module
    · simp [Cover.twAct_apply, hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab,
        Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  have h1 : act 1 v = ∑ a, act (Eab a a) v := by

    rw [← Matrix.sum_single_one, map_sum, LinearMap.sum_apply]
    rfl
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h1, Finset.sum_const, Finset.card_univ]
  module

theorem hwSub_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · exact ⟨fun h => ((Cover.isHW_twAct act μ v).1 ⟨hv, h⟩).2, fun h => ((Cover.isHW_twAct act μ v).2 ⟨hv, h⟩).2⟩

theorem sum_of_inCone {lam μ : Ix p q → ℚ} (h : InCone lam μ) : ∑ a, μ a = ∑ a, lam a := by
  obtain ⟨m, -, rfl⟩ := h
  have e : ∑ c, ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, e, blattner, sum_rhoNC, add_zero]

theorem inCone_add {lam μ : Ix p q → ℚ} (c : ℚ) (h : InCone lam fun a => μ a - c) :
    InCone (fun a => lam a + c) μ := by
  obtain ⟨m, hm, hμ⟩ := h
  refine ⟨m, fun a b hab => add_lt_add_left (hm a b hab) c, funext fun a => ?_⟩
  have := congrFun hμ a
  rw [Cover.blattner_add]
  simp only at this ⊢
  linarith

theorem hasTypes_of_twist (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ)
    (h : HasTypes (Cover.twist R) lam) : HasTypes R fun a => lam a + 1 / 2 := by
  have h1 : Module.finrank ℂ ↥(hwSub (Cover.twAct R.HK.act) (blattner lam)) = 1 := h.1
  have h2 : ∀ v, casimir (Cover.twAct R.HK.act) v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v := h.2.1
  have h3 : ∀ (μ : Ix p q → ℚ) v, IsHW (Cover.twAct R.HK.act) μ v → InCone lam μ := h.2.2
  have hcone : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (fun a => lam a + 1 / 2) μ := fun μ v hv =>
    inCone_add _ (h3 _ v ((Cover.isHW_twAct _ _ v).2 (by simpa only [sub_add_cancel] using hv)))
  refine ⟨by rwa [Cover.blattner_add, ← hwSub_twAct], fun v => ?_, hcone⟩
  set c : ℂ := ((∑ a, (lam a + 1 / 2) : ℚ) : ℂ) with hc
  have htop : LinearMap.ker (R.HK.act 1 - c • LinearMap.id) = ⊤ := by
    refine GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le p q R.HK _ (fun X _ w hw => ?_) fun μ w hw => ?_
    · have e := congrArg (fun f : Module.End ℂ R.HK.V => f w) (R.HK.lie X 1)
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply,
        Module.End.mul_apply] at e
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      rw [← sub_eq_zero.1 e.symm, hw, map_smul]
    · by_cases h0 : w = 0
      · rw [h0]
        exact Submodule.zero_mem _
      have e := sum_of_inCone (hcone μ w ⟨h0, hw⟩)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

      rw [hc, ← e, ← Matrix.sum_single_one, map_sum, LinearMap.sum_apply, Rat.cast_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => ((mem_hwSub_iff _ _ _).1 hw).1 a
  have hv : R.HK.act 1 v = c • v := by
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using Submodule.eq_top_iff'.1 htop v
  have e := casimir_twAct R.HK.act v
  rw [h2, hv] at e
  rw [normSq_add_half, Rat.cast_sub, Rat.cast_sub, Rat.cast_add, ← hc]
  rw [Rat.cast_sub] at e
  push_cast
  linear_combination (norm := module) -e

end GlobalTheory.CoverDS.TwistTypes

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
end
