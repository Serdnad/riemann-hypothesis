module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3
open scoped Matrix

section GlobalTheory

variable {A : Type} [CommRing A] (r k : ℕ)

def hEmbGL : GL (Fin k) A →* GL (Idx r k) A where
  toFun g := ⟨hEmb r (g : Matrix (Fin k) (Fin k) A), hEmb r ((g⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A),
    by rw [MassDataIdxStIm.hEmb_mul, Units.mul_inv, MassDataIdxStIm.hEmb_one],
    by rw [MassDataIdxStIm.hEmb_mul, Units.inv_mul, MassDataIdxStIm.hEmb_one]⟩
  map_one' := Units.ext (by simp [MassDataIdxStIm.hEmb_one])
  map_mul' g h := Units.ext (by simp [MassDataIdxStIm.hEmb_mul])

theorem hEmbGL_val (g : GL (Fin k) A) :
    ((hEmbGL r k g : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) = hEmb r (g : Matrix (Fin k) (Fin k) A) := rfl

theorem hEmbGL_injective : Function.Injective (hEmbGL (A := A) r k) :=
  fun g h e => Units.ext (MassDataIdxStIm.hEmb_inj (congrArg Units.val e))

theorem hEmb_sub_one_mem_iff (I : Ideal A) (B : Matrix (Fin k) (Fin k) A) :
    (∀ a b, (hEmb r B - 1) a b ∈ I) ↔ ∀ i j, (B - 1) i j ∈ I := by
  constructor
  · intro h i j
    have := h (Sum.inr (Sum.inl (Sum.inl i))) (Sum.inr (Sum.inl (Sum.inl j)))
    simpa [hEmb, midEmb, Matrix.one_apply] using this
  · intro h a b
    rcases a with a | ((a | a) | a) <;> rcases b with b | ((b | b) | b) <;>
      simp [hEmb, midEmb, Matrix.one_apply] <;>
      exact h a b

variable {n : Type} [Fintype n] [DecidableEq n]

theorem entries_mul_mem (I : Ideal A) (P M Q : Matrix n n A) (hM : ∀ a b, M a b ∈ I) :
    ∀ a b, (P * M * Q) a b ∈ I := by
  intro a b
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hM m l)

theorem conj_sub_one_mem_iff (I : Ideal A) (c : GL n A) (M : Matrix n n A) :
    (∀ a b, (((c⁻¹ : GL n A) : Matrix n n A) * M * (c : Matrix n n A) - 1) a b ∈ I) ↔ ∀ a b, (M - 1) a b ∈ I := by
  have e : ((c⁻¹ : GL n A) : Matrix n n A) * M * (c : Matrix n n A) - 1 =
      ((c⁻¹ : GL n A) : Matrix n n A) * (M - 1) * (c : Matrix n n A) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [e]
  constructor
  · intro h
    have h2 := entries_mul_mem I (c : Matrix n n A) _ ((c⁻¹ : GL n A) : Matrix n n A) h
    have e2 : (c : Matrix n n A) * (((c⁻¹ : GL n A) : Matrix n n A) * (M - 1) * (c : Matrix n n A)) *
        ((c⁻¹ : GL n A) : Matrix n n A) = M - 1 := by
      simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rwa [e2] at h2
  · intro h
    exact entries_mul_mem I _ _ _ h

end GlobalTheory

variable {D : D7}

def HModel (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) (c : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)),
    Function.Surjective ψ ∧
    (∀ x : KvA X p.1, (∀ i j, ((ψ x : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ MassDataIdxSteps.KgX X p) ∧
    ∀ x : KvA X p.1, (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      c⁻¹ * ψ x * c ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range

def inclH (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : KvH X u p.1 →* KvA X p.1 where
  toFun x := ⟨((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
    HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem psiH_exists (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X)
    (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) (c : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p))
    (hs : Function.Surjective ψ)
    (hk : ∀ x : KvA X p.1, (∀ i j, ((ψ x : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ MassDataIdxSteps.KgX X p)
    (hH : ∀ x : KvA X p.1, (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      c⁻¹ * ψ x * c ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range) :
    ∃ ψH : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p), Function.Surjective ψH ∧
      (∀ x, hEmbGL D.R.rS D.R.k (ψH x) = c⁻¹ * ψ (inclH X u p x) * c) ∧
      ∀ x : KvH X u p.1, (∀ i j, ((ψH x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
        Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ x ∈ KgH X u p := by
  let φ : KvH X u p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (ψ.comp (inclH X u p))
  have hφv : ∀ x, φ x = c⁻¹ * ψ (inclH X u p x) * c := fun x => by
    show c⁻¹ * ψ (inclH X u p x) * c⁻¹⁻¹ = _
    rw [inv_inv]
  have hφ : ∀ x, φ x ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range := fun x => by
    rw [hφv]
    exact (hH (inclH X u p x)).1 (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
  let e := MonoidHom.ofInjective (hEmbGL_injective (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k)
  let ψH : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p) :=
    e.symm.toMonoidHom.comp (φ.codRestrict _ hφ)
  have key : ∀ x, hEmbGL D.R.rS D.R.k (ψH x) = φ x := fun x => by
    rw [← MonoidHom.ofInjective_apply (hEmbGL_injective (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k) (x := ψH x)]
    show ((e (e.symm ⟨φ x, hφ x⟩) : (hEmbGL D.R.rS D.R.k).range) : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) = φ x
    rw [MulEquiv.apply_symm_apply]
  refine ⟨ψH, fun B => ?_, fun x => by rw [key, hφv], fun x => ?_⟩
  · obtain ⟨x', hx'⟩ := hs (c * hEmbGL D.R.rS D.R.k B * c⁻¹)
    have hconj : c⁻¹ * ψ x' * c = hEmbGL D.R.rS D.R.k B := by rw [hx']; group
    have hxH : (x' : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (hH x').2 ⟨B, hconj.symm⟩
    let x : KvH X u p.1 := ⟨⟨(x' : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), hxH⟩, x'.2⟩
    refine ⟨x, hEmbGL_injective D.R.rS D.R.k ?_⟩
    rw [key, hφv]
    have : inclH X u p x = x' := rfl
    rw [this, hconj]
  · have h1 := hEmb_sub_one_mem_iff (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k
      (Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) (ψH x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p))
    rw [← h1, ← hEmbGL_val, key, hφv, Units.val_mul, Units.val_mul, conj_sub_one_mem_iff, hk]
    rfl

theorem hLatGL_of_model (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : HModel X u p) : HLatGL X u p := by
  obtain ⟨ψ, c, hs, hk, hH⟩ := h
  obtain ⟨ψH, hsH, -, hkH⟩ := psiH_exists X u p ψ c hs hk hH
  exact ⟨ψH, hsH, hkH⟩

end PIW.MassDataColumns
end
end

section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem mem_stabT_of_comp (I : Formalism.MainNotions.S.AutInst) (h : HA (Af I.F) I.cm.sig I.J) {a : ℕ}
    (X0 : Fin a → Fin I.n → I.E)
    (hc : ∀ v, PI.MassDataKppVolLemmas.piV I v h ∈ stabT (Fv I.F v) I.cm.sig I.J X0) :
    h ∈ stabT (Af I.F) I.cm.sig I.J X0 := by
  rw [mem_stabT]
  intro b
  funext i
  rw [← sub_eq_zero]
  apply PI.MassDataKppVolLemmas.LocIdxLift_inj I
  intro v
  have hv := hc v
  rw [mem_stabT] at hv
  have e1 : ratV (F := I.F) (Fv I.F v) (X0 b) =
      (PI.MassDataKppVolLemmas.tV I v) ∘ ratV (F := I.F) (Af I.F) (X0 b) := by
    funext j
    simp [ratV, PI.MassDataKppVolLemmas.tV, tensMap_inclR]
  have h2 := congrFun (hv b) i
  rw [map_sub]
  show PI.MassDataKppVolLemmas.tV I v ((((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) *ᵥ ratV (F := I.F) (Af I.F) (X0 b)) i) -
    PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = 0
  rw [RingHom.map_mulVec, ← e1]
  have e2 : ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (PI.MassDataKppVolLemmas.tV I v) =
      ((HA.mat (Fv I.F v) I.cm.sig I.J (PI.MassDataKppVolLemmas.piV I v h) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) := rfl
  rw [e2]
  have e3 : PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = ratV (F := I.F) (Fv I.F v) (X0 b) i := by
    rw [e1]; rfl
  rw [e3, sub_eq_zero]
  exact h2

variable {D : D7}

theorem level_components_surjective : SurjH := by
  classical
  intro D X hb _hK u _hT _hL f
  have key : ∀ S : Finset (TypX X), ∃ z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
      z ∈ KHg X u ∧ ∀ p : TypX X, ((piH X u p.1 z : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        if p ∈ S then (((f p : KvH X u p.1) : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hzK, hz⟩ := ih
      set k : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J :=
        (((f q : KvH X u q.1) : Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) with hk
      have hkK : k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := (f q).2
      have hkH : k ∈ Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (f q : KvH X u q.1).1.2
      obtain ⟨h, hKf, hq1, hq2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I q.1 k hkK
      have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
        apply mem_stabT_of_comp X.B.I h
        intro v
        by_cases hv : v = q.1
        · subst hv; rw [hq1]; exact hkH
        · rw [hq2 v hv]; exact one_mem _
      refine ⟨⟨h, hH⟩ * z, ?_, fun p => ?_⟩
      · show (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
          Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
        exact mul_mem hKf hzK
      · rw [map_mul, Subgroup.coe_mul, hz p]
        show PI.MassDataKppVolLemmas.piV X.B.I p.1 h * _ = _
        by_cases hpq : p = q
        · subst hpq
          rw [if_neg hq, if_pos (Finset.mem_insert_self p S), mul_one, hq1]
        · have hp1 : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
          rw [hq2 p.1 hp1, one_mul]
          by_cases hpS : p ∈ S
          · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
          · rw [if_neg hpS, if_neg]
            intro hm
            rcases Finset.mem_insert.1 hm with e | e
            · exact hpq e
            · exact hpS e
  obtain ⟨z, hzK, hz⟩ := key Finset.univ
  refine ⟨z, hzK, fun p => Subtype.ext (Subtype.ext ?_)⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

end PIW.MassDataColumns
end
end

section

noncomputable section

namespace PIW.MassDataColumns

open MeasureTheory
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def MassUnfoldGen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    (X.measW u).IsTextNorm →
    CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
    ∀ U : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsCompact (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      IsOpen (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      MassFinite (GamHA X u) U →
      ∀ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
        IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μH →
        (X.measW u).μH 𝓕 = (X.measW u).μHinf Set.univ *
          (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) *
          ENNReal.ofReal (massCl (GamHA X u) U)

theorem massCl_nonneg {G : Type} [Group G] (Γ K : Subgroup G) : 0 ≤ massCl Γ K := by
  unfold massCl
  exact finsum_nonneg fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem unfoldGenStep_of (hM : MassUnfoldGen) (hH : MassDataMassesW.HinfCompact) (hF : MassDataMassesW.FDExistsH)
    (hV : MassDataMassesW.VolHTie) : UnfoldGenStep := by
  unfold UnfoldGenStep
  intro D X hb u hT U hUo hUc hMF
  have hN : (X.measW u).IsTextNorm := by
    exact X.measW_norm u
  have hC := hH X u
  have key := hM X u hN hC U hUc hUo hMF
  have hV' := hV X hb u hT
  obtain ⟨𝓕, h𝓕⟩ := hF X u
  have hex : ∃ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕
        (X.measW u).μH := ⟨𝓕, h𝓕⟩
  have hcov : covol (X.measW u).μH = ((X.measW u).μH hex.choose).toReal := by
    unfold covol
    exact dif_pos hex
  obtain ⟨-, hHi, hHf, -⟩ := hN
  haveI := hHi
  haveI := hHf
  have h1 : (X.measW u).μHinf Set.univ ≠ 0 := isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  have h2 : (X.measW u).μHinf Set.univ ≠ ⊤ := (hHi.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ hC)).ne
  have h3 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ 0 := IsOpen.measure_ne_zero (X.measW u).μHf hUo ⟨1, U.one_mem⟩
  have h4 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ ⊤ := (hHf.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact hUc).ne
  refine ⟨?_, ?_⟩
  · rw [hcov, key hex.choose hex.choose_spec, hV', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (massCl_nonneg _ _)]
  · rw [hV']
    exact mul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨h1, h2⟩) (ENNReal.toReal_ne_zero.mpr ⟨h3, h4⟩)

end PIW.MassDataColumns
end
end
