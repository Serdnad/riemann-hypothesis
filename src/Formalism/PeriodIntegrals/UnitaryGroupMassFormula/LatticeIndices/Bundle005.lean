module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def OEp (p : TypX X) : Set (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
  PI.FinKW.psiV X.B.I p.1 '' (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E : Set _)

def InModP (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) : Prop :=
  y ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} ⊔
    Ideal.span {((m : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def LocCong (p : TypX X) (y : HAp X p) : Prop :=
  (∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.e0 a))) ∧
  InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 X.z0) ∧
  ∀ i : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j | j.1 < i.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.bw i))

def StImAloc (p : TypX X) : Prop := KppX X hb p = {y | y ∈ KvX X p ∧ LocCong X p y}

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

theorem tens_topRing {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsTopologicalRing (Fv F v ⊗[F] E) := by
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := inferInstance
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  first
    | exact IsModuleTopology.topologicalRing (Fv F v) _
    | exact IsModuleTopology.isTopologicalRing (Fv F v) _
    | exact IsModuleTopology.Module.topologicalRing (Fv F v) _

theorem ha_contMul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) :
    ContinuousMul (HA (Fv F v) σ J) := by
  haveI := tens_topRing (F := F) (E := E) v
  first
    | infer_instance
    | (unfold HA; infer_instance)
    | (show ContinuousMul (HR (Fv F v) σ J); infer_instance)

theorem stTop {D : D7} (X : HidaSetting D) (p : TypX X) : StTop X p := by
  refine ⟨ha_contMul _ _ _, ?_⟩
  first
    | exact ⟨rfl⟩
    | (unfold HAp HA; infer_instance)
    | (haveI := tens_topRing (F := X.B.I.F) (E := X.B.I.E) p.1; unfold HAp HA; infer_instance)

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev Op (p : TypX X) : Type := p.1.adicCompletionIntegers X.B.I.F

def StResZ (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}

def StLatGL (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      ∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {A : Type} [CommRing A] {r k : ℕ}

def zI : Idx r k := Sum.inr (Sum.inl (Sum.inr ()))

def wI (i : Fin k) : Idx r k := Sum.inr (Sum.inl (Sum.inl i))

def ColC (m : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 m) ∧ b21 m = 0 ∧ b31 m = 0 ∧ (∀ i, m (wI i) zI = 0) ∧ m zI zI = 1 ∧
    ∀ j, m (Sum.inr (Sum.inr j)) zI = 0

def RowC (m : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b33 m) ∧ b31 m = 0 ∧ b32 m = 0 ∧ (∀ i, m zI (wI i) = 0) ∧ m zI zI = 1 ∧
    ∀ j, m zI (Sum.inl j) = 0

theorem det_shape {x : Matrix (Idx r k) (Idx r k) A} (h11 : IsUpUni (b11 x)) (h33 : IsUpUni (b33 x))
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) (h : Matrix (Fin k) (Fin k) A)
    (h22 : b22 x = midEmb h) : x.det = h.det := by
  have e1 : x.toBlocks₂₁ = 0 := by
    ext (i | i) j
    · exact congrFun (congrFun h21 i) j
    · exact congrFun (congrFun h31 i) j
  have e2 : x.toBlocks₂₂.toBlocks₂₁ = 0 := by
    ext i j
    exact congrFun (congrFun h32 i) j
  have d1 : x.toBlocks₁₁.det = 1 := isUpUni_det _ h11
  have d3 : x.toBlocks₂₂.toBlocks₂₂.det = 1 := isUpUni_det _ h33
  have d2 : x.toBlocks₂₂.toBlocks₁₁ = midEmb h := h22
  rw [← Matrix.fromBlocks_toBlocks x, e1, Matrix.det_fromBlocks_zero₂₁, d1, one_mul,
    ← Matrix.fromBlocks_toBlocks x.toBlocks₂₂, e2, Matrix.det_fromBlocks_zero₂₁, d3, mul_one, d2,
    midEmb, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem par_iff_flags (x y : Matrix (Idx r k) (Idx r k) A) (hxy : x * y = 1) (hyx : y * x = 1) :
    Par (fun h => IsUnit h.det) x ↔ ColC x ∧ RowC y := by
  constructor
  · intro hx
    have hy : Par (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) y := par_rinv gpUnit hx hxy
    obtain ⟨h11, -, h21, h31, h32, h, -, h22⟩ := hx
    obtain ⟨-, g33, g21, g31, g32, g, -, g22⟩ := hy
    refine ⟨⟨h11, h21, h31, fun i => ?_, ?_, fun j => ?_⟩, ⟨g33, g31, g32, fun i => ?_, ?_, fun j => ?_⟩⟩
    · simpa [b22, midEmb, wI, zI] using congrFun (congrFun h22 (Sum.inl i)) (Sum.inr ())
    · simpa [b22, midEmb, zI] using congrFun (congrFun h22 (Sum.inr ())) (Sum.inr ())
    · simpa [b32, zI] using congrFun (congrFun h32 j) (Sum.inr ())
    · simpa [b22, midEmb, wI, zI] using congrFun (congrFun g22 (Sum.inr ())) (Sum.inl i)
    · simpa [b22, midEmb, zI] using congrFun (congrFun g22 (Sum.inr ())) (Sum.inr ())
    · simpa [b21, zI] using congrFun (congrFun g21 (Sum.inr ())) j
  · rintro ⟨⟨h11, h21, h31, hwz, hzz, hfz⟩, ⟨g33, g31, g32, gzw, gzz, gze⟩⟩

    set B := b33 y with hB
    have hBu : IsUnit B.det := by rw [isUpUni_det _ g33]; exact isUnit_one
    let R : Matrix (Fin r) (Idx r k) A := Matrix.of fun j c => x (Sum.inr (Sum.inr j)) c
    let E : Matrix (Fin r) (Idx r k) A :=
      Matrix.of fun j c => (1 : Matrix (Idx r k) (Idx r k) A) (Sum.inr (Sum.inr j)) c
    have z1 : ∀ j a, y (Sum.inr (Sum.inr j)) (Sum.inl a) = 0 := fun j a => congrFun (congrFun g31 j) a
    have z2 : ∀ j m, y (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl m)) = 0 :=
      fun j m => congrFun (congrFun g32 j) m
    have key : B * R = E := by
      ext j c
      rw [show E j c = (y * x) (Sum.inr (Sum.inr j)) c by rw [hyx]; rfl, Matrix.mul_apply (M := y) (N := x),
        Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [z1, z2, B, R, b33, Matrix.mul_apply]
    have hRE : R = B⁻¹ * E := by rw [← key, Matrix.nonsing_inv_mul_cancel_left _ _ hBu]
    have fw : ∀ j i, x (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := by
      intro j i
      have := congrFun (congrFun hRE j) (Sum.inr (Sum.inl (Sum.inl i)))
      simpa [R, E, Matrix.mul_apply, Matrix.one_apply] using this
    have hb33 : b33 x = B⁻¹ := by
      ext j j'
      have := congrFun (congrFun hRE j) (Sum.inr (Sum.inr j'))
      simpa [R, E, b33, Matrix.mul_apply, Matrix.one_apply] using this
    have hb32 : b32 x = 0 := by
      ext j (i | u)
      · exact fw j i
      · exact hfz j

    have gze' : ∀ a, y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inl a) = 0 := gze
    have gzw' : ∀ i, y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := gzw
    have gzz' : y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inr ()))) = 1 := gzz
    have zw : ∀ i, x (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := by
      intro i
      have := congrFun (congrFun hyx (Sum.inr (Sum.inl (Sum.inr ())))) (Sum.inr (Sum.inl (Sum.inl i)))
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at this
      simpa [gze', gzw', gzz', fw, Matrix.one_apply] using this
    let h : Matrix (Fin k) (Fin k) A := Matrix.of fun i j => x (wI i) (wI j)
    have hb22 : b22 x = midEmb h := by
      ext (i | u) (i' | u')
      · simp [b22, midEmb, h, wI]
      · simpa [b22, midEmb, wI, zI] using hwz i
      · simpa [b22, midEmb] using zw i'
      · simpa [b22, midEmb, zI] using hzz
    have hb33' : IsUpUni (b33 x) := by rw [hb33]; exact isUpUni_inv _ g33
    refine ⟨h11, hb33', h21, h31, hb32, h, ?_, hb22⟩
    show IsUnit h.det
    rw [← det_shape h11 hb33' h21 h31 hb32 h hb22]
    exact Matrix.isUnit_det_of_right_inverse hxy

theorem mem_sG_iff_flags (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ ColC (g : Matrix (Idx r k) (Idx r k) A) ∧ RowC ((g⁻¹ : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) :=
  par_iff_flags _ _ (Units.mul_inv g) (Units.inv_mul g)

end MassDataIdxStIm
end
end

section

noncomputable section

namespace MassDataIdxStImB

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxStIm MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

section Lift

variable {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)


open Classical in
def lift (s : S) : R := if s = 0 then 0 else if s = 1 then 1 else Function.surjInv hπ s

theorem lift_zero : lift π hπ 0 = 0 := by
  simp [lift]

theorem lift_one [Nontrivial S] : lift π hπ 1 = 1 := by
  simp [lift]

theorem π_lift (s : S) : π (lift π hπ s) = s := by
  unfold lift
  split_ifs with h0 h1
  · rw [h0, map_zero]
  · rw [h1, map_one]
  · exact Function.surjInv_eq hπ s

theorem map_lift {m n : Type} (x : Matrix m n S) : (x.map (lift π hπ)).map π = x := by
  ext i j
  simp only [Matrix.map_apply, π_lift]

end Lift

section Par

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem isUpUni_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {n : ℕ} {h : Matrix (Fin n) (Fin n) A}
    (hh : IsUpUni h) : IsUpUni (h.map f) := by
  obtain ⟨hu, hd⟩ := hh
  refine ⟨?_, fun a => by simp [Matrix.map_apply, hd a, h1]⟩
  intro i j hij
  simp [Matrix.map_apply, hu hij, h0]

theorem midEmb_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) (h : Matrix (Fin k) (Fin k) A) :
    (midEmb h).map f = midEmb (h.map f) := by
  simp only [midEmb, Matrix.fromBlocks_map, Matrix.map_zero f h0, Matrix.map_one f h0 h1]

theorem par_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {P : Matrix (Fin k) (Fin k) A → Prop}
    {P' : Matrix (Fin k) (Fin k) B → Prop} (hPP : ∀ h, P h → P' (h.map f))
    {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : Par P' (x.map f) := by
  obtain ⟨h11, h33, h21, h31, h32, h, hP, h22⟩ := hx
  refine ⟨isUpUni_map f h0 h1 h11, isUpUni_map f h0 h1 h33, ?_, ?_, ?_, h.map f, hPP h hP, ?_⟩
  · show (b21 x).map f = 0
    rw [h21, Matrix.map_zero f h0]
  · show (b31 x).map f = 0
    rw [h31, Matrix.map_zero f h0]
  · show (b32 x).map f = 0
    rw [h32, Matrix.map_zero f h0]
  · show (b22 x).map f = midEmb (h.map f)
    rw [h22, midEmb_map f h0 h1]

variable [Nontrivial B] (π : A →+* B) (hπ : Function.Surjective π)

theorem parG_map_glRed {P : Matrix (Fin k) (Fin k) A → Prop} {P' : Matrix (Fin k) (Fin k) B → Prop}
    (hP : GP P) (hP' : GP P') (hPP : ∀ h, P h → P' (h.map π))
    (hlift : ∀ h, P' h → P (h.map (lift π hπ))) :
    (parG (r := r) hP).map (glRed π) = parG (r := r) hP' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Par P' ((glRed π x : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
    rw [glRed_coe]
    exact par_map π (map_zero π) (map_one π) hPP hx
  · intro hy
    have hy' : Par P' (y : Matrix (Idx r k) (Idx r k) B) := hy
    have hx : Par P ((y : Matrix (Idx r k) (Idx r k) B).map (lift π hπ)) :=
      par_map _ (lift_zero π hπ) (lift_one π hπ) hlift hy'
    refine ⟨Matrix.GeneralLinearGroup.mk'' _ (par_det hP hx), hx, ?_⟩
    apply Units.ext
    rw [glRed_coe]
    exact map_lift π hπ _


end Par

theorem sG_map_glRed {A B : Type} [CommRing A] [IsLocalRing A] [Field B] {r k : ℕ} (π : A →+* B)
    (hπ : Function.Surjective π) : (sG A r k).map (glRed π) = sG B r k := by
  refine parG_map_glRed π hπ _ _ (fun h hh => ?_) (fun h hh => ?_)
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map π
  · refine isUnit_of_map π hπ _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_lift π hπ]
    exact hh

section Grp

theorem map_conj {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G) (c : G) :
    (H.map (MulAut.conj c).toMonoidHom).map f = (H.map f).map (MulAut.conj (f c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

variable {K Q : Type} [Group K] [Group Q] (ρ : K →* Q) (S' : Subgroup K)

theorem map_sup_ker : (S' ⊔ ρ.ker).map ρ = S'.map ρ := by
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff ρ.ker).2 le_rfl, sup_bot_eq]

theorem mem_sup_ker {x : K} : x ∈ S' ⊔ ρ.ker ↔ ∃ s ∈ S', ∃ κ ∈ ρ.ker, s * κ = x := by
  first
    | exact Subgroup.mem_sup_of_normal_right
    | exact Subgroup.mem_sup_of_normal_right (s := S') (t := ρ.ker)

theorem map_eq_conj (ψ : K →* Q) (hψ : Function.Surjective ψ) (S' : Subgroup K) (H : Subgroup Q) (c : Q)
    (h : ∀ x, x ∈ S' ↔ c⁻¹ * ψ x * c ∈ H) : S'.map ψ = H.map (MulAut.conj c).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c⁻¹ * ψ x * c, (h x).1 hx, by group⟩
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨x, hx⟩ := hψ (c * h' * c⁻¹)
    refine ⟨x, (h x).2 ?_, hx⟩
    have e : c⁻¹ * (c * h' * c⁻¹) * c = h' := by group
    rw [hx, e]
    exact hh'

end Grp

end MassDataIdxStImB
end
end
