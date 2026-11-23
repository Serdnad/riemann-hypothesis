module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  · intro h a b
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h a) b)

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conjBy_comp {C D E : Type} [CommRing C] [Group D] [Group E] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C))
    (f : E →* D) : (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy_app, map_inv, map_mul]
  group

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

theorem UpperTheory.V.UnitaryThreeInertia.cond_conj :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (h : GL (Fin 3) R), InHat h →
      (∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r)) ∧
        ∀ r : Γ →* GG (m := 3) (R := R), F.Cond r → F.Cond (conjBy h r) := by
  intro O _ _ G Γ ι _ _ F R _ _ _ h hh
  have hmul : ∀ h' : GL (Fin 3) R, InHat h' → InHat (h * h') := fun h' hh' => by
    refine (congOne_iff _ _).2 ?_
    rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 hh', mul_one]
  have hloc : ∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r) := by
    intro v r ⟨ht, hd, hu⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e s hs => ?_⟩
    · obtain ⟨h', h1, h2, h3⟩ := ht e
      refine ⟨h * h', hmul h' h1, ?_, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
    · obtain ⟨h', h1, ⟨h2, h3⟩, h4⟩ := hd e
      refine ⟨h * h', hmul h' h1, ⟨?_, ?_⟩, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
      · rw [conjBy_conjBy]; exact h4
    · rw [conjBy_app, hu e s hs, mul_one, mul_inv_cancel]
  refine ⟨hloc, fun r hr => ⟨⟨fun g => ?_, fun g => ?_⟩, fun v => ?_⟩⟩
  · have e := congrArg SemidirectProduct.right (map_conjBy _ h hh r g)
    rw [GG.map_right, GG.map_right] at e
    exact e.trans (hr.mult g)
  · have e := congrArg GG.mat (map_conjBy _ h hh r g)
    rw [GG.map_mat, GG.map_mat] at e
    rw [entIn_sub_iff, e, ← entIn_sub_iff]
    exact hr.red g
  · rw [conjBy_comp]
    exact hloc v _ (hr.loc v)
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_diagonal_rep_matrix_eq {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (GG.map (algebraMap O R) (r0 η Ψ g)).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
  rw [GG.map_mat]
  show ((tor O (Ψ g)).val).map (algebraMap O R) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem conjBy_inv_one {R D : Type} [CommRing R] [Group D] (r : D →* @UpperTheory.V.U3.GG 3 R _) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

private theorem diagIn_one {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* @UpperTheory.V.U3.GG 3 R _)
    (hr : ∀ g, (r g).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g)) : DiagIn η Ψ I r 1 := by
  have hne : ∀ a b : Fin 3, wt a b ≠ 0 → a ≠ b := by
    intro a b h hab
    subst hab
    simp [wt] at h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne)
  · intro s _ _ a
    rw [conjBy_inv_one, hr, Matrix.diagonal_apply_eq]
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne')

theorem UpperTheory.V.UnitaryThreeInertia.isPt_rz :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)], F.IsPt g₁ (F.rz R) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hok g₁ R _ _ _ _
  have hmat : ∀ g, (F.rz R g).mat = diagonal fun a => algebraMap O R (psi F.Ψ a g) :=
    fun g => map_diagonal_rep_matrix_eq F.η F.Ψ g
  have hinhat : InHat (1 : GL (Fin 3) R) := by
    intro a b
    simp
  have hloc : ∀ v, ∀ s, ((F.rz R).comp (F.loc v) s).mat =
      diagonal fun a => algebraMap O R (psi (F.Ψv v) a s) := fun v s => hmat _
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro g
    rfl
  · intro g a b
    have e : (F.rz R g).mat = (r0 F.η F.Ψ g).mat.map (algebraMap O R) := GG.map_mat _ _
    rw [e, sub_self, Matrix.zero_apply]
    exact zero_mem _
  · intro v
    refine ⟨fun _ => ⟨1, hinhat, (diagIn_one _ _ _ _ (hloc v)).toTriIn⟩,
      fun _ => ⟨1, hinhat, diagIn_one _ _ _ _ (hloc v)⟩, fun hv s hs => ?_⟩
    have h1 : F.Ψ (F.loc v s) = 1 := hok.teich v hv s hs
    have h2 : F.η (F.loc v s) = 1 := hs.1.2
    show GG.map (algebraMap O R) (r0 F.η F.Ψ (F.loc v s)) = 1
    have e : r0 F.η F.Ψ (F.loc v s) = 1 := by
      apply SemidirectProduct.ext
      · rw [unitaryThreeReflection_left, h1, map_one]
        rfl
      · exact h2
    rw [e, map_one]
  · have hc : ∀ a, psi F.Ψ a F.c = 1 := by
      intro a
      simp [psi, hok.Ψc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmat]
      simp [hc, Matrix.diagonal_one]
    · simp [zmat, hmat]
    · simp [zmat, hmat]
  · intro n
    have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit (algebraMap O R) x hx)) n
    have key : ∀ g g', Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g : O) =
        Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g' : O) → ∀ a,
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g)) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g')) := by
      intro g g' h a
      let q : O →* O ⧸ maximalIdeal O ^ n := (Ideal.Quotient.mk (maximalIdeal O ^ n) : O →* O ⧸ maximalIdeal O ^ n)
      have hu : Units.map q (F.Ψ g) = Units.map q (F.Ψ g') := Units.ext h
      have h2 : ((Units.map q (F.Ψ g ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) =
          ((Units.map q (F.Ψ g' ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) := by
        rw [map_zpow (Units.map q) (F.Ψ g) (wt1 a), map_zpow (Units.map q) (F.Ψ g') (wt1 a), hu]
      have h3 : Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g) =
          Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g') := h2
      rw [Ideal.Quotient.eq] at h3 ⊢
      rw [← map_sub]
      exact hle (Ideal.mem_map_of_mem _ h3)
    have hf := hok.Ψ_cont n
    rw [IsLocallyConstant.iff_exists_open] at hf ⊢
    intro x
    obtain ⟨U, hU, hxU, hUx⟩ := hf x
    refine ⟨U, hU, hxU, fun x' hx' => ?_⟩
    simp only [hmat]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact key x' x (hUx x' hx') a
end
