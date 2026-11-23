module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp only [GG.map, GG.ofGL, SemidirectProduct.map_inl]

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply,
    map_mul, map_inv, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]
  simp [GG.mat, GG.map, SemidirectProduct.map_left]

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨?_, ?_⟩
  · intro g hg a b hab
    rw [conj_push_mat, H.tri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, H.ine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨triIn_push φ H.toTriIn, ?_⟩
  intro g hg a b hab
  rw [conj_push_mat, H.low g hg a b hab, map_zero]

variable [IsLocalRing O] [IsCO O R] [IsCO O R']

private theorem inHat_push (φ : R →ₐ[O] R') {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  have hm : ∀ x ∈ maximalIdeal R, φ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  unfold InHat CongOne EntIn at H ⊢
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    by_cases hab : a = b <;> simp [Matrix.sub_apply, hab]
  rw [e]
  exact hm _ (H a b)

end SlopeTestRemainingChoices

theorem UpperTheory.locAt_push_of_locAt :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (φ : R →ₐ[O] R') (v : ι) (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (((GG.map (φ : R →+* R')).comp r)) := by
  intro O _ _ G Γ ι _ _ F R R' _ _ _ _ _ _ φ v r hr
  unfold Frame.LocAt at hr ⊢
  obtain ⟨hT, hD, hU⟩ := hr
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨h, hh, ht⟩ := hT hv
    exact ⟨_, inHat_push φ hh, triIn_push φ ht⟩
  · obtain ⟨h, hh, ht⟩ := hD hv
    exact ⟨_, inHat_push φ hh, diagIn_push φ ht⟩
  · intro s hs
    have h1 := hU hv s hs
    simp only [MonoidHom.comp_apply, h1, map_one]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition {O M : Type} [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    [Finite M] (hM : ∀ a ∈ maximalIdeal O, ∀ x : M, a • x = 0) :
    ∃ (n : ℕ) (p : Fin n → M →ₗ[O] ResidueField O) (q : Fin n → ResidueField O →ₗ[O] M),
      ∀ x, ∑ i, q i (p i x) = x := by
  have hT : Module.IsTorsionBySet O M (maximalIdeal O) := fun x a => hM a.1 a.2 x
  letI : Module (ResidueField O) M := hT.module
  haveI : IsScalarTower O (ResidueField O) M := hT.isScalarTower
  haveI : Module.Finite (ResidueField O) M := Module.Finite.of_finite
  let B := Module.finBasis (ResidueField O) M
  refine ⟨_, fun i => (B.coord i).restrictScalars O,
    fun i => (LinearMap.toSpanSingleton (ResidueField O) M (B i)).restrictScalars O, fun x => ?_⟩
  simpa using B.sum_repr x

private theorem UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (X : Matrix (Fin 3) (Fin 3) S) (a b : Fin 3) :
    adRep (r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ)) g X a b =
      ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then X a b else -X b.rev a.rev) := by
  rw [adRep_baseLift_apply, Algebra.smul_def, MonoidHom.comp_apply, ← map_zpow]
  rfl

private theorem UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) :
    (GG.map (algebraMap O S)).comp (r0 η Ψ) = r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ) := by
  ext g i j
  · simp [r0, GG.map]
    rw [tor_val, tor_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [← map_zpow, ← map_zpow, Units.coe_map, map_zpow]
      rfl
    · simp
  · simp [r0, GG.map]

private theorem UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary {k D : Type} [CommRing k] [Group D] [TopologicalSpace D]
    (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (h : Subsingleton (H2 (gRep η Ψ j)))
    (κ : D × D → Matrix (Fin 3) (Fin 3) k) (hc : IsLocallyConstant κ) (hw : ∀ z, κ z ∈ gw k j)
    (hκ : ∀ g h l, adRep (r0 η Ψ) g (κ (h, l)) - κ (g * h, l) + κ (g, h * l) - κ (g, h) = 0) :
    ∃ b : D → Matrix (Fin 3) (Fin 3) k, IsLocallyConstant b ∧ (∀ g, b g ∈ gw k j) ∧
      ∀ g h, κ (g, h) = adRep (r0 η Ψ) g (b h) - b (g * h) + b g := by
  let f : D × D → Gb (k := k) j := fun z => (⟨κ z, hw z⟩ : ↥(gw k j))
  have hfl : IsLocallyConstant f :=
    IsLocallyConstant.desc f (fun x : Gb (k := k) j => (x.val : Matrix (Fin 3) (Fin 3) k)) hc
      (fun x y hxy => Subtype.ext hxy)
  have hf : f ∈ Z2 (gRep η Ψ j) := by
    refine (mem_cocycles2 _ _).2 ⟨hfl.continuous, fun g h l => ?_⟩
    apply Subtype.ext
    exact hκ g h l
  have h0 : (Submodule.Quotient.mk ⟨f, hf⟩ : H2 (gRep η Ψ j)) = 0 := Subsingleton.elim _ _
  have hB : f ∈ B2 (gRep η Ψ j) := by
    have := (Submodule.Quotient.mk_eq_zero ((B2 (gRep η Ψ j)).comap (Z2 (gRep η Ψ j)).subtype)
      (x := ⟨f, hf⟩)).1 h0
    simpa using this
  obtain ⟨c, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  refine ⟨fun g => (c g).val, ((IsLocallyConstant.iff_continuous c).2 hcc).comp _,
    fun g => (c g).2, fun g h => ?_⟩
  have e := congrArg (fun x : Gb (k := k) j => x.val) (congrFun hd (g, h))
  rw [d1_apply] at e
  exact e.symm

theorem UpperTheory.V.UnitaryThreeInertia.lifting_obstruction_second_cohomology :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ κ : D × D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant κ → (∀ z, κ z ∈ gw R j) → (∀ z, EntIn K (κ z)) →
      (∀ g h k, adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (κ (h, k)) - κ (g * h, k) + κ (g, h * k) - κ (g, h) = 0) →
      ∃ b : D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant b ∧ (∀ g, b g ∈ gw R j) ∧ (∀ g, EntIn K (b g)) ∧
        ∀ g h, κ (g, h) = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (b h) - b (g * h) + b g := by
  classical
  intro O R D _ _ _ _ _ _ _ _ η Ψ K j hK hH κ hc hw hE hκ
  have memgw : ∀ (S : Type) [CommRing S] (X : Matrix (Fin 3) (Fin 3) S),
      X ∈ gw S j ↔ ∀ a b, ¬ wt a b = j → X a b = 0 := by
    intro S _ X
    unfold gw
    rfl
  have hloc : IsLocalHom (algebraMap O R) := by
    obtain ⟨_, hl, _⟩ := ‹IsCO O R›
    exact hl
  let KO : Submodule O R := K.restrictScalars O
  have hM : ∀ a ∈ maximalIdeal O, ∀ x : KO, a • x = 0 := by
    intro a ha x
    apply Subtype.ext
    have h1 : algebraMap O R a ∈ maximalIdeal R := map_nonunit (algebraMap O R) a ha
    have h2 : algebraMap O R a * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul h1 x.2
    rw [hK] at h2
    simpa [Algebra.smul_def] using h2
  obtain ⟨n, p, q, hpq⟩ := UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition hM
  rw [UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra] at hκ ⊢
  have hE' : ∀ z a b, κ z a b ∈ KO := fun z a b => hE z a b
  let κK : D × D → Fin 3 → Fin 3 → KO := fun z a b => ⟨κ z a b, hE' z a b⟩
  have hres : (Units.map (residue O).toMonoidHom).comp Ψ =
      (Units.map (algebraMap O (ResidueField O)).toMonoidHom).comp Ψ := rfl
  have key : ∀ i, ∃ b : D → Matrix (Fin 3) (Fin 3) (ResidueField O), IsLocallyConstant b ∧
      (∀ g, b g ∈ gw (ResidueField O) j) ∧ ∀ g h, Matrix.of (fun a c => p i (κK (g, h) a c)) =
        adRep (r0 η ((Units.map (residue O).toMonoidHom).comp Ψ)) g (b h) - b (g * h) + b g := by
    intro i
    refine UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary η ((Units.map (residue O).toMonoidHom).comp Ψ) j hH
      (fun z => Matrix.of (fun a c => p i (κK z a c))) ?_ ?_ ?_
    · let G : Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) (ResidueField O) :=
        fun X => Matrix.of fun a c => if h : X a c ∈ KO then p i ⟨X a c, h⟩ else 0
      have hG : (fun z => Matrix.of (fun a c => p i (κK z a c))) = G ∘ κ := by
        funext z
        ext a c
        simp [G, κK, hE' z a c]
      rw [hG]
      exact hc.comp G
    · intro z
      rw [memgw]
      intro a c hac
      have h0 : κK z a c = 0 := Subtype.ext ((memgw R (κ z)).1 (hw z) a c hac)
      simp [h0]
    · intro g h l
      ext a c
      have e := congrFun (congrFun (hκ g h l) a) c
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, Matrix.of_apply] at e ⊢
      rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] at e
      rw [hres, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
      have eK : ((Ψ g ^ wt a c : Oˣ) : O) • (if η g = 1 then κK (h, l) a c else -κK (h, l) c.rev a.rev) -
          κK (g * h, l) a c + κK (g, h * l) a c - κK (g, h) a c = 0 := by
        apply Subtype.ext
        split_ifs at e ⊢ <;> simpa [κK] using e
      have e2 := congrArg (p i) eK
      split_ifs at e2 ⊢ <;> simpa using e2
  choose bs hbl hbw hbe using key
  refine ⟨fun g => Matrix.of fun a c => ((∑ i, q i (bs i g a c) : KO) : R), ?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Filter.eventually_all.2 (fun i => (hbl i).eventually_eq x)] with y hy
    simp only [hy]
  · intro g
    rw [memgw]
    intro a c hac
    have h0 : ∀ i, bs i g a c = 0 := fun i => (memgw _ _).1 (hbw i g) a c hac
    simp [h0]
  · intro g
    unfold EntIn
    intro a c
    exact (∑ i, q i (bs i g a c)).2
  · intro g h
    ext a c
    have e : ∀ i, p i (κK (g, h) a c) = ((Ψ g ^ wt a c : Oˣ) : O) •
        (if η g = 1 then bs i h a c else -bs i h c.rev a.rev) - bs i (g * h) a c + bs i g a c := by
      intro i
      have e1 := congrFun (congrFun (hbe i g h) a) c
      rw [hres] at e1
      simpa only [Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] using e1
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
    simp only [Matrix.of_apply]
    have hx : κ (g, h) a c = ((κK (g, h) a c : KO) : R) := rfl
    rw [hx, ← hpq (κK (g, h) a c)]
    simp_rw [e]
    split_ifs <;> simp [map_add (f := _), map_sub, map_neg, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {m : Ideal R}

private def Kil (m : Ideal R) (X : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, ∀ x ∈ m, x * X a b = 0

private theorem kil_left {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : M * X = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => hX c b _ (hM a c)

private theorem kil_right {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : X * M = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact hX a c _ (hM c b)

private theorem ent_left {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (N * M) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hM c b)

private theorem ent_right {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hM a c)

private theorem core {h hi A D Y γ : Matrix (Fin 3) (Fin 3) R} (hh : EntIn m (h - 1)) (hhi : EntIn m (hi - 1))
    (hA : EntIn m (A - D)) (hY : Kil m Y) (hYm : EntIn m Y) (hγ : Kil m γ) :
    hi * (1 + Y) * ((1 + γ) * A) * ((1 - Y) * h) = hi * A * h + (Y * D + γ * D - D * Y) := by
  obtain ⟨p, rfl⟩ : ∃ p, h = 1 + p := ⟨h - 1, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, hi = 1 + q := ⟨hi - 1, by abel⟩
  obtain ⟨e, rfl⟩ : ∃ e, A = D + e := ⟨A - D, by abel⟩
  simp only [add_sub_cancel_left] at hh hhi hA
  have e1 : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) := by
    have a1 : Y * γ = 0 := kil_left hγ hYm
    have a2 : Y * e = 0 := kil_right hY hA
    have a3 : γ * e = 0 := kil_right hγ hA
    have a4 : e * Y = 0 := kil_left hY hA
    have a5 : Y * (D * Y) = 0 := kil_right hY (ent_left _ hYm)
    have a6 : γ * (D * Y) = 0 := kil_right hγ (ent_left _ hYm)
    have : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) +
        ((Y * γ) * (D + e) * (1 - Y) + (Y * e) * (1 - Y) + (γ * e) * (1 - Y) - e * Y - Y * (D * Y) - γ * (D * Y)) := by
      noncomm_ring
    rw [this, a1, a2, a3, a4, a5, a6]; simp
  have hW : Kil m (Y * D + γ * D - D * Y) := fun a b x hx => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, mul_sub, mul_add, Finset.mul_sum,
      ← mul_assoc, hY _ _ x hx, hγ _ _ x hx, zero_mul, hY _ _ _ (Ideal.mul_mem_right _ _ hx)]
    simp
  generalize Y * D + γ * D - D * Y = W at e1 hW
  have b1 : q * W = 0 := kil_left hW hhi
  have b2 : W * p = 0 := kil_right hW hh
  calc _ = (1 + q) * ((1 + Y) * ((1 + γ) * (D + e)) * (1 - Y)) * (1 + p) := by simp only [Matrix.mul_assoc]
    _ = (1 + q) * (D + e) * (1 + p) + W + ((q * W) * (1 + p) + W * p) := by rw [e1]; noncomm_ring
    _ = _ := by rw [b1, b2]; simp

private theorem conj_mat {D : Type} [Group D] (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem ad_entry {D k : Type} [Group D] [CommRing k] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (hg : η g = 1)
    (X : Matrix (Fin 3) (Fin 3) k) (a b : Fin 3) :
    adRep (r0 η Ψ) g X a b * ((Ψ g ^ wt1 b : kˣ) : k) = ((Ψ g ^ wt1 a : kˣ) : k) * X a b := by
  show (GG.adFun (r0 η Ψ g) X) a b * _ = _
  unfold GG.adFun GG.mat
  rw [unitaryThreeReflection_left, ← map_inv, tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul, unitaryThreeReflection_right, if_pos hg,
    mul_assoc, ← Units.val_mul, ← mul_zpow]
  simp

private theorem condT_deform {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [Algebra O R] [IsCO O R]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (f : R) (hf : ∀ x ∈ maximalIdeal R, x * f = 0)
    (hfm : f ∈ maximalIdeal R) (r r₂ : D →* GG (m := 3) (R := R)) (z : D → Matrix (Fin 3) (Fin 3) (ResidueField O))
    (γ : D → Matrix (Fin 3) (Fin 3) R) (hr : Red η Ψ r) (ht : CondT η Ψ I r)
    (hγ : ∀ g a b, ∃ o : O, residue O o = z g a b ∧ γ g a b = o • f) (hd : IsDeform r γ r₂)
    (μ : Matrix (Fin 3) (Fin 3) (ResidueField O))
    (h1 : ∀ g, η g = 1 → ∀ a b, wt a b < 0 →
      μ a b * residue O (psi Ψ b g) + z g a b * residue O (psi Ψ b g) - residue O (psi Ψ a g) * μ a b = 0)
    (h2 : ∀ s ∈ I, ∀ a, z s a a = 0) : CondT η Ψ I r₂ := by
  obtain ⟨h, hh, htri, hine⟩ := ht
  have hk : ∀ o : O, ∀ x ∈ maximalIdeal R, x * (o • f) = 0 := fun o x hx => by
    rw [mul_smul_comm, hf x hx, smul_zero]
  have h0 : ∀ o : O, residue O o = 0 → o • f = 0 := fun o ho => by
    rw [Algebra.smul_def]
    exact hf _ (map_nonunit (algebraMap O R) o ((residue_eq_zero_iff _).1 ho))
  choose o ho using fun a b => residue_surjective (μ a b)
  let Y : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a b => o a b • f
  have hY : Kil (maximalIdeal R) Y := fun a b => hk _
  have hYm : EntIn (maximalIdeal R) Y := fun a b => Submodule.smul_of_tower_mem _ _ hfm
  have hYY : Y * Y = 0 := kil_left hY hYm
  let u : GL (Fin 3) R := ⟨1 - Y, 1 + Y,
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩
  have hhi : EntIn (maximalIdeal R) (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1) := by
    have := ent_left (-((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) hh
    rwa [Matrix.mul_sub, Matrix.neg_mul, Units.inv_mul, Matrix.mul_one, sub_neg_eq_add, neg_add_eq_sub] at this
  have key : ∀ g, η g = 1 → ∀ a b, ∃ c : O, residue O c = z g a b ∧ (conjBy (u * h)⁻¹ r₂ g).mat a b =
      (conjBy h⁻¹ r g).mat a b + (o a b * psi Ψ b g + c * psi Ψ b g - psi Ψ a g * o a b) • f := by
    intro g hg a b
    obtain ⟨c, hc, hc'⟩ := hγ g a b
    refine ⟨c, hc, ?_⟩
    have hrg : (r g).right = 1 := (hr.mult g).trans hg
    have hγk : Kil (maximalIdeal R) (γ g) := fun a b => by
      obtain ⟨c, -, hc'⟩ := hγ g a b
      rw [hc']; exact hk c
    have hD : ((r0 η Ψ g).mat).map (algebraMap O R) = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
      unfold GG.mat
      rw [unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
      rfl
    have hA := hr.red g
    rw [hD] at hA
    have := core hh hhi hA hY hYm hγk
    rw [conj_mat _ _ _ hrg, conj_mat _ _ _ ((hd g).1.trans hrg), (hd g).2, _root_.mul_inv_rev, Units.val_mul,
      Units.val_mul]
    refine (congrFun (congrFun this a) b).trans ?_
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hc', Y,
      Matrix.of_apply, Algebra.smul_def, map_sub, map_add, map_mul]
    ring
  refine ⟨u * h, ?_, fun g hg a b hab => ?_, fun s hs hη a => ?_⟩
  · have e : ((u * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1 = ((h : Matrix (Fin 3) (Fin 3) R) - 1) - Y * h := by
      show (1 - Y) * (h : Matrix (Fin 3) (Fin 3) R) - 1 = _
      noncomm_ring
    intro a b
    rw [e, Matrix.sub_apply]
    exact Ideal.sub_mem _ (hh a b) (ent_right _ hYm a b)
  · obtain ⟨c, hc, e⟩ := key g hg a b
    rw [e, htri g hg a b hab, zero_add]
    apply h0
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, ho, hc]
    exact h1 g hg a b hab
  · obtain ⟨c, hc, e⟩ := key s hη a a
    rw [e, hine s hs hη a, h0, add_zero]
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, hc, h2 s hs a]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.triangular_condition_at_l_of_first_order_deformation :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v = F.vl →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R _ _ _ f hf hfm j v hv r r₂ z γ hr hl hz hγ hd
  refine ⟨fun _ => ?_, fun h => absurd (hv ▸ h) hF.vl_notMem, fun h => absurd (Set.mem_insert_iff.2 (Or.inl hv)) h⟩
  have hw : ∀ (X : Gb (k := ResidueField O) j) a b, wt a b ≠ j → X.val a b = 0 := fun X => Subtype.property X
  have h2 : ∀ s ∈ F.Iv v, ∀ a, (z s).val a a = 0 := fun s hs a => by
    by_cases hj : j = 0
    · rw [hz.2.2.2 hv hj s hs]; rfl
    · exact hw _ _ _ (by simpa [wt] using Ne.symm hj)
  by_cases hj : j < 0
  · obtain ⟨μ, hμ⟩ := (mem_coboundaries1 _ _).1 (hz.2.2.1 hv hj)
    refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd μ.val ?_ h2
    intro g hg a b _
    have e : (z g).val a b = adRep (r0 F.η F.Ψbar) (F.loc v g) μ.val a b - μ.val a b := by
      rw [hμ g]; rfl
    have hp : ∀ a, residue O (psi (F.Ψv v) a g) = ((F.Ψbar (F.loc v g) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O) :=
      fun a => by
        show _ = ((Units.map (residue O).toMonoidHom (F.Ψ (F.loc v g)) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O)
        rw [← map_zpow]; rfl
    have := ad_entry F.η F.Ψbar (F.loc v g) hg μ.val a b
    simp only [e, hp]
    linear_combination this
  · refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd 0 ?_ h2
    intro g _ a b hab
    simp [hw (z g) a b (by omega)]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.locAt_deform_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v ∉ F.Tb →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j)
        (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F _ _ R _ _ _ f hf _ j v hv r r₂ z γ _ hr hz hγ hd
  have hvl : v ≠ F.vl := fun h => hv (h ▸ Set.mem_insert _ _)
  refine ⟨fun h => absurd h hvl, fun h => absurd (Set.mem_insert_of_mem _ h) hv, fun _ s hs => ?_⟩
  have h1 : r s = 1 := hr.2.2 hv s hs
  have hz0 : z s = 0 := hz.2.1 hvl s hs
  have hγ0 : γ s = 0 := by
    ext a b
    obtain ⟨o, ho, e⟩ := hγ s a b
    rw [hz0] at ho
    have ho' : o ∈ maximalIdeal O := (residue_eq_zero_iff o).1 ho
    have hm : algebraMap O R o ∈ maximalIdeal R := fun h => ho' (IsLocalHom.map_nonunit o h)
    rw [e, Algebra.smul_def]
    exact hf _ hm
  obtain ⟨e1, e2⟩ := hd s
  rw [h1] at e1
  rw [h1, hγ0, add_zero, one_mul] at e2
  exact SemidirectProduct.ext (Units.ext e2) e1
end
