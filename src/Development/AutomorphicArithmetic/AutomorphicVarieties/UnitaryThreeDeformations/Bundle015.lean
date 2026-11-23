module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Mathlib.NumberTheory.Padics.Complex
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
end

section

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rigDiag_fst_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem rigDiag_snd_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib]

private theorem rigDiag_conj_mat {R D : Type} [CommRing R] [Group D] (h : GL (Fin 3) R)
    (r : D →* GG (m := 3) (R := R)) (s : D)
    (hs : (r s).right = 1) :
    (h : Matrix (Fin 3) (Fin 3) R) * (conjBy h⁻¹ r s).mat = (r s).mat * h := by
  simp [conjBy, GG.mat, GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hs]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units h), Matrix.one_mul]

theorem UpperTheory.V.UnitaryThreeInertia.rig_diag :
    ∀ {O K D : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := K))
      (y : D → Matrix (Fin 3) (Fin 3) K) (r' : D →* GG (m := 3) (R := DualNumber K))
      (h : GL (Fin 3) (DualNumber K)),
      (∀ s ∈ I, η s = 1) → HasMult η r →
      IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
        (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' →
      DiagIn η Ψ I r' h → ∃ X, ∀ s ∈ I, y s = adRep r s X - X := by
  intro O K D _ _ _ _ _ η Ψ I r y r' h hI hm hd hD
  set H : Matrix (Fin 3) (Fin 3) (DualNumber K) := (h : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hH
  set Hi : Matrix (Fin 3) (Fin 3) (DualNumber K) := (↑h⁻¹ : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hHi
  refine ⟨-(H.map TrivSqZeroExt.snd * Hi.map TrivSqZeroExt.fst), fun s hs => ?_⟩
  have hη : η s = 1 := hI s hs
  have hr1 : (r s).right = 1 := (hm s).trans hη
  have hd1 := hd s
  have hr'1 : (r' s).right = 1 := by
    rw [hd1.1]
    simpa [GG.map] using hr1
  have hmat : (r' s).mat = (1 + (y s).map TrivSqZeroExt.inr) * (r s).mat.map (algebraMap K (DualNumber K)) := by
    rw [hd1.2]
    simp [GG.map, GG.mat]
  have hker : s ∈ η.ker := hη
  have hoff : ∀ a b, ((conjBy h⁻¹ r' s).mat a b).snd = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hD.ine s hs hη a]
      rfl
    · rcases lt_or_gt_of_ne (show wt a b ≠ 0 by revert a b; decide) with hlt | hlt
      · rw [hD.tri s hker a b hlt]
        rfl
      · rw [hD.low s hker a b hlt]
        rfl
  set C := (conjBy h⁻¹ r' s).mat with hC
  set R := (r s).mat with hR
  set h0 := H.map TrivSqZeroExt.fst
  set h1 := H.map TrivSqZeroExt.snd
  set g0 := Hi.map TrivSqZeroExt.fst
  set C0 := C.map TrivSqZeroExt.fst
  have hc : H * C = (r' s).mat * H := rigDiag_conj_mat h r' s hr'1
  have hCs : C.map TrivSqZeroExt.snd = 0 := by
    ext a b
    exact hoff a b
  have hM0 : (r' s).mat.map TrivSqZeroExt.fst = R := by
    rw [hmat, rigDiag_fst_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, ite_mul]
  have hM1 : (r' s).mat.map TrivSqZeroExt.snd = y s * R := by
    rw [hmat, rigDiag_snd_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl,
      apply_ite TrivSqZeroExt.fst, apply_ite TrivSqZeroExt.snd]
  have e0 : h0 * C0 = R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hc
    simpa only [rigDiag_fst_mul, hM0] using this
  have e1 : h1 * C0 = R * h1 + y s * R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.snd) hc
    simp only [rigDiag_snd_mul, hM0, hM1, hCs, Matrix.mul_zero, zero_add] at this
    exact this
  have hinv1 : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv2 : H * Hi = 1 := by
    rw [hHi, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgh : g0 * h0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv1
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hhg : h0 * g0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv2
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hRR : R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hR, GG.mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : C0 = g0 * R * h0 := by
    rw [← one_mul C0, ← hgh, mul_assoc, e0, ← mul_assoc]
  have e3 : y s * R = h1 * g0 * R - R * (h1 * g0) := by
    have k : y s * R * h0 = h1 * C0 - R * h1 := by
      rw [e1]
      abel
    calc y s * R = y s * R * h0 * g0 := by rw [mul_assoc (y s * R), hhg, mul_one]
      _ = (h1 * C0 - R * h1) * g0 := by rw [k]
      _ = h1 * g0 * R - R * (h1 * g0) := by
        rw [e2]
        simp only [sub_mul, mul_assoc, hhg, mul_one]
  have e4 : y s = y s * R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_assoc, hRR, mul_one]
  rw [e4, e3]
  simp only [adRep, GG.ad, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, GG.adFun, hr1, ite_true]
  rw [← hR]
  simp only [sub_mul, mul_assoc, hRR, mul_one, mul_neg, neg_mul, sub_neg_eq_add]
  abel
end

section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut

namespace UpperTheory.V.UnitaryThreeInertia

def HostVanE : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  F.VanE

def HostXpp : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ q : ℕ, XData l ψ q → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  F.Xpp

end UpperTheory.V.UnitaryThreeInertia

end
end

section

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (a : n) (h1 : ∀ i j, ‖A i j‖ ≤ 1) (h2 : ∀ j, ‖A a j‖ < 1) :
    ‖A.det‖ < 1 := by
  rw [Matrix.det_apply']
  obtain ⟨σ, -, hσ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm n))
    (fun τ : Equiv.Perm n => (((Equiv.Perm.sign τ : ℤ) : K)) * ∏ i, A (τ i) i)
  refine lt_of_le_of_lt hσ ?_
  show ‖(((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, A (σ i) i‖ < 1
  have hs : ‖(((Equiv.Perm.sign σ : ℤ) : K))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, one_mul, norm_prod,
    ← Finset.mul_prod_erase Finset.univ (fun i => ‖A (σ i) i‖) (Finset.mem_univ (σ.symm a))]
  have hle : ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h1 _ _)
  have hlt : ‖A (σ (σ.symm a)) (σ.symm a)‖ < 1 := by
    rw [Equiv.apply_symm_apply]
    exact h2 _
  calc ‖A (σ (σ.symm a)) (σ.symm a)‖ * ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖
      ≤ ‖A (σ (σ.symm a)) (σ.symm a)‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ < 1 := by simpa using hlt

private theorem norm_le_one_of_det_smul_one_sub_eq_zero {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h1 : ∀ i j, ‖M i j‖ ≤ 1) (t : K)
    (ht : (t • (1 : Matrix n n K) - M).det = 0) : ‖t‖ ≤ 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
  rcases isEmpty_or_nonempty n with hn | hn
  · exact absurd (funext fun c => (IsEmpty.false c).elim) hv0
  obtain ⟨b, hb⟩ := Finite.exists_max (fun c => ‖v c‖)
  have hvb : v b ≠ 0 := by
    intro h0
    apply hv0
    funext c
    have := hb c
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow : t * v b = ∑ c, M b c * v c := by
    have := congrFun hv b
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq] at this
    linear_combination this
  have hbound : ‖t * v b‖ ≤ 1 * ‖v b‖ := by
    rw [hrow]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) (fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (h1 b c) (hb c) (norm_nonneg _) zero_le_one
  rw [norm_mul] at hbound
  exact le_of_mul_le_mul_right hbound (norm_pos_iff.mpr hvb)


theorem UpperTheory.V.UnitaryThreeInertia.rig_sep :
    ∀ {l : ℕ} [Fact l.Prime] (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) (d : Fin 3 → PadicAlgCl l) (P : GL (Fin 3) (PadicAlgCl l)), (∀ a b, ‖M a b - Matrix.diagonal d a b‖ < 1) → (∀ a, ‖d a‖ = 1) → (∀ a b, a ≠ b → ‖d a - d b‖ = 1) → (∀ i j, j < i → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i j = 0) → ∀ i j, i ≠ j → ∀ u : PadicAlgCl l, ‖u - 1‖ < 1 → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i i ≠ (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) j j * u := by
  intro l _ M d P hM hd hdd hT i j hij u hu
  set T := ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M *
    (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) with hTdef
  have hsub : ∀ x y : PadicAlgCl l, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hdet : ∀ x : PadicAlgCl l, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det =
      ∏ k, (x - T k k) := by
    intro x
    have h1 : ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
        (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) = x • 1 - T := by
      rw [hTdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Units.inv_mul]
    have h2 : (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
        ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have h3 : (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T).det =
        ∏ k, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T) k k := by
      apply Matrix.det_of_upperTriangular
      intro a b hab
      have hne : a ≠ b := (ne_of_lt hab).symm
      simp [Matrix.sub_apply, Matrix.one_apply, hne, hT a b hab]
    calc (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det
        = ((((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
          ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det) *
          (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det := by rw [h2, one_mul]
      _ = (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
          (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det := by
        rw [Matrix.det_mul, Matrix.det_mul]
        ring
      _ = ∏ k, (x - T k k) := by
        rw [h1, h3]
        simp [Matrix.sub_apply, Matrix.one_apply]
  have hM1 : ∀ a b, ‖M a b‖ ≤ 1 := by
    intro a b
    have hdg : ‖Matrix.diagonal d a b‖ ≤ 1 := by
      by_cases hab : a = b
      · subst hab
        simp [hd a]
      · simp [Matrix.diagonal_apply_ne _ hab]
    have := IsUltrametricDist.norm_add_le_max (M a b - Matrix.diagonal d a b) (Matrix.diagonal d a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM a b).le hdg)
  have ht1 : ∀ k, ‖T k k‖ ≤ 1 := fun k =>
    norm_le_one_of_det_smul_one_sub_eq_zero M hM1 (T k k) (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _))
  have ht2 : ∀ a, ∃ k, ‖d a - T k k‖ < 1 := by
    intro a
    have hsmall : ‖(d a • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det‖ < 1 := by
      apply norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one _ a
      · intro c b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        refine (hsub _ _).trans (max_le ?_ (hM1 c b))
        by_cases hcb : c = b
        · subst hcb
          simp [Matrix.one_apply_eq, hd a]
        · simp [Matrix.one_apply_ne hcb]
      · intro b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        by_cases hab : a = b
        · subst hab
          have := hM a a
          rw [Matrix.diagonal_apply_eq] at this
          rw [norm_sub_rev] at this
          simpa using this
        · have := hM a b
          rw [Matrix.diagonal_apply_ne _ hab, sub_zero] at this
          simpa [Matrix.one_apply_ne hab] using this
    rw [hdet, norm_prod, Fin.prod_univ_three] at hsmall
    by_contra hne
    push_neg at hne
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hne 0) (hne 1)) (hne 2)
    linarith
  choose φ hφ using ht2
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h := hdd a b hne
    have : ‖d a - d b‖ ≤ max ‖d a - T (φ a) (φ a)‖ ‖d b - T (φ a) (φ a)‖ := by
      have := hsub (d a - T (φ a) (φ a)) (d b - T (φ a) (φ a))
      simpa using this
    rw [hab] at this
    have := this.trans_lt (max_lt (hab ▸ hφ a) (hφ b))
    linarith
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨a, rfl⟩ := hsurj i
  obtain ⟨b, rfl⟩ := hsurj j
  have hab : a ≠ b := fun h => hij (h ▸ rfl)
  intro heq
  have hclose : ‖T (φ a) (φ a) - T (φ b) (φ b)‖ < 1 := by
    rw [heq, show T (φ b) (φ b) * u - T (φ b) (φ b) = T (φ b) (φ b) * (u - 1) by ring, norm_mul]
    calc ‖T (φ b) (φ b)‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (ht1 _) (norm_nonneg _)
      _ < 1 := by linarith
  have hsplit : d a - d b = (d a - T (φ a) (φ a)) +
      ((T (φ a) (φ a) - T (φ b) (φ b)) + (T (φ b) (φ b) - d b)) := by ring
  have h3 : ‖d a - d b‖ < 1 := by
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ a) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hclose ?_)
    rw [norm_sub_rev]
    exact hφ b
  have := hdd a b hab
  linarith
end
