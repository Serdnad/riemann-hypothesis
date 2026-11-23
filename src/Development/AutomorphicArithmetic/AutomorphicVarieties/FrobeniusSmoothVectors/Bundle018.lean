module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle012
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C} (hM : UpT M) (hN : UpT N) :
    UpT (M * N) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hM i c hc, zero_mul]
  · rw [hN c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

theorem UpperTheory.V.Fr.pr_correct :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (μ : ResidueField O →+ C'), IsSq O μ → (∀ c, p (μ c) = 0) → ∀ (β : F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) (Y : F.V → Matrix (Fin n) (Fin n) (ResidueField O)) (a : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)), IsLocallyConstant β → (∀ x, D.om x = (dOne (B.bar O).ad β x).map μ) → (∀ v s, D.a v s = (a v s).map μ) → (∀ v s, a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v)) ∈ (B.bar O).b v) → ∃ B' : Box F n C', B'.Cont (maximalIdeal C') ∧ B'.map (p : C' →+* C) = B ∧ ∀ s, (B'.r s).mat = (1 - (β s).map μ) * (D.r s : Matrix (Fin n) (Fin n) C') := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D μ hμ hpμ β Y a hβ hom ha hb
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O C' n μ hμ
  have hres : ∀ z : C', res O C (p z) = res O C' z := fun z => res_map p z
  let x : F.Γ → GG (m := n) (R := C') := fun s => SemidirectProduct.mk (D.r s) (F.del s)
  have hK1 : ∀ s, GG.map (res O C' : C' →+* ResidueField O) (x s) = (B.bar O).r s := by
    intro s
    apply SemidirectProduct.ext
    · ext i j
      simp [x, GG.map, Box.map, hres, ← D.r_map s]
    · simp [x, GG.map, Box.map, B.nu]
  have hdl : ∀ v (s : F.Gv v), F.del (F.loc v s) = 1 := fun v s => MonoidHom.mem_ker.1 (F.loc0 v s).2
  have hAd : ∀ v (s : F.Gv v) M, (B.bar O).ad (F.loc v s) M =
      (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C') * M *
        (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v s M
    show GG.adFun ((B.bar O).r (F.loc v s)) M = _
    rw [← hK1]
    clear hom ha hb he5 he4 he3 he2 he1 hβ hpμ hμ
    simp [GG.adFun, GG.mat, GG.map, x, hdl]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.coe_units_inv]
    calc (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') *
          (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C')
        = ((((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
            (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C')).map (res O C') :=
          (Matrix.map_mul (f := (res O C').toRingHom)).symm
      _ = 1 := by
          rw [Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxmul : ∀ s t, x s * x t = GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
    intro s t
    have hu : D.r s * sgnAct (m := n) (R := C') (F.del s) (D.r t) * (D.r (s * t))⁻¹ = e (dOne (B.bar O).ad β (s, t)) := by
      apply Units.ext
      rw [he1, ← hom (s, t)]
      simp [SetLift.om]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ← hu]
      simp [x]
    · simp [x]
  have hcomm : ∀ s X, x s * GG.ofGL (e X) = GG.ofGL (e ((B.bar O).ad s X)) * x s := by
    intro s X
    rw [he5 (x s) X, hK1 s]
    rfl
  let R' : F.Γ → GG (m := n) (R := C') := fun s => GG.ofGL (e (-β s)) * x s
  have hmul : ∀ s t, R' (s * t) = R' s * R' t := by
    intro s t
    symm
    calc R' s * R' t = GG.ofGL (e (-β s)) * (x s * GG.ofGL (e (-β t))) * x t := by
          simp only [R', mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) * (x s * x t) := by
          rw [hcomm]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) *
            GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [hxmul]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s + (B.bar O).ad s (-β t) + dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [he2, he2, map_mul, map_mul]
      _ = R' (s * t) := by
          simp only [R']
          congr 3
          simp only [dOne, map_neg]
          abel
  let rr : F.Γ →* GG (m := n) (R := C') := MonoidHom.mk' R' hmul
  have hneg : ∀ Z : Matrix (Fin n) (Fin n) (ResidueField O), (-Z).map μ = -(Z.map μ) := by
    intro Z
    ext i j
    simp
  have hpe : ∀ X, GeneralLinearGroup.map (p : C' →+* C) (e X) = 1 := by
    intro X
    ext i j
    simp only [GeneralLinearGroup.map_apply, he1, Matrix.add_apply, Matrix.map_apply, Units.val_one, map_add (f := _)]
    have h0 : (p : C' →+* C) (μ (X i j)) = 0 := hpμ _
    rw [h0, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∀ (A : GL (Fin n) C') X, A * e X * A⁻¹ =
      e ((A : Matrix (Fin n) (Fin n) C').map (res O C') * X * ((A⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
    intro A X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he1, mul_add, mul_one, add_mul, Units.mul_inv, (he4 _ X).1, (he4 _ _).2]
  have hGbar : ∀ v, ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) =
        (D.g v : Matrix (Fin n) (Fin n) C').map (res O C') ∧
      (((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) =
        (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v
    constructor
    · ext i j
      simp [Box.map, ← D.g_map v, hres]
    · ext i j
      simp [Box.map, ← D.g_map v, hres, ← map_inv]
  refine ⟨{ r := rr, nu := ?_, g := fun v => D.g v * e (-(Y v)), tri := ?_ }, ?_, ?_, ?_⟩
  · intro s
    show (GG.ofGL (e (-β s)) * x s).right = F.del s
    simp [x]
  · intro v s
    show UpT ((↑(D.g v * e (-(Y v))) : Matrix (Fin n) (Fin n) C') * (R' (F.loc v s)).mat *
      (((D.g v * e (-(Y v)))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C'))
    have hr : D.r (F.loc v s) = e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [← mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [he1, ← ha v s]
      simp [SetLift.a]
    have hmat : (R' (F.loc v s)).mat = ↑(e (-β (F.loc v s)) * D.r (F.loc v s)) := by
      simp [R', GG.mat, x]
    have h1 : D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹ = e ((B.bar O).ad (F.loc v s) (Y v)) := by
      rw [hconj, hAd]
    have hX : e (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) =
        e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s) := by
      rw [← he2, ← he2, ← he2]
      congr 1
      abel
    have key : D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹ =
        e ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) * D.t v s := by
      rw [← hconj, hX]
      calc D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹
          = D.g v * e (-(Y v)) * e (-β (F.loc v s)) *
              (D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹) * D.r (F.loc v s) * (D.g v)⁻¹ := by
            rw [_root_.mul_inv_rev, he3, neg_neg]
            group
        _ = D.g v * e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) *
              (e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v)) * (D.g v)⁻¹ := by
            rw [h1, ← hr]
        _ = D.g v * (e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s)) *
              (D.g v)⁻¹ * D.t v s := by
            group
    have hW : UpT ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
      rw [← (hGbar v).1, ← (hGbar v).2]
      exact hb v s
    rw [hmat, ← Units.val_mul, ← Units.val_mul, key, Units.val_mul, he1]
    apply upT_mul _ (D.t_tri v s)
    intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.map_apply, hW i j hij, map_zero, add_zero]
  · intro i j N
    have hB : IsLocallyConstant fun s =>
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro s0
      have hall : ∀ᶠ s in nhds s0, ∀ a b,
          Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s : Matrix (Fin n) (Fin n) C') a b) =
            Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s0 : Matrix (Fin n) (Fin n) C') a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
          (IsLocallyConstant.iff_eventually_eq _).1 (D.r_cont a b N) s0
      filter_upwards [hall] with s hs
      ext a b
      exact hs a b
    have hA := hβ.comp (fun Z =>
      ((1 : Matrix (Fin n) (Fin n) C') + (-Z).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N)))
    have hM := (IsLocallyConstant.comp₂ hA hB (· * ·)).comp (fun M => M i j)
    convert hM using 1
    funext s
    change Ideal.Quotient.mk (maximalIdeal C' ^ N) ((R' s).mat i j) =
      (((1 + (-β s).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) *
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) i j
    rw [← Matrix.map_mul, Matrix.map_apply]
    congr 1
    show (R' s).mat i j = _
    simp [R', GG.mat, x, he1]
  · apply Box.ext
    · apply MonoidHom.ext
      intro s
      apply SemidirectProduct.ext
      · show GeneralLinearGroup.map (p : C' →+* C) (R' s).left = (B.r s).left
        simp [R', x, hpe, D.r_map]
      · show (R' s).right = (B.r s).right
        simp [R', x, B.nu]
    · funext v
      show GeneralLinearGroup.map (p : C' →+* C) (D.g v * e (-(Y v))) = B.g v
      rw [map_mul, hpe, mul_one, D.g_map]
  · intro s
    show (R' s).mat = _
    simp [R', GG.mat, x, he1, hneg, sub_eq_add_neg]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_gl {C : Type} [CommRing C] {n : ℕ} (a b c : GL (Fin n) C)
    (ha : UpT (a : Matrix (Fin n) (Fin n) C)) (hb : UpT (b : Matrix (Fin n) (Fin n) C))
    (hc : UpT (c : Matrix (Fin n) (Fin n) C)) :
    UpT (((a * b * c⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - 1) := by
  have ha' : (a : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => ha i j h
  have hb' : (b : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hb i j h
  have hc' : (c : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hc i j h
  letI : Invertible (c : Matrix (Fin n) (Fin n) C) := c.invertible
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hc'
  rw [← Matrix.coe_units_inv] at hi
  intro i j h
  have h1 := ((ha'.mul hb').mul hi) (show id j < id i from h)
  rw [Matrix.sub_apply, Units.val_mul, Units.val_mul, h1, Matrix.one_apply_ne (ne_of_gt h), sub_zero]

private theorem ring_id {R : Type} [Ring R] (o c x a w : R) (h : (1 + o) * (1 + c) = (1 + x) * (1 + a) * (1 + w))
    (h1 : o * c = 0) (h2 : x * a = 0) (h3 : x * w = 0) (h4 : a * w = 0) : o - (x - c + a) = w := by
  have e1 : (1 + o) * (1 + c) = 1 + o + c + o * c := by noncomm_ring
  have e2 : (1 + x) * (1 + a) * (1 + w) = 1 + x + a + w + x * a + x * w + a * w + x * a * w := by noncomm_ring
  rw [e1, e2, h1, h2, h3, h4] at h
  simp only [add_zero, zero_mul] at h
  have : o = 1 + x + a + w - c - 1 := by rw [← h]; abel
  rw [this]; abel

theorem UpperTheory.V.Fr.pr_cocv :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ v s t, (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) ∈ (B.bar O).b v := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK v s t
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' C p B D hK
  have hle : RingHom.ker p ≤ maximalIdeal C' := fun x hx => by
    rw [← res_eq_zero_iff O, ← res_map p, (RingHom.mem_ker).1 hx, map_zero]
  have ev := pr_evk O C' n (RingHom.ker p) u hK hle
  have hdel : ∀ s, F.del (F.loc v s) = 1 := fun s => (F.loc0 v s).2
  have hright : ∀ s, (B.r (F.loc v s)).right = 1 := fun s => (B.nu _).trans (hdel s)
  have hres : ∀ x : GL (Fin n) C', GeneralLinearGroup.map (res O C : C →+* ResidueField O)
      (GeneralLinearGroup.map (p : C' →+* C) x) = GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x := by
    intro x
    ext i j
    exact res_map p _
  have hval : ∀ x : GL (Fin n) C', (x : Matrix (Fin n) (Fin n) C').map (res O C') =
      ((GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x : GL (Fin n) (ResidueField O)) :
        Matrix (Fin n) (Fin n) (ResidueField O)) := fun x => rfl

  set T : Matrix (Fin n) (Fin n) C' :=
    ((D.t v s * D.t v t * (D.t v (s * t))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1 with hT
  have hTup : UpT T := upT_gl _ _ _ (D.t_tri v s) (D.t_tri v t) (D.t_tri v _)
  have hTK : ∀ i j, T i j ∈ RingHom.ker p := by
    have e : GeneralLinearGroup.map (p : C' →+* C) (D.t v s * D.t v t * (D.t v (s * t))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, D.t_map, D.t_map, D.t_map, map_mul, map_mul, SemidirectProduct.mul_left,
        hright, sgnAct_one]
      group
    intro i j
    have e2 := congrArg (fun x : GL (Fin n) C => (x : Matrix (Fin n) (Fin n) C) i j) e
    rw [RingHom.mem_ker, hT, Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 (Eq.trans e2 ?_)
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  set gi : Matrix (Fin n) (Fin n) C' := (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hgi
  set g : Matrix (Fin n) (Fin n) C' := ((D.g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hg
  set ri : Matrix (Fin n) (Fin n) C' := (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hri
  set r : Matrix (Fin n) (Fin n) C' := ((D.r (F.loc v s) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hr
  have hW1 : ∀ i j, (gi * T) i j ∈ RingHom.ker p := fun i j => (((ev T hTK).2.1 gi).1 i j).1
  have hW : ∀ i j, (gi * T * g) i j ∈ RingHom.ker p := fun i j => (((ev _ hW1).2.1 g).1 i j).2
  have hX1 : ∀ i j, (r * D.a v t) i j ∈ RingHom.ker p := fun i j => (((ev _ (ha v t)).2.1 r).1 i j).1
  have hX : ∀ i j, (r * D.a v t * ri) i j ∈ RingHom.ker p := fun i j => (((ev _ hX1).2.1 ri).1 i j).2
  have key : D.om (F.loc v s, F.loc v t) - (r * D.a v t * ri - D.a v (s * t) + D.a v s) = gi * T * g := by
    refine ring_id _ _ _ _ _ ?_ ((ev _ (hom _)).1 _ (ha v _)).1 ((ev _ hX).1 _ (ha v _)).1
      ((ev _ hX).1 _ hW).1 ((ev _ (ha v _)).1 _ hW).1
    have e1 : 1 + r * D.a v t * ri = ((D.r (F.loc v s) * (D.r (F.loc v t) * ((D.g v)⁻¹ * D.t v t * D.g v)⁻¹) *
        (D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') := by
      rw [SetLift.a, mul_sub, sub_mul, mul_one, hr, hri, Units.mul_inv, add_sub_cancel]
      rfl
    have e2 : 1 + gi * T * g = (((D.g v)⁻¹ * (D.t v s * D.t v t * (D.t v (s * t))⁻¹) * D.g v : GL (Fin n) C') :
        Matrix (Fin n) (Fin n) C') := by
      rw [hT, mul_sub, sub_mul, mul_one, hg, hgi, Units.inv_mul, add_sub_cancel]
      rfl
    rw [e1, e2]
    simp only [SetLift.om, SetLift.a, add_sub_cancel, hdel, sgnAct_one, ← Units.val_mul, map_mul]
    congr 1
    group
  have hXc : ∀ i j, (r * D.a v t * ri - D.a v (s * t)) i j ∈ RingHom.ker p := fun i j =>
    sub_mem (hX i j) (ha v _ i j)
  have hXca : ∀ i j, (r * D.a v t * ri - D.a v (s * t) + D.a v s) i j ∈ RingHom.ker p := fun i j =>
    add_mem (hXc i j) (ha v _ i j)
  have k2 := congrArg (fun M : Matrix (Fin n) (Fin n) C' => M.map (evK (RingHom.ker p) u)) key
  rw [((ev _ (hom _)).1 _ hXca).2.2, ((ev _ hXc).1 _ (ha v _)).2.1, ((ev _ hX).1 _ (ha v _)).2.2,
    ((ev _ hX1).2.1 ri).2.2, ((ev _ (ha v t)).2.1 r).2.1, ((ev _ hW1).2.1 g).2.2, ((ev _ hTK).2.1 gi).2.1,
    hr, hri, hg, hgi, hval, hval, hval, hval, map_inv, map_inv, ← hres, ← hres (D.g v), D.r_map, D.g_map] at k2
  have k3 : (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) =
      ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) *
        T.map (evK (RingHom.ker p) u) * ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) := by
    refine Eq.trans ?_ k2
    have e : ((B.bar O).ad.comp (F.loc v)) s ((D.co u).2 v t) =
        ((B.bar O).r (F.loc v s)).adFun ((D.a v t).map (evK (RingHom.ker p) u)) := rfl
    have e' : ((B.bar O).r (F.loc v s)).right = 1 := hright s
    simp only [dOne]
    rw [e, GG.adFun, if_pos e', add_sub_assoc, add_comm]
    rfl
  rw [k3]
  intro i j h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one, Matrix.map_apply, hTup i j h, evK_of_mem u (zero_mem _)]
  exact map_zero u
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem grp_id {H : Type*} [Group H] (a b c ab bc abc : H) :
    (a * b * ab⁻¹) * (ab * c * abc⁻¹) = (a * (b * c * bc⁻¹) * a⁻¹) * (a * bc * abc⁻¹) := by
  group

theorem UpperTheory.V.Fr.borelProjection_isTwoCocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ s t r, (B.bar O).ad s ((D.co u).1 (t, r)) + (D.co u).1 (s, t * r) = (D.co u).1 (s * t, r) + (D.co u).1 (s, t) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK s t r
  have hKm : RingHom.ker p ≤ maximalIdeal C' := by
    intro y hy
    rw [← res_eq_zero_iff O C', ← res_map p y, RingHom.mem_ker.mp hy, map_zero]
  obtain ⟨hom, -, -, -⟩ := pr_omk hF O C' C p B D hK
  obtain ⟨x, hx⟩ : ∃ x : F.Γ → GG (m := n) (R := C'), ∀ a, x a = ⟨D.r a, F.del a⟩ := ⟨_, fun _ => rfl⟩
  have hW : ∀ a b, x a * x b * (x (a * b))⁻¹ =
      GG.ofGL (D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹) := by
    intro a b
    rw [hx, hx, hx]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        SemidirectProduct.inv_right, SemidirectProduct.left_inl, GG.ofGL]
      rw [← MulAut.mul_apply, ← map_mul, map_mul F.del a b, mul_inv_cancel, map_one, MulAut.one_apply]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inl,
        GG.ofGL, map_mul, mul_inv_cancel, mul_one]
  have hz : ∀ a b, ((D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹ : GL (Fin n) C') :
      Matrix (Fin n) (Fin n) C') = 1 + D.om (a, b) := by
    intro a b
    simp [SetLift.om]
  have hbar : (B.bar O).r s = GG.map (res O C' : C' →+* ResidueField O) (x s) := by
    rw [hx]
    apply SemidirectProduct.ext
    · ext i j
      simp [Box.map, GG.map, ← D.r_map s, res_map]
    · simp [Box.map, GG.map, B.nu]
  have key : ∀ a b : GG (m := n) (R := C'), a.right = 1 → (a * b).mat = a.mat * b.mat := by
    intro a b ha
    simp only [GG.mat, SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply, Units.val_mul]
  have hofr : ∀ w : GL (Fin n) C', (GG.ofGL w).right = 1 := fun w => rfl
  have hmat : ∀ w : GL (Fin n) C', (GG.ofGL w).mat = (w : Matrix (Fin n) (Fin n) C') := fun w => rfl
  have hW' : x s * x (t * r) * (x (s * t * r))⁻¹ =
      GG.ofGL (D.r s * sgnAct n C' (F.del s) (D.r (t * r)) * (D.r (s * (t * r)))⁻¹) := by
    rw [mul_assoc s t r]
    exact hW s (t * r)
  have h := grp_id (x s) (x t) (x r) (x (s * t)) (x (t * r)) (x (s * t * r))
  rw [hW s t, hW (s * t) r, hW t r, hW'] at h
  have hyr : (x s * GG.ofGL (D.r t * sgnAct n C' (F.del t) (D.r r) * (D.r (t * r))⁻¹) * (x s)⁻¹).right
      = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, GG.ofGL,
      SemidirectProduct.right_inl, mul_one, mul_inv_cancel]
  have hM := congrArg GG.mat h
  rw [key _ _ (hofr _), key _ _ hyr, hmat, hmat, hmat] at hM
  obtain ⟨-, -, hE3⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (t, r)) (hom (t, r))
  obtain ⟨hAK, hAmap, hconj⟩ := hE3 (x s)
  rw [hconj _ (hz t r), hz s t, hz (s * t) r, hz s (t * r)] at hM
  obtain ⟨h1, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (s, t)) (hom (s, t))
  obtain ⟨h12, h12add, -⟩ := h1 (D.om (s * t, r)) (hom _)
  obtain ⟨hA, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm ((x s).adFun (D.om (t, r))) hAK
  obtain ⟨hA4, hA4add, -⟩ := hA (D.om (s, t * r)) (hom _)
  have hsum : D.om (s, t) + D.om (s * t, r) = (x s).adFun (D.om (t, r)) + D.om (s, t * r) := by
    have e1 : (1 + D.om (s, t)) * (1 + D.om (s * t, r)) = 1 + (D.om (s, t) + D.om (s * t, r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, h12]
      abel
    have e2 : (1 + (x s).adFun (D.om (t, r))) * (1 + D.om (s, t * r)) =
        1 + ((x s).adFun (D.om (t, r)) + D.om (s, t * r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, hA4]
      abel
    rw [e1, e2] at hM
    exact add_left_cancel hM
  change ((B.bar O).r s).adFun ((D.om (t, r)).map (evK (RingHom.ker p) u)) +
      (D.om (s, t * r)).map (evK (RingHom.ker p) u) =
      (D.om (s * t, r)).map (evK (RingHom.ker p) u) + (D.om (s, t)).map (evK (RingHom.ker p) u)
  rw [hbar, ← hAmap, ← hA4add, add_comm ((D.om (s * t, r)).map _), ← h12add, hsum]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_family :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ f : ∀ N : ℕ, S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ N, S.ρ.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1)))) ∧ (∀ N x d, Ideal.Quotient.mk (𝔪 ^ (N + 1 + 1)) d = f (N + 1) x → Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x) ∧ ∀ N, ∀ x ∈ maximalIdeal S.R ^ (N + 1), f N x = 0 := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  choose hco hmax using alg_quot O C 𝔪 hV
  have hex : ∀ N, ∃! f : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1),
      S.ρ.map (f : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
    intro N
    letI := hco N
    exact S.univ _ _ (alg_lift C 𝔪 ρ hM _ (Ideal.Quotient.mkₐ O (𝔪 ^ (N + 1))) (fun x hx => by
      rw [hmax N]
      exact Ideal.mem_map_of_mem _ hx))
  choose f hf huniq using hex
  refine ⟨f, hf, ?_, ?_⟩
  · intro N x d hd
    have hle : 𝔪 ^ (N + 1 + 1) ≤ 𝔪 ^ (N + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    have hcomp : (Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) = f N := by
      apply huniq N
      have e : (((Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
          S.R →+* D ⧸ 𝔪 ^ (N + 1)) =
          ((Ideal.Quotient.factorₐ O hle : D ⧸ 𝔪 ^ (N + 1 + 1) →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
            D ⧸ 𝔪 ^ (N + 1 + 1) →+* D ⧸ 𝔪 ^ (N + 1)).comp (f (N + 1) : S.R →+* D ⧸ 𝔪 ^ (N + 1 + 1)) := rfl
      rw [e, ← NRep.map_map, hf (N + 1), NRep.map_map]
      rfl
    rw [← hcomp, AlgHom.comp_apply, ← hd]
    rfl
  · intro N x hx
    letI := hco N
    have hm : ∀ y ∈ maximalIdeal S.R,
        f N y ∈ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      intro y hy
      rw [← hmax N, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    have hle : Ideal.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) (maximalIdeal S.R) ≤
        Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      rw [Ideal.map_le_iff_le_comap]
      exact hm
    have hx' := Ideal.mem_map_of_mem (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) hx
    rw [Ideal.map_pow] at hx'
    have h2 := Ideal.pow_right_mono hle (N + 1) hx'
    rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2
    exact h2
end
