module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section LC

variable {T A C : Type} [TopologicalSpace T] [CommRing A] [CommRing C] {n : ℕ}

private theorem lc_matrix {B : Type} {f : T → Matrix (Fin n) (Fin n) B}
    (h : ∀ a b, IsLocallyConstant fun s => f s a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hall : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (h a b) x
  filter_upwards [hall] with y hy
  ext a b
  exact hy a b

private theorem lc_gl {I : Ideal A} {f : T → GL (Fin n) A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s) := by
  apply IsLocallyConstant.desc _ (fun u : GL (Fin n) (A ⧸ I ^ N) => (u : Matrix (Fin n) (Fin n) (A ⧸ I ^ N)))
  · apply lc_matrix
    intro a b
    simpa [Function.comp_def] using h a b N
  · exact fun u v huv => Units.ext huv

private theorem mem_ker (p : A →+* C) {u : GL (Fin n) A} (h : GeneralLinearGroup.map p u = 1) (i j : Fin n) :
    ((u : Matrix (Fin n) (Fin n) A) - 1) i j ∈ RingHom.ker p := by
  rw [RingHom.mem_ker]
  have he := congrArg (fun v : GL (Fin n) C => (v : Matrix (Fin n) (Fin n) C) i j) h
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at he
  rw [Matrix.sub_apply, map_sub, he, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → GL (Fin n) A}
    (hf : ∀ s a b, ((f s : Matrix (Fin n) (Fin n) A) - 1) a b ∈ K)
    (h : ∀ N, IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s)) :
    IsLocallyConstant fun s => (f s : Matrix (Fin n) (Fin n) A) - 1 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have h0 : ∀ x ∈ I ^ (k + 1), x ∈ K → x = 0 := by
    intro x hxm hxK
    have hx : x ∈ I ^ (k + 1) • (⊤ : Submodule A A) ⊓ (K : Submodule A A) := by
      refine ⟨?_, hxK⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hxm
    rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
    have hle : I • (I ^ k • (⊤ : Submodule A A) ⊓ (K : Submodule A A)) ≤ I • (K : Submodule A A) :=
      Submodule.smul_mono le_rfl inf_le_right
    have hx' := hle hx
    rw [Ideal.smul_eq_mul, hs] at hx'
    exact (Submodule.mem_bot A).1 hx'
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (h (k + 1)) s] with s' hs'
  ext a b
  have he := congrArg
    (fun v : GL (Fin n) (A ⧸ I ^ (k + 1)) => (v : Matrix (Fin n) (Fin n) (A ⧸ I ^ (k + 1))) a b) hs'
  simp only [GeneralLinearGroup.map_apply] at he
  have hd := Ideal.Quotient.eq.1 he
  have hK : (f s' : Matrix (Fin n) (Fin n) A) a b - (f s : Matrix (Fin n) (Fin n) A) a b ∈ K := by
    have := sub_mem (hf s' a b) (hf s a b)
    simpa [Matrix.sub_apply] using this
  rw [Matrix.sub_apply, Matrix.sub_apply, sub_eq_zero.1 (h0 _ hd hK)]

private theorem map_sgn (f : A →+* C) (s : ℤˣ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (sgnAct n A s g) = sgnAct n C s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · simpa using map_theta f g

private theorem lc_hom {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ z in nhds (1 : G), z ∈ (φ.ker : Set G) := h.mem_nhds (one_mem _)
  have hc : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have := (continuous_const_mul x⁻¹).tendsto x
    rwa [inv_mul_cancel] at this
  filter_upwards [hc.eventually h1] with y hy
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
  exact hy.symm

end LC

theorem UpperTheory.V.Fr.pr_omk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B), maximalIdeal C' * RingHom.ker p = ⊥ → (∀ x i j, D.om x i j ∈ RingHom.ker p) ∧ (∀ v s i j, D.a v s i j ∈ RingHom.ker p) ∧ IsLocallyConstant D.om ∧ ∀ v, IsLocallyConstant (D.a v) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D hker
  have hgrp : ∀ s t, (B.r (s * t)).left = (B.r s).left * sgnAct n C (F.del s) (B.r t).left := by
    intro s t
    rw [map_mul, SemidirectProduct.mul_left, B.nu]
  have hom1 : ∀ x : F.Γ × F.Γ, GeneralLinearGroup.map (p : C' →+* C)
      (D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹) = 1 := by
    intro x
    rw [map_mul, map_mul, map_inv, map_sgn, D.r_map, D.r_map, D.r_map, hgrp, mul_inv_cancel]
  have ha1 : ∀ v s, GeneralLinearGroup.map (p : C' →+* C)
      (D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹) = 1 := by
    intro v s
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, D.r_map, D.g_map, D.t_map]
    group
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  have hrc : ∀ N, IsLocallyConstant fun s : F.Γ =>
      GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.r s) :=
    fun N => lc_gl (fun a b => D.r_cont a b) N
  have hdel : IsLocallyConstant F.del := lc_hom F.del hF.del_open
  refine ⟨fun x i j => mem_ker _ (hom1 x) i j, fun v s i j => mem_ker _ (ha1 v s) i j, ?_, ?_⟩
  · have := lc_ker hker
      (f := fun x : F.Γ × F.Γ => D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹)
      (fun x a b => mem_ker _ (hom1 x) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have e2 := (hrc N).comp_continuous (continuous_snd (X := F.Γ) (Y := F.Γ))
        have e3 := (hrc N).comp_continuous (continuous_mul (M := F.Γ))
        have e4 := hdel.comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have := IsLocallyConstant.comp₂
          (IsLocallyConstant.comp₂ e1 (IsLocallyConstant.comp₂ e4 e2
            fun s g => sgnAct n _ s g) (· * ·)) e3 (fun a b => a * b⁻¹)
        convert this using 1
        funext x
        simp [Function.comp, map_sgn])
    exact this
  · intro v
    have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
    have := lc_ker hker
      (f := fun s : F.Gv v => D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹)
      (fun s a b => mem_ker _ (ha1 v s) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous hloc
        have e2 := lc_gl (fun a b => D.t_cont v a b) N
        have := IsLocallyConstant.comp₂ e1 e2 (fun a b => a *
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹ * b *
            GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹)
        convert this using 1
        funext s
        simp [Function.comp])
    exact this
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (μ : ResidueField O →+ C), IsSq O μ → ∃ e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧ (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧ (∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), A * X.map μ = (A.map (res O C) * X).map μ ∧ X.map μ * A = (X * A.map (res O C)).map μ) ∧ ∀ (x : GG (m := n) (R := C)) (X : Matrix (Fin n) (Fin n) (ResidueField O)), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map (res O C : C →+* ResidueField O) x).adFun X)) * x := by
  intro O _ _ C _ _ _ n μ hμ
  have hsq : ∀ c d, μ c * μ d = 0 := by
    intro c d
    have h := hμ.mul (μ c) d
    rw [(res_eq_zero_iff O C _).2 (hμ.mem c), zero_mul, map_zero] at h
    exact h.symm
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      A * X.map μ = (A.map (res O C) * X).map μ := by
    intro A X
    ext i j

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hμ.mul]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      X.map μ * A = (X * A.map (res O C)).map μ := by
    intro A X
    ext i j

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hμ.mul, mul_comm]
  have hsqM : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), X.map μ * Y.map μ = 0 := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, hsq]
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), (X + Y).map μ = X.map μ + Y.map μ := by
    intro X Y
    ext i j
    simp
  have hzero : (0 : Matrix (Fin n) (Fin n) (ResidueField O)).map μ = 0 := by
    ext i j
    simp
  have hu : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O),
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := by
    intro X Y
    rw [hadd, show (1 + X.map μ) * (1 + Y.map μ) = 1 + (X.map μ + Y.map μ) + X.map μ * Y.map μ by
      noncomm_ring, hsqM, add_zero]
  let e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hu, add_neg_cancel, hzero, add_zero],
      by rw [hu, neg_add_cancel, hzero, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hemul : ∀ X Y, e (X + Y) = e X * e Y := by
    intro X Y
    apply Units.ext
    rw [Units.val_mul, he, he, he, hu]
  have heinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (g : GL (Fin n) C) (h : GL (Fin n) (ResidueField O))
      (Y : Matrix (Fin n) (Fin n) (ResidueField O)),
      (g : Matrix (Fin n) (Fin n) C).map (res O C) = (h : Matrix (Fin n) (Fin n) (ResidueField O)) →
      g * e Y = e ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y *
        (↑h⁻¹ : Matrix (Fin n) (Fin n) (ResidueField O))) * g := by
    intro g h Y hh
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR, hh, Matrix.mul_assoc ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y),
      Units.inv_mul, Matrix.mul_one]
  have hJ : (Jmat (R := C) n).map (res O C) = Jmat (R := ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have htheta : ∀ Y, theta (e Y) = e (thetaLie Y) := by
    intro Y
    apply Units.ext
    rw [theta_val, heinv, he, he, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, ← Matrix.transpose_map, hL, hJ, hR, hJ]
    rw [show thetaLie Y = Jmat (R := ResidueField O) n * (-Y)ᵀ * Jmat (R := ResidueField O) n by
      simp [thetaLie, Matrix.transpose_neg]]
  refine ⟨e, he, hemul, heinv, fun A X => ⟨hL A X, hR A X⟩, ?_⟩
  intro x X
  obtain ⟨g, s⟩ := x
  have hh : (g : Matrix (Fin n) (Fin n) C).map (res O C) =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  have had : GG.adFun (GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))) X =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) *
        (if s = 1 then X else thetaLie X) *
        (↑(GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left⁻¹ :
          Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  rw [had]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one, ite_eq_left rfl]
      exact hconj _ _ X hh
    · rw [sgnAct_neg_one, ite_eq_right (by decide), htheta]
      exact hconj _ _ _ hh
  · simp only [GG.ofGL, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one, one_mul]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mu :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (K : Ideal C') (q : C' →ₐ[O] C'') (u : K →ₗ[O] ResidueField O), maximalIdeal C' * K = ⊥ → K ≤ maximalIdeal C' → Function.Surjective q → (∀ y : K, u y = 0 → q y = 0) → ∃ μ : ResidueField O →+ C'', IsSq O μ ∧ (∀ y : K, μ (u y) = q y) ∧ ∀ c, ∃ y : K, μ c = q y := by
  intro O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker
  classical
  have hwd : ∀ y y' : K, u y = u y' → q y = q y' := by
    intro y y' h
    have h0 : u (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker _ h0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    exact h1
  have hmem : ∀ y : K, q y ∈ maximalIdeal C'' := by
    intro y
    rw [← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]
    exact hKm y.2
  by_cases hu : ∀ y, u y = 0
  · refine ⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩
    show (0 : C'') = q y
    exact (hker y (hu y)).symm
  · push_neg at hu
    obtain ⟨y0, hy0⟩ := hu
    have hsurj : Function.Surjective u := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (c * (u y0)⁻¹)
      refine ⟨o • y0, ?_⟩
      rw [map_smul, Algebra.smul_def]
      show residue O o * u y0 = c
      rw [ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    let s := Function.surjInv hsurj
    have hs : ∀ c, u (s c) = c := Function.surjInv_eq hsurj
    let μ : ResidueField O →+ C'' :=
      { toFun := fun c => q (s c)
        map_zero' := by
          show q (s 0 : C') = 0
          rw [hwd (s 0) 0 (by rw [hs, map_zero])]
          simp
        map_add' := by
          intro c d
          show q (s (c + d) : C') = q (s c : C') + q (s d : C')
          rw [hwd (s (c + d)) (s c + s d) (by rw [hs, map_add (f := _), hs, hs]), Submodule.coe_add, map_add (f := _)] }
    have hμ : ∀ c, μ c = q (s c) := fun c => rfl
    refine ⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro a c
      obtain ⟨b, rfl⟩ := hq a
      obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
      have hby : b * (s c : C') = o • (s c : C') := by
        have hz : (b - algebraMap O C' o) * (s c : C') = 0 := by
          have hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K :=
            Ideal.mul_mem_mul ho (s c).2
          rw [hmK] at hin
          simpa using hin
        rw [Algebra.smul_def]
        linear_combination hz
      have hres : res O C' b = algebraMap O (ResidueField O) o := by
        rw [← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]
        exact ho
      have hw := hwd (s (res O C'' (q b) * c)) (o • s c)
        (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])
      rw [hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]
    · intro c
      rw [hμ]
      exact hmem _
    · intro y
      rw [hμ]
      exact hwd _ _ (hs _)
    · intro c
      exact ⟨s c, rfl⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n (ResidueField O) ((B.bar O).r s) = 1
  rw [hs', map_one]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_upt :
    ∀ {C : Type} [CommRing C] {n : ℕ} (h T T' : Matrix (Fin n) (Fin n) C), UpT T → UpT T' → (∀ i j, j < i → IsUnit (T j j - T' i i)) → h * T = T' * h → UpT h := by
  intro C _ n h T T' hT hT' hu hc
  suffices key : ∀ m, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → h i j = 0 by
    intro i j hji
    exact key _ i j rfl hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    have e := congrFun (congrFun hc i) j
    simp only [Matrix.mul_apply] at e
    have hji' := Fin.lt_iff_val_lt_val.mp hji
    have L : ∑ k, h i k * T k j = h i j * T j j := by
      rw [Finset.sum_eq_single j]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hk | hk
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          rw [ih (k.val + (n - i.val)) (by omega) i k rfl (hk.trans hji), zero_mul]
        · rw [hT k j hk, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ j) hn
    have R : ∑ k, T' i k * h k j = T' i i * h i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hT' i k hk, zero_mul]
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          have hkn := k.isLt
          rw [ih (j.val + (n - k.val)) (by omega) k j rfl (hji.trans hk), mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ i) hn
    rw [L, R] at e
    have e2 : h i j * (T j j - T' i i) = 0 := by
      rw [mul_sub, e, mul_comm]
      exact sub_self _
    exact (hu i j hji).mul_left_eq_zero.mp e2
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem idx_cases (a b : Fin 3) :
    Odd (w 3 a - w 3 b) ∨ (a = 1 ∧ b = 1) ∨ ∃ i j, a = cor i ∧ b = cor j := by
  revert a b
  decide

theorem UpperTheory.V.Fr.frobenius_corner_monomial :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → ∀ (j : ℤ), ∀ x ∈ ρ.mon j, x = 0 ∨ ∃ T : List F.G0, ∃ y ∈ σ.mon j, x = (T.map fun g => ρ.r g 1 1).prod * y := by
  intro l _ k _ F K _ ρ σ hc j x hx
  obtain ⟨L, hL, rfl⟩ := hx
  induction L generalizing j with
  | nil =>
    right
    refine ⟨[], 1, ⟨[], ?_, ?_⟩, ?_⟩
    · simpa using hL
    · simp
    · simp
  | cons s L ih =>
    obtain ⟨g, a, b⟩ := s
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hL ⊢
    rcases ih _ rfl with h | ⟨T, y, ⟨M, hM, hy⟩, he⟩
    · left
      rw [h, mul_zero]
    · rcases idx_cases a b with hab | ⟨rfl, rfl⟩ | ⟨i, i', rfl, rfl⟩
      · left
        rw [hc.odd g a b hab, zero_mul]
      · right
        refine ⟨g :: T, y, ⟨M, ?_, hy⟩, ?_⟩
        · rw [hM, ← hL]
          simp
        · rw [he]
          simp only [List.map_cons, List.prod_cons]
          ring
      · right
        refine ⟨T, σ.r g i i' * y, ⟨(g, i, i') :: M, ?_, ?_⟩, ?_⟩
        · simp only [List.map_cons, List.sum_cons]
          rw [hM, ← hL, w_cor, w_cor]
        · simp only [List.map_cons, List.prod_cons]
          rw [hy]
        · rw [he, hc.r]
          ring
end
