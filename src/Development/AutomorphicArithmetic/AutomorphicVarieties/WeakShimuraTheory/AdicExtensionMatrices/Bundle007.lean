module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxLimPt
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
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private structure SxCOb (O : Type) [CommRing O] [IsLocalRing O] : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]

attribute [local instance] SxCOb.ring SxCOb.alg SxCOb.co

theorem UpperTheory.V.Ws.sxCoprodOpt :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (T : Type) [Finite T] (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra Λ (B t)] [∀ t, IsCO Λ (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (i : A →ₐ[Λ] R) (j : ∀ t, B t →ₐ[Λ] R), ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (fa : A →ₐ[Λ] R') (f : ∀ t, B t →ₐ[Λ] R'), ∃! g : R →ₐ[Λ] R', g.comp i = fa ∧ ∀ t, g.comp (j t) = f t := by
  intro Λ _ _ _ _ T _ A _ _ _ B _ _ _
  let F : Option T → Type := fun o => Option.elim o A B
  letI iR : ∀ o, CommRing (F o) := fun o =>
    match o with
    | none => (inferInstance : CommRing A)
    | some t => (inferInstance : CommRing (B t))
  letI iA : ∀ o, Algebra Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : Algebra Λ A)
    | some t => (inferInstance : Algebra Λ (B t))
  have iC : ∀ o, IsCO Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : IsCO Λ A)
    | some t => (inferInstance : IsCO Λ (B t))
  obtain ⟨R, iRR, iAl, iCO, j, hj⟩ := UpperTheory.V.CA.co_coprod Λ (Option T) F
  refine ⟨R, iRR, iAl, iCO, (j none : A →ₐ[Λ] R), fun t => (j (some t) : B t →ₐ[Λ] R), ?_⟩
  intro R' _ _ _ fa f
  let h : ∀ o, F o →ₐ[Λ] R' := fun o =>
    match o with
    | none => fa
    | some t => f t
  obtain ⟨g, hg, hu⟩ := hj R' h
  refine ⟨g, ⟨hg none, fun t => hg (some t)⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  apply hu
  intro o
  cases o with
  | none => exact h1
  | some t => exact h2 t
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {x y : R}
    (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ N => exact h N

private theorem nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

private theorem isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
    [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
  refine ⟨N + 1, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
        Ideal.pow_right_mono hle _
    _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem UpperTheory.V.Ws.sxNearA :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
  classical
  have liftNilpotent : ∀ (T : Type) [CommRing T] [Algebra Λ T] [IsCO Λ T] (P : RD Φ T),
      IsNilpotent (maximalIdeal T) → Φ.Near a τ P → ∃ f : W.A →ₐ[Λ] T, D'.map (f : W.A →+* T) = P := by
    intro T _ _ _ P hnil hP
    let c := ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs
    have hc : ∀ i j, -(c : ℤ) ≤ τ (wt i j) := by
      intro i j
      have h : (τ (wt i j)).natAbs ≤ c :=
        Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
      omega
    obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
    obtain ⟨P', hP', hr, hψ⟩ := sxScaleRD hnil he hc hP
    obtain ⟨F, hF, -⟩ := hU.2 S P' hP'
    have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (P.r g i j) := by
      intro g i j
      rw [← hr, ← hF]
      rfl
    have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (P.ψ v i s) := by
      intro v i s
      rw [← hψ, ← hF]
      rfl
    have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
      intro s
      rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
      · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
        by_cases hij : i = j
        · rw [(wt_eq_zero i j).2 hij, map_zero]
          exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
        · rw [h3 hij]
          exact ⟨P.r g i j, by simp⟩
      · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
    obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
    have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
      intro g i j
      rw [← hD']
      rfl
    have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
      intro v i s
      rw [← hD']
      rfl
    refine ⟨f, RD.ext ?_ ?_⟩
    · ext g i j
      have hm : D'.r g i j ∈ W.gr (wt i j) := by
        show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
        rw [er]
        exact hG.ent g i j
      have h := hf _ _ hm
      rw [er, hFr] at h
      exact (HahnSeries.single_injective _ h).symm
    · funext v i
      ext s
      have hm : D'.ψ v i s ∈ W.gr 0 := by
        show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
        rw [eψ]
        exact hG.chr v i s
      have h := hf _ _ hm
      rw [eψ, hFψ, map_zero] at h
      exact (HahnSeries.single_injective _ h).symm
  have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
    intro N
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact liftNilpotent _ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
      (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
  have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
      f (W.zA s) = Ideal.Quotient.mk _ y := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
    · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
        congrArg (fun E => E.r g i j) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
        congrArg (fun E => E.ψ v i t) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
  choose y hy using hval
  choose fN hfN using hlev
  have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
    intro N f f' h
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxExtA W hG.max _ f f' h
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
  obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
    (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
  have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
    intro N
    apply huniq
    intro s
    rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
    rfl
  have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
    intro x q hx
    apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
    intro N
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
    rfl
  refine ⟨F, ?_⟩
  apply RD.ext
  · ext g i j
    exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
  · funext v i
    ext t
    exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gsp_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ν : R) (X : M4 R) :
    IsGSp (f ν) (X.map f) ↔ ∀ i j, f ((adj X * X - ν • (1 : M4 R)) i j) = 0 := by
  unfold IsGSp
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h1 : (adj (X.map f) * X.map f) i j = f ((adj X * X) i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, adj_apply, Matrix.map_apply, map_sum, map_mul, map_zsmul]
  have h2 : (f ν • (1 : M4 R')) i j = f ((ν • (1 : M4 R)) i j) := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
    split_ifs <;> simp
  rw [h1, h2, Matrix.sub_apply, map_sub, sub_eq_zero]

private theorem one_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) :
    X.map f = 1 ↔ ∀ i j, f ((X - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h2 : (1 : M4 R') i j = f ((1 : M4 R) i j) := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [h2, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]

private theorem gsp_diag {R : Type} [CommRing R] (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) :
    IsGSp ν (Matrix.diagonal d) := by
  have e : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]
  unfold IsGSp
  rw [e, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_comm, h, mul_one]
  · simp

private theorem rep_closed {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ) (rbar : Γ →* M4 (ResidueField Λ)) :
    Cond.IsClosed (rbar := rbar) fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom := by
  intro R _ _ _ r
  let S : Set R := {x | (∃ g i j, (adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j = x) ∨
    (∃ g ∈ Φ.N, ∃ i j, (r.hom g - 1) i j = x) ∨ ∃ i j, i ≠ j ∧ r.hom Φ.g0 i j = x}
  refine ⟨Ideal.span S, fun R' _ _ _ f => ?_⟩
  have hs : (∀ x ∈ Ideal.span S, f x = 0) ↔ ∀ x ∈ S, f x = 0 :=
    ⟨fun h x hx => h x (Ideal.subset_span hx), fun h _ hx =>
      (Ideal.span_le (I := RingHom.ker f)).2 (fun y hy => h y hy) hx⟩
  have e1 : ∀ g, IsGSp (((algebraMap Λ R').comp a) (Φ.ν g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j) = 0 := fun g => by
    have := gsp_map_iff (f : R →+* R') (algebraMap Λ R (a (Φ.ν g))) (r.hom g)
    rw [RingHom.comp_apply, ← f.commutes]
    exact this
  have e2 : ∀ g, (r.map f).hom g = 1 ↔ ∀ i j, f ((r.hom g - 1) i j) = 0 := fun g =>
    one_map_iff (f : R →+* R') (r.hom g)
  rw [hs]
  constructor
  · rintro H x (⟨g, i, j, rfl⟩ | ⟨g, hg, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact (e1 g).1 (H.mult g) i j
    · exact (e2 g).1 (H.kill g hg) i j
    · exact H.nrm hij
  · intro H
    exact ⟨fun g => (e1 g).2 fun i j => H _ (Or.inl ⟨g, i, j, rfl⟩),
      fun g hg => (e2 g).2 fun i j => H _ (Or.inr (Or.inl ⟨g, hg, i, j, rfl⟩)),
      fun i j hij => H _ (Or.inr (Or.inr ⟨i, j, hij, rfl⟩))⟩

theorem UpperTheory.V.Ws.sxUnivRep :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R), Represents (fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom) r := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a h
  haveI := h.char
  have hd : ∀ g, (Φ.splitRD ((residue Λ).comp a)).r g =
      Matrix.diagonal fun i => ((residue Λ).comp a) (Φ.χ i g) := fun g => by
    show (Matrix.diagonal fun i => (Φ.χ i g : O)).map ((residue Λ).comp a) = _
    exact Matrix.diagonal_map (map_zero _)
  have hlc : IsLocallyConstant (Φ.splitRD ((residue Λ).comp a)).r := by
    have h4 : IsLocallyConstant fun g => fun i => ((residue Λ).comp a) (Φ.χ i g) := by
      have := (((h.ok.lc 0).prodMk (h.ok.lc 1)).prodMk ((h.ok.lc 2).prodMk (h.ok.lc 3))).comp
        fun x => ![x.1.1, x.1.2, x.2.1, x.2.2]
      convert this using 1
      funext g i
      fin_cases i <;> rfl
    have := h4.comp Matrix.diagonal
    convert this using 1
    funext g
    exact hd g
  have hk : ∀ n ∈ Φ.N, (Φ.splitRD ((residue Λ).comp a)).r n = 1 := fun n hn => by
    rw [hd]
    simp only [h.ok.kill n hn, Matrix.diagonal_one]
  obtain ⟨R, _, _, _, r, hr⟩ := sxUnivKill l (Φ.splitRD ((residue Λ).comp a)).r Φ.N h.phi hlc hk
  haveI := (co_res Λ).1
  let r₁ : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r (ResidueField Λ) :=
    { hom := (Φ.splitRD ((residue Λ).comp a)).r
      cont := fun i j N => hlc.comp fun X => Ideal.Quotient.mk _ (X i j)
      red := fun g i j => by
        obtain ⟨x, hx⟩ := residue_surjective ((Φ.splitRD ((residue Λ).comp a)).r g i j)
        rw [← hx]
        exact (res Λ (ResidueField Λ)).commutes x }
  have h1 : Φ.IsRep ((algebraMap Λ (ResidueField Λ)).comp a) r₁.hom := by
    refine ⟨fun g => ?_, hk, ?_⟩
    · show IsGSp (((residue Λ).comp a) (Φ.ν g)) ((Φ.splitRD ((residue Λ).comp a)).r g)
      rw [hd]
      refine gsp_diag _ _ fun i => ?_
      rw [← map_mul, ← Units.val_mul, h.ok.mul]
    · show ((Φ.splitRD ((residue Λ).comp a)).r Φ.g0).IsDiag
      rw [hd]
      exact Matrix.isDiag_diagonal _
  obtain ⟨R', _, _, _, p, -, hp⟩ := univ_cond Λ Γ (Fin 4) _ R r _ _ hr (rep_closed Φ a _)
    ⟨ResidueField Λ, inferInstance, inferInstance, inferInstance, r₁, hk, h1⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((hp C).1 f).2, fun s hs => (hp C).2 s ⟨hs.kill, hs⟩⟩⟩
end
