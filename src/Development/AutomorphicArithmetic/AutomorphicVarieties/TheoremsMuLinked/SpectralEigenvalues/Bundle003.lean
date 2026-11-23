module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.lamW :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (lam : M →+ O) (m₀ : M), TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ (a : B) m, lam (a • m) = x a * lam m) → ∃ (lw : V →+ O) (v : V), (∀ τ w, lw (act τ w) = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) τ * lw w) ∧ lw v = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) f * lam m₀ := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α lam m₀ hT hP hlam
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hT
  letI : Algebra B O := (x : B →+* O).toAlgebra
  let ε : MSplitAlg P n →ₐ[B] O := MSplitAlg.lift P n (fun j i => α j i) (fun j => (hP j).symm)
  have hε : ∀ t : PU R q n, ε (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β.toRingHom t)) =
      MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) t := by
    intro t
    show MvPolynomial.aeval (fun p : Fin q × Fin n => α p.1 p.2) (MvPolynomial.map β.toRingHom t) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  let lamL : M →ₗ[B] O :=
    { toFun := lam
      map_add' := lam.map_add
      map_smul' := fun a m => hlam a m }
  let Λ : MSplitAlg P n ⊗[B] M →ₗ[B] O :=
    TensorProduct.lift ((LinearMap.mul B O).compl₁₂ ε.toLinearMap lamL)
  have hΛt : ∀ a m, Λ (a ⊗ₜ m) = ε a * lam m := by
    intro a m
    show TensorProduct.lift _ (a ⊗ₜ m) = _
    rw [TensorProduct.lift.tmul]
    rfl
  have hΛs : ∀ (a : MSplitAlg P n) z, Λ (a • z) = ε a * Λ z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul a' m => rw [TensorProduct.smul_tmul', smul_eq_mul, hΛt, hΛt, map_mul, mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  refine ⟨Λ.toAddMonoidHom.comp ψ, φ (1 ⊗ₜ m₀), ?_, ?_⟩
  · intro τ w
    show Λ (ψ (act τ w)) = _ * Λ (ψ w)
    rw [h2, hΛs, hε]
  · show Λ (ψ (φ (1 ⊗ₜ m₀))) = _
    rw [h4, hΛs, hε, hΛt, map_one, one_mul]
end

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add (f := _), hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
end

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C) (S : Set C) (hS : GenBy O S)
    (h1 : ∀ b ∈ S, b ∈ f.range) : Function.Surjective f := by
  apply co_surj O R C f
  intro x hx
  obtain ⟨a, ha, hxa⟩ := hS 2 x
  have hrange : Algebra.adjoin O S ≤ f.range := Algebra.adjoin_le (fun b hb => h1 b hb)
  obtain ⟨y, hy⟩ := hrange ha
  have hy' : f y = a := hy
  have hsq : maximalIdeal C ^ 2 ≤ maximalIdeal C := Ideal.pow_le_self (by norm_num)
  have haM : a ∈ maximalIdeal C := by
    have h2 : a = x - (x - a) := by ring
    rw [h2]
    exact sub_mem hx (hsq hxa)
  have hyM : y ∈ maximalIdeal R := by
    rw [← mem_iff f y, hy']
    exact haM
  have hx' : x = f y + (x - a) := by rw [hy']; ring
  rw [hx']
  exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem f hyM)) (Ideal.mem_sup_right hxa)

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp [GDet.lam, GDet.chi, GDet.comap, Finsupp.mapDomain_sub, MonoidAlgebra.mapDomain,
    Finsupp.mapDomain_single]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  simpa using h.2 i

private theorem surjective_levelChangeBaseGroupHom {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) :
    Function.Surjective h.p₀ := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := h.surj x
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, ← h.η y]
  exact hx

theorem UpperTheory.V.Th.Sp.betaSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), GenBy O (pairVals u) → Function.Surjective A.β := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A hgen
  obtain ⟨hD, hψ⟩ := A.β_pair
  refine surj_of_gen A.β _ hgen ?_
  rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
  · obtain ⟨g, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    refine ⟨A.p.D.lam i (MonoidAlgebra.single g 1), ?_⟩
    have h := lam_map A.p.D A.β.toRingHom i g
    rw [hD, lam_comap] at h
    exact h.symm
  · exact ⟨(A.p.ψ v i g : A.R), congrArg (fun χ => ((χ g : _ˣ) : B)) (hψ v i)⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.betaLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), ∀ a : abelian₂ O Empty D, A.β (algebraMap (abelian₂ O Empty D) A.R a) = b.lam a := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A a
  haveI hOO : IsCO O O :=
    { complete := IsCoef.complete
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Empty D) := co_mvps O O (Empty ⊕ Fin D)
  have hmax : ∀ s : Empty ⊕ Fin D, b.lam (MvPowerSeries.X s) ∈ maximalIdeal B := by
    intro s
    rw [← res_eq_zero_iff O B, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h0 := hu.map MvPowerSeries.constantCoeff
    simp at h0
  obtain ⟨F, _, huniq⟩ :=
    co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) hmax
  let F1 : abelian₂ O Empty D →ₐ[O] B :=
    A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have e1 : F1 = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => ?_⟩
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact F1.commutes x
    · rcases s with e | k
      · exact e.elim
      · show A.β (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (Sum.inr k))) = _
        rw [A.segmentWeightExponent k, b.segmentWeightExponent k, map_sub, map_mul, map_one, AlgHom.commutes]
        congr 2
        have hp := congrArg (fun χ => ((χ (b.wt.γ k) : Bˣ) : B)) (A.β_pair.2 (b.wt.v k) (b.wt.i k))
        simpa [pushCh] using hp
  have e2 : b.lam = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => rfl⟩
    rw [MvPowerSeries.c_eq_algebraMap]
    exact b.lam.commutes x
  have := congrArg (fun φ : abelian₂ O Empty D →ₐ[O] B => φ a) (e1.trans e2.symm)
  simpa [F1] using this
end
