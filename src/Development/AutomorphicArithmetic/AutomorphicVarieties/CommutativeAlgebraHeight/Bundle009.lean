module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
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
public import Mathlib.RingTheory.TensorProduct.Pi
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.toDet.chi y = D.chi y ∧ (∀ i, D.toDet.lam i y = D.lam i y) ∧ D.toDet.tr y = D.tr y ∧ (D.toDet.Kills y ↔ D.Kills y) := by
  intro n A G _ _ D y
  have hchi : D.toDet.chi y = D.chi y := by
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
    rfl
  have hlam : ∀ i, D.toDet.lam i y = D.lam i y := fun i => by
    unfold Det.lam GDet.lam
    rw [hchi]
  refine ⟨hchi, hlam, hlam 1, ?_⟩
  have key : ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] MonoidAlgebra A G),
      D.toDet.D B (1 + h * (1 ⊗ₜ y)) =
        D.D B (1 + ofT A G B h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) := by
    intro B _ _ h
    change D.D B (ofT A G B (1 + h * (1 ⊗ₜ y))) = _
    rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
  constructor
  · intro hk B _ _ h
    have := hk B (toT A G B h)
    rwa [key, ofT_toT] at this
  · intro hk B _ _ h
    rw [key]
    exact hk B _
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)]
  [∀ i, Algebra A (E i)]

private theorem UpperTheory.V.CA.prod_piRight_apply (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A S S E y i =
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom A E i) y := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_piRight_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]
    (f : S →ₐ[A] T) (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A T T E (Algebra.TensorProduct.map f (AlgHom.id A _) y) i =
      Algebra.TensorProduct.map f (AlgHom.id A _) (Algebra.TensorProduct.piRight A S S E y i) := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_single_smul (S : Type) [CommRing S] [Algebra A S] (b : S) (i : ι) :
    (Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i (b • (1 : S ⊗[A] E i))) =
      1 + (b - 1) ⊗ₜ[A] (Pi.single i 1 : ∀ i, E i) := by
  rw [AlgEquiv.symm_apply_eq]
  funext j
  rw [map_add (f := _), map_one, Pi.add_apply, Pi.one_apply, Algebra.TensorProduct.piRight_tmul]
  by_cases h : j = i
  · subst h
    simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.add_tmul, add_sub_cancel]
  · simp [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h]

private noncomputable def UpperTheory.V.CA.prodFactor (D : Det n A (∀ i, E i)) (i : ι) (r : ℕ)
    (hr : D.D A[X] (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i)) = (1 + X) ^ r) : Det r A (E i) where
  D S _ _ := (D.D S).comp ((Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => S ⊗[A] E j) i))
  nat S T _ _ _ _ f x := by
    change D.D T ((Algebra.TensorProduct.piRight A T T E).symm (Pi.mulSingle i _)) =
      f (D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i x)))
    rw [← D.nat]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    funext j
    rw [prod_piRight_map, AlgEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  homog S _ _ b x := by
    have h1 : b • x = (b • (1 : S ⊗[A] E i)) * x := by rw [smul_mul_assoc, one_mul]
    rw [h1, map_mul]
    congr 1
    change D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i _)) = _
    rw [prod_single_smul]
    have h2 := D.nat A[X] S (Polynomial.aeval (b - 1)) (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i))
    rw [hr] at h2
    simpa using h2

end

theorem UpperTheory.V.CA.d_prod :
    ∀ {n : ℕ} {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)] [∀ i, Algebra A (E i)] (D : Det n A (∀ i, E i)), ∃ (m : ι → ℕ) (Ds : ∀ i, Det (m i) A (E i)), ∑ i, m i = n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)), D.D S y = ∏ i, ((Ds i).pull (Pi.evalAlgHom A E i)).D S y := by
  intro n A ι _ _ _ _ E _ _ D
  have hid : ∀ i, IsIdempotentElem (Pi.single i 1 : ∀ i, E i) := by
    intro i
    show _ * _ = _
    rw [← Pi.single_mul, one_mul]
  choose r hrle hr using fun i => d_idem_rank D (Pi.single i 1 : ∀ i, E i) (hid i)
  have hpull : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι),
      ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y
        = D.D S ((Algebra.TensorProduct.piRight A S S E).symm
            (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))) := by
    intro S _ _ y i
    rw [prod_piRight_apply]
    rfl
  have hprod : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)),
      D.D S y = ∏ i, ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y := by
    intro S _ _ y
    simp only [hpull]
    let g : (∀ j, S ⊗[A] E j) →* S :=
      (D.D S).comp (Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom
    have hg : ∀ x, g x = D.D S ((Algebra.TensorProduct.piRight A S S E).symm x) := fun x => rfl
    calc D.D S y = g (Algebra.TensorProduct.piRight A S S E y) := by
          rw [hg, AlgEquiv.symm_apply_apply]
      _ = g (Finset.univ.noncommProd
            (fun i => Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))
            fun i _ j _ _ => Pi.mulSingle_apply_commute _ i j) := by
          rw [Finset.noncommProd_mulSingle]
      _ = ∏ i, g (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i)) :=
          (Finset.map_noncommProd _ _ _ g).trans (Finset.noncommProd_eq_prod _ _)
      _ = _ := by simp only [hg]
  refine ⟨r, fun i => prodFactor E D i (r i) (hr i), ?_, hprod⟩
  have h := hprod A[X] ((X : A[X]) • 1)
  simp only [Det.homog, map_one, mul_one] at h
  rw [Finset.prod_pow_eq_pow_sum] at h
  have h' := congrArg Polynomial.natDegree h
  simpa [Polynomial.natDegree_X_pow] using h'.symm
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem UpperTheory.V.CA.pair_map :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R) (f : R →ₐ[O] R'), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ _ _ _ _ n r R R' _ _ _ _ _ _ p f
  have hl : ∀ i y, (p.D.map (f : R →+* R')).lam i (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (p.D.lam i y) :=
    fun i y => ((d_gmap p.D).2.2.1 (f : R →+* R') y).2 i
  have h1 : ∀ g : F.G₀, MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single g 1 := fun g => by rw [MonoidAlgebra.mapRingHom_single, map_one]
  refine ⟨{ D := p.D.map (f : R →+* R'), ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i),
            cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, rfl, fun _ _ => rfl⟩
  · intro i
    have := adic_map f (p.cont i)
    simpa only [← hl, h1] using this
  · rw [(d_gmap p.D).2.1, ← p.red]
    congr 1
    ext x
    exact res_map f x
  · intro v i
    refine ⟨adic_map f (p.psi v i).cont, fun g => (res_map f _).trans ((p.psi v i).red g), fun g => ?_⟩
    change f (p.ψ v i g : R) = _
    rw [(p.psi v i).mu g, f.commutes]
  · intro i g
    have hs : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      rw [star_single, star_single, MonoidAlgebra.mapRingHom_single]
      congr 1
      have he : F.eps O R' g = Units.map ((f : R →+* R') : R →* R') (F.eps O R g) :=
        Units.ext (f.commutes _).symm
      rw [he, ← map_zpow]
      rfl
    rw [hs, hl, p.P, ← hl, h1]
  · intro v g h
    have ho : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      rw [map_mul, h1, GFrame.oEl, GFrame.oEl, map_list_prod, List.map_ofFn]
      congr 3
      funext i
      simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    have := p.Ord v g h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
  · intro u g hg h
    have ho : (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1) : MonoidAlgebra R' F.G₀) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      rw [map_mul, map_sub, h1, h1, map_one]
    have := p.I u g hg h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
end
