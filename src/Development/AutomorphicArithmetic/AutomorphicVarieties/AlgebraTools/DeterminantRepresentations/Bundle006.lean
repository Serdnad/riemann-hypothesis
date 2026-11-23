module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle003
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.irrOpenDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (p : PrimeSpectrum A),
        p.asIdeal = RingHom.ker φ → D.map φ = GDet.ofRep ρ → (p ∈ U ↔ U3.MatIrr H ρ) := by
  intro n A G _ _ D H
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    intro K _ _ φ ρ p _ _
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  · obtain ⟨U, hU, h⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
      (fun h : H => D.tr (MonoidAlgebra.single (h : G) 1))
    refine ⟨U, hU, ?_⟩
    intro K _ _ φ ρ p hp hD
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    refine h K φ (ρ.comp H.subtype) p hp ?_
    intro g
    have hmap : (D.map φ).chi (MonoidAlgebra.single (g : G) 1) =
        (D.chi (MonoidAlgebra.single (g : G) 1)).map φ := by
      let : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let f : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with
          commutes' := fun a => by
            change Polynomial.mapRingHom φ (algebraMap A A[X] a) = algebraMap K K[X] (φ a)
            simp [Polynomial.algebraMap_eq] }
      change D.D K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1)) = f (D.chi _)
      rw [GDet.chi, ← D.nat A[X] K[X] f]
      congr 1
      simp [f]
    have hrep : (GDet.ofRep ρ).chi (MonoidAlgebra.single (g : G) 1) = (ρ g).charpoly := by
      change (GDet.repAlg ρ K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1))).det = _
      rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one, Matrix.charpoly]
      simp only [GDet.repAlg, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
        map_one, one_smul, Polynomial.algebraMap_eq]
      rw [Matrix.charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [hD, hrep] at hmap
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    change (ρ g).trace = φ (D.lam 1 _)
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap, Polynomial.coeff_map]
    simp [GDet.lam]
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extendPoly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    (∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d σ (b • x) = b ^ n * d σ x) →
    ∃ D : GDet n A G, ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), D.D (MvPolynomial σ A) x = d σ x := by
  intro n A G _ _ d hnat hhom
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra A B],
      Function.Surjective (MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)) := by
    intro B _ _
    rw [MonoidAlgebra.coe_mapRingHom]
    refine MonoidAlgebra.map_surjective _ ?_
    intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  have spec : ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G),
      MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)
        (hsurj B y).choose = y :=
    fun B _ _ y => (hsurj B y).choose_spec
  have ind : ∀ (B : Type) [CommRing B] [Algebra A B] (x x' : MonoidAlgebra (MvPolynomial B A) G),
      MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x =
        MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x' →
      MvPolynomial.aeval id (d B x) = MvPolynomial.aeval id (d B x') :=
    fun B _ _ x x' h => UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B B B _ _ x x' h
  refine ⟨⟨fun B _ _ =>
    { toFun := fun y => MvPolynomial.aeval id (d B (hsurj B y).choose)
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩, ?_⟩
  · show MvPolynomial.aeval id (d B (hsurj B 1).choose) = 1
    rw [ind B _ 1 (by rw [spec, map_one]), map_one, map_one]
  · intro y y'
    show MvPolynomial.aeval id (d B (hsurj B (y * y')).choose) =
      MvPolynomial.aeval id (d B (hsurj B y).choose) * MvPolynomial.aeval id (d B (hsurj B y').choose)
    rw [ind B _ ((hsurj B y).choose * (hsurj B y').choose) (by rw [spec, map_mul, spec, spec]),
      map_mul, map_mul]
  · intro B B' _ _ _ _ f y
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B' B' B (MvPolynomial.aeval id)
      (f.comp (MvPolynomial.aeval id)) (hsurj B' (MonoidAlgebra.mapRingHom G (f : B →+* B') y)).choose
      (hsurj B y).choose (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
        rfl)
    exact h
  · intro B _ _ b y
    show MvPolynomial.aeval id (d B (hsurj B (b • y)).choose) =
      b ^ n * MvPolynomial.aeval id (d B (hsurj B y).choose)
    rw [ind B _ (MvPolynomial.X b • (hsurj B y).choose) (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        ext m
        rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_smul_apply (MvPolynomial.X b : MvPolynomial B A) (hsurj B y).choose m]
        simp [smul_eq_mul]), hhom, map_mul, map_pow, MvPolynomial.aeval_X, id]
  · intro σ x
    show MvPolynomial.aeval id (d (MvPolynomial σ A) (hsurj (MvPolynomial σ A) x).choose) = d σ x
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat (MvPolynomial σ A) (MvPolynomial σ A) σ
      (MvPolynomial.aeval id) (AlgHom.id A _) _ x (by rw [spec])
    simpa using h
end

section

open Polynomial UpperTheory.V.W

private theorem injTest_mvInj {A : Type} [CommRing A] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    (f : ∀ x, A →+* K x) (hf : ∀ a, (∀ x, f x a = 0) → a = 0) {σ : Type} (P Q : MvPolynomial σ A)
    (h : ∀ x, MvPolynomial.map (f x) P = MvPolynomial.map (f x) Q) : P = Q := by
  ext β
  rw [← sub_eq_zero]
  refine hf _ fun x => ?_
  have := congrArg (AddMonoidAlgebra.coeff · β) (h x)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this
  rw [map_sub, this, sub_self]

private theorem injTest_smul {R S G : Type} [CommRing R] [CommRing S] [Group G] (φ : R →+* S) (r : R)
    (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (r • z) = φ r • MonoidAlgebra.mapRingHom G φ z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]
  | single g s => simp

private theorem injTest_comp {R S T G : Type} [CommRing R] [CommRing S] [CommRing T] [Group G]
    (φ : R →+* S) (ψ : S →+* T) (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ (MonoidAlgebra.mapRingHom G φ z) = MonoidAlgebra.mapRingHom G (ψ.comp φ) z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp

theorem UpperTheory.V.AlgebraTools.Det.injTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) →
    (∀ D D' : GDet n A G, (∀ x, D.map (f x) = D'.map (f x)) → D = D') ∧
    (∀ (D : GDet n A G) (y : MonoidAlgebra A G), (∀ x, (D.map (f x)).Kills (MonoidAlgebra.mapRingHom G (f x) y)) → D.Kills y) := by
  intro n A G _ _ X K _ f hf
  have mapEval (D : GDet n A G) (x : X) {σ : Type} (z : MonoidAlgebra (MvPolynomial σ A) G) :
      (D.map (f x)).D (MvPolynomial σ (K x)) (MonoidAlgebra.mapRingHom G (MvPolynomial.map (f x)) z) =
        MvPolynomial.map (f x) (D.D (MvPolynomial σ A) z) := by
    let : Algebra A (MvPolynomial σ (K x)) := ((algebraMap (K x) (MvPolynomial σ (K x))).comp (f x)).toAlgebra
    exact D.nat _ _ { MvPolynomial.map (f x) with commutes' := fun a => MvPolynomial.map_C (f x) a } z
  have evalGen (B : Type) [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → G) (b : Fin m → B) :
      MonoidAlgebra.mapRingHom G (MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B)
          (GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)) =
        ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
    simp only [GDet.gen, map_sum, injTest_smul, RingHom.coe_coe, MvPolynomial.aeval_X]
    simp
  refine ⟨fun D D' h => ?_, fun D y h => ?_⟩
  · apply GDet.ext
    intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    let z := GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)
    have hz : D.D (MvPolynomial (Fin m) A) z = D'.D (MvPolynomial (Fin m) A) z := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, ← mapEval D' x z, h x]
    rw [← evalGen B g b, D.nat, D'.nat, hz]
  · intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    set z : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
      1 + GDet.gen (fun j => MonoidAlgebra.single (g j) (1 : A)) * MonoidAlgebra.mapRingHom G MvPolynomial.C y with hz
    have h1 : D.D (MvPolynomial (Fin m) A) z = 1 := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, map_one, hz, map_add, map_one, map_mul, injTest_comp]
      have e : (MvPolynomial.map (f x) : MvPolynomial (Fin m) A →+* _).comp MvPolynomial.C =
          (algebraMap (K x) (MvPolynomial (Fin m) (K x))).comp (f x) := by
        ext a : 1
        simp
      rw [e, ← injTest_comp]
      exact h x _ _
    have h2 := D.nat _ B (MvPolynomial.aeval b) z
    have e : ((MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B) : MvPolynomial (Fin m) A →+* B).comp
        MvPolynomial.C = algebraMap A B := by
      ext a : 1
      simp
    rw [h1, map_one, hz, map_add, map_one, map_mul, injTest_comp, e, evalGen] at h2
    exact h2
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.Kills y →
    ∀ (h : MonoidAlgebra A G) (i : ℕ), 1 ≤ i → i ≤ n → D.lam i (h * y) = 0 := by
  intro n A G _ _ D y hy h i hi1 hin
  have key := UpperTheory.V.AlgebraTools.Det.expand D (h * y) (Polynomial A) 1 Polynomial.X
  have hk := hy (Polynomial A)
    ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h)
  have heq : MonoidAlgebra.single 1 (1 : Polynomial A) +
      (Polynomial.X : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) (h * y) =
      1 + ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h) *
        (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y := by
    rw [map_mul, smul_mul_assoc, MonoidAlgebra.one_def]
  rw [heq, hk] at key
  have hc := congrArg (fun p : Polynomial A => p.coeff i) key
  simp only [one_pow, mul_one, Polynomial.algebraMap_eq, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] at hc
  rw [Finset.sum_ite_eq] at hc
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hi0 : i ≠ 0 := by omega
  simp only [hmem, if_true, hi0, if_false] at hc
  exact hc.symm
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.chiApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G),
    D.lam 0 y = 1 ∧ D.lam n y = D.D A y ∧ (D.chi y).Monic ∧ (D.chi y).natDegree ≤ n ∧
    D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
  intro n A G _ _ D y
  have hsum : D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y (Polynomial A) X (-1)
    have h1 : MonoidAlgebra.single 1 (X : Polynomial A) +
        (-1 : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y =
        MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) y := by
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq]
    rw [h1] at key
    unfold UpperTheory.V.W.GDet.chi
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.algebraMap_eq, C_mul, C_pow, C_neg, C_1]
    ring
  have h0 : D.lam 0 y = 1 := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 1 0
    rw [zero_smul, add_zero, ← MonoidAlgebra.one_def, map_one] at key
    rw [Finset.sum_eq_single 0] at key
    · simpa using key.symm
    · intro b _ hb
      simp [zero_pow hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hn : D.lam n y = D.D A y := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 0 1
    rw [Finset.sum_eq_single n] at key
    · simp only [MonoidAlgebra.single_zero, zero_add, one_smul, Nat.sub_self, pow_zero, one_pow,
        mul_one, Algebra.algebraMap_self, RingHom.id_apply] at key
      rw [← key]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    · intro b hb hbn
      have : n - b ≠ 0 := by
        have := Finset.mem_range.mp hb
        omega
      simp [zero_pow this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hdeg : (D.chi y).natDegree ≤ n := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  have hcoeff : (D.chi y).coeff n = 1 := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [h0]
    · intro b hb hb0
      have : n ≠ n - b := by
        have := Finset.mem_range.mp hb
        omega
      rw [Polynomial.coeff_C_mul_X_pow, if_neg this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  exact ⟨h0, hn, Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hcoeff, hdeg, hsum⟩
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extGen :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D D' : GDet n A G),
    (∀ (m : ℕ) (g : Fin m → G), D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) =
      D'.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) → D = D' := by
  intro n A G _ _ D D' h
  refine GDet.ext fun B _ _ x => ?_
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B x
  rw [UpperTheory.V.AlgebraTools.Det.genEval D B m (fun j => MonoidAlgebra.single (g j) 1) b,
    UpperTheory.V.AlgebraTools.Det.genEval D' B m (fun j => MonoidAlgebra.single (g j) 1) b, h]
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.isContIff :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (I : Ideal A), IsAdic I → ∀ D : GDet n A G,
    D.IsCont I ↔ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ I hI D
  unfold GDet.IsCont
  simp only [UpperTheory.V.AlgebraTools.Det.adicContIff I hI]
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i ≤ n
    · exact h i hi
    · have heq : (fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
          fun g => (-1) ^ (i + n) * D.lam n (MonoidAlgebra.single g 1) := by
        funext g
        unfold GDet.lam
        rw [Nat.sub_eq_zero_of_le (not_le.mp hi).le, Nat.sub_self, ← mul_assoc, ← pow_add, add_assoc,
          ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      rw [heq]
      exact continuous_const.mul (h n le_rfl)
end

section

open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff {n : ℕ} {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.AlgebraTools.Det.repCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    Continuous ρ → ∀ i, Continuous fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ ρ hρ i
  have h : (fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))
      = fun g => (-1) ^ i * (ρ g).charpoly.coeff (n - i) := by
    funext g
    rw [GDet.lam, (UpperTheory.V.AlgebraTools.Det.repApi ρ).2.1]
  rw [h]
  exact continuous_const.mul ((UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff (n - i)).comp hρ)
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_eq_mapRingHom_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B B' : Type) [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B'] (n : ℕ) (φ : B →+* B') (hφ : φ.comp (algebraMap O B) = algebraMap O B') (y : MonoidAlgebra B F.G₀) :
    F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ φ y) = MonoidAlgebra.mapRingHom F.G₀ φ (F.star O B n y) := by
  have h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B') := by
    intro u k
    rw [← map_zpow]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [map_add (f := _), GFrame.star, MulOpposite.unop_add] at *
    rw [ha, hb]
  | single g b =>
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]
    simp
    rw [h1]
    congr 3
    ext
    simp [← hφ]

theorem UpperTheory.V.AlgebraTools.Det.polarInj :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀) {X : Type} (K : X → Type) [∀ x, CommRing (K x)] [∀ x, Algebra O (K x)] (f : ∀ x, R →ₐ[O] K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, F.IsPolar O (D.map (f x : R →+* K x))) → F.IsPolar O D := by
  intro l _ F O _ _ R _ _ n D X K _ _ f hf h
  intro B _ _ _ _ y
  classical
  let u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀ := y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)
  let ev : MvPolynomial F.G₀ R →ₐ[R] B := MvPolynomial.aeval fun g => y.coeff g
  have hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y := by

    simp only [u, map_sum, MonoidAlgebra.mapRingHom_single]
    simp only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact y.sum_single
  have hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B := by
    ext o
    simp [ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]
  have key : D.D _ (F.star O _ n u) = D.D _ u := by
    rw [← sub_eq_zero]
    ext m
    rw [MvPolynomial.coeff_zero]
    apply hf
    intro x
    letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra
    let φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x) := MvPolynomial.aeval MvPolynomial.X
    have hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
      · intro i
        simp [φ]
    have hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x)) := by
      rw [hφ]
      refine RingHom.ext fun o => ?_
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]
      congr 1
      exact (f x).commutes o
    have hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0 := by
      rw [← hφ, map_sub, sub_eq_zero]
      have hx := h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)
      rw [star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO] at hx
      change D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx
      rw [D.nat _ _ φ, D.nat _ _ φ] at hx
      exact hx
    have hc := congrArg (AddMonoidAlgebra.coeff · m) hz
    rw [MvPolynomial.coeff_map] at hc
    simpa using hc
  rw [← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]
end
