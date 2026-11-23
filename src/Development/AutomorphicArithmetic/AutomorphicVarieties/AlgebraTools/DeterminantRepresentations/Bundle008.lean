module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

section

open Polynomial UpperTheory.V.W

private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A']
    (ι : A →+* A') (D' : GDet n A' G)
    (hc : ∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range)
    (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G) :
    D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) ∈ Set.range (MvPolynomial.map ι) := by
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) (G := G) (MvPolynomial σ A) x
  have hP : D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1) ∈ Set.range (MvPolynomial.map ι) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc'
    obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
    exact hc m g β
  obtain ⟨Q, hQ⟩ := hP
  have key := UpperTheory.V.AlgebraTools.Det.genEval D' (MvPolynomial σ A') m (fun j => MonoidAlgebra.single (g j) 1) (fun j => MvPolynomial.map ι (b j))
  refine ⟨MvPolynomial.aeval b Q, ?_⟩
  have hx : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial σ A)) (MonoidAlgebra.single (g j) 1)) = ∑ j, (MvPolynomial.map ι (b j)) • MonoidAlgebra.mapRingHom G (algebraMap A' (MvPolynomial σ A')) (MonoidAlgebra.single (g j) 1) := by

    simp [map_sum, MonoidAlgebra.mapRingHom_single]
  rw [hx, key, ← hQ, MvPolynomial.map_aeval]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]


private theorem mapRingHom_gdet_gen_single_eq_gen_single {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A')
    (m : ℕ) (g : Fin m → G) :
    MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (GDet.gen (A := A) fun j => MonoidAlgebra.single (g j) 1) =
      GDet.gen (A := A') fun j => MonoidAlgebra.single (g j) 1 := by

  simp [GDet.gen, map_sum, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.AlgebraTools.Det.descend :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range) →
    ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι hc
  have hr := fun σ x => exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom ι D' hc σ x
  have hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ := σ) ι) :=
    fun σ => MvPolynomial.map_injective ι hι
  let d : (σ : Type) → MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A := fun σ =>
    { toFun := fun x => Classical.choose (hr σ x)
      map_one' := hinj σ (by rw [Classical.choose_spec (hr σ 1), map_one, map_one, map_one])
      map_mul' := fun x y => hinj σ (by
        rw [Classical.choose_spec (hr σ (x * y)), map_mul, map_mul, map_mul,
          Classical.choose_spec (hr σ x), Classical.choose_spec (hr σ y)]) }
  have hd : ∀ σ x, MvPolynomial.map ι (d σ x) =
      D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) :=
    fun σ x => Classical.choose_spec (hr σ x)
  have hnat : ∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x) := by
    intro σ τ f x
    apply hinj τ
    let f' : MvPolynomial σ A' →ₐ[A'] MvPolynomial τ A' :=
      MvPolynomial.aeval fun i => MvPolynomial.map ι (f (MvPolynomial.X i))
    have hf : (MvPolynomial.map ι).comp (f : MvPolynomial σ A →+* MvPolynomial τ A) =
        (f' : MvPolynomial σ A' →+* MvPolynomial τ A').comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have ha := f.commutes a
        simp only [MvPolynomial.algebraMap_eq] at ha
        simp [f', ha]
      · intro i
        simp [f']
    have e1 : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) =
        MonoidAlgebra.mapRingHom G (f' : MvPolynomial σ A' →+* MvPolynomial τ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) := by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hf, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
    rw [hd, e1, D'.nat (MvPolynomial σ A') (MvPolynomial τ A') f', ← hd]
    exact (RingHom.congr_fun hf _).symm
  have hhom : ∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d σ (b • x) = b ^ n * d σ x := by
    intro σ b x
    apply hinj σ
    have hs : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (b • x) =
        MvPolynomial.map ι b • MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply]
    rw [hd, map_mul, map_pow, hd, hs, D'.homog]
  obtain ⟨D, hD⟩ := UpperTheory.V.AlgebraTools.Det.extendPoly d hnat hhom
  have hex : D.map ι = D' := by
    apply UpperTheory.V.AlgebraTools.Det.extGen
    intro m g
    rw [← mapRingHom_gdet_gen_single_eq_gen_single ι m g, (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.1 (Fin m), hD, hd]
  refine ⟨D, hex, fun D2 h2 => ?_⟩
  exact (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => ι)
    (fun a ha => hι (by rw [ha (), map_zero])) ).1 D2 D (fun _ => by rw [h2, hex])
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.kerTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (D : GDet n A G),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, D.map (f x) = GDet.ofRep (ρ x)) →
    ∀ y : MonoidAlgebra A G, (∀ x, GDet.repAlg (ρ x) (K x) (MonoidAlgebra.mapRingHom G (f x) y) = 0) → D.Kills y := by
  intro n A G _ _ X K _ f ρ D hf hD y hy
  refine (UpperTheory.V.AlgebraTools.Det.injTest K f hf).2 D y fun x => ?_
  rw [hD x]
  exact (UpperTheory.V.AlgebraTools.Det.repApi (ρ x)).2.2.2.2.1 _ (hy x)
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem repAlg_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (B : Type) [CommRing B] [Algebra R B] (g : G) (b : B) :
    GDet.repAlg ρ B (MonoidAlgebra.single g b) = b • (ρ g).map (algebraMap R B) := by
  simp [GDet.repAlg]

private theorem UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (B : Type) [CommRing B] [Algebra R B]
    [Algebra O B] [IsScalarTower O R B] (g : F.G₀) (k : ℤ) :
    ((F.eps O B g ^ k : Bˣ) : B) = algebraMap R B ((F.eps O R g ^ k : Rˣ) : R) := by
  have e : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
    ext
    simp [GFrame.eps, IsScalarTower.algebraMap_apply O R B]
  rw [e, ← map_zpow]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.formRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) {a : ℕ} (r : F.G₀ →* GL (Fin a) R) (P : GL (Fin a) R), F.IsForm O n r P →
    (∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y)) ∧
    (∀ y, GDet.repAlg (mat r) R y = 0 → GDet.repAlg (mat r) R (F.star O R n y) = 0) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.ofRep (mat r)).D B (F.star O B n y) = (GDet.ofRep (mat r)).D B y := by
  intro l _ F O _ _ R _ _ n a r P hP
  have h1 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y) := by
    intro B _ _ _ _ y
    let ρ' : F.G₀ →* Matrix (Fin a) (Fin a) B := (algebraMap R B).mapMatrix.toMonoidHom.comp (mat r)
    have hρ : ∀ g, (mat r g).map (algebraMap R B) = ρ' g := fun g => rfl
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add x z hx hz =>
      rw [(UpperTheory.V.AlgebraTools.Det.starApi F O B n).2.2.1, map_add (f := _), map_add (f := _), Matrix.transpose_add, Matrix.add_mul,
        Matrix.mul_add, hx, hz]
    | single g b =>
      have hs : F.star O B n (MonoidAlgebra.single g b) =
          MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
        simp [GFrame.star, GFrame.starOp]
      rw [hs, repAlg_single, repAlg_single, hρ, hρ, UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq F O R B]
      have hF : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) := by
        have := congrArg (fun M : Matrix (Fin a) (Fin a) R => M.map (algebraMap R B)) (hP g)
        have h' : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
            ((((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R)) • (P : Matrix (Fin a) (Fin a) R)).map (algebraMap R B) := by
          simpa [Matrix.map_mul, Matrix.transpose_map, ρ'] using this
        rw [h']
        ext i j
        simp
      have hinv : ρ' (F.conj g) * ρ' (F.conj g)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have key : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) •
            ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g)⁻¹) := by
        calc (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)
            = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * (ρ' (F.conj g) * ρ' (F.conj g)⁻¹) := by
              rw [hinv, Matrix.mul_one]
          _ = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) * ρ' (F.conj g)⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hF, Matrix.smul_mul]
      rw [Matrix.transpose_smul, Matrix.smul_mul, key, Matrix.mul_smul, smul_smul]
  have hu : ∀ (B : Type) [CommRing B] [Algebra R B],
      IsUnit ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)) := by
    intro B _ _
    exact (P.isUnit.map (algebraMap R B).mapMatrix)
  refine ⟨h1, ?_, ?_⟩
  · intro y hy
    have := h1 R y
    rw [hy, Matrix.transpose_zero, Matrix.zero_mul] at this
    obtain ⟨u, hu'⟩ := hu R
    have h2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin a) (Fin a) R) * M) this
    simp only [← hu', Matrix.mul_zero, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2.symm
  · intro B _ _ _ _ y
    have := congrArg Matrix.det (h1 B y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm] at this
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (hu B)
    exact (hd.mul_left_cancel this).symm
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.oElRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ), HasFlag (r.comp (F.φ v)) ψ →
    ∀ g, GDet.repAlg (mat r) R (F.oEl v ψ g) = 0 := by
  intro l _ F O _ _ R _ _ n r v ψ h g
  rw [← (UpperTheory.V.AlgebraTools.Det.flagRel _ _ h).2 g, GFrame.oEl, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [GDet.repAlg, mat, MonoidAlgebra.lift_single]
end
