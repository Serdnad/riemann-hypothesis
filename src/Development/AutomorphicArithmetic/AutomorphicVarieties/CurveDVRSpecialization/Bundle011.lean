module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001

@[expose] public section

section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr.LkPt2

open Matrix

section Mat

variable {A : Type} [CommRing A]

private def Bl (X : Matrix (Fin 3) (Fin 3) A) : Prop := X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0

private theorem c00 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 0 = X 0 0 := rfl
private theorem c01 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 1 = X 0 2 := rfl
private theorem c10 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 0 = X 2 0 := rfl
private theorem c11 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 1 = X 2 2 := rfl

private theorem corner_mul {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (Y : Matrix (Fin 3) (Fin 3) A) :
    corner (X * Y) = corner X * corner Y := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private theorem corner_one : corner (1 : Matrix (Fin 3) (Fin 3) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem corner_sub (X : Matrix (Fin 3) (Fin 3) A) (a : A) :
    corner (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) = corner X - a • (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem block_sub {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (a : A) :
    Bl (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [*]

private theorem corner_J (X : Matrix (Fin 3) (Fin 3) A) :
    corner (Jmat A 3 * Xᵀ * Jmat A 3) = Jmat A 2 * (corner X)ᵀ * Jmat A 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev]

private theorem ch2 (S : Matrix (Fin 2) (Fin 2) A) (y : A) :
    ((S.trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - S) * (S - y • 1) = (S - y • 1).det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

private theorem drop_mid {H : Type} [Group H] (σ : H →* Matrix (Fin 2) (Fin 2) A) (ψ : H →* Aˣ) (t : H) (y : A)
    (Z : Matrix (Fin 2) (Fin 2) A) (hu : IsUnit (σ t - y • 1).det)
    (h : ∀ a, (σ a - (ψ a : A) • 1) * ((σ t - y • 1) * Z) = 0) (a : H) : (σ a - (ψ a : A) • 1) * Z = 0 := by
  have e : (σ a - (ψ a : A) • 1) * (((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) =
      ((σ t).trace - y) • (σ a - (ψ a : A) • 1) - (σ (a * t) - (ψ (a * t) : A) • 1) +
        (ψ a : A) • (σ t - (ψ t : A) • 1) := by
    rw [map_mul, map_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul (σ a) _ (σ t), Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.one_mul, smul_sub (ψ a : A), smul_smul]
    abel
  have e2 : (σ t - y • 1).det • ((σ a - (ψ a : A) • 1) * Z) = 0 := by
    calc _ = (σ a - (ψ a : A) • 1) * ((((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) * (σ t - y • 1)) * Z := by
          rw [ch2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 0 := by
          rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
            h, h, h]
          simp
  exact (hu.smul_eq_zero).1 e2

end Mat

private theorem w_eq (i : Fin 2) : Fr.w 2 i = Fr.w 3 (![0, 2] i) := by fin_cases i <;> rfl

private theorem w_eq' (i : Fin 2) : Fr.w 2 i = wt1 (![0, 2] i) := by fin_cases i <;> rfl

private theorem ne_of {i j : Fin 2} (h : i ≠ j) : (![0, 2] i : Fin 3) ≠ ![0, 2] j := by
  revert h; fin_cases i <;> fin_cases j <;> decide

private theorem ex_block {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Fr.Frame l (ResidueField O)}
    (f3 : ∀ v, ∃ g, F.Ψ (F.loc v g) ^ 2 ≠ 1) {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsLocalHom (algebraMap O A)] (ρ : Fr.NRep F 3 A) (hρ : IsLiftA O ρ) (hb : ∀ g, Bl (ρ.r g)) :
    ∃ ρ' : Fr.NRep F 2 A, IsLiftA O ρ' ∧ (∀ g, ρ'.r g = corner (ρ.r g)) ∧ ∀ v i, ρ'.ψ v i = ρ.ψ v (![0, 2] i) := by
  let σ : F.G0 →* Matrix (Fin 2) (Fin 2) A :=
    { toFun := fun g => corner (ρ.r g)
      map_one' := by rw [map_one, corner_one]
      map_mul' := fun g h => by rw [map_mul, corner_mul (hb g)] }
  have hσ : ∀ g, σ g = corner (ρ.r g) := fun _ => rfl
  refine ⟨⟨σ, fun v i => ρ.ψ v (![0, 2] i), fun g => ?_, fun i j h => ρ.diag _ _ (ne_of h), fun v g => ?_⟩,
    ⟨⟨fun i j => hρ.cont.1 _ _, fun v i => hρ.cont.2 v _⟩, ⟨fun g i => ?_, fun v i g => ?_⟩,
      fun g i j h => hρ.diag g _ _ (ne_of h)⟩, fun _ => rfl, fun _ _ => rfl⟩
  · rw [hσ, hσ, ρ.pol, corner_J]
  · obtain ⟨t, ht⟩ := f3 v
    have hu : IsUnit (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det := by
      rw [← residue_ne_zero_iff_isUnit]
      have a0 := hρ.bar.1 (F.loc0 v t) 0
      have a2 := hρ.bar.1 (F.loc0 v t) 2
      have b1 := hρ.bar.2 v 1 t
      have c0 := hρ.diag (F.loc0 v t) 0 2 (by decide)
      rw [Fr.NRep.map_r] at a0 a2 c0
      rw [Fr.NRep.map_ψ] at b1
      have w0 : Fr.w 3 0 = 1 := rfl
      have w1 : Fr.w 3 1 = 0 := rfl
      have w2 : Fr.w 3 2 = -1 := rfl
      rw [w0, zpow_one] at a0
      rw [w1, zpow_zero, Units.val_one, map_one] at b1
      rw [w2, _root_.zpow_neg_one] at a2
      have hne : F.Ψ (F.loc0 v t : F.Γ) ≠ 1 := fun e => ht (by
        show F.Ψ (F.loc0 v t : F.Γ) ^ 2 = 1
        rw [e, one_pow])
      have key : ∀ u : (ResidueField O)ˣ, u ≠ 1 → ResidueField.map (algebraMap O A) u - 1 ≠ 0 := fun u hu e => by
        rw [sub_eq_zero, ← map_one (ResidueField.map (algebraMap O A))] at e
        exact hu (Units.ext ((ResidueField.map (algebraMap O A)).injective e))
      have : residue A (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det =
          (residue A (ρ.r (F.loc0 v t) 0 0) - residue A (ρ.ψ v 1 t)) *
            (residue A (ρ.r (F.loc0 v t) 2 2) - residue A (ρ.ψ v 1 t)) -
            residue A (ρ.r (F.loc0 v t) 0 2) * residue A (ρ.r (F.loc0 v t) 2 0) := by
        simp [Matrix.det_fin_two, hσ, c00, c01, c10, c11]
      rw [this, a0, a2, b1, c0, zero_mul, sub_zero]
      exact mul_ne_zero (key _ hne) (key _ (inv_ne_one.2 hne))
    have := drop_mid (σ.comp (F.loc0 v)) (ρ.ψ v 0) t (ρ.ψ v 1 t : A)
      (σ (F.loc0 v (g 1)) - (ρ.ψ v 2 (g 1) : A) • 1) hu (fun a => by
        have h := congrArg corner (ρ.ord v ![a, t, g 1])
        simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h
        rw [corner_mul (block_sub (hb _) _), corner_mul (block_sub (hb _) _), corner_sub, corner_sub, corner_sub] at h
        exact h) (g 0)
    simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact this
  · rw [w_eq]
    exact hρ.bar.1 g _
  · rw [w_eq]
    exact hρ.bar.2 v _ g

end UpperTheory.V.Pr.LkPt2

open UpperTheory.V.Pr.LkPt2 in
theorem UpperTheory.V.Pr.exists_nrep2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)] (r : G ℚ Ω →* GG (m := 3) (R := A)), OrdPt l η Ψ σ g₁ B r → Block η r → ∃ ρ : Fr.NRep Φ 2 A, IsLiftA O ρ ∧ (∀ s : G L Ω, ρ.r (k.p0 s) = corner (r (Base.galEmb ℚ L Ω s)).mat) ∧
      ∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g : A) = algebraMap O A ((Ψ (k.j v g) ^ Fr.w 2 i : Oˣ) : O) := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hM hσ A _ _ _ _ _ _ r hr hb
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hM hσ r hr
  have hbl : ∀ g, Bl (ρ.r g) := fun g => by
    obtain ⟨u, hu⟩ := k.p_surj g.1
    have hη : η u = 1 := by rw [← k.del, hu]; exact g.2
    have hm : u.1 ∈ (Base.galEmb ℚ L Ω).range := by
      rw [Base.range_galEmb, k.gal]
      exact ⟨u.2, hη⟩
    obtain ⟨s, hs⟩ := hm
    have e : g = k.p0 s := Subtype.ext (hu.symm.trans (congrArg k.p (Subtype.ext hs.symm)))
    rw [e, h2, hs]
    exact ⟨hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide)⟩
  obtain ⟨ρ', a1, a2, a3⟩ := ex_block hok.f3 ρ h1 hbl
  refine ⟨ρ', a1, fun s => by rw [a2, h2], fun v i g hg => ?_⟩
  rw [a3, h3 v _ g hg, w_eq']
  rfl
end

section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.finEnd_of_finPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    FinPt O Φ 3 → FinEnd l η Ψ σ g₁ B := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hl hσ hF
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have hidx : (Base.galOf ℚ L Ω).index = Module.finrank ℚ L := (Base.galEmbTop ℚ L Ω).2.2
  refine ⟨Base.galOf ℚ L Ω, ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩, ?_⟩
  intro A _ _ _ h0 r hr g hg _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  let f : ResidueField O →+* A := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O A) h0
  have hf : ∀ a : O, f (residue O a) = algebraMap O A a := fun a => rfl
  letI : Algebra (ResidueField O) A := f.toAlgebra
  haveI : IsScalarTower O (ResidueField O) A := IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hpow : ∀ (s : G ℚ Ω) (n : ℤ), algebraMap O A ((Ψ s ^ n : Oˣ) : O) =
      f ((barChar O Ψ s ^ n : (ResidueField O)ˣ) : ResidueField O) := by
    intro s n
    rw [← hf]
    congr 1
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ s) n)
  have key := hF A ρ h1 (by
    intro v i g hg h
    apply Units.ext
    rw [h3 v i g hg, UnitaryThreeInertia.psi, hpow]
    rw [k.j_loc, k.psi] at h
    rw [h]; simp)
  obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
  rw [← h2, key]
  have : ((r0 η Ψ (Base.galEmb ℚ L Ω s)).mat).map (algebraMap O A) = Matrix.diagonal fun i =>
      algebraMap O A ((Ψ (Base.galEmb ℚ L Ω s) ^ wt1 i : Oˣ) : O) := by
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
  rw [this, Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hpow]
  have h5 : Φ.Ψ (k.p0 s) = barChar O Ψ (Base.galEmb ℚ L Ω s) := k.psi _
  have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
  rw [h5, h6]
  rfl
end

section

theorem UpperTheory.V.Pr.coefIs :
    UpperTheory.V.Pr.CoefIs := by
  intro l hl c
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, ?_⟩
  have h0 : (l : IsLocalRing.ResidueField c.O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  exact (CharP.charP_iff_prime_eq_zero hl.out).2 h0
end

section

open IsLocalRing Matrix Polynomial UpperTheory.V.W

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  simp only [GDet.chi, GDet.map, GDet.ofRep]
  rw [Matrix.charpoly]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Matrix.coe_detMonoidHom]
  congr 1
  simp only [MonoidAlgebra.mapRingHom_single, map_one, GDet.repAlg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_sub, MonoidAlgebra.lift_single]
  refine Matrix.ext fun i k => ?_
  simp [Matrix.charmatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [Matrix.diagonal_apply]
  rfl

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Polynomial.map_add (f := _), hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, RingHom.mapMatrix_apply, apply_ite f]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    have hpow : N ^ k * Y = Y * M ^ k := by
      induction k with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
    rw [mul_assoc, hpow, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem key {n : ℕ} {A K F : Type} [CommRing A] [Field K] [Field F] (f : A →+* K) (j : A →+* F)
    (hj : Function.Injective j) (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) F)
    (hY : j x • (j.mapMatrix M * Y) = Y * j.mapMatrix M) : Y = 0 := by
  classical
  set p := M.charpoly with hp
  set Mf := f.mapMatrix M with hMf
  set Mj := j.mapMatrix M with hMj
  have hint : aeval (j x • Mj) (p.map j) * Y = Y * aeval Mj (p.map j) :=
    aeval_inter Mj (j x • Mj) Y (by rw [smul_mul_assoc]; exact hY) _
  have hCH : aeval Mj (p.map j) = 0 := by
    rw [hp, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  rw [hCH, mul_zero] at hint
  have hfc : Mf.charpoly = (X - C c) ^ n := by
    rw [hMf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    exact hM
  set Nl := Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c with hNl
  have hnil : IsNilpotent Nl := by
    refine ⟨n, ?_⟩
    have h0 := Matrix.aeval_self_charpoly Mf
    rw [hfc, map_pow, map_sub, aeval_X, aeval_C] at h0
    exact h0
  set s : K := (f x - 1) * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hx) hc
  have hunitF : IsUnit (aeval (f x • Mf) (p.map f)) := by
    rw [hp, hM, map_pow, map_sub, aeval_X, aeval_C]
    apply IsUnit.pow
    have heq : f x • Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c =
        algebraMap K (Matrix (Fin n) (Fin n) K) s * ((s⁻¹ * f x) • Nl + 1) := by
      rw [← Algebra.smul_def, smul_add, smul_smul, mul_inv_cancel_left₀ hs0, hNl, hs,
        Algebra.algebraMap_eq_smul_one]
      module
    rw [heq]
    exact (IsUnit.map _ (Ne.isUnit hs0)).mul (hnil.smul _).isUnit_add_one
  set D : A := (aeval (x • M) p).det with hD
  have hfD : f D ≠ 0 := by
    have hsm : f.mapMatrix (x • M) = f x • Mf := by
      ext i k
      simp [hMf]
    have h1 : f D = (aeval (f x • Mf) (p.map f)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunitF).ne_zero
  have hD0 : D ≠ 0 := fun h => hfD (by rw [h, map_zero])
  have hjD : (aeval (j x • Mj) (p.map j)).det ≠ 0 := by
    have hsm : j.mapMatrix (x • M) = j x • Mj := by
      ext i k
      simp [hMj]
    have h1 : j D = (aeval (j x • Mj) (p.map j)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [← h1]
    exact fun h => hD0 (hj (by rw [h, map_zero]))
  have hU : IsUnit (aeval (j x • Mj) (p.map j)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hjD)
  exact (hU.mul_right_eq_zero).mp hint

private theorem absolute_irreducible_rank_four {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (h : r.V0ok) (y : Point r) : y.N4 := by
  intro X hX
  obtain ⟨-, hchi, g, hg, heps⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext i
    exact i.elim0
  letI := y.field
  haveI := y.fin
  letI := y.algk
  letI := y.algO
  haveI := y.tower
  let i0 : Fin n := ⟨0, hn⟩
  let z : O := algebraMap ℤ_[l] O (F.ε g)
  let c : y.K := algebraMap (ResidueField O) y.K (r.chib i0 g)
  refine key (PowerSeries.constantCoeff) (algebraMap y.A y.Fr) (IsFractionRing.injective _ _) (mat y.ρ g)
    (algebraMap O y.A z) c ?_ ?_ ?_ X ?_
  · exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  · intro h1
    apply heps
    apply Units.ext
    apply (algebraMap (ResidueField O) y.K).injective
    rw [Units.val_one, map_one, ← h1]
    show algebraMap (ResidueField O) y.K (algebraMap O (ResidueField O) z) =
      PowerSeries.constantCoeff (algebraMap O y.A z)
    rw [← IsScalarTower.algebraMap_apply]
    first
    | rfl
    | simp [PowerSeries.algebraMap_apply']
  · have hred := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at hred
    rw [hred]
    show Polynomial.map _ (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).charpoly = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hall : ∀ i : Fin n, (Polynomial.X - C (algebraMap (ResidueField O) y.K ↑((r.chib i) g))) =
        Polynomial.X - C c := fun i => by rw [hchi g hg i i0]
    simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have := hX g hg
    exact this

theorem UpperTheory.V.Pr.n4Of :
    UpperTheory.V.Pr.EveryPointSatisfiesFrameCondition := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ k c₁ _ f n ka R y
  exact absolute_irreducible_rank_four R.v0 y
end

section

theorem UpperTheory.V.Pr.dimOf :
    UpperTheory.V.Pr.DimOf := by
  intro O Λ B _ _ _ _ _ _ _ φ J m ⟨e⟩ hfin htf Z hZ
  haveI : NoZeroDivisors O := IsDomain.to_noZeroDivisors O
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalRing O := IsDiscreteValuationRing.toIsLocalRing
  haveI : NoZeroDivisors (MvPowerSeries (Fin m) O) := inferInstance
  haveI : Nontrivial (MvPowerSeries (Fin m) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin m) O) := NoZeroDivisors.to_isDomain _
  haveI : IsDomain Λ := e.toMulEquiv.isDomain
  letI : Algebra Λ (B ⧸ J) := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  haveI : Module.Finite Λ (B ⧸ J) := hfin
  haveI : Algebra.IsIntegral Λ (B ⧸ J) := Algebra.IsIntegral.of_finite Λ (B ⧸ J)
  have hJZ : J ≤ Z := hZ.1.2
  have hZ' := hZ
  rw [Ideal.minimalPrimes_eq_comap] at hZ'
  obtain ⟨P, hP, rfl⟩ := hZ'
  have hnz : ∀ a : Λ, a ≠ 0 → algebraMap Λ (B ⧸ J) a ∈ nonZeroDivisors (B ⧸ J) := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine htf a ha b ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hx
  have h := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component Λ (B ⧸ J) hnz P hP).2.2
  have hq : ringKrullDim (B ⧸ P.comap (Ideal.Quotient.mk J)) = ringKrullDim ((B ⧸ J) ⧸ P) := by
    have hs : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hk : P.comap (Ideal.Quotient.mk J)
        = RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) := by
      ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
    rw [hk]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs)
  show ringKrullDim _ = _
  rw [hq, h, ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
end
