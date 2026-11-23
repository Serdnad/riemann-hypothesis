module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyHamiltonSymmetric
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_rep_conj_chi_smul_and_q_twisted {K : Type} [Field K] {n : ℕ} (u v r ri r' ri' : Matrix (Fin n) (Fin n) K) (e : K)
    (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1) (hr' : r' * ri' = 1)
    (hA : rᵀ * u * r' = e • u) (X : Matrix (Fin n) (Fin n) K) :
    -(v * (r * X * ri)ᵀ * u) = r' * -(v * Xᵀ * u) * ri' := by
  have hrT : riᵀ * rᵀ = 1 := by rw [← Matrix.transpose_mul, hr, Matrix.transpose_one]
  have h1 : u * r' = e • (riᵀ * u) := by
    calc u * r' = riᵀ * (rᵀ * u * r') := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrT, Matrix.one_mul]
      _ = e • (riᵀ * u) := by rw [hA, Matrix.mul_smul]
  have h2 : ∀ Z, r' * (v * Z) = e • (v * (riᵀ * Z)) := by
    intro Z
    calc r' * (v * Z) = v * (u * r') * (v * Z) := by
          rw [← Matrix.mul_assoc v u r', hvu, Matrix.one_mul]
      _ = e • (v * (riᵀ * Z)) := by
          rw [h1]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc u v Z, huv, Matrix.one_mul]
  have hA' : rᵀ * (u * r') = e • u := by rw [← Matrix.mul_assoc]; exact hA
  have h3 : -(v * (r * X * ri)ᵀ * u) * r' = r' * -(v * Xᵀ * u) := by
    simp only [Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hA', h2,
      Matrix.mul_smul]
  calc -(v * (r * X * ri)ᵀ * u) = -(v * (r * X * ri)ᵀ * u) * (r' * ri') := by
        rw [hr', Matrix.mul_one]
    _ = r' * -(v * Xᵀ * u) * ri' := by rw [← Matrix.mul_assoc, h3]

private theorem u_mul_ri_mul_v_eq_transpose_of_eigen {K : Type} [Field K] {n : ℕ} (u v A r ri : Matrix (Fin n) (Fin n) K) (e : K)
    (he : e ≠ 0) (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1)
    (h1 : A * u * r = e • u) (h2 : A * uᵀ * r = e • uᵀ) : u * ri * v = uᵀ * ri * vᵀ := by
  have huvT : uᵀ * vᵀ = 1 := by rw [← Matrix.transpose_mul, hvu, Matrix.transpose_one]
  have hA1 : A = e • (u * ri * v) := by
    calc A = A * u * r * ri * v := by
          rw [Matrix.mul_assoc (A * u) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A u v, huv,
            Matrix.mul_one]
      _ = e • (u * ri * v) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  have hA2 : A = e • (uᵀ * ri * vᵀ) := by
    calc A = A * uᵀ * r * ri * vᵀ := by
          rw [Matrix.mul_assoc (A * uᵀ) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A uᵀ vᵀ, huvT,
            Matrix.mul_one]
      _ = e • (uᵀ * ri * vᵀ) := by rw [h2, Matrix.smul_mul, Matrix.smul_mul]
  exact smul_right_injective _ he (hA1.symm.trans hA2)

private theorem neg_conj_neg_transpose_eq_self_of_symm {K : Type} [Field K] {n : ℕ} (u v X : Matrix (Fin n) (Fin n) K)
    (hvu : v * u = 1) (hS : u * X * v = uᵀ * X * vᵀ) : -(v * (-(v * Xᵀ * u))ᵀ * u) = X := by
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc uᵀ X vᵀ, ← hS, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  simp only [Matrix.mul_assoc]
  rw [hvu, Matrix.mul_one, ← Matrix.mul_assoc, hvu, Matrix.one_mul]

theorem UpperTheory.V.Ws.Eb.adExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K), Full ρ → F.IsForm O n ρ P →
        ∃ R : Representation K F.Γ (Matrix (Fin n) (Fin n) K), IsAdExt F ρ P R := by
  intro l _ F O _ _ K _ _ n ρ P hFull hForm
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hconjv : ∀ g : F.G₀, ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c := by
    intro g
    show F.c * ↑g * F.c⁻¹ = _
    rw [hci]
  have hconj2 : ∀ g : F.G₀, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    rw [hconjv, hconjv]
    simp only [mul_assoc, hcc, mul_one, hcc']
  have heps : ∀ g : F.G₀, F.eps O K (F.conj g) = F.eps O K g := by
    intro g
    simp [W.GFrame.eps, W.GFrame.conj, W.pushCh]
  have hF : ∀ g : F.G₀, (↑(ρ g) : Matrix (Fin n) (Fin n) K)ᵀ * (↑P : Matrix (Fin n) (Fin n) K) *
      (↑(ρ (F.conj g)) : Matrix (Fin n) (Fin n) K) =
      ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (↑P : Matrix (Fin n) (Fin n) K) := hForm
  have huv : (↑P : Matrix (Fin n) (Fin n) K) * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv P
  have hvu : (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * (↑P : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul P
  have hS : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑P : Matrix (Fin n) (Fin n) K) * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) =
      (↑P : Matrix (Fin n) (Fin n) K)ᵀ * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ := by
    intro X
    have hX : X ∈ Submodule.span K (Set.range (W.mat ρ)) := by
      have h : Submodule.span K (Set.range (W.mat ρ)) = ⊤ := hFull
      rw [h]
      exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e1 := hF (F.conj h⁻¹)
      rw [hconj2] at e1
      have e2 := congrArg Matrix.transpose (hF h⁻¹)
      rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc, ← heps h⁻¹] at e2
      refine u_mul_ri_mul_v_eq_transpose_of_eigen _ _ ((↑(ρ (F.conj h⁻¹)) : Matrix (Fin n) (Fin n) K)ᵀ) (↑(ρ h⁻¹)) _ _
        (Units.ne_zero _) huv hvu ?_ e1 e2
      show (↑(ρ h⁻¹) : Matrix (Fin n) (Fin n) K) * (↑(ρ h) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => simp only [Matrix.mul_smul, Matrix.smul_mul, hx]
  let θ : Module.End K (Matrix (Fin n) (Fin n) K) :=
    { toFun := fun X => -((↑P⁻¹ : Matrix (Fin n) (Fin n) K) * Xᵀ * (↑P : Matrix (Fin n) (Fin n) K))
      map_add' := fun X Y => by
        simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
      map_smul' := fun a X => by
        simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
          RingHom.id_apply] }
  have hkey : ∀ g : F.G₀, θ * Loc.adGL ρ g = Loc.adGL ρ (F.conj g) * θ := by
    intro g
    apply LinearMap.ext
    intro X
    exact exists_rep_conj_chi_smul_and_q_twisted _ _ _ _ _ _ _ huv hvu (Units.mul_inv _) (Units.mul_inv _) (hF g) X
  have hθθ : θ * θ = 1 := by
    apply LinearMap.ext
    intro X
    exact neg_conj_neg_transpose_eq_self_of_symm _ _ X hvu (hS X)
  have hker : ∀ γ : F.Γ, F.η γ ≠ 1 → γ * F.c ∈ F.η.ker := by
    intro γ h
    rw [MonoidHom.mem_ker, map_mul, F.η_c]
    rcases Int.units_eq_one_or (F.η γ) with h' | h'
    · exact absurd h' h
    · rw [h']
      exact Int.units_mul_self _
  have hAd : ∀ x y : F.G₀, (x : F.Γ) = y → Loc.adGL ρ x = Loc.adGL ρ y := by
    intro x y hxy
    rw [Subtype.ext hxy]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  let f : F.Γ → Module.End K (Matrix (Fin n) (Fin n) K) := fun γ =>
    if h : F.η γ = 1 then Loc.adGL ρ ⟨γ, h⟩ else Loc.adGL ρ ⟨γ * F.c, hker γ h⟩ * θ
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ⟨?_, ?_⟩⟩
  · show f 1 = 1
    simp only [f, dif_pos (map_one F.η)]
    exact map_one (Loc.adGL ρ)
  · intro a b
    show f (a * b) = f a * f b
    have hab : F.η (a * b) = F.η a * F.η b := map_mul _ _ _
    rcases Int.units_eq_one_or (F.η a) with ha | ha <;>
      rcases Int.units_eq_one_or (F.η b) with hb | hb
    · have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb, one_mul]
      simp only [f, dif_pos ha, dif_pos hb, dif_pos h1]
      rw [← map_mul (Loc.adGL ρ)]
      exact hAd _ _ rfl
    · have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, one_mul]; exact hne
      simp only [f, dif_pos ha, dif_neg hb', dif_neg h1]
      rw [← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [mul_assoc])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, mul_one]; exact hne
      simp only [f, dif_neg ha', dif_pos hb, dif_neg h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, hkey, ← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc'])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb]; exact Int.units_mul_self _
      simp only [f, dif_neg ha', dif_neg hb', dif_pos h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, ← mul_assoc θ, hkey, mul_assoc (Loc.adGL ρ _) θ θ, hθθ,
        mul_one, ← map_mul (Loc.adGL ρ)]
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc, hcc'])
  · intro g X
    show f ↑g X = _
    simp only [f, dif_pos (MonoidHom.mem_ker.mp g.2)]
  · intro X
    show f F.c X = _
    have hn : ¬ F.η F.c = 1 := by rw [F.η_c]; exact hne
    simp only [f, dif_neg hn]
    rw [Module.End.mul_apply]
    have h1 : ∀ p, (⟨F.c * F.c, p⟩ : F.G₀) = 1 := fun p => Subtype.ext hcc
    rw [h1, map_one]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dmk {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (DualNumber K) := Matrix.of fun i j => (⟨A i j, B i j⟩ : DualNumber K)

private theorem dmk_mul {K : Type} [CommRing K] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) K) :
    dmk A B * dmk C D = dmk (A * C) (A * D + B * C) := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    simp only [TrivSqZeroExt.fst_mul, hf]
  · rw [hs, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [TrivSqZeroExt.snd_mul, hf, hs, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

private theorem dmk_one {K : Type} [CommRing K] {n : ℕ} :
    dmk (1 : Matrix (Fin n) (Fin n) K) 0 = 1 := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hs, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.conjOf :
    ∀ {K H : Type} [CommRing K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (X : Matrix (Fin n) (Fin n) K), IsTan ρ y ρ' → (∀ g, y g = Loc.adGL ρ g X - X) →
        ∃ Q : GL (Fin n) (DualNumber K), ∀ g, ρ' g = Q * W.pushRep (algebraMap K (DualNumber K)) ρ g * Q⁻¹ := by
  intro K H _ _ n ρ y ρ' X hT hy
  unfold IsTan at hT
  have hinv : dmk (1 : Matrix (Fin n) (Fin n) K) (-X) * dmk 1 X = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  have hinv' : dmk (1 : Matrix (Fin n) (Fin n) K) X * dmk 1 (-X) = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  refine ⟨⟨dmk 1 (-X), dmk 1 X, hinv, hinv'⟩, fun g => ?_⟩
  have hp : ((W.pushRep (algebraMap K (DualNumber K)) ρ g : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) = dmk (ρ g : Matrix (Fin n) (Fin n) K) 0 := by
    ext i j
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
  have hyg : y g * (ρ g : Matrix (Fin n) (Fin n) K) = 1 * (ρ g : Matrix (Fin n) (Fin n) K) * X + (1 * 0 + -X * (ρ g : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [hy g]
    simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, mul_one, one_mul, mul_zero, zero_add, neg_mul, sub_eq_add_neg]
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, neg_mul]
  ext i j : 2
  rw [Units.val_mul, Units.val_mul, hp, Units.inv_mk]
  rw [dmk_mul, dmk_mul, hT g i j, ← hyg]
  simp only [one_mul, mul_one]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cr_fst_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst :=
  Matrix.map_mul (f := dF K)

private theorem cr_snd_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, mul_comm]

private theorem cr_alg {K : Type} [CommRing K] {n : ℕ} (A B P Q y y' Ai Bi Pi : Matrix (Fin n) (Fin n) K) (e : K)
    (hA : Ai * A = 1) (hB : B * Bi = 1) (hP : Pi * P = 1) (hP' : P * Pi = 1)
    (h1 : Aᵀ * P * B = e • P)
    (h2 : Aᵀ * P * (y' * B) + (Aᵀ * Q + (y * A)ᵀ * P) * B = e • Q) :
    y' = -(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q) := by
  have hBi : Bi * B = 1 := mul_eq_one_comm.mp hB
  have hAi : A * Ai = 1 := mul_eq_one_comm.mp hA
  have canc : ∀ X : Matrix (Fin n) (Fin n) K, Pi * Aiᵀ * (Aᵀ * P * X * B) * Bi = X := by
    intro X
    simp only [Matrix.mul_assoc]
    rw [hB, Matrix.mul_one, ← Matrix.mul_assoc Aiᵀ Aᵀ, ← Matrix.transpose_mul, hAi, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc Pi P, hP, Matrix.one_mul]
  have lhs : Aᵀ * P * y' * B = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    rw [Matrix.transpose_mul] at h2
    rw [← h2]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
    abel
  have rhs : Aᵀ * P * (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)) * B
      = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    have t1 : Aᵀ * P * (Pi * yᵀ * P) * B = Aᵀ * (yᵀ * (P * B)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    have t2 : Aᵀ * P * (B * (Pi * Q) * Bi) * B = e • Q := by
      calc Aᵀ * P * (B * (Pi * Q) * Bi) * B = (Aᵀ * P * B) * (Pi * Q) * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = e • Q := by
            rw [h1, hBi, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_assoc, hP', Matrix.one_mul]
    have t3 : Aᵀ * P * (Pi * Q) * B = Aᵀ * (Q * B) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, t1, t2, t3]
    abel
  rw [← canc y', ← canc (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)), lhs, rhs]

theorem UpperTheory.V.Ws.Eb.cocRel :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (y : F.G₀ → Matrix (Fin n) (Fin n) K) (ρ' : F.G₀ →* GL (Fin n) (DualNumber K)) (P' : GL (Fin n) (DualNumber K)), IsTan ρ y ρ' → F.IsForm O n ρ' P' →
        F.IsForm O n ρ (Matrix.GeneralLinearGroup.map (dF K) P') ∧ ∀ R, IsAdExt F ρ (Matrix.GeneralLinearGroup.map (dF K) P') R → ∃ Z, ∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z) := by
  intro l _ F O _ _ K _ _ n ρ y ρ' P' hT hF
  have hfst : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.fst = W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hsnd : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.snd = y g * W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hP : (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.fst
      = (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hc : ∀ g, ((F.eps O (DualNumber K) g ^ (1 - (n : ℤ)) : (DualNumber K)ˣ) : DualNumber K)
      = (TrivSqZeroExt.inl ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) : DualNumber K) := by
    intro g
    have : F.eps O (DualNumber K) g = Units.map (TrivSqZeroExt.inlHom K K : K →* DualNumber K) (F.eps O K g) :=
      Units.ext rfl
    rw [this, ← map_zpow]; rfl
  have hs1 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.fst = e • M.map TrivSqZeroExt.fst := by
    intro e M; ext i j; simp
  have hs2 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.snd = e • M.map TrivSqZeroExt.snd := by
    intro e M; ext i j; simp
  have part1 : ∀ g, (W.mat ρ g)ᵀ * (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K)
      * W.mat ρ (F.conj g)
      = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) •
        (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    intro g
    have h := congrArg (fun M => M.map TrivSqZeroExt.fst) (hF g)
    rw [cr_fst_mul, cr_fst_mul] at h
    simp only [Matrix.transpose_map, hfst, hP, hc, hs1] at h
    exact h
  refine ⟨fun g => part1 g, fun R hR => ?_⟩
  refine ⟨(↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹ : Matrix (Fin n) (Fin n) K) *
    (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.snd, fun g => ?_⟩
  have h := congrArg (fun M => M.map TrivSqZeroExt.snd) (hF g)
  rw [cr_snd_mul, cr_fst_mul, cr_snd_mul] at h
  simp only [Matrix.transpose_map, hfst, hsnd, hP, hc, hs2] at h
  rw [hR.c, hR.ad]
  exact cr_alg (A := W.mat ρ g) (B := W.mat ρ (F.conj g)) (Ai := ↑(ρ g)⁻¹) (Bi := ↑(ρ (F.conj g))⁻¹)
    (Pi := ↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹) (hA := Units.inv_mul _) (hB := Units.mul_inv _)
    (hP := Units.inv_mul _) (hP' := Units.mul_inv _) (h1 := part1 g) (h2 := h)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Eb

section
variable {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem rf_star_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.star O R n (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp only [W.GFrame.star, W.GFrame.starOp]
  rw [MonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, MonoidAlgebra.smul_single',
    smul_eq_mul]

private noncomputable def rf_dual (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) :
    F.G₀ →* Matrix (Fin n) (Fin n) K where
  toFun g := ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, map_mul, transpose_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

private theorem rf_dual_apply (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) (g : F.G₀) :
    rf_dual F O K n r g = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ := rfl

end

private theorem rf_rep_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (g : G) (b : R) : W.GDet.repAlg ρ R (MonoidAlgebra.single g b) = b • ρ g := by
  simp only [W.GDet.repAlg]
  rw [MonoidAlgebra.lift_single]
  simp

end UpperTheory.V.Ws.Eb

theorem UpperTheory.V.Ws.Eb.relForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [IsLocalRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        ∃ P : GL (Fin n) A, F.IsForm c.O n ρ P := by
  intro l _ F c n r B A _ _ _ f ρ hF hD
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  have hF' : Submodule.span A (Set.range (W.mat ρ)) = ⊤ := hF
  have key : ∀ g : F.G₀, (W.GDet.ofRep (W.mat ρ)).lam 1 (F.star c.O A n (MonoidAlgebra.single g 1)) =
      (W.GDet.ofRep (W.mat ρ)).lam 1 (MonoidAlgebra.single g 1) := by
    intro g
    have h1 := congrArg (f : B.B →+* A) (B.u.P 1 g)
    have hm := (AlgebraTools.Det.mapApi B.u.D (f : B.B →+* A)).2.1 1
    rw [← hm, ← hm] at h1
    have hs := (AlgebraTools.Det.starApi F c.O B.B n).2.2.2.2.2 A f (MonoidAlgebra.single g 1)
    rw [← hs, hD] at h1
    simpa using h1
  have trs : ∀ y, (W.GDet.ofRep (W.mat ρ)).lam 1 y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    intro y
    have h := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn y
    simpa only [W.GDet.tr] using h
  have hsingle : ∀ g, (W.mat ρ g).trace = (rf_dual F c.O A n ρ g).trace := by
    intro g
    have h := key g
    rw [trs, trs, rf_star_single, rf_rep_single, rf_rep_single] at h
    rw [rf_dual_apply, trace_smul, trace_transpose]
    simpa [trace_smul] using h.symm
  have htr : ∀ x, (W.GDet.repAlg (W.mat ρ) A x).trace = (W.GDet.repAlg (rf_dual F c.O A n ρ) A x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, rf_rep_single, one_smul]
      exact hsingle g
    | add x y hx hy => simp only [map_add (f := _), trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, trace_smul, hx]
  have hsurj : Function.Surjective (W.GDet.repAlg (W.mat ρ) A) := by
    intro M
    have hM : M ∈ Submodule.span A (Set.range (W.mat ρ)) := by
      rw [hF']
      trivial
    have hle : Submodule.span A (Set.range (W.mat ρ)) ≤ LinearMap.range (W.GDet.repAlg (W.mat ρ) A).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [rf_rep_single]⟩
    obtain ⟨x, hx⟩ := hle hM
    exact ⟨x, by simpa using hx⟩
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConjugacy.exists_conj_of_surjective (W.GDet.repAlg (W.mat ρ) A)
    (W.GDet.repAlg (rf_dual F c.O A n ρ) A) hsurj htr
  refine ⟨⟨(↑U : Matrix (Fin n) (Fin n) A)ᵀ, (↑U⁻¹ : Matrix (Fin n) (Fin n) A)ᵀ, ?_, ?_⟩, fun g => ?_⟩
  · rw [← transpose_mul, Units.inv_mul, transpose_one]
  · rw [← transpose_mul, Units.mul_inv, transpose_one]
  · show (W.mat ρ g)ᵀ * (↑U : Matrix (Fin n) (Fin n) A)ᵀ * W.mat ρ (F.conj g) = _
    have h := congrArg transpose (hU (MonoidAlgebra.single g 1))
    rw [rf_rep_single, rf_rep_single, one_smul, one_smul, rf_dual_apply, transpose_mul, transpose_mul,
      transpose_smul, transpose_transpose] at h
    rw [← h, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.detRep :
    ∀ {A k G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Field k] (f : A →+* k) [IsLocalHom f] [Group G] {n : ℕ} (D : W.GDet n A G) (ρ : G →* GL (Fin n) k), 1 ≤ n → Function.Surjective f → Full ρ → D.map f = W.GDet.ofRep (W.mat ρ) →
        ∃ ρ' : G →* GL (Fin n) A, D = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep f ρ' = ρ ∧ Full ρ' :=
  _root_.UpperTheory.Reformulated.B.CayleyHamiltonSymmetric.detRep
end
