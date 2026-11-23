module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.RepChi
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private noncomputable def twHom {O Γ : Type} [CommRing O] [Group Γ] (η : Γ →* Oˣ) : Γ →* MonoidAlgebra O Γ where
  toFun g := MonoidAlgebra.single g (η g : O)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single]

private theorem lift_tw {O Γ A : Type} [CommRing O] [Group Γ] [Ring A] [Algebra O A] (η : Γ →* Oˣ) (f f' : Γ →* A)
    (h : ∀ g, f' g = (η g : O) • f g) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O A Γ f (MonoidAlgebra.lift O (MonoidAlgebra O Γ) Γ (twHom η) y) = MonoidAlgebra.lift O A Γ f' y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | single g a =>
    simp only [MonoidAlgebra.lift_single, h, map_smul, smul_smul]
    simp [twHom, MonoidAlgebra.lift_single, smul_smul]

private theorem mem_max {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ < 1) : x ∈ maximalIdeal c.O := by
  haveI := c.fin
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have hint : IsIntegral ℤ_[l] (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) ((u⁻¹ : (c.O)ˣ) : c.O)).map c.O.val
  have h1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 hint
  have h2 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l)‖ < 1 :=
    calc _ ≤ ‖((u : c.O) : PadicAlgCl l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hx
  linarith

private theorem pushCh_zpow_neg_zero_eq_mul_zpow_neg_one {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] (ε : Γ →* c.Oˣ) (g : Γ) :
    ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((0 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap c.O (PadicAlgCl l) (ε g) *
        ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((1 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
  have h := Units.mul_inv (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (ε g))
  simp only [Nat.cast_zero, neg_zero, zpow_zero, MonoidHom.one_apply, Units.val_one, Nat.cast_one,
    zpow_neg, zpow_one, MonoidHom.inv_apply, W.pushCh, MonoidHom.comp_apply]
  rw [← h]
  rfl

theorem UpperTheory.V.Ws.Pu.mOne :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) (PadicAlgCl l)) (χ : Fin n → Γ →* (ResidueField c.O)ˣ) (ε : Γ →* c.Oˣ) (ε' : Γ →* (PadicAlgCl l)ˣ),
      RedTo c ρ χ → ε' = W.pushCh (algebraMap c.O (PadicAlgCl l)) ε → (∀ i j, χ i ≠ χ j * W.pushCh (residue c.O) ε) →
      ∀ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, Γ →* GL (Fin (d i)) (PadicAlgCl l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i) →
        (∀ g, (W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (W.mat (Af.tw (ρ' i) (ε' ^ (-(j : ℤ)))) g).charpoly) → ∀ i, m i = 1 := by
  intro l _ c Γ _ n ρ χ ε ε' hR hε hne a d m ρ' hdm hcp i
  subst hε
  by_contra hmi
  have h2 : 2 ≤ m i := by have := (hdm i).2; omega
  obtain ⟨y, hy1, hy0⟩ := Pu.sepEl (O := c.O) χ (fun b => χ b * W.pushCh (residue c.O) ε) (fun a b => hne a b)
  let Y := MonoidAlgebra.lift c.O (MonoidAlgebra c.O Γ) Γ (twHom ε) y
  let t : Finset (Σ _ : Fin a, ℕ) := Finset.univ.sigma (fun k => Finset.range (m k))
  let dd : (Σ _ : Fin a, ℕ) → ℕ := fun p => d p.1
  let σ : (p : Σ _ : Fin a, ℕ) → Γ →* GL (Fin (dd p)) (PadicAlgCl l) :=
    fun p => Af.tw (ρ' p.1) ((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-(p.2 : ℤ)))
  have hcp' : ∀ g, (W.mat ρ g).charpoly = ∏ p ∈ t, (W.mat (σ p) g).charpoly := by
    intro g
    rw [hcp g, Finset.prod_sigma]
  have hroot : ∀ (M : Matrix (Fin (d i)) (Fin (d i)) (PadicAlgCl l)), ∃ z, z ∈ M.charpoly.roots := by
    intro M
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root M.charpoly (by
      rw [Polynomial.degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim]
      have := (hdm i).1
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
      omega)
    exact ⟨z, (Polynomial.mem_roots M.charpoly_monic.ne_zero).2 hz⟩
  obtain ⟨z, hz⟩ := hroot (MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y)
  have hM : MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 1⟩)) Y =
      MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y := by
    apply lift_tw
    intro g
    simp only [σ, W.mat, MonoidHom.comp_apply, Units.coeHom_apply, Af.tw_val]
    rw [← IsScalarTower.algebraMap_smul (PadicAlgCl l) ((ε g : c.O)), smul_smul, ← pushCh_zpow_neg_zero_eq_mul_zpow_neg_one]
  have hz0 := Pu.cpAlg ρ t dd σ hcp' y ⟨i, 0⟩ (by simp [t]; omega) z hz
  have hz1 := Pu.cpAlg ρ t dd σ hcp' Y ⟨i, 1⟩ (by simp [t]; omega) z (by rw [hM]; exact hz)
  obtain ⟨j0, a0, ha0, hza0⟩ := hR y z hz0
  obtain ⟨j1, a1, ha1, hza1⟩ := hR Y z hz1
  rw [hy1] at ha0
  have hY0 : MonoidAlgebra.lift c.O (ResidueField c.O) Γ ((Units.coeHom (ResidueField c.O)).comp (χ j1)) Y = 0 := by
    rw [lift_tw ε _ ((Units.coeHom (ResidueField c.O)).comp (χ j1 * W.pushCh (residue c.O) ε)) _ y]
    · exact hy0 j1
    · intro g
      simp [Algebra.smul_def, W.pushCh, mul_comm]
  rw [hY0] at ha1
  have hm : a0 - a1 ∈ maximalIdeal c.O := mem_max c _ (by
    have e : ((a0 - a1 : c.O) : PadicAlgCl l) = (z - a1) + -(z - a0) := by push_cast; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [norm_neg]
    exact max_lt hza1 hza0)
  have hr : residue c.O (a0 - a1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
  rw [map_sub, ha0, ha1, sub_zero] at hr
  exact one_ne_zero hr
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_map_eq_map_chi_mapRingHom {n : ℕ} {B K Γ : Type} [CommRing B] [CommRing K] [Group Γ]
    (D : W.GDet n B Γ) (f : B →+* K) (z : MonoidAlgebra B Γ) :
    (D.chi z).map f = (D.map f).chi (MonoidAlgebra.mapRingHom Γ f z) := by
  letI : Algebra B K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  let φ : B[X] →ₐ[B] K[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have e : (MonoidAlgebra.mapRingHom Γ (φ : B[X] →+* K[X]))
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.mapRingHom Γ f z) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · congr 1
      change Polynomial.map f X = X
      simp only [Polynomial.map_X]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g b =>
        simp only [MonoidAlgebra.mapRingHom_single]
        change MonoidAlgebra.single g ((C b).map f) = MonoidAlgebra.single g (C (f b))
        rw [Polynomial.map_C]
  have h := D.nat B[X] K[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z)
  rw [e] at h
  exact h.symm

private theorem chi_ofRep_eq_charpoly_lift {n : ℕ} {K Γ : Type} [CommRing K] [Group Γ]
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (w : MonoidAlgebra K Γ) :
    (W.GDet.ofRep σ).chi w = (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w).charpoly := by
  have e : W.GDet.repAlg σ K[X] (MonoidAlgebra.mapRingHom Γ C w) =
      (C : K →+* K[X]).mapMatrix (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w) := by
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
      ext i j
      simp [Polynomial.smul_eq_C_mul, Polynomial.algebraMap_apply]
  have e1 : W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X) = Matrix.scalar (Fin n) (X : K[X]) := by
    simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, map_one]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  show Matrix.det (W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C w)) = _
  rw [map_sub, e, e1]
  rfl

private theorem chi_map {n : ℕ} {O B K Γ : Type} [CommRing O] [CommRing B] [CommRing K] [Algebra O B] [Algebra O K]
    [Group Γ] (D : W.GDet n B Γ) (f : B →ₐ[O] K) (σ : Γ →* Matrix (Fin n) (Fin n) K)
    (h : D.map (f : B →+* K) = W.GDet.ofRep σ) (y : MonoidAlgebra O Γ) :
    (D.chi (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y)).map (f : B →+* K) =
      (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ σ y).charpoly := by
  rw [chi_map_eq_map_chi_mapRingHom, h, chi_ofRep_eq_charpoly_lift]
  have e : MonoidAlgebra.mapRingHom Γ (f : B →+* K) (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y) =
      MonoidAlgebra.mapRingHom Γ (algebraMap O K) y := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g b => simp [MonoidAlgebra.mapRingHom_single]
  rw [e, MonoidAlgebra.lift_mapRingHom_algebraMap]

private theorem lift_diag {n : ℕ} {O K Γ : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Group Γ] (χ : Fin n → Γ →* Kˣ) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.diagRep χ) y =
      Matrix.diagonal fun i => MonoidAlgebra.lift O K Γ ((Units.coeHom _).comp (χ i)) y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
    congr 1
    funext i
    rw [map_add (f := _)]
  | single g b =>
    ext i j
    simp [W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]

private theorem near {n : ℕ} {B K : Type} [CommRing B] [NormedField K] [IsUltrametricDist K] (I : Ideal B)
    (x : B →+* K) (h1 : ∀ b, ‖x b‖ ≤ 1) (hm : ∀ b ∈ I, ‖x b‖ < 1) (P : B[X]) (hP : (P.map x).Monic) (a : Fin n → B)
    (ha : ∀ k, (P - ∏ i, (X - C (a i))).coeff k ∈ I) (z : K) (hz : (P.map x).IsRoot z) : ∃ i, ‖z - x (a i)‖ < 1 := by
  classical
  have hcoef : ∀ k, ‖(P.map x).coeff k‖ ≤ 1 := fun k => by rw [Polynomial.coeff_map]; exact h1 _
  have hz1 : ‖z‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hev := hz.eq_zero
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at hev
    set d := (P.map x).natDegree
    have hzd : z ^ d = -∑ i ∈ Finset.range d, (P.map x).coeff i * z ^ i := by
      linear_combination hev
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd] at hzd
      simp at hzd
    have hpos : 0 < ‖z‖ ^ (d - 1) := pow_pos (by linarith) _
    have hle : ‖z‖ ^ d ≤ ‖z‖ ^ (d - 1) := by
      rw [← norm_pow, hzd, norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos.le fun i hi => ?_
      rw [norm_mul, norm_pow]
      have hi' : i ≤ d - 1 := by
        have := Finset.mem_range.mp hi
        omega
      calc ‖(P.map x).coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
            mul_le_mul_of_nonneg_right (hcoef i) (by positivity)
        _ = ‖z‖ ^ i := one_mul _
        _ ≤ ‖z‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le hi'
    have : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this] at hle
    nlinarith
  have hE : ‖((P - ∏ i, (X - C (a i))).map x).eval z‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range]
    obtain ⟨k, -, hle⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
        (fun i => ((P - ∏ i, (X - C (a i))).map x).coeff i * z ^ i)
    refine hle.trans_lt ?_
    rw [norm_mul, norm_pow, Polynomial.coeff_map]
    calc ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * ‖z‖ ^ k
        ≤ ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hm _ (ha k)
  have hsum : (P.map x).eval z = (∏ i, (z - x (a i))) + ((P - ∏ i, (X - C (a i))).map x).eval z := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, Polynomial.map_prod, Polynomial.eval_prod]
    simp
  have hprod : ‖∏ i, (z - x (a i))‖ < 1 := by
    have : ∏ i, (z - x (a i)) = -((P - ∏ i, (X - C (a i))).map x).eval z := by
      rw [hz.eq_zero] at hsum
      linear_combination (-1 : K) * hsum
    rw [this, norm_neg]
    exact hE
  by_contra hne
  push_neg at hne
  have : (1 : ℝ) ≤ ‖∏ i, (z - x (a i))‖ := by
    rw [norm_prod]
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, ‖z - x (a i)‖ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hne i)
  linarith

theorem UpperTheory.V.Ws.Pu.ptRed :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → RedTo c ρ fun i => (r.chib i).comp V.pr := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx
  intro y z hz
  letI := B.ring
  letI := B.alg
  haveI := B.co
  set D := B.u.D.comap V.pr with hD
  have hxD : D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) := hx
  have hrD : D.map (res c.O B.B : B.B →+* ResidueField c.O) =
      W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp V.pr) := by
    have h0 : (B.u.D.map (res c.O B.B : B.B →+* ResidueField c.O)).comap V.pr =
        (r.Dbar).comap V.pr := by rw [B.u.red]
    refine h0.trans ?_
    rw [W.Resid.Dbar]
    refine ((AlgebraTools.Det.repApi (W.diagRep r.chib)).2.2.2.2.2.2.1 V.pr).trans ?_
    exact congrArg W.GDet.ofRep (MonoidHom.ext fun g => rfl)
  set P := D.chi (MonoidAlgebra.mapRingHom _ (algebraMap c.O B.B) y) with hP
  have hPx := chi_map D (x : B.B →ₐ[c.O] PadicAlgCl l) (W.mat ρ) hxD y
  have hPr := chi_map D (res c.O B.B) (W.diagRep fun i => (r.chib i).comp V.pr) hrD y
  rw [lift_diag, Matrix.charpoly_diagonal] at hPr
  set d : Fin n → ResidueField c.O := fun i =>
    MonoidAlgebra.lift c.O (ResidueField c.O) _ ((Units.coeHom _).comp ((r.chib i).comp V.pr)) y with hd
  choose a' ha' using fun i => IsLocalRing.residue_surjective (d i)
  have hco := (GradeZeroInterpolatingElement.coPt c B.B).1 x
  obtain ⟨-, e, he1, he0, hen⟩ := hco
  have h1 : ∀ b, ‖(x : B.B →+* PadicAlgCl l) b‖ ≤ 1 := fun b => by
    have := hen 0 b (by simp)
    simpa using this
  have hm : ∀ b ∈ IsLocalRing.maximalIdeal B.B, ‖(x : B.B →+* PadicAlgCl l) b‖ < 1 := fun b hb => by
    have := hen 1 b (by simpa using hb)
    simp only [pow_one] at this
    exact lt_of_le_of_lt this he1
  have hmon : (P.map (x : B.B →+* PadicAlgCl l)).Monic := by
    rw [hPx]
    exact Matrix.charpoly_monic _
  have hroot : (P.map (x : B.B →+* PadicAlgCl l)).IsRoot z := by
    rw [hPx]
    exact Polynomial.isRoot_of_mem_roots hz
  have hres : ∀ i, (res c.O B.B) (algebraMap c.O B.B (a' i)) = d i := fun i => by
    rw [AlgHom.commutes, ← ha' i]
    rfl
  have hcoef : ∀ k, (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).coeff k ∈ IsLocalRing.maximalIdeal B.B := by
    intro k
    rw [← res_eq_zero_iff c.O B.B]
    show (res c.O B.B : B.B →+* ResidueField c.O) _ = 0
    rw [← Polynomial.coeff_map]
    have : (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).map (res c.O B.B : B.B →+* ResidueField c.O) = 0 := by
      rw [Polynomial.map_sub, hPr, Polynomial.map_prod, sub_eq_zero]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      exact (hres i).symm
    rw [this, Polynomial.coeff_zero]
  obtain ⟨i, hi⟩ := near (IsLocalRing.maximalIdeal B.B) (x : B.B →+* PadicAlgCl l) h1 hm P hmon
    (fun i => algebraMap c.O B.B (a' i)) hcoef z hroot
  refine ⟨i, a' i, ha' i, ?_⟩
  have : (x : B.B →+* PadicAlgCl l) (algebraMap c.O B.B (a' i)) = (a' i : PadicAlgCl l) := by
    show x (algebraMap c.O B.B (a' i)) = _
    rw [AlgHom.commutes]
    rfl
  rwa [this] at hi
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_point {A B K : Type} [CommRing A] [CommRing B] [Field K] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* K) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (M.map y).charpoly.scaleRoots (y (i b)) := by
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.Pu.ptCp :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ρ : G T.L Ω →* GL (Fin 4) (PadicAlgCl l)), K.IsPhi X 0 B φ → (Link.pt φ y).IsRep ρ →
      ∀ g, (W.mat ρ g).charpoly = ((X.P.map (y : X.A →+* PadicAlgCl l)).r (resLe T.F_le g)).charpoly.scaleRoots (K.kapQ g : PadicAlgCl l) := by
  intro Ω _ _ _ l _ c D T c' h K X B φ y ρ hφ hρ g
  have hxe : (Link.pt φ y : B.B →+* PadicAlgCl l) =
      ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B) :=
    RingHom.ext fun b => Link.pt_apply K φ y b
  have hs : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B (K.κ g * K.β g ^ 0))) =
      (K.kapQ g : PadicAlgCl l) := by
    rw [← IsScalarTower.algebraMap_apply, pow_zero, mul_one]
    exact y.commutes _
  rw [UpperTheory.V.Ws.Pu.repChi K.V B _ ρ hρ g, hxe, ← Polynomial.map_map]
  refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
  rw [scale_point _ X.inj _ _ _ (X.cp_map _), hs]
  rfl
end
