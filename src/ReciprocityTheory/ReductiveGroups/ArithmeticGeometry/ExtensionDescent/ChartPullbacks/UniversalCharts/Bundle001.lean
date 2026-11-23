module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

private theorem jetAug_zR_lemma {κ : Type} {m : ℕ} (j : κ) : jetAug R κ m (zR m j) = 0 := by
  first
  | (show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
     simp)
  | simp [jetAug, zR, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]

theorem sum_smul_zR_mem {a : ℕ} (m : ℕ) (c : Fin a → R) :
    ∑ i, c i • zR (R := R) m i ∈ RingHom.ker (jetAug R (Fin a) m) := by

  rw [RingHom.mem_ker, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul, jetAug_zR_lemma i, smul_zero]

theorem sum_single {a : ℕ} (c : Fin a → R) : ∑ i, c i • Pi.single i (1 : R) = c := by
  ext k
  simp [Pi.single_apply]

def jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) : JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
  jetLift (R := R) (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
    (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)

theorem jetSub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
    jetSub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
  rw [jetSub, jetLift_zR]

private theorem jet_ext_lemma_2 {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A]
    {f g : JetR R κ m →ₐ[R] A} (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

theorem jetSub_id {a : ℕ} (m : ℕ) : jetSub (R := R) (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by
  apply jet_ext_lemma_2
  intro k
  rw [jetSub_zR]
  simp [Pi.single_apply]

theorem jetSub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
    (jetSub S m).comp (jetSub T m) = jetSub (T.comp S) m := by
  apply jet_ext_lemma_2
  intro k

  rw [AlgHom.comp_apply, jetSub_zR, jetSub_zR, map_sum]
  simp_rw [map_smul, jetSub_zR, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [LinearMap.comp_apply, ← sum_single (S (Pi.single j 1))]

  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

theorem jetAug_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetAug R (Fin a) m).comp (jetSub T m) = jetAug R (Fin b) m := by
  apply jet_ext_lemma_2
  intro k
  rw [AlgHom.comp_apply, jetSub_zR, jetAug_zR_lemma]
  exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)

private theorem trunc_zR_lemma_3 {κ : Type} (m : ℕ) (j : κ) :
    jetTruncR R κ m (zR (m + 1) j) = zR m j := rfl

private theorem zero_zR_lemma_4 {κ : Type} (m : ℕ) (j : κ) :
    jetZeroR R κ m (zR m j) = zR 0 j := rfl

theorem trunc_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetTruncR R (Fin a) m).comp (jetSub T (m + 1)) = (jetSub T m).comp (jetTruncR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k

  simp only [AlgHom.comp_apply, jetSub_zR, trunc_zR_lemma_3, map_sum, map_smul]

theorem zero_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetZeroR R (Fin a) m).comp (jetSub T m) = (jetSub T 0).comp (jetZeroR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k

  simp only [AlgHom.comp_apply, jetSub_zR, zero_zR_lemma_4, map_sum, map_smul]

private theorem sum_inr_lemma_5 {I : Type} (s : Finset I) (f : I → R) :
    ∑ i ∈ s, (TrivSqZeroExt.inr (f i) : DualNumber R) = TrivSqZeroExt.inr (∑ i ∈ s, f i) := by
  first
  | exact (map_sum (TrivSqZeroExt.inrHom R R) f s).symm
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, TrivSqZeroExt.inr_add])

theorem dualLift_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (c : Fin a → R) :
    (dualLift c).comp (jetSub T 1) = dualLift (T c) := by
  apply jet_ext_lemma_2
  intro k

  simp only [AlgHom.comp_apply, jetSub_zR, map_sum, map_smul, dualLift_zR]
  simp_rw [← TrivSqZeroExt.inr_smul, sum_inr_lemma_5]
  congr 1
  conv_rhs => rw [← sum_single c]

  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isUnivChart_sub {n d : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (T : (Fin d → R) ≃ₗ[R] (Fin n → R)) :
    IsUnivChart G d (fun m => spMap (jetSub T.toLinearMap m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · show spMap (jetTruncR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap (m + 1)) ≫ x (m + 1) =
      spMap (jetSub T.toLinearMap m) ≫ x m
    rw [← Category.assoc, spMap_comp, trunc_comp_jetSub, ← spMap_comp, Category.assoc, hx.1 m]
  · show spMap (jetZeroR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap m) ≫ x m = 1
    rw [← Category.assoc, spMap_comp, zero_comp_jetSub, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA y hy
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := hx.2.2 A aug m hA y hy
    have e1 : (jetSub T.symm.toLinearMap m).comp (jetSub T.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    have e2 : (jetSub T.toLinearMap m).comp (jetSub T.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    refine ⟨ψ.comp (jetSub T.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψ1, jetAug_comp_jetSub]
    · show y = spMap (ψ.comp (jetSub T.symm.toLinearMap m)) ≫ spMap (jetSub T.toLinearMap m) ≫ x m
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e1, AlgHom.comp_id]
      exact hψ2
    · rintro φ ⟨hφ1, hφ2⟩
      have hφ2' : y = spMap φ ≫ spMap (jetSub T.toLinearMap m) ≫ x m := hφ2
      have hφ : φ.comp (jetSub T.toLinearMap m) = ψ := by
        apply hψu
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφ1, jetAug_comp_jetSub]
        · rw [hφ2', ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, e2, AlgHom.comp_id]

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

theorem spMap_id (P : Type) [CommRing P] [Algebra R P] : spMap (AlgHom.id R P) = 𝟙 (sp (R₀ := R) P) := by
  apply Over.OverMorphism.ext
  simp only [spMap_left, Over.id_left]
  exact Spec.map_id _

def qD (i : Fin 2) : DualNumber R →ₐ[R] JetR R (Fin 2) 1 :=
  TrivSqZeroExt.lift (Algebra.ofId R _) (LinearMap.toSpanSingleton R _ (zR 1 i))
    (fun a b => by
      simp only [LinearMap.toSpanSingleton_apply]
      rw [smul_mul_smul_comm]
      have : zR (R := R) 1 i * zR 1 i = 0 := by
        show Ideal.Quotient.mk _ (MvPolynomial.X i * MvPolynomial.X i) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_two]
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨i, rfl⟩)
      rw [this, smul_zero])
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, map_mul, Algebra.ofId_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring)
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, map_mul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring)

theorem qD_apply (i : Fin 2) (a : DualNumber R) :
    qD i a = algebraMap R _ a.fst + a.snd • zR (R := R) 1 i := rfl

theorem jetAug_comp_qD (i : Fin 2) : (jetAug R (Fin 2) 1).comp (qD i) = fstD R := by
  ext a
  rw [AlgHom.comp_apply, qD_apply, map_add (f := _), map_smul, AlgHom.commutes, jetAug_zR, smul_zero, add_zero]
  rfl

theorem delta_sq : (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]

def deltaJ : JetR R (Fin 2) 1 →ₐ[R] TrivSqZeroExt R (R × R) :=
  jetLift (R := R) (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) delta_sq
    (fun i => TrivSqZeroExt.inr (if i = 0 then ((1 : R), (0 : R)) else (0, 1)))
    (fun i => (RingHom.mem_ker).mpr rfl)

def rD (l : R × R →ₗ[R] R) : JetR R (Fin 2) 1 →ₐ[R] DualNumber R :=
  (TrivSqZeroExt.map l).comp deltaJ

theorem rD_zR (l : R × R →ₗ[R] R) (i : Fin 2) :
    rD l (zR 1 i) = TrivSqZeroExt.inr (l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) := by
  rw [rD, AlgHom.comp_apply, deltaJ, jetLift_zR, TrivSqZeroExt.map_inr]

theorem snd_rD_add (a : JetR R (Fin 2) 1) :
    (rD (LinearMap.fst R R R + LinearMap.snd R R R) a).snd =
      (rD (LinearMap.fst R R R) a).snd + (rD (LinearMap.snd R R R) a).snd := by
  simp only [rD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.add_apply]

theorem fstD_comp_rD (l : R × R →ₗ[R] R) : (fstD R).comp (rD l) = jetAug R (Fin 2) 1 :=
  jet_ext fun i => by
    rw [AlgHom.comp_apply, rD_zR, jetAug_zR]
    exact inr_mem_kerD _

theorem rD_comp_qD (l : R × R →ₗ[R] R) (i : Fin 2) :
    (rD l).comp (qD i) = TrivSqZeroExt.map ((l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) • LinearMap.id) := by
  apply DualNumber.algHom_ext
  rw [AlgHom.comp_apply, qD_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, map_zero, one_smul, zero_add, rD_zR]
  show _ = TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)
  rw [TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) : IsTan (w₁ * w₂) := by
  rw [IsTan, MonObj.comp_mul, h₁, h₂, _root_.mul_one]

theorem isTan_one : IsTan (1 : sp (R₀ := R) (DualNumber R) ⟶ G) := comp_one' _

abbrev scaleD (c : R) : DualNumber R →ₐ[R] DualNumber R := TrivSqZeroExt.map (c • LinearMap.id)

theorem isTan_scale (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) : IsTan (spMap (scaleD c) ≫ w) := by
  have : (fstD R).comp (scaleD c) = fstD R := by
    ext
    exact TrivSqZeroExt.fst_map _ _
  rw [IsTan, ← Category.assoc, spMap_comp, this]
  exact h

theorem scaleD_one : scaleD (1 : R) = AlgHom.id R (DualNumber R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1
  rw [TrivSqZeroExt.map_inr, one_smul, LinearMap.id_apply]

theorem scaleD_zero : scaleD (0 : R) = (Algebra.ofId R (DualNumber R)).comp (fstD R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = (Algebra.ofId R (DualNumber R)) ((TrivSqZeroExt.inr (1 : R) : DualNumber R).fst)
  rw [TrivSqZeroExt.map_inr, zero_smul, LinearMap.zero_apply, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]

theorem spMap_scaleD_zero {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) : spMap (scaleD (0 : R)) ≫ w = 1 := by
  rw [scaleD_zero, ← spMap_comp, Category.assoc, h, comp_one']

theorem restrictDiag_comp_incl_fst (l : R × R →ₗ[R] R) : (rD l).comp (qD 0) = scaleD (l ((1 : R), (0 : R))) := by
  rw [rD_comp_qD]; simp

theorem restrictDiag_comp_incl_snd (l : R × R →ₗ[R] R) : (rD l).comp (qD 1) = scaleD (l ((0 : R), (1 : R))) := by
  rw [rD_comp_qD]; simp

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem tcoord_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) :
    tcoord hx (w₁ * w₂) (isTan_mul h₁ h₂) = tcoord hx w₁ h₁ + tcoord hx w₂ h₂ := by
  let P : sp (R₀ := R) (JetR R (Fin 2) 1) ⟶ G := (spMap (qD 0) ≫ w₁) * (spMap (qD 1) ≫ w₂)
  have hP : spMap (jetAug R (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, jetAug_comp_qD,
      jetAug_comp_qD, h₁, h₂, _root_.mul_one]
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 _ (jetAug R (Fin 2) 1) 1 (ker_jetAug_pow (Fin 2) 1) P hP
  have key : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = spMap (dualLift (fun j => (rD l (ψ (zR 1 j))).snd)) ≫ x 1 := by
    intro l
    rw [hψ2, ← Category.assoc, spMap_comp,
      eq_dualLift ((rD l).comp ψ) (by rw [← AlgHom.comp_assoc, fstD_comp_rD, hψ1])]
    rfl
  have hval : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = (spMap (scaleD (l ((1 : R), (0 : R)))) ≫ w₁) * (spMap (scaleD (l ((0 : R), (1 : R)))) ≫ w₂) := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, restrictDiag_comp_incl_fst, restrictDiag_comp_incl_snd]
  have e1 : w₁ = spMap (dualLift (fun j => (rD (LinearMap.fst R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₂, _root_.mul_one]
  have e2 : w₂ = spMap (dualLift (fun j => (rD (LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₁, _root_.one_mul]
  have e12 : w₁ * w₂ = spMap (dualLift (fun j =>
      (rD (LinearMap.fst R R R + LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [scaleD_one, spMap_id, Category.id_comp, Category.id_comp]
  rw [tcoord_eq hx _ _ _ e12, tcoord_eq hx _ _ _ e1, tcoord_eq hx _ _ _ e2]
  funext j
  exact snd_rD_add _

theorem tcoord_scale (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) :
    tcoord hx (spMap (scaleD c) ≫ w) (isTan_scale c h) = c • tcoord hx w h := by
  apply tcoord_eq
  conv_lhs => rw [tcoord_spec hx w h]
  rw [← Category.assoc, spMap_comp]
  congr 2
  apply jet_ext
  intro j
  rw [AlgHom.comp_apply, dualLift_zR, dualLift_zR, TrivSqZeroExt.map_inr, LinearMap.smul_apply,
    LinearMap.id_apply, Pi.smul_apply]

theorem tcoord_one : tcoord hx (1 : sp (R₀ := R) (DualNumber R) ⟶ G) isTan_one = 0 := by
  apply tcoord_eq
  have : dualLift (R := R) (0 : Fin n → R) = (Algebra.ofId R (DualNumber R)).comp (jetAug R (Fin n) 1) :=
    jet_ext fun j => by
      rw [dualLift_zR, AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, TrivSqZeroExt.inr_zero]
  rw [this, ← spMap_comp, Category.assoc, spMap_jetAug_alt hx, comp_one']

end ReciprocityTheory.ChartRestriction.G.Chart
end
end
