module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCore_of :
    UnitOfSpan → BasisIn → DetCore := by
  intro hU hB C R S W W' X X' _ _ _ _ _ _ _ _ _ _ _ a π mk mk' c c' j j' M M' w w' A s ha h1
    hspanC hj hj' hMw hM'w hcw hc'w hex hspanS
  obtain ⟨x, b, hb⟩ := hB C W X a mk hspanC ha
  set P0 : Matrix (Fin a) (Fin a) R := Matrix.of fun i k => c (x k) i with hP0
  let v : Fin a → Fin a → S := fun k i => π (c (x k) i)
  have hspan : Submodule.span S (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspanS, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have e1 : (fun i => π (c y i)) = j (mk y) := funext fun i => (hj y i).symm
    have e2 := congrArg j (b.sum_repr (mk y))
    show (fun i => π (c y i)) ∈ Submodule.span S (Set.range v)

    rw [e1, ← e2, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, hb k, ← algebraMap_smul S (b.repr (mk y) k)]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
    funext i
    exact (hj (x k) i).symm
  have hunit : IsUnit (π P0.det) := by
    rw [RingHom.map_det]
    exact hU S a v hspan
  set mb := LinearMap.toMatrix b b M with hmb
  have hM : ∀ k, M (b k) = ∑ l, mb l k • b l := by
    intro k
    simp only [hmb, LinearMap.toMatrix_apply]
    exact (b.sum_repr _).symm
  have hmat : A.map π * (P0.map s).map π = P0.map π * mb.map (algebraMap C S) := by
    ext i k
    have e1 : (A.map π * (P0.map s).map π) i k = π (c (w (x k)) i) := by
      rw [hcw (x k)]

      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, hP0]
    have e2 : π (c (w (x k)) i) = (P0.map π * mb.map (algebraMap C S)) i k := by

      rw [← hj, ← hMw, ← hb k, hM k, map_sum, Finset.sum_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, hb l, hj, mul_comm (algebraMap C S _)]
      simp [hP0]
    rw [e1, e2]
  have hdet : π A.det * π (s P0.det) = π P0.det * algebraMap C S mb.det := by
    have e := congrArg Matrix.det hmat
    simp only [Matrix.det_mul] at e
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using e
  obtain ⟨x', hx'⟩ := hex x
  obtain ⟨d, hd, -⟩ := M'.existsUnique_eq_smul_id_of_finrank_eq_one h1
  have hdM' : LinearMap.det M' = d := by
    rw [hd, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one]
  have e3 : j' (M' (mk' x')) = algebraMap C S d * π P0.det := by
    rw [hd, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Algebra.smul_def, hj', hx']
  have e4 : j' (M' (mk' x')) = π A.det * π (s P0.det) := by
    rw [hM'w, hj', hc'w, hx', map_mul]
  have e5 : algebraMap C S d = algebraMap C S mb.det := by
    have e6 : algebraMap C S d * π P0.det = algebraMap C S mb.det * π P0.det := by
      rw [← e3, e4, hdet, mul_comm]
    exact hunit.mul_left_injective e6
  rw [hdM', ← LinearMap.det_toMatrix b M]
  exact (algebraMap C S).injective e5.symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCo_of :
    CoFacts := by
  intro F L B _ _ _ _ _ a
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [co, map_add (f := _)]
  · intro c x
    funext i
    show AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id (c • x) =
      (c ⊗ₜ[F] (1 : B)) * AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id x
    rw [map_smul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  · intro b x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp_all [co, mul_add]
  · intro T A hT s x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co, Matrix.mulVec, dotProduct]
    | tmul m n =>
      simp [co, onR, hT, Matrix.mulVec, dotProduct, TensorProduct.sum_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply] at hx hy ⊢
      simp_all [co, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  · convert (AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) L L)
      (LinearEquiv.refl F B)).bijective using 1
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co]
    | add x y hx hy => simp_all [co]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem step_fix (hco : CoFacts) {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ}
    (x : Fin a → (Fin a → L) ⊗[F] B) (y : (Fin 1 → L) ⊗[F] B)
    (hy : co y 0 = Matrix.det (Matrix.of fun i k => co (x k) i))
    (T : End L (Fin a → L)) (A : Matrix (Fin a) (Fin a) L) (hT : ∀ v, T v = A.mulVec v)
    (T' : End L (Fin 1 → L)) (A' : Matrix (Fin 1) (Fin 1) L) (hT' : ∀ v, T' v = A'.mulVec v)
    (hdet : A'.det = A.det) (s : B →ₐ[F] B)
    (hfix : ∀ k, AlgebraTensorModule.map T s.toLinearMap (x k) = x k) :
    AlgebraTensorModule.map T' s.toLinearMap y = y := by
  obtain ⟨-, -, -, hmap, -⟩ := hco F L B a
  obtain ⟨-, -, -, hmap', hbij⟩ := hco F L B 1
  set D : Matrix (Fin a) (Fin a) (L ⊗[F] B) := Matrix.of fun i k => co (x k) i with hD
  have hM : D = A.map (algebraMap L (L ⊗[F] B)) * D.map (onR L s) := by
    ext i k
    have h1 := congrFun (hmap T A hT s (x k)) i
    rw [hfix k] at h1
    simpa [D, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1
  have key : D.det = algebraMap L (L ⊗[F] B) A.det * onR L s D.det := by
    conv_lhs => rw [hM]
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]
    rfl
  apply hbij.1
  have h1 := congrFun (hmap' T' A' hT' s y) 0
  have h3 : A' 0 0 = A.det := by rw [← hdet, Matrix.det_fin_one]
  show co _ 0 = co y 0
  rw [h1, hy]
  conv_rhs => rw [key]
  simp [Matrix.mulVec, dotProduct, h3, hy]

private theorem one_ext {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) {a : ℕ} (x : Fin a → ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ k, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
  have hs : ∀ s : Finset (Fin a), ∃ K' : FinExt l, ∀ k ∈ s, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨K, by simp⟩
    | insert k s hk ih =>
      obtain ⟨K₁, h₁⟩ := ih
      obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (x k).2
      refine ⟨supExt K₁ K₂, fun k' hk' g hg => ?_⟩
      rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
      · exact h₁ k' hk' g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
  obtain ⟨K', h⟩ := hs Finset.univ
  exact ⟨K', fun k => h k (Finset.mem_univ k)⟩

theorem UpperTheory.Gal.crystallineComparison.detMem_of :
    CoFacts → DetMem := by
  intro hco l _ P K LL a ρ ρ' A A' hA hA' hdet x
  obtain ⟨K', hK'⟩ := one_ext P ρ x
  obtain ⟨y, hy⟩ := (hco ℚ_[l] ↥LL.1 (Bst P) 1).2.2.2.2.2
    (Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
  exact ⟨⟨y, (mem_Dpst P ρ').mpr ⟨K', fun g hg =>
    step_fix hco (fun k => (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) y hy (ρ g) (A g) (hA g) (ρ' g) (A' g) (hA' g)
      (hdet g) (actSt P (g : GQ l)) fun k => hK' k g hg⟩⟩, hy⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem letter_lift {LL U D N : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [AddCommGroup N] [Module LL N] [Module F N] [IsScalarTower LL F N] (κ' : D →ₗ[LL] N)
    (hκ : ∀ c x, κ' (m c x) = τ c • κ' x) :
    ∃ j : Letter m F τ →ₗ[F] N, ∀ x, j (letterMk m F τ x) = κ' x := by
  have hk : letterKer m F τ ≤ LinearMap.ker (κ'.liftBaseChange F) := by
    refine iSup_le fun c => ?_
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul z x =>
      simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, hκ, smul_smul, mul_comm]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  refine ⟨(letterKer m F τ).liftQ (κ'.liftBaseChange F) hk, fun x => ?_⟩
  show (letterKer m F τ).liftQ (κ'.liftBaseChange F) hk ((letterKer m F τ).mkQ ((1 : F) ⊗ₜ[LL] x)) = κ' x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.liftBaseChange_tmul, one_smul]

theorem UpperTheory.Gal.crystallineComparison.detWdLift_of :
    WdLift := by
  intro l _ P ι K LL V _ _ _ _ ρ N _ _ κ hadd hsmul hmul
  letI := algC ι LL
  letI : Module ↥LL.1 N := Module.compHom N (algebraMap ↥LL.1 ℂ)
  haveI : IsScalarTower ↥LL.1 ℂ N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let κ' : ↥(Dpst P ρ) →ₗ[↥LL.1] N :=
    { toFun := κ
      map_add' := hadd
      map_smul' := fun c x => hsmul c x }
  exact letter_lift (mulD P ρ) ℂ (urC ι) κ' (fun c x => hmul c x)
end

section

noncomputable section

open TensorProduct

namespace UpperTheory.Gal.crystallineComparison

theorem detRingS_of :
    RingS := by
  intro F L U B C _ _ _ _ _ _ _ _ _ _ _ τL τU h
  letI : Algebra U C := τU.toAlgebra
  let S := TensorProduct U C B
  have hS : Nontrivial S :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right U C B τU.injective
  let ψ : B →+* S := (Algebra.TensorProduct.includeRight : B →ₐ[U] S).toRingHom
  have key : ∀ c : U, algebraMap C S (τU c) = (1 : C) ⊗ₜ[U] algebraMap U B c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have e : τU c = c • (1 : C) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [e, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  letI : Algebra F S := (ψ.comp (algebraMap F B)).toAlgebra
  let φ : L →ₐ[F] S :=
    { (algebraMap C S).comp τL with
      commutes' := by
        intro z
        change algebraMap C S (τL (algebraMap F L z)) = ψ (algebraMap F B z)
        rw [h z, key, IsScalarTower.algebraMap_apply F U B z]
        rfl }
  let ψ' : B →ₐ[F] S := { ψ with commutes' := fun _ => rfl }
  let π : L ⊗[F] B →+* S :=
    (Algebra.TensorProduct.lift φ ψ' (fun _ _ => Commute.all _ _)).toRingHom
  refine ⟨S, inferInstance, inferInstance, π, hS, ?_, ?_⟩
  · intro x
    change φ x * ψ' 1 = _
    rw [map_one, mul_one]
    rfl
  · intro c
    change φ 1 * ψ' (algebraMap U B c) = _
    rw [map_one, one_mul, key]
    rfl

end UpperTheory.Gal.crystallineComparison
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detBasis_of :
    BasisIn := by
  intro C W X _ _ _ _ a mk hspan hfin
  obtain ⟨t, hts, hst, hli⟩ := exists_linearIndependent C (Set.range mk)
  have htop : ⊤ ≤ Submodule.span C (Set.range ((↑) : t → W)) := by
    rw [Subtype.range_coe, hst, hspan]
  let b₀ : Basis t C W := Basis.mk hli htop
  haveI : Finite t := Module.Finite.finite_basis b₀
  haveI : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = a := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let e : t ≃ Fin a := Fintype.equivFinOfCardEq hcard
  have hx : ∀ k : Fin a, ∃ x : X, mk x = ((e.symm k : t) : W) := fun k => hts (e.symm k).2
  choose x hx using hx
  refine ⟨x, b₀.reindex e, fun k => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply, hx k]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison


theorem UpperTheory.Gal.crystallineComparison.detCoLift_of :
    CoFacts → WdLift → CoLift := by
  intro hco hwd l _ P ι K LL a ρ S _ _ π h1 h2
  obtain ⟨f1, f2, f3, -, -⟩ := hco ℚ_[l] ↥LL.1 (Bst P) a
  refine Exists.elim (hwd l P ι K LL (Fin a → ↥LL.1) ρ (Fin a → S)
    (fun x i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) ?_ ?_ ?_)
    fun j hj => ⟨j, fun x i => by rw [hj]⟩
  · intro x y
    funext i
    rw [Submodule.coe_add, f1, Pi.add_apply, Pi.add_apply, map_add (f := _)]
  · intro c x
    funext i
    change π (co (c • (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) = _
    rw [f2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, h1,
      Algebra.smul_def]
  · intro c x
    funext i
    have e : co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) = _ :=
      f3 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)
    show π (co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) =
      ι (c : Om l) • π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)
    rw [e, Pi.smul_apply, smul_eq_mul, RingHom.map_mul π, h2, Algebra.smul_def]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL V : Type} [Field LL] [Algebra ℚ_[l] LL]
  [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem phiV_pow_tmul (n : ℕ) (v : V) (b : Bst P) :
    (phiV P LL V ^ n) (v ⊗ₜ[ℚ_[l]] b) = v ⊗ₜ[ℚ_[l]] (phiSt P ^ n) b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, phiV_tmul, ih, pow_succ, AlgHom.mul_apply]

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

private theorem coe_phiD_pow (n : ℕ) (x : ↥(Dpst P ρ)) :
    (((phiD P ρ ^ n) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n) (x : V ⊗[ℚ_[l]] Bst P) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, coe_phiD, pow_succ, Module.End.mul_apply]

private theorem stRep_phiV_pow (γ : ↥(GK K)) (n : ℕ) (y : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρ γ ((phiV P LL V ^ n) y) =
      AlgebraTensorModule.map (ρ γ) ((actSt P (γ : GQ l)).comp (phiSt P ^ n)).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [phiV_pow_tmul, stRep_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end

theorem UpperTheory.Gal.crystallineComparison.detWeil_of :
    WeilCo := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw LL V _ _ _ _ ρ _ g hg x
  have e : -alpha l g = (resDeg l w : ℤ) := by simp [alpha, hg]
  rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD,
    coe_phiD_pow, stRep_phiV_pow]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detUnit_of :
    UnitOfSpan := by
  intro S _ a v hv
  have hmem : ∀ i : Fin a, ∃ c : Fin a → S, ∑ k, c k • v k = Pi.single i 1 := fun i => by
    have h : (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range v) := by
      rw [hv]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  have hQN : (Matrix.of fun i k => v k i) * (Matrix.of fun k i => c i k) =
      (1 : Matrix (Fin a) (Fin a) S) := by
    ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    simp only [mul_comm (v _ i)]
    rw [h, Pi.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hQN
end
