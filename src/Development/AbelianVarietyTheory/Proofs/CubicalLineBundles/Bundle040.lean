module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOne
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Matrix.Hermitian
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
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PerfectTensorKernel

open GlobalTheory.CechPic GlobalTheory.HermTensorKernel GlobalTheory.Serre

theorem kTriv_of_perfect : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (L : LB G.left) (N : LB A.left) (h : M →ₗ[O] M →+ O) (n : ℕ) (x y : Fin n → M), (∀ m, m = ∑ i, h m (y i) • x i) → L.IsLB → N.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∃ t : LB.Gen (Theta A N), t.IsGen) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G)) → Out.KTriv G L → Out.KTriv A N := by
  intro S O _ G A _ _ _ _ a b M _ _ t L N h n x₀ y₀ hdual hL hN hΘL hΘ hiso hK R _ s x hx
  have am := a.hom
  let l : M → (M →ₗ[O] O) := fun n =>
    { toFun := fun m => h m n
      map_add' := fun m m' => by rw [map_add (f := _), AddMonoidHom.add_apply]
      map_smul' := fun c m => by rw [map_smul, AddMonoidHom.smul_apply, RingHom.id_apply] }
  let q : M → (A ⟶ G) := fun n => t.mapLeft (IsTensor.self a) (l n)
  have qm : ∀ n, IsMonHom (q n) := fun n => IsTensor.isMonHom_mapLeft _ _ _
  have hq : ∀ m n, t.tmul m ≫ q n = a.act (h m n) := fun m n => by
    simp only [q, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    rfl
  have basic : ∀ {T : Over S} (g y : T ⟶ G) (m n : M),
      lam (cls N hN) (g ≫ t.tmul m) (y ≫ t.tmul n) = lam (cls L hL) (g ≫ a.act (h m n)) y := by
    intro T g y m n
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hiso m n)
    have h' := congrArg (pull (lift g y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over S} (n : M) (u : T ⟶ A) (y : T ⟶ G),
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y := by
    intro T n u y
    refine t.induction_on (P := fun u =>
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y) u ?_ (fun m g => ?_)
      fun u v hu hv => ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [Category.assoc, hq, basic]
    · rw [lam_mul_left hN hΘ, hu, hv, MonObj.mul_comp, lam_mul_left hL hΘL]
  have H := (translDiff_iff hN x).1 hx
  have z : ∀ n, x ≫ q n = 1 := fun n => by
    refine hK R s _ ((translDiff_iff hL (x ≫ q n)).2 ?_)
    have H' := H.pull (Over.mk s ◁ t.tmul n).left
    rwa [pull_lam, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst_assoc, whiskerLeft_snd, key,
      Category.assoc] at H'
  have dec : ∀ u : Over.mk s ⟶ A, u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i) := by
    intro u
    refine t.induction_on (P := fun u => u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i)) u ?_
      (fun m g => ?_) fun u v hu hv => ?_
    · simp only [MonObj.one_comp, Finset.prod_const_one]
    · simp only [Category.assoc, reassoc_of% hq, ← t.tmul_smul']
      refine Eq.trans ?_ (map_prod (preHom g) _ _)
      rw [← t.tmul_sum, ← hdual]
      rfl
    · simp only [MonObj.mul_comp, Finset.prod_mul_distrib, ← hu, ← hv]
  rw [dec x]
  simp only [z, MonObj.one_comp, Finset.prod_const_one]
  rfl

end GlobalTheory.PerfectTensorKernel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieMetric

section Linear

variable {K : Type} [Field K] {g : ℕ}

def ofGram (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) : HermFam K (Fin g → K) where
  form s c c' := star (s ∘ c) ⬝ᵥ (G s).mulVec (s ∘ c')
  add_right s x y z := by
    rw [show s ∘ (y + z) = s ∘ y + s ∘ z from funext fun i => map_add s _ _, Matrix.mulVec_add, dotProduct_add]
  smul_right s a x y := by
    rw [show s ∘ (a • y) = s a • (s ∘ y) from funext fun i => map_mul s _ _, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  conj_symm s x y := by
    change star _ = _
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (hG s).isHermitian.eq, Matrix.dotProduct_mulVec]
  posDef s n v hv := by
    letI : Algebra K ℂ := s.toAlgebra
    have h1 : LinearIndependent ℂ (fun i => algebraMap K ℂ ∘ v i) := linearIndependent_algebraMap_comp_iff.2 hv
    have h2 := (hG s).conjTranspose_mul_mul_same (B := (Matrix.of fun i => s ∘ v i).transpose)
      (Matrix.mulVec_injective_iff.2 h1)
    convert h2 using 1
    ext i j
    rw [Matrix.mul_assoc]
    rfl

theorem ofGram_single (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) (s : K →+* ℂ) (i j : Fin g) :
    (ofGram G hG).form s (Pi.single i 1) (Pi.single j 1) = G s i j := by
  have e : ∀ i : Fin g, s ∘ (Pi.single i 1 : Fin g → K) = Pi.single i 1 := fun i => by
    ext k
    by_cases h : k = i <;> simp [h]
  simp [ofGram, e, ← Pi.single_star]

theorem form_sum_right (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, s (y j) * h.form s x (Pi.single j 1) := by
  let f : (Fin g → K) →+ ℂ := AddMonoidHom.mk' (h.form s x) (h.add_right s x)
  have e : y = ∑ j, y j • Pi.single j (1 : K) := pi_eq_sum_univ' y
  refine (congrArg f e).trans ((map_sum f _ _).trans (Finset.sum_congr rfl fun j _ => h.smul_right s _ _ _))

theorem ext_single {h h' : HermFam K (Fin g → K)}
    (e : ∀ s i j, h.form s (Pi.single i 1) (Pi.single j 1) = h'.form s (Pi.single i 1) (Pi.single j 1)) : h = h' := by
  have e1 : ∀ s i y, h.form s (Pi.single i 1) y = h'.form s (Pi.single i 1) y := fun s i y => by
    rw [form_sum_right h, form_sum_right h']
    simp only [e]
  have e2 : h.form = h'.form := by
    funext s x y
    rw [form_sum_right h, form_sum_right h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm, ← h'.conj_symm, e1]
  cases h
  cases h'
  congr

theorem posDef_gram {n : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {W : Fin n → Fin g → ℂ}
    (hW : LinearIndependent ℂ W) : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).PosDef := by
  have h1 : Hm.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx =>
    Complex.pos_iff.2 ⟨by simpa using hp (star x) (by simpa using hx), (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h2 := (h1.mul_mul_conjTranspose_same (B := Matrix.of W) (Matrix.vecMul_injective_iff.2 hW)).transpose.smul
    (a := (Real.pi : ℂ)) (by exact_mod_cast Real.pi_pos)
  rw [Matrix.mul_assoc] at h2
  exact h2

end Linear

theorem linearIndependent_of_isLieBasis {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun ((hv.2 w h1).unique h2 h2')

theorem hermForm_eq (hU : ThetaUnifAV) {R : Type} [CommRing R] {P : Out.PolAV (Sp R)} {s : R →+* ℂ}
    {Q Q' : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left} {ψ' : Q'.A.left ⟶ P.A.left} (h : IsPolFibre s P Q ψ)
    (h' : IsPolFibre s P Q' ψ') {g g' : ℕ} {u : HolUnif Q.A Q.L g} {u' : HolUnif Q'.A Q'.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (hu : u.IsAH Hm χ) (hu' : u'.IsAH Hm' χ') {I : Type} {v : I → (epsR R ⟶ P.A)} (hv : ∀ i, IsTangent (v i))
    {w : I → (epsR ℂ ⟶ Q.A)} {w' : I → (epsR ℂ ⟶ Q'.A)} {W : I → Fin g → ℂ} {W' : I → Fin g' → ℂ}
    (hw : ∀ i, IsVecOver s ψ (v i) (w i) ∧ u.IsDiff (W i) (w i))
    (hw' : ∀ i, IsVecOver s ψ' (v i) (w' i) ∧ u'.IsDiff (W' i) (w' i)) (i j : I) :
    hermForm Hm (W i) (W j) = hermForm Hm' (W' i) (W' j) := by
  obtain ⟨e, he, heψ⟩ := grpPullback_iso h.2.1 h'.2.1
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' g' u' Hm' χ' hu'
  obtain ⟨F, hF, -, hd, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L g g' u u' t1 t2
    e.hom he
  have hW : ∀ k, F (W k) = W' k := fun k => by
    obtain ⟨a, b⟩ := hd _ _ ((hw k).1.isTangent h.2.1 (hv k)) (hw k).2
    have c : w k ≫ e.hom = w' k := (existsUnique_isVecOver h'.2.1.1 (v k)).unique
      (by unfold IsVecOver; rw [Over.comp_left, Category.assoc, heψ]; exact (hw k).1) (hw' k).1
    rw [c] at a b
    exact (t1 _ a).unique b (hw' k).2
  obtain ⟨t, ht⟩ : LBIso (Q'.L.pull e.hom.left) Q.L :=
    LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB P.isLB _) Q.isLB (PolFibre.lbIso_pull_comp h'.2.2 _).symm
      (heψ ▸ h.2.2)
  have := hermForm_pull_eq_of_lbIso_pow Q.A Q'.A Q.L Q'.L Q.isLB Q'.isLB g g' u u' Hm χ Hm' χ' hu hu' e.hom F hF 1 1
    ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ (W i) (W j)
  simpa [hW] using this.symm

theorem exists_unique_isHerm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∃ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h) ∧ ∀ h h' : HermFam K (Fin F.P₀.g → K), F.IsHerm h → F.IsHerm h' → h = h' := by
  intro hU hL K _ _ P F
  refine ⟨?_, fun h h' H H' => ext_single fun s i j => ?_⟩
  · have key : ∀ s : K →+* ℂ, ∃ G : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ, G.PosDef ∧
        ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
          (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin F.P₀.g → Fin Q.g → ℂ),
          IsPolFibre s F.P₀ Q ψ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
          ∀ i j, G i j = Real.pi * hermForm Hm (W j) (W i) := fun s => by
      obtain ⟨Q, ψ, h⟩ := exists_isPolFibre hL.polBaseChange s F.P₀
      haveI := F.P₀.isAb.comm
      haveI := Q.isAb.comm
      haveI := F.P₀.smoothDim
      obtain ⟨v', hb, hv'⟩ := exists_isLieBasis_baseChange K ℂ s F.P₀.A Q.A ψ h.2.1
        (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
      obtain ⟨rig, hrig⟩ := Q.rigid
      obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU Q rig hrig
      choose W hW using fun i => (hd _ (hb.1 i)).exists
      exact ⟨_, posDef_gram hA.1 hA.2.1 (linearIndependent_of_isLieBasis u hd' hb hW), Q, ψ, v', u, Hm, χ, W, h, hA,
        fun i => ⟨hv' i, hW i⟩, fun _ _ => rfl⟩
    choose G hG H using key
    refine ⟨ofGram G hG, fun s => ?_⟩
    simpa only [ofGram_single] using H s
  · obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
    obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H' s
    rw [d, d', hermForm_eq hU a a' b b' F.basis.1 c c']

end GlobalTheory.CM.LieMetric
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermWeil

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem ex_natSmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_div_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_natSmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  exact (u.ker _).2 a.2

theorem exists_eq_ex_div {n : ℕ} (hn : 0 < n) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (hx : x ^ n = 1) :
    ∃ a : u.Λ, x = u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 (by rw [ex_natSmul, hx])⟩, ?_⟩
  rw [inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]

theorem map_mem {B : Over (Sp ℂ)} [GrpObj B] {M : LB B.left} {g' : ℕ} (v : HolUnif B M g') {f : A ⟶ B}
    {F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hF : ∀ z, v.ex (F z) = u.ex z ≫ f) (a : u.Λ) : F a ∈ v.Λ := by
  rw [← v.ker, hF, (u.ker _).2 a.2, ← ex_zero u, ← hF, map_zero, ex_zero]

end Unif

def rootVal (m : ℤ) (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n)) (Complex.exp_ne_zero _)

theorem eq_of_rootVal {m m' : ℤ} (h : ∀ n : ℕ, 0 < n → rootVal m n = rootVal m' n) : m = m' := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ m' - m := by
    intro n hn
    have e := congrArg Units.val (h n hn)
    simp only [rootVal, Units.val_mk0] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨k, ?_⟩
    have : ((m' - m : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
      field_simp at hk
      linear_combination (2 * Real.pi * Complex.I) * hk
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key ((m' - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; omega)
  omega

theorem hermForm_eq_of_im {p q a b : ℕ} (HA : Matrix (Fin a) (Fin a) ℂ) (HB : Matrix (Fin b) (Fin b) ℂ)
    (F₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin a → ℂ)) (F₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (G₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (G₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    {S : Set (Fin p → ℂ)} {T : Set (Fin q → ℂ)} (hS : Submodule.span ℝ S = ⊤) (hT : Submodule.span ℝ T = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ T, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im) (z w) :
    hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w) := by
  have him : ∀ z w, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ T := hT ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw => exact h z hz w hw
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx]
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add (f := _), add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul r x _ hx =>
      rw [← Complex.coe_smul]
      simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at hx ⊢
      rw [hx]
  refine Complex.ext ?_ (him z w)
  have e := him (Complex.I • z) w
  simpa only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.I_mul_im] using e

theorem weilIs_iff (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (a b : u.Λ) :
    ∃ m : ℤ, (m : ℝ) = (hermForm Hm a b).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) ↔
        c = rootVal m n) := by
  obtain ⟨Ef, hE, -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P P.g u Hm χ h
  refine ⟨Ef a b, hE a b, fun n c hn => ⟨fun hc => ?_, fun hc => hW n a b c hn (by rw [hc]; rfl)⟩⟩
  exact weilIs_unique_fieldPoint (Sp ℂ) P.A P.L P.isLB ℂ (𝟙 _) n _ _ c _ hc (hW n a b (rootVal (Ef a b) n) hn rfl)

end GlobalTheory.CM.HermWeil

namespace GlobalTheory.CM
open HermWeil

theorem weilEq_iff_hermForm_eq : ThetaUnifAV → Out.Laws → ∀ (X Y A B : Out.PolAV (Sp ℂ)) (uX : HolUnif X.A X.L X.g) (uY : HolUnif Y.A Y.L Y.g) (uA : HolUnif A.A A.L A.g) (uB : HolUnif B.A B.L B.g) (HA : Matrix (Fin A.g) (Fin A.g) ℂ) (HB : Matrix (Fin B.g) (Fin B.g) ℂ) (χA : uA.Λ → ℂ) (χB : uB.Λ → ℂ), uA.IsAH HA χA → uB.IsAH HB χB →
  ∀ (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) (F₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (F₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (G₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)) (G₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)),
  (∀ z, uA.ex (F₁ z) = uX.ex z ≫ f₁) → (∀ z, uA.ex (F₂ z) = uY.ex z ≫ f₂) → (∀ z, uB.ex (G₁ z) = uX.ex z ≫ g₁) → (∀ z, uB.ex (G₂ z) = uY.ex z ≫ g₂) →
  (WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp ℂ)) ↔ ∀ z w, hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w)) := by
  intro hU _ X Y A B uX uY uA uB HA HB χA χB hA hB f₁ f₂ g₁ g₂ F₁ F₂ G₁ G₂ h₁ h₂ h₃ h₄
  have key : ∀ (a : uX.Λ) (b : uY.Λ), ∃ m m' : ℤ, (m : ℝ) = (hermForm HA (F₁ a) (F₂ b)).im ∧
      (m' : ℝ) = (hermForm HB (G₁ a) (G₂ b)).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs A.A A.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ f₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ f₂) (unitOn c) ↔ c = rootVal m n) ∧
      (Out.WeilIs B.A B.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ g₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ g₂) (unitOn c) ↔ c = rootVal m' n) := by
    intro a b
    obtain ⟨m, hm, hw⟩ := weilIs_iff hU A uA hA ⟨_, map_mem uX uA h₁ a⟩ ⟨_, map_mem uY uA h₂ b⟩
    obtain ⟨m', hm', hw'⟩ := weilIs_iff hU B uB hB ⟨_, map_mem uX uB h₃ a⟩ ⟨_, map_mem uY uB h₄ b⟩
    refine ⟨m, m', hm, hm', fun n c hn => ?_⟩
    rw [← h₁, ← h₂, ← h₃, ← h₄, map_smul, map_smul, map_smul, map_smul]
    exact ⟨hw n c hn, hw' n c hn⟩
  constructor
  · intro h
    refine hermForm_eq_of_im HA HB F₁ F₂ G₁ G₂ uX.full uY.full fun a ha b hb => ?_
    obtain ⟨m, m', hm, hm', hw⟩ := key ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hm, ← hm', eq_of_rootVal (m := m) (m' := m') fun n hn => ?_]
    exact (hw n _ hn).2.1 ((h n _ _ _ hn (ex_div_pow uX hn ⟨a, ha⟩) (ex_div_pow uY hn ⟨b, hb⟩)).1
      ((hw n _ hn).1.2 rfl))
  · intro h n x y c hn hx hy
    obtain ⟨a, rfl⟩ := exists_eq_ex_div uX hn x hx
    obtain ⟨b, rfl⟩ := exists_eq_ex_div uY hn y hy
    obtain ⟨m, m', hm, hm', hw⟩ := key a b
    obtain rfl : m = m' := by
      have : (m : ℝ) = m' := by rw [hm, hm', h]
      exact_mod_cast this
    exact (hw n c hn).1.trans (hw n c hn).2.symm

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_fractionalIdeal_traceForm_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), D.p + D.q = 1 → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : D.La →ₗ[𝓞 E] E) (β : E), 𝔞 ≠ 0 ∧ Function.Injective e ∧ LinearMap.range e = (𝔞 : Submodule (𝓞 E) E) ∧ IsCMField.complexConj E β = β ∧ (∀ τ : E →+* ℂ, 0 < (τ β).re) ∧
  (∀ (Ω : Type) [Field Ω] [CharZero Ω], Nat.card (E →+* Ω) = Module.finrank ℚ E → ∀ (τ₀ : E →+* Ω) x y, τ₀ (((h x y : OK H) : 𝓞 E) : E) = ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 (β * e x * IsCMField.complexConj E (e y))) ∧
  2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2 - Real.log (NumberField.rootDiscr E)) := by
  first | exact @GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | exact GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | (intros; apply GlobalTheory.CM.exists_ideal_traceForm_of_rank_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.isEigenvectorAt_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (t₀ : SAB H (Sp K)) (B : SAB H (Sp (𝓞 K))) (m : SABMap t₀ Xo.univ.t x) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K))) (τ : E →+* ℂ) (w : epsR K ⟶ t₀.G), (∀ a : 𝓞 E, ∃ w' : epsR K ⟶ t₀.G, IsLieComb ![LamF.labK c K τ (a : E)] ![w] w' ∧ w.left ≫ m'.φ ≫ (B.act.act a).left = w'.left ≫ m'.φ) → IsEigAt c τ (w.left ≫ m.φ) := by
  first | exact @GlobalTheory.LamT.isEigAt_of_model | exact GlobalTheory.LamT.isEigAt_of_model | (intros; apply GlobalTheory.LamT.isEigAt_of_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.ellipticCurve_lattice_baseChange_stable : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  first | exact @GlobalTheory.curve_lattice_baseChange | exact GlobalTheory.curve_lattice_baseChange | (intros; apply GlobalTheory.curve_lattice_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.isIntegral_derivative_curve_hom_good_reduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  first | exact @GlobalTheory.isIntegral_of_hom_derivative | exact GlobalTheory.isIntegral_of_hom_derivative | (intros; apply GlobalTheory.isIntegral_of_hom_derivative <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.det_dvd_equivariant_framePolynomial : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  first | exact @GlobalTheory.FrameDet.det_dvd_of_equivariant | exact GlobalTheory.FrameDet.det_dvd_of_equivariant | (intros; apply GlobalTheory.FrameDet.det_dvd_of_equivariant <;> assumption)
end
