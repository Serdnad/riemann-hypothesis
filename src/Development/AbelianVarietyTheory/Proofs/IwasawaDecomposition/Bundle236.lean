module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign.DomCurv

section Sqrt

open scoped MatrixOrder

theorem exists_eq_conjTranspose_mul_self {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin k) (Fin k) ℂ, T = Bᴴ * B := by
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

end Sqrt

variable {m r : ℕ}

def domForm (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - Matrix.of x * (Matrix.of x)ᴴ

theorem domGram_eq (x : Fin m → Fin r → ℂ) : domGram m r x = ((domForm m r x)⁻¹)ᵀ := rfl

theorem mContDiffAt_of (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) y := fun a b => by
  show ContDiffAt ℝ k (fun x : Fin m → Fin r → ℂ => x a b) y
  exact ((contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin r → ℂ)) a)).contDiffAt

theorem mdel_of (y ξ : Fin m → Fin r → ℂ) :
    mdel (fun y : Fin m → Fin r → ℂ => Matrix.of y) y ξ = Matrix.of ξ := by
  ext a b
  show del (fun x : Fin m → Fin r → ℂ => x a b) y ξ = ξ a b
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, del_eq_fderiv (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_of (y η : Fin m → Fin r → ℂ) :
    mdbar (fun y : Fin m → Fin r → ℂ => Matrix.of y) y η = 0 := by
  ext a b
  show dbar (fun x : Fin m → Fin r → ℂ => x a b) y η = 0
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem mContDiffAt_domForm (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (domForm m r) y :=
  (mContDiffAt_const 1).sub ((mContDiffAt_of k y).mul (mContDiffAt_of k y).conjTranspose)

theorem domForm_eq_fun : domForm m r = fun y => 1 + -(Matrix.of y * (Matrix.of y)ᴴ) := by
  funext y; simp [domForm, sub_eq_add_neg]

theorem mdel_domForm (y ξ : Fin m → Fin r → ℂ) :
    mdel (domForm m r) y ξ = -(Matrix.of ξ * (Matrix.of y)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdel_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdel_const,
    mdel_neg, mdel_mul h1 h1.conjTranspose, mdel_conjTranspose, mdbar_of, mdel_of]
  simp

theorem mdbar_domForm (y η : Fin m → Fin r → ℂ) :
    mdbar (domForm m r) y η = -(Matrix.of y * (Matrix.of η)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdbar_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdbar_const,
    mdbar_neg, mdbar_mul h1 h1.conjTranspose, mdbar_conjTranspose, mdbar_of, mdel_of]
  simp

theorem conn_domGram {y : Fin m → Fin r → ℂ} (hu : IsUnit (domForm m r y).det)
    (ξ : Fin m → Fin r → ℂ) :
    conn (domGram m r) y ξ = Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) := by
  have e : (fun x => (domGram m r x)ᵀ) = fun x => (domForm m r x)⁻¹ := by
    funext x; rw [domGram_eq, transpose_transpose]
  have e2 : (domGram m r y)ᵀ = (domForm m r y)⁻¹ := congrFun e y
  rw [conn, e2, ← mdel_transpose, e, mdel_inv (mContDiffAt_domForm 1 y) hu, mdel_domForm,
    nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]

theorem curv_domGram_eq {x : Fin m → Fin r → ℂ} (hx : IsUnit (domForm m r x).det)
    (ξ η : Fin m → Fin r → ℂ) :
    curv (domGram m r) x ξ η = -(Matrix.of ξ * ((1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ *
      Matrix.of x) * ((Matrix.of η)ᴴ * (domForm m r x)⁻¹))) := by
  have hev := (mContDiffAt_domForm (m := m) (r := r) 1 x).eventually_isUnit hx
  have he : (fun y => conn (domGram m r) y ξ) =ᶠ[𝓝 x]
      fun y => Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) :=
    hev.mono fun y hy => conn_domGram hy ξ
  have hZ := mContDiffAt_of (m := m) (r := r) 1 x
  have hM := (mContDiffAt_domForm (m := m) (r := r) 1 x).inv hx
  rw [curv, mdbar_congr he, mdbar_mul (mContDiffAt_const (Matrix.of ξ)) (hZ.conjTranspose.mul hM),
    mdbar_const, mdbar_mul hZ.conjTranspose hM, mdbar_inv (mContDiffAt_domForm 1 x) hx,
    mdbar_domForm, mdbar_conjTranspose, mdel_of]
  simp only [Matrix.zero_mul, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_add]
  rw [add_comm]

end GlobalTheory.PointFormSign.DomCurv

namespace GlobalTheory.PointFormSign


open DomCurv in
theorem curv_domGram_isNegSq (m r : ℕ) (x : Fin m → Fin r → ℂ)
    (hx : (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef) : IsNegSq (curv (domGram m r) x) r := by
  have hxA : (domForm m r x).PosDef := hx
  have hu : IsUnit (domForm m r x).det := (isUnit_iff_isUnit_det _).1 hxA.isUnit
  have hM := hxA.inv
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self hM.posSemidef
  have hQ : (1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ * Matrix.of x).PosSemidef :=
    (PosDef.one.add_posSemidef (hM.posSemidef.conjTranspose_mul_mul_same (Matrix.of x))).posSemidef
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hQ
  have hBu : IsUnit B.det := by
    have h1 : IsUnit (Bᴴ * B).det := by rw [← hB]; exact (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  let T : (Fin m → Fin r → ℂ) →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ :=
    { toFun := fun ξ => B * Matrix.of ξ * Cᴴ
      map_add' := fun ξ ξ' => by
        show B * Matrix.of (ξ + ξ') * Cᴴ = B * Matrix.of ξ * Cᴴ + B * Matrix.of ξ' * Cᴴ
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c ξ => by
        show B * (c • Matrix.of ξ) * Cᴴ = c • (B * Matrix.of ξ * Cᴴ)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨B, T, hBu, fun ξ η => ?_⟩
  rw [curv_domGram_eq hu, hC, hB]
  show -(Matrix.of ξ * ((Cᴴ * C) * ((Matrix.of η)ᴴ * (Bᴴ * B)))) =
    B⁻¹ * (-((B * Matrix.of ξ * Cᴴ) * (B * Matrix.of η * Cᴴ)ᴴ)) * B
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hBu]

end GlobalTheory.PointFormSign
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem idS_smul_latS (I : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) {t : Formalism.L2.Herm.intAf F E}
    (ht : t ∈ idS F I) {u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hu : u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N) :
    t • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
  have hA : ∀ p ∈ I, ∀ u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N,
      oToS F E p • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
    intro p hp u hu
    refine Submodule.span_induction (p := fun u _ => oToS F E p • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.subset_span ⟨p • m, Submodule.smul_mem_smul hp hm, ?_⟩
      funext i
      show iA F E ((p • m) i) = (oToS F E p : E ⊗[F] Formalism.L2.Herm.Af F) * iA F E (m i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ c ha
  have hmap : idS F I = Ideal.span (oToS F E '' I) := rfl
  rw [hmap] at ht
  refine Submodule.span_induction (p := fun t _ => t • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨p, hp, rfl⟩
    exact hA p hp u hu
  · rw [zero_smul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [add_smul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c ha

theorem inv_mul_int_away {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (m : ℕ)
    (y y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hle : (Q.asIdeal ^ m) • Formalism.UG.CS.globLat y (stdLat E n) ≤ Formalism.UG.CS.globLat y' (stdLat E n)) :
    ∀ i j, (1 - ε) * (y'⁻¹ * y).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  intro i j
  have hfin := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg
  have hspan : Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using single_mem_stdLat (E := E) k 1
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan
  have hcol : (y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.UG.CS.globLat y (stdLat E n)) := by
    refine (hSR _ _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, mem_latS_std]
    intro k
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  have h1 := idS_smul_latS (Q.asIdeal ^ m) _ (h.one_sub_mem_idS m) hcol
  have h2 := Submodule.span_mono (Set.image_mono hle) h1
  have h3 := ((mem_latS_std _).1 ((hSR y' _).1 h2)) i
  convert h3 using 1
  have e : ((⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) •
      ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) =
      (1 - ε) • ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := rfl
  rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one, Pi.smul_apply,
    smul_eq_mul]
  rfl

end GlobalTheory.InertNbr
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultGelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}

theorem mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem isURep (M : DSModel V S) (τ : D.what₂.Tau) : IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) :=
  isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1

theorem rder_apply (hT : IsMultMap θ M J χ T) [inst : DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq D.what₂.Tau := fun a b => Classical.propDecidable (a = b)
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u)
      (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hT.equiv τ _ (exp_mem_UH hG hX t)
      (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hT τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hT τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hT τ v Z w _ rfl

theorem gelf_apply : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  intro D θ V S M J χ _ T hT _ τ k v w hw
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hT τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

end GlobalTheory.MultGelf

end
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
end
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernSpan

theorem kron_pow' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) (n : ℕ) : kron a b ^ n = kron (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [kron_one]
  | succ n ih => rw [pow_succ, ih, ← kron_mul, pow_succ, pow_succ]

theorem trace_kron' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).trace = a.trace * b.trace := by
  rw [kron, ← Matrix.trace_kronecker]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm fun x => Matrix.kroneckerMap (· * ·) a b x x

theorem trace_pow_kron_add {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R)
    (L' : Matrix (Fin N) (Fin N) R) (i : ℕ) :
    ((kron L 1 + kron 1 L') ^ i).trace =
      ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  have hc : Commute (kron L (1 : Matrix (Fin N) (Fin N) R)) (kron (1 : Matrix (Fin M) (Fin M) R) L') := by
    unfold Commute SemiconjBy
    rw [← kron_mul, ← kron_mul, mul_one, one_mul, mul_one, one_mul]
  rw [hc.add_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kron_pow', kron_pow', one_pow, one_pow, ← kron_mul, mul_one, one_mul, ← Nat.cast_comm,
    ← nsmul_eq_mul, Matrix.trace_smul, nsmul_eq_mul, trace_kron', mul_assoc]

end GlobalTheory.GoodMetric.ChernSpan
end
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trSpan_mul : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ)
    (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  intro ι m S _ _ w w' f g hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl1, hlw, rfl⟩ := hx
      obtain ⟨l', hl1', hlw', rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨l ++ l', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hl1 x h
        · exact hl1' x h
      · simp [List.map_append, List.sum_append, hlw, hlw']
      · funext A
        simp [trProd, List.map_append, List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

end GlobalTheory.GoodMetric.ChernSpan
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conj_principalFractional_integral_idempotentSum : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemIntegral.conj_mem_intAf | exact GlobalTheory.IdemIntegral.conj_mem_intAf | (intros; apply GlobalTheory.IdemIntegral.conj_mem_intAf <;> assumption)
end
