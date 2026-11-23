module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsPshOfTangent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q F 𝔞 had h𝔞 h1 h2
  obtain ⟨h3, h4⟩ := LevelTowerAlt.sub_eig A had.2
  have h5 := (LevelTowerAlt.Sub.of_smul_le h𝔞 h1).trans h3
  have h6 := h4.trans (LevelTowerAlt.Sub.of_smul_le h𝔞 h2)
  have e1 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h3 h4 h5 h2
  have e2 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h5 h6 h3 h1
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  push_cast at e1 e2
  rw [LinPt.labDeg, LinPt.labDeg, ← sub_div, abs_div, abs_of_pos hn]
  refine div_le_div_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) hn.le <;> linarith
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem eigen_projection_conjugate_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  intro E _ _ _ g Λ _ _ Ψ _ R I hI s
  simp only [LevelTowerAlt.eigComp_eq]
  exact ⟨fun v hv w hw => gram_conj R hI s hv hw, fun r v hv hli => proj_indep R hI s hv hli⟩

end LevelTowerAlt
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem riemann_lattice_eigen_projections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨LevelTowerAlt.precomp_injective R, LevelTowerAlt.span_top R,
    fun s => ⟨fun x => ?_, fun x hx => ?_, fun c x y => ?_, fun a x => ?_⟩, fun x => ?_,
    fun s s' hss' x hx y hy => LevelTowerAlt.ip_orth R hss' hx hy⟩
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_mem _ _ _
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_eig_self hx
  · simp only [LevelTowerAlt.eigComp_eq, map_add (f := _), map_smul]
  · simp only [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_act _ _ _ _
  · simp only [LevelTowerAlt.eigComp_eq]
    conv_rhs => rw [← LevelTowerAlt.sum_proj R.B x]
    exact Fintype.sum_equiv (LevelTowerAlt.embEquiv E) _ _ (fun _ => rfl)

end LevelTowerAlt
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Sg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem posDef_Hm (R : RiemLat E g Λ) : R.Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos R.herm fun x hx => ?_
  have h1 := R.pos (star x) (star_ne_zero.2 hx)
  rw [star_star] at h1
  refine Complex.pos_iff.2 ⟨h1, ?_⟩
  have h2 : star (star x ⬝ᵥ R.Hm *ᵥ x) = star x ⬝ᵥ R.Hm *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, R.herm.eq, dotProduct_mulVec, dotProduct_comm]
  exact (Complex.conj_eq_iff_im.1 h2).symm

theorem mul_entry {l m : Type} (A : Matrix l (Fin g) ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (B : Matrix m (Fin g) ℂ)
    (i : l) (j : m) : (A * H * Bᴴ) i j = A i ⬝ᵥ H *ᵥ star (B j) := by
  rw [Matrix.mul_assoc]
  rfl

def per (R : RiemLat E g Λ) (e : Fin g ⊕ Fin g → Λ) : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ := Matrix.of fun k => R.P (e k)

def frm (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (e : Fin g ⊕ Fin g → Λ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  (2 * Complex.I) • (Int.castRingHom ℂ).mapMatrix (Matrix.of fun k l => f (e k) (e l))

theorem per_eq (R : RiemLat E g Λ) (e : Fin g ⊕ Fin g → Λ) :
    per R e * R.Hm * (per R e)ᴴ - (per R e * R.Hm * (per R e)ᴴ)ᵀ = frm R.form e := by
  ext k l
  have hh := (Matrix.isHermitian_mul_mul_conjTranspose (per R e) R.herm).apply l k
  have h1 : ((per R e * R.Hm * (per R e)ᴴ) k l).im = R.form (e k) (e l) := by
    rw [mul_entry]
    exact R.im _ _
  rw [Matrix.sub_apply, Matrix.transpose_apply, ← hh, Complex.star_def, Complex.sub_conj, h1]
  simp [frm]
  ring

theorem frm_det {f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ} (hf : Function.Injective f) (e : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :
    (frm f e).det ≠ 0 := by
  rw [frm, det_smul, ← RingHom.map_det]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)) ?_
  rw [eq_intCast, Int.cast_ne_zero]
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  have h1 : f (∑ k, v k • e k) = 0 := by
    refine e.ext fun l => ?_
    have := congrFun h0 l

    simpa [Matrix.vecMul, dotProduct, map_sum, LinearMap.sum_apply] using this
  have h2 : ∑ k, v k • e k = 0 := hf (by rw [h1, map_zero])
  exact hv (funext (Fintype.linearIndependent_iff.1 e.linearIndependent v h2))

end LevelTowerAlt.Sg

open LevelTowerAlt.Sg in
theorem LevelTowerAlt.holomorphic_family_smooth_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ), IsOpen U → IsHolFam U R → (∀ i j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).re) U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).im) U) ∧ (∀ a x, DifferentiableOn ℂ (fun t => (R t).B a x) U) ∧ ∀ (m : ℕ) (u : Fin m → (Fin n → ℂ) → Fin g → ℂ), (∀ i, DifferentiableOn ℂ (u i) U) → (∀ t ∈ U, LinearIndependent ℂ fun i => u i t) → ReciprocityTheory.AnForm.A.IsPsh U fun t => Real.log ((R t).gram fun i => u i t).det.re := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R hU hR
  rcases U.eq_empty_or_nonempty with rfl | ⟨t1, ht1⟩
  · refine ⟨fun i j => ⟨contDiffOn_empty, contDiffOn_empty⟩, fun a x => differentiableOn_empty, fun m u _ _ => ?_⟩
    exact isPsh_of_tangent (continuousOn_empty _) fun t0 h => absurd h (Set.notMem_empty t0)
  haveI := (R t1).free
  haveI := (R t1).fin
  let e : Module.Basis (Fin g ⊕ Fin g) ℤ Λ :=
    (Module.finBasisOfFinrankEq ℤ Λ (n := g + g) (by rw [(R t1).rank, two_mul])).reindex finSumFinEquiv.symm
  have hK : (frm (R t1).form e).det ≠ 0 := frm_det (R t1).unimod.1 e
  have hper : ∀ v : Fin g ⊕ Fin g → Λ, MS ℂ U fun t => per (R t) v := fun v =>
    MS.of_diff hU fun i j => differentiableOn_pi.1 (hR.2 (v i)) j
  have he : ∀ t ∈ U, per (R t) e * (R t).Hm * (per (R t) e)ᴴ - (per (R t) e * (R t).Hm * (per (R t) e)ᴴ)ᵀ =
      frm (R t1).form e := fun t ht => by rw [per_eq, hR.1 t ht t1 ht1]
  refine ⟨fun i j => ?_, fun a x t0 ht0 => ?_, fun m u hu hli => ?_⟩
  · have h := herm_smooth (H := fun t => (R t).Hm) (hper e) hK he i j
    exact ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩
  · obtain ⟨V, G, C, hVo, htV, hVU, hG, -, hGC, -⟩ :=
      local_frame (H := fun t => (R t).Hm) hU (hper e) hK he ht0
    have hM : MS ℂ V fun t => (Matrix.of fun _ : Unit => x) * (G t * C) * per (R t) (fun k => a • e k) :=
      ((MS.const _).mul (hG.mul (MS.const _))).mul ((hper _).mono hVU)
    have hD : DifferentiableOn ℂ (fun t => (R t).B a x) V := by
      refine differentiableOn_pi.2 fun j => ((hM () j).differentiableOn (by simp)).congr fun t ht => ?_
      have hrow : ∀ (y : Matrix Unit (Fin g ⊕ Fin g) ℂ) (v : Fin g ⊕ Fin g → Λ),
          (y * per (R t) v) () = ∑ k, y () k • (R t).P (v k) := by
        intro y v
        funext b
        simp [Matrix.mul_apply, per, Finset.sum_apply]
      have h1 : x = ∑ k, ((Matrix.of fun _ : Unit => x) * (G t * C)) () k • (R t).P (e k) := by
        rw [← hrow, Matrix.mul_assoc, hGC t ht, Matrix.mul_one]
        rfl
      refine congrFun (f := (R t).B a x) ?_ j
      refine Eq.trans ?_ (hrow ((Matrix.of fun _ : Unit => x) * (G t * C)) fun k => a • e k).symm
      conv_lhs => rw [h1]

      simp only [map_sum, map_smul, (R t).act]
    exact (hD.differentiableAt (hVo.mem_nhds htV)).differentiableWithinAt
  · have h := logdet_psh (H := fun t => (R t).Hm) (u := fun t => Matrix.of fun i => u i t) hU (hper e) hK
      (fun t _ => posDef_Hm (R t)) he (MS.of_diff hU fun i j => differentiableOn_pi.1 (hu i) j) hli
    have e1 : (fun t => Real.log ((R t).gram fun i => u i t).det.re) = fun t =>
        Real.log ((Matrix.of fun i => u i t) * (R t).Hm * (Matrix.of fun i => u i t)ᴴ).det.re := by
      funext t
      rw [← Matrix.det_transpose]
      congr 3
      ext a b
      rw [mul_entry]
      rfl
    rw [e1]
    exact h
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

theorem cuspW_of_conj (R R' : RiemLat E g Λ) (σ σ' : Ψ → (𝓞 E →+* ℂ))
    (h1 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R'.form I ↔ IsIsoSub R.form I)
    (h2 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → ∀ τ, ∀ v ∈ I, ∀ w ∈ I,
      R'.ip (proj R'.B (σ' τ) (R'.P v)) (proj R'.B (σ' τ) (R'.P w)) =
        conj (R.ip (proj R.B (σ τ) (R.P v)) (proj R.B (σ τ) (R.P w)))) : R'.cuspW σ' = R.cuspW σ := by
  have h3 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → R'.nz σ' I = R.nz σ I := by
    intro I hI
    unfold RiemLat.nz
    split_ifs with h
    · have hv := h.choose_spec.choose_spec.2.1
      unfold RiemLat.nzOf
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      have h4 : (R'.gram fun a => eigComp R'.B (σ' τ) (R'.P (h.choose_spec.choose a))) =
          (starRingEnd ℂ).mapMatrix (R.gram fun a => eigComp R.B (σ τ) (R.P (h.choose_spec.choose a))) := by
        ext a b
        simp only [RiemLat.gram, eigComp_eq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
        exact h2 I hI τ _ (hv a) _ (hv b)
      rw [h4, ← RingHom.map_det, Complex.conj_re]
    · rfl
  unfold RiemLat.cuspW RiemLat.IsCusp
  congr 2
  ext x
  constructor
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).1 c⟩, by rw [h3 I ((h1 I).1 c)]⟩
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).2 c⟩, by rw [h3 I c]⟩

def conjL (f : Module.End ℂ (Fin g → ℂ)) : Module.End ℂ (Fin g → ℂ) where
  toFun x := star (f (star x))
  map_add' x y := by rw [star_add, map_add (f := _), star_add]
  map_smul' c x := by rw [star_smul, map_smul, star_smul, star_star, RingHom.id_apply]

theorem conjL_apply (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) : conjL f x = star (f (star x)) := rfl

def conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a := conjL (ρ a)
  map_one' := LinearMap.ext fun x => by simp [conjL_apply]
  map_mul' a b := LinearMap.ext fun x => by simp [conjL_apply]
  map_zero' := LinearMap.ext fun x => by simp [conjL_apply]
  map_add' a b := LinearMap.ext fun x => by simp [conjL_apply]

omit [NumberField E] [IsCMField E] in
theorem conjB_star (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) :
    conjB ρ a (star x) = star (ρ a x) := by
  show star (ρ a (star (star x))) = _
  rw [star_star]

theorem dot_conj (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ H.map (starRingEnd ℂ) *ᵥ star w = conj (star z ⬝ᵥ H *ᵥ star (star w)) := by

  simp only [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, Complex.star_def,
  Complex.conj_conj]

def conjLat (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := neg_eq_zero.2 (R.alt x)
  unimod := neg_involutive.bijective.comp R.unimod
  adj a a' h x y := congrArg Neg.neg (R.adj a a' h x y)
  P := (starAddEquiv : (Fin g → ℂ) ≃+ (Fin g → ℂ)).toAddMonoidHom.comp R.P
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := R.herm.map _ fun _ => rfl
  pos z hz := by
    rw [dot_conj, Complex.conj_re]
    exact R.pos (star z) (star_ne_zero.2 hz)
  im x y := by
    show (star (R.P x) ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star (R.P y))).im = ((-(R.form x y) : ℤ) : ℝ)
    rw [dot_conj]
    simp only [star_star (R.P x), star_star (R.P y)]
    rw [Complex.conj_im, R.im, Int.cast_neg]
  B := conjB R.B
  act a x := by
    show star (R.P (a • x)) = conjB R.B a (star (R.P x))
    rw [conjB_star, R.act]

theorem conjLat_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (conjLat R).ip (star x) (star y) = conj (R.ip x y) := by
  show star y ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star x) = conj (y ⬝ᵥ R.Hm *ᵥ star x)
  rw [dot_conj]
  simp only [star_star x, star_star y]

omit [IsCMField E] in
theorem proj_conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    proj (conjB ρ) ((starRingEnd ℂ).comp s) (star x) = star (proj ρ s x) := by
  rw [proj_apply, proj_apply, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjB_star, star_smul, coef_conj]
  rfl

end

theorem riemann_lattice_conjugate_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ _
  refine ⟨cuspW_of_conj R R σ _ (fun _ => Iff.rfl) fun I hI τ v hv w hw => gram_conj R hI (σ τ) hv hw,
    conjLat R, fun _ => rfl, rfl, conjB_star R.B, cuspW_of_conj R _ σ _ (fun I => ?_) fun I _ τ v _ w _ => ?_⟩
  · exact forall₄_congr fun v _ w _ => neg_eq_zero
  · exact (congrArg₂ (conjLat R).ip (proj_conjB R.B (σ τ) (R.P v)) (proj_conjB R.B (σ τ) (R.P w))).trans
      (conjLat_ip R _ _)

end LevelTowerAlt
end
end
