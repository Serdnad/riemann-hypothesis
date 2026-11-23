module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrSB

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterativeScalingBound.main
  | exact _root_.GlobalTheory.IterativeScalingBound.main
  | (apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)

theorem isLocallyConstant_addChar {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    (ψ : AddChar G ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hker : ∀ y ∈ V, ψ y = 1 := by
    intro y hy
    apply eq_one_of_pow_two_pow
    intro k
    have hm : (2 ^ k) • y ∈ V := V.toAddSubgroup.nsmul_mem hy _
    have := hV hm
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
    have h := ((continuous_sub_right x).tendsto x)
    rwa [sub_self] at h
  filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy
  have e : y = x + (y - x) := by abel
  rw [e, AddChar.map_add_eq_mul, hker _ hy, mul_one]

theorem continuous_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have h : Continuous (GlobalTheory.LatVac.liftV v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp h

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  intro F _ _ κ _ ψ hψ v w φ hφ
  have hloc := isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)
  have hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨?_, ?_⟩
  · exact (hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))
  · have hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1) :=
      hφ.2.comp_homeomorph (Homeomorph.addRight w.1)
    exact hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))

end GlobalTheory.SchrSB
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField F] [NumberField E] in
theorem prod_tens_ext {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] {x y : (A × B) ⊗[F] E}
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz x, hz y, h1, h2]

theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x y : AE F E}
    (hf : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y)
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), piInf τ x = piInf τ y) : x = y := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y := by
    refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have e : ∀ z : AE F E, infEmb τ (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)) = piInf τ z := fun z => by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]; rfl
    rw [e, e]; exact hi w τ
  exact prod_tens_ext (A := Ainf F) (B := Af F) h1 hf

end GlobalTheory.TorusMat

namespace GlobalTheory.TorusMat

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) :
    piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
  simp

theorem piInf_infScale {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (s : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = s := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (GlobalTheory.TorusTheta.infScale F s) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨w, hr⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr]
  exact congrArg (fun x : ℝ => (x : ℂ)) (e.trans rfl)

theorem snd_infScale (s : ℝ) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

end Helpers

theorem isTorusElt_mat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  intro F E _ _ _ _ _ σ h n J r₀ Xf Yf t _ a ha
  let M : Matrix (Fin n) (Fin n) (AE F E) := ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  let ψ : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have f1 : M.map ψ = 1 :=
    congrArg (fun u : GL (Fin n) (Af F ⊗[F] E) => (u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) (MonoidHom.mem_ker.1 ha.1)
  have f2 : ∀ s : Fin r₀ → ℝ, (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map ψ = 1 :=
    fun s => by
      rw [Matrix.diagonal_map (map_zero _)]
      simp only [ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, snd_infScale, Matrix.diagonal_one]
  have g1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w), M.map (piInf τ) = GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) :=
    fun w τ => rfl
  have g2 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin r₀) E), (incM F Z).map (piInf τ) = Z.map τ.1 :=
    fun w τ Z => Matrix.ext fun i j => piInf_inclR τ (Z i j)
  have g3 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r₀ → ℝ),
      (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map (piInf τ) =
        Matrix.diagonal fun i => (s i : ℂ) := fun w τ s => by
    rw [Matrix.diagonal_map (map_zero _)]
    exact congrArg Matrix.diagonal (funext fun i => piInf_infScale h τ (s i))
  have key : ∀ {P Q : Matrix (Fin n) (Fin r₀) (AE F E)}, P.map ψ = Q.map ψ →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w), P.map (piInf τ) = Q.map (piInf τ)) → P = Q :=
    fun hf hi => Matrix.ext fun i j => ae_ext h (congrFun (congrFun hf i) j) fun w τ => congrFun (congrFun (hi w τ) i) j
  refine ⟨key ?_ fun w τ => ?_, key ?_ fun w τ => ?_, fun z hz hz' => funext fun i => ae_ext h ?_ fun w τ => ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 t, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).1]
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 (fun i => (t i)⁻¹), Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).2.1]
    congr 2
    funext i
    push_cast
    rfl
  · change ψ ((M *ᵥ _) i) = ψ _
    rw [RingHom.map_mulVec, f1, Matrix.one_mulVec]
    rfl
  · change piInf τ ((M *ᵥ _) i) = piInf τ _
    rw [RingHom.map_mulVec, g1]
    have e : (piInf τ ∘ fun i => inclR (F := F) (AF F) (z i)) = fun i => τ.1 (z i) := funext fun i => piInf_inclR τ (z i)
    rw [e, (ha.2 w τ).2.2 z hz hz', piInf_inclR]

end GlobalTheory.TorusMat
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassLow

theorem perm_conj' {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix (Fin r) (Fin r) ℂ) :
    permM e * M * (permM e)ᵀ = M.submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, permM]

theorem det_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) (s : realSU Ψ G) (u : UpqT (p ρ) (q ρ))
    (hu : UpqT.mat u * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) :
    (UpqT.mat u).det = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := MassUp.inv_facts hI ρ
  set S := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  set P := permM (e ρ)
  have hS : S.det = 1 := (s.2 (σ ρ)).1
  set M := (Pᵀ * A ρ) * S * mat x (σ ρ) with hM
  have hx : mat x (σ ρ) * M = S * mat x (σ ρ) := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : UpqT.mat u = P * M * Pᵀ := by
    calc UpqT.mat u = UpqT.mat u * (A ρ * (mat x (σ ρ) * Pᵀ)) := by rw [h3, Matrix.mul_one]
      _ = A ρ * (S * mat x (σ ρ)) * Pᵀ := by
        rw [← Matrix.mul_assoc, hu]; simp only [Matrix.mul_assoc]
      _ = P * M * Pᵀ := by
        rw [← hx, ← Matrix.mul_assoc, (hI ρ).2]
  rw [hu', perm_conj', Matrix.det_submatrix_equiv_self, hM, Matrix.det_mul, Matrix.det_mul, hS, mul_one,
    ← Matrix.det_mul, h1, Matrix.det_one]

theorem arith (f r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) :
    (1 / 16 : ℝ) ^ (f * r ^ 2) * (8 * ε) ^ (f * (r ^ 2 - 1)) ≤ (ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1)) ^ f := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (1 / 16 : ℝ) ^ (r ^ 2) * (8 * ε) ^ (r ^ 2 - 1) ≤ ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) := by
    have hrp : (r : ℝ) ^ (r - 1) ≤ 2 ^ (r ^ 2) := by
      have h1 : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (r : ℝ) ^ (r - 1) ≤ ((2 : ℝ) ^ r) ^ (r - 1) := pow_le_pow_left₀ hr0.le h1 _
        _ = 2 ^ (r * (r - 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h8 : (8 : ℝ) ^ (r ^ 2 - 1) ≤ 8 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    rw [le_div_iff₀ (pow_pos hr0 _), mul_pow]
    have hε' : 0 ≤ ε ^ (r ^ 2 - 1) := pow_nonneg hε.le _
    calc (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2 - 1) * ε ^ (r ^ 2 - 1)) * (r : ℝ) ^ (r - 1)
        ≤ (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) * 2 ^ (r ^ 2) := by gcongr
      _ = ((1 / 16 : ℝ) * 8 * 2) ^ (r ^ 2) * ε ^ (r ^ 2 - 1) := by rw [mul_pow, mul_pow]; ring
      _ = ε ^ (r ^ 2 - 1) := by norm_num
  have e1 : (1 / 16 : ℝ) ^ (f * r ^ 2) = ((1 / 16 : ℝ) ^ (r ^ 2)) ^ f := by rw [← pow_mul, mul_comm f]
  have e2 : (8 * ε) ^ (f * (r ^ 2 - 1)) = ((8 * ε) ^ (r ^ 2 - 1)) ^ f := by rw [← pow_mul, mul_comm f]
  rw [e1, e2, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) key f

theorem massLow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))) (ρ₀ : κ), 1 ≤ r → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S ≤ Measure.pi m (π ⁻¹' S ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m ρ₀ hr hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hΨ : 1 ≤ Ψ.card := by
    rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨ρ₀⟩
  have hG : G.det ≠ 0 := MassUp.det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (MassUp.inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set T : Set (∀ ρ, UpqT (p ρ) (q ρ)) := {b | 0 < (UpqT.mat (b ρ₀)).det.im} with hTdef
  have hTo : IsOpen T := isOpen_lt continuous_const
    (Complex.continuous_im.comp ((GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply ρ₀)).matrix_det))
  have hTm : MeasurableSet T := hTo.measurableSet
  set ν := (μ.restrict T).map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := MassUp.exists_lift E r κ p q Ψ G x σ A e hI s
    have hd : (UpqT.mat (b₀ ρ₀)).det = 1 := det_lift hI ρ₀ s (b₀ ρ₀) (hb₀ ρ₀)
    have hpre : (fun b => b₀ * b) ⁻¹' T = T := by
      ext b
      simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Pi.mul_apply]
      rw [show UpqT.mat (b₀ ρ₀ * b ρ₀) = UpqT.mat (b₀ ρ₀) * UpqT.mat (b ρ₀) from rfl, Matrix.det_mul, hd, one_mul]
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀)]
    congr 1
    calc (μ.restrict T).map (fun b => b₀ * b)
        = (μ.restrict ((fun b => b₀ * b) ⁻¹' T)).map (fun b => b₀ * b) := by rw [hpre]
      _ = (μ.map (fun b => b₀ * b)).restrict T := (Measure.restrict_map (measurable_const_mul b₀) hTm).symm
      _ = μ.restrict T := by rw [map_mul_left_eq_self]
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1

  have hup := MassUp.massUp E r κ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro K hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [hν, Measure.map_apply hπm hKm]
    calc μ.restrict T (π ⁻¹' K) ≤ μ (π ⁻¹' K) := Measure.restrict_le_self _
      _ ≤ _ := hup K hKm
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef

  have hplace := fun ρ => GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εu, hεu, hbu⟩ := GlobalTheory.T.riemannianHaar_frameBall_le E r κ p q Ψ G x σ A e hr hI
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εu / 2 with hεdef
  have hεm : ε < min δ εu := half_lt_self (lt_min hδ hεu)
  have hε : 0 < ε := half_pos (lt_min hδ hεu)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεu' : ε < εu := lt_of_lt_of_le hεm (min_le_right _ _)
  have hopen : IsOpen (frBall Ψ G x ε) := by
    have hc' : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc' τ a b) continuous_const
  set L := ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) with hL
  have hlow : ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := by
    rw [hν, Measure.map_apply hπm hopen.measurableSet, Measure.restrict_apply (hπm hopen.measurableSet),
      MassUp.preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε]
    have hsub : Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | (∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε) ∧
        0 < (UpqT.mat u).det.im}) ⊆ Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) |
          ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) ∩ T := by
      intro b hb
      simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hb
      exact ⟨fun ρ _ => (hb ρ).1, (hb ρ₀).2⟩
    refine le_trans ?_ (measure_mono hsub)
    rw [hμ, Measure.pi_pi]
    calc ENNReal.ofReal (L ^ Ψ.card) = ∏ _ρ : κ, ENNReal.ofReal L := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := Finset.prod_le_prod' fun ρ _ => by
          have := hbp ρ ε hε (hεδ ρ)
          rw [hpq ρ] at this
          exact this
  have hupB := hbu ε hε hεu'
  set U := (8 * ε) ^ (Ψ.card * (r ^ 2 - 1)) with hU
  have hcU : L ^ Ψ.card ≤ (c : ℝ) * U := by
    have h1 : ENNReal.ofReal (L ^ Ψ.card) ≤ ENNReal.ofReal ((c : ℝ) * U) := by
      calc ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := hlow
        _ = (c : ℝ≥0∞) * riemHaar Ψ G x (frBall Ψ G x ε) := by
          conv_lhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal U := mul_le_mul_of_nonneg_left hupB (zero_le)
        _ = ENNReal.ofReal ((c : ℝ) * U) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg _) (by positivity))).1 h1
  have hK := arith Ψ.card r ε hr hε
  have hUpos : 0 < U := by positivity
  have hcK : (1 / 16 : ℝ) ^ (Ψ.card * r ^ 2) ≤ c :=
    le_of_mul_le_mul_right (hK.trans hcU) hUpos
  calc ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S
      ≤ (c : ℝ≥0∞) * riemHaar Ψ G x S := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcK
    _ = ν S := by
        conv_rhs => rw [hc]
        rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    _ = μ (π ⁻¹' S ∩ T) := by
        rw [hν, Measure.map_apply hπm hS, Measure.restrict_apply (hπm hS)]

end GlobalTheory.CovTop.VolUp.MassLow
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | exact GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | (intros; apply GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.automorphic_map_phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  exact @GlobalTheory.BCT.TrKer.Phi_injective
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem span_range_wInf_comp_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  intro E _ _ _ n lam
  exact span_wInf lam

end GlobalTheory.BCT.TrKer
end
end
