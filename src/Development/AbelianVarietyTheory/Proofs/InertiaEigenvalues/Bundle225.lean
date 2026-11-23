module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle209
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtale
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle210
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle211
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.CharCancel

section Cancel

variable {K Γ V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem ennreal_volume_ratio_step_cancel (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2))
    (v₀ : V) (hv : ∀ g, a g v₀ = c g • v₀) (hd : (e (v₀, 1)).2 ≠ 0) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  rcases hE : e (v₀, 1) with ⟨w', δ⟩
  have hd0 : δ ≠ 0 := by rw [hE] at hd; exact hd
  have hb : ∀ g, b g w' = c g • w' := by
    intro g
    have h1 := h g v₀ 1
    have h2 : ((a g v₀, c g * 1) : V × K) = c g • ((v₀, 1) : V × K) := by
      rw [hv]; simp
    rw [h2, map_smul, hE] at h1
    have h3 := congrArg Prod.fst h1
    simp at h3
    exact h3.symm
  refine ⟨{ toFun := fun v => (e (v, 0)).1 - ((e (v, 0)).2 / δ) • w'
            invFun := fun w => (e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀
            map_add' := ?_, map_smul' := ?_, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro x y
    have hxy : ((x + y, (0 : K)) : V × K) = (x, 0) + (y, 0) := by simp
    rw [hxy, map_add (f := _)]
    simp only [Prod.fst_add, Prod.snd_add, add_div, add_smul]
    abel
  · intro s x
    have hsx : ((s • x, (0 : K)) : V × K) = s • (x, 0) := by simp
    rw [hsx, map_smul]
    simp [smul_sub, smul_smul, mul_div_assoc]
  · intro v
    dsimp only
    have key : (((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w', (0 : K)) : W × K) =
        e (v, 0) - ((e (v, 0)).2 / δ) • e (v₀, 1) := by
      rw [hE]
      ext
      · simp
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_cancel₀ _ hd0, sub_self]
    rw [key, map_sub, map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    simp
  · intro w
    dsimp only
    have key : (((e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀, (0 : K)) : V × K) =
        e.symm (w, 0) - (e.symm (w, 0)).2 • (v₀, 1) := by
      ext <;> simp
    rw [key, map_sub, map_smul, LinearEquiv.apply_symm_apply, hE]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, zero_sub]
    rw [neg_div, mul_div_cancel_right₀ _ hd0, neg_smul, sub_neg_eq_add, sub_add_cancel]
  · intro g v
    show (e (a g v, 0)).1 - ((e (a g v, 0)).2 / δ) • w' = b g ((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w')
    have h1 := h g v 0
    rw [mul_zero] at h1
    rw [h1, map_sub, map_smul, hb, smul_smul]
    dsimp only
    rw [show c g * (e (v, 0)).2 / δ = (e (v, 0)).2 / δ * c g by ring]

theorem cancel_one (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2)) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  by_cases hd : (e ((0 : V), (1 : K))).2 = 0
  · rcases hq : e.symm ((0 : W), (1 : K)) with ⟨v₁, d'⟩
    have hq' : e (v₁, d') = ((0 : W), (1 : K)) := by rw [← hq]; simp
    have hv1 : ∀ g, a g v₁ = c g • v₁ := by
      intro g
      have h1 := h g v₁ d'
      rw [hq'] at h1
      simp only [map_zero, mul_one] at h1
      have h2 : e (c g • v₁, c g * d') = ((0 : W), c g) := by
        have h3 : ((c g • v₁, c g * d') : V × K) = c g • (v₁, d') := by simp
        rw [h3, map_smul, hq']; simp
      have h4 := e.injective (h1.trans h2.symm)
      simpa using congrArg Prod.fst h4
    have hd1 : (e (v₁, 1)).2 ≠ 0 := by
      have h5 : ((v₁, 1) : V × K) = (v₁, d') + (1 - d') • ((0 : V), (1 : K)) := by ext <;> simp
      rw [h5, map_add (f := _), map_smul, hq']
      simp [hd]
    exact ennreal_volume_ratio_step_cancel a b c e h v₁ hv1 hd1
  · exact ennreal_volume_ratio_step_cancel a b c e h 0 (fun g => by simp) hd

def splitFirst (V : Type) [AddCommGroup V] [Module K V] (t : ℕ) :
    ((V × (Fin t → K)) × K) ≃ₗ[K] (V × (Fin (t + 1) → K)) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  invFun q := ((q.1, fun j => q.2 j.succ), q.2 0)
  map_add' p q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  map_smul' x p := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  left_inv p := by simp
  right_inv q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cancel_fin (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (t : ℕ) :
    ∀ (c : Fin t → Γ → K) (e : (V × (Fin t → K)) ≃ₗ[K] (W × (Fin t → K))),
    (∀ g v x, e (a g v, fun j => c j g * x j) = (b g (e (v, x)).1, fun j => c j g * (e (v, x)).2 j)) →
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  induction t with
  | zero =>
    intro c e h
    refine ⟨((LinearEquiv.prodUnique : (V × (Fin 0 → K)) ≃ₗ[K] V).symm.trans e).trans
      (LinearEquiv.prodUnique : (W × (Fin 0 → K)) ≃ₗ[K] W), fun g v => ?_⟩
    have hx : ((a g v, fun j => c j g * (default : Fin 0 → K) j) : V × (Fin 0 → K)) = (a g v, default) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    have h1 := h g v default
    rw [hx] at h1
    show (e (a g v, default)).1 = b g (e (v, default)).1
    rw [h1]
  | succ t ih =>
    intro c e h
    let S := splitFirst (K := K) V t
    let T := splitFirst (K := K) W t
    let a' : Γ → (V × (Fin t → K)) →ₗ[K] (V × (Fin t → K)) := fun g =>
      (a g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    let b' : Γ → (W × (Fin t → K)) →ₗ[K] (W × (Fin t → K)) := fun g =>
      (b g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    refine (cancel_one a' b' (c 0) ((S.trans e).trans T.symm) ?_).elim fun f' hf' => ?_
    · intro g p y
      obtain ⟨v, x⟩ := p
      have hS : ∀ (u : V) (z : Fin t → K) (s : K), S ((u, z), s) = (u, Fin.cons s z) := fun _ _ _ => rfl
      have hT : ∀ q : W × (Fin (t + 1) → K), T.symm q = ((q.1, fun j => q.2 j.succ), q.2 0) := fun _ => rfl
      have ha : a' g (v, x) = (a g v, fun j => c j.succ g * x j) := rfl
      have hcons : (Fin.cons (c 0 g * y) (fun j => c j.succ g * x j) : Fin (t + 1) → K) =
          fun j => c j g * (Fin.cons y x : Fin (t + 1) → K) j := by
        funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
      simp only [LinearEquiv.trans_apply]
      rw [ha, hS, hS, hcons, h g v (Fin.cons y x : Fin (t + 1) → K), hT, hT]
      rfl
    · exact ih (fun j => c j.succ) f' (fun g v x => hf' g (v, x))

end Cancel

theorem overK_apply {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {k : ℕ}
    (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := by
  simp [overK, mat, toFr, matRep, mapM]

theorem conj_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ σ' : Γ →* GL (Fin n) A) (ρ ρ' : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hP : ∃ Pm : GL (Fin n) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin n) (Fin n) (FractionRing A)) * (mat σ g).map (toFr A) =
        (mat σ' g).map (toFr A) * (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
    (h : ∃ e, IsDecomp (t := t) σ ρ χ e) (h' : ∃ e, IsDecomp (t := t) σ' ρ' χ e) :
    ∃ Pm : GL (Fin r) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) * (mat ρ g).map (toFr A) =
        (mat ρ' g).map (toFr A) * (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) := by
  obtain ⟨Pm, hPm⟩ := hP
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  let L : (Fin n → FractionRing A) ≃ₗ[FractionRing A] (Fin n → FractionRing A) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
      (Matrix.toLin' ((Pm⁻¹ : GL (Fin n) (FractionRing A)) : Matrix (Fin n) (Fin n) (FractionRing A)))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
  have hL : ∀ g u, L (overK σ g u) = overK σ' g (L u) := by
    intro g u
    simp only [L, LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, overK_apply, Matrix.mulVec_mulVec, hPm g]
  refine (cancel_fin (fun g => overK ρ g) (fun g => overK ρ' g) t
    (fun j g => toFr A ((χ (↑j + 1) g : Aˣ) : A)) ((e.symm.trans L).trans e') ?_).elim fun f hf => ?_
  · intro g v x
    have he1 := he g (e.symm (v, x))
    simp only [LinearEquiv.apply_symm_apply] at he1
    have h2 : e.symm (overK ρ g v, fun j => toFr A ((χ (↑j + 1) g : Aˣ) : A) * x j) = overK σ g (e.symm (v, x)) := by
      rw [← he1, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h2, hL, he']
  · refine ⟨⟨LinearMap.toMatrix' (f : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)),
      LinearMap.toMatrix' (f.symm : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)), ?_, ?_⟩,
      fun g => ?_⟩
    · rw [← LinearMap.toMatrix'_comp]; simp
    · rw [← LinearMap.toMatrix'_comp]; simp
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
        Matrix.toLin'_apply, ← overK_apply, LinearEquiv.coe_coe]
      exact hf g v

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  intro R H what₂ N i r r' ρ ρ' π _ hP h h'
  exact conj_of_isDecomp (r π) (r' π) (ρ π) (ρ' π) (N.chi i) hP h h'

end GlobalTheory.CharCancel
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
  first | exact @GlobalTheory.WhitCollapse.collapse | exact GlobalTheory.WhitCollapse.collapse | (intros; apply GlobalTheory.WhitCollapse.collapse <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  first | exact @GlobalTheory.JR.selfDual_pi_trace | exact GlobalTheory.JR.selfDual_pi_trace | (intros; apply GlobalTheory.JR.selfDual_pi_trace <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  first | exact @GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | exact GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | (intros; apply GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  first | exact @GlobalTheory.JR.gammaOne_holds | exact GlobalTheory.JR.gammaOne_holds | (intros; apply GlobalTheory.JR.gammaOne_holds <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  first | exact @GlobalTheory.JR.UnramInt.main | exact GlobalTheory.JR.UnramInt.main | (intros; apply GlobalTheory.JR.UnramInt.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  first | exact @GlobalTheory.LatVol.main | exact GlobalTheory.LatVol.main | (intros; apply GlobalTheory.LatVol.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  first | exact @GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | exact GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | (intros; apply GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l), ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  first | exact @GlobalTheory.PSer.map_pw_eq_pw | exact GlobalTheory.PSer.map_pw_eq_pw | (intros; apply GlobalTheory.PSer.map_pw_eq_pw <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltFrobeniusIntegerPower_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  first | exact @GlobalTheory.PSer.PwLaws.pw_laws | exact GlobalTheory.PSer.PwLaws.pw_laws | (intros; apply GlobalTheory.PSer.PwLaws.pw_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem commutator_mem_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hdet σ hσ τ hτ
  by_contra hc
  have hcA : σ * τ * σ⁻¹ * τ⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) (A.inv_mem hτ)
  obtain ⟨x, a, hx, hnd⟩ := hdet _ hcA hc
  have hadd := GlobalTheory.PMon.Ram.coboundary_int_additive_mod K L p E r A x a hp hE hord hx
  have h1 : (p : ℤ) ^ r ∣ a 1 := by
    have := hadd 1 A.one_mem 1 A.one_mem
    simp only [mul_one] at this
    have h' : a 1 = -(a 1 - a 1 - a 1) := by ring
    rw [h']; exact this.neg_right
  have hinv : ∀ g ∈ A, (p : ℤ) ^ r ∣ a g⁻¹ + a g := by
    intro g hg
    have := hadd g⁻¹ (A.inv_mem hg) g hg
    rw [inv_mul_cancel] at this
    have h' : a g⁻¹ + a g = a 1 - (a 1 - a g⁻¹ - a g) := by ring
    rw [h']; exact dvd_sub h1 this
  have e1 := hadd (σ * τ * σ⁻¹) (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) τ⁻¹ (A.inv_mem hτ)
  have e2 := hadd (σ * τ) (A.mul_mem hσ hτ) σ⁻¹ (A.inv_mem hσ)
  have e3 := hadd σ hσ τ hτ
  have e4 := hinv σ hσ
  have e5 := hinv τ hτ
  apply hnd
  have h' : a (σ * τ * σ⁻¹ * τ⁻¹) =
      (a (σ * τ * σ⁻¹ * τ⁻¹) - a (σ * τ * σ⁻¹) - a τ⁻¹) + (a (σ * τ * σ⁻¹) - a (σ * τ) - a σ⁻¹)
        + (a (σ * τ) - a σ - a τ) + (a σ⁻¹ + a σ) + (a τ⁻¹ + a τ) := by ring
  rw [h']
  exact dvd_add (dvd_add (dvd_add (dvd_add e1 e2) e3) e4) e5

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.integer_coboundary_additive_mod_prime_pow : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A : Subgroup (L ≃ₐ[K] L)) (x : L) (a : (L ≃ₐ[K] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → ∀ σ ∈ A, ∀ τ ∈ A, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := by
  first | exact @GlobalTheory.PMon.Ram.coboundary_int_additive_mod | exact GlobalTheory.PMon.Ram.coboundary_int_additive_mod | (intros; apply GlobalTheory.PMon.Ram.coboundary_int_additive_mod <;> assumption)
end
