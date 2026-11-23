module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle114
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
public import Mathlib.RingTheory.Norm.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dite_eq_left s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.LinDesc

theorem exists_leftMul_of_comm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
    (hG : A.IsGen τ p) (M : Matrix (Fin r) (Fin r) F) (hM : M * companion p = companion p * M) :
    ∃ k : A.K, M = Algebra.leftMulMatrix (bas A hG) k := by
  set b := bas A hG
  set φ : A.K →ₗ[F] A.K := Matrix.toLin b b M with hφ
  have hMφ : LinearMap.toMatrix b b φ = M := by simp [hφ]
  have hlm : ∀ x : A.K, Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (Algebra.lmul F A.K x) := fun x => rfl
  have hτ : φ ∘ₗ Algebra.lmul F A.K τ = Algebra.lmul F A.K τ ∘ₗ φ := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hMφ, ← hlm, leftMul_tau]
    exact hM
  have hτx : ∀ x, φ (τ * x) = τ * φ x := fun x => by
    have := congrArg (fun f => f x) hτ
    simpa using this
  have hpow : ∀ (n : ℕ) x, φ (τ ^ n * x) = τ ^ n * φ x := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', mul_assoc, hτx, ih, ← mul_assoc]
  have hall : ∀ k x, φ (k * x) = k * φ x := by
    intro k x

    rw [← b.sum_repr k, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_mul_assoc, bas_apply, hpow]
  refine ⟨φ 1, ?_⟩
  rw [← hMφ, hlm]
  congr 1
  ext x
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [mul_comm, ← hall, mul_one]

theorem centr : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  intro F E _ _ _ _ A r τ p hG t ht
  have ht' : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p =
      companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
    have h1 : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (t : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p
        = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p *
            ((t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * ((t : Matrix (Fin r) (Fin r) F) * companion p) *
            ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [ht]; simp only [Matrix.mul_assoc]
      _ = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨k, hk⟩ := exists_leftMul_of_comm A hG _ ht
  obtain ⟨k', hk'⟩ := exists_leftMul_of_comm A hG _ ht'
  have hinj := Algebra.leftMulMatrix_injective (bas A hG)
  have e1 : k * k' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hk, ← hk', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : k' * k = 1 := by rw [mul_comm, e1]
  refine ⟨⟨k, k', e1, e2⟩, ?_⟩
  apply Units.ext
  rw [tm_coe]
  exact hk.symm

end GlobalTheory.JR.LinDesc
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem integral_comp_unit_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) [ν.IsAddHaarMeasure]
    (s : A.Kˣ) (g : A.K → ℂ) :
    ∫ b, g ((s : A.K) * b) ∂ν = ((A.absK (s : A.K) : ℂ))⁻¹ * ∫ b, g b ∂ν := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology A.K := by
    let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
    have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
    exact h.isEmbedding.secondCountableTopology
  have hme : MeasurableEmbedding (fun b : A.K => s • b) := (Homeomorph.smul s).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul ν s⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν) := by
    rw [hme.integral_map]; rfl
  have habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    congr 2
    ext; rfl
  rw [hint, hmap, integral_smul_measure, habs]
  simp [Complex.real_smul]

theorem pt_scale_eq_rg_mS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν hν ψ x s Φ
  funext p
  obtain ⟨a, u⟩ := p
  have hs0 : A.absK (s : A.K) ≠ 0 := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    exact_mod_cast (distribHaarChar_pos).ne'
  have key := integral_comp_unit_mul A ν s
    (fun b' => Φ (a * (s : A.K), b') * A.psiK ψ (x * b' * (u * ((s⁻¹ : A.Kˣ) : A.K))))
  simp only [pt, rg, mS, fourB, kx]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, mul_zero, add_zero, zero_add]
  rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hs0)] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e1 : x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u := by
    rw [show x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u * ((s : A.K) * ((s⁻¹ : A.Kˣ) : A.K)) by ring,
      Units.mul_inv, mul_one]
  simp only [e1, mul_comm a (s : A.K)]
  ring

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_E_L [Unram F E] (A : Et F E) : Module.Finite E A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have h := A.push.out
  exact Module.Finite.equiv h.equiv

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have := finite_E_L A
  exact Module.Finite.trans E A.L

theorem finite_K_L [Unram F E] (A : Et F E) : Module.Finite A.K A.L := by
  have := finite_F_L A
  exact Module.Finite.of_restrictScalars_finite F A.K A.L

theorem continuous_NL [Unram F E] (A : Et F E) (hK : IsField A.K) :
    Continuous (fun y : A.L => A.NL y) := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  let b := Module.Free.chooseBasis A.K A.L
  have hfun : (fun y : A.L => A.NL y) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hfun]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  let φ : A.L →ₗ[A.K] A.K := (LinearMap.proj j : (_ → A.K) →ₗ[A.K] A.K) ∘ₗ
    (LinearMap.proj i : (_ → _ → A.K) →ₗ[A.K] _) ∘ₗ (Algebra.leftMulMatrix b).toLinearMap
  have hφ : Continuous (φ.restrictScalars F) := IsModuleTopology.continuous_of_linearMap _
  exact hφ

theorem NL_zero [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) : A.NL (0 : A.L) = 0 := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  exact Algebra.norm_zero

end GlobalTheory.JR.WeilQuad.NearZero

theorem GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  let g : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y)
  have hg : Continuous g := by
    have ht : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
    exact ht.comp (continuous_const.mul (NearZero.continuous_NL A hK))
  have hg0 : g 0 = 0 := by simp [g, NearZero.NL_zero A hK hL]
  have hmem : g ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : A.L) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact Metric.ball_mem_nhds 0 one_pos)
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖g y‖ < 1 := by simpa using hy
  exact hψ.1 _ hy'.le
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Hyp

theorem pt_pt_eq_reflect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  intro F E _ _ _ _ _ A ψ x ν hsd Φ hΦ

  haveI : T2Space A.K := by
    let e := (Module.finBasis F A.K).equivFun
    have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    first
      | exact T2Space.of_continuous_injective e.injective he
      | exact T2Space.of_injective_continuous e.injective he
      | exact e.injective.t2Space he
  funext p
  have hemb : Topology.IsClosedEmbedding (Prod.mk p.1 : A.K → A.K × A.K) := by
    refine ⟨isEmbedding_prodMkRight p.1, ?_⟩
    have : Set.range (Prod.mk p.1 : A.K → A.K × A.K) = ({p.1} : Set A.K) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      simp only [Set.mem_range, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      constructor
      · rintro ⟨y, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨b, rfl, rfl⟩
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  have hf : IsTest (fun b => Φ (p.1, b)) :=
    ⟨hΦ.1.comp_continuous hemb.continuous, hΦ.2.comp_isClosedEmbedding hemb⟩
  exact hsd.2 _ hf p.2

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem NL_smul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (s : A.K) (y : A.L) :
    A.NL (s • y) = s ^ 2 * A.NL y := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hU.finrank_eq
  have hp := ((Algebra.IsPushout.comm F E A.K A.L).1 A.push).out
  let c := hp.basis b
  unfold Et.NL
  rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap_of_basis c, Fintype.card_fin]

theorem mOp_nOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ),
      mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω _ s z φ
  funext y
  simp only [mOp, nOp, NL_smul]
  rw [show (z * (x : A.K) * ((s : A.K) ^ 2 * A.NL y)) = (s : A.K) ^ 2 * z * x * A.NL y by ring]
  ring

end GlobalTheory.JR.WeilQuad
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem wHyp_wS_eq_fourB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  intro F E _ _ _ _ _ A ψ x e ν μ hpt hinv hrg hcc hci hker hlc hint φ hφ y
  set p := ci A e y with hp
  have hy : y = cc A e p := (hci y).symm
  have hG : IsTest (rg A (wS A.K) (pt A ν ψ x (fun q => φ (cc A e q)))) := hrg _ (hpt _ (hcc φ hφ))
  have hh : IsTest (fun y' => φ y' * A.kerL ψ x y' (cc A e p)) :=
    ⟨hφ.1.mul (hlc _), hφ.2.mul_right⟩
  unfold wHyp
  rw [hinv _ hG]
  rw [← hp]
  conv_rhs => rw [hy]
  unfold fourB
  rw [hint _ hh]
  simp only [pt, fourB, rg, wS, hker]
  simp
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  ring

end GlobalTheory.JR.Hyp
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem isTest_coord : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩

end GlobalTheory.JR.Hyp
end

section

open NumberField Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V), Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) → ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite <;> assumption)
end
