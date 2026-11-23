module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  first | exact @GlobalTheory.FrameExt.exists_fr | exact GlobalTheory.FrameExt.exists_fr | (intros; apply GlobalTheory.FrameExt.exists_fr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SvNLinear

theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple

theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.T.schwartz_vanishing_decomposition V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by

    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

open scoped Classical


open GlobalTheory.CharInvForm in
theorem charInv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun f => l (pureA F f g)
        map_add' := fun f f' => by
          rw [← map_add (f := _)]
          congr 1
          funext x
          simp [pureA, add_mul]
        map_smul' := fun s f => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp [pureA, mul_assoc] }
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      show l (pureA F f' g) = l (pureA F f g)
      rw [← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY, mul_assoc])
    exact ⟨α, hα⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add (f := _)]
        congr 1
        funext x
        simp [pureA, mul_add]
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp [pureA, mul_comm, mul_assoc] }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp [pureA, dot_pairA_fin, mul_left_comm])
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add (f := _), h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

theorem eval_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.toBoundedContinuousFunction_apply, smul_eq_mul]
  ring

end GlobalTheory.SvNLinear

namespace GlobalTheory.SvNLinear

open GlobalTheory.AdelicSvN

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ → ∀ (l₁ l₂ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro _ F _ _ ψ hψ κ _ L hL hdim l₁ l₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg

  have hlin : ∀ (a b : ℂ), ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, S (a • φ + b • φ') = a • S φ + b • S φ' := by
    intro a b φ hφ φ' hφ'
    funext x
    obtain ⟨l', _, e⟩ := hSa _ (eval_mem_adm x)
    have hm : a • φ + b • φ' ∈ schA F κ := add_mem (Submodule.smul_mem _ a hφ) (Submodule.smul_mem _ b hφ')
    have e1 := e _ hm
    have e2 := e φ hφ
    have e3 := e φ' hφ'
    simp only [LinearMap.proj_apply] at e1 e2 e3
    rw [← e1, map_add (f := _), map_smul, map_smul, e2, e3]
    rfl
  have key : ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hi
    let f : schA F κ →ₗ[ℂ] ℂ :=
      { toFun := fun φ => l (S φ.1)
        map_add' := fun φ φ' => by
          have := hlin 1 1 φ.1 φ.2 φ'.1 φ'.2
          simp only [one_smul] at this
          simp only [Submodule.coe_add, this, map_add (f := _)]
        map_smul' := fun s φ => by
          have := hlin s 0 φ.1 φ.2 0 (Submodule.zero_mem _)
          simp only [zero_smul, add_zero] at this
          simp only [Submodule.coe_smul, this, map_smul, RingHom.id_apply, smul_eq_mul] }
    obtain ⟨l', hl'⟩ := LinearMap.exists_extend f
    have e : ∀ φ (hφ : φ ∈ schA F κ), l' φ = l (S φ) := fun φ hφ => LinearMap.congr_fun hl' ⟨φ, hφ⟩
    obtain ⟨c, hc⟩ := charInv F ψ hψ κ l' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp

end GlobalTheory.SvNLinear
end
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KInfComm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
  have hB := hP.base
  have hw := hP.weil
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hk1 : k ∈ UAt σ W (evI F) := hk.1
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw ((1 : UA σ X.J)⁻¹, k⁻¹)
    (GlobalTheory.RealConjFac.inv_mem_UAt h1) (GlobalTheory.RealConjFac.inv_mem_UAt hk1)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (A f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hA f) (hT₂ (A f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (A f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, A (T₂ f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hT₂ f) (hA (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (A (T₂ f)) f).2.2.2.1 _ hc (hid f))
  let T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d) :=
    LinearEquiv.ofLinear A T₂ (LinearMap.ext e12) (LinearMap.ext e21)
  set u := M.co.e.symm (fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (a i), fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (b i)) with hu_def
  have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm M a b
  set u' := mat (1 : UA σ X.J) * u * (mat k).transpose with hu'_def
  have hu' : At (evI F) u' := by
    intro c hc
    rw [hu'_def, ← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').1, GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').2, fun f => ?_⟩
  have hf : ActsD (evI F) (M.heisLine B.ψ u) f (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) := by
    refine (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u hu _ _).2 ?_
    rw [hu_def, LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]
  have ht := GlobalTheory.HeisTransport.actsD_heisLine_transport F E σ B n d X W M χX χW om r s r' s' hB hP.herm hP.skew hP.good hw
    1 h1 k hk1 T (fun f => hA f) (fun f => hT₂ f) u hu f _ hf
  exact (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u' hu' _ _).1 ht

end GlobalTheory.KInfComm

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.theta_pair_local_schwartz_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  first | exact @GlobalTheory.IntertwLocal.local_intertw | exact GlobalTheory.IntertwLocal.local_intertw | (intros; apply GlobalTheory.IntertwLocal.local_intertw <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @GlobalTheory.ArchDecay.om_bound_arch | exact GlobalTheory.ArchDecay.om_bound_arch | (intros; apply GlobalTheory.ArchDecay.om_bound_arch <;> assumption)
end

section

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift
open scoped Classical

namespace GlobalTheory.FlagTan

theorem det_eq_prod_diag_of_height {m R : Type} [Fintype m] [DecidableEq m] [CommRing R] (P : Matrix m m R)
    (b : m → ℤ) (h : ∀ k j, P k j ≠ 0 → k = j ∨ b j < b k) : P.det = ∏ k, P k k := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    suffices ∏ i, P (σ i) i = 0 by rw [this, smul_zero]
    by_contra hne
    have h1 : ∀ i, P (σ i) i ≠ 0 := fun i hi => hne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hc
      exact hσ (Equiv.ext fun i => by_contra fun k => hc ⟨i, k⟩)
    have := Finset.sum_lt_sum (s := Finset.univ) (f := b) (g := fun i => b (σ i))
      (fun j _ => (h _ _ (h1 j)).elim (fun e => by rw [e]) le_of_lt)
      ⟨i, Finset.mem_univ _, (h _ _ (h1 i)).resolve_left hi⟩
    rw [Equiv.sum_comp σ b] at this
    exact lt_irrefl _ this
  · simp

theorem prod_pairs_lt {G : Type} [CommGroup G] {n : ℕ} (x : Fin n → G) :
    ∏ q : {q : Fin n × Fin n // q.1 < q.2}, ((x q.1.1)⁻¹ * x q.1.2) =
      ∏ i, x i ^ (((Finset.Iio i).card : ℤ) - (Finset.Ioi i).card) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2) (by simp)
    (fun q => (x q.1)⁻¹ * x q.2), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.prod_filter, ← Finset.prod_filter, Finset.prod_const, Finset.prod_const, zpow_sub, mul_comm]
  simp only [zpow_natCast, inv_pow, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsHalf.prod_univ {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommMonoid G] (g : (E →+* ℂ) → G) :
    ∏ σ, g σ = ∏ τ ∈ Φ, (g τ * g (conjEmb τ)) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Φ]
  congr 1
  refine Finset.prod_bij' (fun σ _ => conjEmb σ) (fun σ _ => conjEmb σ) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => _root_.GlobalTheory.AllWt.conjEmb_conjEmb σ) (fun σ _ => _root_.GlobalTheory.AllWt.conjEmb_conjEmb σ) fun σ _ => by rw [_root_.GlobalTheory.AllWt.conjEmb_conjEmb]
  · rw [h, _root_.GlobalTheory.AllWt.conjEmb_conjEmb]; exact Finset.mem_compl.1 hσ
  · exact Finset.mem_compl.2 ((h σ).1 hσ)

theorem prod_char_eq {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    (∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩))) *
      ∏ k : VIx Dw, ((t (some ⟨k.1, k.2.1.1⟩))⁻¹ * t (some ⟨k.1, k.2.1.2⟩)) = ∏ k, t k ^ detTanEx Dw k := by
  have e1 : ∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩)) =
      ∏ σ, ∏ i, t (some ⟨σ, i⟩) ^ Dw.mult (conjEmb σ) := by
    rw [h.prod_univ, Fintype.prod_sigma, ← Finset.prod_coe_sort Φ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type, _root_.GlobalTheory.AllWt.conjEmb_conjEmb]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
    exact mul_comm _ _
  rw [e1, Fintype.prod_sigma, Fintype.prod_option, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  simp only [detTanEx, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [prod_pairs_lt fun i => t (some ⟨σ, i⟩), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_add, zpow_natCast, mul_comm]

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

theorem exists_move {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') {v' : FrPt Xo c (DualNumber K)} (hv : IsDef y' v') :
    ∃ w, IsDef y w ∧ FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v' := by
  obtain ⟨g', a', hg', h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ v' (fun τ => (g' τ).map (cst c K))
    (Units.map (cst c K).toRingHom.toMonoidHom a') fun τ => by
      have := (hg' τ).map (cst c K).toRingHom
      rwa [RingHom.map_det] at this
  refine ⟨w, (frMap_iff_frChg hw hv).2 ?_, (D.1 _ _ _ _ _ _ _ hw).2 ?_⟩
  · convert h' using 2 with τ
    · ext i j; simp
    · rfl
  · convert D.2.1 v' using 2 with τ
    · rw [← Matrix.map_mul, congrFun e τ, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact (map_mul (cst c K) a a').symm.trans (by rw [e', map_one])

theorem isVert_move {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : Kˣ}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') (hg : ∀ τ, g τ * g' τ = 1) {N : FIx Dw → K}
    {w v' : FrPt Xo c (DualNumber K)} (hv : IsVert y' N v')
    (hw : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v') :
    IsVert y (fun k => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) w := by
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨y₀', h₀', hs⟩ := hv
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  have k1 := (D.1 _ _ _ _ _ _ _ ((frMap_iff_frChg h h₀).1 h₀')).1 hs
  obtain ⟨w', hw', -⟩ := existsUnique_isShift (fun k : FIx Dw => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) y₀
  have k2 : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w' v' := by
    refine (D.1 _ _ _ _ _ _ _ hw').2 ?_
    convert (preTransparency := .reducible) k1 using 1
    · funext τ
      have : g τ * (g' τ * (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ) =
          (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]
      ext i j
      · simp [unip, Matrix.mul_apply, fst_sum, Matrix.one_apply]
      · have := congrFun (congrFun this i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at this
        simpa [unip, Matrix.mul_apply (M := Matrix.map _ _), Matrix.mul_apply (N := Matrix.map _ _), snd_sum] using this
    · ext <;> simp [unip₀, mul_comm]
  obtain ⟨G, A, -, k3⟩ := (frChg_exists_unique E H Dw l Xo c _ v' w).1 hw.1.symm
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c _ w w).2 _ _ _ _ ((D.1 _ _ _ _ _ _ _ hw).1 k3) (D.2.1 w)
  have k4 := (D.1 _ _ _ _ _ _ _ k2).1 k3
  rw [e, e'] at k4
  obtain rfl : w = w' :=
    (existsUnique_frChg E H Dw l Xo c _ w' (fun _ => 1) 1 fun _ => by simp).unique k4 (D.2.1 w')
  exact ⟨y₀, h₀, hw'⟩

end GlobalTheory.FlagTan
end
end
