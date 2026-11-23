module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiFixAlt
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Lean.Meta.ExprDefEq

@[expose] public section

section

open UpperTheory.V.Z.Kato.Joint
open Formalism.ConjugateSelfDual GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

variable {l : ℕ} [Fact l.Prime]

private theorem norm_zl (c : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

private theorem nadd {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem nmul {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ r) : ‖x * y‖ ≤ r := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

private theorem nappr (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - algebraMap ℤ_[l] (Qbar l) c‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hz
  simp only [map_mul, map_pow, map_natCast, map_sub] at h
  rw [norm_sub_rev, ← h]
  exact nmul (by rw [norm_zl]; exact z.norm_le_one) le_rfl

private theorem extend {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (r : ℝ) (f : M → ℕ → Qbar l)
    (hf : ∀ b ∈ B, ∀ b' ∈ B, ∀ c c' : ℤ_[l], ∀ i,
      ‖f (c • b + c' • b') i - (algebraMap ℤ_[l] (Qbar l) c * f b i + algebraMap ℤ_[l] (Qbar l) c' * f b' i)‖ ≤ r) :
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] M) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ B, ∀ i, ‖Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i - f b i‖ ≤ r := by
  classical
  let e := Module.Free.chooseBasis ℤ_[l] B
  let g : B →ₗ[ℤ_[l]] (ℕ → Qbar l) := e.constr ℤ_[l] (fun k => f (e k))
  have h0 : ∀ i, ‖f 0 i‖ ≤ r := fun i => by simpa using hf 0 B.zero_mem 0 B.zero_mem 0 0 i
  have hr : 0 ≤ r := (norm_nonneg _).trans (h0 0)
  have hg : ∀ b : B, ∀ i, ‖g b i - f b i‖ ≤ r := by
    intro b i
    have hb : b ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa [g] using hr
    | zero => simpa using h0 i
    | add x y _ _ hx hy =>
      have h := hf x x.2 y y.2 1 1 i
      simp only [one_smul, map_one, one_mul] at h
      rw [← norm_neg] at h
      have := nadd (nadd hx hy) h
      convert this using 2
      simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add]
      ring
    | smul c x _ hx =>
      have h := hf x x.2 0 B.zero_mem c 0 i
      simp only [zero_smul, add_zero, map_zero, zero_mul] at h
      rw [← norm_neg] at h
      have := nadd (nmul (x := algebraMap ℤ_[l] (Qbar l) c) (by rw [norm_zl]; exact c.norm_le_one) hx) h
      convert this using 2
      simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def]
      ring
  haveI : Module.IsTorsionFree ℤ_[l] (Qbar l) := by
    refine (Module.isTorsionFree_iff_algebraMap_injective).2 ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have := norm_zl a
    rw [ha, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  haveI : Module.Flat ℤ_[l] (Qbar l) := inferInstance
  have hinj : Function.Injective (B.subtype.baseChange (Qbar l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Qbar l) B.subtype B.injective_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange (Qbar l))
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(g.liftBaseChange (Qbar l)) ∘ₗ s, fun b hb i => ?_⟩
  have h1 : s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B) :=
    LinearMap.congr_fun hs ((1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B))
  simpa [h1] using hg ⟨b, hb⟩ i

private theorem sgD_one_mem {N : ℕ} (hN : N ≠ 0) : sgD N l 1 ∈ Gam N l := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (l := l) (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  refine ⟨?_, h1⟩
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)

private theorem act_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gam N l) {b : X.Fn l} (hb : b ∈ X.B N l w) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

open UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt in
theorem UpperTheory.V.Z.Kato.Joint.thLin :
    UpperTheory.V.Z.Kato.Joint.ThLin := by
  intro l _ Ω _ _ _ ε X A N w j hS n
  obtain ⟨hA, h2, hlN, h5, hw, hj⟩ := hS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN).symm
  have hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩
  haveI := (GlobalTheory.T.kummerBettiModule_free_finite ε X ε.injective hhol N l w h2 h5 hcop hw).1
  have hth : ∀ b ∈ X.B N l w, IsThB X A N l n b (thN X A N l n 1 b) := by
    intro b hb
    have h := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol h2 hlN h5 hA n w 1 hw (Nat.coprime_one_left N) b hb).1
    rwa [act_fix X (sgD_one_mem (by omega)) hb] at h
  have hint : ∀ b ∈ X.B N l w, ∀ i, ‖th X A N j n b i‖ ≤ 1 := by
    intro b hb i
    obtain ⟨f, -, -, -, h, -⟩ := hth b hb
    exact hj _ (h _)
  refine extend (X.B N l w) ‖((l : ℕ) : Qbar l) ^ n‖ (th X A N j n) ?_
  intro b hb b' hb' c c' i
  have hm : c • b + c' • b' ∈ X.B N l w := add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hb')
  obtain ⟨z, hz, h⟩ := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol h2 hlN h5 hA n w hw _ hm _ _ (hth _ hm)
    (GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w b b' hb hb' c c' _ _ (hth b hb) (hth b' hb')) ((i : ℚ) / ((1 : ℕ) : ℚ))
  have h1 := congrArg j h
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_sub, map_add (f := _), map_mul, map_pow,
    map_natCast] at h1
  have h3 : ‖j z * ((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := nmul (hj z hz) le_rfl
  have := nadd (nadd h3 (nmul (hint b hb i) (nappr n c))) (nmul (hint b' hb' i) (nappr n c'))
  convert this using 2
  simp only [th, seqN]
  linear_combination h1
end

section

open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem cg_mul_left {l : ℕ} [Fact l.Prime] {n : ℕ} {a b a' b' : Qbar l} (x : Qbar l) (hx : ‖x‖ ≤ 1)
    (h : Cg n a b) (ha : a' = x * a) (hb : b' = x * b) : Cg n a' b' := by
  unfold Cg at h ⊢
  rw [ha, hb, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans h

theorem UpperTheory.V.Z.Kato.Joint.explSmul :
    UpperTheory.V.Z.Kato.Joint.ExplSmul := by
  intro l _ Ω _ _ ι e A c Z j s u w α B cc n β t m ⟨κ, v, m₀, c₀, hκ, hv, ζ, hζ, H⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) l
  have hx : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨(l : Qbar l) ^ m * κ, v, m₀, c₀, mul_ne_zero (pow_ne_zero _ hl0) hκ, hv, ζ, hζ, fun k hk => ?_⟩
  obtain ⟨I, inst, P, o, ⟨p1, p2, p3, p4, q1, q2, q3, q4, q5⟩, hc⟩ := H k hk
  refine ⟨I, inst, P, fun i => (l : Qbar l) ^ m * o i,
    ⟨p1, p2, fun i => c.O.mul_mem (c.O.pow_mem (natCast_mem c.O l) m) (p3 i), p4, q1, q2, q3, fun i => ?_,
      fun s hs h1 h2 => ?_⟩, fun ψ hψ => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) (q4 i)
  · obtain ⟨kk, a1, a2⟩ := q5 s hs h1 h2
    refine ⟨kk, a1, cg_mul_left _ hx a2 rfl ?_⟩
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  · refine cg_mul_left _ hx (hc ψ hψ) ?_ ?_
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold htv
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    · beta_reduce
      split_ifs
      · ring
      · rw [mul_zero]
end

section

open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]
end

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients Ω ε
  exact ⟨T⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def LamEig2 : Prop := ThLin → ThOp → ChiStab → ThP →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (ev : Letter → Qbar l), Std A N w j →
    (∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ev T‖ ≤ (l : ℝ) ^ k) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    (∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ X.B N l w,
      FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b) =
        ev T • FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) →
    ∀ lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam₀ →
    (∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P a)) →
    ∃ c₂ : ℕ, ∀ n, c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      Cg (n - c₂) (lam (th X A N j n (X.op N l T b))) (ev T * lam (th X A N j n b))

def AqBd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) → ∃ k : ℕ, ∀ q : ℕ, q.Prime → ‖ι.symm (g.a q)‖ ≤ (l : ℝ) ^ k

def AdmOf2 : Prop := AdmTop → NewformPartOfTowerModule → AdmRho → JEx → RhoFrob → Unif → FormP → FinP → CoefUb → ThLin → ThOp → ChiStab → ThP → LamEig2 →
  ChiQuad → AqBd → AdmFR

theorem lamEig2 : LamEig2 := by
  intro hLin hOp hStab hP l _ Ω _ _ _ ε X A N w j χ ev hS hev P hPm hEig lam₀ lam hfin hlam
  obtain ⟨k', hev⟩ := hev
  obtain ⟨c, hc⟩ := hP hOp hStab l Ω ε X A N w j χ hS P hPm
  obtain ⟨k, hk⟩ := hfin.exists_loss
  refine ⟨c + k' + k, fun n hn T b hT hb => ?_⟩
  obtain ⟨Θ, hΘ⟩ := hLin l Ω ε X A N w j hS n
  have hTb := hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb
  have h1 := hc n (by omega) Θ hΘ _ hTb
  have h2 := hc n (by omega) Θ hΘ _ hb
  rw [hEig T hT b hb.1, map_smul] at h1
  rw [hlam, hlam, ← smul_eq_mul, ← map_smul, ← Nat.sub_sub, ← Nat.sub_sub]
  refine hk (n - c - k') (by omega) _ _ fun i => ?_
  have h3 := _root_.GlobalTheory.KummerEisensteinGalois.cg_mul_left (k := k') (by omega) (hev T hT) (h2 i)
  have h4 := cg_mono (Nat.sub_le (n - c) k') (h1 i)
  simp only [Pi.smul_apply, smul_eq_mul] at h4 ⊢
  unfold Cg at h3 h4 ⊢
  rw [← norm_neg, neg_sub] at h3
  rw [← sub_add_sub_cancel _ (ev T * Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h4 h3)

end UpperTheory.V.Z.Kato.Joint

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def KatoEulerSystemIwasawaClassStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
      (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
      ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
        (y : G ℚ Ω → Fin 2 → Qbar l),
        IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
        (∀ r y i, Continuous fun s => Y r s y i) ∧
        (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
        (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
        Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
        IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
        SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s)

def SmoothedZetaClassHodgeTateLawStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
      AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
    ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
    ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
      (∀ r s y, Y r s y 1 ∈ cf.O) →
    ∀ (χd : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χd δ)) → (∀ a b : ℕ, χd (a * b) = χd a * χd b) →
      (∀ a b : ℕ, a % N = b % N → χd a = χd b) → ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χd j pr cf lam →
    ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j m₀ c₁
        (fun m ψ z => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
            GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => ((χd n : ℤ_[l]) : Qbar l)) (c : ℤ) (d : ℤ) (x.val : ℤ) i)))

def AdmTop2 : Prop :=
  ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
    [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
    (j : Ω →+* Qbar l),
    Nf e S A W → 1 ≤ e →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    (∀ x ∈ A, ‖j x‖ ≤ 1) →
    ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
    (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
    ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
    ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
      (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
    P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
    (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
    (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
    (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
    (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
    (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
    (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
    ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
    (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
      Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
    ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
      c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
      (∀ b b', pr (b + b') = pr b + pr b') ∧
      (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
      (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
      IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam)

def Glue2 : Prop :=
  KatoEulerSystemIwasawaClassStatement → SmoothedZetaClassHodgeTateLawStatement → AdmFR → TowerEx → GlobalTheory.EisM.CuspidalUnitaryTwistsClaim → Meas3 → JEx → CoefUb → Mono → PsiEx → FrobU → DetIne → HatW → PinOf → SmNz →
    GmEx → ExplSmul → AvgEq → AvgMF → RhsEq → SmSys → ChiFix → ExistsZetaEulerSystemIwasawaData Pin7

end UpperTheory.V.Z.Kato.Joint

end
end
