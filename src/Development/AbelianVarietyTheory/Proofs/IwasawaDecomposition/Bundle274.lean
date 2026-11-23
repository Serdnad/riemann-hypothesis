module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan


open Classical in
theorem avg_level (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (G : Type) [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (f : V) (h : P) :
    r h ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) =
      ((ψ h : Kˣ) : K) • ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f) := by
  have key : ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r h (r p f) = ((ψ h : Kˣ) : K) • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p f := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun p => ?_
    simp only [Equiv.coe_mulLeft, smul_smul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    rw [_root_.mul_inv_rev, map_mul, map_inv, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

  rw [map_smul, map_sum, smul_comm]
  simp only [map_smul]
  rw [key]



theorem jR_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (f : A.fam.amb.FR t), (∀ h : (F.lvl b).P, (A.fam.R t).r h f = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) → ∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), R.B.jR t f (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • R.B.jR t f h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t f hf q hq h
  have e : (R.B.R t).pres.extL (A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f) =
      Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q ((R.B.R t).pres.extL f) :=
    (R.B.R t).act_tie.act_eq ((R.B.R t).act_tie.red q) q rfl f
  have hf' : A.leftGroupActionRight t ((R.B.R t).act_tie.red q) f = (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f := hf ⟨_, hq⟩
  have e3 := congrArg (R.B.R t).pres.extL hf'
  have e4 : (R.B.R t).pres.extL ((((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • f) =
      D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL) • (R.B.R t).pres.extL f :=
    map_smulₛₗ (R.B.R t).pres.extL _ f
  have e5 := congrFun ((e4.symm.trans e3.symm).trans e) h
  simp only [Bridge.g0Act, Pi.smul_apply] at e5
  have e7 := congrArg (fun w => (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂˣ) : ℂ) • w) e5
  simp only [smul_smul, Units.mul_inv, one_smul] at e7
  exact e7.symm

end GlobalTheory.TopSpan
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHoweJoint

theorem exists_bilinear {G G' H H' P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [AddCommGroup P] [Module ℂ P] (S : Set G) (S' : Set G') (τ : G → H →ₗ[ℂ] H) (τ' : G' → H' →ₗ[ℂ] H')
    (a : G → P →ₗ[ℂ] P) (b : G' → P →ₗ[ℂ] P) (hab : ∀ g h x, a g (b h x) = b h (a g x))
    (hirr : ∀ U : Submodule ℂ H, (∀ g ∈ S, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hirr' : ∀ U : Submodule ℂ H', (∀ g ∈ S', ∀ v ∈ U, τ' g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (L : H →ₗ[ℂ] P) (L' : H' →ₗ[ℂ] P) (hL : ∀ g ∈ S, ∀ u, L (τ g u) = a g (L u))
    (hL' : ∀ h ∈ S', ∀ u, L' (τ' h u) = b h (L' u)) (v₀ : H) (v₀' : H') (h0 : L v₀ = L' v₀')
    (hne : L v₀ ≠ 0) :
    ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] P, Ψ ≠ 0 ∧ ∀ h ∈ S', ∀ g ∈ S, ∀ v' v, Ψ (τ' h v') (τ g v) = b h (a g (Ψ v' v)) := by
  let 𝓗 : Submodule ℂ (H →ₗ[ℂ] P) :=
    { carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)}
      add_mem' := fun {A B} hA hB g hg u => by
        simp only [LinearMap.add_apply, map_add (f := _), hA g hg u, hB g hg u]
      zero_mem' := fun g _ u => by simp
      smul_mem' := fun c A hA g hg u => by
        simp only [LinearMap.smul_apply, map_smul, hA g hg u] }
  have hv₀ : v₀ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hv₀' : v₀' ≠ 0 := fun h => hne (by rw [h0, h, map_zero])
  let ev : 𝓗 →ₗ[ℂ] P := (LinearMap.applyₗ v₀).comp 𝓗.subtype
  have hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro A hA
    rcases hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [A.2 g hg v, hv, map_zero]) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀
    · exact Subtype.ext (LinearMap.ker_eq_top.1 h)
  have hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗 := fun h A hA g hg u => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]
  have hrange : ∀ v', L' v' ∈ LinearMap.range ev := by
    rcases hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by
      obtain ⟨A, hA⟩ := hv
      refine ⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩
      rw [hL' h hh, ← hA]
      rfl) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'
    · intro v'
      have : v' ∈ (LinearMap.range ev).comap L' := h ▸ Submodule.mem_top
      exact this
  let Φ : H' →ₗ[ℂ] 𝓗 :=
    (LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)
  have hΦ : ∀ v', ev (Φ v') = L' v' := fun v' =>
    congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))
  refine ⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩
  · rw [h0, ← hΦ, hev]
    exact congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h
  · have key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩ := by
      apply hinj
      rw [hΦ, hL' h hh, ← hΦ v']
      rfl
    show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))
    rw [key]
    show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _
    rw [(Φ v').2 g hg v]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔
    gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

open MvPolynomial in
theorem subst2_one_right {N n : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = ReciprocityTheory.PGsh.rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

open MvPolynomial in
theorem subst2_one_left {N n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin N) ℂ) :
    subst2 1 g (rename Prod.swap P) = rename Prod.swap (ReciprocityTheory.PGsh.rowSubst g P) := by
  have key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) =
      (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι := Fin N) g) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X,
      Finset.sum_eq_single p.2]
    · have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1 := Matrix.one_apply_eq _

      simp [map_sum, h1]
    · intro l _ hl
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0 := Matrix.one_apply_ne hl
      simp [h1]
    · simp
  exact congrArg (fun f => f P) key

theorem isUpperUnitri_one (k : ℕ) : ReciprocityTheory.PGsh.IsUpperUnitri (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩


open MvPolynomial in
theorem exists_joint_intertwiner : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  intro N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'
  obtain ⟨Δ, hΔ, hU, hD⟩ := GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz
  have hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ,
      rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q := fun Q => by
    rw [rename_rename]; simp
  have hinj : Function.Injective
      (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ) :=
    rename_injective _ Prod.swap_injective
  obtain ⟨L', hL', v₀', hv'⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial N (Fin n) ν H' τ' Δ hτ' hK' hΔ
    (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)])
    (fun d => by
      have := hD d (fun _ => 1)
      rw [Matrix.diagonal_one, subst2_one_right] at this
      simpa using this)
  obtain ⟨L, hL, v₀, hv⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ
    (rename Prod.swap Δ) hτ hK
    (fun h => hΔ (by rw [← hsw Δ, h, map_zero]))
    (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg]))
    (fun e => hinj (by
      have := hD (fun _ => 1) e
      rw [Matrix.diagonal_one] at this
      rw [← subst2_one_left, map_smul, hsw, this]
      simp))
  have hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ := by
    show rename Prod.swap (L v₀) = Δ
    rw [hv, hsw]
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_bilinear (UJset (allPos n)) (UJset (allPos N))
    (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap)
    (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap)
    (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap)
    (fun g h x => by simp [subst2_mul])
    (fun U hS => hK.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    (fun U hS => hK'.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) L'
    (fun g hg u => by
      show rename Prod.swap (L (τ g u)) = subst2 1 g (rename Prod.swap (L u))
      rw [hL g hg u, subst2_one_left])
    (fun h hh u => by
      show L' (τ' h u) = subst2 h 1 (L' u)
      rw [hL' h hh u, subst2_one_right])
    v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)
  refine ⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩
  have := hΨe h hh g hg v' v
  simpa [subst2_mul] using this

end GlobalTheory.CompactHoweJoint

end
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.HostSplit

theorem absNorm_eq_of_ncard_placesOver (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ}
    (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E) :
    ∀ v ∈ placesOver E p, Ideal.absNorm v.asIdeal = p := by
  intro v hv
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hPp := v.isPrime
  have hlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
    rw [map_natCast]
    exact hv
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 E)
    (E ≃ₐ[ℚ] E)
  rw [← ncard_placesOver E hp, h, IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal (E ≃ₐ[ℚ] E)] at hf
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h1 := Nat.eq_of_mul_eq_mul_left hpos (hf.trans (mul_one _).symm)
  have h2 := Nat.eq_one_of_mul_eq_one_left h1
  have h3 := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2, pow_one] at h3
  rw [← h3]
  simp

theorem split_completely_of_modEq_one : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK ∧
      ∀ v ∈ placesOver H.E p, Ideal.absNorm v.asIdeal = p := by
  intro R H p hp hc
  have hn : 0 < H.QS := H.QS_pos
  have hq : 0 < H.q := H.hyp.1.pos
  have hd : 1 < H.d := H.hyp.2.1.one_lt
  have hlt : 1 < H.QS * H.q * H.d := by
    have : 0 < H.QS * H.q := by positivity
    nlinarith
  have hm : p % (H.QS * H.q * H.d) = 1 := by
    rw [Nat.ModEq] at hc
    rw [hc, Nat.mod_eq_of_lt hlt]
  obtain ⟨h1, h2⟩ := split_of_one_mod R H p hp hm
  have hG : IsGalois ℚ H.E := H.galois
  exact ⟨h1, h2, absNorm_eq_of_ncard_placesOver H.E hp h1⟩

end GlobalTheory.HostSplit
end

section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN.SelfGood

variable {l : ℕ} [Fact l.Prime]

theorem sqrt_mem (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) (S : IntermediateField ℚ_[l] (Loc.Om l))
    (hS : ∀ z : Loc.Om l, z ^ p = 1 → z ∈ S) (x : Loc.Om l) (hx : x ^ 2 = -(p : Loc.Om l)) : x ∈ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Loc.Om l) p
  let ψ : AddChar (ZMod p) (Loc.Om l) := AddChar.zmodChar p hw.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hw
  let χ : MulChar (ZMod p) (Loc.Om l) := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom (Loc.Om l))
  have hch : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hneg : χ (-1) = -1 := by
    have : quadraticChar (ZMod p) (-1) = -1 := by
      rw [quadraticChar_neg_one hch, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    simp [χ, MulChar.ringHomComp_apply, this]
  have hmu : ∀ a, ψ a ∈ S := fun a => hS _ (by
    rw [AddChar.zmodChar_apply, ← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow])
  have hg : gaussSum χ ψ ^ 2 = -(p : Loc.Om l) := by
    rw [gaussSum_sq hχ1 hχq hψ, hneg, ZMod.card]; simp
  have hm : gaussSum χ ψ ∈ S := by
    unfold gaussSum
    exact sum_mem fun a _ => mul_mem (intCast_mem _ _) (hmu a)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hg.symm) with h | h
  · rw [h]; exact hm
  · rw [h]; exact neg_mem hm

theorem root_mem_Kur {z : Loc.Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : z ^ m = 1) :
    z ∈ Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

end GlobalTheory.MemN.SelfGood
end
