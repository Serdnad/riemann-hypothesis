module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle129
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Formalism.RealPlaceAnalysis.Bundle003
public import GroundTheory.GlobalFields.KummerTheory.Bundle001
public import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibGP

section SlopeTestRemainingChoices

variable (k : Type) [Field k]

theorem blockIndex_false (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨false, a⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin j) :
    eGP m j ⟨true, Fin.castSucc b⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨true, b⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem glEmbMat_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

end SlopeTestRemainingChoices

theorem gpProj_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  intro k _ _ _ _ m j p hp hp'
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  · apply Subtype.ext
    apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]

end GlobalTheory.CompanionTheory.LeibGP

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat (n : ℕ) :
    Continuous (fun v : Multiplicative (Fin n → k) => colMat k n v.toAdd) := by
  refine continuous_matrix fun i j => ?_
  simp only [colMat]
  split_ifs
  · induction i using Fin.lastCases with
    | last => simpa using continuous_const
    | cast i => simpa [Function.comp_def] using (continuous_apply i).comp (continuous_toAdd (X := Fin n → k))
  · exact continuous_const

theorem continuous_unipIn (n : ℕ) : Continuous (unipIn k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat n)
  · exact continuous_const.sub (continuous_colMat n)

theorem smooth_comp {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (hτ : IsSmooth τ) : IsSmooth (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) :=
  fun v => (hτ v).preimage (continuous_unipIn n)

theorem twKer_le_top (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) :
    twKer τ (MirUin k n) (thetaA k ψ a) ≤
      twKer (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) ⊤ (resChr ψ a ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, w₀, rfl⟩
  set x : Multiplicative (Fin n → k) :=
    (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) with hx
  have hu : unipIn k n x = (u : Mir k n) := by
    have h := (unipEquiv k n).apply_symm_apply ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)
    have h2 := congrArg (Subtype.val : MirU k n → GL (Fin (n + 1)) k) h
    apply Subtype.ext
    exact h2
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w₀, ?_⟩
  show τ (u : Mir k n) w₀ - _ = τ (unipIn k n x) w₀ - _
  rw [hu]
  rfl

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (t : kˣ) :
    IsOpen (ann ψ n t : Set (Multiplicative (Fin n → k))) := by
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  refine Subgroup.isOpen_mono (H₁ := polyBall n (t⁻¹ * c)) ?_ (isOpen_polyBall n _)
  intro x hx a ha
  refine hc _ ?_
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (a.toAdd i * x.toAdd i) ≤ valuation k (c : k)
  have h1 : (t : k) * ((t⁻¹ * c : kˣ) : k) = c := by simp
  rw [map_mul, ← h1, map_mul (valuation k) (t : k)]
  exact mul_le_mul' (ha i) (hx i)

end GlobalTheory.CompanionTheory.MirFourier


open GlobalTheory.CompanionTheory.MirFourier in
theorem GlobalTheory.CompanionTheory.MirFourier.fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Fourier k := by
  intro k _ _ _ _ ψ hψ h1 n V _ _ τ hτ v hv
  have hρ := smooth_comp τ hτ
  set ρ : Representation ℂ (Multiplicative (Fin n → k)) V := τ.comp (unipIn k n) with hρdef
  have hv1 : ∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) :=
    fun a => exists_mem_twKer_polyBall ψ ρ a v (twKer_le_top ψ τ a (hv a))
  have hS : {x | ρ x v = v} ∈ 𝓝 (1 : Multiplicative (Fin n → k)) :=
    (hρ v).mem_nhds (by simp)
  obtain ⟨t, ht⟩ := ann_subset_of_mem_nhds ψ h1 n hS
  obtain ⟨s, hs⟩ := exists_polyBall_twKer_uniform ψ hψ ρ v t hv1
  obtain ⟨R, hRne, hRt, hRsum⟩ := exists_reps_sum_eq_zero ψ hψ n t s
  refine GlobalTheory.CompanionTheory.FiniteFourier.eq_zero_of_twKer ρ hρ (polyBall n s) (isCompact_polyBall n s) ((ann ψ n t).subgroupOf _) ?_ v ?_ R hRne
    (fun a => resChr ψ a (polyBall n s)) ?_ (fun a ha => hs a (hRt a ha)) (fun x hx => hRsum x hx)
  · exact (isOpen_ann ψ hψ n t).preimage continuous_subtype_val
  · intro x hx
    exact ht hx
  · intro a ha x hx
    have h2 := hx (Multiplicative.ofAdd a) (hRt a ha)
    show Circle.toUnits (ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)) = 1
    have h3 : ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 := h2
    rw [h3, map_one]

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem twKer_le_comap_levi (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) (m : GL (Fin n) k) :
    twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ≤
      (twKer τ (MirUin k n) (thetaA k ψ a)).comap (τ (levi k n m)) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  intro x hx
  have key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V),
      τ (GlobalTheory.BZMir.levi k n m) (τ u w) =
        τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w) := by
    intro u w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  first
    | (obtain ⟨u, w, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)
    | (obtain ⟨⟨u, w⟩, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)

theorem twKerConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TwKerConj k := by
  unfold GlobalTheory.BZMir.Fun.TwKerConj
  intro ψ n V _ _ τ a m v
  constructor
  · intro hv
    exact GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv
  · intro hv
    have ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k))
        ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [← ha] at hv
    have h := GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
      map_one, map_one, Module.End.one_apply] at h
    exact h

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

namespace PositivityTheory.Rg.BcN.F2

open GlobalTheory.PRep (IsSmooth fixed)
open GlobalTheory.SmGL (HasFiniteLength IsSubquotient)

/-- A finite-length smooth representation contains `π` as a subquotient if the Hecke operator
acts non-nilpotently on its `K`-fixed vectors and vanishes on the fixed vectors of every
irreducible smooth subquotient inequivalent to `π`. -/
def SubOfNonNil' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
    (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ

end PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.T

open PositivityTheory.Rg.BcN.F2 (SubOfNonNil') in
open GlobalTheory.CompanionTheory.HeckeSub (exists_iterate_eq_zero_of_subquot) in
/-- A Hecke operator that vanishes on the fixed vectors of all irreducible
subquotients inequivalent to `π` can act non-nilpotently only if `π` occurs. -/
theorem subquotient_of_non_nilpotent_variant : SubOfNonNil' F ι := by
  intro K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hNonNilpotent
  by_contra hNotSubquotient
  obtain ⟨r, hIterateZero⟩ :=
    exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hNotSubquotient (⊤ : Subrepresentation ρ)
  obtain ⟨u, hu, hIterateNeZero⟩ := hNonNilpotent r
  exact hIterateNeZero (hIterateZero u Submodule.mem_top hu)

end GlobalTheory.T
end

section

open Formalism.REAL

namespace GlobalTheory.CompanionTheory.CapelliAdj

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasAdj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (T S : Module.End ℂ V) : Prop :=
  ∀ φ ψ : V, B (T φ) ψ = B φ (S ψ)

theorem HasAdj.mul {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by
  intro φ ψ
  show B (T (T' φ)) ψ = B φ (S' (S ψ))
  rw [h (T' φ) ψ, h' φ (S ψ)]

theorem HasAdj.one (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 1 1 := by
  intro φ ψ
  rfl

theorem HasAdj.add {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T + T') (S + S') := by
  intro φ ψ
  simp only [LinearMap.add_apply, map_add (f := _), h φ ψ, h' φ ψ]

theorem HasAdj.zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 0 0 := by
  intro φ ψ
  simp

theorem HasAdj.ofFn {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ V) (g : Fin t → (Module.End ℂ V)ᵐᵒᵖ),
      (∀ k, HasAdj B (f k) (MulOpposite.unop (g k))) →
      HasAdj B (List.ofFn f).prod (MulOpposite.unop (List.ofFn g).prod) := by
  intro t
  induction t with
  | zero =>
    intro f g _
    simpa using HasAdj.one B
  | succ t ih =>
    intro f g hk
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    exact (hk 0).mul (ih _ _ fun k => hk k.succ)

private theorem hasAdj_algebraMap_lemma (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (u : ℂ) :
    HasAdj B (algebraMap ℂ (Module.End ℂ V) u) (algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u)) := by
  intro φ ψ
  simp [Module.algebraMap_end_apply]

theorem HasAdj.tm {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (u : ℂ) (i j : Fin n) :
    HasAdj B (Tm X u i j)
      (MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)) := by
  have h1 : HasAdj B (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0)
      (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) := by
    split_ifs
    · exact hasAdj_algebraMap_lemma B u
    · exact HasAdj.zero B
  have h2 : HasAdj B (X i j) (-Y i j) := by
    intro φ ψ
    rw [h i j φ ψ, LinearMap.neg_apply, map_neg]
  have e1 : Tm X u i j = (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) + X i j := rfl
  have e2 : MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)
      = (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) + -Y i j := by
    unfold Tm
    split_ifs <;> simp [MulOpposite.algebraMap_apply]
  rw [e1, e2]
  exact h1.add h2

theorem HasAdj.intCast (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (z : ℤ) :
    HasAdj B (z : Module.End ℂ V) (z : Module.End ℂ V) := by
  intro φ ψ
  simp [Module.End.intCast_apply]

theorem HasAdj.sum {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAdj.zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasAdj_qdet {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by
  unfold qdet qminor
  have e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ),
      MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ) := fun F =>
    map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ
  rw [e]
  refine HasAdj.sum _ _ _ fun σ _ => ?_
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast]
  refine (HasAdj.intCast B _).mul ?_
  apply HasAdj.ofFn
  intro k
  have hk := HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k
  simpa [map_sub, map_natCast] using hk

theorem adj_qdet (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (X Y : Fin n → Fin n → Module.End ℂ V) (hY : GlRel Y)
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) (φ ψ : V) :
    B (qdet X v φ) ψ =
      B φ ((((-1 : ℂ) ^ n) • qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  rw [hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]

end GlobalTheory.CompanionTheory.CapelliAdj
end

section

open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density


open Filter Topology Set in
theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hfin : (degreeOnePrimes L F \ ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩ degreeOnePrimes L F)).Finite := by
    apply hB.subset
    intro v hv
    by_contra hvB
    exact hv.2 ⟨hcon v hv.1 hvB, hv.1⟩
  have hinter : ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩
      degreeOnePrimes L F).HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
      Set.inter_subset_right
      (GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite hfin) 1).mpr
      (GroundTheory.Global.hasDirichletDensity_degreeOnePrimes (K := L) (L := F))
  have hsplit : {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}.HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
      (K := L) _ 1).mp hinter
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely (K := F) (L := M)
  have heq : (1 : ℝ) = 1 / Module.finrank F M :=
    hsplit.dirichletDensity_eq.symm.trans hSd.dirichletDensity_eq
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

theorem _root_.GlobalTheory.T.residue_field_card_eq_norm : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  first | exact @GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV | exact GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV | (intros; apply GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV <;> assumption)
end
