module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.Divisibility.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle047
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X X' : Scheme.{0}}

theorem algebraMap_sec_eq (s : X ⟶ Sp k) (U : X.Opens) (r : k) :
    letI := algΓ s
    algebraMap k (Sec s U) r = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) := rfl

theorem toOm_smul_k (s : X ⟶ Sp k) (q : ℕ) (U : X.Opens) (r : k) (x : OmU s U q) :
    letI := algΓ s
    toOm s q U (r • x) = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) • toOm s q U x := by
  letI := algΓ s
  rw [algebra_compatible_smul (Sec s U) r x, map_smul, algebraMap_sec_eq]
  rfl

def omSecEquiv (s : X ⟶ Sp k) (q : ℕ) (U : X.affineOpens) :
    letI := algΓ s
    OmU s U.1 q ≃ₗ[k] sectionsOn (Omega s q) U.1 :=
  letI := algΓ s
  { (toOmEquiv s q U.2).toAddEquiv.trans (sectionsOn.toΓ (Omega s q) U.1).symm with
    map_smul' := fun r x ↦ (sectionsOn.toΓ (Omega s q) U.1).injective (by
      change toOm s q U.1 (r • x) = _
      rw [toOm_smul_k, sectionsOn.toΓ_smul]
      rfl) }

section Pair

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

end Pair

section PairSec

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

end PairSec

end GlobalTheory.HodgeCoh
end
end

section

open KaehlerDifferential GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem mOm_ιMulti_D_algebraMap (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] (q : ℕ) (w : Fin q → A) :
    ((semiHom_algebraMap k A K).mOm q (exteriorPower.ιMulti A q fun j => D k A (w j)) : DR k K) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (algebraMap A K (w j)) := by
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (SemiHom.mDR_ι _ _).trans (congrArg _ (SemiHom.m1_D _ _))

theorem mOm_injective_and_omB (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Algebra.Smooth k A]
    (B : Subalgebra k K) (hB : ∀ y, y ∈ B ↔ ∃ f : A, algebraMap A K f = y) (q : ℕ) :
    Function.Injective ((semiHom_algebraMap k A K).mOm q) ∧
      ∀ y : DR k K, y ∈ omB k K B q ↔
        ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y := by
  haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q) :=
    (isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)
  haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination A id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance
  haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree
  have hinj : Function.Injective (formLin k A K q) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k])
      (isRegular_iff_ne_zero.mpr (nonZeroDivisors.coe_ne_zero c))) hc
  have hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) =
      algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K) := fun a z => by
    rw [SemiHom.mOm_smul]; rfl
  refine ⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · let S : Submodule k (DR k K) :=
      { carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [map_add (f := _)]; rfl⟩
        zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          refine ⟨algebraMap k A c • a, ?_⟩
          rw [hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
    have : omB k K B q ≤ S := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (hB b).1 hb
      choose w hw using fun j => (hB (v j)).1 (hv j)
      refine ⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩
      rw [hsm, mOm_ιMulti_D_algebraMap]
      simp only [hw]
    exact this hy
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)
    have hz : z ∈ Submodule.span A
        (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k A (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [mOm_ιMulti_D_algebraMap]
      exact ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
    | smul a z _ h => rw [hsm]; exact smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h

end GlobalTheory.PD
end
end

section

open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end

section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_endSpanned_map {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ}
    (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L))
    (h : EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))))) :
    EndSpanned τ U := by
  classical
  intro φ
  set UE := Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))) with hUE
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm

  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  set Y : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' (U.subtype ∘ₗ φ ∘ₗ p) with hY
  have hYv : ∀ v : Fin a → L, Y.mulVec v = (φ (p v) : Fin a → L) := by
    intro v
    rw [hY, LinearMap.toMatrix'_mulVec]
    rfl
  have hYU : ∀ w : U, Y.mulVec (w : Fin a → L) = (φ w : Fin a → L) := by
    intro w
    rw [hYv]
    have : p (w : Fin a → L) = w := by
      have := LinearMap.congr_fun hp w
      simpa using this
    rw [this]
  have hYE : ∀ x ∈ UE, (Y.map f).mulVec x ∈ UE := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap, hYv]
      exact Submodule.subset_span ⟨_, (φ (p v)).2, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact UE.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact UE.smul_mem c hx
  let ψ : UE →ₗ[E] UE := (Matrix.mulVecLin (Y.map f)).restrict hYE
  obtain ⟨XE, hXE, hXEw⟩ := h ψ

  let d := Module.finrank L U
  let b := Module.finBasis L U
  let Φ : Matrix (Fin a) (Fin a) L →ₗ[L] (Fin a × Fin d → L) :=
    { toFun := fun M ik => (M.mulVec (b ik.2 : Fin a → L)) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  let ΦE : Matrix (Fin a) (Fin a) E →ₗ[E] (Fin a × Fin d → E) :=
    { toFun := fun M ik => (M.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  set R := Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) with hR
  set RE := Set.range fun g => ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) with hRE
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  have hΦE : ∀ M : Matrix (Fin a) (Fin a) L, ΦE (M.map f) = f ∘ Φ M := by
    intro M
    funext ik
    show ((M.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((M.mulVec (b ik.2 : Fin a → L)) ik.1)
    rw [hmap]; rfl
  set t : Fin a × Fin d → L := fun ik => (φ (b ik.2) : Fin a → L) ik.1 with ht
  have hXt : ΦE XE = f ∘ t := by
    funext ik
    have hmem : f ∘ (b ik.2 : Fin a → L) ∈ UE := Submodule.subset_span ⟨_, (b ik.2).2, rfl⟩
    have := hXEw ⟨_, hmem⟩
    show (XE.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((φ (b ik.2) : Fin a → L) ik.1)
    rw [this]
    show ((Y.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = _
    rw [hmap, hYU]
    rfl
  have hEspan : f ∘ t ∈ Submodule.span E ((fun v => f ∘ v) '' (Φ '' R)) := by
    rw [← hXt]
    have h1 : ΦE XE ∈ Submodule.map ΦE (Submodule.span E RE) := Submodule.mem_map_of_mem hXE
    rw [Submodule.map_span] at h1
    convert h1 using 2
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, hΦE _⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, (hΦE _).symm⟩
  have hLspan := mem_span_of_map_mem_span f (Φ '' R) t hEspan
  rw [← Submodule.map_span] at hLspan
  obtain ⟨X, hX, hXt'⟩ := hLspan
  refine ⟨X, hX, fun w => ?_⟩
  have hb : ∀ k, X.mulVec (b k : Fin a → L) = (φ (b k) : Fin a → L) := by
    intro k
    funext i
    exact congrFun hXt' (i, k)
  have hext : (Matrix.mulVecLin X) ∘ₗ U.subtype = U.subtype ∘ₗ φ := b.ext fun k => by
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Submodule.subtype_apply]
    exact hb k
  exact LinearMap.congr_fun hext w

end GlobalTheory.SplitField
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.cmData_conj_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  first | exact @GlobalTheory.cmData_sig_isConjOf | exact GlobalTheory.cmData_sig_isConjOf | (intros; apply GlobalTheory.cmData_sig_isConjOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  first | exact @GlobalTheory.LocPlace.exists_place_of_emb | exact GlobalTheory.LocPlace.exists_place_of_emb | (intros; apply GlobalTheory.LocPlace.exists_place_of_emb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.isoSub_span_extension_of_scalars : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  first | exact @GlobalTheory.isoSub_span_map | exact GlobalTheory.isoSub_span_map | (intros; apply GlobalTheory.isoSub_span_map <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)), DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  first | exact @GlobalTheory.semisimple_matrix_rep_decomp | exact GlobalTheory.semisimple_matrix_rep_decomp | (intros; apply GlobalTheory.semisimple_matrix_rep_decomp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
end
