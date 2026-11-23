module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SummableTruncatedGeometric
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle260
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle100
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresBasic

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem coef_inv (f : S.Forms) (c : S.Cl) (g : stab ι J (P.y c)) :
    (χ (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  obtain ⟨g, rfl⟩ := (P.stabI c).surjective g
  rw [← P.coef_act, f.2 c g]

theorem ext_dec (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext (f : S.Cl → S.V) (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hs := P.dec_spec (ι γ * P.y c * k)
  have hc : P.decC (ι γ * P.y c * k) = c :=
    (P.reps (ι γ * P.y c * k)).unique ⟨_, _, hs⟩ ⟨γ, k, rfl⟩
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  generalize P.decG (ι γ * P.y c * k) = γ' at hs ⊢
  generalize P.decK (ι γ * P.y c * k) = k' at hs ⊢
  have e : (P.y c)⁻¹ * ι (γ⁻¹ * γ') * P.y c = (k : G) * (k' : G)⁻¹ := by
    have h2 : ι γ' = ι γ * P.y c * k * (k' : G)⁻¹ * (P.y c)⁻¹ := by rw [hs]; group
    rw [map_mul, map_inv, h2]; group
  have hm : γ⁻¹ * γ' ∈ stab ι J (P.y c) := by
    rw [mem_stab, e]; exact J.mul_mem k.2 (J.inv_mem k'.2)
  have hk : stabK ι (⟨_, hm⟩ : stab ι J (P.y c)) = k' * k⁻¹ := by
    apply Subtype.ext
    simp only [stabK]
    rw [e]; simp
  have hi := coef_inv P f c ⟨_, hm⟩
  rw [hk] at hi
  conv_rhs => rw [← hi]
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
  congr 1
  · rw [map_mul, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, inv_mul_cancel_right]
  · simp

theorem ext_y (f : S.Forms) (c : S.Cl) :
    P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  have := ext_dec P f 1 c 1
  simpa using this

theorem extMem : P.ExtMem := by
  intro f γ h k
  obtain ⟨c, ⟨γ', k', rfl⟩, -⟩ := P.reps h
  have e : ι γ * (ι γ' * P.y c * k') * k = ι (γ * γ') * P.y c * (k' * k : J) := by
    simp [mul_assoc]
  rw [e, ext_dec, ext_dec, map_mul, map_mul, map_smul, smul_smul, Units.val_mul, mul_comm]
  rfl

theorem isom : P.Isom := by
  intro f f'
  unfold adInner CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ext_y, ext_y, P.coef_pair, map_mul, map_inv₀, map_natCast, CSD.wt,
    ← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card]

def bW : Module.Basis S.ιV ℂ W := Module.Basis.mk P.coef_li (by rw [P.coef_span])

theorem bW_apply (j : S.ιV) : bW P j = P.coef (S.bV j) := by simp [bW]

theorem repr_coef (x : S.V) (j : S.ιV) : (bW P).repr (P.coef x) j = σ (S.bV.repr x j) := by
  have : P.coef x = ∑ i, σ (S.bV.repr x i) • bW P i := by
    conv_lhs => rw [← S.bV.sum_repr x]

    rw [map_sum]
    simp only [map_smulₛₗ, bW_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem coef_injective : Function.Injective P.coef := by
  intro x x' h
  apply S.bV.repr.injective
  ext j
  apply σ.injective
  rw [← repr_coef P, ← repr_coef P, h]

theorem extL_injective : Function.Injective P.extL := by
  intro f f' h
  apply Subtype.ext
  funext c
  apply coef_injective P
  rw [← ext_y, ← ext_y]
  exact congrFun h _

theorem eq_of_reps {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext g
  obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
  rw [hF γ _ k, hF' γ _ k, h]

theorem ext_li : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  letI : Algebra K ℂ := σ.toAlgebra
  let Φ : S.Forms →ₗ[K] (S.Cl × S.ιV → K) :=
    { toFun := fun f p => S.bV.repr ((f : S.Cl → S.V) p.1) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f f' h
    apply Subtype.ext
    funext c
    apply S.bV.repr.injective
    ext j
    exact congrFun h (c, j)
  have h1 := S.basis.linearIndependent.map' Φ hΦ
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  let Ψ : (G → W) →ₗ[ℂ] (S.Cl × S.ιV → ℂ) :=
    { toFun := fun F p => (bW P).repr (F (P.y p.1)) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  refine LinearIndependent.of_comp Ψ ?_
  have e : (⇑Ψ ∘ fun i => P.extL (S.basis i)) = fun i => ⇑(algebraMap K ℂ) ∘ (⇑Φ ∘ ⇑S.basis) i := by
    funext i p
    show (bW P).repr (P.ext _ (P.y p.1)) p.2 = σ (S.bV.repr ((S.basis i : S.Cl → S.V) p.1) p.2)
    rw [ext_y, repr_coef]
  rw [e]
  exact h2


open Classical in
def avgForm (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (∑ g : S.Gam c, S.ρ c g x), by
    intro c' γ
    by_cases h : c' = c
    · subst h

      simp only [Pi.single_eq_same, map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun _ => rfl
    · simp [Pi.single_eq_of_ne h]⟩

theorem ext_span : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact extMem P f
  · intro F hF
    have hmem : ∀ M : Submodule ℂ (G → W), (∀ f, P.extL f ∈ M) →
        (∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j))) ∈ M := fun M hM =>
      M.sum_mem fun c _ => M.sum_mem fun j _ => M.smul_mem _ (hM _)
    have key : F = ∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j)) := by
      refine eq_of_reps P hF (hmem _ (extMem P)) fun c => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, ClassPres.extL_apply, ext_y]
      rw [Finset.sum_eq_single c]
      · have hg : ∀ g : S.Gam c, ∑ j, (bW P).repr (F (P.y c)) j • P.coef (S.ρ c g (S.bV j)) = F (P.y c) := by
          intro g
          have h1 := hF (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
          rw [stabK_spec] at h1
          conv_rhs => rw [h1, ← (bW P).sum_repr (F (P.y c))]

          simp only [P.coef_act, map_sum, map_smul, Finset.smul_sum, bW_apply]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

        simp only [avgForm, Pi.single_eq_same, map_sum, mul_smul, ← Finset.smul_sum]
        simp only [Finset.smul_sum (s := (Finset.univ : Finset (S.Gam c)))]
        rw [Finset.sum_comm]
        simp only [hg, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
        exact_mod_cast Fintype.card_ne_zero
      · intro c' _ hc
        simp [avgForm, Pi.single_eq_of_ne (Ne.symm hc)]
      · simp
    rw [key]
    exact hmem _ fun f => Submodule.subset_span ⟨f, rfl⟩

end GlobalTheory.PresBasic

namespace GlobalTheory

theorem classPres_basic : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.Isom ∧ P.ExtBij ∧ (∀ (f : S.Forms) c, P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c)) ∧ Function.Injective P.extL :=
  fun _ _ _ _ _ _ P => ⟨PresBasic.extMem P, PresBasic.isom P, ⟨PresBasic.ext_li P, PresBasic.ext_span P⟩,
    PresBasic.ext_y P, PresBasic.extL_injective P⟩

end GlobalTheory
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocPull

open Formalism.L2.Th1.H (blk4 pow4 slice imgLat tens4 kernel4)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagonalPowFourEquiv (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun z w := φ (slice w.1 z) w.2
  invFun z w := φ.symm (slice w.1 z) w.2
  map_add' x y := by
    funext w
    have e : slice w.1 (x + y) = slice w.1 x + slice w.1 y := rfl
    simp only [e, map_add (f := _), Pi.add_apply]
  map_smul' c x := by
    funext w
    have e : slice w.1 (c • x) = c • slice w.1 x := rfl
    simp only [e, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ (slice w'.1 z) w'.2) = φ (slice w.1 z) := rfl
    simp only [e, LinearEquiv.symm_apply_apply]
    rfl
  right_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ.symm (slice w'.1 z) w'.2) = φ.symm (slice w.1 z) := rfl
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl

theorem slice_pow4E (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (a : Fin 4) (z : Fin 4 × n → ℂ) :
    slice a (diagonalPowFourEquiv φ z) = φ (slice a z) := rfl

theorem fourCopiesHermitianForm_eq_sum_blocks (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) x y = ∑ a : Fin 4, matH h (slice a x) (slice a y) := by
  show (∑ w, ∑ w', x w * blk4 h w w' * conj (y w')) = ∑ a : Fin 4, ∑ i, ∑ j, x (a, i) * h i j * conj (y (a, j))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blk4]
  · intro b _ hb
    simp [blk4, Ne.symm hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem blockwiseActionOnFourCopies_isometry (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (h : Matrix n n ℂ)
    (hφ : IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ))) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y) = matH (blk4 h) x y := by
  rw [fourCopiesHermitianForm_eq_sum_blocks, fourCopiesHermitianForm_eq_sum_blocks]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [slice_pow4E, slice_pow4E]
  exact hφ _ _

theorem imgLat_pull (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    imgLat (((diagonalPowFourEquiv φ).trans g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (pow4 (Λ.comap φ.toLinearMap.toAddMonoidHom)) =
      imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨diagonalPowFourEquiv φ x, fun a => hx a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(diagonalPowFourEquiv φ).symm x, fun a => ?_, ?_⟩
    · show φ (slice a ((diagonalPowFourEquiv φ).symm x)) ∈ Λ
      rw [← slice_pow4E, LinearEquiv.apply_symm_apply]
      exact hx a
    · show g (diagonalPowFourEquiv φ ((diagonalPowFourEquiv φ).symm x)) = g x
      rw [LinearEquiv.apply_symm_apply]

theorem locNorm_pull : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι φ hφ H
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  have hI := imgLat_pull φ Λ g₁
  refine ⟨(diagonalPowFourEquiv φ).trans g₁, ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    exact (hiso (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y)).trans (blockwiseActionOnFourCopies_isometry φ h hφ x y)
  · rw [hI]
    exact hnd
  · rw [hI]
    exact hidx
  · funext z
    have t1 : tens4 (fun z => θ (φ z)) z = tens4 θ (diagonalPowFourEquiv φ z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [hI]
    rfl

end GlobalTheory.ThLoc.LocPull
end
end

section

noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical Formalism.MainNotions.OrbitPlaces PI.OrbBoundFW

namespace GlobalTheory.TwU

theorem orbitBound_overSecondEmbedding_anyBasePoint_alt : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  intro D L X K ce E C6 C hA hS hC p _ h _hc0 _hP hp u i hi t ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i (true, t) Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi (true, t) Th) D.R.k (wOrb D p i (true, t))
    (eOrb E p u i (true, t)) (three_le_k D) (wOrb_pos hS p hi (true, t)) (eOrb_bounds hS p u hi (true, t))
    (dl_off h u i (true, t) Th) (dl_on h u i (true, t) Th)
  refine kvalGe_mono hCor ?_
  have hg : 0 ≤ ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  have hw := sum_Wc_le hS h u hi (true, t) Th
  have hl := loss_le hS hC h hp hi (true, t)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i (true, t) s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi (true, t) s).le
  have hc6 : C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p (true, t) = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s) := rfl
  have hE : errF L K ce (i + 1) p (true, t) = Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p (true, t) : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show FOrb D (i + 1) p (true, t) - errF L K ce (i + 1) p (true, t) ≤
    (∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s)) - C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end GlobalTheory.TwU
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

namespace GlobalTheory.CurveToStdLog

open MvPowerSeries

variable {l : ℕ} [Fact l.Prime] {κ κ' : Type}

theorem mvsubst_subst {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a) {b : MvPowerSeries κ ℂ_[l]}
    (hb : constantCoeff b = 0) (f : PowerSeries ℂ_[l]) :
    MvPowerSeries.subst a (f.subst b : MvPowerSeries κ ℂ_[l]) = f.subst (MvPowerSeries.subst a b) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]
  rfl

theorem subst_expMv [Finite κ] {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : ∀ i, constantCoeff (a i) = 0)
    {f : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf,
    GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]

theorem expMv_add {f g : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expMv (f + g) = expMv f * expMv g := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
    GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expMv_zero : expMv (0 : MvPowerSeries κ ℂ_[l]) = 1 := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero

theorem expMv_sum {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries κ ℂ_[l]}
    (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expMv_zero
  | insert i s hi ih =>

    rw [Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]

theorem cc_ph (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) :
    PowerSeries.constantCoeff g.ph = 0 := by
  have h := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1
  show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
  rw [map_neg, h, neg_zero]

theorem cc_phAt (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) : constantCoeff (g.phAt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)

theorem inv_ePhi1 (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
  have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
  have h := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2
  rw [subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one,
    coe_substAlgHom] at h
  have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
  exact h

end GlobalTheory.CurveToStdLog
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem wPl_pos : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), 0 < wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨y0, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x0 y0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := h0 x (le_trans (le_max_left _ _) hx) hx1 i
  have h2 := (h1 x (le_trans (le_max_right _ _) hx) hx1 i j hj z).1
  linarith

end GlobalTheory.Ggeo
end
