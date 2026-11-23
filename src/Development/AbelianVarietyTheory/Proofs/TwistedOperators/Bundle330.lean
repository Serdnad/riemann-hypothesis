module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle313
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178

@[expose] public section

section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKExtFields

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem dRep_rep_conj (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : M.H τ) :
    dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold Formalism.L2.Theta.dRep DSModel.rep
  congr 1
  funext t
  have h1 : t • ((M.fr τ)⁻¹ * X * M.fr τ) = (M.fr τ)⁻¹ * (t • X) * M.fr τ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, Matrix.exp_conj' _ _ (M.fr_unit τ)]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem foldr_dRep_conj (M : DSModel V S) (τ : D.what₂.Tau) (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (w : M.H τ) :
    (l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ).foldr (dRep (M.rep τ)) w = l.foldr (dRep (M.σ τ)) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_rep_conj]

theorem conj_mem_lieAt (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have h1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have h3 : (M.fr τ)ᴴ * (Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ = 0 := by
    rw [hX']; simp
  simp only [conjTranspose_mul, Matrix.mul_assoc, h1, h2]
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h3

theorem multMap_fields : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)

end GlobalTheory.GKExtFields

end
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory

theorem flathFactorisation_of_tensorProduct (h1 : GlobalTheory.Published.FlathTensorProduct)
    (h2 : GlobalTheory.Published.UnitaryIrreducibleAdmissible) : GlobalTheory.Published.FlathFactorisation := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  obtain ⟨R, ξ, B, hf⟩ := h1 F E σ hc n J hJ H π hπ
  have hirr : ∀ v, (smRep (Flath.finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (Flath.finFactor R v)) := by
    intro v
    have := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
    exact GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr
      (fun K hK hK' => h2 F E σ hc n J hJ v (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr K hK hK')
  refine ⟨R, ξ, B, hf, hirr, ?_⟩
  intro L hL
  have := hL
  have hu : ∀ᶠ v in cofinite, ‖ξ (.inr v)‖ = 1 := Sum.inr_injective.tendsto_cofinite.eventually hf.unit
  filter_upwards [hu, hf.eventually_fixed L,
    GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L
      (by infer_instance)] with v hv hfix hθ
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have sm : ∀ y, y ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) →
      y ∈ GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := by
    intro y hy
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep (Flath.finFactor R v) g y = y}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, map_mul, mul_apply_eq_comp] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk
    exact Subgroup.isOpen_mono hle hKo
  have hξ : ξ (.inr v) ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix k hk
  let x : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := ⟨ξ (.inr v), sm _ hξ⟩
  have hx : x ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hξ k hk)
  have hx0 : x ≠ 0 := fun e => by
    have : ξ (.inr v) = 0 := congrArg Subtype.val e
    rw [this, norm_zero] at hv
    exact zero_ne_one hv
  have hline := GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep (Flath.finFactor R v)) (hirr v).1 (hirr v).2 x hx hx0
  refine le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hξ)
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))) ∈
      fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy'
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory
end

section

noncomputable section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S GlobalTheory.SmVec GlobalTheory.MultGelf Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivValues

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def IsEquivMap (θ : InfFam D) (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)

def IsSobValued (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ : InfFam D} {M : DSModel V S} {T : MMap M}

theorem rder_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hC τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hE hC τ v Z w _ rfl

theorem gelf_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ)) :
    gelf θ V τ k (T v) = T (Function.update v τ w) := by
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem gelf_eigen (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) :
    ∃ c : ℂ, gelf θ V τ k (T v) = c • T v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ)
    (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k
  refine ⟨c, ?_⟩
  have hv := hc _ ((mem_sm M τ).1 (v τ).2)
  rw [gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]
  have := T.map_update_smul v τ c (v τ)
  rw [Function.update_eq_self] at this
  exact this

theorem zfin (hθ : IsInfFam θ) (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (v : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T v ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_eigen hE hC τ k v
  rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem isAutFunSm : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  intro _ D θ hθ V S M T U N hU hT hE hC v
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT v
  exact GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩)
    ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)

end GlobalTheory.EquivValues

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.exists_coset_rep_hecke_element_principal_level : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  first | exact @GlobalTheory.HeckeDC.exists_rep | exact GlobalTheory.HeckeDC.exists_rep | (intros; apply GlobalTheory.HeckeDC.exists_rep <;> assumption)
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_gE_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hE hg h0 g x
  unfold RealDat.models_HE RealDat.models_gE RealDat.models_ν0 at *
  obtain ⟨hinj, hrange, hip⟩ := hE
  obtain ⟨hm, hfd⟩ := h0
  obtain ⟨hHaar, -⟩ := hm

  let u : R.HE.H ≃ₗ[ℂ] R.HE.H :=
    LinearEquiv.ofLinear (R.gE g) (R.gE g⁻¹)
      (by
        ext y
        show R.gE g (R.gE g⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (by
        ext y
        show R.gE g⁻¹ (R.gE g y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have hy : R.HE.e y ∈ LinearMap.range R.HE.e := ⟨y, rfl⟩
    rw [hrange] at hy
    exact (Submodule.mem_inf.mp hy).1

  have hact : ∀ y v, R.HE.e (u y) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e y v) := by
    intro y v
    show R.HE.e (R.gE g y) v = _
    rw [hg]
    rfl
  exact GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) R.HE.H R.HE.e 1 R.ν0 R.fd0
    (fun y z => by rw [one_mul]; exact hip y z) hinj hmem hHaar hfd (R.eG g) u hact x

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gW_norm_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → R.models_gW → R.models_νW → ∀ i σ g x, ‖R.gW i σ g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hH hg hν i σ g x
  unfold RealDat.models_HW at hH
  unfold RealDat.models_gW at hg
  unfold RealDat.models_νW at hν
  obtain ⟨hinj, hrange, hip⟩ := hH i σ
  unfold ipAt at hip
  have hfd := hν i
  unfold IsMeasFD at hfd
  have hHaar : (R.νW i).IsHaarMeasure := by
    have h := hfd.1
    unfold IsMeasLev IsMeasLevW at h
    exact h.1
  let u : (R.HW i σ).H ≃ₗ[ℂ] (R.HW i σ).H :=
    LinearEquiv.ofLinear (R.gW i σ g) (R.gW i σ g⁻¹) (by ext y; simp) (by ext y; simp)
  have hmem : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => by
    rw [← hrange]
    exact LinearMap.mem_range_self _ y
  exact _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MW i σ) (R.βW i) (R.datWp i R.triv) _ _ (R.HW i σ).H (R.HW i σ).e _
    (R.νW i) (R.fdW i) hip hinj hmem hHaar hfd.2 (R.eG g) u
    (fun y v => congrArg (fun T => T v) (hg i σ g y)) x

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  exact @GlobalTheory.RowEvalHH.conj_eval_mem_HH
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.equivariant_of_generator_oneParameterGroup : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  first | exact @GlobalTheory.OneParamEquivariance.equivariant_of_generator | exact GlobalTheory.OneParamEquivariance.equivariant_of_generator | (intros; apply GlobalTheory.OneParamEquivariance.equivariant_of_generator <;> assumption)
end
