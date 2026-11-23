module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPair
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle419
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle108
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle107
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle420
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.gridColumnParameters_negated_dataAR_pair : ∀ (D : D7) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ al be ga de : List ℚ,
    Formalism.MainNotions.SchurIrreducible.DataAR (GlobalTheory.Grid.sLen D - 1) al be ga de ∧
    GlobalTheory.Grid.parP D i τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
    GlobalTheory.Grid.parP D (i + 1) τ =
      dualPar (signed (al ++ block (GlobalTheory.Grid.sLen D - 1) ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) := by
  first | exact @GlobalTheory.NegPair.params | exact GlobalTheory.NegPair.params | (intros; apply GlobalTheory.NegPair.params <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotDictAlg

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A'.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotDictAlg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

theorem conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p, hp, ?_⟩
  have := Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p
  rw [hz, map_zero] at this
  simpa using this

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem jet_negSp_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (u : WO S T) (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT (heisO ψ (negSp S) T u f) (MvPolynomial.monomial k 1) 0 =
      starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (fun w => starRingEnd ℂ (f w)))
        (MvPolynomial.monomial k 1) 0) := by
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2
  have hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcc] at h
  have key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w)) := by
    have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w) := rfl
    rw [h, ← hcj]
    funext w
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [key]

theorem std_eq_colLat_one {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotTransJet

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

end GlobalTheory.BotTransJet
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopColumn

open GlobalTheory.DefiniteMult GlobalTheory.DefLift

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}



theorem exists_form_triv (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (K : Subgroup (GA D V)) (J : Subgroup (Bridge.Gf V))
    (hJ : ∀ κ ∈ GfC V, (finHom V).rangeRestrict κ ∈ J → κ ∈ K)
    {T : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M (K : Set (GA D V)) 1) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J 1, c.toMap pr f = T := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  have h2 := tensor_irreducible D V S M m hp
  obtain ⟨fd, inj, πt, hπ, irr⟩ := h2
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  have hE := GlobalTheory.multT_cont_left_equiv D θ V S M πt _ _ hp (fun τ => (m τ).2.1) inj hπ T hT
  choose Ψ hΨ using fun h : GA D V => hb.2 (LinearMap.proj h ∘ₗ T)
  replace hΨ : ∀ h x, pr (Ψ h) x = T x h := fun h x => LinearMap.congr_fun (hΨ h) x
  have hlev : ∀ k ∈ K, ∀ x g, T x (g * k) = T x g := fun k hk x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level θ M _ _ _ ((mem_multT θ M _ _ _).1 hT) v).2.2 k hk g
      rw [Pi.one_apply, one_mul] at this
      rw [map_smul, Pi.smul_apply, Pi.smul_apply]
      exact congrArg (r • ·) this
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
  let U : Submonoid (GA D V) :=
    { carrier := {a | ∀ h, Ψ (h * a) = c.ρ a⁻¹ (Ψ h)}
      one_mem' := fun h => by rw [mul_one, inv_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha, mul_inv_rev, map_mul]; rfl }
  obtain ⟨f, hf⟩ := exists_descend (finHom V) c.ρ Ψ fun a ha => real_le hθ U (fun τ g hg h => by
      obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [← key, hΨ, hΨ, (hE x).2.2]; rfl) ha
  refine ⟨f, mem_adForms (finHom V) (GQ V) (GfC V) (exists_fin_lift V) c.ρ hc.1 _ _ Ψ f hf fun γ hγ g κ hκ hk => ?_,
    LinearMap.ext fun x => funext fun h => ?_⟩
  · have e2 : Ψ (γ * g * κ) = Ψ g := by
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [hΨ, hΨ, hlev κ (hJ κ hκ hk), (hE x).2.1 γ hγ]
    rw [e2]
    simp
  · have e := GlobalTheory.DefiniteEnd.rho_inv_cancel (c := c) h⁻¹ (Ψ h)
    rw [inv_inv] at e
    exact (congrArg (fun w => pr w x) ((congrArg (c.ρ h⁻¹) (hf h)).trans e)).trans (hΨ h x)

end GlobalTheory.TopColumn

theorem GlobalTheory.TopColumn.exists_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D), IsInfFam θ → ∀ {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core D.R.m)) S), (∀ τ a, M.ε τ a = true) → (coefPlus G θ).Is → ∀ (pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsDualPair θ M (coefPlus G θ) pr → ∀ y ∈ CoreForms G θ D.R.m M, ∃ c ∈ Cols G θ, (coefPlus G θ).toMap pr c = y := by
  intro D T L sc G θ hθ S M hε hc pr hpr y hy
  exact GlobalTheory.TopColumn.exists_form_triv (V := G.V (.core D.R.m)) (c := coefPlus G θ) hθ hε hc hpr
    (lev G (.core D.R.m)) (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.levPlus G) (fun κ hκ h => ⟨hκ, h⟩) hy
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizeGap_of_sizes : SizeGap :=
  fun _ => ⟨0, fun _ large₂ _ _ h => GlobalTheory.RowSizes.sizes_of_sizeRows large₂ h⟩

end GlobalTheory.SepRows

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem conjRead_holds : ConjRead := GlobalTheory.Asc.FamilyModel.conjRead

end GlobalTheory.Asc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselPeriod_ascent_of_tower_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_rungs | exact GlobalTheory.Asc.ascent_of_rungs | (intros; apply GlobalTheory.Asc.ascent_of_rungs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData : DepFixed → DatumDep → PartFixed := by
  first | exact @GlobalTheory.Asc.partFixed_of_depFixed | exact GlobalTheory.Asc.partFixed_of_depFixed | (intros; apply GlobalTheory.Asc.partFixed_of_depFixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

private theorem dualPar_dualPar' (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  rw [Finset.image_image]
  simp [Function.comp_def]

private theorem shift_zero_lemma_2 (S : SPar) : GlobalTheory.SignedHC.shift 0 S = S := by
  unfold GlobalTheory.SignedHC.shift
  simp

private theorem exists_par_of_gridData_bounds {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {ε : Fin (n + 1) → Bool}
    {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {B : ℝ}
    (hke : Even G.k) (hme : Even G.m) (hm2 : 2 ≤ G.m) (hn : n + 1 = G.k + G.m) (h3 : 3 ≤ n)
    (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hvk : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.b (l + 1))
    (hga : 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.ga) (hvk0 : 0 ≤ G.v G.k) (hb1 : 0 < G.b 1)
    (ha0 : ((G.a 0 : ℚ) : ℝ) ≤ B) (hbm : (G.b G.m : ℝ) ≤ B)
    (hl : IsEnum (G.parPi 0) lam ε) (hm : IsEnum G.parD0 mu ε') :
    ∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu B := by
  have hga0 : 0 < G.ga := by
    have h0 : (0 : ℝ) < 1000 * ((n : ℝ) + 1) ^ 3 := by positivity
    exact_mod_cast h0.trans_le hga
  have hH : (2 : ℝ) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hvk1 : 1 ≤ G.v G.k + G.b 1 := by omega
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.card_minus_signs_half_of_even hme hga0 hl hm
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv ε ε' (hc.trans hc'.symm)
  obtain ⟨hHl, hHm⟩ := GlobalTheory.T.harish_chandra_param_of_even hke hme hn hl hm
  have hw := GlobalTheory.T.interlaced_signed_parameters hga0 hvk1 hl hm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parameters_separated_by_one hga0 hv (by omega) hl hm
  obtain ⟨hwl, hwm, hgl, hgm⟩ := GlobalTheory.T.parameters_spacing_and_gap hH hga hv hvk hb hl hm
  have habs : ∀ a c, a ≠ c → 2 ≤ |lam a - lam c| := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact (hwl a c h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      exact (hwl c a h).trans (le_abs_self _)
  have hB := GlobalTheory.T.signed_parameters_bounded hvk0 hb1 ha0 hbm hl hm
  have hk2 := G.two_le_k
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ε' i = false)
  have hneg : ∃ i, ε' i = false := by
    have hpos : 0 < (Finset.univ.filter fun i => ε' i = false).card := by
      rw [hc']
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hpos : (Finset.univ.filter fun i => ε' i = false).card ≤ (Finset.univ.filter fun i => ε' i = true).card := by
    have heq : (Finset.univ.filter fun i => ¬ ε' i = false) = Finset.univ.filter fun i => ε' i = true := by
      ext i
      simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact ⟨e, he, h3, hHl, hHm, hw, GlobalTheory.T.isInterlaced_sub_single_of_spread hw habs hs1 hs2, hwl, hwm, hgl, hgm, hneg, hpos, hB⟩

theorem realInputPar : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ)
    (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε →
    IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧
      Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  intro _ _ _
  refine ⟨0, fun D large₂ _ _ hS T L μ0 _ Gr W M _ => ?_⟩
  intro τ ε lam ε' mu hlam hmu
  obtain ⟨hv, hvk, hb, hga, hvk0, hb1, ha0, hbm, hb1', hb4⟩ := GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds D large₂ hS τ
  have hl : IsEnum ((GlobalTheory.ChiGrid.num D 1 τ).parPi 0) lam ε := hlam
  have hD : dualPar (parB (Ptw D) 0 τ) = (GlobalTheory.ChiGrid.num D 1 τ).parD0 := by
    rw [← GlobalTheory.SignedHC.GridData.parD_zero_zero, parB, ← parV_zero D 1 (Nat.zero_le _) τ, dualPar_dualPar']
    show GlobalTheory.SignedHC.shift (if Odd (0 + 0) then -(1 / 2) else 0) _ = _
    rw [if_neg (by decide), shift_zero_lemma_2]
  have hm' : IsEnum (GlobalTheory.ChiGrid.num D 1 τ).parD0 mu ε' := hD ▸ hmu
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  refine ⟨exists_par_of_gridData_bounds (n := D.R.r) D.R.k_even D.R.m_even h2m
    (by show D.R.r + 1 = D.R.k + D.R.m; omega) (by omega) hv hvk hb hga hvk0 hb1 ha0 hbm hl hm', ?_,
    Real.log_nonneg hb1'⟩
  have hbpos : 0 < large₂.sc.b := by linarith
  show Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2) ≤ 6 * Real.log large₂.sc.b
  have h6 := Real.log_pow large₂.sc.b 6
  push_cast at h6
  rw [← h6]
  apply Real.log_le_log (by positivity)
  calc 8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2 ≤ large₂.sc.b ^ 4 * large₂.sc.b ^ 2 := by gcongr
    _ = large₂.sc.b ^ 6 := by ring

end GlobalTheory.SepPer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.weil_datum_conjugation_dictionary_row_grid : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  first | exact @GlobalTheory.ConjDict.conj_dict | exact GlobalTheory.ConjDict.conj_dict | (intros; apply GlobalTheory.ConjDict.conj_dict <;> assumption)
end
