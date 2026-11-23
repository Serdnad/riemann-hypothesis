module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle063
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
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
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle001
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.PstExt

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [Module LL' V'] [IsScalarTower ℚ_[l] LL' V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

theorem tensCoord_mulV (c : ↥(MaximalUnramifiedExtension l)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (mulV P LL' V' c x) i = mulV P LL V c (tensCoord E (Bst P) x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]

variable (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
include hE

theorem tensCoord_stRep (g : ↥(GK K)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (stRep P ρ' g x) i = stRep P ρ g (tensCoord E (Bst P) x i) := by
  change tensCoord E (Bst P) (AlgebraTensorModule.map (ρ' g)
    (actSt P (g : GQ l)).toLinearMap x) i =
    AlgebraTensorModule.map (ρ g) (actSt P (g : GQ l)).toLinearMap
      (tensCoord E (Bst P) x i)
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

theorem mem_Dpst_coord (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dpst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dpst P ρ := by
  constructor
  · intro hx i
    obtain ⟨K', hK⟩ := (mem_Dpst P ρ').1 hx
    exact (mem_Dpst P ρ).2 ⟨K', fun g hg => by rw [← tensCoord_stRep P hE, hK g hg]⟩
  · intro hx
    choose K' hK using fun i => (mem_Dpst P ρ).1 (hx i)
    have hsum : x = ∑ i, (tensCoord E (Bst P)).symm (Pi.single i (tensCoord E (Bst P) x i)) := by
      apply (tensCoord E (Bst P)).injective

      rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single _).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => (mem_Dpst P ρ').2 ⟨K' i, fun g hg => (tensCoord E (Bst P)).injective ?_⟩
    funext j
    rw [tensCoord_stRep P hE, LinearEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h
      simp [hK j g hg]
    · simp [Pi.single_eq_of_ne h]

def dpstCoord : DpstUr P ρ' ≃ₗ[↥(MaximalUnramifiedExtension l)] (ι → DpstUr P ρ) where
  toFun x i := toUr P ρ ⟨tensCoord E (Bst P) ((toUr P ρ').symm x).1 i,
    (mem_Dpst_coord P hE _).1 ((toUr P ρ').symm x).2 i⟩
  invFun y := toUr P ρ' ⟨(tensCoord E (Bst P)).symm fun i => ((toUr P ρ).symm (y i)).1,
    (mem_Dpst_coord P hE _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      exact ((toUr P ρ).symm (y i)).2⟩
  map_add' x y := by
    funext i
    exact Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
  map_smul' c x := by
    funext i
    exact Subtype.ext (tensCoord_mulV P c x.1 i)
  left_inv x := Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
  right_inv y := by
    funext i
    exact Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i)

theorem isPst_of_coord (h : IsPst P ρ) : IsPst P ρ' := by
  unfold IsPst at h ⊢
  rw [(dpstCoord P hE).rank_eq, (E.restrictScalars ℚ_[l]).rank_eq, rank_fun, rank_fun, h]

end Coord

theorem isPst_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1),
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  intro l _ P E Ω _ _ _ Gw O _ _ _ Bw m L₁ L₂ hL r₁ h
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isPst_of_coord P (E := GlobalTheory.Pst.vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

end GlobalTheory.PstExt
end
end

section

noncomputable section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open Filter Topology

namespace GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

theorem eventually_unrAt (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) :
    ∀ᶠ v in Filter.cofinite, UnrAt χ v := by
  have h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ,
      Valued.v (x : v.adicCompletion L) = 1 ∧
      (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    refine (hc _ ?_).1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp hχ).sub continuous_const).norm
  have h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) :=
    GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx
  have h1 := (hc.tendsto 1).comp h0
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact h2.mono fun v hv => hx' v hv

theorem exists_level (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ,
      Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1 := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub
      continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine hx1.trans_lt ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := by
    have := Valuation.map_one_add_of_lt _ hlt
    simpa using this
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

def truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  infIdele L (infPart L x) * ∏ v ∈ T, localIdele L v (finPart L v x)

theorem truncIdele_inv (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    truncIdele x⁻¹ T = (truncIdele x T)⁻¹ := by
  simp only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]

open Classical in
theorem finPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) :
    finPart L v (truncIdele x T) = if v ∈ T then finPart L v x else 1 := by
  rw [truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _,
      finPart_localIdele]
  · exact Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _

theorem infPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    infPart L (truncIdele x T) = infPart L x := by
  rw [truncIdele, map_mul, infPart_infIdele, map_prod,
    Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]

theorem coe_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L) =
      ((x : AdeleRing (𝓞 L) L).1, GlobalTheory.HeckeProduct.cut (x : AdeleRing (𝓞 L) L).2 T) := by
  classical
  refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
  · exact congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)
  · have h := congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L))
      (finPart_truncIdele x T v)
    refine h.trans ?_
    by_cases hv : v ∈ T
    · simp only [hv, if_true]; exact (if_pos hv).symm
    · simp only [hv, if_false]; exact (if_neg hv).symm

theorem tendsto_truncIdele (x : Ideles L) :
    Tendsto (truncIdele x) atTop (𝓝 x) := by
  have h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (x : AdeleRing (𝓞 L) L)) := fun x => by
    simp only [coe_truncIdele]
    exact tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  have h2 := h x⁻¹
  simp only [truncIdele_inv] at h2
  exact h2

theorem char_eq_prod_local (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (x : Ideles L)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) :
    χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  classical
  have h1 := (hχ.tendsto x).comp (tendsto_truncIdele x)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop S] with T hT
  change _ = χ (truncIdele x T)
  rw [truncIdele, map_mul, map_prod]
  congr 1
  exact Finset.prod_subset hT fun v _ hv => hS v hv

theorem continuous_char_factor : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) :=
  fun _ _ _ χ hχ => ⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩

end GlobalTheory.HeckeSplit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem parUpRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.ParUpRec D.nd D.naut i := by
  intro D T hθ hpair hbc hsplit hrep i x hx Sig hSig
  have h := GlobalTheory.ParUpRoad.main _ _ _ D.nd D.naut hθ (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
    (fun i => splitLift_of_pairLift _ _ _ D.nd D.naut i (hpair i))
    (fun i => GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsplit i) (hrep i))
  exact (GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage.thetaTMapsIntoEig_iff_map_le D.nd D.naut).1 h i x Sig hx hSig

end GlobalTheory.RowTie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem rat_jump_sets_eq_int_multisets : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  intro D i ρ g ep up hpl hup a
  have hP : hcAt D g = D.hc ρ := hcAt_eq_hc D ρ g hpl
  have hs : pos (if ep then 1 else -1) g = up := by
    unfold LJ.TypeU at hup
    rw [Formalism.HC.Frame.mem_Psi_iff] at hup
    rcases Int.units_eq_one_or g.1.2 with h | h <;> cases ep <;> cases up <;> simp_all [pos]
  have hsz : LJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (liftIdx D i) := by
    have := D.nd.j_range i
    unfold LJ.sz liftIdx
    rw [dite_eq_left (by omega)]
  have hc0 : LJ.c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  obtain ⟨h2, h1⟩ := jumps_rat (D.hc ρ) (liftIdx D i) up a
  rw [hP, hs, h1, h2]
  have hblk : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    refine exists_congr fun c => and_congr Iff.rfl ?_
    exact_mod_cast Iff.rfl
  have hblk' : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (D.R.t : ℚ) - 1 - (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    constructor
    · rintro ⟨c, hc, h⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      have h' : (D.R.t : ℤ) - 1 - x = c := by exact_mod_cast h
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      omega
    · rintro ⟨c, hc, rfl⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      ring
  cases up
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, Bool.false_eq_true, if_false, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk' (-a - 1)
    push_cast at this
    exact this
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, if_true, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk (-a - 1)
    push_cast at this
    exact this

end GlobalTheory.HTW.Rec
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem wMax_le_and_ge : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  intro D L C hR
  have hb : (0 : ℝ) ≤ L.sc.b' := by
    obtain ⟨-, h1, -, h3, -⟩ := hR
    linarith
  have hmem : ∀ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat},
      (s : ℝ) ≤ 8 / 5 * L.sc.b' := by
    rintro s ⟨g, j, hg, rfl⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR hg
    have h100 : (100 : ℝ) ≤ L.sc.w'' D.R.n := hR.2.1
    have hpos : (0 : ℤ) ≤ ⌊(hcAt D g).e j⌋ := by
      have : (0 : ℝ) ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    have : ((⌊(hcAt D g).e j⌋.toNat : ℤ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [Int.toNat_of_nonneg hpos]
    have h' : ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [← this]; norm_cast
    rw [h']; exact h2
  have hbdd : BddAbove {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} := by
    refine ⟨⌊8 / 5 * L.sc.b'⌋₊, fun s hs => ?_⟩
    exact Nat.le_floor (hmem s hs)
  refine ⟨?_, ?_⟩
  · unfold wMax
    rcases Set.eq_empty_or_nonempty {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} with he | hne
    · rw [he, csSup_empty]; simp; linarith
    · obtain ⟨s, hs, hseq⟩ : ∃ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, s = sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} :=
        ⟨_, Nat.sSup_mem hne hbdd, rfl⟩
      rw [← hseq]; exact hmem s hs
  · intro g j hg
    have h1 : ⌊(hcAt D g).e j⌋.toNat ≤ wMax D := le_csSup hbdd ⟨g, j, hg, rfl⟩
    calc ⌊(hcAt D g).e j⌋ ≤ (⌊(hcAt D g).e j⌋.toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (wMax D : ℤ) := by exact_mod_cast h1

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.InertWord

theorem inert_nothree_nonthick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 →
    ¬ (φ = R.cc ∧ Thick H τ) →
    NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧
      ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  intro R H τ φ hL hφ hnot
  have h2 : 2 ≤ orderOf φ := by
    rw [GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit φ hφ]
    exact Nat.le_of_dvd (Nat.lcm_pos two_pos (orderOf_pos _)) (Nat.dvd_lcm_left _ _)
  by_cases hc : φ = R.cc
  · have hτ : ¬ Thick H τ := fun h => hnot ⟨hc, h⟩
    subst hc
    have hno : ∀ i : ZMod (orderOf (R.cc)), ¬ Thick H (letter τ (R.cc) i) := by
      intro i h
      apply hτ
      have := (GlobalTheory.T.complexConjugation_orbit_one_realPlace τ).2 i
      unfold Thick at h ⊢
      rw [this] at h
      exact h
    exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne _ h2 (fun a b ha _ => absurd ha (hno a))
  · by_cases hlen : 4 * H.Lw < orderOf φ.2
    · exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow _ H.Lw hL (GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ hlen)
    · have h1 : φ ≠ 1 := by
        rintro rfl
        exact absurd (show (1 : ℤˣ) = -1 from hφ) (by decide)
      have adj : ∀ i : ZMod (orderOf φ), ¬ (Thick H (letter τ φ i) ∧ Thick H (letter τ φ (i + 1))) := fun i h =>
        UpperTheory.KStar.Words.placeOf_letter_succ_ne τ φ h1 hc i
          (GlobalTheory.T.atMostOneThick_short_orbit H τ φ (not_lt.mp hlen) (i + 1) i h.2 h.1)
      refine ⟨fun i h => adj i ⟨h.1, h.2.1⟩, ?_⟩
      by_contra hall
      have hall' : ∀ i, Thick H (letter τ φ i) := fun i => by_contra fun hi => hall ⟨i, hi⟩
      exact adj 0 ⟨hall' 0, hall' (0 + 1)⟩

end GlobalTheory.HTW.InertWord
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.satake_bound_of_isometric_sphericalGL : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | exact GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | (intros; apply GlobalTheory.LatHecke.satake_bound_of_isometric_spherical <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.block_complement_isSub_at_enlargement : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → IsSubOfSums (matRep (C.loc (WpO D.nd i ρ π))) (fun (_ : Unit) s => C.loc (rTwO D.nd i r π) s) := by
  first | exact @GlobalTheory.subWp_sub | exact GlobalTheory.subWp_sub | (intros; apply GlobalTheory.subWp_sub <;> assumption)
end
