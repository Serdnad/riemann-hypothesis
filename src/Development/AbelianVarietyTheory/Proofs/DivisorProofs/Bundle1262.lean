module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle169
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

namespace GlobalTheory.TwistPlacesObj

open GlobalTheory.QPosCompare

section Lin

variable {K X E W : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {σ : K →+* ℂ} {j : X →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)

theorem lin_injective (hj : IsForm j) {n : ℕ} (f : (Fin n → K) →ₗ[K] X) (hf : Function.Injective f)
    (hZ : ∀ y, j (f y) ∈ LinearMap.range (LinearMap.adjoint θ)) :
    Function.Injective (Formalism.IndefR.Cx.lin fun k => θ (j (f (Pi.single k 1)))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 : LinearIndependent K fun k : Fin n => f (Pi.single k 1) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    simpa [Function.comp_def] using this
  have h2 := hj.linInd h1
  set u : E := ∑ k, c k • j (f (Pi.single k 1)) with hu
  have h3 : u ∈ LinearMap.ker θ := by
    rw [Formalism.IndefR.Cx.lin_apply] at hc

    rw [LinearMap.mem_ker, hu, map_sum]
    simpa only [map_smul] using hc
  have h4 : u ∈ (LinearMap.ker θ)ᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ _)
  have h5 : u = 0 := inner_self_eq_zero.1 (h4 u h3)
  funext k
  exact Fintype.linearIndependent_iff.1 h2 c h5 k

variable {G : Type} [Group G] [Fintype G] (r : Representation K G X) (ρ : G → W →ₗ[ℂ] W)

end Lin

section Block

open Formalism.DivisionValues Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)
  {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {j : B.S.Forms →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)
  (ρ : G → W →ₗ[ℂ] W)

theorem toF_mem (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z :=
  (B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y)

end Block

section Content

open Formalism.BasicNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree.DepthCond

end Content

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isForm_tw {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ σ' : K →+* ℂ} (s : Bool) (h : ∀ a, σ' a = cj s (σ a)) {j : X →ₛₗ[σ] E} (hj : IsForm j) :
    IsForm (E := Tw s E) (Tw.semi s h j) := by
  obtain ⟨⟨n, b, h1, h2⟩, h3⟩ := hj
  refine ⟨⟨n, b, (Tw.linInd (E := E) s h1 :), ?_⟩, fun x y => ?_⟩
  · have e : Set.range (Tw.semi s h j) = Tw.mk s '' Set.range j := by rw [← Set.range_comp]; rfl
    rw [e, tw_span, h2]
    rfl
  · obtain ⟨a, ha⟩ := h3 x y
    exact ⟨a, (congrArg (cj s) ha).trans (h a).symm⟩

end Real

end GlobalTheory.TwistPlacesObj

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExt

open GlobalTheory.ConjDS GlobalTheory.LowTypeDetermined

section Gen

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realMap (T : H ≃ₗᵢ⋆[ℂ] H') : H →L[ℝ] H' where
  toFun := T
  map_add' := map_add T
  map_smul' r x := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
  cont := T.continuous

theorem smoothVec_map (T : H ≃ₗᵢ⋆[ℂ] H') (h : ∀ g v, T (σ g v) = σ' g (T v)) {L : Set (Matrix (Fin n) (Fin n) ℂ)}
    {w : H} (hw : SmoothVec L σ w) : SmoothVec L σ' (T w) := by
  intro k Xs hX
  simp only [← h]
  exact (realMap T).contDiff.comp (hw k Xs hX)

theorem lowKSub_stab {lam : Fin n → ℝ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) {w : H}
    (hw : w ∈ lowKSub ε lam σ) : σ g w ∈ lowKSub ε lam σ := by
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => (le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS) (hS.2.1 g hg x hx)
  exact this hw

theorem lowKSub_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {lam : Fin n → ℝ} {w : H} (hw : w ∈ lowKSub ε lam σ) : T.symm w ∈ lowKSub ε' (nr lam) σ' := by
  have : lowKSub ε lam σ ≤ (lowKSub ε' (nr lam) σ').comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
    refine sSup_le fun S hS x hx => ?_
    have h1 := ktype_transfer (sg_symm he) T.symm (symm_inter T h) hS
    rw [← lowK_rev he] at h1
    refine (le_sSup (s := {S | IsKTypeOf ε' σ' (Formalism.QuantumDeterminants.lowK ε' (nr lam)) S}) h1) ?_
    show T (T.symm x) ∈ S
    simpa using hx
  exact this hw

def prm (ε ε' : Fin n → Bool) : Equiv.Perm (Fin n) :=
  ((Fin.revPerm.trans (revNeg ε')).trans Fin.revPerm).trans (revNeg ε).symm

theorem revNeg_prm (a : Fin n) : revNeg ε (prm ε ε' a) = (revNeg ε' a.rev).rev := by
  simp [prm]

theorem eps_prm (he : ∀ a, ε' a = ε a.rev) (a : Fin n) : ε (prm ε ε' a) = ε a := by
  rw [← eps_revNeg ε (prm ε ε' a), revNeg_prm, ← he (revNeg ε' a.rev), eps_revNeg ε' a.rev, he, Fin.rev_rev]

theorem ext_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    (hU : IsURepOn (UJset ε) σ) {lam : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w) :
    IsWtOn (Formalism.REAL.Kset ε') σ' (fun a => Formalism.QuantumDeterminants.lowK ε' (nr lam) (revNeg ε' a))
      (T.symm (σ (pM (prm ε ε')) w)) := by
  have h1 := wt_transfer (sg_symm he) T.symm (symm_inter T h) (isWtOn_perm hU (prm ε ε') (eps_prm he) hw)
  convert h1 using 1
  funext a
  rw [lowK_rev he]
  simp [nr, revNeg_prm]

end Gen

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem conj_rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : (conjModel M).H τ) :
    cj (M.H τ) ((conjModel M).rep τ g w) = M.rep τ g (cj (M.H τ) w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj _ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj _ w)
  rw [e]

theorem smooth_translate (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ g u) := by
  obtain ⟨_, -, hσ, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) (conj_inv_mem hP h hg) hu'

theorem exists_conjModel_ext : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v : M.Vec), IsExtVec M v → ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  intro D V S M v hv
  have he : ∀ τ a, (conjModel M).ε τ a = M.ε τ a.rev := fun _ _ => rfl
  have hK := fun τ => pM_mem (prm (M.ε τ) ((conjModel M).ε τ)) (eps_prm (he τ))
  have hU : ∀ τ, IsURepOn (UJset (M.ε τ)) (M.σ τ) := fun τ => (M.ds τ).2.2.1
  let c : ∀ τ, (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := fun τ => cj (M.H τ)
  have hc : ∀ τ g y, c τ ((conjModel M).σ τ g y) = M.σ τ (rv g) (c τ y) := fun _ _ _ => rfl
  have hr : ∀ τ g y, (c τ).symm (M.rep τ g y) = (conjModel M).rep τ g ((c τ).symm y) := fun τ g y => by
    apply (c τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (conj_rep M τ g _).symm
  refine ⟨conjModel M, c, fun τ => ⟨(c τ).symm (M.σ τ (pM (prm (M.ε τ) ((conjModel M).ε τ))) (v τ)),
    Submodule.subset_span (smoothVec_map (c τ).symm (hr τ) (smooth_translate M τ (v τ) (kset_uj (hK τ))))⟩,
    fun τ g _ y => conj_rep M τ g y, fun τ => ⟨?_, ?_, ?_⟩⟩
  · rw [LinearIsometryEquiv.norm_map, (hU τ).2.1 _ (kset_uj (hK τ)), (hv τ).1]
  · exact lowKSub_transfer (he τ) (c τ) (hc τ) (lowKSub_stab (hK τ) (hv τ).2.1)
  · exact ext_transfer (he τ) (c τ) (hc τ) (hU τ) (hv τ).2.2

end GlobalTheory.ConjExt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealWeil

theorem exists_weylAlg_conj {l : Type} [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : Sch l →ₗ[ℂ] Sch l) (hI : ∀ w f, A' (dRho w f) = dRho (L' w) (A' f))
    {B : Sch l →L[ℂ] Sch l} (hB : B ∈ weylAlg l) :
    ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f) := by
  refine weylAlg_induction (P := fun B => ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f))
    ⟨1, fun f => by simp⟩ ?_ ⟨0, fun f => by simp⟩ ?_ ?_ hB
  · rintro A w ⟨B', h⟩
    refine ⟨B' * dRho (L'.symm w), fun f => ?_⟩
    have e := hI (L'.symm w) f
    rw [LinearEquiv.apply_symm_apply] at e
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← e, h]
  · rintro A B ⟨A₁, h₁⟩ ⟨B₁, h₂⟩
    exact ⟨A₁ + B₁, fun f => by simp [h₁, h₂]⟩
  · rintro c A ⟨A₁, h⟩
    exact ⟨c • A₁, fun f => by simp [h]⟩

theorem norm_toLp_le_of_lintegral_le {l : Type} [Fintype l] (A' : Sch l →ₗ[ℂ] Sch l) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) (f : Sch l) :
    ‖(A' f).toLp 2 volume‖ ≤ C.toReal ^ (1 / 2 : ℝ) * ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
    (f.eLpNorm_lt_top 2 volume).ne) ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (A' f).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (h f) (by norm_num)

end GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  intro l _ L' A' C hC h2 hI
  refine WithSeminorms.continuous_of_continuous_comp (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ) A'
    fun i => ?_
  obtain ⟨B, hB, hle⟩ := GlobalTheory.RealWeil.exists_seminorm_le (l := l) i.1 i.2
  choose B' hB' using fun r => GlobalTheory.RealWeil.exists_weylAlg_conj L' A' hI (hB r)
  let c : NNReal := Real.toNNReal (C.toReal ^ (1 / 2 : ℝ))
  let q : Seminorm ℂ (GlobalTheory.RealWeil.Sch l) := ∑ r, c • (normSeminorm ℂ (GlobalTheory.RealWeil.L2 l)).comp
    ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).toLinearMap
  refine Seminorm.continuous_of_le (q := q) (Seminorm.continuous_finsetSum fun r _ => ?_) fun f => ?_
  · change Continuous fun f => (c : ℝ) * ‖(GlobalTheory.RealWeil.schwartzToL2 l) (B' r f)‖
    exact continuous_const.mul (continuous_norm.comp ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).continuous)
  · have e : q f = ∑ r, (c : ℝ) * ‖(B' r f).toLp 2 volume‖ := by
      simp [q, GlobalTheory.RealWeil.schwartzToL2_apply, NNReal.smul_def, smul_eq_mul]
    rw [e]
    change SchwartzMap.seminorm ℂ i.1 i.2 (A' f) ≤ _
    refine (hle (A' f)).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [hB']
    refine (GlobalTheory.RealWeil.norm_toLp_le_of_lintegral_le A' C hC h2 _).trans (le_of_eq ?_)
    rw [show (c : ℝ) = C.toReal ^ (1 / 2 : ℝ) from Real.coe_toNNReal _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

end
end

section

noncomputable section

open Matrix MvPolynomial ComplexConjugate
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.CurvatureSesquilinearExpansion

theorem eq_sum_coordVec {n : ℕ} (v : V n) : v = ∑ a, v.ofLp a • coordVec a := by
  ext j
  simp [Pi.single_apply]

theorem sesq_expand {n : ℕ} (F : V n → V n → ℂ)
    (h1 : ∀ x y z, F (x + y) z = F x z + F y z) (h2 : ∀ (c : ℂ) x z, F (c • x) z = c * F x z)
    (h3 : ∀ x y z, F x (y + z) = F x y + F x z)
    (h4 : ∀ (c : ℂ) x z, F x (c • z) = conj c * F x z) (ξ η : V n) :
    F ξ η = ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * F (coordVec a) (coordVec b) := by
  have s1 (z : V n) (f : Fin n → V n) : F (∑ a, f a) z = ∑ a, F (f a) z :=
    map_sum (AddMonoidHom.mk' (fun x => F x z) fun x y => h1 x y z) f Finset.univ
  have s2 (x : V n) (f : Fin n → V n) : F x (∑ a, f a) = ∑ a, F x (f a) :=
    map_sum (AddMonoidHom.mk' (fun z => F x z) fun y z => h3 x y z) f Finset.univ
  conv_lhs => rw [eq_sum_coordVec ξ, eq_sum_coordVec η, s1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h2, h4, mul_assoc]

theorem curv_expand {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {z : V n}
    (h : MContDiffAt 2 G z) (hu : IsUnit (G z).det) (ξ η : V n) (i j : r) :
    curv G z ξ η i j =
      ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * curv G z (coordVec a) (coordVec b) i j := by
  have m1 (x y w : V n) : mddbar G z (x + y) w = mddbar G z x w + mddbar G z y w := by
    ext a b; simp
  have m2 (c : ℂ) (x w : V n) : mddbar G z (c • x) w = c • mddbar G z x w := by
    ext a b; simp
  have m3 (x y w : V n) : mddbar G z x (y + w) = mddbar G z x y + mddbar G z x w := by
    ext a b; simp
  have m4 (c : ℂ) (x w : V n) : mddbar G z x (c • w) = conj c • mddbar G z x w := by
    ext a b; simp
  refine sesq_expand (fun ξ η => curv G z ξ η i j) ?_ ?_ ?_ ?_ ξ η
  · intro x y w
    simp only [curv_eq h hu, mdel_add_vec, m1, transpose_add, Matrix.mul_add, Matrix.sub_apply,
      Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdel_smul_vec, m2, transpose_smul, Matrix.mul_smul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · intro x y w
    simp only [curv_eq h hu, mdbar_add_vec, m3, transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdbar_smul_vec, m4, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem curvPoly_pullback : (let d1 : {n n' : ℕ} → (ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) → MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ := @(fun {n n' : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) ↦ MvPolynomial.aeval fun (x : Fin n × Fin n) ↦ ∑ c : Fin n', ∑ d : Fin n', (MvPolynomial.C : (fun (x : Fin n) ↦ ℂ) (Prod.fst x) → MvPolynomial (Fin n' × Fin n') ((fun (x : Fin n) ↦ ℂ) (Prod.fst x))) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec c)) (Prod.fst x) * (starRingEnd ℂ : ℂ → ℂ) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec d)) (Prod.snd x))) * MvPolynomial.X (c, d)); ∀ {n n' : ℕ} {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] {G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {φ : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n} {w : ReciprocityTheory.L2DbarEstimates.V n'}, ContDiffAt ℂ (2 : WithTop ℕ∞) φ w → GlobalTheory.HermFrame.MContDiffAt ((⊤ : ℕ∞) : WithTop ℕ∞) G (φ w) → IsUnit (Matrix.det (G (φ w))) → GlobalTheory.GoodMetric.curvPoly (fun (x : ReciprocityTheory.L2DbarEstimates.V n') ↦ G (φ x)) w = (AlgHom.mapMatrix (d1 (fderiv ℂ φ w)) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) → Matrix r r (MvPolynomial (Fin n' × Fin n') ℂ)) (GlobalTheory.GoodMetric.curvPoly G (φ w))) := by
  intro d1 n n' r _ _ G φ w hφ hG hu
  have h2 : MContDiffAt 2 G (φ w) := hG.of_le (by norm_cast)
  refine Matrix.ext fun i j => ?_

  simp only [d1, curvPoly, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
  aeval_X, aeval_C, algebraMap_eq, curv_comp_holo h2 hu hφ, Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [curv_expand h2 hu (fderiv ℂ φ w (coordVec c))]

  simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CurvatureSesquilinearExpansion
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lam_triv_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL A L x → Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) := by
  intro S A _ hA L hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (fst A T) (snd A T ≫ x))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (fst A T) (snd A T ≫ x)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd A T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hA T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, e, lift_fst, lift_snd_assoc, Category.id_comp, lam_one_left]
  · intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    obtain ⟨W, hW, hw⟩ := exists_pull_eq_zero
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    let U := (snd A T).left ⁻¹ᵁ (V ⊓ W)
    let Y : Over S := Over.mk (U.ι ≫ (A ⊗ T).hom)
    let i : Y ⟶ A ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, e]
    have ht : ∀ z, (i ≫ snd A T).left z ∈ V := fun z ↦ z.2.1
    have h1 := pull_mul_eq hL hTV (i ≫ snd A T) ht (i ≫ fst A T)
    have h2 : CechPic.pull (i ≫ snd A T).left
        (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) = 0 :=
      pull_eq_zero_of_mem W (i ≫ snd A T).left (fun z ↦ z.2.2) hw
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      Category.assoc] at h2
    rw [lam, mul_comm (i ≫ fst A T), ← Category.assoc i (snd A T) x, h1, Category.assoc, sub_self, zero_sub,
      neg_add_eq_zero]
    exact (sub_eq_zero.1 h2)

end GlobalTheory.DualCon
end
end
