module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle053
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibility
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle009
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle191
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle307
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle057
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle081
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle304
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle146
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.WeilBound.CoreStatements.FlagImmersions.AevalEqZeroOfMem
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007

@[expose] public section

section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem sq_of (hT : StTie) (hCmp : StCmp) : StSq := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hX hII hp hq B a
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := TowerPropA.mono_spMap_ringOfIntegers c.F
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.toTowerOrigin.S B := by
    intro p hp hdv
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hdv 2) _
  obtain ⟨M', t, d, S, K, _, ι, _, P, Re, hgen, hR, hdeg, hpos, hS, hF, hPB⟩ :=
    hT hG hW E H D l (Xo l) c Y (o.S B) _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ (o.Or B a).𝔐.S_prime hdisc hp hq
  obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.root_model_origin_compatibility E H D l (Xo l) c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx hmono (hX.1 a)
  obtain ⟨f₁, f₂⟩ := hCmp hIn hC II hII E H D l (Xo l) c _ _ Y _ _ _ _ t
    (RootFieldNumerics.Sq.tieOf (o.Or B a) ((o.Sys a).reg none).1 (o.omVB B a) t.discr hA) hmono hgen
    (fun p hp => (hX.2 B a p hp).trans (hR p hp).symm) hdeg (o.Or B a).Re_deg
  refine ⟨t.Fl.deg, d, S, K, _, ι, _, P, Re, Nat.cast_pos.2 hpos, by rw [o.j_eq]; exact hF, ?_, hS.trans f₂⟩
  rw [hPB II, f₁, map_smul]
  rfl

end SquareStatements
end
end

section

noncomputable section

namespace SquareStatements

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp RootFieldNumerics.Sq
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem cmp_arith {a b e₁ e₂ d₁ d₂ m : ℝ} (p₁ : e₁ ≠ 0) (p₂ : e₂ ≠ 0) (hm : m ≠ 0) (h : e₁ * (m * d₁) = e₂ * d₂) :
    (a / d₁ - (e₁ * a - e₂ * b) / (e₁ * d₁)) / m = b / d₂ := by
  rw [sub_div (e₁ * a), mul_div_mul_left _ _ p₁, sub_sub_cancel, div_div, show e₁ * d₁ * m = e₂ * d₂ by rw [← h]; ring,
    mul_div_mul_left _ _ p₂]

theorem poly_smul_of_sameSing (hN : SheetDecomposition.NumPull) (hIn : PB.Inputs) (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k}
    {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {σ : Type} [Fintype σ] {S₁ S₂ : PB.AnSys D σ}
    {P₁ : Ideal (MRing ι₁)} {P₂ : Ideal (MRing ι₂)} (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) {β : MRing ι} {b : K → ℕ}
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a)
    (hne : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (hdeg : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * (m * Re₁.deg) =
      IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) * Re₂.deg) :
    Re₁.PB II = (m : ℝ) • Re₂.PB II ∧ S₁.degPoly = (m : ℝ) • S₂.degPoly := by
  have hne' : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0 :=
    left_ne_zero_of_mul (hdeg ▸ mul_ne_zero hne (mul_ne_zero hm Re₁.deg_pos.ne'))
  have hW := PairTop.cmpSt_of_eq hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ P₁ P₂ Re₁ Re₂ h₁ h₂ β b hv₁ hv₂ hy hβ hβy
    hA₁ hA₂ hS
  have hG := fun w : Fin D → σ => intNum_cmp hN y hv₁ hv₂ hy hne hne' (fun j => (Re₁.ref (w j)).a) (fun j => (Re₂.ref (w j)).a)
    fun j => (hS (w j)).imp fun f => Exists.imp fun g h => h.1
  rw [h₁, h₂] at hG
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = e₁ at *
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = e₂ at *
  have hdeg' : (e₁ : ℝ) * (m * Re₁.deg) = e₂ * Re₂.deg := by exact_mod_cast hdeg
  have p₁ : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have p₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  have q₁ : (Re₁.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re₁.deg_pos.ne'
  have pm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  constructor
  · rw [PB.Realis.PB, PB.Realis.PB, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly (D + 1)) (funext fun w => ?_)
    obtain ⟨C₃, s₀, -, h⟩ := GlobalTheory.T.agreement_positive hIn D σ S₁ 0 (S₁.reg (w 0)).1
    have c₁ := (h II hII _ _ _ Re₁).1 w
    have c₂ : Tendsto (fun t => Re₂.num II t w) (𝓝[>] 0) (𝓝 (Re₁.limNum II w / m)) := by
      have := (c₁.sub ((hW w).div_const ((e₁ : ℝ) * Re₁.deg))).div_const (m : ℝ)
      rw [zero_div, sub_zero] at this
      refine this.congr fun t => ?_
      exact cmp_arith p₁ p₂ pm hdeg'
    rw [show Re₂.limNum II w = _ from c₂.limUnder_eq, mul_div_cancel₀ _ pm]
  · rw [PB.AnSys.degPoly, PB.AnSys.degPoly, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly D) (funext fun w => ?_)
    have h := congrArg (Int.cast : ℤ → ℝ) (hG w)
    push_cast at h
    rw [← degNum_eq hIn Re₁, ← degNum_eq hIn Re₂, ← mul_assoc, ← mul_assoc, ← hdeg'] at h
    exact mul_left_cancel₀ (mul_ne_zero p₁ q₁) (h.trans (by ring))

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem stCmp : StCmp := by
  intro hIn hC II hII E _ _ _ H D l Xo c O _ β Y S n M M' T T' hβ hgen hR hd hd'
  classical
  have hm : T.Fl.deg ≠ 0 := by
    obtain ⟨_, _, -, -, -, -, -, -, -, -, h, -⟩ := T.Fl.generic
    exact h.ne'
  have hsab : SABMap (twistSAB Xo.univ.t (HostAut.refl H)) Xo.univ.t (Iso.refl Xo.X).hom := by
    rw [(twistSAB_symm_refl E H Xo.X Xo.univ.t (HostAut.refl H)).2.2]
    exact (exists_sabMap_id E H Xo.X Xo.univ.t).choose
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt GlobalTheory.T.theta_uniformisation_complex_abelian_varieties E H D l Xo c O β Y (HostAut.refl H) (Iso.refl Xo.X) hsab (Equiv.refl _) S n M M' T T'
      hβ (by simp) (fun τ => by ext; rfl)
      (Indep.imageCpt_refl_of_genPt E H D l Xo c O β Y S _ _ _ _ _ _ _ _ T.A T'.A hβ hgen) hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  choose Lr hLr using fun r => (hJ.1 (T.sing r)).exists
  choose Lr' hLr' using fun r => (hJ'.1 (T'.sing r)).exists
  refine poly_smul_of_sameSing SheetDecomposition.numPull hIn hC II hII T.Re T'.Re hP hP' hbv hbv' harith hmh hb T.alg T'.alg (fun a => ?_) hne hm
    (by rw [hd, hd', mul_one, hdeg])
  exact GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy T'.Sy T.Re T'.Re b a a _ _ _ _ hbv hbv'
    (hc4 _ _ κ v _ _ _ _ hbv hLr) (hc4 _ _ κ' v' _ _ _ _ hbv' hLr') (T.ref_deg a) (T'.ref_deg a) (T.sing_eq a)
    (T'.sing_eq a) hmpp (hc1 _ Lr Lr' _ fun r => hiso r _ _ (hLr r) (hLr' r))

end SquareStatements
end
end
