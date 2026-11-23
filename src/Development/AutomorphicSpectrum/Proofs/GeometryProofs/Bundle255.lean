module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle252
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Unimod

theorem mem_of_unimodular {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (Ef : LinearMap.BilinForm ℤ Λ) (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im)
    (hB : Function.Bijective Ef) (w : Fin g → ℂ)
    (hw : ∀ l : Λ, ∃ k : ℤ, (hermForm Hm w l).im = k) : w ∈ Λ := by
  have addR : ∀ (v x y : Fin g → ℂ), hermForm Hm v (x + y) = hermForm Hm v x + hermForm Hm v y := fun v x y => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have addL : ∀ (v v' x : Fin g → ℂ), hermForm Hm (v - v') x = hermForm Hm v x - hermForm Hm v' x := fun v v' x => by
    simp [hermForm, sub_dotProduct]
  have smulR : ∀ (v x : Fin g → ℂ) (r : ℝ), hermForm Hm v (r • x) = r * hermForm Hm v x := fun v x r => by
    have e : star (r • x) = (r : ℂ) • star x := by
      ext i
      simp
    simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  choose k hk using hw
  have kadd : ∀ a b : Λ, k (a + b) = k a + k b := fun a b => by
    have h := hk (a + b)
    rw [Submodule.coe_add, addR, Complex.add_im, hk a, hk b] at h
    exact_mod_cast h.symm
  let ℓ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' k kadd).toIntLinearMap
  obtain ⟨c, hc⟩ := hB.2 ℓ
  have hv : ∀ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)), (hermForm Hm (w - c) x).im = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h := hE c ⟨x, hx⟩
      have h' : Ef c ⟨x, hx⟩ = k ⟨x, hx⟩ := LinearMap.congr_fun hc _
      rw [addL, Complex.sub_im, ← h, h']
      have := hk ⟨x, hx⟩
      simp only at this
      rw [this, sub_self]
    | zero => simp [hermForm]
    | add x y _ _ hx hy => rw [addR, Complex.add_im, hx, hy, add_zero]
    | smul r x _ hx => rw [smulR, Complex.im_ofReal_mul, hx, mul_zero]
  have hI : (hermForm Hm (w - c) (Complex.I • (w - c))).im = 0 := hv _ (by rw [hfull]; trivial)
  have hv0 : w - (c : Fin g → ℂ) = 0 := by
    by_contra hne
    have hp := hpos _ hne
    have e : star (Complex.I • (w - (c : Fin g → ℂ))) = (-Complex.I) • star (w - (c : Fin g → ℂ)) := by
      ext i
      simp
    have e' : hermForm Hm (w - c) (Complex.I • (w - c)) = -Complex.I * hermForm Hm (w - c) (w - c) := by
      simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [e'] at hI
    have : (hermForm Hm (w - c) (w - c)).re = 0 := by simpa using hI
    exact hp.ne' this
  rw [sub_eq_zero.1 hv0]
  exact c.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem exists_compare (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) :
    ∃ (g' : ℕ) (Λ₀ : Submodule ℤ (Fin g' → ℂ)) (H₀ : Matrix (Fin g') (Fin g') ℂ) (χ₀ : Λ₀ → ℂ)
      (Ef : LinearMap.BilinForm ℤ Λ₀) (F : (Fin D.g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ : ∀ l ∈ a.u.Λ, F l ∈ Λ₀),
      Submodule.span ℝ (Λ₀ : Set (Fin g' → ℂ)) = ⊤ ∧
      (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) ∧
      (∀ x y : Λ₀, (Ef x y : ℝ) = (hermForm H₀ x y).im) ∧ Function.Bijective Ef ∧
      (∀ l : Λ₀, χ₀ l = 1 ∨ χ₀ l = -1) ∧
      (∀ z w, hermForm a.Hm z w = hermForm H₀ (F z) (F w)) ∧
      (∀ l : a.u.Λ, a.χ l = χ₀ ⟨F l, hΛ l l.2⟩) ∧
      (∀ z, F z ∈ Λ₀ → z ∈ a.u.Λ) ∧ Function.Surjective F := by
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨hpr, hamp, hkt⟩ := D.princ
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left := GeometricallyConnected.connectedSpace D.tK.G.hom D.tK.G.hom.isOpenMap
  obtain ⟨gd, hgd⟩ := exists_dim_of_preconnected D.tK.G.hom (Classical.arbitrary _)
  let P₀ : Out.PolAV (Sp L) :=
    { A := D.tK.G, g := gd, smoothDim := hgd, L := D.tK.PP.L, isLB := D.tK.PP.isLB, ample := hamp, ktriv := hkt
      isAb := ⟨D.tK.semi.comm, D.tK.semi.smooth, hpr, D.tK.semi.geomConnected⟩
      rigid := GlobalTheory.ObjDim.rigidified
      sym := GlobalTheory.ObjDim.sym }
  obtain ⟨P', ψ, hψ, -, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds (Sp L) (Sp ℂ) (spMap σ) P₀
  have hpb : IsGrpPullback P'.A D.tK.G (spMap σ) ψ := by
    refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hψ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hψ.w y), ← hm]
    rfl
  have hpc : IsGrpPullback P'.A D.t.G (emb σ) (ψ ≫ D.m.φ) :=
    (hpb.comp D.m.cart).congr (by rw [spMap_comp_spMap]) rfl
  obtain ⟨e, hmon, he⟩ := grpPullback_iso a.cart hpc
  haveI := hmon
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u₀, H₀, χ₀, Ef, hu₀, -, hv, hw, -, -, hE, hB, -⟩ := GlobalTheory.thetaUnifAV_closed P' rig hrig
  have hol : IsHolTo (Set.univ : Set (Fin D.g → ℂ)) (fun w => (a.u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (Flat.PerGram.isHolTo_ex a.u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P'.A P'.isAb P'.L P'.g D.g u₀ hv hw
    (fun w => a.u.ex w ≫ e.hom) (fun p q => by rw [a.u.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ a.u.Λ, F l ∈ u₀.Λ := fun l hl => (u₀.ker _).1 (by
    rw [hF, (a.u.ker l).2 hl, MonObj.one_comp])
  have back : ∀ z, F z ∈ u₀.Λ → z ∈ a.u.Λ := fun z hz => (a.u.ker z).1 (by
    have h := (u₀.ker _).2 hz
    rw [hF] at h
    have h' := congrArg (· ≫ e.inv) h
    simpa [MonObj.one_comp] using h')
  have hsurj : Function.Surjective F := by
    haveI := u₀.discrete
    refine LinearMap.range_eq_top.1 (GlobalTheory.AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => ?_)
    obtain ⟨z, hz⟩ := a.u.ex_onto (u₀.ex w ≫ e.inv)
    have hz' : u₀.ex (F z) = u₀.ex w := by
      rw [hF, hz, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hz'] at h
    exact ⟨⟨w - F z, (u₀.ker _).1 (mul_eq_right.1 h.symm)⟩, z, by simp⟩
  have i₁ : LBIso P'.L (D.tK.PP.L.pull ψ) := LBIso.symm ⟨t, ht⟩
  have i₂ : LBIso D.tK.PP.L (D.t.PP.L.pull D.m.φ) := by
    obtain ⟨w, hw, -⟩ := D.m.lin
    exact ⟨w, hw⟩
  have i₃ : LBIso (D.tK.PP.L.pull ψ) (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₂ ψ rfl
  have i₄ : LBIso P'.L (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    LBIso.trans P'.isLB (pull_isLB D.tK.PP.isLB _) (pull_isLB D.t.PP.isLB _) i₁ i₃
  have i₅ : LBIso (P'.L.pull e.hom.left) (D.t.PP.L.pull a.φ) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₄ e.hom.left he.symm
  have iso : LBIso (lbPow (D.t.PP.L.pull a.φ) 1) (lbPow (P'.L.pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (LBIso.symm i₅) 1
  obtain ⟨hH, hχ⟩ := GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull a.A P'.A _ P'.L D.g P'.g a.u u₀ a.Hm H₀ a.χ χ₀
    e.hom F hΛ 1 one_pos hLφ P'.isLB a.ah hu₀ hF iso
  exact ⟨P'.g, u₀.Λ, H₀, χ₀, Ef, F, hΛ, u₀.full, hu₀.2.1, hE, hB,
    GlobalTheory.ThetaUnifCompare.chi_eq_one_or_of_sym P'.isLB P'.sym hu₀, hH, fun l => by simpa using hχ l, back, hsurj⟩

theorem frame_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) ∧ (∀ w : Fin D.g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) ∧ (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) ∧ ∀ l : a.u.Λ, a.χ l ^ 2 = 1 := by
  intro E _ _ _ H L _ _ D σ a
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨g', Λ₀, H₀, χ₀, Ef, F, hΛ, hfull, hpos, hE, hB, hχ₀, hH, hχ, back, hsurj⟩ := exists_compare D σ a
  refine ⟨fun l l' => ?_, fun w hw => ?_, fun l l' => GlobalTheory.FrameValue.chi_add hLφ a.ah l l', fun l => ?_⟩
  · obtain ⟨n, hn⟩ := GlobalTheory.FrameValue.exists_int_im hLφ a.ah l l'
    exact ⟨n, hn.symm⟩
  · refine back w (mem_of_unimodular Λ₀ hfull H₀ hpos Ef hE hB (F w) fun l₀ => ?_)
    obtain ⟨z, hz⟩ := hsurj l₀
    have hzΛ : z ∈ a.u.Λ := back z (hz ▸ l₀.2)
    obtain ⟨k, hk⟩ := hw ⟨z, hzΛ⟩
    refine ⟨k, ?_⟩
    rw [← hz, ← hH]
    exact hk
  · rw [hχ l]
    rcases hχ₀ ⟨F l, hΛ l l.2⟩ with h | h <;> simp [h]

end GlobalTheory.CompanionTheory.Ar.Sl.Unimod
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in
theorem exists_sec_ne_zero_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  intro E _ _ _ H L _ _ D
  have hS : SecBaseChangeAnySt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  obtain ⟨hprop, hamp, hkt⟩ := D.princ
  have eid : spMap (RingHom.id L) = 𝟙 (Sp L) := by
    simp [spMap]
  have hpb : IsPullback (𝟙 D.tK.G.left) D.tK.G.hom D.tK.G.hom (spMap (RingHom.id L)) := by
    rw [eid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : LB.Sec D.tK.PP.L, ¬ ∀ y j, (𝟙 D.tK.G.left : D.tK.G.left ⟶ D.tK.G.left) y ∈ D.tK.PP.L.U j →
      gs (𝟙 D.tK.G.left) y _ (β.f j) = 0 := exists_sec_ne hS
    { A := D.tK.G, g := d, smoothDim := hd, L := D.tK.PP.L, isLB := D.tK.PP.isLB
      ample := hamp
      ktriv := hkt
      isAb := ⟨inferInstance, inferInstance, hprop, ‹_›⟩
      rigid := ⟨D.tK.PP.rig, D.tK.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } (RingHom.id L) hpb
  obtain ⟨w, gw', -⟩ := D.m.lin
  have := D.t.semi.separated
  have := D.t.semi.quasiCompact
  have : CompactSpace D.t.G.left := QuasiCompact.compactSpace_of_compactSpace D.t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (nonZeroDivisors (𝓞 L)) D.m.cart.1 D.t.PP.isLB D.tK.PP.isLB
    ((isGen_iff w).1 gw') β
  obtain ⟨w₁, hw₁⟩ := exists_iso_linComb (F := 𝟙 D.t.G.left) D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  have hM := linComb_isLB D.t.PP.L D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 D.t.G.left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨τ, hτ⟩ := sec_pull_down ((isGen_iff w₁).1 hw₁) D.t.PP.isLB hM σ
  refine ⟨τ, fun h0 => hβ fun y k hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart D.t.PP.isLB (D.m.φ y)
  obtain ⟨k', hk'⟩ := exists_chart hM (D.m.φ y)
  have hz : LB.Sec.f τ k' = 0 := congrArg (fun s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ))) => LB.Sec.f s k') h0
  have e₁ := hτ _ D.m.φ y j k' hj hk'
  rw [hz, gs_zero _ y _ hk', mul_zero, Category.comp_id] at e₁
  have e₂ := hσ y j k hj hk
  rw [e₁, D.m.cart.1.w, cst_comp] at e₂
  have ha' : algebraMap (𝓞 L) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero ha)
  have u₁ : IsUnit (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)) :=
    IsUnit.of_mul_eq_one (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)⁻¹) (by
      rw [← cst_mul, mul_inv_cancel₀ ha', cst_one])
  exact (Units.isUnit _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.RdGeo

theorem frame_of_geoRead {P : Prop} : P → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : _root_.GlobalTheory.CompanionTheory.Ar.Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd), letI := Small.cstAlg (o.toTowerOrigin.Or B b); ∃ (φ : Om Z →ₐ[c.F] (T.M B b).Ω) (P : FrPt Xo c (T.M B b).Ω) (t : Ix Dw → ((T.M B b).Ω)ˣ), (∀ x, φ x = Rd.φ x) ∧ FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ ∀ i, i ≠ none → t i = Rd.t i := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y _ T o B b Fr Z Rd hg
  let := Small.cstAlg (o.toTowerOrigin.Or B b)
  obtain ⟨y', hm, hb⟩ := hg
  exact ⟨{ Rd.φ with commutes' := Rd.φ_cst }, y', Rd.t, fun _ => rfl, hm, hb, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Plug.RdGeo
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}

noncomputable def pullPolL (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

theorem isDerivAt0_zero_of_fixed {g : ℕ} {Y : Scheme.{0}} {F : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    {v : Sp (DualNumber ℂ) ⟶ Y} (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = F 0)
    (hv : spMap (epsMul (0 : ℂ)) ≫ v = v) : IsDerivAt0 F 0 v := by
  refine ⟨h0, fun U h f => ?_⟩
  rw [map_zero]
  have key : ∀ (v' : Sp (DualNumber ℂ) ⟶ Y) (_ : v' = spMap (epsMul (0 : ℂ)) ≫ v) (h' : ⊤ ≤ v' ⁻¹ᵁ U),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v'.appLE U ⊤ h').hom f)) = 0 := by
    rintro _ rfl h'
    have hs := ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE (CommRingCat.ofHom (epsMul (0 : ℂ))) v U h' h
    have := ConcreteCategory.congr_hom hs f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    simp [epsMul]
  exact key v hv.symm h

theorem isHolTo_slice {n g : ℕ} {B : Set (Fin n → ℂ)} {Y : Scheme.{0}}
    {F : (Fin n → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo (B ×ˢ Set.univ) F) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z : Fin g → ℂ => F (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun z : Fin g → ℂ => (b, z)) := by fun_prop
  have hmem : ∀ z, z ∈ {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} →
      (b, z) ∈ {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩
  have hset : {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} =
      (fun z => (b, z)) ⁻¹' {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨hmem z, fun hz => ⟨trivial, hz.2⟩⟩
  refine ⟨hset ▸ h1.preimage hc, fun z hz => ?_⟩
  have hd := (h2 _ (hmem z hz)).differentiableAt (h1.mem_nhds (hmem z hz))
  have hi : DifferentiableAt ℂ (fun z : Fin g → ℂ => (b, z)) z := by fun_prop
  exact (DifferentiableAt.comp z hd hi).differentiableWithinAt

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (Mz : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) (x : Fin g → ℂ) :
    IsDerivAt0 (fun z => (e.ex b z).left) x (Mz.pt x).left := by
  have h1 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have h0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left := congrArg (·.left) h1
  have hbas : ∀ i, IsDerivAt0 (fun z => (e.ex b z).left) (Pi.single i 1) (Mz.pt (Pi.single i 1)).left := fun i => by
    have h := e.diff b hb i
    have h' := hL i
    change _ ≫ _ = _ ≫ _ at h'
    rw [Category.comp_id] at h'
    rwa [← h'] at h
  have hsc : ∀ (c : ℂ) i, IsDerivAt0 (fun z => (e.ex b z).left) (c • Pi.single i 1)
      (Mz.pt (c • Pi.single i 1)).left := fun c i => by
    rw [Mz.smul]
    exact isDerivAt0_smul (hbas i) c
  have hzero : IsDerivAt0 (fun z => (e.ex b z).left) 0 (Mz.pt 0).left := by
    refine isDerivAt0_zero_of_fixed ((Mz.tan 0).trans h0.symm) ?_
    have := Mz.smul 0 0
    rw [zero_smul] at this
    exact this.symm
  have hsum : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left) (∑ i ∈ s, x i • Pi.single i 1)
      (Mz.pt (∑ i ∈ s, x i • Pi.single i 1)).left := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Mz.add]
      exact UnifCompare.isDerivAt0_mul h0 (hsc _ _) ih
  have hx : ∑ i, x i • (Pi.single i 1 : Fin g → ℂ) = x := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := hsum Finset.univ
  rwa [hx] at this

theorem isDiff_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp ℂ))
    (hP : IsPrincipal t) {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ t.G.left} (hφ : IsGrpPullback A t.G (𝟙 _) φ)
    {g' : ℕ} (u : HolUnif A (t.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (hA : u.IsAH Hm χ)
    {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w w' : Fin g' → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  obtain ⟨hpr, ham, hk⟩ := hP
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  let Q : Out.PolAV (Sp ℂ) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk
      isAb := ⟨inferInstance, inferInstance, hpr, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym }
  have hφ' : IsGrpPullback A Q.A (𝟙 _) φ := hφ
  obtain ⟨-, -, -, -, t1, -, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all
    (GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol.pullPolL Q hφ') g' u Hm χ hA
  exact (t1 v hv).unique h h'

theorem isDiff_eq_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) → ∀ (x : Fin g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v' : epsR ℂ ⟶ A) (w : Fin g' → ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → v'.left ≫ φ = (v ≫ P.τ.q ≫ P.e.hom).left → u.IsDiff w v' → w = ℓ x := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hφ hA hP hl Mz hL x v v' w hv hv' hw
  have Hc := P.m.cart.1
  have hex : ∀ y, ∃ s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G, s.left ≫ P.m.φ = (e.ex b y).left := fun y =>
    ⟨Over.homMk (Hc.lift (e.ex b y).left (𝟙 _) (by simpa using Over.w (e.ex b y))) (Hc.lift_snd _ _ _),
      Hc.lift_fst _ _ _⟩
  choose s hs using hex
  have hd1 := isDerivAt0_pt e hb Mz hL x
  have hFeq : (fun z => (s z).left ≫ P.m.φ) = fun z => (e.ex b z).left := funext hs
  have hd2 : IsDerivAt0 (fun z => (s z).left) x v.left :=
    GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback Hc (fun z => Over.w (s z))
      (by rw [hFeq]; exact isHolTo_slice e.hol hb) (by simpa using Over.w v) (by rw [hFeq, hv]; exact hd1)
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  have hd3 := isDerivAt0_comp_hom hd2 ((P.τ.q ≫ P.e.hom).left ≫ inv φ)
  have e1 : v.left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ = v'.left := by
    rw [← Category.assoc, ← Over.comp_left, ← hv', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : (fun z => (s z).left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ) = fun z => (u.ex (ℓ z)).left :=
    funext fun z => by
      rw [← Category.assoc, ← Over.comp_left, ← hl z (s z) (hs z), Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
  rw [e1, e2] at hd3
  have hz : (u.ex (ℓ 0)).left = η[A].left := by
    rw [map_zero]
    exact GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u
  have htan : IsTangent v' := hd3.1.trans hz
  have hdiff : u.IsDiff (ℓ x) v' := fun U h f => by
    refine (hd3.2 U h f).trans ?_
    have hU : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      have := tangent_open_preimage_zero hd3 U h
      simpa using this
    have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (ℓ.toContinuousLinearMap 0) := by
      rw [map_zero]
      exact ((u.hol U f).2 0 hU).differentiableAt ((u.hol U f).1.mem_nhds hU)
    have := fderiv_comp (𝕜 := ℂ) (0 : Fin g → ℂ) hd ℓ.toContinuousLinearMap.differentiableAt
    show fderiv ℂ ((fun z => valAt' (u.ex z).left U f) ∘ ℓ.toContinuousLinearMap) 0 x = _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, map_zero]
    rfl
  exact isDiff_unique P.tB hP hφ u Hm χ hA htan hw hdiff

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL
end

section


theorem _root_.GlobalTheory.T.CmpHodgeTied_holds : GlobalTheory.CompanionTheory.Ar.HodgeComparisonCompatibility :=
  PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt
end
