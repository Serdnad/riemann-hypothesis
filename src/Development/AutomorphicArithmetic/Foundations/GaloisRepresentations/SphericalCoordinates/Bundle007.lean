module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle682
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem flat_of_eventuallyEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}}
    {s s' : V → (Sp ℂ ⟶ Y)} {v₀ w : V} (h : s =ᶠ[𝓝 v₀] s') (hf : Flat s v₀ w) : Flat s' v₀ w := by
  intro U f hU
  have h0 : s v₀ = s' v₀ := h.eq_of_nhds
  have hfd : fderiv ℂ (fun v => valAt' (s' v) U f) v₀ = fderiv ℂ (fun v => valAt' (s v) U f) v₀ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h] with v hv
    rw [hv]
  rw [hfd]
  exact hf U f (h0 ▸ hU)


theorem UpperTheory.Gal.W2.ptImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.ExpImm → UpperTheory.Gal.W2.PtImm := by
  intro hComp hPre hPF hExp O _ bar g ρ D X s A _ S k m B P b₀ hB hb₀ hP hu z₀ w hw
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hmem : (b₀, z₀) ∈ B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) := ⟨hb₀, Set.mem_univ _⟩
  have hnhds : B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) ∈ 𝓝 (b₀, z₀) := hBU.mem_nhds hmem
  have hS := S.hol m B P hB hP
  have hw1 : w.1 = 0 := by
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left X (KS.pow A k).hom
      (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.u (P bz.1)) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
    have hfst : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => bz.1)
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)) (b₀, z₀) := hasFDerivAt_fst
    have h3 : Flat (fun b => S.u (P b)) b₀
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ) w) :=
      (hPre (Fin m → ℂ) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X B (fun b => S.u (P b)) hS.1
        (fun bz => bz.1) (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ))
        (b₀, z₀) w hfst hb₀).mp h2
    exact hu _ h3
  have hw2 : ∀ j, w.2 j = 0 := by
    intro j
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left A.left
      (Over.Hom.left (KS.pr A j)) (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) =>
        Over.Hom.left (S.ex (P bz.1) (bz.2 j))) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
    let L : (Fin m → ℂ) × (Fin k → Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
      (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)).prod
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Fin g → ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)))
    have hL : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => (bz.1, bz.2 j)) L (b₀, z₀) :=
      L.hasFDerivAt
    have hmem2 : ((b₀, z₀).1, (b₀, z₀).2 j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h3 : Flat (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => Over.Hom.left (S.ex (P bz.1) bz.2))
        (b₀, z₀ j) (L w) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun bz => (bz.1, bz.2 j)) L (b₀, z₀) w hL hmem2).mp h2
    have hLw : L w = (0, w.2 j) := by
      simp [L, hw1]
    rw [hLw] at h3
    have hι : HasFDerivAt (fun z : Fin g → ℂ => (b₀, z))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) (z₀ j) :=
      (hasFDerivAt_const b₀ (z₀ j)).prodMk (hasFDerivAt_id (z₀ j))
    have hmem3 : (fun z : Fin g → ℂ => (b₀, z)) (z₀ j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h4 : Flat (fun z : Fin g → ℂ => Over.Hom.left (S.ex (P b₀) z)) (z₀ j) (w.2 j) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) (Fin g → ℂ) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun z => (b₀, z)) (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ))
        (z₀ j) (w.2 j) hι hmem3).mpr h3
    exact hExp X A g (S.u (P b₀)) (S.ex (P b₀)) (S.exp _ (hP.1 _ hb₀)) (z₀ j) (w.2 j) h4
  exact Prod.ext hw1 (_root_.funext hw2)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem tanDeriv_of : TanDeriv := by
  intro V _ _ Y s' B s v₀ hB hv₀ hs hss y hy W hyW
  have hv₀S : v₀ ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} := ⟨hv₀, by rw [← hy]; exact hyW⟩
  have hnhds : {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} ∈ 𝓝 v₀ := (hs W 0).1.mem_nhds hv₀S
  have hval : ∀ v (hv : v ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}) (b : Sec s' W),
      valAt' (s v) W b = CxPts.ev s' (RingHom.id ℂ) W b ⟨s v, hss v hv.1⟩ := by
    intro v hv b
    simp only [valAt', CxPts.ev, valR, dif_pos hv.2]
    rfl
  let g : Sec s' W → V → ℂ := fun b v => valAt' (s v) W b
  have hd : ∀ b, DifferentiableAt ℂ (g b) v₀ := fun b =>
    ((hs W b).2 v₀ hv₀S).differentiableAt ((hs W b).1.mem_nhds hv₀S)
  have hadd : ∀ b c, g (b + c) =ᶠ[𝓝 v₀] g b + g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b + c) = valAt' (s v) W b + valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_add _ _ _)
  have hmul : ∀ b c, g (b * c) =ᶠ[𝓝 v₀] g b * g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b * c) = valAt' (s v) W b * valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_mul _ _ _)
  have hconst : ∀ a : ℂ, ∀ᶠ v in 𝓝 v₀, g (algebraMap ℂ (Sec s' W) a) v = a := fun a =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (algebraMap ℂ (Sec s' W) a) = a
      rw [hval v hv]
      exact CxPts.ev_algX (show (⟨s v, hss v hv.1⟩ : CxPts s' (RingHom.id ℂ)) ∈ CxPts.ptsIn s' (RingHom.id ℂ) W from hv.2) a)
  have hyeq : (⟨s v₀, hss v₀ hv₀S.1⟩ : CxPts s' (RingHom.id ℂ)) = y := Subtype.ext hy.symm
  have hv0 : ∀ b, g b v₀ = CxPts.evHom hyW b := fun b => by
    change valAt' (s v₀) W b = _
    rw [hval v₀ hv₀S b, hyeq]
    exact CxPts.ev_eq hyW b
  have hφa : ∀ a : ℂ, CxPts.evHom hyW (algebraMap ℂ (Sec s' W) a) = a := fun a =>
    (CxPts.ev_eq hyW _).symm.trans (CxPts.ev_algX hyW a)
  letI : Module (Sec s' W) (V →L[ℂ] ℂ) := Module.compHom _ (CxPts.evHom hyW)
  haveI : IsScalarTower ℂ (Sec s' W) (V →L[ℂ] ℂ) := ⟨fun a b m => by
    change (CxPts.evHom hyW (a • b)) • m = a • ((CxPts.evHom hyW b) • m)
    have h1 : CxPts.evHom hyW (a • b) = a * CxPts.evHom hyW b :=
      (congrArg (CxPts.evHom hyW) (Algebra.smul_def a b)).trans
        ((map_mul (CxPts.evHom hyW) _ _).trans (congrArg (· * CxPts.evHom hyW b) (hφa a)))
    exact (congrArg (· • m) h1).trans (mul_smul _ _ _)⟩
  let L : Sec s' W →ₗ[ℂ] (V →L[ℂ] ℂ) :=
    { toFun := fun b => fderiv ℂ (g b) v₀
      map_add' := fun b c => by
        change fderiv ℂ (g (b + c)) v₀ = fderiv ℂ (g b) v₀ + fderiv ℂ (g c) v₀
        rw [(hadd b c).fderiv_eq, fderiv_add (hd b) (hd c)]
      map_smul' := fun a b => by
        change fderiv ℂ (g (a • b)) v₀ = a • fderiv ℂ (g b) v₀
        have h' : g (a • b) =ᶠ[𝓝 v₀] fun v => a * g b v := by
          rw [Algebra.smul_def]
          filter_upwards [hmul (algebraMap ℂ _ a) b, hconst a] with v h1 h2
          rw [h1, Pi.mul_apply, h2]
        rw [h'.fderiv_eq, fderiv_const_mul (hd b)] }
  let D : Derivation ℂ (Sec s' W) (V →L[ℂ] ℂ) := Derivation.mk' L (fun b c => by
    change fderiv ℂ (g (b * c)) v₀ =
      (CxPts.evHom hyW b) • fderiv ℂ (g c) v₀ + (CxPts.evHom hyW c) • fderiv ℂ (g b) v₀
    rw [(hmul b c).fderiv_eq, fderiv_mul (hd b) (hd c), hv0 b, hv0 c])
  refine ⟨D.liftKaehlerDifferential.restrictScalars ℂ, fun b ω => ?_, fun b => ?_⟩
  · change D.liftKaehlerDifferential (b • ω) = _
    rw [LinearMap.map_smul]
    exact congrArg (· • D.liftKaehlerDifferential ω) (CxPts.ev_eq hyW b).symm
  · change D.liftKaehlerDifferential (KaehlerDifferential.D ℂ _ b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.triCharpoly_of :
    UpperTheory.Gal.W2.TriCharpoly := by
  intro V W _ _ _ _ _ _ T Θ R G hG
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  have hM : LinearMap.toMatrix (bV.prod bW) (bV.prod bW) G =
      Matrix.fromBlocks (LinearMap.toMatrix bV bV T) 0 (LinearMap.toMatrix bV bW R)
        (LinearMap.toMatrix bW bW Θ) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, hG]
  rw [← LinearMap.charpoly_toMatrix G (bV.prod bW), ← LinearMap.charpoly_toMatrix T bV,
    ← LinearMap.charpoly_toMatrix Θ bW, hM, Matrix.charpoly_fromBlocks_zero₁₂]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.perLin_of :
    UpperTheory.Gal.W2.PerLin := by
  intro O _ bar g ρ D P P' H hP hH hc hP'
  have hdet : LinearMap.det (Matrix.toLin' H) ≠ 0 := by rwa [LinearMap.det_toLin']
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearMap.equivOfDetNeZero _ hdet
  have happ : ∀ z, h z = H *ᵥ z := fun z => rfl
  have key := IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by
    rw [happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])
  have hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P := by
    ext x
    simp [hP', happ]
  rw [hEq]
  exact key
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatComp_of :
    UpperTheory.Gal.W2.FlatComp := by
  intro V _ _ Y Y' f s v₀ w h U a hU
  have hU' : ⊤ ≤ s v₀ ⁻¹ᵁ (f ⁻¹ᵁ U) := hU
  have e : (fun v => valAt' (s v ≫ f) U a) =
      fun v => valAt' (s v) (f ⁻¹ᵁ U) ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom a) :=
    funext fun v => GlobalTheory.ExpCoord.valAt'_comp (s v) f U a
  rw [e]
  exact h _ _ hU'
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj colMat)

namespace UpperTheory.Gal.W2

theorem perCoordLoc_of : PerCoordLoc := by
  intro O _ bar g ρ D P₀ M₀ hP₀ hM₀ d co hco m B P b₀ hB hb₀ hHol hPb₀
  obtain ⟨α, β, hαβ⟩ := PerCoordU.exists_colMat_per hP₀
  obtain ⟨A, hA⟩ : ∃ A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, A b = colMat α ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, Bm b = colMat β ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  have hrep : ∀ b ∈ B, ∀ x, P b x = realMap (A b) (Bm b) (P₀ x) := by
    intro b hb x
    rw [hA, hBm]
    exact hαβ _ (hHol.1 b hb) x
  have hPd : ∀ (x : D.La) (i : Fin g), DifferentiableOn ℂ (fun b => P b x i) B :=
    fun x i => differentiableOn_pi.1 (hHol.2 x) i
  have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := by
    intro i j
    simp only [hA, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hBd : ∀ i j, DifferentiableOn ℂ (fun b => Bm b i j) B := by
    intro i j
    simp only [hBm, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hAc : ContinuousOn A B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hdet : ContinuousOn (fun b => (A b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hAc
  have hSo : IsOpen (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton
  have hAB0 : A b₀ = 1 ∧ Bm b₀ = 0 := by
    apply realMap_inj
    apply PerCoordU.ext_per hP₀
    intro x
    have h1 := hrep b₀ hb₀ x
    rw [hPb₀] at h1
    rw [← h1, realMap_apply]
    simp
  have hb₀S : b₀ ∈ B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ := by
    refine ⟨hb₀, ?_⟩
    simp [hAB0.1]
  have hnhds : B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ ∈ 𝓝 b₀ := hSo.mem_nhds hb₀S
  have hinvd : ∀ i j, DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹)
      (fun i j => (hAd i j).mono Set.inter_subset_left)
      (fun b hb => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by simpa using hb.2)))
  obtain ⟨gL, hgL⟩ := LinearMap.exists_leftInverse_of_injective co (LinearMap.ker_eq_bot.mpr hco.1)
  refine ⟨fun b => gL ((A b)⁻¹ * Bm b), ?_, ?_, ?_⟩
  · rw [differentiableAt_pi]
    intro k
    have e : (fun b => gL ((A b)⁻¹ * Bm b) k) =
        fun b => ∑ i, ∑ j, ((A b)⁻¹ * Bm b) i j * gL (Matrix.single i j 1) k :=
      funext fun b => PerCoordU.coords_sum gL _ k
    rw [e]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.mul_const ?_ _
    simp only [Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_mul ?_ ?_
    · exact (hinvd i l).differentiableAt hnhds
    · exact (hBd l j).differentiableAt (hB.mem_nhds hb₀)
  · simp only
    rw [hAB0.1, hAB0.2, Matrix.mul_zero, map_zero]
  · filter_upwards [hnhds] with b hb
    have hdetb : IsUnit (A b).det := isUnit_iff_ne_zero.mpr (by simpa using hb.2)
    have hCmem : (A b)⁻¹ * Bm b ∈ LinearMap.range co := by
      rw [hco.2]
      exact PerCoordU.mem_Tsp_of_period hP₀ (hHol.1 b hb.1) hM₀.2.2 (hrep b hb.1) hdetb.ne_zero
    obtain ⟨y, hy⟩ := hCmem
    have hcy : co (gL ((A b)⁻¹ * Bm b)) = (A b)⁻¹ * Bm b := by
      rw [← hy, ← LinearMap.comp_apply gL co, hgL, LinearMap.id_apply]
    letI := Matrix.invertibleOfIsUnitDet (A b) hdetb
    refine ⟨Matrix.toLinearEquiv' (A b) this, fun x => ?_⟩
    simp only [hcy, perC_apply]
    rw [hrep b hb.1 x, realMap_apply]
    show A b *ᵥ P₀ x + Bm b *ᵥ star (P₀ x) = A b *ᵥ (P₀ x + ((A b)⁻¹ * Bm b) *ᵥ star (P₀ x))
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdetb]

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open GlobalTheory.HolHom in
theorem UpperTheory.Gal.W2.flatAffine_of :
    UpperTheory.Gal.W2.FlatAffine := by
  intro V _ _ Y B s v₀ w hB hv₀ hs W hW hsW hder U f hU
  have hhol := holAt_of_isHolTo hs hv₀
  have hpU := (le_preimage_iff _ _).1 hU
  have hpW := (le_preimage_iff _ _).1 hsW
  obtain ⟨g, hgle, hpg⟩ := hW.exists_basicOpen_le (V := U) ⟨_, hpU⟩ hpW
  have hDW : Y.basicOpen g ≤ W := Y.basicOpen_le g
  letI := (Y.presheaf.map (homOfLE hDW).op).hom.toAlgebra
  haveI := hW.isLocalization_basicOpen g
  obtain ⟨⟨h, ⟨_, k, rfl⟩⟩, e⟩ :=
    IsLocalization.surj (Submonoid.powers g) ((Y.presheaf.map (homOfLE hgle).op).hom f)
  simp only [RingHom.algebraMap_toAlgebra] at e
  have hD0 : ⊤ ≤ s v₀ ⁻¹ᵁ Y.basicOpen g := (le_preimage_iff _ _).2 hpg
  have hev : ∀ᶠ v in 𝓝 v₀, ⊤ ≤ s v ⁻¹ᵁ Y.basicOpen g := (hhol _ hD0).1
  have heq : (fun v => valAt' (s v) W h) =ᶠ[𝓝 v₀]
      (fun v => valAt' (s v) U f * valAt' (s v) W g ^ k) := by
    filter_upwards [hev] with v hv
    have e' := congrArg (HolHom.evalHom (s v) _ hv) e
    simp only [map_mul, map_pow, ← valR_eq] at e'
    rw [valR_res (s v) hgle f hv, valR_res (s v) hDW g hv, valR_res (s v) hDW h hv] at e'
    simp only [valAt'_eq_valR]
    exact e'.symm
  have hFd := (hhol U hU).2 f
  have hGd := (hhol W hsW).2 g
  have hHd := (hhol W hsW).2 h
  have hL := (hFd.hasFDerivAt.mul (hGd.hasFDerivAt.pow k)).congr_of_eventuallyEq heq
  have huniq := hL.unique hHd.hasFDerivAt
  have hw := congrArg (fun L => L w) huniq
  have hG0 : valAt' (s v₀) W g ≠ 0 := (le_basicOpen_iff _ hsW g).1 hD0
  simp [hder g, hder h, hG0] at hw
  exact hw
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.ptHol_of :
    UpperTheory.Gal.W2.HolPi → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PtHol := by
  intro hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hS := S.hol m B P hB hP
  refine hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ)
    (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_
  · have hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1)) :=
      GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst
        (fun bz hbz => hbz.1)
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
  · intro j
    let φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) :=
      fun bz => (bz.1, bz.2 j)
    have hφ : Differentiable ℂ φ := by
      fun_prop
    have hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))
        (B ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩
    have he := GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
end
