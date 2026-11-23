module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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

theorem UpperTheory.Gal.W2.detReal_of :
    UpperTheory.Gal.W2.DetReal := by
  intro W _ _ _ f
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.mul_conj]
  rfl
end

section

namespace UpperTheory.Gal.W2

theorem conjCharpoly_of : ConjCharpoly := by
  intro V _ _ _ d hd τ G A hτ hG
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := τ.linearEquivOfInjective hτ (by simp [hd])
  let b : Module.Basis (Fin d) ℂ V := (Pi.basisFun ℂ (Fin d)).map e.symm
  have hM : LinearMap.toMatrix b b G = A := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h1 : b j = e.symm (Pi.single j 1) := by simp [b]
    have h2 : ∀ v, b.repr v i = e v i := fun v => by simp [b, Pi.basisFun_repr]
    rw [h2, h1]
    change τ (G (e.symm (Pi.single j 1))) i = A i j
    rw [hG]
    have h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]
      exact e.apply_symm_apply _
    rw [h3, Matrix.mulVec_single_one]
    rfl
  rw [← hM, LinearMap.charpoly_toMatrix]

end UpperTheory.Gal.W2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem affineMap_hasFDerivAt (hTri : UpperTheory.Gal.W2.TriCharpoly) {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (R : V →ₗ[ℂ] W) (c : V × W) (G : V × W → V × W)
    (hG : ∀ v, G v = (T v.1, Θ v.2 + R v.1) + c) (v₀ : V × W) :
    ∃ G' : (V × W) →L[ℂ] (V × W), HasFDerivAt G G' v₀ ∧
      (G' : (V × W) →ₗ[ℂ] (V × W)).charpoly = T.charpoly * Θ.charpoly := by
  unfold UpperTheory.Gal.W2.TriCharpoly at hTri
  let Gl : (V × W) →ₗ[ℂ] (V × W) :=
    LinearMap.prod (T ∘ₗ LinearMap.fst ℂ V W) (Θ ∘ₗ LinearMap.snd ℂ V W + R ∘ₗ LinearMap.fst ℂ V W)
  let G' : (V × W) →L[ℂ] (V × W) := LinearMap.toContinuousLinearMap Gl
  refine ⟨G', ?_, ?_⟩
  · have hfun : G = fun v => G' v + c := by
      funext v
      rw [hG v]
      rfl
    rw [hfun]
    exact G'.hasFDerivAt.add_const c
  · have hc : (G' : (V × W) →ₗ[ℂ] (V × W)) = Gl := rfl
    rw [hc]
    exact hTri V W T Θ R Gl (fun v w => rfl)

theorem UpperTheory.Gal.W2.locTan_of :
    UpperTheory.Gal.W2.TanChart → UpperTheory.Gal.W2.PerNear → UpperTheory.Gal.W2.BaseImm → UpperTheory.Gal.W2.PtHol → UpperTheory.Gal.W2.PtImm → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.TriCharpoly → UpperTheory.Gal.W2.LocTan := by
  intro hTan hPer hBase hHol hImm hFib hCorr hTri
  unfold UpperTheory.Gal.W2.TanChart at hTan
  unfold UpperTheory.Gal.W2.PerNear at hPer
  unfold UpperTheory.Gal.W2.BaseImm at hBase
  unfold UpperTheory.Gal.W2.PtHol at hHol
  unfold UpperTheory.Gal.W2.PtImm at hImm
  unfold UpperTheory.Gal.W2.PtFibre at hFib
  unfold UpperTheory.Gal.W2.CorrChart at hCorr
  unfold UpperTheory.Gal.W2.LocTan
  intro O _ bar g ρ D X s A _ S d hsm k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP₀ hM co hco ga H hfix T hT L hL z₀ hz₀ y hy At hAt
  have hCsp : ∀ b, co b ∈ Csp bar ρ M₀ := by
    intro b
    have hco' := hco
    unfold IsCoordC at hco'
    rw [← hco'.2]
    exact LinearMap.mem_range_self co b
  obtain ⟨B0, hB0o, h0B0, hB0⟩ := hPer O bar g ρ D P₀ M₀ hP₀ hM d co hCsp
  have hB0' := hB0
  unfold PELU.IsHolPeriods at hB0'
  choose x hx using hz₀
  let sec : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Sp ℂ ⟶ (KS.pow A k).left) :=
    fun bz => S.pt k (perC P₀ (co bz.1)) bz.2
  let R : (Fin d → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ) :=
    { toFun := fun b j => -(co (T b) *ᵥ star (P₀ (x j)))
      map_add' := by
        intro a b
        funext j
        simp only [map_add (f := _), Matrix.add_mulVec, Pi.add_apply, neg_add]
      map_smul' := by
        intro c b
        funext j
        simp [Matrix.smul_mulVec] }
  let c : (Fin d → ℂ) × (Fin k → Fin g → ℂ) := (0, fun j => -(P₀ (x j)))
  let G : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Fin d → ℂ) × (Fin k → Fin g → ℂ) :=
    fun v => (T v.1, fibMap H L v.2 - fun j => perC P₀ (co (T v.1)) (x j))
  have hG : ∀ v, G v = (T v.1, fibMap H L v.2 + R v.1) + c := by
    intro v
    refine Prod.ext ?_ ?_
    · show T v.1 = T v.1 + 0
      rw [add_zero]
    · funext j
      show fibMap H L v.2 j - perC P₀ (co (T v.1)) (x j) =
        fibMap H L v.2 j + -(co (T v.1) *ᵥ star (P₀ (x j))) + -(P₀ (x j))
      rw [perC_apply]
      abel
  obtain ⟨G', hG'd, hG'c⟩ := affineMap_hasFDerivAt hTri T (fibMap H L) R c G hG ((0 : Fin d → ℂ), z₀)
  have hfix0 : G ((0 : Fin d → ℂ), z₀) = ((0 : Fin d → ℂ), z₀) := by
    refine Prod.ext (map_zero T) ?_
    funext j
    show fibMap H L z₀ j - perC P₀ (co (T 0)) (x j) = z₀ j
    rw [map_zero T, map_zero co, perC_zero, hx j, sub_sub_cancel]
  have hsec0 : (y : Sp ℂ ⟶ (KS.pow A k).left) = sec ((0 : Fin d → ℂ), z₀) := by
    show _ = S.pt k (perC P₀ (co 0)) z₀
    rw [map_zero co, perC_zero]
    exact hy
  have hev : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), sec v ≫ c₂ = sec (G v) ≫ c₁ := by
    have hTc : Continuous (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1) :=
      (LinearMap.continuous_of_finiteDimensional T).comp continuous_fst
    have hT0 : Filter.Tendsto (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1)
        (𝓝 ((0 : Fin d → ℂ), z₀)) (𝓝 0) := by
      have := hTc.tendsto ((0 : Fin d → ℂ), z₀)
      simpa using this
    have h1 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), v.1 ∈ B0 :=
      (continuous_fst.tendsto ((0 : Fin d → ℂ), z₀)).eventually (hB0o.eventually_mem h0B0)
    have h2 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), T v.1 ∈ B0 :=
      hT0.eventually (hB0o.eventually_mem h0B0)
    filter_upwards [h1, h2] with v hv1 hv2
    obtain ⟨b, z⟩ := v
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hv1
    have hPTb : PELU.IsPeriod D ρ (perC P₀ (co (T b))) := hB0'.1 (T b) hv2
    have hPTb' : PELU.IsPeriod D ρ (perC P₀ (H * co b * (H.map star)⁻¹)) := by
      rw [← hT b]
      exact hPTb
    have step := hCorr O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP₀ hM ga H hfix L hL (co b) hPb hPTb' z
    show S.pt k (perC P₀ (co b)) z ≫ c₂ =
      S.pt k (perC P₀ (co (T b))) (fibMap H L z - fun j => perC P₀ (co (T b)) (x j)) ≫ c₁
    rw [step, ← hT b]
    congr 1
    refine ((hFib O bar g ρ D X s A S k _ hPTb).2.2.2.1 _ _).mpr ?_
    intro j
    refine ⟨x j, ?_⟩
    simp [hT b]
  have hflat := hImm O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) 0 hB0o h0B0 hB0
    (hBase O bar g ρ D X s A S d hsm P₀ M₀ hP₀ hM co hco) z₀
  have hhol := hHol O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) hB0o hB0
  have hsecs : ∀ v ∈ B0 ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)),
      sec v ≫ ((KS.pow A k).hom ≫ s) = spMap (RingHom.id ℂ) := by
    rintro ⟨b, z⟩ ⟨hb, -⟩
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hb
    show S.pt k (perC P₀ (co b)) z ≫ ((KS.pow A k).hom ≫ s) = _
    rw [← Category.assoc, (hFib O bar g ρ D X s A S k _ hPb).1 z, S.ov _ hPb]
  have hfr : Module.finrank ℂ ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) = d + k * g := by
    simp [Module.finrank_pi_fintype]
  have key := hTan ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) (d + k * g) hfr Z (KS.pow A k).left sZ
    ((KS.pow A k).hom ≫ s) c₁ c₂ h₁ h₂ (B0 ×ˢ Set.univ) sec ((0 : Fin d → ℂ), z₀)
    (hB0o.prod isOpen_univ) ⟨h0B0, trivial⟩ hhol hsecs hflat G G' hG'd hfix0 hev y hsec0 At hAt
  rw [key, hG'c]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma det_one_sub_smul_matrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (y : ℂ) :
    (1 - y • M).det = Polynomial.eval y M.charpoly.reverse := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, h]; ring

private lemma det_one_sub_smul_linear {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) (y : ℂ) :
    LinearMap.det (1 - y • f) = Polynomial.eval y f.charpoly.reverse := by
  classical
  let b := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one,
    det_one_sub_smul_matrix, LinearMap.charpoly_toMatrix]

theorem UpperTheory.Gal.W2.detOfCharpoly_of :
    UpperTheory.Gal.W2.DetOfCharpoly := by
  intro V W _ _ _ _ _ _ T Θ d A h y
  rw [det_one_sub_smul_linear, det_one_sub_smul_linear, ← Polynomial.eval_mul,
    ← Polynomial.reverse_mul_of_domain, ← h, det_one_sub_smul_matrix]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.locSum_of :
    UpperTheory.Gal.W2.LocTan → UpperTheory.Gal.W2.TorusCount → UpperTheory.Gal.W2.PiLattice → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.DetOfCharpoly → UpperTheory.Gal.W2.LocSum := by
  intro hTan hCount hPi hFib hChart hDet O _ bar g ρ D X s A _ S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL hlat hinj hdT hdΘ
  classical
  have hrange : Submodule.span ℝ ((P₀.range : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  obtain ⟨hdisc, hspan⟩ := hPi g k P₀.range hP.2.2.1 hrange
  set Λk : AddSubgroup (Fin k → Fin g → ℂ) :=
    AddSubgroup.pi (Set.univ : Set (Fin k)) (fun _ => P₀.range) with hΛk
  have memΛ : ∀ z : Fin k → Fin g → ℂ, z ∈ Λk ↔ ∀ j, z j ∈ P₀.range := by
    intro z; simp [hΛk, AddSubgroup.mem_pi]
  obtain ⟨Fz, hFz1, hFz2, hFzc⟩ := hCount (Fin k → Fin g → ℂ) Λk hdisc hspan (fibMap H L)
    (fun z hz => (memΛ _).2 (hlat z ((memΛ z).1 hz))) hdΘ
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hFib O bar g ρ D X s A S k P₀ hP
  have e0 : H * 0 * (H.map star)⁻¹ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ z, S.pt k P₀ z ≫ c₂ = S.pt k P₀ (fibMap H L z) ≫ c₁ := by
    intro z
    have h := hChart O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP hM ga H hga L hL 0
      (by rw [perC_zero]; exact hP) (by rw [e0, perC_zero]; exact hP) z
    rw [e0, perC_zero] at h
    exact h
  have fixIff : ∀ z, S.pt k P₀ z ≫ c₁ = S.pt k P₀ z ≫ c₂ ↔ fibMap H L z - z ∈ Λk := by
    intro z
    constructor
    · intro h
      have h' : S.pt k P₀ z = S.pt k P₀ (fibMap H L z) := hinj _ _ (h.trans (key z))
      exact (memΛ _).2 ((hf4 _ _).1 h'.symm)
    · intro h
      have h' := (hf4 (fibMap H L z) z).2 ((memΛ _).1 h)
      rw [key z, h']
  let mk : (Fin k → Fin g → ℂ) → CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ) :=
    fun z => ⟨S.pt k P₀ z, by rw [← Category.assoc, hf1 z]; exact S.ov P₀ hP⟩
  have mkInj : Set.InjOn mk Fz := by
    intro z hz z' hz' h
    have h1 : S.pt k P₀ z = S.pt k P₀ z' := congrArg Subtype.val h
    have h2 : z - z' ∈ Λk := (memΛ _).2 ((hf4 z z').1 h1)
    obtain ⟨w, _, hw⟩ := hFz2 z (hFz1 z hz)
    have a := hw z ⟨hz, by rw [sub_self]; exact zero_mem _⟩
    have b := hw z' ⟨hz', h2⟩
    exact a.trans b.symm
  refine ⟨Fz.image mk, ?_, ?_⟩
  · intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hf1 z, (fixIff z).2 (hFz1 z hz)⟩
    · rintro ⟨ho, hfx⟩
      obtain ⟨z, hz⟩ := hf3 y.1 ho
      have hz1 : fibMap H L z - z ∈ Λk := (fixIff z).1 (by rw [← hz]; exact hfx)
      obtain ⟨z', ⟨hz'F, hz'⟩, _⟩ := hFz2 z hz1
      refine ⟨z', hz'F, Subtype.ext ?_⟩
      show S.pt k P₀ z' = y.1
      rw [hz]; exact ((hf4 z z').2 ((memΛ _).1 hz')).symm
  · intro At hAt
    have hdet : ∀ y ∈ Fz.image mk, ∀ t : ℂ, (1 - t • At y).det =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) := by
      intro y hy t
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      have hcp := hTan O bar g ρ D X s A S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL z
        ((memΛ _).1 (hFz1 z hz)) (mk z) rfl (At (mk z)) (hAt _ hy)
      exact hDet _ _ T (fibMap H L) _ _ hcp t
    have hdet1 : ∀ y ∈ Fz.image mk, (1 - At y).det =
        LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L) := by
      intro y hy
      have h := hdet y hy 1
      simpa only [one_smul] using h
    refine ⟨fun y hy => by rw [hdet1 y hy]; exact mul_ne_zero hdT hdΘ, fun t => ?_⟩
    have hterm : ∀ y ∈ Fz.image mk, lefTerm (At y) t =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) /
          (LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L)) := by
      intro y hy
      unfold lefTerm
      rw [hdet y hy t, hdet1 y hy]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_image_of_injOn mkInj, nsmul_eq_mul, hFzc]
    field_simp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_mul_spherical_coordinates {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

private theorem det_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    (A.map star).det = star A.det := by
  exact (RingHom.map_det (starRingEnd ℂ) A).symm

private theorem hermForm_mulVec_mulVec {g : ℕ} (M H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (H *ᵥ z) (H *ᵥ w) = hermForm (Hᵀ * M * H.map star) z w := by
  rw [PerCoordU.herm_mulVec_left, PerCoordU.herm_mulVec_right]

private theorem eq_of_mulVec_period_eq {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, A *ᵥ P x = B *ᵥ P x) : A = B := by
  have e := PerCoordU.ext_per hP (f := PeriodCoord.realMap A 0) (f' := PeriodCoord.realMap B 0)
    (fun x => by simp [PeriodCoord.realMap_apply, h])
  exact (PeriodCoord.realMap_inj e).1

private theorem eq_of_hermForm_im_eq_on_periods {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {N N' : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x y, (hermForm N (P x) (P y)).im = (hermForm N' (P x) (P y)).im) : N = N' := by
  apply PerCoordU.sesq_ext
  have h1 : PeriodCoord.imForm N = PeriodCoord.imForm N' := by
    apply PerCoordU.ext_per hP
    intro x
    apply PerCoordU.ext_per hP
    intro y
    simp only [PeriodCoord.imForm_apply]
    exact h x y
  intro z w
  rw [← PeriodCoord.imForm_apply, ← PeriodCoord.imForm_apply, h1]

private theorem inv_mul_comm_of_mul_comm_of_det_unit {g : ℕ} (X N : Matrix (Fin g) (Fin g) ℂ) (hN : IsUnit N.det)
    (h : X * N = N * X) : N⁻¹ * X = X * N⁻¹ := by
  calc N⁻¹ * X = N⁻¹ * X * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
    _ = N⁻¹ * (X * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = N⁻¹ * (N * X) * N⁻¹ := by rw [h]
    _ = X * N⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN, Matrix.one_mul]

theorem UpperTheory.Gal.W2.adExists_of :
    UpperTheory.Gal.W2.AdExists := by
  intro O _ bar g ρ D P₀ M₀ hP hM ga H hF
  obtain ⟨⟨m, hm, hEF⟩, hga⟩ := hF
  obtain ⟨_, hpos, hIm⟩ := hM
  have hform : Hᵀ * M₀ * H.map star = (m : ℂ) • M₀ := by
    apply eq_of_hermForm_im_eq_on_periods hP
    intro x y
    have hs : hermForm ((m : ℂ) • M₀) (P₀ x) (P₀ y) = (m : ℂ) * hermForm M₀ (P₀ x) (P₀ y) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
    rw [← hermForm_mulVec_mulVec, ← hga x, ← hga y, hIm, hEF, hs, Complex.mul_im, hIm]
    simp
  have hdM : M₀.det ≠ 0 := PeriodCoord.det_ne_zero_of_pos hpos
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hform
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, det_map_star',
      Matrix.det_smul] at e
    simp [hdM, hm.ne'] at e
  have hcomm : ∀ a, ρ a * H = H * ρ a := by
    intro a
    apply eq_of_mulVec_period_eq hP
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hga x, ← hP.1 a (ga x), ← hP.1 a x,
      ← hga (a • x), LinearMap.map_smul]
  refine ⟨hdet, hcomm, ?_⟩
  intro C hC
  set N := H.map star with hNdef
  have hNu : IsUnit N.det := by
    rw [hNdef, det_map_star']
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  have hNtu : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
  have hc' : ∀ b, (ρ b).map star * N = N * (ρ b).map star := by
    intro b
    rw [hNdef, ← map_star_mul_spherical_coordinates, ← map_star_mul_spherical_coordinates, hcomm]
  have hC' : (Cᵀ * M₀)ᵀ = Cᵀ * M₀ ∧
      ∀ a, Cᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * (Cᵀ * M₀) := hC
  obtain ⟨hS1, hS2⟩ := hC'
  have hHM : Hᵀ * M₀ = (m : ℂ) • (M₀ * N⁻¹) := by
    calc Hᵀ * M₀ = Hᵀ * M₀ * N * N⁻¹ := by
          rw [Matrix.mul_assoc (Hᵀ * M₀), Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
      _ = (m : ℂ) • (M₀ * N⁻¹) := by rw [hform, Matrix.smul_mul]
  have hkey : (H * C * N⁻¹)ᵀ * M₀ = (m : ℂ) • (N⁻¹ᵀ * (Cᵀ * M₀) * N⁻¹) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hHM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  show ((H * C * N⁻¹)ᵀ * M₀)ᵀ = (H * C * N⁻¹)ᵀ * M₀ ∧
    ∀ a, (H * C * N⁻¹)ᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * ((H * C * N⁻¹)ᵀ * M₀)
  rw [hkey]
  generalize Cᵀ * M₀ = S at hS1 hS2 ⊢
  constructor
  · simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hS1,
      Matrix.mul_assoc]
  · intro a
    have c1 : N⁻¹ * (ρ (bar a)).map star = (ρ (bar a)).map star * N⁻¹ :=
      inv_mul_comm_of_mul_comm_of_det_unit _ N hNu (hc' (bar a))
    have hX : (ρ a)ᴴ * Nᵀ = Nᵀ * (ρ a)ᴴ := by
      rw [← PerCoordU.map_star_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hc' a]
    have c2 : Nᵀ⁻¹ * (ρ a)ᴴ = (ρ a)ᴴ * Nᵀ⁻¹ := inv_mul_comm_of_mul_comm_of_det_unit _ _ hNtu hX
    rw [Matrix.transpose_nonsing_inv]
    calc (m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹) * (ρ (bar a)).map star
        = (m : ℂ) • (Nᵀ⁻¹ * S * (N⁻¹ * (ρ (bar a)).map star)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (S * (ρ (bar a)).map star) * N⁻¹) := by
          rw [c1]; simp only [Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * ((ρ a)ᴴ * S) * N⁻¹) := by rw [hS2 a]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (ρ a)ᴴ * S * N⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (ρ a)ᴴ * ((m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹)) := by
          rw [c2]; simp only [Matrix.mul_smul, Matrix.mul_assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.piLattice_of :
    UpperTheory.Gal.W2.PiLattice := by
  intro g k Λ hd hs
  constructor
  · let φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ) :=
      fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩
    refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
    · refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    · intro x y hxy
      apply Subtype.ext
      funext i
      have := congrArg (fun z => (z i : Fin g → ℂ)) hxy
      simpa [φ] using this
  · rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hs]; trivial
    have hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map
        (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤
        Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hv
      · simp [hj]
    exact hmap ⟨w i, hw, rfl⟩
end
