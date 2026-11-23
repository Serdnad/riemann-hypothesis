module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  [Algebra c.F K]

theorem exists_genPt (Z : Model Xo c β) (φ : c.F →+* V) (hφ : (algebraMap V K).comp φ = algebraMap c.F K)
    (y : FrPt Xo c K) : ∃ χ : Sp V ⟶ gen Z, χ ≫ genStr Z = spMap φ ∧ GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap φ) (GlobalTheory.AllWt.ptF y ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp, hφ]
    exact pullback.lift_snd _ _ _)
  exact ⟨χ, h2, h1.symm⟩

theorem exists_genIdent (Z : Model Xo c β) {χ : Sp V ⟶ gen Z} {y : FrPt Xo c K}
    (hχ : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)) {t : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap V K))) (mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) (GlobalTheory.AllWt.ptF y)
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) (GlobalTheory.AllWt.ptF y) Z.m mF
  have hj : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap V K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F}

theorem mem_genBd_of_mem_genBd {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'}
    {t t' : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) (m' : SABMap t' Z'.t (χ' ≫ genι Z'))
    (ψ : SABMap t t' (𝟙 (Sp V))) (p : Sp V) (h : χ' p ∈ genBd Z') : χ p ∈ genBd Z := by
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z.t.semi m.cart.1 p]
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z'.t.semi m'.cart.1 p] at h
  have e := abLocus_pullback abLocusOne t'.semi ψ.cart.1 p
  have e0 : (𝟙 (Sp V)) p = p := rfl
  rw [e0] at e
  exact fun hp => h (e.2 hp)

section Chain

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {x : Sp V ⟶ Z.X} {x' : Sp V ⟶ Z'.X} {t t' : SAB H (Sp V)}
  (m : SABMap t Z.t x) (m' : SABMap t' Z'.t x') (ψ : SABMap t t' (𝟙 (Sp V))) {φ : c.F →+* V}

theorem exists_isEigBasis_chain {τ : E →+* ℂ} {n : ℕ} {v' : Fin n → (Sp (DualNumber V) ⟶ Z'.t.G.left)}
    (h : IsEigBasis Z'.t φ x' τ v') : ∃ v : Fin n → (Sp (DualNumber V) ⟶ t.G.left),
      (∀ i, (v i ≫ ψ.φ) ≫ m'.φ = v' i) ∧ (∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) ∧
        IsEigBasis Z.t φ x τ (fun i => v i ≫ m.φ) := by
  have h1 : IsEigBasis Z'.t φ (𝟙 _ ≫ x') τ v' := by rwa [Category.id_comp]
  obtain ⟨v₁, hv₁, h₁⟩ := isEigBasis_pull m' h1
  have h2 : IsEigBasis t' φ (𝟙 _ ≫ 𝟙 _) τ v₁ := by rwa [Category.id_comp]
  obtain ⟨v₂, hv₂, h₂⟩ := isEigBasis_pull ψ h2
  refine ⟨v₂, fun i => by rw [hv₂, hv₁], fun i => by rw [(h₂.1 i).1, Category.comp_id], ?_⟩
  have := isEigBasis_push m h₂
  rwa [Category.id_comp] at this

end Chain

section Frame

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'} {y : FrPt Xo c K}
  {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)} {t t' : SAB H (Sp V)}
  {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Z'.t (χ' ≫ genι Z')} {ψ : SABMap t t' (𝟙 (Sp V))}
  {a : SABMap tK t (spMap (algebraMap V K))} {a' : SABMap tK t' (spMap (algebraMap V K))}
  {mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)} {mF' : SABMap tK Z'.oF.t (GlobalTheory.AllWt.ptF y)}

theorem exists_lift_frameVec (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Z'.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Z'.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber V) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    {u' : Sp (DualNumber K) ⟶ Xo.univ.t.G.left} (hu' : u' ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ y.x)
    {w' : Sp (DualNumber K) ⟶ Z'.oF.t.G.left}
    (hw1 : w' ≫ Z'.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y)
    (hw2 : w' ≫ Z'.m0.toSABMap.φ = u') (hw3 : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = u' ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ v ≫ m.φ := by
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  obtain ⟨u, hu1, hu2⟩ := exists_lift mK (spMap (algebraMap K (DualNumber K))) u' (by rw [hu', ← hx])
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) =
      spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp, PullbackSections.dualMap_comp_alg]
  have e1 : u ≫ mF'.φ = w' := by
    apply Z'.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hF0', hu2, hw2]
    · rw [Category.assoc, mF'.cart.1.w, ← Category.assoc, hu1, hw1]
  have e2 : u ≫ a.φ = spMap (dualMap (algebraMap V K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3]
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  refine ⟨u ≫ mF.φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  · rw [Category.assoc, hF0, hu2]
  · rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]

end Frame

theorem bdExt_of_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z O' _ β' Z' V K _ _ _ _ _ _ _ φ y hφ h
  obtain ⟨χ', g', e1', e2', hw', hb'⟩ := h
  obtain ⟨χ, e1, e2⟩ := exists_genPt Z φ hφ y
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ' ≫ genι Z') Z'.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_genIdent Z e2 mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_genIdent Z' e2' mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map V K t t' tK a a'
  choose v hv1 hv2 hv3 using fun τ => exists_isEigBasis_chain m m' ψ (EigFrame.isEigBasis g' τ)
  refine ⟨χ, eigFrameOf (fun τ i => v τ i ≫ m.φ) hv3, e1, e2, fun τ i => ?_,
    mem_genBd_of_mem_genBd m m' ψ _ hb'⟩
  let w' := Classical.choose (hw' τ i)
  have hw1 := (Classical.choose_spec (hw' τ i)).1
  have hw2 := (Classical.choose_spec (hw' τ i)).2.1
  have hw3 := (Classical.choose_spec (hw' τ i)).2.2
  have hw3' : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v τ i ≫ ψ.φ) ≫ m'.φ :=
    hw3.trans (congrArg (fun z => spMap (dualMap (algebraMap V K)) ≫ z) (hv1 τ i).symm)
  exact exists_lift_frameVec hψ hF0 hFm hF0' hFm' (hv2 τ i) (y.tan τ i).1 hw1 hw2 hw3'

end GlobalTheory.CuspFrom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.combo_of_bounded_rows_bounded : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  intro X g r r₀ T lam u A C hu hC w hw
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  refine ⟨∑ i, |c i| * C, fun x hx => ?_⟩
  have key : ∑ j, ((∑ i, c i • fun j => (A i j : ℝ)) j : ℂ) • lam x j = ∑ i, (c i : ℂ) • u x i := by
    simp_rw [hu x hx, Finset.smul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  rw [key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u x) i).trans (hC x hx)) (abs_nonneg _)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem matrix_mul_bounded_poly_growth : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g d R τ E ⟨C, k, hC⟩ hE j
  choose C' hC' using hE
  refine ⟨max C 0 * ∑ i, max (C' i) 0, k, fun s hs => ?_⟩
  have hp : (0:ℝ) ≤ (1 + ‖s‖) ^ k := pow_nonneg (by positivity) _
  have h1 : ∀ i, ‖τ s i j‖ ≤ max C 0 * (1 + ‖s‖) ^ k := fun i =>
    (norm_le_pi_norm (τ s i) j).trans ((norm_le_pi_norm (τ s) i).trans
      ((hC s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)))
  calc ‖∑ i, τ s i j • E s i‖ ≤ ∑ i, ‖τ s i j • E s i‖ := norm_sum_le _ _
    _ = ∑ i, ‖τ s i j‖ * ‖E s i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, (max C 0 * (1 + ‖s‖) ^ k) * max (C' i) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (h1 i) (le_max_of_le_left (hC' i s hs))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp)
    _ = max C 0 * (∑ i, max (C' i) 0) * (1 + ‖s‖) ^ k := by rw [← Finset.mul_sum]; ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.riemann_extension_of_log_growth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ), IsOpen U → DifferentiableOn ℂ φ U → DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0} → U ⊆ closure {b ∈ U | φ b ≠ 0} → (∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) → ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  first | exact @GlobalTheory.LogExt.riemann_extension_log | exact GlobalTheory.LogExt.riemann_extension_log | (intros; apply GlobalTheory.LogExt.riemann_extension_log <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rowsInd_rat_of_real : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  intro g r r₀ lam u A hu hA
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc i
  have hc' : ∀ m, ∑ i, (c i : ℝ) * (A i m : ℝ) = 0 := by
    intro m
    have h1 := congrFun hc m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h2
    exact h2
  have hsum : ∑ i, (c i : ℝ) • u i = 0 := by
    have e : ∀ i, (c i : ℝ) • u i = ∑ m, ((c i : ℝ) * (A i m : ℝ)) • lam m := by
      intro i
      rw [hA i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc', zero_smul, Finset.sum_const_zero]
  have h3 := hu (fun i => (c i : ℝ)) hsum i
  exact_mod_cast h3

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.hermForm_im_real_comb (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, (hermForm Hm (x i) (x j)).im = M i j) (u v : Fin r → ℝ) :
    (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  have key : hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)
      = ∑ m, ∑ m', ((u m * v m' : ℝ) : ℂ) * hermForm Hm (x m) (x m') := by
    simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
      dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    push_cast
    ring
  rw [key]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  ring
end
