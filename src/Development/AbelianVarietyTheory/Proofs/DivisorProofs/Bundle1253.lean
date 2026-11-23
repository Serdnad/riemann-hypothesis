module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatVecDomain

theorem discrete_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    DiscreteTopology (GlobalTheory.ThetaParseval.ratVec F κ) := by
  obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hN : (Set.univ.pi fun _ : κ => U) ∈ nhds (0 : κ → AdeleRing (𝓞 F) F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
  have hc : ContinuousAt (fun x : GlobalTheory.ThetaParseval.ratVec F κ => (x : κ → AdeleRing (𝓞 F) F)) 0 :=
    continuous_subtype_val.continuousAt
  refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
  rintro ⟨y, hy⟩ hyU
  obtain ⟨ξ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y).1 hy
  have hξ : ξ = 0 := funext fun i => hx _ (hyU i (Set.mem_univ i))
  subst hξ
  refine Subtype.ext ?_
  funext i
  simp

theorem exists_compact_cover_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ K : Set (κ → AdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x, ∃ γ ∈ GlobalTheory.ThetaParseval.ratVec F κ, γ + x ∈ K := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : κ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  refine ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (-c (x i)),
    (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨fun i => -c (x i), rfl⟩, fun i _ => ?_⟩
  have := hc (x i)
  simpa [map_neg, neg_add_eq_sub] using this

theorem exists_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  intro F _ _ κ _ μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := discrete_ratVec F κ
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) :=
    GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover_ratVec F κ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup
    (GlobalTheory.ThetaParseval.ratVec F κ)
  exact ⟨D, hD μ, (hD μ).measure_ne_zero (NeZero.ne μ),
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov μ (hD μ)).ne⟩

end GlobalTheory.RatVecDomain
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.TwoBasesDet

theorem exists_leftInv {K : Type} [Field K] {n g : ℕ} (b : Fin n → Fin g → K)
    (hb : LinearIndependent K b) :
    ∃ A : Matrix (Fin n) (Fin g) K, ∀ i j, ∑ k, A i k * b j k = if i = j then 1 else 0 := by
  let lc : (Fin n → K) →ₗ[K] (Fin g → K) := Fintype.linearCombination K b
  have hinj : LinearMap.ker lc = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by simpa [lc, Fintype.linearCombination_apply] using hc))
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective lc hinj
  refine ⟨LinearMap.toMatrix' f, fun i j => ?_⟩
  have h1 : f (b j) = Pi.single j 1 := by
    have : lc (Pi.single j 1) = b j := by simp [lc, Fintype.linearCombination_apply_single]
    rw [← this, ← LinearMap.comp_apply, hf, LinearMap.id_apply]
  have h3 : (Matrix.mulVec (LinearMap.toMatrix' f) (b j)) = f (b j) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h2 := congrFun (h3.trans h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem vV_algebraMap_unit (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {u : V} (hu : IsUnit u) :
    vV V (algebraMap V K' u) = 0 := by
  unfold vV valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2]
  · simp
  · exact fun h => (HeightOneSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem valuation_div_le_one {K : Type} [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K))
    (c d : 𝓞 K) (hd : d ∉ 𝔓.asIdeal) : 𝔓.valuation K ((c : K) / d) ≤ 1 := by
  rw [map_div₀]
  have h1 : 𝔓.valuation K (d : K) = 1 := by
    rw [show (d : K) = algebraMap (𝓞 K) K d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hd
  rw [h1, div_one, show (c : K) = algebraMap (𝓞 K) K c from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem det_vV_add_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  intro K _ _ 𝔓 T iK hiK g n L b hb M u hu C hW hL
  set B : Fin n → Fin g → T.Fr := fun l k => iK (b l k) with hBdef
  obtain ⟨A, hA⟩ := exists_leftInv b hb.2.1

  have key : ∀ z : Fin n → T.Fr, ∀ i, z i = ∑ k, iK (A i k) * ∑ l, z l * B l k := by
    intro z i
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ k, iK (A i k) * (z l * B l k) = if i = l then z l else 0 := by
      intro l
      have h := congrArg iK (hA i l)

      rw [map_sum] at h
      simp only [map_mul] at h
      calc ∑ k, iK (A i k) * (z l * B l k) = z l * ∑ k, iK (A i k) * iK (b l k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hBdef]; ring
        _ = _ := by rw [h]; split_ifs <;> simp
    simp_rw [h]; simp
  have hinj : ∀ x y : Fin n → T.Fr, (∀ k, ∑ l, x l * B l k = ∑ l, y l * B l k) → x = y := by
    intro x y hxy
    funext i
    rw [key x i, key y i]
    exact Finset.sum_congr rfl fun k _ => by rw [hxy k]

  set P : Matrix (Fin n) (Fin n) T.Fr := C * M.map iK with hPdef
  have hWP : ∀ i k, (∑ j, C i j • fun k => iK (u j k)) k = ∑ l, P i l * B l k := by
    intro i k

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu, map_sum, map_mul, hPdef, Matrix.mul_apply,
    Matrix.map_apply, hBdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  have hint : ∀ x ∈ L, ∃ p : Fin n → T.V, ∀ k, iK (x k) = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hb.2.2 x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hdx
    have hd0 : (d : K) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      rw [this]; exact Submodule.zero_mem _
    choose p hp using fun l => (hiK ((c l : K) / d)).2 (valuation_div_le_one 𝔓 (c l) d hd)
    refine ⟨p, fun k => ?_⟩
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at hk
    have hx' : x k = ∑ l, ((c l : K) / d) * b l k := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      rw [eq_div_iff hd0]
      convert hk.symm using 1
      · ring

    simp only [hp, hBdef, hx', map_sum, map_mul]
  have hspan : ∀ w ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K))),
      ∃ p : Fin n → T.V, ∀ k, w k = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact hint x hx
    | zero => exact ⟨0, fun k => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨p, hp⟩ := h
      obtain ⟨p', hp'⟩ := h'
      exact ⟨p + p', fun k => by simp [hp, hp', add_mul, Finset.sum_add_distrib]⟩
    | smul a w _ h =>
      obtain ⟨p, hp⟩ := h
      refine ⟨a • p, fun k => ?_⟩
      simp only [Pi.smul_apply, Algebra.smul_def, hp, Finset.mul_sum, smul_eq_mul, map_mul, mul_assoc]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Algebra.algebraMap_self, RingHom.id_apply]

  have hPint : ∀ i, ∃ p : Fin n → T.V, ∀ l, P i l = algebraMap T.V T.Fr (p l) := by
    intro i
    obtain ⟨p, hp⟩ := hspan _ (hW i)
    refine ⟨p, fun l => congrFun (hinj (P i) (fun l => algebraMap T.V T.Fr (p l)) fun k => ?_) l⟩
    rw [← hWP, hp]
  choose Pv hPv using hPint
  have hPeq : P = (Matrix.of Pv).map (algebraMap T.V T.Fr) := by
    ext i l; simp [hPv i l]

  have hQint : ∀ l, ∃ q : Fin n → T.V, ∀ m, ∑ i, algebraMap T.V T.Fr (q i) * P i m = if l = m then 1 else 0 := by
    intro l
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hL (b l) (hb.1 l))
    refine ⟨q, fun m => congrFun (hinj (fun m => ∑ i, algebraMap T.V T.Fr (q i) * P i m)
      (fun m => if l = m then 1 else 0) fun k => ?_) m⟩
    have hk : ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k = iK (b l k) := by
      rw [← congrFun hq k, Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ m, algebraMap T.V T.Fr (q i) * P i m * B m k
        = ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hWP, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = B l k := hk
  choose Qv hQv using hQint
  have hQP : Matrix.of Qv * Matrix.of Pv = 1 := by
    apply (Matrix.map_injective (IsFractionRing.injective T.V T.Fr))
    show (Matrix.of Qv * Matrix.of Pv).map (algebraMap T.V T.Fr) = (1 : Matrix (Fin n) (Fin n) T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, ← hPeq, Matrix.map_one _ (map_zero _) (map_one _)]
    ext l m
    simpa [Matrix.mul_apply, Matrix.one_apply] using hQv l m
  have hunit : IsUnit (Matrix.of Pv).det := by
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact ⟨⟨_, _, by rw [mul_comm]; exact this, this⟩, rfl⟩
  have hdetP : P.det = algebraMap T.V T.Fr (Matrix.of Pv).det := by
    rw [hPeq, RingHom.map_det]; rfl
  have hdetP' : P.det = C.det * iK M.det := by
    rw [hPdef, Matrix.det_mul, RingHom.map_det]; rfl
  have hP0 : P.det ≠ 0 := by
    rw [hdetP]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hunit.ne_zero
  have hC0 : C.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, zero_mul])
  have hM0 : iK M.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, mul_zero])
  refine ⟨fun h => hM0 (by rw [h, map_zero]), hC0, ?_⟩
  rw [← vV_mul hC0 hM0, ← hdetP', hdetP]
  exact vV_algebraMap_unit T.V hunit

end GlobalTheory.TwoBasesDet
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeProd

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_resM app_resM)

section Split

variable {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U V : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : VB.IsFrame e₁) (he₂ : VB.IsFrame e₂)


include h h₁ h₂ h₃ h₄ in
theorem repr_left (hV : V ≤ U) (y : Γ(F, V)) (i : Fin n) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.castAdd m i) =
      (he₁.basis hV).repr (i₁.app V y) i := by
  have key : (Finsupp.lapply (Fin.castAdd m i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₁.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₁ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₁]
      change _ = ((he₁.basis hV).repr ((resM F₁ hV) (e₁ j))) i
      rw [← IsFrame.basis_apply he₁ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₄]
      change _ = ((he₁.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
  exact LinearMap.congr_fun key y


include h h₁ h₂ h₃ h₄ in
theorem repr_right (hV : V ≤ U) (y : Γ(F, V)) (i : Fin m) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.natAdd n i) =
      (he₂.basis hV).repr (i₂.app V y) i := by
  have key : (Finsupp.lapply (Fin.natAdd n i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₂.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₂ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₃]
      change _ = ((he₂.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₂]
      change _ = ((he₂.basis hV).repr ((resM F₂ hV) (e₂ j))) i
      rw [← IsFrame.basis_apply he₂ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.natAdd_inj]
  exact LinearMap.congr_fun key y


include h h₁ h₂ h₃ h₄ in
theorem detUnit_append {U' : S.Opens} {e₁' : Fin n → Γ(F₁, U')} {e₂' : Fin m → Γ(F₂, U')}
    (he₁' : VB.IsFrame e₁') (he₂' : VB.IsFrame e₂') (hV : V ≤ U) (hV' : V ≤ U') :
    (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).detUnit
                 (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁' he₂') hV hV' =
      he₁.detUnit he₁' hV hV' * he₂.detUnit he₂' hV hV' := by
  refine Units.ext ?_
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).toMatrix
      (fun k => resM F hV' (Fin.append (fun i => p₁.app U' (e₁' i)) (fun j => p₂.app U' (e₂' j)) k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        ((he₁.basis hV).toMatrix fun i => resM F₁ hV' (e₁' i)) 0 0
        ((he₂.basis hV).toMatrix fun i => resM F₂ hV' (e₂' i))) := by
    ext k l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      simp only [Module.Basis.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fin.append_left,
        Fin.append_right, Matrix.zero_apply]
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₁]; rfl
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₄]
      change ((he₁.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₃]
      change ((he₂.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₂]; rfl
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Split

section Prod

open GlobalTheory.Conormal

variable {S : Scheme.{0}} (G H : Over S) [GrpObj G] [GrpObj H]

theorem lbIso_det_conormal_prod [QuasiSeparated G.hom] [QuasiSeparated H.hom] (g h : ℕ)
    (hG : IsVB (omega G) g) (hH : IsVB (omega H) h) (t : 𝟙_ (Over S) ⟶ G ⊗ H) (ht : t = lift η[G] η[H]) :
    LBIso (VB.det (conormal (sec t)) (g + h)) (CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)) := by
  subst ht
  have i₁ : η[G] ≫ lift (𝟙 G) (toUnit G ≫ η[H]) = lift η[G] η[H] := by simp
  have i₂ : η[H] ≫ lift (toUnit H ≫ η[G]) (𝟙 H) = lift η[G] η[H] := by simp
  have p₁ := lift_fst η[G] η[H]
  have p₂ := lift_snd η[G] η[H]
  have c₁ : η[H] ≫ toUnit H ≫ η[G] = η[G] := by simp
  have c₂ : η[G] ≫ toUnit G ≫ η[H] = η[H] := by simp
  have H₀ := cotMap_prod i₁ i₂ p₁ p₂
  have H₁ := (cotMap_comp p₁ i₁ (lift_fst _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₂ := (cotMap_comp p₂ i₂ (lift_snd _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₃ := (cotMap_comp p₁ i₂ (lift_fst _ _) c₁).trans (cotMap_eq_zero rfl _)
  have H₄ := (cotMap_comp p₂ i₁ (lift_snd _ _) c₂).trans (cotMap_eq_zero rfl _)
  let L := CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)
  have hL : L.IsLB := CechPic.isLB_tens hG.isLB_det hH.isLB_det
  have he : ∀ p : L.ι, IsFrame (Fin.append
      (fun i => (cotMap (fst G H) p₁).app (L.U p) (resM (omega G) inf_le_left (p.1.e i)))
      (fun j => (cotMap (snd G H) p₂).app (L.U p) (resM (omega H) inf_le_right (p.2.e j)))) := fun p =>
    GlobalTheory.TorusCot.isFrame_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
  refine LBIso.symm (lbIso_det_of_frames hL _ he fun p q => ?_).2
  refine Eq.trans ?_ (detUnit_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
    (q.1.isFrame.res inf_le_left) (q.2.isFrame.res inf_le_right) inf_le_left inf_le_right).symm
  exact congrArg₂ (· * ·) ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)
    ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)

end Prod

end GlobalTheory.HodgeProd
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory

theorem simpleU_rev_and_sq : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  intro n k
  have hk := k.isLt
  have hn : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  unfold simpleU partnerU
  split_ifs with h
  · refine ⟨fun i => ?_, ?_⟩
    · have hi := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs at * <;> simp only [Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE] at * <;> omega
    · have hnd : [lo k, lo (⟨k.val + 1, h⟩ : Fin (n / 2)), (lo k).rev,
          (lo (⟨k.val + 1, h⟩ : Fin (n / 2))).rev].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          and_true, Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE, not_false_eq_true]
        omega
      have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [hc.symm.mul_mul_mul_comm, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  · refine ⟨fun i => ?_, Equiv.swap_mul_self _ _⟩
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, lo] <;> omega

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
end
