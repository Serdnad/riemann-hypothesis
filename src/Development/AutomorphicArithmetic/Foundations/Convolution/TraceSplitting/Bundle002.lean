module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
public import GroundTheory.GlobalFields.KummerTheory.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep

namespace UpperTheory.ConvolutionTheory.T

section Rep
variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def pull (e : G ≃ₜ* H) (τ : SmIrr H) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (e : G →* H)
  smooth := fun x => (τ.smooth x).preimage e.continuous
  irred := by
    refine (OrderIso.isSimpleOrder_iff (β := Subrepresentation τ.ρ)
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => ?_⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (e g) hv⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl
        map_rel_iff' := Iff.rfl }).2 τ.irred
    have := S.apply_mem_toSubmodule (e.symm g) hv
    simpa using this

end Rep

section Trace
variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup V] [Module ℂ V]

private theorem hasFinTrace_smul {A : V →ₗ[ℂ] V} {c s : ℂ} (hc : c ≠ 0) (h : HasFinTrace A s) :
    HasFinTrace (c • A) (c * s) := by
  obtain ⟨hf, rfl⟩ := h
  have hR : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul A c hc
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((c • A).restrict h1) =
        c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    rintro _ rfl h1 h2
    have : (c • A).restrict h1 = c • A.restrict h2 := by
      ext x
      simp
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hR ▸ hf, key _ hR _ _⟩

private theorem hasTrace_map (e : G ≃ₜ* H) (mF : Measure G) (mE : Measure H) (c : NNReal) (hc : c ≠ 0)
    (h : mE = c • mF.map e) (π : Representation ℂ H V) (ψ : H → ℂ) (s : ℂ)
    (hs : HasTrace mF (π.comp (e : G →* H)) (fun g => ψ (e g)) s) : HasTrace mE π ψ ((c : ℂ) * s) := by
  obtain ⟨A, hA, hf⟩ := hs
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩
  obtain ⟨hi, hl⟩ := hA x l
  have hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e) := hme.integrable_map_iff.2 hi
  subst h
  refine ⟨hi'.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]
  simp [NNReal.smul_def]

end Trace

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.pullBack :
    UpperTheory.ConvolutionTheory.T.PullBack := by
  intro F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'
  obtain ⟨⟨e, he⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
  have hmap : (mF.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map mF e
  have hscal := Measure.isMulLeftInvariant_eq_smul mE (mF.map e)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)
  have hc0 : mE.haarScalarFactor (mF.map e) ≠ 0 := hpos.ne'
  refine ⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · rintro τ₁ ⟨E₁⟩
    refine ⟨E₁.toLinearEquiv, fun g x => ?_⟩
    rw [← he g]
    exact LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x
  · intro ψ s h
    refine hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_
    have hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g) :=
      funext fun g => by rw [he g]
    rw [hfun]
    exact h
  · intro J U hJ hU
    have hU' : ∀ g, g ∈ U ↔ e g ∈ J := fun g => by rw [he g]; exact hU g
    have hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1)) := Set.ext hU'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hset]
      exact e.toHomeomorph.isCompact_preimage.2 hJ.1
    · rw [hset]
      exact hJ.2.preimage e.continuous
    · intro h h0
      refine h (eq_bot_iff.2 fun x hx => ?_)
      have hx' : x ∈ fixedVectors (pull e τ').ρ U := fun u hu => hx _ ((hU' u).1 hu)
      rw [h0] at hx'
      exact hx'
    · intro φ hφ hinv
      refine ⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous,
        hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩
      · have hu' : e.symm u ∈ U := (hU' _).2 (by simpa using hu)
        simpa [map_mul] using hinv _ hu' (e.symm g)
      · funext g
        rw [← he g]
        simp
end
end

section

open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.T

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  have hK : ∀ x : E, Valued.v (galEquiv v σ w u h (algebraMap E (w.adicCompletion E) x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    have hx := valuation_smul σ w x
    rw [← h] at hx
    rw [galEquiv_algebraMap, HeightOneSpectrum.algebraMap_adicCompletion,
      HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using hx
  have hclosed : IsClosed {y : w.adicCompletion E | Valued.v (galEquiv v σ w u h y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (galEquiv v σ w u h y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_galEquiv v σ w u h).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on y hclosed hK

private theorem galFin_apply (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v)
    (u : PlacesOver E v) :
    galFin σ v y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  have h1 : galFin σ v (tensorEquiv' E v t) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
    simp [galFin, galOf]
  rw [h1]
  clear h1
  induction t with
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
    congr 1
    · exact (galEquiv_algebraMap v σ _ _ _ x).symm
    · exact ((galEquiv v σ _ _ (eq_smul_inv_smul v σ u)).commutes a).symm

variable {w u : HeightOneSpectrum (𝓞 E)} (φ : w.adicCompletion E →+* u.adicCompletion E)

private theorem le_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y ≤ 1) : valuation (u.adicCompletion E) (φ y) ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).le_one_iff_le_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one.1 hy

private theorem lt_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : valuation (u.adicCompletion E) (φ y) < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).lt_one_iff_lt_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one.1 hy

private theorem eq_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y = 1) : valuation (u.adicCompletion E) (φ y) = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).eq_one_iff_eq_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hy

private theorem integral_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.integralGL (u.adicCompletion E) n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  rw [← map_inv]
  simp only [Valuation.mem_integer_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j => le_of_val φ hφ (hg.2 i j)⟩

private theorem iwahori_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.iwahori (u.adicCompletion E) n := by
  rw [GLnLocal.mem_iwahori_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j h => lt_of_val φ hφ (hg.2.1 i j h),
    fun i => eq_of_val φ hφ (hg.2.2 i)⟩

end

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.offStable :
    UpperTheory.ConvolutionTheory.T.OffStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v
  have hv : ∀ (u : PlacesOver E v) y,
      Valued.v ((galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom y) = Valued.v y :=
    fun u y => UpperTheory.ConvolutionTheory.T.val_gal v σ _ _ _ y
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (u : PlacesOver E v),
      GM.cmp u (mapGL n (galFin σ v) x) =
        mapGL n (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom (GM.cmp (σ⁻¹ • u) x) :=
    fun x u => Units.ext (Matrix.ext fun a b => UpperTheory.ConvolutionTheory.T.galFin_apply σ v _ u)
  refine ⟨fun x hx u => ?_, fun x hx u => ?_,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u), ?_⟩,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u),
      fun g => by simp [Subgroup.mem_iInf]⟩,
    fun w => ⟨And.intro (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n),
      And.intro (GLnLocal.isCompact_iwahori _ n) (GLnLocal.isOpen_iwahori _ n),
      GLnLocal.iwahori_le_integralGL _ n⟩⟩
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.integral_map _ n (hv u) (hx _)
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.iwahori_map _ n (hv u) (hx _)
  · ext g
    simp [Subgroup.mem_iInf, unitSet, GM.cmp]
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

open scoped ComplexConjugate

theorem tyEx_of (hLev : SplitLev) (hSt : SplitStable) (hMa : SplitMatch) (hIn : InertData) (hOff : OffStable)
    (hTyp : TypedEx) (hEig : EigBasic) : TyEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV q w₀ hq S hqS hunr hsph mk
  have h1 : ∀ {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G), IsChr J 1 := fun J =>
    ⟨IsLocallyConstant.const 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm⟩
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  have key : ∀ v : Pl F, ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ)
      (c : ℂ) (f₀ : Gw n v → ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
      (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
      (GM.Split E v → ∀ u, χ u = 1) ∧
      (v ∉ S → v ≠ q → (∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ χ u = 1) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧ UF = GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v = q → (∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        UF = GLnLocal.iwahori (v.adicCompletion F) n) ∧
      (v ∈ S → IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧ IsOpen (UF : Set (Gw n v)) ∧
        UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v ∈ S → ¬ GM.Split E v → (∀ u, RankOne μ V u.1 (J u) (χ u)) ∧
        GM.MatchAt σ v c (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f₀ ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f₀ ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f₀ (y * g) = f₀ g) ∧
      (v ∈ S → GM.Split E v → (∀ g, g ∈ UF ↔ mapGL n (completionMap v (mk v).1) g ∈ J (mk v)) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
        ∀ ψ : Gw n (mk v).1 → ℂ, Test ψ → (∀ u ∈ J (mk v), ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ))
          (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) g) ∧
        ∀ y ∈ UF, ∀ g, ψ (mapGL n (completionMap v (mk v).1) (y * g)) = ψ (mapGL n (completionMap v (mk v).1) g)) := by
    intro v
    obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := hOff F E σ hσ hp n hn v
    by_cases hvS : v ∈ S
    · have hvq : v ≠ q := fun h => hqS (h ▸ hvS)
      by_cases hv : GM.Split E v
      · obtain ⟨U, J, hU, hUle, hJ⟩ := hLev F E σ hσ hp n hn μ V hV v hv
        obtain ⟨s1, s2⟩ := hSt F E σ hσ hp n hn v hv U J fun u => (hJ u).2.1
        obtain ⟨UE, e1, e2, e3⟩ := s2 hU hUle
        obtain ⟨c, hc⟩ := hMa F E σ hσ hp n hn v (mk v) hv U J hU fun u => ⟨(hJ u).1, (hJ u).2.1⟩
        refine ⟨J, fun _ => 1, c, 0, UE, U, fun u => ⟨(hJ u).1, h1 _, ?_⟩, fun x hx => ⟨s1 x hx, rfl⟩, fun _ _ => rfl,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨e2, e3, hU.2, hUle⟩, fun _ h => absurd hv h,
          fun _ _ => ⟨(hJ _).2.1, e1, hc⟩⟩
        rw [(hEig E n μ u.1 _ _ (hJ u).1 (h1 _)).2.1]; exact (hJ u).2.2
      · obtain ⟨J, χ, f, UE, UF, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hIn F E σ hσ hp n hn μ V hV v hv
        exact ⟨J, χ, 1, f, UE, UF, fun u => ⟨(i1 u).1, (i1 u).2.1, (i1 u).2.2.2⟩, i2, fun h => absurd h hv,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨i6, i7, i8, i9⟩,
          fun _ _ => ⟨fun u => (i1 u).2.2.1, i3, i4, i5, i10, i11⟩, fun _ h => absurd h hv⟩
    · have hs : ∀ u : PlacesOver E v, V ⊓ fixL μ u.1 (GLnLocal.integralGL (u.1.adicCompletion E) n) ≠ ⊥ := fun u =>
        hsph u.1 (by rw [show u.1.under (𝓞 F) = v from hu v u]; exact hvS)
      by_cases hvq : v = q
      · refine ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U2, GLnLocal.iwahori (v.adicCompletion F) n,
          fun u => ⟨(o5 u.1).2.1, h1 _, ?_⟩, fun x hx => ⟨o2 x hx, rfl⟩, fun _ _ => rfl, fun _ h => absurd hvq h,
          fun _ => ⟨fun _ => rfl, o4, rfl⟩, fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).2.1 (h1 _)).2.1]
        refine fun h => hs u (eq_bot_iff.2 (h ▸ inf_le_inf_left _ ?_))
        exact biInf_mono fun y hy => Subgroup.map_mono (o5 u.1).2.2 hy
      · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U1,
          GLnLocal.integralGL (v.adicCompletion F) n, fun u => ⟨(o5 u.1).1, h1 _, ?_⟩, fun x hx => ⟨o1 x hx, rfl⟩,
          fun _ _ => rfl, fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, o3, rfl⟩, fun h => absurd h hvq,
          fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).1 (h1 _)).2.1]; exact hs u
  choose J χ c f₀ UE UF k1 k2 k3 k4 k5 k6 k7 k8 using key
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => χ (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), J' u.1 = J v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  have eχ : ∀ v (u : PlacesOver E v), χ' u.1 = χ v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  let T : Ty σ n q w₀ :=
    { S := S, q_not := hqS, J := J', χ := χ', mk' := mk
      co := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).1
      chr := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.1
      off := fun w a b => (k4 _ a b).1 ⟨w, ⟨rfl⟩⟩
      at_q := fun w => (eJ q w).trans ((k5 q rfl).1 w)
      triv := fun v hv w => (eχ v w).trans (k3 v hv w)
      stable := fun v x hx => by simp only [eJ, eχ] at hx ⊢; exact k2 v x hx }
  have hsp : ∀ v, v ∈ T.sp ↔ v ∈ S ∧ GM.Split E v := fun v => Finset.mem_filter
  refine ⟨T, rfl, rfl, hTyp E n μ V hV J' χ' (fun w => ⟨T.co w, T.chr w⟩) ?_ (fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.2),
    fun v hv hn u => ?_, c, f₀, UF, fun v hv g => ?_, fun ψ hψ => ?_⟩
  · have hf : {w : Pl E | w.under (𝓞 F) ∈ insert q S}.Finite := by
      refine ((insert q S).finite_toSet.biUnion fun v _ => Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
      exact Set.mem_biUnion hw ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
    refine Filter.mem_of_superset hf.compl_mem_cofinite fun w hw => ?_
    have hw' : w.under (𝓞 F) ∉ insert q S := hw
    rw [Finset.mem_insert, not_or] at hw'
    exact T.off w hw'.2 hw'.1
  · change RankOne μ V u.1 (J' u.1) (χ' u.1)
    rw [eJ, eχ]; exact (k7 v hv hn).1 u
  · change _ ↔ _ ∈ J' (mk v).1
    rw [eJ]; exact (k8 v ((hsp v).1 hv).1 ((hsp v).1 hv).2).1 g
  · have hψ' : ∀ v ∈ S, GM.Split E v → _ := fun v a b => (k8 v a b).2.2 (ψ v) (hψ v ((hsp v).2 ⟨a, b⟩)).1 (by
      have := (hψ v ((hsp v).2 ⟨a, b⟩)).2
      change ∀ u ∈ J' (mk v).1, _ at this
      rw [eJ] at this; exact this)
    let φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then GM.prodFn (Function.update
          (fun u : PlacesOver E v => ((J v u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) (ψ v))
        else GM.prodFn fun u : PlacesOver E v => (J v u : Set (Gw n u.1)).indicator fun x => conj (χ v u x))
      else if h : v = q then GM.iwFn (h ▸ w₀) 0 else (unitSet E n v).indicator 1
    let f : ∀ v : Pl F, Gw n v → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then fun g => ψ v (mapGL n (completionMap v (mk v).1) g) else f₀ v)
      else if v = q then (GM.iwCoset v 0).indicator 1 else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    let L : GM.Loc σ n q w₀ :=
      { S := S, q_not := hqS, unr := hunr, φ := φ, f := f, c := c, UE := UE, UF := UF
        test := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨(hψ' v hv b).2.1.1, (hψ' v hv b).2.1.2, (hψ' v hv b).2.2.1.1, (hψ' v hv b).2.2.1.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact ⟨(k7 v hv b).2.2.1.1, (k7 v hv b).2.2.1.2, (k7 v hv b).2.2.2.1.1, (k7 v hv b).2.2.2.1.2⟩
        lev := k6
        inv := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨fun y hy => (hψ' v hv b).2.2.2.1 y (((k8 v hv b).2.1 y).1 hy), (hψ' v hv b).2.2.2.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.2.2.2
        mat := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact (hψ' v hv b).1
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.1
        at_q := ⟨by simp only [φ, if_neg hqS, dif_pos], by simp only [f, if_neg hqS, if_pos], (k5 q rfl).2⟩
        off := fun v a b => ⟨by simp only [φ, if_neg a, dif_neg b], by simp only [f, if_neg a, if_neg b], (k4 v a b).2⟩ }
    refine ⟨L, ⟨rfl, hψ, fun v hv => ?_, fun v a b => ?_⟩, fun _ _ => ⟨rfl, rfl⟩, fun v hv => ?_, fun v a b => ?_⟩
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change φ v = GM.prodFn (Function.update (fun u : PlacesOver E v => ((J' u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ))
        (mk v) (ψ v)) ∧ ∀ g, g ∈ UE v ↔ ∀ u, GM.cmp u g ∈ J' u.1
      simp only [eJ, φ, if_pos a, if_pos b, true_and]
      exact (k8 v a b).2.1
    · change φ v = GM.prodFn fun u : PlacesOver E v => (J' u.1 : Set (Gw n u.1)).indicator fun x => conj (χ' u.1 x)
      have a' : v ∈ S := a
      simp only [eJ, eχ, φ, if_pos a', if_neg b]
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change f v = _
      simp only [f, if_pos a, if_pos b]
      rfl
    · change f v = _
      simp only [f, if_pos a, if_neg b]

end UpperTheory.ConvolutionTheory.T
end
end

section

open NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1

private theorem cmp_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {v : Pl F} (u : PlacesOver E v) :
    Continuous (GM.cmp (n := n) u : GL (Fin n) (CompletionsOver E v) → GL (Fin n) (u.1.adicCompletion E)) :=
  Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map (continuous_apply u),
      Units.continuous_coe_inv.matrix_map (continuous_apply u)⟩

theorem UpperTheory.ConvolutionTheory.T.splitStable :
    UpperTheory.ConvolutionTheory.T.SplitStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v hs U J hJ
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  obtain ⟨D, w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      GM.cmp (w i) x = mapGL n (completionMap v (w i).1) (D.comp n i x) := fun x i =>
    Units.ext (Matrix.ext fun a b => (hw _ i).symm)
  have hshift : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      D.comp n i (mapGL n (galFin σ v) x) = D.comp n (i + 1) x := fun x i =>
    Units.ext (Matrix.ext fun a b => D.map_shift _ i)
  refine ⟨fun x hx u => ?_, fun hCO hle => ?_⟩
  · obtain ⟨i, rfl⟩ := w.surjective u
    rw [hc]
    refine (hJ (w i) _).1 ?_
    rw [hshift, hJ (w (i + 1)), ← hc]
    exact hx _
  · have hJo : ∀ u, IsOpen (J u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u => by
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h : (J u : Set (GL (Fin n) (u.1.adicCompletion E))) = e.symm ⁻¹' (U : Set (GL (Fin n) (v.adicCompletion F))) := by
        ext y
        have h1 := hJ u (e.symm y)
        rw [← he, e.apply_symm_apply] at h1
        exact h1.symm
      rw [h]
      exact hCO.2.preimage e.symm.continuous
    refine ⟨⨅ u, (J u).comap (GM.cmp u), fun g => by simp [Subgroup.mem_iInf], ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun u => (hJo u).preimage (cmp_continuous u)
    · intro g hg u
      have hgu : GM.cmp u g ∈ J u := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hg u)
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h2 : e.symm (GM.cmp u g) ∈ U := by
        rw [hJ u, ← he, e.apply_symm_apply]
        exact hgu
      have h3 := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).2.1 _ |>.2 (hle h2)
      rw [← he, e.apply_symm_apply] at h3
      exact h3
end
