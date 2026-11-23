module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdeleCharTwist

theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.exists_eq_exp <;> assumption

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.denseRange_fin <;> assumption

theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  apply GlobalTheory.CompanionTheory.AdeleCharLocal.ext_of_inf <;> assumption

theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

theorem exists_realHom [IsTotallyReal F] : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  exact ⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩

theorem exists_trace [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add (f := _), add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add (f := _), hadd, hy, hz, map_add (f := _), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

theorem exists_mul_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  intro F _ _ _ ψ ψ' hψ hψ'
  obtain ⟨a, ha⟩ := exists_trace hψ
  obtain ⟨a', ha'⟩ := exists_trace hψ'
  have h0 := trace_mul_ne_zero hψ ha
  refine ⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩
  refine ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul
    (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_
  have e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 =
      pairA F (algebraMap F _ (a' / a * x)) 0 :=
    Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)
  rw [e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]

end GlobalTheory.AdeleCharTwist
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.Determ

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (finiteSingle L v) := by
  apply GlobalTheory.CompanionTheory.InertOpen.continuous_finiteSingle <;> assumption

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (_root_.Neutral.B1.localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem denseRange_atFin (v : HeightOneSpectrum (𝓞 L)) : DenseRange (_root_.Formalism.L2.Host.atFin v) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have : Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [this]
    exact isOpen_compl_singleton
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, x, hx, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact x.ne_zero hk
  exact ⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem exists_prod_inf_mul_finPart (a : _root_.Neutral.B1.Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (Units.map (p w) a) : _root_.Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem loc_eq_one {ψ : _root_.Neutral.B1.Ideles L →* ℂˣ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ k, ψ (_root_.Neutral.B1.localIdele L v (_root_.Formalism.L2.Host.atFin v k)) = 1) (x : (v.adicCompletion L)ˣ) : ψ (_root_.Neutral.B1.localIdele L v x) = 1 :=
  congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (_root_.Neutral.B1.localIdele L v x)) (h := fun _ => 1)
    (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x

theorem inf_eq_one {ψ : _root_.Neutral.B1.Ideles L →* ℂˣ} (hψ : Continuous ψ) (h : ∀ k, ψ (_root_.Formalism.L2.Host.infDiag k) = 1)
    (y : ∀ w : InfinitePlace L, (w.Completion)ˣ) : ψ (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (y w)) = 1 := by
  refine congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer
    (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (y w))) (h := fun _ => 1)
    (hψ.comp (continuous_finsetProd _ fun w _ =>
      (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))) continuous_const (funext fun k => ?_)) y
  have h1 := h k
  unfold _root_.Formalism.L2.Host.infDiag at h1
  rw [MonoidHom.finsetProd_apply] at h1
  exact h1

theorem eq_one_of_components {ψ : _root_.Neutral.B1.Ideles L →* ℂˣ} (hψ : Continuous ψ)
    (hf : ∀ v k, ψ (_root_.Neutral.B1.localIdele L v (_root_.Formalism.L2.Host.atFin v k)) = 1) (hi : ∀ k, ψ (_root_.Formalism.L2.Host.infDiag k) = 1) (a : _root_.Neutral.B1.Ideles L) : ψ a = 1 := by
  obtain ⟨S, n, u, hu, rfl, -⟩ := exists_prod_unif_mul_unitIdl L a
  obtain ⟨y, hy⟩ := exists_prod_inf_mul_finPart u
  have h1 : ψ (finPartI L u) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x
  rw [← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]
  exact Finset.prod_eq_one fun v _ => by
    rw [map_zpow]
    erw [hf, one_zpow]

end GlobalTheory.Mem.Chr.Determ
end
end

section

namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  apply LevelTowerAlt.LocalPrimeBound.exists_prime_mem <;> assumption

end GlobalTheory.PrimeDvdNatCastMem
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.AeFix

theorem eventually_mem_fixed : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (x : π.V), ∀ᶠ v in Filter.cofinite, x ∈ GlobalTheory.PRep.fixed (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) := by
  intro E _ _ _ a π x
  filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp x.1 x.2).1.level.mem_nhds (by simp))] with w hw
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.AeFix
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem seamEx_lin_cpt {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem seamEx_coords {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    ∃ c : E ≃ₗ[ℂ] (Fin n → ℂ), ∀ x, c.symm (cpt σ x) = j (e x) := by
  let g : (Fin n → K) →ₛₗ[σ] E := j.comp e.toLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] E := lin (fun k => g (Pi.single k 1))
  have hf : ∀ x, f (cpt σ x) = j (e x) := fun x => seamEx_lin_cpt σ g x
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt σ (e.symm (b i)), by rw [hf]; simp⟩
  haveI : Module.Finite K V := Module.Finite.equiv e
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ E := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite ℂ E := Module.Finite.of_basis B
  have hr : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis b, ← e.finrank_eq]
    simp
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj
  exact ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, hf⟩

theorem seam_nonempty (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs)
    (s : Bool) (R : Read D X fc s) (cr : Crd A fc) : Nonempty (Seam R cr) := by
  choose cφ hφ using fun u => seamEx_coords D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u)
  obtain ⟨c, hc⟩ := seamEx_coords D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis
  refine ⟨{ cφ := cφ
            cF := lin (fun k => R.jV (Pi.single k 1))
            eR :=
              { toFun := fun F => X.iC cr true Bs.μ0 (cjv s (c F))
                map_add' := fun F G => ?_
                map_smul' := fun a F => ?_ }
            cφ_eq := hφ
            cF_eq := fun y => seamEx_lin_cpt _ _ y
            eR_eq := fun y => ?_ }⟩
  · rw [← map_add (f := _)]
    congr 1
    funext i
    simp [cjv]
  · rw [← map_smul]
    congr 1
    funext i
    simp [cjv]
  · show X.iC cr true Bs.μ0 (cjv s (c _)) = _
    rw [← hc, LinearEquiv.apply_symm_apply]
    congr 1
    funext i
    simp [cjv, cpt, R.twist]

end GlobalTheory.Mem.SJ

end
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem denseRange_of_im_ne_zero {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (h : ∃ a, (σ a).im ≠ 0) :
    DenseRange σ := by
  obtain ⟨a, ha⟩ := h
  have hg : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by fun_prop
  have hs : Function.Surjective fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by
    intro z
    refine ⟨(z.re - z.im / (σ a).im * (σ a).re, z.im / (σ a).im), ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
      field_simp
      ring
  have hq : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hc := hs.denseRange.comp hq hg
  refine hc.mono ?_
  rintro _ ⟨⟨p, q⟩, rfl⟩
  exact ⟨(p : K) + (q : K) * a, by simp⟩

theorem normAt_sq_eq_majAt_re {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem fnorm_cjv_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (s : Bool), (∀ a, (InfinitePlace.mk σ).embedding a = cj s (σ a)) → (∃ a, (σ a).im ≠ 0) → ∀ (A : HLat K) (d : ℕ) (L : Submodule (RingOfIntegers K) (Fin d → K)) (Xf : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (e : (Fin d → K) ≃ₗ[K] A.V), HLatTie A L Xf e → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : A.V →ₛₗ[σ] W) (c : W ≃ₗ[ℂ] (Fin d → ℂ)), (∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖j x‖) → (∀ x, c.symm (cpt σ x) = j (e x)) → ∀ w : W, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s (c w)) = ‖w‖ := by
  intro K _ _ _ σ s htw hnr A d L Xf e hT W _ _ j c hn hc w
  have hd : DenseRange (cpt σ : (Fin d → K) → Fin d → ℂ) :=
    DenseRange.piMap (fun _ : Fin d => denseRange_of_im_ne_zero σ hnr)
  have hcj : Continuous (cj s) := by
    cases s
    · exact continuous_id
    · exact Complex.continuous_conj
  have h1 : Continuous fun z : Fin d → ℂ => Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) := by
    unfold Formalism.DivisionValues.fnorm Formalism.HermitianLatticesTheory.cnorm cjv Matrix.mulVec dotProduct
    fun_prop
  have h2 : Continuous fun z : Fin d → ℂ => ‖c.symm z‖ :=
    (LinearMap.continuous_of_finiteDimensional c.symm.toLinearMap).norm
  have key : ∀ z : Fin d → ℂ, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) = ‖c.symm z‖ := by
    intro z
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    rw [hc, ← hn, normAt_sq_eq_majAt_re, hT.metric, ← normAt_sq_eq_majAt_re]
    have hv : cjv s (cpt σ x) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) (InfinitePlace.mk σ) x := by
      funext i
      simp [cjv, cpt, Formalism.HermitianLatticesTheory.vecAt, htw]
    rw [hv]
    rfl
  rw [key, c.symm_apply_apply]

end GlobalTheory.Mem.SJ
end

section

noncomputable section

namespace GlobalTheory.Mem.SJ.Pair

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}
  {R : Read D X fc s} {cr : Crd A fc}

theorem cpt_single {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (i : Fin n) :
    (fun k => σ ((Pi.single i 1 : Fin n → K) k)) = (Pi.single i 1 : Fin n → ℂ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem sum_coord_jN (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.jN u (R.eNu u (Pi.single i 1)) = φ := by
  have h : ∀ i, D.jN u (R.eNu u (Pi.single i 1)) = (M.cφ u).symm (Pi.single i 1) := fun i => by
    rw [← M.cφ_eq]
    exact congrArg _ (cpt_single D.what₂.embLL i)

  simp only [h, ← map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_coord_eMu (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.eMu u (D.jN u (R.eNu u (Pi.single i 1))) = D.eMu u φ := by

  simp only [← map_smul, ← map_sum]
  rw [sum_coord_jN]

theorem sum_coord_heq (M : Seam R cr) (u w : D.what₂.Word) (hw : w = u)
    (b : Fin ((fc X.zs).Dc.a (R.wU u)) → (D.mem w).A.Mram)
    (hb : ∀ i, HEq (b i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) (φ : D.what₂.Mu u) :
    HEq (∑ i, M.cφ u φ i • b i) (D.eMu u φ) := by
  subst hw
  have : b = fun i => D.eMu w (D.jN w (R.eNu w (Pi.single i 1))) := funext fun i => eq_of_heq (hb i)
  subst this
  exact heq_of_eq (sum_coord_eMu M w φ)

theorem inner_tw_of_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (x y : Tw s E) (κ₀ : ℂ) (v : E)
    (hx : Tw.out x = κ₀ • v) : ⟪x, y⟫_ℂ = cj s (starRingEnd ℂ κ₀ * ⟪v, Tw.out y⟫_ℂ) := by
  rw [Tw.inner_eq, hx, inner_smul_left]

end GlobalTheory.Mem.SJ.Pair

end
end
