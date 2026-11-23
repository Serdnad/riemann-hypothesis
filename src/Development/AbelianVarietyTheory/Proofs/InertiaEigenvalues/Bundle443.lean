module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityRelaxedSelmerDualSelmerNewPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle085
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle428
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle431
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.reciprocity_relaxedSelmer_dualSelmer_newPlace : PoitouTateTotallyComplex → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ∀ (y : Z1 (repOn ρ κ⁻¹ Y')) (f : GE N → Fin D.R.r → Y), DualSel bkP i s κ ρ β Q y → SelC bkP i s κ Y Q' f → vecPair D.R.r β (f γ) (y.1 σ) = vecPair D.R.r β (f (cConj X γ)) (y.1 (cConj X σ)) := by
  first | exact @GlobalTheory.NewRecip.reciprocity | exact GlobalTheory.NewRecip.reciprocity | (intros; apply GlobalTheory.NewRecip.reciprocity <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.HTBasis

variable {l : ℕ} [Fact l.Prime]

def repOf {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp r)

theorem repOf_apply {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (v : Fin m → ↥LL.1) :
    repOf r g v = (r g : Matrix (Fin m) (Fin m) ↥LL.1).mulVec v := rfl

variable (P : LocPrime l) (LL : FinExt l) (m : ℕ)

def embF : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp LL.1.val

theorem embF_apply (x : ↥LL.1) : embF P LL x = algebraMap (Om l) P.R.BdR (x : Om l) := rfl

def mulF : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (embF P LL) (AlgHom.id ℚ_[l] P.R.BdR) fun _ _ => Commute.all _ _

@[simp] theorem mulF_tmul (c : ↥LL.1) (b : P.R.BdR) : mulF P LL (c ⊗ₜ[ℚ_[l]] b) = embF P LL c * b := by
  simp [mulF]

def coordF : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin m → P.R.BdR) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : Fin m → ↥LL.1) (b : P.R.BdR) j => embF P LL (v j) * b)
    (fun v v' b => by funext j; simp [add_mul])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_assoc])
    (fun v b b' => by funext j; simp [mul_add])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_left_comm]))

@[simp] theorem coordF_tmul (v : Fin m → ↥LL.1) (b : P.R.BdR) :
    coordF P LL m (v ⊗ₜ[ℚ_[l]] b) = fun j => embF P LL (v j) * b := rfl

section Lemmas

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (m : ℕ)

theorem coordF_sm (r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) r x) = mulF P LL r • coordF P LL m x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add (f := _), LinearMap.add_apply, hr, hs, add_smul]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
    | tmul v b' =>
      funext j
      simp only [GlobalTheory.DRFil.sm_tmul, coordF_tmul, mulF_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring

theorem embF_mem_fil (K : FinExt l) (c : ↥LL.1) : embF P LL c ∈ (P.PD K).Fil 0 :=
  (GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem _)

theorem coordF_mem_fil (K : FinExt l) {n : ℤ} {x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n) (j : Fin m) :
    coordF P LL m x j ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K (v j)) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_mem_fil (K : FinExt l) {n : ℤ} {r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR}
    (hr : r ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) n) : mulF P LL r ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _)]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K v) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_idem (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥K.1, ((τ x : ↥LL.1) : Om l) = (x : Om l)) :
    mulF P LL (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ

  rw [h, map_sum]
  have e : ∀ i, mulF P LL (a i ⊗ₜ[ℚ_[l]] algebraMap ↥K.1 P.R.BdR (c i)) =
      algebraMap (Om l) P.R.BdR (((a i * τ (c i) : ↥LL.1)) : Om l) := by
    intro i
    rw [mulF_tmul, embF_apply, IntermediateField.coe_mul, map_mul, hτ]
    rfl

  simp only [e, ← map_sum]
  have h2 := congrArg (fun x : ↥LL.1 => (x : Om l)) h1
  simp only [IntermediateField.coe_sum, IntermediateField.coe_one] at h2
  simp only [IntermediateField.coe_mul] at h2 ⊢
  rw [h2, map_one]

theorem coordF_act (K : FinExt l) (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (hg : ∀ x ∈ LL.1, (g : GQ l) x = x) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (actVdR (P.PD K) (repOf r) g x) =
      ((r g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
        (fun j => P.actQdR (g : GQ l) (coordF P LL m x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    have hfix : ∀ c : ↥LL.1, P.actQdR (g : GQ l) (embF P LL c) = embF P LL c := fun c => by
      rw [embF_apply, P.actQdR_Om, hg _ c.2]
    funext j

    simp only [actVdR, AlgebraTensorModule.map_tmul, coordF_tmul, repOf_apply, P.PD_actdR,
    Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, hfix, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    rw [mul_assoc]
    exact congrArg _ (congrArg _ (P.PD_actdR K g b))

end Lemmas

section Theta

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def thetaOf (T : LocTied l P AI) : Formalism.MainNotions.LocalSituation.ThetaL P AI :=
  (GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI T).some

def colHT (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℂ_[l] :=
  Matrix.of fun j i => J.θ (((GlobalTheory.DeRhamSymbol.tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j)

end Theta

end GlobalTheory.HTBasis
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

theorem isTateEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' χ χ' e hψ hχ he
  classical
  obtain ⟨_, hv1, hord, hres, _⟩ := continuous_iso_keeps_valuation k k' i hi
  set u : kˣ →* k'ˣ := Units.map i.toRingHom.toMonoidHom with hu
  have hcoe : ∀ x : kˣ, ((u x : k'ˣ) : k') = i x := fun x => rfl
  have hle : ∀ x y : k, valuation k' (i x) ≤ valuation k' (i y) ↔ valuation k x ≤ valuation k y := by
    intro x y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy' : i y ≠ 0 := by simpa using hy
      have h1 := hv1 (x / y)
      rw [map_div₀, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hy'),
        div_le_one₀ ((Valuation.pos_iff _).2 hy)] at h1
      exact h1
  have hsurj : ∀ x' : k'ˣ, ∃ x : kˣ, u x = x' := fun x' =>
    ⟨Units.map i.symm.toRingHom.toMonoidHom x', by ext; simp [hu]⟩
  have huinj : Function.Injective u := fun x y h => by
    ext; exact i.injective (by simpa [hcoe] using congrArg (fun z : k'ˣ => (z : k')) h)
  have hunif : ∀ a : ℕ, ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧
      valuation k' (i p) = uniformizer k' ^ a := by
    intro a
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
    obtain ⟨q, hq, hq'⟩ := exists_unit_pow k' a
    refine ⟨p, hp, ?_⟩
    rw [← hq, ← hcoe, valuation_eq_iff_ord, hord, hp', hq']
  have hfilt : ∀ (x : kˣ) (b : ℕ), u x ∈ unitFilt k' b ↔ x ∈ unitFilt k b := by
    intro x b
    obtain ⟨p, hp, hp'⟩ := hunif b
    simp only [unitFilt, Set.mem_setOf_eq]
    have e1 : valuation k' ((u x : k'ˣ) : k') = 1 ↔ valuation k (x : k) = 1 := by
      rw [← ord_eq_zero_iff, ← ord_eq_zero_iff, hord]
    have e2 : valuation k' (((u x : k'ˣ) : k') - 1) ≤ uniformizer k' ^ b ↔
        valuation k ((x : k) - 1) ≤ uniformizer k ^ b := by
      have hs : i ((x : k) - 1) = i x - 1 := by rw [map_sub, map_one]
      rw [← hp, ← hp', hcoe, ← hle, hs]
    rw [e1, e2]
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  refine ⟨u c, a, R.image u, ?_, ?_, ?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := i.surjective x'
    rw [hcoe, hle, ← hc x]
    constructor
    · intro h y hy
      rw [← hψ]
      exact h (i y) ((hle y x).2 hy)
    · intro h y' hy'
      obtain ⟨y, rfl⟩ := i.surjective y'
      rw [hψ]
      exact h y ((hle y x).1 hy')
  · refine ⟨fun x' hx' => ?_, fun b hb => ?_⟩
    · obtain ⟨x, rfl⟩ := hsurj x'
      rw [hχ]
      exact ha.1 x ((hfilt x a).1 hx')
    · obtain ⟨x, hx, hx'⟩ := ha.2 b hb
      exact ⟨u x, (hfilt x b).2 hx, by rw [hχ]; exact hx'⟩
  · refine ⟨fun r' hr' => ?_, fun y' hy' => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr'
      rw [hord, hord]
      exact hR.1 r hr
    · obtain ⟨y, rfl⟩ := hsurj y'
      rw [hord, hord] at hy'
      obtain ⟨r, ⟨hr, hrv⟩, hru⟩ := hR.2 y hy'
      refine ⟨u r, ⟨Finset.mem_image_of_mem u hr, ?_⟩, ?_⟩
      · rw [hcoe, hcoe, hcoe, ← map_sub i, hle]
        exact hrv
      · rintro r' ⟨hr', hr'v⟩
        obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 hr'
        rw [hcoe, hcoe, hcoe, ← map_sub i, hle] at hr'v
        rw [hru r0 ⟨hr0, hr'v⟩]
  · rw [hres, Finset.sum_image (fun x _ y _ h => huinj h)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hχ, hcoe, hψ]

end GlobalTheory.LocalFieldIso
end

section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_trace_completion : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  first | exact @GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension | exact GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension | (intros; apply GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceOff

open Formalism.HermitianLattices.Ext.L3

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isConjPl_iff (D : D7) (P Q : PlE D.host) :
    IsConjPl D.host P Q ↔ ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ conjO D.host.E x ∈ Q.asIdeal := by
  constructor
  · intro h x
    exact h x (conjO D.host.E x) (by rw [conjO_coe, star_eq_hostConj])
  · intro h x y hy
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    subst this
    exact h x

noncomputable def conjPl (D : D7) (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (conjO D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : conjO D.host.E x ∈ P.asIdeal.comap (conjO D.host.E) := by
      rw [Ideal.mem_comap, conjO_conjO]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjO_conjO (K := D.host.E) x, this, map_zero]

theorem mem_conjPl (D : D7) (P : PlE D.host) (x : 𝓞 D.host.E) :
    x ∈ (conjPl D P).asIdeal ↔ conjO D.host.E x ∈ P.asIdeal := Iff.rfl

theorem conjPl_conjPl (D : D7) (P : PlE D.host) : conjPl D (conjPl D P) = P := by
  ext x
  rw [mem_conjPl, mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl (D : D7) (P : PlE D.host) : IsConjPl D.host P (conjPl D P) := by
  rw [isConjPl_iff]
  intro x
  rw [mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl' (D : D7) (P : PlE D.host) : IsConjPl D.host (conjPl D P) P := by
  rw [isConjPl_iff]
  intro x
  rfl

theorem conjIdeal_eq (D : D7) (P : PlE D.host) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl D P).asIdeal :=
  conjIdeal_eq_comap _

theorem isSplitPl_iff (D : D7) (P : PlE D.host) :
    IsSplitPl D.host P ↔ ∃ x : 𝓞 D.host.E, x ∈ P.asIdeal ∧ conjO D.host.E x ∉ P.asIdeal := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h _ (by rw [conjO_coe, star_eq_hostConj])⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    rw [this]; exact h

theorem conjPl_ne_of_split (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    (conjPl D P).asIdeal ≠ P.asIdeal := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  intro he
  apply hcx
  rw [← mem_conjPl, he]
  exact hx

theorem isSplitPl_conjPl (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    IsSplitPl D.host (conjPl D P) := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  rw [isSplitPl_iff]
  refine ⟨conjO D.host.E x, ?_, ?_⟩
  · rw [mem_conjPl, conjO_conjO]; exact hx
  · rw [mem_conjPl, conjO_conjO]; exact hcx

theorem exists_conj_off (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E))
    (P : PlE D.host)
    (hS0 : ∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0)
    (h2 : placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)))
    (hb : ∀ Q ∈ Sb, Q ∈ S0) (hP : IsSplitPl D.host P) (hPS : P ∉ S0) :
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  have hP'S : conjPl D P ∉ S0 := fun h => hPS (hS0 _ _ h (isConjPl_conjPl' D P))
  have hne := conjPl_ne_of_split D hP
  refine ⟨conjPl D P, isConjPl_conjPl D P, isSplitPl_conjPl D hP, hP'S, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [conjIdeal_eq]; exact hne, fun h => hPS (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq] at he
    have : Q = conjPl D P := HeightOneSpectrum.ext he
    exact hP'S (this ▸ hb Q (by exact_mod_cast hQ))
  · refine ⟨by rw [conjIdeal_eq, conjPl_conjPl]; exact hne.symm,
      fun h => hP'S (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq, conjPl_conjPl] at he
    have : Q = P := HeightOneSpectrum.ext he
    exact hPS (this ▸ hb Q (by exact_mod_cast hQ))
  · exact fun h => hPS (h2 h)
  · exact fun h => hP'S (h2 h)

end GlobalTheory.ConjPlaceOff
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  first | exact @GlobalTheory.PMon.Gauss.acris_mul_eq_zero | exact GlobalTheory.PMon.Gauss.acris_mul_eq_zero | (intros; apply GlobalTheory.PMon.Gauss.acris_mul_eq_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.deRhamDieudonne_spans_tensor_deRham_periods : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.Per.DeRhamSpan.tied_deRham_span | exact GlobalTheory.Per.DeRhamSpan.tied_deRham_span | (intros; apply GlobalTheory.Per.DeRhamSpan.tied_deRham_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

theorem _root_.GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  first | exact @GlobalTheory.HostImage.host_image_mem | exact GlobalTheory.HostImage.host_image_mem | (intros; apply GlobalTheory.HostImage.host_image_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.FrobSysCoef.main | exact GlobalTheory.FrobSysCoef.main | (intros; apply GlobalTheory.FrobSysCoef.main <;> assumption)
end
