module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle206
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Map
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

theorem d_cup_one (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a m : ℕ} (h : 1 + a = m) (y : CH.Cn F₂ a) :
    CH.d F₃ m (P.cupC h b y) = -P.cupC (by omega : 1 + (a + 1) = m + 1) b (CH.d F₂ a y) := by
  rw [CrystallineSemistableComparison.P.leibniz, hb]
  simp

def cupMap (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) (a : ℕ) :
    CH.H F₂ a →ₗ[R] CH.H F₃ (a + 1) :=
  Submodule.mapQ _ _ ((((P.cupC (Nat.add_comm 1 a) b).comp (Submodule.subtype _))).codRestrict _ fun y => by
    change CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y.1) = 0
    rw [d_cup_one P b hb]
    have : CH.d F₂ a y.1 = 0 := y.2
    rw [this, map_zero, neg_zero]) (by
      intro y hy
      change P.cupC (Nat.add_comm 1 a) b y.1 ∈ (CH.cx F₃).B (a + 1)
      have hy' : y.1 ∈ (CH.cx F₂).B a := hy
      cases a with
      | zero =>
        have : y.1 = 0 := hy'
        rw [this, map_zero]
        exact Submodule.zero_mem _
      | succ m =>
        obtain ⟨t, ht⟩ := hy'
        refine ⟨-P.cupC (Nat.add_comm 1 m) b t, ?_⟩
        change CH.d F₃ _ _ = _
        rw [map_neg, d_cup_one P b hb, neg_neg]
        change P.cupC _ b (CH.d F₂ m t) = _
        exact congrArg _ ht)

theorem cupMap_cls (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a : ℕ} (y : CH.Cn F₂ a)
    (hy : CH.d F₂ a y = 0) (hz : CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y) = 0) :
    cupMap P b hb a ((CH.cx F₂).cls y hy) = (CH.cx F₃).cls (P.cupC (Nat.add_comm 1 a) b y) hz := rfl

def castH (F : C ⥤ ModuleCat.{0} R) {W W' : ObjectProperty C} (h : W = W') (j : ℕ) : HU F W' j ≃ₗ[R] HU F W j := by
  subst h
  exact LinearEquiv.refl R _

end Map

section Sch
variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem append_cons {M : Type*} {a : ℕ} (t : M) (g : Fin a → M) :
    Fin.append ![t] g ∘ Fin.cast (Nat.add_comm 1 a).symm = (Fin.cons t g : Fin (a + 1) → M) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · have e : Fin.cast (Nat.add_comm 1 a).symm (0 : Fin (a + 1)) = Fin.castAdd a (0 : Fin 1) := Fin.ext (by simp)
    simp only [Function.comp, e, Fin.append_left, Fin.cons_zero]
    rfl
  · have e : Fin.cast (Nat.add_comm 1 a).symm k.succ = Fin.natAdd 1 k := Fin.ext (by simp [Nat.add_comm])
    simp only [Function.comp, e, Fin.append_right, Fin.cons_succ]

theorem form_cup' (hFC : FormCup) {a c : ℕ} (hc : 1 + a = c) (g₁ g₀ : Sec q V) (t : Sec q V) (g : Fin a → Sec q V)
    (x : CH.Cn ((inU q V).ι ⋙ G q 1) 1) (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hx : CH.d _ 1 x = 0) (hy : CH.d _ a y = 0)
    (h₁ : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls x hx)) (h₂ : IsForm q V g₀ g ((CH.cx _).cls y hy)) :
    ∃ hz, IsForm q V (a := c) (g₁ * g₀) (Fin.append ![t] g ∘ Fin.cast hc.symm)
      ((CH.cx ((inU q V).ι ⋙ G q c)).cls (cupU q (inU q V) hc hc x y) hz) := by
  subst hc
  exact hFC K Z q V 1 a g₁ g₀ ![t] g x y hx hy h₁ h₂

theorem cup_form (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V) (b : CH.Cn ((inU q V).ι ⋙ G q 1) 1)
    (hb : CH.d _ 1 b = 0) (hf : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls b hb))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = E₂ ω)
    (hz : CH.d ((inU q V).ι ⋙ G q (a + 1)) (a + 1) (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) = 0) :
    (CH.cx ((inU q V).ι ⋙ G q (a + 1))).cls (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) hz =
      E₃ (g₁ • w ω) := by
  let P := pairU (grOk (smFun Z q) (Nat.add_comm 1 a)).pair (inU q V)
  have key : (cupMap P b hb a).restrictScalars K ∘ₗ E₂ = E₃ ∘ₗ ((g₁ • w).restrictScalars K) := by
    refine lin_ext hFL _ _ fun g₀ v => ?_
    obtain ⟨⟨y', hy'⟩, hyy⟩ := Submodule.Quotient.mk_surjective _ (E₂ (form K g₀ v))
    have hy'' : CH.d _ a y' = 0 := hy'
    have hc' : (CH.cx _).cls y' hy'' = E₂ (form K g₀ v) := hyy
    have hI := h₂ g₀ v
    rw [← hc'] at hI
    obtain ⟨hz', hform⟩ := form_cup' hFC (Nat.add_comm 1 a) g₁ g₀ t v b y' hb hy'' hf hI
    rw [append_cons] at hform
    have hu := ((hFU K Z q V).2 (a + 1) (g₁ * g₀) (Fin.cons t v)).unique hform (h₃ _ _)
    change cupMap P b hb a (E₂ (form K g₀ v)) = E₃ (g₁ • w (form K g₀ v))
    rw [← hc', hw]
    refine (cupMap_cls P b hb y' hy'' hz').trans (hu.trans ?_)
    congr 1
    exact mul_smul _ _ _
  have := LinearMap.congr_fun key ω
  change cupMap P b hb a (E₂ ω) = E₃ (g₁ • w ω) at this
  rw [← hcls] at this
  exact (cupMap_cls P b hb y hy hz).symm.trans this

end Sch

end GlobalTheory.CompanionTheory.RelKill
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.slant_of_hodge_kuenneth : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | exact GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | (intros; apply GlobalTheory.CompanionTheory.KunGlue.slant_of_kun <;> assumption)
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isCompact_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n s d e
  have hle : PositivityTheory.LowerBoundConstant.Gx k e ≤ GlobalTheory.SplitWeil.KO k (Fin n) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right
  have hopen : IsOpen (PositivityTheory.LowerBoundConstant.Gx k e : Set (GL (Fin n) k)) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) (fun x hx => hle hx)

end GlobalTheory.CompanionTheory.MoyPrasad
end

section

namespace GlobalTheory.CompanionTheory.DepthZeroJac

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
open GlobalTheory.DepthZeroJac GlobalTheory.StepData GlobalTheory.IwahoriInj

theorem fixed_inj_smooth (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) :
    ∀ v ∈ fixed π (Gx k e),
      (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = 0 → v = 0 := by
  intro v hv h0
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  have h1 : v ∈ twKer π (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  exact claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v hv hM

end GlobalTheory.CompanionTheory.DepthZeroJac
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isOpen_Gx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) :
    IsOpen (Gx k e : Set (GL (Fin n) k)) := by
  unfold PositivityTheory.LowerBoundConstant.Gx
  exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne

end GlobalTheory.CompanionTheory.MoyPrasad
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GxSplit

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A K : Subgroup G}
    (hc : ∀ w ∈ A, ∀ g ∈ K, w * g * w⁻¹ ∈ K) {g : G} (hg : g ∈ K ⊔ A) :
    ∃ u ∈ A, ∃ h ∈ K, g = u * h := by
  let H : Subgroup G :=
    { carrier := {g | ∃ u ∈ A, ∃ h ∈ K, g = u * h}
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, h₁, hh₁, rfl⟩ ⟨u₂, hu₂, h₂, hh₂, rfl⟩
        refine ⟨u₁ * u₂, A.mul_mem hu₁ hu₂, (u₂⁻¹ * h₁ * u₂⁻¹⁻¹) * h₂,
          K.mul_mem (hc _ (A.inv_mem hu₂) _ hh₁) hh₂, ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨u, hu, h, hh, rfl⟩
        refine ⟨u⁻¹, A.inv_mem hu, u * h⁻¹ * u⁻¹, hc _ hu _ (K.inv_mem hh), ?_⟩
        group }
  have hle : K ⊔ A ≤ H := sup_le (fun h hh => ⟨1, A.one_mem, h, hh, by simp⟩)
    (fun u hu => ⟨u, hu, 1, K.one_mem, by simp⟩)
  exact hle hg

theorem gx_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  intro k _ _ _ _ n s d e g hg
  exact exists_mul_of_mem_sup
    (fun w hw h hh => GlobalTheory.DepthZeroJac.conj_mem_KOne (Subgroup.mem_inf.1 hw).2 hh) hg

end GlobalTheory.CompanionTheory.GxSplit

end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZJoint

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem isOpen_dom (n : ℕ) : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) :=
  isOpen_univ.prod (isOpen_GLs n)

def Pres (Φ : (Mat n → V) → (Mat n → V)) : Prop :=
  ∀ U : ℝ → Mat n → V, ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    ContDiffOn ℝ ∞ (Function.uncurry fun t => Φ (U t)) (Set.univ ×ˢ GLs n)

theorem rd_eq_fderiv (U : ℝ → Mat n → V)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) {t : ℝ} {g : Mat n}
    (hg : g ∈ GLs n) (X : Mat n) :
    Rd X (U t) g = fderiv ℝ (Function.uncurry U) (t, g) ((0 : ℝ), g * X) := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, g) :=
    (hU.contDiffAt ((isOpen_dom n).mem_nhds ⟨Set.mem_univ _, hg⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun x : Mat n => (t, x)) (ContinuousLinearMap.inr ℝ ℝ (Mat n)) g :=
    hasFDerivAt_prodMk_right t g
  have h2 : HasFDerivAt (U t)
      ((fderiv ℝ (Function.uncurry U) (t, g)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) g :=
    HasFDerivAt.comp g (f := fun x : Mat n => (t, x)) (g := Function.uncurry U) hd.hasFDerivAt hi
  simp [Rd, h2.fderiv]

theorem pres_Rd (X : Mat n) : Pres (V := V) (Rd X) := by
  intro U hU
  have h1 := hU.fderiv_of_isOpen (m := ∞) (isOpen_dom n) (by simp)
  let L : Mat n →ₗ[ℝ] Mat n := LinearMap.mulRight ℝ X
  have hL : ContDiff ℝ ∞ (fun x : Mat n => x * X) := (L.toContinuousLinearMap).contDiff
  have hl : ContDiff ℝ ∞ (fun p : ℝ × Mat n => ((0 : ℝ), p.2 * X)) :=
    contDiff_const.prodMk (hL.comp contDiff_snd)
  refine (h1.clm_apply hl.contDiffOn).congr ?_
  rintro ⟨t, g⟩ ⟨-, hg⟩
  exact rd_eq_fderiv U hU hg X

theorem Pres.add {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ f + Ψ f) :=
  fun U hU => (h U hU).add (k U hU)

theorem Pres.smul {Φ : (Mat n → V) → (Mat n → V)} (c : ℂ) (h : Pres Φ) :
    Pres (fun f => c • Φ f) :=
  fun U hU => (h U hU).const_smul c

theorem Pres.comp {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Pres Φ) (k : Pres Ψ) :
    Pres (fun f => Φ (Ψ f)) :=
  fun U hU => h (fun t => Ψ (U t)) (k U hU)

theorem pres_sum {ι : Type} (s : Finset ι) (Φ : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Pres (Φ i)) : Pres (fun f => ∑ i ∈ s, Φ i f) := by
  intro U hU
  have e : (Function.uncurry fun t => ∑ i ∈ s, Φ i (U t)) =
      fun p => ∑ i ∈ s, (Function.uncurry fun t => Φ i (U t)) p := by
    funext p
    simp [Function.uncurry, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun i _ => h i U hU

theorem pres_Eu (s : Bool) (a b : Fin n) : Pres (V := V) (Eu s a b) :=
  Pres.smul (1 / 2 : ℂ) ((pres_Rd _).add (Pres.smul _ (pres_Rd _)))

theorem pres_Epow (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Pres (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b U hU
    by_cases hab : a = b
    · simpa [Epow, hab] using hU
    · have e : (Function.uncurry fun t => Epow (V := V) s 0 a b (U t)) = fun _ => 0 := by
        funext p
        simp [Epow, hab, Function.uncurry]
      rw [e]
      exact contDiffOn_const
  | succ m ih =>
    intro a b
    exact pres_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      fun c => (pres_Eu s a c).comp (ih c b)

theorem pres_gel (s : Bool) (m : ℕ) : Pres (V := V) (gel (n := n) s m) :=
  pres_sum Finset.univ (fun a f => Epow s m a a f) fun a => pres_Epow s m a a

theorem pres_zOp (w : List (Bool × ℕ)) : Pres (V := V) (zOp (n := n) w) := by
  induction w with
  | nil => exact fun U hU => hU
  | cons p w ih => exact (pres_gel p.1 p.2).comp ih

theorem zOp_joint (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (U : ℝ → Mat n → V)
    (w : List (Bool × ℕ)) (h : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t => zOp w (U t)) (Set.univ ×ˢ GLs n) :=
  pres_zOp w U h

end GlobalTheory.CompanionTheory.WaveMult.ZJoint
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem isWave_time_refl : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  intro n E u hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, fun t => h2 (-t), ?_, ?_⟩
  · have hm : Set.MapsTo (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) (Set.univ ×ˢ GLs n) :=
      fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) :=
      (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
    exact h1.comp hc hm
  · intro t g hg
    have := iteratedDeriv_comp_neg (𝕜 := ℝ) 2 (fun s => u s g) t
    rw [this, h3 (-t) g hg]
    simp
  · intro g hg
    have := deriv_comp_neg (𝕜 := ℝ) (fun s => u s g) 0
    rw [this]
    simpa using h4 g hg

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eventuallyEq_of_agree_GLs {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) {x : Mat n}
    (hx : x ∈ GLs n) : F =ᶠ[nhds x] F' := by
  have ho : IsOpen (GLs n) := by
    have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne.preimage this
  exact Filter.eventuallyEq_of_mem (ho.mem_nhds hx) h

theorem Rd_agree_GLs (X : Mat n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Rd X F x = Rd X F' x := by
  intro x hx
  simp only [Rd, (eventuallyEq_of_agree_GLs h hx).fderiv_eq]

theorem Eu_agree_GLs (s : Bool) (a b : Fin n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Eu s a b F x = Eu s a b F' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_agree_GLs _ h x hx]

theorem Epow_agree_GLs (s : Bool) (m : ℕ) (a b : Fin n) {F F' : Mat n → V}
    (h : ∀ g ∈ GLs n, F g = F' g) : ∀ x ∈ GLs n, Epow s m a b F x = Epow s m a b F' x := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    by_cases hab : a = b
    · simpa [Epow, hab] using h x hx
    · simp [Epow, hab]
  | succ m ih =>
    intro x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_agree_GLs s a c (ih c b) x hx

theorem gel_agree_GLs (s : Bool) (m : ℕ) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, gel s m F x = gel s m F' x := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => Epow_agree_GLs s m a a h x hx

end Local

theorem zOp_agree_GLs : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) (F F' : Mat n → V), (∀ g ∈ GLs n, F g = F' g) →
    ∀ x ∈ GLs n, zOp w F x = zOp w F' x := by
  intro n V _ _ w
  induction w with
  | nil => exact fun F F' h x hx => h x hx
  | cons p w ih => exact fun F F' h => gel_agree_GLs p.1 p.2 (ih F F' h)

end GlobalTheory.CompanionTheory.WaveMult
end
end
