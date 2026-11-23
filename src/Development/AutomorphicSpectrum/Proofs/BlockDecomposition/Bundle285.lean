module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle218
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle277
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem exists_inv_fil (a : ℤ) (x : Formalism.Per6.BdR l) (h1 : x ∈ Formalism.Per6.FilD l a) (h2 : x ∉ Formalism.Per6.FilD l (a + 1)) :
    ∃ y ∈ Formalism.Per6.FilD l (-a), x * y = 1 := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l
  have hne := IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 h1
  have hb : IsUnit b := by
    by_contra hb
    have hm : b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hb
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    refine h2 ((IsPerfectoidField.mem_fil_iff hϖ).2 ⟨c, ?_⟩)
    rw [map_mul, zpow_add₀ hne, zpow_one, mul_assoc]
  obtain ⟨u, rfl⟩ := hb
  refine ⟨_, (IsPerfectoidField.mem_fil_iff hϖ).2 ⟨((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l), rfl⟩, ?_⟩
  have h3 : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) *
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_inv_cancel₀ (zpow_ne_zero a hne)
  rw [zpow_neg]
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) = A at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = A' at *
  generalize (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a)⁻¹ = C at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a = D at *
  linear_combination (A * A') * h4 + h3

theorem exists_gal (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL)
    (σ σ' : LL →ₐ[ℚ_[l]] Om l) (h : σ.comp τ = K.1.val) (h' : σ'.comp τ = K.1.val) :
    ∃ g : ↥(GK K), ∀ x, (g : GQ l) (σ x) = σ' x := by
  letI : Algebra LL (Om l) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL (Om l) := .of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Normal ℚ_[l] (Om l) := IsAlgClosure.normal ℚ_[l] (Om l)
  let g₀ : Om l →ₐ[ℚ_[l]] Om l := σ'.liftNormal (Om l)
  have hg₀ : ∀ x, g₀ (σ x) = σ' x := fun x => AlgHom.liftNormal_commutes σ' (Om l) x
  let g : GQ l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  refine ⟨⟨g, ?_⟩, hg₀⟩
  rw [GK, IntermediateField.mem_fixingSubgroup_iff]
  intro c hc
  have h1 : σ (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h ⟨c, hc⟩
  have h2 : σ' (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h' ⟨c, hc⟩
  change g₀ c = c
  rw [← h1, hg₀, h1, h2]

section

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem repE_toGL1 (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw)) (v : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g v = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • v := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem card_emb_le (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1) [Fintype (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)] :
    Fintype.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥Bw.Kw.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Om l)]
  exact Fintype.card_congr
    { toFun := fun τ => LL'.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split τ x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

end GlobalTheory.CompanionTheory.DeRhamChar

open GlobalTheory.CompanionTheory.DeRhamChar Module GlobalTheory.Cmp.JumpDict GroundTheory.PAdicHodge in
theorem GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A _ O _ _ _ Bw _ LL' hLL ψ J hJ
  obtain ⟨T⟩ := hT
  haveI : IsDomain P.R.BdR := T.eD.toMulEquiv.isDomain (Formalism.Per6.BdR l)
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hOm : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD Bw.Kw).Fil 0 := fun x => by
    obtain ⟨y, hy, -⟩ := T.om x
    rw [T.fil, hy]
    exact (IsPerfectoidField.mem_fil_iff (IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l)).2
      ⟨y, by simp⟩
  have hval : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD Bw.Kw).Fil a → x ∉ (P.PD Bw.Kw).Fil (a + 1) →
      ∃ y ∈ (P.PD Bw.Kw).Fil (-a), x * y = 1 := fun a x h1 h2 => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_fil a (T.eD x) ((T.fil _ _ _).1 h1) (fun h => h2 ((T.fil _ _ _).2 h))
    refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by simpa using hy), T.eD.injective ?_⟩
    simpa using hxy
  have hmult : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) a,
      multV (P.PD Bw.Kw) (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) τ a = if a = -J τ then 1 else 0 :=
    fun τ a => multV_inv (P.PD Bw.Kw) (GK Bw.Kw).subtype Bw.Kw.1.val (fun _ => rfl)
      (fun g x => by rw [P.PD_actdR]; exact P.actQdR_Om _ x)
      (fun g c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 c c.2) hOm hval
      (χ := ψ.comp Bw.e.symm.toMonoidHom) (χ' := ψ⁻¹.comp Bw.e.symm.toMonoidHom)
      (fun g v => repE_toGL1 Bw LL' ψ g v) (fun g v => repE_toGL1 Bw LL' ψ⁻¹ g v)
      (fun g => by simp) τ
      (fun σ σ' h h' => exists_gal Bw.Kw τ σ σ' h h') (J τ) (fun a => hJ.2 τ a) a
  refine ⟨?_, fun τ a => hmult τ a⟩
  have := finrank_ddR_of_one_jump (P.PD Bw.Kw) (card_emb_le Bw LL' hLL)
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) (fun τ => ⟨-J τ, hmult τ⟩)
  simpa [LocBridge.IsdRE] using this
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem contDiffOn_of_right_family : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  intro n V P _ _ o d hdiff hR v
  obtain ⟨A, hA, hfr⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  let e := Fintype.equivFin (Bool × Fin n × Fin n)
  refine GlobalTheory.CompanionTheory.SmoothVectors.contDiffOn_of_fderiv_family isOpen_GLs o Set.univ
    (fun i => A (e.symm i)) (fun i => hA _) ?_ v (Set.mem_univ v)
  intro u _
  refine ⟨fun i => d (e.symm i) u, fun i => Set.mem_univ _, fun z hz => ?_⟩
  have hD := hfr V (fderiv ℝ (o u) z) z hz
  have hsum : (∑ i, (A (e.symm i) z).smulRight (o (d (e.symm i) u) z))
      = ∑ p, (A p z).smulRight (o (d p u) z) :=
    e.symm.sum_comp (fun p => (A p z).smulRight (o (d p u) z))
  have hval : ∀ p, fderiv ℝ (o u) z (z * bs p) = o (d p u) z := fun p => hR u p z hz
  have h2 : fderiv ℝ (o u) z = ∑ p, (A p z).smulRight (o (d p u) z) :=
    hD.trans (Finset.sum_congr rfl fun p _ => congrArg (fun y : V => (A p z).smulRight y) (hval p))
  exact (hdiff u z hz).hasFDerivAt.congr_fderiv (h2.trans hsum.symm)

end GlobalTheory.CompanionTheory.PresSobA
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

theorem isOpen_GLs_kerconv (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_unitary_mem_GLs_kerconv {n : ℕ} {y : Mat n} (hy : y ∈ GLs n)
    (k₂ : Matrix.unitaryGroup (Fin n) ℂ) : y * k₂.1 ∈ GLs n := by
  have h1 : y.det ≠ 0 := hy
  have h2 : (k₂.1 : Mat n).det ≠ 0 := by
    have h3 : (star k₂.1 * k₂.1 : Mat n) = 1 := Unitary.star_mul_self_of_mem k₂.2
    intro h0
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h4
    exact zero_ne_one h4
  change (y * k₂.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1 h2

theorem act_congr_kerconv {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) {f f' : Mat n → E.V} (h : ∀ x ∈ GLs n, f x = f' x)
    {x : Mat n} (hx : x ∈ GLs n) : act μ E k f x = act μ E k f' x := by
  unfold act
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hy : (y.val).det ≠ 0 := by
    have := y.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hxy : x * y.val ∈ GLs n := by
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  simp only [h _ hxy]

theorem one_mem_GLs_kerconv (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  change (1 : Mat n).det ≠ 0
  simp

theorem conv_eq_of_isKer : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  intro hLg _ hRC hWS hWE hKU n _ _ μ _ E w w' g g' T T' k k' K hg hg' hk hk' hK y hy
  have rk : KReg k := ⟨hk.1.continuousOn, hk.2.1⟩
  have rk' : KReg k' := ⟨hk'.1.continuousOn, hk'.2.1⟩
  have rK : KReg K := ⟨hK.1.continuousOn, hK.2.1⟩
  have rc : KReg (conv μ E k k') := kReg_conv hLg n μ E k k' rk rk'
  have hk'eq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂ := by
    intro y hy k₂
    have := hk'.2.2.1 y hy 1 k₂
    simpa using this
  have hKeq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K (y * k₂.1) = K y * E.ρ k₂ := by
    intro y hy k₂
    have := hK.2.2.1 y hy 1 k₂
    simpa using this
  have hceq := conv_right_equivariant hLg n μ E k k' rk rk' hk'eq
  have key := hKU n μ E (fun y => conv μ E k k' y - K y) (GLs n) (isOpen_GLs_kerconv n) subset_rfl
    (fun y hy k₂ => mul_unitary_mem_GLs_kerconv hy k₂) (rc.1.sub rK.1)
    (fun y hy k₂ => by
      simp only [hceq y hy k₂, hKeq y hy k₂]
      exact (sub_mul _ _ _).symm)
    (fun f hf hc _ => by
      obtain ⟨u, hu, hu0⟩ := hWE n E f hf
      obtain ⟨v, hv, hv0, hvc⟩ := GlobalTheory.T.wave_kernel_composition hRC hWS n E u w w' g g' T T' hu hg hg'
      have h1 := one_mem_GLs_kerconv n
      have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
      have hlin := act_eq_sum_of_kernel hLg n μ E (ι := Bool) (fun b => if b then 1 else -1)
        (fun b => if b then conv μ E k k' else K) (fun y => conv μ E k k' y - K y) f
        (fun b => by cases b <;> simp [rc, rK])
        (fun y _ => by simp [Fintype.sum_bool, sub_eq_add_neg]) hfc 1 h1
      have hc1 : act μ E (conv μ E k k') f 1 = act μ E k (act μ E k' f) 1 :=
        act_conv hLg n μ E k k' f rk rk' hfc 1 h1
      have hact' : ∀ x ∈ GLs n, act μ E k' f x = v 0 x := by
        intro x hx
        rw [act_congr_kerconv μ E k' (fun z hz => (hu0 z hz).symm) hx, hk'.2.2.2 u hu x hx, hv0 x hx]
      have hc2 : act μ E k (act μ E k' f) 1 = act μ E K f 1 := by
        rw [act_congr_kerconv μ E k hact' h1, hk.2.2.2 v hv 1 h1, hvc 1 h1,
          ← hK.2.2.2 u hu 1 h1]
        exact act_congr_kerconv μ E K hu0 h1
      rw [hlin]
      simp [Fintype.sum_bool, hc1, hc2]) y hy
  exact sub_eq_zero.1 key

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_operator_center_expansion : ∀ (n m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ), (∀ cc : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = ∑ i, c i * ((w i).map (GlobalTheory.Dec.gelfVal cc)).prod) ∧ (RCalc → ∀ (s : Bool) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, gelT s m f x = ∑ i, c i • zOp ((w i).map (fun j => (s, j))) f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | exact GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | (intros; apply GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants <;> assumption)
end

section

open Polynomial

namespace GlobalTheory.CompanionTheory.LinRec

noncomputable def shift : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun u := fun i => u (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shift_apply (u : ℕ → ℂ) (i : ℕ) : shift u i = u (i + 1) := rfl

lemma shift_pow (j : ℕ) (u : ℕ → ℂ) (i : ℕ) : (shift ^ j) u i = u (i + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    rfl

lemma aeval_shift (p : ℂ[X]) (u : ℕ → ℂ) (i : ℕ) :
    aeval shift p u i = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]

lemma aeval_diff (q : ℂ[X]) (z : ℂ) (u : ℕ → ℂ) (hu : aeval shift ((X - C z) * q) u = 0) :
    aeval shift q (fun i => u (i + 1) - z * u i) = 0 := by
  have h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i := by
    funext i
    simp [aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]
  rw [← h, ← Module.End.mul_apply, ← map_mul, mul_comm]
  exact hu

lemma geom_step (z : ℂ) (κ c M : ℝ) (hz : ‖z‖ < Real.exp κ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (u : ℕ → ℂ) (h0 : ‖u 0‖ ≤ M)
    (hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤ c * Real.exp (κ * i) * M) (i : ℕ) :
    ‖u i‖ ≤ (1 + c / (Real.exp κ - ‖z‖)) * Real.exp (κ * i) * M := by
  have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hz
  set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ c / (Real.exp κ - ‖z‖) := div_nonneg hc hpos.le
    linarith
  have hD : ‖z‖ * D + c ≤ D * Real.exp κ := by
    have : D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c := by
      rw [hDdef]; field_simp
    nlinarith
  induction i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  | succ i ih =>
    have hE : 0 < Real.exp (κ * i) := Real.exp_pos _
    have h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖ := by
      have : u (i + 1) = z * u i + (u (i + 1) - z * u i) := by ring
      calc ‖u (i + 1)‖ = ‖z * u i + (u (i + 1) - z * u i)‖ := by rw [← this]
        _ ≤ ‖z * u i‖ + ‖u (i + 1) - z * u i‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc ‖u (i + 1)‖ ≤ ‖z‖ * (D * Real.exp (κ * i) * M) + c * Real.exp (κ * i) * M :=
          h1.trans (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) (hv i))
      _ = (‖z‖ * D + c) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (D * Real.exp κ) * (Real.exp (κ * i) * M) := mul_le_mul_of_nonneg_right hD hEM
      _ = _ := by ring

theorem bound_of_natDegree (n : ℕ) : ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → p.natDegree = n →
    (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < n, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  induction n with
  | zero =>
    intro p κ hp hd _
    refine ⟨0, le_rfl, fun u M hu _ _ i => ?_⟩
    have hp1 : p = 1 := by
      have h1 : p.coeff 0 = 1 := by
        have h2 := hp.coeff_natDegree
        rwa [hd] at h2
      rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
    subst hp1
    have hu0 : u = 0 := by simpa using hu
    simp [hu0]
  | succ n ih =>
    intro p κ hp hd hr
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      have : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      omega)
    have hzlt := hr z hz
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : q.natDegree = n := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C] at hd
      omega
    obtain ⟨C', hC', hB⟩ := ih q κ hq hqd fun w hw => hr w (by
      have hw' : eval w q = 0 := hw
      simp [IsRoot, hw'])
    have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hzlt
    have hc : 0 ≤ C' * (1 + ‖z‖) := by positivity
    refine ⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩
    refine geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i
    have hb := hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu)
      (fun j hj => ?_) (by positivity) i
    · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + ‖z‖) * M) := hb
        _ = _ := by ring
    · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
        _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
        _ ≤ M + ‖z‖ * M := add_le_add (hM _ (by omega))
            (mul_le_mul_of_nonneg_left (hM _ (by omega)) (norm_nonneg _))
        _ = _ := by ring

theorem recBound : PositivityTheory.Rg.Rs.An.RecBound := by
  intro p κ hp hr
  obtain ⟨C, hC, h⟩ := bound_of_natDegree _ p κ hp rfl hr
  refine ⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.exists_galois_extension_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding <;> assumption)
end
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing


theorem _root_.GlobalTheory.T.laplacian_monic_annihilator_measure : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | exact GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | (intros; apply GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian <;> assumption)
end
