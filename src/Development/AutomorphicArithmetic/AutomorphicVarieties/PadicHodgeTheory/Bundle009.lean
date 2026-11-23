module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle357
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle040
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.z1fCoef :
    ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l) {A A' V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A'] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A H V) (ρ' : Representation A' H V') (f : V →ₗ[ℚ_[l]] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ finiteCocycles φ ρ, (fun g => f (c g)) ∈ finiteCocycles φ ρ' := by
  intro l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · simp only [hcc g h, map_add (f := _), hf]
  · have key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
        actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.memIK :
    ∀ {v : ℕ} [Fact v.Prime] (K : FinExt v) (g : ↥(GK K)), g ∈ IK K ↔ (g : GQ v) ∈ Iq v := by
  intro l _ K g
  refine ⟨fun hg => (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK K).subtype)).2 (fun σ hσ => ?_) hg,
    fun hg => Subgroup.subset_closure (GlobalTheory.FrobGen.norm_sub_lt hg)⟩
  change (σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
  rintro x ⟨n, hn, hln, hx⟩
  have key : (σ : GQ l) x = x := GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hln (by rw [← map_pow, hx, map_one]) hx
    (hσ x (GlobalTheory.Pst.norm_eq_one_of_pow_eq_one hn hx).le)
  rintro ⟨_, n, rfl⟩
  exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy _ (σ : GQ l) from key) n
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

variable {l : ℕ} [Fact l.Prime]

private theorem iqb_unit (x : integralClosure ℤ_[l] (PadicAlgCl l)) (h : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : (x : PadicAlgCl l) ≠ 0 := by
    intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  refine IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩
    (Subtype.ext (mul_inv_cancel₀ h0))
  rw [norm_inv, h, inv_one]

private theorem iqb_local : IsLocalRing (integralClosure ℤ_[l] (PadicAlgCl l)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hx : ‖(x : PadicAlgCl l)‖ ≤ 1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2
  rcases hx.eq_or_lt with h | h
  · exact Or.inl (iqb_unit x h)
  · refine Or.inr (iqb_unit _ ?_)
    have : ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖ := by rw [norm_one, norm_neg]; exact h.ne'
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this
    rw [norm_one, norm_neg, max_eq_left hx] at h2
    simpa [sub_eq_add_neg] using h2

private theorem iqb_frob : ∃ g : GQ l, IsFrob g := by
  haveI := iqb_local (l := l)
  have e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l := PadicInt.residueField
  obtain ⟨g, hg⟩ := GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hm⟩ := hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hm
  have hle := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
    (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2
  have hne := mt (iqb_unit _) hm
  have := lt_of_le_of_ne hle hne
  simpa [hy] using this

private theorem iqb_norm (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := KStar.IdealValuations.norm_aut_and_roots.1 g x

private theorem iqb_sub {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

private theorem iqb_mem (g : GQ l) : g ∈ Iq l ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact iqb_sub (by rwa [iqb_norm]) hlt
    · obtain ⟨m, ζ, hm, hζ, hxζ⟩ := KStar.IdealValuations.exists_root_congr heq
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
      have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
      have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact iqb_sub (by rwa [iqb_norm]) hxζ
  · intro hg x hx
    have hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
      rintro ζ ⟨m, hm0, hm, hζ⟩
      have hn : ‖ζ‖ = 1 := by
        have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1
      have h1 : g ζ = ζ := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ
        (hg ζ hn.le)
      have h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ :=
        (Subgroup.zpowers_le (G := GQ l)).2 h1
      exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.iqBasic :
    ∀ (v : ℕ) [Fact v.Prime], (Iq v).Normal ∧ IsClosed (Iq v : Set (GQ v)) ∧ (∀ g : GQ v, g ∈ Iq v ↔ ∀ x : Om v, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) ∧ (∃ σ : GQ v, IsFrob σ) ∧ ∀ σ σ' : GQ v, IsFrob σ → (IsFrob σ' ↔ σ⁻¹ * σ' ∈ Iq v) := by
  intro v _
  refine ⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩
  · rw [iqb_mem] at hn ⊢
    intro x hx
    have h := hn (g⁻¹ x) (by rwa [iqb_norm])
    have e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel,
        AlgEquiv.one_apply]
    rwa [e, iqb_norm]
  · have : IsGalois ℚ_[v] (Om v) := {}
    exact InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)
  · have e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖ := fun x => by
      rw [← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
    rw [iqb_mem]
    simp only [e]
    constructor
    · intro h x hx
      have h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (hσ x hx)
    · intro h x hx
      have h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → BdR) (i : Fin d) :
    (TensorProduct.lid Qp BdR) (LinearMap.rTensor BdR (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by

  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem sum_mem_fil_iff (a : ℤ) (c : Fin d → BdR) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ FilV PD (LL := Qp) (V := V) a ↔ ∀ i, c i ∈ PD.Fil a := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [← coord_sum e c i, ← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v x =>
      have := ((PD.Fil a).restrictScalars Qp).smul_mem (e.coord i v) x.2
      simpa using this
    | add x y hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro h
    exact Submodule.sum_mem _ fun j _ => ⟨e j ⊗ₜ ⟨c j, h j⟩, rfl⟩

private theorem sum_mem_DdR (c : Fin d → BdR)
    (h : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)).mulVec (fun j => PD.actdR g (c j)) = c) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro g
  conv_rhs => rw [← h g]

  simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actdR g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core
    (hinv : ∀ a b, b ∈ PD.Fil a → b ∉ PD.Fil (a + 1) → ∃ β ∈ PD.Fil (-a), β * b - 1 ∈ PD.Fil 1)
    (hT : ∀ n x, x ∈ PD.Fil n → (∀ g, PD.actdR g x - x ∈ PD.Fil (n + 1)) →
      ∃ κ ∈ PD.Fil 0, (∀ g, PD.actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ x - κ ∈ PD.Fil (n + 1))
    (h0 : DdR PD ρ ≤ FilV PD (LL := Qp) (V := V) 0) (h1 : DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 = ⊥)
    (N N' : Matrix (Fin d) (Fin d) BdR) (hN : N * N' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N) :
    (∀ i j, N i j ∈ PD.Fil 0) ∧ ∀ i j, N' i j ∈ PD.Fil 0 := by
  let A : G → Matrix (Fin d) (Fin d) BdR := fun g => (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)
  have hA : ∀ g i j, A g i j ∈ PD.Fil 0 := fun g i j => by
    change algebraMap Qp BdR _ ∈ _
    rw [IsScalarTower.algebraMap_apply Qp K BdR, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ PD.one_mem
  have hcol : ∀ j g, (A g).mulVec (fun i => PD.actdR g (N i j)) = fun i => N i j := fun j g => by
    funext i
    exact congrFun (congrFun (hg g) i) j
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hA' : ∀ g, N' * A g = N'.map (PD.actdR g) := fun g => by
    have h2 : N.map (PD.actdR g) * N'.map (PD.actdR g) = 1 := by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) BdR => X.map (PD.actdR g : BdR →+* BdR)) hN
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc N' * A g = N' * A g * (N.map (PD.actdR g) * N'.map (PD.actdR g)) := by rw [h2, mul_one]
      _ = N' * (A g * N.map (PD.actdR g)) * N'.map (PD.actdR g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg g, hN', one_mul]
  refine ⟨fun i j => (sum_mem_fil_iff PD e 0 (fun i => N i j)).1 (h0 (sum_mem_DdR PD ρ e _ (hcol j))) i,
    fun i j => ?_⟩
  have hFa : Antitone fun a => (PD.Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => PD.Fil_anti a
  let R : G → (Fin d → BdR) →+ (Fin d → BdR) := fun g =>
    { toFun := fun c => (A g).mulVec (fun j => PD.actdR g (c j))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext j
        simp }
  let FM : ℤ → AddSubgroup (Fin d → BdR) := fun a => AddSubgroup.pi Set.univ fun _ => (PD.Fil a).toAddSubgroup
  have hFM : ∀ a c, c ∈ FM a ↔ ∀ i, c i ∈ PD.Fil a := fun a c => by
    simp [FM, AddSubgroup.mem_pi]
  obtain ⟨m, k, b, c, h, hs⟩ := GlobalTheory.DRFil.filtered (G := G) (fun g => (PD.actdR g : BdR →+* BdR)) R
    (fun a => (PD.Fil a).toAddSubgroup) FM
    (fun g b x => by
      change (A g).mulVec _ = _ • (A g).mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      simp)
    PD.Fil_mul
    (fun a c x z hx hz => (hFM _ _).2 fun i => PD.Fil_mul _ _ _ _ hx ((hFM _ _).1 hz i))
    PD.Fil_G
    (fun g a z hz => (hFM _ _).2 fun i => by
      change ∑ j, A g i j * PD.actdR g (z j) ∈ _
      refine Submodule.sum_mem _ fun j _ => ?_
      have := PD.Fil_mul _ _ _ _ (hA g i j) (PD.Fil_G g _ _ ((hFM _ _).1 hz j))
      rwa [zero_add] at this)
    hinv hT hFa (fun a a' h z hz => (hFM _ _).2 fun i => hFa h ((hFM _ _).1 hz i)) PD.Fil_exh
    (fun x => by
      choose r hr using fun i => PD.Fil_exh (x i)
      obtain ⟨a, ha⟩ := (Set.finite_range r).bddBelow
      exact ⟨a, (hFM _ _).2 fun i => hFa (ha ⟨i, rfl⟩) (hr i)⟩)
    0 (fun i => (1 : Matrix (Fin d) (Fin d) BdR) i j)
    ((hFM _ _).2 fun i => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [PD.one_mem, Submodule.zero_mem _])
    d (fun i => N' i j) (fun j i => N i j) (fun j g => hcol j g)
    (by
      funext i
      rw [← hN, Matrix.mul_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
  have h3 : N' i j = ∑ n, b n * N'.mulVec (c n) i := by
    have h4 := congrFun (congrArg N'.mulVec hs) i
    rw [Matrix.mulVec_sum, Finset.sum_apply] at h4
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h4
    rw [← h4]
    exact (congrFun (congrFun (mul_one N') i) j).symm
  rw [h3]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨hc, hk, hb⟩ := h n
  by_cases hk1 : 1 ≤ k n
  · have h5 : ∑ j, e j ⊗ₜ[Qp] c n j ∈ DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 :=
      ⟨sum_mem_DdR PD ρ e _ hc, (sum_mem_fil_iff PD e 1 _).2 fun i => hFa hk1 ((hFM _ _).1 hk i)⟩
    rw [h1, Submodule.mem_bot] at h5
    have h6 : c n = 0 := funext fun i => by
      rw [← coord_sum e (c n) i, h5]
      simp
    rw [h6]
    simp
  · have h5 : b n ∈ PD.Fil 0 := hFa (show (0 : ℤ) ≤ 0 - k n by omega) hb
    obtain ⟨κ, hκ⟩ := PD.invdR (N'.mulVec (c n) i) fun g => by
      have h6 : (A g).mulVec (fun j => PD.actdR g (c n j)) = c n := hc g
      conv_rhs => rw [← h6, Matrix.mulVec_mulVec, hA' g]
      simp [Matrix.mulVec, dotProduct]
    have h6 : N'.mulVec (c n) i ∈ PD.Fil 0 := by
      rw [← hκ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ PD.one_mem
    simpa using PD.Fil_mul _ _ _ _ h5 h6

end Coord

theorem UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → DdR ((PP l).PD K) ρ ≤ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0 → DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 1 = ⊥ → ∀ (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ ∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil 0 := by
  intro l _ K V _ _ _ ρ d e _ h0 h1 M M' hM hg
  obtain ⟨T⟩ := tiedP l
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
  have key := core ((PP l).PD K) ρ e (GlobalTheory.DRFil.graded_inv Θ K) (GlobalTheory.DRFil.graded_invariants T Θ K) h0 h1
    (M.map (PP l).ιB) (M'.map (PP l).ιB)
    (by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) (Bcr l) => X.map ((PP l).ιB : Bcr l →+* Bdr l)) hM
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this)
    (fun g => by
      ext i j
      have := congrArg (PP l).ιB (congrFun (congrFun (hg g) i) j)

      rw [Matrix.map_apply, ← this, Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.map_apply, map_mul, AlgHom.commutes]
      rw [← (PP l).PD_actB K g, ← (PP l).PD_ι K, ← (PP l).PD_ι K, ((PP l).PD K).ι_comm])
  exact ⟨fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.1 i j), fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.2 i j)⟩
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem open_fix {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    (IntermediateField.fixedField H).fixingSubgroup = H :=
  _root_.UpperTheory.Reformulated.B.Qi42.open_fix H hH

private theorem open_index {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    H.index = finrank ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, open_fix H hH]

private theorem open_fin {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    FiniteDimensional ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [← InfiniteGalois.isOpen_iff_finite, open_fix H hH]
  exact hH

private theorem fixed_sup {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) :
    IntermediateField.fixedField (H ⊔ Iq v) = IntermediateField.fixedField H ⊓ MaximalUnramifiedExtension v := by
  have h1 : IntermediateField.fixedField (Iq v) = MaximalUnramifiedExtension v := InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v)
  rw [← h1]
  apply le_antisymm
  · exact le_inf (IntermediateField.fixedField_le le_sup_left) (IntermediateField.fixedField_le le_sup_right)
  · rw [IntermediateField.le_iff_le]
    refine sup_le ?_ ?_
    · rw [← IntermediateField.le_iff_le]; exact inf_le_left
    · rw [← IntermediateField.le_iff_le]; exact inf_le_right

theorem UpperTheory.V.Loc.openField :
    ∀ {v : ℕ} [Fact v.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ), ∃ (K : FinExt v) (e : G ≃* ↥(GK K)), Continuous e ∧ Continuous e.symm ∧ (GK K).subtype.comp e.toMonoidHom = φ ∧ φ.range = GK K ∧ φ.range.index = finrank ℚ_[v] ↥K.1 ∧ (φ.range ⊔ Iq v).index = finrank ℚ_[v] ↥(K0 K) := by
  intro v _ G _ _ _ φ hφ
  have hH : IsOpen (φ.range : Set (GQ v)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  let K : FinExt v := ⟨IntermediateField.fixedField φ.range, open_fin _ hH⟩
  have hK : φ.range = GK K := (open_fix _ hH).symm
  let e : G ≃* ↥(GK K) := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hK)
  have he : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => rfl
  refine ⟨K, e, ?_, ?_, ?_, hK, open_index _ hH, ?_⟩
  · exact continuous_induced_rng.2 hφ.continuous
  · rw [hφ.isInducing.continuous_iff]
    have : φ ∘ e.symm = Subtype.val := by
      funext x
      rw [Function.comp_apply, ← he, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val
  · ext1 g
    exact he g
  · rw [open_index _ (Subgroup.isOpen_mono le_sup_left hH), fixed_sup]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

def UpperTheory.V.Loc.HasLT {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ)
    (wt : Emb l w → ℤ) (a : Weil h →* (w.adicCompletion F)ˣ) : Prop :=
  ∃ (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* ℂˣ), Continuous μ ∧ IsSmooth ξ ∧
    GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 μ) ∧
    (∀ σ, (ξ σ : ℂ) = ι ((μ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) *
      ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ)) ∧
    ∀ σ, (ξ σ : ℂ) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 μ)).eig σ
end
