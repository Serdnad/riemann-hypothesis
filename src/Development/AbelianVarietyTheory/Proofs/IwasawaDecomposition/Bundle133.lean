module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix

namespace GlobalTheory.CuspRep.ContAut

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (pFin E) : GA E a → GL (Fin a) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pFin E))

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf E))

theorem continuous_of_isOpen_stab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsOpen {k | finRep E a k φ = φ} → Continuous φ.1 := by
  intro E _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA E a => g⁻¹ * x := continuous_const.mul continuous_id
  have h1 : Continuous fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((continuous_map_pInf E a).comp hm)
  have h2 : ContinuousAt (fun x : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
      (contDiffAt_chart φ.2 g (val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA E a | finRep E a (GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage ((continuous_map_pFin E a).comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * infGL E a _ * finGL E a _) = _
  rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]

end GlobalTheory.CuspRep.ContAut
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.CuspRep.LocUniq

theorem equiv_of_iSup_range {R M S S' : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] [IsSimpleModule R S] [IsSimpleModule R S']
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (g : S' →ₗ[R] M) (hg : Function.Injective g) :
    Nonempty (S ≃ₗ[R] S') := by
  let s : Set (Submodule R M) := {m | Nonempty (m ≃ₗ[R] S)}
  have : ∀ m : s, IsSimpleModule R m := fun m => m.2.elim fun e => IsSimpleModule.congr e
  have e0 := LinearEquiv.ofInjective g hg
  have : IsSimpleModule R (LinearMap.range g) := IsSimpleModule.congr e0.symm
  have hle : LinearMap.range g ≤ sSup s := fun x _ => by
    refine (iSup_le (a := sSup s) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp
  obtain ⟨m, ⟨e⟩, ⟨e'⟩⟩ := (LinearMap.range g).linearEquiv_of_le_sSup s hle
  exact ⟨(e0.trans (e'.trans e)).symm⟩

section Rep

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def isoPart (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

theorem isoPart_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ∈ isoPart σ ρ) :
    ρ g x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

theorem isoPart_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ isoPart σ ρ) : T x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ)
    ⟨v, rfl⟩
  exact (congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)

theorem equiv_of_isoPart (σ : Representation ℂ G W) (σ' : Representation ℂ G W') (ρ : Representation ℂ G V)
    [σ.IsIrreducible] [σ'.IsIrreducible] (h : isoPart σ ρ = ⊤) (f' : σ'.IntertwiningMap ρ) (hf' : f' ≠ 0) :
    Nonempty (σ.Equiv σ') := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'
  obtain ⟨e⟩ := equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by
    have hx : ρ.asModuleEquiv x ∈ isoPart σ ρ := h ▸ Submodule.mem_top
    have hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule,
        LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      have : Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈
          ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f :=
        Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩
      exact this
    exact hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi
  exact ⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem isoPart_fin {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (k : GL (Fin a) (Af E)) {x : V}
    (hx : x ∈ isoPart σ (τ.comp (locGL E a w))) : τ k x ∈ isoPart σ (τ.comp (locGL E a w)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
  have hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]
  have h1 := isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by
    simp only [MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)
  rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem isoPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : π.V}
    (hx : x ∈ isoPart σ (π.locRep w)) : π.op o x ∈ isoPart σ (π.locRep w) := by
  cases o with
  | fin k =>
    exact isoPart_fin π.finPart w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem isLocComp_unique (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : π.IsLocComp w σ) (h' : π.IsLocComp w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨f', h0', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  refine equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩
    fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1
  · refine absurd (LinearMap.ext fun v => ?_) h0
    have h2 : isoPart σ.ρ (π.locRep w) = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    have h3 : f v ∈ isoPart σ.ρ (π.locRep w) :=
      Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩
    rw [h2] at h3
    exact h3
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.CuspRep.LocUniq

theorem GlobalTheory.CuspRep.CG.IsLoc.unique : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin a) (w.adicCompletion E))), π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ a π w σ σ' h h'
  induction π using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  exact Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ConstNotCusp

variable (E : Type) [Field E] [NumberField E] (a r : ℕ)

theorem discreteTopology_ratN : DiscreteTopology (ratN E a r) := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hW : IsOpen (Set.pi Set.univ fun _ : BlockIx a r => V) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hVo
  convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratN E a r)) using 1
  ext ⟨_, x, rfl⟩
  constructor
  · intro h p _
    have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
    exact h1.symm ▸ hV0
  · intro h
    have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
    subst hx
    exact Subtype.ext (map_zero _)

theorem exists_compact_ratN : ∃ K : Set (BlockIx a r → Ad E), IsCompact K ∧
    ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  choose y hy using fun p => h (x p)
  refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
  change algebraMap E (Ad E) (-y p) + x p ∈ K
  rw [map_neg, neg_add_eq_sub]
  exact hy p

theorem not_isCuspidal_oneFn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    2 ≤ a → ¬ IsCuspidal (oneFn E a).1 := by
  intro E _ _ _ a ha h
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  letI : MeasurableSpace (BlockIx a 1 → Ad E) := borel _
  haveI : BorelSpace (BlockIx a 1 → Ad E) := ⟨rfl⟩
  haveI := discreteTopology_ratN E a 1
  obtain ⟨K, hK, hcov⟩ := exists_compact_ratN E a 1
  obtain ⟨⟨μ, F, hμ, hF, h1⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratN E a 1) K hK hcov
  have h2 : ∫ _ in F, (1 : ℂ) ∂μ = 0 := h 1 one_pos (by omega) μ F hμ hF 1
  simp [Measure.real, h1] at h2

end GlobalTheory.ConstNotCusp
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogFun

theorem partial_eq {R : Type} [CommRing R] (u : ℕ → R) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : R) * u k = 1)
    (x s : R) (n : ℕ) (hn : IsUnit ((n.factorial : ℕ) : R))
    (hs : ((n.factorial : ℕ) : R) * s =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * x ^ (k + 1)) :
    s = ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  apply hn.mul_left_cancel
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : R) = ((n.factorial / (k + 1) : ℕ) : R) * ((k + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, ← h1]
  generalize ((n.factorial / (k + 1) : ℕ) : R) = q at h2 ⊢
  rw [h2]
  linear_combination (-((-1) ^ k * q * x ^ (k + 1))) * hu k

theorem partial_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u : ℕ → R) (x : R) (hx : x ∈ I)
    {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.range m, (-1) ^ k * u k * x ^ (k + 1) -
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) ∈ I ^ n := by
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.1 hk).1; omega) (Ideal.pow_mem_pow hx (k + 1))

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem {e : Per.Fl l} (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ∈ Per.kerP l := by
  exact GlobalTheory.RingIface.alg_mem_kerP l (by rw [Model.theta_mu, he, sub_self])

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem isLog_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) : Per.IsLog l e (j t) := by
  refine GlobalTheory.CrisIncl.isLog_of_partial l e he _ fun n => ?_
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      partial_eq u hu _ _ _ (hf _) hs, partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (partial_sub_mem _ u _ (mu_mem he) (le_max_right _ _)))
  exact ⟨c, hc, by rw [key, ev_alg]⟩

theorem log_fun : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) :=
  fun _ _ _ _ he ht => ⟨fun _ h => Model.isLogA_unique h ht, fun g => Model.isLogA_sigA g ht,
    Model.isLogA_phiA ht, fun _ hj => isLog_map he ht hj⟩

end GlobalTheory.MemLoc.LogFun
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  first | exact @GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | exact GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | (intros; apply GlobalTheory.MemLoc.mem_FilD_iff_xi_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bdRPlus_isDomain_bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @GlobalTheory.MemLoc.BdRField.bdR_isField | exact GlobalTheory.MemLoc.BdRField.bdR_isField | (intros; apply GlobalTheory.MemLoc.BdRField.bdR_isField <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory

theorem restrict_torus_smul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hj _ h₀j
  letI := H.starRing
  have key : ∀ a : 𝓞 E, j ≫ tV.act.act a =
      SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)) ≫ j := by
    intro a
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated tV.G.hom := tV.semi.separated
    have : Flat (splitTorusAff ZU P'.D.toPre.X).hom :=
      (ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp V) P'.D.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (spMap α) _) ?_
    have e1 := TorusPart.pullTorus_comp n.cart n.cart (tV.act.act a) (tΩ.act.act a) (n.act a) j
    have e2 := TorusPart.pullTorus_torusMap_comp n.cart j
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a))
    have e3 := TorusPart.PELUnif.torus_comp_act P' hβ n' a
    rw [hj, e3] at e1
    rw [hj] at e2
    rw [← TorusPart.pullTorus_left n.cart, ← TorusPart.pullTorus_left n.cart, e1, e2]
  have hmono := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P (ResidueField V) ((residue V).comp ψ) 0
    (TorusPart.map_pow_one_eq_zero h₀) t₀.G m₀'.φ m₀'.cart).1
  have key2 : ∀ a : 𝓞 E, ρ.comp (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) =
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)).comp ρ := by
    intro a
    have e := congrArg (TorusPart.pullTorus m₀.cart) (key a)
    rw [TorusPart.pullTorus_comp m₀.cart m₀.cart (tV.act.act a) (t₀.act.act a) (m₀.act a) j,
      TorusPart.pullTorus_torusMap_comp m₀.cart j, h₀j, Category.assoc,
      TorusPart.PELUnif.torus_comp_act P h₀ m₀' a, ← Category.assoc, ← Category.assoc,
      ← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_comp] at e
    haveI : Mono (TorusPart.PELUnif.torus P h₀ m₀') := hmono
    have : Nonempty (Sp (ResidueField V)) := inferInstance
    exact SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro a x
  have k := DFunLike.congr_fun (key2 (H.bar a)) x
  rw [show H.bar (H.bar a) = a from star_star a] at k
  exact k

end GlobalTheory
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  first | exact @GlobalTheory.SplitCrit.splitRep_of_models | exact GlobalTheory.SplitCrit.splitRep_of_models | (intros; apply GlobalTheory.SplitCrit.splitRep_of_models <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.block_data_level_forms_transport_field_map : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ), B.Ok s →
    GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e B B' ℓ ℓ' Z Z' →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x y : Fin (B.dZ ℓ Z) → K, Formalism.DivisionValues.hform (B'.HZ ℓ' Z') (Matrix.mulVec Gm (fun k => φ (x k))) (Matrix.mulVec Gm (fun k => φ (y k))) = φ (Formalism.DivisionValues.hform (B.HZ ℓ Z) x y) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC | exact GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC | (intros; apply GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)) (Ni : Measure (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)), StepData σ J x a B J' → IsProd b ν mi mv → IsProd b ν' mi' mv' → OnOrbit (Ainf F) σ J x mi → (∀ v, OnOrbit (Fv F v) σ J x (mv v)) → IsInvTup (Ainf F) σ J' mi' → (∀ v, IsInvTup (Fv F v) σ J' (mv' v)) → TwoStep (Ainf F) σ J x B mi mi' Ni → (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) → TwoStep (AF F) σ J x B ν ν' N → IsProd b N Ni Nv := by
  first | exact @GlobalTheory.GaugeEx.TsProd.twoStep_isProd | exact GlobalTheory.GaugeEx.TsProd.twoStep_isProd | (intros; apply GlobalTheory.GaugeEx.TsProd.twoStep_isProd <;> assumption)
end
