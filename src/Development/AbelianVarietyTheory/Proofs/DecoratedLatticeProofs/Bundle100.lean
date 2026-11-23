module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle097
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramFrame

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem integral_adelic_lattice_mul_mem {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  exact GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem hz hw

theorem one_int_af : ∀ v : HeightOneSpectrum (𝓞 F),
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := fun v => by
  show (1 : v.adicCompletion F) ∈ _
  exact one_mem _

theorem mem_integral_adelic_lattice_iff (z : GlobalTheory.AdLat.RA F E) :
    z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) ↔
      GlobalTheory.LevSplit.swp F E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [GlobalTheory.LevSplit.swp_tmul]
      have e : (algebraMap (𝓞 E) E x') ⊗ₜ[F] a =
          ((algebraMap (𝓞 E) E x') ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [e]
      refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x', rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add u u' _ _ hu hu' => rw [map_add]; exact add_mem hu hu'
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  · intro hz
    have key : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∃ t ∈ GlobalTheory.AdLat.hat1 F
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E), GlobalTheory.LevSplit.swp F E t = s := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem s hs =>
        rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
        · exact ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E c),
            AddSubgroup.subset_closure ⟨1, one_int_af, _, (FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩, rfl⟩, rfl⟩
        · exact ⟨b ⊗ₜ[F] (1 : E), AddSubgroup.subset_closure ⟨b, hb, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, AddSubgroup.subset_closure ⟨1, one_int_af, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, map_one _⟩
      | add a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t + t', add_mem ht ht', map_add _ _ _⟩
      | neg a _ ha =>
        obtain ⟨t, ht, rfl⟩ := ha
        exact ⟨-t, neg_mem ht, map_neg _ _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t * t', integral_adelic_lattice_mul_mem ht ht', map_mul _ _ _⟩
    obtain ⟨t, ht, e⟩ := key _ hz
    rwa [GlobalTheory.LevSplit.swp_bij.1 e] at ht

end Gen
end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

def conjEquiv (I : AutInst) : Gal(I.E/I.F) :=
  AlgEquiv.ofAlgHom I.cm.sig I.cm.sig
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)

theorem conjEquiv_apply (I : AutInst) (x : I.E) : conjEquiv I x = I.cm.sig x := rfl

theorem hatL_selfDual (I : AutInst) : GlobalTheory.ParahoricLift.HatSelfDual I.cm.sig I.J I.L := by
  have hJ : ∀ a b, I.cm.sig (I.J b a) = I.J a b := fun a b => by
    have := congrFun (congrFun I.J_herm a) b
    exact (by simpa [Formalism.UG.cT] using this : starRingEnd I.E (I.J b a) = I.J a b)
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (conjEquiv I) I.cm.sig (fun _ => rfl) I.J I.L I.L_fg I.L_span
    (fun x => by show star (star x) = x; exact star_star x) (fun a b => ?_) (by rw [Matrix.det_transpose]; exact I.J_det)
    (fun v => ?_) (fun s hs => Formalism.UG.P.csDual_sig_mem I.cm.sig hs) mem_integral_adelic_lattice_iff
  · simp only [Matrix.transpose_apply, conjEquiv_apply]
    exact hJ a b
  · rw [I.L_dual v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : (∑ a, ∑ b, v a * I.Jᵀ a b * conjEquiv I (y b)) =
        Formalism.UG.hform (starRingEnd I.E) I.J y v := by
      unfold Formalism.UG.hform
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.transpose_apply, conjEquiv_apply]
      show _ = star (y a) * _ * _
      have : I.cm.sig (y a) = star (y a) := rfl
      rw [this]; ring
    rw [e]
    rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_frame_int : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  intro I β hβ
  set σ := sigA I with hσ
  set JA : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
    I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) with hJA
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) with hB
  set Gm := Formalism.UG.cT σ B * JA * B with hGm
  have hSD := hatL_selfDual I

  have hmem : ∀ a : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, a i ∈ Formalism.L2.Herm.intAf I.F I.E) →
      B *ᵥ a ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := fun a ha => by
    refine (hβ _).2 fun i => ?_
    rw [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]
    exact ha i
  have hsingle : ∀ k, ∀ i, (Pi.single k (1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Fin I.n → _) i ∈
      Formalism.L2.Herm.intAf I.F I.E := fun k i => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

  have hG : ∀ i j, Gm i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    rw [← Formalism.UG.P.hform_single σ Gm i j, hGm, ← Formalism.UG.P.hform_mulVec]
    exact (hSD _).1 (hmem _ (hsingle j)) _ (hmem _ (hsingle i))

  have hdet : IsUnit Gm.det := by
    have h1 : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 β.isUnit
    have h2 : IsUnit (Formalism.UG.cT σ B).det := by
      rw [Formalism.UG.cT, Matrix.det_transpose, show B.map σ = σ.mapMatrix B from rfl, ← RingHom.map_det]
      exact h1.map σ
    have h3 : IsUnit JA.det := by
      rw [hJA, show I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) = (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).mapMatrix I.J from rfl, ← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 I.J_det).map _
    rw [hGm, Matrix.det_mul, Matrix.det_mul]
    exact (h2.mul h3).mul h1
  have hGi : Gm * Gm⁻¹ = 1 := Matrix.mul_nonsing_inv Gm hdet
  have hiG : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul Gm hdet

  have hG' : ∀ i j, (Gm⁻¹) i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    set c : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun l => (Gm⁻¹) l j with hc
    have hx : B *ᵥ c ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by
      refine (hSD _).2 fun z hz => ?_
      have hz' := (hβ z).1 hz
      set a := ((β⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ z with ha
      have hza : z = B *ᵥ a := by
        rw [ha, Matrix.mulVec_mulVec, hB, Units.mul_inv, Matrix.one_mulVec]
      rw [hza, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot]
      have e : Gm *ᵥ c = Pi.single j 1 := by
        funext k
        have := congrFun (congrFun hGi k) j
        rw [Matrix.mul_apply] at this
        simp only [Matrix.mulVec, dotProduct, hc, this, Pi.single_apply, Matrix.one_apply]
      rw [e]
      simp only [dotProduct, Function.comp_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I (hz' j)
    have := (hβ _).1 hx i
    rwa [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec] at this

  let S := Formalism.L2.Herm.intAf I.F I.E
  have inj : Function.Injective fun M : Matrix (Fin I.n) (Fin I.n) S => M.map S.subtype :=
    Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨Gm i j, hG i j⟩, Matrix.of fun i j => ⟨(Gm⁻¹) i j, hG' i j⟩, inj ?_, inj ?_⟩, ?_⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hGi
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hiG
  · rfl

end GlobalTheory.GramFrame
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.SepTypes

theorem coeffSpan_finiteDimensional {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (_root_.GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | (apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)

theorem coeffSpan_rtrans {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (c : G) {h : G → ℂ} (hh : h ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (fun k => h (k * c)) ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have hle : _root_.GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (_root_.GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c)) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩
    simp [LinearMap.funLeft, map_mul]
  exact hle hh

theorem exists_space {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : ι → Type} [∀ i, Group (Γ i)] (K : Subgroup G) (j : (∀ i, Γ i) →* K)
    (hjs : Function.Surjective j) (a : ∀ i, Γ i → G) (hj : ∀ i k, (j (Pi.mulSingle i k) : G) = a i k)
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (Γ i) (W i)) :
    ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧
      (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧
      ∀ φ : G → ℂ, Continuous φ → (∀ i x, (fun k => φ (x * a i k)) ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan (ρ i)) →
        ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  let S : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan (ρ τ)}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩
      zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩
      smul_mem' := fun c {a} ha => ⟨ha.1.const_smul c, fun τ k₀ => Submodule.smul_mem _ c (ha.2 τ k₀)⟩ }
  have hfd : ∀ τ, FiniteDimensional ℂ (_root_.GlobalTheory.Published.AutFin.coeffSpan (ρ τ)) := fun τ => coeffSpan_finiteDimensional (ρ τ)
  have hfin := GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => _root_.GlobalTheory.Published.AutFin.coeffSpan (ρ τ)) hfd
  have hupd : ∀ (x : ∀ τ, Γ τ) τ y,
      Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y := by
    intro x τ y
    funext τ'
    by_cases h : τ' = τ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
  let M := Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ |
    ∀ τ x, (fun y => F (Function.update x τ y)) ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan (ρ τ)}
  let T : S →ₗ[ℂ] M :=
    { toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by
        have := f.2.2 τ (j (Function.update x τ 1))
        convert this using 2 with y
        rw [hupd x τ y, map_mul]⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hT : Function.Injective T := by
    intro a b hab
    have := congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab
    apply Subtype.ext
    funext k
    obtain ⟨x, rfl⟩ := hjs k
    exact congrFun this x
  refine ⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩
  · intro f hf k
    refine ⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩
    obtain ⟨κ₁, rfl⟩ := hjs k
    have key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ =
        (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ)) := by
      intro κ
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      congr 2
      funext τ'
      by_cases h : τ' = τ
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp only [key]
    exact coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)
  · intro φ hφ hty g
    refine ⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩
    have := hty τ (g * (k₀ : G))
    simpa only [Subgroup.coe_mul, hj, mul_assoc] using this

end GlobalTheory.SepTypes

theorem GlobalTheory.typesFiniteSpace : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ K : Subgroup (GA D V), (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧ (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧ ∀ φ : GA D V → ℂ, Continuous φ → (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) → ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  intro D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ
end
