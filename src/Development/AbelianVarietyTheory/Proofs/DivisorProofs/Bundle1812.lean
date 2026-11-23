module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.StdMass

variable {D : D7}

theorem coord_isIntegral (V : HSp D) (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {x : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (k : Fin V.rank) : IsIntegral ℤ (x k) := by
  have key : ∀ y ∈ V.L0, ∃ a : 𝓞 D.host.E, (a : D.host.E) = V.frame.repr y k := by
    intro y hy
    rw [hL] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = k
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul D.host.E r y, map_smul]
      simp [ha, Algebra.smul_def]
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  obtain ⟨a, ha⟩ := key _ hx'
  have e : V.frame.repr (∑ i, x i • V.frame i) k = x k := by
    rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← e, ← ha]
  exact RingOfIntegers.isIntegral_coe a

theorem mem_lattice_of_rational_mem_completion (V : HSp D) (v : Fin V.rank → D.host.E)
    (h : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] v k) ∈ latHat D.host.F D.host.E (L0c D V)) : v ∈ L0c D V := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hw
      refine ⟨V.frame.equivFun.symm w, ?_, V.frame.equivFun.apply_symm_apply w⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hw
  have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hxy : V.hT (e x) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hyx : V.hT y (e x) = 0 := by
        rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
      simp [hyx]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
        (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective w
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hfull]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  have hr := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L (V.standardTuple_isLattice.fg.map _) hsp).1 v
  rw [← hL]
  refine hr.1 ?_
  have hle : latHat D.host.F D.host.E (L0c D V) ≤ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [← hL] at hx
    exact AddSubgroup.subset_closure ⟨a, fun w => ha w, x, hx, rfl⟩
  exact hle h

theorem card_stab_le (V : HSp D) (hg : V.gram = 1)
    (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Nat.card (Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1) ≤ NumberField.Units.torsionOrder D.host.E ^ V.rank * V.rank.factorial := by
  obtain ⟨hSf, hSc⟩ := GlobalTheory.T.integral_unitary_matrices_finite_card_le D V.rank
  have hx : ∀ x : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1, ∃ u : GL (Fin V.rank) D.host.E,
        u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
        Formalism.UG.bc (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) u =
          HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 := fun x => by
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 x.1.2
    exact ⟨u, hu, e⟩
  choose u hu hue using hx
  have hunit : ∀ x, (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᴴ * (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 :=
    fun x => by
    have h := hu x
    change Formalism.UG.cT _ (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram at h
    rw [hg, Matrix.mul_one] at h
    convert h using 2
    ext a b
    rfl
  have hint : ∀ x a b, IsIntegral ℤ ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun x a b => by
    have hK : x.1.1 ∈ GlobalTheory.Mass.Levels.latStab V := by
      have := x.2
      simpa [Formalism.UG.stabAt] using this
    have hej : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ L0c D V := by
      show ∑ i, (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) i • V.frame i ∈ V.L0
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp), hL]
      rw [Pi.single_eq_same, one_smul]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) ∈
        latHat D.host.F D.host.E (L0c D V) :=
      AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, _, hej, rfl⟩
    have h2 := ((GlobalTheory.Mass.Levels.mem_latStab V x.1.1).1 hK _).1 hy
    have e : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1).1 *ᵥ
        (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) =
        fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b := by
      rw [← hue x]
      funext k
      change ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) *ᵥ
        ((inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ∘ (Pi.single b 1))) k =
          (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b)
      rw [← RingHom.map_mulVec]
      simp [Matrix.mulVec_single_one]
    rw [e] at h2
    exact coord_isIntegral V hL (mem_lattice_of_rational_mem_completion V _ h2) a
  let f : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1 →
      {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
    fun x => ⟨(u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E), hunit x, hint x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = u y := congrArg Subtype.val hxy
    have h2 : u x = u y := Units.ext h1
    have h3 : HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 =
        HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram y.1.1 := by
      rw [← hue x, ← hue y, h2]
    have h4 : x.1.1 = y.1.1 := Subtype.ext h3
    exact Subtype.ext (Subtype.ext h4)
  haveI := hSf.to_subtype
  calc Nat.card _ ≤ Nat.card {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_coe_set_eq _
    _ ≤ _ := hSc

theorem massLower_of_stdV : ∀ D : D7, StdV D → MassLower D := by
  intro D hS i _
  obtain ⟨h1, h2⟩ := hS i
  have hg : (Vc D i).gram = 1 := Matrix.ext fun a b => by
    rw [Matrix.one_apply]
    exact h1 a b
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have e : gramAt D (Vc D i) τ = 1 := Matrix.ext fun a b => by
      simp [gramAt, hg, Matrix.one_apply]
    rw [e]
    exact Matrix.PosDef.one
  have hK := GlobalTheory.Mass.Levels.latStab_compact_open (Vc D i)
  have hfc := GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND (Vc D i)) (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef (Vc D i) hpd) hK.1 hK.2
  have hle := hfc.inv_card_le 1
  have hpos := hfc.stabOrder_pos (DoubleCoset.mk _ _ 1)
  rw [GlobalTheory.Mass.stabOrder_mk] at hpos
  have hc := card_stab_le (Vc D i) hg h2
  have hr : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  unfold GlobalTheory.Mass.unitaryMass
  refine le_trans ?_ hle
  rw [one_div, ← hr]
  exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hc)

end GlobalTheory.LowRow.StdMass
end
end

section

namespace GlobalTheory.TwistedKernelChar

section General

open NumberField IsDedekindDomain Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem inf_triv [_root_.NumberField.IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem hasInf_mul_inv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n m : I → ℤ} {α β γ : HChar L}
    (ha : α.HasInf φ n) (hb : ∀ k, β.inf k = 1) (hc : γ.HasInf φ m) : (α * β * γ⁻¹).HasInf φ (fun i => n i - m i) := by
  intro k
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, hb, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, ha k, hc k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have h1 : φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1, div_eq_mul_inv (_ ^ _)]

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem frame_char (D : D7) (C : Formalism.L2.Host.CharFrame D) (i : Fin D.R.m) (l : ℕ) :
    ∃ (b : ℕ) (n : D.R.Psi → ℤ), b ≠ 0 ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ Q.asIdeal → ((badN D : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → (C.mu0 i * C.delAt l * C.eta⁻¹).UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        ∀ k : D.host.Fˣ, (C.mu0 i * C.delAt l * C.eta⁻¹).resFin (Q.under (𝓞 D.host.F)) k = 1) ∧
      (∀ Q, (C.mu0 i * C.delAt l * C.eta⁻¹).TameAt Q) ∧
      (C.mu0 i * C.delAt l * C.eta⁻¹).HasInf (Formalism.L2.Host.embPsi D.host) n := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨p, hp, hpl, hδ⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ D.host.levelPrimes ∧ Formalism.L2.Host.IsDelta (H := D.host) p (C.delAt l) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    · exact ⟨_, D.host.pde'_prime, D.host.pde_level.2, C.isDel'⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_level.1, C.isDel⟩
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ∀ a b : ℕ, a ∣ b → (a : 𝓞 D.host.E) ∈ Q.asIdeal →
      (b : 𝓞 D.host.E) ∈ Q.asIdeal := by
    rintro Q a b ⟨u, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have lev : ∀ a ∈ D.host.levelPrimes, a ∣ badN D := fun a ha =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) ha) _
  obtain ⟨n, -, hn⟩ := (C.isMu0 i).inf
  obtain ⟨o, ho, hod⟩ := hδ.fin
  refine ⟨D.host.g 0 * D.host.g 1 * p, fun τ => n τ - 1,
    mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) hp.ne_zero, fun Q hQ => ?_,
    fun Q hQ x hx => ?_, fun Q hQ x => ?_, fun Q x hx hx' => ?_,
    hasInf_mul_inv hn (inf_triv _ ho hod) C.isEta.inf⟩
  · rw [Nat.cast_mul, Nat.cast_mul] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · exact key Q _ _ (lev _ (D.host.g_level 0)) h
      · exact key Q _ _ (lev _ (D.host.g_level 1)) h
    · exact key Q _ _ (lev _ hpl) h
  · have a1 : (C.mu0 i).UnrAt Q := (C.isMu0 i).unr Q fun j hj => hQ (key Q _ _ (by
      refine Dvd.dvd.mul_right ?_ p
      rw [← Fin.prod_univ_two D.host.g]
      exact Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)) hj)
    have a2 : (C.delAt l).UnrAt Q := hδ.unr Q fun hj => hQ (key Q _ _ (Dvd.intro_left _ rfl) hj)
    change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [a1 x hx, a2 x hx,
      C.isEta.unr Q x hx, inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
      (C.isMu0 i).triv.1, hδ.triv.1, C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
      Finset.card_pair hQ.symm, ite_eq_right (by norm_num), inv_one, one_mul, one_mul]
  · change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [(C.isMu0 i).tame Q x hx hx',
      hδ.tame Q x hx hx', C.isEta.unr Q x hx, inv_one, one_mul, one_mul]



theorem twisted_kernel_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i _ v _ _ _ _ _ _ _ _ ℓ _ _ χ ξR ω φ hK Λ h N _ _ _ _ _ e Ps yd _ _ hb
  obtain ⟨b, n, h0, h1, h2, h3, h4, h5⟩ := frame_char D R.C i (Formalism.EigenvalueLevelCeiling.plc v)
  refine ⟨_, b, _, _, _, n, h0, fun Q hQ hm => hb Q hQ ?_,
    GlobalTheory.ClassScalarValue.chrEq_mul_inv (hC.lev.mu0 i) hK.chr hC.lev.eta, h2, h3, h4, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (h1 Q hm)

end GlobalTheory.TwistedKernelChar
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnip

theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add (f := _)]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (q : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

end GlobalTheory.MixXUnip
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
end
