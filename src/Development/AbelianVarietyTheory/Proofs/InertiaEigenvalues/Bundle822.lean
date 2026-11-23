module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearizedFrobeniusInvertibleUpToPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle450
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle088
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle811
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle813
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtCoeff

open TensorProduct

theorem exists_ext_map {K' : Type} [Field K'] (σ' : K' →+* ℂ) {X : Type} (V : Submodule K' (MvPolynomial X K'))
    (V' : Submodule ℂ (MvPolynomial X ℂ)) {W : Type*} [AddCommGroup W] [Module ℂ W] (c0 : V →ₛₗ[σ'] W) :
    ∃ c : V' →ₗ[ℂ] W, ∀ (v : V) (v' : V'), (v' : MvPolynomial X ℂ) = MvPolynomial.map σ' (v : MvPolynomial X K') → c v' = c0 v := by
  letI : Algebra K' ℂ := σ'.toAlgebra
  letI : Module K' W := Module.compHom W σ'
  haveI : IsScalarTower K' ℂ W := ⟨fun k a w => by
    show (σ' k * a) • w = σ' k • a • w
    rw [mul_smul]⟩
  let c0l : V →ₗ[K'] W := { toFun := c0, map_add' := c0.map_add, map_smul' := fun k v => c0.map_smulₛₗ k v }
  let F : ℂ ⊗[K'] V →ₗ[ℂ] W := c0l.liftBaseChange ℂ
  let ψ : ℂ ⊗[K'] V →ₗ[ℂ] MvPolynomial X ℂ :=
    (MvPolynomial.algebraTensorAlgEquiv K' ℂ).toLinearMap.comp (V.subtype.baseChange ℂ)
  have hψ1 : ∀ v : V, ψ (1 ⊗ₜ v) = MvPolynomial.map σ' (v : MvPolynomial X K') := by
    intro v
    simp [ψ, MvPolynomial.algebraTensorAlgEquiv_tmul]
    rfl
  have hinj : Function.Injective ψ := by
    refine (MvPolynomial.algebraTensorAlgEquiv K' ℂ).injective.comp ?_
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) V.subtype V.injective_subtype
  let e := LinearEquiv.ofInjective ψ hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (F.comp e.symm.toLinearMap)
  refine ⟨g.comp V'.subtype, fun v v' h => ?_⟩
  have hmem : (v' : MvPolynomial X ℂ) ∈ LinearMap.range ψ := ⟨1 ⊗ₜ v, (hψ1 v).trans h.symm⟩
  have key : g (v' : MvPolynomial X ℂ) = F (e.symm ⟨_, hmem⟩) := LinearMap.congr_fun hg ⟨_, hmem⟩
  have he : e.symm ⟨_, hmem⟩ = 1 ⊗ₜ v := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    simp [e, LinearEquiv.ofInjective_apply, hψ1, h]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, key, he, F, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_extC : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T1 : Type) (A : FamIn D.what₂.LL G Pl0 T1 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) (Tp : Type) (tup : Tp → T1) (O : OMDat T.toCore R j Tp tup), ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c := by
  intro D G _ _ Pl0 T1 A T _ R j Tp tup O
  obtain ⟨c, hc⟩ := exists_ext_map (inC O.c') (VV O.c'.F (lamV D j)) (VV ℂ (lamV D j)) O.c0'
  exact ⟨c, fun v v' h => hc v v' h⟩

end GlobalTheory.ExtCoeff
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I → ∀ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : N →ₛₗ[B.D.φ] P), SemiBC u → ∀ L : P →ₗ[B.A] N, (∀ x, L (u x) = Ψ x) → ∃ n : ℕ, (∀ y, L y = 0 → t ^ n • y = 0) ∧ ∀ x, ∃ y, L y = t ^ n • x := by
  first | exact @GlobalTheory.BSP.LinFrob.linFrob_inv_pow | exact GlobalTheory.BSP.LinFrob.linFrob_inv_pow | (intros; apply GlobalTheory.BSP.LinFrob.linFrob_inv_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniLevelLift

theorem main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r q : ℕ), 1 < q → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ → NG.LevelUni J χ s r ψ₀ ξ → ∀ p : GAf L n, TrivOutside {s.v} p → IsLiftAt s r q (1 : GL (Fin r) (ZMod q)) (s.loc n p) → ∃ h : p ∈ J, χ ⟨p, h⟩ = 1 := by
  intro L _ _ _ n J χ s r q hq ψ₀ ξ hψ hU p hp hL
  haveI : Fact (1 < q) := ⟨hq⟩
  set h := s.loc n p with hh
  have hone : ∀ i j : Fin r, ((((1 : GL (Fin r) (ZMod q)) : Matrix (Fin r) (Fin r) (ZMod q)) i j).val :
      s.v.adicCompletion (maximalRealSubfield L)) = if i = j then 1 else 0 := by
    intro i j
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [ZMod.val_one, Nat.cast_one]
    · rw [ZMod.val_zero, Nat.cast_zero]
  have hent : ∀ a b : Fin n, Valued.v ((h.val - 1) a b) < 1 ∧
      (¬ (a.val < r ∧ b.val < r) → h.val a b = if a = b then 1 else 0) := by
    intro a b
    have := hL a b
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dite_eq_left hab, hone] at this
      refine ⟨?_, fun h' => absurd hab h'⟩
      convert this using 3
      rw [Matrix.sub_apply, Matrix.one_apply]
      by_cases e : a = b
      · subst e; simp
      · have e' : (⟨a.val, hab.1⟩ : Fin r) ≠ ⟨b.val, hab.2⟩ := fun h2 => e (Fin.ext (by simpa using congrArg Fin.val h2))
        rw [if_neg e, if_neg e']
    · rw [dite_eq_right hab] at this
      refine ⟨?_, fun _ => this⟩
      rw [Matrix.sub_apply, this, Matrix.one_apply]
      simp
  have hK : h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) :=
    (GlobalTheory.FixedAtSplit.mem_KOne_iff' h).2 fun a b => (hent a b).1
  have hKi := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 (inv_mem hK)
  have hint : ∀ (y c : s.v.adicCompletion (maximalRealSubfield L)), Valued.v (y - c) < 1 → Valued.v c ≤ 1 →
      Valued.v y ≤ 1 := by
    intro y c h1 h2
    have := Valuation.map_add_le Valued.v (le_of_lt h1) h2
    rwa [sub_add_cancel] at this
  have hone' : ∀ a b : Fin n, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) ≤ 1 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have huni : NG.UniRT s r h := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact (hent a b).1
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact hKi a b
    · have hne : a ≠ b := fun e => by rw [e] at ha; omega
      rw [(hent a b).2 (by omega), if_neg hne, map_zero]; exact zero_lt_one
    · have hne : a ≠ b := fun e => by rw [e] at hlt; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · subst he
      have := (hent a a).1
      rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hpJ : p ∈ J := (hU.mem p hp).2 huni
  have hdet : NG.detDD s r h = 1 := by
    have hm : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1) = 1 := by
      ext a b
      rw [Matrix.of_apply, (hent a.1 b.1).2 (by have := a.2; omega), Matrix.one_apply]
      simp only [Subtype.ext_iff]
    unfold NG.detDD
    rw [hm, Matrix.det_one]
  have hchr := hU.chr p hpJ hp 1 (by rw [Units.val_one, hdet])
  have hsup : ψ₀ (NG.supDiag s r h) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := fun e => by rw [e] at hab; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  refine ⟨hpJ, Units.ext ?_⟩
  rw [hchr, hsup, map_one, one_mul, Units.val_one]

end GlobalTheory.UniLevelLift
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KurValue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie Polynomial

theorem exists_norm_eq_of_mem_closure {K : Type*} [NormedField K] [IsUltrametricDist K] {S : Set K} {x : K}
    (hx : x ∈ closure S) (h0 : x ≠ 0) : ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ‖x‖ (norm_pos_iff.2 h0)
  refine ⟨y, hy, ?_⟩
  rw [dist_comm, dist_eq_norm] at hd
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hd.ne
  rw [sub_add_cancel, max_eq_right hd.le] at this
  exact this.symm

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral (PadicAlgCl p) x) :
    x ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range :=
  minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))

theorem exists_lift {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ ψ : F →+* PadicAlgCl p, ∀ a, algebraMap (PadicAlgCl p) ℂ_[p] (ψ a) = φ a := by
  have h : ∀ a : F, φ a ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range := fun a => by
    have h1 : IsIntegral ℚ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℚ) a).map φ.toRatAlgHom
    exact mem_range_of_isIntegral h1.tower_top
  choose f hf using h
  have hi := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, hf⟩
  · rw [hf, map_one, map_one]
  · simp only [map_mul, hf]
  · simp only [map_zero, hf]
  · simp only [map_add (f := _), hf]

theorem exists_finite {F : Type} [Field F] [NumberField F] (ψ : F →+* PadicAlgCl p) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (∀ a, ψ a ∈ K) ∧
      ∀ x ∈ K, ∃ a, ‖x‖ = ‖ψ a‖ := by
  let b := Module.finBasis ℚ F
  refine ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)), ?_, fun a => ?_, fun x hx => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

  · rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · let M : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      ψ.fieldRange.topologicalClosure.toIntermediateField fun r => by
        have hc : IsClosed {r : ℚ_[p] | algebraMap ℚ_[p] (PadicAlgCl p) r ∈ ψ.fieldRange.topologicalClosure} :=
          (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
        refine (Padic.denseRange_ratCast p).induction_on r hc fun q => ?_
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem _ _
    have hM : IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)) ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      exact Subfield.le_topologicalClosure ψ.fieldRange ⟨b i, rfl⟩
    by_cases h0 : x = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (ψ.fieldRange : Set (PadicAlgCl p))) (hM hx) h0
    exact ⟨a, h⟩

theorem exists_norm_eq {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : x ∈ kurC φ) :
    ∃ a : F, ‖x‖ = ‖φ a‖ := by
  obtain ⟨ψ, hψ⟩ := exists_lift φ
  obtain ⟨K, hK, hmem, hnorm⟩ := exists_finite ψ
  let M : Subfield ℂ_[p] := (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension p K).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])
  have hle : kurC φ ≤ M.topologicalClosure := by
    refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
    · rintro _ ⟨a, rfl⟩
      exact M.le_topologicalClosure ⟨ψ a, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hmem a), hψ a⟩
    · refine Subfield.topologicalClosure_minimal _ (Subfield.closure_le.2 ?_) (Subfield.isClosed_topologicalClosure _)
      rintro ζ ⟨n, hn, hpn, hζ⟩
      obtain ⟨ξ, rfl⟩ := mem_range_of_isIntegral (IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one))
      refine M.le_topologicalClosure ⟨ξ, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow hK hpn ?_, rfl⟩
      apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
      rw [map_pow, hζ, map_one]
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (M : Set ℂ_[p])) (hle hx) h0
  obtain ⟨n, hn, hyn⟩ := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff hK y).1 hy
  obtain ⟨z, hz, hyz⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn p K hK hn hyn
  obtain ⟨a, ha⟩ := hnorm z hz
  refine ⟨a, ?_⟩
  rw [h, ← hψ, norm_algebraMap', norm_algebraMap', ← ha, hyz]

theorem exists_near {F : Type} [Field F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ y ∈ kurC φ, ‖x - y‖ < 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact ⟨0, zero_mem _, by rwa [sub_zero]⟩
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x one_pos
  rw [dist_eq_norm, PadicComplex.coe_eq] at hz
  have hz1 : ‖z‖ = 1 := by
    have h1 : ‖algebraMap (PadicAlgCl p) ℂ_[p] z - x‖ < ‖x‖ := by rwa [norm_sub_rev, heq]
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le, heq, norm_algebraMap'] at this
  obtain ⟨ζ, m, hm, hζ, h⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar z hz1
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] ζ, root_mem_kurC φ hm (by rw [← map_pow, hζ, map_one]), ?_⟩
  have e : x - algebraMap (PadicAlgCl p) ℂ_[p] ζ =
      (x - algebraMap (PadicAlgCl p) ℂ_[p] z) + algebraMap (PadicAlgCl p) ℂ_[p] (z - ζ) := by
    rw [map_sub]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_algebraMap']))

theorem kurC_value_residue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    (∀ x ∈ kurC φ, ∃ a : F, ‖x‖ = ‖φ a‖) ∧ ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ∃ y ∈ kurC φ, ‖x - y‖ < 1 :=
  fun _ _ _ _ _ φ => ⟨fun _ hx => exists_norm_eq φ hx, fun _ hx => exists_near φ hx⟩

end GlobalTheory.KurValue

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExist

theorem exists_algCl {p : ℕ} [Fact p.Prime] {z : ℂ_[p]} (hz : IsAlgebraic ℚ_[p] z) :
    ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = z := by
  have h1 : IsIntegral (PadicAlgCl p) z := (hz.tower_top (PadicAlgCl p)).isIntegral
  have h2 : (minpoly (PadicAlgCl p) z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)
  exact minpoly.mem_range_of_degree_eq_one _ _ h2

theorem exists_factor_algCl {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ b : F →+* PadicAlgCl p, ∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (b x) = φ x := by
  have hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x := fun x => by
    apply exists_algCl
    have h1 : IsAlgebraic ℚ (φ x) := by
      have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
      simpa using this
    exact h1.tower_top ℚ_[p]
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; exact map_mul φ x y
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add (f := _), hf, hf, hf]; exact map_add φ x y

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have h := vV_mul (V := V) hx (inv_ne_zero hx)
  have h1 : vV V (1 : K) = 0 := by simp [vV]
  rw [mul_inv_cancel₀ hx, h1] at h
  omega

theorem norm_lt_one_iff_vV_pos {C : Type} [NormedField C] (c : K →+* C)
    (hn : ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V K)) {y : K} (hy : y ≠ 0) :
    ‖c y‖ < 1 ↔ 0 < vV V y := by
  have key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x := fun x =>
    (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))
  have h0 : 0 < ‖c y‖ := norm_pos_iff.2 ((map_ne_zero c).2 hy)
  have hi := key y⁻¹
  rw [map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0] at hi
  constructor
  · intro h
    by_contra h'
    have := hi.2 (by omega)
    linarith
  · intro h
    by_contra h'
    have := hi.1 (not_lt.1 h')
    omega

end Val

theorem mem_iff_vLa_pos {F : Type} [Field F] [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F)
    (hx : (x : F) ≠ 0) : x ∈ la.asIdeal ↔ 0 < vLa la (x : F) := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have h0 : la.valuation F (x : F) ≠ 0 := (la.valuation F).ne_zero_iff.2 hx
  have e := WithZero.log_lt_log h0 one_ne_zero
  rw [WithZero.log_one] at e
  change _ ↔ 0 < -WithZero.log (la.valuation F (x : F))
  rw [← e]
  omega

theorem exists_isReading : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p])
    (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes →
    ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  intro p _ F _ _ φ T io e ho hT
  obtain ⟨q, hq, c, hn⟩ := GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT

  have ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal := by
    intro x
    by_cases hx : (x : F) = 0
    · have hx' : x = 0 := by exact_mod_cast hx
      subst hx'
      simp
    rw [norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (by positivity)
    · intro h
      exact mul_pos (by exact_mod_cast ho.1) h

  have hqp : q = p := by
    have h1 := (ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)
    have e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q]) := by simp
    rw [e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1
  subst hqp
  obtain ⟨b, hb⟩ := exists_factor_algCl φ
  have hbn : ∀ x, ‖b x‖ = ‖φ x‖ := fun x => by
    rw [← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b
    (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha
      (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))
  refine ⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply]
    have := hg a
    simp only [RingHom.comp_apply] at this
    rw [RingHom.coe_coe, this, hb]
  · intro x
    simp only [RingHom.comp_apply]
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]
    rfl

end GlobalTheory.GeoTie.ReadExist

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gb_sub_b_mem_filZero | exact GlobalTheory.BKGal.gb_sub_b_mem_filZero | (intros; apply GlobalTheory.BKGal.gb_sub_b_mem_filZero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.potentialCocycle_mem_lPow_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.BKGal.potential_cocycle_mem_lpow | exact GlobalTheory.BKGal.potential_cocycle_mem_lpow | (intros; apply GlobalTheory.BKGal.potential_cocycle_mem_lpow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_breuil_kisin_datum_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O) (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂), IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  first | exact @GlobalTheory.CocycleNat.main | exact GlobalTheory.CocycleNat.main | (intros; apply GlobalTheory.CocycleNat.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  first | exact @GlobalTheory.IntConnTaylor.main | exact GlobalTheory.IntConnTaylor.main | (intros; apply GlobalTheory.IntConnTaylor.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K)) (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  first | exact @GlobalTheory.BSP.fhom_ext_bk | exact GlobalTheory.BSP.fhom_ext_bk | (intros; apply GlobalTheory.BSP.fhom_ext_bk <;> assumption)
end
