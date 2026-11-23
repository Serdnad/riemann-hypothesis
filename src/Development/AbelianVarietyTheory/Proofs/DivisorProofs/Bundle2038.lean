module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle018
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneCompl

theorem gram_sum {D : D7} (S : HSp D) (a b : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (a i) * S.gram i j * b j = S.hT (S.frame.equivFun.symm a) (S.frame.equivFun.symm b) := by

  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_compl : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  intro D S Λ x y s hΛ hxx hyy hxy hsplit
  have hyx : S.hT y x = 1 := by rw [← S.herm.eq x y, hxy, map_one]
  let W : Submodule D.host.E S.V := LinearMap.ker (LinearMap.pi fun j : Fin 2 => S.hT (![x, y] j))
  have hW : ∀ w, w ∈ W ↔ S.hT x w = 0 ∧ S.hT y w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, Matrix.head_cons]
  have hdec : ∀ z, z - S.hT y z • x - S.hT x z • y ∈ W := by
    intro z
    rw [hW]
    constructor <;> simp [map_sub, hxx, hyy, hxy, hyx]
  have hind : LinearIndependent D.host.E ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (S.hT x) hab
    have h2 := congrArg (S.hT y) hab
    simp [hxx, hyy, hxy, hyx] at h1 h2
    exact ⟨h2, h1⟩
  have hrk : 2 + Module.finrank D.host.E W = S.rank := by
    have := GlobalTheory.WittLow.finrank_orth S.herm S.nondeg ![x, y] hind
    rw [S.rank_eq] at this
    exact this

  have hrad : ∀ v : W, (∀ w : W, S.hT w v = 0) → v = 0 := by
    intro v hv
    have hv' := (hW v).1 v.2
    apply Subtype.ext
    apply S.nondeg.2 (v : S.V)
    intro z
    have e : z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y := by abel
    have h0 := hv ⟨_, hdec z⟩
    rw [e, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, hv'.1, hv'.2, h0]
    simp
  let h' : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E := S.hT.domRestrict₁₂ W W
  have hs' : h'.IsSymm := ⟨fun a b => S.herm.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun a ha => hrad a fun b => by
    rw [← S.herm.eq]; exact (congrArg _ (ha b)).trans (map_zero _), fun a ha => hrad a ha⟩
  let Λ' : Submodule (𝓞 D.host.E) S.V := Λ.comap ((S.frame.equivFun : S.V →ₗ[D.host.E] (Fin S.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hΛ'm : ∀ z, z ∈ Λ' ↔ GlobalTheory.SqStepK.InLat S Λ z := fun z => Iff.rfl
  have hΛ'lat : Submodule.IsLattice D.host.E Λ' := GlobalTheory.ColRows.isLattice_comap_equiv S.frame.equivFun Λ hΛ.1
  have hΛ'd : ∀ z, z ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT w z := by
    intro z
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, hΛ.2]
    constructor
    · intro h w hw
      obtain ⟨b, hb⟩ := h _ hw
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
    · intro h a ha
      obtain ⟨b, hb⟩ := h (S.frame.equivFun.symm a) (by rw [hΛ'm, GlobalTheory.SqStepK.InLat, LinearEquiv.apply_symm_apply]; exact ha)
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
  let L0 : Submodule (𝓞 D.host.E) W := Λ'.comap (W.subtype.restrictScalars (𝓞 D.host.E))
  have hL0m : ∀ u : W, u ∈ L0 ↔ (u : S.V) ∈ Λ' := fun u => Iff.rfl
  have hL0lat : Submodule.IsLattice D.host.E L0 := GlobalTheory.isLattice_comap_subtype_ringOfIntegers Λ' hΛ'lat W
  have hwz : ∀ z, z ∈ Λ' → z - S.hT y z • x - S.hT x z • y ∈ Λ' := by
    intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z ((hΛ'm z).1 hz)
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, map_sub, map_sub]
    exact Λ.sub_mem (Λ.sub_mem hz hs1) hr1
  have hL0d : ∀ u : W, u ∈ L0 ↔ ∀ u' ∈ L0, ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT u' u := by
    intro u
    have hu := (hW u).1 u.2
    rw [hL0m, hΛ'd]
    constructor
    · intro h u' hu'
      exact h _ hu'
    · intro h z hz
      obtain ⟨b, hb⟩ := h ⟨_, hdec z⟩ (hwz z hz)
      refine ⟨b, ?_⟩
      rw [hb]
      simp [map_sub, hu.1, hu.2]
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L0 := by
    ext v
    rw [GlobalTheory.WittLow.mem_dual, hL0d]
    refine forall₂_congr fun u' _ => ?_
    rw [Submodule.mem_one]
    rfl

  let S₁ : HSp D :=
    { V := W, hT := h', herm := hs', nondeg := hnd', rank := Module.finrank D.host.E W, rank_eq := rfl,
      frame := Module.finBasis D.host.E W, sig := s, L0 := L0, standardTuple_isLattice := hL0lat, baseLattice_isUnimodular := hun }
  let e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) ≃ₗ[D.host.E] W := (Module.finBasis D.host.E W).equivFun.symm
  let Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E) :=
    L0.comap ((e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) →ₗ[D.host.E] W).restrictScalars (𝓞 D.host.E))
  have hΛ₁m : ∀ v, v ∈ Λ₁ ↔ e₁ v ∈ L0 := fun v => Iff.rfl
  have hΛ₁lat : Submodule.IsLattice D.host.E Λ₁ := GlobalTheory.ColRows.isLattice_comap_equiv e₁ L0 hL0lat
  have hin : ∀ u : W, GlobalTheory.SqStepK.InLat S₁ Λ₁ u ↔ GlobalTheory.SqStepK.InLat S Λ (W.subtype u) := by
    intro u
    change (Module.finBasis D.host.E W).equivFun u ∈ Λ₁ ↔ _
    rw [hΛ₁m]
    change (Module.finBasis D.host.E W).equivFun.symm ((Module.finBasis D.host.E W).equivFun u) ∈ L0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hL0m, hΛ'm]
    rfl
  refine ⟨S₁, Λ₁, W.subtype, ⟨?_, fun _ _ => rfl, hxx, hyy, hyx, fun u => ⟨((hW u).1 u.2).1, ((hW u).1 u.2).2⟩, hin, ?_⟩, ⟨hΛ₁lat, ?_⟩, rfl⟩
  · change S.rank = Module.finrank D.host.E W + 2
    omega
  · intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z hz
    refine ⟨S.hT y z, S.hT x z, ⟨_, hdec z⟩, hs1, hr1, (hin _).2 (hwz z hz), ?_⟩
    change z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y
    abel
  · intro v
    simp only [gram_sum]
    rw [hΛ₁m, hL0d]
    constructor
    · intro h a ha
      exact h _ ha
    · intro h u' hu'
      have := h (e₁.symm u') (by rw [hΛ₁m, LinearEquiv.apply_symm_apply]; exact hu')
      obtain ⟨b, hb⟩ := this
      refine ⟨b, ?_⟩
      rw [hb]
      change S.hT (e₁ (e₁.symm u') : S.V) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory.PlaneCompl
end
end

section

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem delta_ne_zero (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem area_pos (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [GlobalTheory.MomDict.area_lamOf D cc δ h.1.1]
  have h1 : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.1.1)
  have h2 := Complex.normSq_pos.2 (delta_ne_zero h)
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem xiR_pos (D : D7) : 0 < Formalism.L2.Pj.xiR D := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [hxi]
  have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem normSq_scale (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    Complex.normSq (δ * embT D τ r) = 2 * Formalism.L2.Pj.xiR D * area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hcj : embT D τ (D.host.conj r) = starRingEnd ℂ (embT D τ r) := by
    have := D.host.isCMField_hostE
    have h : NumberField.IsCMField.complexConj D.host.E r = D.host.conj r := by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [← h, NumberField.IsCMField.complexEmbedding_complexConj]
  have h1 := congrArg (embT D τ) h
  rw [map_mul, map_mul, hcj, Complex.mul_conj, map_natCast, map_natCast] at h1
  have h2 : Complex.normSq (embT D τ r) * (Ideal.absNorm D.host.ccK : ℝ) = (Ideal.absNorm cc : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.MomDict.area_lamOf D cc δ hc, hxi, map_mul, ← h2]
  have h3 : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have h4 : Real.sqrt D.host.d ≠ 0 := by linarith
  field_simp

theorem IsScale.ne_zero (hc : cc ≠ ⊥) (h : IsScale D cc r) : r ≠ 0 := by
  rintro rfl
  have h1 : ((Ideal.absNorm cc : ℕ) : D.host.E) = 0 := by rw [← h]; simp
  exact hc (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem norm_period_sq (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    ‖period D δ r τ‖ ^ 2 = area (lamOf D cc δ) / Real.pi := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [period, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, normSq_scale hc h, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  field_simp

theorem Hf_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (Z X : VC D a d) :
    Hf D (tor0 D cc δ) (fun τ i j => δ * embT D τ r * Z τ i j) (fun τ i j => δ * embT D τ r * X τ i j) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
  have hA : ((area (lamOf D cc δ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (area_pos hc).ne'
  have hL : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  rw [Hf, hL, div_eq_iff hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : δ * embT D τ r * starRingEnd ℂ (δ * embT D τ r) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, normSq_scale hc.1.1 h]; push_cast; ring
  rw [map_mul (starRingEnd ℂ) (δ * embT D τ r)]
  linear_combination (Z τ i j * starRingEnd ℂ (X τ i j)) * h1

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_iff (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) (G : VC D S.rank T.rank → ℂ) (f : WO S T → ℂ) :
    Reads ψ θ rfl rfl cc δ r G f ↔ IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ 1 1 w *
        (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) (GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ w : WO S T, GlobalTheory.FockPos.zCo θ 1 1 w = fun τ => compAt θ τ w := fun w => by
    funext τ
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  have e1 : coordY θ rfl rfl δ r w = fun τ i j => δ * embT D τ r * compAt θ τ w i j := rfl
  have e2 := Hf_scale hc h (fun τ i j => compAt θ τ w i j) (fun τ i j => compAt θ τ w i j)
  rw [e1, e2, GlobalTheory.FockPos.gaussO, hz]
  simp only [Complex.mul_conj']
  congr! 3
  push_cast
  ring

variable {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {G : VC D a d → ℂ} {f f' : WO S T → ℂ}

theorem Reads.smul (h : Reads ψ θ hS hT cc δ r G f) (c : ℂ) : Reads ψ θ hS hT cc δ r (c • G) (c • f) :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem c h.1, fun w hw => by
    rw [Pi.smul_apply, Pi.smul_apply, h.2 w hw, smul_eq_mul, smul_eq_mul]; ring⟩

theorem Reads.add {G' : VC D a d → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f') :
    Reads ψ θ hS hT cc δ r (G + G') (f + f') :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem h.1 h'.1, fun w hw => by
    rw [Pi.add_apply, Pi.add_apply, h.2 w hw, h'.2 w hw]; ring⟩

theorem Reads.unique (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G f') : f = f' :=
  sub_eq_zero.1 (GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real ((GlobalTheory.FinWeilO.thetaSub ψ S T).sub_mem h.1 h'.1)
    fun w hw => by rw [Pi.sub_apply, h.2 w hw, h'.2 w hw, sub_self])

end GlobalTheory.NormExact
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.QuotMonic

variable {M : Type} [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M)

def stabAlg : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ M', f x ∈ M' ∧ (x ∈ K → f x ∈ K)}
  mul_mem' := fun {f g} hf hg x hx => ⟨(hf _ (hg x hx).1).1, fun hk => (hf _ (hg x hx).1).2 ((hg x hx).2 hk)⟩
  add_mem' := fun {f g} hf hg x hx => ⟨M'.add_mem (hf x hx).1 (hg x hx).1, fun hk => K.add_mem ((hf x hx).2 hk) ((hg x hx).2 hk)⟩
  algebraMap_mem' := fun r x hx => ⟨by simpa [Module.algebraMap_end_apply] using M'.smul_mem r hx,
    fun hk => by simpa [Module.algebraMap_end_apply] using K.smul_mem r hk⟩

variable {M' K}

def restrictQ (f : stabAlg M' K) : Module.End ℂ (M' ⧸ K.comap M'.subtype) :=
  (K.comap M'.subtype).mapQ (K.comap M'.subtype) (f.1.restrict fun x hx => (f.2 x hx).1) fun x hx => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.restrict_apply] at hx ⊢
    exact (f.2 x x.2).2 hx


variable (M' K) in
def quotRep : stabAlg M' K →ₐ[ℂ] Module.End ℂ (M' ⧸ K.comap M'.subtype) where
  toFun := restrictQ
  map_one' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_mul' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_zero' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_add' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  commutes' r := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl


variable (M' K) in
def quotIncl : (M' ⧸ K.comap M'.subtype) →ₗ[ℂ] M ⧸ K :=
  (K.comap M'.subtype).liftQ (K.mkQ ∘ₗ M'.subtype) fun x hx => by simpa using hx

theorem quotIncl_injective : Function.Injective (quotIncl M' K) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => by simpa using hx

theorem quotIncl_quotRep (b : stabAlg M' K) (v : M) (hv : v ∈ M') :
    quotIncl M' K (quotRep M' K b (Submodule.Quotient.mk ⟨v, hv⟩)) = K.mkQ (b.1 v) := rfl

end GlobalTheory.LeviHC.QuotMonic

namespace GlobalTheory.LeviHC.QuotMonic


open Algebra in
theorem monicFactorFiniteMod_of (H : MonicFactorFinite) : MonicFactorFiniteMod := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hM hK hc v hv hfin
  classical
  set S := stabAlg M' K
  have hpB : ∀ u, p u ∈ S := fun u x hx => ⟨(hM u x hx).2.1, fun hk => (hK u x hk).1⟩
  have hqB : ∀ u, q u ∈ S := fun u x hx => ⟨(hM u x hx).2.2, fun hk => (hK u x hk).2⟩
  have hcB : ∀ u, c u ∈ S := fun u x hx => ⟨(hM u x hx).1, fun hk =>
    (K.sub_mem_iff_left (hK u _ (hK u x hk).2).1).1 (hc u x hx)⟩
  let pS : ℂ → S := fun u => ⟨p u, hpB u⟩
  let qS : ℂ → S := fun u => ⟨q u, hqB u⟩
  let cS : ℂ → S := fun u => ⟨c u, hcB u⟩
  let ρ := quotRep M' K

  have poly : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, r u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
      ∃ (d : ℕ) (a : ℕ → Module.End ℂ (M' ⧸ K.comap M'.subtype)), a d = 1 ∧
        ∀ u, ρ ⟨r u, hr u⟩ = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    intro r hr ⟨d, a, ha1, hra⟩
    have haB : ∀ i < d + 1, a i ∈ S := fun i hi =>
      (Subalgebra.mem_toSubmodule S).1 ((Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hr u))
        (coeff_mem_span hra hi))
    let a' : ℕ → S := fun i => if h : a i ∈ S then ⟨a i, h⟩ else 0
    have ha' : ∀ i < d + 1, (a' i).1 = a i := fun i hi => by simp [a', haB i hi]
    refine ⟨d, fun i => ρ (a' i), ?_, fun u => ?_⟩
    · have : a' d = 1 := Subtype.ext ((ha' d (Nat.lt_succ_self d)).trans ha1)
      show ρ (a' d) = 1
      rw [this, map_one]
    · have e : (⟨r u, hr u⟩ : S) = ∑ i ∈ Finset.range (d + 1), u ^ i • a' i := by
        apply Subtype.ext
        change r u = _
        rw [hra u]

        rw [show ((∑ i ∈ Finset.range (d + 1), u ^ i • a' i : S) : Module.End ℂ M) = ∑ i ∈ Finset.range (d + 1), u ^ i • (a' i : Module.End ℂ M) from
        map_sum S.val.toLinearMap (fun i => u ^ i • a' i) _ |>.trans (Finset.sum_congr rfl fun i _ => map_smul S.val.toLinearMap _ _)]
        exact Finset.sum_congr rfl fun i hi => by rw [ha' i (Finset.mem_range.1 hi)]

      rw [e, map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hcS : ∀ u, ρ (cS u) = ρ (pS u) * ρ (qS u) := fun u => by
    rw [← map_mul]
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    obtain ⟨x, hx⟩ := x
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    simpa using hc u x hx

  have hval : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (adjoin ℂ (Set.range fun u => (⟨r u, hr u⟩ : S))).map S.val = adjoin ℂ (Set.range r) := by
    intro r hr
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hrho : ∀ (s : ℂ → S), adjoin ℂ (Set.range fun u => ρ (s u)) = (adjoin ℂ (Set.range s)).map ρ := by
    intro s
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  set v' : M' ⧸ K.comap M'.subtype := Submodule.Quotient.mk ⟨v, hv⟩
  have hj := quotIncl_injective (M' := M') (K := K)
  have key := H (M' ⧸ K.comap M'.subtype) (fun u => ρ (pS u)) (fun u => ρ (qS u)) (poly p hpB hp) (poly q hqB hq)
    (fun u u' => (show Commute (pS u) (pS u') from Subtype.ext (hpp u u').eq).map ρ)
    (fun u u' => (show Commute (qS u) (qS u') from Subtype.ext (hqq u u').eq).map ρ)
    (fun u u' => (show Commute (pS u) (qS u') from Subtype.ext (hpq u u').eq).map ρ) v' ?_
  ·
    haveI := key
    unfold FinMod
    refine Submodule.finiteDimensional_of_le (?_ : _ ≤ Submodule.map (quotIncl M' K)
      (Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u)), y = a v'}))
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← hval p hpB] at ha
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
    refine Submodule.subset_span ⟨ρ b v', ⟨ρ b, ?_, rfl⟩, quotIncl_quotRep b v hv⟩
    rw [hrho pS]
    exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)}) := hfin
    set T := Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u) * ρ (qS u)), y = a v'}
    have hle : T.map (quotIncl M' K) ≤
        Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have e : (fun u => ρ (pS u) * ρ (qS u)) = fun u => ρ (cS u) := funext fun u => (hcS u).symm
      rw [e, hrho cS] at ha
      obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
      refine Submodule.subset_span ⟨b.1, ?_, quotIncl_quotRep b v hv⟩
      rw [← hval c hcB]
      exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hj T).symm

end GlobalTheory.LeviHC.QuotMonic
end
end
