module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_of_sub {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (hab : Valued.v (a - b) < 1) : HasRes P b c := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, hr, ?_⟩
  have e : b - algebraMap E _ (algebraMap (𝓞 E) E r) = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (a - b) := by ring
  rw [e]
  exact Valuation.map_sub_lt _ hv hab

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (h' : HasRes P b c) : Valued.v (a - b) < 1 := by
  obtain ⟨r, hr, hv⟩ := h
  obtain ⟨r', hr', hv'⟩ := h'
  have hmem : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 (hr.trans hr'.symm)
  have e : a - b = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (b - algebraMap E _ (algebraMap (𝓞 E) E r')) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - r')) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sub_lt _ hv hv') ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hmem

theorem val_sub_lt_of_hatL {n : ℕ} (a b : Matrix (Fin n) (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (i : Fin n)
    {N : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y ∈ N, Valued.v (adAt F P ((a *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i -
      (b *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i)) < 1)
    {z : Fin n → AfE F E} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) N) :
    Valued.v (adAt F P ((a *ᵥ z) i - (b *ᵥ z) i)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact h v hv
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (a *ᵥ (x + y)) i - (b *ᵥ (x + y)) i = ((a *ᵥ x) i - (b *ᵥ x) i) + ((a *ᵥ y) i - (b *ᵥ y) i) := by
      simp only [Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add (adAt F P)]
    exact Valuation.map_add_lt _ hx hy
  | smul c x _ hx =>
    have e0 : c • x = (c : AfE F E) • x := rfl
    have e : (a *ᵥ (c • x)) i - (b *ᵥ (c • x)) i = (c : AfE F E) * ((a *ᵥ x) i - (b *ᵥ x) i) := by
      rw [e0, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [e, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 c.2 P)) hx

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem pullV_mul_stab (g g' h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x =
      ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem pullV_eq_of_mul (g h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV h x = ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
                 ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem val_sub_pullV_lt {g g' h : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (hh : IsPtOf hc h q) {P : HeightOneSpectrum (𝓞 E)} (i : Fin n)
    (hP : ∀ y ∈ p.deco.1.N, Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV g y i - GlobalTheory.Mem.Col2.pullV g' y i)) < 1)
    {x : Sp E n} (hx : x ∈ q.deco.1.N) :
    Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV h x i - GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x i)) < 1 := by
  have hu : GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hh.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hz : (g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
    refine (hg.lat _).2 ?_
    rwa [← pullV_eq_of_mul]
  have := val_sub_lt_of_hatL _ _ P i (fun y hy => hP y hy) hz
  rwa [← pullV_eq_of_mul, ← pullV_mul_stab] at this

theorem isPtOf_mul_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (g g' h : GL (Fin n) (AfE F E)) (p q : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc g' p → IsPtOf hc h q → IsPtOf hc (h * (g⁻¹ * g')) q := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g g' h p q hg hg' hh
  refine ⟨mul_mem hh.uni (mul_mem (inv_mem hg.uni) hg'.uni), fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_,
    fun P i j => ?_⟩
  · have e : (((h * (g⁻¹ * g'))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
        ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e, hh.lat x, ← hg'.lat, hg.lat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · refine hasRes_of_sub (hh.f P x hx i hi) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.f P y hy i hi) (hg'.f P y hy i hi)
  · refine hasRes_of_sub (hh.be w x hx i) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.be w y hy i) (hg'.be w y hy i)
  · have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) =
        (g' : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) := by
      ext a b
      simp only [Matrix.map_apply]
      rw [hg.fr, hg'.fr]
    have hs : (((g⁻¹ * g' : GL (Fin n) (AfE F E))) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, ← hgg, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have e : adAt F P.1 (((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        ((((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P.1)) i j := rfl
    rw [e, Units.val_mul, Matrix.map_mul, hs, mul_one, Matrix.map_apply]
    exact hh.fr P i j

end GlobalTheory.Mem.Col2.PtStab

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
        let L := p.deco.1.N
        let W := Submodule.span E (L : Set (Sp E n))
        change W = ⊤
        by_contra hW
        let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
        let f : Sp E n →ₗ[E] Module.Dual E W :=
          (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
        have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt hW
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
        have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
        have hsmul (a : E) : a • e x ∈ L := by
          rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : hStd E n (e x) y = 0 :=
            congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let i : E →ₗ[𝓞 E] L :=
          ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
        let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
        let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        hspan
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ResidueLocPlace

theorem norm_le_one_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) (y : O) :
    ‖f y‖ ≤ 1 := by
  have hy : IsIntegral ℤ_[p] y := Algebra.IsIntegral.isIntegral y
  let v := NormedField.valuation (K := Qbar p)
  have hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    have : ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends p]; exact PadicInt.norm_le_one z
    exact_mod_cast this
  let φ : ℤ_[p] →+* v.integer := ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem
  have hI : IsIntegral v.integer (f y) := by
    refine IsIntegral.map_of_comp_eq φ f ?_ hy
    ext z
    simp only [RingHom.comp_apply, hf]
    rfl
  have h := (Valuation.integer.integers v).mem_of_integral hI
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_lt_one_of_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) {y : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) : ‖f y‖ < 1 := by
  have hle : ∀ z : O, ‖f z‖ ≤ 1 := norm_le_one_of_finite f hf
  have hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹ := by
    have h1 := hf (p : ℤ_[p])
    rw [map_natCast] at h1
    rw [h1, PadicAlgCl.norm_extends p]
    simp [Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : (p : O) ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hfp
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := (Fact.out : p.Prime).pos; positivity
    linarith
  have hpu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hu, hfp] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]; exact zero_lt_one
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  obtain ⟨k, w, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have he : e ≠ 0 := by
    rintro rfl; apply hpu; rw [hpe, pow_zero, mul_one]; exact u.isUnit
  have hk : k ≠ 0 := by
    rintro rfl
    rw [hyk, pow_zero, mul_one] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit
  have hu1 : ‖f (u : O)‖ = 1 := by
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h6 := hle (u : O)
    have h5 : 0 ≤ ‖f (u : O)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e := by
    rw [hpe, hyk]; ring
  have hn := congrArg (fun z => ‖f z‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn
  have hw := hle (w : O)
  have hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [hn]
    calc ((p : ℝ)⁻¹) ^ k * ‖f (w : O)‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := mul_one _
  have hB : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) hp1 hk
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)

end GlobalTheory.ResidueLocPlace

namespace GlobalTheory.ResidueLocPlace

theorem exists_residue_lift {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (hp : p.Prime)
    (hq : q.Prime) (ι : Qbar p ≃+* ℂ) (B : ValuationSubring ℂ) (hB : ∀ z, z ∈ B ↔ ‖ι.symm z‖ ≤ 1)
    (κB : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar p)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[q] O]
    [Module.Finite ℤ_[q] O] (iq : FractionRing O →+* Qbar q)
    (iq_alg : ∀ z : ℤ_[q], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[q] O z)) =
      algebraMap ℚ_[q] (Qbar q) (z : ℚ_[q])) :
    ∃ κ : IsLocalRing.ResidueField O →+* Formalism.CyclotomicNorms.Fbar q, ∀ y : O,
      ∃ hy : (((qCast h ι).toRingHom.comp iq).comp (algebraMap O (FractionRing O))) y ∈ B,
        fbCast h hp hq (κB (IsLocalRing.residue B ⟨_, hy⟩)) = κ (IsLocalRing.residue O y) := by
  subst h
  let f : O →+* Qbar p := iq.comp (algebraMap O (FractionRing O))
  have hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := iq_alg
  have hmem : ∀ y, ι (f y) ∈ B := fun y =>
    (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)
  let g : O →+* B := (ι.toRingHom.comp f).codRestrict B.toSubring hmem
  let F : O →+* Formalism.CyclotomicNorms.Fbar p := κB.toRingHom.comp ((IsLocalRing.residue B).comp g)
  have hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0 := by
    intro a ha
    have hlt := norm_lt_one_of_mem_maximalIdeal f hf ha
    have hg : g a ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have h2 : ι (f a) = ((g a : B) : ℂ) := rfl
      rw [← h2] at h1
      have h3 := congrArg (fun z => ‖ι.symm z‖) h1
      simp only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3
      have h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1 := (hB _).1 (((u⁻¹ : Bˣ) : B)).2
      have h5 : 0 ≤ ‖f a‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    show κB (IsLocalRing.residue B (g a)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩

end GlobalTheory.ResidueLocPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselDatum_adelicVector_decomposition : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧ ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) + ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  first | exact @GlobalTheory.BesselDecomp.decomp | exact GlobalTheory.BesselDecomp.decomp | (intros; apply GlobalTheory.BesselDecomp.decomp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  first | exact @GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | exact GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | (intros; apply GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matrixModPlace_basisChange_eq_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_basisChange | exact GlobalTheory.Mem.SymFrame.isMatIn_basisChange | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_basisChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_e0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg b j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 b).1
    · exact ((X.weightVectorsIntegral _).2.2 b).2.2.1
  refine wInt_of_zmod X kv.1 hg ?_
  have hb := b.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]; exact (X.gramIntegral _ _).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2, if_neg (by omega), sub_zero]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]; exact (X.formsAtZero.2 b).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]
    have h := (X.gramIntegral b ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩).2.2
    by_cases e : j.1 = 2 * D.R.rS + D.R.k - b.1
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by simp only; omega))] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (by have := congrArg Fin.val h'; simp only at this; omega))] at h
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end
