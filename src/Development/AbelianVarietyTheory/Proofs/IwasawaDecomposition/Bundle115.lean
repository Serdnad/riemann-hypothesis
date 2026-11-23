module

public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.IrreducibleCharpolyInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.GaloisClause
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.RootPowCard
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidue

open Formalism.L2.DIV HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := (x : Valued.integer (v.adicCompletion F)))

theorem integral_image (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (b : 𝓞 E) :
    φ ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ v.adicCompletionIntegers F := by
  have h0 : IsIntegral ℤ b := Algebra.IsIntegral.isIntegral b
  let ψ : 𝓞 E →+* v.adicCompletion F :=
    φ.comp ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E))
  have h1 : IsIntegral (v.adicCompletionIntegers F) (ψ b) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ψ (RingHom.ext_int _ _) h0
  exact (adicCompletionIntegers.integers F v).mem_of_integral h1

theorem comp_mem (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) (s : Formalism.L2.Herm.intAf F E) :
    φ (prV (E := E) v s.1) ∈ v.adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      Subring.comap (φ.comp (prV (E := E) v)) (v.adicCompletionIntegers F).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show φ (prV (E := E) v ((b : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, ← hb0]
      exact integral_image v φ b0
    · show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] (y : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, hφ]
      exact y.2 v
  exact hle s.2

theorem mem_idS_of_resS_eq_zero (w : HeightOneSpectrum (𝓞 E)) {t : Formalism.L2.Herm.intAf F E}
    (h : resS F w t = 0) : t ∈ idS F w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold resS at h
  rw [RingHom.comp_apply] at h
  exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 h

theorem exists_residue_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (p : 𝓞 E),
    (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) →
    Valued.v (φ (inclE (F := F) (v.adicCompletion F) (p : E))) < 1 →
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → p ∈ P.asIdeal → P = w) →
    ∃ (ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)
      (e : (𝓞 E ⧸ w.asIdeal) ≃+* Formalism.L2.Forms.kv F v),
      (∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1)) ∧
      ∀ s, IsLocalRing.residue _ (ρ s) = e (Formalism.L2.DIV.resS F w s) := by
  intro F E _ _ _ _ _ v w φ p hφ hp hw
  let ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F :=
    (φ.comp ((prV (E := E) v).comp (Formalism.L2.Herm.intAf F E).subtype)).codRestrict
      (v.adicCompletionIntegers F) (fun s => comp_mem v φ hφ s)
  have hρ : ∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1) :=
    fun _ => rfl
  let r : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Forms.kv F v := (IsLocalRing.residue _).comp ρ
  let g : 𝓞 E →+* Formalism.L2.Forms.kv F v := r.comp (oToS F E)
  have hg0 : ∀ b : 𝓞 E, Valued.v (φ (inclE (F := F) (v.adicCompletion F) (b : E))) < 1 → g b = 0 := by
    intro b hb
    show IsLocalRing.residue _ (ρ (oToS F E b)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, hρ]
    exact hb
  have hv : ∀ x ∈ v.asIdeal, g (algebraMap (𝓞 F) (𝓞 E) x) = 0 := by
    intro x hx
    refine hg0 _ ?_
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F x) := by
      show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have e2 : inclE (F := F) (v.adicCompletion F) (algebraMap F E (algebraMap (𝓞 F) F x)) =
        (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) := by
      show (algebraMap F E (algebraMap (𝓞 F) F x)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [e1, e2, hφ]
    refine lt_of_eq_of_lt (valuedAdicCompletion_eq_valuation' v _) ?_
    exact (valuation_lt_one_iff_mem v x).2 hx
  have hne : RingHom.ker g ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 F) (𝓞 E) x ∈ RingHom.ker g := hv x hx
    rw [hb, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (h1.trans (map_zero _).symm))
  let P : HeightOneSpectrum (𝓞 E) := ⟨RingHom.ker g, RingHom.ker_isPrime g, hne⟩
  have hunder : P.under (𝓞 F) = v := by
    refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top ?_).symm
    intro x hx
    exact hv x hx
  have hk : RingHom.ker g = w.asIdeal := congrArg HeightOneSpectrum.asIdeal (hw P hunder (hg0 p hp))
  have hz : idS F w.asIdeal ≤ RingHom.ker r := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [← hk] at ha
    exact ha
  have hfac : ∀ s (b : 𝓞 E), resS F w s = Ideal.Quotient.mk w.asIdeal b → r s = g b := by
    intro s b h
    have h0 : resS F w (s - oToS F E b) = 0 := by rw [map_sub, resS_oToS, h, sub_self]
    have h1 : r (s - oToS F E b) = 0 := hz (mem_idS_of_resS_eq_zero w h0)
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  have hs : Function.Surjective g := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    let s : Formalism.L2.Herm.intAf F E := ⟨(1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F),
      Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd v _ a.2⟩, rfl⟩)⟩
    have hρs : ρ s = a := Subtype.ext (by
      rw [hρ]
      show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F))) = _
      rw [Formalism.UG.P.afsplit_prV_tmul, Formalism.UG.P.afsplitI_self, hφ])
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
    refine ⟨b, (hfac s b hb.symm).symm.trans ?_⟩
    show IsLocalRing.residue _ (ρ s) = _
    rw [hρs]
  refine ⟨ρ, (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs), hρ, ?_⟩
  intro s
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  rw [← hb]
  exact hfac s b hb.symm

end GlobalTheory.SplitResidue
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CuspTwist

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES PI.GreenLabelMapW IntermediateField

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem algebraMap_det_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (γ : Matrix ι ι K).charpoly) {z : AlgebraicClosure K}
    (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) :
    algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) =
      z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmin : (γ : Matrix ι ι K).charpoly = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hdeg : (minpoly K z).natDegree = Fintype.card ι := by
    rw [← hmin, Matrix.charpoly_natDegree_eq_dim]
  let pb := IntermediateField.adjoin.powerBasis hint
  have hnorm : Algebra.norm K pb.gen = Matrix.det (γ : Matrix ι ι K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, Matrix.det_eq_sign_charpoly_coeff, hmin]
    have h1 : pb.dim = Fintype.card ι := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have h2 : pb.gen = IntermediateField.AdjoinSimple.gen K z := IntermediateField.adjoin.powerBasis_gen hint
    rw [h1, h2, IntermediateField.minpoly_gen]
  haveI : FiniteDimensional K K⟮z⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮z⟯ := Module.finite_of_finite K
  have hfr : Module.finrank K K⟮z⟯ = Fintype.card ι := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have h3 := FiniteField.algebraMap_norm_eq_pow_sum (K := K) (L := K⟮z⟯) (x := pb.gen)
  rw [hnorm, hfr, Nat.card_eq_fintype_card] at h3
  have h5 : ((pb.gen ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i : K⟮z⟯) :
      AlgebraicClosure K) = z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
    rw [IntermediateField.coe_pow, IntermediateField.adjoin.powerBasis_gen hint,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← h5, ← h3]
  rfl

theorem gen_one_pow_eq_det (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 1 ≤ Fintype.card ι) (γ : GL ι K) (hγ : Irreducible (γ : Matrix ι ι K).charpoly)
    {z : AlgebraicClosure K} (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) {m : ℕ}
    (hm : Cv.gen (Fintype.card ι) ^ m = z) :
    Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) := by
  have hn := Cv.gen_norm 1 (Fintype.card ι) le_rfl hι
  rw [one_mul, pow_one] at hn
  rw [algebraMap_det_eq_pow γ hγ hz, ← hn, ← hm, ← pow_mul, ← pow_mul,
    Nat.geomSum_eq Fintype.one_lt_card, mul_comm]

theorem twist_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K) (hd : 1 ≤ d) (hx : x ≠ 0) (hs : Simple τ)
    (hc : IsCuspidal K τ) (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ (γ : GL (Fin d) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) =
        Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) :
    rootsBar K (greenLab Cv d τ') =
      (rootsBar K (greenLab Cv d τ)).map (· * algebraMap K (AlgebraicClosure K) x) := by
  set xb := algebraMap K (AlgebraicClosure K) x with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb]; exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).2 hx
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg' : (greenLab Cv d τ).natDegree = d := by rw [hdeg, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg']; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : AlgebraicClosure K),
      σ y * xb = σ (y * xb) := fun σ y => by rw [map_mul, hxb, AlgEquiv.commutes]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ * xb = r₂ * xb → r₁ = r₂ :=
    fun _ _ _ _ h => mul_right_cancel₀ hxb0 h
  have hint : IsIntegral K (w * xb) := Algebra.IsIntegral.isIntegral _
  have hxq : ∀ i : ℕ, xb ^ (Fintype.card K ^ i) = xb := fun i => by
    rw [hxb, ← map_pow, FiniteField.pow_card_pow]
  have hlab : HasCuspLabel Cv τ' (minpoly K (w * xb)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w * xb)
      rw [h, aeval_X] at h0
      exact mul_ne_zero (root_ne_zero hm hi hX hw) hxb0 h0
    · rw [natDegree_minpoly_eq hm hi hw (fun y => y * xb) hf hinj, hdeg]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun y => y * xb) hf y).1 hy
      have hι : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      rw [htr γ m (gen_one_pow_eq_det Cv hι γ hγ hz hm'), hval r hr γ hγ z hz m hm',
        mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : Cv.ι xb ^ (m * Fintype.card K ^ i) = Cv.ι xb ^ m := by
        rw [mul_comm, pow_mul, ← map_pow, hxq i]
      rw [map_mul, mul_pow, e, mul_comm]
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun y => y * xb) hf hinj

theorem exists_labelMap_twist_cuspLabel :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K),
      Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C,
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
          ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ →
            Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  intro K _ _ _ Cv hC
  let O : LabelMap K Cv :=
    { lab := greenLab Cv
      lab_iso := greenLab_iso Cv
      lab_spec := fun d τ hd hs hc => by
        obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec Cv hC hd hs hc
        exact ⟨h1, h2, h3, by rw [h4, Fintype.card_fin]⟩
      lab_inj := fun d τ τ' hd hs hc hs' hc' h =>
        (hC d hd).2.2 τ τ' (greenLab Cv d τ) hs hc hs' hc' (greenLab_spec Cv hC hd hs hc)
          (by rw [h]; exact greenLab_spec Cv hC hd hs' hc')
      lab_one := fun τ x hs hx htr => greenLab_one Cv hC τ x hs hx htr }
  refine ⟨O, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause Cv hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause Cv hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' x hd hx hs hc hs' hc' htr
    exact twist_clause Cv hC d τ τ' x hd hx hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec Cv hC hd hs hc

end GlobalTheory.CuspTwist
end
end

section

open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
end
