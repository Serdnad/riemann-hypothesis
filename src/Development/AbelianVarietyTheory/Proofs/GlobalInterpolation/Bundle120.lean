module

import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.Bundle001
public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle118
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
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle119
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem absNorm_eq_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {w : Ideal (𝓞 E)} (hwp : w.IsPrime) (hw : ((p : ℕ) : 𝓞 E) ∈ w) :
    Ideal.absNorm w = p := by
  apply GlobalTheory.LevDesc.absNorm_eq_of_split <;> assumption

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← absNorm_eq_of_ncard hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TameVal

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  apply GlobalTheory.GalToHecke.locK_eq_of_tame <;> assumption

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  apply GlobalTheory.GalToHecke.exists_approx <;> assumption

theorem locK_mem (χ : HChar L) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (htame : ∀ v, χ.TameAt v) (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : χ.locK P x ∈ G := by
  classical
  have hpr : χ.ProductRule := GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩
  have key : ∀ (a : 𝓞 L) (ha : (a : L) ≠ 0), χ.locK P (Units.mk0 (a : L) ha) ∈ G := by
    intro a ha
    have ha' : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1)
      (fun v => by split_ifs; exacts [ha', one_ne_zero])
    have hP := hy P (Finset.mem_insert_self _ _)
    simp only [if_true] at hP
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hP
      have hpos : 0 < P.valuation L (a : L) := zero_lt_iff.2 (by simpa using ha')
      have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
      rw [one_mul] at this
      exact absurd hP (not_le.2 this)
    have e1 : χ.locK P (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (a : L) ha) :=
      locK_eq_of_tame χ (htame P) _ _ hP
    have e2 : ∏ v ∈ insert P T, χ.locK v (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (y : L) hy0) := by
      refine Finset.prod_eq_single P (fun v hv hne => ?_) (fun h => absurd (Finset.mem_insert_self _ _) h)
      have h1 := hy v hv
      simp only [if_neg hne] at h1
      rw [locK_eq_of_tame χ (htame v) 1 _ (by simpa using h1), map_one]
    have h := hpr (insert P T) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (Units.mk0 (y : L) hy0)
    rw [e2, e1] at h
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ insert P T),
        χ.val v ^ ordF v (Units.mk0 (y : L) hy0)) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 : _ ∈ G := h ▸ G.one_mem
    rw [G.mul_mem_cancel_right hF, G.mul_mem_cancel_left (hinf _)] at h1
    exact h1
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 L) (x : L)
  have hb0 : (b : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have ha0 : (a : L) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab]
    change (a : L) / _ = 0
    rw [h, zero_div]
  have hx : x = Units.mk0 (a : L) ha0 * (Units.mk0 (b : L) hb0)⁻¹ := by
    apply Units.ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0) (G.inv_mem (key b hb0))

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun ha hb => M.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]; exact M.inv_mem ha

theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
  have h2 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_ofNat, div_pow, ← h1]
  field_simp

end GlobalTheory.TameVal
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | exact GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | (intros; apply GlobalTheory.AdelicCharDilate.exists_eq_std_dilate <;> assumption)
end

section

namespace GlobalTheory.UnitPerpObj

theorem unitVectorPerp (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements.UnitVectorPerp D :=
  (GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)

end GlobalTheory.UnitPerpObj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.exists_hermitianForm_descent_coefficientField : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  first | exact @GlobalTheory.Glob.FormDescent.desc | exact GlobalTheory.Glob.FormDescent.desc | (intros; apply GlobalTheory.Glob.FormDescent.desc <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.exists_levelPrimePointModel_realisation : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T), ∃ M : PtModel B.ch i, Nonempty (B.Real i sp M) := by
  first | exact @GlobalTheory.LvT.Built.RealM.exists_real | exact GlobalTheory.LvT.Built.RealM.exists_real | (intros; apply GlobalTheory.LvT.Built.RealM.exists_real <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.unitary_coordinate_algebra_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first | exact @GlobalTheory.PolyRealU.poly_infU | exact GlobalTheory.PolyRealU.poly_infU | (intros; apply GlobalTheory.PolyRealU.poly_infU <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] IsCMField.starRing

theorem _root_.GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  first | exact @GlobalTheory.SelfDualDet.det_eq_norm_mul | exact GlobalTheory.SelfDualDet.det_eq_norm_mul | (intros; apply GlobalTheory.SelfDualDet.det_eq_norm_mul <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add (f := _)]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
end

section

open Formalism.MainNotions

namespace GlobalTheory.Mass

theorem massRatio_all_unramified_cmFields : StandardLattice.SiegelMassRatioCM :=
  Formalism.MainNotions.StandardLattice.standardMassRatio_of_modelMassRatio GlobalTheory.Mass.siegelMassRatio_holds

end GlobalTheory.Mass
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke


theorem _root_.GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  first | exact @GlobalTheory.HalfPeriodValue.halfPeriod_value | exact GlobalTheory.HalfPeriodValue.halfPeriod_value | (intros; apply GlobalTheory.HalfPeriodValue.halfPeriod_value <;> assumption)
end
