module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

end GlobalTheory.JetCalcPf
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.PairFourier
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

theorem _root_.GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  first | exact @GlobalTheory.IwasawaLast.iwasawa_lastRow | exact GlobalTheory.IwasawaLast.iwasawa_lastRow | (intros; apply GlobalTheory.IwasawaLast.iwasawa_lastRow <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k (GlobalTheory.CuspRep.lie E a X φ))) := by
  first | exact @GlobalTheory.CuspRep.KFin.kfin_lie | exact GlobalTheory.CuspRep.KFin.kfin_lie | (intros; apply GlobalTheory.CuspRep.KFin.kfin_lie <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.automorphicForm_GL_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → Continuous φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsAutForm.continuous | exact GlobalTheory.CuspRep.IsAutForm.continuous | (intros; apply GlobalTheory.CuspRep.IsAutForm.continuous <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.mem_zalg_commute_compactRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  first | exact @GlobalTheory.ZalgCpt.zalg_comm_cptRep | exact GlobalTheory.ZalgCpt.zalg_comm_cptRep | (intros; apply GlobalTheory.ZalgCpt.zalg_comm_cptRep <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.chart_unipotent_fderiv_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) := by
  first | exact @GlobalTheory.CuspRep.JointCont.chart_jointCont | exact GlobalTheory.CuspRep.JointCont.chart_jointCont | (intros; apply GlobalTheory.CuspRep.JointCont.chart_jointCont <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  first | (exact @GlobalTheory.Shin.clifford_prime_index) | (exact GlobalTheory.Shin.clifford_prime_index) | (intros; apply GlobalTheory.Shin.clifford_prime_index <;> assumption)
end

section

namespace GlobalTheory.ResidueLift

open IsLocalRing

theorem res_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : GlobalTheory.ZJ.OO l) :
    residue (GlobalTheory.ZJ.OO l) x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.ZH.not_isUnit_OO_iff]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  intro l _ L _ J a b ha hb hab
  let K := PadicAlgCl l
  let O := GlobalTheory.ZJ.OO l
  let a' : J → O := fun j => ⟨a j, (GlobalTheory.ZH.mem_OO_iff _).2 (ha j)⟩
  let b' : J → O := fun j => ⟨b j, (GlobalTheory.ZH.mem_OO_iff _).2 (hb j)⟩
  let As : Subring O := L.toSubalgebra.toSubring.comap O.subtype
  let f : As →+* GlobalTheory.ZJ.kb l := (residue O).comp As.subtype
  let R := f.range
  have key : ∀ (c : J → O) (q : MvPolynomial J As),
      MvPolynomial.aeval (fun j => residue O (c j)) (MvPolynomial.map f.rangeRestrict q) = 0 ↔
      ‖MvPolynomial.eval (fun j => (c j : K)) (MvPolynomial.map (O.subtype.comp As.subtype) q)‖ < 1 := by
    intro c q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval_map]
    have h1 : MvPolynomial.eval₂ ((algebraMap R (GlobalTheory.ZJ.kb l)).comp f.rangeRestrict) (fun j => residue O (c j)) q
        = residue O (MvPolynomial.eval₂ As.subtype c q) := by
      rw [MvPolynomial.eval₂_comp_left]; rfl
    have h2 : MvPolynomial.eval₂ (O.subtype.comp As.subtype) (fun j => (c j : K)) q
        = ((MvPolynomial.eval₂ As.subtype c q : O) : K) :=
      (MvPolynomial.eval₂_comp_left O.subtype As.subtype c q).symm
    rw [h1, h2, res_eq_zero_iff]
  have hII : ∀ p : MvPolynomial J R, MvPolynomial.aeval (fun j => residue O (a' j)) p = 0 →
      MvPolynomial.aeval (fun j => residue O (b' j)) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective f.rangeRestrict f.rangeRestrict_surjective p
    rw [key] at hp ⊢
    refine (hab _ fun n => ?_).1 hp
    rw [MvPolynomial.coeff_map]
    exact ⟨(AddMonoidAlgebra.coeff q n).2, (GlobalTheory.ZH.mem_OO_iff _).1 (((AddMonoidAlgebra.coeff q n : As) : O).2)⟩
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := l)
  obtain ⟨φ, hφR, hφ⟩ := GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' _ GlobalTheory.ZJ.exists_pow_eq_one_kb R J _ _ hII
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl l L φ fun x hx => hφR _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨g, fun j => hg (a' j) (b' j) (hφ j).symm⟩

end GlobalTheory.ResidueLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isCrystallineChern_on_analytic_thickenings : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  first | exact @GlobalTheory.AnPer.isChern_real | exact GlobalTheory.AnPer.isChern_real | (intros; apply GlobalTheory.AnPer.isChern_real <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftUnits

theorem le_pre_inf {X Y : Scheme.{0}} {y : Y ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ y ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := fun _ hp => ⟨hU hp, hV hp⟩

theorem le_pre_of_eq {X Y Z : Scheme.{0}} {f : Z ⟶ Y} {y : Y ⟶ X} {z : Z ⟶ X} (e : f ≫ y = z) {U : X.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ z ⁻¹ᵁ U := by
  subst e
  intro p _
  exact hU (Set.mem_univ (f p))

theorem map_evalAt {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') {x : Sp C ⟶ X}
    {y : Sp C' ⟶ X} (e : spMap φ ≫ x = y) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    φ (evalAt x U h f) = evalAt y U h' f := by
  subst e
  obtain ⟨_, hn, -⟩ := GlobalTheory.EvalNat.evalAt_natural φ x U h
  exact (hn f).symm

theorem evalAt_g_mul {X : Scheme.{0}} {C : Type} [CommRing C] {M : LB X} (hM : M.IsLB) (y : Sp C ⟶ X) {a b c : M.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ M.U a) (hb : ⊤ ≤ y ⁻¹ᵁ M.U b) (hc : ⊤ ≤ y ⁻¹ᵁ M.U c) :
    evalAt y _ (le_pre_inf ha hb) (M.g a b).val * evalAt y _ (le_pre_inf hb hc) (M.g b c).val =
      evalAt y _ (le_pre_inf ha hc) (M.g a c).val := by
  have hres : ∀ {U V : X.Opens} (h : V ≤ U) (u : (Γ(X, U))ˣ),
      ((res h u : (Γ(X, V))ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := fun _ _ => rfl
  have q2 := congrArg (fun u => evalAt y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc) (Units.val u))
    (hM.cocycle a b c)
  simp only [Units.val_mul, map_mul, hres] at q2
  obtain ⟨_, -, hr⟩ := GlobalTheory.EvalNat.evalAt_natural (RingHom.id C) y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc)
  rw [hr (M.U a ⊓ M.U b) (le_trans inf_le_left le_rfl) (le_pre_inf ha hb),
    hr (M.U b ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_right) inf_le_right) (le_pre_inf hb hc),
    hr (M.U a ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (le_pre_inf ha hc)]
  exact q2

theorem isUnit_evalAt {X : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) : IsUnit (evalAt y U h u.val) := u.isUnit.map (evalAt y U h)

theorem mul_eq_one_of_covolume_identity {R : Type} [CommRing R] {g₁ g₂ g₃ g₄ g₅ u v w A S f : R} (c₁ : g₁ * g₂ = g₅) (c₂ : g₃ * g₄ = g₅)
    (hu : u = g₁) (hv : v = g₂ * S) (hw : w = g₃ * f) (hf : f = g₄ * A * S) : u * v * A = w := by
  subst hu hv hw hf
  linear_combination (S * A) * c₁ - (S * A) * c₂

theorem exists_units : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) := by
  intro I _ g Λ _ F B _ X s σ K r M hM j hj fr a hfr hcoc i hi uu huu
  have hjT : ∀ T : K.Obj, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (j T.k) := fun T =>
    le_pre_of_eq (f := spMap ((Ideal.Quotient.mk T.J).comp T.ρ)) (y := r.x T.k) rfl (hj T.k)
  have hlift : ∀ T : K.Obj, ∃ c : T.C, IsUnit c ∧ Ideal.Quotient.mk T.J c =
      @id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k)) := by
    intro T
    have hu : IsUnit (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k))) :=
      (isUnit_evalAt (r.obj T).x (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k))).mul
        (((hfr T.k).map T.ρ).map (Ideal.Quotient.mk T.J))
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T))
      (M.g (i T) (j T.k)).val) * Ideal.Quotient.mk T.J (T.ρ (fr T.k)))
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (((hu.unit⁻¹ : (T.C ⧸ T.J)ˣ)) : T.C ⧸ T.J)
    refine ⟨c, ?_, hc⟩
    have hmem : c * d - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, hd, map_one, IsUnit.mul_val_inv, sub_self]
    have hnil : IsNilpotent (c * d - 1) := by
      obtain ⟨n, hn⟩ := T.nil
      refine ⟨n, ?_⟩
      have hp := Ideal.pow_mem_pow hmem n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
    have hcd : IsUnit (c * d) := by
      have h1 := hnil.isUnit_one_add
      rwa [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left hcd
  choose c hcu hcε using hlift
  refine ⟨fun T => (hcu T).unit, ?_⟩
  intro T T' φ
  have hle : K.le φ.deg T'.k T.k := Charts.Hom.le φ
  have hiT : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (i T) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hi T)
  have hjk : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (j T.k) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hjT T)
  have hxk : ⊤ ≤ r.x T'.k ⁻¹ᵁ (M.U (j T'.k) ⊓ M.U (j T.k)) :=
    le_pre_inf (hj T'.k) (le_pre_of_eq (r.compat hle) (hj T.k))
  have c₁ := evalAt_g_mul hM (r.obj T').x (hi T') hiT hjk
  have c₂ := evalAt_g_mul hM (r.obj T').x (hi T') (hjT T') hjk
  have hu := huu T T' φ (le_pre_inf (hi T') hiT)
  have hS : Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) =
      Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) :=
    Ideal.Quotient.eq.mpr (Close.sub_mem φ.close (fr T.k))
  have hv : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf hiT hjk) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    have h1 : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
        Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (c T)) := by
      rfl
    have h2 : Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (T.ρ (fr T.k))) =
        Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) := by
      rfl
    rw [h1, hcε T, map_mul, h2, hS]
    congr 1
    exact map_evalAt (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem) (x := (r.obj T).x) (y := (r.obj T').x)
      (r.analyticChartsRealization_comp_point_eq φ) _ (le_pre_inf hiT hjk) _
  have hf : Ideal.Quotient.mk T'.J (T'.ρ (fr T'.k)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf (hjT T') hjk) (M.g (j T'.k) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (a φ.deg T'.k)) * Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    rw [hcoc φ.deg T'.k T.k hle hxk, map_mul, map_mul, map_mul, map_mul]
    congr 2
    exact map_evalAt ((Ideal.Quotient.mk T'.J).comp T'.ρ) (x := r.x T'.k) (y := (r.obj T').x) rfl _ _ _
  refine Ideal.Quotient.eq.mp ?_
  rw [map_mul, map_mul]
  exact mul_eq_one_of_covolume_identity (R := T'.C ⧸ T'.J) c₁ c₂ hu hv (hcε T') hf

end GlobalTheory.LiftUnits
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_small_chart_pair_along_linear_map : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧ (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧ ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  first | exact @GlobalTheory.AnPer.ChartPair.exists_pair | exact GlobalTheory.AnPer.ChartPair.exists_pair | (intros; apply GlobalTheory.AnPer.ChartPair.exists_pair <;> assumption)
end
