module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbFn :
    OrbS → OrbFn := by
  intro hS E _ _ _ D M j hj c hc hcs
  have hstab := (hS E D).2.1
  haveI : PolishSpace (G1 E) := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  haveI := M.haar
  haveI := M.right
  have hval : ∀ g : G1 ℚ, (j g).1 = g.1.map (AdeleBaseChange.adeleMap ℚ E) := fun g => by
    have := congrArg Units.val (hj g)
    simpa [em] using this
  have hjc : Continuous j := by
    refine continuous_induced_rng.2 ?_
    exact (continuous_subtype_val.matrix_map AdeleBaseChange.continuous_adeleMap).congr fun g => (hval g).symm
  set O : G1 E → V4 ℚ := fun h => D.act (gl h)⁻¹ (rp X0) with hO
  set cc : G1 E → ℂ := fun h => ∫ g, c (j g * h) ∂M.μ with hcc
  have hgl : Continuous fun h : G1 E => gl h := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : ∀ h : G1 E, ((gl h)⁻¹ : GL (Fin 2) (A E)).val = (h⁻¹ : G1 E).1 := fun h => by
      have : (gl h)⁻¹ = gl h⁻¹ := by simp only [gl, map_inv]
      rw [this]; rfl
    have hi : Continuous fun h : G1 E => (h⁻¹ : G1 E).1 :=
      (continuous_subtype_val : Continuous fun g : G1 E => g.1).comp continuous_inv
    exact hi.congr fun h => (e h).symm
  have hglc : Continuous fun h : G1 E => (gl h)⁻¹ := hgl.inv
  have hOc : Continuous O := D.continuous_act' hglc continuous_const
  have hccm : Measurable cc := by
    have hF : StronglyMeasurable (Function.uncurry fun (h : G1 E) (g : G1 ℚ) => c (j g * h)) :=
      (hc.comp ((hjc.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
    exact (hF.integral_prod_right (ν := M.μ)).measurable
  have hfac : Function.FactorsThrough cc O := by
    intro a b hab
    have h1 : D.act (gl (b * a⁻¹)) (rp X0) = rp X0 := by
      have hab' : D.act (gl a)⁻¹ (rp X0) = D.act (gl b)⁻¹ (rp X0) := hab
      have e : gl (b * a⁻¹) = gl b * (gl a)⁻¹ := by simp only [gl, map_mul, map_inv]
      rw [e, Dat.act_mul, hab', Dat.act_act_inv]
    obtain ⟨g0, hg0⟩ := (hstab (b * a⁻¹)).1 h1
    have h2 : b * a⁻¹ = j g0 := Matrix.SpecialLinearGroup.toGL_injective (hg0.trans (hj g0).symm)
    have h3 : b = j g0 * a := by rw [← h2]; group
    simp only [hcc]
    rw [h3]
    have := integral_mul_right_eq_self (μ := M.μ) (fun g => c (j g * a)) g0
    simp only [map_mul, mul_assoc] at this
    exact this.symm
  refine ⟨Function.extend O cc 0, ?_, fun h => hfac.extend_apply 0 h⟩
  have hR : MeasurableSet (Set.range O) := by
    obtain ⟨K, hK, hU⟩ := isSigmaCompact_range hOc
    rw [← hU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  refine measurable_of_restrict_of_restrict_compl hR ?_ ?_
  · have hr : Measurable (Set.rangeFactorization O) := hOc.measurable.subtype_mk
    refine (Measurable.measurable_comp_iff_of_surjective hr Set.rangeFactorization_surjective).1 ?_
    have e : (Set.range O).domRestrict (Function.extend O cc 0) ∘ Set.rangeFactorization O = cc := by
      funext h
      exact hfac.extend_apply 0 h
    rw [e]
    exact hccm
  · have e : (Set.range O)ᶜ.domRestrict (Function.extend O cc 0) = fun _ => 0 := by
      funext x
      exact Function.extend_apply' cc (0 : V4 ℚ → ℂ) x.1 fun ⟨a, ha⟩ => x.2 ⟨a, ha⟩
    rw [e]
    exact measurable_const
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rev :
    ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal → Dens → Fub → CoefPer → Rev := by
  rintro hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩
  obtain ⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)
    have h1 := hC E D W M N P ph hph φ hφ (qr D.δ X0) 1
    rw [← hE E D W M N P ph hph φ hφ, hn ph hph] at h1
    have hδ : qr D.δ X0 ≠ 0 := by
      have := D.neg (Rat.castHom ℝ)
      simp only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢
      simpa using this.ne
    have e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0} :=
      Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩
    rw [e] at h1
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h1
    refine (mul_eq_zero.1 h1.symm).resolve_left ?_
    simp [Measure.real, adeleMeasure_fundamentalSet]
  obtain ⟨π, hπ, f, hf, h2⟩ := hD M _ (hF E D W M N P ph hph φ hφ) h0
  exact ⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

structure Bd (Ψ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous Ψ
  left : ∀ γ g, Ψ (ratGL E 2 γ * g) = Ψ g
  bdd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖Ψ (gl h * k)‖ ≤ B

def PosC (Ψ : GL (Fin 2) (A E) → ℂ) : Prop := ∀ s g, Ψ (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = Ψ g

variable [_root_.NumberField.IsTotallyComplex E]

structure InvPair (V V' : Submodule ℂ (Sm E 2)) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) : Prop where
  st : _root_.GlobalTheory.CuspRep.IsStable V
  st' : _root_.GlobalTheory.CuspRep.IsStable V'
  fin : ∀ k (x : V) (y : V'), B ⟨act (.fin k) x.1, st _ _ x.2⟩ ⟨act (.fin k) y.1, st' _ _ y.2⟩ = B x y
  cpt : ∀ k (x : V) (y : V'), B ⟨act (.cpt k) x.1, st _ _ x.2⟩ ⟨act (.cpt k) y.1, st' _ _ y.2⟩ = B x y
  lie : ∀ X (x : V) (y : V'), B ⟨act (.lie X) x.1, st _ _ x.2⟩ y + B x ⟨act (.lie X) y.1, st' _ _ y.2⟩ = 0

end Objects

def MeanLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ y, IntegrableOn (fun h => Ψ (gl h * y)) N.D N.μ) ∧ (Continuous fun y => mean N fun x => Ψ (x * y)) ∧
  (∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y)) ∧
  ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y)

def UILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E) ∧
  (∃ B : ℝ, ∀ t : (A E)ˣ, ab t = 1 → ‖β t‖ ≤ B) ∧ ∀ d : (A E)ˣ, ab d = 1 → (UI fun t => β (t * d)) = UI β

def IILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ Ψ', Bd Ψ' → ∀ c : ℂ, (II N fun x => Ψ x + c * Ψ' x) = II N Ψ + c * II N Ψ') ∧
  (PosC Ψ → ∀ g, (II N fun x => Ψ (x * g)) = II N Ψ)

def IILie : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : MeasE E) (Φ φ : Sm E 2) (X),
  (Bd fun x => Φ.1 x * φ.1 x) → (PosC fun x => Φ.1 x * φ.1 x) → (Bd fun x => (act (.lie X) Φ).1 x * φ.1 x) →
  (Bd fun x => Φ.1 x * (act (.lie X) φ).1 x) →
  (II N fun x => (act (.lie X) Φ).1 x * φ.1 x) + (II N fun x => Φ.1 x * (act (.lie X) φ).1 x) = 0

def SpanGrow : Prop := All fun E _ _ _ _ W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π,
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∃ (r : ℕ) (B : ℝ), ∀ b a, ∀ k ∈ C, c ≤ ab a →
    ‖Φ.1 (gl (nU b * mD a) * k)‖ ≤ B * ab a ^ r

def ProdBd : Prop := All fun _ _ _ _ _ W M _ P => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ φ ∈ P.V,
  (Bd fun x => Φ.1 x * φ.1 x) ∧ (PosInv π → GlobalTheory.DiscSpec.IsNormalised P → PosC fun x => Φ.1 x * φ.1 x)

def KillW : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
  (∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → (∀ h, WE D Φ h = 0) → ∀ (h : G1 E) g, Φ (gl h * g) = Φ g

def PairEx : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  ∃ B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ, InvPair _ _ B ∧ (∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g) ∧
    ∀ x : span W M π, (∀ h, WE D x.1.1 h = 0) → B x = 0

def SplitEig : Prop := All fun E _ _ _ D W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ (v : P ℚ) (w : P E), SplitAt v w →
  ∀ B, π.HasSat v B → Fix w Φ.1 → EigAt w B (WE D Φ.1)

def SatPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (w : P E) (T : V →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)),
  (∀ x : V, ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, x.1.1 (g * lc w y) = x.1.1 g) →
  (∀ (x x' : V) y, (∀ g, x'.1.1 g = x.1.1 (g * lc w y)) → ∀ g, T x' g = T x (g * lc w y)) → (∀ x, T x = 0 → B x = 0) →
  ∀ C C' : Multiset ℂˣ, (∀ x : V, Fix w x.1.1 → EigAt w C (T x)) → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹)

def InfPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), m.card = 2 →
  (∀ u, ∀ Φ ∈ V, cap τ u Φ = (m.map (u + ·)).prod • Φ) → Q.HasInfChar τ m' → m' = m.map Neg.neg

def CharSel : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  (UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹)) ≠ 0 →
  ∃ χ : HChar E, (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) ∧
    (∀ z : (A E)ˣ, (∃ s, Matrix.GeneralLinearGroup.scalar (Fin 2) z = GroundTheory.Automorphic.Reduction.centralSection E 2 s) → χ.1 z = 1) ∧
    (UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t) ≠ 0

def CharDown : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (χ : HChar E),
  (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) → ∃ χ₀ : HChar ℚ, ∀ z : (A E)ˣ, χ.1 z = χ₀.1 (ideleNorm ℚ E z)

def FinS : Prop := All fun E _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

def DownN : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], Module.finrank ℚ E = 2 → ∀ P : CuspSub E 2,
  GlobalTheory.DiscSpec.IsNormalised P → ConjInv P → ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

private theorem barW_coe (z : (A E)ˣ) : ((Units.map (D.bar : A E →* A E) z : (A E)ˣ) : A E) = D.bar z := rfl

private theorem bar_mul_barInv (z : (A E)ˣ) :
    D.bar (z : A E) * (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = 1 := by
  rw [← barW_coe, Units.mul_inv]

private theorem sZ_val (z : (A E)ˣ) :
    (sZ D z).val = !![(z : A E), 0; 0, (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E)] := by
  simp only [sZ, Units.val_mul, aE_val, dM_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem em_val (h : GL (Fin 2) (A ℚ)) (i j : Fin 2) : (em E h).val i j = am E (h.val i j) := rfl

private theorem am_norm_mul (z : (A E)ˣ) :
    (z : A E) * D.bar z * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [← D.am_ideleNorm z, ← map_mul, Units.mul_inv, map_one]

private theorem barInv_eq (z : (A E)ˣ) :
    (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) * z := by
  have h2 := am_norm_mul D z
  have h3 := bar_mul_barInv D z
  linear_combination ((z : A E) * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ)) * h3 - (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) * h2

private theorem sZ_mul (z z' : (A E)ˣ) : sZ D (z * z') = sZ D z * sZ D z' := by
  simp only [sZ, map_mul, mul_inv, aE_mul, dM_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc (dM _) (aE z'), dM_mul_aE, ← mul_assoc (aE z')]

private theorem sZ_cont : Continuous (sZ D) := by
  have h : Continuous (Units.map (D.bar : A E →* A E)) := Continuous.units_map _ D.continuous_bar
  exact continuous_aE.mul (continuous_dM.comp h.inv)

private theorem nu_sZ (z : (A E)ˣ) : nu ℚ (sZ D z) = 1 := by
  have h : ideleNorm ℚ E (Units.map (D.bar : A E →* A E) z) = ideleNorm ℚ E z := D.ideleNorm_barU z
  rw [sZ, nu_mul, nu_aE, nu_dM, map_inv, h, mul_inv_cancel]

private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE_def, X0, rp]

private theorem action_fixes_standardVector {h : GL (Fin 2) (A E)}
    (h1 : h.val * !![0, rt D.θ; -rt D.θ, 0] * D.star2 h.val = !![0, rt D.θ; -rt D.θ, 0]) :
    D.act h (rp X0) = rp X0 := by
  apply D.herm_injective
  rw [D.herm_act, hermitian_standardVector, h1]

private theorem act_sZ (z : (A E)ˣ) : D.act (sZ D z) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have h3 : (z : A E) * ((z⁻¹ : (A E)ˣ) : A E) = 1 := Units.mul_inv z
  have h4 : D.bar ((z⁻¹ : (A E)ˣ) : A E) * D.bar (z : A E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sZ_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply]
  · linear_combination (rt D.θ) * h3
  · linear_combination (rt D.θ) * h4

private theorem act_em (g : G1 ℚ) : D.act (em E (gl g)) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have hd : am E (g 0 0) * am E (g 1 1) - am E (g 0 1) * am E (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]
  have e : (em E (gl g)).val = !![am E (g 0 0), am E (g 0 1); am E (g 1 0), am E (g 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, D.bar_am]
  · ring
  · linear_combination (rt D.θ) * hd
  · linear_combination (-rt D.θ) * hd
  · ring

private theorem sZ_diag (e : Eˣ) : ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ := by
  obtain ⟨γ₁, h₁⟩ := exists_ratGL_aE (F := E) e
  obtain ⟨γ₂, h₂⟩ := exists_ratGL_dM (F := E) (Units.map (D.σ : E →* E) e)⁻¹
  refine ⟨γ₁ * γ₂, ?_⟩
  have h : (Units.map (D.bar : A E →* A E) (IdeleGroup.diagonal E e))⁻¹ =
      IdeleGroup.diagonal E (Units.map (D.σ : E →* E) e)⁻¹ := by
    rw [map_inv]
    congr 1
    apply Units.ext
    rw [barW_coe, coe_diagonal, coe_diagonal, D.bar_rt]
    rfl
  rw [sZ, h, map_mul, h₁, h₂]

private theorem sZ_conj (z : (A E)ˣ) (g : G1 ℚ) :
    sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z := by
  have hn := am_norm_mul D z
  have hb := barInv_eq D z
  have hN := D.am_ideleNorm z
  have hc : ∀ i j, (em E (gl (cD (ideleNorm ℚ E z)⁻¹ g))).val i j = am E ((cD (ideleNorm ℚ E z)⁻¹ g).1 i j) := fun _ _ => rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hc, em_val, gl_val, cD_val]
  fin_cases i <;> fin_cases j <;> simp [inv_inv, map_mul, hN]
  · ring
  · rw [GroundTheory.Global.coe_ideleNorm] at hN
    rw [hN]
    linear_combination (-(am E (g 0 1)) * (z : A E)) * hn
  · ring
  · ring

private theorem sZ_scalar (z : (A E)ˣ) :
    sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹) := by
  have hb := barInv_eq D z
  apply Units.ext
  rw [Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, em_val, dM_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · ring

private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws :
    SzLaws := by
  intro E _ _ _ D
  refine ⟨sZ_mul D, sZ_cont D, nu_sZ D, nu_gl, act_sZ D, act_em D, sZ_diag D, sZ_conj D, sZ_scalar D, ?_, quadraticForm_rational_points D.δ⟩
  intro x hx v
  rw [D.quadForm_act, hx]
  simp
end
