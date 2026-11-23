module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem opOf_finset_sum {Γ V ι : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (f : Γ →₀ ℂ) (I : Finset ι) (u : ι → V) : opOf ρ f (∑ i ∈ I, u i) = ∑ i ∈ I, opOf ρ f (u i) := by
  unfold opOf

  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

private theorem finite_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G}
    (hA : IsCompact (A : Set G)) (hB : IsOpen (B : Set G)) : Finite (A ⧸ B.subgroupOf A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A) := hB.preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ ho

private theorem bound_arith {M s ε c t : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hε : 0 < ε) (hc : 0 ≤ c) (ht : t ≤ ε / (M * s + 1)) :
    M * (s * c) * t ≤ ε * c := by
  have hd : 0 < M * s + 1 := by positivity
  have h1 : M * s * t ≤ ε := by
    have hMs : 0 ≤ M * s := by positivity
    calc M * s * t ≤ M * s * (ε / (M * s + 1)) := mul_le_mul_of_nonneg_left ht hMs
      _ = ε * (M * s / (M * s + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  calc M * (s * c) * t = (M * s * t) * c := by ring
    _ ≤ ε * c := mul_le_mul_of_nonneg_right h1 hc

theorem UpperTheory.Gal.Gen.count_pf :
    UpperTheory.Gal.Gen.CountCore → UpperTheory.Gal.Gen.Cover → UpperTheory.Gal.Gen.Sep → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Count := by
  intro hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε
  obtain ⟨M, hM0, hM⟩ := hCore E a W
  obtain ⟨S, hS⟩ := hCover E a w₀ hs K hK J hJ
  have hδ : 0 < ε / (M * (S.card : ℝ) + 1) := by positivity
  obtain ⟨h, h1, h2, h3, h4⟩ := hB _ hδ
  obtain ⟨n₀, hn₀⟩ := hSep E a w₀ hs K hK J hJ S h.support h1 h2
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)
  letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _
  obtain ⟨r, hr, hcov⟩ := hS n
  have hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support :=
    fun y g hg g' hg' γ hγ x hx c hc e =>
      hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e
  have hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v := by
    intro f hf v
    obtain ⟨I, F, hF, rfl⟩ := (hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf
    have e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v := by
      simp [Submodule.coe_sum, LinearMap.sum_apply]
    rw [e, opOf_finset_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    obtain ⟨hP, hfin, hfx, -⟩ := hF π hπ
    refine h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_
    rw [RU_apply]
    exact hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g
  obtain ⟨hfd, hle⟩ := hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B)
    (hPart E a W (lev K w₀ (J n)) B).2.1 hfix
  refine ⟨hfd, hle.trans ?_⟩
  have hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) =
      (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hcard]
  exact bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3
end

section

noncomputable section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def FramedX {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) {J : Type} (t : J → (UA E a →₀ ℂ)) : Prop :=
  ∃ (X : Type) (b : UA E a → X → W.Sp), (∀ f : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (f.1 (b g i) g)‖ ≤ R) ∧
    (∀ f : algForms W, (∀ g i, f.1 (b g i) g = 0) → f = 0) ∧
    ∀ (F : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R : ℝ), (∀ g i, ‖ι.symm (F (b g i) g)‖ ≤ R) →
      ∀ j g i, ‖ι.symm (opOf (RU E a) (t j) (F (b g i)) g)‖ ≤ R

def DenomLe (l d : ℕ) (g : UA E a) : Prop :=
  ∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
    IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
    IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E)))

def IntW {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU (E := E) (n := a) ∧ ∃ d : ℕ, DenomLe l d g ∧ ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

def CoefLe {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type} (R : ℝ) (x : MvPolynomial σ ℂ) : Prop :=
  ∀ m, ‖ι.symm (AddMonoidAlgebra.coeff x m)‖ ≤ R

def ToPolyX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), K ≤ finU (E := E) (n := a) → ∀ (lam : (E →+* ℂ) → DomWeight a)
    (P : Submodule ℂ (UA E a → ℂ) → Prop), Dense ι (Wt.ofFam lam) K P → ∀ (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), FramedX ι (Wt.ofFam lam) t → ActsBy K t η → ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η U' j)}

def Kappa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    ∃ κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ), (∀ γ ∈ ratU E n, κ γ = cAll γ) ∧ (∀ x ∈ infU E n, κ x = 1) ∧
      ∀ (g : UA E n) (d : ℕ), DenomLe l d g → ∀ v i j,
        ‖ι.symm (((κ g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d ∧
        ‖ι.symm ((((κ g v)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d

def DenomBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : ℕ) (Z : Set (UA E n)), IsCompact Z →
    ∃ d : ℕ, ∀ g ∈ Z, DenomLe l d g

def DegLe : Prop :=
  ∀ (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n), ∀ x ∈ Formalism.L2.DIV.VV ℂ lam,
    x.totalDegree ≤ ∑ τ, ∑ i, (lam τ).natW i

def BlockBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) (n : ℕ) (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ R) → ∀ (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ), x.totalDegree ≤ D → CoefLe ι 1 x →
    CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x)

def DetBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ),
    1 ≤ R → (∀ τ i j, ‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R) →
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, n * (lam τ).detShift.natAbs)

def SizeLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a),
    (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs ≤ a * wtSize W.at

def RhoBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a)
    (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R) →
    ∀ x : W.Sp, CoefLe ι 1 x.1 → CoefLe ι (R ^ (a * wtSize W.at)) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1

def LatFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (σ : Type) (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V],
    (∀ φ : V →ₗ[ℂ] ℂ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (x : V), CoefLe ι R x.1 → ‖ι.symm (φ x)‖ ≤ M * R) ∧
    ∀ x : V, ∃ c : ℂ, c ≠ 0 ∧ CoefLe ι 1 (c • x).1

def LevelEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (f : algForms W),
    ∃ C : Subgroup (UA E a), IsLevel C ∧ f ∈ fixedBy W C

def FrameW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a) (J : Type)
    (t : J → (UA E a →₀ ℂ)), (∀ j, IntW ι W.at (t j)) → FramedX ι W t

def MaxCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (H : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (Z : Set (GL (Fin a) (w.adicCompletion E))), IsCompact Z → (H : Set (GL (Fin a) (w.adicCompletion E))) ⊆ Z →
    GlobalTheory.LFun.KGL w (n := a) ≤ H → H ≤ GlobalTheory.LFun.KGL w (n := a)

def PowNhds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a N : ℕ), N ≠ 0 →
    ∀ V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), (fun x => x ^ N) '' V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E))

def KerOpen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (J : Subgroup (GL (Fin a) (w.adicCompletion E))),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (A : Type) [Group A] [Finite A] (θ : J →* A),
    ∃ N : Set (GL (Fin a) (w.adicCompletion E)), IsOpen N ∧ 1 ∈ N ∧ ∀ x : J, x.1 ∈ N → θ x = 1

def TyStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ → ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (W : Wt E a)
    (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), ∀ f ∈ fixedBy W (lev K w₀ J),
      ∃ G ∈ part W K (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U),
        ∃ e : UA E a → ℂ, (∀ g, ‖ι.symm (e g)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ m) ∧ ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def TwistPart : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a))
    (W : Wt E a) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (A : Type) [Group A] (θ : J →* A) (χ : A →* ℂˣ)
    (hC : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J), (∀ k ∈ K, cLoc w₀ k = 1) → ∀ F : algForms W,
    (∀ c (hc : c ∈ lev K w₀ J) v g, F.1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * F.1 v g) →
    F ∈ part W K fun U => HasTypeVec w₀ K J θ χ U

def CharSum : Prop :=
  ∀ (N : ℕ) [NeZero N], ∃ (s : Finset (Multiplicative (ZMod N) →* ℂˣ)), (∀ χ ∈ s, χ ≠ 1) ∧
    ∀ x : Multiplicative (ZMod N), 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = 0 ∨ 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = N

end UpperTheory.Gal.Gen

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.step_pf :
    UpperTheory.Gal.Gen.SmoothAt → UpperTheory.Gal.Gen.Tower → UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.CountGen → UpperTheory.Gal.Gen.StepCore → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Step := by
  intro hSm hTw hLev hEll hCG hSC hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf
  obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs W f
  obtain ⟨J, hJ, hJN, htf, hpow⟩ := hTw E w₀ a l (Fact.out) hl ha N hN
  obtain ⟨n, hfd, hcard⟩ := hCG E a w₀ hs K hK J hJ W S Φ hS
  obtain ⟨lv0, mem0, inJ0, -, sec0, tr0⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  obtain ⟨-, memn, inJn, -, -, -⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  haveI hnorm : ((J n).subgroupOf (J 0)).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hJ.normal n g.1 g.2 x.1 hx⟩
  haveI : CompactSpace (J 0) := isCompact_iff_compactSpace.1 (hJ.compact 0)
  haveI hfin : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) :=
    Subgroup.quotient_finite_of_isOpen _ ((hJ.isOpen n).preimage continuous_subtype_val)
  have hp : IsPGroup l (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hpow n x.1 x.2
  let φ : lev K w₀ (J 0) →* J 0 :=
    ((cLoc w₀).comp (lev K w₀ (J 0)).subtype).codRestrict (J 0) (fun c => inJ0 c.1 c.2)
  let lam : lev K w₀ (J 0) →* (J 0 ⧸ (J n).subgroupOf (J 0)) := (QuotientGroup.mk' _).comp φ
  have hlam : ∀ c : lev K w₀ (J 0), lam c = 1 ↔ cLoc w₀ c.1 ∈ J n := fun c => by
    change ((φ c : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective lam := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, hxy⟩ := sec0 y.1
    have hxC : x ∈ lev K w₀ (J 0) :=
      (mem0 x).2 ⟨1, one_mem _, x, hx, hxy ▸ y.2, (one_mul x).symm⟩
    refine ⟨⟨x, hxC⟩, ?_⟩
    change ((φ ⟨x, hxC⟩ : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = _
    congr 1
    exact Subtype.ext hxy
  have hle : lev K w₀ (J n) ≤ lev K w₀ (J 0) := fun c hc => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (memn c).1 hc
    exact (mem0 _).2 ⟨k, hk, x, hx, hJ.anti (Nat.zero_le n) hxJ, rfl⟩
  have hiff : ∀ c : lev K w₀ (J 0), c.1 ∈ lev K w₀ (J n) ↔ lam c = 1 := fun c => by
    rw [hlam]
    exact ⟨inJn c.1, tr0 (J n) c.1 c.2⟩
  obtain ⟨ℓ, hℓ₁, hℓ₂, hℓ₃⟩ := hEll E a (lev K w₀ (J 0)) lv0 _ lam
    ⟨cLoc w₀ ⁻¹' (J n : Set (GL (Fin a) (w₀.adicCompletion E))), (hJ.isOpen n).preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀),
      by simp [one_mem], fun c hc => (hlam c).2 hc⟩
    (fun c hc => by
      have h1 : cLoc w₀ c.1 = 1 :=
        htf _ (inJ0 c.1 c.2) (MonoidHom.isOfFinOrder ((cLoc w₀).comp (lev K w₀ (J 0)).subtype) hc)
      exact (hlam c).2 (h1 ▸ one_mem _))
  have hfC : f ∈ fixedBy W (lev K w₀ (J 0)) := fun c hc v g => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (mem0 c).1 hc
    rw [← mul_assoc, hfN x hx (hJN hxJ) v (g * k)]
    exact hf k hk v g
  obtain ⟨G, hG, e, he, hfe⟩ := hSC E l ι a W (lev K w₀ (J 0)) (lev K w₀ (J n)) lv0.fin _ hp lam hsurj hle hiff
    ℓ hℓ₁ hℓ₂ hℓ₃ (fun U => ∀ w ∈ S, GenAt w (Φ w) U) hfd hcard f hfC
  exact ⟨G, (hPF E a W (lev K w₀ (J n)) _).2.2.1 K le_sup_left hG, e, he, hfe⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.cover_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.Cover := by
  intro hL hC E _ _ _ a w₀ hw K hK J hJ
  obtain ⟨hlev, hmem, -, -, hsurj, -⟩ := hL E a w₀ hw K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have ho : IsOpen (((lev K w₀ (J 0)).subgroupOf (finU (E := E) (n := a)) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨N, hN, h1, hNC⟩ := hlev.isOpen
    refine Filter.mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds h1) fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 (hNC ⟨hy, y.2⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a _ ho
  refine ⟨S, fun n => ?_⟩
  choose R hR using fun q : J 0 => (hsurj q.1)
  refine ⟨fun q => R q.out, fun q => ⟨(hR _).1, (hR _).2 ▸ q.out.2⟩, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  obtain ⟨k₀, hk₀, j, hj, hjJ, hkeq⟩ := (hmem _).1 (Subgroup.mem_subgroupOf.1 hk)
  have hcomm : j * k₀ = k₀ * j := hC E a w₀ j k₀ hj (hK.one k₀ hk₀)
  let q : J 0 ⧸ (J n).subgroupOf (J 0) := QuotientGroup.mk ⟨cLoc w₀ j, hjJ⟩
  have hq : (q.out)⁻¹ * ⟨cLoc w₀ j, hjJ⟩ ∈ (J n).subgroupOf (J 0) :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
  have hq' : (cLoc w₀ (R q.out))⁻¹ * cLoc w₀ j ∈ J n := by
    have := Subgroup.mem_subgroupOf.1 hq
    rw [(hR q.out).2]
    simpa using this
  have hr : R q.out ∈ locU a w₀ := (hR _).1
  refine ⟨γ, hγ, (⟨s, hs⟩, q), x, hx, (R q.out)⁻¹ * j * k₀, ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hr) hj, ?_⟩)) (Subgroup.mem_sup_left hk₀)
    change cLoc w₀ ((R q.out)⁻¹ * j) ∈ J n
    rwa [map_mul, map_inv]
  · have hxr : R q.out * x = x * R q.out := fin_mul_inf (hlev.fin (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hr, by
      change cLoc w₀ (R q.out) ∈ J 0
      rw [(hR q.out).2]
      exact q.out.2⟩))) hx
    show γ * s * x * (k : UA E a) = γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀)
    rw [hkeq, ← hcomm]
    have e : γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀) = γ * s * (R q.out * x) * ((R q.out)⁻¹ * j * k₀) := by
      group
    rw [e, hxr]
    group
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.algC_pf :
    UpperTheory.Gal.Gen.Alg → UpperTheory.Gal.Gen.AlgC := by
  intro hA l _ ι H _ _ hp P hP hcard
  let P' : Submodule (Qbar l) (H → Qbar l) :=
    { carrier := {f | (fun h => ι (f h)) ∈ P}
      zero_mem' := by
        show (fun h => ι ((0 : H → Qbar l) h)) ∈ P
        convert P.zero_mem using 1
        funext h
        simp
      add_mem' := by
        intro a b ha hb
        show (fun h => ι ((a + b) h)) ∈ P
        convert P.add_mem ha hb using 1
        funext h
        simp
      smul_mem' := by
        intro r a ha
        show (fun h => ι ((r • a) h)) ∈ P
        convert P.smul_mem (ι r) ha using 1
        funext h
        simp }
  let j : P ≃+ P' :=
    { toFun := fun c => ⟨fun h => ι.symm (c.1 h), by
        show (fun h => ι (ι.symm (c.1 h))) ∈ P
        simpa using c.2⟩
      invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩
      left_inv := by
        intro c
        ext h
        simp
      right_inv := by
        intro f
        ext h
        simp
      map_add' := by
        intro a b
        ext h
        simp }
  have hrank : Module.rank ℂ P = Module.rank (Qbar l) P' := by
    refine rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_
    intro r m
    ext h
    change ι.symm (r * m.1 h) = ι.symm r * ι.symm (m.1 h)
    exact map_mul ι.symm r (m.1 h)
  have hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P' := by
    unfold Module.finrank
    rw [hrank]
  have hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P' := by
    intro c hc g
    exact hP _ hc g
  obtain ⟨c, hc, hbound⟩ := hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)
  refine ⟨fun h => ι (c h), hc, ?_⟩
  intro h
  simpa using hbound h
end
