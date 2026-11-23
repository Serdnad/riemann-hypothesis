module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle066
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
end
end

section

noncomputable section

open Matrix GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

theorem mul_mem_ball {s : kˣ} (hs : valuation k (s : k) ≤ 1) {x y : k} (hx : x ∈ cball s)
    (hy : y ∈ cball s) : x * y ∈ cball s := by
  show valuation k (x * y) ≤ valuation k (s : k)
  rw [map_mul]
  calc valuation k x * valuation k y ≤ valuation k (s : k) * 1 :=
        mul_le_mul' hx (le_trans hy hs)
    _ = valuation k (s : k) := mul_one _

def NearOne (s : kˣ) {m : ℕ} (A : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ cball s

theorem NearOne.mul {s : kˣ} (hs : valuation k (s : k) ≤ 1) {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) k} (hA : NearOne s A) (hB : NearOne s B) : NearOne s (A * B) := by
  intro a b
  have e : (A * B) a b - (1 : Matrix (Fin m) (Fin m) k) a b =
      ((A - 1) * (B - 1)) a b + (A a b - (1 : Matrix (Fin m) (Fin m) k) a b) +
        (B a b - (1 : Matrix (Fin m) (Fin m) k) a b) := by
    have : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    exact congrFun (congrFun this a) b
  rw [e]
  refine add_mem_cball (add_mem_cball ?_ (hA a b)) (hB a b)
  rw [Matrix.mul_apply]
  exact (ballSub s).sum_mem fun l _ => mul_mem_ball hs (hA a l) (hB l b)


variable (k) in
def congGL (s : kˣ) (hs : valuation k (s : k) ≤ 1) (m : ℕ) : Subgroup (GL (Fin m) k) where
  carrier := {g | NearOne s (g : Matrix (Fin m) (Fin m) k) ∧
    NearOne s ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)}
  one_mem' := by
    constructor <;> intro a b <;> simp [cball]
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact g1.mul hs h1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact h2.mul hs g2
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    exact ⟨g2, by simpa using g1⟩


variable (k) in
def congM (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) : Subgroup (Mir k n) :=
  (congGL k s hs (n + 1)).comap (Mir k n).subtype

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free

def e0 (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 2) → K :=
  fun _ => Fin.cons 1 fun _ => 0

def consA {K : Type} [Zero K] [One K] {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 2) → K :=
  Fin.cons (Fin.cons 1 fun _ => 0) fun j => Fin.cons (a 0 j) (Fin.cons 0 (Y j))

section PiLocalization₂

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]

def stageInt (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (g : HA R σ (hypOne J)) : ℝ≥0∞ :=
  ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n) ∂m'

end PiLocalization₂

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def latStab (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J) : Prop :=
  ∀ x : Fin 1 → Fin M → Fv F v ⊗[F] E, actW (Fv F v) σ J g x ∈ latV b v ↔ x ∈ latV b v

def primV (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
  {y | ∃ g : HA (Fv F v) σ (hypOne J), latStab σ (hypOne J) b v g ∧
    actW (Fv F v) σ (hypOne J) g (e0 _ M) = y}

def purePr (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) : ℝ≥0∞ :=
  {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v}.indicator
    (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y

def ratA (n : ℕ) : AddSubgroup (Fin 1 → Fin n → AF F ⊗[F] E) where
  carrier := Set.range (ratTup (AF F) : (Fin 1 → Fin n → E) → Fin 1 → Fin n → AF F ⊗[F] E)
  zero_mem' := ⟨0, by funext a i; simp [ratTup]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by funext a i; simp [ratTup]⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by funext a i; simp [ratTup]⟩

def IsCovolOne {n : ℕ} (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) : Prop :=
  dA.IsAddHaarMeasure ∧ ∃ D : Set (Fin 1 → Fin n → AF F ⊗[F] E),
    IsAddFundamentalDomain (ratA (F := F) (E := E) n) D dA ∧ dA D = 1

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.one_le_detW_of_isHermitian : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.coinduced_cech_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.coinduced_nerve_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | exact GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.nerve_cech_degree_zero_compatible : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | exact GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.alternative_local_computation_of_components : GlobalTheory.CompanionTheory.Jp.JpIw → GlobalTheory.CompanionTheory.Jp.JpHgt → GlobalTheory.CompanionTheory.Jp.JpUnif → GlobalTheory.CompanionTheory.Jp.JpCmp → GlobalTheory.CompanionTheory.Jp.JpPos → GlobalTheory.CompanionTheory.Jp.JpCondition := by
  first | exact @GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps | exact GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps | (intros; apply GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps <;> assumption)
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.AvgRes

theorem avg_of_surjective {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (r : G →* H)
    (hr : Function.Surjective r) (hN : N ≤ r.ker) (f : H → ℂ) :
    (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, f (r (Quotient.out u)) = (∑ᶠ g, f g) / (Nat.card H : ℂ) := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set φ : G ⧸ N →* H := QuotientGroup.lift N r hN with hφdef
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨g, rfl⟩ := hr h
    exact ⟨(g : G ⧸ N), QuotientGroup.lift_mk N hN g⟩
  haveI : Finite H := Finite.of_surjective φ hφ
  haveI : Fintype H := Fintype.ofFinite _
  have hout : ∀ u : G ⧸ N, r (Quotient.out u) = φ u := by
    intro u
    conv_rhs => rw [← Quotient.out_eq u]
    exact (QuotientGroup.lift_mk N hN _).symm
  simp_rw [hout]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_comp f φ,
    Finset.image_univ_of_surjective hφ]
  set c := (Finset.univ.filter fun u : G ⧸ N => φ u = 1).card with hc
  have hfib : ∀ b : H, (Finset.univ.filter fun u : G ⧸ N => φ u = b).card = c := fun b =>
    MonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 1)
  have hcard : Fintype.card (G ⧸ N) = Fintype.card H * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image φ Finset.univ,
      Finset.image_univ_of_surjective hφ]
    simp [hfib]
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [hc]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp⟩)
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp_rw [hfib]
  rw [← Finset.smul_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard,
    nsmul_eq_mul]
  push_cast
  field_simp

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem resK_surjective (n : ℕ) : Function.Surjective (resK (n := n) (O := O)) := by
  intro M
  classical
  have hs := IsLocalRing.residue_surjective (R := O)
  let A : Matrix (Ix n) (Ix n) O :=
    (M : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)).map (Function.surjInv hs)
  have hA : (IsLocalRing.residue O).mapMatrix A = (M : Matrix (Ix n) (Ix n) _) := by
    ext i j
    exact Function.surjInv_eq hs _
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]
    exact (Matrix.isUnits_det_units M).ne_zero
  refine ⟨Matrix.nonsingInvUnit A hdet, ?_⟩
  ext i j
  exact Function.surjInv_eq hs _

theorem level_square_congruence_le_reduction_ker (n : ℕ) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) :
    Gam2 (n := n) ϖ ≤ (resK (n := n) (O := O)).ker := by
  intro g hg
  have hg' := MonoidHom.mem_ker.mp hg
  rw [MonoidHom.mem_ker]
  have hle : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hϖ 2 two_pos))
  ext i j
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((g : Matrix (Ix n) (Ix n) O) i j) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j) := by
    have h0 := congrArg
      (fun x : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => (x : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j) hg'
    change Ideal.Quotient.mk _ ((g : Matrix (Ix n) (Ix n) O) i j) =
      (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := Ideal.Quotient.eq.mpr (hle (Ideal.Quotient.eq.mp h1))
  change IsLocalRing.residue O ((g : Matrix (Ix n) (Ix n) O) i j) =
    (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j
  rw [show (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j =
      IsLocalRing.residue O ((1 : Matrix (Ix n) (Ix n) O) i j) by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp]
  exact h2

theorem avgK_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  intro O _ _ _ _ n ϖ hϖ f
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  haveI : (Gam2 (n := n) ϖ).Normal := MonoidHom.normal_ker _
  haveI : Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := GlobalTheory.CompanionTheory.Jp.Unif.finite_quotient_level_square_congruence n hϖ
  exact avg_of_surjective (Gam2 ϖ) resK (resK_surjective n) (level_square_congruence_le_reduction_ker n hm) f

end GlobalTheory.CompanionTheory.Jp.AvgRes

end
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.iwasawa_decomposition_statement : GlobalTheory.CompanionTheory.Jp.JpIw := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Iw.jpIw | exact GlobalTheory.CompanionTheory.Jp.Iw.jpIw | (intros; apply GlobalTheory.CompanionTheory.Jp.Iw.jpIw <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.uniform_boundedness_statement : GlobalTheory.CompanionTheory.Jp.JpUnif := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | exact GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | (intros; apply GlobalTheory.CompanionTheory.Jp.Unif.jpUnif <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.height_bound_statement : GlobalTheory.CompanionTheory.Jp.JpHgt := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | exact GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | (intros; apply GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt <;> assumption)
end
