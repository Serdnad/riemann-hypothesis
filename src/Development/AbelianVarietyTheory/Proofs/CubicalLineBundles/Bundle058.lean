module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle055
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmFamily_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  first | exact @GlobalTheory.CM.isFam_descends_to_numberField | exact GlobalTheory.CM.isFam_descends_to_numberField | (intros; apply GlobalTheory.CM.isFam_descends_to_numberField <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmFamily_extends_over_dedekindDomain : Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ω' : K) (C' : Ell H K ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp K)) (m : SABMap T'.t T.t (spMap (algebraMap R K))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap R K) φ → IsFam C' T' h L ψ' → ∃ ψ : L → (C.P.A ⟶ T.t.G), IsFam C T h L ψ ∧ ∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left := by
  first | exact @GlobalTheory.isFam_extends_dedekind | exact GlobalTheory.isFam_extends_dedekind | (intros; apply GlobalTheory.isFam_extends_dedekind <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieLattice_of_isLocalModel_at_prime : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  first | exact @GlobalTheory.CM.lieLat_of_isLocalModel | exact GlobalTheory.CM.lieLat_of_isLocalModel | (intros; apply GlobalTheory.CM.lieLat_of_isLocalModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.relAmple_lineBundle_of_positive_hermitian_cm_form : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A) (t : Serre.IsTensor A b C.P.A C.act D.La) (N : LB A.left), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → N.IsLB → (∃ t : LB.Gen (Theta A N), t.IsGen) → LBIso N (cubeLB A ![𝟙 A, b.act (wK H)] N) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') C.P.L (C.act.act (h m m')) (𝟙 C.P.A)) → Out.RelAmple A N := by
  first | exact @GlobalTheory.CM.relAmple_of_kForm_pos | exact GlobalTheory.CM.relAmple_of_kForm_pos | (intros; apply GlobalTheory.CM.relAmple_of_kForm_pos <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.existsUnique_differential_monHom_lieBasis : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧ ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧ ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  first | exact @GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf | exact GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf | (intros; apply GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.GenFib


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat (K : Type) [Field K]
    [NumberField K] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K))) (F : _root_.GlobalTheory.CM.GenFib P) (O : Type)
    [CommRing O] (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O P.A) :
    ∃ r : O →+* Module.End K (Fin F.P₀.g → K),
      (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧
      ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔
          c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧
        (c ∈ Submodule.span K (F.eigLat act τ :
            Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  obtain ⟨hex, hinj, -, -, hlie, heig⟩ := _root_.GlobalTheory.CM.integral_tangent_coordinates K P F
  have hcoord : ∀ {u c c'}, F.IsCoord u c → F.IsCoord u c' → c = c' := fun h h' =>
    (hex _ h.1).unique h h'
  have hdiff : ∀ a, ∃! M, F.IsDiffOf F (act.act a) M := fun a =>
    (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F (act.act a) (act.hom a)).1
  choose R hR using fun a => (hdiff a).exists
  have huniq : ∀ a M, F.IsDiffOf F (act.act a) M → R a = M :=
    fun a M h => (hdiff a).unique (hR a) h
  have hone : R 1 = 1 := huniq 1 1 (by
    intro u c h
    simpa [act.one] using h)
  have hmul : ∀ a b, R (a * b) = R a * R b := fun a b => by
    rw [mul_comm a b]
    refine huniq _ _ ?_
    intro u c h
    rw [act.mul, ← Category.assoc]
    exact hR a _ _ (hR b u c h)
  have hadd : ∀ a b, R (a + b) = R a + R b := fun a b => by
    refine huniq _ _ ?_
    intro u c h
    rw [act.add, comp_mul]
    exact _root_.GlobalTheory.CM.IntCoord.isCoord_mul F (hR a u c h) (hR b u c h)

  have hspan : Submodule.span K (F.lieLat :
      Set (Fin F.P₀.g → K)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ0 (LinearMap.ext h)
    have hM : F.IsDiffOf F (act.act 1) (1 + φ.smulRight x) := by
      intro u c h
      have hφc : φ c = 0 := LinearMap.mem_ker.1 (hle (Submodule.subset_span ((hlie c).2 ⟨u, h⟩)))
      simpa [act.one, hφc] using h
    have h1 := LinearMap.congr_fun (hone.symm.trans (huniq 1 _ hM)) x
    simp at h1
    rcases h1 with h1 | h1
    · exact hx h1
    · exact hx (by simp [h1])
  have hlat : ∀ τ : O →+* 𝓞 K, ∀ c, c ∈ F.eigLat act τ ↔
      c ∈ F.lieLat ∧ ∀ a, R a c = τ a • c := by
    intro τ c
    rw [heig O act τ c, hlie c]
    constructor
    · rintro ⟨u, hu, hcomb⟩
      exact ⟨⟨u, hu⟩, fun a =>
        hcoord (hR a u c hu) (_root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu (hcomb a))⟩
    · rintro ⟨⟨u, hu⟩, hc⟩
      refine ⟨u, hu, fun a => ?_⟩
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb ![τ a] ![u] (_root_.GlobalTheory.CM.IntCoord.sc (τ a) ≫ u) :=
        (_root_.GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl
      have he := hinj _ _ _ (hR a u c hu)
        (by rw [hc a]; exact _root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu hs)
      rw [he]
      exact hs
  refine ⟨RingHom.mk' ⟨⟨R, hone⟩, hmul⟩ hadd, fun a => hR a, fun τ c => ⟨hlat τ c, ?_⟩⟩
  show _ ↔ ∀ a, R a c = τ a • c
  constructor
  · intro hc
    refine Submodule.span_induction (p := fun c _ => ∀ a, R a c = τ a • c) ?_ ?_ ?_ ?_ hc
    · exact fun x hx a => ((hlat τ x).1 hx).2 a
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [map_add (f := _), hx, hy, smul_add]
    · intro k x _ hx a
      rw [map_smul, hx, smul_comm]
  · intro hc
    have hcspan : c ∈ Submodule.span K (F.lieLat :
        Set (Fin F.P₀.g → K)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).1 hcspan
    rw [Submodule.span_eq] at hy
    have hzy : (z : 𝓞 K) • (IsLocalization.mk' K (1 : 𝓞 K) z • y) = y := by
      rw [← smul_assoc, Algebra.smul_def (z : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) z),
        IsLocalization.mk'_spec', map_one, one_smul]
    have hyeig : ∀ a, R a y = τ a • y := fun a => by
      rw [← hzy, LinearMap.map_smul_of_tower, hc a, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hlat τ y).2 ⟨hy, hyeig⟩))

end GlobalTheory.CM.GenFib
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isVecLine_mem_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf i ℓ h c
  obtain ⟨hgood, hp, -⟩ := h
  choose M cl hM hcl hc using hp
  obtain ⟨h1, -, h3⟩ := local_global_ideal_lattice K
  refine (h1 ℓ.I cl hgood.1 hcl c).trans (Iff.trans ?_ (h3 _ _ _).symm)
  refine forall_congr' fun p => ?_
  refine (hc p c).symm.trans (Iff.trans ?_ (isModelAt_integral_iff_mem_lieLat K A x φ hf p (M p) (hM p) _))
  have e : (Pi.single i c : Fin x.P.g → K) = c • (Pi.single i 1 : Fin x.P.g → K) := by
    rw [← Pi.single_smul', smul_eq_mul, _root_.mul_one]
  rw [e, Matrix.smul_vecMul]

end GlobalTheory.LamF
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LatticeData

theorem dataXOfModel_of_gamAt : ∀ (D : D7) (T : Core D), GamAt T → ∀ j, ∀ (_h : LawsCore T), InR D j → ∀ (σ₀ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ₀ → ∀ (k : (T.U j σ₀).Comp), ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ₀).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T hG j h hj σ hσ k
  obtain ⟨Xx, h1, h2, h3, -⟩ :=
    exists_dataX_of_hasPrinc D T h j hj σ hσ (fun k γ => hG j hj σ hσ k γ) k
  exact ⟨Xx, h1, h2, h3⟩

end GlobalTheory.LatticeData
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem half_one_add_sqrt_quadratic {K : Type} [Field K] [CharZero K] {d : ℕ} (h4 : d % 4 = 3) {r w : K}
    (hr : r ^ 2 = -(d : K)) (hw : 2 * w = 1 + r) : w * w + (((1 + d) / 4 : ℕ) : K) = w := by
  have e : 4 * ((1 + d) / 4) = 1 + d := by omega
  have e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d := by exact_mod_cast congrArg (Nat.cast : ℕ → K) e
  have e4 : (4 : K) ≠ 0 := by norm_num
  refine mul_left_cancel₀ e4 ?_
  have hr' : r = 2 * w - 1 := by linear_combination -hw
  subst hr'
  linear_combination e' + hr

theorem cmCurve_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  intro hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩
  obtain ⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩ := ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr
  have hnr := (hσ σ₀).1
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩ := GlobalTheory.T.exists_numberField_defining_cm_curve_homs hU hB K h2 σ₀ hnr 𝔟
    (exists_cm_curves_of_weierstrass_curves (GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB) K h2 σ₀ hnr 𝔟)
  have hv : IsTangent v := hP.2.1.1 0
  have hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2 := by
    have e := congrArg σ₀ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hσ₀] at e
    rw [hκ]
    linear_combination e / 2
  refine ⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_,
    GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩
  · obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨β, -, hend, -⟩ := hβ
    obtain ⟨W, hW, hWv⟩ := hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
    have hP₀ := GlobalTheory.T.ellipticCurve_lattice_baseChange_stable _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀
    refine ⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩
    refine LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0)
      hP₀.2.2.1 hW hWv ?_
    have e := congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)
    rwa [map_add, map_mul, map_natCast] at e
  · obtain ⟨c, hc0, hc⟩ := hc
    refine lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_
    rw [hc, hκ]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, n, rfl⟩ := hgen a
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * w, by simp⟩
  · exact ⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_rankOneCuspLatticeData_of_principal : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M → ∀ k : (T.U j σ).Comp, ∃ Xx : ReciprocityTheory.ChartRestriction.G.FD.DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D ∧ (Xx.NA : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ∧ Xx.NC ≤ Ideal.absNorm D.host.ccK := by
  first | exact @GlobalTheory.LatticeData.exists_dataX_of_hasPrinc | exact GlobalTheory.LatticeData.exists_dataX_of_hasPrinc | (intros; apply GlobalTheory.LatticeData.exists_dataX_of_hasPrinc <;> assumption)
end
