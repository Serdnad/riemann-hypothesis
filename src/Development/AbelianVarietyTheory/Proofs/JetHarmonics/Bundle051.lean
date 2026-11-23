module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_ringHom_ringOfIntegers_lift {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, hf⟩

theorem exists_types_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  intro E _ _ _ H l c T io p _ X
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ =>
    exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a)) := by
    intro τ a
    rw [← X.comp, hσV']
  have key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a) := by
    intro τ τ' a
    constructor
    · intro h
      have h1 : embK c τ a = embK c τ' a := by
        apply Subtype.ext
        rw [embK_coe, embK_coe]
        exact h
      have h2 : σV τ a = σV τ' a := hinj (by rw [hσV', hσV', h1])
      rw [h2]
    · intro h
      have h1 : embK c τ a = embK c τ' a :=
        io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))
      exact congrArg (fun z : c.F => (z : ℂ)) h1
  refine ⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩
  · intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact (key τ τ' a).2 (RingHom.congr_fun h a)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    exact hinj (by rw [hσV', hσV', h])

end GlobalTheory.CharDepth
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  first | exact @GlobalTheory.comatrix_picks_eigencomponent | exact GlobalTheory.comatrix_picks_eigencomponent | (intros; apply GlobalTheory.comatrix_picks_eigencomponent <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  first | exact @GlobalTheory.CapelliCasimir.cas_of_capelli | exact GlobalTheory.CapelliCasimir.cas_of_capelli | (intros; apply GlobalTheory.CapelliCasimir.cas_of_capelli <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDer

variable {R : Type} [CommRing R]

theorem exists_jet_factor {κ A : Type} [Finite κ] [CommRing A] [Algebra R A] (T : MvPowerSeries κ R →ₐ[R] A)
    (hT : ∀ p, IsNilpotent (T (X p))) :
    ∃ (n : ℕ) (Θ : JetR R κ (n + 1) →ₐ[R] A), ∀ g, Θ (toJet (n + 1) g) = T g := by
  let J : Ideal A := Ideal.span (Set.range fun p => T (X p))
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hn : IsNilpotent J := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 (by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hT p)
  obtain ⟨n, hn⟩ := hn
  have hJ : J ^ (n + 1 + 1) = ⊥ := by
    rw [add_assoc, pow_add, hn, zero_mul, Ideal.zero_eq_bot]
  have hm : ∀ p, T (X p) ∈ J := fun p => Ideal.subset_span ⟨p, rfl⟩
  refine ⟨n, jetLift R J hJ (fun p => T (X p)) hm, fun g => ?_⟩
  have h := GlobalTheory.algHom_sub_aeval_truncTotal_mem T hm (n + 1 + 1) g
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
  exact h.symm

theorem exists_trunc_one {G : Over (Spec (CommRingCat.of R))} {κ : Type} (x : Fam G κ)
    (hx : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) (n : ℕ) :
    ∃ t : JetR R κ (n + 1) →ₐ[R] JetR R κ 1, (∀ j, t (zR (n + 1) j) = zR 1 j) ∧ spMap t ≫ x (n + 1) = x 1 := by
  induction n with
  | zero =>
    refine ⟨AlgHom.id R _, fun _ => rfl, ?_⟩
    have : spMap (R₀ := R) (AlgHom.id R (JetR R κ 1)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [spMap_left]
      exact Spec.map_id _
    rw [this, Category.id_comp]
  | succ n ih =>
    obtain ⟨t, h1, h2⟩ := ih
    refine ⟨t.comp (jetTruncR R κ (n + 1)), fun j => h1 j, ?_⟩
    rw [← spMap_comp, Category.assoc, hx, h2]

theorem subst_map_algebraMap {σ τ S : Type} [Finite σ] [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (MvPowerSeries.map (algebraMap R S) f) = subst a f := by
  rw [map_algebraMap_eq_subst_X, subst_comp_subst_apply HasSubst.X ha]
  congr 1
  funext s
  exact subst_X ha s

def tanPair (d : ℕ) (v : Fin d → R) : Fin 2 × Fin d → PS (DualNumber R) 1 d := fun p =>
  (![pt (DualNumber R) d 0, fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)] :
    Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2

theorem inr_nilpotent (r : R) : IsNilpotent (TrivSqZeroExt.inr r : DualNumber R) :=
  ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩

theorem hasSubst_tanPair (d : ℕ) (v : Fin d → R) : HasSubst (tanPair d v) := by
  apply hasSubst_of_constantCoeff_nilpotent
  rintro ⟨j, i⟩
  fin_cases j
  · simp [tanPair, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simpa [tanPair] using inr_nilpotent (v i)

theorem ev_pt_pt {d : ℕ} (g : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] g = g := by
  have : (fun p : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [this, subst_self, id]

theorem subst_tanPair_fst {d : ℕ} (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) = MvPowerSeries.map (algebraMap R (DualNumber R)) f := by
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt])
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), map_algebraMap_eq_subst_X]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  exact subst_X (hasSubst_tanPair d v) ((0 : Fin 2), i)

theorem subst_tanPair_add {d : ℕ} (Gl : FGLaw R d) (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof Gl.F v f) := by
  have hF : addOf (n := 2) Gl.F (pt R d 0) (pt R d 1) = Gl.F := funext fun i => ev_pt_pt _
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      exact Gl.const i)
  have e : (fun p : Fin 1 × Fin d => subst (tanPair d v) ((![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2)) =
      fun p : Fin 1 × Fin d => (![addOf (Gl.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))] : Fin 1 → Pt (DualNumber R) 1 d) p.1 p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact (subst_map_algebraMap (hasSubst_tanPair d v) (Gl.F i)).symm
  have hc := ha.comp (hasSubst_tanPair d v)
  simp only [substAlgHom_apply] at hc
  rw [← GlobalTheory.Jets.ev_addOf_eps, hF]
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), ← e, subst_map_algebraMap hc]

theorem dof_eq_of_eigen : JetAlgSt → RepSt → SerSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ Gl : FGLaw R d, IsLawOf x Gl.F → ∀ (U : G.left.Opens), ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ (s : Γ(G.left, U)) (f : PS R 1 d), IsSer1 x U s f → ∀ (v : Fin d → R) (y : R) (φ : JetR R (Fin d) 1 →ₐ[R] DualNumber R), (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i)) → (∀ (A : Type) [CommRing A] [Algebra R A] (c : DualNumber R →ₐ[R] A) (r : sp (R₀ := R) A ⟶ G), ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap c ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U → fnVal (r * (spMap c ≫ spMap φ ≫ x 1)).left U s = c (1 + TrivSqZeroExt.inr y) * fnVal r.left U s) → Dof Gl.F v f = C y * f := by
  intro _ hRep _ R _ G _ d x hx Gl hl U _ s f hf v y φ hφ H
  have hb := hasSubst_tanPair d v
  have hpt : ∀ (k : Fin 2) (j : Fin d), constantCoeff (pt R (n := 2) d k j) = 0 := fun k j => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  obtain ⟨y₁, hy₁, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 0) (hpt 0)
  obtain ⟨y₂, hy₂, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 1) (hpt 1)
  have s₁ := hf 2 _ _ hy₁
  have s₁₂ := hf 2 _ _ (hl.2 2 _ _ _ _ hy₁ hy₂)
  have key : subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      C (1 + TrivSqZeroExt.inr y : DualNumber R) * subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) := by
    refine eq_of_toJet_eq fun m => ?_
    let T : PS R 2 d →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m :=
      ((toJetHom (DualNumber R) (Fin 1 × Fin d) m).restrictScalars R).comp (substAlgHom hb)
    have hT : ∀ g, T g = toJet m (subst (tanPair d v) g) := fun g => by
      rw [← substAlgHom_apply hb]; rfl
    let c : DualNumber R →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m := IsScalarTower.toAlgHom R _ _
    have hc : ∀ a, toJet m (C a : PS (DualNumber R) 1 d) = c a := fun a =>
      (toJetHom (DualNumber R) (Fin 1 × Fin d) m).commutes a
    have hT1 : ∀ i, T (X ((1 : Fin 2), i)) = c (TrivSqZeroExt.inr (v i)) := fun i => by
      rw [hT, subst_X hb, ← hc]; rfl
    have hT0 : ∀ i, T (X ((0 : Fin 2), i)) = zR m ((0 : Fin 1), i) := fun i => by
      rw [hT, subst_X hb, ← toJet_X]; rfl
    obtain ⟨n, Θ, hΘ⟩ := exists_jet_factor T (by
      rintro ⟨j, i⟩
      fin_cases j
      · refine hT0 i ▸ ⟨m + 1, ?_⟩
        have := Ideal.pow_mem_pow (zR_mem_ker (R := DualNumber R) m ((0 : Fin 1), i)) (m + 1)
        rwa [ker_jetAug_pow, Ideal.mem_bot] at this
      · exact hT1 i ▸ (inr_nilpotent (v i)).map c)
    obtain ⟨t, ht, htx⟩ := exists_trunc_one x hx.1 n
    obtain ⟨ψ, hψ, hψy⟩ := hy₂.2 (n + 1)
    have e₂ : spMap c ≫ spMap φ ≫ x 1 = spMap Θ ≫ y₂ (n + 1) := by
      have : c.comp (φ.comp t) = Θ.comp ψ := jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, ht, hφ, hψ, hΘ]
        exact (hT1 j).symm
      rw [hψy, ← htx, ← Category.assoc (spMap φ), spMap_comp, ← Category.assoc, spMap_comp, this,
        ← Category.assoc, spMap_comp]
    have e : (spMap Θ ≫ y₁ (n + 1)) * (spMap c ≫ spMap φ ≫ x 1) = spMap Θ ≫ (y₁ (n + 1) * y₂ (n + 1)) := by
      rw [e₂, MonObj.comp_mul]
    have h := H _ c (spMap Θ ≫ y₁ (n + 1)) (top_le_preimage_comp _ _ U (s₁ (n + 1)).1)
      (by rw [e]; exact top_le_preimage_comp _ _ U (s₁₂ (n + 1)).1)
    have v₁ := fnVal_specMap Θ.toRingHom _ U (s₁ (n + 1)).1 s
    have v₁₂ := fnVal_specMap Θ.toRingHom _ U (s₁₂ (n + 1)).1 s
    rw [(s₁ (n + 1)).2] at v₁
    rw [(s₁₂ (n + 1)).2] at v₁₂
    rw [e] at h
    have h' := v₁₂.symm.trans (h.trans (congrArg (c (1 + TrivSqZeroExt.inr y) * ·) v₁))
    rw [← toJetHom_apply m (C _ * _), map_mul, toJetHom_apply, toJetHom_apply, hc, ← hT, ← hT, ← hΘ, ← hΘ]
    exact h'
  rw [subst_tanPair_add, subst_tanPair_fst] at key
  ext e
  have := congrArg (fun g => TrivSqZeroExt.snd (coeff e g)) key
  simp only [map_add (coeff e), coeff_C_mul, coeff_map] at this
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.EigenDer
end
end

section

noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
namespace GlobalTheory.JetSer

theorem toJet_one_eq {O κ : Type} [CommRing O] [Fintype κ] (u : MvPowerSeries κ O) :
    toJet 1 u = Ideal.Quotient.mk _ (MvPolynomial.C (constantCoeff u) +
      ∑ q, MvPolynomial.C (coeff (Finsupp.single q 1) u) * MvPolynomial.X q) := by
  classical
  refine (toJet_eq_mk_iff 1 u _).2 fun a ha => ?_
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.degree a = 0
  · rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    simp [Finsupp.single_eq_zero]
  · have h1 : a ∈ {d : κ →₀ ℕ | Finsupp.degree d = 1} := by
      show Finsupp.degree a = 1
      omega
    rw [← Finsupp.range_single_one] at h1
    obtain ⟨q, rfl⟩ := h1
    rw [if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_add, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      rwa [Finsupp.single_left_inj one_ne_zero]
    · simp

theorem constantCoeff_dof {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) :
    constantCoeff (Dof (G.mapF f) e u) =
      ∑ j, e j * coeff (Finsupp.single ((0 : Fin 1), j) 1) u := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt O d 0, 0]
      (MvPowerSeries.pderiv (R := O) ((1 : Fin 2), i) (G.mapF f j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_zero_right,
      Finsupp.embDomain_zero, coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, SymbolOne.coeff_law]
    split_ifs <;> simp
  unfold Dof

  simp only [map_sum, map_mul, h, constantCoeff_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem dualNumber_value_toJet : ∀ (R O : Type) [CommRing R] [CommRing O] (f : R →+* O) (d : ℕ) (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) (S : Type) [CommRing S] [Algebra O S] (ψ : JetR O (Fin 1 × Fin d) 1 →ₐ[O] DualNumber S), (∀ q, ψ (zR 1 q) = TrivSqZeroExt.inr (algebraMap O S (e q.2))) → ψ (toJet 1 u) = TrivSqZeroExt.inl (algebraMap O S (MvPowerSeries.constantCoeff u)) + TrivSqZeroExt.inr (algebraMap O S (MvPowerSeries.constantCoeff (Dof (G.mapF f) e u))) := by
  intro R O _ _ f d G e u S _ _ ψ hψ
  have hC : ∀ c : O, ψ (Ideal.Quotient.mk _ (MvPolynomial.C c)) = TrivSqZeroExt.inl (algebraMap O S c) :=
    fun c => ψ.commutes c
  have hX : ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      TrivSqZeroExt.inr (algebraMap O S (e q.2)) := hψ
  rw [toJet_one_eq, constantCoeff_dof]

  simp only [map_add (f := _), map_sum, map_mul, hC, hX, Fintype.sum_prod_type, Fin.sum_univ_one]
  congr 1
  ext
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, mul_comm]
    simp only [Algebra.smul_def]

end GlobalTheory.JetSer
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxLinear

open GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
  {Z : Scheme.{0}}

theorem ext_val {D : DegPre R} {S T : Fam D F k}
    (h : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      sval (S.s α) (𝟙 _) y J = sval (T.s α) (𝟙 _) y J) : S = T := by
  refine fam_ext fun α jj => fn_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  refine (sec_trans (S.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans
    (Eq.trans (congrArg _ (h α y J hJ)) (sec_trans (T.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).symm)

theorem sval_add {D : DegPre R} (S T : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((S + T).s α) q y J = sval (S.s α) q y J + sval (T.s α) q y J :=
  gs_add q y _ (hJ.mem _ q) _ _

theorem sval_smul {D : DegPre R} (c : F) (S : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((c • S).s α) q y J = gs (X := Spec (CommRingCat.of F)) (q ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * sval (S.s α) q y J := by
  refine (gs_mul q y _ (hJ.mem _ q) _ _).trans (congrArg (· * _) ?_)
  exact (gs_res q y le_top (hJ.mem _ q) _).trans (gs_pull q (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem prB_fst (i : Fin j) : prB pD F i ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D'.P.A).left :=
  congrArg (fun g => g.left) (whiskerLeft_fst (TF (R := R) F) (pD.pw.pr i))

theorem box_val {S : Fam D' F k} {s : Fin j → Fam D F k} (h : IsBoxFam pD F k S s) (α' : D'.X)
    (y : (DegPre.BF D' F).left) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a).val * sval (S.s α') (𝟙 _) y J' =
      ∏ i, sval ((s i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J := by
  obtain ⟨hφ, H⟩ := h α'
  exact boxPull_val (w := pD.w) (hφ := hφ) (s := fun i => (s i).s (pD.xe α' i)) H (𝟙 _) y hJ hJ'

theorem prod_update {A S : Type*} [CommMonoid S] {j : ℕ} [DecidableEq (Fin j)] (g : Fin j → A → S) (s : Fin j → A)
    (i : Fin j) (x : A) :
    ∏ l, g l (Function.update s i x l) = g i x * ∏ l ∈ Finset.univ.erase i, g l (s l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun l hl => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem box_unique {S T : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    (hT : IsBoxFam pD F k T s) : S = T :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    exact (Units.mul_right_inj _).1 ((box_val pD hS α y hJ hJ').trans (box_val pD hT α y hJ hJ').symm)

theorem box_add [DecidableEq (Fin j)] {S S₁ S₂ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {a b : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (a + b))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a))
    (h₂ : IsBoxFam pD F k S₂ (Function.update s i b)) : S = S₁ + S₂ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    have e₂ := (box_val pD h₂ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_add _ _ _ _ _ hJ, sval_add _ _ _ _ _ hJ', mul_add, add_mul, e₁, e₂]

theorem box_smul [DecidableEq (Fin j)] {S S₁ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {c : F} {a : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (c • a))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a)) :
    S = c • S₁ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_smul _ _ _ _ _ hJ, sval_smul _ _ _ _ _ hJ', Category.assoc, prB_fst, mul_left_comm, e₁,
      _root_.mul_assoc]

end GlobalTheory.BoxLinear

namespace GlobalTheory

theorem exists_boxFam_multilinear : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  choose bx hbx using BoxFamily.exists_isBoxFam hG R j D D' pD F k
  refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact BoxLinear.box_unique pD h (hbx s)
  · rw [h]; exact hbx s

end GlobalTheory
end
