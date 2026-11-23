module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle070
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle081
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle111
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle205
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YCompOf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MarkFibre

theorem exists_fibre_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  intro E _ _ _ H S₁ S₂ V t₁ t₂ tV f₁ f₂ m₁ m₂ x y₁ y₂ h₁ h₂
  subst h₁ h₂
  have hw₁ : m₁.cm.F ≫ t₁.G.hom = tV.G.hom ≫ f₁ := m₁.cart.1.w
  have hw₂ : m₂.cm.F ≫ t₂.G.hom = tV.G.hom ≫ f₂ := m₂.cart.1.w
  obtain ⟨e₁, he₁, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₁ 0 x (x ≫ f₁) rfl
  obtain ⟨e₂, he₂, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₂ 0 x (x ≫ f₂) rfl
  have mul₁ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₁ (a * b) = Out.toBase hw₁ a * Out.toBase hw₁ b :=
    fun T a b => Over.OverMorphism.ext (m₁.cart.2 T a b (Out.toBase hw₁ a) (Out.toBase hw₁ b) rfl rfl).symm
  have mul₂ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₂ (a * b) = Out.toBase hw₂ a * Out.toBase hw₂ b :=
    fun T a b => Over.OverMorphism.ext (m₂.cart.2 T a b (Out.toBase hw₂ a) (Out.toBase hw₂ b) rfl rfl).symm
  have b₁ : ∀ p, Out.toBase hw₁ (e₁ p) = p := fun p => Over.OverMorphism.ext (he₁ p)
  have b₂ : ∀ p, Out.toBase hw₂ (e₂ p) = p := fun p => Over.OverMorphism.ext (he₂ p)
  have key : ∀ q, e₁ ((e₂.trans e₁.symm) q) = e₂ q := fun q => e₁.apply_symm_apply _
  refine ⟨(e₂.trans e₁.symm).toEquiv, fun q q' => map_mul (e₂.trans e₁.symm) q q', fun q =>
    ⟨(e₂ q).left, Over.w (e₂ q), he₂ q, ?_⟩, fun N q q' ζ h => ?_⟩
  · have := he₁ ((e₂.trans e₁.symm) q)
    rw [key] at this
    exact this
  · have ha : e₂ q ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.1).trans (map_one e₁)
    have ha' : e₂ q' ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.2.1).trans (map_one e₁)
    obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil tV.cub ha ha'
    have c₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₁ _ _ m₁.cm hw₁ mul₁ _ _ t₁.cub tV.cub m₁.lin N _ _ _ ζ' hζ'
    have c₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₂ _ _ m₂.cm hw₂ mul₂ _ _ t₂.cub tV.cub m₂.lin N _ _ _ ζ' hζ'
    rw [b₂, b₂] at c₂
    rw [← key q, ← key q', b₁, b₁] at c₁
    obtain rfl : ζ' = ζ := c₁.unique h
    exact c₂

end GlobalTheory.CompanionTheory.Ar.MarkFibre
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.block_extension_arith_var : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | exact GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcLie

theorem mem_eigSp_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {O : Type} [CommRing O]
    (ρ : O →+* Module.End R V) (σ : O →+* R) (e : V) :
    e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_lie_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J y 𝔐 y₀ cst₀ y₁ hy hy₁ hs₀ hcst
  classical
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).2 inferInstance
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀
  obtain ⟨ρ₀, hρ₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hsl, hli, -, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m 𝔐.Ω₀ Ω 𝔐.ξ₀ 𝔐.ξ 𝔐.fn Li₀ 𝔐.Li M₀ 𝔐.M
    𝔐.gen₀ 𝔐.tie.gen 𝔐.fn_over
  obtain ⟨m₀, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_sabMap_id E H Y.X Y.t
  obtain ⟨hfd₀, hrk₀⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y Y.X 𝔐.Ω₀ 𝔐.ξ₀ (𝟙 _) y₁ Y.t m₀ Li₀ M₀ ρ₀ cst₀
    (by rw [Category.comp_id]; exact hy₁) (by rw [Category.id_comp]; exact hs₀) hρ₀
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y 𝔐.X Ω 𝔐.ξ 𝔐.f y₀ 𝔐.t 𝔐.m 𝔐.Li 𝔐.M 𝔐.ρ 𝔐.cst hy 𝔐.cst_over 𝔐.act
  have hρj : ∀ (a : 𝓞 E) e, j (ρ₀ a e) = 𝔐.ρ a (j e) := by
    intro a e
    apply 𝔐.M.inj
    refine Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ?_)
    · rw [hj, hρ₀ a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc,
        ← Category.assoc (𝔐.M.pt (j e)).left]
      exact congrArg (· ≫ (Y.t.act.act a).left) (hj e).symm
    · rw [Over.w, Over.w]
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun v hv => by_contra fun h0 => ?_
    exact (hli 1 (fun _ => v) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hv
  have hσ : ∀ s (a : 𝓞 E), 𝔐.fn ((cst₀.comp (labelEmb c s)) a) = 𝔐.emb s a := by
    intro s a
    show (𝔐.fn.comp cst₀) (labelEmb c s a) = 𝔐.cst (labelEmb c s a)
    rw [hcst]
  let V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀ := fun s => eigSp ρ₀ (cst₀.comp (labelEmb c s))
  have hV : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s := by
    intro s e
    show e ∈ eigSp ρ₀ _ ↔ j e ∈ eigSp 𝔐.ρ _
    rw [mem_eigSp_iff, mem_eigSp_iff]
    refine forall_congr' fun a => ?_
    rw [← hρj, ← hσ, ← hsl]
    exact hinj.eq_iff.symm
  let B : ∀ s, Module.Basis (Fin (labelRk D s)) 𝔐.Ω₀ (V₀ s) := fun s => Module.finBasisOfFinrankEq _ _ (hrk₀ s)
  let b : ∀ s, Fin (labelRk D s) → Li₀ := fun s k => (B s k : Li₀)
  have hbli : ∀ s, LinearIndependent 𝔐.Ω₀ (b s) := fun s =>
    (B s).linearIndependent.map' (V₀ s).subtype (Submodule.ker_subtype _)
  have hbsp : ∀ s, Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s := by
    intro s
    have h : Set.range (b s) = (V₀ s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h, ← Submodule.map_span, (B s).span_eq, Submodule.map_top, Submodule.range_subtype]
  have hjli : ∀ s, LinearIndependent Ω fun k => j (b s k) := fun s => hli _ _ (hbli s)
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, V₀, b, hj, hsl, hV, fun s => ⟨hbli s, hbsp s⟩, hjli, fun s => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (hV s _).1 ((hbsp s) ▸ Submodule.subset_span ⟨k, rfl⟩)
  · rw [finrank_span_eq_card (hjli s), Fintype.card_fin]
    exact (hrk s).symm

end GlobalTheory.CompanionTheory.Ar.HcLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

theorem exchange {F W : Type} [Field F] [AddCommGroup W] [Module F W] {n : ℕ} {t u : Fin n → W}
    (ht : LinearIndependent F t) (h : Submodule.span F (Set.range t) = Submodule.span F (Set.range u)) :
    LinearIndependent F u ∧ ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, t i = ∑ k, A i k • u k) ∧ IsUnit A.det := by
  have hu : LinearIndependent F u := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have := linearIndependent_iff_card_eq_finrank_span.1 ht
    rw [Set.finrank, ← h]
    exact this
  refine ⟨hu, ?_⟩
  have h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose A hA using h1
  choose B hB using h2
  have hAB : (Matrix.of A) * (Matrix.of B) = 1 := by
    ext i l
    have key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0 := by
      have e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i := by
        conv_rhs => rw [← hA i]
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      have e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i := by
        simp [Matrix.one_apply]
      simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
    have := Fintype.linearIndependent_iff.1 ht _ key l
    exact sub_eq_zero.1 this
  refine ⟨Matrix.of A, fun i => (hA i).symm, ?_⟩
  have := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_value_frame (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U)
    (hβ : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (τ : E →+* ℂ) (F : Type) [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (n : ℕ) (b : Fin n → Z.V)
    (hb : (Z.eig τ).IsFrameAt b ⟨centre (y ≫ Y.j), h⟩) (v : Vecs y n)
    (hv : IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v) :
    ∃ (v₀ : Vecs y n) (A : Matrix (Fin n) (Fin n) F),
      IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v₀ ∧
      (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v₀ i) v') ∧
      (∀ i, IsComb (A i) v₀ (v i)) ∧ IsUnit A.det := by
  obtain ⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩ := GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y F y
  obtain ⟨m, e, cf, h1, h2⟩ := GlobalTheory.T.eigen_projector_field_embedding E c.F (tauIn c τ)
  obtain ⟨u, hval, hspan⟩ := GlobalTheory.T.lie_model_action_specialize Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF
    (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ hy h) h1
    (h2 Z.Ω Z.V Z.inc Z.ρ) hb
  choose t ht using fun i => Mu.onto _ (hv.1 i).1
  have hvt : v = fun i => Mu.pt (t i) := funext fun i => (ht i).symm
  subst hvt
  obtain ⟨hti, hts⟩ := (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv
  obtain ⟨hui, A, hA, hAu⟩ := exchange hti (hts.trans hspan.symm)
  refine ⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩,
    fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩

theorem valAt_mul {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, hu, rfl⟩ := ha
  obtain ⟨_, w, hw, rfl⟩ := hb
  exact ⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩

theorem valAt_eq {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

theorem exists_eq_smul_wedge {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {x : Cpt ξ} {p : ℕ} {f : Fin p → V}
    (hf : L.IsFrameAt f x) {α : Ω} {a : ⋀[Ω]^p V} (hα : α ≠ 0)
    (hL : L.wedge p x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ g₀ : Ω, a = g₀ • exteriorPower.ιMulti Ω p f := by
  have hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x :=
    Submodule.subset_span ⟨f, fun i => by
      rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  have hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f := by
    rw [mul_smul]; exact hr
  have hne := WedgeFrame.wedge_ne_zero f hf.1
  have h0 : (r : Ω) * α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr'; exact hne hr'.symm
  exact ⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

namespace GlobalTheory.CompanionTheory.Ar.Flat

open RepScalar

theorem exists_const_of_flatOnModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'
  obtain ⟨-, a, b, hgen, hrep⟩ := hfl
  obtain ⟨-, a', b', hgen', hrep'⟩ := hfl'
  obtain ⟨x, s, t, hx, ht, hst, ha', hb'⟩ := GlobalTheory.T.line_generator_geometric E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'
  refine ⟨x, hx, fun F _ βF y v w hf => ?_⟩
  obtain ⟨hy, hU, hv, hw⟩ := id hf
  have hpt : y (IsLocalRing.closedPoint F) ∈ U := hU ⟨_, rfl⟩
  have hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := ((Z.closure _).1 hpt).map Y.j.continuous
  have hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨U₁, hU₁, b₁, -, hb₁⟩ := h1 _ hmem
  obtain ⟨U₂, hU₂, b₂, -, hb₂⟩ := h2 _ hmem
  have f₁ := hb₁ _ hmem hU₁
  have f₂ := hb₂ _ hmem hU₂
  obtain ⟨v₀, A, hv₀, hval₁, hA, hAu⟩ := exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv
  obtain ⟨w₀, B, hw₀, hval₂, hB, -⟩ := exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw
  have hf₀ : IsFramed U τ βF y v₀ w₀ := ⟨hy, hU, hv₀, hw₀⟩
  obtain ⟨-, hb0, hco⟩ := hgen
  obtain ⟨α, κ, hα, hκ, hWa, hWb, -⟩ := hco _ hmem
  obtain ⟨ga, hga⟩ := exists_eq_smul_wedge f₁ hα hWa
  obtain ⟨gb, hgb⟩ := exists_eq_smul_wedge f₂ hκ hWb
  have hgb0 : gb ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hgb, zero_smul])
  have r1 := hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂
  have r2 := hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul])
    (by rw [hb', hgb, smul_smul]) hval₁ hval₂
  have r3 := valAt_mul (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1
  have e : s * ga / (t * gb) = Z.inc x * (ga / gb) := by
    rw [hst]; field_simp
  rw [e] at r2
  have e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀ := valAt_eq Z.gen r2 r3
  have c1 := hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  have c2 := hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  refine hAu.mul_left_injective ?_
  show φ' F y v w * A.det = βF x * φ F y v w * A.det
  rw [c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.pullback_frames_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | exact GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_dvr_through_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_comp_of | exact PositivityTheory.UnitarySelfGeneration.y_comp_of
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  first | exact @PositivityTheory.Xgf.cm_image_unique_lattice | exact PositivityTheory.Xgf.cm_image_unique_lattice
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem _root_.GlobalTheory.T.isValFam_of_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) (y' : Sp F' ⟶ Xo.XF c), y' = spMap f ≫ y → ∀ (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (v' : Vecs y' n), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsValFam Z y b v → IsValFam Z y' b v' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.isValFam_spMap | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.isValFam_spMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.isValFam_spMap <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem sigma_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev hG la T io e y evT zT t hI zV hR s
  have hgen := Or.𝔐.tie.gen
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom _ _ Or.𝔐.ξ T.V zV hsp hgen
  have hm : ∀ a : 𝓞 E, Or.𝔐.emb s a ∈ regAt Or.𝔐.ξ ⟨centre zV, hsp⟩ := fun a =>
    HodgeBasic.mem_regAt_of_isIntegral hgen Or.𝔐.all Or.𝔐.normal _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (Or.𝔐.emb s).toIntAlgHom)
  let σ : 𝓞 E →+* T.V := φ.comp ((Or.𝔐.emb s).codRestrict _ hm)
  have hv : ∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a) := fun a => (hφ _ _).2 ⟨hm a, rfl⟩
  refine ⟨σ, hv, fun a => ?_⟩
  have hA : Or.𝔐.cst (labelEmb c s a) ∈ A := hG.1 _
  have h1 := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) (hv a)
  have h2 : GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (evT ⟨_, hA⟩) := hR ⟨_, hA⟩
  have h5 : evT ⟨_, hA⟩ = io (labelEmb c s a) := hI.2.2.2.2.1 _ hA
  exact (LieTangent.valAt_unique hgen h1 h2).trans h5

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem inFibre_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev _ _ hGood la T io e y evT zT t hInt zV hR hu
  obtain ⟨-, -, hinv⟩ := hu
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 hinv
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hv : ValAt Or.𝔐.ξ zV ((p : RM.Ω)⁻¹) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨Or.𝔐.all _, s, hs, rfl⟩
  have hv' := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) hv
  have hcst : Or.𝔐.cst ((p : c.F)⁻¹) = (p : RM.Ω)⁻¹ := by simp
  have hmem := hGood.1 ((p : c.F)⁻¹)
  have hla : (p : 𝓞 c.F) ∈ la.asIdeal := hInt.1
  have hOver : OverLa la T.V io e := hInt.2.1
  have hev : evT ⟨_, hmem⟩ = io ((p : c.F)⁻¹) := hInt.2.2.2.2.1 _ hmem
  have hr := hR ⟨_, hmem⟩
  rw [hev] at hr
  change ValAt _ _ (Or.𝔐.cst ((p : c.F)⁻¹)) _ at hr
  rw [hcst] at hr
  have heq := LieTangent.valAt_unique hgen hv' hr
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : la.valuation c.F (p : c.F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (la.valuation_lt_one_iff_mem _).2 hla
  have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 < vLa la (p : c.F) := by unfold vLa; omega
  have h4 : 0 < vV T.V (io (p : c.F)) := by
    rw [hOver.2]
    exact mul_pos (by exact_mod_cast hOver.1) h3
  have h5 : vV T.V (io ((p : c.F)⁻¹)) = - vV T.V (io (p : c.F)) := by
    simp [vV, map_inv₀]
  have h6 := ReciprocityTheory.ChartRestriction.G.PullbackSections.vV_alg_nonneg T ((Scheme.stalkClosedPointTo zV).hom s)
  rw [heq, h5] at h6
  omega

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
