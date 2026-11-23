module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormula
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLineIdempotentSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle169
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle221
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle159
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle227
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.EqMulInversePow
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle228
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle226
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle036
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem units_mul_relation_rearrange_commRing {Q : Type} [CommRing Q] (D F V : Q) (h : D * D = 0) :
    (1 + D * F) * (1 + D * (V - F)) = 1 + D * V := by
  linear_combination (F * (V - F)) * h



theorem pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (gs : Germ.PS k 2 d), AxOne gs → pow1 g.B p = Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] gs → ∀ y : Tm x p ⟶ t.G, y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ (∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) ∧ ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∀ m : ℕ, ∃ v : Jet k (Fin 1 × Fin d) m, ∀ h : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀), ((rQ t.G x p (g.x m)).appLE _ ⊤ h).hom (C.s fun _ => j₀).val = toΓ _ (1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p))) := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w gs hax hpow y hy hy0 hyp
  obtain ⟨κ, hκ, hκ2, hκ3⟩ := GlobalTheory.T.line_bundle_generator_correspondence E H hstar X0 t p
  have hy1 : spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ y.left =
      spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ (1 : Tm x p ⟶ t.G).left := by
    have e₁ := congrArg (fun q => q.left) hy0
    have e₂ : homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ (1 : Tm x p ⟶ t.G) = 1 := by simp [Hom.one_def]
    exact e₁.trans (congrArg (fun q => q.left) e₂).symm
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.T.line_bundle_section_difference_generator t.G.left t.PP.L t.PP.isLB k p y.left (1 : Tm x p ⟶ t.G).left hy1
  obtain ⟨C, hC, hCv⟩ := GlobalTheory.T.frobenius_torsion_generator_relation E H X0 t k x p y hyp κ hκ τ hτ
  refine ⟨C, hC, GlobalTheory.T.frobenius_generator_correspondence E H X0 t k x p y hy0 κ hκ2 τ hτ1 C hCv, fun j₀ hj₀ m => ?_⟩
  obtain ⟨u, hu, hκ3'⟩ := hκ3 k x d g (p + m + 1)
  obtain ⟨e₀, he₀, hve⟩ := GlobalTheory.T.germ_jet_unit_on_chart E H X0 t k p x d g w m j₀ hj₀
  obtain ⟨τ₀, hτ₀, hvτ⟩ := GlobalTheory.T.jet_section_generator_value E H X0 t k x p y (Jet k (Fin 1 × Fin d) m) hy0 τ hτ1 j₀ hj₀
  have hp0 : ((p : ℕ) : Jet k (Fin 1 × Fin d) m) = 0 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    rw [← map_natCast (algebraMap k (Jet k (Fin 1 × Fin d) m)), this, map_zero]
  obtain ⟨v, hv⟩ := GlobalTheory.T.jet_augmentation_one_pth_power (Jet k (Fin 1 × Fin d) m) p hp0 ((e₀ * τ₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) (by
    rw [Units.val_mul, map_mul, he₀, hτ₀, _root_.one_mul])
  refine ⟨v, fun h => ?_⟩
  have hju : jq w p m (u : Jet k (Fin 2 × Fin d) (p + m + 1)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p)) := by
    rw [hu, hpow]
    exact GlobalTheory.T.germ_jet_quotient_formula k p d m w gs hax
  let f : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p := (jq w p m : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] _)
  let ν : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := Units.map (f : _ →* Jet (Jet k (Fin 1 × Fin d) m) Unit p) u
  let U : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := ν⁻¹ * (e₀ * τ₀) ^ p
  have hU : (U : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = 1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) := by
    have h2p : dQ (Jet k (Fin 1 × Fin d) m) p ^ p * dQ (Jet k (Fin 1 × Fin d) m) p ^ p = 0 := by
      rw [← pow_add]
      exact pow_eq_zero_of_le (by have := (Fact.out : p.Prime).one_lt; omega) (dQ_pow _ p)
    have e := units_mul_relation_rearrange_commRing (dQ (Jet k (Fin 1 × Fin d) m) p ^ p) (algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p))) (algebraMap _ _ (v ^ p)) h2p
    rw [← hju, ← hv, ← RingHom.map_sub (algebraMap (Jet k (Fin 1 × Fin d) m) (Jet (Jet k (Fin 1 × Fin d) m) Unit p))] at e
    show ((ν⁻¹ * (e₀ * τ₀) ^ p : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← e]
    exact Units.inv_mul_cancel_left ν _
  have hval : ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p))
      (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) →
      val C (rQ t.G x p (g.x m)) z J = gm (𝟙 _) z ⊤ (unitΓ U) := by
    intro z J hJ hJ₀
    have hk : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
        gm (𝟙 _) z ⊤ (unitΓ ν) * (gm (𝟙 _) z ⊤ (unitΓ e₀) ^ p)⁻¹ := by
      have e₁ : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
          val (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left) (homAt x (jq w p m)).left z J := by
        rw [GlobalTheory.T.germ_torsion_lift_compat E H X0 t k p x d g w m y hy]
        exact (val_pull hJ _ _ _).symm
      refine e₁.trans ((val_corr hJ hκ3' _).trans ((Pf.val_scale t _ _ _ _ _ z hJ).trans ?_))
      refine (congrArg (gm (spMap f) z ⊤ (unitΓ u) * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (GlobalTheory.T.germ_frobenius_torsion_section E H hstar X0 t k p x d g w m (hy ▸ hyp) z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹)
          ((Pf.val_genPow t _ _ _ p _ z J).trans (congrArg (· ^ p) (hve z J hJ hJ₀)))))))).trans ?_
      rw [_root_.one_mul]
      exact congrArg (· * _) (Pf.gm_spMap f u z)
    have ht : val τ (rQ t.G x p (g.x m) ≫ (fst (Tm x p) t.G).left) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
      rw [rQ_fst]
      exact hvτ z J hJ hJ₀
    rw [hCv _ _ z J hJ, hk, ht]
    let Φ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ →* ((Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)).presheaf.stalk z)ˣ :=
      (gm (𝟙 _) z ⊤).comp (Units.map (toΓ _).toMonoidHom)
    show (Φ ν * (Φ e₀ ^ p)⁻¹)⁻¹ * Φ τ₀ ^ p = Φ (ν⁻¹ * (e₀ * τ₀) ^ p)
    rw [map_mul Φ, map_inv Φ, map_pow Φ, map_mul Φ, mul_pow, mul_inv, inv_inv, _root_.mul_assoc]
  apply fn_ext
  intro z _
  have hz : rQ t.G x p (g.x m) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀) := h trivial
  classical
  choose c hc using fun χ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left => exists_chart t.PP.isLB (χ z)
  let J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι := fun ψ => if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ
  have hJ₀ : ∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀ := fun ψ e => if_pos e
  have hJ : Good t.PP.L z J := fun ψ => by
    by_cases e : ψ z ∈ t.PP.L.U j₀
    · rw [hJ₀ ψ e]; exact e
    · show ψ z ∈ t.PP.L.U (if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ)
      rw [if_neg e]; exact hc ψ
  have e := val_of C (rQ t.G x p (g.x m)) z J (fun _ => j₀) (fun i => hJ₀ _ (Set.mem_iInter.1 hz i))
  refine (Pf.gs_appLE _ _ _ h z trivial _).trans ((gs_unit _ z _ hz _).trans ?_)
  refine (congrArg Units.val (e.symm.trans (hval z J hJ hJ₀))).trans ?_
  rw [← hU]
  exact (gs_unit (𝟙 _) z ⊤ trivial (unitΓ U)).symm

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_finite_extension_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | exact GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgField.exists_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.flag_line_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y) (x : CMType H × Fin (D.p + D.q) → HermLine J) (e : CMType H × Fin (D.p + D.q) → Ω), (∀ r, IsSmoothHerm (x r)) → Fl.RootLines (fun r => (x r).a) e → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ 𝔐.X), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier) (A : FlagPair B (CMType H) D.p D.q), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ((∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i)) → (∀ τ (i : Fin D.p), |Ht.lineHt (x (τ, Fin.castAdd D.q i)) L w - (A.W τ).grDeg i| ≤ C) ∧ ∀ τ (i : Fin D.q), |Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w + (A.S τ).grDeg i.rev| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.root_height | exact GlobalTheory.CompanionTheory.Ar.RootHt.root_height | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.root_height <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | exact GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | (intros; apply GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hermitian_bundle_fibre_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeBC.main | exact GlobalTheory.CompanionTheory.Ar.HodgeBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeBC.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_line_idempotent_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∃ s s' e : Formalism.L2.Pj.Rul Xo c, e ∈ Formalism.L2.Pj.sec Xo c 0 0 ∧ s * s' = e ∧ s * e = s ∧ s' * e = s' ∧ (∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Formalism.L2.Pj.Rul Xo c), (∀ x : (E →+* ℂ) × ℕ, x.2 < D.mult x.1 → (a' x : ℤ) = a x + Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = ComplexEmbedding.conjugate τ} 1 x - Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = τ} 1 x) → (f ∈ Formalism.L2.Pj.sec Xo c a n → f * s ∈ Formalism.L2.Pj.sec Xo c a' n) ∧ (f ∈ Formalism.L2.Pj.sec Xo c a' n → f * s' ∈ Formalism.L2.Pj.sec Xo c a n)) ∧ ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → (¬ Set.range y ⊆ U → ψ (e p z) = 0) ∧ (Set.range y ⊆ U → ψ (e p z) = 1 ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flat_rule | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flat_rule | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flat_rule <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.formal_germ_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S S₂ : Type) [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), ∃ g₂ : GermAt t (spMap f ≫ x) d, IsMapOf f g.B g₂.B ∧ ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  first | exact @PositivityTheory.HtPt.Ce.germ_bc | exact PositivityTheory.HtPt.Ce.germ_bc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  first | exact @PositivityTheory.HtPt.Ce.geompf_tan | exact PositivityTheory.HtPt.Ce.geompf_tan
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germSys_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) :=
  @PositivityTheory.Xgn.germ_system_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_pure_frame_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → LinearIndependent (𝓞 E) x → IsTransition (FU.Di i) x e T → X.IsCMFrame τ hx v w → IsFramed U τ X.β X.y v w ∧ ((φ X.K X.y v w : X.K) : ℂ) * τ T.det * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame | exact GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_relay_bound :
    GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.CommonModel

section Ext

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B] {GK : Over (Sp K)} [GrpObj GK]

theorem hom_unique (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a) (g₁ g₂ : A ⟶ B) [IsMonHom g₁] [IsMonHom g₂]
    (h : a ≫ g₁.left = a ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  have hmap : (Over.pullback (spMap (algebraMap V K))).map g₂ =
      (Over.pullback (spMap (algebraMap V K))).map g₁ := by
    have L : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) =
          pullback.fst A.hom (spMap (algebraMap V K)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have R : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.snd B.hom (spMap (algebraMap V K)) =
          pullback.snd A.hom (spMap (algebraMap V K)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [L, L, ← hio, Category.assoc, Category.assoc, h]
    · rw [R, R]
  obtain ⟨F, -, hu⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    ((Over.pullback (spMap (algebraMap V K))).map g₁) inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap⟩).symm

theorem hom_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ F : A ⟶ B, IsMonHom F ∧ a ≫ F.left = b := by
  obtain ⟨io, hiom, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  obtain ⟨ko, -, hko⟩ := grpPullback_iso ha (isGrpPullback_pullback A (spMap (algebraMap V K)))
  obtain ⟨ko', hko'm, hko'⟩ := grpPullback_iso hb (isGrpPullback_pullback B (spMap (algebraMap V K)))
  have := hiom
  have := hko'm
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply ha.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨F, hFm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst A.hom (spMap (algebraMap V K)) ≫ F.left =
      ((Over.pullback (spMap (algebraMap V K))).map F).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hF, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem iso_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ a ≫ e.hom.left = b := by
  obtain ⟨F, hFm, hF⟩ := hom_exists V K hA hB ha hb
  obtain ⟨F', hF'm, hF'⟩ := hom_exists V K hB hA hb ha
  have := hFm
  have := hF'm
  have h₁ : F ≫ F' = 𝟙 _ := hom_unique V K hA hA ha _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF, hF', Over.id_left, Category.comp_id])
  have h₂ : F' ≫ F = 𝟙 _ := hom_unique V K hB hB hb _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF', hF, Over.id_left, Category.comp_id])
  exact ⟨⟨F, F', h₁, h₂⟩, hFm, hF⟩

end Ext

end GlobalTheory.CompanionTheory.Ar.CommonModel

namespace GlobalTheory.CompanionTheory.Ar

theorem semiAbelian_commonModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  intro V K _ _ _ _ _ _ X X' x x' G G' _ _ GK _ φ φ' hG hG' hφ hφ'
  have pA := isGrpPullback_pullback G x
  have pB := isGrpPullback_pullback G' x'
  have sA : IsSemiAbelian ((Over.pullback x).obj G) := IsSemiAbelian.pullback x G hG
  have sB : IsSemiAbelian ((Over.pullback x').obj G') := IsSemiAbelian.pullback x' G' hG'

  have lift : ∀ {Y : Scheme.{0}} (y : Sp V ⟶ Y) (H : Over Y) [GrpObj H] (θ : GK.left ⟶ H.left),
      IsGrpPullback GK H (spMap (algebraMap V K) ≫ y) θ →
      ∃ κ : GK.left ⟶ ((Over.pullback y).obj H).left,
        IsGrpPullback GK ((Over.pullback y).obj H) (spMap (algebraMap V K)) κ ∧
          κ ≫ pullback.fst H.hom y = θ := by
    intro Y y H _ θ hθ
    have hp := isGrpPullback_pullback H y
    have w : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ ((Over.pullback y).obj H).hom =
        GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
    have f : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ pullback.fst H.hom y = θ := hp.1.lift_fst _ _ _
    exact ⟨_, hp.cancel (by rw [f]; exact hθ) w, f⟩
  obtain ⟨κ, hκ, hκφ⟩ := lift x G φ hφ
  obtain ⟨κ', hκ', hκφ'⟩ := lift x' G' φ' hφ'
  obtain ⟨e, hem, he⟩ := CommonModel.iso_exists V K sA sB hκ hκ'
  have := hem
  refine ⟨(Over.pullback x).obj G, inferInstance, pullback.fst G.hom x,
    e.hom.left ≫ pullback.fst G'.hom x', κ, pA, ?_, hκ, hκφ, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp pB).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, he, hκφ']

end GlobalTheory.CompanionTheory.Ar
end
