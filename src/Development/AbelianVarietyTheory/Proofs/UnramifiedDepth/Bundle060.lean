module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle058
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle053
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import ReciprocityTheory.DualLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Formalism.LocalToGlobal.CharacterGerms.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle059
public import Formalism.LocalToGlobal.CharacterGerms.Bundle021
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | exact GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | (intros; apply GlobalTheory.RowLaw.cv_inv_natCast_smul_mem <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.frobenius_mem_typicalCurveSet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  first | exact @GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | exact GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | (intros; apply GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF.Lift

section Subst
variable {R : Type} [CommRing R] {m n d e : ℕ}

private theorem hasSub (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private noncomputable def subA (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS R m d →ₐ[R] PS R n e :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem subA_apply (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d) : subA a ha f = sub a f := by
  unfold subA sub
  rw [MvPowerSeries.coe_substAlgHom]

private theorem sub_sub {n' e' : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (b : Fin n → Fin e → PS R n' e')
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (f : PS R m d) :
    sub b (sub a f) = sub (fun i j => sub b (a i j)) f := by
  unfold sub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSub a ha) (hasSub b hb)]

private theorem sub_X (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (i : Fin m) (j : Fin d) :
    sub a (MvPowerSeries.X (i, j)) = a i j := by
  unfold sub
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_sub (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem ev_eq_sub (a : Fin m → Pt R n d) (f : PS R m d) : ev a f = sub a f := rfl

private theorem addOf_pt (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem const_one (φ : Fin d → PS R n e) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → Fin d → PS R n e) i j) = 0 := by
  intro i j
  fin_cases i
  exact hφ j

private theorem const_pt (k : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt R d k j) = 0 := by
  intro j
  simp [pt]

private theorem isSum_comp (F : Fin d → PS R 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin e → PS R 2 e) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (J : Fin e → PS R 1 d) (hJ : IsHomF F F' J) (φ φ' ψ : PS R 1 d →ₐ[R] R) (h : IsSum F φ φ' ψ) :
    IsSum F' (φ.comp (subA ![J] (const_one J hJ.1))) (φ'.comp (subA ![J] (const_one J hJ.1)))
      (ψ.comp (subA ![J] (const_one J hJ.1))) := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have hb : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff
      ((![fun i => ev (n := 2) ![pt R d 0] (J i), fun i => ev (n := 2) ![pt R d 1] (J i)] :
        Fin 2 → Fin e → PS R 2 d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact const_sub _ (const_one _ (const_pt 0)) _ (hJ.1 j)
    · exact const_sub _ (const_one _ (const_pt 1)) _ (hJ.1 j)
  refine ⟨Φ.comp (subA _ hb), fun f => ?_, fun f => ?_, fun f => ?_⟩
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h0, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 0)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 0))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 0 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h1, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 1)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 1))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 1 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h2, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ hF') _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ hF)]
    congr 2
    funext i j
    fin_cases i
    exact (hJ.2 j).symm

private theorem isCh_sum (F : Fin d → PS R 2 d) (u : PS R 1 d) (hu : IsCh F u) (φ φ' ψ : PS R 1 d →ₐ[R] R)
    (h : IsSum F φ φ' ψ) : ψ u = φ u * φ' u := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have h3 := hu.2
  rw [addOf_pt] at h3
  rw [← h2, ← h0, ← h1, h3, map_mul]

end Subst

theorem exists_char_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  intro p _ C _ _ _ v O _ _ hv _ _ d r F hFH J A' hJ hA i
  obtain ⟨⟨Gl, hGl⟩, hch, -⟩ := GlobalTheory.ChF.gmLaw_chars_mul O r
  obtain ⟨hchi, hdl⟩ := hch i
  have hFHG : FH p Gl.F := hGl ▸ GlobalTheory.T.multiplicativeFormalGroupLawPower_pTorsion_finiteFree p C v O hv r
  rw [← hGl] at hJ hchi
  obtain ⟨instF, hsF, h0F, hkF⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  obtain ⟨instG, hsG, h0G, hkG⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv r Gl
  obtain ⟨hchain, -, -⟩ := GlobalTheory.ChF.chain_rule_lin O r d J hJ.1
  have hsurj := GlobalTheory.ChF.sub_surjective_of_lin_leftInverse O d r J A' hJ.1 hA
  let j : (PS O 1 r →ₐ[O] O) →+ (PS O 1 d →ₐ[O] O) :=
    { toFun := fun φ => φ.comp (subA ![J] (const_one J hJ.1))
      map_zero' := by
        refine AlgHom.ext fun f => ?_
        rw [AlgHom.comp_apply, subA_apply, h0F, h0G, (hchain f).2]
      map_add' := fun φ φ' =>
        (hsF _ _ _).1 (isSum_comp Gl.F Gl.const F.F F.const J hJ φ φ' _ ((hsG _ _ _).2 rfl)) }
  have hj : ∀ φ f, j φ f = φ (sub ![J] f) := fun φ f => by
    show φ (subA ![J] (const_one J hJ.1) f) = _
    rw [subA_apply]
  have hinj : Function.Injective j := by
    intro φ φ' h
    refine AlgHom.ext fun g => ?_
    obtain ⟨f, rfl⟩ := hsurj g
    rw [← hj, ← hj, h]
  have hunit : IsUnit (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS O 1 r) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hchi.1]
    exact isUnit_one
  let χ : (PS O 1 r →ₐ[O] O) → Cˣ := fun φ => ((hunit.map φ).map (algebraMap O C)).unit
  have hχ : ∀ φ, (χ φ : C) = algebraMap O C (φ (1 + MvPowerSeries.X ((0 : Fin 1), i))) := fun φ => rfl
  have hχm : ∀ a b, χ (a + b) = χ a * χ b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hχ, hχ, hχ, isCh_sum Gl.F _ hchi a b _ ((hsG _ _ _).2 rfl), map_mul]
  obtain ⟨κ, hκm, hκ0, hκj⟩ := GlobalTheory.CharExt.exists_extension _ _ j hinj C p (Fact.out : p.Prime).ne_zero χ hχm
  obtain ⟨u, hu, huκ⟩ := GlobalTheory.T.exists_isCh_eq_character_on_torsion p C v O hv d F hFH (fun φ => (κ φ : C))
    (by
      rintro φ φ' ψ ⟨k, hk⟩ ⟨k', hk'⟩ hs
      rw [(hsF _ _ _).1 hs, hκm φ φ' ⟨k, (hkF _ _).2 hk⟩ ⟨k', (hkF _ _).2 hk'⟩, Units.val_mul])
    (by
      intro φ hφ
      have : φ = 0 := AlgHom.ext fun f => by rw [hφ, h0F]
      show (κ φ : C) = 1
      rw [this, hκ0, Units.val_one])
  refine ⟨u, hu, ?_⟩
  have heq : sub ![J] u - (1 + MvPowerSeries.X ((0 : Fin 1), i)) = 0 := by
    apply (GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv r Gl hFHG).2
    rintro φ ⟨k, hk⟩
    have h1 : p ^ k • φ = 0 := (hkG _ _).2 hk
    have h2 : p ^ k • j φ = 0 := by rw [← map_nsmul, h1, map_zero]
    have h3 := huκ (j φ) ⟨k, (hkF _ _).1 h2⟩
    rw [map_sub, sub_eq_zero]
    apply hv.hom_inj
    rw [← hj, h3, ← hχ, ← hκj φ ⟨k, h1⟩]
  rw [← (hchain u).1, sub_eq_zero.1 heq, hdl]

end GlobalTheory.ChF.Lift
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_abelian_torus_generators_at_place : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ (h : ℕ) (ψ : Fin h → Fin d → O), h ≤ rp + rm ∧ (∀ l j, Pdiv.ChartF.res (W j) (ψ l) ∈ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) ∧ ∃ f : htCoker H w.e w.bar →ₗ[O] ((LinearMap.range (LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))) : Submodule O (Fin w.n × Fin rp → O)) ⧸ (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2)).comap (Submodule.subtype _)), Function.Surjective f := by
  first | exact @GlobalTheory.ChF.GenAtPlace.exists_generators | exact GlobalTheory.ChF.GenAtPlace.exists_generators | (intros; apply GlobalTheory.ChF.GenAtPlace.exists_generators <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_integralSeries_frame_eq_prod_rows : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : ∀ o, RawChart C d (I o) κ) (d₀ : ℕ) (I₀ : Fin 2 → Type) [∀ g, Fintype (I₀ g)] (X₀ : RawChart C d₀ I₀ κ), RLaw X₀ V → (∀ o, (X o).ex = X₀.ex ∧ (X o).h = X₀.h ∧ (X o).k = X₀.k) → ∀ (π : Orb → Fin 2 → Matrix κ κ C) (W : Matrix κ κ C), (∀ o g, IntEnd X₀ V (π o g)) → (∀ o g c, (π o g).mulVec ((X o).u g c) = (X o).u g c) → (∀ o g o' g' c, (o, g) ≠ (o', g') → (π o g).mulVec ((X o').u g' c) = 0) → (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ → ∀ gr : ∀ o, MvPowerSeries (WV (I o)) C, (∀ o, gr o ∈ ExpInt (X o) V) → ∃ F : MvPowerSeries κ C, IntS V F ∧ MvPowerSeries.subst (fun x : κ => MvPowerSeries.subst (fun i : κ => ∑ w : WVO I, (X w.1).u w.2.1 w.2.2 i • (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (X₀.ex x)) (F * mvExp ((X₀.k : C) • hEnd X₀ 1 W)) = ∏ o, MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) (gr o * mvExp (X o).hRow) := by
  first | exact @GlobalTheory.RowVal.exists_intS_frame_eq_prod | exact GlobalTheory.RowVal.exists_intS_frame_eq_prod | (intros; apply GlobalTheory.RowVal.exists_intS_frame_eq_prod <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.monomialBlock_supply_both_typings : MONSupply ∧ RF.MONSupply := by
  first | exact @GlobalTheory.MonBlock.monSupply | exact GlobalTheory.MonBlock.monSupply | (intros; apply GlobalTheory.MonBlock.monSupply <;> assumption)
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.QuadTrace

theorem bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have e := H.bar_eq H.rt
    rw [h] at e
    have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj, ← e]
    have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
      simpa using this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
    rw [hr] at e3
    have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
    have : (0 : ℝ) < H.d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h

theorem cmHost_idempotent_trace_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.HostTraceIdentity H := by
  intro E _ _ _ H _ hstar
  rw [hstar]
  have hb := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, bar_rt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

end GlobalTheory.QuadTrace
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.ChartBaseChange

theorem isCanonGauge_mapFB {R k : Type} [CommRing R] [Algebra ℚ R] [CommRing k] [Algebra ℚ k]
    (f : R →+* k) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {h : PS R 2 d}
    (hg : B.IsCanonGauge R h) :
    (GlobalTheory.FBMap.mapFB f B).IsCanonGauge k (MvPowerSeries.map f h) := by
  letI : Algebra R k := f.toAlgebra
  have h1 : B.IsCanonGauge k (MvPowerSeries.map f h) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId R k) hg
  have hid : ∀ {σ : Type} (g : MvPowerSeries σ k), MvPowerSeries.map (algebraMap k k) g = g := by
    intro σ g
    ext m
    simp [MvPowerSeries.coeff_map]
  have hF : (GlobalTheory.FBMap.mapFB f B).FK k = B.FK k := funext fun i => hid _
  have hA : ∀ a, (GlobalTheory.FBMap.mapFB f B).actK k a = B.actK k a := fun a => funext fun i => hid _
  refine ⟨h1.ax0, h1.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF, ← h1.ph1]; exact hid _
  · rw [hF, ← h1.ph2]; exact hid _
  · rw [← h1.sy]; exact hid _
  · rw [hA, hA, ← h1.ad a]; exact hid _

theorem intS_map {T : CDVR} {C : Type} [Field C] {V : VF C} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {σ : Type} {g : MvPowerSeries σ T.Fr} {g0 : MvPowerSeries σ T.V}
    (hg : g = MvPowerSeries.map (algebraMap T.V T.Fr) g0) : IntS V (MvPowerSeries.map ι g) := by
  intro m
  rw [hg, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  exact (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1 _

theorem exists_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.BCExSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι hac hcpl hl hw k hk
  obtain ⟨gF, gA, g1, g2, gs, ga, -⟩ := C3.gen.1
  have hg : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    letI := io.toAlgebra
    exact C3.ch.gauge
  obtain ⟨lg, ex, hlin, hadd, hc, hle, hel⟩ :=
    GlobalTheory.FormalLog.exists_log_exp C (chD C3.ch) (GlobalTheory.FBMap.mapFB ι (a3B C3)).G
  exact ⟨{ algClosed := hac
           cpl := hcpl
           l_odd := hl
           B := GlobalTheory.FBMap.mapFB ι (a3B C3)
           h := MvPowerSeries.map ι (a3h C3)
           gauge := isCanonGauge_mapFB ι (a3B C3) hg
           intF := fun i => intS_map hι (gF i)
           intAct := fun a i => intS_map hι (gA a i)
           intPh1 := intS_map hι g1
           intPh2 := intS_map hι g2
           intSy := intS_map hι gs
           intAd := fun a => intS_map hι (ga a)
           lg := lg
           lg_lin := hlin
           lg_add := hadd
           ex := ex
           ex_const := hc
           lg_ex := hle
           ex_lg := hel
           w0 := H.w0
           halfIntegralGenerator_add_conj_eq_one := hw
           k := k
           k_unit := hk },
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩⟩

end GlobalTheory.ChartBaseChange
end
