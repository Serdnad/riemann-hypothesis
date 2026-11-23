module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle300
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle060
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionModelRatio
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle180
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle262
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle320
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle215
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AevalRatioForm
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.TestMem
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle192
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle252
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi


theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → FinTr.Linked Rd → ∀ B₁ : Finset RM.Ω, ∃ (B₂ : Finset RM.Ω) (B₃ : Finset (Om Z)), ∀ (A : Subring RM.Ω), (↑B₁ : Set RM.Ω) ⊆ A → (↑B₂ : Set RM.Ω) ⊆ A → ∀ (A' : Subring (Om Z)), (↑B₃ : Set (Om Z)) ⊆ A' → ∀ (p : ℕ) [Fact p.Prime] (ev₁ : A →+* PadicAlgCl p), (∀ x, IsAlgebraic ℤ (ev₁ x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (y : IntFr Xo c T io) (ι : T.Fr →+* PadicAlgCl p) (ev : A' →+* T.Fr), (p : 𝓞 c.F) ∈ la.asIdeal → OverLa la T.V io e₀ → y.IsAlg → (∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x) → FinTr.RegAt h Z io A' ev y.1 → (∀ a : A', ∃ ha : Rd.φ a ∈ A, ev₁ ⟨_, ha⟩ = ι (ev a)) → ∃ z ∈ Small.algPts p (mCoordIdeal RM.y), ∃ rec : RootIx Dw → ℝ, (∀ b (hb : b ∈ A), b ∈ B₁ → Small.HasVal RM.y 0 b z (ev₁ ⟨b, hb⟩)) ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ Rec.secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ∀ s : ℝ, nval T.V e₀ (evI y f) = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hUn O _ β Y SS RM Sys Fx Or Fr Z Rd hOm hram hLk B₁
  classical
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  letI aΩ : Algebra c.F RM.Ω := Small.cstAlg Or
  obtain ⟨B, hB⟩ := GlobalTheory.T.root_origin_frame_height E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨w, tl, hw, htl⟩ := hLk
  have hy0 : ∀ k, ∃ i, RM.y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := RM.arith.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap RM.y _ = 0
    simp [mConeMap, h0]
  obtain ⟨B₂, hB₂⟩ := ModelDimension.Read.point RM.y RM.birational hy0 (B₁ ∪ B ∪
    Finset.univ.image (fun x : Σ k : RM.K, RM.ι k × RM.ι k => RM.y ⟨x.1, x.2.1⟩ / RM.y ⟨x.1, x.2.2⟩) ∪
    Finset.univ.image fun k => (((tl k)⁻¹ : RM.Ωˣ) : RM.Ω))
  refine ⟨B₂, ∅, fun A _ hA A' _ p _ ev₁ halg la T io e₀ y ι ev hp ho hy hι hReg hφ => ?_⟩
  letI aT : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨hcst, q', φ', ψ', yq', z', t', hq1, hq2, hq3, hq4⟩ := hReg
  have hcA : ∀ a : c.F, ∃ ha : Or.𝔐.cst a ∈ A, ev₁ ⟨_, ha⟩ = ι (io a) := fun a => by
    obtain ⟨ha, e1⟩ := hcst a
    obtain ⟨hb, e2⟩ := hφ ⟨_, ha⟩
    have e3 := Rd.φ_cst a
    refine ⟨e3 ▸ hb, ?_⟩
    rw [← e1, ← e2]
    exact congrArg ev₁ (Subtype.ext e3.symm)
  have hn : ∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A := fun n _ => by
    have := (hcA ((n : c.F))⁻¹).1
    rwa [map_inv₀, map_natCast] at this
  obtain ⟨z, hz, hzA, A₂, hle, hBA, hn₂, hev⟩ := hB₂ A hA hn (PadicAlgCl p) ev₁
  have hzalg : z ∈ Small.algPts p (mCoordIdeal RM.y) := ⟨hz, fun q => by
    obtain ⟨a, ha⟩ := hzA q
    rw [ha]
    exact (halg a).extendScalars (algebraMap ℤ ℚ).injective_int⟩
  have hGood := hB A₂ (fun x hx => hBA (by simp [Finset.mem_coe.1 hx])) hn₂
  have hrat : ∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A₂ := fun k i j _ =>
    hBA (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨⟨k, i, j⟩, Finset.mem_univ _, rfl⟩))))
  have htA : ∀ k, (((tl k)⁻¹ : RM.Ωˣ) : RM.Ω) ∈ A₂ := fun k =>
    hBA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)))
  have hram0 := FinRd.ram_pos hp
  have hN : (0 : ℝ) < (e₀ : ℝ) * (ramOverZ la : ℝ) :=
    mul_pos (by exact_mod_cast ho.1) (by exact_mod_cast hram0)
  obtain ⟨T₀, j, iT, r₀, L, hfin, hr₀, hj, hv₀, hzL, hLj, hnorm⟩ := ModelDimension.Read.ext T hy ι _ hN
    (fun x hx => by rw [hι]; unfold FinRd.absT; rw [if_neg hx]) z
  let A₃ : Subring RM.Ω := (j.range.comap ev₁).map A.subtype
  have hA₃ : ∀ x, x ∈ A₃ ↔ ∃ hx : x ∈ A, ∃ b, j b = ev₁ ⟨x, hx⟩ := fun x =>
    ⟨by rintro ⟨a, ⟨b, hb⟩, rfl⟩; exact ⟨a.2, b, hb⟩, fun ⟨hx, b, hb⟩ => ⟨⟨x, hx⟩, ⟨b, hb⟩, rfl⟩⟩
  choose h3A f hf using fun x : A₃ => (hA₃ x).1 x.2
  have hinj : Function.Injective j := j.injective
  let ev₀ : A₃ →+* T₀.Fr :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one]; exact map_one ev₁)
      map_mul' := fun a b => hinj (by rw [hf, map_mul, hf, hf]; exact map_mul ev₁ ⟨_, h3A a⟩ ⟨_, h3A b⟩)
      map_zero' := hinj (by rw [hf, map_zero]; exact map_zero ev₁)
      map_add' := fun a b => hinj (by rw [hf, map_add (f := _), hf, hf]; exact map_add ev₁ ⟨_, h3A a⟩ ⟨_, h3A b⟩) }
  have hev₀ : ∀ x : A₃, j (ev₀ x) = ev₁ ⟨x, h3A x⟩ := hf
  have h23 : A₂ ≤ A₃ := fun x hx => (hA₃ x).2 ⟨hle hx, hLj _ (FinRd.Pt.hasVal_mem hzL (hev ⟨x, hx⟩))⟩
  obtain ⟨y₀, φT, hφT, hy₀⟩ := GlobalTheory.T.integralFramedPoint_baseChange_stable E H Dw l Xo c T T₀ io y iT r₀ hr₀ (fun a _ => hv₀ a)
  have ho₀ : OverLa la T₀.V (iT.comp io) (r₀ * e₀) := ho.bc iT hr₀ hv₀
  obtain ⟨T₂, φV, φ₂, r₂, yy, τ, hfe, hbc, hyA, hτ⟩ := hUn la T₀ (iT.comp io) _ ho₀ y₀ hfin
  letI a0 : Algebra c.F T₀.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra c.F T₂.Fr := (φ₂.comp (iT.comp io)).toAlgebra
  have hφT' : ∀ x, φT x = iT x := fun x => RingHom.congr_fun hφT x
  let φ₂A : T₀.Fr →ₐ[c.F] T₂.Fr := { φ₂ with commutes' := fun _ => rfl }
  have hLaw := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨hc1, ⟨q, φq, yq, hyq, hφA⟩, -, -⟩ := id hGood
  have hc0 : ∀ (a : c.F) (ha : algebraMap c.F RM.Ω a ∈ A₃), ev₀ ⟨_, ha⟩ = algebraMap c.F T₀.Fr a := fun a ha =>
    hinj (by rw [hev₀]; exact (hcA a).2.trans (hj _).symm)
  let ψ₀ : q.R →ₐ[c.F] T₀.Fr := ModelDimension.Spread.evAlg φq A₃ (fun r => h23 (hφA r)) ev₀ hc0
  obtain ⟨w₂, hw₂⟩ := hLaw.bc _ _ ψ₀ yq
  obtain ⟨w₁, hw₁⟩ := hLaw.bc _ _ φT z'
  have hmem : ∀ r, ∃ hr : ((FinTr.phiAlg Rd).comp φ') r ∈ A₃, (φT.comp ψ') r = ev₀ ⟨_, hr⟩ := fun r => by
    obtain ⟨h1, e1⟩ := hq3 r
    obtain ⟨h2, e2⟩ := hφ ⟨_, h1⟩
    have e3 : j (iT (ψ' r)) = ev₁ ⟨_, h2⟩ := by rw [hj, e1, e2]
    refine ⟨(hA₃ _).2 ⟨h2, _, e3⟩, hinj ?_⟩
    rw [hev₀, AlgHom.comp_apply, hφT', e3]
    rfl
  obtain ⟨t₁, ht₁⟩ := ModelDimension.Spread.spec_bor ((FinTr.phiAlg Rd).comp φ') φq
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hq1 hw) hyq htl A₃ (fun r => (hmem r).1) (fun r => h23 (hφA r))
    (fun k => h23 (htA k)) ev₀ (φT.comp ψ') ψ₀ (fun r => (hmem r).2) (fun _ => rfl)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hq2 hw₁) hw₂
  obtain ⟨-, gmul, ginv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c T₀.Fr
  have hb₀ := gmul _ _ _ _ _ (ginv _ _ _ ht₁) (frBorBC _ _ φT _ _ _ _ _ hq4 hw₁ hy₀)
  obtain ⟨zT, hzT⟩ := hLaw.bc _ _ φ₂A w₂
  obtain ⟨t, hFB⟩ : ∃ t, FrBor t zT yy.1 := ⟨_, frBorBC _ _ φ₂A _ _ _ _ _ hb₀ hzT hbc⟩
  let ev₂ : A₂ →+* PadicAlgCl p := ev₁.comp (Subring.inclusion hle)
  let evT : A₂ →+* T₂.Fr := φ₂.comp (ev₀.comp (Subring.inclusion h23))
  have ho₂ := hfe.overLa ho₀
  have hI : FinRd.IsIntPt Fr A₂ ev₂ la T₂ (φ₂.comp (iT.comp io)) (r₂ * (r₀ * e₀)) yy evT zT t := by
    unfold FinRd.IsIntPt
    refine ⟨hp, ho₂, hyA, ⟨τ, hτ⟩, fun a ha => congrArg φ₂ (hc0 a (h23 ha)), fun x => ?_,
      ⟨q, φq, φ₂A.comp ψ₀, yq, hyq, ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hw₂ hzT, fun r => ⟨hφA r, rfl⟩⟩, hFB⟩
    have e1 : ev₂ x = j (ev₀ ⟨x, h23 x.2⟩) := (hev₀ ⟨x, h23 x.2⟩).symm
    have e2 : evT x = φ₂ (ev₀ ⟨x, h23 x.2⟩) := rfl
    rw [e1, e2]
    unfold FinRd.absT
    by_cases hx : ev₀ ⟨x, h23 x.2⟩ = 0
    · rw [hx, map_zero, map_zero, norm_zero, if_pos rfl]
    · rw [if_neg ((map_ne_zero φ₂).2 hx), hnorm _ hx, hfe.2.2.2.2.2]
      have hr2 : (r₂ : ℝ) ≠ 0 := by exact_mod_cast hfe.2.2.2.2.1.ne'
      push_cast
      congr 2
      rw [mul_assoc (r₂ : ℝ), mul_div_mul_left _ _ hr2, mul_assoc]
  let x : (Ref.pjSys Xo c).Pt la := (show Ref.PtU Xo c la from PtV.mk la ho₂ yy hyA τ hτ)
  have hval : ∀ f, (Ref.pjSys Xo c).val x f = nval T₂.V (r₂ * (r₀ * e₀)) (evI yy f) :=
    fun f => Ref.pjSys_val_mk Xo c la ho₂ yy hyA τ hτ f
  have hS := GlobalTheory.T.root_origin_frame_section_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A₂ p z ev₂ hzalg hev la T₂ _ _ yy evT zT t hI x hval
  have hR := GlobalTheory.T.root_origin_frame_degree_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr hOm hram A₂ p z ev₂ hzalg hev hGood hrat
    la T₂ _ _ yy evT zT t hI
  obtain ⟨rec, h1, h2⟩ := FinRd.read_of_reads hz x (FinRd.tOf_pos la T₂ _ t) hS hR
  refine ⟨z, hzalg, rec, fun b hb hb1 => hev ⟨b, hBA (by simp [hb1])⟩, fun r' => ⟨(h1 r').1, ?_⟩,
    fun a n' hn' g hg => ?_⟩
  · rw [← latExp_eq]
    exact (h1 r').2
  obtain ⟨v, hv1, -, hv2⟩ := h2 a n' hn' g hg
  refine ⟨v, hv1, fun s hs => hv2 s ?_⟩
  obtain ⟨pq, χ, u, hu⟩ := y.2.1
  have k1 : evI y g = χ (g pq u) := Formalism.L2.Pj.evR_of_frMap hLaw.wd hg.1 hu
  have k2 : evI yy g = φ₂ (iT (χ (g pq u))) := by
    rw [← hφT']
    exact Formalism.L2.Pj.evR_of_frMap hLaw.wd hg.1
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ φ₂A (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hu hy₀) hbc)
  rw [hval, k2, nval_bc φ₂ hfe.2.2.2.2.1 hfe.2.2.2.2.2, nval_bc iT hr₀ hv₀, ← k1, hs]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @PositivityTheory.Xgn.line_function_model_ratio | exact PositivityTheory.Xgn.line_function_model_ratio
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H

theorem tauIn_rt_eq (τ : E →+* ℂ) (σ : c.F →+* ℂ) :
    σ (tauIn c τ H.rt) = H.rt0 ∨ σ (tauIn c τ H.rt) = -H.rt0 := by
  have h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem gram_det_ne_zero {τ : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    {y : Sp ℂ ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {Γ : Matrix (Fin D.p) (Fin D.p) ℂ}
    (hf : IsFramed Set.univ τ σ y v w) (hΓ : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ) :
    Γ.det ≠ 0 := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := FU.onto _ hs
  obtain ⟨V, hV, hli, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y)
    (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl)
    hf.2.2.1
  obtain ⟨Hm, hH, hpos, him⟩ := hP.2.2.2.2
  have hG := (hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ
    (fun a => (hV a (V a)).2 rfl)).1 hΓ
  let M : Matrix (Fin D.p) (Fin g) ℂ := Matrix.of V
  have hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose) := by
    ext a b
    rw [hG a b, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set z := Matrix.vecMul (star x) M with hz
  have hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z := by
    rw [hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hx, dotProduct_zero] at hq
  have hz0 : z = 0 := by
    by_contra hne
    have := hpos z hne
    have h2 : (hermForm Hm z z) = 0 := by
      rcases mul_eq_zero.1 hq.symm with h | h
      · exact absurd h (by exact_mod_cast Real.pi_ne_zero)
      · exact h
    rw [h2] at this; simp at this
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.2 hli
  have : star x = 0 := hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])
  exact hx0 (by simpa using this)

theorem exists_infNorm_of_rt (hR : Geo.ResK.ResKStatement) (hG : GagaSections) {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {φ : FrameFn Xo c}
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hr : 1 ≤ D.p + D.q) (hτ : τ (H.rt : E) = H.rt0) (hZ : Z.IsGeom) (hl : IsLineFn U τ φ)
    (hm : FlatOnModel Z τ φ) (σ : c.F →+* ℂ) (hσ : σ (tauIn c τ H.rt) = H.rt0) :
    ∃ t : ℝ, HasInfNorm U τ φ σ t := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)
    show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0
    rw [e, hσ]
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.T.abelianScheme_laws_unconditional.1 E H D l Xo _ g ty hr hK hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU
    hty hσ (fun a => rfl)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm
  refine ⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩
  have hf' : IsFramed Set.univ τ σ y v w := ⟨hf.1, Set.subset_univ _, hf.2.2⟩
  have hΓ : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)
  have hΦ0 : ‖Φ y v w‖ ≠ 0 := norm_ne_zero_iff.2 (hΦ.ne y v w hf')
  have hn := congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)
  rw [Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow] at hn
  rw [hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]
  push_cast at hn
  linarith

theorem flat_first_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → FlatLineGeneratorComponent := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm
  have key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t := by
    intro s
    rcases tauIn_rt_eq (c := c) (H := H) τ s with h | h
    · exact exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h
    · obtain ⟨t, ht⟩ := exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s)
        (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])
      refine ⟨t, ?_⟩
      have := GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ _ t hl ht
      rwa [show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp] at this
  refine ⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩
  · obtain ⟨t, ht⟩ := key s
    exact ⟨t, ht, GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ s t hl ht⟩
  · obtain ⟨Φ, hΦ, hfl⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm
    obtain ⟨e, ρ, -, he, hρ⟩ := hfl i
    refine ⟨hmem, hl, e, κ * ρ, he, ?_⟩
    intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
    rw [hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]

end GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem
end
end
