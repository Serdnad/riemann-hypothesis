module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlaces
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesOverLevel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle180
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle190
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle160
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowData_supplied_at_pairs_of_places : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  first | exact @GlobalTheory.RowAt.supply_pairs | exact GlobalTheory.RowAt.supply_pairs | (intros; apply GlobalTheory.RowAt.supply_pairs <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowData_supplied_at_selfConjugate_places : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → SupplyC V Orb lab.n (lab.j + lab.j') (fun o s => Dw.mult (lab.tau o s)) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) nW ν := by
  first | exact @GlobalTheory.RowAt.supplyC_selfConj | exact GlobalTheory.RowAt.supplyC_selfConj | (intros; apply GlobalTheory.RowAt.supplyC_selfConj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaLatticeDepth_le_at_places_prime_to_level : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthPrimeToLevel.depth_le | exact GlobalTheory.DepthPrimeToLevel.depth_le | (intros; apply GlobalTheory.DepthPrimeToLevel.depth_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaLatticeDepth_le_at_places_over_level : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthOverLevel.depth_le_over_level | exact GlobalTheory.DepthOverLevel.depth_le_over_level | (intros; apply GlobalTheory.DepthOverLevel.depth_le_over_level <;> assumption)
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem theta_stable_of_algHom {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (Ψ : X.Forms →ₐ[B.KO] X.Forms) (Sc : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hL : ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Ψ (X.inc wL F) = X.inc wL F')
    (hS : ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Ψ (X.inc w F) = X.inc w F') :
    ∀ x ∈ X.Theta Sc ka wL wF T, Ψ x ∈ X.Theta Sc ka wL wF T := by
  let Φ : X.Forms →ₐ[𝓞 B.KO] X.Forms := Ψ.restrictScalars _
  suffices key : (X.Theta Sc ka wL wF T).map Φ.toLinearMap ≤ X.Theta Sc ka wL wF T from
    fun x hx => key ⟨x, hx, rfl⟩
  change ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Φ (X.inc wL F) = X.inc wL F' at hL
  change ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Φ (X.inc w F) = X.inc w F' at hS
  have hsm : ∀ (s : 𝓞 B.KO) w (F : B.Cusp j w), X.inc w (s • F) = s • X.inc w F := fun s w F =>
    ((X.inc w).restrictScalars (𝓞 B.KO)).map_smul s F
  have hsc : ∀ (s : 𝓞 B.KO) w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') →
      ∀ F ∈ X.scaled s w N, ∃ F' ∈ X.scaled s w N, Φ (X.inc w F) = X.inc w F' := by
    rintro s w N hN _ ⟨F, hF, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    refine ⟨_, ⟨F', hF', rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, hsm, map_smul, e]
  have hemb : ∀ w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') → (X.emb w N).map Φ.toLinearMap ≤ X.emb w N := by
    rintro w N hN _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    exact ⟨F', hF', e.symm⟩
  have h1 : (X.emb wL (X.WWc Sc.sW wL)).map Φ.toLinearMap ≤ X.emb wL (X.WWc Sc.sW wL) :=
    hemb _ _ (hsc _ _ _ hL)
  have h2 : ∀ s w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) →
      (X.emb w (X.Thc s w)).map Φ.toLinearMap ≤ X.emb w (X.Thc s w) := fun s w hw =>
    hemb _ _ (hsc _ _ _ (hsc _ _ _ (hS w hw)))
  unfold WeightAlgebra.PJ.Theta
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_mul, Submodule.map_mul, Submodule.map_pow, Submodule.map_pow]
  refine sup_le_sup (sup_le_sup (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inl rfl)))
    (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inr (Or.inl rfl))))) (h2 _ _ (Or.inr (Or.inr rfl)))

theorem map_mem_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) (ψ : R j →ₗ[K] R j)
    (hs : ∀ f ∈ s, ∃ (u : 𝓞 K) (f' : R j), f' ∈ s ∧ ψ f = (u : K) • f') (F F' : cutR C j w) (e : F'.1 = ψ F.1) (hF : F ∈ spanIn C j w s) :
    F' ∈ spanIn C j w s := by
  change F'.1 ∈ Submodule.span (𝓞 K) s
  rw [e]
  have hle : (Submodule.span (𝓞 K) s).map (ψ.restrictScalars (𝓞 K)) ≤ Submodule.span (𝓞 K) s := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨u, f', hf', e'⟩ := hs f hf
    have e'' : ψ f = u • f' := e'.trans (algebraMap_smul K u f')
    change ψ f ∈ Submodule.span (𝓞 K) s
    rw [e'']
    exact Submodule.smul_mem _ u (Submodule.subset_span hf')
  exact hle ⟨F.1, hF, rfl⟩

theorem coe_one_smul_eq {K : Type} [Field K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] (j : ℕ)
    (x : R j) : x = ((1 : 𝓞 K) : K) • x := by
  simp

noncomputable def actLevAlg {D : D7} (T : Top D) (j : ℕ)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₐ[T.Q.c.F] T.R j :=
  AlgHom.ofLinearMap (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ) rfl (fun _ _ => rfl)

theorem levAct_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j), LawsFull T → (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (Sc : WeightAlgebra.Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ∀ (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j ka → (recB h.toLawsCore).Cusp j ka), IsLevAct T.toTop h j ka ℓ act → ∀ g F, (recPJ h j hj).inc ka F ∈ (recPJ h j hj).Theta Sc ka wL wF Tn → (recPJ h j hj).inc ka (act g F) ∈ (recPJ h j hj).Theta Sc ka wL wF Tn := by
  intro hC D T h j hj hfull hxi Sc ka wL wF Tn _ hn _ hr P ℓ act hact g F hF
  let ψ := actLevAlg T.toTop j (ℓ g)
  let Φ0 : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] AddMonoidAlgebra (T.R j) (Deg D j) :=
    AddMonoidAlgebra.mapAlgHom (Deg D j) ψ
  let Φ : @AlgHom _ _ _ _ _ _ (recPJ h j hj).aF (recPJ h j hj).aF := Φ0
  have hΦ : ∀ w (F F' : (recB h.toLawsCore).Cusp j w), F'.1 = ψ F.1 →
      Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w F F' e
    change Φ0 (AddMonoidAlgebra.single (deg w) F.1) = AddMonoidAlgebra.single (deg w) F'.1
    rw [e]
    exact AddMonoidAlgebra.mapAlgHom_single _ _ _
  have hspan : ∀ w (s : Set (T.R j)), (∀ f ∈ s, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ s ∧ ψ f = (u : T.Q.c.F) • f') →
      ∀ F ∈ spanIn T.C j w s,
      ∃ F' ∈ spanIn T.C j w s, Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w s hs F hF
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelChangeAction_on_cuspForms D T.toTop h j hj w P ℓ
    exact ⟨a g F, map_mem_spanIn T.C j w s ψ.toLinearMap hs F _ (ha g F) hF, hΦ w F _ (ha g F)⟩
  have hone : ∀ x : T.R j, x = ((1 : 𝓞 T.Q.c.F) : T.Q.c.F) • x := fun x => coe_one_smul_eq (R := T.R) j x
  have key := theta_stable_of_algHom (recPJ h j hj) Φ Sc ka wL wF Tn
    (hspan wL (T.th j wL) fun f hf => by
      obtain ⟨_, hnab⟩ := h.nabPin j hj
      exact ⟨1, ψ f, GlobalTheory.T.levelAction_mem_thetaSeries hC D T.toTop h j hj wL (ℓ g) f hf
        (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hnab _ _ f hf), hone _⟩)
    (fun w hw => hspan w (T.toTop.sh j w) fun f hf => GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul hC D T hfull j hj hxi w (by
      rcases hw with rfl | rfl | rfl
      · exact hr
      · exact hr.trans (Nat.le_add_right _ _)
      · rw [hn]; exact hr.trans (Nat.le_add_right _ _)) (ℓ g) f hf)
  rw [← hΦ ka F (act g F) (hact g F)]
  exact key _ hF

end GlobalTheory.FormTies
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem ramOverZ_pos_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  rw [Crude.crv_vLa_natCast_eq] at h
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) < 1 :=
    (la.intValuation_lt_one_iff_mem _).2 (Crude.crv_char_mem la)
  have h2 : WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  omega

theorem vV_eq_zero_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem nuW_le_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hA hH E _ _ _ H Dw l Xo c inst hst f vd hvd hsp hT la hla k n a ha hn Ap hAp hle
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  have hE : IntChartEx Xo c := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.1 hst
  refine max_le ?_ ?_
  · rw [EReal.coe_nonneg]
    positivity
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  have hv : vV T.V ((p : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, ← hla, Crude.crv_vLa_char]
  have he : 0 < e := ho.1
  have hnu : ¬ IsUnit ((p : ℕ) : T.V) := by
    intro hu
    have h0 := vV_eq_zero_of_isUnit T hu
    rw [map_natCast, hv] at h0
    have := ramOverZ_pos_place la
    have : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
    omega
  refine (iInf_le _ C).trans ((GlobalTheory.T.integralChartDepth_le_residueChar_two p hA hH E H Dw l Xo c T io y C hy hnu hsp f vd hvd hT e k n a he ha hn Ap hAp hle).trans (le_of_eq ?_))
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hv, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_cancel_left₀ _ he']

end GlobalTheory.CharDepth
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem levelZeroForm_cutoff_tendsto_of_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c)) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR f 0 w [] []).re) := by
  intro hX hP Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.levelZero_cutoff_eq_bigCell_integral hP Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero hX hP Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N Y hD hχ hf hA hC hdom w hw hN
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') hC
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') hC
  have hd := hdom w hw hN
  have hid := h2 Wp Wq P p f χ A N w hD hχ hf hA hC2 hw.1 hN hd
  have hform := h1 Wp Wq P p f χ A N w hD hχ hf hA hC1 hw.1 hN
  have hptw := GlobalTheory.T.topDensity_cutoff_eventually_eq_smoothCoefficient Wp Wq P p Cb f χ w hD hχ hf hw.1
  obtain ⟨hm, h, hi, hb⟩ := hd
  have key := tendsto_integral_filter_of_dominated_convergence h hm hb hi
    (hptw.mono fun c hc => tendsto_const_nhds.congr' (hc.mono fun _ e => e.symm))
  rw [hid] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hform ε hε).symm

end GlobalTheory
end
