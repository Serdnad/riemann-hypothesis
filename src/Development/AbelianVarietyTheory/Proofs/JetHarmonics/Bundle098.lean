module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  first | exact @GlobalTheory.gN_rpow_neg_integrable_haar | exact GlobalTheory.gN_rpow_neg_integrable_haar | (intros; apply GlobalTheory.gN_rpow_neg_integrable_haar <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

end GlobalTheory.LeafCompare
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConjLevelMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevelFibre.sab_cast e.inv_hom_id.symm i
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

theorem conj_sec {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ≅ S₂}
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂.hom)
    (hr : ρ₂.hom ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {σ σ' : 𝟙_ (Over S₂) ⟶ t₂.G} {τ τ' : 𝟙_ (Over S) ⟶ t.G} (k : ℕ)
    (h₂ : σ'.left ≫ ν₂.φ = ρ₂.hom ≫ σ.left) (hm : (σ' ^ k).left ≫ m.φ = r ≫ τ'.left)
    (h : τ'.left ≫ ν.φ = ρ ≫ τ.left) : (σ ^ k).left ≫ m'.φ = r' ≫ τ.left := by
  have e := OverMove.pow_left_comp ν₂ h₂ k
  have a₁ : ρ₂.hom ≫ (σ ^ k).left ≫ m'.φ = ((σ' ^ k).left ≫ m.φ) ≫ ν.φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m'.φ) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((σ' ^ k).left ≫ ·) hφ).trans (Category.assoc _ _ _).symm)))
  have a₂ : (r ≫ τ'.left) ≫ ν.φ = ρ₂.hom ≫ r' ≫ τ.left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ τ.left) hr.symm).trans (Category.assoc _ _ _))))
  exact (cancel_epi ρ₂.hom).1 (a₁.trans ((congrArg (· ≫ ν.φ) hm).trans a₂))

end ConjLevelMap


open ConjLevelMap in
theorem exists_conj_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  intro E _ _ _ H Dw l Xo c n d hE ρ ν ρ₂ ν₂ gM gA gM₂ gA₂ h h₂ hM hA
  obtain ⟨i, hi⟩ := exists_inv ρ₂ ν₂
  obtain ⟨q, hq⟩ := ObjMaps.exists_sab_comp ν d.m
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_comp q i
  have hr : ρ₂.hom ≫ ρ₂.inv ≫ d.r ≫ ρ = d.r ≫ ρ := ρ₂.hom_inv_id_assoc _
  have hφ : ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ := by
    rw [hm', hq, ← Category.assoc, hi, Category.id_comp]
  have eM : ∀ a, Xo.univ.eta (gM₂ a) = Xo.univ.eta (gM a) := fun a => by
    rw [← sub_add_cancel (gM₂ a) (gM a), Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
  have eA : ∀ a, Xo.univ.etaA (gA₂ a) = Xo.univ.etaA (gA a) := fun a => by
    obtain ⟨x, hx⟩ := hA a
    rw [← sub_add_cancel (gA₂ a) (gA a), Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, _root_.one_mul]
  refine ⟨_, m', hr, hφ, fun a => ?_, fun a => ?_⟩
  · exact conj_sec d.m m' ν ν₂ hr hφ d.pd (h₂.2.1 a) (hE.1 (gM₂ a)) (by rw [eM]; exact h.2.1 a)
  · exact conj_sec d.m m' ν ν₂ hr hφ (d.l₂.A / l.A) (h₂.2.2 a) (hE.2 (gA₂ a)) (by rw [eA]; exact h.2.2 a)

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselSubgroup_product_measure_isHaar : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsMatGroup (Formalism.QuantumDeterminants.Sset k r z) ∧ Formalism.QuantumDeterminants.Sset k r z ⊆ GG k r ∧ PI.IsHaarOnM (Formalism.QuantumDeterminants.Sset k r z) (muSof μW μN) ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Sset k r z) (muSof μW μN) := by
  first | exact @GlobalTheory.muSof_isHaar | exact GlobalTheory.muSof_isHaar | (intros; apply GlobalTheory.muSof_isHaar <;> assumption)
end

section

open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
end

section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

end GlobalTheory.PlaceComponents
end
end
