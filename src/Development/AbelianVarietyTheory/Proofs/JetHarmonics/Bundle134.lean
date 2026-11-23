module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle100
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle106
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle091
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPieri

theorem gg_mul {k r : ℕ} {a b : Mx k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem one_gg (k r : ℕ) : (1 : Mx k r) ∈ GG k r := by
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem one_N (k r : ℕ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
  ⟨one_gg k r, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩

theorem one_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z :=
  ⟨one_gg k r, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem herm_iso {ι : Type} [Fintype ι] [DecidableEq ι] {Γ A : Matrix ι ι ℂ} (hA : Aᴴ * Γ * A = Γ) (x y : ι → ℂ) :
    Formalism.QuantumDeterminants.herm Γ (A *ᵥ x) (A *ᵥ y) = Formalism.QuantumDeterminants.herm Γ x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

theorem coef_inv {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ}
    {d : ℕ} (hρ : IsFRep ρ Γ d) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {om om' : ι → ℂ}
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) (h2 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om')
    {γ : Mx k r} (hγ : γ ∈ GG k r) (p : B.SS k r) (hp : D.inSS p) :
    Formalism.QuantumDeterminants.herm Γ (ρ (B.sgs p γ) *ᵥ om') om = Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  obtain ⟨-, -, -, hmul, hiso, -⟩ := hρ
  have hi := PI.MirrorSection₂.uw_inv hh
  have ni := PI.MirrorSection₂.n_inv hn
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GG k r := gg_mul hi.1 ni.1
  have e1 := h1 _ ⟨_, hi, _, ni, rfl⟩
  have e2 : ρ (Matrix.of p.2.1) *ᵥ om' = om' := h2 _ ⟨_, hh', 1, one_N k r, (Matrix.mul_one _).symm⟩
  have e3 : ρ (Matrix.of p.2.2) *ᵥ om' = om' := h2 _ ⟨1, one_UW k r _, _, hn', (Matrix.one_mul _).symm⟩
  unfold B.sgs
  rw [hmul _ (gg_mul (gg_mul ha hγ) hn'.1) _ hh'.1, hmul _ (gg_mul ha hγ) _ hn'.1, hmul _ ha _ hγ,
    ← mulVec_mulVec, e2, ← mulVec_mulVec, e3, ← mulVec_mulVec]
  conv_lhs => rw [← e1]
  exact herm_iso (hiso _ ha) _ _

theorem pieri_bessel : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDS ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  intro H k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI h Wp _ _ _ _ Wq _ _ _ _ D om om' l l' lI lI' F s FI sI τ
    hR _ hRI hgap hρ hT h1 h2 hBe hF hτ γ hγ
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨Ft, st, hFt, hsum, hz, hst⟩ := GlobalTheory.T.tensor_weighted_bessel_sum H.1.2.2.1 k r ι κ ρ Γ d R RI io pr ep ε mu muI Wp Wq om om'
    l l' lI lI' F s hR (fun I => (hRI I).1) hρ hT hF
  obtain ⟨hloc, hfac, hfin, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  have hOO := fun I => GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul H k r ε (muI I) h (RI I) Wp Wq D (lI I) (lI' I) (hRI I).1 (hRI I).2 hgap
    (hBe I).1 (hBe I).2
  choose OO hOO using hOO
  rw [← hfac (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om) F (fun p hp => coef_inv hρ D h1 h2 hγG p hp),
    (hloc _ (fun g => ∑ I, Ft I g) hsum).1, hfin κ Ft (fun I => (hOO I _ _ (hFt I) γ hγ).1)]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hOO I _ _ (hFt I) γ hγ).2]
  rcases hτ I with ⟨hn, h0⟩ | ⟨hc, hs, κ₀, κ₁, a0, a1, ht⟩
  · rw [hz I hn, h0, zero_smul, zero_smul]
  · rw [(hOO I _ _ hc γ hγ).2, hst I κ₀ κ₁ a0 a1, ht, smul_smul, div_mul_cancel₀ _ hs]

end GlobalTheory.BesselPieri
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_adelic_of_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  intro D V H Dw io hio hEF s hν
  obtain ⟨hinj, hrange⟩ := hio
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : D.host.xi0 ≠ 0 := by
    have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
    have h2 : D.host.sqrtMinusD ≠ 0 := by
      intro h
      have := D.host.sqrtMinusD_sq
      rw [h] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := by
        have := D.host.qd_big.2
        exact_mod_cast (by omega : D.host.d ≠ 0)
      apply hd
      linear_combination this
    exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hA : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 *
      ∑ a, ∑ b, io x a * (-V.gram.transpose) a b * c (io y b)) := by
    intro x y
    rw [hEF, ← trace_herm_gmW V rfl, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    D.host.xi0 hξ Dw.La Dw.La (fun x y => Dw.EF x y) (fun x y => Dw.EF x y) io hinj
    (LinearMap.range io) (LinearEquiv.ofInjective io hinj) hfg hsp hfg hsp hA hA s.f
    (fun n m hn hm a => by
      obtain ⟨e, he⟩ := s.tower n m hn hm a
      exact ⟨e, by rw [← he, add_sub_cancel]⟩)
    (fun n hn => by
      obtain ⟨g, hg⟩ := s.inv n hn
      refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
      · rintro ⟨e, he⟩
        obtain ⟨b, hb⟩ := (hg a).1
        exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul, sub_sub_cancel]⟩
      · rintro ⟨e, he⟩
        exact ⟨s.f n e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, hb⟩ := (hg a').2
        exact ⟨g a', -b, by rw [smul_neg, ← hb, neg_sub, add_sub_cancel]⟩)
    (fun n hn a a' => by
      have := s.mult n hn a a'
      rwa [hν, one_mul] at this)
  obtain ⟨u, -, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have h1 : (latGHat V 1 : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      AdLat.hat D.host.F (LinearMap.range io : Set (Fin V.rank → D.host.E)) := by
    rw [(hlat 1).2, map_one, Units.val_one]
    ext z
    simp
  refine ⟨u, SetLike.coe_injective ?_, fun N hN a => ?_⟩
  · rw [(hlat u).2, hug, hg1, h1]
  · obtain ⟨w, hw, hgw⟩ := hg2 N hN a
    refine ⟨w, ?_, ?_⟩
    · rw [← SetLike.mem_coe, h1]
      exact hw
    · rw [hug]
      exact hgw

end GlobalTheory.ShortMove
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.TypeGlModule

theorem hyp_and_adj :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ)
      (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ)
      (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)),
      inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L →
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) →
      IsFrameOf (n + 1) r [z] B →
      Hyp (EB π B) β L ∧ ∀ a b x y, inner ℂ (EB π B a b x) y = inner ℂ x (EB π B b a y) := by
  intro V _ _ _ n r z π u β L B hz hT hty hL hu hB
  obtain ⟨hnt, hrep, hcont, hunit, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear V (n + 1) r (n + 1) z π B hR hB
  refine ⟨?_, fun a b x y => Formalism.FourierDecayAlt.P5.Kfp.EB_adj hrep hcont hunit hB a b x y⟩
  refine ⟨hgl, ⟨hnt, fun S hS =>
    hirr S (Formalism.FourierDecayAlt.P.lie_stabilizer V (n + 1) r z π B hz hT hR hB S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap B hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

end GlobalTheory.TypeGlModule
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem adjoint_mem_CapSp_subA : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (T : V₂ →L[ℂ] V₁) (μ : Fin n → ℂ), IsRepW (n + 1) r z π₁ → IsRepW (n + 1) r z π₂ → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₁ h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₂ h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → (∀ h ∈ UWset (n + 1) r z, h *ᵥ B (Fin.last n) = B (Fin.last n) → T.comp (π₂ h) = (π₁ h).comp T) → ∀ v ∈ CapSp (subA (EB π₁ B)) μ, ContinuousLinearMap.adjoint T v ∈ CapSp (subA (EB π₂ B)) μ := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ B T μ h₁ h₂ hu₁ hu₂ hB hT v hv
  have hB' : IsFrameOf (n + 1) r [z, B (Fin.last n)] (fun a : Fin n => B a.castSucc) := by
    refine ⟨fun a => hB.1 _, fun a b => ?_, fun a x hx => ?_⟩
    · rw [hB.2.1]
      simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact hB.2.2 _ x (by simp [hx])
      · rw [hx, hB.2.1, if_neg (Fin.castSucc_lt_last a).ne]
  have hlie := GlobalTheory.intertwiner_EB_of_stabiliser V₂ V₁ (n + 1) r n z (B (Fin.last n)) π₂ π₁ T
    (fun a : Fin n => B a.castSucc) h₂ h₁ hB' (fun h hh he w => by
      have := congrArg (fun S : V₂ →L[ℂ] V₁ => S w) (hT h hh he)
      simpa using this)
  have hlie' : ∀ (a b : Fin n) (w : V₂),
      T (EB π₂ B a.castSucc b.castSucc w) = EB π₁ B a.castSucc b.castSucc (T w) := hlie
  have hadj : ∀ (a b : Fin n) (w : V₁),
      (ContinuousLinearMap.adjoint T).toLinearMap (subA (EB π₁ B) a b w) =
        subA (EB π₂ B) a b ((ContinuousLinearMap.adjoint T).toLinearMap w) := by
    intro a b w
    apply ext_inner_right ℂ
    intro y
    show inner ℂ (ContinuousLinearMap.adjoint T (EB π₁ B a.castSucc b.castSucc w)) y =
      inner ℂ (EB π₂ B a.castSucc b.castSucc (ContinuousLinearMap.adjoint T w)) y
    rw [ContinuousLinearMap.adjoint_inner_left,
      Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₁.1 h₁.2 hu₁ hB, Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₂.1 h₂.2 hu₂ hB,
      ContinuousLinearMap.adjoint_inner_left, hlie']
  rw [mem_CapSp] at hv ⊢
  intro w
  have hq := qminor_intertwine V₂ V₁ n n (subA (EB π₂ B)) (subA (EB π₁ B))
    (ContinuousLinearMap.adjoint T).toLinearMap hadj id id w v
  have hq' : ContinuousLinearMap.adjoint T (qdet (subA (EB π₁ B)) w v) =
      qdet (subA (EB π₂ B)) w (ContinuousLinearMap.adjoint T v) := hq
  rw [← hq', hv w, map_smul]

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.CapelliTop

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sum_smul {t n : ℕ} (q : Fin t → Fin n → ℂ) (x : Fin t → Fin n → A) :
    (List.ofFn fun k : Fin t => ∑ d, q k d • x k d).prod =
      ∑ d : Fin t → Fin n, (∏ k, q k (d k)) • (List.ofFn fun k => x k (d k)).prod := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply]
  simp only [RingHom.id_apply]

theorem qminor_eq_zero {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (d : Fin n → Fin n)
    (hd : ¬ Function.Injective d) (u : ℂ) : qminor E id d u = 0 := by
  simp only [Function.Injective, not_forall] at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have h := quantumMinorColSkew_holds A n n E hE id d (Equiv.swap i j) u
  have e : d ∘ Equiv.swap i j = d := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [e, Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_add_self_eq_zero
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  exact add_eq_zero_iff_eq_neg.mpr h

theorem det_smul_qdet {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u : ℂ) : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod := by
  classical
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • qminor E id d u := by
    simp only [Finset.smul_sum, qminor]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [prod_ofFn_sum_smul (fun k d => Q k d) (fun k d => Tm E (u - (k : ℂ)) (σ k) d),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  rw [h1, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro d hd
    rw [qminor_eq_zero E hE d, smul_zero]
    intro hinj
    exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.mp hinj), rfl⟩
  · intro τ
    have h := quantumMinorColSkew_holds A n n E hE id id τ u
    rw [Function.id_comp] at h
    rw [h, mul_comm, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl

theorem mul_pow_shift (x y δ : A) (h : x * δ = δ * (x + y)) (hy : y * δ = δ * y) (s : ℕ) :
    x * δ ^ s = δ ^ s * (x + (s : ℂ) • y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, add_mul, h, smul_mul_assoc, hy,
      Nat.cast_succ, add_smul, one_smul, ← mul_smul_comm, ← mul_add]
    congr 2
    abel

theorem prod_ofFn_semiconj {t : ℕ} (x y : Fin t → A) (g : A) (h : ∀ k, x k * g = g * y k) :
    (List.ofFn x).prod * g = g * (List.ofFn y).prod := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ (fun k => h k.succ), ← mul_assoc, h, mul_assoc]

theorem pt_prod {t : ℕ} (x y : Fin t → A) :
    TL.PT t (fun s : ℂ => (List.ofFn fun k => x k + s • y k).prod) (List.ofFn y).prod := by
  induction t with
  | zero => exact (TL.PT.const 1).congr (fun s => by simp) (by simp)
  | succ t ih =>
    have h := ih (fun k => x k.succ) (fun k => y k.succ)
    refine ((h.mulL (x 0)).up.add (h.mulL (y 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem sum_smul_Tm {n : ℕ} (E : Fin n → Fin n → A) (q : Fin n → ℂ) (u : ℂ) (a : Fin n) :
    ∑ d, q d • Tm E u a d = (q a * u) • (1 : A) + ∑ d, q d • E a d := by
  simp [shiftedGenerator_eq_ite_smul_add, Finset.sum_add_distrib, smul_smul, ite_smul]

theorem top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  intro A _ _ p m E Q δ ν u hE h1 h2 h3
  set X : Equiv.Perm (Fin (p + m)) → Fin p → A := fun σ k =>
    ∑ d, Q (Fin.castAdd m k) d • Tm E (u - ((k : ℕ) : ℂ)) (σ (Fin.castAdd m k)) d with hX
  set Y : Equiv.Perm (Fin (p + m)) → A := fun σ => (List.ofFn fun k : Fin m =>
    ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod with hY
  have e1 : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn (X σ)).prod * Y σ) := by
    rw [det_smul_qdet E hE]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [List.ofFn_add, List.prod_append]
    simp only [hX, hY, Fin.val_natAdd, Nat.cast_add, sub_sub]
    rfl
  have eY : ∀ σ (s : ℕ), Y σ * δ ^ s = δ ^ s * Y σ := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => Commute.pow_right (?_ : _ * _ = _ * _) s
    rw [sum_smul_Tm, add_mul, mul_add, h2]
    simp
  have eX : ∀ σ (s : ℕ), (List.ofFn (X σ)).prod * δ ^ s =
      δ ^ s * (List.ofFn fun k => X σ k + (s : ℂ) • ν (σ (Fin.castAdd m k)) k).prod := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => mul_pow_shift _ _ _ ?_ (h3 _ _) s
    simp only [hX]
    rw [sum_smul_Tm, add_mul, h1, add_assoc, mul_add δ (_ • _)]
    simp
  have e2 : ∀ s : Fin (p + 1), Q.det • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) =
      ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (δ ^ p *
        ((List.ofFn fun k => X σ k + ((s : ℕ) : ℂ) • ν (σ (Fin.castAdd m k)) k).prod * Y σ)) := by
    intro s
    rw [← mul_smul_comm, ← smul_mul_assoc, e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, eY, ← mul_assoc _ (δ ^ (s : ℕ)), eX, mul_assoc,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)]
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_comm Q.det, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := (((pt_prod (X σ) (fun k => ν (σ (Fin.castAdd m k)) k)).mulR (Y σ)).mulL (δ ^ p)).lag
  rw [mul_smul_comm]
  refine Eq.trans ?_ (congrArg _ h.symm)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

end GlobalTheory.CapelliTop
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

theorem exists_isometry_of_isType_of_param_eq :
    ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (u₁ u₂ : ℕ → ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π₁ u₁ → IsType (n + 1) r z π₂ u₂ → (∀ i ∈ Finset.Icc 1 (n + 1), u₁ i = u₂ i) → ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ h ∈ UWset (n + 1) r z, ∀ v, φ (π₁ h v) = π₂ h (φ v) := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ u₁ u₂ hz hT ht₁ ht₂ hu
  obtain ⟨hnt₁, hrep₁, hcont₁, hn₁, hirr₁, hcap₁⟩ := ht₁
  obtain ⟨hnt₂, hrep₂, hcont₂, hn₂, hirr₂, hcap₂⟩ := ht₂
  have hR₁ : IsRepW (n + 1) r z π₁ := ⟨hrep₁, hcont₁⟩
  have hR₂ : IsRepW (n + 1) r z π₂ := ⟨hrep₂, hcont₂⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), IsFrameOf (n + 1) r [z] B :=
    Qx8.frame_exists hz hT
  obtain ⟨g₁, q₁⟩ := frame_general_linear V₁ (n + 1) r (n + 1) z π₁ B hR₁ hB
  obtain ⟨g₂, q₂⟩ := frame_general_linear V₂ (n + 1) r (n + 1) z π₂ B hR₂ hB
  have i₁ : Irr (EB π₁ B) :=
    ⟨hnt₁, fun S hS => hirr₁ S (lie_stabilizer V₁ (n + 1) r z π₁ B hz hT hR₁ hB S hS)⟩
  have i₂ : Irr (EB π₂ B) :=
    ⟨hnt₂, fun S hS => hirr₂ S (lie_stabilizer V₂ (n + 1) r z π₂ B hz hT hR₂ hB S hS)⟩
  let m : Fin (n + 1) → ℂ := fun j => (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2
  have hc : ∀ w : ℂ, (∏ i ∈ Finset.Icc 1 (n + 1), (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 + (u₁ i : ℂ))) =
      cpol m w := by
    intro w
    rw [FrameExtension.prod_Icc_fin]
    unfold cpol
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [m]
    ring
  have c₁ : ∀ w v, qdet (EB π₁ B) w v = cpol m w • v := by
    intro w v
    rw [← q₁ w v, hcap₁ B hB w v, hc]
  have c₂ : ∀ w v, qdet (EB π₂ B) w v = cpol m w • v := by
    intro w v
    rw [← q₂ w v, hcap₂ B hB w v, ← hc]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by rw [hu i hi])
  obtain ⟨T, hTE⟩ := exists_linearEquiv_of_irreducible_capelli V₁ V₂ (n + 1) _ _ m g₁ g₂ i₁ i₂ c₁ c₂
  have hG := intertwiner_group_of_EB V₁ V₂ (n + 1) r z π₁ π₂ (T : V₁ →ₗ[ℂ] V₂) B hz hT hR₁ hR₂ hB hTE
  obtain ⟨φ, hφ⟩ := exists_isometry_of_intertwiner_of_irreducible V₁ V₂ (UWset (n + 1) r z)
    (fun h => π₁ h.1) (fun h => π₂ h.1) T (fun h v => hn₁ h.1 h.2 v) (fun h v => hn₂ h.1 h.2 v)
    (fun S hS => hirr₁ S (fun h hh v hv => hS ⟨h, hh⟩ v hv)) (fun h v => hG h.1 h.2 v)
  exact ⟨φ, fun h hh v => hφ ⟨h, hh⟩ v⟩

end GlobalTheory
end
