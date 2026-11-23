module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_add_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_add_dir_of_hasLevel <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_smul_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.iterated_derivative_eq_hilbert_eisenstein_jet : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t : ℂ) (κ : Emb F → ℕ) (u : List (Emb F)), 0 < τ.im → (∀ i, u.count i = κ i) → iterD u (fun z ↦ (cK F (2 * s) : ℂ) * gval (2 * s) L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 = jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.iterD_eq_jet_of_count | exact GlobalTheory.HilbFam.iterD_eq_jet_of_count | (intros; apply GlobalTheory.HilbFam.iterD_eq_jet_of_count <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.DRAct

section Pull

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} (κ : DividedPowers I) (t : S ⟶ Sp R)
  {A : Over S} [GrpObj A]

theorem primPull_of_eq_id (f : A ⟶ A) [IsMonHom f] (h : f = 𝟙 A) (c : prim κ t A) : primPull κ t f c = c := by
  subst h
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem primPull_of_eq_comp (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f ≫ g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f (primPull κ t g c) := by
  subst h
  exact (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c).symm

theorem primPull_of_eq_mul (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f * g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f c + primPull κ t g c := by
  subst h
  exact Subtype.ext (c.2 A f g)

end Pull

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] (i : OAct O A)

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

end GlobalTheory.AbDatum.DRAct
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Adelic

theorem subset_of_forall_pt_mem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y), IsClosed Z → ∀ U : Set S.Y, IsOpen U →
    (∀ x : S.Pt Ω, ptOf x.1 ∈ Z → ptOf x.1 ∈ U) → Z ⊆ U := by
  intro k _ S hS Ω _ _ _ Z hZ U hU h
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : LocallyOfFiniteType S.str := inferInstance
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  by_contra hne
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 hne
  obtain ⟨y, ⟨hyZ, hyU⟩, hy⟩ := nonempty_inter_closedPoints (Z := Z ∩ Uᶜ) ⟨z, hzZ, hzU⟩
    (hZ.inter hU.isClosed_compl).isLocallyClosed
  have hyc : IsClosed ({y} : Set S.Y) := hy
  haveI : IsFinite (resPt y ≫ S.str) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hyc
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    unfold resPt
    infer_instance
  have hφ : (S.baseHom (resPt y)).IsIntegral := by
    have : IsIntegralHom (Spec.map (Spec.preimage (resPt y ≫ S.str))) := by
      rw [Spec.map_preimage]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at this
    exact this
  letI : Algebra k (S.Y.residueField y) := (S.baseHom (resPt y)).toAlgebra
  haveI : Algebra.IsIntegral k (S.Y.residueField y) := ⟨hφ⟩
  let τ : S.Y.residueField y →ₐ[k] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let x : S.Pt Ω := ⟨spMap τ.toRingHom ≫ resPt y, by
    rw [Category.assoc, S.comp_str, ← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a⟩
  have hx : ptOf x.1 = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  exact hyU (hx ▸ h x (hx.symm ▸ hyZ))

end GlobalTheory.Adelic
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.SectionGrowth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B : LB Y}

theorem local_factor (hB : B.IsLB) {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ B)
    (hc : ∀ j, ContinuousOn (s j) (ptsIn p σ (B.U j))) {i : B.ι} {V Q : Y.Opens} (hV : V ≤ B.U i)
    (u : Γ(Y, V)) (η : Γ(Y, Q)) (hη : Y.basicOpen η = Q ⊓ V)
    (hu : resG Y (inf_le_right : Q ⊓ V ≤ V) u * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1)
    {y₀ : CxPts p σ} (hy₀ : y₀ ∈ ptsIn p σ Q) :
    ∃ (F : CxPts p σ → ℂ) (N : ℕ), ContinuousAt F y₀ ∧
      ∀ᶠ y in 𝓝 y₀, y ∈ ptsIn p σ V → s i y = F y * ev p σ V u y ^ N := by

  obtain ⟨j, hy₀j⟩ : ∃ j, y₀ ∈ ptsIn p σ (B.U j) := ⟨_, mem_pick hB y₀⟩
  obtain ⟨W, hWa, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (Opens.mem_inf.2 ⟨mem_ptsIn.1 hy₀, mem_ptsIn.1 hy₀j⟩ :
      y₀.1 (IsLocalRing.closedPoint ℂ) ∈ Q ⊓ B.U j)
  have hWQ : W ≤ Q := hWle.trans inf_le_left
  have hWj : W ≤ B.U j := hWle.trans inf_le_right
  have hy₀W : y₀ ∈ ptsIn p σ W := mem_ptsIn.2 hzW

  set η' : Γ(Y, W) := resG Y hWQ η with hη'
  have hD : Y.basicOpen η' = W ⊓ (Q ⊓ V) := by
    rw [← hη]
    exact Y.basicOpen_res η (homOfLE hWQ).op
  have hDij : Y.basicOpen η' ≤ B.U i ⊓ B.U j := by
    rw [hD]
    exact le_inf (inf_le_right.trans (inf_le_right.trans hV)) (inf_le_left.trans hWj)

  have := hWa.isLocalization_basicOpen η'
  obtain ⟨⟨a, _, n, rfl⟩, han⟩ :=
    IsLocalization.surj (Submonoid.powers η') (resG Y hDij (B.g i j).val)
  rw [map_pow] at han
  refine ⟨fun y => ev p σ W a y * s j y, n, ?_, ?_⟩
  · exact ((continuousOn_ev a).continuousAt ((isOpen_ptsIn W).mem_nhds hy₀W)).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hy₀j))
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hy₀W] with y hyW hyV
    have hyQ : y ∈ ptsIn p σ Q := ptsIn_mono hWQ hyW
    have hyj : y ∈ ptsIn p σ (B.U j) := ptsIn_mono hWj hyW
    have hyi : y ∈ ptsIn p σ (B.U i) := ptsIn_mono hV hyV
    have hyQV : y ∈ ptsIn p σ (Q ⊓ V) := mem_ptsIn_inf.2 ⟨hyQ, hyV⟩
    have huv : ev p σ V u y * ev p σ Q η y = 1 := by
      have h1 := congrArg (fun f => ev p σ (Q ⊓ V) f y) hu
      rwa [ev_mul, ev_res _ hyQV, ev_res _ hyQV, ev_one hyQV] at h1
    have hηne : ev p σ Q η y ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at huv
      exact zero_ne_one huv
    have hηW : ev p σ W η' y = ev p σ Q η y := ev_res hWQ hyW η
    have hyD : y ∈ ptsIn p σ (Y.basicOpen η') :=
      (mem_ptsIn_basicOpen hyW η').2 (hηW ▸ hηne)
    have hal : ∀ b : Γ(Y, W),
        ev p σ (Y.basicOpen η') (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen η') b) y = ev p σ W b y :=
      fun b => ev_res (Y.basicOpen_le η') hyD b
    have e1 := congrArg (evHom hyD) han
    rw [map_mul, map_pow, ← ev_eq hyD, ← ev_eq hyD, ← ev_eq hyD, hal, hal, ev_res hDij hyD,
      hηW] at e1
    have hg : gv p σ B i j y = ev p σ (B.U i ⊓ B.U j) (B.g i j).val y := rfl
    have hun : (ev p σ V u y * ev p σ Q η y) ^ n = 1 := by rw [huv, one_pow]
    show s i y = ev p σ W a y * s j y * ev p σ V u y ^ n
    rw [hs.1 i j y hyi hyj, hg]
    linear_combination (s j y * ev p σ V u y ^ n) * e1 -
      (ev p σ (B.U i ⊓ B.U j) (B.g i j).val y * s j y) * hun

theorem global_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] (S : Set X) (f T : X → ℝ)
    (hT : ∀ x, 1 ≤ T x)
    (h : ∀ x₀, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀, x ∈ S → f x ≤ C * T x ^ m) :
    ∃ (C : ℝ) (m : ℕ), ∀ x ∈ S, f x ≤ C * T x ^ m := by
  choose C m hC hev using h
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x₀ => {x | x ∈ S → f x ≤ C x₀ * T x ^ m x₀}) (fun x₀ _ => hev x₀)
  refine ⟨∑ x₀ ∈ t, C x₀, t.sup m, fun x hx => ?_⟩
  obtain ⟨x₀, hx₀t, hx₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have h1 : f x ≤ C x₀ * T x ^ m x₀ := hx₀ hx
  have h2 : T x ^ m x₀ ≤ T x ^ t.sup m := pow_le_pow_right₀ (hT x) (Finset.le_sup hx₀t)
  have h3 : C x₀ ≤ ∑ x₀ ∈ t, C x₀ := Finset.single_le_sum (fun i _ => hC i) hx₀t
  have h4 : 0 ≤ T x ^ t.sup m := pow_nonneg (zero_le_one.trans (hT x)) _
  calc f x ≤ C x₀ * T x ^ m x₀ := h1
    _ ≤ C x₀ * T x ^ t.sup m := mul_le_mul_of_nonneg_left h2 (hC x₀)
    _ ≤ (∑ x₀ ∈ t, C x₀) * T x ^ t.sup m := mul_le_mul_of_nonneg_right h3 h4

end GlobalTheory.SectionGrowth

namespace GlobalTheory

theorem continuous_section_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), V ≤ B.U i → (∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧ resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1) → ∃ (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V n u hV hloc
  have := CxPts.compactSpace (RingHom.id ℂ) hp
  obtain ⟨C, m, hCm⟩ := SectionGrowth.global_bound (ptsIn p (RingHom.id ℂ) V) (fun y => ‖s i y‖)
    (fun y => 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖)
    (fun y => le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => norm_nonneg _)) (by
      intro y₀
      obtain ⟨Q, η, l, hzQ, hη, hu⟩ := hloc (y₀.1 (IsLocalRing.closedPoint ℂ))
      obtain ⟨F, N, hF, hev⟩ :=
        SectionGrowth.local_factor hB hs hc hV (u l) η hη hu (mem_ptsIn.2 hzQ)
      have hFb : ∀ᶠ y in 𝓝 y₀, ‖F y‖ < ‖F y₀‖ + 1 :=
        hF.norm.eventually (gt_mem_nhds (lt_add_one _))
      refine ⟨‖F y₀‖ + 1, N, by positivity, ?_⟩
      filter_upwards [hev, hFb] with y hy1 hy2 hyV
      have hle : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤
          1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := by
        have := Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ l)
        linarith
      show ‖s i y‖ ≤ (‖F y₀‖ + 1) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ N
      rw [hy1 hyV, norm_mul, norm_pow]
      exact mul_le_mul hy2.le (pow_le_pow_left₀ (norm_nonneg _) hle N) (by positivity)
        (by positivity))
  exact ⟨C, m, hCm⟩

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Obs

theorem retractLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri
  obtain ⟨e, he, hpe⟩ := GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])
  have hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range) := by
    intro x hx
    have hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro y hy
      simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact hle hx
  refine ⟨e.range, inferInstance, inferInstance,
    ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, GlobalTheory.T.smooth_range_of_idempotent_algHom R B' e he⟩
  · intro c b
    show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))
    rw [Subalgebra.coe_smul, hs' c (b : B'), map_smul]
  · intro y
    obtain ⟨b, hb⟩ := hp' (i y)
    refine ⟨⟨e b, e.mem_range_self b⟩, ?_⟩
    show r (p' (e b)) = y
    rw [hpe, hb]
    simp [hri]
  · intro b
    constructor
    · intro h
      change r (p' (b : B')) = 0 at h
      obtain ⟨c, hc⟩ := b.2
      change e c = (b : B') at hc
      have hfix : e (b : B') = b := by rw [← hc, he]
      have h0 : p' (b : B') = 0 := by
        rw [← hfix, hpe]
        simp [h]
      have hb : e.rangeRestrict (b : B') = b := Subtype.ext hfix
      rw [← hb]
      exact hmem _ ((hker' _).mp h0)
    · intro h
      have hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        have hx0 : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        show r (p' (algebraMap R B' x)) = 0
        rw [hs'.map_algebraMap, hx0, map_zero, map_zero]
      exact hle h

end GlobalTheory.Obs
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 =>
    rw [corrFam_zero, corrFam_zero]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 =>
    rw [corrFam_add_two, corrFam_add_two]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom

theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by simpa only [lineUnit_res] using hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by simpa only [lineUnit_res] using hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
end
end
