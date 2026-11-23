module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section




namespace GlobalTheory.ColSplit

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.AdLat
open scoped TensorProduct

variable {D : D7}

theorem finite_part_apply (V W : HSp D) (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (i : Fin W.rank) (j : Fin V.rank) :
    (ratW W V Y - realPt V W Y : WO V W) i j = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
  change (1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j - (pairA D.host.F 1 0) ⊗ₜ[D.host.F] Y i j = _
  rw [← TensorProduct.sub_tmul]
  congr 1
  exact Prod.ext (sub_self (1 : Ainf D.host.F)) (sub_zero (1 : Af D.host.F))

def rk (V W : HSp D) (s : Fin V.rank → D.host.E) : (Fin W.rank → D.host.E) →+ WO V W where
  toFun c := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c i * ∑ k, star (s k) * V.gram k j)
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem rk_mem (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ LV) (c : Fin W.rank → D.host.E)
    (hc : c ∈ Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) :
    rk V W s c ∈ latO V W LV (L : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hc' := (GlobalTheory.OneMapRef.FactsLat.isAA_span L c).1 hc
  clear hc
  induction hc' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, fun _ h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def colF (V W : HSp D) (s : Fin V.rank → D.host.E) : WO V W →+ (Fin W.rank → RA D.host.F D.host.E) where
  toFun u := fun m => ∑ n, finPart D (u m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n)
  map_zero' := by ext m; simp
  map_add' y z := by
    ext m
    simp only [Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem colF_pure (V W : HSp D) (s : Fin V.rank → D.host.E) (α : Af D.host.F)
    (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    colF V W s (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] X i j) =
      fun m => α ⊗ₜ[D.host.F] ∑ n, X m n * s n := by
  funext m
  change ∑ n, (α ⊗ₜ[D.host.F] X m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.tmul_sum]

theorem colF_mem (V W : HSp D) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ GlobalTheory.Member.latC V) (u : WO V W)
    (hu : u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) (L : Set (Fin W.rank → D.host.E)) fun _ => True) :
    colF V W s u ∈ hat D.host.F ((Submodule.span (𝓞 D.host.E)
      {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v} : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) :
        Set (Fin W.rank → D.host.E)) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s', hs', t, ht, rfl⟩ := hx
    rw [colF_pure V W s α fun i j => a * t i * ∑ k, star (s' k) * V.gram k j]
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
      (((GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.2.2.2.2.2 s).2 hs s' hs')
    refine AddSubgroup.subset_closure ⟨α, hα, a • (r • t), Submodule.subset_span ⟨a, ha, _, L.smul_mem r ht, rfl⟩, ?_⟩
    funext m
    congr 1
    change _ = a * (algebraMap (𝓞 D.host.E) D.host.E r * t m)
    rw [hr]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    change _ = a * (s n * V.gram k n * star (s' k) * t m)
    ring
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem complete (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (n j : Fin V.rank) :
    ∑ a, b n a * ∑ k, star (b k a) * V.gram k j = if n = j then 1 else 0 := by
  have h1 : (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) * b = 1 := by
    ext a a'
    rw [Matrix.one_apply, ← hb.1 a a', Matrix.mul_apply, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_mul]
  have h3 : b * (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) = 1 := mul_eq_one_comm.1 h1
  have h2 := congrFun (congrFun h3 n) j
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  exact h2

theorem cols_iff_moved (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (y : GA D W)
    (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    (∀ a, (fun m => ∑ n, Y m n * b n a) ∈ latG W y) ↔
      (ratW W V Y - realPt V W Y : WO V W) ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hbm : ∀ a, (fun i => b i a) ∈ GlobalTheory.Member.latC V := fun a => by
    rw [← SetLike.mem_coe, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, hb.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  constructor
  · intro h
    have e : (ratW W V Y - realPt V W Y : WO V W) = ∑ a, rk V W (fun i => b i a) fun m => ∑ n, Y m n * b n a := by
      ext i j
      rw [finite_part_apply, Matrix.sum_apply]
      change _ = ∑ a, (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((∑ n, Y i n * b n a) * ∑ k, star (b k a) * V.gram k j)
      rw [← TensorProduct.tmul_sum]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, complete V b hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [e]
    refine sum_mem fun a _ => rk_mem V W _ _ _ (hbm a) _ ?_
    rw [← GlobalTheory.MovedLat.latG_eq]
    exact h a
  · intro h a
    have h1 := colF_mem V W _ _ (hbm a) _ h
    rw [← GlobalTheory.MovedLat.latG_eq] at h1
    have e : (ratW W V Y - realPt V W Y : WO V W) =
        Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
      ext i j; exact finite_part_apply V W Y i j
    rw [e, colF_pure] at h1
    obtain ⟨f1, f2, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W y
    exact ((hat_rational_points_and_approx D.host.F D.host.E W.rank _ f1 f2).1 _).1 h1

theorem moved_iff (V W : HSp D) (y : GA D W) (u : WO V W) :
    u ∈ (latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
      actO V W 1 y⁻¹ u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (GlobalTheory.Member.latC W : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have h1 : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      Matrix.mulVec (finHom V 1).1 z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro z hz
    rw [map_one, Units.val_one, Matrix.one_mulVec]
    exact hz
  constructor
  · exact GlobalTheory.MovedLat.actO_mem V W 1 y⁻¹ _ _ _ _ h1 (GlobalTheory.MovedLat.bwd W y) u
  · intro h
    have h2 := GlobalTheory.MovedLat.actO_mem V W 1 y _ _ _ _ h1 (GlobalTheory.MovedLat.fwd W y) _ h
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv V W 1 y u
    rw [inv_one] at h3
    rwa [h3] at h2

theorem cols_mem_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i b hb y Yr
  have hV := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βV i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  have hW := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βW i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  rw [cols_iff_moved _ _ b hb, moved_iff, ← hV, ← hW]

end GlobalTheory.ColSplit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.DictLatPin

variable {D : D7}

theorem latFrame_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r)
    {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r}
    (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      ∀ τ : (X (dict h).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1)
    (g : GA D W) : ∃ γ ∈ GQ W,
      ((X (castDict hV dict g).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin W.rank → D.host.E => v ∘ Fin.cast hr'.symm) '' (latG W (γ * g) : Set _) ∧
      ∀ τ : (X (castDict hV dict g).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (castDict hV dict g).2 τ =
        Matrix.reindex (finCongr hr') (finCongr hr') (archM W (th (castDict hV dict g).1 τ) (γ * g)) * x₀ τ.1 := by
  subst hV
  exact h g

end GlobalTheory.DictLatPin


open GlobalTheory.DictLatPin in

theorem GlobalTheory.DictLatPin.lat_of_frAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ _ hMods _ hT i σ hσ hV γ hγ g hFr v
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hP := hL.pins
  obtain ⟨hr, g', e, F', ik, φ, th, -, -, hth, hD⟩ := hL.adPin _ hj _ hg
  have hcl := latFrame_cast hV hr (rank_Wc i) (T.dict ((i : ℕ) + 1) T.σ₀) th (T.x₀ ((i : ℕ) + 1) T.σ₀)
    (fun h => by
      obtain ⟨γ₁, hq, hl, -, hf⟩ := hD.2 h
      exact ⟨γ₁, hq, hl, hf⟩) g
  obtain ⟨γ', hγ', hΛ, hf'⟩ := hcl

  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  set k := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i T.σ₀ hV g).1 with hk
  have hU := hL.unf _ hj _ hg
  have hΨ := (hU.2.1 k).2
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hτ₀ : tauE D ρ₀ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := (hΨ _).2 (hP.1.2.2.2 ρ₀)
  let τ₀ : ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := ⟨tauE D ρ₀, hτ₀⟩
  have h1 := hFr ρ₀ τ₀ rfl
  have h2 := hf' τ₀
  have hth' : th k τ₀ = R.θ ρ₀ := GlobalTheory.LettersCheck.isInfEmb_unique (tauE D ρ₀) _ _ (hth k τ₀) (hMods.inf ρ₀)
  rw [← hx.mul] at h1
  rw [hth'] at h2
  have h3 : Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ' * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) := h2.symm.trans h1
  have hx₀ : IsOrthogonalFrame ((T.U ((i : ℕ) + 1) T.σ₀).X k) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hL.familyUniformisationBasePointOrthogonal _ hj _ hg k
  obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).p0 ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm_herm
  have hdet : IsUnit (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀)).det :=
    (((hu2 (fun τ => T.x₀ ((i : ℕ) + 1) T.σ₀ τ.1) fun τ => hx₀ τ.1 τ.2).1 τ₀).1).isUnit
  have h4 : archM (Wc D i) (R.θ ρ₀) (γ' * g) = archM (Wc D i) (R.θ ρ₀) (γ * g) := by
    have := congrArg (· * (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀))⁻¹) h3
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] at this
    exact (Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i))).injective this
  have h5 : ∀ δ : GA D (Wc D i), archM (Wc D i) (R.θ ρ₀) δ =
      archM (Wc D i) (R.θ ρ₀) (δ * g) * archM (Wc D i) (R.θ ρ₀) g⁻¹ := fun δ => by
    rw [← GlobalTheory.PointAtPlace.archM_mul, mul_inv_cancel_right]
  have hγγ : γ' = γ := GlobalTheory.AdTh.MarkUniq.rat_eq_of_archM (Wc D i) hγ' hγ (tauE D ρ₀) (R.θ ρ₀) (hMods.inf ρ₀)
    (by rw [h5 γ', h5 γ, h4])
  subst hγγ
  rw [← SetLike.mem_coe, hΛ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ latG (Wc D i) (γ' * g) := hw
    convert hw' using 1
    funext m
    simp
  · intro hv
    exact ⟨_, hv, funext fun m => by simp⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitInduct

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

theorem induct_suppSplit : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  classical
  intro D V N Q h1 hmul hloc g hg hs
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, Q (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    obtain ⟨PP, hP, hco⟩ := _root_.GlobalTheory.IdemPrime.exists_isIdemAt D v e he
    refine hloc e PP hP ?_ _ (GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}) ?_
    · intro hm
      refine hv'.2 ?_
      rw [← hco, Ideal.mem_comap, map_natCast]
      exact hm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), s ⊆ he2.toFinset →
      Q (GlobalTheory.LocalApprox.cutAt V g s) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v s h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  rw [← hgS]
  exact key _ subset_rfl

end GlobalTheory.SplitInduct

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7}

theorem GQ_negGA_mem (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_GQ (p : Pair T) {γ : GA D (G.V p.small)} {γ' : GA D (G.V p.big)} (hγ : γ ∈ GQ (G.V p.small))
    (hγ' : γ' ∈ GQ (G.V p.big)) : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
  cases p with
  | chi i j => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | mu t i j => exact ⟨hγ, hγ'⟩
  | core i => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | top t j => exact ⟨hγ, hγ'⟩

theorem ker_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T),
    p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  intro D T L sc G W p hp f hf γ hγ γ' hγ' g h
  have hw := W.om_is p hp
  obtain ⟨h1, h2⟩ := toPair_GQ p hγ hγ'
  have e : W.ker p f (γ * g) (γ' * h) =
      W.om p (G.toPair p γ γ') (W.om p (G.toPair p g h) f) 0 := by
    simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.mk.eta, map_mul, Module.End.mul_apply]
  rw [e]
  have := hw.om_aut _ h1 _ h2 (W.om p (G.toPair p g h) f) (hw.om_pres (G.toPair p g h) f hf)
  rw [Prod.mk.eta] at this
  rw [this]
  simp only [GridData.Weil.ker, thetaKO, Prod.mk.eta]

end GlobalTheory.RowReal
end
end
