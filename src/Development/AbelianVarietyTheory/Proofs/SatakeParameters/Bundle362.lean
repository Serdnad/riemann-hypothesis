module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle353
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle326
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle335
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieSerH_series_of_classes : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d ι j hN La _ c' L' _ α _
  exact GlobalTheory.T.coeff_renamed_thetaClass_series t u μ _ (sysS H X std) (hT.gat_pos u w hg) (clsAt X H) ι j hN La (c', L') (d.sH S ι j La (c', L')) α

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem det_map_ringHom {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem frInv_fdOfCharts {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FrInv (fdOfCharts cp a bad) := by
  intro j La v
  simp only [fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self, det_map_ringHom]
  apply IsUnit.map
  rw [Matrix.det_mul, LinearMap.det_toMatrix']
  exact IsUnit.mul (LinearEquiv.isUnit_det' _) (Matrix.isUnits_det_units _)

theorem frames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have h1 : FrInv (J.fd std) := frInv_fdOfCharts _ _ _
  refine ⟨h1, fun d j La v => ?_⟩
  show IsUnit (((star (d.eM j La)).map (J.rho std v)) * (J.fd std).frM j La v).det
  rw [Matrix.det_mul, det_map_ringHom]
  exact IsUnit.mul (IsUnit.map _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La))) (h1 j La v)

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
open Filter Topology

namespace GlobalTheory.LatChoiceSplit

theorem mem_half_iff {D : D7} {S T : HSp D} (e : AE D) (u : WO S T) : u ∈ half S T e ↔ IsHalf e u := by
  change e • u = u ↔ _
  rw [← Matrix.ext_iff]
  rfl

theorem nhdsNE_neBot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_int_mat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] : IsCompact {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_smul_int_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] (A : Set (Matrix Y Y' k)) (hA : IsOpen A) (h0 : (0 : Matrix Y Y' k) ∈ A) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → c • x ∈ A := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}, c • x ∈ A := by
    refine (isCompact_int_mat k Y Y').eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix Y Y' k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have : (fun z : k × Matrix Y Y' k => z.1 • z.2) (0, y) ∈ A := by simpa using h0
    exact hc.continuousAt.preimage_mem_nhds (hA.mem_nhds this)
  haveI := nhdsNE_neBot k
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

theorem natCast_smul {D : D7} {S T : HSp D} (N : ℕ) (x : WO S T) : (N : AE D) • x = N • x :=
  Nat.cast_smul_eq_nsmul _ _ _

theorem symplO_nsmul_swap {D : D7} (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  rw [← natCast_smul, GlobalTheory.PlaceModel.symplO_smul, map_natCast, natCast_smul]

theorem psi_neg_eq_one {F : Type} [AddGroup F] (ψ : AddChar F ℂ) (z : F) (h : ψ z = 1) : ψ (-z) = 1 := by
  have := AddChar.map_add_eq_mul ψ z (-z)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem nsmul_inv_smul {D : D7} {S T : HSp D} {N : ℕ} (hN : 0 < N) (t : WO S T) :
    N • ((incA D (N : D.host.E)⁻¹) • t) = t := by
  rw [smul_comm]
  exact GlobalTheory.PlaceModel.inv_smul_nsmul S T hN t

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  intro i j
  show e * (N • u i j) = N • u i j
  rw [nsmul_eq_mul, mul_left_comm, h i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) (w : AE D) (a : Mx D m n) :
    IsHalf e (w • (e • a)) := by
  intro i j
  show e * (w * (e * a i j)) = w * (e * a i j)
  rw [mul_left_comm, ← mul_assoc e e, he]


open GlobalTheory.LocMod.Witness in
theorem exists_split_lattices : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (U : AddSubgroup (Formalism.IndefR.Datum.WO S T)), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) → ∃ c : k, c ≠ 0 ∧ ∃ L' K : AddSubgroup (Formalism.IndefR.Datum.WO S T), (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → p.up FS FT (c • x) ∈ L' ∧ p.up FS FT (c • x) ∈ U) ∧ (∀ t ∈ L', Formalism.IndefR.Datum.IsHalf p.e t) ∧ (∀ y ∈ K, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y ∧ y ∈ U) ∧ (∃ R : Finset (Formalism.IndefR.Datum.WO S T), ∀ t ∈ L', ∃ r ∈ R, ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ t - r = p.up FS FT (c • x)) ∧ (∀ x ∈ L', ∀ y ∈ K, ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) ∧ (∀ y, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x ∈ L', ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) → y ∈ K) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ U hU
  classical
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  set Λ₀ := latO S T (GlobalTheory.PlaceModel.latFrame S : Set _) (GlobalTheory.PlaceModel.latFrame T : Set _) (fun _ => True) with hΛ₀
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have he : p.e * p.e = p.e := p.split.1
  have hinfe : infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinfe' : infPart D (cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinfe
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hNk : (N : k) ≠ 0 := by
    intro h0
    have h1 : (N : AE D) * incA D ((N : D.host.E)⁻¹) = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    have h2 := congrArg p.π h1
    rw [map_mul, map_natCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  obtain ⟨c, hc0, hc⟩ := exists_smul_int_mem k Y Y'
    (((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) ∩ ((U.comap (upH p FS FT) : AddSubgroup _) : Set _))
    ((lat_open p FS FT hS hT).inter (hU.preimage (up_cont p FS FT)))
    ⟨zero_mem (Λ₀.comap (upH p FS FT)), zero_mem (U.comap (upH p FS FT))⟩
  let L' : AddSubgroup (WO S T) := half S T p.e ⊓ Λ₀.comap (nsmulAddMonoidHom N)
  let K : AddSubgroup (WO S T) := (Λ₀ ⊓ half S T (cA D p.e)).map (nsmulAddMonoidHom N)
  have hL' : ∀ t, t ∈ L' ↔ IsHalf p.e t ∧ N • t ∈ Λ₀ := fun t => by
    rw [AddSubgroup.mem_inf, mem_half_iff]; rfl
  have hK : ∀ y, y ∈ K ↔ ∃ b, (b ∈ Λ₀ ∧ IsHalf (cA D p.e) b) ∧ N • b = y := fun y => by
    simp only [K, AddSubgroup.mem_map, AddSubgroup.mem_inf, mem_half_iff, nsmulAddMonoidHom_apply]
  refine ⟨c, hc0, L', K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hc x hx
    exact ⟨(hL' _).2 ⟨up_half p FS FT _, nsmul_mem (show p.up FS FT (c • x) ∈ Λ₀ from h1) N⟩, h2⟩
  · exact fun t ht => ((hL' t).1 ht).1
  · intro y hy
    obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := (hK y).1 hy
    exact ⟨isHalf_nsmul hb2 N, hNU b hb1⟩
  · have hAc := lat_compact p FS FT hS hT
    have hB : IsCompact ((fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k))) :=
      hAc.image (continuous_const_smul _)
    have hint : IsOpen {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
      have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} =
          ⋂ i, ⋂ j, (fun x : Matrix Y Y' k => x i j) ⁻¹' (𝒪[k] : Set k) := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (Valuation.isOpen_integer (v := valuation k)).preimage ((continuous_apply j).comp (continuous_apply i))
    have hVo : IsOpen ((fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}) :=
      hint.preimage (continuous_const_smul _)
    obtain ⟨G, hG⟩ := compact_covered_by_add_left_translates hB
      (V := (fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]})
      ⟨0, by rw [hVo.interior_eq]; intro i j; simp⟩
    refine ⟨G.image (fun g => p.up FS FT (-g)), fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := (hL' t).1 ht
    have hm : N • p.down FS FT t ∈ ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
      change upH p FS FT (N • p.down FS FT t) ∈ Λ₀
      rw [map_nsmul]
      change N • p.up FS FT (p.down FS FT t) ∈ Λ₀
      rw [up_down p FS FT h1]
      exact h2
    have hmB : p.down FS FT t ∈ (fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) :=
      ⟨_, hm, by simp only; rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hNk, one_smul]⟩
    have hG' := hG hmB
    rw [Set.mem_iUnion₂] at hG'
    obtain ⟨g, hg, hgV⟩ := hG'
    refine ⟨p.up FS FT (-g), Finset.mem_image_of_mem _ hg, c⁻¹ • (g + p.down FS FT t), hgV, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have h3 := up_add p FS FT (-g) (g + p.down FS FT t)
    rw [neg_add_cancel_left, up_down p FS FT h1] at h3
    exact sub_eq_of_eq_add' h3
  · intro x hx y hy
    obtain ⟨h1, h2⟩ := (hL' x).1 hx
    obtain ⟨b, ⟨hb1, -⟩, rfl⟩ := (hK y).1 hy
    rw [← symplO_nsmul_swap]
    have hhalf : IsHalf p.e (N • x) := isHalf_nsmul h1 N
    exact (hdual (N • x) (GlobalTheory.PlaceDatum.infPart_of_half hinfe hhalf)).1 h2 b hb1
  · intro y hy hyL
    obtain ⟨y', hy'h, rfl⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) N hN y ((mem_half_iff _ _).2 hy)
    have hy'h' := (mem_half_iff _ _).1 hy'h
    refine (hK _).2 ⟨y', ⟨?_, hy'h'⟩, rfl⟩
    refine (hdual y' (GlobalTheory.PlaceDatum.infPart_of_half hinfe' hy'h')).2 fun a ha => ?_
    rw [GlobalTheory.PlaceModel.symplO_skew]
    refine psi_neg_eq_one ψ _ ?_
    have hea : p.e • a ∈ Λ₀ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) a ha
    have hNx : N • (incA D ((N : D.host.E)⁻¹) • (p.e • a)) = p.e • a := nsmul_inv_smul hN _
    have hx : incA D ((N : D.host.E)⁻¹) • (p.e • a) ∈ L' := by
      exact (hL' _).2 ⟨isHalf_smul_idem he _ a, by rw [hNx]; exact hea⟩
    have h4 := hyL _ hx
    rw [← symplO_nsmul_swap, hNx, GlobalTheory.PlaceModel.symplO_smul] at h4
    have hcy : cA D p.e • y' = y' := hy'h
    rwa [hcy] at h4

end GlobalTheory.LatChoiceSplit
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwTopQ

theorem topF_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
  topF Ch sel mu cst i P p Y p' x = topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem locq_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hcpl hfr htop hfr' Z
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hD := hok.depthQ P hP
  have hM := hc.M_pos
  have hX : t.X.Ok := hPin.fields.ok
  have hU := qUnif_of t.sel (t.tup μ) hX t.pr_ok hPin.sel
  have hgI : g ∈ GLint t.X.E _ P.1 :=
    hok.int (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β) P ((exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hcpl.1⟩)
  have hg'I : g' ∈ GLint t.X.E _ P.1 := GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime _ _ _ _ _ P hP g' z' htop
  have hdep : topDep t.sel (t.tup μ) (t.cst μ) P = 2 * (t.cst μ).M := if_neg hP
  obtain ⟨hk, hkc⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ.1 p p₁ hx hp hp₁ P (t.cst μ).D g
    (hc.D_pos P) le_rfl hgI hfr
  obtain ⟨hk', hkc'⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ'.1 p' p₁' hx' hp' hp₁' P
    (topDep t.sel (t.tup μ) (t.cst μ)) g' (by rw [hdep]; omega) (by rw [hdep]; exact hD) hg'I hfr'
  rw [hdep] at hkc'
  have hy0 : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
    unfold y0At
    rw [dite_eq_left rfl]
  obtain ⟨hW0, hV1, hW⟩ := GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime A dtU a hPin hTie (Nat.le_of_succ_le hi) β P hP p p₁ g
    ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)) hgI (by rw [hy0]; exact hcpl.2) hk hkc
    (fun w => by simp)
  rw [topF_eq, topF_eq]
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p₁' P) Z =
      ((frsF t.sel (t.tup μ) p₁' P).trans ((frsF t.sel (t.tup μ) p' P).symm.trans g'.symm)).symm.toLinearMap ∘ₗ
        (g'.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) Z ∘ₗ g.toLinearMap) ∘ₗ
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp [inFr, LinearEquiv.trans_symm]
  have e2 : (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)) =
      ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).symm
        (g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)))) := by
    simp [LinearEquiv.trans_symm]
  have hy'' : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).M) *
      g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) l) := by
    have h1 := (hk _).2 hV1
    rw [map_smul] at h1
    have e3 : ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm))
        ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) =
        g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) := by
      simp
    rw [e3] at h1
    intro l
    simpa using (ciMem_stdAt _ _).1 h1 l
  rw [e1, e2, GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime t.Ch t.sel (t.tup μ) (t.cst μ) (m_eq t μ) hc P hP hD _ _ hk hkc hk' hkc' _ _ hy'']
  exact GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) hok hU (A.ib (t.m2 + 1) (cpl_lt t μ) β) P hP g z hcpl.1 g' z' htop _ _ _ hW hW0

end GlobalTheory.TwTopQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSplitProof

private theorem is_smooth_char_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have hk : (χ⁻¹).ker = χ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rw [hk]
  exact h

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  intro hBZ hGL hUP hDZ k _ _ _ _ r t χ π v hχ hT hv hvec

  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hGL hUP hDZ k r t χ π v hχ hT hv hvec
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr ⟨s, d, σ, hsupp, hlt⟩
  ·
    obtain ⟨π₁, π₂, hE, hns⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hGL hUP k r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hGL hDZ k r t χ π π₁ π₂ v hχ hT hns hE hv hvec
    have hχi : IsSmoothChar χ⁻¹ := is_smooth_char_inv hχ
    refine Or.inl ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχi, hsph, ?_⟩
    have h2 := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
    rw [inv_inv] at h2
    show Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
    rw [h2]
    exact hE

end GlobalTheory.BlockSplitProof
end

end

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seriesCoefficients_at_kernelSite_of_classSeries : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelB.tieSerH_series_of_classes | exact GlobalTheory.TwV.DelB.tieSerH_series_of_classes | (intros; apply GlobalTheory.TwV.DelB.tieSerH_series_of_classes <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.siteFrames_and_changedFrames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  first | exact @GlobalTheory.TwV.DelB.frames_invertible | exact GlobalTheory.TwV.DelB.frames_invertible | (intros; apply GlobalTheory.TwV.DelB.frames_invertible <;> assumption)

end
end
