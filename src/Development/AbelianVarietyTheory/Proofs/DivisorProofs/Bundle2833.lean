module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.SubAddEqZeroOfEqAdd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  first | (exact @GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (exact GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (intros; apply GlobalTheory.KerKilledFibre.fibreKilled_of_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sameAt_of_sameAt_comp_algebraMap : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  first | exact @GlobalTheory.Poinc.sameAt_of_generic | exact GlobalTheory.Poinc.sameAt_of_generic | (intros; apply GlobalTheory.Poinc.sameAt_of_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin


theorem _root_.GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  first | exact @GlobalTheory.VertCoeffRing.isLieBasis_tvE | exact GlobalTheory.VertCoeffRing.isLieBasis_tvE | (intros; apply GlobalTheory.VertCoeffRing.isLieBasis_tvE <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.kernelKilledOverOpen_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (W : S'.Opens), (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) → GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  first | (exact @GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (exact GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (intros; apply GlobalTheory.KerKilledLocal.kerKilledOn_of_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localSection_of_openImmersion_spec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  first | exact @GlobalTheory.UMin.LocSecOfImm.exists_locSec | exact GlobalTheory.UMin.LocSecOfImm.exists_locSec | (intros; apply GlobalTheory.UMin.LocSecOfImm.exists_locSec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.localThetaSections_ratio_coordinates_overlap : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  first | exact @GlobalTheory.UMin.ThBdl.cross_ratio_sections | exact GlobalTheory.UMin.ThBdl.cross_ratio_sections | (intros; apply GlobalTheory.UMin.ThBdl.cross_ratio_sections <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

theorem nzFib_of_isLocSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  intro S G _ _ L δ σ i R _ ξ t hξ ht hσ r
  have hP := isGrpPullback_pullback G ξ
  obtain ⟨z, hz, hz'⟩ := hσ (ξ r)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hP.1 z r hz
  obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hk : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k := G.left.basicOpen_le _ hb
  have hle : (bL L ξ).L.U (fun _ => k.1) ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := by
    intro x hx
    refine ⟨mem_pull.1 hx, mem_pull.2 ?_⟩
    have e : G.hom (pullback.fst G.hom ξ x) = ξ (pullback.snd G.hom ξ x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    show G.hom (pullback.fst G.hom ξ x) ∈ δ.U i
    rw [e]
    exact hξ (Set.mem_univ _)
  have hy1 : y ∈ (bL L ξ).L.U (fun _ => k.1) := mem_pull.2 hk.1
  have hy2 := hle hy1
  have hb' : pullback.fst G.hom ξ y ∈ G.left.basicOpen (σ.f (k.1, fun _ => i)) := by
    have hm : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := ⟨hk, hy2⟩
    have e := congrArg G.left.basicOpen (σ.compat k (k.1, fun _ => i))
    rw [Scheme.basicOpen_mul] at e
    have e1 := G.left.basicOpen_res (σ.f k) (homOfLE (inf_le_left : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have e2 := G.left.basicOpen_res (σ.f (k.1, fun _ => i)) (homOfLE (inf_le_right : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have h1 := e1.ge ⟨hm, hb⟩
    have h2 := (e.le h1).2
    exact (e2.le h2).2
  refine ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k.1, ?_⟩⟩
  rw [ht (fun _ => k.1) hle]
  exact (Scheme.basicOpen_appLE (pullback.fst G.hom ξ) _ _ hle _).ge ⟨hy1, hb'⟩

end GlobalTheory.KeyVals

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsPol

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem polOnAb_genPt : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  intro S _ G _ _ L hO hg hpol V _
  obtain ⟨U, hU, hp, hUs⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⟨abLocus G, hO⟩) (x := genericPoint S) hg
  obtain ⟨ha, hk⟩ := hpol U hUs
  obtain ⟨f, hf⟩ : ∃ f : V.toScheme ⟶ U.toScheme, f ≫ U.ι = V.ι ≫ KeyVals.genPt S :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ KeyVals.genPt S) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact KeyVals.genPt_le U hp (Set.mem_univ (V.ι y))), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (KeyVals.genPt S)
  have h' := isGrpPullback_pullback (KeyVals.bG G (KeyVals.genPt S)) V.ι
  have h₀ := isGrpPullback_pullback G U.ι
  have h₂ := (h'.comp h).congr hf.symm rfl
  let A' := (Over.pullback V.ι).obj (KeyVals.bG G (KeyVals.genPt S))
  let a : (KeyVals.bG G (KeyVals.genPt S)).left ⟶ G.left := pullback.fst G.hom (KeyVals.genPt S)
  let b : A'.left ⟶ (KeyVals.bG G (KeyVals.genPt S)).left := pullback.fst (KeyVals.bG G (KeyVals.genPt S)).hom V.ι
  let ψ : A'.left ⟶ ((Over.pullback U.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom U.ι = b ≫ a := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback A' ((Over.pullback U.ι).obj G) f ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB (pull_isLB L.isLB a) b
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom U.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.L.pull a).pull b) ((L.L.pull (pullback.fst G.hom U.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb L.L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (lbIso_self (pull_isLB L.isLB (b ≫ a)))
  have : IsAffine U.toScheme := hU
  exact ⟨relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha,
    kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk⟩

end GlobalTheory.KeyValsPol

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsSec

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (J J' : PUnit → L.ι)
    (hj : F (f y) ∈ L.U (J PUnit.unit)) (hj' : F (f y) ∈ L.U (J' PUnit.unit)) :
    gm f y ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) y _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f y ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U _ ⊓ L.U _) ⟨hj, hj'⟩ _)

theorem exists_sec_of_chart {X X' : Scheme.{0}} (A B : LB X) (hB : B.IsLB) (σ : (CechPic.tens A B).Sec) (b : B.ι)
    (F : X' ⟶ X) (hb : ∀ y : X', F y ∈ B.U b) :
    ∃ t : (A.pull F).Sec, ∀ (j : (A.pull F).ι)
      (h : (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b)),
      t.f j = (F.appLE _ _ h).hom (σ.f (j PUnit.unit, b)) := by
  have hle : ∀ j : (A.pull F).ι, (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b) :=
    fun j y hy => ⟨mem_pull.1 hy, hb y⟩
  refine ⟨⟨fun j => (F.appLE _ _ (hle j)).hom (σ.f (j PUnit.unit, b)), fun j j' => ?_⟩, fun _ _ => rfl⟩
  apply TopCat.Presheaf.section_ext X'.sheaf
  intro y hy
  have hy' : (𝟙 X' : X' ⟶ X') y ∈ (A.pull F).U j ⊓ (A.pull F).U j' := hy
  have hj : F y ∈ A.U (j PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ A.U (j' PUnit.unit) := mem_pull.1 hy.2
  have hp : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j PUnit.unit, b) := ⟨hj, hb y⟩
  have hq : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j' PUnit.unit, b) := ⟨hj', hb y⟩
  have e := gs_compat σ (𝟙 X' ≫ F) y hp hq
  have e₁ := CechPic.gm_tens A B (𝟙 X' ≫ F) y (j PUnit.unit, b) (j' PUnit.unit, b) hp hq
  rw [gm_self hB (𝟙 X' ≫ F) y hp.2, _root_.mul_one] at e₁
  rw [e₁] at e
  refine (gs_eq (𝟙 X') y _ hy' _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X') y _ hy' _))
  refine (gs_res _ y _ hy' _).trans ((gs_appLE F _ _ _ (𝟙 X') y hy'.1 _).trans (e.trans ?_))
  refine Eq.trans ?_ (gs_mul _ y _ hy' _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gs_res _ y _ hy' _).trans (gs_appLE F _ _ _ (𝟙 X') y hy'.2 _)).symm
  exact ((gs_unit _ y _ hy' _).trans (congrArg Units.val (gm_pull_g A F (𝟙 X') y j j' hj hj'))).symm

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  intro S G _ _ L δ σ i R _ ξ hδ hξ
  refine exists_sec_of_chart L.L (δ.pull G.hom) (LB.isLB_pull hδ _) σ (fun _ => i) (pullback.fst G.hom ξ) fun y => ?_
  refine mem_pull.2 ?_
  have h : (pullback.fst G.hom ξ ≫ G.hom) y ∈ δ.U i := by
    rw [pullback.condition]
    exact hξ (Set.mem_univ (pullback.snd G.hom ξ y))
  exact h

end GlobalTheory.KeyValsSec

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeySecRel

theorem appLE_map' {X Y : Scheme.{0}} (p : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) {W : Y.Opens} (h : W ≤ p ⁻¹ᵁ V)
    (h' : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (p.appLE V W h).hom ((X.presheaf.map (homOfLE hVU).op).hom a) = (p.appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_app' {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) {U : S.Opens} {W : Y.Opens}
    (h : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ U)) (h' : W ≤ (p ≫ π) ⁻¹ᵁ U) (a : Γ(S, U)) :
    (p.appLE _ W h).hom ((π.app U).hom a) = ((p ≫ π).appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appLE]

theorem appLE_sec_tens {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) (A : LB X) (hA : A.IsLB) (δ : LB S)
    (σ : (CechPic.tens A (δ.pull π)).Sec) (l : A.ι) (i i' : δ.ι) (W : Y.Opens)
    (h : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i))
    (h' : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i'))
    (hW : W ≤ (p ≫ π) ⁻¹ᵁ (δ.U i ⊓ δ.U i')) :
    (p.appLE _ W h).hom (σ.f (l, fun _ => i)) =
      ((p ≫ π).appLE _ W hW).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) * (p.appLE _ W h').hom (σ.f (l, fun _ => i')) := by
  have hh : W ≤ p ⁻¹ᵁ ((CechPic.tens A (δ.pull π)).U (l, fun _ => i) ⊓ (CechPic.tens A (δ.pull π)).U (l, fun _ => i')) :=
    fun y hy => ⟨h hy, h' hy⟩
  have e := congrArg (p.appLE _ W hh).hom (σ.compat (l, fun _ => i) (l, fun _ => i'))
  rw [map_mul, appLE_map' p _ hh h, appLE_map' p _ hh h'] at e
  rw [e]
  congr 1
  have h1 : W ≤ p ⁻¹ᵁ (A.U l) := fun y hy => (h hy).1
  have h11 : W ≤ p ⁻¹ᵁ (A.U l ⊓ A.U l) := fun y hy => ⟨h1 hy, h1 hy⟩
  have hg : (p.appLE _ W h11).hom (A.g l l : Γ(X, A.U l ⊓ A.U l)) = 1 := by
    have := congrArg (fun u : Γ(X, A.U l)ˣ => (p.appLE _ W h1).hom (u : Γ(X, A.U l))) (hA.g_self l)
    simp only [Units.val_one, map_one] at this
    rw [← this]
    exact (appLE_map' p _ h1 h11 _).symm
  have h2 : W ≤ p ⁻¹ᵁ ((δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i')) := fun y hy => ⟨(h hy).2, (h' hy).2⟩
  have hd : ((δ.pull π).g (fun _ => i) (fun _ => i') : Γ(X, (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i'))) =
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i') PUnit.unit)) :
        (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i') ≤ π ⁻¹ᵁ (δ.U i ⊓ δ.U i'))).op).hom
        ((π.app _).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) := by
    unfold LB.pull LB.LinComb
    dsimp only
    erw [Fintype.prod_unique, zpow_one]
    rfl
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) ((appLE_map' p _ hh h11 _).trans hg) (appLE_map' p _ hh h2 _)).trans ?_
  rw [_root_.one_mul]
  refine (congrArg (p.appLE _ W h2).hom hd).trans ?_
  have hW' : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ (δ.U i ⊓ δ.U i')) := hW
  exact (appLE_map' p _ h2 hW' _).trans (appLE_app' p π hW' hW _)

theorem genPt_appLE {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    ((KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (KeyVals.FF S))).inv.hom (S.presheaf.germ U (genericPoint S) hU a) := by
  have e := Scheme.fromSpecStalk_app (X := S) (x := genericPoint S) hU
  have : (KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU) =
      S.presheaf.germ U (genericPoint S) hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    unfold KeyVals.genPt Scheme.Hom.appLE
    erw [e]
    simp only [Category.assoc]
    erw [← Functor.map_comp]
    refine congrArg (fun z => _ ≫ z) ?_
    refine (congrArg (fun z => _ ≫ (Spec (S.presheaf.stalk (genericPoint S))).presheaf.map z)
      (Subsingleton.elim _ (𝟙 _))).trans ?_
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  rfl

theorem locSec_eq_germ_mul : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  intro S _ G _ _ L δ σ _ i i' h2 t t' ht ht' j
  have hc : pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom =
      (KeyVals.bG G (KeyVals.genPt S)).hom ≫ KeyVals.genPt S := pullback.condition
  have hW : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      (pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom) ⁻¹ᵁ (δ.U i ⊓ δ.U i') := by
    rw [hc]
    exact fun y _ => KeyVals.genPt_le _ h2 (Set.mem_univ _)
  have hl : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => pullback.fst G.hom (KeyVals.genPt S)) j PUnit.unit
  have h : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i) :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).1⟩
  have h' : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i') :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).2⟩
  rw [ht j h, ht' j h']
  refine (appLE_sec_tens _ G.hom L.L L.isLB δ σ _ i i' _ h h' hW).trans ?_
  congr 1
  unfold constFn
  rw [← genPt_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {Y : Scheme.{0}} (f f' : Y ⟶ S) (_ : f = f') (U : S.Opens) (W : Y.Opens) (a : W ≤ f ⁻¹ᵁ U)
      (a' : W ≤ f' ⁻¹ᵁ U) (x : Γ(S, U)), (f.appLE U W a).hom x = (f'.appLE U W a').hom x := by
    intro Y f f' e; subst e; intros; rfl
  exact key _ _ hc _ _ _ _ _

end GlobalTheory.KeySecRel

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem isSymmetric_bL : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric :=
  fun _ G _ _ L _ _ ξ h =>
    CubePf.sym_pull (cubeMapOf (isGrpPullback_pullback G ξ)) L (bL L ξ).isLB (bL L ξ).rigGen h

end GlobalTheory.KeyVals
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  first | (exact @GlobalTheory.ZarhinKer.polUnit_ker_le) | (exact GlobalTheory.ZarhinKer.polUnit_ker_le) | (intros; apply GlobalTheory.ZarhinKer.polUnit_ker_le  <;> assumption)
end
