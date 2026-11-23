module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilDatumSignedHomPairTransportIsometries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

theorem det_submatrix_mul_tri {R : Type} [CommRing R] {n p m : ℕ} (A : Matrix (Fin n) (Fin p) R)
    (B : Matrix (Fin p) (Fin p) R) (hB : B.BlockTriangular id) (h : m + 1 ≤ p) (r : Fin (m + 1) → Fin n) :
    ((A * B).submatrix r (Fin.castLE h)).det =
      (A.submatrix r (Fin.castLE h)).det * ∏ i : Fin (m + 1), B (Fin.castLE h i) (Fin.castLE h i) := by
  have e : (A * B).submatrix r (Fin.castLE h) =
      A.submatrix r (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun _ => rfl)
    have : ¬ (b : ℕ) < m + 1 := fun hb' => hb ⟨⟨b, hb'⟩, rfl⟩
    have h0 : B b (Fin.castLE h l) = 0 := hB (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le l.2 (not_lt.1 this)))
    rw [h0, mul_zero]
  rw [e, Matrix.det_mul, Matrix.det_of_upperTriangular (M := B.submatrix (Fin.castLE h) (Fin.castLE h))]
  · rfl
  · intro i l hil
    exact hB (show Fin.castLE h l < Fin.castLE h i from hil)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem plkU_map_ev (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (hk : ⊤ ≤ w ⁻¹ᵁ F.U k) (hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U)
    (hx' : ⊤ ≤ (w ≫ π) ⁻¹ᵁ (F.M k).U) :
    (plkU F Mc k σ).map (ev w _ h) =
      (lieBasis Mc (w ≫ π) hx).toMatrix (lieBasis (F.M k).toMChart (w ≫ π) hx') * F.uAt k w hk σ := by
  unfold plkU
  rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    ← chg_map Mc (F.M k).toMChart (w ≫ π) hx hx' (le_preimage_inf hx hx')]
  congr 1
  · ext i j; exact ev_appLE w π _ h _ _
  · ext i j; exact ev_res w _ h hk _

theorem plkU_map_ev_chg (F : Frames Y π) (Mc : MChart Y) (k k' : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (h' : ⊤ ≤ w ⁻¹ᵁ (F.U k' ⊓ π ⁻¹ᵁ Mc.U))
    (hh : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    (plkU F Mc k' σ).map (ev w _ h') = (plkU F Mc k σ).map (ev w _ h) * (F.B k k' σ).map (ev w _ hh) := by
  have hk := le_preimage_mono inf_le_left hh
  have hk' := le_preimage_mono inf_le_right hh
  have hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U := fun p hp => (h hp).2
  have a := F.inM hk rfl
  have b := F.inM hk' rfl
  rw [plkU_map_ev F Mc k' σ w h' hk' hx b, plkU_map_ev F Mc k σ w h hk hx a,
    ← Module.Basis.toMatrix_mul_toMatrix (lieBasis Mc (w ≫ π) hx) (lieBasis (F.M k).toMChart (w ≫ π) a),
    ← chg_map (F.M k).toMChart (F.M k').toMChart (w ≫ π) a b (le_preimage_inf a b), Matrix.mul_assoc,
    F.chg_uAt k k' w hk hk' hh rfl (le_preimage_inf a b) σ, Matrix.mul_assoc]

open Classical in
theorem prod_zpow_neg_ind {G : Type} [CommGroup G] (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Ix Dw → G) :
    ∏ ix, t ix ^ (-ind σ m ix) = (∏ i : Fin ((m : ℕ) + 1), t (some ⟨σ, Fin.castLE m.2 i⟩))⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib]
  congr 1
  symm
  refine Fintype.prod_of_injective (fun i : Fin ((m : ℕ) + 1) => (some ⟨σ, Fin.castLE m.2 i⟩ : Ix Dw)) ?_ _
    (fun ix => t ix ^ ind σ m ix) (fun b hb => ?_) (fun i => ?_)
  · intro i i' e
    simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
    exact Fin.castLE_injective _ e
  · rcases b with _ | ⟨τ, j⟩
    · simp [ind]
    · have : ind σ m (some ⟨τ, j⟩) = 0 := by
        simp only [ind, Option.elim]
        rw [if_neg]
        rintro ⟨rfl, hj⟩
        exact hb ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
      rw [this, zpow_zero]
  · simp [ind, not_lt.2 (Nat.lt_succ_iff.1 i.2)]

theorem plkLoc_sec (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) :
    ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  refine ⟨⟨plkLoc F Mc g hg σ m q, fun j j' => ?_⟩, rfl⟩
  unfold plkLoc
  rcases plkIdx Mc m q with _ | r
  · simp
  · refine ext_ev fun S _ z hz => ?_
    have ha := le_preimage_mono inf_le_left hz
    have hb := le_preimage_mono inf_le_right hz
    have h1 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j) ha
    have h2 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j') hb
    have hh : ⊤ ≤ (z ≫ g) ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ F.U (j' PUnit.unit)) :=
      le_preimage_inf (le_preimage_mono inf_le_left h1) (le_preimage_mono inf_le_left h2)
    rw [map_mul, ev_res z _ hz ha, ev_res z _ hz hb, ev_appLE z g _ ha h1, ev_appLE z g _ hb h2,
      ev_pull_g (F.LL (ind σ m)) g j j' z hz hh]
    erw [F.ev_LL_g _ _ _ (z ≫ g) hh]
    unfold plkMinor
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← Matrix.submatrix_map, plkU_map_ev_chg F Mc _ _ σ (z ≫ g) h1 h2 hh,
      det_submatrix_mul_tri (m := (m : ℕ)) _ _ (F.B_map_tri (j PUnit.unit) (j' PUnit.unit) σ (ev (z ≫ g) _ hh)) m.2 r,
      prod_zpow_neg_ind]
    have e : ∏ i : Fin ((m : ℕ) + 1), (F.B (j PUnit.unit) (j' PUnit.unit) σ).map (ev (z ≫ g) _ hh)
        (Fin.castLE m.2 i) (Fin.castLE m.2 i) =
        ((∏ i : Fin ((m : ℕ) + 1), F.TAt (j PUnit.unit) (j' PUnit.unit) (z ≫ g) hh
          (some ⟨σ, Fin.castLE m.2 i⟩) : (S)ˣ) : S) := by
      rw [Units.coe_prod]; rfl
    rw [e, _root_.mul_left_comm, Units.inv_mul, _root_.mul_one]

end GlobalTheory.FlagPlucker

end
end

section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

namespace GlobalTheory.SplitProj

open Filter Topology GlobalTheory.IdemSupport

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

def spl (ε : AE D) : AE D := ε + cA D ε

variable {ε : AE D}

theorem spl_idem (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : spl ε * spl ε = spl ε := by
  obtain ⟨h1, h2, -, -, -⟩ := hε
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  unfold spl
  linear_combination h1 + h3 + 2 * h2

theorem cA_spl (ε : AE D) : cA D (spl ε) = spl ε := by
  unfold spl; rw [RingHom.map_add (f := _), cA_cA, add_comm]

theorem infPart_spl (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : infPart D (spl ε) = 0 := by
  unfold spl
  rw [RingHom.map_add (f := _), (GlobalTheory.IdemSupport.parts_cA ε).1, hε.2.2.1, RingHom.map_zero, add_zero]

theorem spl_mul_split (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {e : AE D} (he : IsSplitIdem D e) :
    spl ε * (e + cA D e) = e + cA D e := by
  have k1 : ∀ x y : AE D, x * y = 0 → cA D x * cA D y = 0 := fun x y h => by
    rw [← RingHom.map_mul, h, RingHom.map_zero]
  have k2 : ∀ x y : AE D, x * y = y → cA D x * cA D y = cA D y := fun x y h => by
    rw [← RingHom.map_mul, h]
  unfold spl
  rcases hε.2.2.2.1 e he with ⟨a, b⟩ | ⟨a, b⟩
  · have c1 := k2 _ _ a
    have c2 := k1 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2
  · have c1 := k1 _ _ a
    have c2 := k2 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2

theorem spl_mul_nonSplit (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hv : NonSplitAt D v η) : spl ε * algebraMap (AF D.host.F) (AE D) η = 0 := by
  have h := hε.2.2.2.2 v η hv
  have h' : algebraMap (AF D.host.F) (AE D) η * cA D ε = 0 := by
    rw [← GlobalTheory.IdemSupport.cA_algebraMap η, ← RingHom.map_mul, h, RingHom.map_zero]
  unfold spl
  linear_combination h + h'

def pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) : GA D V :=
  ⟨piece (spl_idem hε) g.1, piece_mem _ _ (spl_idem hε) (cA_spl ε) g.2⟩

theorem mt_pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) :
    mt V (pc hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

def proj (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) : GA D V →* GA D V :=
  MonoidHom.mk' (pc hε V) fun g h => mt_inj V (by
    simp only [mt_pc, GlobalTheory.IdemSupport.mt_mul]
    rw [mix_mul (spl_idem hε), one_mul])

variable (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {V : HSp D}
include hε

theorem mt_proj (g : GA D V) :
    mt V (proj hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := mt_pc hε V g

theorem proj_eq_self {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = (mt V g - 1) i j) : proj hε V g = g :=
  mt_inj V (by
    rw [mt_proj]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_eq_one {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = 0) : proj hε V g = 1 :=
  mt_inj V (by
    rw [mt_proj, GlobalTheory.IdemSupport.mt_one]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_mem_GfC (g : GA D V) : proj hε V g ∈ GfC V :=
  mem_GfC_of_suppF V (infPart_spl hε) ((suppF_iff V _ _).2 (smul_mix (spl_idem hε) (mt_proj hε g)))

theorem proj_of_suppAt {g : GA D V} (hg : SuppAt ε V g) : proj hε V g = g := proj_eq_self hε hg

theorem proj_of_split {e : AE D} (he : IsSplitIdem D e) {g : GA D V} (hg : SuppAt e V g) : proj hε V g = g :=
  proj_eq_self hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_split hε he]

theorem proj_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D V}
    (hg : SuppPl η V g) : proj hε V g = 1 :=
  proj_eq_one hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_nonSplit hε hv, zero_mul]

theorem proj_of_real {g : GA D V} (hg : g ∈ GinfC V) : proj hε V g = 1 := by
  refine proj_eq_one hε fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, infPart_spl hε, zero_mul, RingHom.map_zero]) ?_
  have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
  have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
    rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
  have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
  rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]

omit hε in
theorem continuous_mt (V : HSp D) : Continuous fun g : GA D V => mt V g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_proj : Continuous (proj hε V) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have c1 : Continuous fun g => mt V (proj hε V g) := by
    simp only [mt_proj]
    exact ((continuous_mt V).const_smul (spl ε)).add continuous_const
  have c2 : Continuous fun g => mt V (proj hε V g)⁻¹ := by
    simp only [← map_inv]
    exact c1.comp continuous_inv
  exact continuous_iff_continuousAt.2 fun g =>
    GlobalTheory.LocalGlobalChar.tendsto_HA _ _ _ (c1.tendsto g) (c2.tendsto g)

end GlobalTheory.SplitProj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory GlobalTheory.TriMove GlobalTheory.Mem.Isom

namespace GlobalTheory.TriMoveConst

variable {D : D7}

def kapME {V V' : HSp D} (I : IsoMat V V') : GA D V ≃ᵐ GA D V' :=
  (Homeomorph.mk I.kap.toEquiv I.continuous_kap I.continuous_kap_symm).toMeasurableEquiv

theorem kapME_apply {V V' : HSp D} (I : IsoMat V V') (g : GA D V) : kapME I g = I.kap g := rfl

theorem preimage_kapME {V V' : HSp D} (I : IsoMat V V') (s : Set (GA D V)) : kapME I ⁻¹' (I.kap.symm ⁻¹' s) = s := by
  ext g
  simp only [Set.mem_preimage, kapME_apply, MulEquiv.symm_apply_apply]

theorem trH_symm_trH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (F : WO S T → ℂ) :
    trH IS.symm IT.symm (trH IS IT F) = F := by
  funext w
  show F ((homMap IS IT).symm (homMap IS IT w)) = F w
  rw [AddEquiv.symm_apply_apply]

theorem thetaKO_omH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) (F : WO S T → ℂ) :
    thetaKO (omH IS IT om) (IS.kap g) (IT.kap h) (trH IS IT F) = thetaKO om g h F := by
  unfold thetaKO
  rw [omH_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, trH_symm_trH]
  show (om (g, h) F) ((homMap IS IT).symm 0) = _
  rw [map_zero]

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

theorem ker_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) (g : GA D B) :
    (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) (IA.kap g) = Y.ker ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ true IA IW Y.rA.s Y.rA.B Y.rW.s Y.rW.B (Y.f t) P
  have hs : ∀ {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ), GlobalTheory.Grid.sgnM true s = -s := fun _ => rfl
  simp only [hs] at hF
  exact (congrArg (thetaKO (omH IA IW (Y.ω t)) (IA.kap g) (IW.kap h)) hF).trans (thetaKO_omH IA IW (Y.ω t) g h _)

theorem ker'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) (g : GA D B') :
    (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) (IA'.kap g) = Y.ker' ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ false IA' IW Y.rA'.s Y.rA'.B Y.rW.s Y.rW.B (Y.f' t) P
  show thetaKO (omH IA' IW (Y.ω' t)) (IA'.kap g) (IW.kap h) (pureTensorO ψ θ (GlobalTheory.Grid.sgn false A') WW
      (fun τ => GlobalTheory.Grid.sgnM false (cartMove IA' τ (Y.rA'.s τ))) (fun τ => cartMove IW τ (Y.rW.s τ))
      (fun τ => basMove IA' τ (Y.rA'.B τ)) (fun τ => basMove IW τ (Y.rW.B τ)) (trH IA' IW (Y.f' t))
      (polMove IW.rank_eq IA'.rank_eq P)) =
    thetaKO (Y.ω' t) g h (pureTensorO ψ θ (GlobalTheory.Grid.sgn false B') WW₁ (fun τ => GlobalTheory.Grid.sgnM false (Y.rA'.s τ)) Y.rW.s Y.rA'.B
      Y.rW.B (Y.f' t) P)
  rw [hF, thetaKO_omH]

theorem I_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) = Y.I ψ θ t P h := by
  show ∫ g in IA.kap.symm ⁻¹' Y.fd, (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) g
      ∂(Y.m.map (kapME IA)) = _
  rw [setIntegral_map_equiv (kapME IA), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd, F g ∂Y.m) (funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g)

theorem I'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) = Y.I' ψ θ t P h := by
  show ∫ g in IA'.kap.symm ⁻¹' Y.fd', (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) g
      ∂(Y.m'.map (kapME IA')) = _
  rw [setIntegral_map_equiv (kapME IA'), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd', F g ∂Y.m') (funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g)

theorem integrableOn_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd
      (triMove IA IA' IW Y).m ↔ IntegrableOn (Y.ker ψ θ t P h) Y.fd Y.m := by
  show IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (IA.kap.symm ⁻¹' Y.fd)
      (Y.m.map (kapME IA)) ↔ _
  rw [IntegrableOn, (kapME IA).restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) ∘ kapME IA = Y.ker ψ θ t P h :=
    funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem integrableOn'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd'
      (triMove IA IA' IW Y).m' ↔ IntegrableOn (Y.ker' ψ θ t P h) Y.fd' Y.m' := by
  show IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (IA'.kap.symm ⁻¹' Y.fd')
      (Y.m'.map (kapME IA')) ↔ _
  rw [IntegrableOn, (kapME IA').restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) ∘ kapME IA' = Y.ker' ψ θ t P h :=
    funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem isConst_triMove : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  intro D T₀ A A' WW B B' WW₁ IA IA' IW Y ψ θ hθ c hY
  obtain ⟨hc, P, P', H⟩ := hY
  refine ⟨hc, polMove IW.rank_eq IA.rank_eq P, polMove IW.rank_eq IA'.rank_eq P', fun t => ?_⟩
  obtain ⟨hint, ⟨h0, hne⟩, heq⟩ := H t
  refine ⟨fun h' => ?_, ⟨IW.kap h0, ?_⟩, fun h' => ?_⟩
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    exact ⟨(integrableOn_move IA IA' IW Y ψ θ hθ t P h).2 (hint h).1,
      (integrableOn'_move IA IA' IW Y ψ θ hθ t P' h).2 (hint h).2⟩
  · rw [I'_move IA IA' IW Y ψ θ hθ t P' h0]
    exact hne
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    rw [I_move IA IA' IW Y ψ θ hθ t P h, I'_move IA IA' IW Y ψ θ hθ t P' h]
    exact heq h

end GlobalTheory.TriMoveConst

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
  GlobalTheory.Grid.IsWeil ψ ε S T χS χT om → GlobalTheory.Grid.IsWeil ψ ε S' T' χS χT (GlobalTheory.TriMove.omH IS IT om) := by
  first | exact @GlobalTheory.IsoBoth.isWeil_omH | exact GlobalTheory.IsoBoth.isWeil_omH | (intros; apply GlobalTheory.IsoBoth.isWeil_omH <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  first | exact @GlobalTheory.InertBigCell.glueW_props | exact GlobalTheory.InertBigCell.glueW_props | (intros; apply GlobalTheory.InertBigCell.glueW_props <;> assumption)
end
