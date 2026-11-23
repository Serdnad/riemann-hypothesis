module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle863
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle917
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle570
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



noncomputable section

namespace GlobalTheory.HalfLatInt

variable {D : D7}

theorem toEAf_idem_mul_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {a : D.host.E}
    (ha : a ∈ D.host.AA) : toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  exact GlobalTheory.ConjHalfInt.toEAf_mul_mem ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))
    (GlobalTheory.HalfCompare.primeToAA_of_not_mem (hP PP hPP)) ha

theorem isIntM_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapO S T βS βT x) := by
  have hx' : e • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO S T βS βT (e • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      unfold frMapO
      rw [GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (βT⁻¹).val, Matrix.mul_assoc]
      exact GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_idem_mul_mem he hP ha) hα')
        (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fT ht)
          (GlobalTheory.ConjHalfInt.pair_row_int hS fS hs))
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
    exact fun i j => neg_mem (hu i j)


open GlobalTheory.ExportSeries.Model in
theorem isIntM_adj {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {x : WO S T} (h : IsIntM (frMapO S T βS βT x)) : IsIntM (frMapAdj S T βS βT x) := by
  have e : x.map (toEAf D) = βT.val * frMapO S T βS βT x * (βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hS fS).2 (int_ct h)) (gram_frame_int T hT fT).1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

theorem mem_of_isIntM {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (h : IsIntM (frMapO S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  refine GlobalTheory.DatumFourier.mem_latO_of_int hS hT fS fT (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj he) hN
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) ?_ ?_ (isIntM_adj hS hT fS fT h)
  · intro PP' hPP' hm
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hPP'
    have h2 : Formalism.L2.DIV.starOHom ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hm
    rw [map_natCast] at h2
    exact hP PP hPP (GlobalTheory.HalfCompare.mem_of_dvd h2 (Dvd.intro_left _ rfl))
  · intro i j
    rw [Formalism.L2.Theta.cA_cA]
    exact hx i j

end GlobalTheory.HalfLatInt

theorem GlobalTheory.HalfLatInt.isIntM_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQ eQ he x hx
  obtain ⟨t, hQt⟩ := hQ
  have hSV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hP : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t PP (hQt hPP)
  exact ⟨GlobalTheory.HalfLatInt.mem_of_isIntM hSV hSW hBV.1 hBW.1 he hP hx,
    GlobalTheory.HalfLatInt.isIntM_of_mem hSV hBV.1 hBW.1 he hP hx⟩
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.CoefIndepProof

theorem coefIndep : GlobalTheory.BaseCmp.CoefIndep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i c0L hc h w hw
  obtain ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩ := hw
  obtain ⟨gramR, c0R, hT⟩ := hc
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := (R.B.L i A.μ0).pres.reps (fin (Vc D i) h)
  have hst : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D i)) : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) :=
    Formalism.L2.DIV.parLev_St k.2.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl _ _ hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP ⊢
  obtain ⟨P', hP', rfl⟩ := hP
  obtain ⟨e', -, h2', -, h4', -⟩ := hT'.coefL i A.μ0
  obtain ⟨e1, -, h2, -, h4, -⟩ := hT.coefL i A.μ0
  rw [← h4' c] at hP'
  obtain ⟨y, hy, rfl⟩ := hP'
  refine ⟨rhoVr (labLL D) (lamV D i) γE (e1 y), ⟨e1 y, ?_, rfl⟩, ?_⟩
  · rw [← h4 c]; exact ⟨y, hy, rfl⟩
  · have a1 := (hT'.mapL i).1 γ γE hγ (e' y)
    have a2 := (hT.mapL i).1 γ γE hγ (e1 y)
    change c0L' i (rhoVr (labLL D) (lamV D i) γE (e' y)) = c0L i (rhoVr (labLL D) (lamV D i) γE (e1 y))
    rw [a1, ← h2', h2]
    exact a2.symm

end GlobalTheory.CoefIndepProof
end
end

section

set_option autoImplicit false

noncomputable section

open Formalism.L2.DIV NumberField
open scoped TensorProduct

namespace GlobalTheory.BaseCmp

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isOfFinOrder_hom_of_finite {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : IsOfFinOrder (f g) :=
  f.isOfFinOrder (isOfFinOrder_of_finite g)

theorem levFn_isOfFinOrder (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E ℂ n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : IsOfFinOrder (levFn β L x) := by
  classical
  have hPP : ∀ PP : Pl E, Finite (kP PP) := fun PP =>
    Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hU : ∀ PP : Pl E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  have hG : ∀ (PP : Pl E) (r : ℕ), Finite (GL (Fin r) (kP PP)) := fun PP r => Finite.of_injective _ Units.val_injective
  have hG0 : Finite (G0 L.Pg L.r) := Pi.finite
  rw [← CommGroup.mem_torsion]
  unfold levFn
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · rw [CommGroup.mem_torsion]
    unfold ext1
    split_ifs with h
    · exact isOfFinOrder_hom_of_finite L.P.chi _
    · exact IsOfFinOrder.one
  · refine Subgroup.prod_mem _ fun PP _ => Subgroup.prod_mem _ fun c _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
  · refine Subgroup.prod_mem _ fun PP _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
end


theorem levLamRoot : LevLamRoot := by
  intro D S T B t k
  have h : IsOfFinOrder (B.levLam t k) := by
    rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
    exact levFn_isOfFinOrder _ _ _
  obtain ⟨m, hm, hmo⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  exact ⟨m, hm.ne', by rw [← Units.val_pow_eq_pow_val, hmo, Units.val_one]⟩

end GlobalTheory.BaseCmp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTypeVec

theorem typeVec_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  obtain ⟨t, hQt⟩ := hQt
  have sdV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hvac := hK.vecOf.1
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  have hth0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hvac.2.theta
  have hlat := hvac.2.lat
  have fixQ := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac R.ψ hlat heQ
  have hQpl := hK.pl
  have hdisj : Disjoint R.Pg (R.Q t) := Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hC.lev t
  obtain ⟨⟨esg, hesg, hegs⟩, -⟩ := heg
  obtain ⟨⟨esQ, hesQ, heQs⟩, -⟩ := heQ
  have h1 : eQ * eg = 0 := by
    rw [hegs, heQs, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    exact Formalism.IndefR.Fin.idem_orth ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP)
      (fun h => Finset.disjoint_left.1 hdisj hP (h ▸ hQt hP'))
  have h2 : eQ * cA D eg = 0 := by

    rw [hegs, heQs, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    refine Formalism.IndefR.Fin.idem_orth_conj ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP) fun hc => ?_
    obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hQpl P' hP'
    obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
    exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top hq (D.host.g_prime k) (hqg k)
      (Formalism.IndefR.Fin.nat_mem_of_conj hc (Formalism.IndefR.Fin.char_mem hq hcard))
      (Formalism.IndefR.Fin.g_mem_of_div R.toLevCh.C hk)
  have h3 : eg * cA D eQ = 0 := by
    have := congrArg (cA D) h2
    rwa [map_mul, Formalism.L2.Theta.cA_cA, map_zero, mul_comm] at this
  have h4 : cA D eg * cA D eQ = 0 := by rw [← map_mul, mul_comm, h1, map_zero]
  refine ⟨sdV, sdW, GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hvac.2.inf hfg hth0, fun u hu hh => ?_⟩
  refine GlobalTheory.VacFix.heisO_fix_of_isThetaAt D R.ψ _ _ (cA D eg) _ 1 (R.vacP i) _ fg u hfg
    (fun a b => ?_) (fun a b => ?_) (fixQ u hu hh)
  · rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm (cA D eg), h2, zero_mul]
    · rw [← hh a b, ← mul_assoc, h4, zero_mul]
  · rw [Formalism.L2.Theta.cA_cA]
    rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm eg, h1, zero_mul]
    · rw [← hh a b, ← mul_assoc, h3, zero_mul]

end GlobalTheory.KerTypeVec
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.LiftEquiv

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1

    simp [rowAct, map_sum, Matrix.map_apply]

theorem rowAct_detPol_eq {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowAct R M (detPol R n) = MvPolynomial.C M.det * detPol R n := by
  unfold detPol
  rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R), ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem rowAct_liftPol_eq {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    rowAct C (M.map e0) (liftPol e0 k f) = (e0 M.det) ^ k • liftPol e0 k (rowAct K M f) := by
  unfold liftPol
  have hd : (M.map e0).det = e0 M.det := (RingHom.map_det e0 M).symm
  rw [map_mul, map_pow, rowAct_detPol_eq, map_rowAct_eq, mul_pow, smul_eq_C_mul, map_pow, mul_assoc, hd]

theorem grp_tprod_eq (C : Type) [CommRing C] {ι : Type} (n : ℕ) (lamW : ι → ℕ → ℕ) (g : ι → GL (Fin n) C)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    grp C n lamW g (PiTensorProduct.tprod C y) =
      PiTensorProduct.tprod C (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (g τ) (y τ)) :=
  PiTensorProduct.map_tprod _ _

theorem scalar_eq {K C : Type} [Field K] [Field C] (e0 : K →+* C) {n : ℕ} (lam : DomWeight n) (k : ℕ) (c : ℤ)
    (h : ∀ hn : 0 < n, (k : ℤ) = lam.w ⟨n - 1, by omega⟩ + c) (g : GL (Fin n) K) :
    e0 (detPow K n (inside₂ K n g) lam.detShift) =
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e0 g) ^ c : Cˣ) : C) *
        e0 ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((inside₂ K n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [← h1]; exact Matrix.det_transpose _
  have h3 : ((Matrix.GeneralLinearGroup.map e0 g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C).det =
      e0 (g : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det e0 _).symm
  have h0 : e0 (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [map_ne_zero]; exact g.det_ne_zero
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, h1, h2, h3, map_zpow₀, map_inv₀]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have he : lam.detShift = k - c := by
      rw [h hn]; simp [DomWeight.detShift, hn]
    rw [he, inv_zpow', inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0]
    congr 1
    ring

theorem phi_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  intro K C _ _ e0 ι _ _ n lam lamW c Φ hS hΦ g v
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨x, hx, rfl⟩ := hP
    let M : ι → Matrix (Fin n) (Fin n) K := fun τ => ((g τ)⁻¹ : GL (Fin n) K)
    have hx' : ∀ τ, rowAct K (M τ) (x τ) ∈ nablaSq K n (lam τ) := fun τ =>
      Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ _ (hx τ)
    let w : VV K lam := ⟨Formalism.L2.DIV.ten fun τ => rowAct K (M τ) (x τ),
      Submodule.subset_span ⟨_, hx', rfl⟩⟩
    obtain ⟨y, hy, hyv⟩ := hΦ x ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ hx rfl
    obtain ⟨y', hy', hyw⟩ := hΦ _ w hx' rfl
    have hr : rhoK lam (invTrK g) ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = detTwK lam (invTrK g) • w := by
      apply Subtype.ext
      show detTwK lam (invTrK g) • trAct (invTrK g) (∏ τ, blockEmb K τ (x τ)) =
        detTwK lam (invTrK g) • ∏ τ, blockEmb K τ (rowAct K (M τ) (x τ))
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (x τ)
    have hg : (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (Matrix.GeneralLinearGroup.map e0 (g τ)) (y τ)) =
        fun τ => (e0 (M τ).det) ^ (lamW τ (n - 1)) • y' τ := by
      funext τ
      apply Subtype.ext
      show rowAct C (((Matrix.GeneralLinearGroup.map e0 (g τ))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) (y τ) =
        (e0 (M τ).det) ^ (lamW τ (n - 1)) • (y' τ : MvPolynomial (Fin n × Fin n) C)
      rw [hy, hy', ← map_inv]
      exact rowAct_liftPol_eq e0 _ (M τ) (x τ)
    rw [hr, LinearMap.map_smulₛₗ, hyw, hyv, lamG_apply, grp_tprod_eq, hg, MultilinearMap.map_smul_univ, smul_smul]
    congr 1
    rw [detTwK, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact scalar_eq e0 (lam τ) _ (c τ) (fun hn => hS τ ⟨n - 1, by omega⟩) (g τ)
  | zero =>
    show Φ (rhoK lam (invTrK g) 0) = lamG C n lamW c _ (Φ 0)
    simp only [map_zero]
  | add a b ha hb iha ihb =>
    show Φ (rhoK lam (invTrK g) (⟨a, ha⟩ + ⟨b, hb⟩)) = lamG C n lamW c _ (Φ (⟨a, ha⟩ + ⟨b, hb⟩))
    simp only [map_add (f := _)]
    rw [iha, ihb]
  | smul r a ha iha =>
    show Φ (rhoK lam (invTrK g) (r • ⟨a, ha⟩)) = lamG C n lamW c _ (Φ (r • ⟨a, ha⟩))
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, iha]

end GlobalTheory.FrameRead.LiftEquiv
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w → (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  first | exact @GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | exact GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | (intros; apply GlobalTheory.LieInj.tangent_eq_of_tanVal_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.BotRam.bottom_ram | exact GlobalTheory.BotRam.bottom_ram | (intros; apply GlobalTheory.BotRam.bottom_ram <;> assumption)
end

end

section

@[expose] public section


theorem _root_.GlobalTheory.T.coefLattice_indep_coefMap_proof : GlobalTheory.BaseCmp.CoefIndep := by
  first | exact @GlobalTheory.CoefIndepProof.coefIndep | exact GlobalTheory.CoefIndepProof.coefIndep | (intros; apply GlobalTheory.CoefIndepProof.coefIndep <;> assumption)

end
end

section

@[expose] public section


theorem _root_.GlobalTheory.T.levelCharacter_finiteOrder_definite_forms : GlobalTheory.BaseCmp.LevLamRoot := by
  first | exact @GlobalTheory.BaseCmp.levLamRoot | exact GlobalTheory.BaseCmp.levLamRoot | (intros; apply GlobalTheory.BaseCmp.levLamRoot <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | exact GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | (intros; apply GlobalTheory.HalfLatInt.isIntM_iff_mem_latP <;> assumption)

end
end
