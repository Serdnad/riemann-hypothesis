module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle439
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle543
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle198
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.ImaginaryGeneratorMulDenominator
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle576
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle199
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.TopLocData
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m) d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) → IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX → ∀ M : GlobalTheory.FinPl.Lat (Yc D (j + 1)), IsSelfDualC (Yc D (j + 1)) M → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M P) → ∃ (Lp : Fin n → LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT) (κ : ℂ), κ ≠ 0 ∧ (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FS (v.N (j + 1)) ∧ IntIn (Lp i).q D.sp.X' (Lp i).FT v.NT) ∧ (∀ F, IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F → comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (Lp i).e g) F) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∃ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (Lp i).q.e) (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) (prodDat Lp) F ∧ IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h d₀ hd₀ hΛ hΛX M hM hMv
  have hψ : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have hLT : IsSelfDualC D.sp.X' f.g.LT := hVT.bT.2 ▸ hv.sdT
  obtain ⟨κ, hκ, hdat⟩ := _root_.GlobalTheory.T.descent_top_standard_character_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h hψ d₀ hd₀ hΛ hΛX M hM hLT hMv
  refine ⟨_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT, κ, hκ, fun i => rfl, fun i => ⟨?_, ?_⟩, fun F hF => (_root_.GlobalTheory.TopLocData.eGT_comb_eq_foldr_eigenvectorAtPlace hGP h).2 F hF, hdat⟩
  · exact intIn_reN (G i).q v.N (_root_.GlobalTheory.TopLocData.s_eq_alt (G i) h) _ ((G i).latY ((G i).s + 1) 0 rfl)
  · have := (G i).latT
    rw [hVT.bT.2] at this ⊢
    exact this
end GlobalTheory.TopLocData
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT


theorem second_step_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  intro hGAR D cf jE A S In low Pq M tup Q hM hPq hGal hRC hCh hstar hexp hsplit
  obtain ⟨c1, hc1⟩ := _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt hGAR D cf jE A hGal hRC hCh hstar
  obtain ⟨c2, hc2⟩ := _root_.GlobalTheory.T.exists_weight_data_integral_alt hGAR D cf jE A hstar hexp
  refine ⟨fun l _ j => ⟨(c1 l j).1 ⊔ (c2 l j).1, by haveI := (c1 l j).2; haveI := (c2 l j).2; infer_instance⟩,
    fun b0 b1 Sx T Sp hc0 hSb hconj hlow => ?_⟩
  have hb1 : ∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_left (hc0 l j)
  have hb2 : ∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_right (hc0 l j)
  obtain ⟨rho, hrho, hrhoS⟩ := hc1 b0 b1 Sx T Sp hb1
  obtain ⟨wt, hwt⟩ := hc2 b0 b1 Sx T Sp hb2
  have hfg := GlobalTheory.T.twisted_lattice_finitely_generated_spanning D S In T
  have hfg' : ∀ i j b, (BsupT D T S i j b).FG := fun i j b => (hfg i j b).1
  have hst := _root_.GlobalTheory.T.hkStab_of_subset_of_star_closed D cf jE A S In b0 b1 Sx T Sp hSb hstar
  obtain ⟨sd, hsd1, hsd2, hsd3, hsd4, hsd5⟩ := _root_.GlobalTheory.T.exists_signature_data_span_alt D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  have he := GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal D
  have hpsi := GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide D S In T hstar
  refine ⟨mkF D T S In hfg' hst sd rho hrho, mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq,
    fun i j b => hfg i j b, fun th => ⟨?_⟩⟩
  let N : TwNew D := ⟨T.ntw A.bare (mkF D T S In hfg' hst sd rho hrho) (TwL.empty T),
    mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq, th, Sp.br, Sp.br_ind⟩
  have hU := tied_U_clauses N.toD7 (fun (i : T.Tw) k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k))
    (fun _ => xiRedNZ N.toD7) (fun h i k => hpsi.2 h i k) rfl (fun i b u => hpsi.1 i b u)
  have hLev : ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m → NX.AdmTw N.toD7 i k Q ψ →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) :=
    fun i j b k Q ψ h1 h2 hadm => _root_.GlobalTheory.T.places_over_real_subfield_split_alt hGAR D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt
      (fun i j b h1 h2 => ⟨(hwt i j b h1 h2).1, (hwt i j b h1 h2).2.1⟩) A.bare (mkF D T S In hfg' hst sd rho hrho)
      i j b k Q ψ h1 h2 hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
  let E : NExpTied N.toD7 :=
    { U_eq := hU.1
      psiU_gen := hU.2.1
      psiU_side := hU.2.2.1
      psiU_xi := hU.2.2.2
      delU_cont := fun (i : T.Tw) Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.1 Q M
      delU_ine := fun i Q M hQ P hP =>
        GlobalTheory.T.inertia_surjective_of_admQ hGAR D cf b0 b1 Sx T Sp A.bare (mkF D T S In hfg' hst sd rho hrho) i Q M hQ P hP
      thU_empty := fun i j b M d => PEmpty.elim d
      sgnT := 1
      sgnT_one := rfl
      Wt := wt.Wt
      acgWt := fun (i : T.Tw) j b => wt.acg i j b
      modWt := fun (i : T.Tw) j b => wt.mod i j b
      fdWt := fun (i : T.Tw) j b => wt.fd i j b
      rhoW := fun (i : T.Tw) j b => wt.rhoW i j b
      rhoW_irr := fun i j b h1 h2 => (hwt i j b h1 h2).1
      rhoW_alg := fun i j b h1 h2 => (hwt i j b h1 h2).2.1
      tauG := fun (i : T.Tw) j b kv => tauT D T i j b kv
      sgnG := 1
      sgnG_one := rfl
      tau_galois_first_character := fun (i : T.Tw) j b kv x u h1 h2 hl hu => by
        have h := GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l hGAR D cf b0 b1 Sx T Sp i j b kv h1 h2 hl
        show ((tauT D T i j b kv x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) =
          baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) ((1 : ℤ) * 1) u).1
        rw [show ((1 : ℤ) * 1) = 1 from rfl]
        unfold tauT
        rw [dite_eq_left h]
        exact h.choose_spec x u hu
      mtV := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        @NX.MtVReal.mk N.toD7 i j b k Q ψ 1 (wt.Wt i j b) (wt.acg i j b) (wt.mod i j b) (wt.rhoW i j b) (tauT D T i j b)
          (WkT D T wt i j b k)
          (inferInstance : AddCommGroup (WkT D T wt i j b k))
          (inferInstance : Module (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (inferInstance : FiniteDimensional (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (rhoKT D T wt i j b k)
          ((hwt i j b h1 h2).2.2.1 k)
          (isAlgWeightF_bc (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b) (hwt i j b h1 h2).2.1)
          ⟨_, inferInstance, inferInstance, Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b),
            Algebra.TensorProduct.basis (FractionRing (T.Ok i k)) (Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b)),
            fun γ => toMatrix_bcRep (K' := FractionRing (T.Ok i k)) _ (wt.rhoW i j b) γ⟩
          (hLev i j b k Q ψ h1 h2 hadm).choose.J
          (hLev i j b k Q ψ h1 h2 hadm).choose.χ
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.QP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.DP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.sp
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.redG
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.1
          (by
            intro κ hκ
            have hgVal (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
                (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
                (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
                NX.gVal N.toD7 i k b kv s red (tauT D T i j b kv) x =
                  gValT D T In.θ i k b kv s red (tauT D T i j b kv) x := by
              unfold NX.gVal gValT
              congr 1
              have hunit_eq : IsUnit (red (NX.intLift s.v (NX.detT N.toD7.R.r x))) ↔
                  IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) := Iff.rfl
              by_cases hunit : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))
              · erw [dif_pos (hunit_eq.mpr hunit), dif_pos hunit]
                rfl
              · erw [dif_neg (fun hp => hunit (hunit_eq.mp hp)), dif_neg hunit]
                rfl
            let A₀ := (hLev i j b k Q ψ h1 h2 hadm).choose
            have eg :
                (∏ kv, NX.gVal N.toD7 i k b kv (A₀.sp (NX.pG N.toD7 kv)) (A₀.redG kv) (tauT D T i j b kv)
                  (NX.locM (A₀.sp (NX.pG N.toD7 kv)) κ)) =
                ∏ kv, gValT D T In.θ i k b kv (A₀.sp (NX.pG D kv)) (A₀.redG kv) (tauT D T i j b kv)
                  (NX.locM (A₀.sp (NX.pG D kv)) κ) := by
              exact Finset.prod_congr rfl fun kv _ => hgVal kv _ _ _
            erw [eg]
            exact (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.2 κ hκ)
          (LinearEquiv.ofEq (MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))
            (NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k)
              (hLev i j b k Q ψ h1 h2 hadm).choose.J (hLev i j b k Q ψ h1 h2 hadm).choose.χ)
            (by rw [MtSubT, dite_eq_left (hLev i j b k Q ψ h1 h2 hadm)]))
      rhoW_hw := fun i j b t h1 h2 => (hwt i j b h1 h2).2.2.2.1 t
      rhoW_wt := fun i j b t hj hjm sh lam h1 h2 => (hwt i j b hj hjm).2.2.2.2 t sh lam h1 h2 }
  exact
    { twF := { K0 := Sp.K0, eO0 := Sp.eO0, j0 := Sp.j0, Lw := Sp.Lw, eO := Sp.eO, eOk := Sp.eOk, iCq := Sp.iCq,
               S0x := fun _ => Sx }
      tw := { pl_emb := fun i => ⟨Sp.eTw i, Sp.pl_emb i⟩
              ringSpec_baseIntegersEquiv_algebraMap := Sp.ringSpec_baseIntegersEquiv_algebraMap
              ringSpec_baseEmbedding_compatible := Sp.ringSpec_baseEmbedding_compatible
              eO_alg := Sp.eO_alg
              eOk_alg := Sp.eOk_alg
              mu_g := Sp.mu_g
              hk_split := fun i j b k P hP => _root_.GlobalTheory.T.lattice_basis_free_module_place_alt D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P
                (hfr := (mkF D T S In hfg' hst sd rho hrho).freeB i j b)
                (hfi := (mkF D T S In hfg' hst sd rho hrho).finB i j b) hP
              ringSpec_excludedPlaces_eq := Sp.ringSpec_excludedPlaces_eq
              concreteTwistFrame_extraExcludedPlaces_conj := fun i P P' h h' => hconj P P' h h'
              B_range := fun (i : T.Tw) j b => by
                show LinearMap.range (BI D T S In i j b).subtype = _
                rw [Submodule.range_subtype]
                rfl
              sig_inj := hsd2
              qs_pos := fun i lam => PEmpty.elim lam
              concreteTwistFrame_extraExcluded_over_smallPrimes := fun i => hlow }
      cover := fun w => GlobalTheory.T.exists_twistIndex_of_coefficientField_place D cf b0 b1 Sx T Sp w
      chiD := { mu0 := Sp.mu0H, etaT := Sp.etaH, del := Sp.delH, psi := fun a => A.bare.elim a,
                chiI := fun s lam => PEmpty.elim lam, embO := Sp.embO }
      chi := { psi := fun a => A.bare.elim a, del_fix := Sp.del_fix, delta := Sp.delta, chi1 := Sp.chi1,
               ringSpec_sidedEmbedding_fixedField := Sp.ringSpec_sidedEmbedding_fixedField, etaT_unr := Sp.etaT_unr, etaT_inf := Sp.etaT_inf,
               lamG := fun s lam => PEmpty.elim lam }
      eta_eq := Sp.eta_eq
      ringSpec_normalisedCharacter_eq := Sp.ringSpec_normalisedCharacter_eq
      del_eq := Sp.del_eq
      iCq_embO := Sp.iCq_embO
      embO_star := Sp.embO_star
      deltaRead := Sp.deltaRead
      exp := E
      pq := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        ⟨(hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.1, (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.1⟩
      psiU := fun i b u hu hu' => rfl
      rho := In.rho
      chiL := In.chi
      hs := In.hs
      eF := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose
      bsup := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.1
      act := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.1
      cHk := fun (i : T.Tw) b P => cHkT D T i b P
      hkEq := fun i j b h1 h2 k P x _ _ _ =>
        (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.2 k P x
      cHk_del := fun i b P hP σ hσ => GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta D T i b P hP σ hσ
      hk_emb := fun (i : T.Tw) j b k P x h1 h2 hP hs hk => by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · show ((hkB D T S In hst i j b 0 P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b 0 P (x : ↥(BI D T S In i j b)).1
          rw [show hkB D T S In hst i j b 0 P = 1 from hkB_zero D T S In hst i j b P,
            show hkT D T S In i j b 0 P = 1 from hkT_zero D T S In i j b P]
          rfl
        · show ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b k P (x : ↥(BI D T S In i j b)).1
          unfold hkB
          rw [dite_eq_left ⟨h1, h2, hk0, hk, hs, hP⟩]
          rfl
      sigSpan := fun i j b h1 h2 => hsd1 i j b h1 h2
      rowS := sd.rowS
      rowS_eig := hsd4
      hEig_zero := hsd5
      rhoS := fun i s => ⟨(hsd3 i s).1, (hsd3 i s).2, fun π hc hr hl φ ι hz hι =>
        hrhoS i (sd.rowS i s) (sd.side i s) ⟨sd.jS i s, (sd.jS_range i s).1, (sd.jS_range i s).2, (hsd3 i s).1⟩
          (hsd3 i s).2 π hc hr hl φ ι hz hι⟩ }
end GlobalTheory.HeightCounting.FormsStep
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
open Formalism.BasicNotions.TH Formalism.IndefR.Mult
section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
open Formalism.BasicNotions.TH Formalism.IndefR.Mult
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
theorem heckeAtState_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∃ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' := by
  intro hL hD hT hR
  refine (_root_.GlobalTheory.T.rationalHecke_of_levelA hL hD hT hR).trans (StepW.of_all fun K B f T w _ _ H P x l => ?_)
  exact exists_heckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) (H P x l) (GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded P x)
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
end
end
end

section



section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DegVal
end GlobalTheory.DegVal
namespace GlobalTheory.DegVal
theorem exists_phiAt_pos_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  intro hP hD _ _
  refine Formalism.MainNotions.Closed.imp hD fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  exact ⟨C, hC, x0, fun x hx hle ι p hp i _ Y _ Z TF y hy ν hν => _root_.GlobalTheory.DegVal.degree_valuation_phi_pos hP TF Z y hy ν hν⟩
end GlobalTheory.DegVal
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  first | exact @_root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt | exact _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt | (intros; apply _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt <;> assumption)
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_chain_step_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 = B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  first | exact @_root_.GlobalTheory.PenVol.pen_vol_alt | exact _root_.GlobalTheory.PenVol.pen_vol_alt | (intros; apply _root_.GlobalTheory.PenVol.pen_vol_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_reduction_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ hy : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U, (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * _root_.GlobalTheory.MiTop.realCharacter W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) = 1 := by
  first | exact @_root_.GlobalTheory.FamTraceChi.trace_chi_alt | exact _root_.GlobalTheory.FamTraceChi.trace_chi_alt | (intros; apply _root_.GlobalTheory.FamTraceChi.trace_chi_alt <;> assumption)
end
end
